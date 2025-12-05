// SPDX-License-Identifier: GPL-2.0+
/*****************************************************************************/

/*
 *      devio.c  --  User space communication with USB devices.
 *
 *      Copyright (C) 1999-2000  Thomas Sailer (sailer@ife.ee.ethz.ch)
 *
 *  This file implements the usbfs/x/y files, where
 *  x is the bus number and y the device number.
 *
 *  It allows user space programs/"drivers" to communicate directly
 *  with USB devices without intervening kernel driver.
 *
 *  Revision history
 *    22.12.1999   0.1   Initial release (split from proc_usb.c)
 *    04.01.2000   0.2   Turned into its own filesystem
 *    30.09.2005   0.3   Fix user-triggerable oops in async URB delivery
 *                             (CAN-2005-3055)
 */

/*****************************************************************************/

#include <linux/fs.h>
#include <linux/mm.h>
#include <linux/sched/signal.h>
#include <linux/slab.h>
#include <linux/signal.h>
#include <linux/poll.h>
#include <linux/module.h>
#include <linux/string.h>
#include <linux/usb.h>
#include <linux/usbdevice_fs.h>
#include <linux/usb/hcd.h>        /* for usbcore internals */
#include <linux/cdev.h>
#include <linux/notifier.h>
#include <linux/security.h>
#include <linux/user_namespace.h>
#include <linux/scatterlist.h>
#include <linux/uaccess.h>
#include <linux/dma-mapping.h>
#include <asm/byteorder.h>
#include <linux/moduleparam.h>

#include "usb.h"

#ifdef CONFIG_PM
#define MAYBE_CAP_SUSPEND        USBDEVFS_CAP_SUSPEND
#else
#define MAYBE_CAP_SUSPEND        0
#endif

#define USB_MAXBUS                        64
#define USB_DEVICE_MAX                        (USB_MAXBUS * 128)
#define USB_SG_SIZE                        16384 

static DEFINE_MUTEX(usbfs_mutex);

struct usb_dev_state {
        struct list_head list;
        struct usb_device *dev;
        struct file *file;
        spinlock_t lock;
        struct list_head async_pending;
        struct list_head async_completed;
        struct list_head memory_list;
        wait_queue_head_t wait;
        wait_queue_head_t wait_for_resume;
        unsigned int discsignr;
        struct pid *disc_pid;
        const struct cred *cred;
        sigval_t disccontext;
        unsigned long ifclaimed;
        u32 disabled_bulk_eps;
        unsigned long interface_allowed_mask;
        int not_yet_resumed;
        bool suspend_allowed;
        bool privileges_dropped;
        
        struct mutex concurrent_mutex;   
        atomic_t active_urbs;           
        wait_queue_head_t wait_queue;
        unsigned int max_concurrent_urbs;
};

struct usb_memory {
        struct list_head memlist;
        int vma_use_count;
        int urb_use_count;
        u32 size;
        void *mem;
        dma_addr_t dma_handle;
        unsigned long vm_start;
        struct usb_dev_state *ps;
};

struct async {
        struct list_head asynclist;
        struct usb_dev_state *ps;
        struct pid *pid;
        const struct cred *cred;
        unsigned int signr;
        unsigned int ifnum;
        void __user *userbuffer;
        void __user *userurb;
        sigval_t userurb_sigval;
        struct urb *urb;
        struct usb_memory *usbm;
        unsigned int mem_usage;
        int status;
        u8 bulk_addr;
        u8 bulk_status;
};

static bool usbfs_snoop;
module_param(usbfs_snoop, bool, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(usbfs_snoop, "true to log all usbfs traffic");

static unsigned usbfs_snoop_max = 65536;
module_param(usbfs_snoop_max, uint, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(usbfs_snoop_max,
                "maximum number of bytes to print while snooping");

#define snoop(dev, format, arg...)                                \
        do {                                                        \
                if (usbfs_snoop)                                \
                        dev_info(dev, format, ## arg);                \
        } while (0)

enum snoop_when {
        SUBMIT, COMPLETE
};

#define USB_DEVICE_DEV                MKDEV(USB_DEVICE_MAJOR, 0)

/* Limit on the total amount of memory we can allocate for transfers */
static u32 usbfs_memory_mb = 16;
module_param(usbfs_memory_mb, uint, 0644);
MODULE_PARM_DESC(usbfs_memory_mb,
                "maximum MB allowed for usbfs buffers (0 = no limit)");

/* Hard limit, necessary to avoid arithmetic overflow */
#define USBFS_XFER_MAX         (UINT_MAX / 2 - 1000000)

static atomic64_t usbfs_memory_usage;        /* Total memory currently allocated */

/* Check whether it's okay to allocate more memory for a transfer */
static int usbfs_increase_memory_usage(u64 amount)
{
        u64 lim;

        lim = READ_ONCE(usbfs_memory_mb);
        lim <<= 20;

        atomic64_add(amount, &usbfs_memory_usage);

        if (lim > 0 && atomic64_read(&usbfs_memory_usage) > lim) {
                atomic64_sub(amount, &usbfs_memory_usage);
                return -ENOMEM;
        }

        return 0;
}

/* Memory for a transfer is being deallocated */
static void usbfs_decrease_memory_usage(u64 amount)
{
        atomic64_sub(amount, &usbfs_memory_usage);
}

static int connected(struct usb_dev_state *ps)
{
        return (!list_empty(&ps->list) &&
                        ps->dev->state != USB_STATE_NOTATTACHED);
}

static void dec_usb_memory_use_count(struct usb_memory *usbm, int *count)
{
        struct usb_dev_state *ps = usbm->ps;
        unsigned long flags;

        spin_lock_irqsave(&ps->lock, flags);
        --*count;
        if (usbm->urb_use_count == 0 && usbm->vma_use_count == 0) {
                list_del(&usbm->memlist);
                spin_unlock_irqrestore(&ps->lock, flags);

                usb_free_coherent(ps->dev, usbm->size, usbm->mem,
                                usbm->dma_handle);
                usbfs_decrease_memory_usage(
                        usbm->size + sizeof(struct usb_memory));
                kfree(usbm);
        } else {
                spin_unlock_irqrestore(&ps->lock, flags);
        }
}

static void usbdev_vm_open(struct vm_area_struct *vma)
{
        struct usb_memory *usbm = vma->vm_private_data;
        unsigned long flags;

        spin_lock_irqsave(&usbm->ps->lock, flags);
        ++usbm->vma_use_count;
        spin_unlock_irqrestore(&usbm->ps->lock, flags);
}

static void usbdev_vm_close(struct vm_area_struct *vma)
{
        struct usb_memory *usbm = vma->vm_private_data;

        dec_usb_memory_use_count(usbm, &usbm->vma_use_count);
}

static const struct vm_operations_struct usbdev_vm_ops = {
        .open = usbdev_vm_open,
        .close = usbdev_vm_close
};

static int usbdev_mmap(struct file *file, struct vm_area_struct *vma)
{
        struct usb_memory *usbm = NULL;
        struct usb_dev_state *ps = file->private_data;
        struct usb_hcd *hcd = bus_to_hcd(ps->dev->bus);
        size_t size = vma->vm_end - vma->vm_start;
        void *mem;
        unsigned long flags;
        dma_addr_t dma_handle;
        int ret;

        ret = usbfs_increase_memory_usage(size + sizeof(struct usb_memory));
        if (ret)
                goto error;

        usbm = kzalloc(sizeof(struct usb_memory), GFP_KERNEL);
        if (!usbm) {
                ret = -ENOMEM;
                goto error_decrease_mem;
        }

        mem = usb_alloc_coherent(ps->dev, size, GFP_USER | __GFP_NOWARN,
                        &dma_handle);
        if (!mem) {
                ret = -ENOMEM;
                goto error_free_usbm;
        }

        memset(mem, 0, size);

        usbm->mem = mem;
        usbm->dma_handle = dma_handle;
        usbm->size = size;
        usbm->ps = ps;
        usbm->vm_start = vma->vm_start;
        usbm->vma_use_count = 1;
        INIT_LIST_HEAD(&usbm->memlist);

        if (hcd->localmem_pool || !hcd_uses_dma(hcd)) {
                if (remap_pfn_range(vma, vma->vm_start,
                                    virt_to_phys(usbm->mem) >> PAGE_SHIFT,
                                    size, vma->vm_page_prot) < 0) {
                        dec_usb_memory_use_count(usbm, &usbm->vma_use_count);
                        return -EAGAIN;
                }
        } else {
                if (dma_mmap_coherent(hcd->self.sysdev, vma, mem, dma_handle,
                                      size)) {
                        dec_usb_memory_use_count(usbm, &usbm->vma_use_count);
                        return -EAGAIN;
                }
        }

        vma->vm_flags |= VM_IO;
        vma->vm_flags |= (VM_DONTEXPAND | VM_DONTDUMP);
        vma->vm_ops = &usbdev_vm_ops;
        vma->vm_private_data = usbm;

        spin_lock_irqsave(&ps->lock, flags);
        list_add_tail(&usbm->memlist, &ps->memory_list);
        spin_unlock_irqrestore(&ps->lock, flags);

        return 0;

error_free_usbm:
        kfree(usbm);
error_decrease_mem:
        usbfs_decrease_memory_usage(size + sizeof(struct usb_memory));
error:
        return ret;
}

static ssize_t usbdev_read(struct file *file, char __user *buf, size_t nbytes,
                           loff_t *ppos)
{
        struct usb_dev_state *ps = file->private_data;
        struct usb_device *dev = ps->dev;
        ssize_t ret = 0;
        unsigned len;
        loff_t pos;
        int i;

        pos = *ppos;
        usb_lock_device(dev);
        if (!connected(ps)) {
                ret = -ENODEV;
                goto err;
        } else if (pos < 0) {
                ret = -EINVAL;
                goto err;
        }

        if (pos < sizeof(struct usb_device_descriptor)) {
                /* 18 bytes - fits on the stack */
                struct usb_device_descriptor temp_desc;

                memcpy(&temp_desc, &dev->descriptor, sizeof(dev->descriptor));
                le16_to_cpus(&temp_desc.bcdUSB);
                le16_to_cpus(&temp_desc.idVendor);
                le16_to_cpus(&temp_desc.idProduct);
                le16_to_cpus(&temp_desc.bcdDevice);

                len = sizeof(struct usb_device_descriptor) - pos;
                if (len > nbytes)
                        len = nbytes;
                if (copy_to_user(buf, ((char *)&temp_desc) + pos, len)) {
                        ret = -EFAULT;
                        goto err;
                }

                *ppos += len;
                buf += len;
                nbytes -= len;
                ret += len;
        }

        pos = sizeof(struct usb_device_descriptor);
        for (i = 0; nbytes && i < dev->descriptor.bNumConfigurations; i++) {
                struct usb_config_descriptor *config =
                        (struct usb_config_descriptor *)dev->rawdescriptors[i];
                unsigned int length = le16_to_cpu(config->wTotalLength);

                if (*ppos < pos + length) {

                        /* The descriptor may claim to be longer than it
                         * really is.  Here is the actual allocated length. */
                        unsigned alloclen =
                                le16_to_cpu(dev->config[i].desc.wTotalLength);

                        len = length - (*ppos - pos);
                        if (len > nbytes)
                                len = nbytes;

                        /* Simply don't write (skip over) unallocated parts */
                        if (alloclen > (*ppos - pos)) {
                                alloclen -= (*ppos - pos);
                                if (copy_to_user(buf,
                                    dev->rawdescriptors[i] + (*ppos - pos),
                                    min(len, alloclen))) {
                                        ret = -EFAULT;
                                        goto err;
                                }
                        }

                        *ppos += len;
                        buf += len;
                        nbytes -= len;
                        ret += len;
                }

                pos += length;
        }

err:
        usb_unlock_device(dev);
        return ret;
}

/*
 * async list handling
 */

static struct async *alloc_async(unsigned int numisoframes)
{
        struct async *as;

        as = kzalloc(sizeof(struct async), GFP_KERNEL);
        if (!as)
                return NULL;
        as->urb = usb_alloc_urb(numisoframes, GFP_KERNEL);
        if (!as->urb) {
                kfree(as);
                return NULL;
        }
        return as;
}

static void free_async(struct async *as)
{
        int i;

        put_pid(as->pid);
        if (as->cred)
                put_cred(as->cred);
        for (i = 0; i < as->urb->num_sgs; i++) {
                if (sg_page(&as->urb->sg[i]))
                        kfree(sg_virt(&as->urb->sg[i]));
        }

        kfree(as->urb->sg);
        if (as->usbm == NULL)
                kfree(as->urb->transfer_buffer);
        else
                dec_usb_memory_use_count(as->usbm, &as->usbm->urb_use_count);

        kfree(as->urb->setup_packet);
        usb_free_urb(as->urb);
        usbfs_decrease_memory_usage(as->mem_usage);
        kfree(as);
}

static void async_newpending(struct async *as)
{
        struct usb_dev_state *ps = as->ps;
        unsigned long flags;

        spin_lock_irqsave(&ps->lock, flags);
        list_add_tail(&as->asynclist, &ps->async_pending);
        spin_unlock_irqrestore(&ps->lock, flags);
}

static void async_removepending(struct async *as)
{
        struct usb_dev_state *ps = as->ps;
        unsigned long flags;

        spin_lock_irqsave(&ps->lock, flags);
        list_del_init(&as->asynclist);
        spin_unlock_irqrestore(&ps->lock, flags);
}

static struct async *async_getcompleted(struct usb_dev_state *ps)
{
        unsigned long flags;
        struct async *as = NULL;

        spin_lock_irqsave(&ps->lock, flags);
        if (!list_empty(&ps->async_completed)) {
                as = list_entry(ps->async_completed.next, struct async,
                                asynclist);
                list_del_init(&as->asynclist);
        }
        spin_unlock_irqrestore(&ps->lock, flags);
        return as;
}

static struct async *async_getpending(struct usb_dev_state *ps,
                                             void __user *userurb)
{
        struct async *as;

        list_for_each_entry(as, &ps->async_pending, asynclist)
                if (as->userurb == userurb) {
                        list_del_init(&as->asynclist);
                        return as;
                }

        return NULL;
}

static void snoop_urb(struct usb_device *udev,
                void __user *userurb, int pipe, unsigned length,
                int timeout_or_status, enum snoop_when when,
                unsigned char *data, unsigned data_len)
{
        static const char *types[] = {"isoc", "int", "ctrl", "bulk"};
        static const char *dirs[] = {"out", "in"};
        int ep;
        const char *t, *d;

        if (!usbfs_snoop)
                return;

        ep = usb_pipeendpoint(pipe);
        t = types[usb_pipetype(pipe)];
        d = dirs[!!usb_pipein(pipe)];

        if (userurb) {                /* Async */
                if (when == SUBMIT)
                        dev_info(&udev->dev, "userurb %px, ep%d %s-%s, "
                                        "length %u\n",
                                        userurb, ep, t, d, length);
                else
                        dev_info(&udev->dev, "userurb %px, ep%d %s-%s, "
                                        "actual_length %u status %d\n",
                                        userurb, ep, t, d, length,
                                        timeout_or_status);
        } else {
                if (when == SUBMIT)
                        dev_info(&udev->dev, "ep%d %s-%s, length %u, "
                                        "timeout %d\n",
                                        ep, t, d, length, timeout_or_status);
                else
                        dev_info(&udev->dev, "ep%d %s-%s, actual_length %u, "
                                        "status %d\n",
                                        ep, t, d, length, timeout_or_status);
        }

        data_len = min(data_len, usbfs_snoop_max);
        if (data && data_len > 0) {
                print_hex_dump(KERN_DEBUG, "data: ", DUMP_PREFIX_NONE, 32, 1,
                        data, data_len, 1);
        }
}

static void snoop_urb_data(struct urb *urb, unsigned len)
{
        int i, size;

        len = min(len, usbfs_snoop_max);
        if (!usbfs_snoop || len == 0)
                return;

        if (urb->num_sgs == 0) {
                print_hex_dump(KERN_DEBUG, "data: ", DUMP_PREFIX_NONE, 32, 1,
                        urb->transfer_buffer, len, 1);
                return;
        }

        for (i = 0; i < urb->num_sgs && len; i++) {
                size = (len > USB_SG_SIZE) ? USB_SG_SIZE : len;
                print_hex_dump(KERN_DEBUG, "data: ", DUMP_PREFIX_NONE, 32, 1,
                        sg_virt(&urb->sg[i]), size, 1);
                len -= size;
        }
}

static int copy_urb_data_to_user(u8 __user *userbuffer, struct urb *urb)
{
        unsigned i, len, size;

        if (urb->number_of_packets > 0)                /* Isochronous */
                len = urb->transfer_buffer_length;
        else                                        /* Non-Isoc */
                len = urb->actual_length;

        if (urb->num_sgs == 0) {
                if (copy_to_user(userbuffer, urb->transfer_buffer, len))
                        return -EFAULT;
                return 0;
        }

        for (i = 0; i < urb->num_sgs && len; i++) {
                size = (len > USB_SG_SIZE) ? USB_SG_SIZE : len;
                if (copy_to_user(userbuffer, sg_virt(&urb->sg[i]), size))
                        return -EFAULT;
                userbuffer += size;
                len -= size;
        }

        return 0;
}

#define AS_CONTINUATION        1
#define AS_UNLINK        2

static void cancel_bulk_urbs(struct usb_dev_state *ps, unsigned bulk_addr)
__releases(ps->lock)
__acquires(ps->lock)
{
        struct urb *urb;
        struct async *as;

        /* Mark all the pending URBs that match bulk_addr, up to but not
         * including the first one without AS_CONTINUATION.  If such an
         * URB is encountered then a new transfer has already started so
         * the endpoint doesn't need to be disabled; otherwise it does.
         */
        list_for_each_entry(as, &ps->async_pending, asynclist) {
                if (as->bulk_addr == bulk_addr) {
                        if (as->bulk_status != AS_CONTINUATION)
                                goto rescan;
                        as->bulk_status = AS_UNLINK;
                        as->bulk_addr = 0;
                }
        }
        ps->disabled_bulk_eps |= (1 << bulk_addr);

        /* Now carefully unlink all the marked pending URBs */
 rescan:
        list_for_each_entry_reverse(as, &ps->async_pending, asynclist) {
                if (as->bulk_status == AS_UNLINK) {
                        as->bulk_status = 0;                /* Only once */
                        urb = as->urb;
                        usb_get_urb(urb);
                        spin_unlock(&ps->lock);                /* Allow completions */
                        usb_unlink_urb(urb);
                        usb_put_urb(urb);
                        spin_lock(&ps->lock);
                        goto rescan;
                }
        }
}

static void async_completed(struct urb *urb)
{
        struct async *as = urb->context;
        struct usb_dev_state *ps = as->ps;
        struct pid *pid = NULL;
        const struct cred *cred = NULL;
        unsigned long flags;
        sigval_t addr;
        int signr, errno;

        spin_lock_irqsave(&ps->lock, flags);
        list_move_tail(&as->asynclist, &ps->async_completed);
        as->status = urb->status;
        signr = as->signr;
        if (signr) {
                errno = as->status;
                addr = as->userurb_sigval;
                pid = get_pid(as->pid);
                cred = get_cred(as->cred);
        }
        snoop(&urb->dev->dev, "urb complete\n");
        snoop_urb(urb->dev, as->userurb, urb->pipe, urb->actual_length,
                        as->status, COMPLETE, NULL, 0);
        if (usb_urb_dir_in(urb))
                snoop_urb_data(urb, urb->actual_length);

        if (as->status < 0 && as->bulk_addr && as->status != -ECONNRESET &&
                        as->status != -ENOENT)
                cancel_bulk_urbs(ps, as->bulk_addr);

        atomic_dec(&ps->active_urbs);
        
        wake_up_interruptible(&ps->wait_queue);

        wake_up(&ps->wait);
        spin_unlock_irqrestore(&ps->lock, flags);

        if (signr) {
                kill_pid_usb_asyncio(signr, errno, addr, pid, cred);
                put_pid(pid);
                put_cred(cred);
        }
}

static void destroy_async(struct usb_dev_state *ps, struct list_head *list)
{
        struct urb *urb;
        struct async *as;
        unsigned long flags;

        spin_lock_irqsave(&ps->lock, flags);
        while (!list_empty(list)) {
                as = list_last_entry(list, struct async, asynclist);
                list_del_init(&as->asynclist);
                urb = as->urb;
                usb_get_urb(urb);

                /* drop the spinlock so the completion handler can run */
                spin_unlock(&ps->lock, flags);
                usb_kill_urb(urb);
                usb_put_urb(urb);
                spin_lock_irqsave(&ps->lock, flags);
        }
        spin_unlock(&ps->lock, flags);
}

static void destroy_async_on_interface(struct usb_dev_state *ps,
                                       unsigned int ifnum)
{
        struct list_head *p, *q, hitlist;
        unsigned long flags;

        INIT_LIST_HEAD(&hitlist);
        spin_lock_irqsave(&ps->lock, flags);
        list_for_each_safe(p, q, &ps->async_pending)
                if (ifnum == list_entry(p, struct async, asynclist)->ifnum)
                        list_move_tail(p, &hitlist);
        spin_unlock_irqrestore(&ps->lock, flags);
        destroy_async(ps, &hitlist);
}

static void destroy_all_async(struct usb_dev_state *ps)
{
        destroy_async(ps, &ps->async_pending);
}

/*
 * interface claims are made only at the request of user level code,
 * which can also release them (explicitly or by closing files).
 * they're also undone when devices disconnect.
 */

static int driver_probe(struct usb_interface *intf,
                        const struct usb_device_id *id)
{
        return -ENODEV;
}

static void driver_disconnect(struct usb_interface *intf)
{
        struct usb_dev_state *ps = usb_get_intfdata(intf);
        unsigned int ifnum = intf->altsetting->desc.bInterfaceNumber;

        if (!ps)
                return;

        /* NOTE:  this relies on usbcore having canceled and completed
         * all pending I/O requests; 2.6 does that.
         */

        if (likely(ifnum < 8*sizeof(ps->ifclaimed)))
                clear_bit(ifnum, &ps->ifclaimed);
        else
                dev_warn(&intf->dev, "interface number %u out of range\n",
                         ifnum);

        usb_set_intfdata(intf, NULL);

        /* force async requests to complete */
        destroy_async_on_interface(ps, ifnum);
}

/* We don't care about suspend/resume of claimed interfaces */
static int driver_suspend(struct usb_interface *intf, pm_message_t msg)
{
        return 0;
}

static int driver_resume(struct usb_interface *intf)
{
        return 0;
}

/* The following routines apply to the entire device, not interfaces */
void usbfs_notify_suspend(struct usb_device *udev)
{
        /* We don't need to handle this */
}

void usbfs_notify_resume(struct usb_device *udev)
{
        struct usb_dev_state *ps;

        /* Protect against simultaneous remove or release */
        mutex_lock(&usbfs_mutex);
        list_for_each_entry(ps, &udev->filelist, list) {
                WRITE_ONCE(ps->not_yet_resumed, 0);
                wake_up_all(&ps->wait_for_resume);
        }
        mutex_unlock(&usbfs_mutex);
}

struct usb_driver usbfs_driver = {
        .name =                "usbfs",
        .probe =        driver_probe,
        .disconnect =        driver_disconnect,
        .suspend =        driver_suspend,
        .resume =        driver_resume,
        .supports_autosuspend = 1,
};

static int claimintf(struct usb_dev_state *ps, unsigned int ifnum)
{
        struct usb_device *dev = ps->dev;
        struct usb_interface *intf;
        int err;

        if (ifnum >= 8*sizeof(ps->ifclaimed))
                return -EINVAL;
        /* already claimed */
        if (test_bit(ifnum, &ps->ifclaimed))
                return 0;

        if (ps->privileges_dropped &&
                        !test_bit(ifnum, &ps->interface_allowed_mask))
                return -EACCES;

        intf = usb_ifnum_to_if(dev, ifnum);
        if (!intf)
                err = -ENOENT;
        else {
                unsigned int old_suppress;

                /* suppress uevents while claiming interface */
                old_suppress = dev_get_uevent_suppress(&intf->dev);
                dev_set_uevent_suppress(&intf->dev, 1);
                err = usb_driver_claim_interface(&usbfs_driver, intf, ps);
                dev_set_uevent_suppress(&intf->dev, old_suppress);
        }
        if (err == 0)
                set_bit(ifnum, &ps->ifclaimed);
        return err;
}

static int releaseintf(struct usb_dev_state *ps, unsigned int ifnum)
{
        struct usb_device *dev;
        struct usb_interface *intf;
        int err;

        err = -EINVAL;
        if (ifnum >= 8*sizeof(ps->ifclaimed))
                return err;
        dev = ps->dev;
        intf = usb_ifnum_to_if(dev, ifnum);
        if (!intf)
                err = -ENOENT;
        else if (test_and_clear_bit(ifnum, &ps->ifclaimed)) {
                unsigned int old_suppress;

                /* suppress uevents while releasing interface */
                old_suppress = dev_get_uevent_suppress(&intf->dev);
                dev_set_uevent_suppress(&intf->dev, 1);
                usb_driver_release_interface(&usbfs_driver, intf);
                dev_set_uevent_suppress(&intf->dev, old_suppress);
                err = 0;
        }
        return err;
}

static int checkintf(struct usb_dev_state *ps, unsigned int ifnum)
{
        if (ps->dev->state != USB_STATE_CONFIGURED)
                return -EHOSTUNREACH;
        if (ifnum >= 8*sizeof(ps->ifclaimed))
                return -EINVAL;
        if (test_bit(ifnum, &ps->ifclaimed))
                return 0;
        /* if not yet claimed, claim it for the driver */
        dev_warn(&ps->dev->dev, "usbfs: process %d (%s) did not claim "
                 "interface %u before use\n", task_pid_nr(current),
                 current->comm, ifnum);
        return claimintf(ps, ifnum);
}

static int findintfep(struct usb_device *dev, unsigned int ep)
{
        unsigned int i, j, e;
        struct usb_interface *intf;
        struct usb_host_interface *alts;
        struct usb_endpoint_descriptor *endpt;

        if (ep & ~(USB_DIR_IN|0xf))
                return -EINVAL;
        if (!dev->actconfig)
                return -ESRCH;
        for (i = 0; i < dev->actconfig->desc.bNumInterfaces; i++) {
                intf = dev->actconfig->interface[i];
                for (j = 0; j < intf->num_altsetting; j++) {
                        alts = &intf->altsetting[j];
                        for (e = 0; e < alts->desc.bNumEndpoints; e++) {
                                endpt = &alts->endpoint[e].desc;
                                if (endpt->bEndpointAddress == ep)
                                        return alts->desc.bInterfaceNumber;
                        }
                }
        }
        return -ENOENT;
}

static int check_ctrlrecip(struct usb_dev_state *ps, unsigned int requesttype,
                           unsigned int request, unsigned int index)
{
        int ret = 0;
        struct usb_host_interface *alt_setting;

        if (ps->dev->state != USB_STATE_UNAUTHENTICATED
         && ps->dev->state != USB_STATE_ADDRESS
         && ps->dev->state != USB_STATE_CONFIGURED)
                return -EHOSTUNREACH;
        if (USB_TYPE_VENDOR == (USB_TYPE_MASK & requesttype))
                return 0;

        /*
         * check for the special corner case 'get_device_id' in the printer
         * class specification, which we always want to allow as it is used
         * to query things like ink level, etc.
         */
        if (requesttype == 0xa1 && request == 0) {
                alt_setting = usb_find_alt_setting(ps->dev->actconfig,
                                                   index >> 8, index & 0xff);
                if (alt_setting
                 && alt_setting->desc.bInterfaceClass == USB_CLASS_PRINTER)
                        return 0;
        }

        index &= 0xff;
        switch (requesttype & USB_RECIP_MASK) {
        case USB_RECIP_ENDPOINT:
                if ((index & ~USB_DIR_IN) == 0)
                        return 0;
                ret = findintfep(ps->dev, index);
                if (ret < 0) {
                        /*
                         * Some not fully compliant Win apps seem to get
                         * index wrong and have the endpoint number here
                         * rather than the endpoint address (with the
                         * correct direction). Win does let this through,
                         * so we'll not reject it here but leave it to
                         * the device to not break KVM. But we warn.
                         */
                        ret = findintfep(ps->dev, index ^ 0x80);
                        if (ret >= 0)
                                dev_info(&ps->dev->dev,
                                        "%s: process %i (%s) requesting ep %02x but needs %02x\n",
                                        __func__, task_pid_nr(current),
                                        current->comm, index, index ^ 0x80);
                }
                if (ret >= 0)
                        ret = checkintf(ps, ret);
                break;

        case USB_RECIP_INTERFACE:
                ret = checkintf(ps, index);
                break;
        }
        return ret;
}

static struct usb_host_endpoint *ep_to_host_endpoint(struct usb_device *dev,
                                                     unsigned char ep)
{
        if (ep & USB_ENDPOINT_DIR_MASK)
                return dev->ep_in[ep & USB_ENDPOINT_NUMBER_MASK];
        else
                return dev->ep_out[ep & USB_ENDPOINT_NUMBER_MASK];
}

static int parse_usbdevfs_streams(struct usb_dev_state *ps,
                                  struct usbdevfs_streams __user *streams,
                                  unsigned int *num_streams_ret,
                                  unsigned int *num_eps_ret,
                                  struct usb_host_endpoint ***eps_ret,
                                  struct usb_interface **intf_ret)
{
        unsigned int i, num_streams, num_eps;
        struct usb_host_endpoint **eps;
        struct usb_interface *intf = NULL;
        unsigned char ep;
        int ifnum, ret;

        if (get_user(num_streams, &streams->num_streams) ||
            get_user(num_eps, &streams->num_eps))
                return -EFAULT;

        if (num_eps < 1 || num_eps > USB_MAXENDPOINTS)
                return -EINVAL;

        /* The XHCI controller allows max 2 ^ 16 streams */
        if (num_streams_ret && (num_streams < 2 || num_streams > 65536))
                return -EINVAL;

        eps = kmalloc_array(num_eps, sizeof(*eps), GFP_KERNEL);
        if (!eps)
                return -ENOMEM;

        for (i = 0; i < num_eps; i++) {
                if (get_user(ep, &streams->eps[i])) {
                        ret = -EFAULT;
                        goto error;
                }
                eps[i] = ep_to_host_endpoint(ps->dev, ep);
                if (!eps[i]) {
                        ret = -EINVAL;
                        goto error;
                }

                /* usb_alloc/free_streams operate on an usb_interface */
                ifnum = findintfep(ps->dev, ep);
                if (ifnum < 0) {
                        ret = ifnum;
                        goto error;
                }

                if (i == 0) {
                        ret = checkintf(ps, ifnum);
                        if (ret < 0)
                                goto error;
                        intf = usb_ifnum_to_if(ps->dev, ifnum);
                } else {
                        /* Verify all eps belong to the same interface */
                        if (ifnum != intf->altsetting->desc.bInterfaceNumber) {
                                ret = -EINVAL;
                                goto error;
                        }
                }
        }

        if (num_streams_ret)
                *num_streams_ret = num_streams;
        *num_eps_ret = num_eps;
        *eps_ret = eps;
        *intf_ret = intf;

        return 0;

error:
        kfree(eps);
        return ret;
}

static struct usb_device *usbdev_lookup_by_devt(dev_t devt)
{
        struct device *dev;

        dev = bus_find_device_by_devt(&usb_bus_type, devt);
        if (!dev)
                return NULL;
        return to_usb_device(dev);
}

/*
 * file operations
 */
static int usbdev_open(struct inode *inode, struct file *file)
{
        struct usb_device *dev = NULL;
        struct usb_dev_state *ps;
        int ret;

        ret = -ENOMEM;
        ps = kzalloc(sizeof(struct usb_dev_state), GFP_KERNEL);
        if (!ps)
                goto out_free_ps;

        ret = -ENODEV;

        /* usbdev device-node */
        if (imajor(inode) == USB_DEVICE_MAJOR)
                dev = usbdev_lookup_by_devt(inode->i_rdev);
        if (!dev)
                goto out_free_ps;

        usb_lock_device(dev);
        if (dev->state == USB_STATE_NOTATTACHED)
                goto out_unlock_device;

        ret = usb_autoresume_device(dev);
        if (ret)
                goto out_unlock_device;

        ps->dev = dev;
        ps->file = file;
        ps->interface_allowed_mask = 0xFFFFFFFF; /* 32 bits */
        spin_lock_init(&ps->lock);
        INIT_LIST_HEAD(&ps->list);
        INIT_LIST_HEAD(&ps->async_pending);
        INIT_LIST_HEAD(&ps->async_completed);
        INIT_LIST_HEAD(&ps->memory_list);
        init_waitqueue_head(&ps->wait);
        init_waitqueue_head(&ps->wait_for_resume);
        ps->disc_pid = get_pid(task_pid(current));
        ps->cred = get_current_cred();
        smp_wmb();

        mutex_init(&ps->concurrent_mutex);
        atomic_set(&ps->active_urbs, 0);
        init_waitqueue_head(&ps->wait_queue);
        ps->max_concurrent_urbs = 37;

        /* Can't race with resume; the device is already active */
        list_add_tail(&ps->list, &dev->filelist);
        file->private_data = ps;
        usb_unlock_device(dev);
        snoop(&dev->dev, "opened by process %d: %s\n", task_pid_nr(current),
                        current->comm);
        return ret;

 out_unlock_device:
        usb_unlock_device(dev);
        usb_put_dev(dev);
 out_free_ps:
        kfree(ps);
        return ret;
}

static int usbdev_release(struct inode *inode, struct file *file)
{
        struct usb_dev_state *ps = file->private_data;
        struct usb_device *dev = ps->dev;
        unsigned int ifnum;
        struct async *as;

        usb_lock_device(dev);
        usb_hub_release_all_ports(dev, ps);

        /* Protect against simultaneous resume */
        mutex_lock(&usbfs_mutex);
        list_del_init(&ps->list);
        mutex_unlock(&usbfs_mutex);

        for (ifnum = 0; ps->ifclaimed && ifnum < 8*sizeof(ps->ifclaimed);
                        ifnum++) {
                if (test_bit(ifnum, &ps->ifclaimed))
                        releaseintf(ps, ifnum);
        }
        destroy_all_async(ps);
        
        wait_event(ps->wait_queue, atomic_read(&ps->active_urbs) == 0);
        
        if (!ps->suspend_allowed)
                usb_autosuspend_device(dev);
        usb_unlock_device(dev);
        usb_put_dev(dev);
        put_pid(ps->disc_pid);
        put_cred(ps->cred);

        as = async_getcompleted(ps);
        while (as) {
                free_async(as);
                as = async_getcompleted(ps);
        }

        kfree(ps);
        return 0;
}
