use std::cmp;
use std::sync::atomic::{AtomicUsize, Ordering, ATOMIC_USIZE_INIT};
use std::time::Duration;
use sys::unix::cvt;
use std::sync::Mutex;

use std::os::unix::io::AsRawFd;
use std::os::unix::io::RawFd;

use {io, Ready, PollOpt, Token};
use event_imp::Event;

/// Each Selector has a globally unique(ish) ID associated with it. This ID
/// gets tracked by `TcpStream`, `TcpListener`, etc... when they are first
/// registered with the `Selector`. If a type that is previously associated with
/// a `Selector` attempts to register itself with a different `Selector`, the
/// operation will return with an error. This matches windows behavior.
static NEXT_ID: AtomicUsize = ATOMIC_USIZE_INIT;

pub struct Selector {
    id: usize,
    fds: Mutex<Vec<PollFd>>,
}

impl Selector {
    pub fn new() -> io::Result<Selector> {
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed) + 1;

        Ok(Selector {
            id: id,
            fds: Mutex::new(vec![]),
        })
    }

    /// Wait for events from the OS
    pub fn select(&self, evts: &mut Events, awakener: Token, timeout: Option<Duration>) -> io::Result<bool> {
        let timeout_ms = timeout
            .map(|to| cmp::min(millis(to), i32::MAX as u64) as i32)
            .unwrap_or(-1);

        match self.fds.lock() {
            Ok(poll_fds) => {
                let result = poll(&mut poll_fds, timeout_ms);
                match result {
                    Ok(nfds) => Ok(nfds > 0),
                    Err(err) => Err(err),
                }
            },
            //Err(err) => Err(err),
            // FIXME: KWA: Figure out how to return a io::Error here given this std::sync::PoisonError
            Err(_) => panic!("KWA Unable to acquire lock in Selector::select"),
        }
    }

    pub fn id(&self) -> usize {
        self.id
    }

    pub fn register(&self, fd: RawFd, token: Token, interests: Ready, opts: PollOpt) -> io::Result<()> {
        self.reregister(fd, token, interests, opts)
    }

    pub fn reregister(&self, fd: RawFd, token: Token, interests: Ready, opts: PollOpt) -> io::Result<()> {
        self.deregister(fd);
        match self.fds.lock() {
            Ok(poll_fds) => {
                (*poll_fds).push(PollFd::new(fd, ioevent_to_pollflag(interests, opts)));
                Ok(())
            },
            // FIXME: KWA: Figure out how to return a io::Error here given this std::sync::PoisonError
            Err(_) => panic!("KWA unable to acquire lock in Selector::reregister()"),
        }
    }

    pub fn deregister(&self, fd: RawFd) -> io::Result<()> {
        match self.fds.lock() {
            Ok(poll_fds) => {
                &mut (*poll_fds).retain(|&p| p.pollfd.fd != fd);
                Ok(())
            },
            // FIXME: KWA: Figure out how to return a io::Error here given this std::sync::PoisonError
            Err(_) => panic!("KWA unable to acquire lock in Selector::reregister()"),
        }
    }
}

impl AsRawFd for Selector {
    fn as_raw_fd(&self) -> RawFd {
        self.id as i32
    }
}

impl Drop for Selector {
    fn drop(&mut self) {
    }
}

pub struct Events {
}

impl Events {
    pub fn len(&self) -> usize {
        0
    }

    pub fn with_capacity(u: usize) -> Events {
        Events{}
    }

    pub fn get(&self, idx: usize) -> Option<Event> {
        let kind = Ready::empty();
        let token = 0;
        Some(Event::new(kind, Token(token as usize)))
    }

    pub fn capacity(&self) -> usize {
        0
    }

    pub fn is_empty(&self) -> bool {
        true
    }

    pub fn clear(&mut self) {
    }

    pub fn push_event(&mut self, event: Event) {
    }
}

const NANOS_PER_MILLI: u32 = 1_000_000;
const MILLIS_PER_SEC: u64 = 1_000;

/// Convert a `Duration` to milliseconds, rounding up and saturating at
/// `u64::MAX`.
///
/// The saturating is fine because `u64::MAX` milliseconds are still many
/// million years.
pub fn millis(duration: Duration) -> u64 {
    // Round up.
    let millis = (duration.subsec_nanos() + NANOS_PER_MILLI - 1) / NANOS_PER_MILLI;
    duration.as_secs().saturating_mul(MILLIS_PER_SEC).saturating_add(millis as u64)
}

fn ioevent_to_pollflag(interest: Ready, opts: PollOpt) -> PollFlags {
    // let mut kind = 0;

    // if interest.is_readable() {
    //     kind |= PollFlags::POLLIN;
    // }

    // if interest.is_writable() {
    //     kind |= PollFlags::POLLOUT;
    // }

    // // KWA: FIXME: map other flags
    // kind
    if interest.is_readable() {
        PollFlags::POLLIN
    } else {
        PollFlags::POLLOUT
    }
}

// NOTE: The stuff below is copied from the nix rust library, version 0.18. That
// library should instead be ported to Haiku, but for now I just need the poll()
// implementation.
//
// https://github.com/nix-rust/nix.
/// This is a wrapper around `libc::pollfd`.
///
/// It's meant to be used as an argument to the [`poll`](fn.poll.html) and
/// [`ppoll`](fn.ppoll.html) functions to specify the events of interest
/// for a specific file descriptor.
///
/// After a call to `poll` or `ppoll`, the events that occured can be
/// retrieved by calling [`revents()`](#method.revents) on the `PollFd`.
/// #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct PollFd {
    pollfd: libc::pollfd,
}

impl PollFd {
    /// Creates a new `PollFd` specifying the events of interest
    /// for a given file descriptor.
    pub fn new(fd: RawFd, events: PollFlags) -> PollFd {
        PollFd {
            pollfd: libc::pollfd {
                fd,
                events: events.bits(),
                revents: PollFlags::empty().bits(),
            },
        }
    }

    /// Returns the events that occured in the last call to `poll` or `ppoll`.
    pub fn revents(self) -> Option<PollFlags> {
        PollFlags::from_bits(self.pollfd.revents)
    }
}

/// The `libc_bitflags!` macro helps with a common use case of defining a public bitflags type
/// with values from the libc crate. It is used the same way as the `bitflags!` macro, except
/// that only the name of the flag value has to be given.
///
/// The `libc` crate must be in scope with the name `libc`.
///
/// # Example
/// ```
/// libc_bitflags!{
///     pub struct ProtFlags: libc::c_int {
///         PROT_NONE;
///         PROT_READ;
///         /// PROT_WRITE enables write protect
///         PROT_WRITE;
///         PROT_EXEC;
///         #[cfg(any(target_os = "linux", target_os = "android"))]
///         PROT_GROWSDOWN;
///         #[cfg(any(target_os = "linux", target_os = "android"))]
///         PROT_GROWSUP;
///     }
/// }
/// ```
///
/// Example with casting, due to a mistake in libc. In this example, the
/// various flags have different types, so we cast the broken ones to the right
/// type.
///
/// ```
/// libc_bitflags!{
///     pub struct SaFlags: libc::c_ulong {
///         SA_NOCLDSTOP as libc::c_ulong;
///         SA_NOCLDWAIT;
///         SA_NODEFER as libc::c_ulong;
///         SA_ONSTACK;
///         SA_RESETHAND as libc::c_ulong;
///         SA_RESTART as libc::c_ulong;
///         SA_SIGINFO;
///     }
/// }
/// ```
macro_rules! libc_bitflags {
    (
        $(#[$outer:meta])*
        pub struct $BitFlags:ident: $T:ty {
            $(
                $(#[$inner:ident $($args:tt)*])*
                $Flag:ident $(as $cast:ty)*;
            )+
        }
    ) => {
        ::bitflags::bitflags! {
            $(#[$outer])*
            pub struct $BitFlags: $T {
                $(
                    $(#[$inner $($args)*])*
                    const $Flag = libc::$Flag $(as $cast)*;
                )+
            }
        }
    };
}

libc_bitflags! {
    /// These flags define the different events that can be monitored by `poll` and `ppoll`
    pub struct PollFlags: libc::c_short {
        /// There is data to read.
        POLLIN;
        /// There is some exceptional condition on the file descriptor.
        ///
        /// Possibilities include:
        ///
        /// *  There is out-of-band data on a TCP socket (see
        ///    [tcp(7)](http://man7.org/linux/man-pages/man7/tcp.7.html)).
        /// *  A pseudoterminal master in packet mode has seen a state
        ///    change on the slave (see
        ///    [ioctl_tty(2)](http://man7.org/linux/man-pages/man2/ioctl_tty.2.html)).
        /// *  A cgroup.events file has been modified (see
        ///    [cgroups(7)](http://man7.org/linux/man-pages/man7/cgroups.7.html)).
        POLLPRI;
        /// Writing is now possible, though a write larger that the
        /// available space in a socket or pipe will still block (unless
        /// `O_NONBLOCK` is set).
        POLLOUT;
        /// Equivalent to [`POLLIN`](constant.POLLIN.html)
        #[cfg(not(target_os = "redox"))]
        POLLRDNORM;
        #[cfg(not(target_os = "redox"))]
        /// Equivalent to [`POLLOUT`](constant.POLLOUT.html)
        POLLWRNORM;
        /// Priority band data can be read (generally unused on Linux).
        #[cfg(not(target_os = "redox"))]
        POLLRDBAND;
        /// Priority data may be written.
        #[cfg(not(target_os = "redox"))]
        POLLWRBAND;
        /// Error condition (only returned in
        /// [`PollFd::revents`](struct.PollFd.html#method.revents);
        /// ignored in [`PollFd::new`](struct.PollFd.html#method.new)).
        /// This bit is also set for a file descriptor referring to the
        /// write end of a pipe when the read end has been closed.
        POLLERR;
        /// Hang up (only returned in [`PollFd::revents`](struct.PollFd.html#method.revents);
        /// ignored in [`PollFd::new`](struct.PollFd.html#method.new)).
        /// Note that when reading from a channel such as a pipe or a stream
        /// socket, this event merely indicates that the peer closed its
        /// end of the channel.  Subsequent reads from the channel will
        /// return 0 (end of file) only after all outstanding data in the
        /// channel has been consumed.
        POLLHUP;
        /// Invalid request: `fd` not open (only returned in
        /// [`PollFd::revents`](struct.PollFd.html#method.revents);
        /// ignored in [`PollFd::new`](struct.PollFd.html#method.new)).
        POLLNVAL;
    }
}

/// `poll` waits for one of a set of file descriptors to become ready to perform I/O.
/// ([`poll(2)`](http://pubs.opengroup.org/onlinepubs/9699919799/functions/poll.html))
///
/// `fds` contains all [`PollFd`](struct.PollFd.html) to poll.
/// The function will return as soon as any event occur for any of these `PollFd`s.
///
/// The `timeout` argument specifies the number of milliseconds that `poll()`
/// should block waiting for a file descriptor to become ready.  The call
/// will block until either:
///
/// *  a file descriptor becomes ready;
/// *  the call is interrupted by a signal handler; or
/// *  the timeout expires.
///
/// Note that the timeout interval will be rounded up to the system clock
/// granularity, and kernel scheduling delays mean that the blocking
/// interval may overrun by a small amount.  Specifying a negative value
/// in timeout means an infinite timeout.  Specifying a timeout of zero
/// causes `poll()` to return immediately, even if no file descriptors are
/// ready.
pub fn poll(fds: &mut Vec<PollFd>, timeout: libc::c_int) -> io::Result<libc::c_int> {
    let res = unsafe {
        libc::poll(fds.as_mut_ptr() as *mut libc::pollfd,
                   fds.len() as libc::nfds_t,
                   timeout)
    };

    cvt(res)
}
