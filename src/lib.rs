//! # mio-pidfd
//!
//! # mio-pidfd
//!
//! A Linux pidfd wrapper for [mio](https://crates.io/crates/mio). This is useful
//! for using mio to wait for multiple child processes to exit in a non-blocking
//! event-driven way.
//!
//! Heavily inspired by [mio-timerfd](https://crates.io/crates/mio-timerfd)
//!
//! ## Example
//!
//! ```rust
//! use mio_pidfd::PidFd;
//! use mio::{Poll, Events, Token, Ready, PollOpt};
//! use std::process::{Command, Child};
//!
//! let poll = Poll::new().unwrap();
//! let mut events = Events::with_capacity(1024);
//! let mut child = Command::new("/bin/sleep").arg("1").spawn().unwrap();
//! let pidfd = PidFd::new(&child).unwrap();
//!
//! poll.register(&pidfd, Token(0), Ready::readable(), PollOpt::edge())
//!              .unwrap();
//!
//! poll.poll(&mut events, None).unwrap();
//! assert!(child.try_wait().unwrap().unwrap().code().unwrap() == 0);
//! ```
//!
//! ## Requirements
//! This library relies on the `pidfd_open()` system call which was introduced
//! in Linux kernel version 5.3.
//! The `pidfd_send_signal()` system call (used by supplementary `kill()`
//! functionality) was introduced in Linux kernel version 5.1

use libc::{c_int, c_uint, pid_t, siginfo_t};
use mio::unix::EventedFd;
use mio::{Evented, Poll, PollOpt, Ready, Token};
use std::convert::TryInto;
use std::io;
use std::os::unix::io::{AsRawFd, RawFd};
use std::process::Child;

#[cfg(not(target_os = "linux"))]
compile_error!("pidfd is a linux specific feature");

const NR_PIDFD_OPEN: c_int = 434;
const NR_PIDFD_SEND_SIGNAL: c_int = 424;

extern "C" {
    fn syscall(num: c_int, ...) -> c_int;
}

/// `pidfd_create` syscall function.
/// Perform the system call directly since no libc supports this at time of
/// writing. Import from libc crate when it is supported there.
/// --------------------------------------------------
/// pidfd_create() - Create a new pid file descriptor.
/// @pid:  struct pid that the pidfd will reference
///
/// This creates a new pid file descriptor with the O_CLOEXEC flag set.
///
/// Note, that this function can only be called after the fd table has
/// been unshared to avoid leaking the pidfd to the new process.
///
/// Return: On success, a cloexec pidfd is returned.
///         On error, a negative errno number will be returned.
unsafe fn pidfd_create(pid: pid_t, flags: c_uint) -> c_int {
    syscall(NR_PIDFD_OPEN, pid, flags)
}

/// `pidfd_send_signal` syscall function.
/// Perform the system call directly since no libc supports this at time of
/// writing. Import from libc crate when it is supported there.
/// --------------------------------------------------
/// sys_pidfd_send_signal - Signal a process through a pidfd
/// @pidfd:  file descriptor of the process
/// @sig:    signal to send
/// @info:   signal info
/// @flags:  future flags
///
/// The syscall currently only signals via PIDTYPE_PID which covers
/// kill(<positive-pid>, <signal>. It does not signal threads or process
/// groups.
/// In order to extend the syscall to threads and process groups the @flags
/// argument should be used. In essence, the @flags argument will determine
/// what is signaled and not the file descriptor itself. Put in other words,
/// grouping is a property of the flags argument not a property of the file
/// descriptor.
///
/// Return: 0 on success, negative errno on failure
///
unsafe fn pidfd_send_signal(
    pidfd: c_int,
    sig: c_int,
    info: *const siginfo_t,
    flags: c_uint,
) -> c_int {
    syscall(NR_PIDFD_SEND_SIGNAL, pidfd, sig, info, flags)
}

//
//
// PidFd
//
//

/// A Linux pidfd abstraction that can be used to poll the exit status of
/// multiple child processes using mio.
pub struct PidFd {
    fd: c_int,
}

impl PidFd {
    /// Create a new pidfd from a child process.
    /// This may be registerd with a mio poll.
    pub fn new(child: &Child) -> io::Result<Self> {
        let flags = 0;
        let pid: pid_t = match child.id().try_into() {
            Ok(pid) => pid,
            Err(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "child process id outside range of pid_t",
                ))
            }
        };
        Self::open(pid, flags)
    }

    /// Send a signal to the process using the pidfd.
    /// Use `std::process::Child::kill()` over this. This `kill()` is here
    /// only for the completeness of the pidfd system calls abstraction.
    pub fn kill(&self, sig: c_int) -> io::Result<()> {
        self.send_signal(sig, std::ptr::null(), 0)
    }

    /// Wrapper to `pidfd_open` system call.
    /// Use instead of `new()` when extra parameters are desired.
    pub fn open(pid: pid_t, flags: c_uint) -> io::Result<Self> {
        let fd = unsafe { pidfd_create(pid, flags) };
        if fd == -1 {
            Err(io::Error::last_os_error())
        } else {
            Ok(Self { fd })
        }
    }

    /// Wrapper to `pidfd_send_signal` system call.
    /// Use instead of `kill()` when extra parameters are desired.
    pub fn send_signal(&self, sig: c_int, info: *const siginfo_t, flags: c_uint) -> io::Result<()> {
        let ret = unsafe { pidfd_send_signal(self.fd, sig, info, flags) };
        if ret == -1 {
            Err(io::Error::last_os_error())
        } else {
            Ok(())
        }
    }
}

impl AsRawFd for PidFd {
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl Evented for PidFd {
    fn register(
        &self,
        poll: &Poll,
        token: Token,
        interest: Ready,
        opts: PollOpt,
    ) -> io::Result<()> {
        EventedFd(&self.fd).register(poll, token, interest, opts)
    }

    fn reregister(
        &self,
        poll: &Poll,
        token: Token,
        interest: Ready,
        opts: PollOpt,
    ) -> io::Result<()> {
        EventedFd(&self.fd).reregister(poll, token, interest, opts)
    }

    fn deregister(&self, poll: &Poll) -> io::Result<()> {
        EventedFd(&self.fd).deregister(poll)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mio::Events;
    use std::os::unix::process::ExitStatusExt;
    use std::process::Command;
    use std::time::Duration;

    const TOK1: Token = Token(1);
    const TOK2: Token = Token(2);
    const TIMEOUT1: Duration = Duration::from_secs(1);
    const TIMEOUT2: Duration = Duration::from_secs(2);

    #[test]
    fn pidfd_new_and_kill() {
        let sig = libc::SIGABRT;
        let mut child = Command::new("/bin/sleep").arg("5").spawn().unwrap();

        let fd = PidFd::new(&child).unwrap();
        fd.kill(sig).unwrap();
        assert!(child.wait().unwrap().signal().unwrap() == sig);
    }

    #[test]
    #[should_panic]
    fn pidfd_open_invalid_pid() {
        PidFd::open(-1, 0).unwrap();
    }

    #[test]
    #[should_panic]
    fn pidfd_kill_invalid_signal() {
        let sig = -1;
        let child = Command::new("/bin/sleep").arg("0").spawn().unwrap();

        let fd = PidFd::new(&child).unwrap();
        fd.kill(sig).unwrap();
    }

    fn create_sleeper(poll: &Poll, timeout: Duration, token: Token) -> Child {
        let child = Command::new("/bin/sleep")
            .arg(format!("{}", timeout.as_secs()))
            .spawn()
            .unwrap();
        let pidfd = PidFd::new(&child).unwrap();

        poll.register(&pidfd, token, Ready::readable(), PollOpt::edge())
            .unwrap();

        return child;
    }

    #[test]
    fn single_process() {
        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);
        let mut child = create_sleeper(&poll, TIMEOUT2, TOK2);

        // child should not exit before the timeout
        poll.poll(&mut events, Some(TIMEOUT2 / 2)).unwrap();
        assert!(events.is_empty());
        match child.try_wait() {
            Ok(None) => {}
            Ok(Some(status)) => {
                panic!("child exited without poll event: {}", status);
            }
            Err(e) => panic!("child error without poll event: {}", e),
        }

        // child should exit with an event
        poll.poll(&mut events, Some(TIMEOUT2)).unwrap();
        assert!(!events.is_empty());
        match child.try_wait() {
            Ok(Some(_)) => {}
            Ok(None) => panic!("poll event occured but child has not exited"),
            Err(e) => panic!("child error without poll event: {}", e),
        }

        // child should not cause event again after exit
        poll.poll(&mut events, Some(Duration::from_nanos(1)))
            .unwrap();
        assert!(events.is_empty());
    }

    #[test]
    fn multi_process() {
        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);
        let mut child1 = create_sleeper(&poll, TIMEOUT1, TOK1);
        let mut child2 = create_sleeper(&poll, TIMEOUT2, TOK2);

        // neither child should exit before the timeout
        poll.poll(&mut events, Some(TIMEOUT1 / 2)).unwrap();
        assert!(events.is_empty());
        match child1.try_wait() {
            Ok(None) => {}
            Ok(Some(status)) => panic!("child1 exited without poll event: {}", status),
            Err(e) => panic!("child1 error without poll event: {}", e),
        }
        match child2.try_wait() {
            Ok(None) => {}
            Ok(Some(status)) => panic!("child2 exited without poll event: {}", status),
            Err(e) => panic!("child2 error without poll event: {}", e),
        }

        // child1 should exit with an event
        poll.poll(&mut events, Some(TIMEOUT1)).unwrap();
        assert!(!events.is_empty());
        for event in events.iter() {
            assert!(event.token() == TOK1);
        }
        match child1.try_wait() {
            Ok(Some(_)) => {}
            Ok(None) => panic!("poll event occured but child1 has not exited"),
            Err(e) => panic!("child1 error without poll event: {}", e),
        }

        // child2 should exit with an event
        poll.poll(&mut events, Some(TIMEOUT2)).unwrap();
        assert!(!events.is_empty());
        for event in events.iter() {
            assert!(event.token() == TOK2);
        }
        match child2.try_wait() {
            Ok(Some(_)) => {}
            Ok(None) => panic!("poll event occured but child2 has not exited"),
            Err(e) => panic!("child2 error without poll event: {}", e),
        }

        // child should not cause event again after exit
        poll.poll(&mut events, Some(Duration::from_nanos(1)))
            .unwrap();
        assert!(events.is_empty());
    }
}
