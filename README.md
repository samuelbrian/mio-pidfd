# mio-pidfd

A Linux pidfd wrapper for [mio](https://crates.io/crates/mio). This is useful
for using mio to wait for multiple child processes to exit in a non-blocking
event-driven way.

Heavily inspired by [mio-timerfd](https://crates.io/crates/mio-timerfd)

## Example

```rust
use mio_pidfd::PidFd;
use std::process::{Command, Child};
use mio::{Poll, Events, Token, Ready, PollOpt};
let poll = Poll::new().unwrap();
let mut events = Events::with_capacity(1024);
let mut child = Command::new("/bin/sleep").arg("1").spawn().unwrap();
let pidfd = PidFd::new(&child).unwrap();

poll.register(&pidfd, Token(0), Ready::readable(), PollOpt::edge())
             .unwrap();

poll.poll(&mut events, None).unwrap();
assert!(child.try_wait().unwrap().unwrap().code().unwrap() == 0);
```

## Requirements
This library relies on the `pidfd_open()` system call which was introduced
in Linux kernel version 5.3.
The `pidfd_send_signal()` system call (used by supplementary `kill()`
functionality) was introduced in Linux kernel version 5.1
