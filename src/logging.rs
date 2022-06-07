/*!

# Logging

There are two orthogonal concepts in the logging infrastructure: a `Channel`, which describes
what _kind_ of messages are to be logged, and a verbosity level (verbosity, level, or log
level), which describes the _verbosity_ of logger.

## Verbosity Levels

Verbosity is a numerical value, with higher values meaning more verbose logging. A verbosity
level is a property of a logger and describes how chatty that logger is.


## Channels

`Channel` takes one of the values:  Critical, Error, Warning, Notice, Info, Debug.

I want to be a lumberjack.

*/

use strum::{
  Display,
  IntoStaticStr
};

use yansi::Paint;


pub type LogLevel = i32;

#[derive(Hash, Display, Eq, PartialEq, Clone, Copy, IntoStaticStr)]
pub enum Channel {
  Critical,
  Error,
  Warning,
  Notice,
  Info,
  Debug,
}

pub struct LogEntry<'s> {
  pub channel: Channel,
  pub log_level: LogLevel,
  pub message: &'s str,
}

pub fn log(channel: Channel, log_level: LogLevel, message: &str) {
  let entry = LogEntry {
    channel,
    log_level,
    message
  };
  log_entry(entry);
}

pub fn log_entry(entry: LogEntry) {
  let prefix = match entry.channel {
    Channel::Critical => Paint::red("Critical"),
    Channel::Error => Paint::red("Error"),
    Channel::Warning => Paint::yellow("Warning"),
    Channel::Notice => Paint::blue("Notice"),
    Channel::Info => Paint::green("Info"),
    Channel::Debug => Paint::white("Debug"),
  };

  log_at_level(entry.log_level, format!("{}: {}", prefix, entry.message)
      .as_str());
}

use verbosity::*;
pub use verbosity::set_verbosity;

// Global control over verbose messaging.
pub(crate) mod verbosity {
  use std::{
    io::{
      Stdout,
      stdout,
      Write
    },
    sync::Mutex
  };
  use lazy_static::lazy_static;
  use yansi::Paint;

  // todo: Put `VERBOSITY` behind a mutex to get rid of `unsafe` and make thread safe.
  pub(crate) static mut VERBOSITY: i32    = 0;
  lazy_static! {
    static ref LOGGING_STREAM: Mutex<Stdout> = Mutex::new(stdout());
  }

  fn verbosity_is_at_least(lvl: i32) -> bool{
    // Mutable static variables require `unsafe`, as they are not thread safe.
    unsafe{
      VERBOSITY >= lvl
    }
  }

  pub fn set_verbosity(new_value: i32) {
    // This function is the closest thing to a setup function we have.
    if cfg!(windows) && !Paint::enable_windows_ascii() {
      Paint::disable();
    }

    unsafe {
      VERBOSITY = new_value;
    }
  }

  pub(crate) fn emit_log(msg: &str) {
    let mut stream = LOGGING_STREAM.lock().unwrap();
    // #[allow(unused_must_use)]
    let _ = stream.write(msg.as_bytes());
    let _ = stream.write("\n".as_bytes());
  }

  /// Only emits a message if the verbosity level is at least `level`.
  pub(crate) fn log_at_level(level: i32, msg: &str){
    if verbosity_is_at_least(level){
      emit_log(msg);
    }
  }
}
