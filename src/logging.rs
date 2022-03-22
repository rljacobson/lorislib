
pub use verbosity::*;


// Global control over verbose messaging.
pub(crate) mod verbosity {
  use std::{io::{Stdout, stdout, Write}, sync::Mutex};
  use lazy_static::lazy_static;

  // todo: Make `VERBOSITY` an enum. Discriminants must be numerically compatible with Z3.
  // todo: Put `VERBOSITY` behind a mutex to get rid of `unsafe` and make thread safe.
  pub(crate) static mut VERBOSITY     : i32    = 0;
  lazy_static! {
    static ref VERBOSE_STREAM: Mutex<Stdout> = Mutex::new(stdout());
  }

  fn verbosity_is_at_least(lvl: i32) -> bool{
    // Mutable static variables require `unsafe`, as they are not thread safe.
    unsafe{
      VERBOSITY >= lvl
    }
  }

  pub fn set_verbosity(new_value: i32) {
    unsafe {
      VERBOSITY = new_value;
    }
  }

  pub(crate) fn verbose_emit(msg: &str) {
    let mut stream = VERBOSE_STREAM.lock().unwrap();
    // #[allow(unused_must_use)]
    let _ = stream.write(msg.as_bytes());
    let _ = stream.write("\n".as_bytes());
  }

  /// Only emits a message if the verbosity level is at least `level`.
  pub(crate) fn log_at_level(level: i32, msg: &str){
    if verbosity_is_at_least(level){
      verbose_emit(msg);
    }
  }
}
