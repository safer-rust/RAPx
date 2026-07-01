use chrono::Local;
use fern::colors::{Color, ColoredLevelConfig};
use fern::{self, Dispatch};
use log::LevelFilter;

fn log_level() -> LevelFilter {
    if let Ok(s) = std::env::var("RAPX_LOG") {
        match s.parse() {
            Ok(level) => return level,
            Err(err) => eprintln!("RAPX_LOG is invalid: {err}"),
        }
    }
    LevelFilter::Info
}

/// Detect `RAPX_LOG` environment variable first; if it's not set,
/// default to INFO level.
pub fn init_log() -> Result<(), fern::InitError> {
    let dispatch = Dispatch::new().level(log_level());

    let color_line = ColoredLevelConfig::new()
        .error(Color::Red)
        .warn(Color::Yellow)
        .info(Color::White)
        .debug(Color::Blue)
        .trace(Color::Cyan);

    let color_level = color_line.info(Color::Green);
    let stderr_dispatch = Dispatch::new()
        .format(move |callback, args, record| {
            let now = Local::now();
            callback.finish(format_args!(
                "{}{}|RAPx|{}{}|: {}\x1B[0m",
                format_args!(
                    "\x1B[{}m",
                    color_line.get_color(&record.level()).to_fg_str()
                ),
                now.format("%H:%M:%S"),
                color_level.color(record.level()),
                format_args!(
                    "\x1B[{}m",
                    color_line.get_color(&record.level()).to_fg_str()
                ),
                args
            ))
        })
        .chain(std::io::stderr());

    /* Note that we cannot dispatch to stdout due to some bugs */
    dispatch.chain(stderr_dispatch).apply()?;
    Ok(())
}

#[macro_export]
macro_rules! rap_trace {
    ($($arg:tt)+) => (
        ::log::trace!(target: "RAPx", $($arg)+)
    );
}

#[macro_export]
macro_rules! rap_debug {
    ($($arg:tt)+) => (
        ::log::debug!(target: "RAPx", $($arg)+)
    );
}

#[macro_export]
macro_rules! rap_info {
    (green, $($arg:tt)+) => (
        ::log::info!(target: "RAPx", "\x1B[32m{}\x1B[0m", format_args!($($arg)+))
    );
    (yellow, $($arg:tt)+) => (
        ::log::info!(target: "RAPx", "\x1B[33m{}\x1B[0m", format_args!($($arg)+))
    );
    (red, $($arg:tt)+) => (
        ::log::info!(target: "RAPx", "\x1B[31m{}\x1B[0m", format_args!($($arg)+))
    );
    ($($arg:tt)+) => (
        ::log::info!(target: "RAPx", $($arg)+)
    );
}

#[macro_export]
macro_rules! rap_warn {
    (green, $($arg:tt)+) => (
        ::log::warn!(target: "RAPx", "\x1B[32m{}\x1B[0m", format_args!($($arg)+))
    );
    (yellow, $($arg:tt)+) => (
        ::log::warn!(target: "RAPx", "\x1B[33m{}\x1B[0m", format_args!($($arg)+))
    );
    (red, $($arg:tt)+) => (
        ::log::warn!(target: "RAPx", "\x1B[31m{}\x1B[0m", format_args!($($arg)+))
    );
    ($($arg:tt)+) => (
        ::log::warn!(target: "RAPx", $($arg)+)
    );
}

#[macro_export]
macro_rules! rap_error {
    (green, $($arg:tt)+) => (
        ::log::error!(target: "RAPx", "\x1B[32m{}\x1B[0m", format_args!($($arg)+))
    );
    (yellow, $($arg:tt)+) => (
        ::log::error!(target: "RAPx", "\x1B[33m{}\x1B[0m", format_args!($($arg)+))
    );
    (red, $($arg:tt)+) => (
        ::log::error!(target: "RAPx", "\x1B[31m{}\x1B[0m", format_args!($($arg)+))
    );
    ($($arg:tt)+) => (
        ::log::error!(target: "RAPx", $($arg)+)
    );
}

pub fn rap_error_and_exit(msg: impl AsRef<str>) -> ! {
    rap_error!("{}", msg.as_ref());
    std::process::exit(1)
}

// Re-export span utilities so existing imports from utils::log keep working.
pub use super::span::*;
