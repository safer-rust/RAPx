use crate::rap_warn;
use chrono::Local;
use fern::colors::{Color, ColoredLevelConfig};
use fern::{self, Dispatch};
use log::LevelFilter;

fn parse_rapx_log() -> (LevelFilter, Vec<(String, LevelFilter)>) {
    let mut global_level = LevelFilter::Info;
    let mut module_levels = Vec::new();
    let crate_name = env!("CARGO_PKG_NAME");

    let Ok(raw) = std::env::var("RAPX_LOG") else {
        return (global_level, module_levels);
    };

    for item in raw.split(',') {
        let item = item.trim();
        if item.is_empty() {
            continue;
        }

        // `module:LEVEL`
        if let Some((module, level)) = item.rsplit_once(':') {
            let module = module.trim();
            let level = level.trim();
            if module.is_empty() {
                rap_warn!("RAPX_LOG module is empty in entry: {item}");
                continue;
            }
            match level.parse() {
                Ok(parsed) => module_levels.push((format!("{}::{}", crate_name, module), parsed)),
                Err(err) => rap_warn!("RAPX_LOG entry is invalid: {item} ({err})"),
            }
            continue;
        }

        match item.parse() {
            Ok(parsed) => global_level = parsed,
            Err(err) => rap_warn!("RAPX_LOG entry is invalid: {item} ({err})"),
        }
    }

    (global_level, module_levels)
}

/// Detect `RAPX_LOG` environment variable first; if it's not set,
/// default to INFO level.
///
/// Supported forms:
/// - `RAPX_LOG=TRACE` -> global level
/// - `RAPX_LOG=some::module:DEBUG` -> module level
/// - `RAPX_LOG=TRACE,some::module:INFO,other::module:DEBUG` -> mixed
pub fn init_log() -> Result<(), fern::InitError> {
    let (global_level, module_levels) = parse_rapx_log();
    let mut dispatch = Dispatch::new().level(global_level);
    for (module, level) in module_levels {
        dispatch = dispatch.level_for(module, level);
    }

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
        ::log::trace!($($arg)+)
    );
}

#[macro_export]
macro_rules! rap_debug {
    ($($arg:tt)+) => (
        ::log::debug!($($arg)+)
    );
}

#[macro_export]
macro_rules! rap_info {
    (green, $($arg:tt)+) => (
        ::log::info!("\x1B[32m{}\x1B[0m", format_args!($($arg)+))
    );
    (yellow, $($arg:tt)+) => (
        ::log::info!("\x1B[33m{}\x1B[0m", format_args!($($arg)+))
    );
    (red, $($arg:tt)+) => (
        ::log::info!("\x1B[31m{}\x1B[0m", format_args!($($arg)+))
    );
    ($($arg:tt)+) => (
        ::log::info!($($arg)+)
    );
}

#[macro_export]
macro_rules! rap_warn {
    (green, $($arg:tt)+) => (
        ::log::warn!("\x1B[32m{}\x1B[0m", format_args!($($arg)+))
    );
    (yellow, $($arg:tt)+) => (
        ::log::warn!("\x1B[33m{}\x1B[0m", format_args!($($arg)+))
    );
    (red, $($arg:tt)+) => (
        ::log::warn!("\x1B[31m{}\x1B[0m", format_args!($($arg)+))
    );
    ($($arg:tt)+) => (
        ::log::warn!($($arg)+)
    );
}

#[macro_export]
macro_rules! rap_error {
    (green, $($arg:tt)+) => (
        ::log::error!("\x1B[32m{}\x1B[0m", format_args!($($arg)+))
    );
    (yellow, $($arg:tt)+) => (
        ::log::error!("\x1B[33m{}\x1B[0m", format_args!($($arg)+))
    );
    (red, $($arg:tt)+) => (
        ::log::error!("\x1B[31m{}\x1B[0m", format_args!($($arg)+))
    );
    ($($arg:tt)+) => (
        ::log::error!($($arg)+)
    );
}

pub fn rap_error_and_exit(msg: impl AsRef<str>) -> ! {
    rap_error!("{}", msg.as_ref());
    std::process::exit(1)
}
