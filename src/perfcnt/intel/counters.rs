//! Performance counter for all Intel architectures.
/// The content of this file is automatically generated by `build.rs`
/// from the data in `x86data/perfmon_data`.

use phf;
use super::description::IntelPerformanceCounterDescription;
use super::description::Counter;
use super::description::PebsType;
use super::description::Tuple;
use super::description::MSRIndex;

include!(concat!(env!("OUT_DIR"), "/counters.rs"));
