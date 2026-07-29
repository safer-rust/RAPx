use rustc_span::def_id::DefId;

use crate::utils::source::get_fn_name_byid;

pub fn should_check(def_id: DefId) -> bool {
    let fn_name = get_fn_name_byid(&def_id);
    let last_segment = fn_name.rsplit("::").next().unwrap_or(&fn_name);
    if last_segment.contains("drop")
        || last_segment.contains("dealloc")
        || last_segment.contains("release")
        || last_segment.contains("destroy")
    {
        return false;
    }
    true
}
