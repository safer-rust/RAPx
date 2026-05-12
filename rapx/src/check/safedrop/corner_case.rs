use rustc_span::def_id::DefId;

pub fn should_check(def_id: DefId) -> bool {
    let mut def_str = format!("{:?}", def_id);
    if let Some(x) = def_str.rfind("::") {
        def_str = def_str.get((x + "::".len())..).unwrap().to_string();
    }
    if let Some(_) = def_str.find("drop") {
        return false;
    }
    if let Some(_) = def_str.find("dealloc") {
        return false;
    }
    if let Some(_) = def_str.find("release") {
        return false;
    }
    if let Some(_) = def_str.find("destroy") {
        return false;
    }
    return true;
}
