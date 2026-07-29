use std::fs::{File, remove_file};
use std::io::Write;
use std::process::Command;

fn render_dot_file(dir_name: &str, name: &str, dot_graph: &str) {
    let _ = Command::new("mkdir")
        .args([dir_name])
        .output();

    let file_name = format!("{}.dot", name);
    let mut file = File::create(&file_name).expect("Unable to create file");
    file.write_all(dot_graph.as_bytes())
        .expect("Unable to write data");

    Command::new("dot")
        .args([
            "-Tpng",
            &file_name,
            "-o",
            &format!("{}/{}.png", dir_name, name),
        ])
        .output()
        .expect("Failed to execute Graphviz dot command");

    remove_file(&file_name).expect("Failed to delete .dot file");
}

pub fn render_dot_graphs(dot_graphs: Vec<(String, String)>) {
    for (_index, dot) in dot_graphs.into_iter().enumerate() {
        render_dot_file("SafetyFlow", &dot.0, &dot.1);
    }
}

pub fn render_dot_string(name: String, dot_graph: String) {
    rap_debug!("render graph {:?}", name);
    render_dot_file("MIR_dot_graph", &name, &dot_graph);
}
