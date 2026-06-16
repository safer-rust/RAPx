use std::fs::{File, remove_file};
use std::io::Write;
use std::process::Command;

// please ensure 'graphviz' has been installed
pub fn render_dot_graphs(dot_graphs: Vec<(String, String)>) {
    Command::new("mkdir")
        .args(["SafetyFlow"])
        .output()
        .expect("Failed to create directory");

    for (_index, dot) in dot_graphs.into_iter().enumerate() {
        let file_name = format!("{}.dot", dot.0);
        let mut file = File::create(&file_name).expect("Unable to create file");
        file.write_all(dot.1.as_bytes())
            .expect("Unable to write data");

        Command::new("dot")
            .args([
                "-Tpng",
                &file_name,
                "-o",
                &format!("SafetyFlow/{}.png", dot.0),
            ])
            .output()
            .expect("Failed to execute Graphviz dot command");

        remove_file(&file_name).expect("Failed to delete .dot file");
    }
}

pub fn render_dot_string(name: String, dot_graph: String) {
    Command::new("mkdir")
        .args(["MIR_dot_graph"])
        .output()
        .expect("Failed to create directory");

    let file_name = format!("{}.dot", name);
    rap_debug!("render graph {:?}", file_name);
    let mut file = File::create(&file_name).expect("Unable to create file");
    file.write_all(dot_graph.as_bytes())
        .expect("Unable to write data");

    Command::new("dot")
        .args([
            "-Tpng",
            &file_name,
            "-o",
            &format!("MIR_dot_graph/{}.png", name),
        ])
        .output()
        .expect("Failed to execute Graphviz dot command");

    remove_file(&file_name).expect("Failed to delete .dot file");
}
