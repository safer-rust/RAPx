use std::collections::HashMap;
use std::fs::{File, remove_file};
use std::io::Write;
use std::process::Command;

const HTML_TEMPLATE: &str = include_str!("assets/index.html.template");

#[derive(Debug)]
pub struct DotGraph {
    pub name: String,
    pub content: String,
    pub url_map: HashMap<String, String>, // from node label to URL path
}

impl DotGraph {
    pub fn new(name: String, content: String) -> Self {
        Self {
            name,
            content,
            url_map: HashMap::new(),
        }
    }

    pub fn new_with_url_map(
        name: String,
        content: String,
        url_map: HashMap<String, String>,
    ) -> Self {
        Self {
            name,
            content,
            url_map,
        }
    }
}

// please ensure 'graphviz' has been installed
pub fn render_dot_graphs(dot_graphs: &Vec<DotGraph>) {
    Command::new("mkdir")
        .args(["UPG"])
        .output()
        .expect("Failed to create directory");

    for dot_graph in dot_graphs.iter() {
        let file_name = format!("{}.dot", dot_graph.name);
        let mut file = File::create(&file_name).expect("Unable to create file");
        file.write_all(dot_graph.content.as_bytes())
            .expect("Unable to write data");

        Command::new("dot")
            .args([
                "-Tpng",
                &file_name,
                "-o",
                &format!("UPG/{}.png", dot_graph.name),
            ])
            .output()
            .expect("Failed to execute Graphviz dot command");

        remove_file(&file_name).expect("Failed to delete .dot file");
    }
}

pub fn render_dot_graphs_html(dot_graphs: &Vec<DotGraph>) {
    Command::new("mkdir")
        .args(["UPG"])
        .output()
        .expect("Failed to create directory");

    for dot_graph in dot_graphs.iter() {
        let title = &dot_graph.name;
        let dot = &dot_graph.content;
        let url_map = serde_json::to_string_pretty(&dot_graph.url_map).unwrap();
        let html = HTML_TEMPLATE
            .replace("{{TITLE}}", title)
            .replace("{{DOT}}", dot)
            .replace("{{URL_MAP}}", &url_map);

        let file_name = format!("UPG/{}.html", dot_graph.name);
        let mut file = File::create(&file_name).expect("Unable to create file");
        file.write_all(html.as_bytes())
            .expect("Unable to write data");
    }
}

pub fn render_dot_string(dot_graph: &DotGraph) {
    Command::new("mkdir")
        .args(["MIR_dot_graph"])
        .output()
        .expect("Failed to create directory");

    let file_name = format!("{}.dot", dot_graph.name);
    rap_debug!("render graph {:?}", file_name);
    let mut file = File::create(&file_name).expect("Unable to create file");
    file.write_all(dot_graph.content.as_bytes())
        .expect("Unable to write data");

    Command::new("dot")
        .args([
            "-Tpng",
            &file_name,
            "-o",
            &format!("MIR_dot_graph/{}.png", dot_graph.name),
        ])
        .output()
        .expect("Failed to execute Graphviz dot command");

    remove_file(&file_name).expect("Failed to delete .dot file");
}
