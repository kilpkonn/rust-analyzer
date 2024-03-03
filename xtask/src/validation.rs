use regex::Regex;
use serde::{Deserialize, Serialize};
use xshell::{cmd, Shell};

use crate::flags;

impl flags::Validation {
    pub(crate) fn run(self, sh: &Shell) -> anyhow::Result<()> {
        cmd!(sh, "cargo build --release --package rust-analyzer --bin rust-analyzer").run()?;

        let categories: Vec<Category> = fetch_categories()
            .categories
            .into_iter()
            .filter(|it| it.crates_count > 1000)
            // .take(1)
            .collect();

        for depth in 0..=10 {
            let filename = format!("results_{depth}.csv");
            std::fs::remove_file(&filename).ok();
            let mut wtr = csv::Writer::from_writer(std::fs::File::create(&filename).unwrap());
            categories
                .iter()
                .flat_map(|category| {
                    fetch_top_crates(&category, 5).into_iter().flat_map(move |krate| {
                        let dirname = download_crate(
                            sh,
                            &category.id,
                            &krate.name,
                            &krate.version.clone().unwrap_or(krate.newest_version.clone()),
                        );

                        run_on_crate(sh, &dirname, &category, &krate, depth)
                    })
                })
                .for_each(|line| {
                    wtr.serialize(line).unwrap();
                    wtr.flush().unwrap();
                });
        }

        Ok(())
    }
}

fn get(url: &str) -> reqwest::Result<reqwest::blocking::Response> {
    println!("Getting: {url}");
    reqwest::blocking::ClientBuilder::new()
        .user_agent("Rust Corpus - Top Crates Scrapper")
        .build()?
        .get(url)
        .send()
}

#[derive(Debug, Deserialize)]
struct Crate {
    #[serde(rename = "id")]
    name: String,
    #[serde(rename = "max_stable_version")]
    version: Option<String>,
    #[serde(rename = "newest_version")]
    newest_version: String,
}

#[derive(Debug, Deserialize)]
struct CratesList {
    crates: Vec<Crate>,
}

#[allow(dead_code)]
fn load_to_crates(category: &Category, count: usize) -> Option<Vec<Crate>> {
    let cat_name = &category.id;
    let dirname = format!("{FILES_PATH}/{cat_name}");

    let categories: Vec<_> = std::fs::read_dir(dirname)
        .ok()?
        .filter_map(|it| it.ok())
        .filter(|it| it.file_type().map(|ty| ty.is_dir()).unwrap_or(false))
        .map(|it| {
            let filename = it.file_name().into_string().unwrap();
            let mut split = filename.split("-");

            Crate {
                name: split.next().unwrap().to_string(),
                version: None,
                newest_version: split.next().unwrap().to_string(),
            }
        })
        .collect();

    if categories.len() != count {
        return None;
    }
    Some(categories)
}

fn fetch_top_crates(category: &Category, count: usize) -> Vec<Crate> {
    let url = format!(
        "https://crates.io/api/v1/crates?category={}&page=1&per_page={}&sort=downloads",
        category.id, count
    );
    let resp = get(&url).unwrap();
    let crates: CratesList = serde_json::from_reader(resp).unwrap();

    crates.crates
}

#[derive(Debug, Deserialize)]
struct Category {
    #[serde(rename = "id")]
    id: String,
    #[serde(rename = "crates_cnt")]
    crates_count: u64,
}

#[derive(Debug, Deserialize)]
struct CategoriesList {
    categories: Vec<Category>,
}

fn fetch_categories() -> CategoriesList {
    let url = "	https://crates.io/api/v1/categories?page=1&per_page=100&sort=crates";
    let resp = get(&url).unwrap();
    let resp: CategoriesList = serde_json::from_reader(resp).unwrap();
    resp
}

#[allow(dead_code)]
fn load_categories() -> Option<Vec<Category>> {
    let categories = std::fs::read_dir(FILES_PATH)
        .ok()?
        .filter_map(|it| it.ok())
        .filter(|it| it.file_type().map(|ty| ty.is_dir()).unwrap_or(false))
        .map(|it| Category { id: it.file_name().into_string().unwrap(), crates_count: 0 })
        .collect();
    Some(categories)
}

const FILES_PATH: &str = "/home/tavo/Downloads/ra-tests";

fn download_crate(sh: &Shell, category: &str, name: &str, version: &str) -> String {
    let dirname = format!("{FILES_PATH}/{category}");
    let filename = format!("{dirname}/{name}-{version}.crate");
    if !std::path::PathBuf::from(&filename).exists() {
        let dl = format!("https://crates.io/api/v1/crates/{}/{}/download", name, version);
        let mut resp = get(&dl).expect("Could not fetch top crates");
        std::fs::create_dir_all(&dirname).unwrap();
        let mut file = std::fs::File::create(&filename).unwrap();
        resp.copy_to(&mut file).unwrap();
    }
    extract_crate(sh, &dirname, &filename)
}

fn extract_crate(sh: &Shell, dirname: &str, filename: &str) -> String {
    cmd!(sh, "tar -xf {filename} -C {dirname}").run().unwrap();
    filename.strip_suffix(".crate").unwrap().to_string()
}

#[derive(Debug, Serialize)]
struct SynthesisResult {
    category: String,
    krate: String,
    syntax_hits: u64,
    found: u64,
    suggestions_per_expr: f64,
    avg_time_ms: u64,
    total: u64,
    depth: usize,
}

fn run_on_crate(
    sh: &Shell,
    dirname: &str,
    category: &Category,
    krate: &Crate,
    depth: usize,
) -> anyhow::Result<SynthesisResult> {
    let depth_str = depth.to_string();
    let output = cmd!(
        sh,
        "./target/release/rust-analyzer analysis-stats {dirname}/Cargo.toml --run-term-search --skip-lowering --term-search-depth {depth_str}"
    )
    .read()?;

    let re_syntax_hits = Regex::new(r"Tail Expr syntactic hits: (\d+)/(\d+)").unwrap();
    let re_found = Regex::new(r"Tail Exprs found: (\d+)/(\d+)").unwrap();
    let re_terms_per_expr = Regex::new(r"Avg exprs per term: (\d+\.\d?)").unwrap();
    let re_avg_time = Regex::new(r"Term search avg time: (\d+)ms").unwrap();

    let syntax_caps = re_syntax_hits.captures(&output).unwrap();
    let found_caps = re_found.captures(&output).unwrap();
    let terms_per_expr_caps = re_terms_per_expr.captures(&output).unwrap();
    let time_caps = re_avg_time.captures(&output).unwrap();

    Ok(SynthesisResult {
        syntax_hits: syntax_caps.get(1).unwrap().as_str().parse().unwrap(),
        found: found_caps.get(1).unwrap().as_str().parse().unwrap(),
        suggestions_per_expr: terms_per_expr_caps.get(1).unwrap().as_str().parse().unwrap(),
        avg_time_ms: time_caps.get(1).unwrap().as_str().parse().unwrap(),
        total: syntax_caps.get(2).unwrap().as_str().parse().unwrap(),
        depth,
        category: category.id.clone(),
        krate: format!(
            "{}-{}",
            krate.name,
            krate.version.clone().unwrap_or(krate.newest_version.clone())
        ),
    })
}
