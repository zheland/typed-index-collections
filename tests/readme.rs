trait StrStripPrefix {
    fn strip_prefix(&self, prefix: &Self) -> Option<&Self>;
}

impl StrStripPrefix for str {
    fn strip_prefix<'a, 'b>(&'a self, prefix: &'b Self) -> Option<&'a Self> {
        let prefix_len = prefix.len();
        if self.len() < prefix_len {
            None
        } else if &self.as_bytes()[0..prefix_len] == prefix.as_bytes() {
            Some(&self[prefix_len..])
        } else {
            None
        }
    }
}

#[cfg(all(feature = "impl-index-from", any(feature = "alloc", feature = "std")))]
#[test]
fn test_readme_docs_sync() {
    use std::fs::read_to_string;
    use std::vec::Vec;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum LibRsDocsLine {
        AddedTitle,
        AddedNewlineAfterTitle,
        No(usize),
    }

    let pkg_name = env!("CARGO_PKG_NAME");
    let crate_author = "zheland";
    let pkg_name_underscore = pkg_name.replace("-", "_");
    let doc_root_url = format!("https://docs.rs/{}/*/{}/", pkg_name, pkg_name_underscore);
    let mut is_last_line_used = false;

    // The only transformation to README.md is removing badges and next line after then
    let readme_md = read_to_string("README.md").unwrap();
    let readme_docs = readme_md
        .split('\n')
        .enumerate()
        .filter_map(|(j, line)| {
            is_last_line_used = (is_last_line_used || line != "")
                && !line.starts_with("[![")
                && line != "## Documentation"
                && !line.starts_with("[API Documentation]");
            if is_last_line_used {
                Some((j + 1, line))
            } else {
                None
            }
        }) // Skip badges
        .collect::<Vec<(usize, &str)>>();

    // Library docs index is transformed from src/lib.rs with much transformations
    let lib_rs = read_to_string("src/lib.rs").unwrap();
    let mut is_code_block = false;
    let mut is_cfg_block = false;
    let mut lib_docs = vec![
        (LibRsDocsLine::AddedTitle, format!("# {}", pkg_name)),
        (LibRsDocsLine::AddedNewlineAfterTitle, String::new()),
    ];
    lib_docs.extend(
        lib_rs
            .split('\n')
            .enumerate()
            .filter_map(|(j, line)| {
                StrStripPrefix::strip_prefix(line, "//! ")
                    .or_else(|| StrStripPrefix::strip_prefix(line, "//!"))
                    .or_else(|| {
                        if line == "#![cfg_attr("
                            || line
                                == concat!(
                                    r#"    all(feature = "impl-index-from", "#,
                                    r#"any(feature = "alloc", feature = "std")),"#
                                )
                            || line == r#"    doc = r#""#
                            || line == r##""#"##
                        {
                            is_cfg_block = true;
                            None
                        } else if line == ")]" {
                            is_cfg_block = false;
                            None
                        } else if is_cfg_block {
                            StrStripPrefix::strip_prefix(line, "    ").or(Some(line))
                        } else {
                            None
                        }
                    })
                    .map(|line| (j, line))
            })
            .filter_map(|(j, line)| {
                if line.starts_with("```") {
                    is_code_block = !is_code_block;
                    Some((LibRsDocsLine::No(j + 1), line.to_string()))
                } else if is_code_block {
                    if line.starts_with("# ") {
                        None // Skip hidden code blocks parts
                    } else {
                        Some((LibRsDocsLine::No(j + 1), line.to_string()))
                    }
                } else if line.starts_with("#") {
                    Some((LibRsDocsLine::No(j + 1), "#".to_string() + line)) // Add extra "#" for titles
                } else if line.starts_with("[") && !line.contains("]: http") {
                    // Use full paths for documentation links
                    Some((
                        LibRsDocsLine::No(j + 1),
                        line.replace("]: ", &("]: ".to_string() + &doc_root_url)),
                    ))
                } else {
                    Some((LibRsDocsLine::No(j + 1), line.to_string()))
                }
            })
            .map(|(j, line)| {
                (
                    j,
                    line.replace(
                        &format!(
                            "https://github.com/{}/{}/blob/master/",
                            crate_author, pkg_name
                        ),
                        "",
                    ),
                )
            }),
    );

    for ((lhs_j, lhs), (rhs_j, rhs)) in readme_docs.iter().zip(lib_docs.iter()) {
        assert_eq!(
            lhs, rhs,
            "lib.rs README.md and docs match failed on README.md line {} and lib.rs line \"{:?}\"",
            lhs_j, rhs_j,
        );
    }
}
