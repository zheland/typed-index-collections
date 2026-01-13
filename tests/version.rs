#![allow(missing_docs, reason = "okay in tests")]
#![expect(unused_crate_dependencies, reason = "okay in tests")]

#[cfg(all(test, not(miri)))]
#[test]
fn test_readme_deps() {
    if !env!("CARGO_PKG_VERSION").contains("-pre") {
        version_sync::assert_markdown_deps_updated!("README.md");
    }
}

#[cfg(all(test, not(miri)))]
#[test]
fn test_html_root_url() {
    if !env!("CARGO_PKG_VERSION").contains("-pre") {
        version_sync::assert_html_root_url_updated!("src/lib.rs");
    }
}

#[cfg(all(test, not(miri)))]
#[test]
fn test_changelog_mentions_version() {
    if !env!("CARGO_PKG_VERSION").contains("-pre") {
        version_sync::assert_contains_regex!("CHANGELOG.md", "^## \\[{version}\\] - ");
        version_sync::assert_contains_regex!("CHANGELOG.md", "\\[{version}\\]: ");
    }
}
