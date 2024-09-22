#[cfg(all(test, not(miri)))]
#[test]
fn test_readme_deps() {
    version_sync::assert_markdown_deps_updated!("README.md");
}

#[cfg(all(test, not(miri)))]
#[test]
fn test_html_root_url() {
    version_sync::assert_html_root_url_updated!("src/lib.rs");
}

#[cfg(all(test, not(miri)))]
#[test]
fn test_changelog_mentions_version() {
    version_sync::assert_contains_regex!("CHANGELOG.md", "^## \\[{version}\\] - ");
    version_sync::assert_contains_regex!("CHANGELOG.md", "\\[{version}\\]: ");
}
