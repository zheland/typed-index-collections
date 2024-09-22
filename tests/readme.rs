#![allow(missing_docs, reason = "okay in tests")]
#![expect(
    unused_crate_dependencies,
    clippy::unwrap_used,
    reason = "okay in tests"
)]

#[cfg(all(test, not(miri)))]
#[test]
fn test_readme_sync() {
    use readme_sync::{assert_sync, CMarkDocs, CMarkReadme, Config, Package};

    let package = Package::from_path(env!("CARGO_MANIFEST_DIR").into()).unwrap();
    let config = Config::from_package_docs_rs_features(&package);
    let readme = CMarkReadme::from_package(&package).unwrap();
    let docs = CMarkDocs::from_package_and_config(&package, &config).unwrap();

    let readme = readme
        .remove_badges_paragraph()
        .remove_documentation_section()
        .disallow_absolute_repository_blob_links()
        .unwrap()
        .use_absolute_repository_blob_urls()
        .unwrap();

    let docs = docs
        .increment_heading_levels()
        .add_package_title()
        .remove_codeblock_rust_test_tags()
        .use_default_codeblock_rust_tag()
        .remove_hidden_rust_code()
        .disallow_absolute_package_docs_links()
        .unwrap()
        .use_absolute_package_docs_urls()
        .unwrap();

    assert_sync(&readme, &docs);
}
