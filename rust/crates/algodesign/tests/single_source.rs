// SPDX-License-Identifier: Apache-2.0
//! Numbers that must be written once, and speed choices no answer shows. The `occ` block width is
//! [`DEFAULT_BLOCK`] and the sampling rate is `SAMPLE`, each declared in one place and imported
//! everywhere else, so two copies cannot drift apart. Structure, not behaviour, so a test of
//! answers cannot see it; these tests read the source instead.

use std::path::Path;

use algodesign::strings::count_index::{ByteIndex, DEFAULT_BLOCK};
use algodesign::strings::fm_index::SAMPLE;

/// The code of one line: everything before a `//` comment.
fn code(line: &str) -> &str {
    line.split("//").next().unwrap_or("")
}

/// Whether `word` occurs in `text` as a whole token, not inside a longer name or number.
fn has_token(text: &str, word: &str) -> bool {
    let is_part = |c: char| c.is_ascii_alphanumeric() || c == '_';
    text.match_indices(word).any(|(i, _)| {
        let before = text[..i].chars().next_back();
        let after = text[i + word.len()..].chars().next();
        !before.is_some_and(is_part) && !after.is_some_and(is_part)
    })
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

#[test]
fn the_block_width_is_written_once_in_the_library() {
    assert_eq!(DEFAULT_BLOCK, 512);
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/strings");
    let mut uses = Vec::new();
    for entry in std::fs::read_dir(&src).expect("src/strings/") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|e| e == "rs") {
            for line in read(&path).lines() {
                if has_token(code(line), "512") {
                    let file = path.file_name().expect("a file").to_string_lossy();
                    uses.push(format!("{file}: {}", line.trim()));
                }
            }
        }
    }
    assert_eq!(
        uses,
        ["count_index.rs: pub const DEFAULT_BLOCK: usize = 512;"],
        "a block width written as a literal outside DEFAULT_BLOCK"
    );
}

#[test]
fn the_benchmark_imports_the_library_s_sampling_rate() {
    assert_eq!(SAMPLE, 32);
    let bench = read(&Path::new(env!("CARGO_MANIFEST_DIR")).join("benches/strings.rs"));
    for name in ["SAMPLE", "DEFAULT_BLOCK"] {
        let declared = bench
            .lines()
            .map(code)
            .any(|l| l.contains("const ") && has_token(l.split(':').next().unwrap_or(""), name));
        assert!(!declared, "benches/strings.rs declares its own {name}");
    }
    assert!(bench.contains("use algodesign::strings::fm_index::SAMPLE;"));
}

/// The code lines of the item that opens with `header` in `file` (under `src/strings/`), up to the
/// closing brace at column 0. Panics if the item is missing, so a rename fails loudly.
fn item(file: &str, header: &str) -> Vec<String> {
    let src = read(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/strings")
            .join(file),
    );
    let start = src
        .find(header)
        .unwrap_or_else(|| panic!("{file}: no `{header}`"));
    src[start..]
        .lines()
        .take_while(|l| *l != "}")
        .map(|l| code(l).to_string())
        .collect()
}

/// `DEFAULT_BLOCK` is declared once, and `ByteIndex` defaults to that one: a second declaration
/// elsewhere -- `1 << 9`, say -- would pass the literal-`512` check above and keep every answer,
/// while two defaults were free to drift apart again. The function below does not compile unless
/// the default *is* `DEFAULT_BLOCK`'s value.
#[test]
fn the_block_width_is_declared_once() {
    fn byte_index(x: ByteIndex) -> ByteIndex<DEFAULT_BLOCK> {
        x
    }
    let _ = byte_index;
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/strings");
    let mut declared = Vec::new();
    for entry in std::fs::read_dir(&src).expect("src/strings/") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|e| e == "rs") {
            for line in read(&path).lines() {
                if code(line).contains("const DEFAULT_BLOCK") {
                    declared.push(line.trim().to_string());
                }
            }
        }
    }
    assert_eq!(declared, ["pub const DEFAULT_BLOCK: usize = 512;"]);
}

/// The `occ` tail is tallied by a fold into a `u8`, 255 bytes at a time: the narrow accumulator
/// is what vectorises 16 lanes wide. `count_index`'s test pins the `u8` in
/// `tally`'s signature; a body that counted in a `usize` and cast the result would keep the
/// signature and every answer, and lose the speed.
#[test]
fn the_tail_tally_folds_into_a_u8() {
    let body = item("count_index.rs", "fn tally(");
    let text = body.join("\n");
    assert!(text.contains(".fold(0u8,"), "{text}");
    for bad in ["count(", " as ", "sum("] {
        assert!(
            !text.contains(bad),
            "tally counts wider than a u8 ({bad}): {text}"
        );
    }
}

/// One counting sort per suffix array, in round 0, and no other sort anywhere in the loop's
/// function (`doubling`, which `suffix_array` calls):
/// every doubling round reads the second-component order off `sa`. The
/// `SORTS` counter in `suffix_array`'s tests sees a second `counting_sort_by`; this sees any
/// other sort -- `sort_by_key` on the laid-out positions builds the same array too.
#[test]
fn the_doubling_rounds_sort_nothing() {
    let body = item("suffix_array.rs", "fn doubling(");
    let sorts: Vec<usize> = (0..body.len())
        .filter(|&i| body[i].contains("sort"))
        .collect();
    let rounds = body
        .iter()
        .position(|l| l.contains("while top < n32"))
        .expect("the doubling loop");
    assert_eq!(
        sorts.len(),
        1,
        "{:?}",
        sorts.iter().map(|&i| &body[i]).collect::<Vec<_>>()
    );
    assert!(
        sorts[0] < rounds,
        "the one sort is inside the doubling loop: {}",
        body[sorts[0]]
    );
}
