#!/usr/bin/env bash
#
# Fetch the corpus the Strings benchmark (`benches/strings.rs`) measures, from Project Gutenberg.
#
# The ids are written down here rather than passed in, because a benchmark whose corpus depends
# on what the operator felt like downloading measures nothing anyone else can check. Re-running
# this script on any machine with network access produces the same bytes, so the benchmark's
# numbers are reproducible rather than merely reported.
#
# Each text is cut to its body -- Project Gutenberg's licence header and footer are the same
# boilerplate in every file, so leaving them in would put one repeated block of English in the
# index dozens of times and flatter every compressed-search number. What is left is prose.
#
# Usage:  scripts/fetch_corpus.sh [--force]
#
# Writes `corpus/pg<id>.txt` per text and `corpus/corpus.txt`, their concatenation, which is what
# the benchmark indexes. `corpus/` is not committed: it is someone else's text and it is
# reproducible from this script.
#
# Exits non-zero, with the id named and every partial file removed, if any text cannot be
# fetched or does not carry both boundary markers. A half-corpus would silently change every
# number in the table.

set -euo pipefail

# Ten works in English prose. Chosen to be long enough that the index is not dominated by
# constant-size overheads, varied enough in author and century that the byte statistics are not
# one writer's habits, and small enough in total that a full sweep (nine index builds, each one
# an O(n log n) suffix array) finishes in minutes.
IDS=(
	1342 # Austen, Pride and Prejudice
	84   # Shelley, Frankenstein
	2701 # Melville, Moby Dick
	1661 # Doyle, The Adventures of Sherlock Holmes
	98   # Dickens, A Tale of Two Cities
	1400 # Dickens, Great Expectations
	345  # Stoker, Dracula
	174  # Wilde, The Picture of Dorian Gray
	76   # Twain, Adventures of Huckleberry Finn
	11   # Carroll, Alice's Adventures in Wonderland
)

# The bytes the benchmark was measured on, per text after the cuts below and for the
# concatenation. A checksum rather than a length: Project Gutenberg revises its texts in place,
# and a revised text is a different corpus -- every published number was taken on these bytes,
# and on different ones it is a different measurement that merely looks comparable. A mismatch
# is an error that names the text; if Gutenberg has revised one, re-measure, then move these and
# the numbers together.
# A function rather than an associative array, which needs bash 4: stock macOS bash is 3.2.
expected_sha256() {
	case "$1" in
	1342) echo e79303d04de9260489f9d5a2ad4aae5776680fcec484f2e732d6ded7411bf402 ;;
	84) echo 5e07c3d9c8f1b6b2e88b6d6b5dd6ea13fd410c22e749e71111effcdf11ed2b04 ;;
	2701) echo cdccdc99703c9f38f270dd9572591857243a87fe3991f1ab7df383fc1d117e75 ;;
	1661) echo 3552d466d95a92fb58e96bbfabbfc02370d359ac95933b5feafe4ebaf3f243b3 ;;
	98) echo eb2da2c905cdc30f2265e0473e3abf8533cf46432923f31a5309cf108d5650a0 ;;
	1400) echo 9b38641197993d0d63d3a464243a2b789271d2bd1a49504fd107d43012033283 ;;
	345) echo a7786a4c81df95265b33d8c24dbbcaee80ab531d7d266a9782d52301718ce7c7 ;;
	174) echo f363ec3dfcc54f18cafaf025769c3e298e27c6704cc8782d632c821e8d64a2c1 ;;
	76) echo 6992a76ed348e0cd7592bce2b6c34644921aee5742c1381169fd6d1c3a25c49e ;;
	11) echo e3917589f48b4e9f4b731a6b7e127cf9ddd6e1b3819c78be02a2702ee73bfdb1 ;;
	*) echo unknown ;;
	esac
}
CORPUS_SHA256=eeaf298576e53dc616e5d03460717f79219b7ff7250a0a54e6ac40f5422cc77a

sha256_of() {
	if command -v sha256sum >/dev/null; then
		sha256sum "$1" | cut -d' ' -f1
	else
		shasum -a 256 "$1" | cut -d' ' -f1
	fi
}

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS_DIR="$REPO_ROOT/corpus"
CONCAT="$CORPUS_DIR/corpus.txt"
UA="algodesign-corpus-fetch/1.0 (benchmark corpus; https://github.com/mbrcic/algodesign)"

FORCE=0
if [[ "${1:-}" == "--force" ]]; then
	FORCE=1
elif [[ $# -gt 0 ]]; then
	echo "usage: $0 [--force]" >&2
	exit 2
fi

command -v curl >/dev/null || {
	echo "fetch_corpus: curl is not installed; cannot fetch the corpus." >&2
	exit 1
}

mkdir -p "$CORPUS_DIR"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

fetch_one() {
	local id="$1" out="$CORPUS_DIR/pg$id.txt"
	if [[ -s "$out" && $FORCE -eq 0 ]]; then
		printf '  pg%-5s %9d bytes (cached)\n' "$id" "$(wc -c <"$out")"
		return 0
	fi

	local raw="$tmp/pg$id.raw" body="$tmp/pg$id.body"
	if ! curl --fail --silent --show-error --location --max-time 120 \
		--user-agent "$UA" \
		"https://www.gutenberg.org/cache/epub/$id/pg$id.txt" -o "$raw"; then
		echo "fetch_corpus: could not download Project Gutenberg text $id." >&2
		echo "  No network access, or Gutenberg refused the request. The corpus is NOT usable;" >&2
		echo "  run the benchmark anyway and it will say, in its own output, that its numbers" >&2
		echo "  are from generated text rather than from this corpus." >&2
		return 1
	fi

	# The body: everything strictly between the two boilerplate markers. Both spellings occur --
	# newer files say "THE PROJECT GUTENBERG EBOOK", older ones "THIS PROJECT GUTENBERG EBOOK".
	# The marker lines themselves are dropped, and so is the UTF-8 BOM, which falls before START.
	awk '
		/^\*\*\* *END OF (THE|THIS) PROJECT GUTENBERG EBOOK/ { inside = 0 }
		inside { print }
		/^\*\*\* *START OF (THE|THIS) PROJECT GUTENBERG EBOOK/ { inside = 1; seen_start = 1 }
		END { exit (seen_start ? 0 : 1) }
	' "$raw" >"$body" || {
		echo "fetch_corpus: text $id carries no START marker; the file is not what we expect." >&2
		return 1
	}
	if ! grep -q '^\*\*\* *END OF \(THE\|THIS\) PROJECT GUTENBERG EBOOK' "$raw"; then
		echo "fetch_corpus: text $id carries no END marker; the download may be truncated." >&2
		return 1
	fi

	# Two byte-level edits, both of which change what the index measures:
	#   * CR. These files are CRLF, and a carriage return is a byte of the effective alphabet
	#     that no reader of the prose would call a symbol of it. Removing it keeps sigma_eff and
	#     H_0 about English rather than about the file format.
	#   * NUL. `bwt::encode` reserves 0x00 as the sentinel and panics on an interior one. Prose
	#     files should hold none; if one appears it is dropped and counted, out loud.
	local nuls
	nuls="$(tr -dc '\000' <"$body" | wc -c | tr -d ' ')"
	tr -d '\r\000' <"$body" >"$body.clean"
	[[ -s "$body.clean" ]] || {
		echo "fetch_corpus: text $id is empty after the markers were cut." >&2
		return 1
	}
	mv "$body.clean" "$out"
	printf '  pg%-5s %9d bytes' "$id" "$(wc -c <"$out")"
	[[ "$nuls" == "0" ]] || printf '  (%s NUL byte(s) dropped)' "$nuls"
	printf '\n'
}

echo "fetch_corpus: ${#IDS[@]} texts from Project Gutenberg into $CORPUS_DIR"
for id in "${IDS[@]}"; do
	if ! fetch_one "$id"; then
		echo "fetch_corpus: FAILED on text $id. Removing every fetched file so that no" >&2
		echo "  half-corpus is left behind for a benchmark to measure and call complete." >&2
		rm -f "$CORPUS_DIR"/pg*.txt "$CONCAT"
		exit 1
	fi
	got="$(sha256_of "$CORPUS_DIR/pg$id.txt")"
	want="$(expected_sha256 "$id")"
	if [[ "$got" != "$want" ]]; then
		echo "fetch_corpus: text $id is not the text the benchmark was measured on:" >&2
		echo "  sha256 $got, expected $want." >&2
		echo "  Project Gutenberg revises texts in place. Removing it and the concatenation, so" >&2
		echo "  that no benchmark reports numbers on a different corpus. To adopt" >&2
		echo "  the new text, re-run the benchmark and move expected_sha256 with its numbers." >&2
		rm -f "$CORPUS_DIR/pg$id.txt" "$CONCAT"
		exit 1
	fi
	# Gutenberg rate-limits; a download every second is polite and still finishes in seconds.
	sleep 1
done

# The concatenation, in the fixed order above, is what the benchmark indexes.
: >"$CONCAT"
for id in "${IDS[@]}"; do
	cat "$CORPUS_DIR/pg$id.txt" >>"$CONCAT"
	printf '\n' >>"$CONCAT"
done

got="$(sha256_of "$CONCAT")"
if [[ "$got" != "$CORPUS_SHA256" ]]; then
	echo "fetch_corpus: corpus.txt has sha256 $got, expected $CORPUS_SHA256, although every" >&2
	echo "  text matched: the concatenation itself changed. Removing it." >&2
	rm -f "$CONCAT"
	exit 1
fi
echo "corpus.txt: sha256 $got, the corpus the benchmark was measured on"

# The corpus's own statistics: its size, how many distinct byte values it uses (sigma_eff, which
# is one directory per symbol inside the FM-index and therefore the whole of its overhead term),
# and its zeroth-order entropy in bits per byte. The benchmark recomputes both on the exact bytes
# it indexes and prints them again; these are here so the fetch can be checked without a build.
od -An -v -tu1 -w1 <"$CONCAT" | LC_ALL=C awk -v bytes="$(wc -c <"$CONCAT")" '
	{ n[$1]++ }
	END {
		h = 0
		for (b in n) { p = n[b] / bytes; h -= p * log(p) / log(2) }
		printf "\ncorpus.txt: %d bytes, sigma_eff = %d distinct byte values, H_0 = %.3f bits/byte\n", bytes, length(n), h
	}
'
echo "The benchmark reads this file automatically: cargo bench -p algodesign --bench strings"
