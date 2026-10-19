#!/usr/bin/env bash
# Download arXiv:1611.09877v2 into paper/ and compare it with the PDF used for the formalization.
set -euo pipefail
cd "$(dirname "$0")/.."
expected=11556ec3855cee0b91212b98a82dce7456883915c20cceab05d6bd632f6f0eb7
out=paper/1611.09877v2.pdf
curl -fL --retry 3 -o "$out" https://arxiv.org/pdf/1611.09877v2
if command -v sha256sum >/dev/null; then actual=$(sha256sum "$out" | cut -d' ' -f1)
else actual=$(shasum -a 256 "$out" | cut -d' ' -f1); fi
if [ "$actual" = "$expected" ]; then
  echo "OK: $out matches the PDF used for the formalization"
else
  echo "WARNING: $out has SHA-256 $actual, expected $expected (arXiv may have regenerated the PDF)" >&2
  exit 1
fi
