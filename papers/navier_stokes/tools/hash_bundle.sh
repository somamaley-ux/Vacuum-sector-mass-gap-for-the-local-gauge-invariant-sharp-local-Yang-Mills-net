#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
find . -type f \( -name "*.tex" -o -name "*.bib" -o -name "*.md" -o -name "*.txt" -o -name "*.sh" -o -name "latexmkrc" \) \
  ! -path "./phase7_readiness/06_source_manifest_sha256.txt" \
  ! -path "./main.pdf" ! -path "./phase7_readiness_pack.pdf" \
  ! -path "./*.aux" ! -path "./*.bbl" ! -path "./*.bcf" ! -path "./*.blg" ! -path "./*.fdb_latexmk" ! -path "./*.fls" ! -path "./*.log" ! -path "./*.out" ! -path "./*.run.xml" ! -path "./*.toc" \
  -print0 | sort -z | xargs -0 sha256sum > phase7_readiness/06_source_manifest_sha256.txt

echo "wrote phase7_readiness/06_source_manifest_sha256.txt"
