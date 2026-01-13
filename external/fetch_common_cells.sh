#!/bin/bash
#
# Fetch required files from PULP Platform common_cells repository
#
# This script downloads only the files needed for fpnew integration,
# avoiding a full submodule clone of 80+ files we don't need.
#
# Required files:
#   - lzc.sv           : Leading zero counter
#   - rr_arb_tree.sv   : Round-robin arbiter (uses lzc)
#   - cf_math_pkg.sv   : Math utilities (idx_width, etc.)
#   - assertions.svh   : Assertion macros
#   - registers.svh    : Register macros (FFLARNC, etc.)
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEST_DIR="${SCRIPT_DIR}/common_cells"
VERSION="v1.35.0"
BASE_URL="https://raw.githubusercontent.com/pulp-platform/common_cells/${VERSION}"

# Files to fetch
FILES=(
    "src/lzc.sv"
    "src/rr_arb_tree.sv"
    "src/cf_math_pkg.sv"
    "include/common_cells/assertions.svh"
    "include/common_cells/registers.svh"
)

echo "Fetching common_cells files (version ${VERSION})..."

# Create destination directories
mkdir -p "${DEST_DIR}/src"
mkdir -p "${DEST_DIR}/include/common_cells"

for file in "${FILES[@]}"; do
    dest="${DEST_DIR}/${file}"
    url="${BASE_URL}/${file}"
    echo "  Fetching ${file}..."
    curl -sS -o "${dest}" "${url}"
done

# Write version file for tracking
echo "${VERSION}" > "${DEST_DIR}/VERSION"
echo "Fetched from: https://github.com/pulp-platform/common_cells" >> "${DEST_DIR}/VERSION"
echo "Date: $(date -u +%Y-%m-%d)" >> "${DEST_DIR}/VERSION"

echo "Done. Files saved to ${DEST_DIR}/"
