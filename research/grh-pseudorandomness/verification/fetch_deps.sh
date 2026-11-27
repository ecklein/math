#!/bin/sh
# Fetch pinned dependencies. Run from this project's root (research/grh-pseudorandomness/).
set -eu
GRH_REV=72fead102f663d5c7a407964a13dc0cf9d977207
mkdir -p vendor
[ -d vendor/grh-lean ] || git clone https://github.com/lsernau/grh-lean vendor/grh-lean
git -C vendor/grh-lean checkout -q "$GRH_REV"
test "$(git -C vendor/grh-lean rev-parse HEAD)" = "$GRH_REV"
echo "grh-lean at $GRH_REV"
