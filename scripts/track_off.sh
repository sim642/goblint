#/bin/bash
scripts/set_version.sh
grep -q 'tracking = true' src/config.ml && \
  sed 's/tracking = true/tracking = false/' src/config.ml > src/config.tmp && mv src/config.tmp src/config.ml
make
