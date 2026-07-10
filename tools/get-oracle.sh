#!/usr/bin/env bash
# Download and install the official SAL 3.3 binary distribution into .oracle/
# so it can be used as the ground-truth oracle for differential testing.
#
# After this script completes, source .oracle/env.sh (or prepend
# .oracle/sal-3.3/bin to PATH) before running the oracle tools. The bundled
# Yices 1.0.38 MUST shadow any system yices: sal-bmc/sal-inf-bmc pass
# Yices-1-only flags (e.g. --evidence) that Yices 2 rejects.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ORACLE="$ROOT/.oracle"
URL="https://sri-fm.github.io/sal/opendownload/sal-3.3-bin-x86_64-unknown-linux-gnu.tar.gz"

if [ -x "$ORACLE/sal-3.3/bin/sal-smc" ]; then
    echo "Oracle already installed in $ORACLE"
    exit 0
fi

mkdir -p "$ORACLE"
cd "$ORACLE"
if [ ! -f sal-3.3-bin.tar.gz ]; then
    echo "Downloading $URL ..."
    curl -fsSL -o sal-3.3-bin.tar.gz "$URL"
fi
tar xzf sal-3.3-bin.tar.gz
cd sal-3.3
./install.sh > install.log

cat > "$ORACLE/env.sh" <<EOF
export PATH="$ORACLE/sal-3.3/bin:\$PATH"
EOF

echo "Oracle installed. Use:  source $ORACLE/env.sh"
"$ORACLE/sal-3.3/bin/sal-smc" --version || true
