#!/bin/sh
# class 2: the generic run.sh of ../class1 with this directory's donor.conf and model.txt; outputs here (out-port2/).
#   run.sh WT HUB DONOR_DIR TARGET_DIR ALRELOC [--write]      (see ../class1/run.sh)
here=$(cd "$(dirname "$0")" && pwd)
CLSDIR=$here exec "$here/../class1/run.sh" "$@"
