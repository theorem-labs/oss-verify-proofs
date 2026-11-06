#!/bin/sh
# The run of record: writes provenance/evidence/memchr-A and memchr-B. Set the variables of env.example.sh first.
# usage: run.sh EVIDENCE_DIR
set -e
D=$(dirname "$0")
for i in A B; do python3 "$D/mk_evidence_memchr.py" "$i" "$1/memchr-$i"; done
