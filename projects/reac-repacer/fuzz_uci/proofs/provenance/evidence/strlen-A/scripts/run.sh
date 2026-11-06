#!/bin/sh
# The run of record: writes provenance/evidence/strlen-A. Set the variables of env.example.sh first.
# The builder checks the kit in $KIT against its SHA256SUMS (sha256(SHA256SUMS) must start with 4bbd3a74be89, each file
# must match its line) and copies exactly its seven files into one temporary directory, where it runs them.
# usage: run.sh EVIDENCE_DIR
set -e
: "${KIT:?set KIT to the cmpkit 4bbd3a74be89 directory (SHA256SUMS and its seven files)}"
D=$(dirname "$0")
python3 "$D/mk_evidence_strlen_kit.py" "$1/strlen-A"
