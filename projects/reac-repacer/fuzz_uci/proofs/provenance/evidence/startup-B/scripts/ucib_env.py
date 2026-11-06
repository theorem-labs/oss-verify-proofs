"""ucib_env.py -- every machine-specific path the fuzz_uci image-B start-up writers read, in ONE place, from the
environment (set by the caller; env.example.sh beside this file names each variable). No host path is written in
any writer or in anything a writer emits for the repository: a writer names an input by the variable that holds it
or by a path relative to the repository root. A variable that is not set stops the writer with its name.

  UCIB_OVPI      a git checkout of the proofs repository (the donor text, decode / grant / a9 commits are read from it)
  UCIB_LT        local scratch; holds donorlib/ = `git archive 25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib`
  UCIB_TLIB      the unit lib being written: proofs/reac-repacer/fuzz_uci/lib of a checkout
  UCIB_UB        fuzz_uci.asan-ubsan pin (sha256 a1b86e424adde6f6...)    UCIB_UBS  its unstripped twin (8d07ffcf5948...)
  UCIB_UA        fuzz_uci.asan pin (sha256 6ea017c24525...)              UCIB_UAS  its unstripped twin (56822e263d76...)
  UCIB_CB        cgif_file_fuzzer.asan-ubsan (sha256 1c29845fe605...)    UCIB_CA   cgif_file_fuzzer.asan (7093581aab04...)
  UCIB_OLDSYMS   cgif's release symbol cache 1c29845fe6058de6.978e0a064c5a4c6e.v4.json (port_core --old-syms)
  UCIB_PGRELOC   port_core pg-reloc 0e4e065eab9f (commit 7f0e4b05267 tools/pg-reloc/0e4e065eab9f; cited, not shipped)
  UCIB_FROZEN    the frozen start-up tool set directory (the frozen/ dir of commit dbb5a97ad14's corrected start-up
                 set, materialised by name, or 8cd71d3a4bb's; cited, not shipped)
  UCIB_AB1HK     the directory holding gen_ab1hk.py (sha256 0f51cb9cdb18; cited, not shipped)
  UCIB_GENDEC    the directory holding decode's gen.py as gen_dec.py (sha256 6ccd419c977f; cited, not shipped)
  UCIB_DECB      fuzz_decode.asan-ubsan pin (sha256 5d05689fd5b1...)  UCIB_DECBS its unstripped twin (6744989bb2e6...)
  UCIB_GRB       fuzz_grant.asan-ubsan pin                             UCIB_GRBS  its unstripped twin
  UCIB_PACE165   the port_addr_check e165063a0081 versioned directory (cited, not shipped)
  UCIB_PACEFA1   the port_addr_check efa19b81e92b versioned directory, of record (cited, not shipped)
  UCIB_EXITDRV   the exit-driver lane directory (inputs/, binmatch/, tools/ of gen_exitB.py)
  UCIB_EXITWORK  where gen_exitB.py writes out/
  UCIB_MAPTOOL   the image address-map tool that made exitdrv's data map (sha256 4d51ec1c0069; cited, not shipped;
                 exitdrv/run.sh checks the sha256 before it runs the tool)
  UCIB_AF0MB     the directory holding the af0m base inputs (base.YF0m.v, cgif.YF0m.v, cgif.syms.v4.json)
  UCIB_DECREF    a checkout path of commit 7eb81ddb186 proofs/libreac/fuzz_decode/provenance/startup-gen/B (af0m adds list)
"""
import os


def need(name):
    v = os.environ.get(name)
    if not v:
        raise SystemExit('ucib_env: set %s (see env.example.sh)' % name)
    return v


def rel(path, root=None):
    """path relative to the repository root when it lies inside it, else the variable that names it, for messages."""
    for var in ('UCIB_TLIB', 'UCIB_LT', 'UCIB_OVPI', 'UCIB_UB', 'UCIB_UBS', 'UCIB_UA', 'UCIB_UAS', 'UCIB_CB', 'UCIB_CA',
                'UCIB_OLDSYMS', 'UCIB_PGRELOC', 'UCIB_FROZEN', 'UCIB_AB1HK', 'UCIB_GENDEC', 'UCIB_DECREF', 'UCIB_DECB', 'UCIB_DECBS', 'UCIB_GRB', 'UCIB_GRBS', 'UCIB_AF0MB', 'UCIB_PACE165'):
        v = os.environ.get(var)
        if v and (path == v or path.startswith(v.rstrip('/') + '/')):
            return '$%s%s' % (var, path[len(v.rstrip('/')):])
    return path
