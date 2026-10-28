# The checker image: stock Rocq, the libraries the process model needs, and
# the model itself, rocq-linux-process-semantics-core (with its elf-snapshot
# tool).  Nothing else: `oft` runs from the checkout, and no proof automation
# is installed.
#
#   docker build -f toolchain/checker.Dockerfile --build-context lps=<dir> toolchain/
#
# Every input is pinned: the base image by digest, the two opam repositories
# by commit, every package at an explicit version whose archive opam checks
# against the checksum in its package file, and the model's files by a hash
# over them (LPS_TREE_SHA256).
#
# Every opam build step runs with no network at all (RUN --network=none): the
# archives are gathered first, by the `opam-archives` stage, and opam checks
# each against the checksum in its package file before using it.  So the
# image is a function of the pins above, whoever builds it.  To build without
# downloading, replace the two stages that download with local directories:
#   --build-context rocq-opam-released=<dir>   an opam repository holding (at
#                                              least) the packages below
#   --build-context opam-archives=<dir>        their archives, in opam's
#                                              download-cache layout
#                                              (<algo>/<2 hex digits>/<digest>)
#
# The model is theorem-labs/rocq-linux-process-semantics at the commit release.yaml names (semantics.commit), cut to
# the files toolchain/lps-core.paths lists, which is all that rocq-linux-process-semantics-core builds from:
#   grep -v -e '^#' -e '^$' toolchain/lps-core.paths | xargs -d '\n' git -C <checkout> archive <commit> -- | tar -x -C <dir>
# That directory is the `lps` build context, and the build refuses one whose hash differs.

ARG OPAM_BASE=ocaml/opam:ubuntu-24.04-ocaml-4.14@sha256:6ecfb14609386743ec4356e59e4b24a16a018925de47bc983eba3a4609ac850b

# ---- inputs -----------------------------------------------------------------

# Installed from the default repository of the base image, and from the Rocq
# released repository at ROCQ_OPAM_REPO_SHA.  conf-g++ is named so that the
# solver does not pick conf-clang for coq-flocq.
ARG OPAM_PACKAGES="conf-g++.1.0 dune.3.23.0 rocq-runtime.9.2.0 rocq-core.9.2.0 rocq-stdlib.9.2.0 rocq-stdpp.1.13.0 rocq-stdpp-bitvector.1.13.0 coq-flocq.4.2.2 rocq-read-file.0.0.2"

# git checks every object it fetches against its hash, so the files below are
# the commit's, whichever roots the base image's store trusts.
FROM ${OPAM_BASE} AS fetch-rocq-opam
ARG ROCQ_OPAM_REPO_SHA=d330865276542eb86269e88d4f3d9d4c974fee2e
RUN git init -q /tmp/repo && cd /tmp/repo && \
    git fetch -q --depth 1 https://github.com/rocq-prover/opam.git "${ROCQ_OPAM_REPO_SHA}" && \
    test "$(git rev-parse FETCH_HEAD)" = "${ROCQ_OPAM_REPO_SHA}" && \
    mkdir -p /tmp/released && \
    git archive FETCH_HEAD released | tar -x -C /tmp/released --strip-components=1

FROM scratch AS rocq-opam-released
COPY --from=fetch-rocq-opam /tmp/released/ /

FROM ${OPAM_BASE} AS fetch-opam-archives
ARG OPAM_PACKAGES
ENV OPAMYES=1 OPAMCOLOR=never OPAMNODEPEXTS=1
COPY --from=rocq-opam-released --chown=opam:opam / rocq-opam-released/
RUN opam repo add --this-switch rocq-released "${HOME}/rocq-opam-released" && \
    opam install --download-only ${OPAM_PACKAGES:?} && \
    cp -r "$(opam var root)/download-cache" /tmp/opam-archives

FROM scratch AS opam-archives
COPY --from=fetch-opam-archives /tmp/opam-archives/ /

# Must be supplied (see above).
FROM scratch AS lps

# ---- the image --------------------------------------------------------------

FROM ${OPAM_BASE} AS checker
USER root
SHELL ["/bin/bash", "-euo", "pipefail", "-c"]
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get install -y --no-install-recommends libgmp-dev pkg-config m4 python3 time && \
    apt-get clean

USER opam
WORKDIR ${HOME}
ENV OPAMYES=1 OPAMCOLOR=never OPAMCONFIRMLEVEL=unsafe-yes OPAMNODEPEXTS=1
ARG OPAMJOBS=8
ENV OPAMJOBS=${OPAMJOBS}
ARG OPAM_PACKAGES

COPY --from=rocq-opam-released --chown=opam:opam / rocq-opam-released/
COPY --from=opam-archives --chown=opam:opam / .opam/download-cache/

# The compiler is the base image's own switch (OCaml 4.14); the default opam
# repository is the one inside the base image, pinned by its digest.
RUN --network=none \
    opam repo add --this-switch rocq-released "${HOME}/rocq-opam-released" && \
    { ulimit -s unlimited || true; } && \
    opam install ${OPAM_PACKAGES:?}

ARG LPS_TREE_SHA256=c69c38f381767a112d0b4d5692548369f65cbf3a73ba198f76f98310894dd4de
COPY --from=lps --chown=opam:opam / lps/
RUN cd "${HOME}/lps" && \
    got="$(find . -type f -printf '%P\n' | LC_ALL=C sort | xargs -d '\n' -r sha256sum | sha256sum | awk '{print $1}')" && \
    echo "rocq-linux-process-semantics-core files sha256: ${got}" && \
    test "${got}" = "${LPS_TREE_SHA256:?}"
RUN --network=none \
    { ulimit -s unlimited || true; } && \
    opam pin add --yes rocq-linux-process-semantics-core "${HOME}/lps"

# CI runs the image as the runner's own user (docker run -u), with HOME=/tmp:
# the switch must be readable by any user, and no opam wrapper may stand in
# front of the command.
USER root
RUN chmod a+rx ~opam ~opam/.opam && \
    find ~opam/.opam/4.14 -type d ! -perm -o=rx -exec chmod a+rx {} + && \
    find ~opam/.opam/4.14 -type f ! -perm -o=r -exec chmod a+r {} +
# Trust no root of eMudhra's emSign CAs or of Comodo's AAA Certificate
# Services: private keys of intermediates under them are compromised
# (Mozilla's security blog, 2026-10-20, for emSign; Mozilla's mail to
# oss-security that day, "eMudhra Intermediates Compromise", says the
# intermediates were cross-signed under AAA Certificate Services).  The base image's
# ca-certificates (20240203) has all five.  This step disables exactly those
# five in the system store, cuts them out of each certifi cacert.pem under
# /usr (the image has none today), and fails the build if a store still holds
# one, or holds none at all, or if the conf does not name all five.  It needs
# no network.  The checks run this image with no network; the step is for
# anything in it that ever uses TLS.
RUN --network=none python3 - <<'DISTRUST'
import pathlib, re, subprocess, sys

BAD = re.compile(r"emSign|eMudhra|CN ?= ?AAA Certificate Services", re.I)
ENTRIES = {
    "mozilla/Comodo_AAA_Services_root.crt",
    "mozilla/emSign_Root_CA_-_G1.crt",
    "mozilla/emSign_Root_CA_-_C1.crt",
    "mozilla/emSign_ECC_Root_CA_-_G3.crt",
    "mozilla/emSign_ECC_Root_CA_-_C3.crt",
}

conf = pathlib.Path("/etc/ca-certificates.conf")
lines = conf.read_text().splitlines()
found = {l for l in lines if l in ENTRIES}
if found != ENTRIES:
    sys.exit(f"FAIL: {conf} lacks {sorted(ENTRIES - found)}")
conf.write_text("".join(("!" + l if l in ENTRIES else l) + "\n" for l in lines))
subprocess.run(["update-ca-certificates", "--fresh"], check=True, stdout=subprocess.DEVNULL)

bundles = [p for p in pathlib.Path("/usr").rglob("certifi/cacert.pem") if p.is_file()]
for pem in bundles:
    blocks = re.split(r"\n(?=\n# Issuer:)", pem.read_text())
    kept = [b for b in blocks if not any(BAD.search(h) for h in re.findall(r"^# (?:Issuer|Subject|Label):.*$", b, re.M))]
    pem.write_text("\n".join(kept))
    print(f"{pem}: removed {len(blocks) - len(kept)} roots")

def subjects(path):
    p7 = subprocess.run(["openssl", "crl2pkcs7", "-nocrl", "-certfile", str(path)], check=True, capture_output=True)
    out = subprocess.run(["openssl", "pkcs7", "-print_certs", "-noout"], input=p7.stdout, check=True, capture_output=True)
    return [l for l in out.stdout.decode().splitlines() if l.startswith("subject=")]

failed = False
for path in [pathlib.Path("/etc/ssl/certs/ca-certificates.crt"), *bundles]:
    subs = subjects(path)
    left = [s for s in subs if BAD.search(s)]
    if not subs or left:
        print(f"FAIL: {path}: {len(subs)} roots, still trusted: {left}")
        failed = True
sys.exit(failed)
DISTRUST
USER opam
ENTRYPOINT []
CMD ["bash"]

# Self-test in the finished image: the tools run, the specification loads, a
# statement ascribed at the wrong type is refused, and rocqchk checks the
# specification.  rocqchk runs without its bytecode machine
# (-bytecode-compiler no), here and in every check this repository makes:
# rocq-core 9.2.0's rocqchk refuses the machine code stored in these libraries
# ("Validation failed: bad constant constructor 11 (in vm_caml_prim)"), and
# without the machine it checks the same proofs by reduction instead.
RUN --network=none eval "$(opam env)" && \
    mkdir -p /tmp/selftest && cd /tmp/selftest && \
    rocq --version > versions.txt && rocqchk --version >> versions.txt 2>&1 && cat versions.txt && \
    elf-snapshot --help > /dev/null && \
    printf '%s\n' \
      'From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed.' \
      'Check strong_universal_error_free_T_budgets.' 'Check halts_allowed_T_scfg_budgets.' > Ok.v && \
    printf '%s\n' 'Definition bad : False := I.' > Bad.v && \
    rocq compile -native-compiler no -R . T Ok.v > /dev/null && \
    { ! rocq compile -native-compiler no -R . T Bad.v 2> /dev/null; } && \
    rocqchk -o -bytecode-compiler no -R . T T.Ok > chk.log 2>&1 && \
    grep -q 'Modules were successfully checked' chk.log && \
    echo "checker image self-test: pass"

ENV OPAM_SWITCH_PREFIX=${HOME}/.opam/4.14 \
    PATH=${HOME}/.opam/4.14/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
    CAML_LD_LIBRARY_PATH=${HOME}/.opam/4.14/lib/stublibs:${HOME}/.opam/4.14/lib/ocaml/stublibs:${HOME}/.opam/4.14/lib/ocaml
LABEL org.opencontainers.image.title="oss-fuzz-theorems checker" \
      org.opencontainers.image.licenses="MIT"
WORKDIR /work
