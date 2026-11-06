#!/usr/bin/env python3
"""tests/mutate.py: a vacuous statement kind must fail the controls.

    python3 tests/mutate.py        (from the repository root, in the checker image; tests/check.sh runs it)

For each statement kind of theories/Shapes.v this makes the kind vacuous, or true of every program, in a scratch
copy of theories/, tests/, toolchain/ and dune-project, and requires `dune build --root . theories tests` of that copy
to FAIL, at a file other than Shapes.v (theories/Premises.v, a refutation under tests/proofs/, tests/toy/Controls.v).
It requires the same build of an unmutated copy to pass.  It exits 1 if any kind's mutation is not caught, if a
mutation does not apply to the text of Shapes.v exactly once, or if the unmutated copy does not build.

In every copy, the unmutated one included, each proof of Shapes.v is replaced by Admitted.  Those lemmas
(`_is_lps`, `_mono`, `_of_classifier`) are facts about the shapes, not controls, and a mutation breaks some of them;
the change being simulated arrives with them restated.  An Admitted lemma can let a file that uses it compile, never
make one fail, so a failure downstream is the mutation's doing.  (Nothing here is ever checked as a proof: the copies
are deleted.)

The mutations include the ones the reviews of these controls used, and, for each other agreement and halting shape, a
premise that contradicts the shape's input predicate.

The checkout itself is never written: Shapes.v is read from it, each mutated text is written only into a copy under a
fresh temporary directory, and each copy is deleted when its build ends, whether it passes, fails or raises.
"""
import concurrent.futures
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.getcwd()
COPY = ("theories", "tests", "toolchain", "dune-project")

CONTRADICTS = {
    "valid_input": "in_abort_terminal inp = true",          # valid_input pins in_abort_terminal to false
    "valid_input_abort": "in_abort_terminal inp = false",   # valid_input_abort pins it to true
    "valid_input_hwcap_rv64gc": "in_hwcap inp <> hwcap_rv64gc",
    "valid_input_abort_hwcap_rv64gc": "in_hwcap inp <> hwcap_rv64gc",
}


def premise(pred, extra):
    """Add the premise `extra` after the shape's `pred inp ->` line."""
    line = "    %s inp ->\n" % pred
    return (line, line + "    %s ->\n" % extra)


BOUND = ("(sum_weights w l <= b * M)%Q", "(sum_weights w l <= b * M + (if Qle_bool b 0 then 0 else M))%Q")
DECIDE_C = ("exists C : Image, image_wf C /\\ ", "exists C : Image, ")

# (kind, what the mutation does, (old text, new text) inside the kind's Definition)
MUTATIONS = [
    ("halts_within_budget", "a premise contradicting valid_input",
     premise("valid_input", CONTRADICTS["valid_input"])),
    ("halts_may_fail", "the premise valid_input_abort inp (a reviewer's)",
     premise("valid_input", "valid_input_abort inp")),
] + [
    (kind, "a premise contradicting " + pred, premise(pred, CONTRADICTS[pred]))
    for kind, pred in (("agrees", "valid_input"), ("agrees_in", "valid_input"),
                       ("agrees_abort_modelled", "valid_input_abort"),
                       ("agrees_in_abort_modelled", "valid_input_abort"),
                       ("agrees_rv64gc", "valid_input_hwcap_rv64gc"),
                       ("agrees_in_rv64gc", "valid_input_hwcap_rv64gc"),
                       ("agrees_abort_modelled_rv64gc", "valid_input_abort_hwcap_rv64gc"))
] + [
    ("disagrees_at_most", "true at every b > 0 (a reviewer's)", BOUND),
    ("disagrees_at_most_rv64gc", "true at every b > 0", BOUND),
    ("agreement_decidable", "the image_wf C conjunct dropped (a reviewer's)", DECIDE_C),
    ("agreement_decidable_rv64gc", "the image_wf C conjunct dropped", DECIDE_C),
]


def definition_span(text, kind):
    start = text.index("\nDefinition %s " % kind) + 1
    end = text.index("\n\n", start)
    return start, end


def mutate(text, kind, old, new):
    start, end = definition_span(text, kind)
    block = text[start:end]
    if block.count(old) != 1:
        raise ValueError("the mutation of %s matches %d times in its Definition" % (kind, block.count(old)))
    return text[:start] + block.replace(old, new) + text[end:]


def admit_all(text):
    return re.sub(r"Proof\..*?Qed\.", "Admitted.", text, flags=re.S)


def build(label, shapes_text, jobs):
    """Build a copy whose Shapes.v is shapes_text: (passed, the files dune reports errors in)."""
    d = tempfile.mkdtemp(prefix="mutate-%s-" % label)
    try:
        for p in COPY:
            src, dst = os.path.join(ROOT, p), os.path.join(d, p)
            if os.path.isdir(src):
                shutil.copytree(src, dst, ignore=shutil.ignore_patterns("_build", "__pycache__"))
            else:
                shutil.copy2(src, dst)
        with open(os.path.join(d, "theories", "Shapes.v"), "w", encoding="utf-8") as f:
            f.write(shapes_text)
        r = subprocess.run(["dune", "build", "--root", ".", "-j", str(jobs), "theories", "tests"], cwd=d,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=dict(os.environ, DUNE_CACHE="disabled"))
        out = r.stdout.decode("utf-8", "replace")
        files = sorted(set(re.findall(r'^File "\./([^"]+)"', out, re.M)))
        return r.returncode == 0, files, out
    finally:
        shutil.rmtree(d, ignore_errors=True)


def main():
    with open(os.path.join(ROOT, "theories", "Shapes.v"), encoding="utf-8") as f:
        shapes = f.read()
    parallel = max(1, min(4, (os.cpu_count() or 2) // 2))
    jobs = max(1, (os.cpu_count() or 2) // parallel)
    texts = []
    for kind, what, (old, new) in MUTATIONS:
        try:
            texts.append((kind, what, admit_all(mutate(shapes, kind, old, new))))
        except ValueError as e:
            print("BROKEN  %s: %s" % (kind, e))
            return 1
    base = admit_all(shapes)
    with concurrent.futures.ThreadPoolExecutor(parallel) as pool:
        base_run = pool.submit(build, "base", base, jobs)
        runs = [(k, w, pool.submit(build, k, t, jobs)) for k, w, t in texts]
        ok, files, out = base_run.result()
        if not ok:
            print("BROKEN  the unmutated copy does not build:\n" + out[-3000:])
            return 1
        print("PASS    unmutated copy builds")
        caught = 0
        for kind, what, fut in runs:
            ok, files, out = fut.result()
            outside = [f for f in files if f != "theories/Shapes.v"]
            if not ok and outside and "theories/Shapes.v" not in files:
                caught += 1
                print("CAUGHT  %s, %s: the build fails at %s" % (kind, what, ", ".join(outside)))
            elif not ok:
                print("MISSED  %s, %s: the build fails only at %s\n%s" % (kind, what, ", ".join(files) or "?", out[-2000:]))
            else:
                print("MISSED  %s, %s: the copy builds" % (kind, what))
    print("mutations caught: %d of %d kinds" % (caught, len(MUTATIONS)))
    return 0 if caught == len(MUTATIONS) else 1


if __name__ == "__main__":
    sys.exit(main())
