#!/bin/sh
# run.sh -- the whole kit re-run of ALLOC-PATTERN.md section 8 on cmpkit 4bbd3a74be89. Read-only on every binary.
# Run it from a directory of your choice; it writes the outputs of this record beside itself.
set -eu
HUB=${HUB:-HUB}
KITCOMMIT=3c3e62ee2786af6133699ff6684d17d66adcb03c          # BRANCH, the kit commit
KIT=./cmpkit-4bbd3a74be89
C=DONOR_TWIN          # donor twin ce511d541cda
A=DECODE_A_TWIN   # decode A twin 4cb0a852e826
CPIN=$HUB/projects/cgif/bin/cgif_file_fuzzer/cgif_file_fuzzer.asan-ubsan                    # donor pin 1c29845fe605
APIN=DECODE_A_PIN       # decode pin 5973b76807d8
OLD=OLD_RECORD/out                       # the old record's outputs

# 0. the kit, exactly its 7 files, from the hub
rm -rf "$KIT"; mkdir "$KIT"
git -C "$HUB" archive $KITCOMMIT tools/cmpkit/4bbd3a74be89 | tar -x --strip-components=3 -C "$KIT"
(cd "$KIT" && sha256sum -c SHA256SUMS && sha256sum SHA256SUMS)   # kit id = first 12 of sha256(SHA256SUMS)

# 1. both sides are the unstripped twins of the pinned binaries (the kit needs .symtab on both sides)
python3 "$KIT"/drvcmp.py twins "$APIN" "$A" "$CPIN" "$C" | tee twins.out

# 2. controls, before the run
#    the old repin_check e5487165abb8 that controls/negctl.py loads, from the same BRANCH commit
mkdir -p NEGCTL_ROOT/tools/repin_check/e5487165abb8
git -C "$HUB" show $KITCOMMIT:tools/repin_check/e5487165abb8/repin_check.py \
  > NEGCTL_ROOT/tools/repin_check/e5487165abb8/repin_check.py
python3 "$KIT"/controls/negctl.py "$KIT" | tee negctl-mine.out
diff "$KIT"/controls/repin-negctl.out negctl-mine.out && echo 'negctl: IDENTICAL to the kit record'
python3 ./ownctl.py "$KIT" | tee ownctl.out            # 3 plants on this run's own inputs

# 3. the run of record: the 7 function pairs, strictcmp2 16982e3ef42b (THE one compare)
FNS=$(awk -F'\t' 'NR>1{printf "%s%s",(NR>2?",":""),$1}' "$OLD"/pairs.tsv)
python3 "$KIT"/strictcmp2.py cmp "$FNS" C=$C A=$A C:A > run-strictcmp2.out
printf 'strictcmp2 rc=%s\n' $?

# 4. selection: each of the 7 names is exactly one symbol in each image
python3 ./symcheck.py "$KIT" "$OLD"/pairs.tsv | tee symcheck.out

# 5. the 417 code numerals: the word at each donor symbol+offset in the decode copy
python3 ./numerals.py "$KIT" "$OLD"/numerals.tsv "$OLD"/pairs.tsv $C $A numerals-kit.tsv | tee numerals-kit.out

# 6. the one reported row: Allocate +0xdc, the kit's KNOWN FALSE-DIFFERENCE class, measured by hand
python3 ./probe_tbl.py "$KIT" | tee probe_tbl.out

# 7. duplicated names: every STT_FUNC symbol of each name in .symtab AND .dynsym of both images, and strictcmp2 at
#    every same-size candidate of the target (funcpair.py d37a0f9a14fb keeps only the first symtab entry per name)
python3 ./dupnames.py "$KIT" "$OLD"/pairs.tsv | tee dupnames.out

# 8. header scope: every address the 47 shipped .v headers cite as 're-derived by funcpair.py', against this re-run
python3 ./headers.py "$HUB" 88154566652a ../numdiff.tsv "$OLD"/numerals.tsv "$OLD"/calls.tsv | tee headers.out

# 9. every numeral the 47 released headers cite, resolved in decode A's own .symtab and categorised (a)/(b)/(c)
python3 ./resolve.py "$KIT" "$HUB" 88154566652a ../numdiff.tsv "$OLD"/numerals.tsv resolve-kit.tsv | tee resolve-kit.out

# 10. duplicated STT_FUNC names of both images, and whether any address of this record lies in one
python3 ./dupzone.py "$OLD"/numerals.tsv resolve-kit.tsv "$OLD"/pairs.tsv | tee dupzone.out

# 11. the FULL differing-target list of every pair, from strictcmp2's tcmp itself (printed output truncates)
python3 ./fulldiff.py "$OLD"/pairs.tsv | tee fulldiff.out

# 12. symtab entry count of each paired name in both twins, and a by-ADDRESS re-run of every pair
python3 ./nmcount.py "$OLD"/pairs.tsv | tee nmcount.out
