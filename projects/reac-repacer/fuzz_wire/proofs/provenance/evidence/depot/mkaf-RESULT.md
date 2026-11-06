# mkAF audit at 4483a8de6e6f (the publication owner via the unit owner's ruling, 23:39Z)
Every `mkAF` (word) row of the lib, classified by mkaf_audit.py (git-archive export of the head, no edits).
Total 1,250 rows in 210 lib files (the unit owner's count): 619 A-core (101 files), 631 trunk (a8, 109 files).
(a) PROVED position: 1,227. All 619 A-core rows are (a) and 608 trunk rows. Of these, 876 sit in a premise every caller
    proves in its own proof; 189 in a definition used only inside proofs / lemma conclusions; 91 inside Qed proof
    scripts; 59 in lemma conclusions; 4 in tactic code; 8 are (a) through the exit-site contract (A/AD20.v:66-68,
    A/AD2f.v:34, A/AD2i.v:750, Reusable/YP08.v:283/285/288): that contract is proved by tfib_exit_site (A/AD1j.v:123)
    and assumed as Section Hypothesis EXS (A/AD1p.v:77), which is discharged before every composition top: the
    Print Assumptions of those tops are primitives + functional extensionality only, NO Section variable
    (pa-wire.tsv), so no mkAF premise reaches a top undischarged.
(b) PREMISE position: 0. Nothing to derive; STOP list empty.
Neither (23, all trunk): 22 in four definitions nothing in the lib references (cbb_facts and three cbl_facts_* in
    Reusable/YI08.v and its U/ copy) and 1 is the `Record afact := mkAF {..}` declaration (Reusable/YP0m.v:459).
Identical to donor: 614 of the 614 lib/A rows that have a donor match it (grant W4 524/524, knock k17 32/32, both-paired
    files vs knock 58/58). The single text that differs from grant W4 is A/AFek.v:33 aTOT `mkAF 1 131072 0` (grant: 2),
    the taken knock value (empty depot: TOT counts from the first Put), an (a) row.
