# Derivation of the values in wire A's taken knock hunks (rule: the publication owner via the unit owner's ruling, 22:06Z + the stage-pairing audit)

Two records, together covering every value a taken knock hunk carries.

## 1. Hypothesis-position values: hyp-values.tsv (188 values, all DERIVED, 0 STOP)
Section Hypothesis / Variable types, mkAF atom ranges, KRange facts, register indices, return addresses, frame /
stack depths of the taken hunks. Each derived from fuzz_wire's own definitions (lib Definition at file:line, or the
pinned twin's symbol + offset). See hypvals-RESULT.md.

## 2. Every numeral that DIFFERS from the donor: differing-numerals.tsv (698 occurrences)
For each lib/A file paired through its run's stage map (stage-pairing.tsv), every numeral token that differs from the
donor's relocated stage-out, with its exact unit line, its position (proof body / statement), and its source:
- twin-row (31): a value port_core's k-run moved, carried in that run's check.tsv / fixed.tsv / review.tsv with a twin
  symbol (code-same / coderef / code-end): verified on the twin by the k-run's own gate.
- AE34-derived (2): A/AE34.v's __asan_memmove length 880 = 220 words, derived from the twin symtab.
- knock-unmoved (665): a value equal to a knock-release value the k-run did not move. 442 sit in a proof body (the build
  checks them) and 223 in a statement / definition position; the statement ones are the hypothesis-position values of
  record 1 (derived there) or are grant-identical after relocation (the first Section g of AFis / AFj6, byte-equal to
  the W4 donor: grant's own relocated values).
No value was changed on the strength of a build alone; none is a STOP.
