# fuzz_wire: the FILE sink is option-typed, and YH03 loses the cgif FILE-sink cells

Code commits before BASE:

1. 21a12f93ff3: file_sink_syms and sk_file : option file_sink_syms in lib/Reusable/YI14.v, env_ivl in YL03.v, and src0_sink
   with sk_file := None in YI5c.v (lib/Reusable and lib/U/Reusable). YI14.v and YL03.v are libreac/fuzz_grant's files
   at 197e1eccfcd with module paths changed and without the comment lines grant added or reworded (libreac/fuzz_knock
   e4ef51a4690 form). YI5c.v carries grant's hunks on this unit's file and keeps its own bounds. New YI5cSat.v (both
   copies) is grant's 4ee60a453489 file with module paths changed and cs_env_addr_range's bound set to this unit's
   src0_env_addr_range. Item 7 deletes both copies again.
2. 5dc55e235e5: in lib/Reusable/YH03.v and lib/U/Reusable/YH03.v, src0_D_str_wb (0x102a2), src0_D_str_tmp_out_gif (0x10304),
   src0_D_str_3 (0x10311) and src0_D_str_rwa (0x102ed) are deleted (libreac/fuzz_grant e6d75498860 form), then
   `yh03regen.py --pinned --elf --proofs --write` (sha256 prefix 1254e5c96a44) removes src0_A_stdio_read (ABSENT: the
   image links no __stdio_read).
3. 8b420399cf8c (review): YI14.v's comment above closed_stdio_env is the base's text again (the port had carried the
   donor's rewording), and YH03.v loses the
   comment line yh03regen left behind.
4. 167c590ef1b8: lib/Reusable/YK1a.v:901, :907, :911, :917, two Aborted jalr self-tests (no theorem, no reader), hold the
   donor's model constant 0x20000 again; the relocation had moved it as an address. The file now equals
   libreac/fuzz_decode's (25e3d17bdb50) except for module paths.
5. a8248a48a2c5: src0_A_stdio_write / _seek / _close stay in YH03.v (commit 3 had also deleted them): they are present and true
   in this unit's images, with 0 readers; the series removes only ABSENT or FALSE unread cells. YH03.v:5 then said the file
   keeps only the definitions the unit uses, which did not hold for these three; a later commit of the series rewrote
   that line to name them as kept though unread.
6. 4f4da94a3b6a: lib/Lib/Acfg.v is the shared clean-room restatement, taken byte-equal (blob 856bba129dff, sha256
   e593ed06c2e910bd93735dae0be5ea136cfeba1b501f358b0ee77af47b3858a5). A later commit of the series (c60f89d18849) takes the
   next version of that shared file, again byte-equal by its object id: blob f6823e3203523bd010870ce2a6fcba0a107f2c97
   (sha256 52757821ba5f), which changes two comment lines (:631 and :667) that their proofs did not derive.
7. 05336ebfc612: lib/Reusable/YI5cSat.v and lib/U/Reusable/YI5cSat.v (added by item 1) are deleted: no .v file of the
   unit requires them and no top depends on them, so the series head has no YI5cSat.v.
8. b96006e5d59f: lib/Reusable/R/Cfg.v is the shared clean-room restatement, taken byte-equal (blob ccff5f969374, sha256
   f50add21a0613ed380d2fc6e09d562116e1550b02170884858962aaa4857623b); lib/U/Reusable/R/Cfg.v is unchanged.

Why: the old src0_sink named cgif's FILE sink (stdio read / write / seek / close, "/tmp/out.gif", "wb", ";", "rwa").
This unit's images (plain c8763dfc4e81, ubsan 6e91fe0b5555) have no __stdio_read, and at 0x102a2 / 0x10304 / 0x10311 / 0x102ed they hold
a printf flag string, "", and parts of "len overruns input" / "ut >= %u bytes, refused", not those strings. No proof
of the unit uses sink_at, file_at, stdio_env, fopen_spec, unlink_spec, file_sink_syms or sk_file outside YI14 / YI5c /
YL03 / YI5cSat (callsites.tsv: sink-file-use 0 uses in 0 files; sink-syms-use 111 uses in 61 files; src0-sink-use 29 uses in 23 files; env-addr-reader 8 uses in 2 files; env-of-st-ok 264 uses in 60 files; env-check 132 uses in 60 files). The users of the restated sink_syms record and of src0_sink read only the fields
that stay (sk_ofl_lock, sk_ofl_head, sk_threaded, sk_highs_addr, sk_ones_addr); the build compiles every one. These counts were
taken before item 7; they exclude YI5cSat.v, so its deletion does not change them.

Checks:
- yh03check.py (sha256 prefix fb3bfbc1eea8) --pinned, each image against its own pin and twin: # self-test: 223 known answers OK (yh03regen 163 + yh03check 60); # rows checked: 30; rows not OK: 0 (both copies).
  Before the commits: 31 rows, 1 not OK (src0_A_stdio_read).
- Whole-unit build without cache (CACHE=none, fresh) of the series tree (old layout, same bytes): rc 0, 1233 of 1233 files compiled, 0 failed,
  the 4 pinned binaries matched.
- Print Assumptions of plain_halts, ubsan_halts and ubsan_agrees: 15 axioms each, all on the allowed list, the same set
  as the shipped release check (PrimInt63 / PrimString / PrimArray primitives, functional_extensionality_dep,
  Classical_Prop.classic).
- L2 layout: the whole-unit build without cache of 4f4da94a3b6a (item 6; cb d02a58a345b9, the unit's L2 base build): rc 0,
  1233 files compiled, 0 failed, the 4 pinned binaries matched; the build of 05336ebfc612 (item 7) on that tree: rc 0,
  nothing to recompile. On that tree, the Print Assumptions output (assumptions.out) of plain_halts, ubsan_halts and
  ubsan_agrees is byte-equal to the pre-series release's, the same file for all three tops (item 8 is not in that tree): sha256
  d0a538d26101ede968a64d67ea6f7ea33908754e40a174a54c535542d8a11f75.
- The relocation gate on the series tree: ../gate/GATE.md.

Verbatim outputs: yh03check the internal record of the series (named in the pull request body), file sinkfix/yh03check-plain.out, sha256 977af2e45ea286831bbee6de1c8b326fe538d5c699a55cda425c584321b887b8 and the internal record of the series (named in the pull request body), file sinkfix/yh03check-ubsan.out, sha256 d3aadf21de82b9005d3ca62ed95f43bc5f865dd8ff3198f716542e83e3988857; build log tail the internal record of the series (named in the pull request body), file sinkfix/build-fresh.log.tail, sha256 d1afb690a0518982dd41ea448936ce8c20f5c30b14f2cb32916e4e24c33db860.
