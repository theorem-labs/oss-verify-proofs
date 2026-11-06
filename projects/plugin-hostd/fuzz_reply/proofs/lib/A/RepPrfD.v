(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepPrfD.v (commit f01d79f3fb5, cf refill round 3; file sha256 0a8172a7e453) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 7 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 7 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (accept.tsv, re-measured each run): _ZN11__sanitizer9VSNPrintfEPciPKcPv+0x1c0 (data-differs: ACCEPTED by hand: jump table (33 entries, each the same VSNPrintf+off on both images))), and 13 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane's report walk, slice F2): the decode table of __sanitizer::Printf's silent
   path at cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605).  tfibtbl_rtD (YB1q.v:28) already covers
   VSNPrintf .. AppendNumber (0x67fbc, 756 words: __sanitizer_on_print 0x68580, Printf 0x68584, SharedPrintfCode
   0x685d0) and internal_memset 0x65204; reptbl adds the words the walk executes past them:
   SharedPrintfCodeNoBuffer 0x68b8c (88 words, to its ret 0x68ce8), RawWrite 0x620b8 (14), internal_strlen 0x65358
   (7), ReportFile::Write's silent head 0x67c88 (4), RemoveANSIEscapeSequencesFromString 0x6158c (40), LogMessageOnPrintf
   0x6ec84 (6), UnmapOrDie 0x67254 (26).  The counts were read from the image bytes (a Theorem Labs lane's rvdis.py).
   rule 24: no function proved here (kind: decode table). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition reptbl_build : ctable :=
  build_table tfibsegs 0x68b8c 88%nat (build_table tfibsegs 0x620b8 14%nat (build_table tfibsegs 0x65358 7%nat
  (build_table tfibsegs 0x67c88 4%nat (build_table tfibsegs 0x6158c 40%nat (build_table tfibsegs 0x6ec84 6%nat
  (build_table tfibsegs 0x67254 26%nat tfibtbl_rtD)))))).
Definition reptbl : ctable := Eval vm_compute in reptbl_build.
Lemma reptbl_eq : reptbl = reptbl_build.
Proof. vm_cast_no_check (@eq_refl ctable reptbl). Qed.
Lemma reptbl_ok : table_ok tfibsegs reptbl.
Proof. rewrite reptbl_eq. unfold reptbl_build. do 7 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtD_ok. Qed.
