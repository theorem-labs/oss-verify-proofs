(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S1_tbl.v (hub ddc081c1a03, blob f434810b61d6) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), every image numeral moved by symbol + offset; it compiles on image A; record, the internal file A5.md. *)
(* fuzz_state image A, realloc segment S1 (RtS1, 2026-10-29).
   The decode table of the realloc prefix's code, port of cgif_rgb_fuzzer lib/YF77.v (tfxtbl_rr) at fs.asan's addresses
   (capstone over fs.asan sha256 64b53ff86172bb07..., RV64, no compressed instructions):
   - 0x53b38, 118 instructions: __interceptor_realloc, 0x53b38 `addi sp, sp, -0x7f0` .. 0x53d0c `ret`;
   - 0x32f40, 131 instructions: asan_realloc 0x32f40 `addi sp, sp, -0x10` .. 0x32fe8 `ret`, then Allocator::Reallocate
     0x32fec `addi sp, sp, -0x30` .. 0x3310c `ret` and its CHECK tails to 0x33148 `jal 0x39d3c`;
   over tfibtbl_rtA (A/AB1q.v), whose last range 0x3255c (633 instructions) ends at 0x32f40. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rr_build : ctable := build_table tfibsegs 0x53b38 118%nat (build_table tfibsegs 0x32f40 131%nat tfibtbl_rtA).
Definition tfibtbl_rr : ctable := Eval vm_compute in tfibtbl_rr_build.
Lemma tfibtbl_rr_eq : tfibtbl_rr = tfibtbl_rr_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rr). Qed.
Lemma tfibtbl_rr_ok : table_ok tfibsegs tfibtbl_rr.
Proof. rewrite tfibtbl_rr_eq. unfold tfibtbl_rr_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
