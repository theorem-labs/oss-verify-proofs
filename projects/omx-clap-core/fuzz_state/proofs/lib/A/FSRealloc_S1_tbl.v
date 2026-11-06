(* fuzz_state image A, realloc segment S1 (a Theorem Labs lane, 2026-10-29): WORK IN PROGRESS, NOT YET COMPILED.
   The decode table of the realloc prefix's code, port of cgif_rgb_fuzzer lib/YF77.v (tfxtbl_rr) at fs.asan's addresses
   (capstone over fs.asan sha256 64b53ff86172bb07..., RV64, no compressed instructions):
   - 0x53474, 118 instructions: __interceptor_realloc, 0x53474 `addi sp, sp, -0x7f0` .. 0x53648 `ret`;
   - 0x3287c, 131 instructions: asan_realloc 0x3287c `addi sp, sp, -0x10` .. 0x32924 `ret`, then Allocator::Reallocate
     0x32928 `addi sp, sp, -0x30` .. 0x32a48 `ret` and its CHECK tails to 0x32a84 `jal 0x39678`;
   over tfibtbl_rtA (A/AB1q.v), whose last range 0x31e98 (633 instructions) ends at 0x3287c. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.
Definition tfibtbl_rr_build : ctable := build_table tfibsegs 0x53474 118%nat (build_table tfibsegs 0x3287c 131%nat tfibtbl_rtA).
Definition tfibtbl_rr : ctable := Eval vm_compute in tfibtbl_rr_build.
Lemma tfibtbl_rr_eq : tfibtbl_rr = tfibtbl_rr_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rr). Qed.
Lemma tfibtbl_rr_ok : table_ok tfibsegs tfibtbl_rr.
Proof. rewrite tfibtbl_rr_eq. unfold tfibtbl_rr_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
