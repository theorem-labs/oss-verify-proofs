(* Modified by Theorem Labs, 2026-10: from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S1_tbl.v (commit ddc081c1a03, fuzz_state's realloc segment S1; file sha256 242ff2b140b9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair_fs.py; 0 code pcs the tool read as sizes, by funcpair_fs.py), and 12 pcs named in comments; no other numeral changed. *)
(* Provenance: in the header prose, 1 instruction immediate quoted in the prose (jal / auipc / lw) restated from fuzz_reply.asan's own instruction words. *)
(* fuzz_state image A, realloc segment S1 (RtS1, 2026-10-29): WORK IN PROGRESS, NOT YET COMPILED.
   The decode table of the realloc prefix's code, port of cgif_rgb_fuzzer lib/YF77.v (tfxtbl_rr) at fs.asan's addresses
   (capstone over fs.asan sha256 64b53ff86172bb07..., RV64, no compressed instructions):
   - 0x541ec, 118 instructions: __interceptor_realloc, 0x541ec `addi sp, sp, -0x7f0` .. 0x543c0 `ret`;
   - 0x32560, 131 instructions: asan_realloc 0x32560 `addi sp, sp, -0x10` .. 0x32608 `ret`, then Allocator::Reallocate
     0x3260c `addi sp, sp, -0x30` .. 0x3272c `ret` and its CHECK tails to 0x32768 `jal 0x3ad64`;
   over tfibtbl_rtA (A/AB1q.v), whose last range 0x31b7c (633 instructions) ends at 0x32560. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rr_build : ctable := build_table tfibsegs 0x541ec 118%nat (build_table tfibsegs 0x32560 131%nat tfibtbl_rtA).
Definition tfibtbl_rr : ctable := Eval vm_compute in tfibtbl_rr_build.
Lemma tfibtbl_rr_eq : tfibtbl_rr = tfibtbl_rr_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rr). Qed.
Lemma tfibtbl_rr_ok : table_ok tfibsegs tfibtbl_rr.
Proof. rewrite tfibtbl_rr_eq. unfold tfibtbl_rr_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
