(* fs program part, lane CHECKS, image B (fs.asan-ubsan): the decode table of fuzz_alloc_live's own text, for walks
   that run through it (lib/B/FSW_K.v fsw_run_AJU takes `table_ok tfibsegs tbl`; build_table on top of a caller's table
   adds these words). The range is lib/B/YB1w.v's names: tfib_A_fuzz_alloc_live = 0x82eec .. tfib_E_fuzz_alloc_live =
   0x82ef8, 12 bytes. build_table steps pc + 4 (Reusable/YP02.v), so the count is in 32-bit words: 3. MEASURED on the
   pinned fs.asan-ubsan (sha256 5ac5ce09...): those 12 bytes decode to exactly 3 instructions, each 4 bytes (capstone,
   RISCV64 + C): `auipc a0, 0x558; ld a0, -0x42c(a0); ret`, a0 := the 8 bytes at 0x5daac0 = lib/B/FSH_Base.v G_LIVE.
   Twin of lib/A/FSW_fuzz_alloc_live_tbl.v (a working branch 3694074f8f1). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition fal_text_start : Z := tfib_A_fuzz_alloc_live.
Definition fal_text_count : nat := Z.to_nat ((tfib_E_fuzz_alloc_live - tfib_A_fuzz_alloc_live) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma fal_text_exact : Z.of_nat fal_text_count * 4 = tfib_E_fuzz_alloc_live - tfib_A_fuzz_alloc_live.
Proof. vm_compute. reflexivity. Qed.

Definition fal_tbl : ctable := Eval vm_compute in (build_table tfibsegs fal_text_start fal_text_count TEmpty).
Lemma fal_tbl_eq : fal_tbl = build_table tfibsegs fal_text_start fal_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl fal_tbl). Qed.
Lemma fal_tbl_ok : table_ok tfibsegs fal_tbl.
Proof. rewrite fal_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* fuzz_alloc_live's words on top of a caller's table *)
Definition fal_tbl_on (t : ctable) : ctable := build_table tfibsegs fal_text_start fal_text_count t.
Lemma fal_tbl_on_ok : forall t, table_ok tfibsegs t -> table_ok tfibsegs (fal_tbl_on t).
Proof. intros t Ht. unfold fal_tbl_on. apply build_table_ok; [cbv; discriminate | exact Ht]. Qed.
