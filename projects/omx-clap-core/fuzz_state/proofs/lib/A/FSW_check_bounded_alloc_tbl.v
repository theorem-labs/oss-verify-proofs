(* fs program part, lane CHECKS: the decode table of check_bounded_alloc's own text, for the walk's symbolic runs
   (FSW_K.v fsw_run_AJU takes `table_ok tfibsegs tbl`). The range is RELOC's AB1w.v names:
   tfib_A_check_bounded_alloc = 0x81560 .. tfib_E_check_bounded_alloc = 0x81590, 48 bytes. build_table steps pc + 4
   (Reusable/YP02.v), so the count is in 32-bit words: 12. MEASURED on the pinned fs.asan (sha256 64b53ff8...): those
   48 bytes decode to exactly 12 instructions, each 4 bytes (capstone, RISCV64 + C). Pattern: lib/A/FSW_crt_tbl.v (lane
   CRT). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition cba_text_start : Z := tfib_A_check_bounded_alloc.
Definition cba_text_count : nat := Z.to_nat ((tfib_E_check_bounded_alloc - tfib_A_check_bounded_alloc) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma cba_text_exact : Z.of_nat cba_text_count * 4 = tfib_E_check_bounded_alloc - tfib_A_check_bounded_alloc.
Proof. vm_compute. reflexivity. Qed.

Definition cba_tbl : ctable := Eval vm_compute in (build_table tfibsegs cba_text_start cba_text_count TEmpty).
Lemma cba_tbl_eq : cba_tbl = build_table tfibsegs cba_text_start cba_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl cba_tbl). Qed.
Lemma cba_tbl_ok : table_ok tfibsegs cba_tbl.
Proof. rewrite cba_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
