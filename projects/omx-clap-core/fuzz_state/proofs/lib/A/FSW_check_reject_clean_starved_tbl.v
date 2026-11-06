(* fs program part, lane CHECKS: the decode table of check_reject_clean_starved's own text (fs.asan 0x82508, 544 bytes),
   for the walk's symbolic runs (FSW_K.v fsw_run_AJU / fsw_run_to_AJU take `table_ok tfibsegs tbl`).
   build_table steps pc + 4 (Reusable/YP02.v:19-22), so the count is in 32-bit words: 136. MEASURED on the pinned fs.asan
   (capstone, RISCV64 + C): the 544 bytes decode to exactly 136 instructions, so the function has no compressed
   instruction and every instruction it executes is a table entry; its calls leave the range.
   Ported from: a working branch 0c8f540c787 lib/A/FSW_crt_tbl.v (the table pattern of RELOC's AB1k.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v FSH_Base.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition crcs_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_reject_clean_starved 136 TEmpty.
Lemma crcs_tbl_eq : crcs_tbl = build_table tfibsegs A_check_reject_clean_starved 136 TEmpty.
Proof. vm_cast_no_check (eq_refl crcs_tbl). Qed.
Lemma crcs_tbl_ok : table_ok tfibsegs crcs_tbl.
Proof. rewrite crcs_tbl_eq. apply build_table_ok0. unfold A_check_reject_clean_starved. lia. Qed.
