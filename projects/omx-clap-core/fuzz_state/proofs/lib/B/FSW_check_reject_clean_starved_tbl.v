(* fs program part, lane CHECKS, image B (fs.asan-ubsan): the decode table of check_reject_clean_starved's own text
   (fs.asan-ubsan 0x82670 = lib/B/FSH_Base.v A_check_reject_clean_starved, symbol size 548 bytes), for the walk's symbolic
   runs (lib/B/FSW_K.v fsw_run_AJU / fsw_run_to_AJU take `table_ok tfibsegs tbl`).
   build_table steps pc + 4 (Reusable/YP02.v:19-22), so the count is in 32-bit words: 137. MEASURED on the pinned
   fs.asan-ubsan (sha256 5ac5ce0954f8..., capstone 5.0.7, RISCV64 + C; the unstripped twin b1566a1ca816... has the same
   548 bytes): the body decodes to 137 four-byte words, no compressed instruction; the last word 0x82890 is an `unimp`
   after the noreturn `jal abort` at 0x8288c, never executed; the calls leave the range.
   Twin of lib/A/FSW_check_reject_clean_starved_tbl.v (a working branch), same lemma names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition crcs_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_reject_clean_starved 137 TEmpty.
Lemma crcs_tbl_eq : crcs_tbl = build_table tfibsegs A_check_reject_clean_starved 137 TEmpty.
Proof. vm_cast_no_check (eq_refl crcs_tbl). Qed.
Lemma crcs_tbl_ok : table_ok tfibsegs crcs_tbl.
Proof. rewrite crcs_tbl_eq. apply build_table_ok0. unfold A_check_reject_clean_starved. lia. Qed.
