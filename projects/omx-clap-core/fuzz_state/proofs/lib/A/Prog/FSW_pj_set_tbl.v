(* The decode table of pj_set in fs.asan (image tfibsegs), built over its AB1w range [tfib_A_pj_set, tfib_E_pj_set) =
   [0x838e8, 0x83a48): 352 bytes, 88 instructions. build_table steps pc + 4: fs.asan has no compressed instruction
   (ELF e_flags 0x4, EF_RISCV_RVC clear; capstone with RVC decoding on finds 0 two-byte instructions in .text, and
   pj_set's st_size 352 = 4 * 88; a Theorem Labs lane's rvc-check.md). A table only (rule 24: no function
   proved here). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w FSH_Base.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the AB1w range, in instructions *)
Definition pj_set_ninsn : nat := Z.to_nat ((tfib_E_pj_set - tfib_A_pj_set) / 4).
Lemma pj_set_range : A_pj_set = tfib_A_pj_set /\ tfib_E_pj_set - tfib_A_pj_set = 352 /\ pj_set_ninsn = 88%nat.
Proof. split; [|split]; reflexivity. Qed.

Definition pj_set_tbl : ctable := Eval vm_compute in build_table tfibsegs tfib_A_pj_set pj_set_ninsn TEmpty.
Lemma pj_set_tbl_ok : table_ok tfibsegs pj_set_tbl.
Proof.
assert (E : pj_set_tbl = build_table tfibsegs tfib_A_pj_set pj_set_ninsn TEmpty) by (vm_cast_no_check (eq_refl pj_set_tbl)).
rewrite E. apply build_table_ok0. unfold tfib_A_pj_set. lia.
Qed.
