(* The decode table of grow in fs.asan (image tfibsegs), built over its AB1w range [tfib_A_grow, tfib_E_grow) =
   [0x83a48, 0x83be4): 412 bytes, 103 instructions. build_table steps pc + 4: fs.asan has no compressed instruction
   (ELF e_flags 0x4, EF_RISCV_RVC clear; capstone with RVC decoding on finds 0 two-byte instructions in .text, and
   grow's st_size 412 = 4 * 103; a Theorem Labs lane's rvc-check.md). A table only (rule 24: no function
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
Definition grow_ninsn : nat := Z.to_nat ((tfib_E_grow - tfib_A_grow) / 4).
Lemma grow_range : A_grow = tfib_A_grow /\ tfib_E_grow - tfib_A_grow = 412 /\ grow_ninsn = 103%nat.
Proof. split; [|split]; reflexivity. Qed.

Definition grow_tbl : ctable := Eval vm_compute in build_table tfibsegs tfib_A_grow grow_ninsn TEmpty.
Lemma grow_tbl_ok : table_ok tfibsegs grow_tbl.
Proof.
assert (E : grow_tbl = build_table tfibsegs tfib_A_grow grow_ninsn TEmpty) by (vm_cast_no_check (eq_refl grow_tbl)).
rewrite E. apply build_table_ok0. unfold tfib_A_grow. lia.
Qed.
