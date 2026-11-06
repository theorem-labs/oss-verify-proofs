(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS_I := ImgB.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_77ca0 : bv 32 := 0x000b2597.
Lemma F_77ca0 : fetch_word BSEGS_I (0x77ca0 : word) = Some W_77ca0.
Proof. vm_refl. Qed.
Lemma D_77ca0 : decode_any W_77ca0 = Some (Auipc 11 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ca4 : bv 32 := 0x6e05b583.
Lemma F_77ca4 : fetch_word BSEGS_I (0x77ca4 : word) = Some W_77ca4.
Proof. vm_refl. Qed.
Lemma D_77ca4 : decode_any W_77ca4 = Some (Load SZ8 true 11 11 1760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ca8 : bv 32 := 0x0005b583.
Lemma F_77ca8 : fetch_word BSEGS_I (0x77ca8 : word) = Some W_77ca8.
Proof. vm_refl. Qed.
Lemma D_77ca8 : decode_any W_77ca8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cac : bv 32 := 0xfff58613.
Lemma F_77cac : fetch_word BSEGS_I (0x77cac : word) = Some W_77cac.
Proof. vm_refl. Qed.
Lemma D_77cac : decode_any W_77cac = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cb0 : bv 32 := 0x00c5b6b3.
Lemma F_77cb0 : fetch_word BSEGS_I (0x77cb0 : word) = Some W_77cb0.
Proof. vm_refl. Qed.
Lemma D_77cb0 : decode_any W_77cb0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cb4 : bv 32 := 0xfff68693.
Lemma F_77cb4 : fetch_word BSEGS_I (0x77cb4 : word) = Some W_77cb4.
Proof. vm_refl. Qed.
Lemma D_77cb4 : decode_any W_77cb4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cb8 : bv 32 := 0x00c6f6b3.
Lemma F_77cb8 : fetch_word BSEGS_I (0x77cb8 : word) = Some W_77cb8.
Proof. vm_refl. Qed.
Lemma D_77cb8 : decode_any W_77cb8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cbc : bv 32 := 0x04a6f263.
Lemma F_77cbc : fetch_word BSEGS_I (0x77cbc : word) = Some W_77cbc.
Proof. vm_refl. Qed.
Lemma D_77cbc : decode_any W_77cbc = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cc0 : bv 32 := 0x000b2697.
Lemma F_77cc0 : fetch_word BSEGS_I (0x77cc0 : word) = Some W_77cc0.
Proof. vm_refl. Qed.
Lemma D_77cc0 : decode_any W_77cc0 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cc4 : bv 32 := 0x6c86b683.
Lemma F_77cc4 : fetch_word BSEGS_I (0x77cc4 : word) = Some W_77cc4.
Proof. vm_refl. Qed.
Lemma D_77cc4 : decode_any W_77cc4 = Some (Load SZ8 true 13 13 1736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cc8 : bv 32 := 0x000b2717.
Lemma F_77cc8 : fetch_word BSEGS_I (0x77cc8 : word) = Some W_77cc8.
Proof. vm_refl. Qed.
Lemma D_77cc8 : decode_any W_77cc8 = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ccc : bv 32 := 0x6c873703.
Lemma F_77ccc : fetch_word BSEGS_I (0x77ccc : word) = Some W_77ccc.
Proof. vm_refl. Qed.
Lemma D_77ccc : decode_any W_77ccc = Some (Load SZ8 true 14 14 1736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cd0 : bv 32 := 0x0006b803.
Lemma F_77cd0 : fetch_word BSEGS_I (0x77cd0 : word) = Some W_77cd0.
Proof. vm_refl. Qed.
Lemma D_77cd0 : decode_any W_77cd0 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cd4 : bv 32 := 0x00073683.
Lemma F_77cd4 : fetch_word BSEGS_I (0x77cd4 : word) = Some W_77cd4.
Proof. vm_refl. Qed.
Lemma D_77cd4 : decode_any W_77cd4 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cd8 : bv 32 := 0xfff80793.
Lemma F_77cd8 : fetch_word BSEGS_I (0x77cd8 : word) = Some W_77cd8.
Proof. vm_refl. Qed.
Lemma D_77cd8 : decode_any W_77cd8 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cdc : bv 32 := 0x00a7f463.
Lemma F_77cdc : fetch_word BSEGS_I (0x77cdc : word) = Some W_77cdc.
Proof. vm_refl. Qed.
Lemma D_77cdc : decode_any W_77cdc = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ce0 : bv 32 := 0x02a6f063.
Lemma F_77ce0 : fetch_word BSEGS_I (0x77ce0 : word) = Some W_77ce0.
Proof. vm_refl. Qed.
Lemma D_77ce0 : decode_any W_77ce0 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ce4 : bv 32 := 0x000b2717.
Lemma F_77ce4 : fetch_word BSEGS_I (0x77ce4 : word) = Some W_77ce4.
Proof. vm_refl. Qed.
Lemma D_77ce4 : decode_any W_77ce4 = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ce8 : bv 32 := 0x6b473703.
Lemma F_77ce8 : fetch_word BSEGS_I (0x77ce8 : word) = Some W_77ce8.
Proof. vm_refl. Qed.
Lemma D_77ce8 : decode_any W_77ce8 = Some (Load SZ8 true 14 14 1716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cec : bv 32 := 0x00073283.
Lemma F_77cec : fetch_word BSEGS_I (0x77cec : word) = Some W_77cec.
Proof. vm_refl. Qed.
Lemma D_77cec : decode_any W_77cec = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cf0 : bv 32 := 0x0032d713.
Lemma F_77cf0 : fetch_word BSEGS_I (0x77cf0 : word) = Some W_77cf0.
Proof. vm_refl. Qed.
Lemma D_77cf0 : decode_any W_77cf0 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cf4 : bv 32 := 0x00b708b3.
Lemma F_77cf4 : fetch_word BSEGS_I (0x77cf4 : word) = Some W_77cf4.
Proof. vm_refl. Qed.
Lemma D_77cf4 : decode_any W_77cf4 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cf8 : bv 32 := 0x00a2ea63.
Lemma F_77cf8 : fetch_word BSEGS_I (0x77cf8 : word) = Some W_77cf8.
Proof. vm_refl. Qed.
Lemma D_77cf8 : decode_any W_77cf8 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cfc : bv 32 := 0x00a8f863.
Lemma F_77cfc : fetch_word BSEGS_I (0x77cfc : word) = Some W_77cfc.
Proof. vm_refl. Qed.
Lemma D_77cfc : decode_any W_77cfc = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d00 : bv 32 := 0x00355513.
Lemma F_77d00 : fetch_word BSEGS_I (0x77d00 : word) = Some W_77d00.
Proof. vm_refl. Qed.
Lemma D_77d00 : decode_any W_77d00 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d04 : bv 32 := 0x00a58533.
Lemma F_77d04 : fetch_word BSEGS_I (0x77d04 : word) = Some W_77d04.
Proof. vm_refl. Qed.
Lemma D_77d04 : decode_any W_77d04 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d08 : bv 32 := 0x00008067.
Lemma F_77d08 : fetch_word BSEGS_I (0x77d08 : word) = Some W_77d08.
Proof. vm_refl. Qed.
Lemma D_77d08 : decode_any W_77d08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7812c : bv 32 := 0xfc010113.
Lemma F_7812c : fetch_word BSEGS_I (0x7812c : word) = Some W_7812c.
Proof. vm_refl. Qed.
Lemma D_7812c : decode_any W_7812c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78130 : bv 32 := 0x02113c23.
Lemma F_78130 : fetch_word BSEGS_I (0x78130 : word) = Some W_78130.
Proof. vm_refl. Qed.
Lemma D_78130 : decode_any W_78130 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78134 : bv 32 := 0x02813823.
Lemma F_78134 : fetch_word BSEGS_I (0x78134 : word) = Some W_78134.
Proof. vm_refl. Qed.
Lemma D_78134 : decode_any W_78134 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.
