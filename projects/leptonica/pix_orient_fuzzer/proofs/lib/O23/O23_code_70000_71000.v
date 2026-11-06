(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_70d8c : bv 32 := 0xfe010113.
Lemma F_70d8c : fetch_word Plain.M.loaded_segments (0x70de4 : word) = Some W_70d8c.
Proof. vm_refl. Qed.
Lemma D_70d8c : decode_any W_70d8c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70d90 : bv 32 := 0x00113c23.
Lemma F_70d90 : fetch_word Plain.M.loaded_segments (0x70de8 : word) = Some W_70d90.
Proof. vm_refl. Qed.
Lemma D_70d90 : decode_any W_70d90 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70d94 : bv 32 := 0x00813823.
Lemma F_70d94 : fetch_word Plain.M.loaded_segments (0x70dec : word) = Some W_70d94.
Proof. vm_refl. Qed.
Lemma D_70d94 : decode_any W_70d94 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70d98 : bv 32 := 0x00913423.
Lemma F_70d98 : fetch_word Plain.M.loaded_segments (0x70df0 : word) = Some W_70d98.
Proof. vm_refl. Qed.
Lemma D_70d98 : decode_any W_70d98 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70d9c : bv 32 := 0x06050463.
Lemma F_70d9c : fetch_word Plain.M.loaded_segments (0x70df4 : word) = Some W_70d9c.
Proof. vm_refl. Qed.
Lemma D_70d9c : decode_any W_70d9c = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70da0 : bv 32 := 0x00050413.
Lemma F_70da0 : fetch_word Plain.M.loaded_segments (0x70df8 : word) = Some W_70da0.
Proof. vm_refl. Qed.
Lemma D_70da0 : decode_any W_70da0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70da4 : bv 32 := 0x00410613.
Lemma F_70da4 : fetch_word Plain.M.loaded_segments (0x70dfc : word) = Some W_70da4.
Proof. vm_refl. Qed.
Lemma D_70da4 : decode_any W_70da4 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70da8 : bv 32 := 0x00000593.
Lemma F_70da8 : fetch_word Plain.M.loaded_segments (0x70e00 : word) = Some W_70da8.
Proof. vm_refl. Qed.
Lemma D_70da8 : decode_any W_70da8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dac : bv 32 := 0x0dc000ef.
Lemma F_70dac : fetch_word Plain.M.loaded_segments (0x70e04 : word) = Some W_70dac.
Proof. vm_refl. Qed.
Lemma D_70dac : decode_any W_70dac = Some (Jal 1 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70db0 : bv 32 := 0x00412503.
Lemma F_70db0 : fetch_word Plain.M.loaded_segments (0x70e08 : word) = Some W_70db0.
Proof. vm_refl. Qed.
Lemma D_70db0 : decode_any W_70db0 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70db4 : bv 32 := 0x08050663.
Lemma F_70db4 : fetch_word Plain.M.loaded_segments (0x70e0c : word) = Some W_70db4.
Proof. vm_refl. Qed.
Lemma D_70db4 : decode_any W_70db4 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70db8 : bv 32 := 0x00100513.
Lemma F_70db8 : fetch_word Plain.M.loaded_segments (0x70e10 : word) = Some W_70db8.
Proof. vm_refl. Qed.
Lemma D_70db8 : decode_any W_70db8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dbc : bv 32 := 0x01800593.
Lemma F_70dbc : fetch_word Plain.M.loaded_segments (0x70e14 : word) = Some W_70dbc.
Proof. vm_refl. Qed.
Lemma D_70dbc : decode_any W_70dbc = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dc0 : bv 32 := 0x424890ef.
Lemma F_70dc0 : fetch_word Plain.M.loaded_segments (0x70e18 : word) = Some W_70dc0.
Proof. vm_refl. Qed.
Lemma D_70dc0 : decode_any W_70dc0 = Some (Jal 1 562212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dc4 : bv 32 := 0x00050493.
Lemma F_70dc4 : fetch_word Plain.M.loaded_segments (0x70e1c : word) = Some W_70dc4.
Proof. vm_refl. Qed.
Lemma D_70dc4 : decode_any W_70dc4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dc8 : bv 32 := 0x00c42503.
Lemma F_70dc8 : fetch_word Plain.M.loaded_segments (0x70e20 : word) = Some W_70dc8.
Proof. vm_refl. Qed.
Lemma D_70dc8 : decode_any W_70dc8 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dcc : bv 32 := 0x0025159b.
Lemma F_70dcc : fetch_word Plain.M.loaded_segments (0x70e24 : word) = Some W_70dcc.
Proof. vm_refl. Qed.
Lemma D_70dcc : decode_any W_70dcc = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dd0 : bv 32 := 0x00100513.
Lemma F_70dd0 : fetch_word Plain.M.loaded_segments (0x70e28 : word) = Some W_70dd0.
Proof. vm_refl. Qed.
Lemma D_70dd0 : decode_any W_70dd0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dd4 : bv 32 := 0x410890ef.
Lemma F_70dd4 : fetch_word Plain.M.loaded_segments (0x70e2c : word) = Some W_70dd4.
Proof. vm_refl. Qed.
Lemma D_70dd4 : decode_any W_70dd4 = Some (Jal 1 562192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dd8 : bv 32 := 0x00a4b023.
Lemma F_70dd8 : fetch_word Plain.M.loaded_segments (0x70e30 : word) = Some W_70dd8.
Proof. vm_refl. Qed.
Lemma D_70dd8 : decode_any W_70dd8 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70ddc : bv 32 := 0x01042603.
Lemma F_70ddc : fetch_word Plain.M.loaded_segments (0x70e34 : word) = Some W_70ddc.
Proof. vm_refl. Qed.
Lemma D_70ddc : decode_any W_70ddc = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70de0 : bv 32 := 0x00043583.
Lemma F_70de0 : fetch_word Plain.M.loaded_segments (0x70e38 : word) = Some W_70de0.
Proof. vm_refl. Qed.
Lemma D_70de0 : decode_any W_70de0 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70de4 : bv 32 := 0x00261613.
Lemma F_70de4 : fetch_word Plain.M.loaded_segments (0x70e3c : word) = Some W_70de4.
Proof. vm_refl. Qed.
Lemma D_70de4 : decode_any W_70de4 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70de8 : bv 32 := 0x671980ef.
Lemma F_70de8 : fetch_word Plain.M.loaded_segments (0x70e40 : word) = Some W_70de8.
Proof. vm_refl. Qed.
Lemma D_70de8 : decode_any W_70de8 = Some (Jal 1 626288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dec : bv 32 := 0x00048513.
Lemma F_70dec : fetch_word Plain.M.loaded_segments (0x70e44 : word) = Some W_70dec.
Proof. vm_refl. Qed.
Lemma D_70dec : decode_any W_70dec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70df0 : bv 32 := 0x01042583.
Lemma F_70df0 : fetch_word Plain.M.loaded_segments (0x70e48 : word) = Some W_70df0.
Proof. vm_refl. Qed.
Lemma D_70df0 : decode_any W_70df0 = Some (Load SZ4 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70df4 : bv 32 := 0x00b4a823.
Lemma F_70df4 : fetch_word Plain.M.loaded_segments (0x70e4c : word) = Some W_70df4.
Proof. vm_refl. Qed.
Lemma D_70df4 : decode_any W_70df4 = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70df8 : bv 32 := 0x00843583.
Lemma F_70df8 : fetch_word Plain.M.loaded_segments (0x70e50 : word) = Some W_70df8.
Proof. vm_refl. Qed.
Lemma D_70df8 : decode_any W_70df8 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70dfc : bv 32 := 0x00b4b423.
Lemma F_70dfc : fetch_word Plain.M.loaded_segments (0x70e54 : word) = Some W_70dfc.
Proof. vm_refl. Qed.
Lemma D_70dfc : decode_any W_70dfc = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e00 : bv 32 := 0x0740006f.
Lemma F_70e00 : fetch_word Plain.M.loaded_segments (0x70e58 : word) = Some W_70e00.
Proof. vm_refl. Qed.
Lemma D_70e00 : decode_any W_70e00 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e74 : bv 32 := 0x01813083.
Lemma F_70e74 : fetch_word Plain.M.loaded_segments (0x70ecc : word) = Some W_70e74.
Proof. vm_refl. Qed.
Lemma D_70e74 : decode_any W_70e74 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e78 : bv 32 := 0x01013403.
Lemma F_70e78 : fetch_word Plain.M.loaded_segments (0x70ed0 : word) = Some W_70e78.
Proof. vm_refl. Qed.
Lemma D_70e78 : decode_any W_70e78 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e7c : bv 32 := 0x00813483.
Lemma F_70e7c : fetch_word Plain.M.loaded_segments (0x70ed4 : word) = Some W_70e7c.
Proof. vm_refl. Qed.
Lemma D_70e7c : decode_any W_70e7c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e80 : bv 32 := 0x02010113.
Lemma F_70e80 : fetch_word Plain.M.loaded_segments (0x70ed8 : word) = Some W_70e80.
Proof. vm_refl. Qed.
Lemma D_70e80 : decode_any W_70e80 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e84 : bv 32 := 0x00008067.
Lemma F_70e84 : fetch_word Plain.M.loaded_segments (0x70edc : word) = Some W_70e84.
Proof. vm_refl. Qed.
Lemma D_70e84 : decode_any W_70e84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
