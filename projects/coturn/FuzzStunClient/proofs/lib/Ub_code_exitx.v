(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_13ee8 : bv 32 := 0x00023517.
Lemma F_13ee8 : fetch_word Ubsan.M.loaded_segments (0x13ee8 : word) = Some W_13ee8.
Proof. vm_refl. Qed.
Lemma D_13ee8 : decode_any W_13ee8 = Some (Auipc 10 35, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eec : bv 32 := 0xc5c54503.
Lemma F_13eec : fetch_word Ubsan.M.loaded_segments (0x13eec : word) = Some W_13eec.
Proof. vm_refl. Qed.
Lemma D_13eec : decode_any W_13eec = Some (Load SZ1 false 10 10 3164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef0 : bv 32 := 0x00051463.
Lemma F_13ef0 : fetch_word Ubsan.M.loaded_segments (0x13ef0 : word) = Some W_13ef0.
Proof. vm_refl. Qed.
Lemma D_13ef0 : decode_any W_13ef0 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef4 : bv 32 := 0x00008067.
Lemma F_13ef4 : fetch_word Ubsan.M.loaded_segments (0x13ef4 : word) = Some W_13ef4.
Proof. vm_refl. Qed.
Lemma D_13ef4 : decode_any W_13ef4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf0 : bv 32 := 0x00892583.
Lemma F_1bdf0 : fetch_word Ubsan.M.loaded_segments (0x1bdf0 : word) = Some W_1bdf0.
Proof. vm_refl. Qed.
Lemma D_1bdf0 : decode_any W_1bdf0 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf4 : bv 32 := 0x0180006f.
Lemma F_1bdf4 : fetch_word Ubsan.M.loaded_segments (0x1bdf4 : word) = Some W_1bdf4.
Proof. vm_refl. Qed.
Lemma D_1bdf4 : decode_any W_1bdf4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf8 : bv 32 := 0x00053503.
Lemma F_1bdf8 : fetch_word Ubsan.M.loaded_segments (0x1bdf8 : word) = Some W_1bdf8.
Proof. vm_refl. Qed.
Lemma D_1bdf8 : decode_any W_1bdf8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdfc : bv 32 := 0x02000593.
Lemma F_1bdfc : fetch_word Ubsan.M.loaded_segments (0x1bdfc : word) = Some W_1bdfc.
Proof. vm_refl. Qed.
Lemma D_1bdfc : decode_any W_1bdfc = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be00 : bv 32 := 0x00b92423.
Lemma F_1be00 : fetch_word Ubsan.M.loaded_segments (0x1be00 : word) = Some W_1be00.
Proof. vm_refl. Qed.
Lemma D_1be00 : decode_any W_1be00 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be04 : bv 32 := 0x00a93823.
Lemma F_1be04 : fetch_word Ubsan.M.loaded_segments (0x1be04 : word) = Some W_1be04.
Proof. vm_refl. Qed.
Lemma D_1be04 : decode_any W_1be04 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be08 : bv 32 := 0x04050a63.
Lemma F_1be08 : fetch_word Ubsan.M.loaded_segments (0x1be08 : word) = Some W_1be08.
Proof. vm_refl. Qed.
Lemma D_1be08 : decode_any W_1be08 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be0c : bv 32 := 0xfff5861b.
Lemma F_1be0c : fetch_word Ubsan.M.loaded_segments (0x1be0c : word) = Some W_1be0c.
Proof. vm_refl. Qed.
Lemma D_1be0c : decode_any W_1be0c = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be10 : bv 32 := 0x00c92423.
Lemma F_1be10 : fetch_word Ubsan.M.loaded_segments (0x1be10 : word) = Some W_1be10.
Proof. vm_refl. Qed.
Lemma D_1be10 : decode_any W_1be10 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be14 : bv 32 := 0xfeb052e3.
Lemma F_1be14 : fetch_word Ubsan.M.loaded_segments (0x1be14 : word) = Some W_1be14.
Proof. vm_refl. Qed.
Lemma D_1be14 : decode_any W_1be14 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be18 : bv 32 := 0x01093503.
Lemma F_1be18 : fetch_word Ubsan.M.loaded_segments (0x1be18 : word) = Some W_1be18.
Proof. vm_refl. Qed.
Lemma D_1be18 : decode_any W_1be18 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be1c : bv 32 := 0x00361613.
Lemma F_1be1c : fetch_word Ubsan.M.loaded_segments (0x1be1c : word) = Some W_1be1c.
Proof. vm_refl. Qed.
Lemma D_1be1c : decode_any W_1be1c = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be20 : bv 32 := 0x00c50533.
Lemma F_1be20 : fetch_word Ubsan.M.loaded_segments (0x1be20 : word) = Some W_1be20.
Proof. vm_refl. Qed.
Lemma D_1be20 : decode_any W_1be20 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be24 : bv 32 := 0x00853983.
Lemma F_1be24 : fetch_word Ubsan.M.loaded_segments (0x1be24 : word) = Some W_1be24.
Proof. vm_refl. Qed.
Lemma D_1be24 : decode_any W_1be24 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be28 : bv 32 := 0x10853483.
Lemma F_1be28 : fetch_word Ubsan.M.loaded_segments (0x1be28 : word) = Some W_1be28.
Proof. vm_refl. Qed.
Lemma D_1be28 : decode_any W_1be28 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be2c : bv 32 := 0x00040513.
Lemma F_1be2c : fetch_word Ubsan.M.loaded_segments (0x1be2c : word) = Some W_1be2c.
Proof. vm_refl. Qed.
Lemma D_1be2c : decode_any W_1be2c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be30 : bv 32 := 0x680080ef.
Lemma F_1be30 : fetch_word Ubsan.M.loaded_segments (0x1be30 : word) = Some W_1be30.
Proof. vm_refl. Qed.
Lemma D_1be30 : decode_any W_1be30 = Some (Jal 1 34432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be34 : bv 32 := 0x00048513.
Lemma F_1be34 : fetch_word Ubsan.M.loaded_segments (0x1be34 : word) = Some W_1be34.
Proof. vm_refl. Qed.
Lemma D_1be34 : decode_any W_1be34 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be38 : bv 32 := 0x000980e7.
Lemma F_1be38 : fetch_word Ubsan.M.loaded_segments (0x1be38 : word) = Some W_1be38.
Proof. vm_refl. Qed.
Lemma D_1be38 : decode_any W_1be38 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be3c : bv 32 := 0x00040513.
Lemma F_1be3c : fetch_word Ubsan.M.loaded_segments (0x1be3c : word) = Some W_1be3c.
Proof. vm_refl. Qed.
Lemma D_1be3c : decode_any W_1be3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be40 : bv 32 := 0x3e8080ef.
Lemma F_1be40 : fetch_word Ubsan.M.loaded_segments (0x1be40 : word) = Some W_1be40.
Proof. vm_refl. Qed.
Lemma D_1be40 : decode_any W_1be40 = Some (Jal 1 33768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be44 : bv 32 := 0x00892503.
Lemma F_1be44 : fetch_word Ubsan.M.loaded_segments (0x1be44 : word) = Some W_1be44.
Proof. vm_refl. Qed.
Lemma D_1be44 : decode_any W_1be44 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be48 : bv 32 := 0xfff5061b.
Lemma F_1be48 : fetch_word Ubsan.M.loaded_segments (0x1be48 : word) = Some W_1be48.
Proof. vm_refl. Qed.
Lemma D_1be48 : decode_any W_1be48 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be4c : bv 32 := 0x00c92423.
Lemma F_1be4c : fetch_word Ubsan.M.loaded_segments (0x1be4c : word) = Some W_1be4c.
Proof. vm_refl. Qed.
Lemma D_1be4c : decode_any W_1be4c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be50 : bv 32 := 0xfca044e3.
Lemma F_1be50 : fetch_word Ubsan.M.loaded_segments (0x1be50 : word) = Some W_1be50.
Proof. vm_refl. Qed.
Lemma D_1be50 : decode_any W_1be50 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be54 : bv 32 := 0x01093503.
Lemma F_1be54 : fetch_word Ubsan.M.loaded_segments (0x1be54 : word) = Some W_1be54.
Proof. vm_refl. Qed.
Lemma D_1be54 : decode_any W_1be54 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be58 : bv 32 := 0xfa1ff06f.
Lemma F_1be58 : fetch_word Ubsan.M.loaded_segments (0x1be58 : word) = Some W_1be58.
Proof. vm_refl. Qed.
Lemma D_1be58 : decode_any W_1be58 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf4c : bv 32 := 0x00050067.
Lemma F_1bf4c : fetch_word Ubsan.M.loaded_segments (0x1bf4c : word) = Some W_1bf4c.
Proof. vm_refl. Qed.
Lemma D_1bf4c : decode_any W_1bf4c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.
