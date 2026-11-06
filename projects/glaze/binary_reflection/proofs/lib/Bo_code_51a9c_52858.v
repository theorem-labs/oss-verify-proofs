(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
From OSSVerify.Proofs.glaze.binary_reflection.lib.Common Require InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_51aa0 : bv 32 := @BV 32 0x02852583%Z I.
Lemma F_51aa0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51aa0%Z I : word) = Some W_51aa0.
Proof. vm_refl. Qed.
Lemma D_51aa0 : decode_any W_51aa0 = Some (Load SZ4 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51aa4 : bv 32 := @BV 32 0x0c05c263%Z I.
Lemma F_51aa4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51aa4%Z I : word) = Some W_51aa4.
Proof. vm_refl. Qed.
Lemma D_51aa4 : decode_any W_51aa4 = Some (Branch BC_LT (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 196%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ad4 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_51ad4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51ad4%Z I : word) = Some W_51ad4.
Proof. vm_refl. Qed.
Lemma D_51ad4 : decode_any W_51ad4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ad8 : bv 32 := @BV 32 0xf7dff06f%Z I.
Lemma F_51ad8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51ad8%Z I : word) = Some W_51ad8.
Proof. vm_refl. Qed.
Lemma D_51ad8 : decode_any W_51ad8 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097020%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b68 : bv 32 := @BV 32 0x00000a13%Z I.
Lemma F_51b68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51b68%Z I : word) = Some W_51b68.
Proof. vm_refl. Qed.
Lemma D_51b68 : decode_any W_51b68 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b6c : bv 32 := @BV 32 0xd7dff06f%Z I.
Lemma F_51b6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51b6c%Z I : word) = Some W_51b6c.
Proof. vm_refl. Qed.
Lemma D_51b6c : decode_any W_51b6c = Some (Jal (@BV 5 0%Z I) (@BV 21 2096508%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bb4 : bv 32 := @BV 32 0xff010113%Z I.

Lemma D_51bb4 : decode_any W_51bb4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bb8 : bv 32 := @BV 32 0x00113423%Z I.

Lemma D_51bb8 : decode_any W_51bb8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bbc : bv 32 := @BV 32 0x02051693%Z I.

Lemma D_51bbc : decode_any W_51bbc = Some (ShiftImm ALU_SLL (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bc0 : bv 32 := @BV 32 0x00f00593%Z I.

Lemma D_51bc0 : decode_any W_51bc0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bc4 : bv 32 := @BV 32 0x0206d693%Z I.

Lemma D_51bc4 : decode_any W_51bc4 = Some (ShiftImm ALU_SRL (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bc8 : bv 32 := @BV 32 0x06a5f663%Z I.

Lemma D_51bc8 : decode_any W_51bc8 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 108%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bcc : bv 32 := @BV 32 0x000015b7%Z I.

Lemma D_51bcc : decode_any W_51bcc = Some (Lui (@BV 5 11%Z I) (@BV 20 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bd0 : bv 32 := @BV 32 0x8015859b%Z I.

Lemma D_51bd0 : decode_any W_51bd0 = Some (OpImm32 (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2049%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bd4 : bv 32 := @BV 32 0x06b57e63%Z I.

Lemma D_51bd4 : decode_any W_51bd4 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bd8 : bv 32 := @BV 32 0xfff68593%Z I.

Lemma D_51bd8 : decode_any W_51bd8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bdc : bv 32 := @BV 32 0x00b6f5b3%Z I.

Lemma D_51bdc : decode_any W_51bdc = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51be0 : bv 32 := @BV 32 0x08059863%Z I.

Lemma D_51be0 : decode_any W_51be0 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51be4 : bv 32 := @BV 32 0x40d005b3%Z I.

Lemma D_51be4 : decode_any W_51be4 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51be8 : bv 32 := @BV 32 0xfffbf617%Z I.
Lemma F_51be8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51be8%Z I : word) = Some W_51be8.
Proof. vm_refl. Qed.
Lemma D_51be8 : decode_any W_51be8 = Some (Auipc (@BV 5 12%Z I) (@BV 20 1048511%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bec : bv 32 := @BV 32 0x8a063603%Z I.
Lemma F_51bec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51bec%Z I : word) = Some W_51bec.
Proof. vm_refl. Qed.
Lemma D_51bec : decode_any W_51bec = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 2208%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bf0 : bv 32 := @BV 32 0xfffbf717%Z I.
Lemma F_51bf0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51bf0%Z I : word) = Some W_51bf0.
Proof. vm_refl. Qed.
Lemma D_51bf0 : decode_any W_51bf0 = Some (Auipc (@BV 5 14%Z I) (@BV 20 1048511%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bf4 : bv 32 := @BV 32 0x00b6f5b3%Z I.

Lemma D_51bf4 : decode_any W_51bf4 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bf8 : bv 32 := @BV 32 0xa0870713%Z I.
Lemma F_51bf8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x51bf8%Z I : word) = Some W_51bf8.
Proof. vm_refl. Qed.
Lemma D_51bf8 : decode_any W_51bf8 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 2568%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bfc : bv 32 := @BV 32 0x02c585b3%Z I.

Lemma D_51bfc : decode_any W_51bfc = Some (Mul M_MUL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c00 : bv 32 := @BV 32 0x03a5d593%Z I.

Lemma D_51c00 : decode_any W_51c00 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 58%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c04 : bv 32 := @BV 32 0x00b705b3%Z I.

Lemma D_51c04 : decode_any W_51c04 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 14%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c08 : bv 32 := @BV 32 0x0005c603%Z I.

Lemma D_51c08 : decode_any W_51c08 = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c0c : bv 32 := @BV 32 0xffc60593%Z I.

Lemma D_51c0c : decode_any W_51c0c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c10 : bv 32 := @BV 32 0x00800713%Z I.

Lemma D_51c10 : decode_any W_51c10 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c14 : bv 32 := @BV 32 0x06e5fe63%Z I.

Lemma D_51c14 : decode_any W_51c14 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 14%Z I) (@BV 13 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c18 : bv 32 := @BV 32 0x00100713%Z I.

Lemma D_51c18 : decode_any W_51c18 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c1c : bv 32 := @BV 32 0x00c7173b%Z I.

Lemma D_51c1c : decode_any W_51c1c = Some (Op32 ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c20 : bv 32 := @BV 32 0x08e51a63%Z I.

Lemma D_51c20 : decode_any W_51c20 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 14%Z I) (@BV 13 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c24 : bv 32 := @BV 32 0x00058513%Z I.

Lemma D_51c24 : decode_any W_51c24 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c28 : bv 32 := @BV 32 0x00813083%Z I.

Lemma D_51c28 : decode_any W_51c28 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c2c : bv 32 := @BV 32 0x01010113%Z I.

Lemma D_51c2c : decode_any W_51c2c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c30 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_51c30 : decode_any W_51c30 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
