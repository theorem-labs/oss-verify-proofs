(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6dcc4 : bv 32 := 0x00068597.
Lemma F_6dcc4 : fetch_word AsanUbsan.M.loaded_segments (0x6dcc4 : word) = Some W_6dcc4.
Proof. vm_refl. Qed.
Lemma D_6dcc4 : decode_any W_6dcc4 = Some (Auipc 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcc8 : bv 32 := 0x7f45b583.
Lemma F_6dcc8 : fetch_word AsanUbsan.M.loaded_segments (0x6dcc8 : word) = Some W_6dcc8.
Proof. vm_refl. Qed.
Lemma D_6dcc8 : decode_any W_6dcc8 = Some (Load SZ8 true 11 11 2036, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dccc : bv 32 := 0x0905b583.
Lemma F_6dccc : fetch_word AsanUbsan.M.loaded_segments (0x6dccc : word) = Some W_6dccc.
Proof. vm_refl. Qed.
Lemma D_6dccc : decode_any W_6dccc = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcd0 : bv 32 := 0x00058e63.
Lemma F_6dcd0 : fetch_word AsanUbsan.M.loaded_segments (0x6dcd0 : word) = Some W_6dcd0.
Proof. vm_refl. Qed.
Lemma D_6dcd0 : decode_any W_6dcd0 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcd4 : bv 32 := 0x00100617.
Lemma F_6dcd4 : fetch_word AsanUbsan.M.loaded_segments (0x6dcd4 : word) = Some W_6dcd4.
Proof. vm_refl. Qed.
Lemma D_6dcd4 : decode_any W_6dcd4 = Some (Auipc 12 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcd8 : bv 32 := 0x52460613.
Lemma F_6dcd8 : fetch_word AsanUbsan.M.loaded_segments (0x6dcd8 : word) = Some W_6dcd8.
Proof. vm_refl. Qed.
Lemma D_6dcd8 : decode_any W_6dcd8 = Some (OpImm ALU_ADD 12 12 1316, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcdc : bv 32 := 0x00a6362f.
Lemma F_6dcdc : fetch_word AsanUbsan.M.loaded_segments (0x6dcdc : word) = Some W_6dcdc.
Proof. vm_refl. Qed.
Lemma D_6dcdc : decode_any W_6dcdc = Some (Amo AMO_ADD AD false false 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce0 : bv 32 := 0x00a60533.
Lemma F_6dce0 : fetch_word AsanUbsan.M.loaded_segments (0x6dce0 : word) = Some W_6dce0.
Proof. vm_refl. Qed.
Lemma D_6dce0 : decode_any W_6dce0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce4 : bv 32 := 0x01455513.
Lemma F_6dce4 : fetch_word AsanUbsan.M.loaded_segments (0x6dce4 : word) = Some W_6dce4.
Proof. vm_refl. Qed.
Lemma D_6dce4 : decode_any W_6dce4 = Some (ShiftImm ALU_SRL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce8 : bv 32 := 0x00b57463.
Lemma F_6dce8 : fetch_word AsanUbsan.M.loaded_segments (0x6dce8 : word) = Some W_6dce8.
Proof. vm_refl. Qed.
Lemma D_6dce8 : decode_any W_6dce8 = Some (Branch BC_GEU 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcec : bv 32 := 0x00008067.
Lemma F_6dcec : fetch_word AsanUbsan.M.loaded_segments (0x6dcec : word) = Some W_6dcec.
Proof. vm_refl. Qed.
Lemma D_6dcec : decode_any W_6dcec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf0 : bv 32 := 0xff010113.
Lemma F_6dcf0 : fetch_word AsanUbsan.M.loaded_segments (0x6dcf0 : word) = Some W_6dcf0.
Proof. vm_refl. Qed.
Lemma D_6dcf0 : decode_any W_6dcf0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf4 : bv 32 := 0x00113423.
Lemma F_6dcf4 : fetch_word AsanUbsan.M.loaded_segments (0x6dcf4 : word) = Some W_6dcf4.
Proof. vm_refl. Qed.
Lemma D_6dcf4 : decode_any W_6dcf4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf8 : bv 32 := 0xfffa6517.
Lemma F_6dcf8 : fetch_word AsanUbsan.M.loaded_segments (0x6dcf8 : word) = Some W_6dcf8.
Proof. vm_refl. Qed.
Lemma D_6dcf8 : decode_any W_6dcf8 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcfc : bv 32 := 0x9c650513.
Lemma F_6dcfc : fetch_word AsanUbsan.M.loaded_segments (0x6dcfc : word) = Some W_6dcfc.
Proof. vm_refl. Qed.
Lemma D_6dcfc : decode_any W_6dcfc = Some (OpImm ALU_ADD 10 10 2502, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd00 : bv 32 := 0x794000ef.
Lemma F_6dd00 : fetch_word AsanUbsan.M.loaded_segments (0x6dd00 : word) = Some W_6dd00.
Proof. vm_refl. Qed.
Lemma D_6dd00 : decode_any W_6dd00 = Some (Jal 1 1940, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd04 : bv 32 := 0x5180b0ef.
Lemma F_6dd04 : fetch_word AsanUbsan.M.loaded_segments (0x6dd04 : word) = Some W_6dd04.
Proof. vm_refl. Qed.
Lemma D_6dd04 : decode_any W_6dd04 = Some (Jal 1 46360, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd08 : bv 32 := 0x00068597.
Lemma F_6dd08 : fetch_word AsanUbsan.M.loaded_segments (0x6dd08 : word) = Some W_6dd08.
Proof. vm_refl. Qed.
Lemma D_6dd08 : decode_any W_6dd08 = Some (Auipc 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd0c : bv 32 := 0x7b05b583.
Lemma F_6dd0c : fetch_word AsanUbsan.M.loaded_segments (0x6dd0c : word) = Some W_6dd0c.
Proof. vm_refl. Qed.
Lemma D_6dd0c : decode_any W_6dd0c = Some (Load SZ8 true 11 11 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd10 : bv 32 := 0x0905b583.
Lemma F_6dd10 : fetch_word AsanUbsan.M.loaded_segments (0x6dd10 : word) = Some W_6dd10.
Proof. vm_refl. Qed.
Lemma D_6dd10 : decode_any W_6dd10 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd14 : bv 32 := 0x00058a63.
Lemma F_6dd14 : fetch_word AsanUbsan.M.loaded_segments (0x6dd14 : word) = Some W_6dd14.
Proof. vm_refl. Qed.
Lemma D_6dd14 : decode_any W_6dd14 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd18 : bv 32 := 0x40a00533.
Lemma F_6dd18 : fetch_word AsanUbsan.M.loaded_segments (0x6dd18 : word) = Some W_6dd18.
Proof. vm_refl. Qed.
Lemma D_6dd18 : decode_any W_6dd18 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd1c : bv 32 := 0x00100597.
Lemma F_6dd1c : fetch_word AsanUbsan.M.loaded_segments (0x6dd1c : word) = Some W_6dd1c.
Proof. vm_refl. Qed.
Lemma D_6dd1c : decode_any W_6dd1c = Some (Auipc 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd20 : bv 32 := 0x4dc58593.
Lemma F_6dd20 : fetch_word AsanUbsan.M.loaded_segments (0x6dd20 : word) = Some W_6dd20.
Proof. vm_refl. Qed.
Lemma D_6dd20 : decode_any W_6dd20 = Some (OpImm ALU_ADD 11 11 1244, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd24 : bv 32 := 0x00a5b02f.
Lemma F_6dd24 : fetch_word AsanUbsan.M.loaded_segments (0x6dd24 : word) = Some W_6dd24.
Proof. vm_refl. Qed.
Lemma D_6dd24 : decode_any W_6dd24 = Some (Amo AMO_ADD AD false false 0 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd28 : bv 32 := 0x00008067.
Lemma F_6dd28 : fetch_word AsanUbsan.M.loaded_segments (0x6dd28 : word) = Some W_6dd28.
Proof. vm_refl. Qed.
Lemma D_6dd28 : decode_any W_6dd28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
