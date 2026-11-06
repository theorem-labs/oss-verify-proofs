(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_22db8 : bv 32 := 0x00853683.
Lemma F_22db8 : fetch_word Plain.M.loaded_segments (0x22db8 : word) = Some W_22db8.
Proof. vm_refl. Qed.
Lemma D_22db8 : decode_any W_22db8 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dbc : bv 32 := 0x01053603.
Lemma F_22dbc : fetch_word Plain.M.loaded_segments (0x22dbc : word) = Some W_22dbc.
Proof. vm_refl. Qed.
Lemma D_22dbc : decode_any W_22dbc = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dc0 : bv 32 := 0x05853703.
Lemma F_22dc0 : fetch_word Plain.M.loaded_segments (0x22dc0 : word) = Some W_22dc0.
Proof. vm_refl. Qed.
Lemma D_22dc0 : decode_any W_22dc0 = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dc4 : bv 32 := 0x00b037b3.
Lemma F_22dc4 : fetch_word Plain.M.loaded_segments (0x22dc4 : word) = Some W_22dc4.
Proof. vm_refl. Qed.
Lemma D_22dc4 : decode_any W_22dc4 = Some (Op ALU_SLTU 15 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dc8 : bv 32 := 0x40d60833.
Lemma F_22dc8 : fetch_word Plain.M.loaded_segments (0x22dc8 : word) = Some W_22dc8.
Proof. vm_refl. Qed.
Lemma D_22dc8 : decode_any W_22dc8 = Some (Op ALU_SUB 16 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dcc : bv 32 := 0x0105a833.
Lemma F_22dcc : fetch_word Plain.M.loaded_segments (0x22dcc : word) = Some W_22dcc.
Proof. vm_refl. Qed.
Lemma D_22dcc : decode_any W_22dcc = Some (Op ALU_SLT 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dd0 : bv 32 := 0x0107f7b3.
Lemma F_22dd0 : fetch_word Plain.M.loaded_segments (0x22dd0 : word) = Some W_22dd0.
Proof. vm_refl. Qed.
Lemma D_22dd0 : decode_any W_22dd0 = Some (Op ALU_AND 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dd4 : bv 32 := 0x40d70733.
Lemma F_22dd4 : fetch_word Plain.M.loaded_segments (0x22dd4 : word) = Some W_22dd4.
Proof. vm_refl. Qed.
Lemma D_22dd4 : decode_any W_22dd4 = Some (Op ALU_SUB 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dd8 : bv 32 := 0x0cb53023.
Lemma F_22dd8 : fetch_word Plain.M.loaded_segments (0x22dd8 : word) = Some W_22dd8.
Proof. vm_refl. Qed.
Lemma D_22dd8 : decode_any W_22dd8 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ddc : bv 32 := 0x0ce53423.
Lemma F_22ddc : fetch_word Plain.M.loaded_segments (0x22ddc : word) = Some W_22ddc.
Proof. vm_refl. Qed.
Lemma D_22ddc : decode_any W_22ddc = Some (Store SZ8 10 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22de0 : bv 32 := 0x00078463.
Lemma F_22de0 : fetch_word Plain.M.loaded_segments (0x22de0 : word) = Some W_22de0.
Proof. vm_refl. Qed.
Lemma D_22de0 : decode_any W_22de0 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22de8 : bv 32 := 0x0ac53c23.
Lemma F_22de8 : fetch_word Plain.M.loaded_segments (0x22de8 : word) = Some W_22de8.
Proof. vm_refl. Qed.
Lemma D_22de8 : decode_any W_22de8 = Some (Store SZ8 10 12 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22dec : bv 32 := 0x00008067.
Lemma F_22dec : fetch_word Plain.M.loaded_segments (0x22dec : word) = Some W_22dec.
Proof. vm_refl. Qed.
Lemma D_22dec : decode_any W_22dec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22eb8 : bv 32 := 0xfb010113.
Lemma F_22eb8 : fetch_word Plain.M.loaded_segments (0x22eb8 : word) = Some W_22eb8.
Proof. vm_refl. Qed.
Lemma D_22eb8 : decode_any W_22eb8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ebc : bv 32 := 0x04113423.
Lemma F_22ebc : fetch_word Plain.M.loaded_segments (0x22ebc : word) = Some W_22ebc.
Proof. vm_refl. Qed.
Lemma D_22ebc : decode_any W_22ebc = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ec0 : bv 32 := 0x04813023.
Lemma F_22ec0 : fetch_word Plain.M.loaded_segments (0x22ec0 : word) = Some W_22ec0.
Proof. vm_refl. Qed.
Lemma D_22ec0 : decode_any W_22ec0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ec4 : bv 32 := 0x02913c23.
Lemma F_22ec4 : fetch_word Plain.M.loaded_segments (0x22ec4 : word) = Some W_22ec4.
Proof. vm_refl. Qed.
Lemma D_22ec4 : decode_any W_22ec4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ec8 : bv 32 := 0x03213823.
Lemma F_22ec8 : fetch_word Plain.M.loaded_segments (0x22ec8 : word) = Some W_22ec8.
Proof. vm_refl. Qed.
Lemma D_22ec8 : decode_any W_22ec8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ecc : bv 32 := 0x03313423.
Lemma F_22ecc : fetch_word Plain.M.loaded_segments (0x22ecc : word) = Some W_22ecc.
Proof. vm_refl. Qed.
Lemma D_22ecc : decode_any W_22ecc = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ed0 : bv 32 := 0x03413023.
Lemma F_22ed0 : fetch_word Plain.M.loaded_segments (0x22ed0 : word) = Some W_22ed0.
Proof. vm_refl. Qed.
Lemma D_22ed0 : decode_any W_22ed0 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ed4 : bv 32 := 0x01513c23.
Lemma F_22ed4 : fetch_word Plain.M.loaded_segments (0x22ed4 : word) = Some W_22ed4.
Proof. vm_refl. Qed.
Lemma D_22ed4 : decode_any W_22ed4 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ed8 : bv 32 := 0x01613823.
Lemma F_22ed8 : fetch_word Plain.M.loaded_segments (0x22ed8 : word) = Some W_22ed8.
Proof. vm_refl. Qed.
Lemma D_22ed8 : decode_any W_22ed8 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22edc : bv 32 := 0x01713423.
Lemma F_22edc : fetch_word Plain.M.loaded_segments (0x22edc : word) = Some W_22edc.
Proof. vm_refl. Qed.
Lemma D_22edc : decode_any W_22edc = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ee0 : bv 32 := 0x01813023.
Lemma F_22ee0 : fetch_word Plain.M.loaded_segments (0x22ee0 : word) = Some W_22ee0.
Proof. vm_refl. Qed.
Lemma D_22ee0 : decode_any W_22ee0 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ee4 : bv 32 := 0x00058913.
Lemma F_22ee4 : fetch_word Plain.M.loaded_segments (0x22ee4 : word) = Some W_22ee4.
Proof. vm_refl. Qed.
Lemma D_22ee4 : decode_any W_22ee4 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ee8 : bv 32 := 0x02400593.
Lemma F_22ee8 : fetch_word Plain.M.loaded_segments (0x22ee8 : word) = Some W_22ee8.
Proof. vm_refl. Qed.
Lemma D_22ee8 : decode_any W_22ee8 = Some (OpImm ALU_ADD 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22eec : bv 32 := 0x1325ee63.
Lemma F_22eec : fetch_word Plain.M.loaded_segments (0x22eec : word) = Some W_22eec.
Proof. vm_refl. Qed.
Lemma D_22eec : decode_any W_22eec = Some (Branch BC_LTU 11 18 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ef0 : bv 32 := 0x00050493.
Lemma F_22ef0 : fetch_word Plain.M.loaded_segments (0x22ef0 : word) = Some W_22ef0.
Proof. vm_refl. Qed.
Lemma D_22ef0 : decode_any W_22ef0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ef4 : bv 32 := 0x00100513.
Lemma F_22ef4 : fetch_word Plain.M.loaded_segments (0x22ef4 : word) = Some W_22ef4.
Proof. vm_refl. Qed.
Lemma D_22ef4 : decode_any W_22ef4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ef8 : bv 32 := 0x12a90863.
Lemma F_22ef8 : fetch_word Plain.M.loaded_segments (0x22ef8 : word) = Some W_22ef8.
Proof. vm_refl. Qed.
Lemma D_22ef8 : decode_any W_22ef8 = Some (Branch BC_EQ 18 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22efc : bv 32 := 0x00068413.
Lemma F_22efc : fetch_word Plain.M.loaded_segments (0x22efc : word) = Some W_22efc.
Proof. vm_refl. Qed.
Lemma D_22efc : decode_any W_22efc = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f00 : bv 32 := 0x00060993.
Lemma F_22f00 : fetch_word Plain.M.loaded_segments (0x22f00 : word) = Some W_22f00.
Proof. vm_refl. Qed.
Lemma D_22f00 : decode_any W_22f00 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f04 : bv 32 := 0x00500a13.
Lemma F_22f04 : fetch_word Plain.M.loaded_segments (0x22f04 : word) = Some W_22f04.
Proof. vm_refl. Qed.
Lemma D_22f04 : decode_any W_22f04 = Some (OpImm ALU_ADD 20 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f08 : bv 32 := 0x02000a93.
Lemma F_22f08 : fetch_word Plain.M.loaded_segments (0x22f08 : word) = Some W_22f08.
Proof. vm_refl. Qed.
Lemma D_22f08 : decode_any W_22f08 = Some (OpImm ALU_ADD 21 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f0c : bv 32 := 0x0140006f.
Lemma F_22f0c : fetch_word Plain.M.loaded_segments (0x22f0c : word) = Some W_22f0c.
Proof. vm_refl. Qed.
Lemma D_22f0c : decode_any W_22f0c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f20 : bv 32 := 0x0084b503.
Lemma F_22f20 : fetch_word Plain.M.loaded_segments (0x22f20 : word) = Some W_22f20.
Proof. vm_refl. Qed.
Lemma D_22f20 : decode_any W_22f20 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f24 : bv 32 := 0x0b84b583.
Lemma F_22f24 : fetch_word Plain.M.loaded_segments (0x22f24 : word) = Some W_22f24.
Proof. vm_refl. Qed.
Lemma D_22f24 : decode_any W_22f24 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f28 : bv 32 := 0xfeb504e3.
Lemma F_22f28 : fetch_word Plain.M.loaded_segments (0x22f28 : word) = Some W_22f28.
Proof. vm_refl. Qed.
Lemma D_22f28 : decode_any W_22f28 = Some (Branch BC_EQ 10 11 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f2c : bv 32 := 0x00150593.
Lemma F_22f2c : fetch_word Plain.M.loaded_segments (0x22f2c : word) = Some W_22f2c.
Proof. vm_refl. Qed.
Lemma D_22f2c : decode_any W_22f2c = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f30 : bv 32 := 0x00b4b423.
Lemma F_22f30 : fetch_word Plain.M.loaded_segments (0x22f30 : word) = Some W_22f30.
Proof. vm_refl. Qed.
Lemma D_22f30 : decode_any W_22f30 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f34 : bv 32 := 0x00054503.
Lemma F_22f34 : fetch_word Plain.M.loaded_segments (0x22f34 : word) = Some W_22f34.
Proof. vm_refl. Qed.
Lemma D_22f34 : decode_any W_22f34 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f38 : bv 32 := 0xff750593.
Lemma F_22f38 : fetch_word Plain.M.loaded_segments (0x22f38 : word) = Some W_22f38.
Proof. vm_refl. Qed.
Lemma D_22f38 : decode_any W_22f38 = Some (OpImm ALU_ADD 11 10 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f3c : bv 32 := 0xff45e2e3.
Lemma F_22f3c : fetch_word Plain.M.loaded_segments (0x22f3c : word) = Some W_22f3c.
Proof. vm_refl. Qed.
Lemma D_22f3c : decode_any W_22f3c = Some (Branch BC_LTU 11 20 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f40 : bv 32 := 0xff5500e3.
Lemma F_22f40 : fetch_word Plain.M.loaded_segments (0x22f40 : word) = Some W_22f40.
Proof. vm_refl. Qed.
Lemma D_22f40 : decode_any W_22f40 = Some (Branch BC_EQ 10 21 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f44 : bv 32 := 0x02d00593.
Lemma F_22f44 : fetch_word Plain.M.loaded_segments (0x22f44 : word) = Some W_22f44.
Proof. vm_refl. Qed.
Lemma D_22f44 : decode_any W_22f44 = Some (OpImm ALU_ADD 11 0 45, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f48 : bv 32 := 0x00b50663.
Lemma F_22f48 : fetch_word Plain.M.loaded_segments (0x22f48 : word) = Some W_22f48.
Proof. vm_refl. Qed.
Lemma D_22f48 : decode_any W_22f48 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f4c : bv 32 := 0x02b00593.
Lemma F_22f4c : fetch_word Plain.M.loaded_segments (0x22f4c : word) = Some W_22f4c.
Proof. vm_refl. Qed.
Lemma D_22f4c : decode_any W_22f4c = Some (OpImm ALU_ADD 11 0 43, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f50 : bv 32 := 0x02b51a63.
Lemma F_22f50 : fetch_word Plain.M.loaded_segments (0x22f50 : word) = Some W_22f50.
Proof. vm_refl. Qed.
Lemma D_22f50 : decode_any W_22f50 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f54 : bv 32 := 0x0084b583.
Lemma F_22f54 : fetch_word Plain.M.loaded_segments (0x22f54 : word) = Some W_22f54.
Proof. vm_refl. Qed.
Lemma D_22f54 : decode_any W_22f54 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f58 : bv 32 := 0x0b84b603.
Lemma F_22f58 : fetch_word Plain.M.loaded_segments (0x22f58 : word) = Some W_22f58.
Proof. vm_refl. Qed.
Lemma D_22f58 : decode_any W_22f58 = Some (Load SZ8 true 12 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f5c : bv 32 := 0xfd350513.
Lemma F_22f5c : fetch_word Plain.M.loaded_segments (0x22f5c : word) = Some W_22f5c.
Proof. vm_refl. Qed.
Lemma D_22f5c : decode_any W_22f5c = Some (OpImm ALU_ADD 10 10 4051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f60 : bv 32 := 0x00a03a33.
Lemma F_22f60 : fetch_word Plain.M.loaded_segments (0x22f60 : word) = Some W_22f60.
Proof. vm_refl. Qed.
Lemma D_22f60 : decode_any W_22f60 = Some (Op ALU_SLTU 20 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f64 : bv 32 := 0xfffa0a1b.
Lemma F_22f64 : fetch_word Plain.M.loaded_segments (0x22f64 : word) = Some W_22f64.
Proof. vm_refl. Qed.
Lemma D_22f64 : decode_any W_22f64 = Some (OpImm32 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f68 : bv 32 := 0x02c58663.
Lemma F_22f68 : fetch_word Plain.M.loaded_segments (0x22f68 : word) = Some W_22f68.
Proof. vm_refl. Qed.
Lemma D_22f68 : decode_any W_22f68 = Some (Branch BC_EQ 11 12 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f6c : bv 32 := 0x00158513.
Lemma F_22f6c : fetch_word Plain.M.loaded_segments (0x22f6c : word) = Some W_22f6c.
Proof. vm_refl. Qed.
Lemma D_22f6c : decode_any W_22f6c = Some (OpImm ALU_ADD 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f70 : bv 32 := 0x00a4b423.
Lemma F_22f70 : fetch_word Plain.M.loaded_segments (0x22f70 : word) = Some W_22f70.
Proof. vm_refl. Qed.
Lemma D_22f70 : decode_any W_22f70 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f74 : bv 32 := 0x0005c503.
Lemma F_22f74 : fetch_word Plain.M.loaded_segments (0x22f74 : word) = Some W_22f74.
Proof. vm_refl. Qed.
Lemma D_22f74 : decode_any W_22f74 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f78 : bv 32 := 0xfef97593.
Lemma F_22f78 : fetch_word Plain.M.loaded_segments (0x22f78 : word) = Some W_22f78.
Proof. vm_refl. Qed.
Lemma D_22f78 : decode_any W_22f78 = Some (OpImm ALU_AND 11 18 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f7c : bv 32 := 0x02058463.
Lemma F_22f7c : fetch_word Plain.M.loaded_segments (0x22f7c : word) = Some W_22f7c.
Proof. vm_refl. Qed.
Lemma D_22f7c : decode_any W_22f7c = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f80 : bv 32 := 0x06c0006f.
Lemma F_22f80 : fetch_word Plain.M.loaded_segments (0x22f80 : word) = Some W_22f80.
Proof. vm_refl. Qed.
Lemma D_22f80 : decode_any W_22f80 = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f84 : bv 32 := 0x00000a13.
Lemma F_22f84 : fetch_word Plain.M.loaded_segments (0x22f84 : word) = Some W_22f84.
Proof. vm_refl. Qed.
Lemma D_22f84 : decode_any W_22f84 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f88 : bv 32 := 0xfef97593.
Lemma F_22f88 : fetch_word Plain.M.loaded_segments (0x22f88 : word) = Some W_22f88.
Proof. vm_refl. Qed.
Lemma D_22f88 : decode_any W_22f88 = Some (OpImm ALU_AND 11 18 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f8c : bv 32 := 0x00058c63.
Lemma F_22f8c : fetch_word Plain.M.loaded_segments (0x22f8c : word) = Some W_22f8c.
Proof. vm_refl. Qed.
Lemma D_22f8c : decode_any W_22f8c = Some (Branch BC_EQ 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22f90 : bv 32 := 0x05c0006f.
Lemma F_22f90 : fetch_word Plain.M.loaded_segments (0x22f90 : word) = Some W_22f90.
Proof. vm_refl. Qed.
Lemma D_22f90 : decode_any W_22f90 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22fec : bv 32 := 0x00091463.
Lemma F_22fec : fetch_word Plain.M.loaded_segments (0x22fec : word) = Some W_22fec.
Proof. vm_refl. Qed.
Lemma D_22fec : decode_any W_22fec = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ff4 : bv 32 := 0xfffee597.
Lemma F_22ff4 : fetch_word Plain.M.loaded_segments (0x22ff4 : word) = Some W_22ff4.
Proof. vm_refl. Qed.
Lemma D_22ff4 : decode_any W_22ff4 = Some (Auipc 11 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ff8 : bv 32 := 0x47058593.
Lemma F_22ff8 : fetch_word Plain.M.loaded_segments (0x22ff8 : word) = Some W_22ff8.
Proof. vm_refl. Qed.
Lemma D_22ff8 : decode_any W_22ff8 = Some (OpImm ALU_ADD 11 11 1136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ffc : bv 32 := 0x00a585b3.
Lemma F_22ffc : fetch_word Plain.M.loaded_segments (0x22ffc : word) = Some W_22ffc.
Proof. vm_refl. Qed.
Lemma D_22ffc : decode_any W_22ffc = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23000 : bv 32 := 0x0015c583.
Lemma F_23000 : fetch_word Plain.M.loaded_segments (0x23000 : word) = Some W_23000.
Proof. vm_refl. Qed.
Lemma D_23000 : decode_any W_23000 = Some (Load SZ1 false 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23004 : bv 32 := 0x0525e863.
Lemma F_23004 : fetch_word Plain.M.loaded_segments (0x23004 : word) = Some W_23004.
Proof. vm_refl. Qed.
Lemma D_23004 : decode_any W_23004 = Some (Branch BC_LTU 11 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23008 : bv 32 := 0x0c04b503.
Lemma F_23008 : fetch_word Plain.M.loaded_segments (0x23008 : word) = Some W_23008.
Proof. vm_refl. Qed.
Lemma D_23008 : decode_any W_23008 = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2300c : bv 32 := 0x00054863.
Lemma F_2300c : fetch_word Plain.M.loaded_segments (0x2300c : word) = Some W_2300c.
Proof. vm_refl. Qed.
Lemma D_2300c : decode_any W_2300c = Some (Branch BC_LT 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23010 : bv 32 := 0x0084b503.
Lemma F_23010 : fetch_word Plain.M.loaded_segments (0x23010 : word) = Some W_23010.
Proof. vm_refl. Qed.
Lemma D_23010 : decode_any W_23010 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23014 : bv 32 := 0xfff50513.
Lemma F_23014 : fetch_word Plain.M.loaded_segments (0x23014 : word) = Some W_23014.
Proof. vm_refl. Qed.
Lemma D_23014 : decode_any W_23014 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23018 : bv 32 := 0x00a4b423.
Lemma F_23018 : fetch_word Plain.M.loaded_segments (0x23018 : word) = Some W_23018.
Proof. vm_refl. Qed.
Lemma D_23018 : decode_any W_23018 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2301c : bv 32 := 0x00048513.
Lemma F_2301c : fetch_word Plain.M.loaded_segments (0x2301c : word) = Some W_2301c.
Proof. vm_refl. Qed.
Lemma D_2301c : decode_any W_2301c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23020 : bv 32 := 0x00000593.
Lemma F_23020 : fetch_word Plain.M.loaded_segments (0x23020 : word) = Some W_23020.
Proof. vm_refl. Qed.
Lemma D_23020 : decode_any W_23020 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23024 : bv 32 := 0xd95ff0ef.
Lemma F_23024 : fetch_word Plain.M.loaded_segments (0x23024 : word) = Some W_23024.
Proof. vm_refl. Qed.
Lemma D_23024 : decode_any W_23024 = Some (Jal 1 2096532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23028 : bv 32 := 0x889f80ef.
Lemma F_23028 : fetch_word Plain.M.loaded_segments (0x23028 : word) = Some W_23028.
Proof. vm_refl. Qed.
Lemma D_23028 : decode_any W_23028 = Some (Jal 1 2066568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2302c : bv 32 := 0x00000413.
Lemma F_2302c : fetch_word Plain.M.loaded_segments (0x2302c : word) = Some W_2302c.
Proof. vm_refl. Qed.
Lemma D_2302c : decode_any W_2302c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23030 : bv 32 := 0x01600593.
Lemma F_23030 : fetch_word Plain.M.loaded_segments (0x23030 : word) = Some W_23030.
Proof. vm_refl. Qed.
Lemma D_23030 : decode_any W_23030 = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23034 : bv 32 := 0x00b52023.
Lemma F_23034 : fetch_word Plain.M.loaded_segments (0x23034 : word) = Some W_23034.
Proof. vm_refl. Qed.
Lemma D_23034 : decode_any W_23034 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23038 : bv 32 := 0x4240006f.
Lemma F_23038 : fetch_word Plain.M.loaded_segments (0x23038 : word) = Some W_23038.
Proof. vm_refl. Qed.
Lemma D_23038 : decode_any W_23038 = Some (Jal 0 1060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23054 : bv 32 := 0x00a00593.
Lemma F_23054 : fetch_word Plain.M.loaded_segments (0x23054 : word) = Some W_23054.
Proof. vm_refl. Qed.
Lemma D_23054 : decode_any W_23054 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23058 : bv 32 := 0x12b91463.
Lemma F_23058 : fetch_word Plain.M.loaded_segments (0x23058 : word) = Some W_23058.
Proof. vm_refl. Qed.
Lemma D_23058 : decode_any W_23058 = Some (Branch BC_NE 18 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2305c : bv 32 := 0xfd050a9b.
Lemma F_2305c : fetch_word Plain.M.loaded_segments (0x2305c : word) = Some W_2305c.
Proof. vm_refl. Qed.
Lemma D_2305c : decode_any W_2305c = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23060 : bv 32 := 0x00000993.
Lemma F_23060 : fetch_word Plain.M.loaded_segments (0x23060 : word) = Some W_23060.
Proof. vm_refl. Qed.
Lemma D_23060 : decode_any W_23060 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23064 : bv 32 := 0x00900913.
Lemma F_23064 : fetch_word Plain.M.loaded_segments (0x23064 : word) = Some W_23064.
Proof. vm_refl. Qed.
Lemma D_23064 : decode_any W_23064 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23068 : bv 32 := 0x07596063.
Lemma F_23068 : fetch_word Plain.M.loaded_segments (0x23068 : word) = Some W_23068.
Proof. vm_refl. Qed.
Lemma D_23068 : decode_any W_23068 = Some (Branch BC_LTU 18 21 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2306c : bv 32 := 0x00a00b13.
Lemma F_2306c : fetch_word Plain.M.loaded_segments (0x2306c : word) = Some W_2306c.
Proof. vm_refl. Qed.
Lemma D_2306c : decode_any W_2306c = Some (OpImm ALU_ADD 22 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23070 : bv 32 := 0x1999a537.
Lemma F_23070 : fetch_word Plain.M.loaded_segments (0x23070 : word) = Some W_23070.
Proof. vm_refl. Qed.
Lemma D_23070 : decode_any W_23070 = Some (Lui 10 104858, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23074 : bv 32 := 0x99950b9b.
Lemma F_23074 : fetch_word Plain.M.loaded_segments (0x23074 : word) = Some W_23074.
Proof. vm_refl. Qed.
Lemma D_23074 : decode_any W_23074 = Some (OpImm32 23 10 2457, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23078 : bv 32 := 0x0200006f.
Lemma F_23078 : fetch_word Plain.M.loaded_segments (0x23078 : word) = Some W_23078.
Proof. vm_refl. Qed.
Lemma D_23078 : decode_any W_23078 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23094 : bv 32 := 0x0379f663.
Lemma F_23094 : fetch_word Plain.M.loaded_segments (0x23094 : word) = Some W_23094.
Proof. vm_refl. Qed.
Lemma D_23094 : decode_any W_23094 = Some (Branch BC_GEU 19 23 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23098 : bv 32 := 0x0084b503.
Lemma F_23098 : fetch_word Plain.M.loaded_segments (0x23098 : word) = Some W_23098.
Proof. vm_refl. Qed.
Lemma D_23098 : decode_any W_23098 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2309c : bv 32 := 0x0b84b583.
Lemma F_2309c : fetch_word Plain.M.loaded_segments (0x2309c : word) = Some W_2309c.
Proof. vm_refl. Qed.
Lemma D_2309c : decode_any W_2309c = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230a0 : bv 32 := 0xfcb50ee3.
Lemma F_230a0 : fetch_word Plain.M.loaded_segments (0x230a0 : word) = Some W_230a0.
Proof. vm_refl. Qed.
Lemma D_230a0 : decode_any W_230a0 = Some (Branch BC_EQ 10 11 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230a4 : bv 32 := 0x00150593.
Lemma F_230a4 : fetch_word Plain.M.loaded_segments (0x230a4 : word) = Some W_230a4.
Proof. vm_refl. Qed.
Lemma D_230a4 : decode_any W_230a4 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230a8 : bv 32 := 0x00b4b423.
Lemma F_230a8 : fetch_word Plain.M.loaded_segments (0x230a8 : word) = Some W_230a8.
Proof. vm_refl. Qed.
Lemma D_230a8 : decode_any W_230a8 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230ac : bv 32 := 0x00054503.
Lemma F_230ac : fetch_word Plain.M.loaded_segments (0x230ac : word) = Some W_230ac.
Proof. vm_refl. Qed.
Lemma D_230ac : decode_any W_230ac = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230b0 : bv 32 := 0x036985b3.
Lemma F_230b0 : fetch_word Plain.M.loaded_segments (0x230b0 : word) = Some W_230b0.
Proof. vm_refl. Qed.
Lemma D_230b0 : decode_any W_230b0 = Some (Mul M_MUL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230b4 : bv 32 := 0x015589bb.
Lemma F_230b4 : fetch_word Plain.M.loaded_segments (0x230b4 : word) = Some W_230b4.
Proof. vm_refl. Qed.
Lemma D_230b4 : decode_any W_230b4 = Some (Op32 ALU_ADD 19 11 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230b8 : bv 32 := 0xfd050a9b.
Lemma F_230b8 : fetch_word Plain.M.loaded_segments (0x230b8 : word) = Some W_230b8.
Proof. vm_refl. Qed.
Lemma D_230b8 : decode_any W_230b8 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230bc : bv 32 := 0xfd597ce3.
Lemma F_230bc : fetch_word Plain.M.loaded_segments (0x230bc : word) = Some W_230bc.
Proof. vm_refl. Qed.
Lemma D_230bc : decode_any W_230bc = Some (Branch BC_GEU 18 21 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230c0 : bv 32 := 0x02099993.
Lemma F_230c0 : fetch_word Plain.M.loaded_segments (0x230c0 : word) = Some W_230c0.
Proof. vm_refl. Qed.
Lemma D_230c0 : decode_any W_230c0 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230c4 : bv 32 := 0x0209d993.
Lemma F_230c4 : fetch_word Plain.M.loaded_segments (0x230c4 : word) = Some W_230c4.
Proof. vm_refl. Qed.
Lemma D_230c4 : decode_any W_230c4 = Some (ShiftImm ALU_SRL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230c8 : bv 32 := 0x2d596463.
Lemma F_230c8 : fetch_word Plain.M.loaded_segments (0x230c8 : word) = Some W_230c8.
Proof. vm_refl. Qed.
Lemma D_230c8 : decode_any W_230c8 = Some (Branch BC_LTU 18 21 712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230cc : bv 32 := 0xfffed517.
Lemma F_230cc : fetch_word Plain.M.loaded_segments (0x230cc : word) = Some W_230cc.
Proof. vm_refl. Qed.
Lemma D_230cc : decode_any W_230cc = Some (Auipc 10 1048557, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230d0 : bv 32 := 0x4ac53b03.
Lemma F_230d0 : fetch_word Plain.M.loaded_segments (0x230d0 : word) = Some W_230d0.
Proof. vm_refl. Qed.
Lemma D_230d0 : decode_any W_230d0 = Some (Load SZ8 true 22 10 1196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230d4 : bv 32 := 0x00a00513.
Lemma F_230d4 : fetch_word Plain.M.loaded_segments (0x230d4 : word) = Some W_230d4.
Proof. vm_refl. Qed.
Lemma D_230d4 : decode_any W_230d4 = Some (OpImm ALU_ADD 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230d8 : bv 32 := 0x02a98c33.
Lemma F_230d8 : fetch_word Plain.M.loaded_segments (0x230d8 : word) = Some W_230d8.
Proof. vm_refl. Qed.
Lemma D_230d8 : decode_any W_230d8 = Some (Mul M_MUL 24 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230dc : bv 32 := 0x00900b93.
Lemma F_230dc : fetch_word Plain.M.loaded_segments (0x230dc : word) = Some W_230dc.
Proof. vm_refl. Qed.
Lemma D_230dc : decode_any W_230dc = Some (OpImm ALU_ADD 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230e0 : bv 32 := 0x0084b503.
Lemma F_230e0 : fetch_word Plain.M.loaded_segments (0x230e0 : word) = Some W_230e0.
Proof. vm_refl. Qed.
Lemma D_230e0 : decode_any W_230e0 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230e4 : bv 32 := 0x0b84b583.
Lemma F_230e4 : fetch_word Plain.M.loaded_segments (0x230e4 : word) = Some W_230e4.
Proof. vm_refl. Qed.
Lemma D_230e4 : decode_any W_230e4 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230e8 : bv 32 := 0x02b50063.
Lemma F_230e8 : fetch_word Plain.M.loaded_segments (0x230e8 : word) = Some W_230e8.
Proof. vm_refl. Qed.
Lemma D_230e8 : decode_any W_230e8 = Some (Branch BC_EQ 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230ec : bv 32 := 0x00150593.
Lemma F_230ec : fetch_word Plain.M.loaded_segments (0x230ec : word) = Some W_230ec.
Proof. vm_refl. Qed.
Lemma D_230ec : decode_any W_230ec = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230f0 : bv 32 := 0x00b4b423.
Lemma F_230f0 : fetch_word Plain.M.loaded_segments (0x230f0 : word) = Some W_230f0.
Proof. vm_refl. Qed.
Lemma D_230f0 : decode_any W_230f0 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230f4 : bv 32 := 0x00054503.
Lemma F_230f4 : fetch_word Plain.M.loaded_segments (0x230f4 : word) = Some W_230f4.
Proof. vm_refl. Qed.
Lemma D_230f4 : decode_any W_230f4 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230f8 : bv 32 := 0x015c09b3.
Lemma F_230f8 : fetch_word Plain.M.loaded_segments (0x230f8 : word) = Some W_230f8.
Proof. vm_refl. Qed.
Lemma D_230f8 : decode_any W_230f8 = Some (Op ALU_ADD 19 24 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_230fc : bv 32 := 0xfd050a9b.
Lemma F_230fc : fetch_word Plain.M.loaded_segments (0x230fc : word) = Some W_230fc.
Proof. vm_refl. Qed.
Lemma D_230fc : decode_any W_230fc = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23100 : bv 32 := 0x015bfe63.
Lemma F_23100 : fetch_word Plain.M.loaded_segments (0x23100 : word) = Some W_23100.
Proof. vm_refl. Qed.
Lemma D_23100 : decode_any W_23100 = Some (Branch BC_GEU 23 21 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23104 : bv 32 := 0x26c0006f.
Lemma F_23104 : fetch_word Plain.M.loaded_segments (0x23104 : word) = Some W_23104.
Proof. vm_refl. Qed.
Lemma D_23104 : decode_any W_23104 = Some (Jal 0 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2311c : bv 32 := 0x2569fa63.
Lemma F_2311c : fetch_word Plain.M.loaded_segments (0x2311c : word) = Some W_2311c.
Proof. vm_refl. Qed.
Lemma D_2311c : decode_any W_2311c = Some (Branch BC_GEU 19 22 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23120 : bv 32 := 0x00a00913.
Lemma F_23120 : fetch_word Plain.M.loaded_segments (0x23120 : word) = Some W_23120.
Proof. vm_refl. Qed.
Lemma D_23120 : decode_any W_23120 = Some (OpImm ALU_ADD 18 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23124 : bv 32 := 0x03298c33.
Lemma F_23124 : fetch_word Plain.M.loaded_segments (0x23124 : word) = Some W_23124.
Proof. vm_refl. Qed.
Lemma D_23124 : decode_any W_23124 = Some (Mul M_MUL 24 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23128 : bv 32 := 0xfffac593.
Lemma F_23128 : fetch_word Plain.M.loaded_segments (0x23128 : word) = Some W_23128.
Proof. vm_refl. Qed.
Lemma D_23128 : decode_any W_23128 = Some (OpImm ALU_XOR 11 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2312c : bv 32 := 0xfb85fae3.
Lemma F_2312c : fetch_word Plain.M.loaded_segments (0x2312c : word) = Some W_2312c.
Proof. vm_refl. Qed.
Lemma D_2312c : decode_any W_2312c = Some (Branch BC_GEU 11 24 8116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23130 : bv 32 := 0x24c0006f.
Lemma F_23130 : fetch_word Plain.M.loaded_segments (0x23130 : word) = Some W_23130.
Proof. vm_refl. Qed.
Lemma D_23130 : decode_any W_23130 = Some (Jal 0 588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23370 : bv 32 := 0x00900593.
Lemma F_23370 : fetch_word Plain.M.loaded_segments (0x23370 : word) = Some W_23370.
Proof. vm_refl. Qed.
Lemma D_23370 : decode_any W_23370 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23374 : bv 32 := 0x0155ee63.
Lemma F_23374 : fetch_word Plain.M.loaded_segments (0x23374 : word) = Some W_23374.
Proof. vm_refl. Qed.
Lemma D_23374 : decode_any W_23374 = Some (Branch BC_LTU 11 21 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23378 : bv 32 := 0x00a00913.
Lemma F_23378 : fetch_word Plain.M.loaded_segments (0x23378 : word) = Some W_23378.
Proof. vm_refl. Qed.
Lemma D_23378 : decode_any W_23378 = Some (OpImm ALU_ADD 18 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2337c : bv 32 := 0xfffee597.
Lemma F_2337c : fetch_word Plain.M.loaded_segments (0x2337c : word) = Some W_2337c.
Proof. vm_refl. Qed.
Lemma D_2337c : decode_any W_2337c = Some (Auipc 11 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23380 : bv 32 := 0x0e858a93.
Lemma F_23380 : fetch_word Plain.M.loaded_segments (0x23380 : word) = Some W_23380.
Proof. vm_refl. Qed.
Lemma D_23380 : decode_any W_23380 = Some (OpImm ALU_ADD 21 11 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23384 : bv 32 := 0x00aa8533.
Lemma F_23384 : fetch_word Plain.M.loaded_segments (0x23384 : word) = Some W_23384.
Proof. vm_refl. Qed.
Lemma D_23384 : decode_any W_23384 = Some (Op ALU_ADD 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23388 : bv 32 := 0x00154503.
Lemma F_23388 : fetch_word Plain.M.loaded_segments (0x23388 : word) = Some W_23388.
Proof. vm_refl. Qed.
Lemma D_23388 : decode_any W_23388 = Some (Load SZ1 false 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2338c : bv 32 := 0x03256e63.
Lemma F_2338c : fetch_word Plain.M.loaded_segments (0x2338c : word) = Some W_2338c.
Proof. vm_refl. Qed.
Lemma D_2338c : decode_any W_2338c = Some (Branch BC_LTU 10 18 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23390 : bv 32 := 0x0c04b503.
Lemma F_23390 : fetch_word Plain.M.loaded_segments (0x23390 : word) = Some W_23390.
Proof. vm_refl. Qed.
Lemma D_23390 : decode_any W_23390 = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23394 : bv 32 := 0x00054863.
Lemma F_23394 : fetch_word Plain.M.loaded_segments (0x23394 : word) = Some W_23394.
Proof. vm_refl. Qed.
Lemma D_23394 : decode_any W_23394 = Some (Branch BC_LT 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23398 : bv 32 := 0x0084b503.
Lemma F_23398 : fetch_word Plain.M.loaded_segments (0x23398 : word) = Some W_23398.
Proof. vm_refl. Qed.
Lemma D_23398 : decode_any W_23398 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2339c : bv 32 := 0xfff50513.
Lemma F_2339c : fetch_word Plain.M.loaded_segments (0x2339c : word) = Some W_2339c.
Proof. vm_refl. Qed.
Lemma D_2339c : decode_any W_2339c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233a0 : bv 32 := 0x00a4b423.
Lemma F_233a0 : fetch_word Plain.M.loaded_segments (0x233a0 : word) = Some W_233a0.
Proof. vm_refl. Qed.
Lemma D_233a0 : decode_any W_233a0 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233a4 : bv 32 := 0x0689f863.
Lemma F_233a4 : fetch_word Plain.M.loaded_segments (0x233a4 : word) = Some W_233a4.
Proof. vm_refl. Qed.
Lemma D_233a4 : decode_any W_233a4 = Some (Branch BC_GEU 19 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233a8 : bv 32 := 0x0149c533.
Lemma F_233a8 : fetch_word Plain.M.loaded_segments (0x233a8 : word) = Some W_233a8.
Proof. vm_refl. Qed.
Lemma D_233a8 : decode_any W_233a8 = Some (Op ALU_XOR 10 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233ac : bv 32 := 0x41450433.
Lemma F_233ac : fetch_word Plain.M.loaded_segments (0x233ac : word) = Some W_233ac.
Proof. vm_refl. Qed.
Lemma D_233ac : decode_any W_233ac = Some (Op ALU_SUB 8 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233b0 : bv 32 := 0x0ac0006f.
Lemma F_233b0 : fetch_word Plain.M.loaded_segments (0x233b0 : word) = Some W_233b0.
Proof. vm_refl. Qed.
Lemma D_233b0 : decode_any W_233b0 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233c8 : bv 32 := 0x0084b503.
Lemma F_233c8 : fetch_word Plain.M.loaded_segments (0x233c8 : word) = Some W_233c8.
Proof. vm_refl. Qed.
Lemma D_233c8 : decode_any W_233c8 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233cc : bv 32 := 0x0b84b583.
Lemma F_233cc : fetch_word Plain.M.loaded_segments (0x233cc : word) = Some W_233cc.
Proof. vm_refl. Qed.
Lemma D_233cc : decode_any W_233cc = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233d0 : bv 32 := 0xfeb502e3.
Lemma F_233d0 : fetch_word Plain.M.loaded_segments (0x233d0 : word) = Some W_233d0.
Proof. vm_refl. Qed.
Lemma D_233d0 : decode_any W_233d0 = Some (Branch BC_EQ 10 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233d4 : bv 32 := 0x00150593.
Lemma F_233d4 : fetch_word Plain.M.loaded_segments (0x233d4 : word) = Some W_233d4.
Proof. vm_refl. Qed.
Lemma D_233d4 : decode_any W_233d4 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233d8 : bv 32 := 0x00b4b423.
Lemma F_233d8 : fetch_word Plain.M.loaded_segments (0x233d8 : word) = Some W_233d8.
Proof. vm_refl. Qed.
Lemma D_233d8 : decode_any W_233d8 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233dc : bv 32 := 0x00054503.
Lemma F_233dc : fetch_word Plain.M.loaded_segments (0x233dc : word) = Some W_233dc.
Proof. vm_refl. Qed.
Lemma D_233dc : decode_any W_233dc = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233e0 : bv 32 := 0x00aa8533.
Lemma F_233e0 : fetch_word Plain.M.loaded_segments (0x233e0 : word) = Some W_233e0.
Proof. vm_refl. Qed.
Lemma D_233e0 : decode_any W_233e0 = Some (Op ALU_ADD 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233e4 : bv 32 := 0x00154503.
Lemma F_233e4 : fetch_word Plain.M.loaded_segments (0x233e4 : word) = Some W_233e4.
Proof. vm_refl. Qed.
Lemma D_233e4 : decode_any W_233e4 = Some (Load SZ1 false 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233e8 : bv 32 := 0xff2560e3.
Lemma F_233e8 : fetch_word Plain.M.loaded_segments (0x233e8 : word) = Some W_233e8.
Proof. vm_refl. Qed.
Lemma D_233e8 : decode_any W_233e8 = Some (Branch BC_LTU 10 18 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233ec : bv 32 := 0xcc4f80ef.
Lemma F_233ec : fetch_word Plain.M.loaded_segments (0x233ec : word) = Some W_233ec.
Proof. vm_refl. Qed.
Lemma D_233ec : decode_any W_233ec = Some (Jal 1 2065604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f0 : bv 32 := 0x02200593.
Lemma F_233f0 : fetch_word Plain.M.loaded_segments (0x233f0 : word) = Some W_233f0.
Proof. vm_refl. Qed.
Lemma D_233f0 : decode_any W_233f0 = Some (OpImm ALU_ADD 11 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f4 : bv 32 := 0x00b52023.
Lemma F_233f4 : fetch_word Plain.M.loaded_segments (0x233f4 : word) = Some W_233f4.
Proof. vm_refl. Qed.
Lemma D_233f4 : decode_any W_233f4 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f8 : bv 32 := 0x00147513.
Lemma F_233f8 : fetch_word Plain.M.loaded_segments (0x233f8 : word) = Some W_233f8.
Proof. vm_refl. Qed.
Lemma D_233f8 : decode_any W_233f8 = Some (OpImm ALU_AND 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233fc : bv 32 := 0xfff5051b.
Lemma F_233fc : fetch_word Plain.M.loaded_segments (0x233fc : word) = Some W_233fc.
Proof. vm_refl. Qed.
Lemma D_233fc : decode_any W_233fc = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23400 : bv 32 := 0x01457a33.
Lemma F_23400 : fetch_word Plain.M.loaded_segments (0x23400 : word) = Some W_23400.
Proof. vm_refl. Qed.
Lemma D_23400 : decode_any W_23400 = Some (Op ALU_AND 20 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23404 : bv 32 := 0x00040993.
Lemma F_23404 : fetch_word Plain.M.loaded_segments (0x23404 : word) = Some W_23404.
Proof. vm_refl. Qed.
Lemma D_23404 : decode_any W_23404 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23408 : bv 32 := 0x0c04b503.
Lemma F_23408 : fetch_word Plain.M.loaded_segments (0x23408 : word) = Some W_23408.
Proof. vm_refl. Qed.
Lemma D_23408 : decode_any W_23408 = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2340c : bv 32 := 0xf80556e3.
Lemma F_2340c : fetch_word Plain.M.loaded_segments (0x2340c : word) = Some W_2340c.
Proof. vm_refl. Qed.
Lemma D_2340c : decode_any W_2340c = Some (Branch BC_GE 10 0 8076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23414 : bv 32 := 0x00147513.
Lemma F_23414 : fetch_word Plain.M.loaded_segments (0x23414 : word) = Some W_23414.
Proof. vm_refl. Qed.
Lemma D_23414 : decode_any W_23414 = Some (OpImm ALU_AND 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23418 : bv 32 := 0x00051e63.
Lemma F_23418 : fetch_word Plain.M.loaded_segments (0x23418 : word) = Some W_23418.
Proof. vm_refl. Qed.
Lemma D_23418 : decode_any W_23418 = Some (Branch BC_NE 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23434 : bv 32 := 0xf7347ae3.
Lemma F_23434 : fetch_word Plain.M.loaded_segments (0x23434 : word) = Some W_23434.
Proof. vm_refl. Qed.
Lemma D_23434 : decode_any W_23434 = Some (Branch BC_GEU 8 19 8052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2345c : bv 32 := 0x00040513.
Lemma F_2345c : fetch_word Plain.M.loaded_segments (0x2345c : word) = Some W_2345c.
Proof. vm_refl. Qed.
Lemma D_2345c : decode_any W_2345c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23460 : bv 32 := 0x04813083.
Lemma F_23460 : fetch_word Plain.M.loaded_segments (0x23460 : word) = Some W_23460.
Proof. vm_refl. Qed.
Lemma D_23460 : decode_any W_23460 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23464 : bv 32 := 0x04013403.
Lemma F_23464 : fetch_word Plain.M.loaded_segments (0x23464 : word) = Some W_23464.
Proof. vm_refl. Qed.
Lemma D_23464 : decode_any W_23464 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23468 : bv 32 := 0x03813483.
Lemma F_23468 : fetch_word Plain.M.loaded_segments (0x23468 : word) = Some W_23468.
Proof. vm_refl. Qed.
Lemma D_23468 : decode_any W_23468 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2346c : bv 32 := 0x03013903.
Lemma F_2346c : fetch_word Plain.M.loaded_segments (0x2346c : word) = Some W_2346c.
Proof. vm_refl. Qed.
Lemma D_2346c : decode_any W_2346c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23470 : bv 32 := 0x02813983.
Lemma F_23470 : fetch_word Plain.M.loaded_segments (0x23470 : word) = Some W_23470.
Proof. vm_refl. Qed.
Lemma D_23470 : decode_any W_23470 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23474 : bv 32 := 0x02013a03.
Lemma F_23474 : fetch_word Plain.M.loaded_segments (0x23474 : word) = Some W_23474.
Proof. vm_refl. Qed.
Lemma D_23474 : decode_any W_23474 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23478 : bv 32 := 0x01813a83.
Lemma F_23478 : fetch_word Plain.M.loaded_segments (0x23478 : word) = Some W_23478.
Proof. vm_refl. Qed.
Lemma D_23478 : decode_any W_23478 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2347c : bv 32 := 0x01013b03.
Lemma F_2347c : fetch_word Plain.M.loaded_segments (0x2347c : word) = Some W_2347c.
Proof. vm_refl. Qed.
Lemma D_2347c : decode_any W_2347c = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23480 : bv 32 := 0x00813b83.
Lemma F_23480 : fetch_word Plain.M.loaded_segments (0x23480 : word) = Some W_23480.
Proof. vm_refl. Qed.
Lemma D_23480 : decode_any W_23480 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23484 : bv 32 := 0x00013c03.
Lemma F_23484 : fetch_word Plain.M.loaded_segments (0x23484 : word) = Some W_23484.
Proof. vm_refl. Qed.
Lemma D_23484 : decode_any W_23484 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23488 : bv 32 := 0x05010113.
Lemma F_23488 : fetch_word Plain.M.loaded_segments (0x23488 : word) = Some W_23488.
Proof. vm_refl. Qed.
Lemma D_23488 : decode_any W_23488 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2348c : bv 32 := 0x00008067.
Lemma F_2348c : fetch_word Plain.M.loaded_segments (0x2348c : word) = Some W_2348c.
Proof. vm_refl. Qed.
Lemma D_2348c : decode_any W_2348c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23490 : bv 32 := 0xee010113.
Lemma F_23490 : fetch_word Plain.M.loaded_segments (0x23490 : word) = Some W_23490.
Proof. vm_refl. Qed.
Lemma D_23490 : decode_any W_23490 = Some (OpImm ALU_ADD 2 2 3808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23494 : bv 32 := 0x10113c23.
Lemma F_23494 : fetch_word Plain.M.loaded_segments (0x23494 : word) = Some W_23494.
Proof. vm_refl. Qed.
Lemma D_23494 : decode_any W_23494 = Some (Store SZ8 2 1 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23498 : bv 32 := 0x10813823.
Lemma F_23498 : fetch_word Plain.M.loaded_segments (0x23498 : word) = Some W_23498.
Proof. vm_refl. Qed.
Lemma D_23498 : decode_any W_23498 = Some (Store SZ8 2 8 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2349c : bv 32 := 0x10913423.
Lemma F_2349c : fetch_word Plain.M.loaded_segments (0x2349c : word) = Some W_2349c.
Proof. vm_refl. Qed.
Lemma D_2349c : decode_any W_2349c = Some (Store SZ8 2 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234a0 : bv 32 := 0x11213023.
Lemma F_234a0 : fetch_word Plain.M.loaded_segments (0x234a0 : word) = Some W_234a0.
Proof. vm_refl. Qed.
Lemma D_234a0 : decode_any W_234a0 = Some (Store SZ8 2 18 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234a4 : bv 32 := 0x0f313c23.
Lemma F_234a4 : fetch_word Plain.M.loaded_segments (0x234a4 : word) = Some W_234a4.
Proof. vm_refl. Qed.
Lemma D_234a4 : decode_any W_234a4 = Some (Store SZ8 2 19 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234a8 : bv 32 := 0x00060913.
Lemma F_234a8 : fetch_word Plain.M.loaded_segments (0x234a8 : word) = Some W_234a8.
Proof. vm_refl. Qed.
Lemma D_234a8 : decode_any W_234a8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234ac : bv 32 := 0x00058413.
Lemma F_234ac : fetch_word Plain.M.loaded_segments (0x234ac : word) = Some W_234ac.
Proof. vm_refl. Qed.
Lemma D_234ac : decode_any W_234ac = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234b0 : bv 32 := 0x00050493.
Lemma F_234b0 : fetch_word Plain.M.loaded_segments (0x234b0 : word) = Some W_234b0.
Proof. vm_refl. Qed.
Lemma D_234b0 : decode_any W_234b0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234b4 : bv 32 := 0x00002517.
Lemma F_234b4 : fetch_word Plain.M.loaded_segments (0x234b4 : word) = Some W_234b4.
Proof. vm_refl. Qed.
Lemma D_234b4 : decode_any W_234b4 = Some (Auipc 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234b8 : bv 32 := 0xe4453983.
Lemma F_234b8 : fetch_word Plain.M.loaded_segments (0x234b8 : word) = Some W_234b8.
Proof. vm_refl. Qed.
Lemma D_234b8 : decode_any W_234b8 = Some (Load SZ8 true 19 10 3652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234bc : bv 32 := 0x0009b503.
Lemma F_234bc : fetch_word Plain.M.loaded_segments (0x234bc : word) = Some W_234bc.
Proof. vm_refl. Qed.
Lemma D_234bc : decode_any W_234bc = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234c0 : bv 32 := 0x0ea13823.
Lemma F_234c0 : fetch_word Plain.M.loaded_segments (0x234c0 : word) = Some W_234c0.
Proof. vm_refl. Qed.
Lemma D_234c0 : decode_any W_234c0 = Some (Store SZ8 2 10 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234c4 : bv 32 := 0xfff00513.
Lemma F_234c4 : fetch_word Plain.M.loaded_segments (0x234c4 : word) = Some W_234c4.
Proof. vm_refl. Qed.
Lemma D_234c4 : decode_any W_234c4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234c8 : bv 32 := 0x06913023.
Lemma F_234c8 : fetch_word Plain.M.loaded_segments (0x234c8 : word) = Some W_234c8.
Proof. vm_refl. Qed.
Lemma D_234c8 : decode_any W_234c8 = Some (Store SZ8 2 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234cc : bv 32 := 0x00913823.
Lemma F_234cc : fetch_word Plain.M.loaded_segments (0x234cc : word) = Some W_234cc.
Proof. vm_refl. Qed.
Lemma D_234cc : decode_any W_234cc = Some (Store SZ8 2 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d0 : bv 32 := 0x00a13c23.
Lemma F_234d0 : fetch_word Plain.M.loaded_segments (0x234d0 : word) = Some W_234d0.
Proof. vm_refl. Qed.
Lemma D_234d0 : decode_any W_234d0 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d4 : bv 32 := 0x00810513.
Lemma F_234d4 : fetch_word Plain.M.loaded_segments (0x234d4 : word) = Some W_234d4.
Proof. vm_refl. Qed.
Lemma D_234d4 : decode_any W_234d4 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d8 : bv 32 := 0x00000593.
Lemma F_234d8 : fetch_word Plain.M.loaded_segments (0x234d8 : word) = Some W_234d8.
Proof. vm_refl. Qed.
Lemma D_234d8 : decode_any W_234d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234dc : bv 32 := 0x8ddff0ef.
Lemma F_234dc : fetch_word Plain.M.loaded_segments (0x234dc : word) = Some W_234dc.
Proof. vm_refl. Qed.
Lemma D_234dc : decode_any W_234dc = Some (Jal 1 2095324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234e0 : bv 32 := 0x00810513.
Lemma F_234e0 : fetch_word Plain.M.loaded_segments (0x234e0 : word) = Some W_234e0.
Proof. vm_refl. Qed.
Lemma D_234e0 : decode_any W_234e0 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234e4 : bv 32 := 0x00100613.
Lemma F_234e4 : fetch_word Plain.M.loaded_segments (0x234e4 : word) = Some W_234e4.
Proof. vm_refl. Qed.
Lemma D_234e4 : decode_any W_234e4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234e8 : bv 32 := 0xfff00693.
Lemma F_234e8 : fetch_word Plain.M.loaded_segments (0x234e8 : word) = Some W_234e8.
Proof. vm_refl. Qed.
Lemma D_234e8 : decode_any W_234e8 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234ec : bv 32 := 0x00090593.
Lemma F_234ec : fetch_word Plain.M.loaded_segments (0x234ec : word) = Some W_234ec.
Proof. vm_refl. Qed.
Lemma D_234ec : decode_any W_234ec = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234f0 : bv 32 := 0x9c9ff0ef.
Lemma F_234f0 : fetch_word Plain.M.loaded_segments (0x234f0 : word) = Some W_234f0.
Proof. vm_refl. Qed.
Lemma D_234f0 : decode_any W_234f0 = Some (Jal 1 2095560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234f4 : bv 32 := 0x02040063.
Lemma F_234f4 : fetch_word Plain.M.loaded_segments (0x234f4 : word) = Some W_234f4.
Proof. vm_refl. Qed.
Lemma D_234f4 : decode_any W_234f4 = Some (Branch BC_EQ 8 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23514 : bv 32 := 0x0009b583.
Lemma F_23514 : fetch_word Plain.M.loaded_segments (0x23514 : word) = Some W_23514.
Proof. vm_refl. Qed.
Lemma D_23514 : decode_any W_23514 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23518 : bv 32 := 0x0f013603.
Lemma F_23518 : fetch_word Plain.M.loaded_segments (0x23518 : word) = Some W_23518.
Proof. vm_refl. Qed.
Lemma D_23518 : decode_any W_23518 = Some (Load SZ8 true 12 2 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2351c : bv 32 := 0x02c59063.
Lemma F_2351c : fetch_word Plain.M.loaded_segments (0x2351c : word) = Some W_2351c.
Proof. vm_refl. Qed.
Lemma D_2351c : decode_any W_2351c = Some (Branch BC_NE 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23520 : bv 32 := 0x11813083.
Lemma F_23520 : fetch_word Plain.M.loaded_segments (0x23520 : word) = Some W_23520.
Proof. vm_refl. Qed.
Lemma D_23520 : decode_any W_23520 = Some (Load SZ8 true 1 2 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23524 : bv 32 := 0x11013403.
Lemma F_23524 : fetch_word Plain.M.loaded_segments (0x23524 : word) = Some W_23524.
Proof. vm_refl. Qed.
Lemma D_23524 : decode_any W_23524 = Some (Load SZ8 true 8 2 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23528 : bv 32 := 0x10813483.
Lemma F_23528 : fetch_word Plain.M.loaded_segments (0x23528 : word) = Some W_23528.
Proof. vm_refl. Qed.
Lemma D_23528 : decode_any W_23528 = Some (Load SZ8 true 9 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2352c : bv 32 := 0x10013903.
Lemma F_2352c : fetch_word Plain.M.loaded_segments (0x2352c : word) = Some W_2352c.
Proof. vm_refl. Qed.
Lemma D_2352c : decode_any W_2352c = Some (Load SZ8 true 18 2 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23530 : bv 32 := 0x0f813983.
Lemma F_23530 : fetch_word Plain.M.loaded_segments (0x23530 : word) = Some W_23530.
Proof. vm_refl. Qed.
Lemma D_23530 : decode_any W_23530 = Some (Load SZ8 true 19 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23534 : bv 32 := 0x12010113.
Lemma F_23534 : fetch_word Plain.M.loaded_segments (0x23534 : word) = Some W_23534.
Proof. vm_refl. Qed.
Lemma D_23534 : decode_any W_23534 = Some (OpImm ALU_ADD 2 2 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23538 : bv 32 := 0x00008067.
Lemma F_23538 : fetch_word Plain.M.loaded_segments (0x23538 : word) = Some W_23538.
Proof. vm_refl. Qed.
Lemma D_23538 : decode_any W_23538 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23540 : bv 32 := 0x0d00006f.
Lemma F_23540 : fetch_word Plain.M.loaded_segments (0x23540 : word) = Some W_23540.
Proof. vm_refl. Qed.
Lemma D_23540 : decode_any W_23540 = Some (Jal 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23544 : bv 32 := 0x0ff5f593.
Lemma F_23544 : fetch_word Plain.M.loaded_segments (0x23544 : word) = Some W_23544.
Proof. vm_refl. Qed.
Lemma D_23544 : decode_any W_23544 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23548 : bv 32 := 0x00757693.
Lemma F_23548 : fetch_word Plain.M.loaded_segments (0x23548 : word) = Some W_23548.
Proof. vm_refl. Qed.
Lemma D_23548 : decode_any W_23548 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2354c : bv 32 := 0x00c03733.
Lemma F_2354c : fetch_word Plain.M.loaded_segments (0x2354c : word) = Some W_2354c.
Proof. vm_refl. Qed.
Lemma D_2354c : decode_any W_2354c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23550 : bv 32 := 0x02068c63.
Lemma F_23550 : fetch_word Plain.M.loaded_segments (0x23550 : word) = Some W_23550.
Proof. vm_refl. Qed.
Lemma D_23550 : decode_any W_23550 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23554 : bv 32 := 0x02060a63.
Lemma F_23554 : fetch_word Plain.M.loaded_segments (0x23554 : word) = Some W_23554.
Proof. vm_refl. Qed.
Lemma D_23554 : decode_any W_23554 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23558 : bv 32 := 0x00150793.
Lemma F_23558 : fetch_word Plain.M.loaded_segments (0x23558 : word) = Some W_23558.
Proof. vm_refl. Qed.
Lemma D_23558 : decode_any W_23558 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2355c : bv 32 := 0x00100813.
Lemma F_2355c : fetch_word Plain.M.loaded_segments (0x2355c : word) = Some W_2355c.
Proof. vm_refl. Qed.
Lemma D_2355c : decode_any W_2355c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23560 : bv 32 := 0x00054703.
Lemma F_23560 : fetch_word Plain.M.loaded_segments (0x23560 : word) = Some W_23560.
Proof. vm_refl. Qed.
Lemma D_23560 : decode_any W_23560 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23564 : bv 32 := 0x00060693.
Lemma F_23564 : fetch_word Plain.M.loaded_segments (0x23564 : word) = Some W_23564.
Proof. vm_refl. Qed.
Lemma D_23564 : decode_any W_23564 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23568 : bv 32 := 0x06b70e63.
Lemma F_23568 : fetch_word Plain.M.loaded_segments (0x23568 : word) = Some W_23568.
Proof. vm_refl. Qed.
Lemma D_23568 : decode_any W_23568 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2356c : bv 32 := 0x00150513.
Lemma F_2356c : fetch_word Plain.M.loaded_segments (0x2356c : word) = Some W_2356c.
Proof. vm_refl. Qed.
Lemma D_2356c : decode_any W_2356c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23570 : bv 32 := 0xfff68613.
Lemma F_23570 : fetch_word Plain.M.loaded_segments (0x23570 : word) = Some W_23570.
Proof. vm_refl. Qed.
Lemma D_23570 : decode_any W_23570 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23574 : bv 32 := 0x0077f893.
Lemma F_23574 : fetch_word Plain.M.loaded_segments (0x23574 : word) = Some W_23574.
Proof. vm_refl. Qed.
Lemma D_23574 : decode_any W_23574 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23578 : bv 32 := 0x00c03733.
Lemma F_23578 : fetch_word Plain.M.loaded_segments (0x23578 : word) = Some W_23578.
Proof. vm_refl. Qed.
Lemma D_23578 : decode_any W_23578 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2357c : bv 32 := 0x00088663.
Lemma F_2357c : fetch_word Plain.M.loaded_segments (0x2357c : word) = Some W_2357c.
Proof. vm_refl. Qed.
Lemma D_2357c : decode_any W_2357c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23580 : bv 32 := 0x00178793.
Lemma F_23580 : fetch_word Plain.M.loaded_segments (0x23580 : word) = Some W_23580.
Proof. vm_refl. Qed.
Lemma D_23580 : decode_any W_23580 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23584 : bv 32 := 0xfd069ee3.
Lemma F_23584 : fetch_word Plain.M.loaded_segments (0x23584 : word) = Some W_23584.
Proof. vm_refl. Qed.
Lemma D_23584 : decode_any W_23584 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23588 : bv 32 := 0x06070863.
Lemma F_23588 : fetch_word Plain.M.loaded_segments (0x23588 : word) = Some W_23588.
Proof. vm_refl. Qed.
Lemma D_23588 : decode_any W_23588 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2358c : bv 32 := 0x00054683.
Lemma F_2358c : fetch_word Plain.M.loaded_segments (0x2358c : word) = Some W_2358c.
Proof. vm_refl. Qed.
Lemma D_2358c : decode_any W_2358c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23590 : bv 32 := 0x04b68663.
Lemma F_23590 : fetch_word Plain.M.loaded_segments (0x23590 : word) = Some W_23590.
Proof. vm_refl. Qed.
Lemma D_23590 : decode_any W_23590 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23594 : bv 32 := 0x00800693.
Lemma F_23594 : fetch_word Plain.M.loaded_segments (0x23594 : word) = Some W_23594.
Proof. vm_refl. Qed.
Lemma D_23594 : decode_any W_23594 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23598 : bv 32 := 0x04d66263.
Lemma F_23598 : fetch_word Plain.M.loaded_segments (0x23598 : word) = Some W_23598.
Proof. vm_refl. Qed.
Lemma D_23598 : decode_any W_23598 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2359c : bv 32 := 0xfffed697.
Lemma F_2359c : fetch_word Plain.M.loaded_segments (0x2359c : word) = Some W_2359c.
Proof. vm_refl. Qed.
Lemma D_2359c : decode_any W_2359c = Some (Auipc 13 1048557, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235a0 : bv 32 := 0x0046b683.
Lemma F_235a0 : fetch_word Plain.M.loaded_segments (0x235a0 : word) = Some W_235a0.
Proof. vm_refl. Qed.
Lemma D_235a0 : decode_any W_235a0 = Some (Load SZ8 true 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235a4 : bv 32 := 0xfffed717.
Lemma F_235a4 : fetch_word Plain.M.loaded_segments (0x235a4 : word) = Some W_235a4.
Proof. vm_refl. Qed.
Lemma D_235a4 : decode_any W_235a4 = Some (Auipc 14 1048557, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235a8 : bv 32 := 0xfe473703.
Lemma F_235a8 : fetch_word Plain.M.loaded_segments (0x235a8 : word) = Some W_235a8.
Proof. vm_refl. Qed.
Lemma D_235a8 : decode_any W_235a8 = Some (Load SZ8 true 14 14 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235ac : bv 32 := 0x00168793.
Lemma F_235ac : fetch_word Plain.M.loaded_segments (0x235ac : word) = Some W_235ac.
Proof. vm_refl. Qed.
Lemma D_235ac : decode_any W_235ac = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235b0 : bv 32 := 0x02f587b3.
Lemma F_235b0 : fetch_word Plain.M.loaded_segments (0x235b0 : word) = Some W_235b0.
Proof. vm_refl. Qed.
Lemma D_235b0 : decode_any W_235b0 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235b4 : bv 32 := 0x00700813.
Lemma F_235b4 : fetch_word Plain.M.loaded_segments (0x235b4 : word) = Some W_235b4.
Proof. vm_refl. Qed.
Lemma D_235b4 : decode_any W_235b4 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235b8 : bv 32 := 0x00053883.
Lemma F_235b8 : fetch_word Plain.M.loaded_segments (0x235b8 : word) = Some W_235b8.
Proof. vm_refl. Qed.
Lemma D_235b8 : decode_any W_235b8 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235bc : bv 32 := 0x00f8c8b3.
Lemma F_235bc : fetch_word Plain.M.loaded_segments (0x235bc : word) = Some W_235bc.
Proof. vm_refl. Qed.
Lemma D_235bc : decode_any W_235bc = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235c0 : bv 32 := 0x411682b3.
Lemma F_235c0 : fetch_word Plain.M.loaded_segments (0x235c0 : word) = Some W_235c0.
Proof. vm_refl. Qed.
Lemma D_235c0 : decode_any W_235c0 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235c4 : bv 32 := 0x0112e8b3.
Lemma F_235c4 : fetch_word Plain.M.loaded_segments (0x235c4 : word) = Some W_235c4.
Proof. vm_refl. Qed.
Lemma D_235c4 : decode_any W_235c4 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235c8 : bv 32 := 0x00e8f8b3.
Lemma F_235c8 : fetch_word Plain.M.loaded_segments (0x235c8 : word) = Some W_235c8.
Proof. vm_refl. Qed.
Lemma D_235c8 : decode_any W_235c8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235cc : bv 32 := 0x02e89a63.
Lemma F_235cc : fetch_word Plain.M.loaded_segments (0x235cc : word) = Some W_235cc.
Proof. vm_refl. Qed.
Lemma D_235cc : decode_any W_235cc = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235d0 : bv 32 := 0xff860613.
Lemma F_235d0 : fetch_word Plain.M.loaded_segments (0x235d0 : word) = Some W_235d0.
Proof. vm_refl. Qed.
Lemma D_235d0 : decode_any W_235d0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235d4 : bv 32 := 0x00850513.
Lemma F_235d4 : fetch_word Plain.M.loaded_segments (0x235d4 : word) = Some W_235d4.
Proof. vm_refl. Qed.
Lemma D_235d4 : decode_any W_235d4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235d8 : bv 32 := 0xfec860e3.
Lemma F_235d8 : fetch_word Plain.M.loaded_segments (0x235d8 : word) = Some W_235d8.
Proof. vm_refl. Qed.
Lemma D_235d8 : decode_any W_235d8 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235dc : bv 32 := 0x00060693.
Lemma F_235dc : fetch_word Plain.M.loaded_segments (0x235dc : word) = Some W_235dc.
Proof. vm_refl. Qed.
Lemma D_235dc : decode_any W_235dc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235e0 : bv 32 := 0x00060c63.
Lemma F_235e0 : fetch_word Plain.M.loaded_segments (0x235e0 : word) = Some W_235e0.
Proof. vm_refl. Qed.
Lemma D_235e0 : decode_any W_235e0 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235e4 : bv 32 := 0x00054603.
Lemma F_235e4 : fetch_word Plain.M.loaded_segments (0x235e4 : word) = Some W_235e4.
Proof. vm_refl. Qed.
Lemma D_235e4 : decode_any W_235e4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235e8 : bv 32 := 0x00b60a63.
Lemma F_235e8 : fetch_word Plain.M.loaded_segments (0x235e8 : word) = Some W_235e8.
Proof. vm_refl. Qed.
Lemma D_235e8 : decode_any W_235e8 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235ec : bv 32 := 0xfff68693.
Lemma F_235ec : fetch_word Plain.M.loaded_segments (0x235ec : word) = Some W_235ec.
Proof. vm_refl. Qed.
Lemma D_235ec : decode_any W_235ec = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.
