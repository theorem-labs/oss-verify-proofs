(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_77b5c : bv 32 := 0x000b2597.
Lemma F_77b5c : fetch_word ASEGS_I (0x77b5c : word) = Some W_77b5c.
Proof. vm_refl. Qed.
Lemma D_77b5c : decode_any W_77b5c = Some (Auipc 11 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b60 : bv 32 := 0x34c5b583.
Lemma F_77b60 : fetch_word ASEGS_I (0x77b60 : word) = Some W_77b60.
Proof. vm_refl. Qed.
Lemma D_77b60 : decode_any W_77b60 = Some (Load SZ8 true 11 11 844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b64 : bv 32 := 0x0005b583.
Lemma F_77b64 : fetch_word ASEGS_I (0x77b64 : word) = Some W_77b64.
Proof. vm_refl. Qed.
Lemma D_77b64 : decode_any W_77b64 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b68 : bv 32 := 0xfff58613.
Lemma F_77b68 : fetch_word ASEGS_I (0x77b68 : word) = Some W_77b68.
Proof. vm_refl. Qed.
Lemma D_77b68 : decode_any W_77b68 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b6c : bv 32 := 0x00c5b6b3.
Lemma F_77b6c : fetch_word ASEGS_I (0x77b6c : word) = Some W_77b6c.
Proof. vm_refl. Qed.
Lemma D_77b6c : decode_any W_77b6c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b70 : bv 32 := 0xfff68693.
Lemma F_77b70 : fetch_word ASEGS_I (0x77b70 : word) = Some W_77b70.
Proof. vm_refl. Qed.
Lemma D_77b70 : decode_any W_77b70 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b74 : bv 32 := 0x00c6f6b3.
Lemma F_77b74 : fetch_word ASEGS_I (0x77b74 : word) = Some W_77b74.
Proof. vm_refl. Qed.
Lemma D_77b74 : decode_any W_77b74 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b78 : bv 32 := 0x04a6f263.
Lemma F_77b78 : fetch_word ASEGS_I (0x77b78 : word) = Some W_77b78.
Proof. vm_refl. Qed.
Lemma D_77b78 : decode_any W_77b78 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b7c : bv 32 := 0x000b2697.
Lemma F_77b7c : fetch_word ASEGS_I (0x77b7c : word) = Some W_77b7c.
Proof. vm_refl. Qed.
Lemma D_77b7c : decode_any W_77b7c = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b80 : bv 32 := 0x3346b683.
Lemma F_77b80 : fetch_word ASEGS_I (0x77b80 : word) = Some W_77b80.
Proof. vm_refl. Qed.
Lemma D_77b80 : decode_any W_77b80 = Some (Load SZ8 true 13 13 820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b84 : bv 32 := 0x000b2717.
Lemma F_77b84 : fetch_word ASEGS_I (0x77b84 : word) = Some W_77b84.
Proof. vm_refl. Qed.
Lemma D_77b84 : decode_any W_77b84 = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b88 : bv 32 := 0x33473703.
Lemma F_77b88 : fetch_word ASEGS_I (0x77b88 : word) = Some W_77b88.
Proof. vm_refl. Qed.
Lemma D_77b88 : decode_any W_77b88 = Some (Load SZ8 true 14 14 820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b8c : bv 32 := 0x0006b803.
Lemma F_77b8c : fetch_word ASEGS_I (0x77b8c : word) = Some W_77b8c.
Proof. vm_refl. Qed.
Lemma D_77b8c : decode_any W_77b8c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b90 : bv 32 := 0x00073683.
Lemma F_77b90 : fetch_word ASEGS_I (0x77b90 : word) = Some W_77b90.
Proof. vm_refl. Qed.
Lemma D_77b90 : decode_any W_77b90 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b94 : bv 32 := 0xfff80793.
Lemma F_77b94 : fetch_word ASEGS_I (0x77b94 : word) = Some W_77b94.
Proof. vm_refl. Qed.
Lemma D_77b94 : decode_any W_77b94 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b98 : bv 32 := 0x00a7f463.
Lemma F_77b98 : fetch_word ASEGS_I (0x77b98 : word) = Some W_77b98.
Proof. vm_refl. Qed.
Lemma D_77b98 : decode_any W_77b98 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b9c : bv 32 := 0x02a6f063.
Lemma F_77b9c : fetch_word ASEGS_I (0x77b9c : word) = Some W_77b9c.
Proof. vm_refl. Qed.
Lemma D_77b9c : decode_any W_77b9c = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ba0 : bv 32 := 0x000b2717.
Lemma F_77ba0 : fetch_word ASEGS_I (0x77ba0 : word) = Some W_77ba0.
Proof. vm_refl. Qed.
Lemma D_77ba0 : decode_any W_77ba0 = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ba4 : bv 32 := 0x32073703.
Lemma F_77ba4 : fetch_word ASEGS_I (0x77ba4 : word) = Some W_77ba4.
Proof. vm_refl. Qed.
Lemma D_77ba4 : decode_any W_77ba4 = Some (Load SZ8 true 14 14 800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ba8 : bv 32 := 0x00073283.
Lemma F_77ba8 : fetch_word ASEGS_I (0x77ba8 : word) = Some W_77ba8.
Proof. vm_refl. Qed.
Lemma D_77ba8 : decode_any W_77ba8 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bac : bv 32 := 0x0032d713.
Lemma F_77bac : fetch_word ASEGS_I (0x77bac : word) = Some W_77bac.
Proof. vm_refl. Qed.
Lemma D_77bac : decode_any W_77bac = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bb0 : bv 32 := 0x00b708b3.
Lemma F_77bb0 : fetch_word ASEGS_I (0x77bb0 : word) = Some W_77bb0.
Proof. vm_refl. Qed.
Lemma D_77bb0 : decode_any W_77bb0 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bb4 : bv 32 := 0x00a2ea63.
Lemma F_77bb4 : fetch_word ASEGS_I (0x77bb4 : word) = Some W_77bb4.
Proof. vm_refl. Qed.
Lemma D_77bb4 : decode_any W_77bb4 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bb8 : bv 32 := 0x00a8f863.
Lemma F_77bb8 : fetch_word ASEGS_I (0x77bb8 : word) = Some W_77bb8.
Proof. vm_refl. Qed.
Lemma D_77bb8 : decode_any W_77bb8 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bbc : bv 32 := 0x00355513.
Lemma F_77bbc : fetch_word ASEGS_I (0x77bbc : word) = Some W_77bbc.
Proof. vm_refl. Qed.
Lemma D_77bbc : decode_any W_77bbc = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bc0 : bv 32 := 0x00a58533.
Lemma F_77bc0 : fetch_word ASEGS_I (0x77bc0 : word) = Some W_77bc0.
Proof. vm_refl. Qed.
Lemma D_77bc0 : decode_any W_77bc0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bc4 : bv 32 := 0x00008067.
Lemma F_77bc4 : fetch_word ASEGS_I (0x77bc4 : word) = Some W_77bc4.
Proof. vm_refl. Qed.
Lemma D_77bc4 : decode_any W_77bc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fe8 : bv 32 := 0xfc010113.
Lemma F_77fe8 : fetch_word ASEGS_I (0x77fe8 : word) = Some W_77fe8.
Proof. vm_refl. Qed.
Lemma D_77fe8 : decode_any W_77fe8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fec : bv 32 := 0x02113c23.
Lemma F_77fec : fetch_word ASEGS_I (0x77fec : word) = Some W_77fec.
Proof. vm_refl. Qed.
Lemma D_77fec : decode_any W_77fec = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ff0 : bv 32 := 0x02813823.
Lemma F_77ff0 : fetch_word ASEGS_I (0x77ff0 : word) = Some W_77ff0.
Proof. vm_refl. Qed.
Lemma D_77ff0 : decode_any W_77ff0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ff4 : bv 32 := 0x02913423.
Lemma F_77ff4 : fetch_word ASEGS_I (0x77ff4 : word) = Some W_77ff4.
Proof. vm_refl. Qed.
Lemma D_77ff4 : decode_any W_77ff4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ff8 : bv 32 := 0x03213023.
Lemma F_77ff8 : fetch_word ASEGS_I (0x77ff8 : word) = Some W_77ff8.
Proof. vm_refl. Qed.
Lemma D_77ff8 : decode_any W_77ff8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ffc : bv 32 := 0x01313c23.
Lemma F_77ffc : fetch_word ASEGS_I (0x77ffc : word) = Some W_77ffc.
Proof. vm_refl. Qed.
Lemma D_77ffc : decode_any W_77ffc = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78000 : bv 32 := 0x01413823.
Lemma F_78000 : fetch_word ASEGS_I (0x78000 : word) = Some W_78000.
Proof. vm_refl. Qed.
Lemma D_78000 : decode_any W_78000 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78004 : bv 32 := 0x01513423.
Lemma F_78004 : fetch_word ASEGS_I (0x78004 : word) = Some W_78004.
Proof. vm_refl. Qed.
Lemma D_78004 : decode_any W_78004 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78008 : bv 32 := 0x14058c63.
Lemma F_78008 : fetch_word ASEGS_I (0x78008 : word) = Some W_78008.
Proof. vm_refl. Qed.
Lemma D_78008 : decode_any W_78008 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7800c : bv 32 := 0x00058493.
Lemma F_7800c : fetch_word ASEGS_I (0x7800c : word) = Some W_7800c.
Proof. vm_refl. Qed.
Lemma D_7800c : decode_any W_7800c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78010 : bv 32 := 0x00050413.
Lemma F_78010 : fetch_word ASEGS_I (0x78010 : word) = Some W_78010.
Proof. vm_refl. Qed.
Lemma D_78010 : decode_any W_78010 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78014 : bv 32 := 0x000b2517.
Lemma F_78014 : fetch_word ASEGS_I (0x78014 : word) = Some W_78014.
Proof. vm_refl. Qed.
Lemma D_78014 : decode_any W_78014 = Some (Auipc 10 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78018 : bv 32 := 0xe9453a83.
Lemma F_78018 : fetch_word ASEGS_I (0x78018 : word) = Some W_78018.
Proof. vm_refl. Qed.
Lemma D_78018 : decode_any W_78018 = Some (Load SZ8 true 21 10 3732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7801c : bv 32 := 0x000ab583.
Lemma F_7801c : fetch_word ASEGS_I (0x7801c : word) = Some W_7801c.
Proof. vm_refl. Qed.
Lemma D_7801c : decode_any W_7801c = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78020 : bv 32 := 0xfff58513.
Lemma F_78020 : fetch_word ASEGS_I (0x78020 : word) = Some W_78020.
Proof. vm_refl. Qed.
Lemma D_78020 : decode_any W_78020 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78024 : bv 32 := 0x00a5b633.
Lemma F_78024 : fetch_word ASEGS_I (0x78024 : word) = Some W_78024.
Proof. vm_refl. Qed.
Lemma D_78024 : decode_any W_78024 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78028 : bv 32 := 0xfff60613.
Lemma F_78028 : fetch_word ASEGS_I (0x78028 : word) = Some W_78028.
Proof. vm_refl. Qed.
Lemma D_78028 : decode_any W_78028 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7802c : bv 32 := 0x00a67633.
Lemma F_7802c : fetch_word ASEGS_I (0x7802c : word) = Some W_7802c.
Proof. vm_refl. Qed.
Lemma D_7802c : decode_any W_7802c = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78030 : bv 32 := 0x04867263.
Lemma F_78030 : fetch_word ASEGS_I (0x78030 : word) = Some W_78030.
Proof. vm_refl. Qed.
Lemma D_78030 : decode_any W_78030 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78034 : bv 32 := 0x000b2697.
Lemma F_78034 : fetch_word ASEGS_I (0x78034 : word) = Some W_78034.
Proof. vm_refl. Qed.
Lemma D_78034 : decode_any W_78034 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78038 : bv 32 := 0xe7c6b683.
Lemma F_78038 : fetch_word ASEGS_I (0x78038 : word) = Some W_78038.
Proof. vm_refl. Qed.
Lemma D_78038 : decode_any W_78038 = Some (Load SZ8 true 13 13 3708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7803c : bv 32 := 0x000b2717.
Lemma F_7803c : fetch_word ASEGS_I (0x7803c : word) = Some W_7803c.
Proof. vm_refl. Qed.
Lemma D_7803c : decode_any W_7803c = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78040 : bv 32 := 0xe7c73703.
Lemma F_78040 : fetch_word ASEGS_I (0x78040 : word) = Some W_78040.
Proof. vm_refl. Qed.
Lemma D_78040 : decode_any W_78040 = Some (Load SZ8 true 14 14 3708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78044 : bv 32 := 0x0006b803.
Lemma F_78044 : fetch_word ASEGS_I (0x78044 : word) = Some W_78044.
Proof. vm_refl. Qed.
Lemma D_78044 : decode_any W_78044 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78048 : bv 32 := 0x00073683.
Lemma F_78048 : fetch_word ASEGS_I (0x78048 : word) = Some W_78048.
Proof. vm_refl. Qed.
Lemma D_78048 : decode_any W_78048 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7804c : bv 32 := 0xfff80793.
Lemma F_7804c : fetch_word ASEGS_I (0x7804c : word) = Some W_7804c.
Proof. vm_refl. Qed.
Lemma D_7804c : decode_any W_7804c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78050 : bv 32 := 0x0087f463.
Lemma F_78050 : fetch_word ASEGS_I (0x78050 : word) = Some W_78050.
Proof. vm_refl. Qed.
Lemma D_78050 : decode_any W_78050 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78054 : bv 32 := 0x0286f063.
Lemma F_78054 : fetch_word ASEGS_I (0x78054 : word) = Some W_78054.
Proof. vm_refl. Qed.
Lemma D_78054 : decode_any W_78054 = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78058 : bv 32 := 0x000b2717.
Lemma F_78058 : fetch_word ASEGS_I (0x78058 : word) = Some W_78058.
Proof. vm_refl. Qed.
Lemma D_78058 : decode_any W_78058 = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7805c : bv 32 := 0xe6873703.
Lemma F_7805c : fetch_word ASEGS_I (0x7805c : word) = Some W_7805c.
Proof. vm_refl. Qed.
Lemma D_7805c : decode_any W_7805c = Some (Load SZ8 true 14 14 3688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78060 : bv 32 := 0x00073283.
Lemma F_78060 : fetch_word ASEGS_I (0x78060 : word) = Some W_78060.
Proof. vm_refl. Qed.
Lemma D_78060 : decode_any W_78060 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78064 : bv 32 := 0x0032d713.
Lemma F_78064 : fetch_word ASEGS_I (0x78064 : word) = Some W_78064.
Proof. vm_refl. Qed.
Lemma D_78064 : decode_any W_78064 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78068 : bv 32 := 0x00b708b3.
Lemma F_78068 : fetch_word ASEGS_I (0x78068 : word) = Some W_78068.
Proof. vm_refl. Qed.
Lemma D_78068 : decode_any W_78068 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7806c : bv 32 := 0x1282e063.
Lemma F_7806c : fetch_word ASEGS_I (0x7806c : word) = Some W_7806c.
Proof. vm_refl. Qed.
Lemma D_7806c : decode_any W_7806c = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78070 : bv 32 := 0x1088fe63.
Lemma F_78070 : fetch_word ASEGS_I (0x78070 : word) = Some W_78070.
Proof. vm_refl. Qed.
Lemma D_78070 : decode_any W_78070 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78074 : bv 32 := 0x00848933.
Lemma F_78074 : fetch_word ASEGS_I (0x78074 : word) = Some W_78074.
Proof. vm_refl. Qed.
Lemma D_78074 : decode_any W_78074 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78078 : bv 32 := 0x05267263.
Lemma F_78078 : fetch_word ASEGS_I (0x78078 : word) = Some W_78078.
Proof. vm_refl. Qed.
Lemma D_78078 : decode_any W_78078 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7807c : bv 32 := 0x000b2617.
Lemma F_7807c : fetch_word ASEGS_I (0x7807c : word) = Some W_7807c.
Proof. vm_refl. Qed.
Lemma D_7807c : decode_any W_7807c = Some (Auipc 12 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78080 : bv 32 := 0xe3463603.
Lemma F_78080 : fetch_word ASEGS_I (0x78080 : word) = Some W_78080.
Proof. vm_refl. Qed.
Lemma D_78080 : decode_any W_78080 = Some (Load SZ8 true 12 12 3636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78084 : bv 32 := 0x000b2697.
Lemma F_78084 : fetch_word ASEGS_I (0x78084 : word) = Some W_78084.
Proof. vm_refl. Qed.
Lemma D_78084 : decode_any W_78084 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78088 : bv 32 := 0xe346b683.
Lemma F_78088 : fetch_word ASEGS_I (0x78088 : word) = Some W_78088.
Proof. vm_refl. Qed.
Lemma D_78088 : decode_any W_78088 = Some (Load SZ8 true 13 13 3636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7808c : bv 32 := 0x00063783.
Lemma F_7808c : fetch_word ASEGS_I (0x7808c : word) = Some W_7808c.
Proof. vm_refl. Qed.
Lemma D_7808c : decode_any W_7808c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78090 : bv 32 := 0x0006b603.
Lemma F_78090 : fetch_word ASEGS_I (0x78090 : word) = Some W_78090.
Proof. vm_refl. Qed.
Lemma D_78090 : decode_any W_78090 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78094 : bv 32 := 0xfff78713.
Lemma F_78094 : fetch_word ASEGS_I (0x78094 : word) = Some W_78094.
Proof. vm_refl. Qed.
Lemma D_78094 : decode_any W_78094 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78098 : bv 32 := 0x01277463.
Lemma F_78098 : fetch_word ASEGS_I (0x78098 : word) = Some W_78098.
Proof. vm_refl. Qed.
Lemma D_78098 : decode_any W_78098 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7809c : bv 32 := 0x03267063.
Lemma F_7809c : fetch_word ASEGS_I (0x7809c : word) = Some W_7809c.
Proof. vm_refl. Qed.
Lemma D_7809c : decode_any W_7809c = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780a0 : bv 32 := 0x000b2697.
Lemma F_780a0 : fetch_word ASEGS_I (0x780a0 : word) = Some W_780a0.
Proof. vm_refl. Qed.
Lemma D_780a0 : decode_any W_780a0 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780a4 : bv 32 := 0xe206b683.
Lemma F_780a4 : fetch_word ASEGS_I (0x780a4 : word) = Some W_780a4.
Proof. vm_refl. Qed.
Lemma D_780a4 : decode_any W_780a4 = Some (Load SZ8 true 13 13 3616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780a8 : bv 32 := 0x0006b883.
Lemma F_780a8 : fetch_word ASEGS_I (0x780a8 : word) = Some W_780a8.
Proof. vm_refl. Qed.
Lemma D_780a8 : decode_any W_780a8 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780ac : bv 32 := 0x0038d693.
Lemma F_780ac : fetch_word ASEGS_I (0x780ac : word) = Some W_780ac.
Proof. vm_refl. Qed.
Lemma D_780ac : decode_any W_780ac = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780b0 : bv 32 := 0x00b68833.
Lemma F_780b0 : fetch_word ASEGS_I (0x780b0 : word) = Some W_780b0.
Proof. vm_refl. Qed.
Lemma D_780b0 : decode_any W_780b0 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780b4 : bv 32 := 0x1328e463.
Lemma F_780b4 : fetch_word ASEGS_I (0x780b4 : word) = Some W_780b4.
Proof. vm_refl. Qed.
Lemma D_780b4 : decode_any W_780b4 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780b8 : bv 32 := 0x13287263.
Lemma F_780b8 : fetch_word ASEGS_I (0x780b8 : word) = Some W_780b8.
Proof. vm_refl. Qed.
Lemma D_780b8 : decode_any W_780b8 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780bc : bv 32 := 0x23247863.
Lemma F_780bc : fetch_word ASEGS_I (0x780bc : word) = Some W_780bc.
Proof. vm_refl. Qed.
Lemma D_780bc : decode_any W_780bc = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780c0 : bv 32 := 0x00740513.
Lemma F_780c0 : fetch_word ASEGS_I (0x780c0 : word) = Some W_780c0.
Proof. vm_refl. Qed.
Lemma D_780c0 : decode_any W_780c0 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780c4 : bv 32 := 0xff857513.
Lemma F_780c4 : fetch_word ASEGS_I (0x780c4 : word) = Some W_780c4.
Proof. vm_refl. Qed.
Lemma D_780c4 : decode_any W_780c4 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780c8 : bv 32 := 0xff897a13.
Lemma F_780c8 : fetch_word ASEGS_I (0x780c8 : word) = Some W_780c8.
Proof. vm_refl. Qed.
Lemma D_780c8 : decode_any W_780c8 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780cc : bv 32 := 0xa91ff0ef.
Lemma F_780cc : fetch_word ASEGS_I (0x780cc : word) = Some W_780cc.
Proof. vm_refl. Qed.
Lemma D_780cc : decode_any W_780cc = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780d0 : bv 32 := 0x00050993.
Lemma F_780d0 : fetch_word ASEGS_I (0x780d0 : word) = Some W_780d0.
Proof. vm_refl. Qed.
Lemma D_780d0 : decode_any W_780d0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780d4 : bv 32 := 0x000a0513.
Lemma F_780d4 : fetch_word ASEGS_I (0x780d4 : word) = Some W_780d4.
Proof. vm_refl. Qed.
Lemma D_780d4 : decode_any W_780d4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780d8 : bv 32 := 0xa85ff0ef.
Lemma F_780d8 : fetch_word ASEGS_I (0x780d8 : word) = Some W_780d8.
Proof. vm_refl. Qed.
Lemma D_780d8 : decode_any W_780d8 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780dc : bv 32 := 0x000ab583.
Lemma F_780dc : fetch_word ASEGS_I (0x780dc : word) = Some W_780dc.
Proof. vm_refl. Qed.
Lemma D_780dc : decode_any W_780dc = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780e0 : bv 32 := 0x00345613.
Lemma F_780e0 : fetch_word ASEGS_I (0x780e0 : word) = Some W_780e0.
Proof. vm_refl. Qed.
Lemma D_780e0 : decode_any W_780e0 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780e4 : bv 32 := 0x00c58633.
Lemma F_780e4 : fetch_word ASEGS_I (0x780e4 : word) = Some W_780e4.
Proof. vm_refl. Qed.
Lemma D_780e4 : decode_any W_780e4 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780e8 : bv 32 := 0x00060603.
Lemma F_780e8 : fetch_word ASEGS_I (0x780e8 : word) = Some W_780e8.
Proof. vm_refl. Qed.
Lemma D_780e8 : decode_any W_780e8 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780ec : bv 32 := 0x00060663.
Lemma F_780ec : fetch_word ASEGS_I (0x780ec : word) = Some W_780ec.
Proof. vm_refl. Qed.
Lemma D_780ec : decode_any W_780ec = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f0 : bv 32 := 0x00747693.
Lemma F_780f0 : fetch_word ASEGS_I (0x780f0 : word) = Some W_780f0.
Proof. vm_refl. Qed.
Lemma D_780f0 : decode_any W_780f0 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f4 : bv 32 := 0x02c6d063.
Lemma F_780f4 : fetch_word ASEGS_I (0x780f4 : word) = Some W_780f4.
Proof. vm_refl. Qed.
Lemma D_780f4 : decode_any W_780f4 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f8 : bv 32 := 0xfff90913.
Lemma F_780f8 : fetch_word ASEGS_I (0x780f8 : word) = Some W_780f8.
Proof. vm_refl. Qed.
Lemma D_780f8 : decode_any W_780f8 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780fc : bv 32 := 0x00395613.
Lemma F_780fc : fetch_word ASEGS_I (0x780fc : word) = Some W_780fc.
Proof. vm_refl. Qed.
Lemma D_780fc : decode_any W_780fc = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78100 : bv 32 := 0x00c585b3.
Lemma F_78100 : fetch_word ASEGS_I (0x78100 : word) = Some W_78100.
Proof. vm_refl. Qed.
Lemma D_78100 : decode_any W_78100 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78104 : bv 32 := 0x00058583.
Lemma F_78104 : fetch_word ASEGS_I (0x78104 : word) = Some W_78104.
Proof. vm_refl. Qed.
Lemma D_78104 : decode_any W_78104 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78108 : bv 32 := 0x04058263.
Lemma F_78108 : fetch_word ASEGS_I (0x78108 : word) = Some W_78108.
Proof. vm_refl. Qed.
Lemma D_78108 : decode_any W_78108 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7810c : bv 32 := 0x00797613.
Lemma F_7810c : fetch_word ASEGS_I (0x7810c : word) = Some W_7810c.
Proof. vm_refl. Qed.
Lemma D_7810c : decode_any W_7810c = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78110 : bv 32 := 0x02b64e63.
Lemma F_78110 : fetch_word ASEGS_I (0x78110 : word) = Some W_78110.
Proof. vm_refl. Qed.
Lemma D_78110 : decode_any W_78110 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78114 : bv 32 := 0x000ab503.
Lemma F_78114 : fetch_word ASEGS_I (0x78114 : word) = Some W_78114.
Proof. vm_refl. Qed.
Lemma D_78114 : decode_any W_78114 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78118 : bv 32 := 0x00040593.
Lemma F_78118 : fetch_word ASEGS_I (0x78118 : word) = Some W_78118.
Proof. vm_refl. Qed.
Lemma D_78118 : decode_any W_78118 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7811c : bv 32 := 0x0140006f.
Lemma F_7811c : fetch_word ASEGS_I (0x7811c : word) = Some W_7811c.
Proof. vm_refl. Qed.
Lemma D_7811c : decode_any W_7811c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78120 : bv 32 := 0x00140413.
Lemma F_78120 : fetch_word ASEGS_I (0x78120 : word) = Some W_78120.
Proof. vm_refl. Qed.
Lemma D_78120 : decode_any W_78120 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78124 : bv 32 := 0xfff48493.
Lemma F_78124 : fetch_word ASEGS_I (0x78124 : word) = Some W_78124.
Proof. vm_refl. Qed.
Lemma D_78124 : decode_any W_78124 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78128 : bv 32 := 0x00158593.
Lemma F_78128 : fetch_word ASEGS_I (0x78128 : word) = Some W_78128.
Proof. vm_refl. Qed.
Lemma D_78128 : decode_any W_78128 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7812c : bv 32 := 0x1e048063.
Lemma F_7812c : fetch_word ASEGS_I (0x7812c : word) = Some W_7812c.
Proof. vm_refl. Qed.
Lemma D_7812c : decode_any W_7812c = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78130 : bv 32 := 0x00345613.
Lemma F_78130 : fetch_word ASEGS_I (0x78130 : word) = Some W_78130.
Proof. vm_refl. Qed.
Lemma D_78130 : decode_any W_78130 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78134 : bv 32 := 0x00c50633.
Lemma F_78134 : fetch_word ASEGS_I (0x78134 : word) = Some W_78134.
Proof. vm_refl. Qed.
Lemma D_78134 : decode_any W_78134 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78138 : bv 32 := 0x00060603.
Lemma F_78138 : fetch_word ASEGS_I (0x78138 : word) = Some W_78138.
Proof. vm_refl. Qed.
Lemma D_78138 : decode_any W_78138 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7813c : bv 32 := 0xfe0602e3.
Lemma F_7813c : fetch_word ASEGS_I (0x7813c : word) = Some W_7813c.
Proof. vm_refl. Qed.
Lemma D_7813c : decode_any W_7813c = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78140 : bv 32 := 0x0075f693.
Lemma F_78140 : fetch_word ASEGS_I (0x78140 : word) = Some W_78140.
Proof. vm_refl. Qed.
Lemma D_78140 : decode_any W_78140 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78144 : bv 32 := 0xfcc6cee3.
Lemma F_78144 : fetch_word ASEGS_I (0x78144 : word) = Some W_78144.
Proof. vm_refl. Qed.
Lemma D_78144 : decode_any W_78144 = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78148 : bv 32 := 0x01c0006f.
Lemma F_78148 : fetch_word ASEGS_I (0x78148 : word) = Some W_78148.
Proof. vm_refl. Qed.
Lemma D_78148 : decode_any W_78148 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7814c : bv 32 := 0x00a9fa63.
Lemma F_7814c : fetch_word ASEGS_I (0x7814c : word) = Some W_7814c.
Proof. vm_refl. Qed.
Lemma D_7814c : decode_any W_7814c = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78150 : bv 32 := 0x413505b3.
Lemma F_78150 : fetch_word ASEGS_I (0x78150 : word) = Some W_78150.
Proof. vm_refl. Qed.
Lemma D_78150 : decode_any W_78150 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78154 : bv 32 := 0x00098513.
Lemma F_78154 : fetch_word ASEGS_I (0x78154 : word) = Some W_78154.
Proof. vm_refl. Qed.
Lemma D_78154 : decode_any W_78154 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.
