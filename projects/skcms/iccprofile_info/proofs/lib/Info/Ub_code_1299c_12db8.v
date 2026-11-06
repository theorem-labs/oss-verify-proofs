(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1299c : bv 32 := 0xffffe197.
Lemma F_1299c : fetch_word Ubsan.M.loaded_segments (0x1299c : word) = Some W_1299c.
Proof. vm_refl. Qed.
Lemma D_1299c : decode_any W_1299c = Some (Auipc 3 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_129a0 : bv 32 := 0xe6418193.
Lemma F_129a0 : fetch_word Ubsan.M.loaded_segments (0x129a0 : word) = Some W_129a0.
Proof. vm_refl. Qed.
Lemma D_129a0 : decode_any W_129a0 = Some (OpImm ALU_ADD 3 3 3684, 4%Z).
Proof. vm_refl. Qed.

Definition W_129a4 : bv 32 := 0x00010513.
Lemma F_129a4 : fetch_word Ubsan.M.loaded_segments (0x129a4 : word) = Some W_129a4.
Proof. vm_refl. Qed.
Lemma D_129a4 : decode_any W_129a4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129a8 : bv 32 := 0xfffed597.
Lemma F_129a8 : fetch_word Ubsan.M.loaded_segments (0x129a8 : word) = Some W_129a8.
Proof. vm_refl. Qed.
Lemma D_129a8 : decode_any W_129a8 = Some (Auipc 11 1048557, 4%Z).
Proof. vm_refl. Qed.

Definition W_129ac : bv 32 := 0x65858593.
Lemma F_129ac : fetch_word Ubsan.M.loaded_segments (0x129ac : word) = Some W_129ac.
Proof. vm_refl. Qed.
Lemma D_129ac : decode_any W_129ac = Some (OpImm ALU_ADD 11 11 1624, 4%Z).
Proof. vm_refl. Qed.

Definition W_129b0 : bv 32 := 0xff017113.
Lemma F_129b0 : fetch_word Ubsan.M.loaded_segments (0x129b0 : word) = Some W_129b0.
Proof. vm_refl. Qed.
Lemma D_129b0 : decode_any W_129b0 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_129b4 : bv 32 := 0x0040006f.
Lemma F_129b4 : fetch_word Ubsan.M.loaded_segments (0x129b4 : word) = Some W_129b4.
Proof. vm_refl. Qed.
Lemma D_129b4 : decode_any W_129b4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_129b8 : bv 32 := 0x00052583.
Lemma F_129b8 : fetch_word Ubsan.M.loaded_segments (0x129b8 : word) = Some W_129b8.
Proof. vm_refl. Qed.
Lemma D_129b8 : decode_any W_129b8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129bc : bv 32 := 0x0000d617.
Lemma F_129bc : fetch_word Ubsan.M.loaded_segments (0x129bc : word) = Some W_129bc.
Proof. vm_refl. Qed.
Lemma D_129bc : decode_any W_129bc = Some (Auipc 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_129c0 : bv 32 := 0x0000d697.
Lemma F_129c0 : fetch_word Ubsan.M.loaded_segments (0x129c0 : word) = Some W_129c0.
Proof. vm_refl. Qed.
Lemma D_129c0 : decode_any W_129c0 = Some (Auipc 13 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_129c4 : bv 32 := 0x0000d717.
Lemma F_129c4 : fetch_word Ubsan.M.loaded_segments (0x129c4 : word) = Some W_129c4.
Proof. vm_refl. Qed.
Lemma D_129c4 : decode_any W_129c4 = Some (Auipc 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_129c8 : bv 32 := 0x72c63783.
Lemma F_129c8 : fetch_word Ubsan.M.loaded_segments (0x129c8 : word) = Some W_129c8.
Proof. vm_refl. Qed.
Lemma D_129c8 : decode_any W_129c8 = Some (Load SZ8 true 15 12 1836, 4%Z).
Proof. vm_refl. Qed.

Definition W_129cc : bv 32 := 0x7306b683.
Lemma F_129cc : fetch_word Ubsan.M.loaded_segments (0x129cc : word) = Some W_129cc.
Proof. vm_refl. Qed.
Lemma D_129cc : decode_any W_129cc = Some (Load SZ8 true 13 13 1840, 4%Z).
Proof. vm_refl. Qed.

Definition W_129d0 : bv 32 := 0x73473703.
Lemma F_129d0 : fetch_word Ubsan.M.loaded_segments (0x129d0 : word) = Some W_129d0.
Proof. vm_refl. Qed.
Lemma D_129d0 : decode_any W_129d0 = Some (Load SZ8 true 14 14 1844, 4%Z).
Proof. vm_refl. Qed.

Definition W_129d4 : bv 32 := 0x00850613.
Lemma F_129d4 : fetch_word Ubsan.M.loaded_segments (0x129d4 : word) = Some W_129d4.
Proof. vm_refl. Qed.
Lemma D_129d4 : decode_any W_129d4 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_129d8 : bv 32 := 0x00078513.
Lemma F_129d8 : fetch_word Ubsan.M.loaded_segments (0x129d8 : word) = Some W_129d8.
Proof. vm_refl. Qed.
Lemma D_129d8 : decode_any W_129d8 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129dc : bv 32 := 0x00000793.
Lemma F_129dc : fetch_word Ubsan.M.loaded_segments (0x129dc : word) = Some W_129dc.
Proof. vm_refl. Qed.
Lemma D_129dc : decode_any W_129dc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129e0 : bv 32 := 0x5600406f.
Lemma F_129e0 : fetch_word Ubsan.M.loaded_segments (0x129e0 : word) = Some W_129e0.
Proof. vm_refl. Qed.
Lemma D_129e0 : decode_any W_129e0 = Some (Jal 0 17760, 4%Z).
Proof. vm_refl. Qed.

Definition W_129e4 : bv 32 := 0xff010113.
Lemma F_129e4 : fetch_word Ubsan.M.loaded_segments (0x129e4 : word) = Some W_129e4.
Proof. vm_refl. Qed.
Lemma D_129e4 : decode_any W_129e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_129e8 : bv 32 := 0x00113423.
Lemma F_129e8 : fetch_word Ubsan.M.loaded_segments (0x129e8 : word) = Some W_129e8.
Proof. vm_refl. Qed.
Lemma D_129e8 : decode_any W_129e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_129ec : bv 32 := 0x00813023.
Lemma F_129ec : fetch_word Ubsan.M.loaded_segments (0x129ec : word) = Some W_129ec.
Proof. vm_refl. Qed.
Lemma D_129ec : decode_any W_129ec = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129f0 : bv 32 := 0x01010413.
Lemma F_129f0 : fetch_word Ubsan.M.loaded_segments (0x129f0 : word) = Some W_129f0.
Proof. vm_refl. Qed.
Lemma D_129f0 : decode_any W_129f0 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_129f4 : bv 32 := 0x0000f517.
Lemma F_129f4 : fetch_word Ubsan.M.loaded_segments (0x129f4 : word) = Some W_129f4.
Proof. vm_refl. Qed.
Lemma D_129f4 : decode_any W_129f4 = Some (Auipc 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_129f8 : bv 32 := 0x98c50513.
Lemma F_129f8 : fetch_word Ubsan.M.loaded_segments (0x129f8 : word) = Some W_129f8.
Proof. vm_refl. Qed.
Lemma D_129f8 : decode_any W_129f8 = Some (OpImm ALU_ADD 10 10 2444, 4%Z).
Proof. vm_refl. Qed.

Definition W_129fc : bv 32 := 0x00054503.
Lemma F_129fc : fetch_word Ubsan.M.loaded_segments (0x129fc : word) = Some W_129fc.
Proof. vm_refl. Qed.
Lemma D_129fc : decode_any W_129fc = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a00 : bv 32 := 0x00157513.
Lemma F_12a00 : fetch_word Ubsan.M.loaded_segments (0x12a00 : word) = Some W_12a00.
Proof. vm_refl. Qed.
Lemma D_12a00 : decode_any W_12a00 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a04 : bv 32 := 0x00050663.
Lemma F_12a04 : fetch_word Ubsan.M.loaded_segments (0x12a04 : word) = Some W_12a04.
Proof. vm_refl. Qed.
Lemma D_12a04 : decode_any W_12a04 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a10 : bv 32 := 0x0000f517.
Lemma F_12a10 : fetch_word Ubsan.M.loaded_segments (0x12a10 : word) = Some W_12a10.
Proof. vm_refl. Qed.
Lemma D_12a10 : decode_any W_12a10 = Some (Auipc 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a14 : bv 32 := 0x97050593.
Lemma F_12a14 : fetch_word Ubsan.M.loaded_segments (0x12a14 : word) = Some W_12a14.
Proof. vm_refl. Qed.
Lemma D_12a14 : decode_any W_12a14 = Some (OpImm ALU_ADD 11 10 2416, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a18 : bv 32 := 0x00100513.
Lemma F_12a18 : fetch_word Ubsan.M.loaded_segments (0x12a18 : word) = Some W_12a18.
Proof. vm_refl. Qed.
Lemma D_12a18 : decode_any W_12a18 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a1c : bv 32 := 0x00a58023.
Lemma F_12a1c : fetch_word Ubsan.M.loaded_segments (0x12a1c : word) = Some W_12a1c.
Proof. vm_refl. Qed.
Lemma D_12a1c : decode_any W_12a1c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a20 : bv 32 := 0x0000d517.
Lemma F_12a20 : fetch_word Ubsan.M.loaded_segments (0x12a20 : word) = Some W_12a20.
Proof. vm_refl. Qed.
Lemma D_12a20 : decode_any W_12a20 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a24 : bv 32 := 0x6e053503.
Lemma F_12a24 : fetch_word Ubsan.M.loaded_segments (0x12a24 : word) = Some W_12a24.
Proof. vm_refl. Qed.
Lemma D_12a24 : decode_any W_12a24 = Some (Load SZ8 true 10 10 1760, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a28 : bv 32 := 0x02050063.
Lemma F_12a28 : fetch_word Ubsan.M.loaded_segments (0x12a28 : word) = Some W_12a28.
Proof. vm_refl. Qed.
Lemma D_12a28 : decode_any W_12a28 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a48 : bv 32 := 0x00813083.
Lemma F_12a48 : fetch_word Ubsan.M.loaded_segments (0x12a48 : word) = Some W_12a48.
Proof. vm_refl. Qed.
Lemma D_12a48 : decode_any W_12a48 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a4c : bv 32 := 0x00013403.
Lemma F_12a4c : fetch_word Ubsan.M.loaded_segments (0x12a4c : word) = Some W_12a4c.
Proof. vm_refl. Qed.
Lemma D_12a4c : decode_any W_12a4c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a50 : bv 32 := 0x01010113.
Lemma F_12a50 : fetch_word Ubsan.M.loaded_segments (0x12a50 : word) = Some W_12a50.
Proof. vm_refl. Qed.
Lemma D_12a50 : decode_any W_12a50 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a54 : bv 32 := 0x00008067.
Lemma F_12a54 : fetch_word Ubsan.M.loaded_segments (0x12a54 : word) = Some W_12a54.
Proof. vm_refl. Qed.
Lemma D_12a54 : decode_any W_12a54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a58 : bv 32 := 0xff010113.
Lemma F_12a58 : fetch_word Ubsan.M.loaded_segments (0x12a58 : word) = Some W_12a58.
Proof. vm_refl. Qed.
Lemma D_12a58 : decode_any W_12a58 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a5c : bv 32 := 0x00113423.
Lemma F_12a5c : fetch_word Ubsan.M.loaded_segments (0x12a5c : word) = Some W_12a5c.
Proof. vm_refl. Qed.
Lemma D_12a5c : decode_any W_12a5c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a60 : bv 32 := 0x00813023.
Lemma F_12a60 : fetch_word Ubsan.M.loaded_segments (0x12a60 : word) = Some W_12a60.
Proof. vm_refl. Qed.
Lemma D_12a60 : decode_any W_12a60 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a64 : bv 32 := 0x01010413.
Lemma F_12a64 : fetch_word Ubsan.M.loaded_segments (0x12a64 : word) = Some W_12a64.
Proof. vm_refl. Qed.
Lemma D_12a64 : decode_any W_12a64 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a68 : bv 32 := 0x0000f517.
Lemma F_12a68 : fetch_word Ubsan.M.loaded_segments (0x12a68 : word) = Some W_12a68.
Proof. vm_refl. Qed.
Lemma D_12a68 : decode_any W_12a68 = Some (Auipc 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a6c : bv 32 := 0x96050513.
Lemma F_12a6c : fetch_word Ubsan.M.loaded_segments (0x12a6c : word) = Some W_12a6c.
Proof. vm_refl. Qed.
Lemma D_12a6c : decode_any W_12a6c = Some (OpImm ALU_ADD 10 10 2400, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a70 : bv 32 := 0x00054503.
Lemma F_12a70 : fetch_word Ubsan.M.loaded_segments (0x12a70 : word) = Some W_12a70.
Proof. vm_refl. Qed.
Lemma D_12a70 : decode_any W_12a70 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a74 : bv 32 := 0x00157513.
Lemma F_12a74 : fetch_word Ubsan.M.loaded_segments (0x12a74 : word) = Some W_12a74.
Proof. vm_refl. Qed.
Lemma D_12a74 : decode_any W_12a74 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a78 : bv 32 := 0x00050663.
Lemma F_12a78 : fetch_word Ubsan.M.loaded_segments (0x12a78 : word) = Some W_12a78.
Proof. vm_refl. Qed.
Lemma D_12a78 : decode_any W_12a78 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a84 : bv 32 := 0x0000f517.
Lemma F_12a84 : fetch_word Ubsan.M.loaded_segments (0x12a84 : word) = Some W_12a84.
Proof. vm_refl. Qed.
Lemma D_12a84 : decode_any W_12a84 = Some (Auipc 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a88 : bv 32 := 0x94450593.
Lemma F_12a88 : fetch_word Ubsan.M.loaded_segments (0x12a88 : word) = Some W_12a88.
Proof. vm_refl. Qed.
Lemma D_12a88 : decode_any W_12a88 = Some (OpImm ALU_ADD 11 10 2372, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a8c : bv 32 := 0x00100513.
Lemma F_12a8c : fetch_word Ubsan.M.loaded_segments (0x12a8c : word) = Some W_12a8c.
Proof. vm_refl. Qed.
Lemma D_12a8c : decode_any W_12a8c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a90 : bv 32 := 0x00a58023.
Lemma F_12a90 : fetch_word Ubsan.M.loaded_segments (0x12a90 : word) = Some W_12a90.
Proof. vm_refl. Qed.
Lemma D_12a90 : decode_any W_12a90 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a94 : bv 32 := 0x0000d517.
Lemma F_12a94 : fetch_word Ubsan.M.loaded_segments (0x12a94 : word) = Some W_12a94.
Proof. vm_refl. Qed.
Lemma D_12a94 : decode_any W_12a94 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a98 : bv 32 := 0x67453503.
Lemma F_12a98 : fetch_word Ubsan.M.loaded_segments (0x12a98 : word) = Some W_12a98.
Proof. vm_refl. Qed.
Lemma D_12a98 : decode_any W_12a98 = Some (Load SZ8 true 10 10 1652, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a9c : bv 32 := 0x00050e63.
Lemma F_12a9c : fetch_word Ubsan.M.loaded_segments (0x12a9c : word) = Some W_12a9c.
Proof. vm_refl. Qed.
Lemma D_12a9c : decode_any W_12a9c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ab8 : bv 32 := 0x0000d517.
Lemma F_12ab8 : fetch_word Ubsan.M.loaded_segments (0x12ab8 : word) = Some W_12ab8.
Proof. vm_refl. Qed.
Lemma D_12ab8 : decode_any W_12ab8 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12abc : bv 32 := 0x65853503.
Lemma F_12abc : fetch_word Ubsan.M.loaded_segments (0x12abc : word) = Some W_12abc.
Proof. vm_refl. Qed.
Lemma D_12abc : decode_any W_12abc = Some (Load SZ8 true 10 10 1624, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ac0 : bv 32 := 0x00050c63.
Lemma F_12ac0 : fetch_word Ubsan.M.loaded_segments (0x12ac0 : word) = Some W_12ac0.
Proof. vm_refl. Qed.
Lemma D_12ac0 : decode_any W_12ac0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ad8 : bv 32 := 0x00813083.
Lemma F_12ad8 : fetch_word Ubsan.M.loaded_segments (0x12ad8 : word) = Some W_12ad8.
Proof. vm_refl. Qed.
Lemma D_12ad8 : decode_any W_12ad8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12adc : bv 32 := 0x00013403.
Lemma F_12adc : fetch_word Ubsan.M.loaded_segments (0x12adc : word) = Some W_12adc.
Proof. vm_refl. Qed.
Lemma D_12adc : decode_any W_12adc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ae0 : bv 32 := 0x01010113.
Lemma F_12ae0 : fetch_word Ubsan.M.loaded_segments (0x12ae0 : word) = Some W_12ae0.
Proof. vm_refl. Qed.
Lemma D_12ae0 : decode_any W_12ae0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ae4 : bv 32 := 0x00008067.
Lemma F_12ae4 : fetch_word Ubsan.M.loaded_segments (0x12ae4 : word) = Some W_12ae4.
Proof. vm_refl. Qed.
Lemma D_12ae4 : decode_any W_12ae4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b3c : bv 32 := 0x24050a63.
Lemma F_12b3c : fetch_word Ubsan.M.loaded_segments (0x12b3c : word) = Some W_12b3c.
Proof. vm_refl. Qed.
Lemma D_12b3c : decode_any W_12b3c = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b40 : bv 32 := 0x00050b93.
Lemma F_12b40 : fetch_word Ubsan.M.loaded_segments (0x12b40 : word) = Some W_12b40.
Proof. vm_refl. Qed.
Lemma D_12b40 : decode_any W_12b40 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b44 : bv 32 := 0x00000993.
Lemma F_12b44 : fetch_word Ubsan.M.loaded_segments (0x12b44 : word) = Some W_12b44.
Proof. vm_refl. Qed.
Lemma D_12b44 : decode_any W_12b44 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b48 : bv 32 := 0x0000f517.
Lemma F_12b48 : fetch_word Ubsan.M.loaded_segments (0x12b48 : word) = Some W_12b48.
Proof. vm_refl. Qed.
Lemma D_12b48 : decode_any W_12b48 = Some (Auipc 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b4c : bv 32 := 0x88150b13.
Lemma F_12b4c : fetch_word Ubsan.M.loaded_segments (0x12b4c : word) = Some W_12b4c.
Proof. vm_refl. Qed.
Lemma D_12b4c : decode_any W_12b4c = Some (OpImm ALU_ADD 22 10 2177, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b50 : bv 32 := 0x03501263.
Lemma F_12b50 : fetch_word Ubsan.M.loaded_segments (0x12b50 : word) = Some W_12b50.
Proof. vm_refl. Qed.
Lemma D_12b50 : decode_any W_12b50 = Some (Branch BC_NE 0 21 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b58 : bv 32 := 0x01348533.
Lemma F_12b58 : fetch_word Ubsan.M.loaded_segments (0x12b58 : word) = Some W_12b58.
Proof. vm_refl. Qed.
Lemma D_12b58 : decode_any W_12b58 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b5c : bv 32 := 0x000b0593.
Lemma F_12b5c : fetch_word Ubsan.M.loaded_segments (0x12b5c : word) = Some W_12b5c.
Proof. vm_refl. Qed.
Lemma D_12b5c : decode_any W_12b5c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b60 : bv 32 := 0x000b8613.
Lemma F_12b60 : fetch_word Ubsan.M.loaded_segments (0x12b60 : word) = Some W_12b60.
Proof. vm_refl. Qed.
Lemma D_12b60 : decode_any W_12b60 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b64 : bv 32 := 0x3790b0ef.
Lemma F_12b64 : fetch_word Ubsan.M.loaded_segments (0x12b64 : word) = Some W_12b64.
Proof. vm_refl. Qed.
Lemma D_12b64 : decode_any W_12b64 = Some (Jal 1 47992, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b68 : bv 32 := 0x013b89b3.
Lemma F_12b68 : fetch_word Ubsan.M.loaded_segments (0x12b68 : word) = Some W_12b68.
Proof. vm_refl. Qed.
Lemma D_12b68 : decode_any W_12b68 = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b6c : bv 32 := 0x00048b93.
Lemma F_12b6c : fetch_word Ubsan.M.loaded_segments (0x12b6c : word) = Some W_12b6c.
Proof. vm_refl. Qed.
Lemma D_12b6c : decode_any W_12b6c = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b70 : bv 32 := 0x01598663.
Lemma F_12b70 : fetch_word Ubsan.M.loaded_segments (0x12b70 : word) = Some W_12b70.
Proof. vm_refl. Qed.
Lemma D_12b70 : decode_any W_12b70 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b74 : bv 32 := 0x000b8493.
Lemma F_12b74 : fetch_word Ubsan.M.loaded_segments (0x12b74 : word) = Some W_12b74.
Proof. vm_refl. Qed.
Lemma D_12b74 : decode_any W_12b74 = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b78 : bv 32 := 0x03c0006f.
Lemma F_12b78 : fetch_word Ubsan.M.loaded_segments (0x12b78 : word) = Some W_12b78.
Proof. vm_refl. Qed.
Lemma D_12b78 : decode_any W_12b78 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bb4 : bv 32 := 0x413a8633.
Lemma F_12bb4 : fetch_word Ubsan.M.loaded_segments (0x12bb4 : word) = Some W_12bb4.
Proof. vm_refl. Qed.
Lemma D_12bb4 : decode_any W_12bb4 = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bb8 : bv 32 := 0x00010537.
Lemma F_12bb8 : fetch_word Ubsan.M.loaded_segments (0x12bb8 : word) = Some W_12bb8.
Proof. vm_refl. Qed.
Lemma D_12bb8 : decode_any W_12bb8 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bbc : bv 32 := 0x00a66463.
Lemma F_12bbc : fetch_word Ubsan.M.loaded_segments (0x12bbc : word) = Some W_12bbc.
Proof. vm_refl. Qed.
Lemma D_12bbc : decode_any W_12bbc = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bc0 : bv 32 := 0x00010637.
Lemma F_12bc0 : fetch_word Ubsan.M.loaded_segments (0x12bc0 : word) = Some W_12bc0.
Proof. vm_refl. Qed.
Lemma D_12bc0 : decode_any W_12bc0 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bc4 : bv 32 := 0x000a0513.
Lemma F_12bc4 : fetch_word Ubsan.M.loaded_segments (0x12bc4 : word) = Some W_12bc4.
Proof. vm_refl. Qed.
Lemma D_12bc4 : decode_any W_12bc4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bc8 : bv 32 := 0x000b0593.
Lemma F_12bc8 : fetch_word Ubsan.M.loaded_segments (0x12bc8 : word) = Some W_12bc8.
Proof. vm_refl. Qed.
Lemma D_12bc8 : decode_any W_12bc8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bcc : bv 32 := 0x4b80c0ef.
Lemma F_12bcc : fetch_word Ubsan.M.loaded_segments (0x12bcc : word) = Some W_12bcc.
Proof. vm_refl. Qed.
Lemma D_12bcc : decode_any W_12bcc = Some (Jal 1 50360, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bd0 : bv 32 := 0x14054263.
Lemma F_12bd0 : fetch_word Ubsan.M.loaded_segments (0x12bd0 : word) = Some W_12bd0.
Proof. vm_refl. Qed.
Lemma D_12bd0 : decode_any W_12bd0 = Some (Branch BC_LT 10 0 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bd4 : bv 32 := 0x00050b93.
Lemma F_12bd4 : fetch_word Ubsan.M.loaded_segments (0x12bd4 : word) = Some W_12bd4.
Proof. vm_refl. Qed.
Lemma D_12bd4 : decode_any W_12bd4 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bd8 : bv 32 := 0xf80510e3.
Lemma F_12bd8 : fetch_word Ubsan.M.loaded_segments (0x12bd8 : word) = Some W_12bd8.
Proof. vm_refl. Qed.
Lemma D_12bd8 : decode_any W_12bd8 = Some (Branch BC_NE 10 0 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bdc : bv 32 := 0x000a0513.
Lemma F_12bdc : fetch_word Ubsan.M.loaded_segments (0x12bdc : word) = Some W_12bdc.
Proof. vm_refl. Qed.
Lemma D_12bdc : decode_any W_12bdc = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12be0 : bv 32 := 0x4440c0ef.
Lemma F_12be0 : fetch_word Ubsan.M.loaded_segments (0x12be0 : word) = Some W_12be0.
Proof. vm_refl. Qed.
Lemma D_12be0 : decode_any W_12be0 = Some (Jal 1 50244, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c5c : bv 32 := 0x000ac663.
Lemma F_12c5c : fetch_word Ubsan.M.loaded_segments (0x12c5c : word) = Some W_12c5c.
Proof. vm_refl. Qed.
Lemma D_12c5c : decode_any W_12c5c = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c60 : bv 32 := 0x00050413.
Lemma F_12c60 : fetch_word Ubsan.M.loaded_segments (0x12c60 : word) = Some W_12c60.
Proof. vm_refl. Qed.
Lemma D_12c60 : decode_any W_12c60 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c64 : bv 32 := 0x0780006f.
Lemma F_12c64 : fetch_word Ubsan.M.loaded_segments (0x12c64 : word) = Some W_12c64.
Proof. vm_refl. Qed.
Lemma D_12c64 : decode_any W_12c64 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c68 : bv 32 := 0x148000ef.
Lemma F_12c68 : fetch_word Ubsan.M.loaded_segments (0x12c68 : word) = Some W_12c68.
Proof. vm_refl. Qed.
Lemma D_12c68 : decode_any W_12c68 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c6c : bv 32 := 0x0fb00593.
Lemma F_12c6c : fetch_word Ubsan.M.loaded_segments (0x12c6c : word) = Some W_12c6c.
Proof. vm_refl. Qed.
Lemma D_12c6c : decode_any W_12c6c = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c70 : bv 32 := 0x00050413.
Lemma F_12c70 : fetch_word Ubsan.M.loaded_segments (0x12c70 : word) = Some W_12c70.
Proof. vm_refl. Qed.
Lemma D_12c70 : decode_any W_12c70 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c74 : bv 32 := 0x06b56463.
Lemma F_12c74 : fetch_word Ubsan.M.loaded_segments (0x12c74 : word) = Some W_12c74.
Proof. vm_refl. Qed.
Lemma D_12c74 : decode_any W_12c74 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_12db0 : bv 32 := 0x00000513.
Lemma F_12db0 : fetch_word Ubsan.M.loaded_segments (0x12db0 : word) = Some W_12db0.
Proof. vm_refl. Qed.
Lemma D_12db0 : decode_any W_12db0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12db4 : bv 32 := 0x00008067.
Lemma F_12db4 : fetch_word Ubsan.M.loaded_segments (0x12db4 : word) = Some W_12db4.
Proof. vm_refl. Qed.
Lemma D_12db4 : decode_any W_12db4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
