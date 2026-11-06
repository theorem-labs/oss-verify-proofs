(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1293c : bv 32 := 0xffffe197.
Lemma F_1293c : fetch_word Plain.M.loaded_segments (0x1293c : word) = Some W_1293c.
Proof. vm_refl. Qed.
Lemma D_1293c : decode_any W_1293c = Some (Auipc 3 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_12940 : bv 32 := 0xec418193.
Lemma F_12940 : fetch_word Plain.M.loaded_segments (0x12940 : word) = Some W_12940.
Proof. vm_refl. Qed.
Lemma D_12940 : decode_any W_12940 = Some (OpImm ALU_ADD 3 3 3780, 4%Z).
Proof. vm_refl. Qed.

Definition W_12944 : bv 32 := 0x00010513.
Lemma F_12944 : fetch_word Plain.M.loaded_segments (0x12944 : word) = Some W_12944.
Proof. vm_refl. Qed.
Lemma D_12944 : decode_any W_12944 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12948 : bv 32 := 0xfffed597.
Lemma F_12948 : fetch_word Plain.M.loaded_segments (0x12948 : word) = Some W_12948.
Proof. vm_refl. Qed.
Lemma D_12948 : decode_any W_12948 = Some (Auipc 11 1048557, 4%Z).
Proof. vm_refl. Qed.

Definition W_1294c : bv 32 := 0x6b858593.
Lemma F_1294c : fetch_word Plain.M.loaded_segments (0x1294c : word) = Some W_1294c.
Proof. vm_refl. Qed.
Lemma D_1294c : decode_any W_1294c = Some (OpImm ALU_ADD 11 11 1720, 4%Z).
Proof. vm_refl. Qed.

Definition W_12950 : bv 32 := 0xff017113.
Lemma F_12950 : fetch_word Plain.M.loaded_segments (0x12950 : word) = Some W_12950.
Proof. vm_refl. Qed.
Lemma D_12950 : decode_any W_12950 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_12954 : bv 32 := 0x0040006f.
Lemma F_12954 : fetch_word Plain.M.loaded_segments (0x12954 : word) = Some W_12954.
Proof. vm_refl. Qed.
Lemma D_12954 : decode_any W_12954 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_12958 : bv 32 := 0x00052583.
Lemma F_12958 : fetch_word Plain.M.loaded_segments (0x12958 : word) = Some W_12958.
Proof. vm_refl. Qed.
Lemma D_12958 : decode_any W_12958 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1295c : bv 32 := 0x0000d617.
Lemma F_1295c : fetch_word Plain.M.loaded_segments (0x1295c : word) = Some W_1295c.
Proof. vm_refl. Qed.
Lemma D_1295c : decode_any W_1295c = Some (Auipc 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12960 : bv 32 := 0x0000d697.
Lemma F_12960 : fetch_word Plain.M.loaded_segments (0x12960 : word) = Some W_12960.
Proof. vm_refl. Qed.
Lemma D_12960 : decode_any W_12960 = Some (Auipc 13 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12964 : bv 32 := 0x0000d717.
Lemma F_12964 : fetch_word Plain.M.loaded_segments (0x12964 : word) = Some W_12964.
Proof. vm_refl. Qed.
Lemma D_12964 : decode_any W_12964 = Some (Auipc 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12968 : bv 32 := 0xc9463783.
Lemma F_12968 : fetch_word Plain.M.loaded_segments (0x12968 : word) = Some W_12968.
Proof. vm_refl. Qed.
Lemma D_12968 : decode_any W_12968 = Some (Load SZ8 true 15 12 3220, 4%Z).
Proof. vm_refl. Qed.

Definition W_1296c : bv 32 := 0xc986b683.
Lemma F_1296c : fetch_word Plain.M.loaded_segments (0x1296c : word) = Some W_1296c.
Proof. vm_refl. Qed.
Lemma D_1296c : decode_any W_1296c = Some (Load SZ8 true 13 13 3224, 4%Z).
Proof. vm_refl. Qed.

Definition W_12970 : bv 32 := 0xc9c73703.
Lemma F_12970 : fetch_word Plain.M.loaded_segments (0x12970 : word) = Some W_12970.
Proof. vm_refl. Qed.
Lemma D_12970 : decode_any W_12970 = Some (Load SZ8 true 14 14 3228, 4%Z).
Proof. vm_refl. Qed.

Definition W_12974 : bv 32 := 0x00850613.
Lemma F_12974 : fetch_word Plain.M.loaded_segments (0x12974 : word) = Some W_12974.
Proof. vm_refl. Qed.
Lemma D_12974 : decode_any W_12974 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12978 : bv 32 := 0x00078513.
Lemma F_12978 : fetch_word Plain.M.loaded_segments (0x12978 : word) = Some W_12978.
Proof. vm_refl. Qed.
Lemma D_12978 : decode_any W_12978 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1297c : bv 32 := 0x00000793.
Lemma F_1297c : fetch_word Plain.M.loaded_segments (0x1297c : word) = Some W_1297c.
Proof. vm_refl. Qed.
Lemma D_1297c : decode_any W_1297c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12980 : bv 32 := 0x2c50306f.
Lemma F_12980 : fetch_word Plain.M.loaded_segments (0x12980 : word) = Some W_12980.
Proof. vm_refl. Qed.
Lemma D_12980 : decode_any W_12980 = Some (Jal 0 15044, 4%Z).
Proof. vm_refl. Qed.

Definition W_12984 : bv 32 := 0xff010113.
Lemma F_12984 : fetch_word Plain.M.loaded_segments (0x12984 : word) = Some W_12984.
Proof. vm_refl. Qed.
Lemma D_12984 : decode_any W_12984 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_12988 : bv 32 := 0x00113423.
Lemma F_12988 : fetch_word Plain.M.loaded_segments (0x12988 : word) = Some W_12988.
Proof. vm_refl. Qed.
Lemma D_12988 : decode_any W_12988 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1298c : bv 32 := 0x00813023.
Lemma F_1298c : fetch_word Plain.M.loaded_segments (0x1298c : word) = Some W_1298c.
Proof. vm_refl. Qed.
Lemma D_1298c : decode_any W_1298c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12990 : bv 32 := 0x01010413.
Lemma F_12990 : fetch_word Plain.M.loaded_segments (0x12990 : word) = Some W_12990.
Proof. vm_refl. Qed.
Lemma D_12990 : decode_any W_12990 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12994 : bv 32 := 0x0000e517.
Lemma F_12994 : fetch_word Plain.M.loaded_segments (0x12994 : word) = Some W_12994.
Proof. vm_refl. Qed.
Lemma D_12994 : decode_any W_12994 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_12998 : bv 32 := 0xefc50513.
Lemma F_12998 : fetch_word Plain.M.loaded_segments (0x12998 : word) = Some W_12998.
Proof. vm_refl. Qed.
Lemma D_12998 : decode_any W_12998 = Some (OpImm ALU_ADD 10 10 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_1299c : bv 32 := 0x00054503.
Lemma F_1299c : fetch_word Plain.M.loaded_segments (0x1299c : word) = Some W_1299c.
Proof. vm_refl. Qed.
Lemma D_1299c : decode_any W_1299c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129a0 : bv 32 := 0x00157513.
Lemma F_129a0 : fetch_word Plain.M.loaded_segments (0x129a0 : word) = Some W_129a0.
Proof. vm_refl. Qed.
Lemma D_129a0 : decode_any W_129a0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_129a4 : bv 32 := 0x00050663.
Lemma F_129a4 : fetch_word Plain.M.loaded_segments (0x129a4 : word) = Some W_129a4.
Proof. vm_refl. Qed.
Lemma D_129a4 : decode_any W_129a4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_129b0 : bv 32 := 0x0000e517.
Lemma F_129b0 : fetch_word Plain.M.loaded_segments (0x129b0 : word) = Some W_129b0.
Proof. vm_refl. Qed.
Lemma D_129b0 : decode_any W_129b0 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_129b4 : bv 32 := 0xee050593.
Lemma F_129b4 : fetch_word Plain.M.loaded_segments (0x129b4 : word) = Some W_129b4.
Proof. vm_refl. Qed.
Lemma D_129b4 : decode_any W_129b4 = Some (OpImm ALU_ADD 11 10 3808, 4%Z).
Proof. vm_refl. Qed.

Definition W_129b8 : bv 32 := 0x00100513.
Lemma F_129b8 : fetch_word Plain.M.loaded_segments (0x129b8 : word) = Some W_129b8.
Proof. vm_refl. Qed.
Lemma D_129b8 : decode_any W_129b8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_129bc : bv 32 := 0x00a58023.
Lemma F_129bc : fetch_word Plain.M.loaded_segments (0x129bc : word) = Some W_129bc.
Proof. vm_refl. Qed.
Lemma D_129bc : decode_any W_129bc = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129c0 : bv 32 := 0x0000d517.
Lemma F_129c0 : fetch_word Plain.M.loaded_segments (0x129c0 : word) = Some W_129c0.
Proof. vm_refl. Qed.
Lemma D_129c0 : decode_any W_129c0 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_129c4 : bv 32 := 0xc4853503.
Lemma F_129c4 : fetch_word Plain.M.loaded_segments (0x129c4 : word) = Some W_129c4.
Proof. vm_refl. Qed.
Lemma D_129c4 : decode_any W_129c4 = Some (Load SZ8 true 10 10 3144, 4%Z).
Proof. vm_refl. Qed.

Definition W_129c8 : bv 32 := 0x02050063.
Lemma F_129c8 : fetch_word Plain.M.loaded_segments (0x129c8 : word) = Some W_129c8.
Proof. vm_refl. Qed.
Lemma D_129c8 : decode_any W_129c8 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_129e8 : bv 32 := 0x00813083.
Lemma F_129e8 : fetch_word Plain.M.loaded_segments (0x129e8 : word) = Some W_129e8.
Proof. vm_refl. Qed.
Lemma D_129e8 : decode_any W_129e8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_129ec : bv 32 := 0x00013403.
Lemma F_129ec : fetch_word Plain.M.loaded_segments (0x129ec : word) = Some W_129ec.
Proof. vm_refl. Qed.
Lemma D_129ec : decode_any W_129ec = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129f0 : bv 32 := 0x01010113.
Lemma F_129f0 : fetch_word Plain.M.loaded_segments (0x129f0 : word) = Some W_129f0.
Proof. vm_refl. Qed.
Lemma D_129f0 : decode_any W_129f0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_129f4 : bv 32 := 0x00008067.
Lemma F_129f4 : fetch_word Plain.M.loaded_segments (0x129f4 : word) = Some W_129f4.
Proof. vm_refl. Qed.
Lemma D_129f4 : decode_any W_129f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_129f8 : bv 32 := 0xff010113.
Lemma F_129f8 : fetch_word Plain.M.loaded_segments (0x129f8 : word) = Some W_129f8.
Proof. vm_refl. Qed.
Lemma D_129f8 : decode_any W_129f8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_129fc : bv 32 := 0x00113423.
Lemma F_129fc : fetch_word Plain.M.loaded_segments (0x129fc : word) = Some W_129fc.
Proof. vm_refl. Qed.
Lemma D_129fc : decode_any W_129fc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a00 : bv 32 := 0x00813023.
Lemma F_12a00 : fetch_word Plain.M.loaded_segments (0x12a00 : word) = Some W_12a00.
Proof. vm_refl. Qed.
Lemma D_12a00 : decode_any W_12a00 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a04 : bv 32 := 0x01010413.
Lemma F_12a04 : fetch_word Plain.M.loaded_segments (0x12a04 : word) = Some W_12a04.
Proof. vm_refl. Qed.
Lemma D_12a04 : decode_any W_12a04 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a08 : bv 32 := 0x0000e517.
Lemma F_12a08 : fetch_word Plain.M.loaded_segments (0x12a08 : word) = Some W_12a08.
Proof. vm_refl. Qed.
Lemma D_12a08 : decode_any W_12a08 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a0c : bv 32 := 0xed050513.
Lemma F_12a0c : fetch_word Plain.M.loaded_segments (0x12a0c : word) = Some W_12a0c.
Proof. vm_refl. Qed.
Lemma D_12a0c : decode_any W_12a0c = Some (OpImm ALU_ADD 10 10 3792, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a10 : bv 32 := 0x00054503.
Lemma F_12a10 : fetch_word Plain.M.loaded_segments (0x12a10 : word) = Some W_12a10.
Proof. vm_refl. Qed.
Lemma D_12a10 : decode_any W_12a10 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a14 : bv 32 := 0x00157513.
Lemma F_12a14 : fetch_word Plain.M.loaded_segments (0x12a14 : word) = Some W_12a14.
Proof. vm_refl. Qed.
Lemma D_12a14 : decode_any W_12a14 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a18 : bv 32 := 0x00050663.
Lemma F_12a18 : fetch_word Plain.M.loaded_segments (0x12a18 : word) = Some W_12a18.
Proof. vm_refl. Qed.
Lemma D_12a18 : decode_any W_12a18 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a24 : bv 32 := 0x0000e517.
Lemma F_12a24 : fetch_word Plain.M.loaded_segments (0x12a24 : word) = Some W_12a24.
Proof. vm_refl. Qed.
Lemma D_12a24 : decode_any W_12a24 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a28 : bv 32 := 0xeb450593.
Lemma F_12a28 : fetch_word Plain.M.loaded_segments (0x12a28 : word) = Some W_12a28.
Proof. vm_refl. Qed.
Lemma D_12a28 : decode_any W_12a28 = Some (OpImm ALU_ADD 11 10 3764, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a2c : bv 32 := 0x00100513.
Lemma F_12a2c : fetch_word Plain.M.loaded_segments (0x12a2c : word) = Some W_12a2c.
Proof. vm_refl. Qed.
Lemma D_12a2c : decode_any W_12a2c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a30 : bv 32 := 0x00a58023.
Lemma F_12a30 : fetch_word Plain.M.loaded_segments (0x12a30 : word) = Some W_12a30.
Proof. vm_refl. Qed.
Lemma D_12a30 : decode_any W_12a30 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a34 : bv 32 := 0x0000d517.
Lemma F_12a34 : fetch_word Plain.M.loaded_segments (0x12a34 : word) = Some W_12a34.
Proof. vm_refl. Qed.
Lemma D_12a34 : decode_any W_12a34 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a38 : bv 32 := 0xbdc53503.
Lemma F_12a38 : fetch_word Plain.M.loaded_segments (0x12a38 : word) = Some W_12a38.
Proof. vm_refl. Qed.
Lemma D_12a38 : decode_any W_12a38 = Some (Load SZ8 true 10 10 3036, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a3c : bv 32 := 0x00050e63.
Lemma F_12a3c : fetch_word Plain.M.loaded_segments (0x12a3c : word) = Some W_12a3c.
Proof. vm_refl. Qed.
Lemma D_12a3c : decode_any W_12a3c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a58 : bv 32 := 0x0000d517.
Lemma F_12a58 : fetch_word Plain.M.loaded_segments (0x12a58 : word) = Some W_12a58.
Proof. vm_refl. Qed.
Lemma D_12a58 : decode_any W_12a58 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a5c : bv 32 := 0xbc053503.
Lemma F_12a5c : fetch_word Plain.M.loaded_segments (0x12a5c : word) = Some W_12a5c.
Proof. vm_refl. Qed.
Lemma D_12a5c : decode_any W_12a5c = Some (Load SZ8 true 10 10 3008, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a60 : bv 32 := 0x00050c63.
Lemma F_12a60 : fetch_word Plain.M.loaded_segments (0x12a60 : word) = Some W_12a60.
Proof. vm_refl. Qed.
Lemma D_12a60 : decode_any W_12a60 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a78 : bv 32 := 0x00813083.
Lemma F_12a78 : fetch_word Plain.M.loaded_segments (0x12a78 : word) = Some W_12a78.
Proof. vm_refl. Qed.
Lemma D_12a78 : decode_any W_12a78 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a7c : bv 32 := 0x00013403.
Lemma F_12a7c : fetch_word Plain.M.loaded_segments (0x12a7c : word) = Some W_12a7c.
Proof. vm_refl. Qed.
Lemma D_12a7c : decode_any W_12a7c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a80 : bv 32 := 0x01010113.
Lemma F_12a80 : fetch_word Plain.M.loaded_segments (0x12a80 : word) = Some W_12a80.
Proof. vm_refl. Qed.
Lemma D_12a80 : decode_any W_12a80 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a84 : bv 32 := 0x00008067.
Lemma F_12a84 : fetch_word Plain.M.loaded_segments (0x12a84 : word) = Some W_12a84.
Proof. vm_refl. Qed.
Lemma D_12a84 : decode_any W_12a84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12adc : bv 32 := 0x24050a63.
Lemma F_12adc : fetch_word Plain.M.loaded_segments (0x12adc : word) = Some W_12adc.
Proof. vm_refl. Qed.
Lemma D_12adc : decode_any W_12adc = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ae0 : bv 32 := 0x00050b93.
Lemma F_12ae0 : fetch_word Plain.M.loaded_segments (0x12ae0 : word) = Some W_12ae0.
Proof. vm_refl. Qed.
Lemma D_12ae0 : decode_any W_12ae0 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ae4 : bv 32 := 0x00000993.
Lemma F_12ae4 : fetch_word Plain.M.loaded_segments (0x12ae4 : word) = Some W_12ae4.
Proof. vm_refl. Qed.
Lemma D_12ae4 : decode_any W_12ae4 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ae8 : bv 32 := 0x0000e517.
Lemma F_12ae8 : fetch_word Plain.M.loaded_segments (0x12ae8 : word) = Some W_12ae8.
Proof. vm_refl. Qed.
Lemma D_12ae8 : decode_any W_12ae8 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_12aec : bv 32 := 0xdf150b13.
Lemma F_12aec : fetch_word Plain.M.loaded_segments (0x12aec : word) = Some W_12aec.
Proof. vm_refl. Qed.
Lemma D_12aec : decode_any W_12aec = Some (OpImm ALU_ADD 22 10 3569, 4%Z).
Proof. vm_refl. Qed.

Definition W_12af0 : bv 32 := 0x03501263.
Lemma F_12af0 : fetch_word Plain.M.loaded_segments (0x12af0 : word) = Some W_12af0.
Proof. vm_refl. Qed.
Lemma D_12af0 : decode_any W_12af0 = Some (Branch BC_NE 0 21 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_12af8 : bv 32 := 0x01348533.
Lemma F_12af8 : fetch_word Plain.M.loaded_segments (0x12af8 : word) = Some W_12af8.
Proof. vm_refl. Qed.
Lemma D_12af8 : decode_any W_12af8 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_12afc : bv 32 := 0x000b0593.
Lemma F_12afc : fetch_word Plain.M.loaded_segments (0x12afc : word) = Some W_12afc.
Proof. vm_refl. Qed.
Lemma D_12afc : decode_any W_12afc = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b00 : bv 32 := 0x000b8613.
Lemma F_12b00 : fetch_word Plain.M.loaded_segments (0x12b00 : word) = Some W_12b00.
Proof. vm_refl. Qed.
Lemma D_12b00 : decode_any W_12b00 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b04 : bv 32 := 0x0dc0b0ef.
Lemma F_12b04 : fetch_word Plain.M.loaded_segments (0x12b04 : word) = Some W_12b04.
Proof. vm_refl. Qed.
Lemma D_12b04 : decode_any W_12b04 = Some (Jal 1 45276, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b08 : bv 32 := 0x013b89b3.
Lemma F_12b08 : fetch_word Plain.M.loaded_segments (0x12b08 : word) = Some W_12b08.
Proof. vm_refl. Qed.
Lemma D_12b08 : decode_any W_12b08 = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b0c : bv 32 := 0x00048b93.
Lemma F_12b0c : fetch_word Plain.M.loaded_segments (0x12b0c : word) = Some W_12b0c.
Proof. vm_refl. Qed.
Lemma D_12b0c : decode_any W_12b0c = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b10 : bv 32 := 0x01598663.
Lemma F_12b10 : fetch_word Plain.M.loaded_segments (0x12b10 : word) = Some W_12b10.
Proof. vm_refl. Qed.
Lemma D_12b10 : decode_any W_12b10 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b14 : bv 32 := 0x000b8493.
Lemma F_12b14 : fetch_word Plain.M.loaded_segments (0x12b14 : word) = Some W_12b14.
Proof. vm_refl. Qed.
Lemma D_12b14 : decode_any W_12b14 = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b18 : bv 32 := 0x03c0006f.
Lemma F_12b18 : fetch_word Plain.M.loaded_segments (0x12b18 : word) = Some W_12b18.
Proof. vm_refl. Qed.
Lemma D_12b18 : decode_any W_12b18 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b54 : bv 32 := 0x413a8633.
Lemma F_12b54 : fetch_word Plain.M.loaded_segments (0x12b54 : word) = Some W_12b54.
Proof. vm_refl. Qed.
Lemma D_12b54 : decode_any W_12b54 = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b58 : bv 32 := 0x00010537.
Lemma F_12b58 : fetch_word Plain.M.loaded_segments (0x12b58 : word) = Some W_12b58.
Proof. vm_refl. Qed.
Lemma D_12b58 : decode_any W_12b58 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b5c : bv 32 := 0x00a66463.
Lemma F_12b5c : fetch_word Plain.M.loaded_segments (0x12b5c : word) = Some W_12b5c.
Proof. vm_refl. Qed.
Lemma D_12b5c : decode_any W_12b5c = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b60 : bv 32 := 0x00010637.
Lemma F_12b60 : fetch_word Plain.M.loaded_segments (0x12b60 : word) = Some W_12b60.
Proof. vm_refl. Qed.
Lemma D_12b60 : decode_any W_12b60 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b64 : bv 32 := 0x000a0513.
Lemma F_12b64 : fetch_word Plain.M.loaded_segments (0x12b64 : word) = Some W_12b64.
Proof. vm_refl. Qed.
Lemma D_12b64 : decode_any W_12b64 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b68 : bv 32 := 0x000b0593.
Lemma F_12b68 : fetch_word Plain.M.loaded_segments (0x12b68 : word) = Some W_12b68.
Proof. vm_refl. Qed.
Lemma D_12b68 : decode_any W_12b68 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b6c : bv 32 := 0x21d0b0ef.
Lemma F_12b6c : fetch_word Plain.M.loaded_segments (0x12b6c : word) = Some W_12b6c.
Proof. vm_refl. Qed.
Lemma D_12b6c : decode_any W_12b6c = Some (Jal 1 47644, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b70 : bv 32 := 0x14054263.
Lemma F_12b70 : fetch_word Plain.M.loaded_segments (0x12b70 : word) = Some W_12b70.
Proof. vm_refl. Qed.
Lemma D_12b70 : decode_any W_12b70 = Some (Branch BC_LT 10 0 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b74 : bv 32 := 0x00050b93.
Lemma F_12b74 : fetch_word Plain.M.loaded_segments (0x12b74 : word) = Some W_12b74.
Proof. vm_refl. Qed.
Lemma D_12b74 : decode_any W_12b74 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b78 : bv 32 := 0xf80510e3.
Lemma F_12b78 : fetch_word Plain.M.loaded_segments (0x12b78 : word) = Some W_12b78.
Proof. vm_refl. Qed.
Lemma D_12b78 : decode_any W_12b78 = Some (Branch BC_NE 10 0 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b7c : bv 32 := 0x000a0513.
Lemma F_12b7c : fetch_word Plain.M.loaded_segments (0x12b7c : word) = Some W_12b7c.
Proof. vm_refl. Qed.
Lemma D_12b7c : decode_any W_12b7c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12b80 : bv 32 := 0x1a90b0ef.
Lemma F_12b80 : fetch_word Plain.M.loaded_segments (0x12b80 : word) = Some W_12b80.
Proof. vm_refl. Qed.
Lemma D_12b80 : decode_any W_12b80 = Some (Jal 1 47528, 4%Z).
Proof. vm_refl. Qed.

Definition W_12bfc : bv 32 := 0x000ac663.
Lemma F_12bfc : fetch_word Plain.M.loaded_segments (0x12bfc : word) = Some W_12bfc.
Proof. vm_refl. Qed.
Lemma D_12bfc : decode_any W_12bfc = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c00 : bv 32 := 0x00050413.
Lemma F_12c00 : fetch_word Plain.M.loaded_segments (0x12c00 : word) = Some W_12c00.
Proof. vm_refl. Qed.
Lemma D_12c00 : decode_any W_12c00 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c04 : bv 32 := 0x0780006f.
Lemma F_12c04 : fetch_word Plain.M.loaded_segments (0x12c04 : word) = Some W_12c04.
Proof. vm_refl. Qed.
Lemma D_12c04 : decode_any W_12c04 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c08 : bv 32 := 0x148000ef.
Lemma F_12c08 : fetch_word Plain.M.loaded_segments (0x12c08 : word) = Some W_12c08.
Proof. vm_refl. Qed.
Lemma D_12c08 : decode_any W_12c08 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c0c : bv 32 := 0x0fb00593.
Lemma F_12c0c : fetch_word Plain.M.loaded_segments (0x12c0c : word) = Some W_12c0c.
Proof. vm_refl. Qed.
Lemma D_12c0c : decode_any W_12c0c = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c10 : bv 32 := 0x00050413.
Lemma F_12c10 : fetch_word Plain.M.loaded_segments (0x12c10 : word) = Some W_12c10.
Proof. vm_refl. Qed.
Lemma D_12c10 : decode_any W_12c10 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c14 : bv 32 := 0x06b56463.
Lemma F_12c14 : fetch_word Plain.M.loaded_segments (0x12c14 : word) = Some W_12c14.
Proof. vm_refl. Qed.
Lemma D_12c14 : decode_any W_12c14 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_12d50 : bv 32 := 0x00000513.
Lemma F_12d50 : fetch_word Plain.M.loaded_segments (0x12d50 : word) = Some W_12d50.
Proof. vm_refl. Qed.
Lemma D_12d50 : decode_any W_12d50 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12d54 : bv 32 := 0x00008067.
Lemma F_12d54 : fetch_word Plain.M.loaded_segments (0x12d54 : word) = Some W_12d54.
Proof. vm_refl. Qed.
Lemma D_12d54 : decode_any W_12d54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
