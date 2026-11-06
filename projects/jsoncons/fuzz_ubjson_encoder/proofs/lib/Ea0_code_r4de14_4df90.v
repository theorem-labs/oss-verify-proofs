(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_64068 : bv 32 := 0x06048a63.
Lemma F_64068 : fetch_word Asan.M.loaded_segments (0x640b8 : word) = Some W_64068.
Proof. vm_refl. Qed.
Lemma D_64068 : decode_any W_64068 = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6406c : bv 32 := 0x000d5597.
Lemma F_6406c : fetch_word Asan.M.loaded_segments (0x640bc : word) = Some W_6406c.
Proof. vm_refl. Qed.
Lemma D_6406c : decode_any W_6406c = Some (Auipc 11 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_64070 : bv 32 := 0x0ec5ba83.
Lemma F_64070 : fetch_word Asan.M.loaded_segments (0x640c0 : word) = Some W_64070.
Proof. vm_refl. Qed.
Lemma D_64070 : decode_any W_64070 = Some (Load SZ8 true 21 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_64074 : bv 32 := 0x0fbac583.
Lemma F_64074 : fetch_word Asan.M.loaded_segments (0x640c4 : word) = Some W_64074.
Proof. vm_refl. Qed.
Lemma D_64074 : decode_any W_64074 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_64078 : bv 32 := 0x06058263.
Lemma F_64078 : fetch_word Asan.M.loaded_segments (0x640c8 : word) = Some W_64078.
Proof. vm_refl. Qed.
Lemma D_64078 : decode_any W_64078 = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6407c : bv 32 := 0x00150493.
Lemma F_6407c : fetch_word Asan.M.loaded_segments (0x640cc : word) = Some W_6407c.
Proof. vm_refl. Qed.
Lemma D_6407c : decode_any W_6407c = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64080 : bv 32 := 0x0934f463.
Lemma F_64080 : fetch_word Asan.M.loaded_segments (0x640d0 : word) = Some W_64080.
Proof. vm_refl. Qed.
Lemma D_64080 : decode_any W_64080 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_64084 : bv 32 := 0xfff94593.
Lemma F_64084 : fetch_word Asan.M.loaded_segments (0x640d4 : word) = Some W_64084.
Proof. vm_refl. Qed.
Lemma D_64084 : decode_any W_64084 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64088 : bv 32 := 0x80040a13.
Lemma F_64088 : fetch_word Asan.M.loaded_segments (0x640d8 : word) = Some W_64088.
Proof. vm_refl. Qed.
Lemma D_64088 : decode_any W_64088 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6408c : bv 32 := 0xfa8a0a13.
Lemma F_6408c : fetch_word Asan.M.loaded_segments (0x640dc : word) = Some W_6408c.
Proof. vm_refl. Qed.
Lemma D_6408c : decode_any W_6408c = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_64090 : bv 32 := 0x0895e663.
Lemma F_64090 : fetch_word Asan.M.loaded_segments (0x640e0 : word) = Some W_64090.
Proof. vm_refl. Qed.
Lemma D_64090 : decode_any W_64090 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_64094 : bv 32 := 0xfbf48593.
Lemma F_64094 : fetch_word Asan.M.loaded_segments (0x640e4 : word) = Some W_64094.
Proof. vm_refl. Qed.
Lemma D_64094 : decode_any W_64094 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_64098 : bv 32 := 0xfbf00613.
Lemma F_64098 : fetch_word Asan.M.loaded_segments (0x640e8 : word) = Some W_64098.
Proof. vm_refl. Qed.
Lemma D_64098 : decode_any W_64098 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6409c : bv 32 := 0x0eb67863.
Lemma F_6409c : fetch_word Asan.M.loaded_segments (0x640ec : word) = Some W_6409c.
Proof. vm_refl. Qed.
Lemma D_6409c : decode_any W_6409c = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_640a0 : bv 32 := 0x000d5597.
Lemma F_640a0 : fetch_word Asan.M.loaded_segments (0x640f0 : word) = Some W_640a0.
Proof. vm_refl. Qed.
Lemma D_640a0 : decode_any W_640a0 = Some (Auipc 11 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_640a4 : bv 32 := 0x0c85b583.
Lemma F_640a4 : fetch_word Asan.M.loaded_segments (0x640f4 : word) = Some W_640a4.
Proof. vm_refl. Qed.
Lemma D_640a4 : decode_any W_640a4 = Some (Load SZ8 true 11 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_640a8 : bv 32 := 0x009906b3.
Lemma F_640a8 : fetch_word Asan.M.loaded_segments (0x640f8 : word) = Some W_640a8.
Proof. vm_refl. Qed.
Lemma D_640a8 : decode_any W_640a8 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_640ac : bv 32 := 0x0005b603.
Lemma F_640ac : fetch_word Asan.M.loaded_segments (0x640fc : word) = Some W_640ac.
Proof. vm_refl. Qed.
Lemma D_640ac : decode_any W_640ac = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_640b0 : bv 32 := 0x00395593.
Lemma F_640b0 : fetch_word Asan.M.loaded_segments (0x64100 : word) = Some W_640b0.
Proof. vm_refl. Qed.
Lemma D_640b0 : decode_any W_640b0 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_640b4 : bv 32 := 0xfff68693.
Lemma F_640b4 : fetch_word Asan.M.loaded_segments (0x64104 : word) = Some W_640b4.
Proof. vm_refl. Qed.
Lemma D_640b4 : decode_any W_640b4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_640b8 : bv 32 := 0x0036d713.
Lemma F_640b8 : fetch_word Asan.M.loaded_segments (0x64108 : word) = Some W_640b8.
Proof. vm_refl. Qed.
Lemma D_640b8 : decode_any W_640b8 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_640bc : bv 32 := 0x00b605b3.
Lemma F_640bc : fetch_word Asan.M.loaded_segments (0x6410c : word) = Some W_640bc.
Proof. vm_refl. Qed.
Lemma D_640bc : decode_any W_640bc = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_640c0 : bv 32 := 0x00e60633.
Lemma F_640c0 : fetch_word Asan.M.loaded_segments (0x64110 : word) = Some W_640c0.
Proof. vm_refl. Qed.
Lemma D_640c0 : decode_any W_640c0 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_640c4 : bv 32 := 0xff85f713.
Lemma F_640c4 : fetch_word Asan.M.loaded_segments (0x64114 : word) = Some W_640c4.
Proof. vm_refl. Qed.
Lemma D_640c4 : decode_any W_640c4 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_640c8 : bv 32 := 0xff867793.
Lemma F_640c8 : fetch_word Asan.M.loaded_segments (0x64118 : word) = Some W_640c8.
Proof. vm_refl. Qed.
Lemma D_640c8 : decode_any W_640c8 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_640cc : bv 32 := 0x00073703.
Lemma F_640cc : fetch_word Asan.M.loaded_segments (0x6411c : word) = Some W_640cc.
Proof. vm_refl. Qed.
Lemma D_640cc : decode_any W_640cc = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_640d0 : bv 32 := 0x0007b783.
Lemma F_640d0 : fetch_word Asan.M.loaded_segments (0x64120 : word) = Some W_640d0.
Proof. vm_refl. Qed.
Lemma D_640d0 : decode_any W_640d0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_640d4 : bv 32 := 0x00e7e733.
Lemma F_640d4 : fetch_word Asan.M.loaded_segments (0x64124 : word) = Some W_640d4.
Proof. vm_refl. Qed.
Lemma D_640d4 : decode_any W_640d4 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_640d8 : bv 32 := 0x0a071e63.
Lemma F_640d8 : fetch_word Asan.M.loaded_segments (0x64128 : word) = Some W_640d8.
Proof. vm_refl. Qed.
Lemma D_640d8 : decode_any W_640d8 = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6418c : bv 32 := 0x02049e63.
Lemma F_6418c : fetch_word Asan.M.loaded_segments (0x641dc : word) = Some W_6418c.
Proof. vm_refl. Qed.
Lemma D_6418c : decode_any W_6418c = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_641c8 : bv 32 := 0x00050b13.
Lemma F_641c8 : fetch_word Asan.M.loaded_segments (0x64218 : word) = Some W_641c8.
Proof. vm_refl. Qed.
Lemma D_641c8 : decode_any W_641c8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_641cc : bv 32 := 0x00090513.
Lemma F_641cc : fetch_word Asan.M.loaded_segments (0x6421c : word) = Some W_641cc.
Proof. vm_refl. Qed.
Lemma D_641cc : decode_any W_641cc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_641d0 : bv 32 := 0x00048593.
Lemma F_641d0 : fetch_word Asan.M.loaded_segments (0x64220 : word) = Some W_641d0.
Proof. vm_refl. Qed.
Lemma D_641d0 : decode_any W_641d0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_641d4 : bv 32 := 0x421170ef.
Lemma F_641d4 : fetch_word Asan.M.loaded_segments (0x64224 : word) = Some W_641d4.
Proof. vm_refl. Qed.
Lemma D_641d4 : decode_any W_641d4 = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

Definition W_641d8 : bv 32 := 0x00050913.
Lemma F_641d8 : fetch_word Asan.M.loaded_segments (0x64228 : word) = Some W_641d8.
Proof. vm_refl. Qed.
Lemma D_641d8 : decode_any W_641d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_641dc : bv 32 := 0x000b0513.
Lemma F_641dc : fetch_word Asan.M.loaded_segments (0x6422c : word) = Some W_641dc.
Proof. vm_refl. Qed.
Lemma D_641dc : decode_any W_641dc = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_641e0 : bv 32 := 0xee090ee3.
Lemma F_641e0 : fetch_word Asan.M.loaded_segments (0x64230 : word) = Some W_641e0.
Proof. vm_refl. Qed.
Lemma D_641e0 : decode_any W_641e0 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.
