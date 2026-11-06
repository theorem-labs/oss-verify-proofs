(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_42ee8 : bv 32 := 0xfa010113.
Lemma F_42ee8 : fetch_word Plain.M.loaded_segments (0x42f30 : word) = Some W_42ee8.
Proof. vm_refl. Qed.
Lemma D_42ee8 : decode_any W_42ee8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_42eec : bv 32 := 0x04113c23.
Lemma F_42eec : fetch_word Plain.M.loaded_segments (0x42f34 : word) = Some W_42eec.
Proof. vm_refl. Qed.
Lemma D_42eec : decode_any W_42eec = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ef0 : bv 32 := 0x04813823.
Lemma F_42ef0 : fetch_word Plain.M.loaded_segments (0x42f38 : word) = Some W_42ef0.
Proof. vm_refl. Qed.
Lemma D_42ef0 : decode_any W_42ef0 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ef4 : bv 32 := 0x04913423.
Lemma F_42ef4 : fetch_word Plain.M.loaded_segments (0x42f3c : word) = Some W_42ef4.
Proof. vm_refl. Qed.
Lemma D_42ef4 : decode_any W_42ef4 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ef8 : bv 32 := 0x05213023.
Lemma F_42ef8 : fetch_word Plain.M.loaded_segments (0x42f40 : word) = Some W_42ef8.
Proof. vm_refl. Qed.
Lemma D_42ef8 : decode_any W_42ef8 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_42efc : bv 32 := 0x03313c23.
Lemma F_42efc : fetch_word Plain.M.loaded_segments (0x42f44 : word) = Some W_42efc.
Proof. vm_refl. Qed.
Lemma D_42efc : decode_any W_42efc = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f00 : bv 32 := 0x03413823.
Lemma F_42f00 : fetch_word Plain.M.loaded_segments (0x42f48 : word) = Some W_42f00.
Proof. vm_refl. Qed.
Lemma D_42f00 : decode_any W_42f00 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f04 : bv 32 := 0x03513423.
Lemma F_42f04 : fetch_word Plain.M.loaded_segments (0x42f4c : word) = Some W_42f04.
Proof. vm_refl. Qed.
Lemma D_42f04 : decode_any W_42f04 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f08 : bv 32 := 0x03613023.
Lemma F_42f08 : fetch_word Plain.M.loaded_segments (0x42f50 : word) = Some W_42f08.
Proof. vm_refl. Qed.
Lemma D_42f08 : decode_any W_42f08 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f0c : bv 32 := 0x00050913.
Lemma F_42f0c : fetch_word Plain.M.loaded_segments (0x42f54 : word) = Some W_42f0c.
Proof. vm_refl. Qed.
Lemma D_42f0c : decode_any W_42f0c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f10 : bv 32 := 0x16058663.
Lemma F_42f10 : fetch_word Plain.M.loaded_segments (0x42f58 : word) = Some W_42f10.
Proof. vm_refl. Qed.
Lemma D_42f10 : decode_any W_42f10 = Some (Branch BC_EQ 11 0 364, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f14 : bv 32 := 0x00068493.
Lemma F_42f14 : fetch_word Plain.M.loaded_segments (0x42f5c : word) = Some W_42f14.
Proof. vm_refl. Qed.
Lemma D_42f14 : decode_any W_42f14 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f18 : bv 32 := 0x00060993.
Lemma F_42f18 : fetch_word Plain.M.loaded_segments (0x42f60 : word) = Some W_42f18.
Proof. vm_refl. Qed.
Lemma D_42f18 : decode_any W_42f18 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f1c : bv 32 := 0x00058a13.
Lemma F_42f1c : fetch_word Plain.M.loaded_segments (0x42f64 : word) = Some W_42f1c.
Proof. vm_refl. Qed.
Lemma D_42f1c : decode_any W_42f1c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f20 : bv 32 := 0x00b90433.
Lemma F_42f20 : fetch_word Plain.M.loaded_segments (0x42f68 : word) = Some W_42f20.
Proof. vm_refl. Qed.
Lemma D_42f20 : decode_any W_42f20 = Some (Op ALU_ADD 8 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f24 : bv 32 := 0x03000593.
Lemma F_42f24 : fetch_word Plain.M.loaded_segments (0x42f6c : word) = Some W_42f24.
Proof. vm_refl. Qed.
Lemma D_42f24 : decode_any W_42f24 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f28 : bv 32 := 0x00090513.
Lemma F_42f28 : fetch_word Plain.M.loaded_segments (0x42f70 : word) = Some W_42f28.
Proof. vm_refl. Qed.
Lemma D_42f28 : decode_any W_42f28 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f2c : bv 32 := 0x00054603.
Lemma F_42f2c : fetch_word Plain.M.loaded_segments (0x42f74 : word) = Some W_42f2c.
Proof. vm_refl. Qed.
Lemma D_42f2c : decode_any W_42f2c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f30 : bv 32 := 0x00b61663.
Lemma F_42f30 : fetch_word Plain.M.loaded_segments (0x42f78 : word) = Some W_42f30.
Proof. vm_refl. Qed.
Lemma D_42f30 : decode_any W_42f30 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f34 : bv 32 := 0x00150513.
Lemma F_42f34 : fetch_word Plain.M.loaded_segments (0x42f7c : word) = Some W_42f34.
Proof. vm_refl. Qed.
Lemma D_42f34 : decode_any W_42f34 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f38 : bv 32 := 0xfe856ae3.
Lemma F_42f38 : fetch_word Plain.M.loaded_segments (0x42f80 : word) = Some W_42f38.
Proof. vm_refl. Qed.
Lemma D_42f38 : decode_any W_42f38 = Some (Branch BC_LTU 10 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f3c : bv 32 := 0x00850a63.
Lemma F_42f3c : fetch_word Plain.M.loaded_segments (0x42f84 : word) = Some W_42f3c.
Proof. vm_refl. Qed.
Lemma D_42f3c : decode_any W_42f3c = Some (Branch BC_EQ 10 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f40 : bv 32 := 0x00a00513.
Lemma F_42f40 : fetch_word Plain.M.loaded_segments (0x42f88 : word) = Some W_42f40.
Proof. vm_refl. Qed.
Lemma D_42f40 : decode_any W_42f40 = Some (OpImm ALU_ADD 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f44 : bv 32 := 0x04aa7863.
Lemma F_42f44 : fetch_word Plain.M.loaded_segments (0x42f8c : word) = Some W_42f44.
Proof. vm_refl. Qed.
Lemma D_42f44 : decode_any W_42f44 = Some (Branch BC_GEU 20 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f48 : bv 32 := 0x00100593.
Lemma F_42f48 : fetch_word Plain.M.loaded_segments (0x42f90 : word) = Some W_42f48.
Proof. vm_refl. Qed.
Lemma D_42f48 : decode_any W_42f48 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f4c : bv 32 := 0x0600006f.
Lemma F_42f4c : fetch_word Plain.M.loaded_segments (0x42f94 : word) = Some W_42f4c.
Proof. vm_refl. Qed.
Lemma D_42f4c : decode_any W_42f4c = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f50 : bv 32 := 0x00010023.
Lemma F_42f50 : fetch_word Plain.M.loaded_segments (0x42f98 : word) = Some W_42f50.
Proof. vm_refl. Qed.
Lemma D_42f50 : decode_any W_42f50 = Some (Store SZ1 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f54 : bv 32 := 0x00013423.
Lemma F_42f54 : fetch_word Plain.M.loaded_segments (0x42f9c : word) = Some W_42f54.
Proof. vm_refl. Qed.
Lemma D_42f54 : decode_any W_42f54 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f58 : bv 32 := 0x00013823.
Lemma F_42f58 : fetch_word Plain.M.loaded_segments (0x42fa0 : word) = Some W_42f58.
Proof. vm_refl. Qed.
Lemma D_42f58 : decode_any W_42f58 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f5c : bv 32 := 0x00013c23.
Lemma F_42f5c : fetch_word Plain.M.loaded_segments (0x42fa4 : word) = Some W_42f5c.
Proof. vm_refl. Qed.
Lemma D_42f5c : decode_any W_42f5c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f60 : bv 32 := 0x00010593.
Lemma F_42f60 : fetch_word Plain.M.loaded_segments (0x42fa8 : word) = Some W_42f60.
Proof. vm_refl. Qed.
Lemma D_42f60 : decode_any W_42f60 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f64 : bv 32 := 0x00048513.
Lemma F_42f64 : fetch_word Plain.M.loaded_segments (0x42fac : word) = Some W_42f64.
Proof. vm_refl. Qed.
Lemma D_42f64 : decode_any W_42f64 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f68 : bv 32 := 0x3e0000ef.
Lemma F_42f68 : fetch_word Plain.M.loaded_segments (0x42fb0 : word) = Some W_42f68.
Proof. vm_refl. Qed.
Lemma D_42f68 : decode_any W_42f68 = Some (Jal 1 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f6c : bv 32 := 0x00014503.
Lemma F_42f6c : fetch_word Plain.M.loaded_segments (0x42fb4 : word) = Some W_42f6c.
Proof. vm_refl. Qed.
Lemma D_42f6c : decode_any W_42f6c = Some (Load SZ1 false 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f70 : bv 32 := 0x00157513.
Lemma F_42f70 : fetch_word Plain.M.loaded_segments (0x42fb8 : word) = Some W_42f70.
Proof. vm_refl. Qed.
Lemma D_42f70 : decode_any W_42f70 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f74 : bv 32 := 0x00050c63.
Lemma F_42f74 : fetch_word Plain.M.loaded_segments (0x42fbc : word) = Some W_42f74.
Proof. vm_refl. Qed.
Lemma D_42f74 : decode_any W_42f74 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f78 : bv 32 := 0x01813503.
Lemma F_42f78 : fetch_word Plain.M.loaded_segments (0x42fc0 : word) = Some W_42f78.
Proof. vm_refl. Qed.
Lemma D_42f78 : decode_any W_42f78 = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f7c : bv 32 := 0x00050863.
Lemma F_42f7c : fetch_word Plain.M.loaded_segments (0x42fc4 : word) = Some W_42f7c.
Proof. vm_refl. Qed.
Lemma D_42f7c : decode_any W_42f7c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f80 : bv 32 := 0x01013583.
Lemma F_42f80 : fetch_word Plain.M.loaded_segments (0x42fc8 : word) = Some W_42f80.
Proof. vm_refl. Qed.
Lemma D_42f80 : decode_any W_42f80 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f84 : bv 32 := 0x00359593.
Lemma F_42f84 : fetch_word Plain.M.loaded_segments (0x42fcc : word) = Some W_42f84.
Proof. vm_refl. Qed.
Lemma D_42f84 : decode_any W_42f84 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f88 : bv 32 := 0x5f5200ef.
Lemma F_42f88 : fetch_word Plain.M.loaded_segments (0x42fd0 : word) = Some W_42f88.
Proof. vm_refl. Qed.
Lemma D_42f88 : decode_any W_42f88 = Some (Jal 1 134644, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f8c : bv 32 := 0x00000493.
Lemma F_42f8c : fetch_word Plain.M.loaded_segments (0x42fd4 : word) = Some W_42f8c.
Proof. vm_refl. Qed.
Lemma D_42f8c : decode_any W_42f8c = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f90 : bv 32 := 0x0b00006f.
Lemma F_42f90 : fetch_word Plain.M.loaded_segments (0x42fd8 : word) = Some W_42f90.
Proof. vm_refl. Qed.
Lemma D_42f90 : decode_any W_42f90 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f94 : bv 32 := 0x00001537.
Lemma F_42f94 : fetch_word Plain.M.loaded_segments (0x42fdc : word) = Some W_42f94.
Proof. vm_refl. Qed.
Lemma D_42f94 : decode_any W_42f94 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f98 : bv 32 := 0xd4a5051b.
Lemma F_42f98 : fetch_word Plain.M.loaded_segments (0x42fe0 : word) = Some W_42f98.
Proof. vm_refl. Qed.
Lemma D_42f98 : decode_any W_42f98 = Some (OpImm32 10 10 3402, 4%Z).
Proof. vm_refl. Qed.

Definition W_42f9c : bv 32 := 0x02aa0533.
Lemma F_42f9c : fetch_word Plain.M.loaded_segments (0x42fe4 : word) = Some W_42f9c.
Proof. vm_refl. Qed.
Lemma D_42f9c : decode_any W_42f9c = Some (Mul M_MUL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fa0 : bv 32 := 0x00a55513.
Lemma F_42fa0 : fetch_word Plain.M.loaded_segments (0x42fe8 : word) = Some W_42fa0.
Proof. vm_refl. Qed.
Lemma D_42fa0 : decode_any W_42fa0 = Some (ShiftImm ALU_SRL 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fa4 : bv 32 := 0x04050593.
Lemma F_42fa4 : fetch_word Plain.M.loaded_segments (0x42fec : word) = Some W_42fa4.
Proof. vm_refl. Qed.
Lemma D_42fa4 : decode_any W_42fa4 = Some (OpImm ALU_ADD 11 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fa8 : bv 32 := 0x0065d593.
Lemma F_42fa8 : fetch_word Plain.M.loaded_segments (0x42ff0 : word) = Some W_42fa8.
Proof. vm_refl. Qed.
Lemma D_42fa8 : decode_any W_42fa8 = Some (ShiftImm ALU_SRL 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fac : bv 32 := 0x00010023.
Lemma F_42fac : fetch_word Plain.M.loaded_segments (0x42ff4 : word) = Some W_42fac.
Proof. vm_refl. Qed.
Lemma D_42fac : decode_any W_42fac = Some (Store SZ1 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fb0 : bv 32 := 0x00013423.
Lemma F_42fb0 : fetch_word Plain.M.loaded_segments (0x42ff8 : word) = Some W_42fb0.
Proof. vm_refl. Qed.
Lemma D_42fb0 : decode_any W_42fb0 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fb4 : bv 32 := 0x00013823.
Lemma F_42fb4 : fetch_word Plain.M.loaded_segments (0x42ffc : word) = Some W_42fb4.
Proof. vm_refl. Qed.
Lemma D_42fb4 : decode_any W_42fb4 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fb8 : bv 32 := 0x00013c23.
Lemma F_42fb8 : fetch_word Plain.M.loaded_segments (0x43000 : word) = Some W_42fb8.
Proof. vm_refl. Qed.
Lemma D_42fb8 : decode_any W_42fb8 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fbc : bv 32 := 0x00010513.
Lemma F_42fbc : fetch_word Plain.M.loaded_segments (0x43004 : word) = Some W_42fbc.
Proof. vm_refl. Qed.
Lemma D_42fbc : decode_any W_42fbc = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fc0 : bv 32 := 0x558000ef.
Lemma F_42fc0 : fetch_word Plain.M.loaded_segments (0x43008 : word) = Some W_42fc0.
Proof. vm_refl. Qed.
Lemma D_42fc0 : decode_any W_42fc0 = Some (Jal 1 1368, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fc4 : bv 32 := 0x001a3513.
Lemma F_42fc4 : fetch_word Plain.M.loaded_segments (0x4300c : word) = Some W_42fc4.
Proof. vm_refl. Qed.
Lemma D_42fc4 : decode_any W_42fc4 = Some (OpImm ALU_SLTU 10 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fc8 : bv 32 := 0x00aa0a33.
Lemma F_42fc8 : fetch_word Plain.M.loaded_segments (0x43010 : word) = Some W_42fc8.
Proof. vm_refl. Qed.
Lemma D_42fc8 : decode_any W_42fc8 = Some (Op ALU_ADD 20 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fcc : bv 32 := 0x00900a93.
Lemma F_42fcc : fetch_word Plain.M.loaded_segments (0x43014 : word) = Some W_42fcc.
Proof. vm_refl. Qed.
Lemma D_42fcc : decode_any W_42fcc = Some (OpImm ALU_ADD 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fd0 : bv 32 := 0x00094b03.
Lemma F_42fd0 : fetch_word Plain.M.loaded_segments (0x43018 : word) = Some W_42fd0.
Proof. vm_refl. Qed.
Lemma D_42fd0 : decode_any W_42fd0 = Some (Load SZ1 false 22 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fd4 : bv 32 := 0xfd0b0513.
Lemma F_42fd4 : fetch_word Plain.M.loaded_segments (0x4301c : word) = Some W_42fd4.
Proof. vm_refl. Qed.
Lemma D_42fd4 : decode_any W_42fd4 = Some (OpImm ALU_ADD 10 22 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fd8 : bv 32 := 0x08aaec63.
Lemma F_42fd8 : fetch_word Plain.M.loaded_segments (0x43020 : word) = Some W_42fd8.
Proof. vm_refl. Qed.
Lemma D_42fd8 : decode_any W_42fd8 = Some (Branch BC_LTU 21 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fdc : bv 32 := 0x00010513.
Lemma F_42fdc : fetch_word Plain.M.loaded_segments (0x43024 : word) = Some W_42fdc.
Proof. vm_refl. Qed.
Lemma D_42fdc : decode_any W_42fdc = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fe0 : bv 32 := 0x00a00593.
Lemma F_42fe0 : fetch_word Plain.M.loaded_segments (0x43028 : word) = Some W_42fe0.
Proof. vm_refl. Qed.
Lemma D_42fe0 : decode_any W_42fe0 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fe4 : bv 32 := 0x0e8000ef.
Lemma F_42fe4 : fetch_word Plain.M.loaded_segments (0x4302c : word) = Some W_42fe4.
Proof. vm_refl. Qed.
Lemma D_42fe4 : decode_any W_42fe4 = Some (Jal 1 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fe8 : bv 32 := 0x00fb7593.
Lemma F_42fe8 : fetch_word Plain.M.loaded_segments (0x43030 : word) = Some W_42fe8.
Proof. vm_refl. Qed.
Lemma D_42fe8 : decode_any W_42fe8 = Some (OpImm ALU_AND 11 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_42fec : bv 32 := 0x00010513.
Lemma F_42fec : fetch_word Plain.M.loaded_segments (0x43034 : word) = Some W_42fec.
Proof. vm_refl. Qed.
Lemma D_42fec : decode_any W_42fec = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ff0 : bv 32 := 0x1d0000ef.
Lemma F_42ff0 : fetch_word Plain.M.loaded_segments (0x43038 : word) = Some W_42ff0.
Proof. vm_refl. Qed.
Lemma D_42ff0 : decode_any W_42ff0 = Some (Jal 1 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ff4 : bv 32 := 0xfffa0a13.
Lemma F_42ff4 : fetch_word Plain.M.loaded_segments (0x4303c : word) = Some W_42ff4.
Proof. vm_refl. Qed.
Lemma D_42ff4 : decode_any W_42ff4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ff8 : bv 32 := 0x00190913.
Lemma F_42ff8 : fetch_word Plain.M.loaded_segments (0x43040 : word) = Some W_42ff8.
Proof. vm_refl. Qed.
Lemma D_42ff8 : decode_any W_42ff8 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ffc : bv 32 := 0xfc0a1ae3.
Lemma F_42ffc : fetch_word Plain.M.loaded_segments (0x43044 : word) = Some W_42ffc.
Proof. vm_refl. Qed.
Lemma D_42ffc : decode_any W_42ffc = Some (Branch BC_NE 20 0 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_43000 : bv 32 := 0x00098863.
Lemma F_43000 : fetch_word Plain.M.loaded_segments (0x43048 : word) = Some W_43000.
Proof. vm_refl. Qed.
Lemma D_43000 : decode_any W_43000 = Some (Branch BC_EQ 19 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_43004 : bv 32 := 0x00014503.
Lemma F_43004 : fetch_word Plain.M.loaded_segments (0x4304c : word) = Some W_43004.
Proof. vm_refl. Qed.
Lemma D_43004 : decode_any W_43004 = Some (Load SZ1 false 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43008 : bv 32 := 0x00256513.
Lemma F_43008 : fetch_word Plain.M.loaded_segments (0x43050 : word) = Some W_43008.
Proof. vm_refl. Qed.
Lemma D_43008 : decode_any W_43008 = Some (OpImm ALU_OR 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_4300c : bv 32 := 0x00a10023.
Lemma F_4300c : fetch_word Plain.M.loaded_segments (0x43054 : word) = Some W_4300c.
Proof. vm_refl. Qed.
Lemma D_4300c : decode_any W_4300c = Some (Store SZ1 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43010 : bv 32 := 0x00010593.
Lemma F_43010 : fetch_word Plain.M.loaded_segments (0x43058 : word) = Some W_43010.
Proof. vm_refl. Qed.
Lemma D_43010 : decode_any W_43010 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43014 : bv 32 := 0x00048513.
Lemma F_43014 : fetch_word Plain.M.loaded_segments (0x4305c : word) = Some W_43014.
Proof. vm_refl. Qed.
Lemma D_43014 : decode_any W_43014 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43018 : bv 32 := 0x330000ef.
Lemma F_43018 : fetch_word Plain.M.loaded_segments (0x43060 : word) = Some W_43018.
Proof. vm_refl. Qed.
Lemma D_43018 : decode_any W_43018 = Some (Jal 1 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_4301c : bv 32 := 0x00000493.
Lemma F_4301c : fetch_word Plain.M.loaded_segments (0x43064 : word) = Some W_4301c.
Proof. vm_refl. Qed.
Lemma D_4301c : decode_any W_4301c = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43020 : bv 32 := 0x00014503.
Lemma F_43020 : fetch_word Plain.M.loaded_segments (0x43068 : word) = Some W_43020.
Proof. vm_refl. Qed.
Lemma D_43020 : decode_any W_43020 = Some (Load SZ1 false 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43024 : bv 32 := 0x00157513.
Lemma F_43024 : fetch_word Plain.M.loaded_segments (0x4306c : word) = Some W_43024.
Proof. vm_refl. Qed.
Lemma D_43024 : decode_any W_43024 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_43028 : bv 32 := 0x00050c63.
Lemma F_43028 : fetch_word Plain.M.loaded_segments (0x43070 : word) = Some W_43028.
Proof. vm_refl. Qed.
Lemma D_43028 : decode_any W_43028 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4302c : bv 32 := 0x01813503.
Lemma F_4302c : fetch_word Plain.M.loaded_segments (0x43074 : word) = Some W_4302c.
Proof. vm_refl. Qed.
Lemma D_4302c : decode_any W_4302c = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_43030 : bv 32 := 0x00050863.
Lemma F_43030 : fetch_word Plain.M.loaded_segments (0x43078 : word) = Some W_43030.
Proof. vm_refl. Qed.
Lemma D_43030 : decode_any W_43030 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_43034 : bv 32 := 0x01013583.
Lemma F_43034 : fetch_word Plain.M.loaded_segments (0x4307c : word) = Some W_43034.
Proof. vm_refl. Qed.
Lemma D_43034 : decode_any W_43034 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_43038 : bv 32 := 0x00359593.
Lemma F_43038 : fetch_word Plain.M.loaded_segments (0x43080 : word) = Some W_43038.
Proof. vm_refl. Qed.
Lemma D_43038 : decode_any W_43038 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4303c : bv 32 := 0x541200ef.
Lemma F_4303c : fetch_word Plain.M.loaded_segments (0x43084 : word) = Some W_4303c.
Proof. vm_refl. Qed.
Lemma D_4303c : decode_any W_4303c = Some (Jal 1 134464, 4%Z).
Proof. vm_refl. Qed.

Definition W_43040 : bv 32 := 0x00040513.
Lemma F_43040 : fetch_word Plain.M.loaded_segments (0x43088 : word) = Some W_43040.
Proof. vm_refl. Qed.
Lemma D_43040 : decode_any W_43040 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43044 : bv 32 := 0x00048593.
Lemma F_43044 : fetch_word Plain.M.loaded_segments (0x4308c : word) = Some W_43044.
Proof. vm_refl. Qed.
Lemma D_43044 : decode_any W_43044 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43048 : bv 32 := 0x05813083.
Lemma F_43048 : fetch_word Plain.M.loaded_segments (0x43090 : word) = Some W_43048.
Proof. vm_refl. Qed.
Lemma D_43048 : decode_any W_43048 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4304c : bv 32 := 0x05013403.
Lemma F_4304c : fetch_word Plain.M.loaded_segments (0x43094 : word) = Some W_4304c.
Proof. vm_refl. Qed.
Lemma D_4304c : decode_any W_4304c = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_43050 : bv 32 := 0x04813483.
Lemma F_43050 : fetch_word Plain.M.loaded_segments (0x43098 : word) = Some W_43050.
Proof. vm_refl. Qed.
Lemma D_43050 : decode_any W_43050 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_43054 : bv 32 := 0x04013903.
Lemma F_43054 : fetch_word Plain.M.loaded_segments (0x4309c : word) = Some W_43054.
Proof. vm_refl. Qed.
Lemma D_43054 : decode_any W_43054 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_43058 : bv 32 := 0x03813983.
Lemma F_43058 : fetch_word Plain.M.loaded_segments (0x430a0 : word) = Some W_43058.
Proof. vm_refl. Qed.
Lemma D_43058 : decode_any W_43058 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4305c : bv 32 := 0x03013a03.
Lemma F_4305c : fetch_word Plain.M.loaded_segments (0x430a4 : word) = Some W_4305c.
Proof. vm_refl. Qed.
Lemma D_4305c : decode_any W_4305c = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_43060 : bv 32 := 0x02813a83.
Lemma F_43060 : fetch_word Plain.M.loaded_segments (0x430a8 : word) = Some W_43060.
Proof. vm_refl. Qed.
Lemma D_43060 : decode_any W_43060 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_43064 : bv 32 := 0x02013b03.
Lemma F_43064 : fetch_word Plain.M.loaded_segments (0x430ac : word) = Some W_43064.
Proof. vm_refl. Qed.
Lemma D_43064 : decode_any W_43064 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_43068 : bv 32 := 0x06010113.
Lemma F_43068 : fetch_word Plain.M.loaded_segments (0x430b0 : word) = Some W_43068.
Proof. vm_refl. Qed.
Lemma D_43068 : decode_any W_43068 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4306c : bv 32 := 0x00008067.
Lemma F_4306c : fetch_word Plain.M.loaded_segments (0x430b4 : word) = Some W_4306c.
Proof. vm_refl. Qed.
Lemma D_4306c : decode_any W_4306c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43070 : bv 32 := 0x01600493.
Lemma F_43070 : fetch_word Plain.M.loaded_segments (0x430b8 : word) = Some W_43070.
Proof. vm_refl. Qed.
Lemma D_43070 : decode_any W_43070 = Some (OpImm ALU_ADD 9 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_43074 : bv 32 := 0x00090413.
Lemma F_43074 : fetch_word Plain.M.loaded_segments (0x430bc : word) = Some W_43074.
Proof. vm_refl. Qed.
Lemma D_43074 : decode_any W_43074 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43078 : bv 32 := 0xfa9ff06f.
Lemma F_43078 : fetch_word Plain.M.loaded_segments (0x430c0 : word) = Some W_43078.
Proof. vm_refl. Qed.
Lemma D_43078 : decode_any W_43078 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4307c : bv 32 := 0x01600493.
Lemma F_4307c : fetch_word Plain.M.loaded_segments (0x430c4 : word) = Some W_4307c.
Proof. vm_refl. Qed.
Lemma D_4307c : decode_any W_4307c = Some (OpImm ALU_ADD 9 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_43080 : bv 32 := 0x00090413.
Lemma F_43080 : fetch_word Plain.M.loaded_segments (0x430c8 : word) = Some W_43080.
Proof. vm_refl. Qed.
Lemma D_43080 : decode_any W_43080 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43084 : bv 32 := 0xfbdff06f.
Lemma F_43084 : fetch_word Plain.M.loaded_segments (0x430cc : word) = Some W_43084.
Proof. vm_refl. Qed.
Lemma D_43084 : decode_any W_43084 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

Definition W_43088 : bv 32 := 0x00014583.
Lemma F_43088 : fetch_word Plain.M.loaded_segments (0x430d0 : word) = Some W_43088.
Proof. vm_refl. Qed.
Lemma D_43088 : decode_any W_43088 = Some (Load SZ1 false 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4308c : bv 32 := 0x0015f593.
Lemma F_4308c : fetch_word Plain.M.loaded_segments (0x430d4 : word) = Some W_4308c.
Proof. vm_refl. Qed.
Lemma D_4308c : decode_any W_4308c = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_43090 : bv 32 := 0x00050413.
Lemma F_43090 : fetch_word Plain.M.loaded_segments (0x430d8 : word) = Some W_43090.
Proof. vm_refl. Qed.
Lemma D_43090 : decode_any W_43090 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43094 : bv 32 := 0x00059e63.
Lemma F_43094 : fetch_word Plain.M.loaded_segments (0x430dc : word) = Some W_43094.
Proof. vm_refl. Qed.
Lemma D_43094 : decode_any W_43094 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_43098 : bv 32 := 0x02c0006f.
Lemma F_43098 : fetch_word Plain.M.loaded_segments (0x430e0 : word) = Some W_43098.
Proof. vm_refl. Qed.
Lemma D_43098 : decode_any W_43098 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4309c : bv 32 := 0x0040006f.
Lemma F_4309c : fetch_word Plain.M.loaded_segments (0x430e4 : word) = Some W_4309c.
Proof. vm_refl. Qed.
Lemma D_4309c : decode_any W_4309c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_430a0 : bv 32 := 0x00050413.
Lemma F_430a0 : fetch_word Plain.M.loaded_segments (0x430e8 : word) = Some W_430a0.
Proof. vm_refl. Qed.
Lemma D_430a0 : decode_any W_430a0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_430a4 : bv 32 := 0x00014503.
Lemma F_430a4 : fetch_word Plain.M.loaded_segments (0x430ec : word) = Some W_430a4.
Proof. vm_refl. Qed.
Lemma D_430a4 : decode_any W_430a4 = Some (Load SZ1 false 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_430a8 : bv 32 := 0x00157513.
Lemma F_430a8 : fetch_word Plain.M.loaded_segments (0x430f0 : word) = Some W_430a8.
Proof. vm_refl. Qed.
Lemma D_430a8 : decode_any W_430a8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_430ac : bv 32 := 0x00050c63.
Lemma F_430ac : fetch_word Plain.M.loaded_segments (0x430f4 : word) = Some W_430ac.
Proof. vm_refl. Qed.
Lemma D_430ac : decode_any W_430ac = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_430b0 : bv 32 := 0x01813503.
Lemma F_430b0 : fetch_word Plain.M.loaded_segments (0x430f8 : word) = Some W_430b0.
Proof. vm_refl. Qed.
Lemma D_430b0 : decode_any W_430b0 = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_430b4 : bv 32 := 0x00050863.
Lemma F_430b4 : fetch_word Plain.M.loaded_segments (0x430fc : word) = Some W_430b4.
Proof. vm_refl. Qed.
Lemma D_430b4 : decode_any W_430b4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_430b8 : bv 32 := 0x01013583.
Lemma F_430b8 : fetch_word Plain.M.loaded_segments (0x43100 : word) = Some W_430b8.
Proof. vm_refl. Qed.
Lemma D_430b8 : decode_any W_430b8 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_430bc : bv 32 := 0x00359593.
Lemma F_430bc : fetch_word Plain.M.loaded_segments (0x43104 : word) = Some W_430bc.
Proof. vm_refl. Qed.
Lemma D_430bc : decode_any W_430bc = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_430c0 : bv 32 := 0x4bd200ef.
Lemma F_430c0 : fetch_word Plain.M.loaded_segments (0x43108 : word) = Some W_430c0.
Proof. vm_refl. Qed.
Lemma D_430c0 : decode_any W_430c0 = Some (Jal 1 134332, 4%Z).
Proof. vm_refl. Qed.

Definition W_430c4 : bv 32 := 0x00040513.
Lemma F_430c4 : fetch_word Plain.M.loaded_segments (0x4310c : word) = Some W_430c4.
Proof. vm_refl. Qed.
Lemma D_430c4 : decode_any W_430c4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_430c8 : bv 32 := 0x7495e0ef.
Lemma F_430c8 : fetch_word Plain.M.loaded_segments (0x43110 : word) = Some W_430c8.
Proof. vm_refl. Qed.
Lemma D_430c8 : decode_any W_430c8 = Some (Jal 1 388936, 4%Z).
Proof. vm_refl. Qed.

Definition W_430cc : bv 32 := 0xfd010113.
Lemma F_430cc : fetch_word Plain.M.loaded_segments (0x43114 : word) = Some W_430cc.
Proof. vm_refl. Qed.
Lemma D_430cc : decode_any W_430cc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_430d0 : bv 32 := 0x02113423.
Lemma F_430d0 : fetch_word Plain.M.loaded_segments (0x43118 : word) = Some W_430d0.
Proof. vm_refl. Qed.
Lemma D_430d0 : decode_any W_430d0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_430d4 : bv 32 := 0x02813023.
Lemma F_430d4 : fetch_word Plain.M.loaded_segments (0x4311c : word) = Some W_430d4.
Proof. vm_refl. Qed.
Lemma D_430d4 : decode_any W_430d4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_430d8 : bv 32 := 0x00913c23.
Lemma F_430d8 : fetch_word Plain.M.loaded_segments (0x43120 : word) = Some W_430d8.
Proof. vm_refl. Qed.
Lemma D_430d8 : decode_any W_430d8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_430dc : bv 32 := 0x01213823.
Lemma F_430dc : fetch_word Plain.M.loaded_segments (0x43124 : word) = Some W_430dc.
Proof. vm_refl. Qed.
Lemma D_430dc : decode_any W_430dc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_430e0 : bv 32 := 0x01313423.
Lemma F_430e0 : fetch_word Plain.M.loaded_segments (0x43128 : word) = Some W_430e0.
Proof. vm_refl. Qed.
Lemma D_430e0 : decode_any W_430e0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_430e4 : bv 32 := 0x01413023.
Lemma F_430e4 : fetch_word Plain.M.loaded_segments (0x4312c : word) = Some W_430e4.
Proof. vm_refl. Qed.
Lemma D_430e4 : decode_any W_430e4 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_430e8 : bv 32 := 0x00058493.
Lemma F_430e8 : fetch_word Plain.M.loaded_segments (0x43130 : word) = Some W_430e8.
Proof. vm_refl. Qed.
Lemma D_430e8 : decode_any W_430e8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_430ec : bv 32 := 0x00050413.
Lemma F_430ec : fetch_word Plain.M.loaded_segments (0x43134 : word) = Some W_430ec.
Proof. vm_refl. Qed.
Lemma D_430ec : decode_any W_430ec = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_430f0 : bv 32 := 0x00054503.
Lemma F_430f0 : fetch_word Plain.M.loaded_segments (0x43138 : word) = Some W_430f0.
Proof. vm_refl. Qed.
Lemma D_430f0 : decode_any W_430f0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_430f4 : bv 32 := 0x00843a03.
Lemma F_430f4 : fetch_word Plain.M.loaded_segments (0x4313c : word) = Some W_430f4.
Proof. vm_refl. Qed.
Lemma D_430f4 : decode_any W_430f4 = Some (Load SZ8 true 20 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_430f8 : bv 32 := 0x00157593.
Lemma F_430f8 : fetch_word Plain.M.loaded_segments (0x43140 : word) = Some W_430f8.
Proof. vm_refl. Qed.
Lemma D_430f8 : decode_any W_430f8 = Some (OpImm ALU_AND 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_430fc : bv 32 := 0x01040913.
Lemma F_430fc : fetch_word Plain.M.loaded_segments (0x43144 : word) = Some W_430fc.
Proof. vm_refl. Qed.
Lemma D_430fc : decode_any W_430fc = Some (OpImm ALU_ADD 18 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_43100 : bv 32 := 0x00090513.
Lemma F_43100 : fetch_word Plain.M.loaded_segments (0x43148 : word) = Some W_43100.
Proof. vm_refl. Qed.
Lemma D_43100 : decode_any W_43100 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43104 : bv 32 := 0x00058463.
Lemma F_43104 : fetch_word Plain.M.loaded_segments (0x4314c : word) = Some W_43104.
Proof. vm_refl. Qed.
Lemma D_43104 : decode_any W_43104 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_43108 : bv 32 := 0x01843503.
Lemma F_43108 : fetch_word Plain.M.loaded_segments (0x43150 : word) = Some W_43108.
Proof. vm_refl. Qed.
Lemma D_43108 : decode_any W_43108 = Some (Load SZ8 true 10 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4310c : bv 32 := 0x00053983.
Lemma F_4310c : fetch_word Plain.M.loaded_segments (0x43154 : word) = Some W_4310c.
Proof. vm_refl. Qed.
Lemma D_4310c : decode_any W_4310c = Some (Load SZ8 true 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43110 : bv 32 := 0x001a0593.
Lemma F_43110 : fetch_word Plain.M.loaded_segments (0x43158 : word) = Some W_43110.
Proof. vm_refl. Qed.
Lemma D_43110 : decode_any W_43110 = Some (OpImm ALU_ADD 11 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_43114 : bv 32 := 0x00040513.
Lemma F_43114 : fetch_word Plain.M.loaded_segments (0x4315c : word) = Some W_43114.
Proof. vm_refl. Qed.
Lemma D_43114 : decode_any W_43114 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43118 : bv 32 := 0x2dc000ef.
Lemma F_43118 : fetch_word Plain.M.loaded_segments (0x43160 : word) = Some W_43118.
Proof. vm_refl. Qed.
Lemma D_43118 : decode_any W_43118 = Some (Jal 1 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_4311c : bv 32 := 0x00044503.
Lemma F_4311c : fetch_word Plain.M.loaded_segments (0x43164 : word) = Some W_4311c.
Proof. vm_refl. Qed.
Lemma D_4311c : decode_any W_4311c = Some (Load SZ1 false 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43120 : bv 32 := 0x00157513.
Lemma F_43120 : fetch_word Plain.M.loaded_segments (0x43168 : word) = Some W_43120.
Proof. vm_refl. Qed.
Lemma D_43120 : decode_any W_43120 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_43124 : bv 32 := 0x00050463.
Lemma F_43124 : fetch_word Plain.M.loaded_segments (0x4316c : word) = Some W_43124.
Proof. vm_refl. Qed.
Lemma D_43124 : decode_any W_43124 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_43128 : bv 32 := 0x01843903.
Lemma F_43128 : fetch_word Plain.M.loaded_segments (0x43170 : word) = Some W_43128.
Proof. vm_refl. Qed.
Lemma D_43128 : decode_any W_43128 = Some (Load SZ8 true 18 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4312c : bv 32 := 0x003a1513.
Lemma F_4312c : fetch_word Plain.M.loaded_segments (0x43174 : word) = Some W_4312c.
Proof. vm_refl. Qed.
Lemma D_4312c : decode_any W_4312c = Some (ShiftImm ALU_SLL 10 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_43130 : bv 32 := 0x00000593.
Lemma F_43130 : fetch_word Plain.M.loaded_segments (0x43178 : word) = Some W_43130.
Proof. vm_refl. Qed.
Lemma D_43130 : decode_any W_43130 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43134 : bv 32 := 0x040a0c63.
Lemma F_43134 : fetch_word Plain.M.loaded_segments (0x4317c : word) = Some W_43134.
Proof. vm_refl. Qed.
Lemma D_43134 : decode_any W_43134 = Some (Branch BC_EQ 20 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_43138 : bv 32 := 0x02049693.
Lemma F_43138 : fetch_word Plain.M.loaded_segments (0x43180 : word) = Some W_43138.
Proof. vm_refl. Qed.
Lemma D_43138 : decode_any W_43138 = Some (ShiftImm ALU_SLL 13 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4313c : bv 32 := 0x00890613.
Lemma F_4313c : fetch_word Plain.M.loaded_segments (0x43184 : word) = Some W_4313c.
Proof. vm_refl. Qed.
Lemma D_4313c : decode_any W_4313c = Some (OpImm ALU_ADD 12 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_43140 : bv 32 := 0x0206d693.
Lemma F_43140 : fetch_word Plain.M.loaded_segments (0x43188 : word) = Some W_43140.
Proof. vm_refl. Qed.
Lemma D_43140 : decode_any W_43140 = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_43144 : bv 32 := 0x00a60733.
Lemma F_43144 : fetch_word Plain.M.loaded_segments (0x4318c : word) = Some W_43144.
Proof. vm_refl. Qed.
Lemma D_43144 : decode_any W_43144 = Some (Op ALU_ADD 14 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_43148 : bv 32 := 0x0209d793.
Lemma F_43148 : fetch_word Plain.M.loaded_segments (0x43190 : word) = Some W_43148.
Proof. vm_refl. Qed.
Lemma D_43148 : decode_any W_43148 = Some (ShiftImm ALU_SRL 15 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4314c : bv 32 := 0x02099993.
Lemma F_4314c : fetch_word Plain.M.loaded_segments (0x43194 : word) = Some W_4314c.
Proof. vm_refl. Qed.
Lemma D_4314c : decode_any W_4314c = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_43150 : bv 32 := 0x0209d813.
Lemma F_43150 : fetch_word Plain.M.loaded_segments (0x43198 : word) = Some W_43150.
Proof. vm_refl. Qed.
Lemma D_43150 : decode_any W_43150 = Some (ShiftImm ALU_SRL 16 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_43154 : bv 32 := 0x02d787b3.
Lemma F_43154 : fetch_word Plain.M.loaded_segments (0x4319c : word) = Some W_43154.
Proof. vm_refl. Qed.
Lemma D_43154 : decode_any W_43154 = Some (Mul M_MUL 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_43158 : bv 32 := 0x02d80833.
Lemma F_43158 : fetch_word Plain.M.loaded_segments (0x431a0 : word) = Some W_43158.
Proof. vm_refl. Qed.
Lemma D_43158 : decode_any W_43158 = Some (Mul M_MUL 16 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4315c : bv 32 := 0x02079893.
Lemma F_4315c : fetch_word Plain.M.loaded_segments (0x431a4 : word) = Some W_4315c.
Proof. vm_refl. Qed.
Lemma D_4315c : decode_any W_4315c = Some (ShiftImm ALU_SLL 17 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_43160 : bv 32 := 0x0207d793.
Lemma F_43160 : fetch_word Plain.M.loaded_segments (0x431a8 : word) = Some W_43160.
Proof. vm_refl. Qed.
Lemma D_43160 : decode_any W_43160 = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_43164 : bv 32 := 0x01088833.
Lemma F_43164 : fetch_word Plain.M.loaded_segments (0x431ac : word) = Some W_43164.
Proof. vm_refl. Qed.
Lemma D_43164 : decode_any W_43164 = Some (Op ALU_ADD 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_43168 : bv 32 := 0x011838b3.
Lemma F_43168 : fetch_word Plain.M.loaded_segments (0x431b0 : word) = Some W_43168.
Proof. vm_refl. Qed.
Lemma D_43168 : decode_any W_43168 = Some (Op ALU_SLTU 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4316c : bv 32 := 0x011787b3.
Lemma F_4316c : fetch_word Plain.M.loaded_segments (0x431b4 : word) = Some W_4316c.
Proof. vm_refl. Qed.
Lemma D_4316c : decode_any W_4316c = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_43170 : bv 32 := 0x00063983.
Lemma F_43170 : fetch_word Plain.M.loaded_segments (0x431b8 : word) = Some W_43170.
Proof. vm_refl. Qed.
Lemma D_43170 : decode_any W_43170 = Some (Load SZ8 true 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43174 : bv 32 := 0x00b805b3.
Lemma F_43174 : fetch_word Plain.M.loaded_segments (0x431bc : word) = Some W_43174.
Proof. vm_refl. Qed.
Lemma D_43174 : decode_any W_43174 = Some (Op ALU_ADD 11 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_43178 : bv 32 := 0x0105b833.
Lemma F_43178 : fetch_word Plain.M.loaded_segments (0x431c0 : word) = Some W_43178.
Proof. vm_refl. Qed.
Lemma D_43178 : decode_any W_43178 = Some (Op ALU_SLTU 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4317c : bv 32 := 0xfeb63c23.
Lemma F_4317c : fetch_word Plain.M.loaded_segments (0x431c4 : word) = Some W_4317c.
Proof. vm_refl. Qed.
Lemma D_4317c : decode_any W_4317c = Some (Store SZ8 12 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_43180 : bv 32 := 0x00860613.
Lemma F_43180 : fetch_word Plain.M.loaded_segments (0x431c8 : word) = Some W_43180.
Proof. vm_refl. Qed.
Lemma D_43180 : decode_any W_43180 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_43184 : bv 32 := 0x010785b3.
Lemma F_43184 : fetch_word Plain.M.loaded_segments (0x431cc : word) = Some W_43184.
Proof. vm_refl. Qed.
Lemma D_43184 : decode_any W_43184 = Some (Op ALU_ADD 11 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_43188 : bv 32 := 0xfce610e3.
Lemma F_43188 : fetch_word Plain.M.loaded_segments (0x431d0 : word) = Some W_43188.
Proof. vm_refl. Qed.
Lemma D_43188 : decode_any W_43188 = Some (Branch BC_NE 12 14 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_4318c : bv 32 := 0x00a90533.
Lemma F_4318c : fetch_word Plain.M.loaded_segments (0x431d4 : word) = Some W_4318c.
Proof. vm_refl. Qed.
Lemma D_4318c : decode_any W_4318c = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_43190 : bv 32 := 0x00b53023.
Lemma F_43190 : fetch_word Plain.M.loaded_segments (0x431d8 : word) = Some W_43190.
Proof. vm_refl. Qed.
Lemma D_43190 : decode_any W_43190 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43194 : bv 32 := 0x00040513.
Lemma F_43194 : fetch_word Plain.M.loaded_segments (0x431dc : word) = Some W_43194.
Proof. vm_refl. Qed.
Lemma D_43194 : decode_any W_43194 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_43198 : bv 32 := 0x64c000ef.
Lemma F_43198 : fetch_word Plain.M.loaded_segments (0x431e0 : word) = Some W_43198.
Proof. vm_refl. Qed.
Lemma D_43198 : decode_any W_43198 = Some (Jal 1 1612, 4%Z).
Proof. vm_refl. Qed.

Definition W_4319c : bv 32 := 0x00040513.
Lemma F_4319c : fetch_word Plain.M.loaded_segments (0x431e4 : word) = Some W_4319c.
Proof. vm_refl. Qed.
Lemma D_4319c : decode_any W_4319c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_431a0 : bv 32 := 0x02813083.
Lemma F_431a0 : fetch_word Plain.M.loaded_segments (0x431e8 : word) = Some W_431a0.
Proof. vm_refl. Qed.
Lemma D_431a0 : decode_any W_431a0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_431a4 : bv 32 := 0x02013403.
Lemma F_431a4 : fetch_word Plain.M.loaded_segments (0x431ec : word) = Some W_431a4.
Proof. vm_refl. Qed.
Lemma D_431a4 : decode_any W_431a4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_431a8 : bv 32 := 0x01813483.
Lemma F_431a8 : fetch_word Plain.M.loaded_segments (0x431f0 : word) = Some W_431a8.
Proof. vm_refl. Qed.
Lemma D_431a8 : decode_any W_431a8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_431ac : bv 32 := 0x01013903.
Lemma F_431ac : fetch_word Plain.M.loaded_segments (0x431f4 : word) = Some W_431ac.
Proof. vm_refl. Qed.
Lemma D_431ac : decode_any W_431ac = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_431b0 : bv 32 := 0x00813983.
Lemma F_431b0 : fetch_word Plain.M.loaded_segments (0x431f8 : word) = Some W_431b0.
Proof. vm_refl. Qed.
Lemma D_431b0 : decode_any W_431b0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_431b4 : bv 32 := 0x00013a03.
Lemma F_431b4 : fetch_word Plain.M.loaded_segments (0x431fc : word) = Some W_431b4.
Proof. vm_refl. Qed.
Lemma D_431b4 : decode_any W_431b4 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_431b8 : bv 32 := 0x03010113.
Lemma F_431b8 : fetch_word Plain.M.loaded_segments (0x43200 : word) = Some W_431b8.
Proof. vm_refl. Qed.
Lemma D_431b8 : decode_any W_431b8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_431bc : bv 32 := 0x00008067.
Lemma F_431bc : fetch_word Plain.M.loaded_segments (0x43204 : word) = Some W_431bc.
Proof. vm_refl. Qed.
Lemma D_431bc : decode_any W_431bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
