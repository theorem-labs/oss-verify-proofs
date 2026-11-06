(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_c3f68 : bv 32 := 0x0035f693.
Lemma F_c3f68 : fetch_word Plain.M.loaded_segments (0xc4120 : word) = Some W_c3f68.
Proof. vm_refl. Qed.
Lemma D_c3f68 : decode_any W_c3f68 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f6c : bv 32 := 0x10068863.
Lemma F_c3f6c : fetch_word Plain.M.loaded_segments (0xc4124 : word) = Some W_c3f6c.
Proof. vm_refl. Qed.
Lemma D_c3f6c : decode_any W_c3f6c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f70 : bv 32 := 0x02060e63.
Lemma F_c3f70 : fetch_word Plain.M.loaded_segments (0xc4128 : word) = Some W_c3f70.
Proof. vm_refl. Qed.
Lemma D_c3f70 : decode_any W_c3f70 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f74 : bv 32 := 0x00158713.
Lemma F_c3f74 : fetch_word Plain.M.loaded_segments (0xc412c : word) = Some W_c3f74.
Proof. vm_refl. Qed.
Lemma D_c3f74 : decode_any W_c3f74 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f78 : bv 32 := 0x00100793.
Lemma F_c3f78 : fetch_word Plain.M.loaded_segments (0xc4130 : word) = Some W_c3f78.
Proof. vm_refl. Qed.
Lemma D_c3f78 : decode_any W_c3f78 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f7c : bv 32 := 0x00050693.
Lemma F_c3f7c : fetch_word Plain.M.loaded_segments (0xc4134 : word) = Some W_c3f7c.
Proof. vm_refl. Qed.
Lemma D_c3f7c : decode_any W_c3f7c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f80 : bv 32 := 0x0005c883.
Lemma F_c3f80 : fetch_word Plain.M.loaded_segments (0xc4138 : word) = Some W_c3f80.
Proof. vm_refl. Qed.
Lemma D_c3f80 : decode_any W_c3f80 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f84 : bv 32 := 0x00060813.
Lemma F_c3f84 : fetch_word Plain.M.loaded_segments (0xc413c : word) = Some W_c3f84.
Proof. vm_refl. Qed.
Lemma D_c3f84 : decode_any W_c3f84 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f88 : bv 32 := 0x00158593.
Lemma F_c3f88 : fetch_word Plain.M.loaded_segments (0xc4140 : word) = Some W_c3f88.
Proof. vm_refl. Qed.
Lemma D_c3f88 : decode_any W_c3f88 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f8c : bv 32 := 0x00377293.
Lemma F_c3f8c : fetch_word Plain.M.loaded_segments (0xc4144 : word) = Some W_c3f8c.
Proof. vm_refl. Qed.
Lemma D_c3f8c : decode_any W_c3f8c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f90 : bv 32 := 0x01168023.
Lemma F_c3f90 : fetch_word Plain.M.loaded_segments (0xc4148 : word) = Some W_c3f90.
Proof. vm_refl. Qed.
Lemma D_c3f90 : decode_any W_c3f90 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f94 : bv 32 := 0x00168693.
Lemma F_c3f94 : fetch_word Plain.M.loaded_segments (0xc414c : word) = Some W_c3f94.
Proof. vm_refl. Qed.
Lemma D_c3f94 : decode_any W_c3f94 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f98 : bv 32 := 0xfff60613.
Lemma F_c3f98 : fetch_word Plain.M.loaded_segments (0xc4150 : word) = Some W_c3f98.
Proof. vm_refl. Qed.
Lemma D_c3f98 : decode_any W_c3f98 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f9c : bv 32 := 0x00028a63.
Lemma F_c3f9c : fetch_word Plain.M.loaded_segments (0xc4154 : word) = Some W_c3f9c.
Proof. vm_refl. Qed.
Lemma D_c3f9c : decode_any W_c3f9c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fa0 : bv 32 := 0x00170713.
Lemma F_c3fa0 : fetch_word Plain.M.loaded_segments (0xc4158 : word) = Some W_c3fa0.
Proof. vm_refl. Qed.
Lemma D_c3fa0 : decode_any W_c3fa0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fa4 : bv 32 := 0xfcf81ee3.
Lemma F_c3fa4 : fetch_word Plain.M.loaded_segments (0xc415c : word) = Some W_c3fa4.
Proof. vm_refl. Qed.
Lemma D_c3fa4 : decode_any W_c3fa4 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fa8 : bv 32 := 0x0080006f.
Lemma F_c3fa8 : fetch_word Plain.M.loaded_segments (0xc4160 : word) = Some W_c3fa8.
Proof. vm_refl. Qed.
Lemma D_c3fa8 : decode_any W_c3fa8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fac : bv 32 := 0x00050693.
Lemma F_c3fac : fetch_word Plain.M.loaded_segments (0xc4164 : word) = Some W_c3fac.
Proof. vm_refl. Qed.
Lemma D_c3fac : decode_any W_c3fac = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fb0 : bv 32 := 0x0036f793.
Lemma F_c3fb0 : fetch_word Plain.M.loaded_segments (0xc4168 : word) = Some W_c3fb0.
Proof. vm_refl. Qed.
Lemma D_c3fb0 : decode_any W_c3fb0 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fb4 : bv 32 := 0x0c078a63.
Lemma F_c3fb4 : fetch_word Plain.M.loaded_segments (0xc416c : word) = Some W_c3fb4.
Proof. vm_refl. Qed.
Lemma D_c3fb4 : decode_any W_c3fb4 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fb8 : bv 32 := 0x02000713.
Lemma F_c3fb8 : fetch_word Plain.M.loaded_segments (0xc4170 : word) = Some W_c3fb8.
Proof. vm_refl. Qed.
Lemma D_c3fb8 : decode_any W_c3fb8 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fbc : bv 32 := 0x02e67063.
Lemma F_c3fbc : fetch_word Plain.M.loaded_segments (0xc4174 : word) = Some W_c3fbc.
Proof. vm_refl. Qed.
Lemma D_c3fbc : decode_any W_c3fbc = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fc0 : bv 32 := 0x01000713.
Lemma F_c3fc0 : fetch_word Plain.M.loaded_segments (0xc4178 : word) = Some W_c3fc0.
Proof. vm_refl. Qed.
Lemma D_c3fc0 : decode_any W_c3fc0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fc4 : bv 32 := 0x24e67863.
Lemma F_c3fc4 : fetch_word Plain.M.loaded_segments (0xc417c : word) = Some W_c3fc4.
Proof. vm_refl. Qed.
Lemma D_c3fc4 : decode_any W_c3fc4 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fc8 : bv 32 := 0x00867713.
Lemma F_c3fc8 : fetch_word Plain.M.loaded_segments (0xc4180 : word) = Some W_c3fc8.
Proof. vm_refl. Qed.
Lemma D_c3fc8 : decode_any W_c3fc8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fcc : bv 32 := 0x2c071e63.
Lemma F_c3fcc : fetch_word Plain.M.loaded_segments (0xc4184 : word) = Some W_c3fcc.
Proof. vm_refl. Qed.
Lemma D_c3fcc : decode_any W_c3fcc = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fd0 : bv 32 := 0x00467713.
Lemma F_c3fd0 : fetch_word Plain.M.loaded_segments (0xc4188 : word) = Some W_c3fd0.
Proof. vm_refl. Qed.
Lemma D_c3fd0 : decode_any W_c3fd0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fd4 : bv 32 := 0x32071463.
Lemma F_c3fd4 : fetch_word Plain.M.loaded_segments (0xc418c : word) = Some W_c3fd4.
Proof. vm_refl. Qed.
Lemma D_c3fd4 : decode_any W_c3fd4 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fd8 : bv 32 := 0x3500006f.
Lemma F_c3fd8 : fetch_word Plain.M.loaded_segments (0xc4190 : word) = Some W_c3fd8.
Proof. vm_refl. Qed.
Lemma D_c3fd8 : decode_any W_c3fd8 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fdc : bv 32 := 0x0005a703.
Lemma F_c3fdc : fetch_word Plain.M.loaded_segments (0xc4194 : word) = Some W_c3fdc.
Proof. vm_refl. Qed.
Lemma D_c3fdc : decode_any W_c3fdc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fe0 : bv 32 := 0x00300813.
Lemma F_c3fe0 : fetch_word Plain.M.loaded_segments (0xc4198 : word) = Some W_c3fe0.
Proof. vm_refl. Qed.
Lemma D_c3fe0 : decode_any W_c3fe0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fe4 : bv 32 := 0x11078e63.
Lemma F_c3fe4 : fetch_word Plain.M.loaded_segments (0xc419c : word) = Some W_c3fe4.
Proof. vm_refl. Qed.
Lemma D_c3fe4 : decode_any W_c3fe4 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fe8 : bv 32 := 0x00200813.
Lemma F_c3fe8 : fetch_word Plain.M.loaded_segments (0xc41a0 : word) = Some W_c3fe8.
Proof. vm_refl. Qed.
Lemma D_c3fe8 : decode_any W_c3fe8 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3fec : bv 32 := 0x19079c63.
Lemma F_c3fec : fetch_word Plain.M.loaded_segments (0xc41a4 : word) = Some W_c3fec.
Proof. vm_refl. Qed.
Lemma D_c3fec : decode_any W_c3fec = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ff0 : bv 32 := 0x00875793.
Lemma F_c3ff0 : fetch_word Plain.M.loaded_segments (0xc41a8 : word) = Some W_c3ff0.
Proof. vm_refl. Qed.
Lemma D_c3ff0 : decode_any W_c3ff0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ff4 : bv 32 := 0xffe60613.
Lemma F_c3ff4 : fetch_word Plain.M.loaded_segments (0xc41ac : word) = Some W_c3ff4.
Proof. vm_refl. Qed.
Lemma D_c3ff4 : decode_any W_c3ff4 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ff8 : bv 32 := 0x00e68023.
Lemma F_c3ff8 : fetch_word Plain.M.loaded_segments (0xc41b0 : word) = Some W_c3ff8.
Proof. vm_refl. Qed.
Lemma D_c3ff8 : decode_any W_c3ff8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ffc : bv 32 := 0x00f680a3.
Lemma F_c3ffc : fetch_word Plain.M.loaded_segments (0xc41b4 : word) = Some W_c3ffc.
Proof. vm_refl. Qed.
Lemma D_c3ffc : decode_any W_c3ffc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4000 : bv 32 := 0x00268693.
Lemma F_c4000 : fetch_word Plain.M.loaded_segments (0xc41b8 : word) = Some W_c4000.
Proof. vm_refl. Qed.
Lemma D_c4000 : decode_any W_c4000 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4004 : bv 32 := 0x01058593.
Lemma F_c4004 : fetch_word Plain.M.loaded_segments (0xc41bc : word) = Some W_c4004.
Proof. vm_refl. Qed.
Lemma D_c4004 : decode_any W_c4004 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4008 : bv 32 := 0x01100793.
Lemma F_c4008 : fetch_word Plain.M.loaded_segments (0xc41c0 : word) = Some W_c4008.
Proof. vm_refl. Qed.
Lemma D_c4008 : decode_any W_c4008 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c400c : bv 32 := 0x0107581b.
Lemma F_c400c : fetch_word Plain.M.loaded_segments (0xc41c4 : word) = Some W_c400c.
Proof. vm_refl. Qed.
Lemma D_c400c : decode_any W_c400c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4010 : bv 32 := 0xff45a883.
Lemma F_c4010 : fetch_word Plain.M.loaded_segments (0xc41c8 : word) = Some W_c4010.
Proof. vm_refl. Qed.
Lemma D_c4010 : decode_any W_c4010 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4014 : bv 32 := 0xff85a283.
Lemma F_c4014 : fetch_word Plain.M.loaded_segments (0xc41cc : word) = Some W_c4014.
Proof. vm_refl. Qed.
Lemma D_c4014 : decode_any W_c4014 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4018 : bv 32 := 0xffc5a303.
Lemma F_c4018 : fetch_word Plain.M.loaded_segments (0xc41d0 : word) = Some W_c4018.
Proof. vm_refl. Qed.
Lemma D_c4018 : decode_any W_c4018 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c401c : bv 32 := 0x0005a703.
Lemma F_c401c : fetch_word Plain.M.loaded_segments (0xc41d4 : word) = Some W_c401c.
Proof. vm_refl. Qed.
Lemma D_c401c : decode_any W_c401c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4020 : bv 32 := 0x01089393.
Lemma F_c4020 : fetch_word Plain.M.loaded_segments (0xc41d8 : word) = Some W_c4020.
Proof. vm_refl. Qed.
Lemma D_c4020 : decode_any W_c4020 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4024 : bv 32 := 0x0108d89b.
Lemma F_c4024 : fetch_word Plain.M.loaded_segments (0xc41dc : word) = Some W_c4024.
Proof. vm_refl. Qed.
Lemma D_c4024 : decode_any W_c4024 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4028 : bv 32 := 0x0103e833.
Lemma F_c4028 : fetch_word Plain.M.loaded_segments (0xc41e0 : word) = Some W_c4028.
Proof. vm_refl. Qed.
Lemma D_c4028 : decode_any W_c4028 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c402c : bv 32 := 0x01029393.
Lemma F_c402c : fetch_word Plain.M.loaded_segments (0xc41e4 : word) = Some W_c402c.
Proof. vm_refl. Qed.
Lemma D_c402c : decode_any W_c402c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4030 : bv 32 := 0x0102d29b.
Lemma F_c4030 : fetch_word Plain.M.loaded_segments (0xc41e8 : word) = Some W_c4030.
Proof. vm_refl. Qed.
Lemma D_c4030 : decode_any W_c4030 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4034 : bv 32 := 0x0113e8b3.
Lemma F_c4034 : fetch_word Plain.M.loaded_segments (0xc41ec : word) = Some W_c4034.
Proof. vm_refl. Qed.
Lemma D_c4034 : decode_any W_c4034 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4038 : bv 32 := 0x01031393.
Lemma F_c4038 : fetch_word Plain.M.loaded_segments (0xc41f0 : word) = Some W_c4038.
Proof. vm_refl. Qed.
Lemma D_c4038 : decode_any W_c4038 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c403c : bv 32 := 0x0103531b.
Lemma F_c403c : fetch_word Plain.M.loaded_segments (0xc41f4 : word) = Some W_c403c.
Proof. vm_refl. Qed.
Lemma D_c403c : decode_any W_c403c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4040 : bv 32 := 0x0053e2b3.
Lemma F_c4040 : fetch_word Plain.M.loaded_segments (0xc41f8 : word) = Some W_c4040.
Proof. vm_refl. Qed.
Lemma D_c4040 : decode_any W_c4040 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4044 : bv 32 := 0x01071393.
Lemma F_c4044 : fetch_word Plain.M.loaded_segments (0xc41fc : word) = Some W_c4044.
Proof. vm_refl. Qed.
Lemma D_c4044 : decode_any W_c4044 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4048 : bv 32 := 0x0063e333.
Lemma F_c4048 : fetch_word Plain.M.loaded_segments (0xc4200 : word) = Some W_c4048.
Proof. vm_refl. Qed.
Lemma D_c4048 : decode_any W_c4048 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c404c : bv 32 := 0xff060613.
Lemma F_c404c : fetch_word Plain.M.loaded_segments (0xc4204 : word) = Some W_c404c.
Proof. vm_refl. Qed.
Lemma D_c404c : decode_any W_c404c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4050 : bv 32 := 0x0106a023.
Lemma F_c4050 : fetch_word Plain.M.loaded_segments (0xc4208 : word) = Some W_c4050.
Proof. vm_refl. Qed.
Lemma D_c4050 : decode_any W_c4050 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4054 : bv 32 := 0x0116a223.
Lemma F_c4054 : fetch_word Plain.M.loaded_segments (0xc420c : word) = Some W_c4054.
Proof. vm_refl. Qed.
Lemma D_c4054 : decode_any W_c4054 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4058 : bv 32 := 0x0056a423.
Lemma F_c4058 : fetch_word Plain.M.loaded_segments (0xc4210 : word) = Some W_c4058.
Proof. vm_refl. Qed.
Lemma D_c4058 : decode_any W_c4058 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c405c : bv 32 := 0x0066a623.
Lemma F_c405c : fetch_word Plain.M.loaded_segments (0xc4214 : word) = Some W_c405c.
Proof. vm_refl. Qed.
Lemma D_c405c : decode_any W_c405c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4060 : bv 32 := 0x01068693.
Lemma F_c4060 : fetch_word Plain.M.loaded_segments (0xc4218 : word) = Some W_c4060.
Proof. vm_refl. Qed.
Lemma D_c4060 : decode_any W_c4060 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4064 : bv 32 := 0x01058593.
Lemma F_c4064 : fetch_word Plain.M.loaded_segments (0xc421c : word) = Some W_c4064.
Proof. vm_refl. Qed.
Lemma D_c4064 : decode_any W_c4064 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4068 : bv 32 := 0xfac7e2e3.
Lemma F_c4068 : fetch_word Plain.M.loaded_segments (0xc4220 : word) = Some W_c4068.
Proof. vm_refl. Qed.
Lemma D_c4068 : decode_any W_c4068 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c406c : bv 32 := 0xff258593.
Lemma F_c406c : fetch_word Plain.M.loaded_segments (0xc4224 : word) = Some W_c406c.
Proof. vm_refl. Qed.
Lemma D_c406c : decode_any W_c406c = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4070 : bv 32 := 0x01000713.
Lemma F_c4070 : fetch_word Plain.M.loaded_segments (0xc4228 : word) = Some W_c4070.
Proof. vm_refl. Qed.
Lemma D_c4070 : decode_any W_c4070 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4074 : bv 32 := 0xf4e66ae3.
Lemma F_c4074 : fetch_word Plain.M.loaded_segments (0xc422c : word) = Some W_c4074.
Proof. vm_refl. Qed.
Lemma D_c4074 : decode_any W_c4074 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4078 : bv 32 := 0x19c0006f.
Lemma F_c4078 : fetch_word Plain.M.loaded_segments (0xc4230 : word) = Some W_c4078.
Proof. vm_refl. Qed.
Lemma D_c4078 : decode_any W_c4078 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c407c : bv 32 := 0x00050693.
Lemma F_c407c : fetch_word Plain.M.loaded_segments (0xc4234 : word) = Some W_c407c.
Proof. vm_refl. Qed.
Lemma D_c407c : decode_any W_c407c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4080 : bv 32 := 0x00357793.
Lemma F_c4080 : fetch_word Plain.M.loaded_segments (0xc4238 : word) = Some W_c4080.
Proof. vm_refl. Qed.
Lemma D_c4080 : decode_any W_c4080 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4084 : bv 32 := 0xf2079ae3.
Lemma F_c4084 : fetch_word Plain.M.loaded_segments (0xc423c : word) = Some W_c4084.
Proof. vm_refl. Qed.
Lemma D_c4084 : decode_any W_c4084 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4088 : bv 32 := 0x01000713.
Lemma F_c4088 : fetch_word Plain.M.loaded_segments (0xc4240 : word) = Some W_c4088.
Proof. vm_refl. Qed.
Lemma D_c4088 : decode_any W_c4088 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c408c : bv 32 := 0x02e66c63.
Lemma F_c408c : fetch_word Plain.M.loaded_segments (0xc4244 : word) = Some W_c408c.
Proof. vm_refl. Qed.
Lemma D_c408c : decode_any W_c408c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4090 : bv 32 := 0x00f00713.
Lemma F_c4090 : fetch_word Plain.M.loaded_segments (0xc4248 : word) = Some W_c4090.
Proof. vm_refl. Qed.
Lemma D_c4090 : decode_any W_c4090 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4094 : bv 32 := 0x0005a783.
Lemma F_c4094 : fetch_word Plain.M.loaded_segments (0xc424c : word) = Some W_c4094.
Proof. vm_refl. Qed.
Lemma D_c4094 : decode_any W_c4094 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4098 : bv 32 := 0x0045a803.
Lemma F_c4098 : fetch_word Plain.M.loaded_segments (0xc4250 : word) = Some W_c4098.
Proof. vm_refl. Qed.
Lemma D_c4098 : decode_any W_c4098 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c409c : bv 32 := 0x0085a883.
Lemma F_c409c : fetch_word Plain.M.loaded_segments (0xc4254 : word) = Some W_c409c.
Proof. vm_refl. Qed.
Lemma D_c409c : decode_any W_c409c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40a0 : bv 32 := 0x00c5a283.
Lemma F_c40a0 : fetch_word Plain.M.loaded_segments (0xc4258 : word) = Some W_c40a0.
Proof. vm_refl. Qed.
Lemma D_c40a0 : decode_any W_c40a0 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40a4 : bv 32 := 0x01058593.
Lemma F_c40a4 : fetch_word Plain.M.loaded_segments (0xc425c : word) = Some W_c40a4.
Proof. vm_refl. Qed.
Lemma D_c40a4 : decode_any W_c40a4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40a8 : bv 32 := 0xff060613.
Lemma F_c40a8 : fetch_word Plain.M.loaded_segments (0xc4260 : word) = Some W_c40a8.
Proof. vm_refl. Qed.
Lemma D_c40a8 : decode_any W_c40a8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40ac : bv 32 := 0x00f6a023.
Lemma F_c40ac : fetch_word Plain.M.loaded_segments (0xc4264 : word) = Some W_c40ac.
Proof. vm_refl. Qed.
Lemma D_c40ac : decode_any W_c40ac = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40b0 : bv 32 := 0x0106a223.
Lemma F_c40b0 : fetch_word Plain.M.loaded_segments (0xc4268 : word) = Some W_c40b0.
Proof. vm_refl. Qed.
Lemma D_c40b0 : decode_any W_c40b0 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40b4 : bv 32 := 0x0116a423.
Lemma F_c40b4 : fetch_word Plain.M.loaded_segments (0xc426c : word) = Some W_c40b4.
Proof. vm_refl. Qed.
Lemma D_c40b4 : decode_any W_c40b4 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40b8 : bv 32 := 0x0056a623.
Lemma F_c40b8 : fetch_word Plain.M.loaded_segments (0xc4270 : word) = Some W_c40b8.
Proof. vm_refl. Qed.
Lemma D_c40b8 : decode_any W_c40b8 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40bc : bv 32 := 0x01068693.
Lemma F_c40bc : fetch_word Plain.M.loaded_segments (0xc4274 : word) = Some W_c40bc.
Proof. vm_refl. Qed.
Lemma D_c40bc : decode_any W_c40bc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40c0 : bv 32 := 0xfcc76ae3.
Lemma F_c40c0 : fetch_word Plain.M.loaded_segments (0xc4278 : word) = Some W_c40c0.
Proof. vm_refl. Qed.
Lemma D_c40c0 : decode_any W_c40c0 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40c4 : bv 32 := 0x00800713.
Lemma F_c40c4 : fetch_word Plain.M.loaded_segments (0xc427c : word) = Some W_c40c4.
Proof. vm_refl. Qed.
Lemma D_c40c4 : decode_any W_c40c4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40c8 : bv 32 := 0x00e66e63.
Lemma F_c40c8 : fetch_word Plain.M.loaded_segments (0xc4280 : word) = Some W_c40c8.
Proof. vm_refl. Qed.
Lemma D_c40c8 : decode_any W_c40c8 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40cc : bv 32 := 0x0005a703.
Lemma F_c40cc : fetch_word Plain.M.loaded_segments (0xc4284 : word) = Some W_c40cc.
Proof. vm_refl. Qed.
Lemma D_c40cc : decode_any W_c40cc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40d0 : bv 32 := 0x0045a783.
Lemma F_c40d0 : fetch_word Plain.M.loaded_segments (0xc4288 : word) = Some W_c40d0.
Proof. vm_refl. Qed.
Lemma D_c40d0 : decode_any W_c40d0 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40d4 : bv 32 := 0x00e6a023.
Lemma F_c40d4 : fetch_word Plain.M.loaded_segments (0xc428c : word) = Some W_c40d4.
Proof. vm_refl. Qed.
Lemma D_c40d4 : decode_any W_c40d4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40d8 : bv 32 := 0x00f6a223.
Lemma F_c40d8 : fetch_word Plain.M.loaded_segments (0xc4290 : word) = Some W_c40d8.
Proof. vm_refl. Qed.
Lemma D_c40d8 : decode_any W_c40d8 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40dc : bv 32 := 0x00868693.
Lemma F_c40dc : fetch_word Plain.M.loaded_segments (0xc4294 : word) = Some W_c40dc.
Proof. vm_refl. Qed.
Lemma D_c40dc : decode_any W_c40dc = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40e0 : bv 32 := 0x00858593.
Lemma F_c40e0 : fetch_word Plain.M.loaded_segments (0xc4298 : word) = Some W_c40e0.
Proof. vm_refl. Qed.
Lemma D_c40e0 : decode_any W_c40e0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40e4 : bv 32 := 0x00467713.
Lemma F_c40e4 : fetch_word Plain.M.loaded_segments (0xc429c : word) = Some W_c40e4.
Proof. vm_refl. Qed.
Lemma D_c40e4 : decode_any W_c40e4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40e8 : bv 32 := 0x24070063.
Lemma F_c40e8 : fetch_word Plain.M.loaded_segments (0xc42a0 : word) = Some W_c40e8.
Proof. vm_refl. Qed.
Lemma D_c40e8 : decode_any W_c40e8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40ec : bv 32 := 0x0005a703.
Lemma F_c40ec : fetch_word Plain.M.loaded_segments (0xc42a4 : word) = Some W_c40ec.
Proof. vm_refl. Qed.
Lemma D_c40ec : decode_any W_c40ec = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40f0 : bv 32 := 0x00458593.
Lemma F_c40f0 : fetch_word Plain.M.loaded_segments (0xc42a8 : word) = Some W_c40f0.
Proof. vm_refl. Qed.
Lemma D_c40f0 : decode_any W_c40f0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40f4 : bv 32 := 0x00e6a023.
Lemma F_c40f4 : fetch_word Plain.M.loaded_segments (0xc42ac : word) = Some W_c40f4.
Proof. vm_refl. Qed.
Lemma D_c40f4 : decode_any W_c40f4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40f8 : bv 32 := 0x00468693.
Lemma F_c40f8 : fetch_word Plain.M.loaded_segments (0xc42b0 : word) = Some W_c40f8.
Proof. vm_refl. Qed.
Lemma D_c40f8 : decode_any W_c40f8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c40fc : bv 32 := 0x22c0006f.
Lemma F_c40fc : fetch_word Plain.M.loaded_segments (0xc42b4 : word) = Some W_c40fc.
Proof. vm_refl. Qed.
Lemma D_c40fc : decode_any W_c40fc = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4100 : bv 32 := 0x00e68023.
Lemma F_c4100 : fetch_word Plain.M.loaded_segments (0xc42b8 : word) = Some W_c4100.
Proof. vm_refl. Qed.
Lemma D_c4100 : decode_any W_c4100 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4104 : bv 32 := 0x00168693.
Lemma F_c4104 : fetch_word Plain.M.loaded_segments (0xc42bc : word) = Some W_c4104.
Proof. vm_refl. Qed.
Lemma D_c4104 : decode_any W_c4104 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4108 : bv 32 := 0xfff60613.
Lemma F_c4108 : fetch_word Plain.M.loaded_segments (0xc42c0 : word) = Some W_c4108.
Proof. vm_refl. Qed.
Lemma D_c4108 : decode_any W_c4108 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c410c : bv 32 := 0x01058593.
Lemma F_c410c : fetch_word Plain.M.loaded_segments (0xc42c4 : word) = Some W_c410c.
Proof. vm_refl. Qed.
Lemma D_c410c : decode_any W_c410c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4110 : bv 32 := 0x01200793.
Lemma F_c4110 : fetch_word Plain.M.loaded_segments (0xc42c8 : word) = Some W_c4110.
Proof. vm_refl. Qed.
Lemma D_c4110 : decode_any W_c4110 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4114 : bv 32 := 0x0087581b.
Lemma F_c4114 : fetch_word Plain.M.loaded_segments (0xc42cc : word) = Some W_c4114.
Proof. vm_refl. Qed.
Lemma D_c4114 : decode_any W_c4114 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4118 : bv 32 := 0xff45a883.
Lemma F_c4118 : fetch_word Plain.M.loaded_segments (0xc42d0 : word) = Some W_c4118.
Proof. vm_refl. Qed.
Lemma D_c4118 : decode_any W_c4118 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c411c : bv 32 := 0xff85a283.
Lemma F_c411c : fetch_word Plain.M.loaded_segments (0xc42d4 : word) = Some W_c411c.
Proof. vm_refl. Qed.
Lemma D_c411c : decode_any W_c411c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4120 : bv 32 := 0xffc5a303.
Lemma F_c4120 : fetch_word Plain.M.loaded_segments (0xc42d8 : word) = Some W_c4120.
Proof. vm_refl. Qed.
Lemma D_c4120 : decode_any W_c4120 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4124 : bv 32 := 0x0005a703.
Lemma F_c4124 : fetch_word Plain.M.loaded_segments (0xc42dc : word) = Some W_c4124.
Proof. vm_refl. Qed.
Lemma D_c4124 : decode_any W_c4124 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4128 : bv 32 := 0x01889393.
Lemma F_c4128 : fetch_word Plain.M.loaded_segments (0xc42e0 : word) = Some W_c4128.
Proof. vm_refl. Qed.
Lemma D_c4128 : decode_any W_c4128 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c412c : bv 32 := 0x0088d89b.
Lemma F_c412c : fetch_word Plain.M.loaded_segments (0xc42e4 : word) = Some W_c412c.
Proof. vm_refl. Qed.
Lemma D_c412c : decode_any W_c412c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4130 : bv 32 := 0x0103e833.
Lemma F_c4130 : fetch_word Plain.M.loaded_segments (0xc42e8 : word) = Some W_c4130.
Proof. vm_refl. Qed.
Lemma D_c4130 : decode_any W_c4130 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4134 : bv 32 := 0x01829393.
Lemma F_c4134 : fetch_word Plain.M.loaded_segments (0xc42ec : word) = Some W_c4134.
Proof. vm_refl. Qed.
Lemma D_c4134 : decode_any W_c4134 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4138 : bv 32 := 0x0082d29b.
Lemma F_c4138 : fetch_word Plain.M.loaded_segments (0xc42f0 : word) = Some W_c4138.
Proof. vm_refl. Qed.
Lemma D_c4138 : decode_any W_c4138 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c413c : bv 32 := 0x0113e8b3.
Lemma F_c413c : fetch_word Plain.M.loaded_segments (0xc42f4 : word) = Some W_c413c.
Proof. vm_refl. Qed.
Lemma D_c413c : decode_any W_c413c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4140 : bv 32 := 0x01831393.
Lemma F_c4140 : fetch_word Plain.M.loaded_segments (0xc42f8 : word) = Some W_c4140.
Proof. vm_refl. Qed.
Lemma D_c4140 : decode_any W_c4140 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4144 : bv 32 := 0x0083531b.
Lemma F_c4144 : fetch_word Plain.M.loaded_segments (0xc42fc : word) = Some W_c4144.
Proof. vm_refl. Qed.
Lemma D_c4144 : decode_any W_c4144 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4148 : bv 32 := 0x0053e2b3.
Lemma F_c4148 : fetch_word Plain.M.loaded_segments (0xc4300 : word) = Some W_c4148.
Proof. vm_refl. Qed.
Lemma D_c4148 : decode_any W_c4148 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c414c : bv 32 := 0x01871393.
Lemma F_c414c : fetch_word Plain.M.loaded_segments (0xc4304 : word) = Some W_c414c.
Proof. vm_refl. Qed.
Lemma D_c414c : decode_any W_c414c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4150 : bv 32 := 0x0063e333.
Lemma F_c4150 : fetch_word Plain.M.loaded_segments (0xc4308 : word) = Some W_c4150.
Proof. vm_refl. Qed.
Lemma D_c4150 : decode_any W_c4150 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4154 : bv 32 := 0xff060613.
Lemma F_c4154 : fetch_word Plain.M.loaded_segments (0xc430c : word) = Some W_c4154.
Proof. vm_refl. Qed.
Lemma D_c4154 : decode_any W_c4154 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4158 : bv 32 := 0x0106a023.
Lemma F_c4158 : fetch_word Plain.M.loaded_segments (0xc4310 : word) = Some W_c4158.
Proof. vm_refl. Qed.
Lemma D_c4158 : decode_any W_c4158 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c415c : bv 32 := 0x0116a223.
Lemma F_c415c : fetch_word Plain.M.loaded_segments (0xc4314 : word) = Some W_c415c.
Proof. vm_refl. Qed.
Lemma D_c415c : decode_any W_c415c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4160 : bv 32 := 0x0056a423.
Lemma F_c4160 : fetch_word Plain.M.loaded_segments (0xc4318 : word) = Some W_c4160.
Proof. vm_refl. Qed.
Lemma D_c4160 : decode_any W_c4160 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4164 : bv 32 := 0x0066a623.
Lemma F_c4164 : fetch_word Plain.M.loaded_segments (0xc431c : word) = Some W_c4164.
Proof. vm_refl. Qed.
Lemma D_c4164 : decode_any W_c4164 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4168 : bv 32 := 0x01068693.
Lemma F_c4168 : fetch_word Plain.M.loaded_segments (0xc4320 : word) = Some W_c4168.
Proof. vm_refl. Qed.
Lemma D_c4168 : decode_any W_c4168 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c416c : bv 32 := 0x01058593.
Lemma F_c416c : fetch_word Plain.M.loaded_segments (0xc4324 : word) = Some W_c416c.
Proof. vm_refl. Qed.
Lemma D_c416c : decode_any W_c416c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4170 : bv 32 := 0xfac7e2e3.
Lemma F_c4170 : fetch_word Plain.M.loaded_segments (0xc4328 : word) = Some W_c4170.
Proof. vm_refl. Qed.
Lemma D_c4170 : decode_any W_c4170 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4174 : bv 32 := 0xff158593.
Lemma F_c4174 : fetch_word Plain.M.loaded_segments (0xc432c : word) = Some W_c4174.
Proof. vm_refl. Qed.
Lemma D_c4174 : decode_any W_c4174 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4178 : bv 32 := 0x01000713.
Lemma F_c4178 : fetch_word Plain.M.loaded_segments (0xc4330 : word) = Some W_c4178.
Proof. vm_refl. Qed.
Lemma D_c4178 : decode_any W_c4178 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c417c : bv 32 := 0xe4e666e3.
Lemma F_c417c : fetch_word Plain.M.loaded_segments (0xc4334 : word) = Some W_c417c.
Proof. vm_refl. Qed.
Lemma D_c417c : decode_any W_c417c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4180 : bv 32 := 0x0940006f.
Lemma F_c4180 : fetch_word Plain.M.loaded_segments (0xc4338 : word) = Some W_c4180.
Proof. vm_refl. Qed.
Lemma D_c4180 : decode_any W_c4180 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4184 : bv 32 := 0x00875793.
Lemma F_c4184 : fetch_word Plain.M.loaded_segments (0xc433c : word) = Some W_c4184.
Proof. vm_refl. Qed.
Lemma D_c4184 : decode_any W_c4184 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4188 : bv 32 := 0x01075813.
Lemma F_c4188 : fetch_word Plain.M.loaded_segments (0xc4340 : word) = Some W_c4188.
Proof. vm_refl. Qed.
Lemma D_c4188 : decode_any W_c4188 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c418c : bv 32 := 0xffd60613.
Lemma F_c418c : fetch_word Plain.M.loaded_segments (0xc4344 : word) = Some W_c418c.
Proof. vm_refl. Qed.
Lemma D_c418c : decode_any W_c418c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4190 : bv 32 := 0x00e68023.
Lemma F_c4190 : fetch_word Plain.M.loaded_segments (0xc4348 : word) = Some W_c4190.
Proof. vm_refl. Qed.
Lemma D_c4190 : decode_any W_c4190 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4194 : bv 32 := 0x00f680a3.
Lemma F_c4194 : fetch_word Plain.M.loaded_segments (0xc434c : word) = Some W_c4194.
Proof. vm_refl. Qed.
Lemma D_c4194 : decode_any W_c4194 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4198 : bv 32 := 0x01068123.
Lemma F_c4198 : fetch_word Plain.M.loaded_segments (0xc4350 : word) = Some W_c4198.
Proof. vm_refl. Qed.
Lemma D_c4198 : decode_any W_c4198 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c419c : bv 32 := 0x00368693.
Lemma F_c419c : fetch_word Plain.M.loaded_segments (0xc4354 : word) = Some W_c419c.
Proof. vm_refl. Qed.
Lemma D_c419c : decode_any W_c419c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41a0 : bv 32 := 0x01058593.
Lemma F_c41a0 : fetch_word Plain.M.loaded_segments (0xc4358 : word) = Some W_c41a0.
Proof. vm_refl. Qed.
Lemma D_c41a0 : decode_any W_c41a0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41a4 : bv 32 := 0x01000793.
Lemma F_c41a4 : fetch_word Plain.M.loaded_segments (0xc435c : word) = Some W_c41a4.
Proof. vm_refl. Qed.
Lemma D_c41a4 : decode_any W_c41a4 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41a8 : bv 32 := 0x0187581b.
Lemma F_c41a8 : fetch_word Plain.M.loaded_segments (0xc4360 : word) = Some W_c41a8.
Proof. vm_refl. Qed.
Lemma D_c41a8 : decode_any W_c41a8 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41ac : bv 32 := 0xff45a883.
Lemma F_c41ac : fetch_word Plain.M.loaded_segments (0xc4364 : word) = Some W_c41ac.
Proof. vm_refl. Qed.
Lemma D_c41ac : decode_any W_c41ac = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41b0 : bv 32 := 0xff85a283.
Lemma F_c41b0 : fetch_word Plain.M.loaded_segments (0xc4368 : word) = Some W_c41b0.
Proof. vm_refl. Qed.
Lemma D_c41b0 : decode_any W_c41b0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41b4 : bv 32 := 0xffc5a303.
Lemma F_c41b4 : fetch_word Plain.M.loaded_segments (0xc436c : word) = Some W_c41b4.
Proof. vm_refl. Qed.
Lemma D_c41b4 : decode_any W_c41b4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41b8 : bv 32 := 0x0005a703.
Lemma F_c41b8 : fetch_word Plain.M.loaded_segments (0xc4370 : word) = Some W_c41b8.
Proof. vm_refl. Qed.
Lemma D_c41b8 : decode_any W_c41b8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41bc : bv 32 := 0x00889393.
Lemma F_c41bc : fetch_word Plain.M.loaded_segments (0xc4374 : word) = Some W_c41bc.
Proof. vm_refl. Qed.
Lemma D_c41bc : decode_any W_c41bc = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41c0 : bv 32 := 0x0188d89b.
Lemma F_c41c0 : fetch_word Plain.M.loaded_segments (0xc4378 : word) = Some W_c41c0.
Proof. vm_refl. Qed.
Lemma D_c41c0 : decode_any W_c41c0 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41c4 : bv 32 := 0x0103e833.
Lemma F_c41c4 : fetch_word Plain.M.loaded_segments (0xc437c : word) = Some W_c41c4.
Proof. vm_refl. Qed.
Lemma D_c41c4 : decode_any W_c41c4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41c8 : bv 32 := 0x00829393.
Lemma F_c41c8 : fetch_word Plain.M.loaded_segments (0xc4380 : word) = Some W_c41c8.
Proof. vm_refl. Qed.
Lemma D_c41c8 : decode_any W_c41c8 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41cc : bv 32 := 0x0182d29b.
Lemma F_c41cc : fetch_word Plain.M.loaded_segments (0xc4384 : word) = Some W_c41cc.
Proof. vm_refl. Qed.
Lemma D_c41cc : decode_any W_c41cc = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41d0 : bv 32 := 0x0113e8b3.
Lemma F_c41d0 : fetch_word Plain.M.loaded_segments (0xc4388 : word) = Some W_c41d0.
Proof. vm_refl. Qed.
Lemma D_c41d0 : decode_any W_c41d0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41d4 : bv 32 := 0x00831393.
Lemma F_c41d4 : fetch_word Plain.M.loaded_segments (0xc438c : word) = Some W_c41d4.
Proof. vm_refl. Qed.
Lemma D_c41d4 : decode_any W_c41d4 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41d8 : bv 32 := 0x0183531b.
Lemma F_c41d8 : fetch_word Plain.M.loaded_segments (0xc4390 : word) = Some W_c41d8.
Proof. vm_refl. Qed.
Lemma D_c41d8 : decode_any W_c41d8 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41dc : bv 32 := 0x0053e2b3.
Lemma F_c41dc : fetch_word Plain.M.loaded_segments (0xc4394 : word) = Some W_c41dc.
Proof. vm_refl. Qed.
Lemma D_c41dc : decode_any W_c41dc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41e0 : bv 32 := 0x00871393.
Lemma F_c41e0 : fetch_word Plain.M.loaded_segments (0xc4398 : word) = Some W_c41e0.
Proof. vm_refl. Qed.
Lemma D_c41e0 : decode_any W_c41e0 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41e4 : bv 32 := 0x0063e333.
Lemma F_c41e4 : fetch_word Plain.M.loaded_segments (0xc439c : word) = Some W_c41e4.
Proof. vm_refl. Qed.
Lemma D_c41e4 : decode_any W_c41e4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41e8 : bv 32 := 0xff060613.
Lemma F_c41e8 : fetch_word Plain.M.loaded_segments (0xc43a0 : word) = Some W_c41e8.
Proof. vm_refl. Qed.
Lemma D_c41e8 : decode_any W_c41e8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41ec : bv 32 := 0x0106a023.
Lemma F_c41ec : fetch_word Plain.M.loaded_segments (0xc43a4 : word) = Some W_c41ec.
Proof. vm_refl. Qed.
Lemma D_c41ec : decode_any W_c41ec = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41f0 : bv 32 := 0x0116a223.
Lemma F_c41f0 : fetch_word Plain.M.loaded_segments (0xc43a8 : word) = Some W_c41f0.
Proof. vm_refl. Qed.
Lemma D_c41f0 : decode_any W_c41f0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41f4 : bv 32 := 0x0056a423.
Lemma F_c41f4 : fetch_word Plain.M.loaded_segments (0xc43ac : word) = Some W_c41f4.
Proof. vm_refl. Qed.
Lemma D_c41f4 : decode_any W_c41f4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41f8 : bv 32 := 0x0066a623.
Lemma F_c41f8 : fetch_word Plain.M.loaded_segments (0xc43b0 : word) = Some W_c41f8.
Proof. vm_refl. Qed.
Lemma D_c41f8 : decode_any W_c41f8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c41fc : bv 32 := 0x01068693.
Lemma F_c41fc : fetch_word Plain.M.loaded_segments (0xc43b4 : word) = Some W_c41fc.
Proof. vm_refl. Qed.
Lemma D_c41fc : decode_any W_c41fc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4200 : bv 32 := 0x01058593.
Lemma F_c4200 : fetch_word Plain.M.loaded_segments (0xc43b8 : word) = Some W_c4200.
Proof. vm_refl. Qed.
Lemma D_c4200 : decode_any W_c4200 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4204 : bv 32 := 0xfac7e2e3.
Lemma F_c4204 : fetch_word Plain.M.loaded_segments (0xc43bc : word) = Some W_c4204.
Proof. vm_refl. Qed.
Lemma D_c4204 : decode_any W_c4204 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4208 : bv 32 := 0xff358593.
Lemma F_c4208 : fetch_word Plain.M.loaded_segments (0xc43c0 : word) = Some W_c4208.
Proof. vm_refl. Qed.
Lemma D_c4208 : decode_any W_c4208 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c420c : bv 32 := 0x01000713.
Lemma F_c420c : fetch_word Plain.M.loaded_segments (0xc43c4 : word) = Some W_c420c.
Proof. vm_refl. Qed.
Lemma D_c420c : decode_any W_c420c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4210 : bv 32 := 0xdae66ce3.
Lemma F_c4210 : fetch_word Plain.M.loaded_segments (0xc43c8 : word) = Some W_c4210.
Proof. vm_refl. Qed.
Lemma D_c4210 : decode_any W_c4210 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4214 : bv 32 := 0x0005c703.
Lemma F_c4214 : fetch_word Plain.M.loaded_segments (0xc43cc : word) = Some W_c4214.
Proof. vm_refl. Qed.
Lemma D_c4214 : decode_any W_c4214 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4218 : bv 32 := 0x0015c783.
Lemma F_c4218 : fetch_word Plain.M.loaded_segments (0xc43d0 : word) = Some W_c4218.
Proof. vm_refl. Qed.
Lemma D_c4218 : decode_any W_c4218 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c421c : bv 32 := 0x0025c803.
Lemma F_c421c : fetch_word Plain.M.loaded_segments (0xc43d4 : word) = Some W_c421c.
Proof. vm_refl. Qed.
Lemma D_c421c : decode_any W_c421c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4220 : bv 32 := 0x0035c883.
Lemma F_c4220 : fetch_word Plain.M.loaded_segments (0xc43d8 : word) = Some W_c4220.
Proof. vm_refl. Qed.
Lemma D_c4220 : decode_any W_c4220 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4224 : bv 32 := 0x0045c283.
Lemma F_c4224 : fetch_word Plain.M.loaded_segments (0xc43dc : word) = Some W_c4224.
Proof. vm_refl. Qed.
Lemma D_c4224 : decode_any W_c4224 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4228 : bv 32 := 0x0055c303.
Lemma F_c4228 : fetch_word Plain.M.loaded_segments (0xc43e0 : word) = Some W_c4228.
Proof. vm_refl. Qed.
Lemma D_c4228 : decode_any W_c4228 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c422c : bv 32 := 0x0065c383.
Lemma F_c422c : fetch_word Plain.M.loaded_segments (0xc43e4 : word) = Some W_c422c.
Proof. vm_refl. Qed.
Lemma D_c422c : decode_any W_c422c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4230 : bv 32 := 0x0075ce03.
Lemma F_c4230 : fetch_word Plain.M.loaded_segments (0xc43e8 : word) = Some W_c4230.
Proof. vm_refl. Qed.
Lemma D_c4230 : decode_any W_c4230 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4234 : bv 32 := 0x00e68023.
Lemma F_c4234 : fetch_word Plain.M.loaded_segments (0xc43ec : word) = Some W_c4234.
Proof. vm_refl. Qed.
Lemma D_c4234 : decode_any W_c4234 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4238 : bv 32 := 0x00f680a3.
Lemma F_c4238 : fetch_word Plain.M.loaded_segments (0xc43f0 : word) = Some W_c4238.
Proof. vm_refl. Qed.
Lemma D_c4238 : decode_any W_c4238 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c423c : bv 32 := 0x01068123.
Lemma F_c423c : fetch_word Plain.M.loaded_segments (0xc43f4 : word) = Some W_c423c.
Proof. vm_refl. Qed.
Lemma D_c423c : decode_any W_c423c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4240 : bv 32 := 0x011681a3.
Lemma F_c4240 : fetch_word Plain.M.loaded_segments (0xc43f8 : word) = Some W_c4240.
Proof. vm_refl. Qed.
Lemma D_c4240 : decode_any W_c4240 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4244 : bv 32 := 0x0085c703.
Lemma F_c4244 : fetch_word Plain.M.loaded_segments (0xc43fc : word) = Some W_c4244.
Proof. vm_refl. Qed.
Lemma D_c4244 : decode_any W_c4244 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4248 : bv 32 := 0x0095c783.
Lemma F_c4248 : fetch_word Plain.M.loaded_segments (0xc4400 : word) = Some W_c4248.
Proof. vm_refl. Qed.
Lemma D_c4248 : decode_any W_c4248 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c424c : bv 32 := 0x00a5c803.
Lemma F_c424c : fetch_word Plain.M.loaded_segments (0xc4404 : word) = Some W_c424c.
Proof. vm_refl. Qed.
Lemma D_c424c : decode_any W_c424c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4250 : bv 32 := 0x00b5c883.
Lemma F_c4250 : fetch_word Plain.M.loaded_segments (0xc4408 : word) = Some W_c4250.
Proof. vm_refl. Qed.
Lemma D_c4250 : decode_any W_c4250 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4254 : bv 32 := 0x00568223.
Lemma F_c4254 : fetch_word Plain.M.loaded_segments (0xc440c : word) = Some W_c4254.
Proof. vm_refl. Qed.
Lemma D_c4254 : decode_any W_c4254 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4258 : bv 32 := 0x006682a3.
Lemma F_c4258 : fetch_word Plain.M.loaded_segments (0xc4410 : word) = Some W_c4258.
Proof. vm_refl. Qed.
Lemma D_c4258 : decode_any W_c4258 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c425c : bv 32 := 0x00768323.
Lemma F_c425c : fetch_word Plain.M.loaded_segments (0xc4414 : word) = Some W_c425c.
Proof. vm_refl. Qed.
Lemma D_c425c : decode_any W_c425c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4260 : bv 32 := 0x01c683a3.
Lemma F_c4260 : fetch_word Plain.M.loaded_segments (0xc4418 : word) = Some W_c4260.
Proof. vm_refl. Qed.
Lemma D_c4260 : decode_any W_c4260 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4264 : bv 32 := 0x00c5c283.
Lemma F_c4264 : fetch_word Plain.M.loaded_segments (0xc441c : word) = Some W_c4264.
Proof. vm_refl. Qed.
Lemma D_c4264 : decode_any W_c4264 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4268 : bv 32 := 0x00d5c303.
Lemma F_c4268 : fetch_word Plain.M.loaded_segments (0xc4420 : word) = Some W_c4268.
Proof. vm_refl. Qed.
Lemma D_c4268 : decode_any W_c4268 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c426c : bv 32 := 0x00e5c383.
Lemma F_c426c : fetch_word Plain.M.loaded_segments (0xc4424 : word) = Some W_c426c.
Proof. vm_refl. Qed.
Lemma D_c426c : decode_any W_c426c = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4270 : bv 32 := 0x00f5ce03.
Lemma F_c4270 : fetch_word Plain.M.loaded_segments (0xc4428 : word) = Some W_c4270.
Proof. vm_refl. Qed.
Lemma D_c4270 : decode_any W_c4270 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4274 : bv 32 := 0x01058593.
Lemma F_c4274 : fetch_word Plain.M.loaded_segments (0xc442c : word) = Some W_c4274.
Proof. vm_refl. Qed.
Lemma D_c4274 : decode_any W_c4274 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4278 : bv 32 := 0x00e68423.
Lemma F_c4278 : fetch_word Plain.M.loaded_segments (0xc4430 : word) = Some W_c4278.
Proof. vm_refl. Qed.
Lemma D_c4278 : decode_any W_c4278 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c427c : bv 32 := 0x00f684a3.
Lemma F_c427c : fetch_word Plain.M.loaded_segments (0xc4434 : word) = Some W_c427c.
Proof. vm_refl. Qed.
Lemma D_c427c : decode_any W_c427c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4280 : bv 32 := 0x01068523.
Lemma F_c4280 : fetch_word Plain.M.loaded_segments (0xc4438 : word) = Some W_c4280.
Proof. vm_refl. Qed.
Lemma D_c4280 : decode_any W_c4280 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4284 : bv 32 := 0x011685a3.
Lemma F_c4284 : fetch_word Plain.M.loaded_segments (0xc443c : word) = Some W_c4284.
Proof. vm_refl. Qed.
Lemma D_c4284 : decode_any W_c4284 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4288 : bv 32 := 0x01068713.
Lemma F_c4288 : fetch_word Plain.M.loaded_segments (0xc4440 : word) = Some W_c4288.
Proof. vm_refl. Qed.
Lemma D_c4288 : decode_any W_c4288 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c428c : bv 32 := 0x00568623.
Lemma F_c428c : fetch_word Plain.M.loaded_segments (0xc4444 : word) = Some W_c428c.
Proof. vm_refl. Qed.
Lemma D_c428c : decode_any W_c428c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4290 : bv 32 := 0x006686a3.
Lemma F_c4290 : fetch_word Plain.M.loaded_segments (0xc4448 : word) = Some W_c4290.
Proof. vm_refl. Qed.
Lemma D_c4290 : decode_any W_c4290 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4294 : bv 32 := 0x00768723.
Lemma F_c4294 : fetch_word Plain.M.loaded_segments (0xc444c : word) = Some W_c4294.
Proof. vm_refl. Qed.
Lemma D_c4294 : decode_any W_c4294 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4298 : bv 32 := 0x01c687a3.
Lemma F_c4298 : fetch_word Plain.M.loaded_segments (0xc4450 : word) = Some W_c4298.
Proof. vm_refl. Qed.
Lemma D_c4298 : decode_any W_c4298 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c429c : bv 32 := 0x00070693.
Lemma F_c429c : fetch_word Plain.M.loaded_segments (0xc4454 : word) = Some W_c429c.
Proof. vm_refl. Qed.
Lemma D_c429c : decode_any W_c429c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42a0 : bv 32 := 0x00867713.
Lemma F_c42a0 : fetch_word Plain.M.loaded_segments (0xc4458 : word) = Some W_c42a0.
Proof. vm_refl. Qed.
Lemma D_c42a0 : decode_any W_c42a0 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42a4 : bv 32 := 0xd20706e3.
Lemma F_c42a4 : fetch_word Plain.M.loaded_segments (0xc445c : word) = Some W_c42a4.
Proof. vm_refl. Qed.
Lemma D_c42a4 : decode_any W_c42a4 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42a8 : bv 32 := 0x0005c703.
Lemma F_c42a8 : fetch_word Plain.M.loaded_segments (0xc4460 : word) = Some W_c42a8.
Proof. vm_refl. Qed.
Lemma D_c42a8 : decode_any W_c42a8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42ac : bv 32 := 0x0015c783.
Lemma F_c42ac : fetch_word Plain.M.loaded_segments (0xc4464 : word) = Some W_c42ac.
Proof. vm_refl. Qed.
Lemma D_c42ac : decode_any W_c42ac = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42b0 : bv 32 := 0x0025c803.
Lemma F_c42b0 : fetch_word Plain.M.loaded_segments (0xc4468 : word) = Some W_c42b0.
Proof. vm_refl. Qed.
Lemma D_c42b0 : decode_any W_c42b0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42b4 : bv 32 := 0x0035c883.
Lemma F_c42b4 : fetch_word Plain.M.loaded_segments (0xc446c : word) = Some W_c42b4.
Proof. vm_refl. Qed.
Lemma D_c42b4 : decode_any W_c42b4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42b8 : bv 32 := 0x0045c283.
Lemma F_c42b8 : fetch_word Plain.M.loaded_segments (0xc4470 : word) = Some W_c42b8.
Proof. vm_refl. Qed.
Lemma D_c42b8 : decode_any W_c42b8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42bc : bv 32 := 0x0055c303.
Lemma F_c42bc : fetch_word Plain.M.loaded_segments (0xc4474 : word) = Some W_c42bc.
Proof. vm_refl. Qed.
Lemma D_c42bc : decode_any W_c42bc = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42c0 : bv 32 := 0x0065c383.
Lemma F_c42c0 : fetch_word Plain.M.loaded_segments (0xc4478 : word) = Some W_c42c0.
Proof. vm_refl. Qed.
Lemma D_c42c0 : decode_any W_c42c0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42c4 : bv 32 := 0x0075ce03.
Lemma F_c42c4 : fetch_word Plain.M.loaded_segments (0xc447c : word) = Some W_c42c4.
Proof. vm_refl. Qed.
Lemma D_c42c4 : decode_any W_c42c4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42c8 : bv 32 := 0x00858593.
Lemma F_c42c8 : fetch_word Plain.M.loaded_segments (0xc4480 : word) = Some W_c42c8.
Proof. vm_refl. Qed.
Lemma D_c42c8 : decode_any W_c42c8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42cc : bv 32 := 0x00e68023.
Lemma F_c42cc : fetch_word Plain.M.loaded_segments (0xc4484 : word) = Some W_c42cc.
Proof. vm_refl. Qed.
Lemma D_c42cc : decode_any W_c42cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42d0 : bv 32 := 0x00f680a3.
Lemma F_c42d0 : fetch_word Plain.M.loaded_segments (0xc4488 : word) = Some W_c42d0.
Proof. vm_refl. Qed.
Lemma D_c42d0 : decode_any W_c42d0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42d4 : bv 32 := 0x01068123.
Lemma F_c42d4 : fetch_word Plain.M.loaded_segments (0xc448c : word) = Some W_c42d4.
Proof. vm_refl. Qed.
Lemma D_c42d4 : decode_any W_c42d4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42d8 : bv 32 := 0x011681a3.
Lemma F_c42d8 : fetch_word Plain.M.loaded_segments (0xc4490 : word) = Some W_c42d8.
Proof. vm_refl. Qed.
Lemma D_c42d8 : decode_any W_c42d8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42dc : bv 32 := 0x00868713.
Lemma F_c42dc : fetch_word Plain.M.loaded_segments (0xc4494 : word) = Some W_c42dc.
Proof. vm_refl. Qed.
Lemma D_c42dc : decode_any W_c42dc = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42e0 : bv 32 := 0x00568223.
Lemma F_c42e0 : fetch_word Plain.M.loaded_segments (0xc4498 : word) = Some W_c42e0.
Proof. vm_refl. Qed.
Lemma D_c42e0 : decode_any W_c42e0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42e4 : bv 32 := 0x006682a3.
Lemma F_c42e4 : fetch_word Plain.M.loaded_segments (0xc449c : word) = Some W_c42e4.
Proof. vm_refl. Qed.
Lemma D_c42e4 : decode_any W_c42e4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42e8 : bv 32 := 0x00768323.
Lemma F_c42e8 : fetch_word Plain.M.loaded_segments (0xc44a0 : word) = Some W_c42e8.
Proof. vm_refl. Qed.
Lemma D_c42e8 : decode_any W_c42e8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42ec : bv 32 := 0x01c683a3.
Lemma F_c42ec : fetch_word Plain.M.loaded_segments (0xc44a4 : word) = Some W_c42ec.
Proof. vm_refl. Qed.
Lemma D_c42ec : decode_any W_c42ec = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42f0 : bv 32 := 0x00070693.
Lemma F_c42f0 : fetch_word Plain.M.loaded_segments (0xc44a8 : word) = Some W_c42f0.
Proof. vm_refl. Qed.
Lemma D_c42f0 : decode_any W_c42f0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42f4 : bv 32 := 0x00467713.
Lemma F_c42f4 : fetch_word Plain.M.loaded_segments (0xc44ac : word) = Some W_c42f4.
Proof. vm_refl. Qed.
Lemma D_c42f4 : decode_any W_c42f4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42f8 : bv 32 := 0x02070863.
Lemma F_c42f8 : fetch_word Plain.M.loaded_segments (0xc44b0 : word) = Some W_c42f8.
Proof. vm_refl. Qed.
Lemma D_c42f8 : decode_any W_c42f8 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c42fc : bv 32 := 0x0005c703.
Lemma F_c42fc : fetch_word Plain.M.loaded_segments (0xc44b4 : word) = Some W_c42fc.
Proof. vm_refl. Qed.
Lemma D_c42fc : decode_any W_c42fc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4300 : bv 32 := 0x0015c783.
Lemma F_c4300 : fetch_word Plain.M.loaded_segments (0xc44b8 : word) = Some W_c4300.
Proof. vm_refl. Qed.
Lemma D_c4300 : decode_any W_c4300 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4304 : bv 32 := 0x0025c803.
Lemma F_c4304 : fetch_word Plain.M.loaded_segments (0xc44bc : word) = Some W_c4304.
Proof. vm_refl. Qed.
Lemma D_c4304 : decode_any W_c4304 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4308 : bv 32 := 0x0035c883.
Lemma F_c4308 : fetch_word Plain.M.loaded_segments (0xc44c0 : word) = Some W_c4308.
Proof. vm_refl. Qed.
Lemma D_c4308 : decode_any W_c4308 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c430c : bv 32 := 0x00458593.
Lemma F_c430c : fetch_word Plain.M.loaded_segments (0xc44c4 : word) = Some W_c430c.
Proof. vm_refl. Qed.
Lemma D_c430c : decode_any W_c430c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4310 : bv 32 := 0x00468293.
Lemma F_c4310 : fetch_word Plain.M.loaded_segments (0xc44c8 : word) = Some W_c4310.
Proof. vm_refl. Qed.
Lemma D_c4310 : decode_any W_c4310 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4314 : bv 32 := 0x00e68023.
Lemma F_c4314 : fetch_word Plain.M.loaded_segments (0xc44cc : word) = Some W_c4314.
Proof. vm_refl. Qed.
Lemma D_c4314 : decode_any W_c4314 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4318 : bv 32 := 0x00f680a3.
Lemma F_c4318 : fetch_word Plain.M.loaded_segments (0xc44d0 : word) = Some W_c4318.
Proof. vm_refl. Qed.
Lemma D_c4318 : decode_any W_c4318 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c431c : bv 32 := 0x01068123.
Lemma F_c431c : fetch_word Plain.M.loaded_segments (0xc44d4 : word) = Some W_c431c.
Proof. vm_refl. Qed.
Lemma D_c431c : decode_any W_c431c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4320 : bv 32 := 0x011681a3.
Lemma F_c4320 : fetch_word Plain.M.loaded_segments (0xc44d8 : word) = Some W_c4320.
Proof. vm_refl. Qed.
Lemma D_c4320 : decode_any W_c4320 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4324 : bv 32 := 0x00028693.
Lemma F_c4324 : fetch_word Plain.M.loaded_segments (0xc44dc : word) = Some W_c4324.
Proof. vm_refl. Qed.
Lemma D_c4324 : decode_any W_c4324 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4328 : bv 32 := 0x00267713.
Lemma F_c4328 : fetch_word Plain.M.loaded_segments (0xc44e0 : word) = Some W_c4328.
Proof. vm_refl. Qed.
Lemma D_c4328 : decode_any W_c4328 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c432c : bv 32 := 0x00071863.
Lemma F_c432c : fetch_word Plain.M.loaded_segments (0xc44e4 : word) = Some W_c432c.
Proof. vm_refl. Qed.
Lemma D_c432c : decode_any W_c432c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4330 : bv 32 := 0x00167613.
Lemma F_c4330 : fetch_word Plain.M.loaded_segments (0xc44e8 : word) = Some W_c4330.
Proof. vm_refl. Qed.
Lemma D_c4330 : decode_any W_c4330 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4334 : bv 32 := 0x02061663.
Lemma F_c4334 : fetch_word Plain.M.loaded_segments (0xc44ec : word) = Some W_c4334.
Proof. vm_refl. Qed.
Lemma D_c4334 : decode_any W_c4334 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4338 : bv 32 := 0x00008067.
Lemma F_c4338 : fetch_word Plain.M.loaded_segments (0xc44f0 : word) = Some W_c4338.
Proof. vm_refl. Qed.
Lemma D_c4338 : decode_any W_c4338 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c433c : bv 32 := 0x0005c703.
Lemma F_c433c : fetch_word Plain.M.loaded_segments (0xc44f4 : word) = Some W_c433c.
Proof. vm_refl. Qed.
Lemma D_c433c : decode_any W_c433c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4340 : bv 32 := 0x0015c783.
Lemma F_c4340 : fetch_word Plain.M.loaded_segments (0xc44f8 : word) = Some W_c4340.
Proof. vm_refl. Qed.
Lemma D_c4340 : decode_any W_c4340 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4344 : bv 32 := 0x00258593.
Lemma F_c4344 : fetch_word Plain.M.loaded_segments (0xc44fc : word) = Some W_c4344.
Proof. vm_refl. Qed.
Lemma D_c4344 : decode_any W_c4344 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4348 : bv 32 := 0x00268813.
Lemma F_c4348 : fetch_word Plain.M.loaded_segments (0xc4500 : word) = Some W_c4348.
Proof. vm_refl. Qed.
Lemma D_c4348 : decode_any W_c4348 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c434c : bv 32 := 0x00e68023.
Lemma F_c434c : fetch_word Plain.M.loaded_segments (0xc4504 : word) = Some W_c434c.
Proof. vm_refl. Qed.
Lemma D_c434c : decode_any W_c434c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4350 : bv 32 := 0x00f680a3.
Lemma F_c4350 : fetch_word Plain.M.loaded_segments (0xc4508 : word) = Some W_c4350.
Proof. vm_refl. Qed.
Lemma D_c4350 : decode_any W_c4350 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4354 : bv 32 := 0x00080693.
Lemma F_c4354 : fetch_word Plain.M.loaded_segments (0xc450c : word) = Some W_c4354.
Proof. vm_refl. Qed.
Lemma D_c4354 : decode_any W_c4354 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4358 : bv 32 := 0x00167613.
Lemma F_c4358 : fetch_word Plain.M.loaded_segments (0xc4510 : word) = Some W_c4358.
Proof. vm_refl. Qed.
Lemma D_c4358 : decode_any W_c4358 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c435c : bv 32 := 0xfc060ee3.
Lemma F_c435c : fetch_word Plain.M.loaded_segments (0xc4514 : word) = Some W_c435c.
Proof. vm_refl. Qed.
Lemma D_c435c : decode_any W_c435c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4360 : bv 32 := 0x0005c583.
Lemma F_c4360 : fetch_word Plain.M.loaded_segments (0xc4518 : word) = Some W_c4360.
Proof. vm_refl. Qed.
Lemma D_c4360 : decode_any W_c4360 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4364 : bv 32 := 0x00b68023.
Lemma F_c4364 : fetch_word Plain.M.loaded_segments (0xc451c : word) = Some W_c4364.
Proof. vm_refl. Qed.
Lemma D_c4364 : decode_any W_c4364 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4368 : bv 32 := 0x00008067.
Lemma F_c4368 : fetch_word Plain.M.loaded_segments (0xc4520 : word) = Some W_c4368.
Proof. vm_refl. Qed.
Lemma D_c4368 : decode_any W_c4368 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c436c : bv 32 := 0x08b50663.
Lemma F_c436c : fetch_word Plain.M.loaded_segments (0xc4524 : word) = Some W_c436c.
Proof. vm_refl. Qed.
Lemma D_c436c : decode_any W_c436c = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.
