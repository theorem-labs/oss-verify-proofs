(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_11350 : bv 32 := 0xfffff197.
Lemma D_11350 : decode_any W_11350 = Some (Auipc 3 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11354 : bv 32 := 0x4b018193.
Lemma D_11354 : decode_any W_11354 = Some (OpImm ALU_ADD 3 3 1200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11358 : bv 32 := 0x00010513.
Lemma D_11358 : decode_any W_11358 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135c : bv 32 := 0xfffef597.
Lemma D_1135c : decode_any W_1135c = Some (Auipc 11 1048559, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11360 : bv 32 := 0xca458593.
Lemma D_11360 : decode_any W_11360 = Some (OpImm ALU_ADD 11 11 3236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11364 : bv 32 := 0xff017113.
Lemma D_11364 : decode_any W_11364 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11368 : bv 32 := 0x0040006f.
Lemma D_11368 : decode_any W_11368 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1136c : bv 32 := 0x00052583.
Lemma D_1136c : decode_any W_1136c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11370 : bv 32 := 0x00002617.
Lemma D_11370 : decode_any W_11370 = Some (Auipc 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11374 : bv 32 := 0x00002697.
Lemma D_11374 : decode_any W_11374 = Some (Auipc 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11378 : bv 32 := 0x00002717.
Lemma D_11378 : decode_any W_11378 = Some (Auipc 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1137c : bv 32 := 0xd2863783.
Lemma D_1137c : decode_any W_1137c = Some (Load SZ8 true 15 12 3368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11380 : bv 32 := 0xd2c6b683.
Lemma D_11380 : decode_any W_11380 = Some (Load SZ8 true 13 13 3372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11384 : bv 32 := 0xd3073703.
Lemma D_11384 : decode_any W_11384 = Some (Load SZ8 true 14 14 3376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11388 : bv 32 := 0x00850613.
Lemma D_11388 : decode_any W_11388 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1138c : bv 32 := 0x00078513.
Lemma D_1138c : decode_any W_1138c = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11390 : bv 32 := 0x00000793.
Lemma D_11390 : decode_any W_11390 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11394 : bv 32 := 0x3980006f.
Lemma D_11394 : decode_any W_11394 = Some (Jal 0 920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11398 : bv 32 := 0xff010113.
Lemma D_11398 : decode_any W_11398 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139c : bv 32 := 0x00113423.
Lemma D_1139c : decode_any W_1139c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a0 : bv 32 := 0x00813023.
Lemma D_113a0 : decode_any W_113a0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a4 : bv 32 := 0x01010413.
Lemma D_113a4 : decode_any W_113a4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a8 : bv 32 := 0x00003517.
Lemma D_113a8 : decode_any W_113a8 = Some (Auipc 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ac : bv 32 := 0xd6850513.
Lemma D_113ac : decode_any W_113ac = Some (OpImm ALU_ADD 10 10 3432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113b0 : bv 32 := 0x00054503.
Lemma D_113b0 : decode_any W_113b0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113b4 : bv 32 := 0x00157513.
Lemma D_113b4 : decode_any W_113b4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113b8 : bv 32 := 0x00050663.
Lemma D_113b8 : decode_any W_113b8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113c4 : bv 32 := 0x00003517.
Lemma D_113c4 : decode_any W_113c4 = Some (Auipc 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113c8 : bv 32 := 0xd4c50593.
Lemma D_113c8 : decode_any W_113c8 = Some (OpImm ALU_ADD 11 10 3404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113cc : bv 32 := 0x00100513.
Lemma D_113cc : decode_any W_113cc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113d0 : bv 32 := 0x00a58023.
Lemma D_113d0 : decode_any W_113d0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113d4 : bv 32 := 0x00002517.
Lemma D_113d4 : decode_any W_113d4 = Some (Auipc 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113d8 : bv 32 := 0xcdc53503.
Lemma D_113d8 : decode_any W_113d8 = Some (Load SZ8 true 10 10 3292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113dc : bv 32 := 0x02050063.
Lemma D_113dc : decode_any W_113dc = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113fc : bv 32 := 0x00813083.
Lemma D_113fc : decode_any W_113fc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11400 : bv 32 := 0x00013403.
Lemma D_11400 : decode_any W_11400 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11404 : bv 32 := 0x01010113.
Lemma D_11404 : decode_any W_11404 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11408 : bv 32 := 0x00008067.
Lemma D_11408 : decode_any W_11408 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1149c : bv 32 := 0xff010113.
Lemma D_1149c : decode_any W_1149c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114a0 : bv 32 := 0x00113423.
Lemma D_114a0 : decode_any W_114a0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114a4 : bv 32 := 0x00000513.
Lemma D_114a4 : decode_any W_114a4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114a8 : bv 32 := 0x5e8000ef.
Lemma D_114a8 : decode_any W_114a8 = Some (Jal 1 1512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114ac : bv 32 := 0x00008067.
Lemma D_114ac : decode_any W_114ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114b0 : bv 32 := 0x00008067.
Lemma D_114b0 : decode_any W_114b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114b4 : bv 32 := 0xe8010113.
Lemma D_114b4 : decode_any W_114b4 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114b8 : bv 32 := 0x16113c23.
Lemma D_114b8 : decode_any W_114b8 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114bc : bv 32 := 0x16813823.
Lemma D_114bc : decode_any W_114bc = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114c0 : bv 32 := 0x16913423.
Lemma D_114c0 : decode_any W_114c0 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114c4 : bv 32 := 0x17213023.
Lemma D_114c4 : decode_any W_114c4 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114c8 : bv 32 := 0x00058413.
Lemma D_114c8 : decode_any W_114c8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114cc : bv 32 := 0x00050493.
Lemma D_114cc : decode_any W_114cc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114d0 : bv 32 := 0x03010513.
Lemma D_114d0 : decode_any W_114d0 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114d4 : bv 32 := 0x13000613.
Lemma D_114d4 : decode_any W_114d4 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114d8 : bv 32 := 0x00000593.
Lemma D_114d8 : decode_any W_114d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114dc : bv 32 := 0x299000ef.
Lemma D_114dc : decode_any W_114dc = Some (Jal 1 2712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114e0 : bv 32 := 0x00002517.
Lemma D_114e0 : decode_any W_114e0 = Some (Auipc 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114e4 : bv 32 := 0xbe853503.
Lemma D_114e4 : decode_any W_114e4 = Some (Load SZ8 true 10 10 3048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114e8 : bv 32 := 0x00953023.
Lemma D_114e8 : decode_any W_114e8 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114ec : bv 32 := 0x0004b503.
Lemma D_114ec : decode_any W_114ec = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114f0 : bv 32 := 0x00848493.
Lemma D_114f0 : decode_any W_114f0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114f4 : bv 32 := 0xfe051ce3.
Lemma D_114f4 : decode_any W_114f4 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114f8 : bv 32 := 0x00003517.
Lemma D_114f8 : decode_any W_114f8 = Some (Auipc 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_114fc : bv 32 := 0xe1850913.
Lemma D_114fc : decode_any W_114fc = Some (OpImm ALU_ADD 18 10 3608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11500 : bv 32 := 0x00993423.
Lemma D_11500 : decode_any W_11500 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11504 : bv 32 := 0x0004b583.
Lemma D_11504 : decode_any W_11504 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11508 : bv 32 := 0x04058c63.
Lemma D_11508 : decode_any W_11508 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1150c : bv 32 := 0x01048493.
Lemma D_1150c : decode_any W_1150c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11510 : bv 32 := 0x02500513.
Lemma D_11510 : decode_any W_11510 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11514 : bv 32 := 0x03010613.
Lemma D_11514 : decode_any W_11514 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11518 : bv 32 := 0x0100006f.
Lemma D_11518 : decode_any W_11518 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1151c : bv 32 := 0x0004b583.
Lemma D_1151c : decode_any W_1151c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11520 : bv 32 := 0x01048493.
Lemma D_11520 : decode_any W_11520 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11524 : bv 32 := 0x00058e63.
Lemma D_11524 : decode_any W_11524 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11528 : bv 32 := 0xfeb56ae3.
Lemma D_11528 : decode_any W_11528 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1152c : bv 32 := 0xff84b683.
Lemma D_1152c : decode_any W_1152c = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11530 : bv 32 := 0x00359593.
Lemma D_11530 : decode_any W_11530 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11534 : bv 32 := 0x00b605b3.
Lemma D_11534 : decode_any W_11534 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11538 : bv 32 := 0x00d5b023.
Lemma D_11538 : decode_any W_11538 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1153c : bv 32 := 0xfe1ff06f.
Lemma D_1153c : decode_any W_1153c = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11540 : bv 32 := 0x0b013583.
Lemma D_11540 : decode_any W_11540 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11544 : bv 32 := 0x13013503.
Lemma D_11544 : decode_any W_11544 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11548 : bv 32 := 0x00003617.
Lemma D_11548 : decode_any W_11548 = Some (Auipc 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1154c : bv 32 := 0xe2b63823.
Lemma D_1154c : decode_any W_1154c = Some (Store SZ8 12 11 3632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11550 : bv 32 := 0x00050c63.
Lemma D_11550 : decode_any W_11550 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11568 : bv 32 := 0x06013503.
Lemma D_11568 : decode_any W_11568 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1156c : bv 32 := 0x02a93823.
Lemma D_1156c : decode_any W_1156c = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11570 : bv 32 := 0x00041463.
Lemma D_11570 : decode_any W_11570 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11578 : bv 32 := 0x00041663.
Lemma D_11578 : decode_any W_11578 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11584 : bv 32 := 0x00002517.
Lemma D_11584 : decode_any W_11584 = Some (Auipc 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11588 : bv 32 := 0xb4c53583.
Lemma D_11588 : decode_any W_11588 = Some (Load SZ8 true 11 10 2892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1158c : bv 32 := 0x00002517.
Lemma D_1158c : decode_any W_1158c = Some (Auipc 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11590 : bv 32 := 0xb4c53503.
Lemma D_11590 : decode_any W_11590 = Some (Load SZ8 true 10 10 2892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11594 : bv 32 := 0x0085b023.
Lemma D_11594 : decode_any W_11594 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11598 : bv 32 := 0x00140593.
Lemma D_11598 : decode_any W_11598 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1159c : bv 32 := 0x00853023.
Lemma D_1159c : decode_any W_1159c = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115a0 : bv 32 := 0x02f00613.
Lemma D_115a0 : decode_any W_115a0 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115a4 : bv 32 := 0x00c0006f.
Lemma D_115a4 : decode_any W_115a4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115a8 : bv 32 := 0x00b53023.
Lemma D_115a8 : decode_any W_115a8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115ac : bv 32 := 0x00158593.
Lemma D_115ac : decode_any W_115ac = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115b0 : bv 32 := 0xfff5c683.
Lemma D_115b0 : decode_any W_115b0 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115b4 : bv 32 := 0xfec68ae3.
Lemma D_115b4 : decode_any W_115b4 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115b8 : bv 32 := 0xfe069ae3.
Lemma D_115b8 : decode_any W_115b8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115bc : bv 32 := 0x03010513.
Lemma D_115bc : decode_any W_115bc = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115c0 : bv 32 := 0x214000ef.
Lemma D_115c0 : decode_any W_115c0 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115c4 : bv 32 := 0x0f813503.
Lemma D_115c4 : decode_any W_115c4 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115c8 : bv 32 := 0xee9ff0ef.
Lemma D_115c8 : decode_any W_115c8 = Some (Jal 1 2096872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115cc : bv 32 := 0x08813503.
Lemma D_115cc : decode_any W_115cc = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115d0 : bv 32 := 0x09013583.
Lemma D_115d0 : decode_any W_115d0 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115d4 : bv 32 := 0x00b51c63.
Lemma D_115d4 : decode_any W_115d4 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115d8 : bv 32 := 0x09813503.
Lemma D_115d8 : decode_any W_115d8 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115dc : bv 32 := 0x0a013583.
Lemma D_115dc : decode_any W_115dc = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115e0 : bv 32 := 0x00b51663.
Lemma D_115e0 : decode_any W_115e0 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115e4 : bv 32 := 0x0e813503.
Lemma D_115e4 : decode_any W_115e4 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115e8 : bv 32 := 0x0e050063.
Lemma D_115e8 : decode_any W_115e8 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116c8 : bv 32 := 0x17813083.
Lemma D_116c8 : decode_any W_116c8 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116cc : bv 32 := 0x17013403.
Lemma D_116cc : decode_any W_116cc = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116d0 : bv 32 := 0x16813483.
Lemma D_116d0 : decode_any W_116d0 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116d4 : bv 32 := 0x16013903.
Lemma D_116d4 : decode_any W_116d4 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116d8 : bv 32 := 0x18010113.
Lemma D_116d8 : decode_any W_116d8 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116dc : bv 32 := 0x00008067.
Lemma D_116dc : decode_any W_116dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116e0 : bv 32 := 0xfe010113.
Lemma D_116e0 : decode_any W_116e0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116e4 : bv 32 := 0x00113c23.
Lemma D_116e4 : decode_any W_116e4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116e8 : bv 32 := 0x00813823.
Lemma D_116e8 : decode_any W_116e8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116ec : bv 32 := 0x00913423.
Lemma D_116ec : decode_any W_116ec = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116f0 : bv 32 := 0xdbdff0ef.
Lemma D_116f0 : decode_any W_116f0 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116f4 : bv 32 := 0x00002517.
Lemma D_116f4 : decode_any W_116f4 = Some (Auipc 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116f8 : bv 32 := 0x00002597.
Lemma D_116f8 : decode_any W_116f8 = Some (Auipc 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116fc : bv 32 := 0x9ec53403.
Lemma D_116fc : decode_any W_116fc = Some (Load SZ8 true 8 10 2540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11700 : bv 32 := 0x9f05b483.
Lemma D_11700 : decode_any W_11700 = Some (Load SZ8 true 9 11 2544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11704 : bv 32 := 0x0084fa63.
Lemma D_11704 : decode_any W_11704 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11708 : bv 32 := 0x0004b503.
Lemma D_11708 : decode_any W_11708 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1170c : bv 32 := 0x000500e7.
Lemma D_1170c : decode_any W_1170c = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11710 : bv 32 := 0x00848493.
Lemma D_11710 : decode_any W_11710 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11714 : bv 32 := 0xfe84eae3.
Lemma D_11714 : decode_any W_11714 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11718 : bv 32 := 0x01813083.
Lemma D_11718 : decode_any W_11718 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1171c : bv 32 := 0x01013403.
Lemma D_1171c : decode_any W_1171c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11720 : bv 32 := 0x00813483.
Lemma D_11720 : decode_any W_11720 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11724 : bv 32 := 0x02010113.
Lemma D_11724 : decode_any W_11724 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11728 : bv 32 := 0x00008067.
Lemma D_11728 : decode_any W_11728 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1172c : bv 32 := 0xfe010113.
Lemma D_1172c : decode_any W_1172c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11730 : bv 32 := 0x00113c23.
Lemma D_11730 : decode_any W_11730 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11734 : bv 32 := 0x00813823.
Lemma D_11734 : decode_any W_11734 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11738 : bv 32 := 0x00913423.
Lemma D_11738 : decode_any W_11738 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1173c : bv 32 := 0x01213023.
Lemma D_1173c : decode_any W_1173c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11740 : bv 32 := 0x00060413.
Lemma D_11740 : decode_any W_11740 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11744 : bv 32 := 0x00058493.
Lemma D_11744 : decode_any W_11744 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11748 : bv 32 := 0x00050913.
Lemma D_11748 : decode_any W_11748 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1174c : bv 32 := 0x00063583.
Lemma D_1174c : decode_any W_1174c = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11750 : bv 32 := 0x00349513.
Lemma D_11750 : decode_any W_11750 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11754 : bv 32 := 0x00a60533.
Lemma D_11754 : decode_any W_11754 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11758 : bv 32 := 0x00850513.
Lemma D_11758 : decode_any W_11758 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1175c : bv 32 := 0xd59ff0ef.
Lemma D_1175c : decode_any W_1175c = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11760 : bv 32 := 0x00000517.
Lemma D_11760 : decode_any W_11760 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11764 : bv 32 := 0x02c50313.
Lemma D_11764 : decode_any W_11764 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11768 : bv 32 := 0x00090513.
Lemma D_11768 : decode_any W_11768 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1176c : bv 32 := 0x00048593.
Lemma D_1176c : decode_any W_1176c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11770 : bv 32 := 0x00040613.
Lemma D_11770 : decode_any W_11770 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11774 : bv 32 := 0x01813083.
Lemma D_11774 : decode_any W_11774 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11778 : bv 32 := 0x01013403.
Lemma D_11778 : decode_any W_11778 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1177c : bv 32 := 0x00813483.
Lemma D_1177c : decode_any W_1177c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11780 : bv 32 := 0x00013903.
Lemma D_11780 : decode_any W_11780 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11784 : bv 32 := 0x02010113.
Lemma D_11784 : decode_any W_11784 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11788 : bv 32 := 0x00030067.
Lemma D_11788 : decode_any W_11788 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1178c : bv 32 := 0xfd010113.
Lemma D_1178c : decode_any W_1178c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11790 : bv 32 := 0x02113423.
Lemma D_11790 : decode_any W_11790 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11794 : bv 32 := 0x02813023.
Lemma D_11794 : decode_any W_11794 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11798 : bv 32 := 0x00913c23.
Lemma D_11798 : decode_any W_11798 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1179c : bv 32 := 0x01213823.
Lemma D_1179c : decode_any W_1179c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117a0 : bv 32 := 0x01313423.
Lemma D_117a0 : decode_any W_117a0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117a4 : bv 32 := 0x00060413.
Lemma D_117a4 : decode_any W_117a4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117a8 : bv 32 := 0x00058493.
Lemma D_117a8 : decode_any W_117a8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117ac : bv 32 := 0x00050913.
Lemma D_117ac : decode_any W_117ac = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117b0 : bv 32 := 0x00359513.
Lemma D_117b0 : decode_any W_117b0 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117b4 : bv 32 := 0x00a60533.
Lemma D_117b4 : decode_any W_117b4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117b8 : bv 32 := 0x00850993.
Lemma D_117b8 : decode_any W_117b8 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117bc : bv 32 := 0xf25ff0ef.
Lemma D_117bc : decode_any W_117bc = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117c0 : bv 32 := 0x00048513.
Lemma D_117c0 : decode_any W_117c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117c4 : bv 32 := 0x00040593.
Lemma D_117c4 : decode_any W_117c4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117c8 : bv 32 := 0x00098613.
Lemma D_117c8 : decode_any W_117c8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117cc : bv 32 := 0x000900e7.
Lemma D_117cc : decode_any W_117cc = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117d4 : bv 32 := 0xfc010113.
Lemma D_117d4 : decode_any W_117d4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117d8 : bv 32 := 0x02113c23.
Lemma D_117d8 : decode_any W_117d8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117dc : bv 32 := 0x02813823.
Lemma D_117dc : decode_any W_117dc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117e0 : bv 32 := 0x02913423.
Lemma D_117e0 : decode_any W_117e0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117e4 : bv 32 := 0x03213023.
Lemma D_117e4 : decode_any W_117e4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117e8 : bv 32 := 0x01313c23.
Lemma D_117e8 : decode_any W_117e8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117ec : bv 32 := 0x01413823.
Lemma D_117ec : decode_any W_117ec = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117f0 : bv 32 := 0x01513423.
Lemma D_117f0 : decode_any W_117f0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117f4 : bv 32 := 0x02853683.
Lemma D_117f4 : decode_any W_117f4 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117f8 : bv 32 := 0x00003597.
Lemma D_117f8 : decode_any W_117f8 = Some (Auipc 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_117fc : bv 32 := 0x97058613.
Lemma D_117fc : decode_any W_117fc = Some (OpImm ALU_ADD 12 11 2416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11800 : bv 32 := 0x00003597.
Lemma D_11800 : decode_any W_11800 = Some (Auipc 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11804 : bv 32 := 0xb1058493.
Lemma D_11804 : decode_any W_11804 = Some (OpImm ALU_ADD 9 11 2832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11808 : bv 32 := 0x0c068e63.
Lemma D_11808 : decode_any W_11808 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1180c : bv 32 := 0x00000593.
Lemma D_1180c : decode_any W_1180c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11810 : bv 32 := 0x00000893.
Lemma D_11810 : decode_any W_11810 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11814 : bv 32 := 0x00003717.
Lemma D_11814 : decode_any W_11814 = Some (Auipc 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11818 : bv 32 := 0x01853783.
Lemma D_11818 : decode_any W_11818 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1181c : bv 32 := 0x02053503.
Lemma D_1181c : decode_any W_1181c = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11820 : bv 32 := 0x00600813.
Lemma D_11820 : decode_any W_11820 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11824 : bv 32 := 0x00002297.
Lemma D_11824 : decode_any W_11824 = Some (Auipc 5 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11828 : bv 32 := 0x8f476f03.
Lemma D_11828 : decode_any W_11828 = Some (Load SZ4 false 30 14 2292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1182c : bv 32 := 0x86c2b283.
Lemma D_1182c : decode_any W_1182c = Some (Load SZ8 true 5 5 2156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11830 : bv 32 := 0x00200313.
Lemma D_11830 : decode_any W_11830 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11834 : bv 32 := 0x00700393.
Lemma D_11834 : decode_any W_11834 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11838 : bv 32 := 0x6474ee37.
Lemma D_11838 : decode_any W_11838 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1183c : bv 32 := 0x551e0e1b.
Lemma D_1183c : decode_any W_1183c = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11840 : bv 32 := 0x00078e93.
Lemma D_11840 : decode_any W_11840 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11844 : bv 32 := 0x0180006f.
Lemma D_11844 : decode_any W_11844 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11848 : bv 32 := 0x010eb583.
Lemma D_11848 : decode_any W_11848 = Some (Load SZ8 true 11 29 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1184c : bv 32 := 0x40b785b3.
Lemma D_1184c : decode_any W_1184c = Some (Op ALU_SUB 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11850 : bv 32 := 0xfff68693.
Lemma D_11850 : decode_any W_11850 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11854 : bv 32 := 0x00ae8eb3.
Lemma D_11854 : decode_any W_11854 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11858 : bv 32 := 0x04068a63.
Lemma D_11858 : decode_any W_11858 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1185c : bv 32 := 0x000ea403.
Lemma D_1185c : decode_any W_1185c = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11860 : bv 32 := 0xff0404e3.
Lemma D_11860 : decode_any W_11860 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11864 : bv 32 := 0x00028a63.
Lemma D_11864 : decode_any W_11864 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11878 : bv 32 := 0x000e8f93.
Lemma D_11878 : decode_any W_11878 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1187c : bv 32 := 0x00740463.
Lemma D_1187c : decode_any W_1187c = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11880 : bv 32 := 0x00088f93.
Lemma D_11880 : decode_any W_11880 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11884 : bv 32 := 0x03c41063.
Lemma D_11884 : decode_any W_11884 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11888 : bv 32 := 0x028eb883.
Lemma D_11888 : decode_any W_11888 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1188c : bv 32 := 0x011f7c63.
Lemma D_1188c : decode_any W_1188c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118a4 : bv 32 := 0x000f8893.
Lemma D_118a4 : decode_any W_118a4 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118a8 : bv 32 := 0xfa9ff06f.
Lemma D_118a8 : decode_any W_118a8 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118ac : bv 32 := 0x02088c63.
Lemma D_118ac : decode_any W_118ac = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118e4 : bv 32 := 0x01063583.
Lemma D_118e4 : decode_any W_118e4 = Some (Load SZ8 true 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118e8 : bv 32 := 0x02063683.
Lemma D_118e8 : decode_any W_118e8 = Some (Load SZ8 true 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118ec : bv 32 := 0x02863503.
Lemma D_118ec : decode_any W_118ec = Some (Load SZ8 true 10 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118f0 : bv 32 := 0x00b68733.
Lemma D_118f0 : decode_any W_118f0 = Some (Op ALU_ADD 14 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118f4 : bv 32 := 0xfff50793.
Lemma D_118f4 : decode_any W_118f4 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118f8 : bv 32 := 0x40e00733.
Lemma D_118f8 : decode_any W_118f8 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_118fc : bv 32 := 0x00b7f5b3.
Lemma D_118fc : decode_any W_118fc = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11900 : bv 32 := 0x00e7f733.
Lemma D_11900 : decode_any W_11900 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11904 : bv 32 := 0x00700793.
Lemma D_11904 : decode_any W_11904 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11908 : bv 32 := 0x00d706b3.
Lemma D_11908 : decode_any W_11908 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1190c : bv 32 := 0x02d63023.
Lemma D_1190c : decode_any W_1190c = Some (Store SZ8 12 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11910 : bv 32 := 0x02b63823.
Lemma D_11910 : decode_any W_11910 = Some (Store SZ8 12 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11914 : bv 32 := 0x00a7e663.
Lemma D_11914 : decode_any W_11914 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11918 : bv 32 := 0x00800513.
Lemma D_11918 : decode_any W_11918 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1191c : bv 32 := 0x02a63423.
Lemma D_1191c : decode_any W_1191c = Some (Store SZ8 12 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11920 : bv 32 := 0x00d585b3.
Lemma D_11920 : decode_any W_11920 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11924 : bv 32 := 0x15100693.
Lemma D_11924 : decode_any W_11924 = Some (OpImm ALU_ADD 13 0 337, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11928 : bv 32 := 0x00a585b3.
Lemma D_11928 : decode_any W_11928 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1192c : bv 32 := 0x0df58593.
Lemma D_1192c : decode_any W_1192c = Some (OpImm ALU_ADD 11 11 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11930 : bv 32 := 0xff85f593.
Lemma D_11930 : decode_any W_11930 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11934 : bv 32 := 0x00b4bc23.
Lemma D_11934 : decode_any W_11934 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11938 : bv 32 := 0x02a4b023.
Lemma D_11938 : decode_any W_11938 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1193c : bv 32 := 0x04d5e063.
Lemma D_1193c : decode_any W_1193c = Some (Branch BC_LTU 11 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1197c : bv 32 := 0x03860593.
Lemma D_1197c : decode_any W_1197c = Some (OpImm ALU_ADD 11 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11980 : bv 32 := 0x0184b503.
Lemma D_11980 : decode_any W_11980 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11984 : bv 32 := 0x0204b683.
Lemma D_11984 : decode_any W_11984 = Some (Load SZ8 true 13 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11988 : bv 32 := 0x0284b603.
Lemma D_11988 : decode_any W_11988 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1198c : bv 32 := 0x0104ba03.
Lemma D_1198c : decode_any W_1198c = Some (Load SZ8 true 20 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11990 : bv 32 := 0xf3800713.
Lemma D_11990 : decode_any W_11990 = Some (OpImm ALU_ADD 14 0 3896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11994 : bv 32 := 0x40b70733.
Lemma D_11994 : decode_any W_11994 = Some (Op ALU_SUB 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11998 : bv 32 := 0xfff64793.
Lemma D_11998 : decode_any W_11998 = Some (OpImm ALU_XOR 15 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1199c : bv 32 := 0xfff68693.
Lemma D_1199c : decode_any W_1199c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119a0 : bv 32 := 0x00379793.
Lemma D_119a0 : decode_any W_119a0 = Some (ShiftImm ALU_SLL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119a4 : bv 32 := 0x00e6f6b3.
Lemma D_119a4 : decode_any W_119a4 = Some (Op ALU_AND 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119a8 : bv 32 := 0x00f507b3.
Lemma D_119a8 : decode_any W_119a8 = Some (Op ALU_ADD 15 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119ac : bv 32 := 0x00d58933.
Lemma D_119ac : decode_any W_119ac = Some (Op ALU_ADD 18 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119b0 : bv 32 := 0x00f589b3.
Lemma D_119b0 : decode_any W_119b0 = Some (Op ALU_ADD 19 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119b4 : bv 32 := 0x0c890413.
Lemma D_119b4 : decode_any W_119b4 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119b8 : bv 32 := 0x040a0463.
Lemma D_119b8 : decode_any W_119b8 = Some (Branch BC_EQ 20 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a00 : bv 32 := 0x00c9b023.
Lemma D_11a00 : decode_any W_11a00 = Some (Store SZ8 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a04 : bv 32 := 0x0d393023.
Lemma D_11a04 : decode_any W_11a04 = Some (Store SZ8 18 19 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a08 : bv 32 := 0x01293023.
Lemma D_11a08 : decode_any W_11a08 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a0c : bv 32 := 0x00040513.
Lemma D_11a0c : decode_any W_11a0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a10 : bv 32 := 0x65c000ef.
Lemma D_11a10 : decode_any W_11a10 = Some (Jal 1 1628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a14 : bv 32 := 0x04054a63.
Lemma D_11a14 : decode_any W_11a14 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a18 : bv 32 := 0x00051663.
Lemma D_11a18 : decode_any W_11a18 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a1c : bv 32 := 0x00100513.
Lemma D_11a1c : decode_any W_11a1c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a20 : bv 32 := 0x00a48023.
Lemma D_11a20 : decode_any W_11a20 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a24 : bv 32 := 0x00200513.
Lemma D_11a24 : decode_any W_11a24 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a28 : bv 32 := 0x00002597.
Lemma D_11a28 : decode_any W_11a28 = Some (Auipc 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a2c : bv 32 := 0x02a92423.
Lemma D_11a2c : decode_any W_11a2c = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a30 : bv 32 := 0x06000893.
Lemma D_11a30 : decode_any W_11a30 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a34 : bv 32 := 0x74058513.
Lemma D_11a34 : decode_any W_11a34 = Some (OpImm ALU_ADD 10 11 1856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a38 : bv 32 := 0x03848593.
Lemma D_11a38 : decode_any W_11a38 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a3c : bv 32 := 0x00000073.
Lemma D_11a3c : decode_any W_11a3c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_11a3c : is_ecall W_11a3c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_11a40 : bv 32 := 0x07890613.
Lemma D_11a40 : decode_any W_11a40 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a44 : bv 32 := 0x02a92023.
Lemma D_11a44 : decode_any W_11a44 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a48 : bv 32 := 0x08b93c23.
Lemma D_11a48 : decode_any W_11a48 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a4c : bv 32 := 0x06c93c23.
Lemma D_11a4c : decode_any W_11a4c = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a50 : bv 32 := 0x00003517.
Lemma D_11a50 : decode_any W_11a50 = Some (Auipc 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a54 : bv 32 := 0x8a853503.
Lemma D_11a54 : decode_any W_11a54 = Some (Load SZ8 true 10 10 2216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a58 : bv 32 := 0x01293423.
Lemma D_11a58 : decode_any W_11a58 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a5c : bv 32 := 0x01293823.
Lemma D_11a5c : decode_any W_11a5c = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a60 : bv 32 := 0x00a93c23.
Lemma D_11a60 : decode_any W_11a60 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a64 : bv 32 := 0x0080006f.
Lemma D_11a64 : decode_any W_11a64 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a6c : bv 32 := 0x03813083.
Lemma D_11a6c : decode_any W_11a6c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a70 : bv 32 := 0x03013403.
Lemma D_11a70 : decode_any W_11a70 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a74 : bv 32 := 0x02813483.
Lemma D_11a74 : decode_any W_11a74 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a78 : bv 32 := 0x02013903.
Lemma D_11a78 : decode_any W_11a78 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a7c : bv 32 := 0x01813983.
Lemma D_11a7c : decode_any W_11a7c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a80 : bv 32 := 0x01013a03.
Lemma D_11a80 : decode_any W_11a80 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a84 : bv 32 := 0x00813a83.
Lemma D_11a84 : decode_any W_11a84 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a88 : bv 32 := 0x04010113.
Lemma D_11a88 : decode_any W_11a88 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a8c : bv 32 := 0x00008067.
Lemma D_11a8c : decode_any W_11a8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a90 : bv 32 := 0x00050593.
Lemma D_11a90 : decode_any W_11a90 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a94 : bv 32 := 0x05e00893.
Lemma D_11a94 : decode_any W_11a94 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11a98 : bv 32 := 0x00000073.
Lemma D_11a98 : decode_any W_11a98 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_11a98 : is_ecall W_11a98 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_11f74 : bv 32 := 0x0e060a63.
Lemma D_11f74 : decode_any W_11f74 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f78 : bv 32 := 0x00b50023.
Lemma D_11f78 : decode_any W_11f78 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f7c : bv 32 := 0x00c506b3.
Lemma D_11f7c : decode_any W_11f7c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f80 : bv 32 := 0x00300713.
Lemma D_11f80 : decode_any W_11f80 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f84 : bv 32 := 0xfeb68fa3.
Lemma D_11f84 : decode_any W_11f84 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f88 : bv 32 := 0x0ee66063.
Lemma D_11f88 : decode_any W_11f88 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f8c : bv 32 := 0x00b500a3.
Lemma D_11f8c : decode_any W_11f8c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f90 : bv 32 := 0x00b50123.
Lemma D_11f90 : decode_any W_11f90 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f94 : bv 32 := 0x00700713.
Lemma D_11f94 : decode_any W_11f94 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f98 : bv 32 := 0xfeb68ea3.
Lemma D_11f98 : decode_any W_11f98 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11f9c : bv 32 := 0xfeb68f23.
Lemma D_11f9c : decode_any W_11f9c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fa0 : bv 32 := 0x0ce66463.
Lemma D_11fa0 : decode_any W_11fa0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fa4 : bv 32 := 0x00b501a3.
Lemma D_11fa4 : decode_any W_11fa4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fa8 : bv 32 := 0x00900793.
Lemma D_11fa8 : decode_any W_11fa8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fac : bv 32 := 0xfeb68e23.
Lemma D_11fac : decode_any W_11fac = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fb0 : bv 32 := 0x0af66c63.
Lemma D_11fb0 : decode_any W_11fb0 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fb4 : bv 32 := 0x40a006bb.
Lemma D_11fb4 : decode_any W_11fb4 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fb8 : bv 32 := 0x03859813.
Lemma D_11fb8 : decode_any W_11fb8 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fbc : bv 32 := 0x101015b7.
Lemma D_11fbc : decode_any W_11fbc = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fc0 : bv 32 := 0x0036f693.
Lemma D_11fc0 : decode_any W_11fc0 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fc4 : bv 32 := 0x00459713.
Lemma D_11fc4 : decode_any W_11fc4 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fc8 : bv 32 := 0x40d60633.
Lemma D_11fc8 : decode_any W_11fc8 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fcc : bv 32 := 0x00d505b3.
Lemma D_11fcc : decode_any W_11fcc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fd0 : bv 32 := 0x10070693.
Lemma D_11fd0 : decode_any W_11fd0 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fd4 : bv 32 := 0xffc67713.
Lemma D_11fd4 : decode_any W_11fd4 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fd8 : bv 32 := 0x02d83633.
Lemma D_11fd8 : decode_any W_11fd8 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fdc : bv 32 := 0x00c5a023.
Lemma D_11fdc : decode_any W_11fdc = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fe0 : bv 32 := 0x00e586b3.
Lemma D_11fe0 : decode_any W_11fe0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fe4 : bv 32 := 0xfec6ae23.
Lemma D_11fe4 : decode_any W_11fe4 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fe8 : bv 32 := 0x08f76063.
Lemma D_11fe8 : decode_any W_11fe8 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11fec : bv 32 := 0x00c5a223.
Lemma D_11fec : decode_any W_11fec = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11ff0 : bv 32 := 0x00c5a423.
Lemma D_11ff0 : decode_any W_11ff0 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11ff4 : bv 32 := 0x01900793.
Lemma D_11ff4 : decode_any W_11ff4 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11ff8 : bv 32 := 0xfec6aa23.
Lemma D_11ff8 : decode_any W_11ff8 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11ffc : bv 32 := 0xfec6ac23.
Lemma D_11ffc : decode_any W_11ffc = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12000 : bv 32 := 0x06f76463.
Lemma D_12000 : decode_any W_12000 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12004 : bv 32 := 0x00c5a623.
Lemma D_12004 : decode_any W_12004 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12008 : bv 32 := 0x00c5a823.
Lemma D_12008 : decode_any W_12008 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1200c : bv 32 := 0x00c5aa23.
Lemma D_1200c : decode_any W_1200c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12010 : bv 32 := 0x00c5ac23.
Lemma D_12010 : decode_any W_12010 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12014 : bv 32 := 0x0045f793.
Lemma D_12014 : decode_any W_12014 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12018 : bv 32 := 0x02000813.
Lemma D_12018 : decode_any W_12018 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1201c : bv 32 := 0x01878793.
Lemma D_1201c : decode_any W_1201c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12020 : bv 32 := 0x40f70733.
Lemma D_12020 : decode_any W_12020 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12024 : bv 32 := 0xfec6a223.
Lemma D_12024 : decode_any W_12024 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12028 : bv 32 := 0xfec6a423.
Lemma D_12028 : decode_any W_12028 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1202c : bv 32 := 0xfec6a623.
Lemma D_1202c : decode_any W_1202c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12030 : bv 32 := 0xfec6a823.
Lemma D_12030 : decode_any W_12030 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12034 : bv 32 := 0x03076a63.
Lemma D_12034 : decode_any W_12034 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12038 : bv 32 := 0x02061613.
Lemma D_12038 : decode_any W_12038 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1203c : bv 32 := 0x00f585b3.
Lemma D_1203c : decode_any W_1203c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12040 : bv 32 := 0x02065693.
Lemma D_12040 : decode_any W_12040 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12044 : bv 32 := 0x00d66633.
Lemma D_12044 : decode_any W_12044 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12048 : bv 32 := 0x01f00693.
Lemma D_12048 : decode_any W_12048 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1204c : bv 32 := 0x00c5b023.
Lemma D_1204c : decode_any W_1204c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12050 : bv 32 := 0x00c5b423.
Lemma D_12050 : decode_any W_12050 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12054 : bv 32 := 0x00c5b823.
Lemma D_12054 : decode_any W_12054 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12058 : bv 32 := 0x00c5bc23.
Lemma D_12058 : decode_any W_12058 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1205c : bv 32 := 0xfe070713.
Lemma D_1205c : decode_any W_1205c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12060 : bv 32 := 0x02058593.
Lemma D_12060 : decode_any W_12060 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12064 : bv 32 := 0xfee6e4e3.
Lemma D_12064 : decode_any W_12064 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12068 : bv 32 := 0x00008067.
Lemma D_12068 : decode_any W_12068 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1206c : bv 32 := 0x00050213.
Lemma D_1206c : decode_any W_1206c = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12070 : bv 32 := 0x00000513.
Lemma D_12070 : decode_any W_12070 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12074 : bv 32 := 0x00008067.
Lemma D_12074 : decode_any W_12074 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
