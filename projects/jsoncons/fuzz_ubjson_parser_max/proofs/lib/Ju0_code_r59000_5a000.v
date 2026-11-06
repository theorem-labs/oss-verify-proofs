(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKU.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_aa2d4 : bv 32 := 0x01000713.
Lemma F_aa2d4 : CTabKU.F 0xaa2d4 W_aa2d4.
Proof. vm_refl. Qed.
Lemma D_aa2d4 : CTabKU.D W_aa2d4 (OpImm ALU_ADD 14 0 16).
Proof. vm_refl. Qed.
Definition W_aa2d8 : bv 32 := 0x02e66c63.
Lemma F_aa2d8 : CTabKU.F 0xaa2d8 W_aa2d8.
Proof. vm_refl. Qed.
Lemma D_aa2d8 : CTabKU.D W_aa2d8 (Branch BC_LTU 12 14 56).
Proof. vm_refl. Qed.
Definition W_aa2dc : bv 32 := 0x00f00713.
Lemma F_aa2dc : CTabKU.F 0xaa2dc W_aa2dc.
Proof. vm_refl. Qed.
Lemma D_aa2dc : CTabKU.D W_aa2dc (OpImm ALU_ADD 14 0 15).
Proof. vm_refl. Qed.
Definition W_aa2e0 : bv 32 := 0x0005a783.
Lemma F_aa2e0 : CTabKU.F 0xaa2e0 W_aa2e0.
Proof. vm_refl. Qed.
Lemma D_aa2e0 : CTabKU.D W_aa2e0 (Load SZ4 true 15 11 0).
Proof. vm_refl. Qed.
Definition W_aa2e4 : bv 32 := 0x0045a803.
Lemma F_aa2e4 : CTabKU.F 0xaa2e4 W_aa2e4.
Proof. vm_refl. Qed.
Lemma D_aa2e4 : CTabKU.D W_aa2e4 (Load SZ4 true 16 11 4).
Proof. vm_refl. Qed.
Definition W_aa2e8 : bv 32 := 0x0085a883.
Lemma F_aa2e8 : CTabKU.F 0xaa2e8 W_aa2e8.
Proof. vm_refl. Qed.
Lemma D_aa2e8 : CTabKU.D W_aa2e8 (Load SZ4 true 17 11 8).
Proof. vm_refl. Qed.
Definition W_aa2ec : bv 32 := 0x00c5a283.
Lemma F_aa2ec : CTabKU.F 0xaa2ec W_aa2ec.
Proof. vm_refl. Qed.
Lemma D_aa2ec : CTabKU.D W_aa2ec (Load SZ4 true 5 11 12).
Proof. vm_refl. Qed.
Definition W_aa2f0 : bv 32 := 0x01058593.
Lemma F_aa2f0 : CTabKU.F 0xaa2f0 W_aa2f0.
Proof. vm_refl. Qed.
Lemma D_aa2f0 : CTabKU.D W_aa2f0 (OpImm ALU_ADD 11 11 16).
Proof. vm_refl. Qed.
Definition W_aa2f4 : bv 32 := 0xff060613.
Lemma F_aa2f4 : CTabKU.F 0xaa2f4 W_aa2f4.
Proof. vm_refl. Qed.
Lemma D_aa2f4 : CTabKU.D W_aa2f4 (OpImm ALU_ADD 12 12 4080).
Proof. vm_refl. Qed.
Definition W_aa2f8 : bv 32 := 0x00f6a023.
Lemma F_aa2f8 : CTabKU.F 0xaa2f8 W_aa2f8.
Proof. vm_refl. Qed.
Lemma D_aa2f8 : CTabKU.D W_aa2f8 (Store SZ4 13 15 0).
Proof. vm_refl. Qed.
Definition W_aa2fc : bv 32 := 0x0106a223.
Lemma F_aa2fc : CTabKU.F 0xaa2fc W_aa2fc.
Proof. vm_refl. Qed.
Lemma D_aa2fc : CTabKU.D W_aa2fc (Store SZ4 13 16 4).
Proof. vm_refl. Qed.
Definition W_aa300 : bv 32 := 0x0116a423.
Lemma F_aa300 : CTabKU.F 0xaa300 W_aa300.
Proof. vm_refl. Qed.
Lemma D_aa300 : CTabKU.D W_aa300 (Store SZ4 13 17 8).
Proof. vm_refl. Qed.
Definition W_aa304 : bv 32 := 0x0056a623.
Lemma F_aa304 : CTabKU.F 0xaa304 W_aa304.
Proof. vm_refl. Qed.
Lemma D_aa304 : CTabKU.D W_aa304 (Store SZ4 13 5 12).
Proof. vm_refl. Qed.
Definition W_aa308 : bv 32 := 0x01068693.
Lemma F_aa308 : CTabKU.F 0xaa308 W_aa308.
Proof. vm_refl. Qed.
Lemma D_aa308 : CTabKU.D W_aa308 (OpImm ALU_ADD 13 13 16).
Proof. vm_refl. Qed.
Definition W_aa30c : bv 32 := 0xfcc76ae3.
Lemma F_aa30c : CTabKU.F 0xaa30c W_aa30c.
Proof. vm_refl. Qed.
Lemma D_aa30c : CTabKU.D W_aa30c (Branch BC_LTU 14 12 8148).
Proof. vm_refl. Qed.
Definition W_aa310 : bv 32 := 0x00800713.
Lemma F_aa310 : CTabKU.F 0xaa310 W_aa310.
Proof. vm_refl. Qed.
Lemma D_aa310 : CTabKU.D W_aa310 (OpImm ALU_ADD 14 0 8).
Proof. vm_refl. Qed.
Definition W_aa314 : bv 32 := 0x00e66e63.
Lemma F_aa314 : CTabKU.F 0xaa314 W_aa314.
Proof. vm_refl. Qed.
Lemma D_aa314 : CTabKU.D W_aa314 (Branch BC_LTU 12 14 28).
Proof. vm_refl. Qed.
Definition W_aa318 : bv 32 := 0x0005a703.
Lemma F_aa318 : CTabKU.F 0xaa318 W_aa318.
Proof. vm_refl. Qed.
Lemma D_aa318 : CTabKU.D W_aa318 (Load SZ4 true 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa31c : bv 32 := 0x0045a783.
Lemma F_aa31c : CTabKU.F 0xaa31c W_aa31c.
Proof. vm_refl. Qed.
Lemma D_aa31c : CTabKU.D W_aa31c (Load SZ4 true 15 11 4).
Proof. vm_refl. Qed.
Definition W_aa320 : bv 32 := 0x00e6a023.
Lemma F_aa320 : CTabKU.F 0xaa320 W_aa320.
Proof. vm_refl. Qed.
Lemma D_aa320 : CTabKU.D W_aa320 (Store SZ4 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa324 : bv 32 := 0x00f6a223.
Lemma F_aa324 : CTabKU.F 0xaa324 W_aa324.
Proof. vm_refl. Qed.
Lemma D_aa324 : CTabKU.D W_aa324 (Store SZ4 13 15 4).
Proof. vm_refl. Qed.
Definition W_aa328 : bv 32 := 0x00868693.
Lemma F_aa328 : CTabKU.F 0xaa328 W_aa328.
Proof. vm_refl. Qed.
Lemma D_aa328 : CTabKU.D W_aa328 (OpImm ALU_ADD 13 13 8).
Proof. vm_refl. Qed.
Definition W_aa32c : bv 32 := 0x00858593.
Lemma F_aa32c : CTabKU.F 0xaa32c W_aa32c.
Proof. vm_refl. Qed.
Lemma D_aa32c : CTabKU.D W_aa32c (OpImm ALU_ADD 11 11 8).
Proof. vm_refl. Qed.
Definition W_aa330 : bv 32 := 0x00467713.
Lemma F_aa330 : CTabKU.F 0xaa330 W_aa330.
Proof. vm_refl. Qed.
Lemma D_aa330 : CTabKU.D W_aa330 (OpImm ALU_AND 14 12 4).
Proof. vm_refl. Qed.
Definition W_aa334 : bv 32 := 0x24070063.
Lemma F_aa334 : CTabKU.F 0xaa334 W_aa334.
Proof. vm_refl. Qed.
Lemma D_aa334 : CTabKU.D W_aa334 (Branch BC_EQ 14 0 576).
Proof. vm_refl. Qed.
Definition W_aa338 : bv 32 := 0x0005a703.
Lemma F_aa338 : CTabKU.F 0xaa338 W_aa338.
Proof. vm_refl. Qed.
Lemma D_aa338 : CTabKU.D W_aa338 (Load SZ4 true 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa33c : bv 32 := 0x00458593.
Lemma F_aa33c : CTabKU.F 0xaa33c W_aa33c.
Proof. vm_refl. Qed.
Lemma D_aa33c : CTabKU.D W_aa33c (OpImm ALU_ADD 11 11 4).
Proof. vm_refl. Qed.
Definition W_aa340 : bv 32 := 0x00e6a023.
Lemma F_aa340 : CTabKU.F 0xaa340 W_aa340.
Proof. vm_refl. Qed.
Lemma D_aa340 : CTabKU.D W_aa340 (Store SZ4 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa344 : bv 32 := 0x00468693.
Lemma F_aa344 : CTabKU.F 0xaa344 W_aa344.
Proof. vm_refl. Qed.
Lemma D_aa344 : CTabKU.D W_aa344 (OpImm ALU_ADD 13 13 4).
Proof. vm_refl. Qed.
Definition W_aa348 : bv 32 := 0x22c0006f.
Lemma F_aa348 : CTabKU.F 0xaa348 W_aa348.
Proof. vm_refl. Qed.
Lemma D_aa348 : CTabKU.D W_aa348 (Jal 0 556).
Proof. vm_refl. Qed.
Definition W_aa34c : bv 32 := 0x00e68023.
Lemma F_aa34c : CTabKU.F 0xaa34c W_aa34c.
Proof. vm_refl. Qed.
Lemma D_aa34c : CTabKU.D W_aa34c (Store SZ1 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa350 : bv 32 := 0x00168693.
Lemma F_aa350 : CTabKU.F 0xaa350 W_aa350.
Proof. vm_refl. Qed.
Lemma D_aa350 : CTabKU.D W_aa350 (OpImm ALU_ADD 13 13 1).
Proof. vm_refl. Qed.
Definition W_aa354 : bv 32 := 0xfff60613.
Lemma F_aa354 : CTabKU.F 0xaa354 W_aa354.
Proof. vm_refl. Qed.
Lemma D_aa354 : CTabKU.D W_aa354 (OpImm ALU_ADD 12 12 4095).
Proof. vm_refl. Qed.
Definition W_aa358 : bv 32 := 0x01058593.
Lemma F_aa358 : CTabKU.F 0xaa358 W_aa358.
Proof. vm_refl. Qed.
Lemma D_aa358 : CTabKU.D W_aa358 (OpImm ALU_ADD 11 11 16).
Proof. vm_refl. Qed.
Definition W_aa35c : bv 32 := 0x01200793.
Lemma F_aa35c : CTabKU.F 0xaa35c W_aa35c.
Proof. vm_refl. Qed.
Lemma D_aa35c : CTabKU.D W_aa35c (OpImm ALU_ADD 15 0 18).
Proof. vm_refl. Qed.
Definition W_aa360 : bv 32 := 0x0087581b.
Lemma F_aa360 : CTabKU.F 0xaa360 W_aa360.
Proof. vm_refl. Qed.
Lemma D_aa360 : CTabKU.D W_aa360 (ShiftImm32 ALU_SRL 16 14 8).
Proof. vm_refl. Qed.
Definition W_aa364 : bv 32 := 0xff45a883.
Lemma F_aa364 : CTabKU.F 0xaa364 W_aa364.
Proof. vm_refl. Qed.
Lemma D_aa364 : CTabKU.D W_aa364 (Load SZ4 true 17 11 4084).
Proof. vm_refl. Qed.
Definition W_aa368 : bv 32 := 0xff85a283.
Lemma F_aa368 : CTabKU.F 0xaa368 W_aa368.
Proof. vm_refl. Qed.
Lemma D_aa368 : CTabKU.D W_aa368 (Load SZ4 true 5 11 4088).
Proof. vm_refl. Qed.
Definition W_aa36c : bv 32 := 0xffc5a303.
Lemma F_aa36c : CTabKU.F 0xaa36c W_aa36c.
Proof. vm_refl. Qed.
Lemma D_aa36c : CTabKU.D W_aa36c (Load SZ4 true 6 11 4092).
Proof. vm_refl. Qed.
Definition W_aa370 : bv 32 := 0x0005a703.
Lemma F_aa370 : CTabKU.F 0xaa370 W_aa370.
Proof. vm_refl. Qed.
Lemma D_aa370 : CTabKU.D W_aa370 (Load SZ4 true 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa374 : bv 32 := 0x01889393.
Lemma F_aa374 : CTabKU.F 0xaa374 W_aa374.
Proof. vm_refl. Qed.
Lemma D_aa374 : CTabKU.D W_aa374 (ShiftImm ALU_SLL 7 17 24).
Proof. vm_refl. Qed.
Definition W_aa378 : bv 32 := 0x0088d89b.
Lemma F_aa378 : CTabKU.F 0xaa378 W_aa378.
Proof. vm_refl. Qed.
Lemma D_aa378 : CTabKU.D W_aa378 (ShiftImm32 ALU_SRL 17 17 8).
Proof. vm_refl. Qed.
Definition W_aa37c : bv 32 := 0x0103e833.
Lemma F_aa37c : CTabKU.F 0xaa37c W_aa37c.
Proof. vm_refl. Qed.
Lemma D_aa37c : CTabKU.D W_aa37c (Op ALU_OR 16 7 16).
Proof. vm_refl. Qed.
Definition W_aa380 : bv 32 := 0x01829393.
Lemma F_aa380 : CTabKU.F 0xaa380 W_aa380.
Proof. vm_refl. Qed.
Lemma D_aa380 : CTabKU.D W_aa380 (ShiftImm ALU_SLL 7 5 24).
Proof. vm_refl. Qed.
Definition W_aa384 : bv 32 := 0x0082d29b.
Lemma F_aa384 : CTabKU.F 0xaa384 W_aa384.
Proof. vm_refl. Qed.
Lemma D_aa384 : CTabKU.D W_aa384 (ShiftImm32 ALU_SRL 5 5 8).
Proof. vm_refl. Qed.
Definition W_aa388 : bv 32 := 0x0113e8b3.
Lemma F_aa388 : CTabKU.F 0xaa388 W_aa388.
Proof. vm_refl. Qed.
Lemma D_aa388 : CTabKU.D W_aa388 (Op ALU_OR 17 7 17).
Proof. vm_refl. Qed.
Definition W_aa38c : bv 32 := 0x01831393.
Lemma F_aa38c : CTabKU.F 0xaa38c W_aa38c.
Proof. vm_refl. Qed.
Lemma D_aa38c : CTabKU.D W_aa38c (ShiftImm ALU_SLL 7 6 24).
Proof. vm_refl. Qed.
Definition W_aa390 : bv 32 := 0x0083531b.
Lemma F_aa390 : CTabKU.F 0xaa390 W_aa390.
Proof. vm_refl. Qed.
Lemma D_aa390 : CTabKU.D W_aa390 (ShiftImm32 ALU_SRL 6 6 8).
Proof. vm_refl. Qed.
Definition W_aa394 : bv 32 := 0x0053e2b3.
Lemma F_aa394 : CTabKU.F 0xaa394 W_aa394.
Proof. vm_refl. Qed.
Lemma D_aa394 : CTabKU.D W_aa394 (Op ALU_OR 5 7 5).
Proof. vm_refl. Qed.
Definition W_aa398 : bv 32 := 0x01871393.
Lemma F_aa398 : CTabKU.F 0xaa398 W_aa398.
Proof. vm_refl. Qed.
Lemma D_aa398 : CTabKU.D W_aa398 (ShiftImm ALU_SLL 7 14 24).
Proof. vm_refl. Qed.
Definition W_aa39c : bv 32 := 0x0063e333.
Lemma F_aa39c : CTabKU.F 0xaa39c W_aa39c.
Proof. vm_refl. Qed.
Lemma D_aa39c : CTabKU.D W_aa39c (Op ALU_OR 6 7 6).
Proof. vm_refl. Qed.
Definition W_aa3a0 : bv 32 := 0xff060613.
Lemma F_aa3a0 : CTabKU.F 0xaa3a0 W_aa3a0.
Proof. vm_refl. Qed.
Lemma D_aa3a0 : CTabKU.D W_aa3a0 (OpImm ALU_ADD 12 12 4080).
Proof. vm_refl. Qed.
Definition W_aa3a4 : bv 32 := 0x0106a023.
Lemma F_aa3a4 : CTabKU.F 0xaa3a4 W_aa3a4.
Proof. vm_refl. Qed.
Lemma D_aa3a4 : CTabKU.D W_aa3a4 (Store SZ4 13 16 0).
Proof. vm_refl. Qed.
Definition W_aa3a8 : bv 32 := 0x0116a223.
Lemma F_aa3a8 : CTabKU.F 0xaa3a8 W_aa3a8.
Proof. vm_refl. Qed.
Lemma D_aa3a8 : CTabKU.D W_aa3a8 (Store SZ4 13 17 4).
Proof. vm_refl. Qed.
Definition W_aa3ac : bv 32 := 0x0056a423.
Lemma F_aa3ac : CTabKU.F 0xaa3ac W_aa3ac.
Proof. vm_refl. Qed.
Lemma D_aa3ac : CTabKU.D W_aa3ac (Store SZ4 13 5 8).
Proof. vm_refl. Qed.
Definition W_aa3b0 : bv 32 := 0x0066a623.
Lemma F_aa3b0 : CTabKU.F 0xaa3b0 W_aa3b0.
Proof. vm_refl. Qed.
Lemma D_aa3b0 : CTabKU.D W_aa3b0 (Store SZ4 13 6 12).
Proof. vm_refl. Qed.
Definition W_aa3b4 : bv 32 := 0x01068693.
Lemma F_aa3b4 : CTabKU.F 0xaa3b4 W_aa3b4.
Proof. vm_refl. Qed.
Lemma D_aa3b4 : CTabKU.D W_aa3b4 (OpImm ALU_ADD 13 13 16).
Proof. vm_refl. Qed.
Definition W_aa3b8 : bv 32 := 0x01058593.
Lemma F_aa3b8 : CTabKU.F 0xaa3b8 W_aa3b8.
Proof. vm_refl. Qed.
Lemma D_aa3b8 : CTabKU.D W_aa3b8 (OpImm ALU_ADD 11 11 16).
Proof. vm_refl. Qed.
Definition W_aa3bc : bv 32 := 0xfac7e2e3.
Lemma F_aa3bc : CTabKU.F 0xaa3bc W_aa3bc.
Proof. vm_refl. Qed.
Lemma D_aa3bc : CTabKU.D W_aa3bc (Branch BC_LTU 15 12 8100).
Proof. vm_refl. Qed.
Definition W_aa3c0 : bv 32 := 0xff158593.
Lemma F_aa3c0 : CTabKU.F 0xaa3c0 W_aa3c0.
Proof. vm_refl. Qed.
Lemma D_aa3c0 : CTabKU.D W_aa3c0 (OpImm ALU_ADD 11 11 4081).
Proof. vm_refl. Qed.
Definition W_aa3c4 : bv 32 := 0x01000713.
Lemma F_aa3c4 : CTabKU.F 0xaa3c4 W_aa3c4.
Proof. vm_refl. Qed.
Lemma D_aa3c4 : CTabKU.D W_aa3c4 (OpImm ALU_ADD 14 0 16).
Proof. vm_refl. Qed.
Definition W_aa3c8 : bv 32 := 0xe4e666e3.
Lemma F_aa3c8 : CTabKU.F 0xaa3c8 W_aa3c8.
Proof. vm_refl. Qed.
Lemma D_aa3c8 : CTabKU.D W_aa3c8 (Branch BC_LTU 12 14 7756).
Proof. vm_refl. Qed.
Definition W_aa3cc : bv 32 := 0x0940006f.
Lemma F_aa3cc : CTabKU.F 0xaa3cc W_aa3cc.
Proof. vm_refl. Qed.
Lemma D_aa3cc : CTabKU.D W_aa3cc (Jal 0 148).
Proof. vm_refl. Qed.
Definition W_aa3d0 : bv 32 := 0x00875793.
Lemma F_aa3d0 : CTabKU.F 0xaa3d0 W_aa3d0.
Proof. vm_refl. Qed.
Lemma D_aa3d0 : CTabKU.D W_aa3d0 (ShiftImm ALU_SRL 15 14 8).
Proof. vm_refl. Qed.
Definition W_aa3d4 : bv 32 := 0x01075813.
Lemma F_aa3d4 : CTabKU.F 0xaa3d4 W_aa3d4.
Proof. vm_refl. Qed.
Lemma D_aa3d4 : CTabKU.D W_aa3d4 (ShiftImm ALU_SRL 16 14 16).
Proof. vm_refl. Qed.
Definition W_aa3d8 : bv 32 := 0xffd60613.
Lemma F_aa3d8 : CTabKU.F 0xaa3d8 W_aa3d8.
Proof. vm_refl. Qed.
Lemma D_aa3d8 : CTabKU.D W_aa3d8 (OpImm ALU_ADD 12 12 4093).
Proof. vm_refl. Qed.
Definition W_aa3dc : bv 32 := 0x00e68023.
Lemma F_aa3dc : CTabKU.F 0xaa3dc W_aa3dc.
Proof. vm_refl. Qed.
Lemma D_aa3dc : CTabKU.D W_aa3dc (Store SZ1 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa3e0 : bv 32 := 0x00f680a3.
Lemma F_aa3e0 : CTabKU.F 0xaa3e0 W_aa3e0.
Proof. vm_refl. Qed.
Lemma D_aa3e0 : CTabKU.D W_aa3e0 (Store SZ1 13 15 1).
Proof. vm_refl. Qed.
Definition W_aa3e4 : bv 32 := 0x01068123.
Lemma F_aa3e4 : CTabKU.F 0xaa3e4 W_aa3e4.
Proof. vm_refl. Qed.
Lemma D_aa3e4 : CTabKU.D W_aa3e4 (Store SZ1 13 16 2).
Proof. vm_refl. Qed.
Definition W_aa3e8 : bv 32 := 0x00368693.
Lemma F_aa3e8 : CTabKU.F 0xaa3e8 W_aa3e8.
Proof. vm_refl. Qed.
Lemma D_aa3e8 : CTabKU.D W_aa3e8 (OpImm ALU_ADD 13 13 3).
Proof. vm_refl. Qed.
Definition W_aa3ec : bv 32 := 0x01058593.
Lemma F_aa3ec : CTabKU.F 0xaa3ec W_aa3ec.
Proof. vm_refl. Qed.
Lemma D_aa3ec : CTabKU.D W_aa3ec (OpImm ALU_ADD 11 11 16).
Proof. vm_refl. Qed.
Definition W_aa3f0 : bv 32 := 0x01000793.
Lemma F_aa3f0 : CTabKU.F 0xaa3f0 W_aa3f0.
Proof. vm_refl. Qed.
Lemma D_aa3f0 : CTabKU.D W_aa3f0 (OpImm ALU_ADD 15 0 16).
Proof. vm_refl. Qed.
Definition W_aa3f4 : bv 32 := 0x0187581b.
Lemma F_aa3f4 : CTabKU.F 0xaa3f4 W_aa3f4.
Proof. vm_refl. Qed.
Lemma D_aa3f4 : CTabKU.D W_aa3f4 (ShiftImm32 ALU_SRL 16 14 24).
Proof. vm_refl. Qed.
Definition W_aa3f8 : bv 32 := 0xff45a883.
Lemma F_aa3f8 : CTabKU.F 0xaa3f8 W_aa3f8.
Proof. vm_refl. Qed.
Lemma D_aa3f8 : CTabKU.D W_aa3f8 (Load SZ4 true 17 11 4084).
Proof. vm_refl. Qed.
Definition W_aa3fc : bv 32 := 0xff85a283.
Lemma F_aa3fc : CTabKU.F 0xaa3fc W_aa3fc.
Proof. vm_refl. Qed.
Lemma D_aa3fc : CTabKU.D W_aa3fc (Load SZ4 true 5 11 4088).
Proof. vm_refl. Qed.
Definition W_aa400 : bv 32 := 0xffc5a303.
Lemma F_aa400 : CTabKU.F 0xaa400 W_aa400.
Proof. vm_refl. Qed.
Lemma D_aa400 : CTabKU.D W_aa400 (Load SZ4 true 6 11 4092).
Proof. vm_refl. Qed.
Definition W_aa404 : bv 32 := 0x0005a703.
Lemma F_aa404 : CTabKU.F 0xaa404 W_aa404.
Proof. vm_refl. Qed.
Lemma D_aa404 : CTabKU.D W_aa404 (Load SZ4 true 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa408 : bv 32 := 0x00889393.
Lemma F_aa408 : CTabKU.F 0xaa408 W_aa408.
Proof. vm_refl. Qed.
Lemma D_aa408 : CTabKU.D W_aa408 (ShiftImm ALU_SLL 7 17 8).
Proof. vm_refl. Qed.
Definition W_aa40c : bv 32 := 0x0188d89b.
Lemma F_aa40c : CTabKU.F 0xaa40c W_aa40c.
Proof. vm_refl. Qed.
Lemma D_aa40c : CTabKU.D W_aa40c (ShiftImm32 ALU_SRL 17 17 24).
Proof. vm_refl. Qed.
Definition W_aa410 : bv 32 := 0x0103e833.
Lemma F_aa410 : CTabKU.F 0xaa410 W_aa410.
Proof. vm_refl. Qed.
Lemma D_aa410 : CTabKU.D W_aa410 (Op ALU_OR 16 7 16).
Proof. vm_refl. Qed.
Definition W_aa414 : bv 32 := 0x00829393.
Lemma F_aa414 : CTabKU.F 0xaa414 W_aa414.
Proof. vm_refl. Qed.
Lemma D_aa414 : CTabKU.D W_aa414 (ShiftImm ALU_SLL 7 5 8).
Proof. vm_refl. Qed.
Definition W_aa418 : bv 32 := 0x0182d29b.
Lemma F_aa418 : CTabKU.F 0xaa418 W_aa418.
Proof. vm_refl. Qed.
Lemma D_aa418 : CTabKU.D W_aa418 (ShiftImm32 ALU_SRL 5 5 24).
Proof. vm_refl. Qed.
Definition W_aa41c : bv 32 := 0x0113e8b3.
Lemma F_aa41c : CTabKU.F 0xaa41c W_aa41c.
Proof. vm_refl. Qed.
Lemma D_aa41c : CTabKU.D W_aa41c (Op ALU_OR 17 7 17).
Proof. vm_refl. Qed.
Definition W_aa420 : bv 32 := 0x00831393.
Lemma F_aa420 : CTabKU.F 0xaa420 W_aa420.
Proof. vm_refl. Qed.
Lemma D_aa420 : CTabKU.D W_aa420 (ShiftImm ALU_SLL 7 6 8).
Proof. vm_refl. Qed.
Definition W_aa424 : bv 32 := 0x0183531b.
Lemma F_aa424 : CTabKU.F 0xaa424 W_aa424.
Proof. vm_refl. Qed.
Lemma D_aa424 : CTabKU.D W_aa424 (ShiftImm32 ALU_SRL 6 6 24).
Proof. vm_refl. Qed.
Definition W_aa428 : bv 32 := 0x0053e2b3.
Lemma F_aa428 : CTabKU.F 0xaa428 W_aa428.
Proof. vm_refl. Qed.
Lemma D_aa428 : CTabKU.D W_aa428 (Op ALU_OR 5 7 5).
Proof. vm_refl. Qed.
Definition W_aa42c : bv 32 := 0x00871393.
Lemma F_aa42c : CTabKU.F 0xaa42c W_aa42c.
Proof. vm_refl. Qed.
Lemma D_aa42c : CTabKU.D W_aa42c (ShiftImm ALU_SLL 7 14 8).
Proof. vm_refl. Qed.
Definition W_aa430 : bv 32 := 0x0063e333.
Lemma F_aa430 : CTabKU.F 0xaa430 W_aa430.
Proof. vm_refl. Qed.
Lemma D_aa430 : CTabKU.D W_aa430 (Op ALU_OR 6 7 6).
Proof. vm_refl. Qed.
Definition W_aa434 : bv 32 := 0xff060613.
Lemma F_aa434 : CTabKU.F 0xaa434 W_aa434.
Proof. vm_refl. Qed.
Lemma D_aa434 : CTabKU.D W_aa434 (OpImm ALU_ADD 12 12 4080).
Proof. vm_refl. Qed.
Definition W_aa438 : bv 32 := 0x0106a023.
Lemma F_aa438 : CTabKU.F 0xaa438 W_aa438.
Proof. vm_refl. Qed.
Lemma D_aa438 : CTabKU.D W_aa438 (Store SZ4 13 16 0).
Proof. vm_refl. Qed.
Definition W_aa43c : bv 32 := 0x0116a223.
Lemma F_aa43c : CTabKU.F 0xaa43c W_aa43c.
Proof. vm_refl. Qed.
Lemma D_aa43c : CTabKU.D W_aa43c (Store SZ4 13 17 4).
Proof. vm_refl. Qed.
Definition W_aa440 : bv 32 := 0x0056a423.
Lemma F_aa440 : CTabKU.F 0xaa440 W_aa440.
Proof. vm_refl. Qed.
Lemma D_aa440 : CTabKU.D W_aa440 (Store SZ4 13 5 8).
Proof. vm_refl. Qed.
Definition W_aa444 : bv 32 := 0x0066a623.
Lemma F_aa444 : CTabKU.F 0xaa444 W_aa444.
Proof. vm_refl. Qed.
Lemma D_aa444 : CTabKU.D W_aa444 (Store SZ4 13 6 12).
Proof. vm_refl. Qed.
Definition W_aa448 : bv 32 := 0x01068693.
Lemma F_aa448 : CTabKU.F 0xaa448 W_aa448.
Proof. vm_refl. Qed.
Lemma D_aa448 : CTabKU.D W_aa448 (OpImm ALU_ADD 13 13 16).
Proof. vm_refl. Qed.
Definition W_aa44c : bv 32 := 0x01058593.
Lemma F_aa44c : CTabKU.F 0xaa44c W_aa44c.
Proof. vm_refl. Qed.
Lemma D_aa44c : CTabKU.D W_aa44c (OpImm ALU_ADD 11 11 16).
Proof. vm_refl. Qed.
Definition W_aa450 : bv 32 := 0xfac7e2e3.
Lemma F_aa450 : CTabKU.F 0xaa450 W_aa450.
Proof. vm_refl. Qed.
Lemma D_aa450 : CTabKU.D W_aa450 (Branch BC_LTU 15 12 8100).
Proof. vm_refl. Qed.
Definition W_aa454 : bv 32 := 0xff358593.
Lemma F_aa454 : CTabKU.F 0xaa454 W_aa454.
Proof. vm_refl. Qed.
Lemma D_aa454 : CTabKU.D W_aa454 (OpImm ALU_ADD 11 11 4083).
Proof. vm_refl. Qed.
Definition W_aa458 : bv 32 := 0x01000713.
Lemma F_aa458 : CTabKU.F 0xaa458 W_aa458.
Proof. vm_refl. Qed.
Lemma D_aa458 : CTabKU.D W_aa458 (OpImm ALU_ADD 14 0 16).
Proof. vm_refl. Qed.
Definition W_aa45c : bv 32 := 0xdae66ce3.
Lemma F_aa45c : CTabKU.F 0xaa45c W_aa45c.
Proof. vm_refl. Qed.
Lemma D_aa45c : CTabKU.D W_aa45c (Branch BC_LTU 12 14 7608).
Proof. vm_refl. Qed.
Definition W_aa460 : bv 32 := 0x0005c703.
Lemma F_aa460 : CTabKU.F 0xaa460 W_aa460.
Proof. vm_refl. Qed.
Lemma D_aa460 : CTabKU.D W_aa460 (Load SZ1 false 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa464 : bv 32 := 0x0015c783.
Lemma F_aa464 : CTabKU.F 0xaa464 W_aa464.
Proof. vm_refl. Qed.
Lemma D_aa464 : CTabKU.D W_aa464 (Load SZ1 false 15 11 1).
Proof. vm_refl. Qed.
Definition W_aa468 : bv 32 := 0x0025c803.
Lemma F_aa468 : CTabKU.F 0xaa468 W_aa468.
Proof. vm_refl. Qed.
Lemma D_aa468 : CTabKU.D W_aa468 (Load SZ1 false 16 11 2).
Proof. vm_refl. Qed.
Definition W_aa46c : bv 32 := 0x0035c883.
Lemma F_aa46c : CTabKU.F 0xaa46c W_aa46c.
Proof. vm_refl. Qed.
Lemma D_aa46c : CTabKU.D W_aa46c (Load SZ1 false 17 11 3).
Proof. vm_refl. Qed.
Definition W_aa470 : bv 32 := 0x0045c283.
Lemma F_aa470 : CTabKU.F 0xaa470 W_aa470.
Proof. vm_refl. Qed.
Lemma D_aa470 : CTabKU.D W_aa470 (Load SZ1 false 5 11 4).
Proof. vm_refl. Qed.
Definition W_aa474 : bv 32 := 0x0055c303.
Lemma F_aa474 : CTabKU.F 0xaa474 W_aa474.
Proof. vm_refl. Qed.
Lemma D_aa474 : CTabKU.D W_aa474 (Load SZ1 false 6 11 5).
Proof. vm_refl. Qed.
Definition W_aa478 : bv 32 := 0x0065c383.
Lemma F_aa478 : CTabKU.F 0xaa478 W_aa478.
Proof. vm_refl. Qed.
Lemma D_aa478 : CTabKU.D W_aa478 (Load SZ1 false 7 11 6).
Proof. vm_refl. Qed.
Definition W_aa47c : bv 32 := 0x0075ce03.
Lemma F_aa47c : CTabKU.F 0xaa47c W_aa47c.
Proof. vm_refl. Qed.
Lemma D_aa47c : CTabKU.D W_aa47c (Load SZ1 false 28 11 7).
Proof. vm_refl. Qed.
Definition W_aa480 : bv 32 := 0x00e68023.
Lemma F_aa480 : CTabKU.F 0xaa480 W_aa480.
Proof. vm_refl. Qed.
Lemma D_aa480 : CTabKU.D W_aa480 (Store SZ1 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa484 : bv 32 := 0x00f680a3.
Lemma F_aa484 : CTabKU.F 0xaa484 W_aa484.
Proof. vm_refl. Qed.
Lemma D_aa484 : CTabKU.D W_aa484 (Store SZ1 13 15 1).
Proof. vm_refl. Qed.
Definition W_aa488 : bv 32 := 0x01068123.
Lemma F_aa488 : CTabKU.F 0xaa488 W_aa488.
Proof. vm_refl. Qed.
Lemma D_aa488 : CTabKU.D W_aa488 (Store SZ1 13 16 2).
Proof. vm_refl. Qed.
Definition W_aa48c : bv 32 := 0x011681a3.
Lemma F_aa48c : CTabKU.F 0xaa48c W_aa48c.
Proof. vm_refl. Qed.
Lemma D_aa48c : CTabKU.D W_aa48c (Store SZ1 13 17 3).
Proof. vm_refl. Qed.
Definition W_aa490 : bv 32 := 0x0085c703.
Lemma F_aa490 : CTabKU.F 0xaa490 W_aa490.
Proof. vm_refl. Qed.
Lemma D_aa490 : CTabKU.D W_aa490 (Load SZ1 false 14 11 8).
Proof. vm_refl. Qed.
Definition W_aa494 : bv 32 := 0x0095c783.
Lemma F_aa494 : CTabKU.F 0xaa494 W_aa494.
Proof. vm_refl. Qed.
Lemma D_aa494 : CTabKU.D W_aa494 (Load SZ1 false 15 11 9).
Proof. vm_refl. Qed.
Definition W_aa498 : bv 32 := 0x00a5c803.
Lemma F_aa498 : CTabKU.F 0xaa498 W_aa498.
Proof. vm_refl. Qed.
Lemma D_aa498 : CTabKU.D W_aa498 (Load SZ1 false 16 11 10).
Proof. vm_refl. Qed.
Definition W_aa49c : bv 32 := 0x00b5c883.
Lemma F_aa49c : CTabKU.F 0xaa49c W_aa49c.
Proof. vm_refl. Qed.
Lemma D_aa49c : CTabKU.D W_aa49c (Load SZ1 false 17 11 11).
Proof. vm_refl. Qed.
Definition W_aa4a0 : bv 32 := 0x00568223.
Lemma F_aa4a0 : CTabKU.F 0xaa4a0 W_aa4a0.
Proof. vm_refl. Qed.
Lemma D_aa4a0 : CTabKU.D W_aa4a0 (Store SZ1 13 5 4).
Proof. vm_refl. Qed.
Definition W_aa4a4 : bv 32 := 0x006682a3.
Lemma F_aa4a4 : CTabKU.F 0xaa4a4 W_aa4a4.
Proof. vm_refl. Qed.
Lemma D_aa4a4 : CTabKU.D W_aa4a4 (Store SZ1 13 6 5).
Proof. vm_refl. Qed.
Definition W_aa4a8 : bv 32 := 0x00768323.
Lemma F_aa4a8 : CTabKU.F 0xaa4a8 W_aa4a8.
Proof. vm_refl. Qed.
Lemma D_aa4a8 : CTabKU.D W_aa4a8 (Store SZ1 13 7 6).
Proof. vm_refl. Qed.
Definition W_aa4ac : bv 32 := 0x01c683a3.
Lemma F_aa4ac : CTabKU.F 0xaa4ac W_aa4ac.
Proof. vm_refl. Qed.
Lemma D_aa4ac : CTabKU.D W_aa4ac (Store SZ1 13 28 7).
Proof. vm_refl. Qed.
Definition W_aa4b0 : bv 32 := 0x00c5c283.
Lemma F_aa4b0 : CTabKU.F 0xaa4b0 W_aa4b0.
Proof. vm_refl. Qed.
Lemma D_aa4b0 : CTabKU.D W_aa4b0 (Load SZ1 false 5 11 12).
Proof. vm_refl. Qed.
Definition W_aa4b4 : bv 32 := 0x00d5c303.
Lemma F_aa4b4 : CTabKU.F 0xaa4b4 W_aa4b4.
Proof. vm_refl. Qed.
Lemma D_aa4b4 : CTabKU.D W_aa4b4 (Load SZ1 false 6 11 13).
Proof. vm_refl. Qed.
Definition W_aa4b8 : bv 32 := 0x00e5c383.
Lemma F_aa4b8 : CTabKU.F 0xaa4b8 W_aa4b8.
Proof. vm_refl. Qed.
Lemma D_aa4b8 : CTabKU.D W_aa4b8 (Load SZ1 false 7 11 14).
Proof. vm_refl. Qed.
Definition W_aa4bc : bv 32 := 0x00f5ce03.
Lemma F_aa4bc : CTabKU.F 0xaa4bc W_aa4bc.
Proof. vm_refl. Qed.
Lemma D_aa4bc : CTabKU.D W_aa4bc (Load SZ1 false 28 11 15).
Proof. vm_refl. Qed.
Definition W_aa4c0 : bv 32 := 0x01058593.
Lemma F_aa4c0 : CTabKU.F 0xaa4c0 W_aa4c0.
Proof. vm_refl. Qed.
Lemma D_aa4c0 : CTabKU.D W_aa4c0 (OpImm ALU_ADD 11 11 16).
Proof. vm_refl. Qed.
Definition W_aa4c4 : bv 32 := 0x00e68423.
Lemma F_aa4c4 : CTabKU.F 0xaa4c4 W_aa4c4.
Proof. vm_refl. Qed.
Lemma D_aa4c4 : CTabKU.D W_aa4c4 (Store SZ1 13 14 8).
Proof. vm_refl. Qed.
Definition W_aa4c8 : bv 32 := 0x00f684a3.
Lemma F_aa4c8 : CTabKU.F 0xaa4c8 W_aa4c8.
Proof. vm_refl. Qed.
Lemma D_aa4c8 : CTabKU.D W_aa4c8 (Store SZ1 13 15 9).
Proof. vm_refl. Qed.
Definition W_aa4cc : bv 32 := 0x01068523.
Lemma F_aa4cc : CTabKU.F 0xaa4cc W_aa4cc.
Proof. vm_refl. Qed.
Lemma D_aa4cc : CTabKU.D W_aa4cc (Store SZ1 13 16 10).
Proof. vm_refl. Qed.
Definition W_aa4d0 : bv 32 := 0x011685a3.
Lemma F_aa4d0 : CTabKU.F 0xaa4d0 W_aa4d0.
Proof. vm_refl. Qed.
Lemma D_aa4d0 : CTabKU.D W_aa4d0 (Store SZ1 13 17 11).
Proof. vm_refl. Qed.
Definition W_aa4d4 : bv 32 := 0x01068713.
Lemma F_aa4d4 : CTabKU.F 0xaa4d4 W_aa4d4.
Proof. vm_refl. Qed.
Lemma D_aa4d4 : CTabKU.D W_aa4d4 (OpImm ALU_ADD 14 13 16).
Proof. vm_refl. Qed.
Definition W_aa4d8 : bv 32 := 0x00568623.
Lemma F_aa4d8 : CTabKU.F 0xaa4d8 W_aa4d8.
Proof. vm_refl. Qed.
Lemma D_aa4d8 : CTabKU.D W_aa4d8 (Store SZ1 13 5 12).
Proof. vm_refl. Qed.
Definition W_aa4dc : bv 32 := 0x006686a3.
Lemma F_aa4dc : CTabKU.F 0xaa4dc W_aa4dc.
Proof. vm_refl. Qed.
Lemma D_aa4dc : CTabKU.D W_aa4dc (Store SZ1 13 6 13).
Proof. vm_refl. Qed.
Definition W_aa4e0 : bv 32 := 0x00768723.
Lemma F_aa4e0 : CTabKU.F 0xaa4e0 W_aa4e0.
Proof. vm_refl. Qed.
Lemma D_aa4e0 : CTabKU.D W_aa4e0 (Store SZ1 13 7 14).
Proof. vm_refl. Qed.
Definition W_aa4e4 : bv 32 := 0x01c687a3.
Lemma F_aa4e4 : CTabKU.F 0xaa4e4 W_aa4e4.
Proof. vm_refl. Qed.
Lemma D_aa4e4 : CTabKU.D W_aa4e4 (Store SZ1 13 28 15).
Proof. vm_refl. Qed.
Definition W_aa4e8 : bv 32 := 0x00070693.
Lemma F_aa4e8 : CTabKU.F 0xaa4e8 W_aa4e8.
Proof. vm_refl. Qed.
Lemma D_aa4e8 : CTabKU.D W_aa4e8 (OpImm ALU_ADD 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa4ec : bv 32 := 0x00867713.
Lemma F_aa4ec : CTabKU.F 0xaa4ec W_aa4ec.
Proof. vm_refl. Qed.
Lemma D_aa4ec : CTabKU.D W_aa4ec (OpImm ALU_AND 14 12 8).
Proof. vm_refl. Qed.
Definition W_aa4f0 : bv 32 := 0xd20706e3.
Lemma F_aa4f0 : CTabKU.F 0xaa4f0 W_aa4f0.
Proof. vm_refl. Qed.
Lemma D_aa4f0 : CTabKU.D W_aa4f0 (Branch BC_EQ 14 0 7468).
Proof. vm_refl. Qed.
Definition W_aa4f4 : bv 32 := 0x0005c703.
Lemma F_aa4f4 : CTabKU.F 0xaa4f4 W_aa4f4.
Proof. vm_refl. Qed.
Lemma D_aa4f4 : CTabKU.D W_aa4f4 (Load SZ1 false 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa4f8 : bv 32 := 0x0015c783.
Lemma F_aa4f8 : CTabKU.F 0xaa4f8 W_aa4f8.
Proof. vm_refl. Qed.
Lemma D_aa4f8 : CTabKU.D W_aa4f8 (Load SZ1 false 15 11 1).
Proof. vm_refl. Qed.
Definition W_aa4fc : bv 32 := 0x0025c803.
Lemma F_aa4fc : CTabKU.F 0xaa4fc W_aa4fc.
Proof. vm_refl. Qed.
Lemma D_aa4fc : CTabKU.D W_aa4fc (Load SZ1 false 16 11 2).
Proof. vm_refl. Qed.
Definition W_aa500 : bv 32 := 0x0035c883.
Lemma F_aa500 : CTabKU.F 0xaa500 W_aa500.
Proof. vm_refl. Qed.
Lemma D_aa500 : CTabKU.D W_aa500 (Load SZ1 false 17 11 3).
Proof. vm_refl. Qed.
Definition W_aa504 : bv 32 := 0x0045c283.
Lemma F_aa504 : CTabKU.F 0xaa504 W_aa504.
Proof. vm_refl. Qed.
Lemma D_aa504 : CTabKU.D W_aa504 (Load SZ1 false 5 11 4).
Proof. vm_refl. Qed.
Definition W_aa508 : bv 32 := 0x0055c303.
Lemma F_aa508 : CTabKU.F 0xaa508 W_aa508.
Proof. vm_refl. Qed.
Lemma D_aa508 : CTabKU.D W_aa508 (Load SZ1 false 6 11 5).
Proof. vm_refl. Qed.
Definition W_aa50c : bv 32 := 0x0065c383.
Lemma F_aa50c : CTabKU.F 0xaa50c W_aa50c.
Proof. vm_refl. Qed.
Lemma D_aa50c : CTabKU.D W_aa50c (Load SZ1 false 7 11 6).
Proof. vm_refl. Qed.
Definition W_aa510 : bv 32 := 0x0075ce03.
Lemma F_aa510 : CTabKU.F 0xaa510 W_aa510.
Proof. vm_refl. Qed.
Lemma D_aa510 : CTabKU.D W_aa510 (Load SZ1 false 28 11 7).
Proof. vm_refl. Qed.
Definition W_aa514 : bv 32 := 0x00858593.
Lemma F_aa514 : CTabKU.F 0xaa514 W_aa514.
Proof. vm_refl. Qed.
Lemma D_aa514 : CTabKU.D W_aa514 (OpImm ALU_ADD 11 11 8).
Proof. vm_refl. Qed.
Definition W_aa518 : bv 32 := 0x00e68023.
Lemma F_aa518 : CTabKU.F 0xaa518 W_aa518.
Proof. vm_refl. Qed.
Lemma D_aa518 : CTabKU.D W_aa518 (Store SZ1 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa51c : bv 32 := 0x00f680a3.
Lemma F_aa51c : CTabKU.F 0xaa51c W_aa51c.
Proof. vm_refl. Qed.
Lemma D_aa51c : CTabKU.D W_aa51c (Store SZ1 13 15 1).
Proof. vm_refl. Qed.
Definition W_aa520 : bv 32 := 0x01068123.
Lemma F_aa520 : CTabKU.F 0xaa520 W_aa520.
Proof. vm_refl. Qed.
Lemma D_aa520 : CTabKU.D W_aa520 (Store SZ1 13 16 2).
Proof. vm_refl. Qed.
Definition W_aa524 : bv 32 := 0x011681a3.
Lemma F_aa524 : CTabKU.F 0xaa524 W_aa524.
Proof. vm_refl. Qed.
Lemma D_aa524 : CTabKU.D W_aa524 (Store SZ1 13 17 3).
Proof. vm_refl. Qed.
Definition W_aa528 : bv 32 := 0x00868713.
Lemma F_aa528 : CTabKU.F 0xaa528 W_aa528.
Proof. vm_refl. Qed.
Lemma D_aa528 : CTabKU.D W_aa528 (OpImm ALU_ADD 14 13 8).
Proof. vm_refl. Qed.
Definition W_aa52c : bv 32 := 0x00568223.
Lemma F_aa52c : CTabKU.F 0xaa52c W_aa52c.
Proof. vm_refl. Qed.
Lemma D_aa52c : CTabKU.D W_aa52c (Store SZ1 13 5 4).
Proof. vm_refl. Qed.
Definition W_aa530 : bv 32 := 0x006682a3.
Lemma F_aa530 : CTabKU.F 0xaa530 W_aa530.
Proof. vm_refl. Qed.
Lemma D_aa530 : CTabKU.D W_aa530 (Store SZ1 13 6 5).
Proof. vm_refl. Qed.
Definition W_aa534 : bv 32 := 0x00768323.
Lemma F_aa534 : CTabKU.F 0xaa534 W_aa534.
Proof. vm_refl. Qed.
Lemma D_aa534 : CTabKU.D W_aa534 (Store SZ1 13 7 6).
Proof. vm_refl. Qed.
Definition W_aa538 : bv 32 := 0x01c683a3.
Lemma F_aa538 : CTabKU.F 0xaa538 W_aa538.
Proof. vm_refl. Qed.
Lemma D_aa538 : CTabKU.D W_aa538 (Store SZ1 13 28 7).
Proof. vm_refl. Qed.
Definition W_aa53c : bv 32 := 0x00070693.
Lemma F_aa53c : CTabKU.F 0xaa53c W_aa53c.
Proof. vm_refl. Qed.
Lemma D_aa53c : CTabKU.D W_aa53c (OpImm ALU_ADD 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa540 : bv 32 := 0x00467713.
Lemma F_aa540 : CTabKU.F 0xaa540 W_aa540.
Proof. vm_refl. Qed.
Lemma D_aa540 : CTabKU.D W_aa540 (OpImm ALU_AND 14 12 4).
Proof. vm_refl. Qed.
Definition W_aa544 : bv 32 := 0x02070863.
Lemma F_aa544 : CTabKU.F 0xaa544 W_aa544.
Proof. vm_refl. Qed.
Lemma D_aa544 : CTabKU.D W_aa544 (Branch BC_EQ 14 0 48).
Proof. vm_refl. Qed.
Definition W_aa548 : bv 32 := 0x0005c703.
Lemma F_aa548 : CTabKU.F 0xaa548 W_aa548.
Proof. vm_refl. Qed.
Lemma D_aa548 : CTabKU.D W_aa548 (Load SZ1 false 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa54c : bv 32 := 0x0015c783.
Lemma F_aa54c : CTabKU.F 0xaa54c W_aa54c.
Proof. vm_refl. Qed.
Lemma D_aa54c : CTabKU.D W_aa54c (Load SZ1 false 15 11 1).
Proof. vm_refl. Qed.
Definition W_aa550 : bv 32 := 0x0025c803.
Lemma F_aa550 : CTabKU.F 0xaa550 W_aa550.
Proof. vm_refl. Qed.
Lemma D_aa550 : CTabKU.D W_aa550 (Load SZ1 false 16 11 2).
Proof. vm_refl. Qed.
Definition W_aa554 : bv 32 := 0x0035c883.
Lemma F_aa554 : CTabKU.F 0xaa554 W_aa554.
Proof. vm_refl. Qed.
Lemma D_aa554 : CTabKU.D W_aa554 (Load SZ1 false 17 11 3).
Proof. vm_refl. Qed.
Definition W_aa558 : bv 32 := 0x00458593.
Lemma F_aa558 : CTabKU.F 0xaa558 W_aa558.
Proof. vm_refl. Qed.
Lemma D_aa558 : CTabKU.D W_aa558 (OpImm ALU_ADD 11 11 4).
Proof. vm_refl. Qed.
Definition W_aa55c : bv 32 := 0x00468293.
Lemma F_aa55c : CTabKU.F 0xaa55c W_aa55c.
Proof. vm_refl. Qed.
Lemma D_aa55c : CTabKU.D W_aa55c (OpImm ALU_ADD 5 13 4).
Proof. vm_refl. Qed.
Definition W_aa560 : bv 32 := 0x00e68023.
Lemma F_aa560 : CTabKU.F 0xaa560 W_aa560.
Proof. vm_refl. Qed.
Lemma D_aa560 : CTabKU.D W_aa560 (Store SZ1 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa564 : bv 32 := 0x00f680a3.
Lemma F_aa564 : CTabKU.F 0xaa564 W_aa564.
Proof. vm_refl. Qed.
Lemma D_aa564 : CTabKU.D W_aa564 (Store SZ1 13 15 1).
Proof. vm_refl. Qed.
Definition W_aa568 : bv 32 := 0x01068123.
Lemma F_aa568 : CTabKU.F 0xaa568 W_aa568.
Proof. vm_refl. Qed.
Lemma D_aa568 : CTabKU.D W_aa568 (Store SZ1 13 16 2).
Proof. vm_refl. Qed.
Definition W_aa56c : bv 32 := 0x011681a3.
Lemma F_aa56c : CTabKU.F 0xaa56c W_aa56c.
Proof. vm_refl. Qed.
Lemma D_aa56c : CTabKU.D W_aa56c (Store SZ1 13 17 3).
Proof. vm_refl. Qed.
Definition W_aa570 : bv 32 := 0x00028693.
Lemma F_aa570 : CTabKU.F 0xaa570 W_aa570.
Proof. vm_refl. Qed.
Lemma D_aa570 : CTabKU.D W_aa570 (OpImm ALU_ADD 13 5 0).
Proof. vm_refl. Qed.
Definition W_aa574 : bv 32 := 0x00267713.
Lemma F_aa574 : CTabKU.F 0xaa574 W_aa574.
Proof. vm_refl. Qed.
Lemma D_aa574 : CTabKU.D W_aa574 (OpImm ALU_AND 14 12 2).
Proof. vm_refl. Qed.
Definition W_aa578 : bv 32 := 0x00071863.
Lemma F_aa578 : CTabKU.F 0xaa578 W_aa578.
Proof. vm_refl. Qed.
Lemma D_aa578 : CTabKU.D W_aa578 (Branch BC_NE 14 0 16).
Proof. vm_refl. Qed.
Definition W_aa57c : bv 32 := 0x00167613.
Lemma F_aa57c : CTabKU.F 0xaa57c W_aa57c.
Proof. vm_refl. Qed.
Lemma D_aa57c : CTabKU.D W_aa57c (OpImm ALU_AND 12 12 1).
Proof. vm_refl. Qed.
Definition W_aa580 : bv 32 := 0x02061663.
Lemma F_aa580 : CTabKU.F 0xaa580 W_aa580.
Proof. vm_refl. Qed.
Lemma D_aa580 : CTabKU.D W_aa580 (Branch BC_NE 12 0 44).
Proof. vm_refl. Qed.
Definition W_aa584 : bv 32 := 0x00008067.
Lemma F_aa584 : CTabKU.F 0xaa584 W_aa584.
Proof. vm_refl. Qed.
Lemma D_aa584 : CTabKU.D W_aa584 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_aa588 : bv 32 := 0x0005c703.
Lemma F_aa588 : CTabKU.F 0xaa588 W_aa588.
Proof. vm_refl. Qed.
Lemma D_aa588 : CTabKU.D W_aa588 (Load SZ1 false 14 11 0).
Proof. vm_refl. Qed.
Definition W_aa58c : bv 32 := 0x0015c783.
Lemma F_aa58c : CTabKU.F 0xaa58c W_aa58c.
Proof. vm_refl. Qed.
Lemma D_aa58c : CTabKU.D W_aa58c (Load SZ1 false 15 11 1).
Proof. vm_refl. Qed.
Definition W_aa590 : bv 32 := 0x00258593.
Lemma F_aa590 : CTabKU.F 0xaa590 W_aa590.
Proof. vm_refl. Qed.
Lemma D_aa590 : CTabKU.D W_aa590 (OpImm ALU_ADD 11 11 2).
Proof. vm_refl. Qed.
Definition W_aa594 : bv 32 := 0x00268813.
Lemma F_aa594 : CTabKU.F 0xaa594 W_aa594.
Proof. vm_refl. Qed.
Lemma D_aa594 : CTabKU.D W_aa594 (OpImm ALU_ADD 16 13 2).
Proof. vm_refl. Qed.
Definition W_aa598 : bv 32 := 0x00e68023.
Lemma F_aa598 : CTabKU.F 0xaa598 W_aa598.
Proof. vm_refl. Qed.
Lemma D_aa598 : CTabKU.D W_aa598 (Store SZ1 13 14 0).
Proof. vm_refl. Qed.
Definition W_aa59c : bv 32 := 0x00f680a3.
Lemma F_aa59c : CTabKU.F 0xaa59c W_aa59c.
Proof. vm_refl. Qed.
Lemma D_aa59c : CTabKU.D W_aa59c (Store SZ1 13 15 1).
Proof. vm_refl. Qed.
Definition W_aa5a0 : bv 32 := 0x00080693.
Lemma F_aa5a0 : CTabKU.F 0xaa5a0 W_aa5a0.
Proof. vm_refl. Qed.
Lemma D_aa5a0 : CTabKU.D W_aa5a0 (OpImm ALU_ADD 13 16 0).
Proof. vm_refl. Qed.
Definition W_aa5a4 : bv 32 := 0x00167613.
Lemma F_aa5a4 : CTabKU.F 0xaa5a4 W_aa5a4.
Proof. vm_refl. Qed.
Lemma D_aa5a4 : CTabKU.D W_aa5a4 (OpImm ALU_AND 12 12 1).
Proof. vm_refl. Qed.
Definition W_aa5a8 : bv 32 := 0xfc060ee3.
Lemma F_aa5a8 : CTabKU.F 0xaa5a8 W_aa5a8.
Proof. vm_refl. Qed.
Lemma D_aa5a8 : CTabKU.D W_aa5a8 (Branch BC_EQ 12 0 8156).
Proof. vm_refl. Qed.
Definition W_aa5ac : bv 32 := 0x0005c583.
Lemma F_aa5ac : CTabKU.F 0xaa5ac W_aa5ac.
Proof. vm_refl. Qed.
Lemma D_aa5ac : CTabKU.D W_aa5ac (Load SZ1 false 11 11 0).
Proof. vm_refl. Qed.
Definition W_aa5b0 : bv 32 := 0x00b68023.
Lemma F_aa5b0 : CTabKU.F 0xaa5b0 W_aa5b0.
Proof. vm_refl. Qed.
Lemma D_aa5b0 : CTabKU.D W_aa5b0 (Store SZ1 13 11 0).
Proof. vm_refl. Qed.
Definition W_aa5b4 : bv 32 := 0x00008067.
Lemma F_aa5b4 : CTabKU.F 0xaa5b4 W_aa5b4.
Proof. vm_refl. Qed.
Lemma D_aa5b4 : CTabKU.D W_aa5b4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_aa734 : bv 32 := 0x0e060a63.
Lemma F_aa734 : CTabKU.F 0xaa734 W_aa734.
Proof. vm_refl. Qed.
Lemma D_aa734 : CTabKU.D W_aa734 (Branch BC_EQ 12 0 244).
Proof. vm_refl. Qed.
Definition W_aa738 : bv 32 := 0x00b50023.
Lemma F_aa738 : CTabKU.F 0xaa738 W_aa738.
Proof. vm_refl. Qed.
Lemma D_aa738 : CTabKU.D W_aa738 (Store SZ1 10 11 0).
Proof. vm_refl. Qed.
Definition W_aa73c : bv 32 := 0x00c506b3.
Lemma F_aa73c : CTabKU.F 0xaa73c W_aa73c.
Proof. vm_refl. Qed.
Lemma D_aa73c : CTabKU.D W_aa73c (Op ALU_ADD 13 10 12).
Proof. vm_refl. Qed.
Definition W_aa740 : bv 32 := 0x00300713.
Lemma F_aa740 : CTabKU.F 0xaa740 W_aa740.
Proof. vm_refl. Qed.
Lemma D_aa740 : CTabKU.D W_aa740 (OpImm ALU_ADD 14 0 3).
Proof. vm_refl. Qed.
Definition W_aa744 : bv 32 := 0xfeb68fa3.
Lemma F_aa744 : CTabKU.F 0xaa744 W_aa744.
Proof. vm_refl. Qed.
Lemma D_aa744 : CTabKU.D W_aa744 (Store SZ1 13 11 4095).
Proof. vm_refl. Qed.
Definition W_aa748 : bv 32 := 0x0ee66063.
Lemma F_aa748 : CTabKU.F 0xaa748 W_aa748.
Proof. vm_refl. Qed.
Lemma D_aa748 : CTabKU.D W_aa748 (Branch BC_LTU 12 14 224).
Proof. vm_refl. Qed.
Definition W_aa74c : bv 32 := 0x00b500a3.
Lemma F_aa74c : CTabKU.F 0xaa74c W_aa74c.
Proof. vm_refl. Qed.
Lemma D_aa74c : CTabKU.D W_aa74c (Store SZ1 10 11 1).
Proof. vm_refl. Qed.
Definition W_aa750 : bv 32 := 0x00b50123.
Lemma F_aa750 : CTabKU.F 0xaa750 W_aa750.
Proof. vm_refl. Qed.
Lemma D_aa750 : CTabKU.D W_aa750 (Store SZ1 10 11 2).
Proof. vm_refl. Qed.
Definition W_aa754 : bv 32 := 0x00700713.
Lemma F_aa754 : CTabKU.F 0xaa754 W_aa754.
Proof. vm_refl. Qed.
Lemma D_aa754 : CTabKU.D W_aa754 (OpImm ALU_ADD 14 0 7).
Proof. vm_refl. Qed.
Definition W_aa758 : bv 32 := 0xfeb68ea3.
Lemma F_aa758 : CTabKU.F 0xaa758 W_aa758.
Proof. vm_refl. Qed.
Lemma D_aa758 : CTabKU.D W_aa758 (Store SZ1 13 11 4093).
Proof. vm_refl. Qed.
Definition W_aa75c : bv 32 := 0xfeb68f23.
Lemma F_aa75c : CTabKU.F 0xaa75c W_aa75c.
Proof. vm_refl. Qed.
Lemma D_aa75c : CTabKU.D W_aa75c (Store SZ1 13 11 4094).
Proof. vm_refl. Qed.
Definition W_aa760 : bv 32 := 0x0ce66463.
Lemma F_aa760 : CTabKU.F 0xaa760 W_aa760.
Proof. vm_refl. Qed.
Lemma D_aa760 : CTabKU.D W_aa760 (Branch BC_LTU 12 14 200).
Proof. vm_refl. Qed.
Definition W_aa764 : bv 32 := 0x00b501a3.
Lemma F_aa764 : CTabKU.F 0xaa764 W_aa764.
Proof. vm_refl. Qed.
Lemma D_aa764 : CTabKU.D W_aa764 (Store SZ1 10 11 3).
Proof. vm_refl. Qed.
Definition W_aa768 : bv 32 := 0x00900793.
Lemma F_aa768 : CTabKU.F 0xaa768 W_aa768.
Proof. vm_refl. Qed.
Lemma D_aa768 : CTabKU.D W_aa768 (OpImm ALU_ADD 15 0 9).
Proof. vm_refl. Qed.
Definition W_aa76c : bv 32 := 0xfeb68e23.
Lemma F_aa76c : CTabKU.F 0xaa76c W_aa76c.
Proof. vm_refl. Qed.
Lemma D_aa76c : CTabKU.D W_aa76c (Store SZ1 13 11 4092).
Proof. vm_refl. Qed.
Definition W_aa770 : bv 32 := 0x0af66c63.
Lemma F_aa770 : CTabKU.F 0xaa770 W_aa770.
Proof. vm_refl. Qed.
Lemma D_aa770 : CTabKU.D W_aa770 (Branch BC_LTU 12 15 184).
Proof. vm_refl. Qed.
Definition W_aa774 : bv 32 := 0x40a006bb.
Lemma F_aa774 : CTabKU.F 0xaa774 W_aa774.
Proof. vm_refl. Qed.
Lemma D_aa774 : CTabKU.D W_aa774 (Op32 ALU_SUB 13 0 10).
Proof. vm_refl. Qed.
Definition W_aa778 : bv 32 := 0x03859813.
Lemma F_aa778 : CTabKU.F 0xaa778 W_aa778.
Proof. vm_refl. Qed.
Lemma D_aa778 : CTabKU.D W_aa778 (ShiftImm ALU_SLL 16 11 56).
Proof. vm_refl. Qed.
Definition W_aa77c : bv 32 := 0x101015b7.
Lemma F_aa77c : CTabKU.F 0xaa77c W_aa77c.
Proof. vm_refl. Qed.
Lemma D_aa77c : CTabKU.D W_aa77c (Lui 11 65793).
Proof. vm_refl. Qed.
Definition W_aa780 : bv 32 := 0x0036f693.
Lemma F_aa780 : CTabKU.F 0xaa780 W_aa780.
Proof. vm_refl. Qed.
Lemma D_aa780 : CTabKU.D W_aa780 (OpImm ALU_AND 13 13 3).
Proof. vm_refl. Qed.
Definition W_aa784 : bv 32 := 0x00459713.
Lemma F_aa784 : CTabKU.F 0xaa784 W_aa784.
Proof. vm_refl. Qed.
Lemma D_aa784 : CTabKU.D W_aa784 (ShiftImm ALU_SLL 14 11 4).
Proof. vm_refl. Qed.
Definition W_aa788 : bv 32 := 0x40d60633.
Lemma F_aa788 : CTabKU.F 0xaa788 W_aa788.
Proof. vm_refl. Qed.
Lemma D_aa788 : CTabKU.D W_aa788 (Op ALU_SUB 12 12 13).
Proof. vm_refl. Qed.
Definition W_aa78c : bv 32 := 0x00d505b3.
Lemma F_aa78c : CTabKU.F 0xaa78c W_aa78c.
Proof. vm_refl. Qed.
Lemma D_aa78c : CTabKU.D W_aa78c (Op ALU_ADD 11 10 13).
Proof. vm_refl. Qed.
Definition W_aa790 : bv 32 := 0x10070693.
Lemma F_aa790 : CTabKU.F 0xaa790 W_aa790.
Proof. vm_refl. Qed.
Lemma D_aa790 : CTabKU.D W_aa790 (OpImm ALU_ADD 13 14 256).
Proof. vm_refl. Qed.
Definition W_aa794 : bv 32 := 0xffc67713.
Lemma F_aa794 : CTabKU.F 0xaa794 W_aa794.
Proof. vm_refl. Qed.
Lemma D_aa794 : CTabKU.D W_aa794 (OpImm ALU_AND 14 12 4092).
Proof. vm_refl. Qed.
Definition W_aa798 : bv 32 := 0x02d83633.
Lemma F_aa798 : CTabKU.F 0xaa798 W_aa798.
Proof. vm_refl. Qed.
Lemma D_aa798 : CTabKU.D W_aa798 (Mul M_MULHU 12 16 13).
Proof. vm_refl. Qed.
Definition W_aa79c : bv 32 := 0x00c5a023.
Lemma F_aa79c : CTabKU.F 0xaa79c W_aa79c.
Proof. vm_refl. Qed.
Lemma D_aa79c : CTabKU.D W_aa79c (Store SZ4 11 12 0).
Proof. vm_refl. Qed.
Definition W_aa7a0 : bv 32 := 0x00e586b3.
Lemma F_aa7a0 : CTabKU.F 0xaa7a0 W_aa7a0.
Proof. vm_refl. Qed.
Lemma D_aa7a0 : CTabKU.D W_aa7a0 (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_aa7a4 : bv 32 := 0xfec6ae23.
Lemma F_aa7a4 : CTabKU.F 0xaa7a4 W_aa7a4.
Proof. vm_refl. Qed.
Lemma D_aa7a4 : CTabKU.D W_aa7a4 (Store SZ4 13 12 4092).
Proof. vm_refl. Qed.
Definition W_aa7a8 : bv 32 := 0x08f76063.
Lemma F_aa7a8 : CTabKU.F 0xaa7a8 W_aa7a8.
Proof. vm_refl. Qed.
Lemma D_aa7a8 : CTabKU.D W_aa7a8 (Branch BC_LTU 14 15 128).
Proof. vm_refl. Qed.
Definition W_aa7ac : bv 32 := 0x00c5a223.
Lemma F_aa7ac : CTabKU.F 0xaa7ac W_aa7ac.
Proof. vm_refl. Qed.
Lemma D_aa7ac : CTabKU.D W_aa7ac (Store SZ4 11 12 4).
Proof. vm_refl. Qed.
Definition W_aa7b0 : bv 32 := 0x00c5a423.
Lemma F_aa7b0 : CTabKU.F 0xaa7b0 W_aa7b0.
Proof. vm_refl. Qed.
Lemma D_aa7b0 : CTabKU.D W_aa7b0 (Store SZ4 11 12 8).
Proof. vm_refl. Qed.
Definition W_aa7b4 : bv 32 := 0x01900793.
Lemma F_aa7b4 : CTabKU.F 0xaa7b4 W_aa7b4.
Proof. vm_refl. Qed.
Lemma D_aa7b4 : CTabKU.D W_aa7b4 (OpImm ALU_ADD 15 0 25).
Proof. vm_refl. Qed.
Definition W_aa7b8 : bv 32 := 0xfec6aa23.
Lemma F_aa7b8 : CTabKU.F 0xaa7b8 W_aa7b8.
Proof. vm_refl. Qed.
Lemma D_aa7b8 : CTabKU.D W_aa7b8 (Store SZ4 13 12 4084).
Proof. vm_refl. Qed.
Definition W_aa7bc : bv 32 := 0xfec6ac23.
Lemma F_aa7bc : CTabKU.F 0xaa7bc W_aa7bc.
Proof. vm_refl. Qed.
Lemma D_aa7bc : CTabKU.D W_aa7bc (Store SZ4 13 12 4088).
Proof. vm_refl. Qed.
Definition W_aa7c0 : bv 32 := 0x06f76463.
Lemma F_aa7c0 : CTabKU.F 0xaa7c0 W_aa7c0.
Proof. vm_refl. Qed.
Lemma D_aa7c0 : CTabKU.D W_aa7c0 (Branch BC_LTU 14 15 104).
Proof. vm_refl. Qed.
Definition W_aa7c4 : bv 32 := 0x00c5a623.
Lemma F_aa7c4 : CTabKU.F 0xaa7c4 W_aa7c4.
Proof. vm_refl. Qed.
Lemma D_aa7c4 : CTabKU.D W_aa7c4 (Store SZ4 11 12 12).
Proof. vm_refl. Qed.
Definition W_aa7c8 : bv 32 := 0x00c5a823.
Lemma F_aa7c8 : CTabKU.F 0xaa7c8 W_aa7c8.
Proof. vm_refl. Qed.
Lemma D_aa7c8 : CTabKU.D W_aa7c8 (Store SZ4 11 12 16).
Proof. vm_refl. Qed.
Definition W_aa7cc : bv 32 := 0x00c5aa23.
Lemma F_aa7cc : CTabKU.F 0xaa7cc W_aa7cc.
Proof. vm_refl. Qed.
Lemma D_aa7cc : CTabKU.D W_aa7cc (Store SZ4 11 12 20).
Proof. vm_refl. Qed.
Definition W_aa7d0 : bv 32 := 0x00c5ac23.
Lemma F_aa7d0 : CTabKU.F 0xaa7d0 W_aa7d0.
Proof. vm_refl. Qed.
Lemma D_aa7d0 : CTabKU.D W_aa7d0 (Store SZ4 11 12 24).
Proof. vm_refl. Qed.
Definition W_aa7d4 : bv 32 := 0x0045f793.
Lemma F_aa7d4 : CTabKU.F 0xaa7d4 W_aa7d4.
Proof. vm_refl. Qed.
Lemma D_aa7d4 : CTabKU.D W_aa7d4 (OpImm ALU_AND 15 11 4).
Proof. vm_refl. Qed.
Definition W_aa7d8 : bv 32 := 0x02000813.
Lemma F_aa7d8 : CTabKU.F 0xaa7d8 W_aa7d8.
Proof. vm_refl. Qed.
Lemma D_aa7d8 : CTabKU.D W_aa7d8 (OpImm ALU_ADD 16 0 32).
Proof. vm_refl. Qed.
Definition W_aa7dc : bv 32 := 0x01878793.
Lemma F_aa7dc : CTabKU.F 0xaa7dc W_aa7dc.
Proof. vm_refl. Qed.
Lemma D_aa7dc : CTabKU.D W_aa7dc (OpImm ALU_ADD 15 15 24).
Proof. vm_refl. Qed.
Definition W_aa7e0 : bv 32 := 0x40f70733.
Lemma F_aa7e0 : CTabKU.F 0xaa7e0 W_aa7e0.
Proof. vm_refl. Qed.
Lemma D_aa7e0 : CTabKU.D W_aa7e0 (Op ALU_SUB 14 14 15).
Proof. vm_refl. Qed.
Definition W_aa7e4 : bv 32 := 0xfec6a223.
Lemma F_aa7e4 : CTabKU.F 0xaa7e4 W_aa7e4.
Proof. vm_refl. Qed.
Lemma D_aa7e4 : CTabKU.D W_aa7e4 (Store SZ4 13 12 4068).
Proof. vm_refl. Qed.
Definition W_aa7e8 : bv 32 := 0xfec6a423.
Lemma F_aa7e8 : CTabKU.F 0xaa7e8 W_aa7e8.
Proof. vm_refl. Qed.
Lemma D_aa7e8 : CTabKU.D W_aa7e8 (Store SZ4 13 12 4072).
Proof. vm_refl. Qed.
Definition W_aa7ec : bv 32 := 0xfec6a623.
Lemma F_aa7ec : CTabKU.F 0xaa7ec W_aa7ec.
Proof. vm_refl. Qed.
Lemma D_aa7ec : CTabKU.D W_aa7ec (Store SZ4 13 12 4076).
Proof. vm_refl. Qed.
Definition W_aa7f0 : bv 32 := 0xfec6a823.
Lemma F_aa7f0 : CTabKU.F 0xaa7f0 W_aa7f0.
Proof. vm_refl. Qed.
Lemma D_aa7f0 : CTabKU.D W_aa7f0 (Store SZ4 13 12 4080).
Proof. vm_refl. Qed.
Definition W_aa7f4 : bv 32 := 0x03076a63.
Lemma F_aa7f4 : CTabKU.F 0xaa7f4 W_aa7f4.
Proof. vm_refl. Qed.
Lemma D_aa7f4 : CTabKU.D W_aa7f4 (Branch BC_LTU 14 16 52).
Proof. vm_refl. Qed.
Definition W_aa7f8 : bv 32 := 0x02061613.
Lemma F_aa7f8 : CTabKU.F 0xaa7f8 W_aa7f8.
Proof. vm_refl. Qed.
Lemma D_aa7f8 : CTabKU.D W_aa7f8 (ShiftImm ALU_SLL 12 12 32).
Proof. vm_refl. Qed.
Definition W_aa7fc : bv 32 := 0x00f585b3.
Lemma F_aa7fc : CTabKU.F 0xaa7fc W_aa7fc.
Proof. vm_refl. Qed.
Lemma D_aa7fc : CTabKU.D W_aa7fc (Op ALU_ADD 11 11 15).
Proof. vm_refl. Qed.
Definition W_aa800 : bv 32 := 0x02065693.
Lemma F_aa800 : CTabKU.F 0xaa800 W_aa800.
Proof. vm_refl. Qed.
Lemma D_aa800 : CTabKU.D W_aa800 (ShiftImm ALU_SRL 13 12 32).
Proof. vm_refl. Qed.
Definition W_aa804 : bv 32 := 0x00d66633.
Lemma F_aa804 : CTabKU.F 0xaa804 W_aa804.
Proof. vm_refl. Qed.
Lemma D_aa804 : CTabKU.D W_aa804 (Op ALU_OR 12 12 13).
Proof. vm_refl. Qed.
Definition W_aa808 : bv 32 := 0x01f00693.
Lemma F_aa808 : CTabKU.F 0xaa808 W_aa808.
Proof. vm_refl. Qed.
Lemma D_aa808 : CTabKU.D W_aa808 (OpImm ALU_ADD 13 0 31).
Proof. vm_refl. Qed.
Definition W_aa80c : bv 32 := 0x00c5b023.
Lemma F_aa80c : CTabKU.F 0xaa80c W_aa80c.
Proof. vm_refl. Qed.
Lemma D_aa80c : CTabKU.D W_aa80c (Store SZ8 11 12 0).
Proof. vm_refl. Qed.
Definition W_aa810 : bv 32 := 0x00c5b423.
Lemma F_aa810 : CTabKU.F 0xaa810 W_aa810.
Proof. vm_refl. Qed.
Lemma D_aa810 : CTabKU.D W_aa810 (Store SZ8 11 12 8).
Proof. vm_refl. Qed.
Definition W_aa814 : bv 32 := 0x00c5b823.
Lemma F_aa814 : CTabKU.F 0xaa814 W_aa814.
Proof. vm_refl. Qed.
Lemma D_aa814 : CTabKU.D W_aa814 (Store SZ8 11 12 16).
Proof. vm_refl. Qed.
Definition W_aa818 : bv 32 := 0x00c5bc23.
Lemma F_aa818 : CTabKU.F 0xaa818 W_aa818.
Proof. vm_refl. Qed.
Lemma D_aa818 : CTabKU.D W_aa818 (Store SZ8 11 12 24).
Proof. vm_refl. Qed.
Definition W_aa81c : bv 32 := 0xfe070713.
Lemma F_aa81c : CTabKU.F 0xaa81c W_aa81c.
Proof. vm_refl. Qed.
Lemma D_aa81c : CTabKU.D W_aa81c (OpImm ALU_ADD 14 14 4064).
Proof. vm_refl. Qed.
Definition W_aa820 : bv 32 := 0x02058593.
Lemma F_aa820 : CTabKU.F 0xaa820 W_aa820.
Proof. vm_refl. Qed.
Lemma D_aa820 : CTabKU.D W_aa820 (OpImm ALU_ADD 11 11 32).
Proof. vm_refl. Qed.
Definition W_aa824 : bv 32 := 0xfee6e4e3.
Lemma F_aa824 : CTabKU.F 0xaa824 W_aa824.
Proof. vm_refl. Qed.
Lemma D_aa824 : CTabKU.D W_aa824 (Branch BC_LTU 13 14 8168).
Proof. vm_refl. Qed.
Definition W_aa828 : bv 32 := 0x00008067.
Lemma F_aa828 : CTabKU.F 0xaa828 W_aa828.
Proof. vm_refl. Qed.
Lemma D_aa828 : CTabKU.D W_aa828 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_aac18 : bv 32 := 0x00757593.
Lemma F_aac18 : CTabKU.F 0xaac18 W_aac18.
Proof. vm_refl. Qed.
Lemma D_aac18 : CTabKU.D W_aac18 (OpImm ALU_AND 11 10 7).
Proof. vm_refl. Qed.
Definition W_aac1c : bv 32 := 0x00050613.
Lemma F_aac1c : CTabKU.F 0xaac1c W_aac1c.
Proof. vm_refl. Qed.
Lemma D_aac1c : CTabKU.D W_aac1c (OpImm ALU_ADD 12 10 0).
Proof. vm_refl. Qed.
Definition W_aac20 : bv 32 := 0x02058a63.
Lemma F_aac20 : CTabKU.F 0xaac20 W_aac20.
Proof. vm_refl. Qed.
Lemma D_aac20 : CTabKU.D W_aac20 (Branch BC_EQ 11 0 52).
Proof. vm_refl. Qed.
Definition W_aac24 : bv 32 := 0x00054583.
Lemma F_aac24 : CTabKU.F 0xaac24 W_aac24.
Proof. vm_refl. Qed.
Lemma D_aac24 : CTabKU.D W_aac24 (Load SZ1 false 11 10 0).
Proof. vm_refl. Qed.
Definition W_aac28 : bv 32 := 0x06058c63.
Lemma F_aac28 : CTabKU.F 0xaac28 W_aac28.
Proof. vm_refl. Qed.
Lemma D_aac28 : CTabKU.D W_aac28 (Branch BC_EQ 11 0 120).
Proof. vm_refl. Qed.
Definition W_aac2c : bv 32 := 0x00150613.
Lemma F_aac2c : CTabKU.F 0xaac2c W_aac2c.
Proof. vm_refl. Qed.
Lemma D_aac2c : CTabKU.D W_aac2c (OpImm ALU_ADD 12 10 1).
Proof. vm_refl. Qed.
Definition W_aac30 : bv 32 := 0x00050593.
Lemma F_aac30 : CTabKU.F 0xaac30 W_aac30.
Proof. vm_refl. Qed.
Lemma D_aac30 : CTabKU.D W_aac30 (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_aac34 : bv 32 := 0x00158693.
Lemma F_aac34 : CTabKU.F 0xaac34 W_aac34.
Proof. vm_refl. Qed.
Lemma D_aac34 : CTabKU.D W_aac34 (OpImm ALU_ADD 13 11 1).
Proof. vm_refl. Qed.
Definition W_aac38 : bv 32 := 0x0076f693.
Lemma F_aac38 : CTabKU.F 0xaac38 W_aac38.
Proof. vm_refl. Qed.
Lemma D_aac38 : CTabKU.D W_aac38 (OpImm ALU_AND 13 13 7).
Proof. vm_refl. Qed.
Definition W_aac3c : bv 32 := 0x00068c63.
Lemma F_aac3c : CTabKU.F 0xaac3c W_aac3c.
Proof. vm_refl. Qed.
Lemma D_aac3c : CTabKU.D W_aac3c (Branch BC_EQ 13 0 24).
Proof. vm_refl. Qed.
Definition W_aac40 : bv 32 := 0x00064683.
Lemma F_aac40 : CTabKU.F 0xaac40 W_aac40.
Proof. vm_refl. Qed.
Lemma D_aac40 : CTabKU.D W_aac40 (Load SZ1 false 13 12 0).
Proof. vm_refl. Qed.
Definition W_aac44 : bv 32 := 0x00160613.
Lemma F_aac44 : CTabKU.F 0xaac44 W_aac44.
Proof. vm_refl. Qed.
Lemma D_aac44 : CTabKU.D W_aac44 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_aac48 : bv 32 := 0x00158593.
Lemma F_aac48 : CTabKU.F 0xaac48 W_aac48.
Proof. vm_refl. Qed.
Lemma D_aac48 : CTabKU.D W_aac48 (OpImm ALU_ADD 11 11 1).
Proof. vm_refl. Qed.
Definition W_aac4c : bv 32 := 0xfe0694e3.
Lemma F_aac4c : CTabKU.F 0xaac4c W_aac4c.
Proof. vm_refl. Qed.
Lemma D_aac4c : CTabKU.D W_aac4c (Branch BC_NE 13 0 8168).
Proof. vm_refl. Qed.
Definition W_aac50 : bv 32 := 0x0480006f.
Lemma F_aac50 : CTabKU.F 0xaac50 W_aac50.
Proof. vm_refl. Qed.
Lemma D_aac50 : CTabKU.D W_aac50 (Jal 0 72).
Proof. vm_refl. Qed.
Definition W_aac54 : bv 32 := 0xfff69597.
Lemma F_aac54 : CTabKU.F 0xaac54 W_aac54.
Proof. vm_refl. Qed.
Lemma D_aac54 : CTabKU.D W_aac54 (Auipc 11 1048425).
Proof. vm_refl. Qed.
Definition W_aac58 : bv 32 := 0xfff69717.
Lemma F_aac58 : CTabKU.F 0xaac58 W_aac58.
Proof. vm_refl. Qed.
Lemma D_aac58 : CTabKU.D W_aac58 (Auipc 14 1048425).
Proof. vm_refl. Qed.
Definition W_aac5c : bv 32 := 0xe545b683.
Lemma F_aac5c : CTabKU.F 0xaac5c W_aac5c.
Proof. vm_refl. Qed.
Lemma D_aac5c : CTabKU.D W_aac5c (Load SZ8 true 13 11 3668).
Proof. vm_refl. Qed.
Definition W_aac60 : bv 32 := 0xe4073703.
Lemma F_aac60 : CTabKU.F 0xaac60 W_aac60.
Proof. vm_refl. Qed.
Lemma D_aac60 : CTabKU.D W_aac60 (Load SZ8 true 14 14 3648).
Proof. vm_refl. Qed.
Definition W_aac64 : bv 32 := 0xff760593.
Lemma F_aac64 : CTabKU.F 0xaac64 W_aac64.
Proof. vm_refl. Qed.
Lemma D_aac64 : CTabKU.D W_aac64 (OpImm ALU_ADD 11 12 4087).
Proof. vm_refl. Qed.
Definition W_aac68 : bv 32 := 0xff860613.
Lemma F_aac68 : CTabKU.F 0xaac68 W_aac68.
Proof. vm_refl. Qed.
Lemma D_aac68 : CTabKU.D W_aac68 (OpImm ALU_ADD 12 12 4088).
Proof. vm_refl. Qed.
Definition W_aac6c : bv 32 := 0x00863783.
Lemma F_aac6c : CTabKU.F 0xaac6c W_aac6c.
Proof. vm_refl. Qed.
Lemma D_aac6c : CTabKU.D W_aac6c (Load SZ8 true 15 12 8).
Proof. vm_refl. Qed.
Definition W_aac70 : bv 32 := 0x00860613.
Lemma F_aac70 : CTabKU.F 0xaac70 W_aac70.
Proof. vm_refl. Qed.
Lemma D_aac70 : CTabKU.D W_aac70 (OpImm ALU_ADD 12 12 8).
Proof. vm_refl. Qed.
Definition W_aac74 : bv 32 := 0x40f68833.
Lemma F_aac74 : CTabKU.F 0xaac74 W_aac74.
Proof. vm_refl. Qed.
Lemma D_aac74 : CTabKU.D W_aac74 (Op ALU_SUB 16 13 15).
Proof. vm_refl. Qed.
Definition W_aac78 : bv 32 := 0x00f867b3.
Lemma F_aac78 : CTabKU.F 0xaac78 W_aac78.
Proof. vm_refl. Qed.
Lemma D_aac78 : CTabKU.D W_aac78 (Op ALU_OR 15 16 15).
Proof. vm_refl. Qed.
Definition W_aac7c : bv 32 := 0x00e7f7b3.
Lemma F_aac7c : CTabKU.F 0xaac7c W_aac7c.
Proof. vm_refl. Qed.
Lemma D_aac7c : CTabKU.D W_aac7c (Op ALU_AND 15 15 14).
Proof. vm_refl. Qed.
Definition W_aac80 : bv 32 := 0x00858593.
Lemma F_aac80 : CTabKU.F 0xaac80 W_aac80.
Proof. vm_refl. Qed.
Lemma D_aac80 : CTabKU.D W_aac80 (OpImm ALU_ADD 11 11 8).
Proof. vm_refl. Qed.
Definition W_aac84 : bv 32 := 0xfee784e3.
Lemma F_aac84 : CTabKU.F 0xaac84 W_aac84.
Proof. vm_refl. Qed.
Lemma D_aac84 : CTabKU.D W_aac84 (Branch BC_EQ 15 14 8168).
Proof. vm_refl. Qed.
Definition W_aac88 : bv 32 := 0x00064683.
Lemma F_aac88 : CTabKU.F 0xaac88 W_aac88.
Proof. vm_refl. Qed.
Lemma D_aac88 : CTabKU.D W_aac88 (Load SZ1 false 13 12 0).
Proof. vm_refl. Qed.
Definition W_aac8c : bv 32 := 0x00160613.
Lemma F_aac8c : CTabKU.F 0xaac8c W_aac8c.
Proof. vm_refl. Qed.
Lemma D_aac8c : CTabKU.D W_aac8c (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_aac90 : bv 32 := 0x00158593.
Lemma F_aac90 : CTabKU.F 0xaac90 W_aac90.
Proof. vm_refl. Qed.
Lemma D_aac90 : CTabKU.D W_aac90 (OpImm ALU_ADD 11 11 1).
Proof. vm_refl. Qed.
Definition W_aac94 : bv 32 := 0xfe069ae3.
Lemma F_aac94 : CTabKU.F 0xaac94 W_aac94.
Proof. vm_refl. Qed.
Lemma D_aac94 : CTabKU.D W_aac94 (Branch BC_NE 13 0 8180).
Proof. vm_refl. Qed.
Definition W_aac98 : bv 32 := 0x40a58533.
Lemma F_aac98 : CTabKU.F 0xaac98 W_aac98.
Proof. vm_refl. Qed.
Lemma D_aac98 : CTabKU.D W_aac98 (Op ALU_SUB 10 11 10).
Proof. vm_refl. Qed.
Definition W_aac9c : bv 32 := 0x00008067.
Lemma F_aac9c : CTabKU.F 0xaac9c W_aac9c.
Proof. vm_refl. Qed.
Lemma D_aac9c : CTabKU.D W_aac9c (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_aaca0 : bv 32 := 0x40a50533.
Lemma F_aaca0 : CTabKU.F 0xaaca0 W_aaca0.
Proof. vm_refl. Qed.
Lemma D_aaca0 : CTabKU.D W_aaca0 (Op ALU_SUB 10 10 10).
Proof. vm_refl. Qed.
Definition W_aaca4 : bv 32 := 0x00008067.
Lemma F_aaca4 : CTabKU.F 0xaaca4 W_aaca4.
Proof. vm_refl. Qed.
Lemma D_aaca4 : CTabKU.D W_aaca4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_aaca8 : bv 32 := 0xfe010113.
Lemma F_aaca8 : CTabKU.F 0xaaca8 W_aaca8.
Proof. vm_refl. Qed.
Lemma D_aaca8 : CTabKU.D W_aaca8 (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_aacac : bv 32 := 0x00113c23.
Lemma F_aacac : CTabKU.F 0xaacac W_aacac.
Proof. vm_refl. Qed.
Lemma D_aacac : CTabKU.D W_aacac (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_aacb0 : bv 32 := 0x00813823.
Lemma F_aacb0 : CTabKU.F 0xaacb0 W_aacb0.
Proof. vm_refl. Qed.
Lemma D_aacb0 : CTabKU.D W_aacb0 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_aacb4 : bv 32 := 0x00913423.
Lemma F_aacb4 : CTabKU.F 0xaacb4 W_aacb4.
Proof. vm_refl. Qed.
Lemma D_aacb4 : CTabKU.D W_aacb4 (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_aacb8 : bv 32 := 0x00058413.
Lemma F_aacb8 : CTabKU.F 0xaacb8 W_aacb8.
Proof. vm_refl. Qed.
Lemma D_aacb8 : CTabKU.D W_aacb8 (OpImm ALU_ADD 8 11 0).
Proof. vm_refl. Qed.
Definition W_aacbc : bv 32 := 0x00050493.
Lemma F_aacbc : CTabKU.F 0xaacbc W_aacbc.
Proof. vm_refl. Qed.
Lemma D_aacbc : CTabKU.D W_aacbc (OpImm ALU_ADD 9 10 0).
Proof. vm_refl. Qed.
Definition W_aacc0 : bv 32 := 0x00000593.
Lemma F_aacc0 : CTabKU.F 0xaacc0 W_aacc0.
Proof. vm_refl. Qed.
Lemma D_aacc0 : CTabKU.D W_aacc0 (OpImm ALU_ADD 11 0 0).
Proof. vm_refl. Qed.
Definition W_aacc4 : bv 32 := 0x00040613.
Lemma F_aacc4 : CTabKU.F 0xaacc4 W_aacc4.
Proof. vm_refl. Qed.
Lemma D_aacc4 : CTabKU.D W_aacc4 (OpImm ALU_ADD 12 8 0).
Proof. vm_refl. Qed.
Definition W_aacc8 : bv 32 := 0xbf0ff0ef.
Lemma F_aacc8 : CTabKU.F 0xaacc8 W_aacc8.
Proof. vm_refl. Qed.
Lemma D_aacc8 : CTabKU.D W_aacc8 (Jal 1 2094064).
Proof. vm_refl. Qed.
Definition W_aaccc : bv 32 := 0x00050463.
Lemma F_aaccc : CTabKU.F 0xaaccc W_aaccc.
Proof. vm_refl. Qed.
Lemma D_aaccc : CTabKU.D W_aaccc (Branch BC_EQ 10 0 8).
Proof. vm_refl. Qed.
Definition W_aacd0 : bv 32 := 0x40950433.
Lemma F_aacd0 : CTabKU.F 0xaacd0 W_aacd0.
Proof. vm_refl. Qed.
Lemma D_aacd0 : CTabKU.D W_aacd0 (Op ALU_SUB 8 10 9).
Proof. vm_refl. Qed.
Definition W_aacd4 : bv 32 := 0x00040513.
Lemma F_aacd4 : CTabKU.F 0xaacd4 W_aacd4.
Proof. vm_refl. Qed.
Lemma D_aacd4 : CTabKU.D W_aacd4 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_aacd8 : bv 32 := 0x01813083.
Lemma F_aacd8 : CTabKU.F 0xaacd8 W_aacd8.
Proof. vm_refl. Qed.
Lemma D_aacd8 : CTabKU.D W_aacd8 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_aacdc : bv 32 := 0x01013403.
Lemma F_aacdc : CTabKU.F 0xaacdc W_aacdc.
Proof. vm_refl. Qed.
Lemma D_aacdc : CTabKU.D W_aacdc (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_aace0 : bv 32 := 0x00813483.
Lemma F_aace0 : CTabKU.F 0xaace0 W_aace0.
Proof. vm_refl. Qed.
Lemma D_aace0 : CTabKU.D W_aace0 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_aace4 : bv 32 := 0x02010113.
Lemma F_aace4 : CTabKU.F 0xaace4 W_aace4.
Proof. vm_refl. Qed.
Lemma D_aace4 : CTabKU.D W_aace4 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_aace8 : bv 32 := 0x00008067.
Lemma F_aace8 : CTabKU.F 0xaace8 W_aace8.
Proof. vm_refl. Qed.
Lemma D_aace8 : CTabKU.D W_aace8 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_aae44 : bv 32 := 0x0003e597.
Lemma F_aae44 : CTabKU.F 0xaae44 W_aae44.
Proof. vm_refl. Qed.
Lemma D_aae44 : CTabKU.D W_aae44 (Auipc 11 62).
Proof. vm_refl. Qed.
Definition W_aae48 : bv 32 := 0x0ff58683.
Lemma F_aae48 : CTabKU.F 0xaae48 W_aae48.
Proof. vm_refl. Qed.
Lemma D_aae48 : CTabKU.D W_aae48 (Load SZ1 true 13 11 255).
Proof. vm_refl. Qed.
Definition W_aae4c : bv 32 := 0x1e068863.
Lemma F_aae4c : CTabKU.F 0xaae4c W_aae4c.
Proof. vm_refl. Qed.
Lemma D_aae4c : CTabKU.D W_aae4c (Branch BC_EQ 13 0 496).
Proof. vm_refl. Qed.
Definition W_ab03c : bv 32 := 0x00008067.
Lemma F_ab03c : CTabKU.F 0xab03c W_ab03c.
Proof. vm_refl. Qed.
Lemma D_ab03c : CTabKU.D W_ab03c (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_ab140 : bv 32 := 0x00050893.
Lemma F_ab140 : CTabKU.F 0xab140 W_ab140.
Proof. vm_refl. Qed.
Lemma D_ab140 : CTabKU.D W_ab140 (OpImm ALU_ADD 17 10 0).
Proof. vm_refl. Qed.
Definition W_ab144 : bv 32 := 0x00058513.
Lemma F_ab144 : CTabKU.F 0xab144 W_ab144.
Proof. vm_refl. Qed.
Lemma D_ab144 : CTabKU.D W_ab144 (OpImm ALU_ADD 10 11 0).
Proof. vm_refl. Qed.
Definition W_ab148 : bv 32 := 0x00060593.
Lemma F_ab148 : CTabKU.F 0xab148 W_ab148.
Proof. vm_refl. Qed.
Lemma D_ab148 : CTabKU.D W_ab148 (OpImm ALU_ADD 11 12 0).
Proof. vm_refl. Qed.
Definition W_ab14c : bv 32 := 0x00068613.
Lemma F_ab14c : CTabKU.F 0xab14c W_ab14c.
Proof. vm_refl. Qed.
Lemma D_ab14c : CTabKU.D W_ab14c (OpImm ALU_ADD 12 13 0).
Proof. vm_refl. Qed.
Definition W_ab150 : bv 32 := 0x00070693.
Lemma F_ab150 : CTabKU.F 0xab150 W_ab150.
Proof. vm_refl. Qed.
Lemma D_ab150 : CTabKU.D W_ab150 (OpImm ALU_ADD 13 14 0).
Proof. vm_refl. Qed.
Definition W_ab154 : bv 32 := 0x00078713.
Lemma F_ab154 : CTabKU.F 0xab154 W_ab154.
Proof. vm_refl. Qed.
Lemma D_ab154 : CTabKU.D W_ab154 (OpImm ALU_ADD 14 15 0).
Proof. vm_refl. Qed.
Definition W_ab158 : bv 32 := 0x00080793.
Lemma F_ab158 : CTabKU.F 0xab158 W_ab158.
Proof. vm_refl. Qed.
Lemma D_ab158 : CTabKU.D W_ab158 (OpImm ALU_ADD 15 16 0).
Proof. vm_refl. Qed.
Definition W_ab160 : bv 32 := 0x00008067.
Lemma F_ab160 : CTabKU.F 0xab160 W_ab160.
Proof. vm_refl. Qed.
Lemma D_ab160 : CTabKU.D W_ab160 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_ab164 : bv 32 := 0xfddff06f.
Lemma F_ab164 : CTabKU.F 0xab164 W_ab164.
Proof. vm_refl. Qed.
Lemma D_ab164 : CTabKU.D W_ab164 (Jal 0 2097116).
Proof. vm_refl. Qed.
