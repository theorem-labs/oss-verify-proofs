(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation PSEGS := ImgP.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9835c : bv 32 := 0x1c050463.
Lemma F_9835c : fetch_word PSEGS (0x9835c : word) = Some W_9835c.
Proof. vm_refl. Qed.
Lemma D_9835c : decode_any W_9835c = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98360 : bv 32 := 0xfd010113.
Lemma F_98360 : fetch_word PSEGS (0x98360 : word) = Some W_98360.
Proof. vm_refl. Qed.
Lemma D_98360 : decode_any W_98360 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98364 : bv 32 := 0x02113423.
Lemma F_98364 : fetch_word PSEGS (0x98364 : word) = Some W_98364.
Proof. vm_refl. Qed.
Lemma D_98364 : decode_any W_98364 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98368 : bv 32 := 0x02813023.
Lemma F_98368 : fetch_word PSEGS (0x98368 : word) = Some W_98368.
Proof. vm_refl. Qed.
Lemma D_98368 : decode_any W_98368 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9836c : bv 32 := 0x00913c23.
Lemma F_9836c : fetch_word PSEGS (0x9836c : word) = Some W_9836c.
Proof. vm_refl. Qed.
Lemma D_9836c : decode_any W_9836c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98370 : bv 32 := 0x01213823.
Lemma F_98370 : fetch_word PSEGS (0x98370 : word) = Some W_98370.
Proof. vm_refl. Qed.
Lemma D_98370 : decode_any W_98370 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98374 : bv 32 := 0x01313423.
Lemma F_98374 : fetch_word PSEGS (0x98374 : word) = Some W_98374.
Proof. vm_refl. Qed.
Lemma D_98374 : decode_any W_98374 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98378 : bv 32 := 0x00050493.
Lemma F_98378 : fetch_word PSEGS (0x98378 : word) = Some W_98378.
Proof. vm_refl. Qed.
Lemma D_98378 : decode_any W_98378 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9837c : bv 32 := 0x1ac000ef.
Lemma F_9837c : fetch_word PSEGS (0x9837c : word) = Some W_9837c.
Proof. vm_refl. Qed.
Lemma D_9837c : decode_any W_9837c = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98380 : bv 32 := 0x02053583.
Lemma F_98380 : fetch_word PSEGS (0x98380 : word) = Some W_98380.
Proof. vm_refl. Qed.
Lemma D_98380 : decode_any W_98380 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98384 : bv 32 := 0xffd4c683.
Lemma F_98384 : fetch_word PSEGS (0x98384 : word) = Some W_98384.
Proof. vm_refl. Qed.
Lemma D_98384 : decode_any W_98384 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98388 : bv 32 := 0x00c5d613.
Lemma F_98388 : fetch_word PSEGS (0x98388 : word) = Some W_98388.
Proof. vm_refl. Qed.
Lemma D_98388 : decode_any W_98388 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9838c : bv 32 := 0x01f6f413.
Lemma F_9838c : fetch_word PSEGS (0x9838c : word) = Some W_9838c.
Proof. vm_refl. Qed.
Lemma D_9838c : decode_any W_9838c = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98390 : bv 32 := 0x00060e63.
Lemma F_98390 : fetch_word PSEGS (0x98390 : word) = Some W_98390.
Proof. vm_refl. Qed.
Lemma D_98390 : decode_any W_98390 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98394 : bv 32 := 0x01f5f613.
Lemma F_98394 : fetch_word PSEGS (0x98394 : word) = Some W_98394.
Proof. vm_refl. Qed.
Lemma D_98394 : decode_any W_98394 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98398 : bv 32 := 0x00061a63.
Lemma F_98398 : fetch_word PSEGS (0x98398 : word) = Some W_98398.
Proof. vm_refl. Qed.
Lemma D_98398 : decode_any W_98398 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9839c : bv 32 := 0xfffff637.
Lemma F_9839c : fetch_word PSEGS (0x9839c : word) = Some W_9839c.
Proof. vm_refl. Qed.
Lemma D_9839c : decode_any W_9839c = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983a0 : bv 32 := 0x00c5f633.
Lemma F_983a0 : fetch_word PSEGS (0x983a0 : word) = Some W_983a0.
Proof. vm_refl. Qed.
Lemma D_983a0 : decode_any W_983a0 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983a4 : bv 32 := 0xff060613.
Lemma F_983a4 : fetch_word PSEGS (0x983a4 : word) = Some W_983a4.
Proof. vm_refl. Qed.
Lemma D_983a4 : decode_any W_983a4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983a8 : bv 32 := 0x0200006f.
Lemma F_983a8 : fetch_word PSEGS (0x983a8 : word) = Some W_983a8.
Proof. vm_refl. Qed.
Lemma D_983a8 : decode_any W_983a8 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983ac : bv 32 := 0x0055d613.
Lemma F_983ac : fetch_word PSEGS (0x983ac : word) = Some W_983ac.
Proof. vm_refl. Qed.
Lemma D_983ac : decode_any W_983ac = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983b0 : bv 32 := 0xfff83717.
Lemma F_983b0 : fetch_word PSEGS (0x983b0 : word) = Some W_983b0.
Proof. vm_refl. Qed.
Lemma D_983b0 : decode_any W_983b0 = Some (Auipc 14 1048451, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983b4 : bv 32 := 0x07e67613.
Lemma F_983b4 : fetch_word PSEGS (0x983b4 : word) = Some W_983b4.
Proof. vm_refl. Qed.
Lemma D_983b4 : decode_any W_983b4 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983b8 : bv 32 := 0x81870713.
Lemma F_983b8 : fetch_word PSEGS (0x983b8 : word) = Some W_983b8.
Proof. vm_refl. Qed.
Lemma D_983b8 : decode_any W_983b8 = Some (OpImm ALU_ADD 14 14 2072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983bc : bv 32 := 0x00c70633.
Lemma F_983bc : fetch_word PSEGS (0x983bc : word) = Some W_983bc.
Proof. vm_refl. Qed.
Lemma D_983bc : decode_any W_983bc = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983c0 : bv 32 := 0x00065603.
Lemma F_983c0 : fetch_word PSEGS (0x983c0 : word) = Some W_983c0.
Proof. vm_refl. Qed.
Lemma D_983c0 : decode_any W_983c0 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983c4 : bv 32 := 0x00461613.
Lemma F_983c4 : fetch_word PSEGS (0x983c4 : word) = Some W_983c4.
Proof. vm_refl. Qed.
Lemma D_983c4 : decode_any W_983c4 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983c8 : bv 32 := 0x01053703.
Lemma F_983c8 : fetch_word PSEGS (0x983c8 : word) = Some W_983c8.
Proof. vm_refl. Qed.
Lemma D_983c8 : decode_any W_983c8 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983cc : bv 32 := 0x028607b3.
Lemma F_983cc : fetch_word PSEGS (0x983cc : word) = Some W_983cc.
Proof. vm_refl. Qed.
Lemma D_983cc : decode_any W_983cc = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983d0 : bv 32 := 0x0a000813.
Lemma F_983d0 : fetch_word PSEGS (0x983d0 : word) = Some W_983d0.
Proof. vm_refl. Qed.
Lemma D_983d0 : decode_any W_983d0 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983d4 : bv 32 := 0x00c70633.
Lemma F_983d4 : fetch_word PSEGS (0x983d4 : word) = Some W_983d4.
Proof. vm_refl. Qed.
Lemma D_983d4 : decode_any W_983d4 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983d8 : bv 32 := 0x00f607b3.
Lemma F_983d8 : fetch_word PSEGS (0x983d8 : word) = Some W_983d8.
Proof. vm_refl. Qed.
Lemma D_983d8 : decode_any W_983d8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983dc : bv 32 := 0x00c78613.
Lemma F_983dc : fetch_word PSEGS (0x983dc : word) = Some W_983dc.
Proof. vm_refl. Qed.
Lemma D_983dc : decode_any W_983dc = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983e0 : bv 32 := 0x0056d713.
Lemma F_983e0 : fetch_word PSEGS (0x983e0 : word) = Some W_983e0.
Proof. vm_refl. Qed.
Lemma D_983e0 : decode_any W_983e0 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983e4 : bv 32 := 0x0306e663.
Lemma F_983e4 : fetch_word PSEGS (0x983e4 : word) = Some W_983e4.
Proof. vm_refl. Qed.
Lemma D_983e4 : decode_any W_983e4 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983e8 : bv 32 := 0x00500693.
Lemma F_983e8 : fetch_word PSEGS (0x983e8 : word) = Some W_983e8.
Proof. vm_refl. Qed.
Lemma D_983e8 : decode_any W_983e8 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983ec : bv 32 := 0x00d70463.
Lemma F_983ec : fetch_word PSEGS (0x983ec : word) = Some W_983ec.
Proof. vm_refl. Qed.
Lemma D_983ec : decode_any W_983ec = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983f4 : bv 32 := 0x0087e703.
Lemma F_983f4 : fetch_word PSEGS (0x983f4 : word) = Some W_983f4.
Proof. vm_refl. Qed.
Lemma D_983f4 : decode_any W_983f4 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983f8 : bv 32 := 0x00400693.
Lemma F_983f8 : fetch_word PSEGS (0x983f8 : word) = Some W_983f8.
Proof. vm_refl. Qed.
Lemma D_983f8 : decode_any W_983f8 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_983fc : bv 32 := 0x00e6e463.
Lemma F_983fc : fetch_word PSEGS (0x983fc : word) = Some W_983fc.
Proof. vm_refl. Qed.
Lemma D_983fc : decode_any W_983fc = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98404 : bv 32 := 0x0077c683.
Lemma F_98404 : fetch_word PSEGS (0x98404 : word) = Some W_98404.
Proof. vm_refl. Qed.
Lemma D_98404 : decode_any W_98404 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98408 : bv 32 := 0x00068463.
Lemma F_98408 : fetch_word PSEGS (0x98408 : word) = Some W_98408.
Proof. vm_refl. Qed.
Lemma D_98408 : decode_any W_98408 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98410 : bv 32 := 0x409606b3.
Lemma F_98410 : fetch_word PSEGS (0x98410 : word) = Some W_98410.
Proof. vm_refl. Qed.
Lemma D_98410 : decode_any W_98410 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98414 : bv 32 := 0x00e6f463.
Lemma F_98414 : fetch_word PSEGS (0x98414 : word) = Some W_98414.
Proof. vm_refl. Qed.
Lemma D_98414 : decode_any W_98414 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9841c : bv 32 := 0x40e606b3.
Lemma F_9841c : fetch_word PSEGS (0x9841c : word) = Some W_9841c.
Proof. vm_refl. Qed.
Lemma D_9841c : decode_any W_9841c = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98420 : bv 32 := 0x0006c683.
Lemma F_98420 : fetch_word PSEGS (0x98420 : word) = Some W_98420.
Proof. vm_refl. Qed.
Lemma D_98420 : decode_any W_98420 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98424 : bv 32 := 0x00068463.
Lemma F_98424 : fetch_word PSEGS (0x98424 : word) = Some W_98424.
Proof. vm_refl. Qed.
Lemma D_98424 : decode_any W_98424 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9842c : bv 32 := 0x00064603.
Lemma F_9842c : fetch_word PSEGS (0x9842c : word) = Some W_9842c.
Proof. vm_refl. Qed.
Lemma D_9842c : decode_any W_9842c = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98430 : bv 32 := 0x00060463.
Lemma F_98430 : fetch_word PSEGS (0x98430 : word) = Some W_98430.
Proof. vm_refl. Qed.
Lemma D_98430 : decode_any W_98430 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98528 : bv 32 := 0x00f57593.
Lemma F_98528 : fetch_word PSEGS (0x98528 : word) = Some W_98528.
Proof. vm_refl. Qed.
Lemma D_98528 : decode_any W_98528 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9852c : bv 32 := 0x00058463.
Lemma F_9852c : fetch_word PSEGS (0x9852c : word) = Some W_9852c.
Proof. vm_refl. Qed.
Lemma D_9852c : decode_any W_9852c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98534 : bv 32 := 0xffc54603.
Lemma F_98534 : fetch_word PSEGS (0x98534 : word) = Some W_98534.
Proof. vm_refl. Qed.
Lemma D_98534 : decode_any W_98534 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98538 : bv 32 := 0xffd54683.
Lemma F_98538 : fetch_word PSEGS (0x98538 : word) = Some W_98538.
Proof. vm_refl. Qed.
Lemma D_98538 : decode_any W_98538 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9853c : bv 32 := 0xffe55583.
Lemma F_9853c : fetch_word PSEGS (0x9853c : word) = Some W_9853c.
Proof. vm_refl. Qed.
Lemma D_9853c : decode_any W_9853c = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98540 : bv 32 := 0x00060e63.
Lemma F_98540 : fetch_word PSEGS (0x98540 : word) = Some W_98540.
Proof. vm_refl. Qed.
Lemma D_98540 : decode_any W_98540 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9855c : bv 32 := 0x00459613.
Lemma F_9855c : fetch_word PSEGS (0x9855c : word) = Some W_9855c.
Proof. vm_refl. Qed.
Lemma D_9855c : decode_any W_9855c = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98560 : bv 32 := 0x40c50633.
Lemma F_98560 : fetch_word PSEGS (0x98560 : word) = Some W_98560.
Proof. vm_refl. Qed.
Lemma D_98560 : decode_any W_98560 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98564 : bv 32 := 0xff063503.
Lemma F_98564 : fetch_word PSEGS (0x98564 : word) = Some W_98564.
Proof. vm_refl. Qed.
Lemma D_98564 : decode_any W_98564 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98568 : bv 32 := 0x01053703.
Lemma F_98568 : fetch_word PSEGS (0x98568 : word) = Some W_98568.
Proof. vm_refl. Qed.
Lemma D_98568 : decode_any W_98568 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9856c : bv 32 := 0xff060613.
Lemma F_9856c : fetch_word PSEGS (0x9856c : word) = Some W_9856c.
Proof. vm_refl. Qed.
Lemma D_9856c : decode_any W_9856c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98570 : bv 32 := 0x01f6f693.
Lemma F_98570 : fetch_word PSEGS (0x98570 : word) = Some W_98570.
Proof. vm_refl. Qed.
Lemma D_98570 : decode_any W_98570 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98574 : bv 32 := 0x00c70463.
Lemma F_98574 : fetch_word PSEGS (0x98574 : word) = Some W_98574.
Proof. vm_refl. Qed.
Lemma D_98574 : decode_any W_98574 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9857c : bv 32 := 0x02053603.
Lemma F_9857c : fetch_word PSEGS (0x9857c : word) = Some W_9857c.
Proof. vm_refl. Qed.
Lemma D_9857c : decode_any W_9857c = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98580 : bv 32 := 0x01f67713.
Lemma F_98580 : fetch_word PSEGS (0x98580 : word) = Some W_98580.
Proof. vm_refl. Qed.
Lemma D_98580 : decode_any W_98580 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98584 : bv 32 := 0x00d77463.
Lemma F_98584 : fetch_word PSEGS (0x98584 : word) = Some W_98584.
Proof. vm_refl. Qed.
Lemma D_98584 : decode_any W_98584 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9858c : bv 32 := 0x01852783.
Lemma F_9858c : fetch_word PSEGS (0x9858c : word) = Some W_9858c.
Proof. vm_refl. Qed.
Lemma D_9858c : decode_any W_9858c = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98590 : bv 32 := 0x00100713.
Lemma F_98590 : fetch_word PSEGS (0x98590 : word) = Some W_98590.
Proof. vm_refl. Qed.
Lemma D_98590 : decode_any W_98590 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98594 : bv 32 := 0x00d7173b.
Lemma F_98594 : fetch_word PSEGS (0x98594 : word) = Some W_98594.
Proof. vm_refl. Qed.
Lemma D_98594 : decode_any W_98594 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98598 : bv 32 := 0x00e7f7b3.
Lemma F_98598 : fetch_word PSEGS (0x98598 : word) = Some W_98598.
Proof. vm_refl. Qed.
Lemma D_98598 : decode_any W_98598 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9859c : bv 32 := 0x00078463.
Lemma F_9859c : fetch_word PSEGS (0x9859c : word) = Some W_9859c.
Proof. vm_refl. Qed.
Lemma D_9859c : decode_any W_9859c = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985a4 : bv 32 := 0x01c52783.
Lemma F_985a4 : fetch_word PSEGS (0x985a4 : word) = Some W_985a4.
Proof. vm_refl. Qed.
Lemma D_985a4 : decode_any W_985a4 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985a8 : bv 32 := 0x00e7f733.
Lemma F_985a8 : fetch_word PSEGS (0x985a8 : word) = Some W_985a8.
Proof. vm_refl. Qed.
Lemma D_985a8 : decode_any W_985a8 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985ac : bv 32 := 0x00070463.
Lemma F_985ac : fetch_word PSEGS (0x985ac : word) = Some W_985ac.
Proof. vm_refl. Qed.
Lemma D_985ac : decode_any W_985ac = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985b4 : bv 32 := 0xfffff737.
Lemma F_985b4 : fetch_word PSEGS (0x985b4 : word) = Some W_985b4.
Proof. vm_refl. Qed.
Lemma D_985b4 : decode_any W_985b4 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985b8 : bv 32 := 0x0004c797.
Lemma F_985b8 : fetch_word PSEGS (0x985b8 : word) = Some W_985b8.
Proof. vm_refl. Qed.
Lemma D_985b8 : decode_any W_985b8 = Some (Auipc 15 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985bc : bv 32 := 0x00e57733.
Lemma F_985bc : fetch_word PSEGS (0x985bc : word) = Some W_985bc.
Proof. vm_refl. Qed.
Lemma D_985bc : decode_any W_985bc = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985c0 : bv 32 := 0x00073703.
Lemma F_985c0 : fetch_word PSEGS (0x985c0 : word) = Some W_985c0.
Proof. vm_refl. Qed.
Lemma D_985c0 : decode_any W_985c0 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985c4 : bv 32 := 0x7707b783.
Lemma F_985c4 : fetch_word PSEGS (0x985c4 : word) = Some W_985c4.
Proof. vm_refl. Qed.
Lemma D_985c4 : decode_any W_985c4 = Some (Load SZ8 true 15 15 1904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985c8 : bv 32 := 0x00f70463.
Lemma F_985c8 : fetch_word PSEGS (0x985c8 : word) = Some W_985c8.
Proof. vm_refl. Qed.
Lemma D_985c8 : decode_any W_985c8 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985d0 : bv 32 := 0x03461713.
Lemma F_985d0 : fetch_word PSEGS (0x985d0 : word) = Some W_985d0.
Proof. vm_refl. Qed.
Lemma D_985d0 : decode_any W_985d0 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985d4 : bv 32 := 0x03a75713.
Lemma F_985d4 : fetch_word PSEGS (0x985d4 : word) = Some W_985d4.
Proof. vm_refl. Qed.
Lemma D_985d4 : decode_any W_985d4 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985d8 : bv 32 := 0x02f00793.
Lemma F_985d8 : fetch_word PSEGS (0x985d8 : word) = Some W_985d8.
Proof. vm_refl. Qed.
Lemma D_985d8 : decode_any W_985d8 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985dc : bv 32 := 0x02e7ea63.
Lemma F_985dc : fetch_word PSEGS (0x985dc : word) = Some W_985dc.
Proof. vm_refl. Qed.
Lemma D_985dc : decode_any W_985dc = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985e0 : bv 32 := 0x00171713.
Lemma F_985e0 : fetch_word PSEGS (0x985e0 : word) = Some W_985e0.
Proof. vm_refl. Qed.
Lemma D_985e0 : decode_any W_985e0 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985e4 : bv 32 := 0xfff82797.
Lemma F_985e4 : fetch_word PSEGS (0x985e4 : word) = Some W_985e4.
Proof. vm_refl. Qed.
Lemma D_985e4 : decode_any W_985e4 = Some (Auipc 15 1048450, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985e8 : bv 32 := 0x5e478793.
Lemma F_985e8 : fetch_word PSEGS (0x985e8 : word) = Some W_985e8.
Proof. vm_refl. Qed.
Lemma D_985e8 : decode_any W_985e8 = Some (OpImm ALU_ADD 15 15 1508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985ec : bv 32 := 0x00e78733.
Lemma F_985ec : fetch_word PSEGS (0x985ec : word) = Some W_985ec.
Proof. vm_refl. Qed.
Lemma D_985ec : decode_any W_985ec = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985f0 : bv 32 := 0x00075703.
Lemma F_985f0 : fetch_word PSEGS (0x985f0 : word) = Some W_985f0.
Proof. vm_refl. Qed.
Lemma D_985f0 : decode_any W_985f0 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985f4 : bv 32 := 0x02d707b3.
Lemma F_985f4 : fetch_word PSEGS (0x985f4 : word) = Some W_985f4.
Proof. vm_refl. Qed.
Lemma D_985f4 : decode_any W_985f4 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_985f8 : bv 32 := 0x00f5f463.
Lemma F_985f8 : fetch_word PSEGS (0x985f8 : word) = Some W_985f8.
Proof. vm_refl. Qed.
Lemma D_985f8 : decode_any W_985f8 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98600 : bv 32 := 0x00168693.
Lemma F_98600 : fetch_word PSEGS (0x98600 : word) = Some W_98600.
Proof. vm_refl. Qed.
Lemma D_98600 : decode_any W_98600 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98604 : bv 32 := 0x02e686b3.
Lemma F_98604 : fetch_word PSEGS (0x98604 : word) = Some W_98604.
Proof. vm_refl. Qed.
Lemma D_98604 : decode_any W_98604 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98608 : bv 32 := 0x00d5f863.
Lemma F_98608 : fetch_word PSEGS (0x98608 : word) = Some W_98608.
Proof. vm_refl. Qed.
Lemma D_98608 : decode_any W_98608 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9860c : bv 32 := 0x0100006f.
Lemma F_9860c : fetch_word PSEGS (0x9860c : word) = Some W_9860c.
Proof. vm_refl. Qed.
Lemma D_9860c : decode_any W_9860c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98610 : bv 32 := 0x03f00693.
Lemma F_98610 : fetch_word PSEGS (0x98610 : word) = Some W_98610.
Proof. vm_refl. Qed.
Lemma D_98610 : decode_any W_98610 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98614 : bv 32 := 0x00d70463.
Lemma F_98614 : fetch_word PSEGS (0x98614 : word) = Some W_98614.
Proof. vm_refl. Qed.
Lemma D_98614 : decode_any W_98614 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9861c : bv 32 := 0x00c65613.
Lemma F_9861c : fetch_word PSEGS (0x9861c : word) = Some W_9861c.
Proof. vm_refl. Qed.
Lemma D_9861c : decode_any W_9861c = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98620 : bv 32 := 0x00060a63.
Lemma F_98620 : fetch_word PSEGS (0x98620 : word) = Some W_98620.
Proof. vm_refl. Qed.
Lemma D_98620 : decode_any W_98620 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98624 : bv 32 := 0x00861613.
Lemma F_98624 : fetch_word PSEGS (0x98624 : word) = Some W_98624.
Proof. vm_refl. Qed.
Lemma D_98624 : decode_any W_98624 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98628 : bv 32 := 0xfff60613.
Lemma F_98628 : fetch_word PSEGS (0x98628 : word) = Some W_98628.
Proof. vm_refl. Qed.
Lemma D_98628 : decode_any W_98628 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9862c : bv 32 := 0x00b67463.
Lemma F_9862c : fetch_word PSEGS (0x9862c : word) = Some W_9862c.
Proof. vm_refl. Qed.
Lemma D_9862c : decode_any W_9862c = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98634 : bv 32 := 0x00008067.
Lemma F_98634 : fetch_word PSEGS (0x98634 : word) = Some W_98634.
Proof. vm_refl. Qed.
Lemma D_98634 : decode_any W_98634 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989b8 : bv 32 := 0x00072503.
Lemma F_989b8 : fetch_word PSEGS (0x989b8 : word) = Some W_989b8.
Proof. vm_refl. Qed.
Lemma D_989b8 : decode_any W_989b8 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989bc : bv 32 := 0x00b56633.
Lemma F_989bc : fetch_word PSEGS (0x989bc : word) = Some W_989bc.
Proof. vm_refl. Qed.
Lemma D_989bc : decode_any W_989bc = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989c0 : bv 32 := 0x160726af.
Lemma F_989c0 : fetch_word PSEGS (0x989c0 : word) = Some W_989c0.
Proof. vm_refl. Qed.
Lemma D_989c0 : decode_any W_989c0 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989c4 : bv 32 := 0x00a69663.
Lemma F_989c4 : fetch_word PSEGS (0x989c4 : word) = Some W_989c4.
Proof. vm_refl. Qed.
Lemma D_989c4 : decode_any W_989c4 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989c8 : bv 32 := 0x1ec727af.
Lemma F_989c8 : fetch_word PSEGS (0x989c8 : word) = Some W_989c8.
Proof. vm_refl. Qed.
Lemma D_989c8 : decode_any W_989c8 = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989cc : bv 32 := 0xfe079ae3.
Lemma F_989cc : fetch_word PSEGS (0x989cc : word) = Some W_989cc.
Proof. vm_refl. Qed.
Lemma D_989cc : decode_any W_989cc = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989d0 : bv 32 := 0x0006869b.
Lemma F_989d0 : fetch_word PSEGS (0x989d0 : word) = Some W_989d0.
Proof. vm_refl. Qed.
Lemma D_989d0 : decode_any W_989d0 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_989d4 : bv 32 := 0xfea692e3.
Lemma F_989d4 : fetch_word PSEGS (0x989d4 : word) = Some W_989d4.
Proof. vm_refl. Qed.
Lemma D_989d4 : decode_any W_989d4 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a54 : bv 32 := 0x00000493.
Lemma F_98a54 : fetch_word PSEGS (0x98a54 : word) = Some W_98a54.
Proof. vm_refl. Qed.
Lemma D_98a54 : decode_any W_98a54 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a58 : bv 32 := 0x41c655b7.
Lemma F_98a58 : fetch_word PSEGS (0x98a58 : word) = Some W_98a58.
Proof. vm_refl. Qed.
Lemma D_98a58 : decode_any W_98a58 = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a5c : bv 32 := 0x00010613.
Lemma F_98a5c : fetch_word PSEGS (0x98a5c : word) = Some W_98a5c.
Proof. vm_refl. Qed.
Lemma D_98a5c : decode_any W_98a5c = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a60 : bv 32 := 0x00843503.
Lemma F_98a60 : fetch_word PSEGS (0x98a60 : word) = Some W_98a60.
Proof. vm_refl. Qed.
Lemma D_98a60 : decode_any W_98a60 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a64 : bv 32 := 0xe6d5859b.
Lemma F_98a64 : fetch_word PSEGS (0x98a64 : word) = Some W_98a64.
Proof. vm_refl. Qed.
Lemma D_98a64 : decode_any W_98a64 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a68 : bv 32 := 0x02b605b3.
Lemma F_98a68 : fetch_word PSEGS (0x98a68 : word) = Some W_98a68.
Proof. vm_refl. Qed.
Lemma D_98a68 : decode_any W_98a68 = Some (Mul M_MUL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a6c : bv 32 := 0x00b13023.
Lemma F_98a6c : fetch_word PSEGS (0x98a6c : word) = Some W_98a6c.
Proof. vm_refl. Qed.
Lemma D_98a6c : decode_any W_98a6c = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a70 : bv 32 := 0x01900a13.
Lemma F_98a70 : fetch_word PSEGS (0x98a70 : word) = Some W_98a70.
Proof. vm_refl. Qed.
Lemma D_98a70 : decode_any W_98a70 = Some (OpImm ALU_ADD 20 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a74 : bv 32 := 0x0200006f.
Lemma F_98a74 : fetch_word PSEGS (0x98a74 : word) = Some W_98a74.
Proof. vm_refl. Qed.
Lemma D_98a74 : decode_any W_98a74 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a78 : bv 32 := 0x00863583.
Lemma F_98a78 : fetch_word PSEGS (0x98a78 : word) = Some W_98a78.
Proof. vm_refl. Qed.
Lemma D_98a78 : decode_any W_98a78 = Some (Load SZ8 true 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a7c : bv 32 := 0x00858593.
Lemma F_98a7c : fetch_word PSEGS (0x98a7c : word) = Some W_98a7c.
Proof. vm_refl. Qed.
Lemma D_98a7c : decode_any W_98a7c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a80 : bv 32 := 0x00010513.
Lemma F_98a80 : fetch_word PSEGS (0x98a80 : word) = Some W_98a80.
Proof. vm_refl. Qed.
Lemma D_98a80 : decode_any W_98a80 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a84 : bv 32 := 0x00800613.
Lemma F_98a84 : fetch_word PSEGS (0x98a84 : word) = Some W_98a84.
Proof. vm_refl. Qed.
Lemma D_98a84 : decode_any W_98a84 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a88 : bv 32 := 0x4a10d0ef.
Lemma F_98a88 : fetch_word PSEGS (0x98a88 : word) = Some W_98a88.
Proof. vm_refl. Qed.
Lemma D_98a88 : decode_any W_98a88 = Some (Jal 1 56480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a8c : bv 32 := 0x00843503.
Lemma F_98a8c : fetch_word PSEGS (0x98a8c : word) = Some W_98a8c.
Proof. vm_refl. Qed.
Lemma D_98a8c : decode_any W_98a8c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a90 : bv 32 := 0x01048493.
Lemma F_98a90 : fetch_word PSEGS (0x98a90 : word) = Some W_98a90.
Proof. vm_refl. Qed.
Lemma D_98a90 : decode_any W_98a90 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a94 : bv 32 := 0x00950633.
Lemma F_98a94 : fetch_word PSEGS (0x98a94 : word) = Some W_98a94.
Proof. vm_refl. Qed.
Lemma D_98a94 : decode_any W_98a94 = Some (Op ALU_ADD 12 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a98 : bv 32 := 0x00063583.
Lemma F_98a98 : fetch_word PSEGS (0x98a98 : word) = Some W_98a98.
Proof. vm_refl. Qed.
Lemma D_98a98 : decode_any W_98a98 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98a9c : bv 32 := 0xfd458ee3.
Lemma F_98a9c : fetch_word PSEGS (0x98a9c : word) = Some W_98a9c.
Proof. vm_refl. Qed.
Lemma D_98a9c : decode_any W_98a9c = Some (Branch BC_EQ 11 20 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98aa0 : bv 32 := 0xfe0598e3.
Lemma F_98aa0 : fetch_word PSEGS (0x98aa0 : word) = Some W_98aa0.
Proof. vm_refl. Qed.
Lemma D_98aa0 : decode_any W_98aa0 = Some (Branch BC_NE 11 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98aa4 : bv 32 := 0x00013503.
Lemma F_98aa4 : fetch_word PSEGS (0x98aa4 : word) = Some W_98aa4.
Proof. vm_refl. Qed.
Lemma D_98aa4 : decode_any W_98aa4 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98aa8 : bv 32 := 0x00100593.
Lemma F_98aa8 : fetch_word PSEGS (0x98aa8 : word) = Some W_98aa8.
Proof. vm_refl. Qed.
Lemma D_98aa8 : decode_any W_98aa8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98aac : bv 32 := 0x00a9b423.
Lemma F_98aac : fetch_word PSEGS (0x98aac : word) = Some W_98aac.
Proof. vm_refl. Qed.
Lemma D_98aac : decode_any W_98aac = Some (Store SZ8 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ab0 : bv 32 := 0x00b9a823.
Lemma F_98ab0 : fetch_word PSEGS (0x98ab0 : word) = Some W_98ab0.
Proof. vm_refl. Qed.
Lemma D_98ab0 : decode_any W_98ab0 = Some (Store SZ4 19 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ab4 : bv 32 := 0x03043403.
Lemma F_98ab4 : fetch_word PSEGS (0x98ab4 : word) = Some W_98ab4.
Proof. vm_refl. Qed.
Lemma D_98ab4 : decode_any W_98ab4 = Some (Load SZ8 true 8 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ab8 : bv 32 := 0x00001537.
Lemma F_98ab8 : fetch_word PSEGS (0x98ab8 : word) = Some W_98ab8.
Proof. vm_refl. Qed.
Lemma D_98ab8 : decode_any W_98ab8 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98abc : bv 32 := 0x00856463.
Lemma F_98abc : fetch_word PSEGS (0x98abc : word) = Some W_98abc.
Proof. vm_refl. Qed.
Lemma D_98abc : decode_any W_98abc = Some (Branch BC_LTU 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ac0 : bv 32 := 0x00001437.
Lemma F_98ac0 : fetch_word PSEGS (0x98ac0 : word) = Some W_98ac0.
Proof. vm_refl. Qed.
Lemma D_98ac0 : decode_any W_98ac0 = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ac4 : bv 32 := 0x0189b503.
Lemma F_98ac4 : fetch_word PSEGS (0x98ac4 : word) = Some W_98ac4.
Proof. vm_refl. Qed.
Lemma D_98ac4 : decode_any W_98ac4 = Some (Load SZ8 true 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ac8 : bv 32 := 0x02050a63.
Lemma F_98ac8 : fetch_word PSEGS (0x98ac8 : word) = Some W_98ac8.
Proof. vm_refl. Qed.
Lemma D_98ac8 : decode_any W_98ac8 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98acc : bv 32 := 0x00853583.
Lemma F_98acc : fetch_word PSEGS (0x98acc : word) = Some W_98acc.
Proof. vm_refl. Qed.
Lemma D_98acc : decode_any W_98acc = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ad0 : bv 32 := 0x04a58063.
Lemma F_98ad0 : fetch_word PSEGS (0x98ad0 : word) = Some W_98ad0.
Proof. vm_refl. Qed.
Lemma D_98ad0 : decode_any W_98ad0 = Some (Branch BC_EQ 11 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ad4 : bv 32 := 0x00053603.
Lemma F_98ad4 : fetch_word PSEGS (0x98ad4 : word) = Some W_98ad4.
Proof. vm_refl. Qed.
Lemma D_98ad4 : decode_any W_98ad4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ad8 : bv 32 := 0x00b63423.
Lemma F_98ad8 : fetch_word PSEGS (0x98ad8 : word) = Some W_98ad8.
Proof. vm_refl. Qed.
Lemma D_98ad8 : decode_any W_98ad8 = Some (Store SZ8 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98adc : bv 32 := 0x00053583.
Lemma F_98adc : fetch_word PSEGS (0x98adc : word) = Some W_98adc.
Proof. vm_refl. Qed.
Lemma D_98adc : decode_any W_98adc = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ae0 : bv 32 := 0x00853603.
Lemma F_98ae0 : fetch_word PSEGS (0x98ae0 : word) = Some W_98ae0.
Proof. vm_refl. Qed.
Lemma D_98ae0 : decode_any W_98ae0 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ae4 : bv 32 := 0x00b63023.
Lemma F_98ae4 : fetch_word PSEGS (0x98ae4 : word) = Some W_98ae4.
Proof. vm_refl. Qed.
Lemma D_98ae4 : decode_any W_98ae4 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98aec : bv 32 := 0x18a59c63.
Lemma F_98aec : fetch_word PSEGS (0x98aec : word) = Some W_98aec.
Proof. vm_refl. Qed.
Lemma D_98aec : decode_any W_98aec = Some (Branch BC_NE 11 10 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98af0 : bv 32 := 0x00853583.
Lemma F_98af0 : fetch_word PSEGS (0x98af0 : word) = Some W_98af0.
Proof. vm_refl. Qed.
Lemma D_98af0 : decode_any W_98af0 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98af4 : bv 32 := 0x00b9bc23.
Lemma F_98af4 : fetch_word PSEGS (0x98af4 : word) = Some W_98af4.
Proof. vm_refl. Qed.
Lemma D_98af4 : decode_any W_98af4 = Some (Store SZ8 19 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98afc : bv 32 := 0x0289b583.
Lemma F_98afc : fetch_word PSEGS (0x98afc : word) = Some W_98afc.
Proof. vm_refl. Qed.
Lemma D_98afc : decode_any W_98afc = Some (Load SZ8 true 11 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b00 : bv 32 := 0x00058c63.
Lemma F_98b00 : fetch_word PSEGS (0x98b00 : word) = Some W_98b00.
Proof. vm_refl. Qed.
Lemma D_98b00 : decode_any W_98b00 = Some (Branch BC_EQ 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b08 : bv 32 := 0xfff58593.
Lemma F_98b08 : fetch_word PSEGS (0x98b08 : word) = Some W_98b08.
Proof. vm_refl. Qed.
Lemma D_98b08 : decode_any W_98b08 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b0c : bv 32 := 0x16c0006f.
Lemma F_98b0c : fetch_word PSEGS (0x98b0c : word) = Some W_98b0c.
Proof. vm_refl. Qed.
Lemma D_98b0c : decode_any W_98b0c = Some (Jal 0 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b14 : bv 32 := 0x1700006f.
Lemma F_98b14 : fetch_word PSEGS (0x98b14 : word) = Some W_98b14.
Proof. vm_refl. Qed.
Lemma D_98b14 : decode_any W_98b14 = Some (Jal 0 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b18 : bv 32 := 0x0309b503.
Lemma F_98b18 : fetch_word PSEGS (0x98b18 : word) = Some W_98b18.
Proof. vm_refl. Qed.
Lemma D_98b18 : decode_any W_98b18 = Some (Load SZ8 true 10 19 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b1c : bv 32 := 0x0a051063.
Lemma F_98b1c : fetch_word PSEGS (0x98b1c : word) = Some W_98b1c.
Proof. vm_refl. Qed.
Lemma D_98b1c : decode_any W_98b1c = Some (Branch BC_NE 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b24 : bv 32 := 0xfff00593.
Lemma F_98b24 : fetch_word PSEGS (0x98b24 : word) = Some W_98b24.
Proof. vm_refl. Qed.
Lemma D_98b24 : decode_any W_98b24 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b28 : bv 32 := 0x08b48a63.
Lemma F_98b28 : fetch_word PSEGS (0x98b28 : word) = Some W_98b28.
Proof. vm_refl. Qed.
Lemma D_98b28 : decode_any W_98b28 = Some (Branch BC_EQ 9 11 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c20 : bv 32 := 0x00957533.
Lemma F_98c20 : fetch_word PSEGS (0x98c20 : word) = Some W_98c20.
Proof. vm_refl. Qed.
Lemma D_98c20 : decode_any W_98c20 = Some (Op ALU_AND 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c24 : bv 32 := 0x08050a63.
Lemma F_98c24 : fetch_word PSEGS (0x98c24 : word) = Some W_98c24.
Proof. vm_refl. Qed.
Lemma D_98c24 : decode_any W_98c24 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c2c : bv 32 := 0x00001637.
Lemma F_98c2c : fetch_word PSEGS (0x98c2c : word) = Some W_98c2c.
Proof. vm_refl. Qed.
Lemma D_98c2c : decode_any W_98c2c = Some (Lui 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c30 : bv 32 := 0x0489b503.
Lemma F_98c30 : fetch_word PSEGS (0x98c30 : word) = Some W_98c30.
Proof. vm_refl. Qed.
Lemma D_98c30 : decode_any W_98c30 = Some (Load SZ8 true 10 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c34 : bv 32 := 0x00c48633.
Lemma F_98c34 : fetch_word PSEGS (0x98c34 : word) = Some W_98c34.
Proof. vm_refl. Qed.
Lemma D_98c34 : decode_any W_98c34 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c38 : bv 32 := 0xfff58593.
Lemma F_98c38 : fetch_word PSEGS (0x98c38 : word) = Some W_98c38.
Proof. vm_refl. Qed.
Lemma D_98c38 : decode_any W_98c38 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c54 : bv 32 := 0x0089b503.
Lemma F_98c54 : fetch_word PSEGS (0x98c54 : word) = Some W_98c54.
Proof. vm_refl. Qed.
Lemma D_98c54 : decode_any W_98c54 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c58 : bv 32 := 0x0499b423.
Lemma F_98c58 : fetch_word PSEGS (0x98c58 : word) = Some W_98c58.
Proof. vm_refl. Qed.
Lemma D_98c58 : decode_any W_98c58 = Some (Store SZ8 19 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c5c : bv 32 := 0x00a4b023.
Lemma F_98c5c : fetch_word PSEGS (0x98c5c : word) = Some W_98c5c.
Proof. vm_refl. Qed.
Lemma D_98c5c : decode_any W_98c5c = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c60 : bv 32 := 0x0489b503.
Lemma F_98c60 : fetch_word PSEGS (0x98c60 : word) = Some W_98c60.
Proof. vm_refl. Qed.
Lemma D_98c60 : decode_any W_98c60 = Some (Load SZ8 true 10 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c64 : bv 32 := 0x06500593.
Lemma F_98c64 : fetch_word PSEGS (0x98c64 : word) = Some W_98c64.
Proof. vm_refl. Qed.
Lemma D_98c64 : decode_any W_98c64 = Some (OpImm ALU_ADD 11 0 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c68 : bv 32 := 0x00b52823.
Lemma F_98c68 : fetch_word PSEGS (0x98c68 : word) = Some W_98c68.
Proof. vm_refl. Qed.
Lemma D_98c68 : decode_any W_98c68 = Some (Store SZ4 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c6c : bv 32 := 0x0489b503.
Lemma F_98c6c : fetch_word PSEGS (0x98c6c : word) = Some W_98c6c.
Proof. vm_refl. Qed.
Lemma D_98c6c : decode_any W_98c6c = Some (Load SZ8 true 10 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c74 : bv 32 := 0x06400593.
Lemma F_98c74 : fetch_word PSEGS (0x98c74 : word) = Some W_98c74.
Proof. vm_refl. Qed.
Lemma D_98c74 : decode_any W_98c74 = Some (OpImm ALU_ADD 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c78 : bv 32 := 0x02850613.
Lemma F_98c78 : fetch_word PSEGS (0x98c78 : word) = Some W_98c78.
Proof. vm_refl. Qed.
Lemma D_98c78 : decode_any W_98c78 = Some (OpImm ALU_ADD 12 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c7c : bv 32 := 0x02c9b023.
Lemma F_98c7c : fetch_word PSEGS (0x98c7c : word) = Some W_98c7c.
Proof. vm_refl. Qed.
Lemma D_98c7c : decode_any W_98c7c = Some (Store SZ8 19 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c84 : bv 32 := 0x00053423.
Lemma F_98c84 : fetch_word PSEGS (0x98c84 : word) = Some W_98c84.
Proof. vm_refl. Qed.
Lemma D_98c84 : decode_any W_98c84 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c88 : bv 32 := 0x00053023.
Lemma F_98c88 : fetch_word PSEGS (0x98c88 : word) = Some W_98c88.
Proof. vm_refl. Qed.
Lemma D_98c88 : decode_any W_98c88 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c8c : bv 32 := 0x00093583.
Lemma F_98c8c : fetch_word PSEGS (0x98c8c : word) = Some W_98c8c.
Proof. vm_refl. Qed.
Lemma D_98c8c : decode_any W_98c8c = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c90 : bv 32 := 0x00813603.
Lemma F_98c90 : fetch_word PSEGS (0x98c90 : word) = Some W_98c90.
Proof. vm_refl. Qed.
Lemma D_98c90 : decode_any W_98c90 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c94 : bv 32 := 0x04c59863.
Lemma F_98c94 : fetch_word PSEGS (0x98c94 : word) = Some W_98c94.
Proof. vm_refl. Qed.
Lemma D_98c94 : decode_any W_98c94 = Some (Branch BC_NE 11 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c9c : bv 32 := 0x03013403.
Lemma F_98c9c : fetch_word PSEGS (0x98c9c : word) = Some W_98c9c.
Proof. vm_refl. Qed.
Lemma D_98c9c : decode_any W_98c9c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ca0 : bv 32 := 0x02813483.
Lemma F_98ca0 : fetch_word PSEGS (0x98ca0 : word) = Some W_98ca0.
Proof. vm_refl. Qed.
Lemma D_98ca0 : decode_any W_98ca0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ca4 : bv 32 := 0x02013903.
Lemma F_98ca4 : fetch_word PSEGS (0x98ca4 : word) = Some W_98ca4.
Proof. vm_refl. Qed.
Lemma D_98ca4 : decode_any W_98ca4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cac : bv 32 := 0x01013a03.
Lemma F_98cac : fetch_word PSEGS (0x98cac : word) = Some W_98cac.
Proof. vm_refl. Qed.
Lemma D_98cac : decode_any W_98cac = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cb0 : bv 32 := 0x04010113.
Lemma F_98cb0 : fetch_word PSEGS (0x98cb0 : word) = Some W_98cb0.
Proof. vm_refl. Qed.
Lemma D_98cb0 : decode_any W_98cb0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cb4 : bv 32 := 0x00008067.
Lemma F_98cb4 : fetch_word PSEGS (0x98cb4 : word) = Some W_98cb4.
Proof. vm_refl. Qed.
Lemma D_98cb4 : decode_any W_98cb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cb8 : bv 32 := 0x00300613.
Lemma F_98cb8 : fetch_word PSEGS (0x98cb8 : word) = Some W_98cb8.
Proof. vm_refl. Qed.
Lemma D_98cb8 : decode_any W_98cb8 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cbc : bv 32 := 0x00048513.
Lemma F_98cbc : fetch_word PSEGS (0x98cbc : word) = Some W_98cbc.
Proof. vm_refl. Qed.
Lemma D_98cbc : decode_any W_98cbc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cc0 : bv 32 := 0x00040593.
Lemma F_98cc0 : fetch_word PSEGS (0x98cc0 : word) = Some W_98cc0.
Proof. vm_refl. Qed.
Lemma D_98cc0 : decode_any W_98cc0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cc8 : bv 32 := 0xf60500e3.
Lemma F_98cc8 : fetch_word PSEGS (0x98cc8 : word) = Some W_98cc8.
Proof. vm_refl. Qed.
Lemma D_98cc8 : decode_any W_98cc8 = Some (Branch BC_EQ 10 0 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ccc : bv 32 := 0x830fd0ef.
Lemma F_98ccc : fetch_word PSEGS (0x98ccc : word) = Some W_98ccc.
Proof. vm_refl. Qed.
Lemma D_98ccc : decode_any W_98ccc = Some (Jal 1 2084912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cd0 : bv 32 := 0x00052503.
Lemma F_98cd0 : fetch_word PSEGS (0x98cd0 : word) = Some W_98cd0.
Proof. vm_refl. Qed.
Lemma D_98cd0 : decode_any W_98cd0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cd4 : bv 32 := 0x02600593.
Lemma F_98cd4 : fetch_word PSEGS (0x98cd4 : word) = Some W_98cd4.
Proof. vm_refl. Qed.
Lemma D_98cd4 : decode_any W_98cd4 = Some (OpImm ALU_ADD 11 0 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cd8 : bv 32 := 0xf4b508e3.
Lemma F_98cd8 : fetch_word PSEGS (0x98cd8 : word) = Some W_98cd8.
Proof. vm_refl. Qed.
Lemma D_98cd8 : decode_any W_98cd8 = Some (Branch BC_EQ 10 11 8016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cdc : bv 32 := 0x00000513.
Lemma F_98cdc : fetch_word PSEGS (0x98cdc : word) = Some W_98cdc.
Proof. vm_refl. Qed.
Lemma D_98cdc : decode_any W_98cdc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ce0 : bv 32 := 0xfadff06f.
Lemma F_98ce0 : fetch_word PSEGS (0x98ce0 : word) = Some W_98ce0.
Proof. vm_refl. Qed.
Lemma D_98ce0 : decode_any W_98ce0 = Some (Jal 0 2097068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ce4 : bv 32 := 0xd68fd0ef.
Lemma F_98ce4 : fetch_word PSEGS (0x98ce4 : word) = Some W_98ce4.
Proof. vm_refl. Qed.
Lemma D_98ce4 : decode_any W_98ce4 = Some (Jal 1 2086248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ce8 : bv 32 := 0xfd010113.
Lemma F_98ce8 : fetch_word PSEGS (0x98ce8 : word) = Some W_98ce8.
Proof. vm_refl. Qed.
Lemma D_98ce8 : decode_any W_98ce8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cec : bv 32 := 0x02113423.
Lemma F_98cec : fetch_word PSEGS (0x98cec : word) = Some W_98cec.
Proof. vm_refl. Qed.
Lemma D_98cec : decode_any W_98cec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cf0 : bv 32 := 0x02813023.
Lemma F_98cf0 : fetch_word PSEGS (0x98cf0 : word) = Some W_98cf0.
Proof. vm_refl. Qed.
Lemma D_98cf0 : decode_any W_98cf0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cf8 : bv 32 := 0x01213823.
Lemma F_98cf8 : fetch_word PSEGS (0x98cf8 : word) = Some W_98cf8.
Proof. vm_refl. Qed.
Lemma D_98cf8 : decode_any W_98cf8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cfc : bv 32 := 0x01313423.
Lemma F_98cfc : fetch_word PSEGS (0x98cfc : word) = Some W_98cfc.
Proof. vm_refl. Qed.
Lemma D_98cfc : decode_any W_98cfc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d00 : bv 32 := 0x01413023.
Lemma F_98d00 : fetch_word PSEGS (0x98d00 : word) = Some W_98d00.
Proof. vm_refl. Qed.
Lemma D_98d00 : decode_any W_98d00 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d04 : bv 32 := 0xffffe5b7.
Lemma F_98d04 : fetch_word PSEGS (0x98d04 : word) = Some W_98d04.
Proof. vm_refl. Qed.
Lemma D_98d04 : decode_any W_98d04 = Some (Lui 11 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d08 : bv 32 := 0xfff5859b.
Lemma F_98d08 : fetch_word PSEGS (0x98d08 : word) = Some W_98d08.
Proof. vm_refl. Qed.
Lemma D_98d08 : decode_any W_98d08 = Some (OpImm32 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d0c : bv 32 := 0x0015d593.
Lemma F_98d0c : fetch_word PSEGS (0x98d0c : word) = Some W_98d0c.
Proof. vm_refl. Qed.
Lemma D_98d0c : decode_any W_98d0c = Some (ShiftImm ALU_SRL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d14 : bv 32 := 0xfe9fc0ef.
Lemma F_98d14 : fetch_word PSEGS (0x98d14 : word) = Some W_98d14.
Proof. vm_refl. Qed.
Lemma D_98d14 : decode_any W_98d14 = Some (Jal 1 2084840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d18 : bv 32 := 0x00c00593.
Lemma F_98d18 : fetch_word PSEGS (0x98d18 : word) = Some W_98d18.
Proof. vm_refl. Qed.
Lemma D_98d18 : decode_any W_98d18 = Some (OpImm ALU_ADD 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d1c : bv 32 := 0x00b52023.
Lemma F_98d1c : fetch_word PSEGS (0x98d1c : word) = Some W_98d1c.
Proof. vm_refl. Qed.
Lemma D_98d1c : decode_any W_98d1c = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d20 : bv 32 := 0x00000513.
Lemma F_98d20 : fetch_word PSEGS (0x98d20 : word) = Some W_98d20.
Proof. vm_refl. Qed.
Lemma D_98d20 : decode_any W_98d20 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d24 : bv 32 := 0x02813083.
Lemma F_98d24 : fetch_word PSEGS (0x98d24 : word) = Some W_98d24.
Proof. vm_refl. Qed.
Lemma D_98d24 : decode_any W_98d24 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d2c : bv 32 := 0x01813483.
Lemma F_98d2c : fetch_word PSEGS (0x98d2c : word) = Some W_98d2c.
Proof. vm_refl. Qed.
Lemma D_98d2c : decode_any W_98d2c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b0 : bv 32 := 0x058bb603.
Lemma F_990b0 : fetch_word PSEGS (0x990b0 : word) = Some W_990b0.
Proof. vm_refl. Qed.
Lemma D_990b0 : decode_any W_990b0 = Some (Load SZ8 true 12 23 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b4 : bv 32 := 0x058b8a93.
Lemma F_990b4 : fetch_word PSEGS (0x990b4 : word) = Some W_990b4.
Proof. vm_refl. Qed.
Lemma D_990b4 : decode_any W_990b4 = Some (OpImm ALU_ADD 21 23 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b8 : bv 32 := 0x18060063.
Lemma F_990b8 : fetch_word PSEGS (0x990b8 : word) = Some W_990b8.
Proof. vm_refl. Qed.
Lemma D_990b8 : decode_any W_990b8 = Some (Branch BC_EQ 12 0 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990bc : bv 32 := 0x01862583.
Lemma F_990bc : fetch_word PSEGS (0x990bc : word) = Some W_990bc.
Proof. vm_refl. Qed.
Lemma D_990bc : decode_any W_990bc = Some (Load SZ4 true 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c0 : bv 32 := 0x00058663.
Lemma F_990c0 : fetch_word PSEGS (0x990c0 : word) = Some W_990c0.
Proof. vm_refl. Qed.
Lemma D_990c0 : decode_any W_990c0 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c4 : bv 32 := 0x00060513.
Lemma F_990c4 : fetch_word PSEGS (0x990c4 : word) = Some W_990c4.
Proof. vm_refl. Qed.
Lemma D_990c4 : decode_any W_990c4 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c8 : bv 32 := 0x1300006f.
Lemma F_990c8 : fetch_word PSEGS (0x990c8 : word) = Some W_990c8.
Proof. vm_refl. Qed.
Lemma D_990c8 : decode_any W_990c8 = Some (Jal 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990cc : bv 32 := 0x01c62583.
Lemma F_990cc : fetch_word PSEGS (0x990cc : word) = Some W_990cc.
Proof. vm_refl. Qed.
Lemma D_990cc : decode_any W_990cc = Some (Load SZ4 true 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99198 : bv 32 := 0x00062703.
Lemma F_99198 : fetch_word PSEGS (0x99198 : word) = Some W_99198.
Proof. vm_refl. Qed.
Lemma D_99198 : decode_any W_99198 = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9919c : bv 32 := 0x00d777b3.
Lemma F_9919c : fetch_word PSEGS (0x9919c : word) = Some W_9919c.
Proof. vm_refl. Qed.
Lemma D_9919c : decode_any W_9919c = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_991a0 : bv 32 := 0x1606282f.
Lemma F_991a0 : fetch_word PSEGS (0x991a0 : word) = Some W_991a0.
Proof. vm_refl. Qed.
Lemma D_991a0 : decode_any W_991a0 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_991a4 : bv 32 := 0x00e81663.
Lemma F_991a4 : fetch_word PSEGS (0x991a4 : word) = Some W_991a4.
Proof. vm_refl. Qed.
Lemma D_991a4 : decode_any W_991a4 = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_991a8 : bv 32 := 0x1ef628af.
Lemma F_991a8 : fetch_word PSEGS (0x991a8 : word) = Some W_991a8.
Proof. vm_refl. Qed.
Lemma D_991a8 : decode_any W_991a8 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_991ac : bv 32 := 0xfe089ae3.
Lemma F_991ac : fetch_word PSEGS (0x991ac : word) = Some W_991ac.
Proof. vm_refl. Qed.
Lemma D_991ac : decode_any W_991ac = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_991b0 : bv 32 := 0x0008081b.
Lemma F_991b0 : fetch_word PSEGS (0x991b0 : word) = Some W_991b0.
Proof. vm_refl. Qed.
Lemma D_991b0 : decode_any W_991b0 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_991b4 : bv 32 := 0xfee812e3.
Lemma F_991b4 : fetch_word PSEGS (0x991b4 : word) = Some W_991b4.
Proof. vm_refl. Qed.
Lemma D_991b4 : decode_any W_991b4 = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.
