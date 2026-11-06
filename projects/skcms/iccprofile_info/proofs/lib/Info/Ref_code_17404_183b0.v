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

Definition W_17404 : bv 32 := 0x00072503.
Lemma F_17404 : fetch_word Plain.M.loaded_segments (0x17404 : word) = Some W_17404.
Proof. vm_refl. Qed.
Lemma D_17404 : decode_any W_17404 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17408 : bv 32 := 0x00b56633.
Lemma F_17408 : fetch_word Plain.M.loaded_segments (0x17408 : word) = Some W_17408.
Proof. vm_refl. Qed.
Lemma D_17408 : decode_any W_17408 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1740c : bv 32 := 0x160726af.
Lemma F_1740c : fetch_word Plain.M.loaded_segments (0x1740c : word) = Some W_1740c.
Proof. vm_refl. Qed.
Lemma D_1740c : decode_any W_1740c = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17410 : bv 32 := 0x00a69663.
Lemma F_17410 : fetch_word Plain.M.loaded_segments (0x17410 : word) = Some W_17410.
Proof. vm_refl. Qed.
Lemma D_17410 : decode_any W_17410 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17414 : bv 32 := 0x1ec727af.
Lemma F_17414 : fetch_word Plain.M.loaded_segments (0x17414 : word) = Some W_17414.
Proof. vm_refl. Qed.
Lemma D_17414 : decode_any W_17414 = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17418 : bv 32 := 0xfe079ae3.
Lemma F_17418 : fetch_word Plain.M.loaded_segments (0x17418 : word) = Some W_17418.
Proof. vm_refl. Qed.
Lemma D_17418 : decode_any W_17418 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1741c : bv 32 := 0x0006869b.
Lemma F_1741c : fetch_word Plain.M.loaded_segments (0x1741c : word) = Some W_1741c.
Proof. vm_refl. Qed.
Lemma D_1741c : decode_any W_1741c = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17420 : bv 32 := 0xfea692e3.
Lemma F_17420 : fetch_word Plain.M.loaded_segments (0x17420 : word) = Some W_17420.
Proof. vm_refl. Qed.
Lemma D_17420 : decode_any W_17420 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_17be4 : bv 32 := 0x00062703.
Lemma F_17be4 : fetch_word Plain.M.loaded_segments (0x17be4 : word) = Some W_17be4.
Proof. vm_refl. Qed.
Lemma D_17be4 : decode_any W_17be4 = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17be8 : bv 32 := 0x00d777b3.
Lemma F_17be8 : fetch_word Plain.M.loaded_segments (0x17be8 : word) = Some W_17be8.
Proof. vm_refl. Qed.
Lemma D_17be8 : decode_any W_17be8 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17bec : bv 32 := 0x1606282f.
Lemma F_17bec : fetch_word Plain.M.loaded_segments (0x17bec : word) = Some W_17bec.
Proof. vm_refl. Qed.
Lemma D_17bec : decode_any W_17bec = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17bf0 : bv 32 := 0x00e81663.
Lemma F_17bf0 : fetch_word Plain.M.loaded_segments (0x17bf0 : word) = Some W_17bf0.
Proof. vm_refl. Qed.
Lemma D_17bf0 : decode_any W_17bf0 = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17bf4 : bv 32 := 0x1ef628af.
Lemma F_17bf4 : fetch_word Plain.M.loaded_segments (0x17bf4 : word) = Some W_17bf4.
Proof. vm_refl. Qed.
Lemma D_17bf4 : decode_any W_17bf4 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17bf8 : bv 32 := 0xfe089ae3.
Lemma F_17bf8 : fetch_word Plain.M.loaded_segments (0x17bf8 : word) = Some W_17bf8.
Proof. vm_refl. Qed.
Lemma D_17bf8 : decode_any W_17bf8 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_17bfc : bv 32 := 0x0008081b.
Lemma F_17bfc : fetch_word Plain.M.loaded_segments (0x17bfc : word) = Some W_17bfc.
Proof. vm_refl. Qed.
Lemma D_17bfc : decode_any W_17bfc = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17c00 : bv 32 := 0xfee812e3.
Lemma F_17c00 : fetch_word Plain.M.loaded_segments (0x17c00 : word) = Some W_17c00.
Proof. vm_refl. Qed.
Lemma D_17c00 : decode_any W_17c00 = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_18348 : bv 32 := 0x02053703.
Lemma F_18348 : fetch_word Plain.M.loaded_segments (0x18348 : word) = Some W_18348.
Proof. vm_refl. Qed.
Lemma D_18348 : decode_any W_18348 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1834c : bv 32 := 0x00c75793.
Lemma F_1834c : fetch_word Plain.M.loaded_segments (0x1834c : word) = Some W_1834c.
Proof. vm_refl. Qed.
Lemma D_1834c : decode_any W_1834c = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18350 : bv 32 := 0x00078e63.
Lemma F_18350 : fetch_word Plain.M.loaded_segments (0x18350 : word) = Some W_18350.
Proof. vm_refl. Qed.
Lemma D_18350 : decode_any W_18350 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_18354 : bv 32 := 0x01f77793.
Lemma F_18354 : fetch_word Plain.M.loaded_segments (0x18354 : word) = Some W_18354.
Proof. vm_refl. Qed.
Lemma D_18354 : decode_any W_18354 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_18358 : bv 32 := 0x00079a63.
Lemma F_18358 : fetch_word Plain.M.loaded_segments (0x18358 : word) = Some W_18358.
Proof. vm_refl. Qed.
Lemma D_18358 : decode_any W_18358 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1835c : bv 32 := 0xfffff7b7.
Lemma F_1835c : fetch_word Plain.M.loaded_segments (0x1835c : word) = Some W_1835c.
Proof. vm_refl. Qed.
Lemma D_1835c : decode_any W_1835c = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_18360 : bv 32 := 0x00f77733.
Lemma F_18360 : fetch_word Plain.M.loaded_segments (0x18360 : word) = Some W_18360.
Proof. vm_refl. Qed.
Lemma D_18360 : decode_any W_18360 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_18364 : bv 32 := 0xff070713.
Lemma F_18364 : fetch_word Plain.M.loaded_segments (0x18364 : word) = Some W_18364.
Proof. vm_refl. Qed.
Lemma D_18364 : decode_any W_18364 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18368 : bv 32 := 0x0200006f.
Lemma F_18368 : fetch_word Plain.M.loaded_segments (0x18368 : word) = Some W_18368.
Proof. vm_refl. Qed.
Lemma D_18368 : decode_any W_18368 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1836c : bv 32 := 0x00575713.
Lemma F_1836c : fetch_word Plain.M.loaded_segments (0x1836c : word) = Some W_1836c.
Proof. vm_refl. Qed.
Lemma D_1836c : decode_any W_1836c = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18370 : bv 32 := 0xffff8797.
Lemma F_18370 : fetch_word Plain.M.loaded_segments (0x18370 : word) = Some W_18370.
Proof. vm_refl. Qed.
Lemma D_18370 : decode_any W_18370 = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18374 : bv 32 := 0x07e77713.
Lemma F_18374 : fetch_word Plain.M.loaded_segments (0x18374 : word) = Some W_18374.
Proof. vm_refl. Qed.
Lemma D_18374 : decode_any W_18374 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_18378 : bv 32 := 0x19878793.
Lemma F_18378 : fetch_word Plain.M.loaded_segments (0x18378 : word) = Some W_18378.
Proof. vm_refl. Qed.
Lemma D_18378 : decode_any W_18378 = Some (OpImm ALU_ADD 15 15 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_1837c : bv 32 := 0x00e78733.
Lemma F_1837c : fetch_word Plain.M.loaded_segments (0x1837c : word) = Some W_1837c.
Proof. vm_refl. Qed.
Lemma D_1837c : decode_any W_1837c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18380 : bv 32 := 0x00075703.
Lemma F_18380 : fetch_word Plain.M.loaded_segments (0x18380 : word) = Some W_18380.
Proof. vm_refl. Qed.
Lemma D_18380 : decode_any W_18380 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18384 : bv 32 := 0x00471713.
Lemma F_18384 : fetch_word Plain.M.loaded_segments (0x18384 : word) = Some W_18384.
Proof. vm_refl. Qed.
Lemma D_18384 : decode_any W_18384 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18388 : bv 32 := 0x01053803.
Lemma F_18388 : fetch_word Plain.M.loaded_segments (0x18388 : word) = Some W_18388.
Proof. vm_refl. Qed.
Lemma D_18388 : decode_any W_18388 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1838c : bv 32 := 0x02b707b3.
Lemma F_1838c : fetch_word Plain.M.loaded_segments (0x1838c : word) = Some W_1838c.
Proof. vm_refl. Qed.
Lemma D_1838c : decode_any W_1838c = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18390 : bv 32 := 0x00f807b3.
Lemma F_18390 : fetch_word Plain.M.loaded_segments (0x18390 : word) = Some W_18390.
Proof. vm_refl. Qed.
Lemma D_18390 : decode_any W_18390 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_18394 : bv 32 := 0x00d7c883.
Lemma F_18394 : fetch_word Plain.M.loaded_segments (0x18394 : word) = Some W_18394.
Proof. vm_refl. Qed.
Lemma D_18394 : decode_any W_18394 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18398 : bv 32 := 0x40c702b3.
Lemma F_18398 : fetch_word Plain.M.loaded_segments (0x18398 : word) = Some W_18398.
Proof. vm_refl. Qed.
Lemma D_18398 : decode_any W_18398 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1839c : bv 32 := 0xffc28293.
Lemma F_1839c : fetch_word Plain.M.loaded_segments (0x1839c : word) = Some W_1839c.
Proof. vm_refl. Qed.
Lemma D_1839c : decode_any W_1839c = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a0 : bv 32 := 0x01078793.
Lemma F_183a0 : fetch_word Plain.M.loaded_segments (0x183a0 : word) = Some W_183a0.
Proof. vm_refl. Qed.
Lemma D_183a0 : decode_any W_183a0 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a4 : bv 32 := 0x00088663.
Lemma F_183a4 : fetch_word Plain.M.loaded_segments (0x183a4 : word) = Some W_183a4.
Proof. vm_refl. Qed.
Lemma D_183a4 : decode_any W_183a4 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a8 : bv 32 := 0xffe7d683.
Lemma F_183a8 : fetch_word Plain.M.loaded_segments (0x183a8 : word) = Some W_183a8.
Proof. vm_refl. Qed.
Lemma D_183a8 : decode_any W_183a8 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_183ac : bv 32 := 0x00168693.
Lemma F_183ac : fetch_word Plain.M.loaded_segments (0x183ac : word) = Some W_183ac.
Proof. vm_refl. Qed.
Lemma D_183ac : decode_any W_183ac = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
