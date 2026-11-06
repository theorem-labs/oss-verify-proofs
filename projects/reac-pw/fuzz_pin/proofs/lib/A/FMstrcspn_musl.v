(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMstrlen_musl.v at 6ebe35ba632; the fetch, decode and step lemmas walk the loops of musl __strchrnul in reac-pw/fuzz_pin.asan (0x91760 .. 0x9181c) instead of musl strlen, the byte loops also stop at the byte c, the word loop also tests each word for c (the xor with c * ONES, as lib/A/AE3a.v's musl memchr), and the result is CS_MUSL_LOOPS of lib/A/FMcs0.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP02.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE3a.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PPgWrap.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.FMcs0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
(* musl __strchrnul, tfib_A_strchrnul .. tfib_E_strchrnul (0x9174c .. 0x9182c in fuzz_pin.asan); the loops, entered
   at 0x14 with a0 = s and a1 = c (0 < c < 256), end at 0xd0 (the epilogue):
   0x14 andi a2,a0,7; 0x18 beqz a2 -> 0x3c (word loop); 0x1c addi a2,a0,1
   0x20 L1: lbu a3,0(a0); beqz a3 -> 0xd0; beq a3,a1 -> 0xd0; addi a0,a0,1; andi a3,a2,7; addi a2,a2,1; bnez a3 -> 0x20
   0x3c auipc a2; ld a2 (C1 = ONES - 1); ld a4,0(a0); auipc a3; ld a3 (HIGHS)
   0x50 sub a5,a2,a4; or a5,a5,a4; and a5,a5,a3; bne a5,a3 -> 0xb8 (the first word has a NUL)
   0x60 addi a5,a2,1; mul a5,a1,a5 (c * ONES)
   0x68 L2: xor a4,a4,a5; sub a6,a2,a4; or a4,a6,a4; and a4,a4,a3; bne a4,a3 -> 0xb8 (the word has c)
   0x7c ld a4,8(a0); addi a6,a0,8; sub a0,a2,a4; or a0,a0,a4; and a7,a0,a3; mv a0,a6; beq a7,a3 -> 0x68
   0x98 j 0xbc
   0xb8 mv a6,a0; 0xbc addi a0,a6,-1
   0xc0 L3: lbu a2,1(a0); addi a0,a0,1; beqz a2 -> 0xd0; bne a2,a1 -> 0xc0
   0xd0 the epilogue *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma FC_014 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x14)) = Some (0x00757613%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_014 : decode_any (0x00757613%bv : bv 32) = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_018 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x18)) = Some (0x02060263%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_018 : decode_any (0x02060263%bv : bv 32) = Some (Branch BC_EQ 12 0 36, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_01c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x1c)) = Some (0x00150613%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_01c : decode_any (0x00150613%bv : bv 32) = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_020 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x20)) = Some (0x00054683%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_020 : decode_any (0x00054683%bv : bv 32) = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_024 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x24)) = Some (0x0a068663%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_024 : decode_any (0x0a068663%bv : bv 32) = Some (Branch BC_EQ 13 0 172, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_028 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x28)) = Some (0x0ab68463%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_028 : decode_any (0x0ab68463%bv : bv 32) = Some (Branch BC_EQ 13 11 168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_02c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x2c)) = Some (0x00150513%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_02c : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_030 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x30)) = Some (0x00767693%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_030 : decode_any (0x00767693%bv : bv 32) = Some (OpImm ALU_AND 13 12 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_034 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x34)) = Some (0x00160613%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_034 : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_038 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x38)) = Some (0xfe0694e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_038 : decode_any (0xfe0694e3%bv : bv 32) = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_044 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x44)) = Some (0x00053703%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_044 : decode_any (0x00053703%bv : bv 32) = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_050 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x50)) = Some (0x40e607b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_050 : decode_any (0x40e607b3%bv : bv 32) = Some (Op ALU_SUB 15 12 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_054 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x54)) = Some (0x00e7e7b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_054 : decode_any (0x00e7e7b3%bv : bv 32) = Some (Op ALU_OR 15 15 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_058 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x58)) = Some (0x00d7f7b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_058 : decode_any (0x00d7f7b3%bv : bv 32) = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_05c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x5c)) = Some (0x04d79e63%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_05c : decode_any (0x04d79e63%bv : bv 32) = Some (Branch BC_NE 15 13 92, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_060 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x60)) = Some (0x00160793%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_060 : decode_any (0x00160793%bv : bv 32) = Some (OpImm ALU_ADD 15 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_064 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x64)) = Some (0x02f587b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_064 : decode_any (0x02f587b3%bv : bv 32) = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_068 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x68)) = Some (0x00f74733%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_068 : decode_any (0x00f74733%bv : bv 32) = Some (Op ALU_XOR 14 14 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_06c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x6c)) = Some (0x40e60833%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_06c : decode_any (0x40e60833%bv : bv 32) = Some (Op ALU_SUB 16 12 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_070 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x70)) = Some (0x00e86733%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_070 : decode_any (0x00e86733%bv : bv 32) = Some (Op ALU_OR 14 16 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_074 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x74)) = Some (0x00d77733%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_074 : decode_any (0x00d77733%bv : bv 32) = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_078 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x78)) = Some (0x04d71063%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_078 : decode_any (0x04d71063%bv : bv 32) = Some (Branch BC_NE 14 13 64, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_07c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x7c)) = Some (0x00853703%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_07c : decode_any (0x00853703%bv : bv 32) = Some (Load SZ8 true 14 10 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_080 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x80)) = Some (0x00850813%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_080 : decode_any (0x00850813%bv : bv 32) = Some (OpImm ALU_ADD 16 10 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_084 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x84)) = Some (0x40e60533%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_084 : decode_any (0x40e60533%bv : bv 32) = Some (Op ALU_SUB 10 12 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_088 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x88)) = Some (0x00e56533%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_088 : decode_any (0x00e56533%bv : bv 32) = Some (Op ALU_OR 10 10 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_08c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x8c)) = Some (0x00d578b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_08c : decode_any (0x00d578b3%bv : bv 32) = Some (Op ALU_AND 17 10 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_090 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x90)) = Some (0x00080513%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_090 : decode_any (0x00080513%bv : bv 32) = Some (OpImm ALU_ADD 10 16 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_094 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x94)) = Some (0xfcd88ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_094 : decode_any (0xfcd88ae3%bv : bv 32) = Some (Branch BC_EQ 17 13 8148, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_098 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x98)) = Some (0x0240006f%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_098 : decode_any (0x0240006f%bv : bv 32) = Some (Jal 0 36, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_0b8 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0xb8)) = Some (0x00050813%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_0b8 : decode_any (0x00050813%bv : bv 32) = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_0bc : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0xbc)) = Some (0xfff80513%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_0bc : decode_any (0xfff80513%bv : bv 32) = Some (OpImm ALU_ADD 10 16 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_0c0 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0xc0)) = Some (0x00154603%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_0c0 : decode_any (0x00154603%bv : bv 32) = Some (Load SZ1 false 12 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_0c4 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0xc4)) = Some (0x00150513%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_0c4 : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_0c8 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0xc8)) = Some (0x00060463%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_0c8 : decode_any (0x00060463%bv : bv 32) = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_0cc : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0xcc)) = Some (0xfeb61ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma DC_0cc : decode_any (0xfeb61ae3%bv : bv 32) = Some (Branch BC_NE 12 11 8180, 4%Z).
Proof. vm_refl_bv. Qed.
(* the two auipc/ld pairs that load the constants; their words are read from the table so that
   the file carries no address-dependent immediate *)
Definition cm_w03c : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_strchrnul + 0x3c).
Definition cm_w040 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_strchrnul + 0x40).
Definition cm_w048 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_strchrnul + 0x48).
Definition cm_w04c : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_strchrnul + 0x4c).
Definition cm_i03c : Z := Eval vm_compute in auipc_imm20 cm_w03c.
Definition cm_i040 : Z := Eval vm_compute in ld_imm12 cm_w040.
Definition cm_i048 : Z := Eval vm_compute in auipc_imm20 cm_w048.
Definition cm_i04c : Z := Eval vm_compute in ld_imm12 cm_w04c.
Definition cm_aui1 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (tfib_A_strchrnul + 0x3c)) (Z.shiftl (bv_signed (Z_to_bv 20 cm_i03c)) 12)).
Definition cm_aui2 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (tfib_A_strchrnul + 0x48)) (Z.shiftl (bv_signed (Z_to_bv 20 cm_i048)) 12)).
Lemma FC_03c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x3c)) = Some (Z_to_bv 32 cm_w03c).
Proof. ftac. Qed.
Lemma DC_03c : decode_any (Z_to_bv 32 cm_w03c) = Some (Auipc 12 (Z_to_bv 20 cm_i03c), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_040 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x40)) = Some (Z_to_bv 32 cm_w040).
Proof. ftac. Qed.
Lemma DC_040 : decode_any (Z_to_bv 32 cm_w040) = Some (Load SZ8 true 12 12 (Z_to_bv 12 cm_i040), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_048 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x48)) = Some (Z_to_bv 32 cm_w048).
Proof. ftac. Qed.
Lemma DC_048 : decode_any (Z_to_bv 32 cm_w048) = Some (Auipc 13 (Z_to_bv 20 cm_i048), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FC_04c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_strchrnul + 0x4c)) = Some (Z_to_bv 32 cm_w04c).
Proof. ftac. Qed.
Lemma DC_04c : decode_any (Z_to_bv 32 cm_w04c) = Some (Load SZ8 true 13 13 (Z_to_bv 12 cm_i04c), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma cm_ld_targets :
bv_unsigned (v_addi (Z_to_bv 64 cm_aui1) (bv_signed (Z_to_bv 12 cm_i040))) = tfib_D_const_ONES_0x0101010101010100 /\
bv_unsigned (v_addi (Z_to_bv 64 cm_aui2) (bv_signed (Z_to_bv 12 cm_i04c))) = tfib_D_const_HIGHS_0x8080808080808080.
Proof. vm_compute. split; reflexivity. Qed.
End f.
(* musl strcspn with a set of one byte c is __strchrnul: cspn_len [c] s stops at the first byte of s equal to c *)
Lemma cspn1_props : forall (c : byte) (s : list byte),
(PPgWrap.cspn_len [c] s <= length s)%nat /\
(forall j, (j < PPgWrap.cspn_len [c] s)%nat -> bv_unsigned (nth j s NUL) <> bv_unsigned c) /\
(PPgWrap.cspn_len [c] s = length s \/ bv_unsigned (nth (PPgWrap.cspn_len [c] s) s NUL) = bv_unsigned c).
Proof.
intros c s. induction s as [|x s IH].
- cbn [PPgWrap.cspn_len length]. split; [lia|]. split; [intros j Hj; lia|]. left; reflexivity.
- change (PPgWrap.cspn_len [c] (x :: s)) with
  (if (bv_unsigned c =? bv_unsigned x) || false then O else S (PPgWrap.cspn_len [c] s)).
  rewrite Bool.orb_false_r. cbn [length].
  destruct (Z.eqb_spec (bv_unsigned c) (bv_unsigned x)) as [Ex|Ex].
  + split; [lia|]. split; [intros j Hj; lia|]. right. cbn [nth]. lia.
  + destruct IH as (H1 & H2 & H3). split; [lia|]. split.
    * intros j Hj. destruct j as [|j]; cbn [nth]; [lia|]. apply H2. lia.
    * destruct H3 as [H3|H3]; [left; lia | right; cbn [nth]; exact H3].
Qed.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable s : list byte.
Variable c : byte.
Variable p : word.
Variable mem rom : word -> option byte.
Definition cm_P : Z := bv_unsigned p.
Definition cm_L : Z := Z.of_nat (length s).
Definition cm_E : Z := cm_P + cm_L.
Definition cm_Rn : nat := PPgWrap.cspn_len [c] s.
Definition cm_R : Z := Z.of_nat cm_Rn.
Definition cm_K : Z := bv_unsigned c * (C1 + 1).
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hcz : bv_unsigned c <> 0.
Hypothesis Hfit : bv_unsigned p + Z.of_nat (length s) + 8 < 2^64.
Hypothesis Hstr : forall j, (j <= length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Hypothesis Hrd : forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 <> None.
Hypothesis Hrom : forall a : Z, tfib_D_const_HIGHS_0x8080808080808080 <= a < (tfib_D_const_ONES_0x0101010101010100 + 8) ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Lemma cm_E_eq : cm_E = bv_unsigned p + Z.of_nat (length s). Proof. reflexivity. Qed.
Lemma cm_P_eq : cm_P = bv_unsigned p. Proof. reflexivity. Qed.
Lemma cm_L_eq : cm_L = Z.of_nat (length s). Proof. reflexivity. Qed.
Lemma cm_R_eq : cm_R = Z.of_nat cm_Rn. Proof. reflexivity. Qed.
Lemma cm_R_le : (cm_Rn <= length s)%nat.
Proof. unfold cm_Rn. apply (proj1 (cspn1_props c s)). Qed.
Ltac epl := pose proof cm_E_eq as EpE; pose proof cm_P_eq as EpP; pose proof cm_L_eq as EpL;
pose proof cm_R_eq as EpR; pose proof (u64_range p) as EpU; pose proof cm_R_le as EpRL.
Lemma cm_byte_nz : forall j, (j < length s)%nat -> nth j (s ++ [NUL]) NUL <> NUL.
Proof. intros j Hj Hc. apply Hnul. rewrite <- Hc. apply nth_app_nul_in. exact Hj. Qed.
Lemma cm_p_lit : Z_to_bv 64 (bv_unsigned p + Z.of_nat 0) = p.
Proof. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* the bytes before index R are neither NUL nor c; the byte at R is NUL or c *)
Lemma cm_before : forall j, (j < cm_Rn)%nat ->
nth j (s ++ [NUL]) NUL <> NUL /\ bv_unsigned (nth j (s ++ [NUL]) NUL) <> bv_unsigned c.
Proof.
intros j Hj. destruct (cspn1_props c s) as (H1 & H2 & H3). unfold cm_Rn in Hj. split.
- apply cm_byte_nz. lia.
- rewrite app_nth1 by lia. apply H2. exact Hj.
Qed.
Lemma cm_at : bv_unsigned (nth cm_Rn (s ++ [NUL]) NUL) = 0 \/
bv_unsigned (nth cm_Rn (s ++ [NUL]) NUL) = bv_unsigned c.
Proof.
destruct (cspn1_props c s) as (H1 & H2 & H3). unfold cm_Rn.
destruct (Nat.eq_dec (PPgWrap.cspn_len [c] s) (length s)) as [He|He].
- left. rewrite He, nth_app_nul_last. reflexivity.
- right. rewrite app_nth1 by lia. destruct H3 as [H3|H3]; [exfalso; exact (He H3) | exact H3].
Qed.
Lemma cm_K_range : 0 <= cm_K < 2^64.
Proof. unfold cm_K, C1. pose proof (u8_range c). lia. Qed.
Lemma cm_zb_K : forall i, (i < 8)%nat -> HZ.zb cm_K i = bv_unsigned c.
Proof.
intros i Hi. pose proof (u8_range c) as Hc.
replace cm_K with (HZ.zdig [bv_unsigned c; bv_unsigned c; bv_unsigned c; bv_unsigned c;
bv_unsigned c; bv_unsigned c; bv_unsigned c; bv_unsigned c])
by (unfold cm_K, C1; cbn [HZ.zdig]; lia).
rewrite HZ.zb_zdig.
- destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth]; first [reflexivity | lia].
- apply Forall_forall. intros d Hd. cbn [In] in Hd. lia.
- cbn [length]. lia.
Qed.
Lemma cm_zb_y : forall x i, (i < 8)%nat -> HZ.zb (Z.lxor x cm_K) i = Z.lxor (HZ.zb x i) (bv_unsigned c).
Proof. intros x i Hi. rewrite HZ.zb_lxor, cm_zb_K by exact Hi. reflexivity. Qed.
Lemma cm_floor_le : cm_P + cm_R - (cm_P + cm_R) mod 8 <= cm_E - cm_E mod 8.
Proof.
epl.
pose proof (Z.div_mod (cm_P + cm_R) 8 ltac:(lia)) as H1.
pose proof (Z.div_mod cm_E 8 ltac:(lia)) as H2.
pose proof (Z.mod_pos_bound (cm_P + cm_R) 8 ltac:(lia)) as H3.
pose proof (Z.mod_pos_bound cm_E 8 ltac:(lia)) as H4.
lia.
Qed.
(* L3, the byte loop after the word loop: a0 = R - d - 1, the next byte is R - d *)
Lemma cm_tail : forall d regs,
(d <= cm_Rn)%nat ->
getr regs 10 = Z_to_bv 64 (cm_P + cm_R - Z.of_nat d - 1) ->
getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0xc0)) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (cm_P + cm_R)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> getr regs' r = getr regs r).
Proof.
induction d as [|d IH]; intros regs Hd H10 H11; epl.
- set (b := nth cm_Rn (s ++ [NUL]) NUL).
  assert (Hb : bv_unsigned b = 0 \/ bv_unsigned b = bv_unsigned c) by exact cm_at.
  set (regs1 := regupd (regupd regs 12 (Z_to_bv 64 (bv_unsigned b))) 10 (Z_to_bv 64 (cm_P + cm_R))).
  assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0xc0)) mem rom)
  (mkst regs1 (Z_to_bv 64 (tfib_A_strchrnul + 0xc8)) mem rom)).
  { norm_pc.
    steplbu FC_0c0 DC_0c0
    ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_lit;
    match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
      replace a with (bv_unsigned p + Z.of_nat cm_Rn) by lia end;
    apply Hstr; lia).
    stepiv' FC_0c4 DC_0c4 (Z_to_bv 64 (cm_P + cm_R))
    ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_lit; f_equal; lia).
    subst regs1 b. msteps_done. }
  exists regs1. split; [|split].
  + eapply msteps_trans; [exact Hpre|]. norm_pc.
    destruct Hb as [Hb|Hb].
    * stepbt FC_0c8 DC_0c8
      ltac:(subst regs1; gr; cbn [branch_taken]; unfold bv_eqb; rewrite u_zext8, u_lit0, Hb; reflexivity).
      msteps_done.
    * stepbf FC_0c8 DC_0c8
      ltac:(subst regs1; gr; cbn [branch_taken]; unfold bv_eqb; rewrite u_zext8, u_lit0, Hb;
      apply Z.eqb_neq; exact Hcz).
      stepbf FC_0cc DC_0cc
      ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; apply negb_false_iff; unfold bv_eqb;
      rewrite !u_zext8, Hb; apply Z.eqb_refl).
      msteps_done.
  + subst regs1. gr. reflexivity.
  + intros r Hr10 Hr12. subst regs1. rewrite !getr_other by assumption. reflexivity.
- destruct (cm_before (cm_Rn - S d) ltac:(lia)) as [Hb0 Hbc].
  set (b := nth (cm_Rn - S d) (s ++ [NUL]) NUL) in *.
  assert (Hbn : bv_unsigned b <> 0) by (apply byte_nz_u; exact Hb0).
  set (regs1 := regupd (regupd regs 12 (Z_to_bv 64 (bv_unsigned b))) 10 (Z_to_bv 64 (cm_P + cm_R - Z.of_nat d - 1))).
  destruct (IH regs1) as (regs' & Hms & H10' & Hfr).
  { lia. }
  { subst regs1. gr. reflexivity. }
  { subst regs1. gr. exact H11. }
  exists regs'. split; [|split].
  + eapply msteps_trans; [|exact Hms].
    norm_pc.
    steplbu FC_0c0 DC_0c0
    ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_lit;
    match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
      replace a with (bv_unsigned p + Z.of_nat (cm_Rn - S d)) by lia end;
    apply Hstr; lia).
    stepiv' FC_0c4 DC_0c4 (Z_to_bv 64 (cm_P + cm_R - Z.of_nat d - 1))
    ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_lit; f_equal; lia).
    stepbf FC_0c8 DC_0c8
    ltac:(gr; cbn [branch_taken]; unfold bv_eqb; rewrite u_zext8, u_lit0; apply Z.eqb_neq; exact Hbn).
    stepbt FC_0cc DC_0cc
    ltac:(gr; rewrite H11; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
    rewrite !u_zext8; apply Z.eqb_neq; exact Hbc).
    subst regs1 b. msteps_done.
  + exact H10'.
  + intros r Hr10 Hr12. rewrite (Hfr r Hr10 Hr12). subst regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
(* 0xbc: a6 = w, the first byte the tail loop reads, P <= w <= R *)
Lemma cm_tail_bc : forall regs w,
cm_P <= w <= cm_P + cm_R ->
getr regs 16 = Z_to_bv 64 w ->
getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0xbc)) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (cm_P + cm_R)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> getr regs' r = getr regs r).
Proof.
intros regs w Hw H16 H11. epl.
set (d := Z.to_nat (cm_P + cm_R - w)).
set (regs1 := regupd regs 10 (Z_to_bv 64 (cm_P + cm_R - Z.of_nat d - 1))).
destruct (cm_tail d regs1) as (regs' & Hms & H10' & Hfr).
{ subst d. lia. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. exact H11. }
exists regs'. split; [|split].
- eapply msteps_trans; [|exact Hms]. norm_pc.
  stepiv' FC_0bc DC_0bc (Z_to_bv 64 (cm_P + cm_R - Z.of_nat d - 1))
  ltac:(gr; rewrite H16; imm_norm; rewrite v_addi_lit; f_equal; subst d; lia).
  subst regs1. msteps_done.
- exact H10'.
- intros r Hr10 Hr12. rewrite (Hfr r Hr10 Hr12). subst regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
(* 0xb8: a0 = w *)
Lemma cm_tail_b8 : forall regs w,
cm_P <= w <= cm_P + cm_R ->
getr regs 10 = Z_to_bv 64 w ->
getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0xb8)) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (cm_P + cm_R)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 16%bv -> getr regs' r = getr regs r).
Proof.
intros regs w Hw H10 H11.
set (regs1 := regupd regs 16 (Z_to_bv 64 w)).
destruct (cm_tail_bc regs1 w) as (regs' & Hms & H10' & Hfr).
{ exact Hw. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. exact H11. }
exists regs'. split; [|split].
- eapply msteps_trans; [|exact Hms]. norm_pc.
  stepiv' FC_0b8 DC_0b8 (Z_to_bv 64 w) ltac:(gr; rewrite H10; imm_norm; apply v_addi_0).
  subst regs1. msteps_done.
- exact H10'.
- intros r Hr10 Hr12 Hr16. rewrite (Hfr r Hr10 Hr12). subst regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma cm_word_at : forall w, cm_P <= w -> w + 8 <= cm_E - cm_E mod 8 + 8 ->
exists bs, rdn tfibsegs mem (Z_to_bv 64 w) 8 = Some bs /\ length bs = 8%nat /\
(forall i, (i < 8)%nat -> w + Z.of_nat i <= cm_E ->
nth i bs NUL = nth (Z.to_nat (w - cm_P) + i) (s ++ [NUL]) NUL).
Proof.
intros w Hlo Hhi. unfold cm_E, cm_P, cm_L in *.
pose proof (u64_range p) as Hp.
assert (Hm2 : 0 <= (bv_unsigned p + Z.of_nat (length s)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (rdn_total tfibsegs mem 8 (Z_to_bv 64 w)) as [bs Hbs].
{ intros k Hk. rewrite word_add_nat, u_Z2bv by lia.
destruct (Z_lt_le_dec (bv_unsigned p + Z.of_nat (length s)) (w + Z.of_nat k)) as [Hpast|Hin].
- apply Hrd. lia.
- replace (w + Z.of_nat k) with (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + k)) by lia.
rewrite Hstr by lia. discriminate. }
exists bs. split; [exact Hbs|]. split; [exact (rdn_length _ _ _ _ _ Hbs)|].
intros i Hi HiE.
pose proof (rdn_nth tfibsegs mem 8 (Z_to_bv 64 w) bs i Hbs ltac:(lia)) as H1.
rewrite word_add_nat, u_Z2bv in H1 by lia.
pose proof (Hstr (Z.to_nat (w - bv_unsigned p) + i)%nat ltac:(lia)) as H2.
replace (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + i)) with (w + Z.of_nat i) in H2 by lia.
rewrite H1 in H2. injection H2 as H3. exact H3.
Qed.
Lemma cm_zb_byte : forall w bs i, cm_P <= w -> length bs = 8%nat -> (i < 8)%nat -> w + Z.of_nat i <= cm_E ->
(forall i, (i < 8)%nat -> w + Z.of_nat i <= cm_E ->
nth i bs NUL = nth (Z.to_nat (w - cm_P) + i) (s ++ [NUL]) NUL) ->
HZ.zb (bytes_le_to_Z bs) i = bv_unsigned (nth (Z.to_nat (w - cm_P) + i) (s ++ [NUL]) NUL).
Proof.
intros w bs i Hw Hlen Hi HiE Hnth. rewrite zb_of_bytes by lia. fold NUL. rewrite Hnth by lia. reflexivity.
Qed.
(* a word wholly before R has no NUL and no c *)
Lemma cm_word_before : forall w bs, cm_P <= w -> w + 8 <= cm_P + cm_R -> length bs = 8%nat ->
(forall i, (i < 8)%nat -> w + Z.of_nat i <= cm_E ->
nth i bs NUL = nth (Z.to_nat (w - cm_P) + i) (s ++ [NUL]) NUL) ->
HZ.Tz (bytes_le_to_Z bs) = 0 /\ HZ.Tz (Z.lxor (bytes_le_to_Z bs) cm_K) = 0.
Proof.
intros w bs Hw HwR Hlen Hnth. epl.
pose proof (bytes_le_to_Z_range bs Hlen) as Hx.
assert (Hc : forall i, (i < 8)%nat ->
HZ.zb (bytes_le_to_Z bs) i <> 0 /\ HZ.zb (bytes_le_to_Z bs) i <> bv_unsigned c).
{ intros i Hi. rewrite (cm_zb_byte w bs i) by (try exact Hnth; lia).
  destruct (cm_before (Z.to_nat (w - cm_P) + i) ltac:(lia)) as [H1 H2].
  split; [apply byte_nz_u; exact H1 | exact H2]. }
split.
- apply HZ.Tz_nozero; [exact Hx|]. intros i Hi. apply (Hc i Hi).
- apply HZ.Tz_nozero.
  + apply HZ.lxor_lt64; [exact Hx | apply cm_K_range].
  + intros i Hi. rewrite cm_zb_y by exact Hi. intros H0. apply (proj1 (Z.lxor_eq_0_iff _ _)) in H0.
    apply (Hc i Hi). exact H0.
Qed.
(* the word that holds R: when it has no NUL, it has c *)
Lemma cm_word_R : forall w bs, cm_P <= w <= cm_P + cm_R -> cm_P + cm_R < w + 8 -> length bs = 8%nat ->
(forall i, (i < 8)%nat -> w + Z.of_nat i <= cm_E ->
nth i bs NUL = nth (Z.to_nat (w - cm_P) + i) (s ++ [NUL]) NUL) ->
HZ.Tz (bytes_le_to_Z bs) = 0 -> HZ.Tz (Z.lxor (bytes_le_to_Z bs) cm_K) <> 0.
Proof.
intros w bs Hw HwR Hlen Hnth HT. epl.
pose proof (bytes_le_to_Z_range bs Hlen) as Hx.
set (i0 := Z.to_nat (cm_P + cm_R - w)).
assert (Hi0 : (i0 < 8)%nat) by (subst i0; lia).
assert (Hidx : (Z.to_nat (w - cm_P) + i0)%nat = cm_Rn) by (subst i0; lia).
assert (Hlow : forall j, (j < i0)%nat ->
HZ.zb (bytes_le_to_Z bs) j <> 0 /\ HZ.zb (bytes_le_to_Z bs) j <> bv_unsigned c).
{ intros j Hj. rewrite (cm_zb_byte w bs j) by (try exact Hnth; subst i0; lia).
  destruct (cm_before (Z.to_nat (w - cm_P) + j) ltac:(subst i0; lia)) as [H1 H2].
  split; [apply byte_nz_u; exact H1 | exact H2]. }
assert (Hat : HZ.zb (bytes_le_to_Z bs) i0 = bv_unsigned (nth cm_Rn (s ++ [NUL]) NUL)).
{ rewrite (cm_zb_byte w bs i0) by (try exact Hnth; subst i0; lia). rewrite Hidx. reflexivity. }
destruct cm_at as [H0|H0]; rewrite <- Hat in H0.
- exfalso. refine (HZ.Tz_haszero (bytes_le_to_Z bs) i0 Hx Hi0 H0 _ HT).
  intros j Hj. apply (Hlow j Hj).
- apply (HZ.Tz_haszero (Z.lxor (bytes_le_to_Z bs) cm_K) i0).
  + apply HZ.lxor_lt64; [exact Hx | apply cm_K_range].
  + exact Hi0.
  + rewrite cm_zb_y by exact Hi0. rewrite H0. apply Z.lxor_nilpotent.
  + intros j Hj. rewrite cm_zb_y by lia. intros Hz. apply (proj1 (Z.lxor_eq_0_iff _ _)) in Hz.
    apply (Hlow j Hj). exact Hz.
Qed.
(* L2, the word loop: a0 = w (the current word, which has no NUL), a4 = the word, a2 = C1, a3 = HIGHS,
   a5 = c * ONES; k counts the words left to the word that holds R *)
Lemma cm_words : forall k regs w bs,
w + 8 * Z.of_nat k = cm_P + cm_R - (cm_P + cm_R) mod 8 ->
cm_P <= w ->
rdn tfibsegs mem (Z_to_bv 64 w) 8 = Some bs ->
HZ.Tz (bytes_le_to_Z bs) = 0 ->
getr regs 10 = Z_to_bv 64 w ->
getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
getr regs 12 = Z_to_bv 64 C1 ->
getr regs 13 = Z_to_bv 64 HZ.HIGHS ->
getr regs 14 = Z_to_bv 64 (bytes_le_to_Z bs) ->
getr regs 15 = Z_to_bv 64 cm_K ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x68)) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (cm_P + cm_R)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs' r = getr regs r).
Proof.
induction k as [|k IH]; intros regs w bs Hk Hpw Hbs HT H10 H11 H12 H13 H14 H15.
all: epl.
all: pose proof cm_floor_le as HF.
all: assert (Hm2 : 0 <= (cm_P + cm_R) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
all: assert (HmE : 0 <= cm_E mod 8 < 8) by (apply Z.mod_pos_bound; lia).
all: destruct (cm_word_at w) as (bs0 & Hbs0 & Hlen & Hnth); [lia|lia|].
all: rewrite Hbs in Hbs0; injection Hbs0 as Hbs0; subst bs0.
all: pose proof (bytes_le_to_Z_range bs Hlen) as Hx.
all: set (x := bytes_le_to_Z bs) in *.
all: set (v := Z_to_bv 64 x) in *.
all: assert (Hv : bv_unsigned v = x) by (subst v; apply u_Z2bv; lia).
all: pose proof cm_K_range as HK.
all: set (y := Z.lxor x cm_K).
all: assert (Hy : 0 <= y < 2^64) by (subst y; apply HZ.lxor_lt64; lia).
all: set (vy := Z_to_bv 64 y).
all: assert (Hvy : bv_unsigned vy = y) by (subst vy; apply u_Z2bv; lia).
all: set (tw := v_and (v_or (v_sub (Z_to_bv 64 C1) vy) vy) (Z_to_bv 64 HZ.HIGHS)).
all: set (regs5 := regupd (regupd (regupd (regupd regs 14 vy) 16 (v_sub (Z_to_bv 64 C1) vy))
14 (v_or (v_sub (Z_to_bv 64 C1) vy) vy)) 14 tw).
all: assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x68)) mem rom)
(mkst regs5 (Z_to_bv 64 (tfib_A_strchrnul + 0x78)) mem rom)).
1,3: norm_pc;
stepov FC_068 DC_068 vy
ltac:(rewrite alu_xor; gr; rewrite H14, H15; unfold v_xor; rewrite Hv, (u_Z2bv cm_K) by lia; reflexivity);
stepov FC_06c DC_06c (v_sub (Z_to_bv 64 C1) vy) ltac:(rewrite alu_sub; gr; rewrite H12; reflexivity);
stepov FC_070 DC_070 (v_or (v_sub (Z_to_bv 64 C1) vy) vy) ltac:(rewrite alu_or; gr; reflexivity);
stepov FC_074 DC_074 tw ltac:(rewrite alu_and; gr; rewrite H13; reflexivity);
subst regs5; msteps_done.
all: assert (Htw : bv_unsigned tw = HZ.HIGHS - HZ.Tz y) by (subst tw; rewrite haszero_ref, Hvy; reflexivity).
all: pose proof (HZ.Tz_range y) as HTy.
- assert (HTnz : HZ.Tz y <> 0) by exact (cm_word_R w bs ltac:(lia) ltac:(lia) Hlen Hnth HT).
  destruct (cm_tail_b8 regs5 w) as (regs' & Hms & H10' & Hfr).
  { lia. }
  { subst regs5. gr. exact H10. }
  { subst regs5. gr. exact H11. }
  exists regs'. split; [|split].
  + eapply msteps_trans; [exact Hpre|].
    eapply msteps_trans; [|exact Hms].
    norm_pc.
    stepbt FC_078 DC_078
    ltac:(subst regs5; gr; rewrite H13; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
    rewrite Htw, u_Z2bv by (unfold HZ.HIGHS; lia); apply Z.eqb_neq; lia).
    msteps_done.
  + exact H10'.
  + intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr16). subst regs5.
    rewrite !getr_other by assumption. reflexivity.
- assert (HTy0 : HZ.Tz y = 0) by exact (proj2 (cm_word_before w bs ltac:(lia) ltac:(lia) Hlen Hnth)).
  destruct (cm_word_at (w + 8)) as (bs' & Hbs' & Hlen' & Hnth'); [lia|lia|].
  pose proof (bytes_le_to_Z_range bs' Hlen') as Hx'.
  set (x' := bytes_le_to_Z bs') in *.
  set (v' := Z_to_bv 64 x').
  assert (Hv' : bv_unsigned v' = x') by (subst v'; apply u_Z2bv; lia).
  set (tw' := v_and (v_or (v_sub (Z_to_bv 64 C1) v') v') (Z_to_bv 64 HZ.HIGHS)).
  assert (Htw' : bv_unsigned tw' = HZ.HIGHS - HZ.Tz x') by (subst tw'; rewrite haszero_ref, Hv'; reflexivity).
  pose proof (HZ.Tz_range x') as HTx'.
  set (regs7 := regupd (regupd (regupd (regupd (regupd (regupd regs5 14 v') 16 (Z_to_bv 64 (w + 8)))
  10 (v_sub (Z_to_bv 64 C1) v')) 10 (v_or (v_sub (Z_to_bv 64 C1) v') v')) 17 tw') 10 (Z_to_bv 64 (w + 8))).
  assert (Hmid : msteps tfibsegs (mkst regs5 (Z_to_bv 64 (tfib_A_strchrnul + 0x78)) mem rom)
  (mkst regs7 (Z_to_bv 64 (tfib_A_strchrnul + 0x94)) mem rom)).
  { norm_pc.
    stepbf FC_078 DC_078
    ltac:(subst regs5; gr; rewrite H13; cbn [branch_taken]; apply negb_false_iff; unfold bv_eqb;
    rewrite Htw, HTy0, u_Z2bv by (unfold HZ.HIGHS; lia); rewrite Z.sub_0_r; apply Z.eqb_refl).
    chain_step; [reflexivity | eapply step_ld with (bs := bs') (v := v');
    [ exact_lit FC_07c | reflexivity | exact DC_07c
    | subst regs5; gr; rewrite H10; imm_norm; rewrite v_addi_lit; exact Hbs'
    | rewrite Hv'; reflexivity ] | step_simpl ].
    stepiv' FC_080 DC_080 (Z_to_bv 64 (w + 8))
    ltac:(subst regs5; gr; rewrite H10; imm_norm; rewrite v_addi_lit; reflexivity).
    stepov FC_084 DC_084 (v_sub (Z_to_bv 64 C1) v') ltac:(rewrite alu_sub; subst regs5; gr; rewrite H12; reflexivity).
    stepov FC_088 DC_088 (v_or (v_sub (Z_to_bv 64 C1) v') v') ltac:(rewrite alu_or; gr; reflexivity).
    stepov FC_08c DC_08c tw' ltac:(rewrite alu_and; subst regs5; gr; rewrite H13; reflexivity).
    stepiv' FC_090 DC_090 (Z_to_bv 64 (w + 8)) ltac:(gr; imm_norm; apply v_addi_0).
    subst regs7 regs5. msteps_done. }
  destruct (Z.eq_dec (HZ.Tz x') 0) as [HTz'|HTz'].
  + destruct (IH regs7 (w + 8) bs') as (regs' & Hms & H10' & Hfr).
    { lia. }
    { lia. }
    { exact Hbs'. }
    { exact HTz'. }
    { subst regs7. gr. reflexivity. }
    { subst regs7 regs5. gr. exact H11. }
    { subst regs7 regs5. gr. exact H12. }
    { subst regs7 regs5. gr. exact H13. }
    { subst regs7. gr. reflexivity. }
    { subst regs7 regs5. gr. exact H15. }
    exists regs'. split; [|split].
    * eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
      eapply msteps_trans; [|exact Hms]. norm_pc.
      stepbt FC_094 DC_094
      ltac:(subst regs7 regs5; gr; rewrite H13; cbn [branch_taken]; unfold bv_eqb;
      rewrite Htw', HTz', u_Z2bv by (unfold HZ.HIGHS; lia); rewrite Z.sub_0_r; apply Z.eqb_refl).
      msteps_done.
    * exact H10'.
    * intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
      rewrite (Hfr r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17). subst regs7 regs5.
      rewrite !getr_other by assumption. reflexivity.
  + destruct (cm_tail_bc regs7 (w + 8)) as (regs' & Hms & H10' & Hfr).
    { lia. }
    { subst regs7. gr. reflexivity. }
    { subst regs7 regs5. gr. exact H11. }
    exists regs'. split; [|split].
    * eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
      eapply msteps_trans; [|exact Hms]. norm_pc.
      stepbf FC_094 DC_094
      ltac:(subst regs7 regs5; gr; rewrite H13; cbn [branch_taken]; unfold bv_eqb;
      rewrite Htw', u_Z2bv by (unfold HZ.HIGHS; lia); apply Z.eqb_neq; lia).
      stepj' FC_098 DC_098.
      msteps_done.
    * exact H10'.
    * intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12). subst regs7 regs5.
      rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma cm_rd_C1 : exists bs, rdn tfibsegs mem (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100) 8 = Some bs /\ bytes_le_to_Z bs = C1.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
Lemma cm_rd_HIGHS : exists bs, rdn tfibsegs mem (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080) 8 = Some bs /\ bytes_le_to_Z bs = HZ.HIGHS.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
(* the word-loop set-up at 0x3c: a0 = q, the first aligned address, P <= q <= R *)
Lemma cm_aligned : forall regs (q : Z),
cm_P <= q <= cm_P + cm_R -> q mod 8 = 0 ->
getr regs 10 = Z_to_bv 64 q ->
getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x3c)) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (cm_P + cm_R)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs' r = getr regs r).
Proof.
intros regs q Hq Hq8 H10 H11. epl.
pose proof cm_floor_le as HF.
assert (HA8 : cm_P + cm_R = 8 * ((cm_P + cm_R) / 8) + (cm_P + cm_R) mod 8) by (apply Z.div_mod; lia).
assert (Hq8' : q = 8 * (q / 8)) by (pose proof (Z.div_mod q 8 ltac:(lia)); lia).
assert (Hm2 : 0 <= (cm_P + cm_R) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HmE : 0 <= cm_E mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct cm_rd_C1 as (bs1 & Hbs1 & Hv1).
destruct cm_rd_HIGHS as (bs2 & Hbs2 & Hv2).
destruct (cm_word_at q) as (bs & Hbs & Hlen & Hnth); [lia|lia|].
pose proof (bytes_le_to_Z_range bs Hlen) as Hx.
set (x := bytes_le_to_Z bs) in *.
set (v := Z_to_bv 64 x).
assert (Hv : bv_unsigned v = x) by (subst v; apply u_Z2bv; lia).
set (tw := v_and (v_or (v_sub (Z_to_bv 64 C1) v) v) (Z_to_bv 64 HZ.HIGHS)).
assert (Htw : bv_unsigned tw = HZ.HIGHS - HZ.Tz x) by (subst tw; rewrite haszero_ref, Hv; reflexivity).
pose proof (HZ.Tz_range x) as HTx.
set (regs2 := regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
12 (Z_to_bv 64 cm_aui1)) 12 (Z_to_bv 64 C1)) 14 v)
13 (Z_to_bv 64 cm_aui2)) 13 (Z_to_bv 64 HZ.HIGHS))
15 (v_sub (Z_to_bv 64 C1) v)) 15 (v_or (v_sub (Z_to_bv 64 C1) v) v)) 15 tw).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x3c)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_strchrnul + 0x5c)) mem rom)).
{ norm_pc.
stepiv' FC_03c DC_03c (Z_to_bv 64 cm_aui1) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs1) (v := Z_to_bv 64 C1);
[ exact_lit FC_040 | reflexivity | exact DC_040
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100) by bveq end; exact Hbs1
| rewrite Hv1; reflexivity ] | step_simpl ].
chain_step; [reflexivity | eapply step_ld with (bs := bs) (v := v);
[ exact_lit FC_044 | reflexivity | exact DC_044
| gr; rewrite H10; imm_norm; rewrite v_addi_0; exact Hbs
| rewrite Hv; reflexivity ] | step_simpl ].
stepiv' FC_048 DC_048 (Z_to_bv 64 cm_aui2) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs2) (v := Z_to_bv 64 HZ.HIGHS);
[ exact_lit FC_04c | reflexivity | exact DC_04c
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080) by bveq end; exact Hbs2
| rewrite Hv2; reflexivity ] | step_simpl ].
stepov FC_050 DC_050 (v_sub (Z_to_bv 64 C1) v) ltac:(rewrite alu_sub; gr; reflexivity).
stepov FC_054 DC_054 (v_or (v_sub (Z_to_bv 64 C1) v) v) ltac:(rewrite alu_or; gr; reflexivity).
stepov FC_058 DC_058 tw ltac:(rewrite alu_and; gr; reflexivity).
subst regs2. msteps_done. }
destruct (Z.eq_dec (HZ.Tz x) 0) as [HTz|HTz].
- set (regs3 := regupd (regupd regs2 15 (Z_to_bv 64 (C1 + 1))) 15 (Z_to_bv 64 cm_K)).
  destruct (cm_words (Z.to_nat ((cm_P + cm_R) / 8 - q / 8)) regs3 q bs) as (regs' & Hms & H10' & Hfr).
  { lia. }
  { lia. }
  { exact Hbs. }
  { exact HTz. }
  { subst regs3 regs2. gr. exact H10. }
  { subst regs3 regs2. gr. exact H11. }
  { subst regs3 regs2. gr. reflexivity. }
  { subst regs3 regs2. gr. reflexivity. }
  { subst regs3 regs2. gr. reflexivity. }
  { subst regs3. gr. reflexivity. }
  exists regs'. split; [|split].
  + eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [|exact Hms]. norm_pc.
    stepbf FC_05c DC_05c
    ltac:(subst regs2; gr; cbn [branch_taken]; apply negb_false_iff; unfold bv_eqb;
    rewrite Htw, HTz, u_Z2bv by (unfold HZ.HIGHS; lia); rewrite Z.sub_0_r; apply Z.eqb_refl).
    stepiv' FC_060 DC_060 (Z_to_bv 64 (C1 + 1)) ltac:(subst regs2; gr; imm_norm; apply v_addi_lit).
    stepiv' FC_064 DC_064 (Z_to_bv 64 cm_K)
    ltac:(subst regs2; gr; rewrite H11; unfold v_mul; rewrite u_zext8, (u_Z2bv (C1 + 1)) by (unfold C1; lia);
    reflexivity).
    subst regs3 regs2. msteps_done.
  + exact H10'.
  + intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
    subst regs3 regs2. rewrite !getr_other by assumption. reflexivity.
- destruct (cm_tail_b8 regs2 q) as (regs' & Hms & H10' & Hfr).
  { lia. }
  { subst regs2. gr. exact H10. }
  { subst regs2. gr. exact H11. }
  exists regs'. split; [|split].
  + eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [|exact Hms]. norm_pc.
    stepbt FC_05c DC_05c
    ltac:(subst regs2; gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
    rewrite Htw, u_Z2bv by (unfold HZ.HIGHS; lia); apply Z.eqb_neq; lia).
    msteps_done.
  + exact H10'.
  + intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr16). subst regs2.
    rewrite !getr_other by assumption. reflexivity.
Qed.
(* L1, the byte loop before alignment: a0 = P + j, a2 = P + j + 1, j <= R;
   m counts the passes left until a0 + 1 is aligned *)
Lemma cm_bytes : forall m regs (j : nat),
cm_P mod 8 <> 0 ->
(0 < m)%nat -> Z.of_nat j + Z.of_nat m = 8 - cm_P mod 8 ->
(j <= cm_Rn)%nat ->
getr regs 10 = Z_to_bv 64 (cm_P + Z.of_nat j) ->
getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
getr regs 12 = Z_to_bv 64 (cm_P + Z.of_nat j + 1) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x20)) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (cm_P + cm_R)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs' r = getr regs r).
Proof.
induction m as [|m IH]; intros regs j HA Hm Hjm Hj H10 H11 H12; [lia|].
epl.
assert (HA8 : 0 <= cm_P mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HP8 : cm_P = 8 * (cm_P / 8) + cm_P mod 8) by (apply Z.div_mod; lia).
assert (Hm8 : 0 <= (cm_P + Z.of_nat j + 1) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (b := nth j (s ++ [NUL]) NUL).
set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x20)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_strchrnul + 0x24)) mem rom)).
{ norm_pc.
steplbu FC_020 DC_020
ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0;
replace (cm_P + Z.of_nat j) with (bv_unsigned p + Z.of_nat j) by lia;
apply Hstr; lia).
subst regs1 b. msteps_done. }
destruct (Nat.eq_dec j cm_Rn) as [HjR|HjR].
- assert (Hb : bv_unsigned b = 0 \/ bv_unsigned b = bv_unsigned c) by (subst b; rewrite HjR; exact cm_at).
  exists regs1. split; [|split].
  + eapply msteps_trans; [exact Hpre|]. norm_pc.
    destruct Hb as [Hb|Hb].
    * stepbt FC_024 DC_024
      ltac:(subst regs1; gr; cbn [branch_taken]; unfold bv_eqb; rewrite u_zext8, u_lit0, Hb; reflexivity).
      msteps_done.
    * stepbf FC_024 DC_024
      ltac:(subst regs1; gr; cbn [branch_taken]; unfold bv_eqb; rewrite u_zext8, u_lit0, Hb;
      apply Z.eqb_neq; exact Hcz).
      stepbt FC_028 DC_028
      ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb; rewrite !u_zext8, Hb;
      apply Z.eqb_refl).
      msteps_done.
  + subst regs1. gr. rewrite H10. f_equal. lia.
  + intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. subst regs1. rewrite !getr_other by assumption. reflexivity.
- destruct (cm_before j ltac:(lia)) as [Hb0 Hbc].
  assert (Hbn : bv_unsigned b <> 0) by (apply byte_nz_u; exact Hb0).
  assert (Hbc' : bv_unsigned b <> bv_unsigned c) by exact Hbc.
  set (regs2 := regupd (regupd (regupd regs1
  10 (Z_to_bv 64 (cm_P + Z.of_nat j + 1)))
  13 (Z_to_bv 64 ((cm_P + Z.of_nat j + 1) mod 8)))
  12 (Z_to_bv 64 (cm_P + Z.of_nat j + 2))).
  assert (Hmid : msteps tfibsegs (mkst regs1 (Z_to_bv 64 (tfib_A_strchrnul + 0x24)) mem rom)
  (mkst regs2 (Z_to_bv 64 (tfib_A_strchrnul + 0x38)) mem rom)).
  { norm_pc.
    stepbf FC_024 DC_024
    ltac:(subst regs1; gr; cbn [branch_taken]; unfold bv_eqb; rewrite u_zext8, u_lit0;
    apply Z.eqb_neq; exact Hbn).
    stepbf FC_028 DC_028
    ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb; rewrite !u_zext8;
    apply Z.eqb_neq; exact Hbc').
    stepiv' FC_02c DC_02c (Z_to_bv 64 (cm_P + Z.of_nat j + 1))
    ltac:(subst regs1; gr; rewrite H10; imm_norm; rewrite v_addi_lit; reflexivity).
    stepiv' FC_030 DC_030 (Z_to_bv 64 ((cm_P + Z.of_nat j + 1) mod 8))
    ltac:(subst regs1; gr; rewrite H12; imm_norm; unfold v_andi; rewrite u_Z2bv by lia;
    change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    stepiv' FC_034 DC_034 (Z_to_bv 64 (cm_P + Z.of_nat j + 2))
    ltac:(subst regs1; gr; rewrite H12; imm_norm; rewrite v_addi_lit; f_equal; lia).
    subst regs2 regs1. msteps_done. }
  destruct (Z.eq_dec ((cm_P + Z.of_nat j + 1) mod 8) 0) as [Hal|Hal].
  + destruct (cm_aligned regs2 (cm_P + Z.of_nat j + 1)) as (regs' & Hms & H10' & Hfr).
    { lia. }
    { exact Hal. }
    { subst regs2. gr. reflexivity. }
    { subst regs2 regs1. gr. exact H11. }
    exists regs'. split; [|split].
    * eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
      eapply msteps_trans; [|exact Hms]. norm_pc.
      stepbf FC_038 DC_038 ltac:(subst regs2; gr; rewrite Hal; vm_compute; reflexivity).
      msteps_done.
    * exact H10'.
    * intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
      subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
  + assert (Hm' : (0 < m)%nat).
    { destruct m; [|lia]. exfalso. apply Hal.
      replace (cm_P + Z.of_nat j + 1) with (8 * (cm_P / 8 + 1)) by lia.
      rewrite Z.mul_comm. apply Z_mod_mult. }
    destruct (IH regs2 (S j)) as (regs' & Hms & H10' & Hfr).
    { exact HA. }
    { exact Hm'. }
    { lia. }
    { lia. }
    { subst regs2. gr. f_equal. lia. }
    { subst regs2 regs1. gr. exact H11. }
    { subst regs2. gr. f_equal. lia. }
    exists regs'. split; [|split].
    * eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
      eapply msteps_trans; [|exact Hms]. norm_pc.
      stepbt FC_038 DC_038
      ltac:(subst regs2; gr; cbn [branch_taken]; apply negb_true_iff; apply eqb_w_false; lia).
      msteps_done.
    * exact H10'.
    * intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
      subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
(* 0x14, the loops' entry: a0 = s, a1 = c *)
Lemma cm_entry : forall regs,
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x14)) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (bv_unsigned p + Z.of_nat (PPgWrap.cspn_len [c] s))
/\ (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs' r = getr regs r).
Proof.
intros regs H10 H11. epl.
change (bv_unsigned p + Z.of_nat (PPgWrap.cspn_len [c] s)) with (cm_P + cm_R).
assert (HA8 : 0 <= cm_P mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs1 := regupd regs 12 (Z_to_bv 64 (cm_P mod 8))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_strchrnul + 0x14)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_strchrnul + 0x18)) mem rom)).
{ norm_pc.
stepiv' FC_014 DC_014 (Z_to_bv 64 (cm_P mod 8))
ltac:(gr; rewrite H10; imm_norm; unfold v_andi;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
subst regs1. msteps_done. }
destruct (Z.eq_dec (cm_P mod 8) 0) as [HA|HA].
- destruct (cm_aligned regs1 cm_P) as (regs' & Hms & H10' & Hfr).
  { lia. }
  { exact HA. }
  { subst regs1. gr. rewrite H10. unfold cm_P. symmetry. apply Z_to_bv_bv_unsigned. }
  { subst regs1. gr. exact H11. }
  exists regs'. split; [|split].
  + eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [|exact Hms]. norm_pc.
    stepbt FC_018 DC_018 ltac:(subst regs1; gr; rewrite HA; vm_compute; reflexivity).
    msteps_done.
  + exact H10'.
  + intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
    subst regs1. rewrite !getr_other by assumption. reflexivity.
- set (regs2 := regupd regs1 12 (Z_to_bv 64 (cm_P + Z.of_nat 0 + 1))).
  destruct (cm_bytes (Z.to_nat (8 - cm_P mod 8)) regs2 0) as (regs' & Hms & H10' & Hfr).
  { exact HA. }
  { lia. }
  { lia. }
  { lia. }
  { subst regs2 regs1. gr. rewrite H10. symmetry. exact cm_p_lit. }
  { subst regs2 regs1. gr. exact H11. }
  { subst regs2. gr. reflexivity. }
  exists regs'. split; [|split].
  + eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [|exact Hms]. norm_pc.
    stepbf FC_018 DC_018 ltac:(subst regs1; gr; cbn [branch_taken]; apply eqb_w_false; lia).
    stepiv' FC_01c DC_01c (Z_to_bv 64 (cm_P + Z.of_nat 0 + 1))
    ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi; f_equal; lia).
    subst regs2 regs1. msteps_done.
  + exact H10'.
  + intros r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
    subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
End h.
Theorem cs_musl_loops : CS_MUSL_LOOPS.
Proof.
unfold CS_MUSL_LOOPS. intros s c p mem rom regs Hnul Hc Hfit Hstr Hrd Hrom H10 H11.
change (Z_to_bv 64 CS_LOOP) with (Z_to_bv 64 (tfib_A_strchrnul + 0x14)).
change (Z_to_bv 64 CS_LOOP_END) with (Z_to_bv 64 (tfib_A_strchrnul + 0xd0)).
eapply cm_entry; eassumption.
Qed.
End g.
