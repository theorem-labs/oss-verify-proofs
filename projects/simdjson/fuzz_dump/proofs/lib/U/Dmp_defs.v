(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Export Layout El_os_defs El_ins_iface.
From OSSVerify.simdjson.fuzz_dump.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition DMP_LFTOI : Z := 0x3a5fc.
Definition DMP_LFTOI_GATE : Z := 0x3a664.
Definition DMP_OKARM : Z := 0x3a674.
Definition DMP_OKARM_CTOR_RET : Z := 0x3a684.
Definition DMP_OKARM_PJ_RET : Z := 0x3a698.
Definition DMP_JOIN : Z := 0x3a6cc.
Definition DMP_PDTOR_RET : Z := 0x3a6d4.
Definition DMP_OKARM_STACK : Z := 212992.
Definition DMP_UNIMP_LFTOI : Z := 0x3a6f0.
Definition DMP_UNIMP_PJ : Z := 0x3aee4.

Definition DMP_PJ : Z := 0x3a808.
Definition DMP_PJ_FRAME : Z := 192.
Definition DMP_PJ_DISPATCH : Z := 0x3a880.
Definition DMP_PJ_EXIT : Z := 0x3ae20.

Definition DMP_INS_B : Z := 0x7d8f4.
Definition DMP_NPB_SLOT : Z := 0xd58b0.
Definition DMP_NP_BOOL : Z := 0x88638.

Definition dmp_dcc (m : word -> option byte) : Prop := rw_cells usegs m DMP_NPB_SLOT [C8 (Z_to_bv 64 DMP_NP_BOOL)].

Definition DMP_LIT_LBRACE : Z := 0x13072.
Definition DMP_LIT_LBRACK : Z := 0x1117a.
Definition DMP_LIT_COMMA : Z := 0x1117c.
Definition DMP_LIT_RBRACK : Z := 0x12082.
Definition DMP_LIT_RBRACE : Z := 0x104d1.
Definition DMP_LIT_QUOTE : Z := 0x1233a.
Definition DMP_LIT_QCOLON : Z := 0x13205.
Definition DMP_LIT_NULL : Z := 0x10e1a.

Definition lit (A : Z) (n : nat) : list byte := match image_bytes usegs A n with Some bs => bs | None => [] end.
Lemma lit_bytes : forall A n, ro_bytes_b usegs A (lit A n) = true -> length (lit A n) = n -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  forall m, mem_inv usegs m -> bytes_at usegs m A (lit A n).
Proof.
  intros A n RB L A0 AH m MI. apply ro_bytes_at; [exact MI| lia| rewrite L; lia| apply ro_bytes_b_sound; exact RB].
Qed.

Ltac lit_at A n m MI H HL :=
  pose proof (lit_bytes A n ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) m MI) as H;
  assert (HL : Z.of_nat (length (lit A n)) = Z.of_nat n) by (vm_compute; reflexivity).

Lemma lit_lbrace : lit DMP_LIT_LBRACE 1 = [Z_to_bv 8 123]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_lbrack : lit DMP_LIT_LBRACK 1 = [Z_to_bv 8 91]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_comma : lit DMP_LIT_COMMA 1 = [Z_to_bv 8 44]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_rbrack : lit DMP_LIT_RBRACK 1 = [Z_to_bv 8 93]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_rbrace : lit DMP_LIT_RBRACE 1 = [Z_to_bv 8 125]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_quote : lit DMP_LIT_QUOTE 1 = [Z_to_bv 8 34]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_qcolon : lit DMP_LIT_QCOLON 3 = [Z_to_bv 8 34; Z_to_bv 8 58; Z_to_bv 8 32]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_null : lit DMP_LIT_NULL 4 = [Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 108; Z_to_bv 8 108]. Proof. vm_compute. reflexivity. Qed.
Lemma lit_ro : ro_bytes_b usegs DMP_LIT_LBRACE (lit DMP_LIT_LBRACE 1) = true /\ ro_bytes_b usegs DMP_LIT_LBRACK (lit DMP_LIT_LBRACK 1) = true
  /\ ro_bytes_b usegs DMP_LIT_COMMA (lit DMP_LIT_COMMA 1) = true /\ ro_bytes_b usegs DMP_LIT_RBRACK (lit DMP_LIT_RBRACK 1) = true
  /\ ro_bytes_b usegs DMP_LIT_RBRACE (lit DMP_LIT_RBRACE 1) = true /\ ro_bytes_b usegs DMP_LIT_QUOTE (lit DMP_LIT_QUOTE 1) = true
  /\ ro_bytes_b usegs DMP_LIT_QCOLON (lit DMP_LIT_QCOLON 3) = true /\ ro_bytes_b usegs DMP_LIT_NULL (lit DMP_LIT_NULL 4) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition pjsaves (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma pjsaves_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, cells_size (pjsaves ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. intros. reflexivity. Qed.

Definition pjolits : list cell :=
  [C8 (Z_to_bv 64 DMP_LIT_RBRACE); C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 0x100000001); C8 (Z_to_bv 64 0x4020200)].
Lemma pjolits_size : cells_size pjolits = 32%nat. Proof. reflexivity. Qed.

Definition ins_b_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill v pp ep : Z) (pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - INS_DEPTH)%Z -> (0x10b000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xea088 + 48) ->
  rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) -> PUTINV OS pp ep -> FILLOK fill ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z -> (v = 0 \/ v = 1)%Z ->
  rw_cells usegs m 0xea088 [C8 (Z_to_bv 64 0x10a380)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> dmp_dcc m -> mem_inv usegs m ->
  evt usegs (ins_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS 0x1002 (fill_after fill) j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DMP_INS_B) fc None m (seg_rom usegs)).
