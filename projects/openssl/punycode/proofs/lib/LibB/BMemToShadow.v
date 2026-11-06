(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_m2s stops := wp_go 0x1bf9b8 79%nat C_memtoshadow_eq C_memtoshadow stops.

Definition KS_M2S : list nat := [5; 10; 11; 12; 13; 14; 15; 16; 17]%nat.

(* [comment removed for export] *)
Lemma lowmem_end_val :
  v_and (v_addi (v_sltu (W SB) (W (SB + -1))) (-1)) (W (SB + -1)) = W (SB - 1).
Proof. apply bv_eq. reflexivity. Qed.

Lemma midbeg_m1_val : W (0 + -1) = W (2 ^ 64 - 1).
Proof. apply bv_eq. reflexivity. Qed.

Lemma hishadow_end_val : v_add (v_srli (W (HIMEM_END - 1)) 3) (W SB) = W (HIMEM_BEG - 1).
Proof. apply bv_eq. reflexivity. Qed.

Theorem memtoshadow_cps : forall rom (Post : word -> regfile -> mem -> Prop) M x l,
  rt_ok M -> inmem x ->
  length l = 32%nat -> rget l 10 = W x ->
  (forall l', length l' = 32%nat -> same_except KS_M2S l l' -> rget l' 10 = W (sha x) ->
              reach BSEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1bf9b8) l M Post.
Proof.
  intros rom Post M x l (H1 & H2 & H3 & H4 & H5 & (v6 & H6) & H7 & H8 & _) Hx Hl H10 K.
  unfold G_SB, C_SB, G_MIDBEG, C_MIDBEG, G_MIDEND, C_MIDEND, G_HIEND, C_HIEND in *.
  regs_open l Hl. subst a0. cbn [rget lget] in K.
  assert (Hxr : 0 <= x < 2 ^ 64) by (unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END in Hx; lia).
  assert (Esh : v_add (W SB) (v_srli (W x) 3) = W (sha x)).
  { rewrite srli3_W by lia. rewrite add_W. f_equal. unfold sha. lia. }
  wp_m2s [0x1bfa24]. mem_auto. rewrite lowmem_end_val. rewrite Esh.
  split; intros Hb1.
  - apply K; [reflexivity | same_ex | reflexivity].
  - mem_auto. rewrite midbeg_m1_val.
    split; intros Hb2.
    + mem_auto. rewrite hishadow_end_val. rewrite !Wu in * by (unfold SB, HIMEM_BEG, HIMEM_END in *; lia).
      split; intros Hb3; [exfalso; unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END, SB in *; lia|].
      split; intros Hb4; [exfalso; unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END, SB in *; lia|].
      apply K; [reflexivity | same_ex | reflexivity].
    + exfalso. rewrite !Wu in Hb2 by lia. lia.
Qed.
