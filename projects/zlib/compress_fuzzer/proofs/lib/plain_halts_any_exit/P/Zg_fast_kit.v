(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_rod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_FAST_AOUT : Z := 0x19014.
Definition Z_FAST_HEAD : Z := 0x19024.
Definition Z_FAST_HASH : Z := 0x19050.
Definition Z_FAST_MTEST : Z := 0x190cc.
Definition Z_FAST_DIST : Z := 0x190d4.
Definition Z_FAST_LMCALL : Z := 0x192a0.
Definition Z_FAST_LIT : Z := 0x192b0.
Definition Z_FAST_FBA : Z := 0x19340.
Definition Z_FAST_TAIL : Z := 0x19408.
Definition Z_FAST_FBB : Z := 0x1942c.
Definition Z_FAST_FBC : Z := 0x19450.
Definition Z_FAST_EPI : Z := 0x195d8.

(* 1.4 (zl14-cmp): sp+0 is never written (junk), 0xffffffff moves to sp+8, &dyn_dtree lives in s9 (no frame slot),
   _length_code / _dist_code are pc-relative in s4 / s8 (1.3.1: GOT loads into s9 / s4), 0xffff moves s8 -> s11. *)
Definition fast_frame (j0 : list byte) (flush : Z) (r : sregs) : list cell :=
  [CB 8 j0; C8 (wz 4294967295); C8 (wz flush); C8 (r_s11 r); C8 (r_s10 r); C8 (r_s9 r); C8 (r_s8 r); C8 (r_s7 r); C8 (r_s6 r);
   C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].

Definition fastR (L : dlay) (r : sregs) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word) : bvmap 5 word :=
  mkR x1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) x5 x6 x7 (wz (dl_As L)) (wz 261) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (wz Z_LENGTH_CODE) (wz (-1)) (wz (dl_As L + 212)) (wz (dl_As L + 5888)) (wz Z_DIST_CODE) (wz (dl_As L + 2504)) (wz 3) (wz 65535) x28 x29 x30 x31.

Definition FINV (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ dout m L rest0 (ds_strm X) /\ Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat
  /\ (exists j0, rw_cells psegs m (bv_unsigned (r_sp r) + -128) (fast_frame j0 flush r))
  /\ stk psegs m lo (bv_unsigned (r_sp r) + -128)
  /\ munch (slow_W L rest0 lo r) me m /\ wmono psegs me m /\ mem_inv psegs m.

Definition FK (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom psegs)).

Definition FKA (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 y10 y11 (wz (ds_strstart X)) y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz Z_FAST_FBA) fc None m' (seg_rom psegs)).

Definition FKD (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz (ds_match_length X)) y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz Z_FAST_DIST) fc None m' (seg_rom psegs)).

Definition FKL (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) (hh : Z) : Prop :=
  forall (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 y10 (wz hh) y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz Z_FAST_LMCALL) fc None m' (seg_rom psegs)).

Definition FK9 (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                          (wz Z_LENGTH_CODE) (wz (-1)) (wz (dl_As L + 212)) (wz (dl_As L + 5888)) (wz Z_DIST_CODE) (wz (dl_As L + 2504)) (wz 3) (wz 65535) y28 y29 y30 y31)
                     F (wz pc) fc None m' (seg_rom psegs)).

Definition FKs (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                          y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                     F (wz pc) fc None m' (seg_rom psegs)).

Definition FKret (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (code : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 (wz code) y11 y12 y13 y14 y15 y16 y17 y18 y19
                          y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                     F (wz Z_FAST_EPI) fc None m' (seg_rom psegs)).

Lemma fst_prf : forall {A B} (a : A) (b : B), fst (a, b) = a. Proof. reflexivity. Qed.
Lemma snd_prf : forall {A B} (a : A) (b : B), snd (a, b) = b. Proof. reflexivity. Qed.

Section KIT.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma fast_epi : forall (dF : deflate_state) (code : Z), FKret L flush rest0 lo r F fc me (slow_post_gen r F fc L dF code inp rest0 lo me) code dF.
Proof.
  intros dF code. unfold FKret. intros until m'. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI). unfold fast_frame in FR. unfold Z_FAST_EPI.
  pose proof (slow_din L inp rest0 lo r me CTX m' MU) as DIN. unfold slow_W in MU.
  pose proof (sc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_SLOW_STACK in LOsp.
  do 15 zs.
  release_frame FR STK (bv_unsigned (r_sp r)).
  apply evt_done. unfold slow_post_gen. do 14 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.
End KIT.
