(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs: reply image row img-constapart-B (its CONST_APART half) of the cf layer at plugin-hostd/fuzz_reply.
   rule 24: no function proved (kind: closed image fact over the constant-cell table of reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   CONST_APART, proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:66-70 @ fa961f42daf, over the image class
   (Context {IM : AImg}).  Reply does not carry YGcfInstDrainX.v nor YGcfInstBase.v, so the Lemma states the body of
   CONST_APART VERBATIM at reply's instance IM := AImg_reply (B/AGif2reply.v:24: im_syms := YF0m.TfibSyms,
   im_const := YF0m.Tfib_const), with the premise ly_img_ok B ly unfolded; ly_img_ok is
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstBase.v:140-142 @ fa961f42daf (= @ e73dee6cc107):
   ly_img_ok B ly := layout_ok ly /\ ly_tsd ly = as_tsd B /\
                     Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B).
   qhdr is DMiface.qhdr, the same text in reply (B/DMiface.v:73-75) as in the layer
   (proofs/cgif/cgif_file_fuzzer/lib/DMiface.v:69-71 @ fa961f42daf).
   Proof at image B: the third conjunct puts the image window ly_img around [TFIB_IMG_LO, TFIB_IMG_END) (two scans of
   Tfib_owned_static ++ Tfib_zero_shadow, B/YF0m.v:819-854).  Each cell of Tfib_const passes the check const_apart_okb
   by computation (cgif's pattern: YFev.const_loc_okd / Tfib_const_locd, B/YFev.v:394-410, with the cell's value
   added for the mutex cell): an absolute, TSD, TP or instance cell lies in the image or the image's shadow and off
   the instance's quarantine header words; an AT / AC / AD cell lies in (ly_T, 80) / (ly_C, 256) / (ly_D, 4096); the
   one exception is the 2-byte zero cell at inst + o_q_cmutex + 2.  lo_disj / lo_app / lo_high of layout_ok keep
   these apart from the thread's quarantine header (ly_T + t_qc, 32) and the primary reserve. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMiface.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The check of one constant cell, by computation. *)
Definition in_img_or_shadow (a w : Z) : bool :=
  ((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) ||
  ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition apart_q (a w : Z) : bool :=
  ((a + w <=? TFIB_INST + o_quar + 152) || (TFIB_INST + o_quar + 156 <=? a)) &&
  ((a + w <=? TFIB_INST + o_quar + 160) || (TFIB_INST + o_quar + 192 <=? a)).
Definition aval_is_zero (v : aval) : bool := match v with AV (ANum z) => z =? 0 | _ => false end.
Definition const_apart_okb (c : acell) : bool :=
  let w := Z.max 1 (Z.of_nat (c_w c)) in
  match c_at c with
  | ANum a => (in_img_or_shadow a w && apart_q a w) ||
              ((a =? TFIB_INST + o_q_cmutex + 2) && Nat.eqb (c_w c) 2 && aval_is_zero (c_val c))
  | AT o => (0 <=? o) && (o + w <=? t_qc)
  | AC o => (0 <=? o) && (o + w <=? 256)
  | AD o => (0 <=? o) && (o + w <=? 4096)
  | ATsd o => in_img_or_shadow (TFIB_TSD + o) w && apart_q (TFIB_TSD + o) w
  | ATp o => in_img_or_shadow (TFIB_TP + o) w && apart_q (TFIB_TP + o) w
  | AInst o => in_img_or_shadow (TFIB_INST + o) w && apart_q (TFIB_INST + o) w
  | _ => false
  end.
Lemma Tfib_const_apart_okb : forall ly, forallb const_apart_okb (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Lemma aval_is_zero_eq : forall v, aval_is_zero v = true -> v = AV (ANum 0).
Proof.
intros v H. destruct v as [e|m x]; [|discriminate H]. destruct e; try discriminate H.
apply Z.eqb_eq in H. subst. reflexivity.
Qed.

(* Two extents of a layout_ok layout on either side of a cut of static_extents are apart (lo_disj). *)
Lemma static_apart : forall {rc : YM05.RunCeil} ly n x y, layout_ok ly ->
  In x (firstn n (static_extents ly)) -> In y (skipn n (static_extents ly)) -> zdisjoint x y.
Proof.
intros rc ly n x y LO Hx Hy.
exact (pairwise_In zdisjoint (static_extents ly) x y _ _ (eq_sym (firstn_skipn n _)) (lo_disj _ LO) Hx Hy).
Qed.
Local Ltac mem_static := unfold static_extents, owned_extents; cbn [firstn skipn app In];
  repeat (first [left; reflexivity | right]).
Local Ltac mem_owned := unfold owned_extents; cbn [In]; repeat (first [left; reflexivity | right]).

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* CONST_APART at image B: YGcfInstDrainX.v:66-70 @ fa961f42daf, ly_img_ok unfolded, at IM := AImg_reply. *)
Lemma CONST_APART_B : forall B ly c, @im_syms AImg_reply B ->
  (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) ->
  In c (@im_const AImg_reply ly) ->
  (aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
   ~ DMiface.qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\
   ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize)).
Proof.
intros B ly c TS (LO & HTSD & SUB) Hc. change (TfibSyms B) in TS. change (In c (Tfib_const ly)) in Hc.
pose proof (ts_inst B TS) as EI. rewrite (ts_tsd B TS) in HTSD. pose proof (ts_tp B TS) as ETP.
rewrite (ts_owned B TS), (ts_zsh B TS) in SUB.
(* the image window covers the image *)
assert (W1 : fst (ly_img ly) <= TFIB_IMG_LO).
{ assert (E : existsb (fun r => fst r <=? TFIB_IMG_LO) (Tfib_owned_static ++ Tfib_zero_shadow) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in E as (r & Hr & Hb). apply Z.leb_le in Hb.
  destruct (proj1 (Forall_forall _ _) SUB r Hr) as [S1 _]. lia. }
assert (W2 : TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly)).
{ assert (E : existsb (fun r => TFIB_IMG_END <=? fst r + snd r) (Tfib_owned_static ++ Tfib_zero_shadow) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in E as (r & Hr & Hb). apply Z.leb_le in Hb.
  destruct (proj1 (Forall_forall _ _) SUB r Hr) as [_ S2]. lia. }
clear SUB.
(* the layout's extents *)
pose proof (lo_high _ LO) as [P1 _].
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_T ly, kThreadObjSize) ltac:(mem_owned)) as AT.
pose proof (static_apart ly 9 (ly_T ly, kThreadObjSize) (ly_img ly) LO ltac:(mem_static) ltac:(mem_static)) as DTI.
pose proof (static_apart ly 9 (ly_C ly, 256) (ly_img ly) LO ltac:(mem_static) ltac:(mem_static)) as DCI.
pose proof (static_apart ly 9 (ly_D ly, 4096) (ly_img ly) LO ltac:(mem_static) ltac:(mem_static)) as DDI.
pose proof (static_apart ly 1 (ly_prim ly, kPrimResvSize) (ly_T ly, kThreadObjSize) LO ltac:(mem_static) ltac:(mem_static)) as PT.
pose proof (static_apart ly 1 (ly_prim ly, kPrimResvSize) (ly_C ly, 256) LO ltac:(mem_static) ltac:(mem_static)) as PC.
pose proof (static_apart ly 1 (ly_prim ly, kPrimResvSize) (ly_D ly, 4096) LO ltac:(mem_static) ltac:(mem_static)) as PD.
pose proof (static_apart ly 3 (ly_T ly, kThreadObjSize) (ly_C ly, 256) LO ltac:(mem_static) ltac:(mem_static)) as TC.
pose proof (static_apart ly 3 (ly_T ly, kThreadObjSize) (ly_D ly, 4096) LO ltac:(mem_static) ltac:(mem_static)) as TD.
unfold in_high, in_app, zdisjoint in P1, AT, DTI, DCI, DDI, PT, PC, PD, TC, TD.
cbn [fst snd] in P1, AT, DTI, DCI, DDI, PT, PC, PD, TC, TD.
(* an address of the image or of its shadow is off the thread object and the primary reserve *)
assert (LOWA : forall a W, in_img_or_shadow a W && apart_q a W = true -> forall k, 0 <= k < W ->
  ~ DMiface.qhdr TFIB_INST ly (a + k) /\ ~ (ly_prim ly <= a + k < ly_prim ly + kPrimResvSize)).
{ intros a W K k Hk. unfold in_img_or_shadow, apart_q in K.
  repeat (rewrite Bool.andb_true_iff in K || rewrite Bool.orb_true_iff in K || rewrite Z.leb_le in K).
  unfold DMiface.qhdr.
  clear - K Hk W1 W2 DTI AT P1.
  unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, TFIB_INST, o_quar, t_qc, kThreadObjSize, kLowShadowBeg, kHighMemBeg,
    kPrimResvSize in *.
  lia. }
pose proof (proj1 (forallb_forall _ _) (Tfib_const_apart_okb ly) c Hc) as K. clear Hc.
destruct c as [e w v]. unfold const_apart_okb in K.
destruct e; cbn [c_at c_w c_val] in K; try discriminate K; cbn [aeval c_at c_w c_val].
- (* ANum *) apply Bool.orb_prop in K as [K|K].
  + right. rewrite EI. exact (LOWA _ _ K).
  + left. apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2].
    apply Z.eqb_eq in K1. apply Nat.eqb_eq in K2. apply aval_is_zero_eq in K3.
    split; [rewrite EI; exact K1 | split; [exact K2 | exact K3]].
- (* AT *) right. intros k Hk. apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold DMiface.qhdr. rewrite EI. clear - K1 K2 Hk W1 W2 DTI PT.
  unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, o_quar, t_qc, kThreadObjSize, kPrimResvSize in *. lia.
- (* AC *) right. intros k Hk. apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold DMiface.qhdr. rewrite EI. clear - K1 K2 Hk W1 W2 DCI PC TC.
  unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, o_quar, t_qc, kThreadObjSize, kPrimResvSize in *. lia.
- (* ATsd *) right. rewrite HTSD, EI. exact (LOWA _ _ K).
- (* AInst *) right. rewrite EI. exact (LOWA _ _ K).
- (* ATp *) right. rewrite ETP, EI. exact (LOWA _ _ K).
- (* AD *) right. intros k Hk. apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold DMiface.qhdr. rewrite EI. clear - K1 K2 Hk W1 W2 DDI PD TD.
  unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, o_quar, t_qc, kThreadObjSize, kPrimResvSize in *. lia.
Qed.

End r.
