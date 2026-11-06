(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_constapart.v (commit 67deba317dfb, blob e38ee586c2fd) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetImg_oomconst.
Import ListNotations.
Open Scope Z_scope.

Definition qhdr_inst_b (x : Z) : bool :=
  ((TFIB_INST + o_quar + 152 <=? x) && (x <? TFIB_INST + o_quar + 156)) ||
  ((TFIB_INST + o_quar + 160 <=? x) && (x <? TFIB_INST + o_quar + 192)).

Definition cmutex_cell_b (c : acell) : bool :=
  match c with
  | ACell (ANum a) w (AV (ANum v)) => (a =? TFIB_INST + o_q_cmutex + 2) && Nat.eqb w 2 && (v =? 0)
  | _ => false
  end.

Lemma tfib_abs_shadow_q :
  forallb (fun c => cmutex_cell_b c || cell_bytes_ok (fun x => negb (qhdr_inst_b x)) c) (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma abs_shadow_q : forall c, In c (Tfib_const_abs ++ Tfib_const_shadow) ->
  c = ACell (ANum (TFIB_INST + o_q_cmutex + 2)) 2 (AV (ANum 0)) \/
  exists a, c_at c = ANum a /\ forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
    ~ (TFIB_INST + o_quar + 152 <= a + k < TFIB_INST + o_quar + 156) /\
    ~ (TFIB_INST + o_quar + 160 <= a + k < TFIB_INST + o_quar + 192).
Proof.
intros c Hc. pose proof (forallb_In _ _ _ tfib_abs_shadow_q Hc) as H. cbv beta in H.
apply orb_true_iff in H as [H|H].
- left. destruct c as [e w v]. destruct e; try discriminate. destruct v as [e'|m x]; try discriminate.
  destruct e'; try discriminate. cbn [cmutex_cell_b] in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
- right. destruct (cell_bytes_ok_sound _ _ H) as (a & E & K). exists a. split; [exact E|].
  intros k Hk. specialize (K k Hk). apply negb_true_iff in K. unfold qhdr_inst_b in K.
  apply orb_false_iff in K as [K1 K2]. apply andb_false_iff in K1. apply andb_false_iff in K2.
  destruct K1 as [K1|K1]; [apply Z.leb_gt in K1 | apply Z.ltb_ge in K1];
  (destruct K2 as [K2|K2]; [apply Z.leb_gt in K2 | apply Z.ltb_ge in K2]); split; lia.
Qed.

Definition band_b (lo hi : Z) (c : acell) : bool :=
  match c_at c with
  | ANum a => (lo <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? hi)
  | _ => false
  end.

Lemma band_b_sound : forall lo hi c, band_b lo hi c = true ->
  exists a, c_at c = ANum a /\ forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> lo <= a + k < hi.
Proof.
intros lo hi c H. unfold band_b in H. destruct (c_at c); try discriminate. cbv beta iota in H.
exists z. split; [reflexivity|].
apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. intros k Hk. lia.
Qed.

Lemma tfib_abs_band : forallb (band_b 4096 kLowShadowBeg) Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tfib_shadow_band : forallb (band_b kLowShadowBeg kHighMemBeg) Tfib_const_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pairwise_nth : forall {X} (R : X -> X -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
  nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros X R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Section g. Context {rc : YM05.RunCeil}.

Lemma sdisj : forall ly i j x y, layout_ok ly -> (i < j)%nat -> nth_error (static_extents ly) i = Some x ->
  nth_error (static_extents ly) j = Some y -> zdisjoint x y.
Proof. intros ly i j x y L Hij Hi Hj. exact (pairwise_nth _ _ i j x y (@lo_disj _ ly L) Hij Hi Hj). Qed.

Lemma prim_high : forall ly, layout_ok ly -> kHighMemBeg <= ly_prim ly.
Proof. intros ly L. pose proof (@lo_high _ ly L) as [H _]. exact H. Qed.

Lemma T_app : forall ly, layout_ok ly -> (ly_T ly + kThreadObjSize <= kLowShadowBeg) \/ kHighMemBeg <= ly_T ly.
Proof.
intros ly L. pose proof (@lo_app _ ly L) as A. unfold owned_extents in A. rewrite Forall_forall in A.
assert (Hin : In (ly_T ly, kThreadObjSize) [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize);
  (ly_F ly, kFakeStackSize); (ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096)])
  by (right; right; left; reflexivity).
destruct (A _ Hin) as [_ [H|[H _]]]; cbn [fst snd] in H; [left | right]; lia.
Qed.

Lemma const_apart_core : forall B ly c, TfibSyms B -> layout_ok ly -> ly_tsd ly = as_tsd B ->
  Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B) ->
  In c (Tfib_const ly) ->
  (aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
   ~ DMiface.qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\
   ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize)).
Proof.
intros B ly c TS L HT HS Hc. pose proof (prim_high ly L) as PH. pose proof (ts_inst B TS) as I.
assert (OWN := fun x => own_off B ly x TS L HS).
assert (DTP : forall x, ly_T ly <= x < ly_T ly + kThreadObjSize -> ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize)).
{ intros x Hx Hp. pose proof (sdisj ly 0 2 (ly_prim ly, kPrimResvSize) (ly_T ly, kThreadObjSize) L ltac:(lia) eq_refl eq_refl) as D.
  unfold zdisjoint in D; cbn [fst snd] in D. lia. }
assert (DCP : forall x, ly_C ly <= x < ly_C ly + 256 -> ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize)).
{ intros x Hx Hp. pose proof (sdisj ly 0 6 (ly_prim ly, kPrimResvSize) (ly_C ly, 256) L ltac:(lia) eq_refl eq_refl) as D.
  unfold zdisjoint in D; cbn [fst snd] in D. lia. }
assert (DDP : forall x, ly_D ly <= x < ly_D ly + 4096 -> ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize)).
{ intros x Hx Hp. pose proof (sdisj ly 0 7 (ly_prim ly, kPrimResvSize) (ly_D ly, 4096) L ltac:(lia) eq_refl eq_refl) as D.
  unfold zdisjoint in D; cbn [fst snd] in D. lia. }
assert (DTC : forall x, ly_C ly <= x < ly_C ly + 256 -> ~ (ly_T ly <= x < ly_T ly + kThreadObjSize)).
{ intros x Hx Ht. pose proof (sdisj ly 2 6 (ly_T ly, kThreadObjSize) (ly_C ly, 256) L ltac:(lia) eq_refl eq_refl) as D.
  unfold zdisjoint in D; cbn [fst snd] in D. lia. }
assert (DTD : forall x, ly_D ly <= x < ly_D ly + 4096 -> ~ (ly_T ly <= x < ly_T ly + kThreadObjSize)).
{ intros x Hx Ht. pose proof (sdisj ly 2 7 (ly_T ly, kThreadObjSize) (ly_D ly, 4096) L ltac:(lia) eq_refl eq_refl) as D.
  unfold zdisjoint in D; cbn [fst snd] in D. lia. }

assert (QO : forall x, TFIB_INST + o_quar + 152 <= x < TFIB_INST + o_quar + 192 -> Exists (in_zr x) Tfib_owned_static)
  by (intros x Hx; apply own_inst; unfold o_quar in Hx; lia).
unfold Tfib_const in Hc. apply in_app_or in Hc as [Hc|Hc].
- right. intros k Hk. pose proof (ts_tp B TS) as P. pose proof (ts_tsd B TS) as TD.
  unfold DMiface.qhdr. rewrite I. unfold t_qc, kThreadObjSize in *.
  destruct (sym_where B ly c k Hc Hk) as [W|[W|[W|[W|[W|[W|W]]]]]]; set (x := aeval B ly (c_at c) + k) in *.
  +  split.
    * intros [Q|[Q|Q]]; [| |lia]; apply (proj1 (OWN x (QO x ltac:(unfold o_quar in *; lia)))); lia.
    * apply DTP. lia.
  +  split.
    * intros [Q|[Q|Q]]; [| |apply (DTC x ltac:(lia)); lia];
        apply (proj1 (proj2 (OWN x (QO x ltac:(unfold o_quar in *; lia))))); lia.
    * apply DCP. lia.
  +  split.
    * intros [Q|[Q|Q]]; [| |apply (DTD x ltac:(lia)); lia];
        apply (proj2 (proj2 (OWN x (QO x ltac:(unfold o_quar in *; lia))))); lia.
    * apply DDP. lia.
  +  rewrite I in W. split.
    * intros [Q|[Q|Q]]; [unfold o_quar in Q; lia | unfold o_quar in Q; lia |].
      apply (proj1 (OWN x (own_inst x ltac:(lia)))). lia.
    * unfold kHighMemBeg in PH. unfold TFIB_INST in W. lia.
  +  rewrite P in W. split.
    * intros [Q|[Q|Q]]; [unfold o_quar, TFIB_INST, TFIB_TP in *; lia | unfold o_quar, TFIB_INST, TFIB_TP in *; lia |].
      apply (proj1 (OWN x (own_tp x ltac:(lia)))). lia.
    * unfold kHighMemBeg in PH. unfold TFIB_TP in W. lia.
  +  rewrite P in W. split.
    * intros [Q|[Q|Q]]; [unfold o_quar, TFIB_INST, TFIB_TP in *; lia | unfold o_quar, TFIB_INST, TFIB_TP in *; lia |].
      apply (proj1 (OWN x (own_tp x ltac:(lia)))). lia.
    * unfold kHighMemBeg in PH. unfold TFIB_TP in W. lia.
  +  rewrite HT, TD in W. split.
    * intros [Q|[Q|Q]]; [unfold o_quar, TFIB_INST, TFIB_TSD in *; lia | unfold o_quar, TFIB_INST, TFIB_TSD in *; lia |].
      apply (proj1 (OWN x (own_tsd x ltac:(lia)))). lia.
    * unfold kHighMemBeg in PH. unfold TFIB_TSD in W. lia.
- destruct (abs_shadow_q c Hc) as [->|(a & E & K)].
  + left. cbn [aeval c_at c_w c_val]. rewrite I. split; [reflexivity | split; reflexivity].
  + right. intros k Hk. rewrite E. cbn [aeval]. destruct (K k Hk) as [K1 K2].
    unfold DMiface.qhdr. rewrite I. unfold t_qc.
    apply in_app_or in Hc as [Ha|Hs].
    * destruct (abs_owned c Ha) as (a' & E' & O). rewrite E in E'. injection E' as <-.
      destruct (band_b_sound _ _ _ (forallb_In _ _ _ tfib_abs_band Ha)) as (a'' & E'' & Bd).
      rewrite E in E''. injection E'' as <-. pose proof (Bd k Hk) as Bk.
      pose proof (OWN (a + k) (O k Hk)) as (N1 & _ & _). unfold kThreadObjSize in N1.
      split; [intros [Q|[Q|Q]]; [exact (K1 Q) | exact (K2 Q) | lia] |].
      unfold kLowShadowBeg, kHighMemBeg in *. lia.
    * destruct (band_b_sound _ _ _ (forallb_In _ _ _ tfib_shadow_band Hs)) as (a'' & E'' & Bd).
      rewrite E in E''. injection E'' as <-. pose proof (Bd k Hk) as Bk. pose proof (T_app ly L) as TA.
      unfold kThreadObjSize in TA.
      split; [intros [Q|[Q|Q]]; [exact (K1 Q) | exact (K2 Q) | lia] |].
      unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma CONST_APART_A : forall B ly c, @im_syms AImg_A B ->
  (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) ->
  In c (@im_const AImg_A ly) ->
  (aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
   ~ DMiface.qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\
   ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize)).
Proof.
intros B ly c TS (L & HT & HS) Hc. change (TfibSyms B) in TS. change (In c (Tfib_const ly)) in Hc.
exact (const_apart_core B ly c TS L HT HS Hc).
Qed.

End g.
