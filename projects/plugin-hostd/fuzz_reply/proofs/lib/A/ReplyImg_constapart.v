(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs (for the cf layer at plugin-hostd/fuzz_reply; row img-constapart-A, its CONST_APART half).
   rule 24: no function proved (kind: image row; closed computations over reply image A's constant-cell table and
   owned-static table, fuzz_reply.asan, pin 42c58610e125, and the layout geometry of layout_ok).

   CONST_APART at image A, in the cf layer's restated form: CONST_APART
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:66-70 @ fa961f42daf), over the layout predicate ly_img_ok
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstBase.v:140-142 @ e73dee6cc107, the same text @ fa961f42daf):
     ly_img_ok B ly := layout_ok ly /\ ly_tsd ly = as_tsd B /\
                       Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B).
   The reply tree does not carry those layer files, so the Lemma at the end states CONST_APART's body at reply's
   instance IM := AImg_reply (proofs/plugin-hostd/fuzz_reply/lib/A/AGif2reply.v:23 @ d2bd679271c: im_syms := TfibSyms,
   im_const := lib/A/AF0m.v:817 Tfib_const) with ly_img_ok UNFOLDED and qhdr = DMiface.qhdr
   (proofs/plugin-hostd/fuzz_reply/lib/A/DMiface.v:71-73 @ d2bd679271c, the same text as
   proofs/cgif/cgif_file_fuzzer/lib/DMiface.v:69-71 @ fa961f42daf).  The form over layout_ok alone is false at this
   image (CONST_APART_refuted_A, lib/A/ReplyImg_constapart_refuted.v @ 9c5a7ec6f3a).  The row's other fact, IMG_QAPART,
   is lib/A/ReplyImg_qapart.v.
   - the absolute cells (Tfib_const_abs ++ Tfib_const_shadow): a boolean scan (vm_compute) shows each is the 2-byte zero
     cell at TFIB_INST + o_q_cmutex + 2 (0xa2dca) or has no byte in the instance's quarantine header words; the cells of
     Tfib_const_abs are owned static bytes in [4096, kLowShadowBeg) (so in ly_img, apart from the thread object, and
     below the primary reserve, which layout_ok puts at kHighMemBeg or above); the cells of Tfib_const_shadow lie in
     [kLowShadowBeg, kHighMemBeg) (apart from the thread object by layout_ok's lo_app, and below the primary reserve);
   - the SYM cells (lib/A/ReplyImg_oomconst.v's sym_where): the bytes in [ly_T, + 80) lie below the thread header
     [ly_T + 80, + 112); the ones in [ly_C, + 160) / [ly_D, + 32) lie in owned extents apart from the thread object and the
     primary reserve (lo_disj) and from ly_img, which holds the instance's header words; the ones at fixed addresses of
     B (the instance + 0 .. 88, the thread pointer - 88 .. + 16, the TSD slot) are owned static bytes, so apart from the
     thread object, and lie below the instance's header words and the primary reserve. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyImg_oomconst.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The instance's quarantine header words hold no absolute cell but the 2-byte zero cell after the mutex.          *)
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

(* The bands of the absolute cells. *)
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

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Layout geometry.                                                                                                 *)
Lemma pairwise_nth : forall {X} (R : X -> X -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
  nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros X R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Section g. Context {rc : YM05.RunCeil}.

(* static_extents ly = [prim; Q; T; F; NB; SB; C; D; stack; img] (lib/Reusable/YG0f.v:294-299 @ d2bd679271c). *)
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

(* CONST_APART's disjunction at every cell of Tfib_const ly, under ly_img_ok's three conjuncts. *)
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
(* the instance's quarantine header words are owned static bytes *)
assert (QO : forall x, TFIB_INST + o_quar + 152 <= x < TFIB_INST + o_quar + 192 -> Exists (in_zr x) Tfib_owned_static)
  by (intros x Hx; apply own_inst; unfold o_quar in Hx; lia).
unfold Tfib_const in Hc. apply in_app_or in Hc as [Hc|Hc].
- right. intros k Hk. pose proof (ts_tp B TS) as P. pose proof (ts_tsd B TS) as TD.
  unfold DMiface.qhdr. rewrite I. unfold t_qc, kThreadObjSize in *.
  destruct (sym_where B ly c k Hc Hk) as [W|[W|[W|[W|[W|[W|W]]]]]]; set (x := aeval B ly (c_at c) + k) in *.
  + (* T *) split.
    * intros [Q|[Q|Q]]; [| |lia]; apply (proj1 (OWN x (QO x ltac:(unfold o_quar in *; lia)))); lia.
    * apply DTP. lia.
  + (* C *) split.
    * intros [Q|[Q|Q]]; [| |apply (DTC x ltac:(lia)); lia];
        apply (proj1 (proj2 (OWN x (QO x ltac:(unfold o_quar in *; lia))))); lia.
    * apply DCP. lia.
  + (* D *) split.
    * intros [Q|[Q|Q]]; [| |apply (DTD x ltac:(lia)); lia];
        apply (proj2 (proj2 (OWN x (QO x ltac:(unfold o_quar in *; lia))))); lia.
    * apply DDP. lia.
  + (* the instance + 0 .. 88 *) rewrite I in W. split.
    * intros [Q|[Q|Q]]; [unfold o_quar in Q; lia | unfold o_quar in Q; lia |].
      apply (proj1 (OWN x (own_inst x ltac:(lia)))). lia.
    * unfold kHighMemBeg in PH. unfold TFIB_INST in W. lia.
  + (* the thread pointer - 88 .. - 80 *) rewrite P in W. split.
    * intros [Q|[Q|Q]]; [unfold o_quar, TFIB_INST, TFIB_TP in *; lia | unfold o_quar, TFIB_INST, TFIB_TP in *; lia |].
      apply (proj1 (OWN x (own_tp x ltac:(lia)))). lia.
    * unfold kHighMemBeg in PH. unfold TFIB_TP in W. lia.
  + (* the thread pointer - 8 .. + 16 *) rewrite P in W. split.
    * intros [Q|[Q|Q]]; [unfold o_quar, TFIB_INST, TFIB_TP in *; lia | unfold o_quar, TFIB_INST, TFIB_TP in *; lia |].
      apply (proj1 (OWN x (own_tp x ltac:(lia)))). lia.
    * unfold kHighMemBeg in PH. unfold TFIB_TP in W. lia.
  + (* the TSD slot *) rewrite HT, TD in W. split.
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

(* CONST_APART at image A: proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:66-70 @ fa961f42daf, with ly_img_ok
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstBase.v:140-142 @ e73dee6cc107) unfolded. *)
Lemma CONST_APART_A : forall B ly c, @im_syms AImg_reply B ->
  (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) ->
  In c (@im_const AImg_reply ly) ->
  (aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
   ~ DMiface.qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\
   ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize)).
Proof.
intros B ly c TS (L & HT & HS) Hc. change (TfibSyms B) in TS. change (In c (Tfib_const ly)) in Hc.
exact (const_apart_core B ly c TS L HT HS Hc).
Qed.

End g.
