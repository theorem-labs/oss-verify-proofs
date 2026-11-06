(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v, with its module paths changed; 324 of its 380 lines of code are new or changed and 736 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoYEntBodyStmt.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma yb_fs6 : fs_frame_bytes DFRAME_CLASS = 4096.
Proof. reflexivity. Qed.

Lemma yb_length_our : forall pl, length (our_of pl) = 6%nat.
Proof. intros pl. unfold our_of. rewrite length_map, length_seq. reflexivity. Qed.

Lemma yb_inFP_range_dec : forall FP lo hi,
  {exists a, inFP FP a /\ lo <= a < hi} + {forall a, inFP FP a -> ~ (lo <= a < hi)}.
Proof.
intros FP lo hi. induction FP as [|[x y] FP IH].
- right. intros a Ha. destruct (inFP_nil a Ha).
- destruct (Z.max x lo <? Z.min y hi) eqn:E.
  + left. apply Z.ltb_lt in E. exists (Z.max x lo). split; [|lia].
    exists (x, y). split; [left; reflexivity | cbn [fst snd]; lia].
  + destruct IH as [IH | IH].
    * left. destruct IH as (a & (r & Hr & Ha) & Hl).
      exists a. split; [exists r; split; [right; exact Hr | exact Ha] | exact Hl].
    * right. apply Z.ltb_ge in E. intros a (r & [<- | Hr] & Ha) Hl; [cbn [fst snd] in Ha; lia|].
      exact (IH a (ex_intro _ r (conj Hr Ha)) Hl).
Qed.

Lemma yb_Forall_drop_mid : forall {X} (P : X -> Prop) (a : X) L1 M L2,
  Forall P (a :: L1 ++ M ++ L2) -> Forall P (a :: L1 ++ L2).
Proof.
intros X P a L1 M L2 H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H).
destruct Hx as [<- | Hx]; [left; reflexivity | right].
apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left; exact Hx | right; apply in_or_app; right; exact Hx].
Qed.

Lemma yb_sum_snd_perm : forall l l' : list (Z * Z), Permutation l l' ->
  fold_right (fun b acc => snd b + acc) 0 l = fold_right (fun b acc => snd b + acc) 0 l'.
Proof. intros l l' HP. induction HP; cbn [fold_right]; lia. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma yb_objr_frame : forall cx o a, d_objr cx o a -> d_FB cx <= a < d_FB cx + DFRAME_SIZE.
Proof. intros cx o a. unfold d_objr, d_obj, DFRAME_SIZE. destruct o; cbn [dobj_off dobj_size]; lia. Qed.

Lemma yb_in_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; assumption | exact (pa_relro_img a Hr)].
Qed.

Definition yb_trk (cx : dcx) (h a : Z) : Prop :=
  d_objr cx OT a \/ d_objr cx OG a \/ d_objr cx OLOCK a \/ d_objr cx OOUR a \/ (h <= a < h + HUNT_SIZE).

Lemma yb_trk_cases : forall cx h a, yb_trk cx h a ->
  (h <= a < h + HUNT_SIZE) \/ (d_FB cx <= a < d_FB cx + DFRAME_SIZE).
Proof.
intros cx h a Ht. unfold yb_trk in Ht.
destruct Ht as [Ht | [Ht | [Ht | [Ht | Ht]]]]; try (right; exact (yb_objr_frame _ _ _ Ht)). left. exact Ht.
Qed.

Lemma yb_objs_kept : forall cx h T G Lk H W m W' m',
  d_objs cx h T G Lk H W m ->
  (forall a, yb_trk cx h a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_objs cx h T G Lk H W' m'.
Proof.
intros cx h T G Lk H W m W' m'
  (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO) K.
unfold d_objs.
refine (conj LT (conj _ (conj QT (conj LG (conj _ (conj QG (conj LL (conj _ (conj QL (conj _ (conj LH (conj _ (conj QH EO))))))))))))).
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GT).
  intros a Ha. apply K. left. unfold d_objr. rewrite length_map, LT in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GG).
  intros a Ha. apply K. right; left. unfold d_objr. rewrite length_map, LG in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GL).
  intros a Ha. apply K. right; right; left. unfold d_objr. rewrite length_map, LL in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GO).
  intros a Ha. apply K. right; right; right; left. unfold d_objr. rewrite length_map, yb_length_our in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GH).
  intros a Ha. apply K. right; right; right; right. rewrite length_map, LH in Ha. unfold HUNT_SIZE. lia.
Qed.

Lemma yb_objs_hupd : forall cx h T G Lk H W m W' m',
  d_geo cx h -> d_objs cx h T G Lk H W m ->
  (forall a, yb_trk cx h a -> ~ (h <= a < h + HUNT_SIZE) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_h_new cx h W' m' ->
  exists H', d_objs cx h T G Lk H' W' m'.
Proof.
intros cx h T G Lk H W m W' m' Hgeo (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO) K
  (H' & LH' & GH' & QH' & EO').
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite yb_fs6 in G2, G7.
assert (KF : forall o a, d_objr cx o a -> yb_trk cx h a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a).
{ intros o a Ho Ht. apply K; [exact Ht|]. pose proof (yb_objr_frame _ _ _ Ho) as Hf. unfold DFRAME_SIZE, HUNT_SIZE in *. lia. }
exists H'. unfold d_objs. refine (conj LT (conj _ (conj QT (conj LG (conj _ (conj QG (conj LL (conj _ (conj QL (conj _ (conj LH' (conj GH' (conj QH' EO'))))))))))))).
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GT).
  intros a Ha. rewrite length_map, LT in Ha. assert (Hr : d_objr cx OT a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OT a Hr). unfold yb_trk; tauto.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GG).
  intros a Ha. rewrite length_map, LG in Ha. assert (Hr : d_objr cx OG a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OG a Hr). unfold yb_trk; tauto.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GL).
  intros a Ha. rewrite length_map, LL in Ha. assert (Hr : d_objr cx OLOCK a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OLOCK a Hr). unfold yb_trk; tauto.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GO).
  intros a Ha. rewrite length_map, yb_length_our in Ha. assert (Hr : d_objr cx OOUR a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OOUR a Hr). unfold yb_trk; tauto.
Qed.

Lemma yb_objs_of_kept : forall cx h T G Lk H W m W' m',
  d_objs cx h T G Lk H W m ->
  (forall a, h <= a < h + HUNT_SIZE -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_objs cx h T G Lk H W' m'.
Proof.
intros cx h T G Lk H W m W' m' Ho KH KF. apply (yb_objs_kept cx h T G Lk H W m W' m' Ho).
intros a Ht. destruct (yb_trk_cases cx h a Ht) as [Ha | Ha]; [exact (KH a Ha) | exact (KF a Ha)].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma yb_base_input : forall cx, d_base B MT XM_LIB RLO RHI tfib_K cx -> 0 < c_n cx ->
  In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)).
Proof.
intros cx ((_ & _ & _ & _ & Hin & _) & _) Hn. destruct Hin as [(E & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

Lemma yb_blocks_bytes_ablocks : forall ly S,
  blocks_bytes S = fold_right (fun b acc => snd b + acc) 0 (ablocks B ly S).
Proof. intros ly S. exact (blocks_bytes_bsum B ly S). Qed.

Lemma yb_blocks_perm : forall cx h xb ly S ly' S',
  d_blocks B cx h xb ly S -> Permutation (ablocks B ly' S') (ablocks B ly S) -> d_blocks B cx h xb ly' S'.
Proof.
intros cx h xb ly S ly' S' (P & F & Bb & O) HP. unfold d_blocks.
split; [exact (Permutation_trans HP P)|]. split; [exact F|]. split; [|exact O].
rewrite (yb_blocks_bytes_ablocks ly' S'), (yb_sum_snd_perm _ _ HP), <- (yb_blocks_bytes_ablocks ly S). exact Bb.
Qed.

Lemma yb_jr_facts : forall cx ly S W m md k,
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k ->
  AR SEGS B ly S W m md /\ In (DFRAME_CLASS, c_fpos cx) (frames S) /\
  frame_addr ly DFRAME_CLASS (c_fpos cx) = d_FB cx.
Proof.
intros cx ly S W m md k (Hbase & HJ).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
split; [exact HAR|]. split; [rewrite Hfrs; left; reflexivity|].
unfold frame_addr, d_FB, frame_addr. rewrite EF. reflexivity.
Qed.

Lemma yb_sep_perm2 : AR_laws SEGS B -> forall ly S W m md x y L1 L2 L3,
  AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (L1 ++ x :: L2 ++ y :: L3) ->
  zdisjoint (block_rng x) (block_rng y).
Proof.
intros LAWS ly S W m md x y L1 L2 L3 HAR HP.
apply (sep_blocks_perm SEGS B LAWS ly S W m md x y (L1 ++ L2 ++ L3) HAR).
eapply Permutation_trans; [exact HP|].
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
apply perm_skip. rewrite app_assoc.
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
apply perm_skip. rewrite app_assoc. apply Permutation_refl.
Qed.

Lemma d_body_frame_disj : AR_laws SEGS B -> forall cx ly S W m md k b n,
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k -> In (b, n) (ablocks B ly S) ->
  b + req_size n <= d_FB cx \/ d_FB cx + 4096 <= b.
Proof.
intros LAWS cx ly S W m md k b n Hjr Hb.
destruct (yb_jr_facts cx ly S W m md k Hjr) as (HAR & Hfin & EFB).
pose proof (sep_block_frame SEGS B LAWS ly S W m md b n DFRAME_CLASS (c_fpos cx) HAR Hb Hfin) as Hz.
rewrite EFB, yb_fs6 in Hz. unfold zdisjoint in Hz. cbn [fst snd] in Hz. exact Hz.
Qed.

Lemma d_body_frame_low : AR_laws SEGS B -> forall cx ly S W m md k,
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k -> 4096 <= d_FB cx.
Proof.
intros LAWS cx ly S W m md k Hjr.
destruct (yb_jr_facts cx ly S W m md k Hjr) as (HAR & Hfin & EFB).
pose proof (frames_bounds SEGS B LAWS ly S W m md DFRAME_CLASS (c_fpos cx) HAR Hfin) as (F & _).
rewrite EFB in F. exact F.
Qed.

Hypothesis STEP : d_body_step_stmt B MT XM_LIB RLO RHI tfib_K.

Theorem d_body_pcall : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS DRO DCAN cx h n xb shf shf' ly3 S3 W3 m3 md3 ly4 S4 W4 m4 md4 k4 STK sp FP kc
  HB Hjr CJ Hlo Hhi HFP Hhn HP Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite yb_fs6 in G2, G7.
destruct (yb_jr_facts cx ly4 S4 W4 m4 md4 k4 Hjr) as (HAR4 & Hfin4 & EFB4).
pose proof (d_body_frame_low LAWS cx ly4 S4 W4 m4 md4 k4 Hjr) as F4096.
pose proof CJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & C1 & C2 & C3 & C4 & _).
cbn [app] in Hfrs.
assert (Hfin3 : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite <- Hfrs; exact Hfin4).
assert (EFB3 : frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx).
{ rewrite <- EFB4. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof Hbl as (Hperm & Hnot & _ & _).
assert (IN3 : forall x, In x (xb ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) -> In x (ablocks B ly3 S3)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym Hperm) Hx). }
assert (IN4 : forall x, In x (xb ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) -> In x (ablocks B ly4 S4)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym (Permutation_trans HP Hperm)) Hx). }
assert (NFF : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ inFP FP a).
{ intros a Ha Hf. destruct (HFP a Hf) as [(b & m & Hbm & Hr) | [Hh | Hd]].
  - pose proof (d_body_frame_disj LAWS cx ly4 S4 W4 m4 md4 k4 b m Hjr (IN4 _ (in_or_app _ _ _ (or_introl Hbm)))). lia.
  - unfold HUNT_SIZE in *. lia.
  - exact (inFP_nil a Hd). }
assert (KF : forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha. unfold DFRAME_SIZE in Ha. apply (C4 DFRAME_CLASS (c_fpos cx) a Hfin3); [|apply NFF; lia].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3, yb_fs6. lia. }
assert (Hh3 : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; left; reflexivity).
assert (Hh4 : In (h, HUNT_SIZE) (ablocks B ly4 S4)) by (apply IN4, in_or_app; right; left; reflexivity).
assert (Hobj4 : exists T' G' Lk' H', d_objs cx h T' G' Lk' H' W4 m4).
{ destruct (yb_inFP_range_dec FP h (h + HUNT_SIZE)) as [Htouch | Hno].
  - destruct (yb_objs_hupd cx h T G Lk H W3 m3 W4 m4 Hgeo Hobj) as (H' & Ho).
    + intros a Ht Hnh. destruct (yb_trk_cases cx h a Ht) as [Ha | Ha]; [exfalso; exact (Hnh Ha) | exact (KF a Ha)].
    + exact (Hhn Htouch).
    + exists T, G, Lk, H'. exact Ho.
  - exists T, G, Lk, H. apply (yb_objs_of_kept cx h T G Lk H W3 m3 W4 m4 Hobj); [|exact KF].
    intros a Ha. replace a with (h + (a - h)) by lia.
    apply (C2 h HUNT_SIZE (a - h) Hh3 Hh4); [unfold req_size, HUNT_SIZE in *; cbn; lia|].
    intros Hf. apply (Hno _ Hf). lia. }
assert (KI : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hc Ha. destruct (G8 Hc) as (P0 & P1 & P2 & P3).
  pose proof (yb_base_input cx (proj1 Hjr) Hc) as HpE.
  assert (Hp3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; right; exact HpE).
  assert (Hp4 : In (c_p cx, c_n cx) (ablocks B ly4 S4)) by (apply IN4, in_or_app; right; right; exact HpE).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrs).
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (C2 (c_p cx) (c_n cx) (a - c_p cx) Hp3 Hp4); [lia|].
  replace (c_p cx + (a - c_p cx)) with a by lia.
  intros Hf. destruct (HFP a Hf) as [(b & m & Hbm & Hr) | [Hh | Hd]].
  - assert (Hne : (b, m) <> (c_p cx, c_n cx)).
    { intros E. rewrite E in Hbm. exact (proj1 (Forall_forall _ _) Hnot _ (or_intror Hbm) HpE). }
    pose proof (sep_blocks SEGS B LAWS ly4 S4 W4 m4 md4 b m _ _ HAR4 (IN4 _ (in_or_app _ _ _ (or_introl Hbm))) Hp4 Hne) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
  - unfold HUNT_SIZE in *. lia.
  - exact (inFP_nil a Hd). }
assert (KR : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hro Ho He. exact (C3 a (yb_in_roP_img a Hro) Ho He (ro_spares SEGS pa_relro_lo pa_relro_hi FP a Hro)). }
destruct Hobj4 as (T' & G' & Lk' & H' & Hobj4).
exact (STEP LAWS DRO DCAN cx h n xb xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4
  T' G' Lk' H' HB Hjr (yb_blocks_perm cx h xb ly3 S3 ly4 S4 Hbl HP) Hobj4 KI KR Hfr' Hsh').
Qed.

Theorem d_body_malloc : d_body_malloc_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS DRO DCAN cx h n xb shf shf' ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 lo hi xr
  HB Hjr3 Hjr4 Hlen Hlo Hhi Hab Hoffr K Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite yb_fs6 in G2, G7.
destruct (yb_jr_facts cx ly3 S3 W3 m3 md3 k3 Hjr3) as (HAR3 & Hfin3 & EFB3).
destruct (yb_jr_facts cx ly4 S4 W4 m4 md4 k4 Hjr4) as (HAR4 & Hfin4 & EFB4).
pose proof K as (_ & K2 & K3 & K4 & _).
pose proof Hbl as (Hperm & Hnot & Hbb & Hoffs).
assert (IN3 : forall x, In x (xb ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) -> In x (ablocks B ly3 S3)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym Hperm) Hx). }
assert (XR4 : forall x, In x xr -> In x (ablocks B ly4 S4)).
{ intros x Hx. rewrite Hab. apply in_or_app. right. exact Hx. }
assert (SEP : forall x y, In x (ablocks B ly3 S3) -> In y xr -> zdisjoint (block_rng x) (block_rng y)).
{ intros x y Hx Hy. apply in_split in Hx as (l1 & l2 & E1). apply in_split in Hy as (l3 & l4 & E2).
  apply (sep_blocks_pos SEGS B LAWS ly4 S4 W4 m4 md4 x y l1 (l2 ++ l3) l4 HAR4).
  rewrite Hab, E1, E2. rewrite <- !app_assoc. reflexivity. }
assert (KF : forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha. unfold DFRAME_SIZE in Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3, yb_fs6. lia.
  - intros (b & m & Hbm & Hr).
    pose proof (d_body_frame_disj LAWS cx ly4 S4 W4 m4 md4 k4 b m Hjr4 (XR4 _ Hbm)). lia. }
assert (KB : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + req_size m ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros b m a Hx Ha. replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hx); [lia|]. replace (b + (a - b)) with a by lia.
  intros (b' & m' & Hbm & Hr). pose proof (SEP (b, m) (b', m') Hx Hbm) as Hz.
  unfold zdisjoint, block_rng in Hz. cbn [fst snd] in Hz. lia. }
assert (Hh3 : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; left; reflexivity).
assert (Hobj4 : d_objs cx h T G Lk H W4 m4).
{ apply (yb_objs_of_kept cx h T G Lk H W3 m3 W4 m4 Hobj); [|exact KF].
  intros a Ha. apply (KB h HUNT_SIZE a Hh3). unfold req_size, HUNT_SIZE in *. cbn. lia. }
assert (KI : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hc Ha. pose proof (yb_base_input cx (proj1 Hjr3) Hc) as HpE.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrs).
  apply (KB (c_p cx) (c_n cx) a); [apply IN3, in_or_app; right; right; exact HpE | lia]. }
assert (KR : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hro Ho He. exact (K3 a (yb_in_roP_img a Hro) Ho He). }
assert (Hbl4 : d_blocks B cx h (xr ++ xb) ly4 S4).
{ unfold d_blocks. split; [|split; [|split]].
  - rewrite Hab, <- app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|].
    apply Permutation_app_head. exact Hperm.
  - apply Forall_forall. intros x Hx. destruct Hx as [<- | Hx]; [exact (Forall_inv Hnot)|].
    apply in_app_or in Hx as [Hx | Hx]; [| exact (proj1 (Forall_forall _ _) Hnot x (or_intror Hx))].
    intros HE. destruct x as [b m].
    pose proof (SEP (b, m) (b, m) (IN3 (b, m) (in_or_app xb ((h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) (b, m)
      (or_intror (or_intror HE)))) Hx) as Hz.
    pose proof (al_blocks _ _ LAWS ly4 S4 W4 m4 md4 b m HAR4 (XR4 _ Hx)) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m (proj1 Hm)) as (Hr1 & _).
    unfold zdisjoint, block_rng in Hz. cbn [fst snd] in Hz. lia.
  - assert (Hbb' : bsum (ablocks B ly3 S3) <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum xb)
      by (rewrite <- blocks_bytes_bsum; exact Hbb).
    change (blocks_bytes S4 <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum (xr ++ xb)).
    rewrite (blocks_bytes_bsum B ly4 S4), Hab, !bsum_app. lia.
  - apply Forall_cons; [exact (Forall_inv Hoffs)|]. apply Forall_app. split; [exact Hoffr | exact (Forall_inv_tail Hoffs)]. }
exact (STEP LAWS DRO DCAN cx h n xb (xr ++ xb) shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4
  T G Lk H HB Hjr4 Hbl4 Hobj4 KI KR Hfr' Hsh').
Qed.

Theorem d_body_free : d_body_free_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS DRO DCAN cx h n xb1 xb2 pz shf shf' ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 lo hi l1 l2
  HB Hjr3 Hjr4 Hlen Hlo Hhi Hab3 Hab4 K Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite yb_fs6 in G2, G7.
destruct (yb_jr_facts cx ly3 S3 W3 m3 md3 k3 Hjr3) as (HAR3 & Hfin3 & EFB3).
pose proof K as (_ & K2 & K3 & K4 & _).
pose proof Hbl as (Hperm & Hnot & Hbb & Hoffs).
assert (IN3 : forall x, In x ((xb1 ++ pz ++ xb2) ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) ->
  In x (ablocks B ly3 S3)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym Hperm) Hx). }
assert (PZXB : forall x, In x pz -> In x (xb1 ++ pz ++ xb2)).
{ intros x Hx. apply in_or_app. right. apply in_or_app. left. exact Hx. }
assert (PZ3 : forall x, In x pz -> In x (ablocks B ly3 S3)).
{ intros x Hx. apply IN3, in_or_app. left. exact (PZXB x Hx). }
assert (PZH : forall x, In x pz -> zdisjoint (block_rng x) (block_rng (h, HUNT_SIZE))).
{ intros x Hx. destruct (in_split _ _ (PZXB x Hx)) as (L1 & L2 & E1).
  apply (yb_sep_perm2 LAWS ly3 S3 W3 m3 md3 x (h, HUNT_SIZE) L1 L2 (ablocks B (c_ly cx) (c_S cx)) HAR3).
  pose proof Hperm as HP'. rewrite E1, <- app_assoc in HP'. exact HP'. }
assert (KF : forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha. unfold DFRAME_SIZE in Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3, yb_fs6. lia.
  - intros (b & m & Hbm & Hr).
    pose proof (d_body_frame_disj LAWS cx ly3 S3 W3 m3 md3 k3 b m Hjr3 (PZ3 _ Hbm)). lia. }
assert (KB : forall b m a, In (b, m) (ablocks B ly3 S3) ->
  (forall y, In y pz -> zdisjoint (block_rng (b, m)) (block_rng y)) -> b <= a < b + req_size m ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros b m a Hx Hd Ha. replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hx); [lia|]. replace (b + (a - b)) with a by lia.
  intros (b' & m' & Hbm & Hr). pose proof (Hd (b', m') Hbm) as Hz.
  unfold zdisjoint, block_rng in Hz. cbn [fst snd] in Hz. lia. }
assert (Hh3 : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; left; reflexivity).
assert (Hobj4 : d_objs cx h T G Lk H W4 m4).
{ apply (yb_objs_of_kept cx h T G Lk H W3 m3 W4 m4 Hobj); [|exact KF].
  intros a Ha. apply (KB h HUNT_SIZE a Hh3); [|unfold req_size, HUNT_SIZE in *; cbn; lia].
  intros y Hy. pose proof (PZH y Hy) as Hz. unfold zdisjoint in *. lia. }
assert (KI : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hc Ha. pose proof (yb_base_input cx (proj1 Hjr3) Hc) as HpE.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrs).
  assert (Hp3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; right; exact HpE).
  apply (KB (c_p cx) (c_n cx) a Hp3); [|lia].
  intros [b m] Hy. assert (Hne : (b, m) <> (c_p cx, c_n cx)).
  { intros E. rewrite E in Hy. exact (proj1 (Forall_forall _ _) Hnot _ (or_intror (PZXB _ Hy)) HpE). }
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 m3 md3 b m _ _ HAR3 (PZ3 _ Hy) Hp3 Hne) as Hz.
  unfold zdisjoint, block_rng in *. cbn [fst snd] in *. lia. }
assert (KR : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hro Ho He. exact (K3 a (yb_in_roP_img a Hro) Ho He). }
assert (Hbl4 : d_blocks B cx h (xb1 ++ xb2) ly4 S4).
{ unfold d_blocks. split; [|split; [|split]].
  - rewrite Hab4, <- app_assoc. rewrite Hab3, <- !app_assoc in Hperm.
    exact (Permutation_app_inv_m _ _ _ _ _ Hperm).
  - exact (yb_Forall_drop_mid _ _ _ _ _ Hnot).
  - assert (Hbb' : bsum (ablocks B ly3 S3) <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum (xb1 ++ pz ++ xb2))
      by (rewrite <- blocks_bytes_bsum; exact Hbb).
    rewrite Hab3, !bsum_app in Hbb'.
    change (blocks_bytes S4 <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum (xb1 ++ xb2)).
    rewrite (blocks_bytes_bsum B ly4 S4), Hab4, !bsum_app. lia.
  - exact (yb_Forall_drop_mid _ _ _ _ _ Hoffs). }
exact (STEP LAWS DRO DCAN cx h n (xb1 ++ pz ++ xb2) (xb1 ++ xb2) shf shf'
  ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T G Lk H HB Hjr4 Hbl4 Hobj4 KI KR Hfr' Hsh').
Qed.
End h.
End f.
End d.
