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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC88 DiscoEntryInv DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma dobj_eq_dec : forall o o' : dobj, {o = o'} + {o <> o'}.
Proof. decide equality. Defined.
Lemma fs6 : fs_frame_bytes DFRAME_CLASS = 4096.
Proof. reflexivity. Qed.

Lemma pairwise_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [pairwise]; intros H.
- exact I.
- destruct H as [F P]. split; [|exact (IH P)]. apply Forall_forall. intros z Hz.
  apply (proj1 (Forall_forall _ _) F). exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as [Fy [Fx P]]. inversion Fy as [|? ? Ryx Fy']; subst.
  split; [constructor; [exact (Hs _ _ Ryx) | exact Fx]|]. split; [exact Fy' | exact P].
- exact (IH2 (IH1 H)).
Qed.
Lemma pairwise_map_inv : forall {X Y} (R : Y -> Y -> Prop) (f : X -> Y) l,
  pairwise R (map f l) -> pairwise (fun x y => R (f x) (f y)) l.
Proof.
intros X Y R f l. induction l as [|x l IH]; cbn [map pairwise]; intros H; [exact I|].
destruct H as [F P]. split; [|exact (IH P)]. apply Forall_forall. intros z Hz.
apply (proj1 (Forall_forall _ _) F). apply in_map. exact Hz.
Qed.

Lemma pw_app_cross : forall {X} (R : X -> X -> Prop) l1 l2,
  pairwise R (l1 ++ l2) -> pairwise R l1 /\ forall x y, In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1 l2. induction l1 as [|z l1 IH]; cbn [app pairwise]; intros H; [split; [exact I | intros x y []]|].
destruct H as [F P]. destruct (IH P) as [P1 C]. apply Forall_app in F as [F1 F2].
split; [split; assumption|]. intros x y [<- | Hx] Hy; [exact (proj1 (Forall_forall _ _) F2 y Hy) | exact (C x y Hx Hy)].
Qed.

Lemma pw_in2 : forall {X} (R : X -> X -> Prop) l x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn [In pairwise] in *; [destruct Hx|].
destruct HP as [F P].
destruct Hx as [<- | Hx], Hy as [<- | Hy].
- exfalso; exact (Hne eq_refl).
- left. exact (proj1 (Forall_forall _ _) F y Hy).
- right. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y P Hx Hy Hne).
Qed.
Lemma pw_dup : forall {X} (R : X -> X -> Prop) l1 x l2 l3,
  pairwise R (l1 ++ x :: l2 ++ x :: l3) -> R x x.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros x l2 l3 H; cbn [app pairwise] in H.
- destruct H as [F _]. apply (proj1 (Forall_forall _ _) F). apply in_or_app. right. left. reflexivity.
- destruct H as [_ P]. exact (IH x l2 l3 P).
Qed.

Lemma zdisj_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b. unfold zdisjoint. lia. Qed.

Lemma zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma objr_frame : forall cx o a, d_objr cx o a -> d_FB cx <= a < d_FB cx + DFRAME_SIZE.
Proof. intros cx o a. unfold d_objr, d_obj, DFRAME_SIZE. destruct o; cbn [dobj_off dobj_size]; lia. Qed.
Lemma objr_uniq : forall cx o o' a, d_objr cx o a -> d_objr cx o' a -> o = o'.
Proof.
intros cx o o' a. unfold d_objr, d_obj.
destruct o, o'; cbn [dobj_off dobj_size]; intros H1 H2; first [reflexivity | exfalso; lia].
Qed.
Lemma in_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; assumption | exact (pa_relro_img a Hr)].
Qed.
Lemma in_img_ceil : forall a, in_img SEGS a -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a Ha. pose proof (pa_img_range a Ha) as Hr. pose proof alloc_ceiling_val as Hc.
unfold IMG_LO, IMG_TOP in Hr. lia.
Qed.
Lemma off_img_not_img : forall p n a, off_img p n -> p <= a < p + n -> ~ in_img SEGS a.
Proof.
intros p n a Ho Ha Hi. pose proof (pa_img_range a Hi) as Hr. unfold off_img in Ho. lia.
Qed.
Lemma length_our : forall pl, length (our_of pl) = 6%nat.
Proof. intros pl. unfold our_of. rewrite length_map, length_seq. reflexivity. Qed.

Section h.
Variable B : asyms.

Lemma d_img_kept : forall W m W' m',
  d_img B W m -> (forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_img B W' m'.
Proof. intros W m W' m' H K a Hro Ho He. rewrite (K a Hro Ho He). exact (H a Hro Ho He). Qed.

Lemma d_can_kept : forall cx W m W' m',
  d_can cx W m -> (forall a, AE2k.FF_canary <= a < AE2k.FF_canary + 8 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_can cx W' m'.
Proof.
intros cx W m W' m' (Hv & Hr & Hi) K. split; [|split; [exact Hr | exact Hi]].
refine (val_mem_aview_kept_x SEGS (w_H W) (w_H W') m m' _ _ _ _ Hv). intros x Hx. apply K. cbn in Hx. lia.
Qed.
Lemma can_rdword : forall cx (W : world SEGS) m,
  d_can cx W m -> rdword (aview SEGS (w_H W) m) AE2k.FF_canary = Some (c_canary cx).
Proof. intros cx W m (Hv & Hr & _). exact (rdword_of_val_mem SEGS (w_H W) m _ _ Hv Hr). Qed.

Definition d_trk (cx : dcx) (h a : Z) : Prop :=
  d_objr cx OT a \/ d_objr cx OG a \/ d_objr cx OLOCK a \/ d_objr cx OOUR a \/ (h <= a < h + HUNT_SIZE).

Lemma d_objs_kept : forall cx h T G Lk H W m W' m',
  d_objs cx h T G Lk H W m ->
  (forall a, d_trk cx h a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
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
  intros a Ha. apply K. right; right; right; left. unfold d_objr. rewrite length_map, length_our in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GH).
  intros a Ha. apply K. right; right; right; right. rewrite length_map, LH in Ha. unfold HUNT_SIZE. lia.
Qed.

Lemma d_input_kept : forall cx n n' W m W' m',
  d_input cx n W m -> Z.of_nat (length (c_pl cx)) = c_n cx -> 0 <= n' <= n ->
  (forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_input cx n' W' m'.
Proof.
intros cx n n' W m W' m' (Hn & Hg & Ho) Hlen Hn' K. unfold d_input. split; [lia|]. split; [|exact Ho].
destruct (c_pl cx) as [|b pl] eqn:Epl.
- cbn. apply garr8_nil.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ Hg).
  intros a Ha. rewrite length_map in Ha. cbn [length] in Hlen, Ha. apply K; lia.
Qed.

Lemma d_geo_out : forall cx h a lo hi,
  d_geo cx h -> d_S cx - LLVMF_STK <= lo -> a < YM05.alloc_ceiling -> ~ (lo <= a < hi).
Proof. intros cx h a lo hi G Hlo Ha Hw. unfold d_geo in G. lia. Qed.

Lemma d_trk_ceil : forall cx h a, d_geo cx h -> d_trk cx h a -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros cx h a G Ht. pose proof G as (G1 & G2 & G3 & G4 & _). rewrite fs6 in G2. unfold d_trk in Ht.
destruct Ht as [Ht | [Ht | [Ht | [Ht | Ht]]]];
  try (pose proof (objr_frame _ _ _ Ht) as Hf; unfold DFRAME_SIZE in Hf; lia).
unfold HUNT_SIZE in *. lia.
Qed.

Lemma d_trk_rdset : forall cx h a, d_trk cx h a -> d_rdset B cx h a.
Proof. intros cx h a Ht. unfold d_rdset. unfold d_trk in Ht. tauto. Qed.

Lemma frame_present_kept : forall cx (W : world SEGS) (m m' : word -> option byte),
  off_img (d_FB cx) (fs_frame_bytes DFRAME_CLASS) ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
intros cx W m m' Ho P a Ha Hp. apply P; [|exact Hp].
apply (off_img_not_img _ _ a Ho). rewrite fs6. unfold DFRAME_SIZE in Ha. lia.
Qed.

Lemma d_rL_rX : forall (cx : dcx) (h : Z) (regs : bvmap 5 word),
  d_rL B cx regs -> getr regs 19 = w64 h -> d_rX B cx h regs.
Proof.
intros cx h regs (Hsp & Hgp & Htp & H8 & H9 & H18 & _) H19.
unfold d_rX. repeat split; assumption.
Qed.

Lemma d_body_rt_gen : forall cx h n n' xb shf shf' ly3 S3 W3 mem mem' (R : Z -> Prop) lo hi,
  d_body B cx h n xb shf ly3 S3 W3 mem -> d_S cx - LLVMF_STK <= lo ->
  (forall a, R a -> (lo <= a < hi) \/ ~ d_rdset B cx h a) ->
  d_kept R W3 mem W3 mem' ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W3) mem a -> apresent (w_H W3) mem' a) ->
  d_frame cx h shf' W3 mem' -> d_shadow cx shf' W3 mem' -> 0 <= n' <= n ->
  d_body B cx h n' xb shf' ly3 S3 W3 mem'.
Proof.
intros cx h n n' xb shf shf' ly3 S3 W3 mem mem' R lo hi
  (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr) Hlo HR K P Hfr' Hsh' Hn'.
assert (KR : forall a, d_rdset B cx h a -> 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem a).
{ intros a Hd Ha. apply K; [pose proof alloc_ceiling_lt; lia|]. intros HRa.
  destruct (HR a HRa) as [Hw | Hn]; [exact (d_geo_out cx h a lo hi Hgeo Hlo (proj2 Ha) Hw) | exact (Hn Hd)]. }
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
exists T, G, Lk, H.
refine (conj Hfr' (conj Hsh' (conj _ (conj Hbl (conj _ (conj _ (conj Hoff (conj Hgeo (conj _ (conj Hstk _)))))))))).
- apply (d_objs_kept cx h T G Lk H W3 mem W3 mem' Hobj).
  intros a Ht. apply KR; [exact (d_trk_rdset _ _ _ Ht) | exact (d_trk_ceil _ _ _ Hgeo Ht)].
- apply (d_input_kept cx n n' W3 mem W3 mem' Hin G6 Hn').
  intros a Hc Ha. destruct (G8 Hc) as (P1 & P2 & _). apply KR; [unfold d_rdset; tauto | lia].
- apply (d_img_kept W3 mem W3 mem' Himg).
  intros a Hro Ho He. apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (in_roP_img a Hro))].
- apply (d_can_kept cx W3 mem W3 mem' Hcan). intros a Ha.
  apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (proj2 (proj2 Hcan) a Ha))].
- intros a Ha. split; [exact (proj1 (Hwr a Ha)) |].
  exact (frame_present_kept cx W3 mem mem' Hoff P a Ha (proj2 (Hwr a Ha))).
Qed.

Theorem d_body_rt : d_body_rt_stmt B.
Proof.
intros cx h n n' xb shf shf' ly3 S3 W3 mem mem' lo hi R HB Hlo Hhi HR K P Hfr Hsh Hn.
exact (d_body_rt_gen cx h n n' xb shf shf' ly3 S3 W3 mem mem' R lo hi HB Hlo HR K P Hfr Hsh Hn).
Qed.

Theorem d_body_keep : d_body_keep_stmt B.
Proof.
intros cx h n n' shf ly3 S3 W3 mem mem' lo hi HB Hlo Hhi K P Hfr Hsh Hn.
apply (d_body_rt_gen cx h n n' [] shf shf ly3 S3 W3 mem mem' (fun a => lo <= a < hi) lo hi HB Hlo);
  [intros a Ha; left; exact Ha | | exact P | exact Hfr | exact Hsh | exact Hn].
intros a Ha Hn'. exact (K a Ha Hn').
Qed.


Lemma sum_snd_perm : forall l l' : list (Z * Z), Permutation l l' ->
  fold_right (fun b acc => snd b + acc) 0 l = fold_right (fun b acc => snd b + acc) 0 l'.
Proof. intros l l' HP. induction HP; cbn [fold_right]; lia. Qed.

Lemma blocks_bytes_ablocks : forall ly S, blocks_bytes S = fold_right (fun b acc => snd b + acc) 0 (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks.
induction (st_chunks S) as [|k l IH]; [reflexivity|].
simpl. destruct (is_alloc k); simpl; rewrite IH; reflexivity.
Qed.

Lemma d_blocks_perm : forall cx h xb ly S ly' S',
  d_blocks B cx h xb ly S -> Permutation (ablocks B ly' S') (ablocks B ly S) -> d_blocks B cx h xb ly' S'.
Proof.
intros cx h xb ly S ly' S' (P & F & Bb & O) HP. unfold d_blocks.
split; [exact (Permutation_trans HP P)|]. split; [exact F|]. split; [|exact O].
rewrite (blocks_bytes_ablocks ly' S'), (sum_snd_perm _ _ HP), <- (blocks_bytes_ablocks ly S). exact Bb.
Qed.


Lemma d_objs_upd : forall cx h T G Lk H W m W' m' os,
  d_geo cx h -> d_objs cx h T G Lk H W m ->
  (forall a, d_trk cx h a -> ~ Exists (fun o => d_objr cx o a) os -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  Forall (fun o => d_obj_new cx o W' m') os ->
  exists T' G' Lk', d_objs cx h T' G' Lk' H W' m'.
Proof.
intros cx h T G Lk H W m W' m' os Hgeo (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO) K F.
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7. pose proof fs6 as F6.
assert (NOEX : forall o a, ~ In o os -> d_objr cx o a -> ~ Exists (fun o' => d_objr cx o' a) os).
{ intros o a Hno Ho Hex. apply Exists_exists in Hex as (o' & Hin & Ho'). rewrite (objr_uniq cx o' o a Ho' Ho) in Hin. exact (Hno Hin). }
assert (NEW : forall o, In o os -> d_obj_new cx o W' m') by (intros o Hin; exact (proj1 (Forall_forall _ _) F o Hin)).
assert (HT : exists T' : list byte, length T' = 400%nat /\
  garr8 SEGS (rd W' m') (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T') /\ disco_table_c.table_ok T').
{ destruct (In_dec dobj_eq_dec OT os) as [Hin|Hno]; [exact (NEW OT Hin)|].
  exists T. split; [exact LT|]. split; [|exact QT].
  refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GT).
  intros a Ha. rewrite length_map, LT in Ha. assert (Hr : d_objr cx OT a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply K; [unfold d_trk; tauto | exact (NOEX OT a Hno Hr)]. }
assert (HG : exists G' : list byte, length G' = 264%nat /\
  garr8 SEGS (rd W' m') (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G') /\ disco_classify_c.gate_ok G').
{ destruct (In_dec dobj_eq_dec OG os) as [Hin|Hno]; [exact (NEW OG Hin)|].
  exists G. split; [exact LG|]. split; [|exact QG].
  refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GG).
  intros a Ha. rewrite length_map, LG in Ha. assert (Hr : d_objr cx OG a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply K; [unfold d_trk; tauto | exact (NOEX OG a Hno Hr)]. }
assert (HL : exists Lk' : list byte, length Lk' = 12%nat /\
  garr8 SEGS (rd W' m') (d_obj cx OLOCK) (map (fun b : byte => bv_unsigned b) Lk') /\ disco_classify_c.lock_ok Lk').
{ destruct (In_dec dobj_eq_dec OLOCK os) as [Hin|Hno]; [exact (NEW OLOCK Hin)|].
  exists Lk. split; [exact LL|]. split; [|exact QL].
  refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GL).
  intros a Ha. rewrite length_map, LL in Ha. assert (Hr : d_objr cx OLOCK a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply K; [unfold d_trk; tauto | exact (NOEX OLOCK a Hno Hr)]. }
assert (HO : garr8 SEGS (rd W' m') (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))).
{ destruct (In_dec dobj_eq_dec OOUR os) as [Hin|Hno]; [exact (NEW OOUR Hin)|].
  refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GO).
  intros a Ha. rewrite length_map, length_our in Ha. assert (Hr : d_objr cx OOUR a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply K; [unfold d_trk; tauto | exact (NOEX OOUR a Hno Hr)]. }
assert (HH : garr8 SEGS (rd W' m') h (map (fun b : byte => bv_unsigned b) H)).
{ refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GH).
  intros a Ha. rewrite length_map, LH in Ha. apply K; [unfold d_trk, HUNT_SIZE; lia|].
  intros Hex. apply Exists_exists in Hex as (o & _ & Ho). pose proof (objr_frame _ _ _ Ho) as Hf.
  unfold DFRAME_SIZE, HUNT_SIZE in *. lia. }
destruct HT as (T' & LT' & GT' & QT'). destruct HG as (G' & LG' & GG' & QG'). destruct HL as (Lk' & LL' & GL' & QL').
exists T', G', Lk'. unfold d_objs.
exact (conj LT' (conj GT' (conj QT' (conj LG' (conj GG' (conj QG' (conj LL' (conj GL' (conj QL' (conj HO (conj LH (conj HH (conj QH EO))))))))))))).
Qed.

Lemma d_objs_hupd : forall cx h T G Lk H W m W' m',
  d_geo cx h -> d_objs cx h T G Lk H W m ->
  (forall a, d_trk cx h a -> ~ (h <= a < h + HUNT_SIZE) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_h_new cx h W' m' ->
  exists H', d_objs cx h T G Lk H' W' m'.
Proof.
intros cx h T G Lk H W m W' m' Hgeo (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO) K
  (H' & LH' & GH' & QH' & EO').
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7. pose proof fs6 as F6.
assert (KF : forall o a, d_objr cx o a -> d_trk cx h a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a).
{ intros o a Ho Ht. apply K; [exact Ht|]. pose proof (objr_frame _ _ _ Ho) as Hf. unfold DFRAME_SIZE, HUNT_SIZE in *. lia. }
exists H'. unfold d_objs. refine (conj LT (conj _ (conj QT (conj LG (conj _ (conj QG (conj LL (conj _ (conj QL (conj _ (conj LH' (conj GH' (conj QH' EO'))))))))))))).
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GT).
  intros a Ha. rewrite length_map, LT in Ha. assert (Hr : d_objr cx OT a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OT a Hr). unfold d_trk; tauto.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GG).
  intros a Ha. rewrite length_map, LG in Ha. assert (Hr : d_objr cx OG a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OG a Hr). unfold d_trk; tauto.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GL).
  intros a Ha. rewrite length_map, LL in Ha. assert (Hr : d_objr cx OLOCK a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OLOCK a Hr). unfold d_trk; tauto.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GO).
  intros a Ha. rewrite length_map, length_our in Ha. assert (Hr : d_objr cx OOUR a) by (unfold d_objr; cbn [dobj_size]; lia).
  apply (KF OOUR a Hr). unfold d_trk; tauto.
Qed.

Lemma le_byte_1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. replace (2 ^ 8) with 256 by reflexivity. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma garr8_det : forall (m : word -> option byte) p (L1 L2 : list byte),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L1) -> garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L2) ->
  length L1 = length L2 -> L1 = L2.
Proof.
intros m p L1 L2 H1 H2 HL.
assert (EM : map (fun b : byte => bv_unsigned b) L1 = map (fun b : byte => bv_unsigned b) L2).
{ apply nth_ext with (d := 0) (d' := 0); [rewrite !length_map; exact HL|].
  intros j Hj. rewrite length_map in Hj.
  destruct (H1 j ltac:(rewrite length_map; exact Hj)) as [V1 R1].
  destruct (H2 j ltac:(rewrite length_map; lia)) as [V2 R2].
  specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
  rewrite V1 in V2.
  apply (f_equal (fun o : option byte => match o with Some b => bv_unsigned b | None => 0 end)) in V2.
  cbv beta iota in V2. rewrite !Z_to_bv_unsigned in V2.
  rewrite (le_byte_1 _ R1), (le_byte_1 _ R2) in V2.
  rewrite !bv_wrap_small in V2; [exact V2 | change (bv_modulus 8) with 256; lia | change (bv_modulus 8) with 256; lia]. }
clear H1 H2. revert L2 HL EM.
induction L1 as [|b1 L1 IH]; intros [|b2 L2] HL EM; cbn in HL, EM; try discriminate; [reflexivity|].
injection EM as Eb EL. f_equal; [apply bv_eq; exact Eb | apply IH; [lia | exact EL]].
Qed.

Theorem d_body_read : d_body_read_stmt B.
Proof.
intros cx h n xb shf ly S W m (T & G & Lk & H & _ & _ & Hobj & _).
pose proof Hobj as (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO).
split; [intros T' L' G''; rewrite <- (garr8_det _ _ T T' GT G'' ltac:(rewrite LT, L'; reflexivity)); exact QT|].
split; [intros G' L' G''; rewrite <- (garr8_det _ _ G G' GG G'' ltac:(rewrite LG, L'; reflexivity)); exact QG|].
split; [intros Lk' L' G''; rewrite <- (garr8_det _ _ Lk Lk' GL G'' ltac:(rewrite LL, L'; reflexivity)); exact QL|].
intros H' L' G''. rewrite <- (garr8_det _ _ H H' GH G'' ltac:(rewrite LH, L'; reflexivity)). split; [exact QH | exact EO].
Qed.

Lemma d_frame_x_of : forall cx h shf W m, d_frame cx h shf W m -> d_frame_x cx W m.
Proof.
intros cx h shf W m (E & HE & HR & Hfl & _ & _). exists E. split; [exact HE|]. split; [|exact Hfl].
unfold d_regions in HR. unfold d_regions_x.
apply Forall_inv_tail in HR as HR1. apply Forall_inv in HR as R1.
apply Forall_inv_tail in HR1 as HR2. apply Forall_inv in HR1 as R2.
apply Forall_inv_tail in HR2 as HR3. apply Forall_inv in HR2 as R3.
apply Forall_inv in HR3 as R4.
destruct R2 as (A1 & A2 & A3 & A4). destruct R3 as (C1 & C2 & C3 & _). destruct R4 as (D1 & D2 & D3 & _).
constructor; [exact R1|]. constructor.
- refine (conj A1 (conj A2 (conj A3 _))).
  assert (IN : forall k v, In (k, v) [(16, SLit 0xffff); (24, SLit INV9); (32, SOff AT_F 0); (40, SOff AT_F 0); (48, SOff AT_F 2656);
     (144, SOff AT_F 2960); (160, SLit STALE_NS); (168, SOff AT_SH 275); (176, SOff AT_F 2200); (184, SOff AT_SH 30);
     (192, SOff AT_F 2128); (200, SLit MS_NS); (208, SOff AT_F 2992); (240, SOff AT_F 2624); (256, SOff AT_F 1920);
     (264, SOff AT_F 1792); (272, SOff AT_F 32); (288, SOff AT_F 1856); (296, SLit W0X0); (304, SOff AT_SH 270);
     (312, SOff AT_F 2162); (320, SOff AT_F 2064); (328, SOff AT_F 1664); (352, SOff AT_F 240); (360, SOff AT_F 2000);
     (376, SOff AT_F 1728); (384, SOff AT_F 2160); (400, SOff AT_SH 0); (416, SOff AT_F 0)] ->
     YP09.chunk_ok SEGS E (rd W m) (base_val E (Some AT_A)) (YP09.mkChunk k (CVal 8 v))).
  { intros k v Hin. apply (proj1 (Forall_forall _ _) A4). unfold dslot_chunks.
    apply (in_map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (snd kv))) _ (k, v) Hin). }
  constructor; [apply IN; cbn [In]; repeat (first [left; reflexivity | right])|].
  constructor; [apply IN; cbn [In]; repeat (first [left; reflexivity | right])|].
  constructor; [apply IN; cbn [In]; repeat (first [left; reflexivity | right])|].
  constructor.
- constructor; [exact (conj C1 (conj C2 (conj C3 (Forall_nil _))))|].
  constructor; [exact (conj D1 (conj D2 (conj D3 (Forall_nil _))))|].
  constructor.
Qed.

Lemma d_body_x_of : forall cx h n shf ly S W m, d_body B cx h n [] shf ly S W m -> d_body_x B cx h ly S W m.
Proof.
intros cx h n shf ly S W m (T & G & Lk & H & Hfr & _ & _ & Hbl & _ & Himg & _).
exact (conj (d_frame_x_of cx h shf W m Hfr) (conj Hbl Himg)).
Qed.
Section j.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma d_jr_facts : forall cx ly S W m md k,
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k ->
  AR SEGS B ly S W m md /\ In (DFRAME_CLASS, c_fpos cx) (frames S) /\
  frame_addr ly DFRAME_CLASS (c_fpos cx) = d_FB cx /\ ly_stk_lo ly = ly_stk_lo (c_ly cx) /\
  YM05.alloc_ceiling <= ly_stk_lo (c_ly cx).
Proof.
intros cx ly S W m md k (Hbase & HJ).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Eslo & _).
pose proof Hstatic as (_ & _ & Hceil & _).
split; [exact HAR|]. split; [rewrite Hfrs; left; reflexivity|].
split; [unfold frame_addr, d_FB, frame_addr; rewrite EF; reflexivity|].
split; [exact Eslo | exact Hceil].
Qed.

Lemma d_body_step_gen : AR_laws SEGS B ->
  forall cx h n xb xb' shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T' G' Lk' H',
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 ->
  d_blocks B cx h xb' ly4 S4 -> d_objs cx h T' G' Lk' H' W4 m4 ->
  (forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  d_can cx W4 m4 ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb' shf' ly4 S4 W4 m4.
Proof.
intros LAWS cx h n xb xb' shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T' G' Lk' H'
  (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr)
  Hjr Hbl' Hobj' KI KR Hcan4 Hfr' Hsh'.
destruct (d_jr_facts cx ly4 S4 W4 m4 md4 k4 Hjr) as (HAR & Hfin & EFB & Eslo & Hceil).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2.
pose proof (al_frames _ _ LAWS ly4 S4 W4 m4 md4 DFRAME_CLASS (c_fpos cx) HAR Hfin) as (_ & _ & Hfp & _).
rewrite EFB, fs6 in Hfp.
exists T', G', Lk', H'.
refine (conj Hfr' (conj Hsh' (conj Hobj' (conj Hbl' (conj _ (conj _ (conj Hoff (conj Hgeo (conj _ (conj _ _)))))))))).
- exact (d_input_kept cx n n W3 m3 W4 m4 Hin G6 (conj (proj1 (proj1 Hin)) (Z.le_refl n)) KI).
- exact (d_img_kept W3 m3 W4 m4 Himg KR).
- exact Hcan4.
- intros a Ha. left. rewrite Eslo. unfold DFRAME_SIZE in Ha. lia.
- intros a Ha. unfold DFRAME_SIZE in Ha. split.
  + right; right; right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|].
    left. unfold in_zr. rewrite EFB, fs6. cbn [fst snd]. lia.
  + exact (proj1 (Hfp a ltac:(lia))).
Qed.

Lemma d_body_kept_step : AR_laws SEGS B ->
  forall cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi (R : Z -> Prop),
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 ->
  d_S cx - LLVMF_STK <= lo ->
  (forall a, R a -> (lo <= a < hi) \/ ~ d_rdset B cx h a) ->
  d_kept R W3 m3 W4 m4 ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb shf' ly4 S4 W4 m4.
Proof.
intros LAWS cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi R HB Hjr Hlo HR K HP Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
assert (KR : forall a, d_rdset B cx h a -> 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hd Ha. apply K; [pose proof alloc_ceiling_lt; lia|]. intros HRa.
  destruct (HR a HRa) as [Hw | Hn]; [exact (d_geo_out cx h a lo hi Hgeo Hlo (proj2 Ha) Hw) | exact (Hn Hd)]. }
apply (d_body_step_gen LAWS cx h n xb xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T G Lk H HB Hjr
  (d_blocks_perm cx h xb ly3 S3 ly4 S4 Hbl HP)).
- apply (d_objs_kept cx h T G Lk H W3 m3 W4 m4 Hobj).
  intros a Ht. apply KR; [exact (d_trk_rdset _ _ _ Ht) | exact (d_trk_ceil _ _ _ Hgeo Ht)].
- intros a Hc Ha. destruct (G8 Hc) as (P1 & P2 & _). apply KR; [unfold d_rdset; tauto | lia].
- intros a Hro Ho He. apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (in_roP_img a Hro))].
- apply (d_can_kept cx W3 m3 W4 m4 Hcan).
  intros a Ha. apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (proj2 (proj2 Hcan) a Ha))].
- exact Hfr'.
- exact Hsh'.
Qed.

Theorem d_body_call_keep : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi HB Hjr Hlo Hhi K HP Hfr Hsh.
apply (d_body_kept_step LAWS cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi (fun a => lo <= a < hi)
  HB Hjr Hlo); [intros a Ha; left; exact Ha | exact K | exact HP | exact Hfr | exact Hsh].
Qed.

Theorem d_body_tobs : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi os R HB Hjr Hlo Hhi HR K Fnew HP Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7. pose proof fs6 as F6.
assert (NOTOBJ : forall a, ~ (d_FB cx <= a < d_FB cx + DFRAME_SIZE) -> ~ Exists (fun o => d_objr cx o a) os).
{ intros a Hn Hex. apply Exists_exists in Hex as (o & _ & Ho). exact (Hn (objr_frame _ _ _ Ho)). }
assert (KR : forall a, d_rdset B cx h a -> 0 <= a < YM05.alloc_ceiling -> ~ Exists (fun o => d_objr cx o a) os ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hd Ha Hno. apply K; [pose proof alloc_ceiling_lt; lia|]. intros HRa.
  destruct (HR a HRa) as [Hw | [He | Hn]]; [exact (d_geo_out cx h a lo hi Hgeo Hlo (proj2 Ha) Hw) | exact (Hno He) | exact (Hn Hd)]. }
destruct (d_objs_upd cx h T G Lk H W3 m3 W4 m4 os Hgeo Hobj) as (T' & G' & Lk' & Hobj').
- intros a Ht Hno. apply KR; [exact (d_trk_rdset _ _ _ Ht) | exact (d_trk_ceil _ _ _ Hgeo Ht) | exact Hno].
- exact Fnew.
- apply (d_body_step_gen LAWS cx h n xb xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T' G' Lk' H HB Hjr
    (d_blocks_perm cx h xb ly3 S3 ly4 S4 Hbl HP) Hobj').
  + intros a Hc Ha. destruct (G8 Hc) as (P1 & P2 & P3 & _). apply KR; [unfold d_rdset; tauto | lia |].
    apply NOTOBJ. unfold DFRAME_SIZE. lia.
  + intros a Hro Ho He. apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (in_roP_img a Hro)) |].
    apply NOTOBJ. intros Ha. apply (off_img_not_img _ _ a Hoff); [rewrite fs6; unfold DFRAME_SIZE in Ha; lia | exact (in_roP_img a Hro)].
  + apply (d_can_kept cx W3 m3 W4 m4 Hcan).
    intros a Ha. apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (proj2 (proj2 Hcan) a Ha)) |].
    apply NOTOBJ. intros Hf. apply (off_img_not_img _ _ a Hoff); [rewrite fs6; unfold DFRAME_SIZE in Hf; lia | exact (proj2 (proj2 Hcan) a Ha)].
  + exact Hfr'.
  + exact Hsh'.
Qed.

Theorem d_body_hwr : d_body_hwr_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi HB Hjr Hlo Hhi K Hnew HP Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7. pose proof fs6 as F6.
pose proof Hbl as (_ & _ & _ & Fo). apply Forall_inv in Fo. cbn [fst snd] in Fo.
assert (KR : forall a, d_rdset B cx h a -> 0 <= a < YM05.alloc_ceiling -> ~ (h <= a < h + HUNT_SIZE) ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hd Ha Hnh. apply K; [pose proof alloc_ceiling_lt; lia|]. intros [Hw | Hh];
  [exact (d_geo_out cx h a lo hi Hgeo Hlo (proj2 Ha) Hw) | exact (Hnh Hh)]. }
destruct (d_objs_hupd cx h T G Lk H W3 m3 W4 m4 Hgeo Hobj) as (H' & Hobj').
- intros a Ht Hnh. apply KR; [exact (d_trk_rdset _ _ _ Ht) | exact (d_trk_ceil _ _ _ Hgeo Ht) | exact Hnh].
- exact Hnew.
- apply (d_body_step_gen LAWS cx h n xb xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T G Lk H' HB Hjr
    (d_blocks_perm cx h xb ly3 S3 ly4 S4 Hbl HP) Hobj').
  + intros a Hc Ha. destruct (G8 Hc) as (P1 & P2 & P3 & P4). apply KR; [unfold d_rdset; tauto | lia | unfold HUNT_SIZE in *; lia].
  + intros a Hro Ho He. apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (in_roP_img a Hro)) |].
    intros Hh. apply (off_img_not_img _ _ a Fo); [unfold req_size, HUNT_SIZE in *; cbn; lia | exact (in_roP_img a Hro)].
  + apply (d_can_kept cx W3 m3 W4 m4 Hcan).
    intros a Ha. apply KR; [unfold d_rdset; tauto | exact (in_img_ceil a (proj2 (proj2 Hcan) a Ha)) |].
    intros Hh. apply (off_img_not_img _ _ a Fo); [unfold req_size, HUNT_SIZE in *; cbn; lia | exact (proj2 (proj2 Hcan) a Ha)].
  + exact Hfr'.
  + exact Hsh'.
Qed.

Lemma lat_exit_weaken : forall cx h W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx EXIT_OFF (EV_HEAD MAX_OPS) (ACC_HEAD MT MAX_OPS)
    (fun regs ly3 S3 W3 mem3 md3 => exists n, d_rX B cx h regs /\ d_body B cx h n [] dsh_loop ly3 S3 W3 mem3) W c ->
  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W c.
Proof.
intros cx h W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfrm & Hb & HJ & Hfr & Hk & Hn & Hmo & Hacc & (n & HX & HB)).
exists fq, ly3, S3, regs, mem3, md3, k, acc.
exact (conj Hc (conj Hfrm (conj Hb (conj HJ (conj Hfr (conj Hk (conj Hn (conj Hmo (conj Hacc
  (conj HX (d_body_x_of cx h n dsh_loop ly3 S3 W mem3 HB))))))))))).
Qed.

Lemma xb_out : AR_laws SEGS B -> forall cx h xb ly S W m md k a,
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k -> d_blocks B cx h xb ly S -> d_inxb xb a ->
  ~ (d_FB cx <= a < d_FB cx + fs_frame_bytes DFRAME_CLASS) /\ ~ (h <= a < h + HUNT_SIZE) /\
  ~ (0 < c_n cx /\ c_p cx <= a < c_p cx + c_n cx) /\ ~ in_img SEGS a.
Proof.
intros LAWS cx h xb ly S W m md k a Hjr Hbl (b & nb & Hinb & Ha).
pose proof Hjr as (Hbase & _).
destruct (d_jr_facts cx ly S W m md k Hjr) as (HAR & Hfin & EFB & _ & _).
pose proof Hbl as (Pb & Fb & _ & Ob).
assert (Hob : off_img b (req_size nb)) by (exact (proj1 (Forall_forall _ _) Ob (b, nb) (or_intror Hinb))).
assert (Hnb : ~ In (b, nb) (ablocks B (c_ly cx) (c_S cx))) by (exact (proj1 (Forall_forall _ _) Fb (b, nb) (or_intror Hinb))).
assert (Hab : In (b, nb) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Pb)); apply in_or_app; left; exact Hinb).
assert (Hah : In (h, HUNT_SIZE) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Pb)); apply in_or_app; right; left; reflexivity).
destruct (al_sep _ _ LAWS ly S W m md HAR) as (Hpw & _).
destruct (pw_app_cross _ _ _ Hpw) as (Pbl & PX).
pose proof (pairwise_map_inv _ _ _ Pbl) as Pbl'. cbn beta in Pbl'.
assert (DIS : forall x, In x (ablocks B ly S) -> x <> (b, nb) -> zdisjoint (b, req_size nb) (fst x, req_size (snd x))).
{ intros x Hx Hne. destruct (pw_in2 _ _ (b, nb) x Pbl' Hab Hx (fun E => Hne (eq_sym E))) as [D | D];
  [exact D | exact (zdisj_sym _ _ D)]. }
split; [|split; [|split]].
- intros Hf. pose proof (PX (b, req_size nb) (frame_addr ly DFRAME_CLASS (c_fpos cx), fs_frame_bytes DFRAME_CLASS)) as D.
  assert (Z1 : In (b, req_size nb) (map (fun b0 => (fst b0, req_size (snd b0))) (ablocks B ly S)))
    by (apply (in_map (fun b0 => (fst b0, req_size (snd b0))) _ (b, nb) Hab)).
  assert (Z2 : In (frame_addr ly DFRAME_CLASS (c_fpos cx), fs_frame_bytes DFRAME_CLASS)
    (map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (frames S)))
    by (apply (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (DFRAME_CLASS, c_fpos cx) Hfin)).
  specialize (D Z1 Z2). rewrite EFB in D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- intros Hh. destruct (zz_eq_dec (b, nb) (h, HUNT_SIZE)) as [E | Hne].
  + injection E as -> ->. apply in_split in Hinb as (x1 & x2 & ->).
    pose proof (pairwise_perm _ (fun x y D => zdisj_sym _ _ D) _ _ Pb Pbl') as Pall.
    rewrite <- app_assoc in Pall. cbn [app] in Pall.
    pose proof (pw_dup _ x1 (h, HUNT_SIZE) x2 (ablocks B (c_ly cx) (c_S cx)) Pall) as D. cbn beta in D.
    unfold zdisjoint, req_size, HUNT_SIZE in D. cbn [fst snd Z.eqb] in D. lia.
  + pose proof (DIS (h, HUNT_SIZE) Hah (fun E => Hne (eq_sym E))) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. unfold req_size, HUNT_SIZE in *. cbn [Z.eqb] in D.
    pose proof (req_size_pos nb) as Rp. destruct (Z_le_gt_dec 0 nb); [specialize (Rp ltac:(lia)); lia|].
    unfold req_size in Ha. destruct (nb =? 0) eqn:Enb; [apply Z.eqb_eq in Enb; lia | lia].
- intros (Hc & Hp). pose proof Hbase as (Hpre & _). pose proof Hpre as (_ & _ & _ & _ & Hcase & _).
  destruct Hcase as [(Hn0 & _) | (Hn & Hin)]; [lia|].
  assert (Hin' : In (c_p cx, c_n cx) (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym Pb)); apply in_or_app; right; right; exact Hin).
  assert (Hne : (c_p cx, c_n cx) <> (b, nb)) by (intros E; rewrite E in Hin; exact (Hnb Hin)).
  pose proof (DIS _ Hin' Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Rn).
  pose proof (req_size_pos nb) as Rb. destruct (Z_le_gt_dec 0 nb); [specialize (Rb ltac:(lia)); lia|].
  unfold req_size in Ha. destruct (nb =? 0) eqn:Enb; [apply Z.eqb_eq in Enb; lia | lia].
- exact (off_img_not_img _ _ a Hob Ha).
Qed.

Theorem d_body_hcall : d_body_hcall_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi HB Hjr Hlo Hhi K HP Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7. pose proof fs6 as F6.
pose proof (d_blocks_perm cx h xb ly3 S3 ly4 S4 Hbl HP) as Hbl4.
assert (KR : forall a, 0 <= a < YM05.alloc_ceiling ->
  (d_FB cx <= a < d_FB cx + fs_frame_bytes DFRAME_CLASS) \/ (h <= a < h + HUNT_SIZE) \/
  (0 < c_n cx /\ c_p cx <= a < c_p cx + c_n cx) \/ in_img SEGS a ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hw. apply K; [pose proof alloc_ceiling_lt; lia|]. intros [Hwin | Hx];
  [exact (d_geo_out cx h a lo hi Hgeo Hlo (proj2 Ha) Hwin)|].
  destruct (xb_out LAWS cx h xb ly4 S4 W4 m4 md4 k4 a Hjr Hbl4 Hx) as (N1 & N2 & N3 & N4). tauto. }
apply (d_body_step_gen LAWS cx h n xb xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T G Lk H HB Hjr Hbl4).
- apply (d_objs_kept cx h T G Lk H W3 m3 W4 m4 Hobj).
  intros a Ht. apply KR; [exact (d_trk_ceil _ _ _ Hgeo Ht)|].
  unfold d_trk in Ht. destruct Ht as [Ht | [Ht | [Ht | [Ht | Ht]]]];
    try (left; pose proof (objr_frame _ _ _ Ht) as Hf; unfold DFRAME_SIZE in Hf; lia).
  right; left; exact Ht.
- intros a Hc Ha. destruct (G8 Hc) as (P1 & P2 & _). apply KR; [lia | right; right; left; split; assumption].
- intros a Hro Ho He. apply KR; [exact (in_img_ceil a (in_roP_img a Hro)) | right; right; right; exact (in_roP_img a Hro)].
- apply (d_can_kept cx W3 m3 W4 m4 Hcan).
  intros a Ha. apply KR; [exact (in_img_ceil a (proj2 (proj2 Hcan) a Ha)) | right; right; right; exact (proj2 (proj2 Hcan) a Ha)].
- exact Hfr'.
- exact Hsh'.
Qed.

Lemma d_can_of_journal : forall cx ly S W m md k,
  asink_img_laws SEGS B tfib_K -> ak_canary tfib_K = AE2k.FF_canary ->
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k ->
  val_mem SEGS (rd W m) AE2k.FF_canary 8 (c_canary cx).
Proof.
intros cx ly S W m md k AIL Ecan (Hbase & HJ).
pose proof (proj2 (proj2 Hbase)) as Hv.
refine (val_mem_frame SEGS _ _ _ _ _ _ Hv). intros x Hx. cbn in Hx.
assert (Ho : Exists (YG0n.in_zr x) (ak_owned tfib_K)).
{ apply (ail_owned_core _ _ _ AIL). unfold aenv_core. right; right; right. rewrite Ecan. lia. }
eapply (aenv_kept _ _ _ AIL); [exact HJ | |].
- unfold aenv_addr. left. exact Ho.
- apply fp_spares_off. exact (ail_env_static _ _ _ AIL x Ho).
Qed.

Theorem d_body_step : d_body_step_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS HRO (AIL & Ecan) cx h n xb xb' shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T' G' Lk' H'
  HB Hjr Hbl' Hobj' KI KR Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & _ & _ & _ & _ & _ & _ & _ & _ & Hcan & _).
refine (d_body_step_gen LAWS cx h n xb xb' shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T' G' Lk' H'
  HB Hjr Hbl' Hobj' KI KR _ Hfr' Hsh').
split; [exact (d_can_of_journal cx ly4 S4 W4 m4 md4 k4 AIL Ecan Hjr)|].
split; [exact (proj1 (proj2 Hcan)) | exact (proj2 (proj2 Hcan))].
Qed.

Lemma can_got_rdword : forall (K : asink_syms) ly S (W : world SEGS) m md,
  asink_img_laws SEGS B K -> ak_can_got K = AE2k.FF_got_canary -> ak_canary K = AE2k.FF_canary ->
  AR SEGS B ly S W m md -> rdword (aview SEGS (w_H W) m) AE2k.FF_got_canary = Some AE2k.FF_canary.
Proof.
intros K ly S W m md AIL E1 E2 HAR.
pose proof (acan_got_of_AR SEGS B K AIL ly S W m md HAR) as V. rewrite E1, E2 in V.
apply rdword_of_val_mem; [exact V | unfold AE2k.FF_canary; lia].
Qed.
End j.
End h.
End f.
End d.
