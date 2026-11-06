From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_add_b_c op_add_c SlotInv SlotRI3.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma nw_filter_none (l : list (Z * Z)) q : (forall m, ~ In (q, m) l) -> zsum snd (filter (fun t => fst t =? q) l) = 0.
Proof.
  induction l as [|[a m] l IH]; intros H; [reflexivity|]. cbn [filter fst].
  destruct (Z.eqb_spec a q) as [->|Hne].
  - exfalso. apply (H m). left. reflexivity.
  - apply IH. intros m' Hm'. apply (H m'). right. exact Hm'.
Qed.

Lemma nw_filter_one (l : list (Z * Z)) q n : List.NoDup (map fst l) -> In (q, n) l ->
  zsum snd (filter (fun t => fst t =? q) l) = n.
Proof.
  induction l as [|[a m] l IH]; intros HN Hin; [destruct Hin|].
  cbn [map fst] in HN. apply NoDup_cons_iff in HN as [Ha HN]. cbn [filter fst].
  destruct Hin as [Ei|Hin].
  - inversion Ei; subst. rewrite Z.eqb_refl, zsum_cons. cbn [snd].
    rewrite (nw_filter_none l q); [lia|]. intros m' Hm'. apply Ha. apply in_map_iff. exists (q, m'). split; [reflexivity|exact Hm'].
  - destruct (Z.eqb_spec a q) as [->|Hne].
    + exfalso. apply Ha. apply in_map_iff. exists (q, n). split; [reflexivity|exact Hin].
    + exact (IH HN Hin).
Qed.

Lemma nw_sz_at L A q n : List.NoDup (map fst (blocks L A)) -> In (q, n) (blocks L A) -> nc_sz L A q = n.
Proof. intros HN Hin. unfold nc_sz. exact (nw_filter_one _ q n HN Hin). Qed.

Lemma nw_sz_none L A q : (forall m, ~ In (q, m) (blocks L A)) -> nc_sz L A q = 0.
Proof. intros H. unfold nc_sz. exact (nw_filter_none _ q H). Qed.

Lemma nw_zsum_concat {X Y : Type} (f : Y -> Z) (g : X -> list Y) l :
  zsum f (concat (map g l)) = zsum (fun x => zsum f (g x)) l.
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [map concat]. rewrite zsum_app, zsum_cons, IH. reflexivity.
Qed.

Lemma nw_zsum_le {X : Type} (f g : X -> Z) l : (forall x, In x l -> f x <= g x) -> zsum f l <= zsum g l.
Proof.
  induction l as [|x l IH]; intros H; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons.
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.

Lemma nw_f2_r {X Y : Type} (R : X -> Y -> Prop) l1 l2 y : Forall2 R l1 l2 -> In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros HF. induction HF as [|x y' l1 l2 Hxy HF IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin].
  - exists x. split; [left; reflexivity|exact Hxy].
  - destruct (IH Hin) as (x' & Hx' & HR). exists x'. split; [right; exact Hx'|exact HR].
Qed.

Section NW.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma nw_no_zero L A mem md : aa_MR API L A mem md -> forall m, ~ In (0, m) (blocks L A).
Proof.
  intros HM m Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & Ep & Hp). cbn [fst snd] in Ep.
  inversion Ep as [[E0 E1]]. pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md p n HM Hp) as [R _]. lia.
Qed.

Lemma nw_list_le L A mem LA l lines : List.NoDup (map fst (blocks L A)) -> list_at B L A mem LA l lines ->
  zsum (nc_sz L A) (arr_nc l) <= nw_list l.
Proof.
  intros HN (_ & Hn & Hc & _). unfold arr_nc, nw_list, NC_PER.
  destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0].
  - rewrite zsum_nil. lia.
  - destruct Hc as [(Hc0 & _)|(_ & Hin & _)]; [lia|].
    rewrite zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN Hin). lia.
Qed.

Lemma nw_src_le L A mem HA h : List.NoDup (map fst (blocks L A)) -> src_at B L A mem HA h ->
  zsum (nc_sz L A) (src_nc h) <= nw_src h.
Proof.
  intros HN (_ & _ & _ & _ & _ & Lp & _ & _ & _ & _ & Hpart & _ & _ & _ & _ & Le & Lh & _).
  unfold src_nc, nw_src. rewrite !zsum_app, zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN Hpart).
  pose proof (nw_list_le L A mem _ _ _ HN Lp). pose proof (nw_list_le L A mem _ _ _ HN Le).
  pose proof (nw_list_le L A mem _ _ _ HN Lh). unfold DATA_PER, PARTIAL_BYTES. lia.
Qed.

Lemma nw_ent_le L A mem e : List.NoDup (map fst (blocks L A)) -> entry_ok B L A mem e ->
  zsum (nc_sz L A) (entry_nc e) <= nw_ent e.
Proof.
  intros HN (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _). unfold entry_nc, nw_ent, DATA_PER.
  rewrite zsum_app.
  assert (X1 : zsum (nc_sz L A) (if re_cap e =? 0 then [] else [re_buf e]) <= re_cap e).
  { destruct (Z.eqb_spec (re_cap e) 0) as [E0|E0].
    - rewrite zsum_nil. lia.
    - destruct Hbuf as [(Hc0 & _)|(_ & Hin & _)]; [lia|].
      rewrite zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN Hin). lia. }
  assert (X2 : zsum (nc_sz L A) (if re_hp e =? 0 then [] else [re_hp e]) <= (if re_hp e =? 0 then 0 else re_kh e)).
  { destruct (Z.eqb_spec (re_hp e) 0) as [E0|E0].
    - rewrite zsum_nil. lia.
    - destruct Hhp as [(Hh0 & _)|(Hin & _)]; [lia|].
      rewrite zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN Hin). lia. }
  lia.
Qed.

Theorem ncs_le_wt L A mem md t nfd G nout cap out es hj :
  aa_MR API L A mem md ->
  output_at B L A mem nout cap out ->
  relay_at B L A mem t nfd G (bv_unsigned out) es hj ->
  (length es <= 4)%nat ->
  List.NoDup (map fst (blocks L A)) ->
  ncs (view_of G (bv_unsigned out) es hj) L A <= nc_wt es hj.
Proof.
  intros HM HO HR Hes HN.
  destruct HR as (_ & HG & _ & Hent & _ & _ & Hpair & _).
  pose proof (Forall2_length Hpair) as Hlen.
  assert (XG : nc_sz L A G <= SRC_TABLE) by (rewrite (nw_sz_at L A _ _ HN HG); lia).
  assert (XO : nc_sz L A (bv_unsigned out) <= TBBYTES).
  { unfold output_at in HO. cbv zeta in HO. destruct HO as ((O & junk & Hc) & Hcap).
    destruct Hc as [(Hc0 & Ho0 & _)|(_ & _ & Hin & _)].
    - rewrite Ho0, (nw_sz_none L A 0 (nw_no_zero L A mem md HM)). unfold TBBYTES. lia.
    - rewrite (nw_sz_at L A _ _ HN Hin). exact Hcap. }
  assert (XE : zsum (nc_sz L A) (concat (map entry_nc es)) <= zsum nw_ent es).
  { rewrite nw_zsum_concat. apply nw_zsum_le. intros e He.
    rewrite Forall_forall in Hent. exact (nw_ent_le L A mem e HN (Hent e He)). }
  assert (XS : zsum (nc_sz L A) (concat (map (fun p => src_nc (fst p)) hj)) <= zsum (fun p => nw_src (fst p)) hj).
  { rewrite nw_zsum_concat. apply nw_zsum_le. intros p Hp.
    destruct (nw_f2_r _ _ _ p Hpair Hp) as (e & _ & Hok).
    unfold pair_ok in Hok. cbv zeta in Hok. destruct Hok as (Hsrc & _).
    exact (nw_src_le L A mem _ (fst p) HN Hsrc). }
  unfold ncs, view_of, nc_wt. cbn [rv_nc]. rewrite !zsum_cons, zsum_app.
  unfold NW_ENT0, NW_SRC0, PARTIAL_BYTES. lia.
Qed.

End NW.
