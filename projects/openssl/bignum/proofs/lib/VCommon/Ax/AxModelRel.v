(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxSys AxOcc AxAcct AxMeasure AxSysMmap AxPack.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxFd AxLz.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ent_ok (ρ : valuation) (e : aent) : Prop :=
  0 < leval ρ (ae_base e) /\ 0 < ae_size e /\ leval ρ (ae_base e) + ae_size e < two64.

Definition in_ent (ρ : valuation) (e : aent) (z : Z) : Prop := leval ρ (ae_base e) <= z < leval ρ (ae_base e) + ae_size e.

Definition in_exp (ρ : valuation) (exps : list (aent * lin * Z)) (e : aent) (z : Z) : Prop :=
  exists x, In x exps /\ fst (fst x) = e /\ leval ρ (snd (fst x)) <= z < leval ρ (snd (fst x)) + snd x.

Section MRdef.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.

Record MR (ρ : valuation) (am : amodel) (m : Model) : Prop := {
  mr_res : vm_reserved (m_vmmaps m) = segments_reserved segs;
  mr_maps : vm_maps (m_vmmaps m) = map (ent_val ρ) (am_maps am);
  mr_ents : Forall (ent_ok ρ) (am_maps am);
  mr_brk0 : bv_unsigned (vm_start_brk (m_vmmaps m)) = leval ρ (am_brk0 am);
  mr_brk : bv_unsigned (vm_brk (m_vmmaps m)) = leval ρ (am_brk am);
  mr_atop : alloc_top (m_vmmaps m) = leval ρ (am_atop am);
  mr_tid : match am_tid am with None => m_tid m = None | Some t => exists y, m_tid m = Some y /\ xv_val ρ t y end;
  mr_fds : fd_rel fs0 ρ (am_fd am) (m_fds m);
  mr_fs : m_fs m = fs0;
  mr_lazy : forall p, In p (m_vm_lazy m) -> bv_unsigned (fst p) + bv_unsigned (snd p) <= alloc_top (m_vmmaps m);
  mr_shadow : am_shadow am = true -> In ls_ent (am_maps am) /\ In gap_ent (am_maps am) /\ In hs_ent (am_maps am);
  mr_disj : forall p q, In p (vm_maps (m_vmmaps m)) -> In q (vm_reserved (m_vmmaps m)) -> iv_disj (bas p) (bas p + bsz p) q;
  mr_na : nowrap (vm_noaccess (m_vmmaps m));
  mr_pw : pw_disj (vm_maps (m_vmmaps m));
  mr_nacov : forall e z, In e (am_maps am) -> ae_na e = true -> in_ent ρ e z -> ~ in_exp ρ (am_exp am) e z ->
             inl (vm_noaccess (m_vmmaps m)) z;
  mr_na_maps : forall z, inl (vm_noaccess (m_vmmaps m)) z -> inl (vm_maps (m_vmmaps m)) z;
  mr_top : forall p, In p (vm_maps (m_vmmaps m)) -> bas p + bsz p <= alloc_top (m_vmmaps m);
  mr_span : am_shadow am = true -> forall e, In e (am_maps am) -> var_ent e = true ->
            leval ρ (ae_base e) + ae_size e <= sh_lo \/ sh_hi <= leval ρ (ae_base e);
  mr_nacov2 : forall e, In e (am_maps am) -> ae_na e = true -> (forall x, In x (am_exp am) -> fst (fst x) <> e) ->
              In (ent_val ρ e) (vm_noaccess (m_vmmaps m));
  mr_lazy_res : forall p q, In p (m_vm_lazy m) -> In q (vm_reserved (m_vmmaps m)) -> iv_disj (bas p) (bas p + bsz p) q;

  mr_lz : LZr ρ (am_maps am) (m_vm_lazy m) (vm_noaccess (m_vmmaps m))
}.

Lemma ent_val_bas (ρ : valuation) (e : aent) : ent_ok ρ e -> bas (ent_val ρ e) = leval ρ (ae_base e).
Proof. intros (H1 & H2 & H3). unfold bas, ent_val. cbn [fst]. apply u_Z_to_bv. lia. Qed.

Lemma ent_val_bsz (ρ : valuation) (e : aent) : ent_ok ρ e -> bsz (ent_val ρ e) = ae_size e.
Proof. intros (H1 & H2 & H3). unfold bsz, ent_val. cbn [snd]. apply u_Z_to_bv. lia. Qed.

Lemma MR_ent (ρ : valuation) (am : amodel) (m : Model) (e : aent) : MR ρ am m -> In e (am_maps am) -> ent_ok ρ e.
Proof. intros HM Hin. exact (proj1 (Forall_forall _ _) (mr_ents ρ am m HM) e Hin). Qed.

Lemma MR_ent_in (ρ : valuation) (am : amodel) (m : Model) (e : aent) :
  MR ρ am m -> In e (am_maps am) -> In (ent_val ρ e) (vm_maps (m_vmmaps m)).
Proof. intros HM Hin. rewrite (mr_maps ρ am m HM). apply in_map. exact Hin. Qed.

Lemma MR_maps_ent (ρ : valuation) (am : amodel) (m : Model) (p : word * word) :
  MR ρ am m -> In p (vm_maps (m_vmmaps m)) -> exists e, In e (am_maps am) /\ p = ent_val ρ e /\ ent_ok ρ e.
Proof.
  intros HM Hin. rewrite (mr_maps ρ am m HM) in Hin. apply in_map_iff in Hin as [e [<- He]].
  exists e. split; [exact He | split; [reflexivity | exact (MR_ent ρ am m e HM He)]].
Qed.

Lemma MR_maps_pos (ρ : valuation) (am : amodel) (m : Model) : MR ρ am m -> forall q, In q (vm_maps (m_vmmaps m)) -> 0 < bsz q.
Proof. intros HM q Hq. destruct (MR_maps_ent ρ am m q HM Hq) as [e [_ [-> He]]]. rewrite (ent_val_bsz ρ e He). exact (proj1 (proj2 He)). Qed.

Lemma MR_maps_nowrap (ρ : valuation) (am : amodel) (m : Model) : MR ρ am m -> nowrap (vm_maps (m_vmmaps m)).
Proof.
  intros HM q Hq. pose proof (mr_top ρ am m HM q Hq) as Ht. pose proof (alloc_top_lt (m_vmmaps m)) as Ha.
  change two_pow_64 with two64 in Ha. lia.
Qed.

Lemma MR_lazy_nowrap (ρ : valuation) (am : amodel) (m : Model) : MR ρ am m -> nowrap (m_vm_lazy m).
Proof.
  intros HM q Hq. pose proof (mr_lazy ρ am m HM q Hq) as Ht. pose proof (alloc_top_lt (m_vmmaps m)) as Ha.
  change two_pow_64 with two64 in Ha. unfold bas, bsz. lia.
Qed.

Lemma MR_in_ent_inl (ρ : valuation) (am : amodel) (m : Model) (e : aent) (z : Z) :
  MR ρ am m -> In e (am_maps am) -> in_ent ρ e z -> inl (vm_maps (m_vmmaps m)) z.
Proof.
  intros HM Hin Hz. exists (ent_val ρ e). split; [exact (MR_ent_in ρ am m e HM Hin)|].
  pose proof (MR_ent ρ am m e HM Hin) as He. rewrite (ent_val_bas ρ e He), (ent_val_bsz ρ e He). exact Hz.
Qed.

Lemma MR_inl_ent (ρ : valuation) (am : amodel) (m : Model) (z : Z) :
  MR ρ am m -> inl (vm_maps (m_vmmaps m)) z -> exists e, In e (am_maps am) /\ in_ent ρ e z.
Proof.
  intros HM [p [Hp Hz]]. destruct (MR_maps_ent ρ am m p HM Hp) as [e [He [-> Hok]]].
  exists e. split; [exact He|]. rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok) in Hz. exact Hz.
Qed.

Lemma MR_mat (ρ : valuation) (am : amodel) (m : Model) (pages : list word) :
  MR ρ am m -> MR ρ am (with_vm_backing (m_vm_lazy m) pages m).
Proof.
  destruct m as [fd [maps lazy mat] io fs proc lim tm].
  intros [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21]. constructor; assumption.
Qed.

Lemma MR_next (ρ : valuation) (am : amodel) (m : Model) (nx : int) :
  MR ρ am m -> MR ρ (AM (am_maps am) (am_brk0 am) (am_brk am) (am_tid am) (am_shadow am) nx (am_atop am) (am_out am) (am_exp am) (am_fd am)) m.
Proof.
  intros [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  constructor; cbn [am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd]; assumption.
Qed.

Lemma MR_out (ρ : valuation) (am : amodel) (m : Model) (o : list piece) :
  MR ρ am m -> MR ρ (AM (am_maps am) (am_brk0 am) (am_brk am) (am_tid am) (am_shadow am) (am_next am) (am_atop am) o (am_exp am) (am_fd am)) m.
Proof.
  intros [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  constructor; cbn [am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd]; assumption.
Qed.

Lemma MR_tid (ρ : valuation) (am : amodel) (m : Model) (t : xv) (y : word) (nx : int) :
  MR ρ am m -> xv_val ρ t y ->
  MR ρ (AM (am_maps am) (am_brk0 am) (am_brk am) (Some t) (am_shadow am) nx (am_atop am) (am_out am) (am_exp am) (am_fd am)) (with_tid y m).
Proof.
  destruct m as [fd [maps lazy mat] io fs proc lim tm].
  intros [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21] Hv.
  constructor; cbn [am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd]; try assumption.
  exists y. split; [reflexivity | exact Hv].
Qed.

Lemma MR_agree (v : int) (ρ ρ' : valuation) (am : amodel) (m : Model) :
  (forall x, x <> v -> ρ' x = ρ x) -> model_occ v am = false -> MR ρ am m -> MR ρ' am m.
Proof.
  intros Hag Ho [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  destruct (model_occ_parts v am Ho) as (Ofd & Omaps & Obrk0 & Obrk & Oatop & Otid & Oexp & _).
  assert (Hent : forall e, In e (am_maps am) -> leval ρ' (ae_base e) = leval ρ (ae_base e)).
  { intros e He. apply (leval_agree v ρ ρ' Hag). destruct (ts_occ v (snd (ae_base e))) eqn:E; [|reflexivity].
    assert (X : existsb (ent_occ v) (am_maps am) = true) by (apply existsb_exists; exists e; split; [exact He | exact E]).
    rewrite X in Omaps. discriminate Omaps. }
  assert (Hval : forall e, In e (am_maps am) -> ent_val ρ' e = ent_val ρ e) by (intros e He; unfold ent_val; rewrite (Hent e He); reflexivity).
  assert (Hxf : forall x, In x (am_exp am) -> leval ρ' (snd (fst x)) = leval ρ (snd (fst x))).
  { intros x Hx. apply (leval_agree v ρ ρ' Hag). destruct (ts_occ v (snd (snd (fst x)))) eqn:E2; [|reflexivity].
    assert (X : existsb (fun x => ent_occ v (fst (fst x)) || ts_occ v (snd (snd (fst x)))) (am_exp am) = true).
    { apply existsb_exists. exists x. split; [exact Hx|]. cbv beta. apply orb_true_iff. right. exact E2. }
    rewrite X in Oexp. discriminate Oexp. }
  assert (Hexp : forall e z, in_exp ρ' (am_exp am) e z <-> in_exp ρ (am_exp am) e z).
  { intros e z. unfold in_exp. split; intros [x [Hx [E Hz]]]; exists x; (split; [exact Hx|]); (split; [exact E|]).
    - rewrite <- (Hxf x Hx). exact Hz.
    - rewrite (Hxf x Hx). exact Hz. }
  constructor; try assumption.
  - rewrite H2. apply map_ext_in. intros e He. symmetry. exact (Hval e He).
  - rewrite Forall_forall in *. intros e He. specialize (H3 e He). unfold ent_ok in *. rewrite (Hent e He). exact H3.
  - rewrite (leval_agree v ρ ρ' Hag _ Obrk0). exact H4.
  - rewrite (leval_agree v ρ ρ' Hag _ Obrk). exact H5.
  - rewrite (leval_agree v ρ ρ' Hag _ Oatop). exact H6.
  - destruct (am_tid am) as [t|]; [|exact H7]. destruct H7 as [y [Ey Hy]]. exists y. split; [exact Ey | exact (xv_val_agree v ρ ρ' t y Hag Otid Hy)].
  - exact (fd_rel_agree fs0 v ρ ρ' (am_fd am) (m_fds m) Hag Ofd H8).
  - intros e z He Hna Hz Hex. apply (H15 e z He Hna).
    + unfold in_ent in *. rewrite <- (Hent e He). exact Hz.
    + intros X. apply Hex. apply Hexp. exact X.
  - intros Hs e He Hv. rewrite (Hent e He). exact (H18 Hs e He Hv).
  - intros e He Hna Hex. rewrite (Hval e He). exact (H19 e He Hna Hex).
  - exact (LZr_ext ρ ρ' _ _ _ Hent H21).
Qed.

Lemma pw_disj_cons (p : word * word) (l : list (word * word)) :
  (forall q, In q l -> iv_disj (bas p) (bas p + bsz p) q) -> pw_disj l -> pw_disj (p :: l).
Proof.
  intros H1 H2 l1 q l2 E. destruct l1 as [|x l1]; cbn [app] in E.
  - injection E as <- <-. exact H1.
  - injection E as _ E. exact (H2 l1 q l2 E).
Qed.

Section Grant.
Variable ρ : valuation.
Variable am : amodel.
Variable m : Model.
Hypothesis HM : MR ρ am m.
Variable e : aent.
Variable a : word.
Variable nZ : Z.
Variable flags : word.
Variable nx : int.
Hypothesis Hbase : leval ρ (ae_base e) = bv_unsigned a.
Hypothesis Hsize : ae_size e = nZ.
Hypothesis Hn : 0 < nZ.
Hypothesis Hok : null_ok m nZ a.
Hypothesis Hspan : am_shadow am = true -> var_ent e = true -> bv_unsigned a + nZ <= sh_lo \/ sh_hi <= bv_unsigned a.

Local Notation n := (Z_to_bv 64 nZ).
Local Notation h := (m_vmmaps m).

Lemma grant_bounds : 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h /\ bv_unsigned a + nZ < two64 /\ bv_unsigned n = nZ.
Proof.
  destruct Hok as (_ & H2 & H3 & _). pose proof (alloc_top_lt h) as Ht. change two_pow_64 with two64 in Ht.
  repeat split; try lia. apply u_Z_to_bv. lia.
Qed.

Lemma grant_ent_val : ent_val ρ e = (a, n).
Proof. unfold ent_val. rewrite Hbase, Hsize, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma grant_ent_ok : ent_ok ρ e.
Proof. destruct grant_bounds as (B1 & B2 & B3 & B4). unfold ent_ok. rewrite Hbase, Hsize. lia. Qed.

Lemma grant_free_maps : forall q, In q (vm_maps h) -> iv_disj (bv_unsigned a) (bv_unsigned a + nZ) q.
Proof.
  intros q Hq. destruct Hok as (_ & _ & _ & Hf). destruct grant_bounds as (_ & _ & _ & B4).
  pose proof (proj1 (region_free_disj _ _ _) Hf q (in_or_app _ _ _ (or_intror Hq))) as D. rewrite B4 in D. exact D.
Qed.

Lemma grant_free_res : forall q, In q (vm_reserved h) -> iv_disj (bv_unsigned a) (bv_unsigned a + nZ) q.
Proof.
  intros q Hq. destruct Hok as (_ & _ & _ & Hf). destruct grant_bounds as (_ & _ & _ & B4).
  pose proof (proj1 (region_free_disj _ _ _) Hf q (in_or_app _ _ _ (or_introl Hq))) as D. rewrite B4 in D. exact D.
Qed.

Lemma MR_grant_gen (m' : Model) (na' : list (word * word)) (b : lin) :
  vm_reserved (m_vmmaps m') = vm_reserved h -> vm_maps (m_vmmaps m') = (a, n) :: vm_maps h -> vm_noaccess (m_vmmaps m') = na' ->
  vm_start_brk (m_vmmaps m') = vm_start_brk h -> alloc_top (m_vmmaps m') = alloc_top h ->
  bv_unsigned (vm_brk (m_vmmaps m')) = leval ρ b ->
  m_tid m' = m_tid m -> m_fds m' = m_fds m -> m_fs m' = m_fs m ->
  (forall p, In p (m_vm_lazy m') -> In p (m_vm_lazy m) \/ (bv_unsigned a <= bas p /\ bas p + bsz p <= bv_unsigned a + nZ)) ->
  nowrap na' ->
  (forall z, inl (vm_noaccess h) z -> inl na' z) ->
  (forall z, inl na' z -> inl (vm_noaccess h) z \/ bv_unsigned a <= z < bv_unsigned a + nZ) ->
  (forall p, In p (vm_noaccess h) -> In p na') ->
  (ae_na e = true -> In (a, n) na') ->

  (forall p, In p (m_vm_lazy m') -> In p (m_vm_lazy m) \/ (bv_unsigned a <= bas p /\ bas p + bsz p <= bv_unsigned a + nZ /\ BIGMIN <= nZ)) ->
  (forall p, In p (m_vm_lazy m) -> In p (m_vm_lazy m')) ->
  Forall pos_al na' -> Forall pos_al (m_vm_lazy m') ->
  (lzfull e = true -> forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     page_in_ranges (page_base x) (m_vm_lazy m') = true /\ ~ inl na' (bv_unsigned x)) ->
  MR ρ (AM (e :: am_maps am) (am_brk0 am) b (am_tid am) (am_shadow am) nx (am_atop am) (am_out am) (am_exp am) (am_fd am)) m'.
Proof.
  intros Er Em Ena Esb Eat Eb Et Ef Efs Hlz Hnw Hsub Hsup Hin Hnew Hlzb Hlzm Hnapos Hlzpos Hfull.
  destruct grant_bounds as (B1 & B2 & B3 & B4).
  pose proof HM as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  constructor; cbn [am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd];
    rewrite ?Er, ?Em, ?Ena, ?Esb, ?Eat, ?Et, ?Ef, ?Efs; try assumption.
  -   cbn [map]. rewrite grant_ent_val, H2. reflexivity.
  -   constructor; [exact grant_ent_ok | exact H3].
  -   intros p Hp. destruct (Hlz p Hp) as [Hp'|[L1 L2]]; [exact (H10 p Hp')|]. unfold bas, bsz in L1, L2. lia.
  -   intros Hs. destruct (H11 Hs) as (S1 & S2 & S3). repeat split; right; assumption.
  -   intros p q [<-|Hp] Hq; [|exact (H12 p q Hp Hq)]. unfold bas at 1 2, bsz at 1. cbn [fst snd]. rewrite B4. exact (grant_free_res q Hq).
  -   apply pw_disj_cons; [|exact H14]. intros q Hq. unfold bas at 1 2, bsz at 1. cbn [fst snd]. rewrite B4. exact (grant_free_maps q Hq).
  -   intros e0 z [<-|He0] Hna Hz Hex.
    + exists (a, n). split; [exact (Hnew Hna)|]. unfold in_ent in Hz. rewrite Hbase, Hsize in Hz. unfold bas, bsz. cbn [fst snd]. rewrite B4. exact Hz.
    + apply Hsub. exact (H15 e0 z He0 Hna Hz Hex).
  -   intros z Hz. apply inl_cons. destruct (Hsup z Hz) as [Hz'|Hz']; [right; exact (H16 z Hz') | left].
    unfold bas, bsz. cbn [fst snd]. rewrite B4. exact Hz'.
  -   intros p [<-|Hp]; [|exact (H17 p Hp)]. unfold bas, bsz. cbn [fst snd]. rewrite B4. exact B2.
  -   intros Hs e0 [<-|He0] Hv; [|exact (H18 Hs e0 He0 Hv)]. rewrite Hbase, Hsize. exact (Hspan Hs Hv).
  -   intros e0 [<-|He0] Hna Hex; [rewrite grant_ent_val; exact (Hnew Hna) | exact (Hin _ (H19 e0 He0 Hna Hex))].
  -   intros p q Hp Hq. destruct (Hlz p Hp) as [Hp'|[L1 L2]]; [exact (H20 p q Hp' Hq)|].
    pose proof (grant_free_res q Hq) as D. unfold iv_disj in *. lia.
  -   apply (LZr_grant ρ (am_maps am) (m_vm_lazy m) (vm_noaccess h) _ _ e (bv_unsigned a) nZ H21); try assumption.
    intros e' He'. pose proof (grant_free_maps (ent_val ρ e') (MR_ent_in ρ am m e' HM He')) as D.
      pose proof (MR_ent ρ am m e' HM He') as Hok'. unfold iv_disj in D. rewrite (ent_val_bas ρ e' Hok'), (ent_val_bsz ρ e' Hok') in D.
      unfold ent_lo, ent_hi. lia.
Qed.

Lemma grant_lazy (m0 : Model) : m_vm_lazy m0 = m_vm_lazy m ->
  forall p, In p (m_vm_lazy (with_mmap_backing flags a n m0)) -> In p (m_vm_lazy m) \/ (bv_unsigned a <= bas p /\ bas p + bsz p <= bv_unsigned a + nZ).
Proof.
  intros E p Hp. destruct grant_bounds as (B1 & B2 & B3 & B4).
  destruct (with_mmap_backing_fields flags a n m0) as (_ & _ & _ & _ & _ & El). rewrite El in Hp.
  destruct (mmap_noreserve_b flags); [|left; rewrite <- E; exact Hp].
  apply in_app_or in Hp as [Hp|Hp]; [|left; rewrite <- E; exact Hp]. right.
  destruct (lazy_interior_within a n p ltac:(rewrite B4; lia) Hp) as (_ & L1 & L2). rewrite B4 in L2. split; assumption.
Qed.

Hypothesis Hbig : mmap_noreserve_b flags = true -> BIGMIN <= nZ.
Hypothesis Hfull : lzfull e = true -> mmap_noreserve_b flags = true /\ bv_unsigned a mod 4096 = 0 /\ nZ mod 4096 = 0.

Lemma grant_lazy_big (m0 : Model) : m_vm_lazy m0 = m_vm_lazy m ->
  forall p, In p (m_vm_lazy (with_mmap_backing flags a n m0)) ->
    In p (m_vm_lazy m) \/ (bv_unsigned a <= bas p /\ bas p + bsz p <= bv_unsigned a + nZ /\ BIGMIN <= nZ).
Proof.
  intros E p Hp. destruct grant_bounds as (B1 & B2 & B3 & B4).
  destruct (with_mmap_backing_fields flags a n m0) as (_ & _ & _ & _ & _ & El). rewrite El in Hp.
  destruct (mmap_noreserve_b flags) eqn:Ef; [|left; rewrite <- E; exact Hp].
  apply in_app_or in Hp as [Hp|Hp]; [|left; rewrite <- E; exact Hp]. right.
  destruct (lazy_interior_within a n p ltac:(rewrite B4; lia) Hp) as (_ & L1 & L2). rewrite B4 in L2. repeat split; try assumption. exact (Hbig eq_refl).
Qed.

Lemma grant_lazy_mono (m0 : Model) : m_vm_lazy m0 = m_vm_lazy m ->
  forall p, In p (m_vm_lazy m) -> In p (m_vm_lazy (with_mmap_backing flags a n m0)).
Proof.
  intros E p Hp. destruct (with_mmap_backing_fields flags a n m0) as (_ & _ & _ & _ & _ & El). rewrite El, E.
  destruct (mmap_noreserve_b flags); [apply in_or_app; right; exact Hp | exact Hp].
Qed.

Lemma grant_lazy_posal (m0 : Model) : m_vm_lazy m0 = m_vm_lazy m -> Forall pos_al (m_vm_lazy (with_mmap_backing flags a n m0)).
Proof.
  intros E. destruct grant_bounds as (B1 & B2 & B3 & B4). destruct (with_mmap_backing_fields flags a n m0) as (_ & _ & _ & _ & _ & El). rewrite El, E.
  pose proof (proj2 (proj2 (proj2 (mr_lz ρ am m HM)))) as Z6.
  destruct (mmap_noreserve_b flags); [apply Forall_app; split; [apply posal_interior; rewrite B4; lia | exact Z6] | exact Z6].
Qed.

Lemma grant_full_lazy (m0 : Model) : lzfull e = true -> forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
  page_in_ranges (page_base x) (m_vm_lazy (with_mmap_backing flags a n m0)) = true.
Proof.
  intros Hf x Hx. destruct grant_bounds as (B1 & B2 & B3 & B4). destruct (Hfull Hf) as (Fn & Fa & Fz).
  destruct (with_mmap_backing_fields flags a n m0) as (_ & _ & _ & _ & _ & El). rewrite El, Fn.
  assert (Fh : (bv_unsigned a + nZ) mod 4096 = 0) by (rewrite Z.add_mod, Fa, Fz by lia; reflexivity).
  destruct (page_in_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Fa Fh Hx) as [I1 I2].
  apply pir_app_l. apply pir_interior; rewrite ?B4; try assumption; lia.
Qed.

Lemma grant_fresh_na (x : Z) : bv_unsigned a <= x < bv_unsigned a + nZ -> ~ inl (vm_noaccess h) x.
Proof.
  intros Hx Hi. destruct (mr_na_maps ρ am m HM x Hi) as [q [Hq Hxq]]. pose proof (grant_free_maps q Hq) as D. unfold iv_disj in D. lia.
Qed.

Theorem MR_grant_rw : ae_na e = false -> MR ρ (am_grant am e nx) (null_rw_model flags a n m).
Proof.
  intros Hna. unfold null_rw_model.
  destruct (with_mmap_backing_fields flags a n (with_vmmaps (grant_maps m a n (vm_noaccess h)) m)) as (Ev & _ & Ef & Efs & Et & _).
  apply (MR_grant_gen _ (vm_noaccess h) (am_brk am)); rewrite ?Ev; try assumption; try reflexivity.
  - exact (mr_brk ρ am m HM).
  - apply grant_lazy. reflexivity.
  - exact (mr_na ρ am m HM).
  - tauto.
  - tauto.
  - tauto.
  - rewrite Hna. discriminate.
  - apply grant_lazy_big. reflexivity.
  - apply grant_lazy_mono. reflexivity.
  - exact (proj1 (proj2 (proj2 (mr_lz ρ am m HM)))).
  - apply grant_lazy_posal. reflexivity.
  - intros Hf x Hx. split; [exact (grant_full_lazy _ Hf x Hx) | exact (grant_fresh_na _ Hx)].
Qed.

Theorem MR_grant_na : lzfull e = false -> nZ mod 4096 = 0 -> MR ρ (am_grant am e nx) (null_na_model flags a n m).
Proof.
  intros Hnfull Hnal. unfold null_na_model. destruct grant_bounds as (B1 & B2 & B3 & B4).
  destruct (with_mmap_backing_fields flags a n (with_vmmaps (grant_maps m a n ((a, n) :: vm_noaccess h)) m)) as (Ev & _ & Ef & Efs & Et & _).
  apply (MR_grant_gen _ ((a, n) :: vm_noaccess h) (am_brk am)); rewrite ?Ev; try assumption; try reflexivity.
  - exact (mr_brk ρ am m HM).
  - apply grant_lazy. reflexivity.
  - apply nowrap_cons; [unfold bas, bsz; cbn [fst snd]; lia | exact (mr_na ρ am m HM)].
  - intros z Hz. apply inl_cons. right. exact Hz.
  - intros z Hz. apply inl_cons in Hz as [Hz|Hz]; [right | left; exact Hz]. unfold bas, bsz in Hz. cbn [fst snd] in Hz. lia.
  - intros p Hp. right. exact Hp.
  - intros _. left. reflexivity.
  - apply grant_lazy_big. reflexivity.
  - apply grant_lazy_mono. reflexivity.
  - constructor; [|exact (proj1 (proj2 (proj2 (mr_lz ρ am m HM))))]. unfold pos_al. rewrite bas_mk, bsz_mk, B4.
    destruct Hok as (A1 & _). unfold page_size in A1. auto.
  - apply grant_lazy_posal. reflexivity.
  - intros Hf. rewrite Hf in Hnfull. discriminate Hnfull.
Qed.

Theorem MR_brk_grow (H' : VmMaps) (b : lin) :
  ae_na e = false -> lzfull e = false -> vm_reserved H' = vm_reserved h -> vm_maps H' = (a, n) :: vm_maps h -> vm_noaccess H' = vm_noaccess h ->
  vm_start_brk H' = vm_start_brk h -> vm_init_sp H' = vm_init_sp h -> bv_unsigned (vm_brk H') = leval ρ b ->
  MR ρ (am_brk_grow am e b nx) (with_vmmaps H' m).
Proof.
  intros Hna Hnfull Er Em Ena Esb Esp Eb. unfold am_brk_grow.
  apply (MR_grant_gen (with_vmmaps H' m) (vm_noaccess h) b); try assumption; try reflexivity.
  - unfold alloc_top. change (m_vmmaps (with_vmmaps H' m)) with H'. rewrite Esp. reflexivity.
  - intros p Hp. left. exact Hp.
  - exact (mr_na ρ am m HM).
  - tauto.
  - tauto.
  - tauto.
  - rewrite Hna. discriminate.
  - intros p Hp. left. exact Hp.
  - intros p Hp. exact Hp.
  - exact (proj1 (proj2 (proj2 (mr_lz ρ am m HM)))).
  - exact (proj2 (proj2 (proj2 (mr_lz ρ am m HM)))).
  - intros Hf. rewrite Hf in Hnfull. discriminate Hnfull.
Qed.

End Grant.

Lemma MR_live (ρ : valuation) (l : list aent) : Forall (ent_ok ρ) l -> live_bytes (map (ent_val ρ) l) = ents_total l.
Proof.
  induction 1 as [|e r He _ IH]; [reflexivity|]. cbn [map ents_total fold_right]. rewrite live_bytes_cons, IH, (ent_val_bsz ρ e He). reflexivity.
Qed.

Lemma MR_grant_exists (ρ : valuation) (am : amodel) (m : Model) (nZ : Z) :
  MR ρ am m -> 0 < nZ ->
  4096 + (live_bytes (segments_reserved segs) + ents_total (am_maps am))
  + Z.of_nat (length (segments_reserved segs) + length (am_maps am)) * (nZ + 4096) + nZ <= leval ρ (am_atop am) ->
  exists a, null_ok m nZ a.
Proof.
  intros HM Hn Hb. pose proof (alloc_top_lt (m_vmmaps m)) as Ht. change two_pow_64 with two64 in Ht.
  destruct (grant_exists (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) nZ (alloc_top (m_vmmaps m)) Hn ltac:(lia)) as [a (A1 & A2 & A3 & A4)].
  - rewrite live_bytes_app, length_app, (mr_res ρ am m HM), (mr_maps ρ am m HM), length_map, (MR_live ρ _ (mr_ents ρ am m HM)), (mr_atop ρ am m HM). exact Hb.
  - exists a. repeat split; assumption.
Qed.

Lemma lit_ent_val (ρ : valuation) (c n : Z) (b : bool) : 0 <= c < two64 -> 0 <= n < two64 ->
  bas (ent_val ρ (AE (c, []) n b)) = c /\ bsz (ent_val ρ (AE (c, []) n b)) = n.
Proof.
  intros Hc Hn. unfold bas, bsz, ent_val, leval. cbn [ae_base ae_size fst snd teval]. rewrite Z.add_0_r, !u_Z_to_bv by assumption. split; reflexivity.
Qed.

Lemma MR_free_span (ρ : valuation) (am : amodel) (m : Model) (a : word) (nZ : Z) :
  MR ρ am m -> 0 < nZ -> bv_unsigned a + nZ < two64 -> region_free (vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  am_shadow am = true -> bv_unsigned a + nZ <= sh_lo \/ sh_hi <= bv_unsigned a.
Proof.
  intros HM Hn Hw Hf Hs. destruct (mr_shadow ρ am m HM Hs) as (S1 & S2 & S3).
  pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with two64 in Ha.
  assert (Hu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u_Z_to_bv; lia).
  pose proof (proj1 (region_free_disj _ _ _) Hf _ (MR_ent_in ρ am m _ HM S1)) as D1.
  pose proof (proj1 (region_free_disj _ _ _) Hf _ (MR_ent_in ρ am m _ HM S2)) as D2.
  pose proof (proj1 (region_free_disj _ _ _) Hf _ (MR_ent_in ρ am m _ HM S3)) as D3.
  unfold iv_disj in D1, D2, D3. rewrite Hu in D1, D2, D3. unfold ls_ent, gap_ent, hs_ent in D1, D2, D3.
  destruct (lit_ent_val ρ 2147446784 268435456 false ltac:(unfold two64; lia) ltac:(unfold two64; lia)) as [E1 E2].
  destruct (lit_ent_val ρ 2415882240 2199023255552 true ltac:(unfold two64; lia) ltac:(unfold two64; lia)) as [E3 E4].
  destruct (lit_ent_val ρ 2201439137792 15392894357504 false ltac:(unfold two64; lia) ltac:(unfold two64; lia)) as [E5 E6].
  rewrite E1, E2 in D1. rewrite E3, E4 in D2. rewrite E5, E6 in D3. unfold sh_lo, sh_hi. lia.
Qed.

Lemma MR_shadow_on (ρ : valuation) (am : amodel) (m : Model) :
  MR ρ am m -> In ls_ent (am_maps am) -> In gap_ent (am_maps am) -> In hs_ent (am_maps am) ->
  (forall e, In e (am_maps am) -> var_ent e = false) -> MR ρ (am_shadow_on am) m.
Proof.
  intros [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21] S1 S2 S3 Hlit.
  constructor; unfold am_shadow_on; cbn [am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd]; try assumption.
  - intros _. repeat split; assumption.
  - intros _ e0 He0 Hv. rewrite (Hlit e0 He0) in Hv. discriminate Hv.
Qed.

End MRdef.
