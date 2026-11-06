(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HttpRepA AWKit HObjA.
Import ListNotations.
Open Scope Z_scope.

Section IDS.
  Context {K : Type}.
  Notation BLK := (block K).
  Definition idj (A B : list BLK) : Prop := forall a b, In a A -> In b B -> blk_id a <> blk_id b.
  #[using="Type"] Lemma idj_sym : forall A B, idj A B -> idj B A.
  Proof. intros A B H a b Ha Hb E. exact (H b a Hb Ha (eq_sym E)). Qed.
  #[using="Type"] Lemma idj_app_l : forall A B C, idj (A ++ B) C <-> idj A C /\ idj B C.
  Proof.
    intros A B C. unfold idj. split.
    - intros H. split; intros a b Ha Hb; apply H; auto; apply in_or_app; auto.
    - intros [H1 H2] a b Ha Hb. apply in_app_or in Ha. destruct Ha; [eapply H1| eapply H2]; eauto.
  Qed.
  #[using="Type"] Lemma idj_app_r : forall A B C, idj A (B ++ C) <-> idj A B /\ idj A C.
  Proof.
    intros A B C. split.
    - intros H. split; apply idj_sym; apply idj_sym in H; apply idj_app_l in H; tauto.
    - intros [H1 H2]. apply idj_sym. apply idj_app_l. split; apply idj_sym; assumption.
  Qed.
  #[using="Type"] Lemma idj_cons_l : forall a B C, idj (a :: B) C <-> idj [a] C /\ idj B C.
  Proof. intros a B C. change (a :: B) with ([a] ++ B). apply idj_app_l. Qed.
  #[using="Type"] Lemma idj_cons_r : forall A b C, idj A (b :: C) <-> idj A [b] /\ idj A C.
  Proof. intros A b C. change (b :: C) with ([b] ++ C). apply idj_app_r. Qed.
  #[using="Type"] Lemma idj_sub_l : forall A A' B, idj A B -> (forall x, In x A' -> In x A) -> idj A' B.
  Proof. intros A A' B H S a b Ha Hb. apply H; auto. Qed.
  #[using="Type"] Lemma idj_sub_r : forall A B B', idj A B -> (forall x, In x B' -> In x B) -> idj A B'.
  Proof. intros A B B' H S a b Ha Hb. apply H; auto. Qed.

  #[using="Type"] Lemma nd_app : forall (A B : list BLK), NoDup (map blk_id (A ++ B)) <-> NoDup (map blk_id A) /\ idj A B /\ NoDup (map blk_id B).
  Proof.
    intros A B. rewrite map_app, list.NoDup_app. unfold idj. split.
    - intros (N1 & D & N2). split; [exact N1|]. split; [| exact N2].
      intros a b Ha Hb E. apply (D (blk_id a)); [apply base.list_elem_of_In; apply in_map; exact Ha|].
      rewrite E. apply base.list_elem_of_In. apply in_map. exact Hb.
    - intros (N1 & D & N2). split; [exact N1|]. split; [| exact N2].
      intros x Hx Hx2. apply base.list_elem_of_In in Hx. apply base.list_elem_of_In in Hx2.
      apply in_map_iff in Hx. destruct Hx as (a & <- & Ha). apply in_map_iff in Hx2. destruct Hx2 as (b & E & Hb).
      exact (D a b Ha Hb (eq_sym E)).
  Qed.
  #[using="Type"] Lemma nd_cons : forall (a : BLK) B, NoDup (map blk_id (a :: B)) <-> idj [a] B /\ NoDup (map blk_id B).
  Proof.
    intros a B. change (a :: B) with ([a] ++ B). rewrite nd_app. split; [tauto|]. intros [H1 H2]. split; [| tauto].
    cbn. constructor; [| constructor]. intros X. apply base.list_elem_of_In in X. exact X.
  Qed.
  #[using="Type"] Lemma idj_neq : forall A B a b, idj A B -> In a A -> In b B -> a <> b.
  Proof. intros A B a b H Ha Hb ->. exact (H b b Ha Hb eq_refl). Qed.
End IDS.

Section W.
Context {HC : HasCeiling}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Notation K := (am_K FI AI).
  Notation BLK := (block K).
  Notation BL := (list (block K)).
  Notation bsub := (bsub FI AI).
  Notation dlseg := (dlseg FI AI).
  Notation flseg := (flseg FI AI).
  Notation hdro_mem := (hdro_mem FI AI).
  Notation hdrs_mem := (hdrs_mem FI AI).
  Notation hblocks := (hblocks FI AI).
  Notation hdrs_blocks := (hdrs_blocks FI AI).

  Definition bkeep (OB : BL) (m m' : mem) : Prop :=
    forall b A cs, In b OB -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b ->
      rw_cells asegs m A cs -> rw_cells asegs m' A cs.

  #[using="Type"] Lemma bkeep_sub : forall OB OB' m m', bkeep OB m m' -> bsub OB' OB -> bkeep OB' m m'.
  Proof. intros OB OB' m m' H S b A cs Hb. apply H. apply S. exact Hb. Qed.
  #[using="Type"] Lemma bkeep_trans : forall OB m1 m2 m3, bkeep OB m1 m2 -> bkeep OB m2 m3 -> bkeep OB m1 m3.
  Proof. intros OB m1 m2 m3 H1 H2 b A cs Hb L1 L2 C. eapply H2; eauto. Qed.

  #[using="Type"] Lemma bkeep_of_apres : forall OB (LBK : BL) q m m', apres FI AI LBK q m m' -> bsub OB LBK -> bkeep OB m m'.
  Proof.
    intros OB LBK q m m' AP S b A cs Hb L1 L2 C. eapply (apres_rw_cells FI AI); [exact AP| exact C|].
    eapply (aclient_range_block FI AI); [apply S; exact Hb| exact L1| exact L2].
  Qed.

  #[using="Type"] Lemma bkeep_of_apx : forall OB W (LBK : BL) q m m',
    apx FI AI W LBK q m m' -> bsub OB LBK -> (forall b, In b OB -> disjoint_from W (blk_addr b) (blk_size b)) -> bkeep OB m m'.
  Proof.
    intros OB W LBK q m m' AP S D b A cs Hb L1 L2 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| |].
    - eapply (aclient_range_block FI AI); [apply S; exact Hb| exact L1| exact L2].
    - eapply disjoint_from_sub; [exact (D b Hb)| exact L1| exact L2].
  Qed.

  #[using="Type"] Lemma bkeep_of_munch : forall OB W m m',
    munch W m m' -> wmono asegs m m' -> (forall b, In b OB -> disjoint_from W (blk_addr b) (blk_size b)) -> bkeep OB m m'.
  Proof.
    intros OB W m m' MU WM D b A cs Hb L1 L2 C. eapply rw_cells_transport; [exact C| exact MU| exact WM|].
    eapply disjoint_from_sub; [exact (D b Hb)| exact L1| exact L2].
  Qed.

  #[using="Type"] Lemma dlseg_bkeep : forall ns OB m m' pv TAIL,
    dlseg m ns pv TAIL -> bkeep OB m m' -> (forall b it, In (b, it) ns -> In b OB) -> dlseg m' ns pv TAIL.
  Proof.
    induction ns as [|[b it] ns IH]; intros OB m m' pv TAIL DL BK SUB; cbn [HObjA.dlseg] in *; [exact I|].
    destruct DL as (SZ & NZ & NT & ITR & NC & DL'). repeat (split; [assumption|]). split.
    - eapply (BK b); [eapply SUB; left; reflexivity| lia| unfold node_cells; cbn [cells_size csize Nat.add]; lia| exact NC].
    - eapply IH; [exact DL'| exact BK|]. intros b0 it0 H. eapply SUB. right. exact H.
  Qed.

  #[using="Type"] Lemma flseg_bkeep : forall FB OB m m' N, flseg m FB N -> bkeep OB m m' -> bsub FB OB -> flseg m' FB N.
  Proof.
    induction FB as [|b FB IH]; intros OB m m' N FL BK SUB; cbn [HObjA.flseg] in *; [exact FL|].
    destruct FL as (NZ & Eb & nx & j1 & j2 & NC & FL'). split; [exact NZ|]. split; [exact Eb|]. exists nx, j1, j2. split.
    - eapply (BK b); [apply SUB; left; reflexivity| rewrite Eb; cbn; lia| rewrite Eb; cbn; lia| exact NC].
    - eapply IH; [exact FL'| exact BK|]. intros b0 H. apply SUB. right. exact H.
  Qed.

  #[using="Type"] Lemma hdro_mem_bkeep : forall OB m m' h,
    hdro_mem m h -> bkeep OB m m' -> bsub (hblocks h) OB -> 0 <= vcap FI AI h -> 0 <= ncap FI AI h -> hdro_mem m' h.
  Proof.
    intros OB m m' h ([pad HCc] & VC & [vbs [VB VN]] & NC & [nbs [NB NN]]) BK SUB VP NP.
    pose proof (SUB _ (or_introl eq_refl)) as B1. pose proof (SUB _ (or_intror (or_introl eq_refl))) as B2.
    pose proof (SUB _ (or_intror (or_intror (or_introl eq_refl)))) as B3.
    split; [| split; [| split; [| split]]].
    - exists pad. eapply (BK _ _ _ B1); [cbn; lia| cbn; lia| exact HCc].
    - eapply (BK _ _ _ B1); [cbn; lia| unfold mbuf_cells; cbn; lia| exact VC].
    - exists vbs. split; [| exact VN]. eapply (BK _ _ _ B2); [cbn; lia| cbn; lia| exact VB].
    - eapply (BK _ _ _ B1); [cbn; lia| unfold mbuf_cells; cbn; lia| exact NC].
    - exists nbs. split; [| exact NN]. eapply (BK _ _ _ B3); [cbn; lia| cbn; lia| exact NB].
  Qed.

  #[using="Type"] Lemma hdrs_mem_bkeep : forall hs OB m m', hdrs_mem m hs -> bkeep OB m m' -> bsub (hdrs_blocks hs) OB -> hdrs_mem m' hs.
  Proof.
    induction hs as [|h hs IH]; intros OB m m' HS BK SUB; cbn [HObjA.hdrs_mem] in *; [exact I|].
    destruct HS as (HM & HP0 & HS'). change (bsub (hblocks h ++ hdrs_blocks hs) OB) in SUB. apply (bsub_app FI AI) in SUB. destruct SUB as [S1 S2].
    split; [| split; [exact HP0|]].
    - eapply hdro_mem_bkeep; [exact HM| exact BK| exact S1| unfold hdro_pure in HP0; lia| unfold hdro_pure in HP0; lia].
    - eapply IH; [exact HS'| exact BK| exact S2].
  Qed.

  Definition cw_iv (LB : BL) (st : fsstate FI) (iv : Z * Z) : Prop :=
    fst iv <= snd iv /\
    ( alloc_ceiling <= fst iv
      \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
      \/ lb (fs_live FI st) (fst iv) (snd iv - fst iv) ).

  #[using="Type"] Lemma cw_frames : forall s (LB : BL) st m m' W,
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m -> munch W m m' -> wmono asegs m m' ->
    Forall (cw_iv LB st) W ->
    RHEAP_A FI AI s LB m' /\ RFAKE FI st m' /\ asan_env asegs m'.
  Proof.
    intros s LB st m m' W HR RF AE MU WM HW.
    pose proof (fsb_ok FI) as (F1 & F2 & _ & _). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    split; [| split].
    - eapply (am_heap_frame FI AI); [exact HR| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
      intros iv [LE [H|[(b & Hb & H1 & H2)|H]]].
      + left. exact H.
      + right; right; left. exists b. split; [exact Hb| lia].
      + destruct (lb_geom FI st m _ _ RF H) as [G1 G2]. do 3 right; left. lia.
    - eapply (rfake_frame FI); [exact RF| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
      intros iv [LE [H|[(b & Hb & H1 & H2)|H]]].
      + apply (rf_ok_stack FI). exact H.
      + eapply (rf_ok_blk FI AI s LB m st b); [exact HR| exact Hb| exact H1| exact H2| exact LE].
      + right; left. exact H.
    - eapply asan_env_frame; [exact AE| exact MU| exact WM|]. unfold env_safe. eapply Forall_impl; [| exact HW].
      intros iv [LE [H|[(b & Hb & H1 & H2)|H]]]; left.
      + lia.
      + destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & _ & _ & B4 & _). lia.
      + destruct (lb_geom FI st m _ _ RF H) as [G1 G2]. lia.
  Qed.

  #[using="Type"] Lemma cw_iv_mlocNB : forall (LB : BL) q st X n lo' hi',
    mlocNB FI AI q st X n -> alloc_ceiling <= q -> X <= lo' -> lo' <= hi' -> hi' <= X + n -> cw_iv LB st (lo', hi').
  Proof.
    intros LB q st X n lo' hi' [H|H] HQ H1 H2 H3; split; cbn [fst snd]; [exact H2| left; lia| exact H2|].
    right; right. destruct H as (g & Hg & G1 & G2). exists g. split; [exact Hg|]. lia.
  Qed.
  #[using="Type"] Lemma cw_iv_blk : forall (LB : BL) st (b : BLK) lo' hi',
    In b LB -> blk_addr b <= lo' -> lo' <= hi' -> hi' <= blk_addr b + blk_size b -> cw_iv LB st (lo', hi').
  Proof. intros LB st b lo' hi' Hb H1 H2 H3. split; [exact H2|]. right; left. exists b. cbn [fst snd]. split; [exact Hb| lia]. Qed.
  #[using="Type"] Lemma cw_iv_stack : forall (LB : BL) st lo' hi', alloc_ceiling <= lo' -> lo' <= hi' -> cw_iv LB st (lo', hi').
  Proof. intros LB st lo' hi' H1 H2. split; [exact H2| left; exact H1]. Qed.

  #[using="Type"] Lemma mlocNB_sub : forall q st X n X' n', mlocNB FI AI q st X n -> X <= X' -> X' + n' <= X + n -> mlocNB FI AI q st X' n'.
  Proof.
    intros q st X n X' n' [H|(g & Hg & G1 & G2)] H1 H2; [left; lia| right]. exists g. split; [exact Hg| lia].
  Qed.

  #[using="Type"] Lemma shw_band_eq : forall m m' A n lo hi,
    shw m A n -> (forall a, lo <= a < hi -> forall v, mrd asegs m (wa a) = Some v -> mrd asegs m' (wa a) = Some v) ->
    0 <= lo -> hi <= 2^64 -> lo mod 8 = 0 -> hi mod 8 = 0 -> lo <= sh A -> (0 < n -> sh (A + n - 1) < hi) -> shw m' A n.
  Proof.
    intros m m' A n lo hi (AC & RD & WK) EQ L0 H64 LAL HAL H1 H2. split; [| split; [| exact WK]].
    - intros a Ha. destruct (AC a Ha) as (k & (B0 & B1 & BB) & Hk). exists k. split; [| exact Hk].
      split; [exact B0|]. split; [exact B1|]. intros i Hi.
      cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [nth_error]. apply EQ; [| exact (BB 0%nat ltac:(cbn [length]; lia))]. rewrite Z.add_0_r.
      assert (sh A <= sh a) by (apply sh_mono; lia). assert (sh a <= sh (A + n - 1)) by (apply sh_mono; lia). specialize (H2 ltac:(lia)). lia.
    - intros Hn a Ha. destruct (RD Hn a Ha) as (v & Hv). exists v. apply EQ; [| exact Hv].
      specialize (H2 Hn). Z.div_mod_to_equations. lia.
  Qed.

  #[using="AMS"] Lemma mlocNB_shw_apx : forall W (LB : BL) q st m m' X n,
    mlocNB FI AI q st X n -> shw m X n -> apx FI AI W LB q m m' -> app_ivs W -> RFAKE FI st m -> alloc_ceiling <= q ->
    shw m' X n.
  Proof.
    intros W LB q st m m' X n ML SW AP AW RF HQ.
    pose proof (shw_win_ok _ _ _ SW) as [Hn _].
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (am_stack_ok FI AI) as (_ & _ & TK3 & _).
    assert (EQ : forall a, shband a -> aclient FI AI LB q a -> forall v, mrd asegs m (wa a) = Some v -> mrd asegs m' (wa a) = Some v).
    { intros a Hb Hc v Hv. exact (gkeep_mrd _ _ _ v (proj1 (AP a (shband_range a Hb) Hc (app_ivs_outside W a AW Hb))) Hv). }
    destruct ML as [H|H].
    - pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
      assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
      eapply (shw_band_eq m m' X n (sh alloc_ceiling - sh alloc_ceiling mod 8) 0x10007fff8000 SW).
      + intros a Ha. apply EQ; [unfold shband, SH_LO, SH_HI; lia|]. right; left. exists (sh alloc_ceiling - sh alloc_ceiling mod 8), 0x10007fff8000. split; [| lia].
        apply AMS. unfold a0_static. split; [unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia|]. repeat right. lia.
      + lia.
      + lia.
      + clear. Z.div_mod_to_equations. lia.
      + reflexivity.
      + assert (sh alloc_ceiling <= sh X) by (apply sh_mono; lia). lia.
      + intros Hp. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
    - destruct (lb_geom FI st m X n RF H) as [G1 G2]. pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4).
      eapply (shw_band_eq m m' X n (sh (FSB FI)) (sh (FSB FI) + A0_FS_SHSIZE) SW).
      + intros a Ha. apply EQ; [unfold shband, SH_LO, SH_HI; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia|]. do 4 right; left. exact Ha.
      + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
      + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
      + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
      + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
      + apply sh_mono. lia.
      + intros Hp. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  Qed.

  Definition fsw_iv (iv : Z * Z) : Prop :=
    app_iv iv \/ (sh (FSB FI) <= fst iv /\ snd iv <= sh (FSB FI) + A0_FS_SHSIZE).

  #[using="Type"] Lemma fsw_outside : forall W a, Forall fsw_iv W -> shband a ->
    (a < sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= a) -> outside W a.
  Proof.
    induction W as [|[lo' hi'] W IH]; intros a HW Hb Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    destruct H1 as [H1|H1]; cbn [fst snd] in H1.
    - unfold app_iv, SH_HI in H1. unfold shband, SH_LO, SH_HI in Hb. cbn [fst snd] in H1. lia.
    - lia.
  Qed.

  #[using="Type"] Lemma shw_frame_fs : forall W m m' X n,
    shw m X n -> munch W m m' -> Forall fsw_iv W -> (X + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= X) -> shw m' X n.
  Proof.
    intros W m m' X n (AC & RD & WK) MU HW OUT.
    pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4).
    assert (S8 : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
    assert (FD : FSB FI = 8 * (FSB FI / 8)) by (clear - F4; Z.div_mod_to_equations; lia).
    split; [| split; [| exact WK]].
    - intros a Ha. destruct (AC a Ha) as (k & (B0 & B1 & BB) & Hk). exists k. split; [| exact Hk].
      split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (BB i Hi).
      cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r.
      pose proof (win_ok_sh_band X n a WK Ha) as SB.
      apply (mrd_munch W m m' (sh a) MU); [| exact (shband_range _ SB)].
      apply fsw_outside; [exact HW| exact SB|]. unfold sh, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    - intros Hn a Ha. destruct (RD Hn a Ha) as (v & Hv). exists v. rewrite <- Hv.
      pose proof (win_ok_words_band X n a WK Hn Ha) as SB.
      apply (mrd_munch W m m' a MU); [| exact (shband_range _ SB)].
      apply fsw_outside; [exact HW| exact SB|]. unfold sh, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
  Qed.
End W.
