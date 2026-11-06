(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA.
Import ListNotations.
Open Scope Z_scope.

Section F.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation K := (am_K FI AI).
Local Notation BL := (list (block K)).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.

Definition fclient (LB : BL) (q : Z) (st : fsstate FI) (a : Z) : Prop :=
  q <= a
  \/ (exists lo hi, am_static FI AI lo hi /\ lo <= a < hi)
  \/ in_block LB a
  \/ (exists b, In b LB /\ sh (blk_addr b) <= a < sh (blk_addr b) + Z.of_nat (length (block_shadow (blk_size b))))
  \/ (exists g, In g (fs_live FI st) /\ in_pieces g a).

Definition apxF (W : list ivl) (LB : BL) (q : Z) (st : fsstate FI) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> fclient LB q st a -> outside W a ->
    gkeep m m' (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

#[using="Type"] Lemma apxF_refl : forall W LB q st m, apxF W LB q st m m.
Proof. intros W LB q st m a _ _ _; split; [apply gkeep_refl| auto]. Qed.
#[using="Type"] Lemma apxF_trans : forall W LB q st m1 m2 m3, apxF W LB q st m1 m2 -> apxF W LB q st m2 m3 -> apxF W LB q st m1 m3.
Proof.
  intros W LB q st m1 m2 m3 H1 H2 a Ha Hc Ho. destruct (H1 a Ha Hc Ho) as [E1 W1]. destruct (H2 a Ha Hc Ho) as [E2 W2].
  split; [exact (gkeep_trans _ _ _ _ E1 E2)| auto].
Qed.

#[using="Type"] Lemma apxF_mrd : forall W LB q st m m' a b, apxF W LB q st m m' -> 0 <= a < 2^64 -> fclient LB q st a -> outside W a ->
  mrd asegs m (wa a) = Some b -> mrd asegs m' (wa a) = Some b.
Proof. intros W LB q st m m' a b AP Ha Hc Ho Hr. exact (gkeep_mrd m m' (wa a) b (proj1 (AP a Ha Hc Ho)) Hr). Qed.

#[using="Type"] Lemma fclient_weaken : forall (LB LB' : BL) q q' st st' a,
  fclient LB' q' st' a -> q <= q' -> (forall b, In b LB' -> In b LB) ->
  (forall g, In g (fs_live FI st') -> In g (fs_live FI st)) -> fclient LB q st a.
Proof.
  intros LB LB' q q' st st' a Hc HS HL HF.
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|(g & Hg & Hp)]]]].
  - left; lia.
  - right; left; exact Hc.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - do 3 right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - do 4 right. exists g. split; [apply HF; exact Hg| exact Hp].
Qed.

#[using="Type"] Lemma apxF_weaken : forall W W' (LB LB' : BL) q q' st st' m m',
  apxF W LB q st m m' -> sub_fp W W' -> q <= q' -> (forall b, In b LB' -> In b LB) ->
  (forall g, In g (fs_live FI st') -> In g (fs_live FI st)) -> apxF W' LB' q' st' m m'.
Proof.
  intros W W' LB LB' q q' st st' m m' H HW HS HL HF a Ha Hc Ho. apply H; [exact Ha| | apply HW; exact Ho].
  eapply fclient_weaken; eauto.
Qed.
#[using="Type"] Lemma apxF_live_eq : forall W LB q st st' m m', apxF W LB q st m m' -> fs_live FI st' = fs_live FI st -> apxF W LB q st' m m'.
Proof.
  intros W LB q st st' m m' H E. eapply apxF_weaken; [exact H| intros x Hx; exact Hx| lia| auto| intros g Hg; rewrite <- E; exact Hg].
Qed.

#[using="Type"] Lemma fclient_aclient : forall (LB : BL) q st mx a, RFAKE FI st mx -> fclient LB q st a -> aclient FI AI LB q a.
Proof.
  intros LB q st mx a RF [Hc|[Hc|[Hc|[Hc|(g & Hg & Hp)]]]].
  - left; exact Hc.
  - right; left; exact Hc.
  - right; right; left; exact Hc.
  - do 5 right; exact Hc.
  - destruct (live_pieces_inside FI st mx g a RF Hg Hp) as [X|X]; [do 3 right; left; exact X| do 4 right; left; exact X].
Qed.

#[using="Type"] Lemma apxF_of_apx : forall W (LB LB' : BL) q q' st st' mx m m',
  apx FI AI W LB' q' m m' -> RFAKE FI st' mx -> q' <= q -> (forall b, In b LB -> In b LB') ->
  (forall g, In g (fs_live FI st) -> In g (fs_live FI st')) -> apxF W LB q st m m'.
Proof.
  intros W LB LB' q q' st st' mx m m' H RF HS HL HF a Ha Hc Ho. apply H; [exact Ha| | exact Ho].
  eapply (fclient_aclient LB' q' st' mx a RF). eapply fclient_weaken; eauto.
Qed.

#[using="ASL"] Lemma fclient_not_stack : forall s LB0 (LB : BL) m0 q st mx a,
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> RFAKE FI st mx -> fclient LB q st a -> alloc_ceiling <= a -> q <= a.
Proof.
  intros s LB0 LB m0 q st mx a HR HSUB RF Hc Ha.
  eapply (aclient_not_stack FI AI ASL s LB0 LB m0 q a HR HSUB); [| exact Ha]. eapply fclient_aclient; eauto.
Qed.

#[using="ASL"] Lemma fclient_fs_live : forall s LB0 (LB : BL) m0 q st a,
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> alloc_ceiling <= q ->
  fclient LB q st a ->
  (FSB FI <= a < FSB FI + A0_FS_SIZE) \/ (sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE) ->
  exists g, In g (fs_live FI st) /\ in_pieces g a.
Proof.
  intros s LB0 LB m0 q st a HR HSUB HQ Hc HFS.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (fsb_ok FI) as (F1 & F2 & _ & F4 & F5).
  assert (SHE : sh (FSB FI) + A0_FS_SHSIZE = sh (FSB FI + A0_FS_SIZE)) by (unfold sh, SHADOW_OFF; clear - F4; Z.div_mod_to_equations; lia).
  pose proof (fs_shadow_below_band FI) as FSG. rewrite SHE in FSG.
  destruct Hc as [Hc|[(lo & hi & Hst & Hr)|[(b & Hb & Hr)|[(b & Hb & Hr)|Hc]]]]; [exfalso| exfalso| exfalso| exfalso| exact Hc].
  - destruct HFS as [X|X]; [lia|]. rewrite SHE in X. unfold sh, SHADOW_OFF in X. Z.div_mod_to_equations. lia.
  - apply ASL in Hst. destruct Hst as [LE Hst]. rewrite SHE in HFS. unfold sh, SHADOW_OFF in HFS, Hst.
    destruct Hst as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]; destruct HFS as [X|X]; destruct F5 as [F5|F5]; Z.div_mod_to_equations; lia.
  - destruct (am_block_range FI AI s LB0 m0 b HR (HSUB b Hb)) as (B0 & B1 & B2 & B3 & B4 & B5 & B6). unfold in_block in *.
    destruct HFS as [X|X]; [lia|]. rewrite SHE in X. unfold sh, SHADOW_OFF in X. destruct F5 as [F5|F5]; Z.div_mod_to_equations; lia.
  - destruct (am_block_range FI AI s LB0 m0 b HR (HSUB b Hb)) as (B0 & B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (block_shadow_length (blk_size b) B2) as BL8. rewrite SHE in HFS. unfold sh, SHADOW_OFF in HFS, Hr.
    destruct HFS as [X|X]; destruct F5 as [F5|F5]; destruct B5 as [B5|B5]; destruct B6 as [B6|B6]; Z.div_mod_to_equations; lia.
Qed.

#[using="ASL"] Lemma apxF_of_munch_fkeep : forall s LB0 (LB : BL) m0 mx q lo st W m m',
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> RFAKE FI st mx -> alloc_ceiling <= lo -> lo <= q ->
  munch ((lo, q) :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W st m m' ->
  apxF W LB q st m m'.
Proof.
  intros s LB0 LB m0 mx q lo st W m m' HR HSUB RF CLO LQ MU WM FK a Ha Hc Ho.
  split; [| intros Hw; apply WM; exact Hw].
  destruct (Z_lt_le_dec a q) as [AQ|AQ].
  - assert (NS : ~ (lo <= a < q)).
    { intros Hr. pose proof (fclient_not_stack s LB0 LB m0 q st mx a HR HSUB RF Hc ltac:(lia)). lia. }
    destruct (Z_le_dec (FSB FI) a) as [L1|L1]; [destruct (Z_lt_le_dec a (FSB FI + A0_FS_SIZE)) as [L2|L2]|].
    + apply FK; [exact Ha| | exact Ho]. apply (fclient_fs_live s LB0 LB m0 q st a HR HSUB ltac:(lia) Hc); left; lia.
    + destruct (Z_le_dec (sh (FSB FI)) a) as [L3|L3]; [destruct (Z_lt_le_dec a (sh (FSB FI) + A0_FS_SHSIZE)) as [L4|L4]|].
      * apply FK; [exact Ha| | exact Ho]. apply (fclient_fs_live s LB0 LB m0 q st a HR HSUB ltac:(lia) Hc); right; lia.
      * apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. unfold wa. apply E.
        cbn [outside]. split; [exact NS|]. split; [lia|]. split; [lia| exact Ho].
      * apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. unfold wa. apply E.
        cbn [outside]. split; [exact NS|]. split; [lia|]. split; [lia| exact Ho].
    + pose proof (fsb_ok FI) as (F1 & F2 & _ & F4 & F5).
      destruct (Z_le_dec (sh (FSB FI)) a) as [L3|L3]; [destruct (Z_lt_le_dec a (sh (FSB FI) + A0_FS_SHSIZE)) as [L4|L4]|].
      * apply FK; [exact Ha| | exact Ho]. apply (fclient_fs_live s LB0 LB m0 q st a HR HSUB ltac:(lia) Hc); right; lia.
      * apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. unfold wa. apply E.
        cbn [outside]. split; [exact NS|]. split; [lia|]. split; [lia| exact Ho].
      * apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. unfold wa. apply E.
        cbn [outside]. split; [exact NS|]. split; [lia|]. split; [lia| exact Ho].
  -
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (F1 & F2 & _ & F4 & F5).
    apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. unfold wa. apply E.
    cbn [outside]. split; [lia|]. split; [lia|]. split; [| exact Ho].
    unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

#[using="ASL"] Lemma apxF_of_munch : forall s LB0 (LB : BL) m0 mx q st W W0 m m',
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> RFAKE FI st mx ->
  munch W0 m m' -> wmono asegs m m' ->
  Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= q)
                    \/ (forall a, fst iv <= a < snd iv -> ~ fclient LB q st a)
                    \/ inside W (fst iv) (snd iv - fst iv)) W0 ->
  apxF W LB q st m m'.
Proof.
  intros s LB0 LB m0 mx q st W W0 m m' HR HSUB RF MU WM OK a Ha Hc Ho. split; [| intros Hw; apply WM; exact Hw].
  apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia.
  unfold wa. apply E. apply outside_of_forall.
  eapply Forall_impl; [| exact OK]. cbn. intros [lo' hi'] [[H1 H2]|[H3|H4]]; cbn in *.
  - intros Hr. pose proof (fclient_not_stack s LB0 LB m0 q st mx a HR HSUB RF Hc ltac:(lia)). lia.
  - intros Hr. exact (H3 a Hr Hc).
  - intros Hr. apply (inside_not_outside W lo' (hi' - lo') a H4); [lia| exact Ho].
Qed.

#[using="ASL"] Lemma fs_apart_not_fclient : forall s LB0 (LB : BL) m0 q st lo' hi',
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> alloc_ceiling <= q ->
  ((FSB FI <= lo' /\ hi' <= FSB FI + A0_FS_SIZE) \/ (sh (FSB FI) <= lo' /\ hi' <= sh (FSB FI) + A0_FS_SHSIZE)) ->
  Forall (fun g => (hi' <= ff_addr g \/ ff_addr g + ff_size g <= lo')
                   /\ (hi' <= sh (ff_addr g) \/ sh (ff_addr g) + ff_shsize g <= lo')
                   /\ (hi' <= ff_flag g \/ ff_flag g + 1 <= lo')) (fs_live FI st) ->
  forall a, lo' <= a < hi' -> ~ fclient LB q st a.
Proof.
  intros s LB0 LB m0 q st lo' hi' HR HSUB HQ HFS AP a Hr Hc.
  destruct (fclient_fs_live s LB0 LB m0 q st a HR HSUB HQ Hc ltac:(lia)) as (g & Hg & Hp).
  rewrite Forall_forall in AP. specialize (AP g Hg). unfold in_pieces in Hp. lia.
Qed.

#[using="ASL"] Lemma new_frame_not_fclient : forall s LB0 (LB : BL) m0 q st k mx F SF FL,
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> alloc_ceiling <= q ->
  RFAKE FI st mx -> 0 <= k <= 10 -> F = fs_F FI st k -> SF = sh F -> FL = fs_FL FI st k ->
  forall a, ((F <= a < F + FB_of k) \/ (SF <= a < SF + SB_of k) \/ a = FL) -> ~ fclient LB q st a.
Proof.
  intros s LB0 LB m0 q st k mx F SF FL HR HSUB HQ RF Hk EF ESF EFL a HIN.
  assert (HIN' : (F <= a /\ a + 1 <= F + FB_of k) \/ (SF <= a /\ a + 1 <= SF + SB_of k) \/ (a = FL /\ 1 = 1)) by lia.
  pose proof (new_frame_fk FI st k mx F SF FL RF Hk EF ESF EFL [] a 1 HIN') as FKOK.
  unfold fk_ok in FKOK. cbn [fst snd inside] in FKOK.
  destruct (new_frame_facts FI st k mx F SF FL RF Hk EF ESF EFL) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  pose proof (fsb_ok FI) as (F1 & F2 & _ & F4 & F5).
  assert (SBF : SB_of k * 8 = FB_of k).
  { unfold SB_of, FB_of. destruct k as [|p|p]; try reflexivity; repeat (destruct p; try reflexivity). }
  assert (INFS : (FSB FI <= a /\ a + 1 <= FSB FI + A0_FS_SIZE) \/ (sh (FSB FI) <= a /\ a + 1 <= sh (FSB FI) + A0_FS_SHSIZE)).
  { subst SF. unfold sh, SHADOW_OFF in *. destruct HIN as [Y|[Y|Y]]; [left| right| left]; Z.div_mod_to_equations; lia. }
  destruct FKOK as [X|[X|X]]; [destruct X| exfalso; lia|].
  apply (fs_apart_not_fclient s LB0 LB m0 q st a (a + 1) HR HSUB HQ INFS X a). lia.
Qed.

#[using="ASL"] Lemma apxF_epilogue : forall s LB0 (LB : BL) m0 mx q lo st k F SF FL W m m',
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> RFAKE FI st mx -> alloc_ceiling <= lo -> lo <= q ->
  0 <= k <= 10 -> F = fs_F FI st k -> SF = sh F -> FL = fs_FL FI st k ->
  munch [(lo, q); (F, F + FB_of k); (SF, SF + SB_of k); (FL, FL + 1)] m m' -> wmono asegs m m' ->
  apxF W LB q st m m'.
Proof.
  intros s LB0 LB m0 mx q lo st k F SF FL W m m' HR HSUB RF CLO LQ Hk EF ESF EFL MU WM.
  eapply (apxF_of_munch s LB0 LB m0 mx q st W _ m m' HR HSUB RF MU WM).
  apply Forall_cons; [left; cbn [fst snd]; lia|].
  assert (HQ : alloc_ceiling <= q) by lia.
  apply Forall_cons; [right; left; cbn [fst snd]; intros a Ha; apply (new_frame_not_fclient s LB0 LB m0 q st k mx F SF FL HR HSUB HQ RF Hk EF ESF EFL a); left; lia|].
  apply Forall_cons; [right; left; cbn [fst snd]; intros a Ha; apply (new_frame_not_fclient s LB0 LB m0 q st k mx F SF FL HR HSUB HQ RF Hk EF ESF EFL a); right; left; lia|].
  apply Forall_cons; [right; left; cbn [fst snd]; intros a Ha; apply (new_frame_not_fclient s LB0 LB m0 q st k mx F SF FL HR HSUB HQ RF Hk EF ESF EFL a); right; right; lia|].
  apply Forall_nil.
Qed.

#[using="Type"] Lemma apxF_fkeep : forall W LB q st m m', apxF W LB q st m m' -> fkeep FI W st m m'.
Proof. intros W LB q st m m' H a Ha Hg Ho. apply (H a Ha); [do 4 right; exact Hg| exact Ho]. Qed.

Definition fclient_range (LB : BL) (q : Z) (st : fsstate FI) (A n : Z) : Prop := forall a, A <= a < A + n -> fclient LB q st a.
#[using="Type"] Lemma fclient_range_above : forall LB q st A n, q <= A -> fclient_range LB q st A n.
Proof. intros LB q st A n H a Ha. left. lia. Qed.
#[using="Type"] Lemma fclient_range_static : forall LB q st A n lo hi, am_static FI AI lo hi -> lo <= A -> A + n <= hi -> fclient_range LB q st A n.
Proof. intros LB q st A n lo hi H H1 H2 a Ha. right; left. exists lo, hi. split; [exact H| lia]. Qed.
#[using="Type"] Lemma fclient_range_block : forall (LB : BL) q st A n (b : block K),
  In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> fclient_range LB q st A n.
Proof. intros LB q st A n b Hb H1 H2 a Ha. right; right; left. exists b. split; [exact Hb| lia]. Qed.
#[using="Type"] Lemma fclient_range_lb : forall LB q st A n, lb (fs_live FI st) A n -> fclient_range LB q st A n.
Proof. intros LB q st A n (g & Hg & G1 & G2) a Ha. do 4 right. exists g. split; [exact Hg| left; lia]. Qed.
#[using="Type"] Lemma fclient_range_ls : forall LB q st A n, ls (fs_live FI st) A n -> fclient_range LB q st A n.
Proof. intros LB q st A n (g & Hg & G1 & G2) a Ha. do 4 right. exists g. split; [exact Hg| right; left; lia]. Qed.
#[using="Type"] Lemma fclient_range_lf : forall LB q st A, lf (fs_live FI st) A -> fclient_range LB q st A 1.
Proof. intros LB q st A (g & Hg & G1) a Ha. do 4 right. exists g. split; [exact Hg| right; right; lia]. Qed.

#[using="Type"] Lemma apxF_bytes_at : forall W LB q st m m' A bs,
  apxF W LB q st m m' -> bytes_at asegs m A bs -> fclient_range LB q st A (Z.of_nat (length bs)) ->
  disjoint_from W A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros W LB q st m m' A bs HP HB HR HD. pose proof HB as (H0 & H1 & _). apply (bytes_at_gkeep m m' A bs HB). intros i Hi.
  exact (proj1 (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia]))).
Qed.
#[using="Type"] Lemma apxF_wr_at : forall W LB q st m m' A n,
  apxF W LB q st m m' -> wr_at asegs m A n -> fclient_range LB q st A n -> disjoint_from W A n -> wr_at asegs m' A n.
Proof.
  intros W LB q st m m' A n HP (H0 & H1 & HW) HR HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia])) as [_ Wv].
  apply Wv. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma apxF_rw_cells : forall W LB q st m m' A cs,
  apxF W LB q st m m' -> rw_cells asegs m A cs -> fclient_range LB q st A (Z.of_nat (cells_size cs)) ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros W LB q st m m' A cs HP [[Hwf HB] HW] HR HD. split; [split; [exact Hwf|]|].
  - eapply apxF_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
  - eapply apxF_wr_at; eauto.
Qed.
End F.
