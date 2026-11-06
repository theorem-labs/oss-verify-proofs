(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr Agree SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HApxF HttpRepA AWKit HObjA HObjK HObjF.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_snocA : forall m a bs b,
  bytes_at asegs m a bs -> mrd asegs m (wa (a + Z.of_nat (length bs))) = Some b -> a + Z.of_nat (length bs) + 1 <= 2^64 ->
  bytes_at asegs m a (bs ++ [b]).
Proof.
  intros m a bs b (H0 & H1 & HB) RD HI. split; [exact H0|]. rewrite length_app. cbn [length]. split; [lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i (length bs)).
  - rewrite nth_error_app1 by lia. apply HB. lia.
  - assert (i = length bs) by lia. subst i. rewrite nth_error_app2, Nat.sub_diag by lia. cbn. exact RD.
Qed.
Lemma bytes_at_extendA : forall k m a bs,
  bytes_at asegs m a bs ->
  (forall x, a + Z.of_nat (length bs) <= x < a + Z.of_nat (length bs) + Z.of_nat k -> exists v, mrd asegs m (wa x) = Some v) ->
  a + Z.of_nat (length bs) + Z.of_nat k <= 2^64 ->
  exists sl, bytes_at asegs m a (bs ++ sl) /\ length sl = k.
Proof.
  induction k as [|k IH]; intros m a bs B RD HI.
  - exists []. rewrite app_nil_r. split; [exact B| reflexivity].
  - destruct (RD (a + Z.of_nat (length bs)) ltac:(lia)) as [v Hv].
    pose proof (bytes_at_snocA m a bs v B Hv ltac:(lia)) as B1.
    destruct (IH m a (bs ++ [v]) B1) as (sl & B2 & L2).
    + intros x Hx. apply RD. rewrite length_app in Hx. cbn [length] in Hx. lia.
    + rewrite length_app. cbn [length]. lia.
    + exists (v :: sl). rewrite <- app_assoc in B2. cbn [app] in B2. split; [exact B2| cbn; lia].
Qed.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

#[using="Type"] Lemma block_slackA : forall s (LB : BL) m (b : BLK) bs,
  RHEAP_A FI AI s LB m -> In b LB -> bytes_at asegs m (blk_addr b) bs -> Z.of_nat (length bs) = blk_size b ->
  exists sl kE, bytes_at asegs m (blk_addr b + blk_size b) sl /\ Z.of_nat (length sl) <= 7
                /\ blk_addr b + blk_size b + Z.of_nat (length sl) = 8 * kE.
Proof.
  intros s LB m b bs HR HIN B L.
  destruct (am_block_range FI AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (RU : blk_addr b + blk_size b <= round_up8 (blk_addr b + blk_size b) <= blk_addr b + blk_size b + 7) by (unfold round_up8; Z.div_mod_to_equations; lia).
  destruct (bytes_at_extendA (Z.to_nat (round_up8 (blk_addr b + blk_size b) - (blk_addr b + blk_size b))) m (blk_addr b) bs B) as (sl & B2 & L2).
  - intros x Hx. eapply (am_block_slack FI AI); [exact HR| exact HIN| lia].
  - lia.
  - apply bytes_at_app in B2. destruct B2 as [_ B2]. rewrite L in B2.
    exists sl, ((blk_addr b + blk_size b + 7) / 8). split; [exact B2|]. split; [lia|].
    rewrite L2. unfold round_up8 in *. Z.div_mod_to_equations. lia.
Qed.

#[using="AMS"] Lemma stack_shadow_client : forall (LB : BL) q lo' a,
  sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> lo' <= a < 0x10007fff8000 -> aclient FI AI LB q a.
Proof.
  intros LB q lo' a H1 H2. right; left. exists lo', 0x10007fff8000. split; [| lia].
  apply AMS. unfold a0_static. split; [lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
Qed.
#[using="AMS"] Lemma shz_apx : forall W (LB : BL) q m m' lo' hi',
  shz m lo' hi' -> apx FI AI W LB q m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shz m' lo' hi'.
Proof.
  intros W LB q m m' lo' hi' Z AP H1 H2 OUT a Ha.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(lia) (stack_shadow_client LB q lo' a H1 ltac:(lia)) (OUT a Ha))) (Z a Ha)).
Qed.
#[using="AMS"] Lemma shr_apx : forall W (LB : BL) q m m' lo' hi',
  shr m lo' hi' -> apx FI AI W LB q m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shr m' lo' hi'.
Proof.
  intros W LB q m m' lo' hi' Z AP H1 H2 OUT a Ha. destruct (Z a Ha) as [v Hv]. exists v.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) (stack_shadow_client LB q lo' a H1 ltac:(lia)) (OUT a Ha))) Hv).
Qed.

#[using="Type"] Lemma apx_stk : forall W (LB : BL) q m m' lo' hi',
  apx FI AI W LB q m m' -> stk asegs m lo' hi' -> aclient_range FI AI LB q lo' (hi' - lo') -> disjoint_from W lo' (hi' - lo') ->
  stk asegs m' lo' hi'.
Proof.
  intros W LB q m m' lo' hi' AP ST HR HD.
  eapply (stk_gagree (fun a => aclient FI AI LB q a /\ outside W a)); [intros a Ha [Hc Ho]; exact (AP a Ha Hc Ho)| exact ST|].
  intros a Ha. split; [apply HR; lia| eapply disjoint_outside; [exact HD| lia]].
Qed.

#[using="Type"] Lemma shw_apxF_lb : forall W (LB : BL) q st m m' X n,
  shw m X n -> apxF FI AI W LB q st m m' -> RFAKE FI st m -> lb (fs_live FI st) X n ->
  (forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside W a) -> shw m' X n.
Proof.
  intros W LB q st m m' X n SW AP RF HL OUT.
  eapply (shw_fkeep FI W st m m' X n SW); [exact (apxF_fkeep FI AI W LB q st m m' AP)| exact RF| exact HL| exact OUT].
Qed.
#[using="AMS"] Lemma stack_shadow_fclient : forall (LB : BL) q st lo' a,
  sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> lo' <= a < 0x10007fff8000 -> fclient FI AI LB q st a.
Proof.
  intros LB q st lo' a H1 H2. right; left. exists lo', 0x10007fff8000. split; [| lia].
  apply AMS. unfold a0_static. split; [lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
Qed.
#[using="AMS"] Lemma shz_apxF : forall W (LB : BL) q st m m' lo' hi',
  shz m lo' hi' -> apxF FI AI W LB q st m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shz m' lo' hi'.
Proof.
  intros W LB q st m m' lo' hi' Z AP H1 H2 OUT a Ha.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(lia) (stack_shadow_fclient LB q st lo' a H1 ltac:(lia)) (OUT a Ha))) (Z a Ha)).
Qed.
#[using="AMS"] Lemma shr_apxF : forall W (LB : BL) q st m m' lo' hi',
  shr m lo' hi' -> apxF FI AI W LB q st m m' -> sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> hi' <= 0x10007fff8000 ->
  (forall a, lo' <= a < hi' -> outside W a) -> shr m' lo' hi'.
Proof.
  intros W LB q st m m' lo' hi' Z AP H1 H2 OUT a Ha. destruct (Z a Ha) as [v Hv]. exists v.
  assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
  exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) (stack_shadow_fclient LB q st lo' a H1 ltac:(lia)) (OUT a Ha))) Hv).
Qed.

#[using="Type"] Lemma rw_cells_nil0 : forall m, rw_cells asegs m 0 [CB 0 []].
Proof.
  intros m. split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.
End W.
