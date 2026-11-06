(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma e8_of_16 : forall A, A mod 16 = 0 -> A = 8 * (A / 8).
Proof. intros A H. Z.div_mod_to_equations. lia. Qed.
Lemma e8_of_8 : forall A, A mod 8 = 0 -> A = 8 * (A / 8).
Proof. intros A H. Z.div_mod_to_equations. lia. Qed.
Lemma e16_of_16 : forall A, A mod 16 = 0 -> A = 16 * (A / 16).
Proof. intros A H. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma fp_of_le : forall (W : list SX.awin) E (RNG : footprint),
  Forall (fun w => rng RNG (fst (SX.awin_den E w)) (snd (SX.awin_den E w) - fst (SX.awin_den E w))) W ->
  fp_le (SX.fp_of (Some W) E) RNG.
Proof.
  intros W E RNG HW b j (w & Hw & H1 & H2).
  destruct (proj1 (Forall_forall _ _) HW w Hw) as (_ & _ & R). apply R; lia.
Qed.

Lemma aw_genuine_of_rng : forall (W : list SX.awin) E (RNG : footprint),
  Forall (fun w => rng RNG (fst (SX.awin_den E w)) (snd (SX.awin_den E w) - fst (SX.awin_den E w))) W ->
  SX.aw_genuine E (Some W).
Proof.
  intros W E RNG HW w Hw. destruct (proj1 (Forall_forall _ _) HW w Hw) as (R1 & R2 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma uchain_fp_step : forall m top pc spc fp s00 ra0 k tr0,
  spc < fp -> fp < top - 16 -> fp mod 8 = 0 -> (0 < k)%nat ->
  bytes_at asegs m (fp - 16) (le8 (Z_to_bv 64 s00)) -> bytes_at asegs m (fp - 8) (le8 (Z_to_bv 64 ra0)) ->
  4096 <= ra0 < 2^64 -> 0 <= s00 < 2^64 -> ra0 <> pc ->
  uchain m top pc fp s00 (Nat.pred k) tr0 ->
  uchain m top pc spc fp k (ra0 :: tr0).
Proof.
  intros m top pc spc fp s00 ra0 k tr0 H1 H2 H3 H4 B1 B2 Hra Hs0 Hne HC.
  replace (ra0 :: tr0) with ((if ra0 =? pc then [] else [ra0]) ++ tr0)
    by (destruct (Z.eqb_spec ra0 pc); [lia| reflexivity]).
  eapply uc_step; eauto.
  destruct (Z.eqb_spec ra0 pc); [lia| exact HC].
Qed.

(* [comment removed for export] *)
Section PresW.
  Variable CI : list (Z * Z).

  Lemma aheap_pres_W_bytes_at : forall LB SP W m m' A bs,
    aheap_pres_W CI LB SP W m m' -> bytes_at asegs m A bs -> aclient_range CI LB SP A (Z.of_nat (length bs)) ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> outside W a) -> bytes_at asegs m' A bs.
  Proof.
    intros LB SP W m m' A bs HP (H0 & H1 & HB) HR HO. split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia]) ltac:(apply HO; lia)) as [E _].
    rewrite E. reflexivity.
  Qed.

  Lemma aheap_pres_W_wr_at : forall LB SP W m m' A n,
    aheap_pres_W CI LB SP W m m' -> wr_at asegs m A n -> aclient_range CI LB SP A n ->
    (forall a, A <= a < A + n -> outside W a) -> wr_at asegs m' A n.
  Proof.
    intros LB SP W m m' A n HP (H0 & H1 & HW) HR HO. split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia]) ltac:(apply HO; lia)) as [_ WV].
    apply WV. apply HW. exact Hi.
  Qed.

  Lemma aheap_pres_W_rw_cells : forall LB SP W m m' A cs,
    aheap_pres_W CI LB SP W m m' -> rw_cells asegs m A cs -> aclient_range CI LB SP A (Z.of_nat (cells_size cs)) ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) -> rw_cells asegs m' A cs.
  Proof.
    intros LB SP W m m' A cs HP [[Hwf HB] HW] HR HO. split; [split; [exact Hwf|]|].
    - eapply aheap_pres_W_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
    - eapply aheap_pres_W_wr_at; eauto.
  Qed.

  Lemma aheap_pres_W_stk : forall LB SP W m m' lo hi,
    aheap_pres_W CI LB SP W m m' -> stk asegs m lo hi -> SP <= lo -> hi <= 2^47 ->
    (forall a, lo <= a < hi -> outside W a) -> stk asegs m' lo hi.
  Proof.
    intros LB SP W m m' lo hi HP ST HS HH HO. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia) (HO i Hi)) as [E W']. destruct (HW i Hi) as [W0 [b Hb]].
    split; [apply W', W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma aheap_pres_W_weaken : forall LB LB' SP SP' W W' m m',
    aheap_pres_W CI LB SP W m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) ->
    (forall a, outside W' a -> outside W a) -> aheap_pres_W CI LB' SP' W' m m'.
  Proof.
    intros LB LB' SP SP' W W' m m' H HS HL HW a Ha Hc Ho. apply H; [exact Ha| | apply HW; exact Ho].
    destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - left; lia.
    - right; left; exact Hc.
    - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
    - right; right; right. exists a'. split; [|reflexivity].
      destruct Ha' as [X|[X|(c & A & n & Hin & X)]]; [left; lia| right; left; exact X| right; right].
      exists c, A, n. split; [apply HL; exact Hin| exact X].
  Qed.

  Lemma aheap_pres_W_of_munch : forall LB SP W W' m m', munch W' m m' -> wmono asegs m m' ->
    (forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> outside W a -> outside W' a) -> aheap_pres_W CI LB SP W m m'.
  Proof.
    intros LB SP W W' m m' MU WM HW a Ha Hc Hx. split.
    - apply MU. unfold wa. rewrite unsigned_lit by lia. apply HW; assumption.
    - intros Hv. apply WM. exact Hv.
  Qed.
End PresW.
End CANSEC.
