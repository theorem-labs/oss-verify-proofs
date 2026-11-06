(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot
  AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_alloc_iface A_live A_policy5 A_budget5 A_slack5 A_bundle A_benv5 A_balloc5 AF_fakestack_rep AF_place.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Definition kBatchPages : Z := 100000.   (* [comment removed for export] *)
Definition kGapDPad : Z := 15000.
Definition gapR (a : astate) : Z := 4096 * (160 * as_nprim_ever a + kBatchPages) - regions_bytes a.
Definition gapD (a : astate) : Z :=
  4096 * (as_ndepot_ins a + kGapDPad - 256 * zlen (as_node_blocks a) - 2050 * zlen (as_store_blocks a)).
(* [comment removed for export] *)
Definition gapP (a : astate) : Z := if as_ptr_committed a =? 0 then kPtrArrayCommit else 0.
Lemma gapP_nonneg : forall a, 0 <= gapP a.
Proof. intros a. unfold gapP, kPtrArrayCommit. destruct (as_ptr_committed a =? 0); lia. Qed.

Lemma gapR_eq : forall a a', as_nprim_ever a' = as_nprim_ever a -> regions_bytes a' = regions_bytes a -> gapR a' = gapR a.
Proof. intros a a' H1 H2. unfold gapR. rewrite H1, H2. reflexivity. Qed.
Lemma gapD_eq : forall a a', as_ndepot_ins a' = as_ndepot_ins a -> as_node_blocks a' = as_node_blocks a -> as_store_blocks a' = as_store_blocks a ->
  gapD a' = gapD a.
Proof. intros a a' H1 H2 H3. unfold gapD. rewrite H1, H2, H3. reflexivity. Qed.
Lemma gapP_eq : forall a a', as_ptr_committed a' = as_ptr_committed a -> gapP a' = gapP a.
Proof. intros a a' H. unfold gapP. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Theorem budget_headroom2 : forall A0 EB0 E s LB,
  Forall (fun iv => fst iv <= snd iv) A0 -> 0 <= EB0 ->
  AWf E [] [] (aps_alloc s) -> AQbound (aps_alloc s) -> depot_inv E (aps_alloc s) -> binv (aps_alloc s) ->
  blocks_match LB (aps_alloc s) -> BUDGET s LB ->
  zlen (ae_keys0 E) <= 1000 -> 0 <= ae_frames0 E <= 4096 ->
  A_policy5.aEB EB0 s + 4096 * A_policy5.aNz A0 s + 4096 * aps_credit s
    + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) + 4096 <= BUDGET_STATIC A0 EB0
  /\ 0 <= gapR (aps_alloc s) /\ 0 <= gapD (aps_alloc s).
Proof.
  intros A0 EB0 E s LB A0ok EB0nn WF QB DI BI BM (B0 & B1 & B2 & B3) K0 [F00 F0].
  pose proof (M1 E _ WF QB BI) as X1. pose proof (M2 E _ WF QB BI) as X2.
  pose proof (depot_growth_amortised E [] [] _ WF DI K0 F0) as X3.
  pose proof (DEP_live LB _ BM) as X5.
  destruct DI as (D1 & D2 & D3 & D4 & D5 & D6).
  unfold ACC in B3. rewrite X5 in B3. unfold kInitialCredit in B3.
  unfold A_policy5.aEB, aEBa, A_policy5.aNz, aNza, a_eager_bytes, BUDGET_STATIC, gapR, gapD, gapP, kGapDPad.
  change (AsanBudget2.interiors_a (aps_alloc s)) with (interiors_bound (aps_alloc s)) in X1.
  unfold kInitialCredit, kDepotNodeBlockBytes, kPtrArrayCommit, kBatchPages, kStoreBlockFrames in *.
  pose proof (zlen_nonneg (as_store_blocks (aps_alloc s))) as ZS. pose proof (zlen_nonneg (as_node_blocks (aps_alloc s))) as ZN.
  pose proof (zlen_nonneg (as_residue (aps_alloc s))) as ZR. pose proof (A0_pages_nonneg A0 A0ok) as ZA.
  assert (DZ : 0 <= dep_live (aps_alloc s)) by (rewrite <- X5; apply DEP_nonneg).
  destruct (as_ptr_committed (aps_alloc s) =? 0); clear -X1 X2 X3 B0 B1 B2 B3 ZS ZN ZR ZA DZ EB0nn D2 D3 F0; lia.
Qed.

Section Rtok.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis HS_tot : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat.

#[local] Notation AHKc := (AHK StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aNzc := (A_bundle.aNz E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).

Ltac ahk_open H :=
  destruct H as (Hrep & Hwf & Hkern & Hkvm & Hres & Hqb & Hdi & Hbinv & Hbm & Hfs & Hicp & Hyst & Hlow & Hrt & Hso & Hkm & Hli & Hbud & Hmi & Henv & Hycl & Hss & Hcs).
Ltac cstat := try clear HR0_ok; try clear EB0_ok; try clear ENV_depot; try clear HS_tot.

(* [comment removed for export] *)
Definition RTOK (C C' : Z) (s : aps) (mo : Model) : Prop :=
  0 <= C /\ 0 <= gapR (aps_alloc s) /\ 0 <= gapD (aps_alloc s) /\ 0 <= C'
  /\ exists R R', ATOKc R R' s mo /\ 4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) <= 4096 * R /\ C' <= R'.

Lemma RTOK_intro : forall C C' s mo R R',
  ATOKc R R' s mo -> 0 <= C -> 0 <= gapR (aps_alloc s) -> 0 <= gapD (aps_alloc s) ->
  4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) <= 4096 * R -> 0 <= C' <= R' -> RTOK C C' s mo.
Proof.
  cstat. intros C C' s mo R R' T HC G1 G2 LE HC'. split; [exact HC|]. split; [exact G1|]. split; [exact G2|]. split; [lia|].
  exists R, R'. split; [exact T|]. split; [exact LE| lia].
Qed.

Lemma RTOK_elim : forall C C' s mo, RTOK C C' s mo ->
  exists R R', ATOKc R R' s mo /\ 0 <= C <= R /\ 0 <= C' <= R' /\ 0 <= gapR (aps_alloc s) /\ 0 <= gapD (aps_alloc s)
            /\ 4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) <= 4096 * R.
Proof.
  cstat. intros C C' s mo (HC & G1 & G2 & HC' & R & R' & T & LE & LE'). pose proof (gapP_nonneg (aps_alloc s)).
  exists R, R'. split; [exact T|]. split; [lia|]. split; [lia|]. split; [exact G1|]. split; [exact G2| exact LE].
Qed.

(* [comment removed for export] *)
Lemma RTOK_elim_roomR : forall C C' s mo L, RTOK C C' s mo -> L <= gapR (aps_alloc s) ->
  exists R R', ATOKc R R' s mo /\ 0 <= C <= R /\ 0 <= C' <= R' /\ L <= 4096 * R /\ 0 <= gapD (aps_alloc s) /\ 0 <= gapP (aps_alloc s)
            /\ 4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) <= 4096 * R.
Proof.
  cstat. intros C C' s mo L T HL. destruct (RTOK_elim C C' s mo T) as (R & R' & TK & HC & HC' & G1 & G2 & LE). pose proof (gapP_nonneg (aps_alloc s)).
  exists R, R'. split; [exact TK|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact LE].
Qed.
Lemma RTOK_elim_roomD : forall C C' s mo k, RTOK C C' s mo -> 4096 * k <= gapD (aps_alloc s) ->
  exists R R', ATOKc R R' s mo /\ 0 <= C <= R /\ 0 <= C' <= R' /\ k <= R /\ 0 <= gapR (aps_alloc s) /\ 0 <= gapP (aps_alloc s)
            /\ 4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) <= 4096 * R.
Proof.
  cstat. intros C C' s mo k T Hk. destruct (RTOK_elim C C' s mo T) as (R & R' & TK & HC & HC' & G1 & G2 & LE). pose proof (gapP_nonneg (aps_alloc s)).
  exists R, R'. split; [exact TK|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact LE].
Qed.
(* [comment removed for export] *)
Lemma RTOK_elim_roomP : forall C C' s mo, RTOK C C' s mo -> as_ptr_committed (aps_alloc s) = 0 ->
  exists R R', ATOKc R R' s mo /\ 0 <= C <= R /\ 0 <= C' <= R' /\ kPtrArrayCommit <= 4096 * R /\ 0 <= gapR (aps_alloc s) /\ 0 <= gapD (aps_alloc s)
            /\ 4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + kPtrArrayCommit <= 4096 * R.
Proof.
  cstat. intros C C' s mo T HP. destruct (RTOK_elim C C' s mo T) as (R & R' & TK & HC & HC' & G1 & G2 & LE). unfold gapP in LE. rewrite HP in LE. cbn [Z.eqb] in LE.
  exists R, R'. split; [exact TK|]. split; [lia|]. split; [lia|]. split; [unfold kPtrArrayCommit in *; lia|]. split; [lia|]. split; [lia| exact LE].
Qed.

(* [comment removed for export] *)
Theorem RTOK_open : forall s LB LF m mo, AHKc s LB LF m mo -> nbig LB <= 8000 -> RTOK (aps_credit s) OPSLACK s mo.
Proof.
  intros s LB LF m mo H NB.
  pose proof (ATOK_open _ _ _ _ _ _ _ _ HR0_ok EB0_ok ENV_depot HS_tot s LB LF m mo 0 H) as T0.
  pose proof H as H0. ahk_open H. destruct Hkm as (Kh & Kmi & Klim).
  assert (EE : aps_env s = E0) by (destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _); exact EE).
  pose proof Hwf as WF0. rewrite EE in WF0. pose proof Hdi as DI0. rewrite EE in DI0.
  destruct (budget_headroom2 (A0 E0 FSB0 HR0) EB0 E0 s LB (A0_ok E0 FSB0 HR0 HR0_ok) (proj1 EB0_ok) WF0 Hqb DI0 Hbinv Hbm Hbud (proj1 ENV_depot) (proj2 ENV_depot))
    as (BH & G1 & G2).
  pose proof (BUDGET_STATIC_ok E0 FSB0 HR0 EB0 HR0_ok EB0_ok) as BS.
  pose proof (gapP_nonneg (aps_alloc s)) as G3. pose proof (BUDGET_credit_nonneg s LB Hbud) as B0.
  destruct (T0 ltac:(clear -B0; lia) NB) as (K & _ & E & V & KV & P).
  set (G := gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s)) in *.
  apply (RTOK_intro _ _ _ _ (aps_credit s + (G + 4095) / 4096) OPSLACK).
  - split; [exact K|]. split; [| split; [exact E| split; [exact V| split; [exact KV| exact P]]]].
    split; [clear -B0 G1 G2 G3; subst G; Z.div_mod_to_equations; lia|].
    unfold OSL. rewrite Klim. change (A_bundle.aEB EB0 s) with (A_policy5.aEB EB0 s). change (A_bundle.aNz E0 FSB0 HR0 s) with (A_policy5.aNz (A0 E0 FSB0 HR0) s).
    clear -BH BS B0 G1 G2 G3. subst G. Z.div_mod_to_equations. lia.
  - exact B0.
  - exact G1.
  - exact G2.
  - clear -G1 G2 G3. subst G. Z.div_mod_to_equations. lia.
  - unfold OPSLACK. lia.
Qed.

Lemma RTOK_le : forall C C' D D' s mo, RTOK C C' s mo -> 0 <= D <= C -> 0 <= D' <= C' -> RTOK D D' s mo.
Proof. cstat. intros C C' D D' s mo (HC & G1 & G2 & HC' & R & R' & T & LE & LE') H H'. apply (RTOK_intro _ _ _ _ R R' T); lia. Qed.

Lemma RTOK_magree : forall C C' s mo mo', RTOK C C' s mo -> magree mo mo' -> KIA (aSc s) (aNc s) (aEBc s) mo' -> RTOK C C' s mo'.
Proof.
  cstat. intros C C' s mo mo' (HC & G1 & G2 & HC' & R & R' & T & LE & LE') Hag K. apply (RTOK_intro _ _ _ _ R R'); auto; try lia.
  eapply ATOK_magree; eauto.
Qed.

Lemma RTOK_aps : forall C C' s s' mo,
  RTOK C C' s mo -> aps_env s' = aps_env s -> aps_fsbase s' = aps_fsbase s -> aps_alloc s' = aps_alloc s -> RTOK C C' s' mo.
Proof.
  cstat. intros C C' s s' mo (HC & G1 & G2 & HC' & R & R' & T & LE & LE') E1 E2 E3. apply (RTOK_intro _ _ _ _ R R'); try (rewrite E3; assumption); auto; try lia.
  eapply ATOK_aps; eauto.
Qed.

(* [comment removed for export] *)
Lemma RTOK_same_fp_pay : forall C C' D s a a' mo,
  RTOK C C' (sA a s) mo -> same_fp a a' ->
  gapR a <= gapR a' -> gapD a <= gapD a' -> 0 <= D ->
  4096 * D + gapR a' + gapD a' <= 4096 * C + gapR a + gapD a ->
  RTOK D C' (sA a' s) mo.
Proof.
  cstat. intros C C' D s a a' mo (HC & G1 & G2 & HC' & R & R' & T & LE & LE') SF M1' M2' HD PAY. cbn [aps_alloc sA aps_set_alloc] in *.
  pose proof SF as (_ & _ & F3 & _). pose proof (gapP_eq a a' F3) as EP.
  apply (RTOK_intro _ _ _ _ R R'); cbn [aps_alloc sA aps_set_alloc]; [eapply ATOK_same_fp; eauto| lia| lia| lia| lia| lia].
Qed.
Lemma RTOK_same_fp : forall C C' s a a' mo,
  RTOK C C' (sA a s) mo -> same_fp a a' -> as_nprim_ever a' = as_nprim_ever a -> as_ndepot_ins a' = as_ndepot_ins a ->
  RTOK C C' (sA a' s) mo.
Proof.
  cstat. intros C C' s a a' mo T SF EN ED. pose proof SF as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (gapR_eq a a' EN F1) as ER. pose proof (gapD_eq a a' ED F5 F6) as EDp.
  pose proof (proj1 T) as HC. eapply (RTOK_same_fp_pay C C' C s a a' mo T SF); lia.
Qed.

(* [comment removed for export] *)
Lemma RTOK_step : forall C C' D D' s s' mo mo' (k g : Z),
  RTOK C C' s mo ->
  (forall R R', ATOKc R R' s mo -> 0 <= C <= R -> 0 <= C' <= R' ->
     4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) <= 4096 * R -> ATOKc (R - k) (R' - g) s' mo') ->
  0 <= D -> 0 <= gapR (aps_alloc s') -> 0 <= gapD (aps_alloc s') -> 0 <= D' -> D' + g <= C' ->
  4096 * D + gapR (aps_alloc s') + gapD (aps_alloc s') + gapP (aps_alloc s') + 4096 * k
    <= 4096 * C + gapR (aps_alloc s) + gapD (aps_alloc s) + gapP (aps_alloc s) ->
  RTOK D D' s' mo'.
Proof.
  cstat. intros C C' D D' s s' mo mo' k g T EV HD G1' G2' HD' HG FIT. destruct (RTOK_elim C C' s mo T) as (R & R' & TK & HC & HC' & G1 & G2 & LE).
  apply (RTOK_intro _ _ _ _ (R - k) (R' - g)); [apply EV; auto| exact HD| exact G1'| exact G2'| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma RTOK_ATOK : forall C C' s mo, RTOK C C' s mo -> exists R R', ATOKc R R' s mo /\ C <= R /\ C' <= R'.
Proof. cstat. intros C C' s mo T. destruct (RTOK_elim C C' s mo T) as (R & R' & TK & HC & HC' & _). exists R, R'. split; [exact TK| lia]. Qed.
End Rtok.
End RC__1.
