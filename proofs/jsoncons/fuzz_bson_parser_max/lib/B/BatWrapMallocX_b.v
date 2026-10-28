(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b BatCARSpec_b BatAlloc3Pure_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b
     BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b BatLift_b BatWrapPure_b BatWrapKit_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_cost_sum_app : forall l1 l2, art_cost_sum (l1 ++ l2) = art_cost_sum l1 + art_cost_sum l2.
Proof. induction l1 as [|e l IH]; intros l2; [reflexivity|]. cbn [app]. unfold art_cost_sum in *. cbn [fold_right]. rewrite IH. lia. Qed.

Lemma art_ca_pre_free_len : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  Z.of_nat (length (cl_free (art_ca_pre c cl))) <= Z.of_nat (length (cl_free cl)) + 8192.
Proof.
  intros c cl Hc OK. pose proof (art_new_le c cl Hc OK) as Hnew. unfold art_ca_pre. destruct (cl_cache cl); [|lia].
  rewrite art_cls_refill_eq. cbn [art_cls_take cl_free]. rewrite length_firstn. unfold art_cls_pre_take.
  destruct (art_cls_needs_populate c cl); [|lia]. cbn [art_cls_populate cl_free]. rewrite length_app, art_carved_length. lia.
Qed.

Lemma art_removelast_le : forall (l : list Z), (length (removelast l) <= length l)%nat.
Proof. induction l as [|a l IH]; [cbn; lia|]. cbn [removelast]. destruct l; [cbn; lia|]. cbn [length] in *. lia. Qed.

(* [comment removed for export] *)
Lemma art_pre_pop_len : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  let cl' := art_cls_pop (art_ca_pre c cl) in
  Z.of_nat (length (cl_free cl')) + Z.of_nat (length (cl_cache cl')) <= Z.of_nat (length (cl_free cl)) + Z.of_nat (length (cl_cache cl))
  \/ Z.of_nat (length (cl_free cl')) + Z.of_nat (length (cl_cache cl')) <= 8 + 8192.
Proof.
  intros c cl Hc OK cl'. subst cl'. pose proof (art_new_le c cl Hc OK) as Hnew. destruct (art_refill_need c Hc) as (_ & Hn8).
  unfold art_cls_pop. cbn [cl_free cl_cache].
  match goal with |- context [length (removelast ?l)] => pose proof (art_removelast_le l) as RL end. revert RL.
  unfold art_ca_pre. destruct (cl_cache cl) as [|z l] eqn:E.
  - rewrite art_cls_refill_eq. cbn [art_cls_take cl_free cl_cache]. rewrite length_firstn, length_skipn. unfold art_cls_pre_take.
    destruct (art_cls_needs_populate c cl) eqn:NP.
    + intros RL. right. cbn [art_cls_populate cl_free] in *. rewrite length_app, art_carved_length in *. unfold art_cls_needs_populate in NP. apply Nat.ltb_lt in NP. lia.
    + intros RL. left. cbn [length]. lia.
  - intros RL. left. rewrite E in *. cbn [length] in *. lia.
Qed.

Lemma art_nq_nonneg : forall bs, 0 <= art_nq bs.
Proof. induction bs as [|b r IH]; [cbn; lia|]. unfold art_nq in *. cbn [fold_right]. lia. Qed.

Section Credit.
Variable FSG : Type.

(* [comment removed for export] *)
#[using="Type"] Lemma art_wmx_credit : forall BUDGET rn (G : art_gs FSG) LB cr c w u n (kb : nat) kk cost,
  1 <= c <= 30 -> art_cls_ok c (g_cls FSG G c) -> art_credit_ok FSG BUDGET rn G LB cr -> g_depot FSG G = Datatypes.S kb ->
  3 <= kk <= fst cr -> 2 ^ 20 <= cost <= snd cr ->
  art_credit_ok FSG BUDGET rn (art_gs_malloc G (rn_spb rn) c w u n kb) ((u, n) :: LB) (fst cr - kk, snd cr - cost).
Proof.
  intros BUDGET rn G LB cr c w u n kb kk cost Hc OK (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) Edep Hkk Hcost.
  pose proof (art_ca_cost (rn_spb rn) c (g_cls FSG G c) Hc OK) as Hev.
  pose proof (art_nq_nonneg (g_qt FSG G ++ g_qg FSG G)) as Hnq.
  unfold art_credit_ok, art_nret in *. cbn [art_gs_malloc g_log g_sec g_depot g_cls g_qt g_qg fst snd length] in *.
  rewrite Nat2Z.inj_succ.
  split; [lia|]. split; [lia|]. split; [rewrite art_cost_sum_app; lia|]. split; [rewrite art_live_ca_events; lia|]. split; [lia|].
  split; [rewrite Edep in C6; lia|]. split; [lia|].
  intros c0 Hc0. destruct (C8 c0 Hc0) as (D1 & D2). destruct (Z.eqb_spec c0 c) as [->|Ne]; [|split; lia].
  pose proof (art_pre_pop_len c (g_cls FSG G c) Hc OK) as HL. cbv zeta in HL.
  split.
  - cbn [art_cls_pop cl_mu]. destruct (art_ca_pre_mu_cases c (g_cls FSG G c)) as [(E & _)|(_ & _ & E)]; rewrite E; lia.
  - destruct HL as [HL|HL]; lia.
Qed.
End Credit.

Lemma art_page_base_bounds : forall w : word, U (page_base w) <= U w < U (page_base w) + 4096.
Proof.
  intros w. unfold page_base, page_base_of, page_size. pose proof (u64_range w) as R.
  pose proof (Z.div_mod (U w) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (U w) 4096 ltac:(lia)) as Rm.
  assert (0 <= U w / 4096) by (apply Z.div_pos; lia).
  rewrite art_u_lit by lia. lia.
Qed.

Lemma art_page_allowedb_incl : forall A A' p, incl A A' -> page_allowedb A p = true -> page_allowedb A' p = true.
Proof.
  intros A A' p INC H. unfold page_allowedb in *. apply existsb_exists in H. destruct H as (iv & Hin & Hiv).
  apply existsb_exists. exists iv. split; [apply INC; exact Hin|exact Hiv].
Qed.

Section Lazy.
Variable FSG : Type.

#[using="Type"] Lemma art_wmx_lazy : forall rn (G : art_gs FSG) A lazy A' lazy' c w u n (kb : nat),
  art_lazy_ok FSG rn G A lazy -> incl A A' ->
  (forall x : word, mkH lazy' A' x = true -> mkH lazy A x = true) ->
  (forall wd, In wd A' -> In wd A) ->
  (forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) ->
  (forall x : word, let cl' := art_cls_pop (art_ca_pre c (g_cls FSG G c)) in
     (rn_spb rn + c * 2 ^ 32 <= U x < rn_spb rn + c * 2 ^ 32 + cl_mu cl'
      \/ rn_spb rn + c * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + c * 2 ^ 32 + 3758096384 + cl_mfa cl') -> mkH lazy' A' x = false) ->
  art_lazy_ok FSG rn (art_gs_malloc G (rn_spb rn) c w u n kb) A' lazy'.
Proof.
  intros rn G A lazy A' lazy' c w u n kb (L1 & L2 & L3 & L4) INC B2 B4 B5 VIS.
  split; [|split; [|split]].
  - intros x Hlz. destruct (page_allowedb A' (page_base x)) eqn:EA.
    + unfold page_allowedb in EA. apply existsb_exists in EA. destruct EA as (iv & Hin & Hiv). apply andb_prop in Hiv as [I1 I2].
      apply Z.leb_le in I1. apply Z.leb_le in I2. unfold page_size in I2. pose proof (art_page_base_bounds x) as PB.
      destruct (L2 iv (B4 iv Hin)) as [Z|[Z|NL]]; [left; lia|right; left; lia|]. exfalso. pose proof (B5 x Hlz) as E0. rewrite (NL x ltac:(lia)) in E0. discriminate E0.
    + assert (Hh : mkH lazy' A' x = true) by (unfold mkH; rewrite Hlz, EA; reflexivity).
      pose proof (B2 x Hh) as Hh0. unfold mkH in Hh0. apply andb_prop in Hh0 as [Hl0 _].
      destruct (L1 x Hl0) as [Z|[Z|[Z NC]]]; [left; exact Z|right; left; exact Z|]. right; right. split; [exact Z|].
      intros [RI|[(c0 & Hc0 & Zc)|P]]; apply NC.
      * left. exact RI.
      * cbn [art_gs_malloc g_cls] in Zc. destruct (Z.eqb_spec c0 c) as [->|Ne].
        -- exfalso. rewrite (VIS x Zc) in Hh. discriminate Hh.
        -- right; left. exists c0. split; [exact Hc0|exact Zc].
      * right; right. exact P.
  - intros wd Hwd. destruct (L2 wd (B4 wd Hwd)) as [Z|[Z|NL]]; [left; exact Z|right; left; exact Z|right; right].
    intros x Hx. destruct (page_in_ranges (page_base x) lazy') eqn:E; [|reflexivity]. pose proof (B5 x E) as E0. rewrite (NL x Hx) in E0. discriminate E0.
  - intros x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (L3 x Hx).
  - intros x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (L4 x Hx).
Qed.
End Lazy.

(* [comment removed for export] *)
Section Eager.
Variable FSG : Type.
#[using="Type"] Lemma art_wmx_eager : forall rn (G' : art_gs FSG) LB A lazy A' lazy' u n,
  art_eager_ok LB A lazy -> A_wf A' -> art_lazy_ok FSG rn G' A' lazy' ->
  (forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) ->
  0x10007fff8000 <= rn_spb rn -> apart (rn_blk rn) (2 ^ 23) (rn_spb rn) (2 ^ 37 + 4096) ->
  rn_spb rn <= u -> u + n <= rn_spb rn + 2 ^ 37 -> (forall a, u <= a < u + n -> art_committed FSG rn G' a) ->
  art_eager_ok ((u, n) :: LB) A' lazy'.
Proof.
  intros rn G' LB A lazy A' lazy' u n (AW & EG) AW' (L1 & _) B5 Hspb Abs Hu1 Hu2 CM. split; [exact AW'|].
  intros b x [<-|Hb] Hx; cbn [fst snd] in Hx; destruct (page_in_ranges (page_base x) lazy') eqn:E; try reflexivity; exfalso.
  - destruct (L1 x E) as [Z|[Z|[Z NC]]]; [lia|unfold apart in Abs; lia|]. apply NC. apply CM. exact Hx.
  - pose proof (B5 x E) as E0. rewrite (EG b x Hb Hx) in E0. discriminate E0.
Qed.
End Eager.

