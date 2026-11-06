(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRuns ArtBridge EatInitCache EatPopulate1 EatCls EatClsGfa2 EatCARSpec EatFxBatch3 EatSecRSpec EatWrapPure EatInvMallocPure EarInv EarInvMalloc EarInvMallocL EarInvFreePure EarWrapMallocX EarWrapMallocLX EarCreditQ EarCreditC EarCredit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition art_cl_maps (cl : art_cls) : Z := cl_mu cl + cl_mfa cl.
Lemma art_primsum_eq : forall cls, art_primsum cls = fold_right (fun c z => art_cl_maps (cls c) + z) 0 (map Z.of_nat (seq 1 30)).
Proof. intros. unfold art_primsum, art_cl_maps. reflexivity. Qed.
Lemma art_sum_le : forall (g : Z -> Z) (B : Z) (l : list Z), (forall x, In x l -> g x <= B) -> fold_right (fun c z => g c + z) 0 l <= B * Z.of_nat (length l).
Proof.
  intros g B l. induction l as [|x r IH]; intros H; [cbn [fold_right length]; lia|]. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
  specialize (IH (fun y Hy => H y (or_intror Hy))). specialize (H x (or_introl eq_refl)). lia.
Qed.
Lemma art_sum_upd : forall (g : Z -> Z) (c v : Z) (l : list Z), List.NoDup l -> In c l ->
  fold_right (fun x z => (if x =? c then v else g x) + z) 0 l = fold_right (fun x z => g x + z) 0 l + v - g c.
Proof.
  intros g c v l ND. induction ND as [|x r Hx ND IH]; intros Hin; [destruct Hin|]. cbn [fold_right].
  destruct Hin as [->|Hin].
  - rewrite Z.eqb_refl.
    assert (E : fold_right (fun x z => (if x =? c then v else g x) + z) 0 r = fold_right (fun x z => g x + z) 0 r).
    { clear IH ND. induction r as [|y r' IHr]; [reflexivity|]. cbn [fold_right].
      destruct (Z.eqb_spec y c) as [->|Ne]; [exfalso; apply Hx; left; reflexivity|]. rewrite IHr; [reflexivity|]. intros H. apply Hx. right. exact H. }
    rewrite E. lia.
  - destruct (Z.eqb_spec x c) as [->|Ne]; [contradiction|]. rewrite (IH Hin). lia.
Qed.
Lemma art_cls130_in : forall c, 1 <= c <= 30 <-> In c (map Z.of_nat (seq 1 30)).
Proof.
  intros c. rewrite in_map_iff. split.
  - intros Hc. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
Qed.
Lemma art_cls130_nodup : List.NoDup (map Z.of_nat (seq 1 30)).
Proof. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup]. intros x y _ _ E. lia. Qed.

Lemma art_primsum_le : forall cls, (forall c, 1 <= c <= 30 -> art_cls_ok c (cls c)) -> art_primsum cls <= PRIMCAP.
Proof.
  intros cls OK. rewrite art_primsum_eq.
  pose proof (art_sum_le (fun c => art_cl_maps (cls c)) (2 ^ 32) (map Z.of_nat (seq 1 30))) as S.
  rewrite length_map, length_seq in S. unfold PRIMCAP. change (Z.of_nat 30) with 30 in S. rewrite (Z.mul_comm (2 ^ 32) 30) in S. apply S.
  intros c Hc. apply art_cls130_in in Hc. destruct (OK c Hc) as (_ & _ & _ & _ & _ & Hmu & _ & (_ & Hmfa) & _). unfold art_cl_maps. lia.
Qed.
Lemma art_fold_ext : forall (f g : Z -> Z -> Z) (l : list Z) a, (forall x z, f x z = g x z) -> fold_right f a l = fold_right g a l.
Proof. intros f g l a H. induction l as [|x r IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. apply H. Qed.
Lemma art_primsum_upd : forall cls c cl', 1 <= c <= 30 ->
  art_primsum (fun c0 => if c0 =? c then cl' else cls c0) = art_primsum cls + art_cl_maps cl' - art_cl_maps (cls c).
Proof.
  intros cls c cl' Hc. rewrite !art_primsum_eq.
  rewrite <- (art_sum_upd (fun x => art_cl_maps (cls x)) c (art_cl_maps cl') _ art_cls130_nodup (proj1 (art_cls130_in c) Hc)).
  apply art_fold_ext. intros x z. destruct (x =? c); reflexivity.
Qed.

Lemma art_ca_events_cost : forall spb c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  art_cost_sum (art_ca_events spb c cl) = art_cl_maps (art_cls_pop (art_ca_pre c cl)) - art_cl_maps cl.
Proof.
  intros spb c cl Hc OK. unfold art_cl_maps, art_cls_pop. cbn [cl_mu cl_mfa].
  unfold art_ca_events, art_ca_pre, art_refill_events. destruct (cl_cache cl); [|cbn; lia].
  rewrite art_cls_refill_eq. cbn [art_cls_take cl_mu cl_mfa]. unfold art_cls_pre_take.
  destruct (art_cls_needs_populate c cl); [|cbn; lia].
  cbn [art_cls_populate cl_mu cl_mfa].
  unfold art_cls_mfa'. destruct (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <=? cl_mfa cl) eqn:E; unfold art_cost_sum; cbn [fold_right art_cost]; lia.
Qed.
Lemma art_cost_sec_app : forall l1 l2, art_cost_sec (l1 ++ l2) = art_cost_sec l1 + art_cost_sec l2.
Proof. induction l1 as [|e l IH]; intros l2; [reflexivity|]. cbn [app]. unfold art_cost_sec in *. cbn [fold_right]. rewrite IH. lia. Qed.
Lemma art_cost_sec_ca : forall spb c cl, art_cost_sec (art_ca_events spb c cl) = 0.
Proof.
  intros spb c cl. unfold art_ca_events, art_refill_events. destruct (cl_cache cl); [|reflexivity].
  destruct (art_cls_needs_populate c cl); [|reflexivity].
  match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Lemma art_cost_sec_nonneg : forall log, (forall len r, In (AMmapNull len r) log -> 0 <= len) -> 0 <= art_cost_sec log.
Proof.
  induction log as [|e l IH]; intros H; [cbn; lia|]. unfold art_cost_sec in *. cbn [fold_right].
  specialize (IH (fun len r Hin => H len r (or_intror Hin))).
  destruct e as [a len|len r|a len|a len|a len]; try lia.
  pose proof (H len r (or_introl eq_refl)). assert (0 <= len / 8) by (apply Z.div_pos; lia). lia.
Qed.

Section T.
Variable FSG : Type.
Variable BUDGET : Z.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (cr : credit).
Hypothesis CRED : art_credit_ok FSG BUDGET rn G LB cr.
Hypothesis CLSOK : forall c, 1 <= c <= 30 -> art_cls_ok c (g_cls FSG G c).

Lemma art_cr_budget_ca : art_cost_sum (g_log FSG G) + 2 ^ 19 <= BUDGET.
Proof.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & _). pose proof (art_primsum_le (g_cls FSG G) CLSOK) as P.
  change (2 ^ 20) with 1048576 in C5. change (2 ^ 19) with 524288. destruct (g_sec_committed FSG G); lia.
Qed.

Lemma art_cr_depot : 1 <= fst cr -> exists kb, g_depot FSG G = Datatypes.S kb.
Proof.
  intros H. destruct CRED as (irr & _ & _ & _ & _ & _ & _ & _ & _ & C9 & _).
  destruct (g_depot FSG G) as [|kb]; [exfalso; cbn in C9; lia | exists kb; reflexivity].
Qed.

Lemma art_cr_depot_lb : 1 <= Z.of_nat (length LB) -> exists kb, g_depot FSG G = Datatypes.S kb.
Proof.
  intros H. destruct CRED as (irr & C1 & _ & _ & _ & _ & _ & _ & _ & C9 & _).
  destruct (g_depot FSG G) as [|kb]; [exfalso; cbn in C9; lia | exists kb; reflexivity].
Qed.

Lemma art_cr_sec : forall cost, 1 <= fst cr -> 0 <= cost <= snd cr ->
  Z.of_nat (length (g_sec FSG G)) + 1 <= 16384 /\ Z.of_nat (length (art_live (g_log FSG G))) < KMAX
  /\ art_cost_sum (g_log FSG G) + cost + 131072 <= BUDGET.
Proof.
  intros cost H Hc. destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _). pose proof (art_primsum_le (g_cls FSG G) CLSOK) as P.
  change (2 ^ 20) with 1048576 in C5. unfold KCNT, KMAX in *. split; [lia|]. split; [lia|]. destruct (g_sec_committed FSG G); lia.
Qed.

Lemma art_wmx_creditR : forall c w u n (kb : nat) kk cost,
  1 <= c <= 30 -> g_depot FSG G = Datatypes.S kb ->
  3 <= kk <= fst cr -> 0 <= cost <= snd cr ->
  art_credit_ok FSG BUDGET rn (art_gs_malloc G (rn_spb rn) c w u n kb) ((u, n) :: LB) (fst cr - kk, snd cr - cost).
Proof.
  intros c w u n kb kk cost Hc Edep Hkk Hcost. pose proof (CLSOK c Hc) as OK.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG).
  exists (irr + 1). unfold art_credit_ok. cbn [art_gs_malloc g_log g_sec g_sec_committed g_depot g_cls g_qt g_qg fst snd length].
  rewrite Nat2Z.inj_succ, Edep in *. rewrite Nat2Z.inj_succ in C9.
  rewrite art_cost_sum_app, art_cost_sec_app, art_cost_sec_ca, art_live_ca_events, (art_primsum_upd _ c _ Hc), (art_ca_events_cost _ c _ Hc OK).
  unfold art_hdrs. cbn [map]. fold (art_hdrs LB). rewrite art_nirr_cons.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [destruct (art_irr (rn_spb rn) (fst (u, n) - 16, snd (u, n))); lia|]. split; assumption.
Qed.

Lemma art_wmx_creditW : forall c w u n,
  1 <= c <= 30 -> 1 <= fst cr -> art_irr (rn_spb rn) (u - 16, n) = false ->
  art_credit_ok FSG BUDGET rn (art_gs_malloc G (rn_spb rn) c w u n (g_depot FSG G)) ((u, n) :: LB) (fst cr - 1, snd cr).
Proof.
  intros c w u n Hc Hk Hreg. pose proof (CLSOK c Hc) as OK.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG).
  exists irr. unfold art_credit_ok. cbn [art_gs_malloc g_log g_sec g_sec_committed g_depot g_cls g_qt g_qg fst snd length].
  rewrite Nat2Z.inj_succ.
  rewrite art_cost_sum_app, art_cost_sec_app, art_cost_sec_ca, art_live_ca_events, (art_primsum_upd _ c _ Hc), (art_ca_events_cost _ c _ Hc OK).
  unfold art_hdrs. cbn [map]. fold (art_hdrs LB). rewrite art_nirr_cons. cbn [fst snd]. rewrite Hreg.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; assumption.
Qed.

Lemma art_wmlx_creditR : forall msz r u n (kb : nat) kk cost,
  g_depot FSG G = Datatypes.S kb -> 0 <= msz ->
  3 <= kk <= fst cr -> msz + msz / 8 + 8192 <= cost -> cost <= snd cr ->
  art_credit_ok FSG BUDGET rn (art_gs_malloc_sec G (rn_parr rn) msz r u n kb) ((u, n) :: LB) (fst cr - kk, snd cr - cost).
Proof.
  intros msz r u n kb kk cost Edep Hm Hkk Hcost Hcost'.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG).
  assert (Hm8 : 0 <= msz / 8) by (apply Z.div_pos; lia).
  exists (irr + 1). unfold art_credit_ok. cbn [art_gs_malloc_sec g_log g_sec g_sec_committed g_depot g_cls g_qt g_qg fst snd length].
  rewrite Nat2Z.inj_succ, Edep in *. rewrite Nat2Z.inj_succ in C9.
  rewrite art_cost_sum_app, art_cost_sec_app, art_live_sec_events, length_app. cbn [length]. rewrite Nat2Z.inj_succ, Nat2Z.inj_add. cbn [Z.of_nat].
  unfold art_hdrs. cbn [map]. fold (art_hdrs LB). rewrite art_nirr_cons.
  assert (E1 : art_cost_sec (art_sec_events msz r (rn_parr rn) (Z.of_nat (length (g_sec FSG G))) (g_sec_committed FSG G)) = msz + msz / 8 + 8192).
  { unfold art_sec_events, art_cost_sec. destruct (g_sec_committed FSG G); cbn [fold_right]; lia. }
  assert (E2 : art_cost_sum (art_sec_events msz r (rn_parr rn) (Z.of_nat (length (g_sec FSG G))) (g_sec_committed FSG G))
               = msz + msz / 8 + 8192 + (if g_sec_committed FSG G then 0 else 131072)).
  { unfold art_sec_events, art_cost_sum. destruct (g_sec_committed FSG G); cbn [fold_right art_cost]; lia. }
  rewrite E1, E2.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [destruct (g_sec_committed FSG G); lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [destruct (art_irr (rn_spb rn) (fst (u, n) - 16, snd (u, n))); lia|]. split; assumption.
Qed.

Lemma art_cr_kbU : forall (warm : bool) (Kz : list Z) (D : list (list Z)), (exists kb, g_depot FSG G = Datatypes.S kb) -> (warm = true -> In Kz D) ->
  exists kb0 kb : nat, g_depot FSG G = Datatypes.S kb0 /\ (kb <= g_depot FSG G)%nat
    /\ (kb <= if HeapIfaceAEr.HAR.kin Kz D then Datatypes.S kb0 else pred (Datatypes.S kb0))%nat
    /\ (if warm then kb = g_depot FSG G else g_depot FSG G = Datatypes.S kb).
Proof.
  intros warm Kz D (kb0 & E) HW. exists kb0. destruct warm.
  - exists (Datatypes.S kb0). rewrite (In_kin Kz D (HW eq_refl)), E. split; [reflexivity|]. split; [apply le_n|]. split; [apply le_n|reflexivity].
  - exists kb0. rewrite E. split; [reflexivity|]. split; [apply le_S, le_n|]. split; [|reflexivity].
    destruct (HeapIfaceAEr.HAR.kin Kz D); cbn [pred]; [apply le_S, le_n|apply le_n].
Qed.

Lemma art_wmx_creditU : forall (warm : bool) (L : asan_layout) (P : Prop) c w u n (kb : nat),
  1 <= c <= 30 -> 3 <= hl_k_per_malloc L -> 0 <= hl_b_lin L * n -> 0 <= hl_b_overhead L ->
  (if warm then P /\ 64 <= n <= 128 /\ 1 <= fst cr else acredit_ok L cr n) ->
  (if warm then kb = g_depot FSG G else g_depot FSG G = Datatypes.S kb) ->
  (warm = true -> art_irr (rn_spb rn) (u - 16, n) = false) ->
  art_credit_ok FSG BUDGET rn (art_gs_malloc G (rn_spb rn) c w u n kb) ((u, n) :: LB) (if warm then (fst cr - 1, snd cr) else adebit L cr n).
Proof.
  intros warm L P c w u n kb Hc HLk Hlin Hov MODE KBW HREG. destruct warm.
  - destruct MODE as (_ & Hn & H1). rewrite KBW. exact (art_wmx_creditW c w u n Hc H1 (HREG eq_refl)).
  - destruct MODE as (AC1 & AC2). unfold adebit. apply (art_wmx_creditR c w u n kb _ _ Hc KBW); lia.
Qed.
End T.

Lemma art_primsum_0 : forall cls, (forall c, cl_mu (cls c) = 0 /\ cl_mfa (cls c) = 0) -> art_primsum cls = 0.
Proof.
  intros cls H. rewrite art_primsum_eq. induction (map Z.of_nat (seq 1 30)) as [|x r IH]; [reflexivity|]. cbn [fold_right]. rewrite IH.
  unfold art_cl_maps. destruct (H x) as (E1 & E2). rewrite E1, E2. reflexivity.
Qed.
Lemma art_credit_gs0 : forall FSG BUDGET rn (gfs0 : FSG) (k0 : nat) B0,
  0 <= B0 -> B0 + 2 ^ 20 <= BUDGET - PRIMCAP -> 2 * KCNT <= Z.of_nat k0 ->
  art_credit_ok FSG BUDGET rn (art_gs0 FSG gfs0 k0) [] (KCNT, B0).
Proof.
  intros FSG BUDGET rn gfs0 k0 B0 HB HBud Hk. exists 0. unfold art_credit_ok, art_gs0. cbn [g_log g_sec g_sec_committed g_depot g_cls g_qt g_qg fst snd length app].
  rewrite (art_primsum_0 (fun _ => art_cls0)) by (intros c; split; reflexivity).
  change (art_cost_sec []) with 0. change (art_cost_sum []) with 0. change (art_live []) with (@nil (Z * Z)). cbn [length].
  change (art_hdrs []) with (@nil (Z * Z)). change (art_items []) with (@nil (Z * Z)). rewrite art_nirr_nil.
  unfold KCNT, KMAX in *. change (Z.of_nat 0) with 0.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact art_qt_ok_nil | exact I].
Qed.
