(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim APrimLem APrimPop APrimPopR APrimSpec2 APrimQ AFrame APrimFrame.
Import ListNotations.
Open Scope Z_scope.

Lemma in_firstn_in : forall {A} (n : nat) (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Definition pop_cls (k : pclass) : pclass :=
  mkPCL (p_nf k) (p_mfa k) (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k - 1) (firstn (Z.to_nat (p_cnt k - 1)) (p_chunks k)).

Lemma pop_cls_wf : forall c k, pclass_wf c k -> 0 < p_cnt k -> pclass_wf c (pop_cls k).
Proof.
  intros c k (Lnf & Lcnt & CR & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA) C0.
  unfold pclass_wf, pop_cls. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks].
  split; [exact Lnf|]. split; [rewrite length_firstn; lia|]. split; [lia|]. split; [exact NF4|]. split; [exact MFA|]. split; [exact MFAM|].
  split; [exact AU|]. split; [exact MUF|]. split; [exact MUM|]. split; [exact AUS|]. split; [exact GAP|].
  split.
  - apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
    rewrite <- (firstn_skipn (Z.to_nat (p_cnt k - 1)) (p_chunks k)), app_assoc in ND. exact (NoDup_app_remove_r _ _ ND).
  - split; [| exact NA]. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) FB).
    apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx| right; exact (in_firstn_in _ _ _ Hx)].
Qed.

Lemma cache_alloc_hit : forall P c, 0 < p_cnt (get_cls P c) ->
  cache_alloc P c = (mkPRIM (set_nth (Z.to_nat c) (pop_cls (get_cls P c)) (pr_cls P)) true (pr_calloc P + class_size c)
                            (pr_cmapped P + (p_mu (pop_cls (get_cls P c)) - p_mu (get_cls P c))),
                     nth (Z.to_nat (p_cnt (get_cls P c) - 1)) (p_chunks (get_cls P c)) 0).
Proof.
  intros P c CNT. unfold cache_alloc, cache_alloc_cls.
  replace (p_cnt (get_cls P c) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Section PL.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
Notation THR := (at_thr (al_thread AL)).

#[using="HC AO"] Lemma pop_W_miss_body : forall c c' k', 1 <= c <= 31 -> 1 <= c' <= 31 ->
  Forall (cls_miss_body AL c' k') [(pcl_addr AL c, pcl_addr AL c + 4); (THR + CSTATS_OFF + 16, THR + CSTATS_OFF + 24)].
Proof.
  intros c c' k' Hc Hc'.
  layout_facts AO 0%nat SPF. destruct SPF as (S1 & S2 & _ & _ & S5 & _ & S7).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_apart_fact AO 0%nat 3%nat LP03.
  pose proof (region_range AL c' Hc') as [R1 R2].
  pose proof (sh_le 0 (region AL c') ltac:(lia)) as L1. change (sh 0) with 2147450880 in L1.
  pose proof (sh_le (region AL c' + K_REGION) (2^47) ltac:(lia)) as L2. change (sh (2^47)) with 17594333495296 in L2.
  unfold cls_miss_body, pcl_addr, ri_addr, RIB.
  repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| left; lia]).
Qed.

#[using="HC AO"] Theorem RPRIM_pop : RPRIM_pop_stmt AL.
Proof.
  intros P m c RP POK Hc CNT. cbv zeta.
  set (k := get_cls P c) in *. set (cnt := p_cnt k) in *. set (v := nth (Z.to_nat (cnt - 1)) (p_chunks k) 0).
  pose proof RP as (LEN & PENV & CLS & STAT & (ts & TS)).
  destruct (CLS c Hc) as (WFc & RIc & (PCc & (ws & CAc & CLc & CXc)) & FAc & TLc & FCHc). fold k in WFc, RIc, PCc, CXc, FAc, TLc, FCHc.
  assert (INI : pr_inited P = true). { destruct (pr_inited P) eqn:E; [reflexivity|]. specialize (POK E c Hc). fold k in POK. fold cnt in POK. lia. }
  rewrite INI in *.
  pose proof WFc as (Lnf & Lcnt & CR & _ & _ & _ & AU & MUF & _ & _ & _ & _ & FB & _). fold cnt in Lcnt, CR.
  assert (VIN : In v (p_chunks k)) by (unfold v; apply nth_In; lia).
  pose proof (proj1 (Forall_forall _ _) FB v (in_or_app _ _ _ (or_intror VIN))) as (V0 & V1 & V2). cbv beta in V0, V1, V2.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  split; [reflexivity|]. split; [exact V0|]. split; [exact V1|]. split; [exact V2|]. split; [lia|]. split; [exact PENV|].
  split; [exact PCc|].
  split.
  { exists ws. split; [exact CAc|]. split; [exact CLc|].
    assert (E : nth (Z.to_nat (cnt - 1)) ws (wz 0) = nth (Z.to_nat (cnt - 1)) (firstn (length (p_chunks k)) ws) (wz 0)).
    { rewrite nth_firstn. replace (Z.to_nat (cnt - 1) <? length (p_chunks k))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    rewrite E, CXc. apply (map_nth wz). }
  split; [exact STAT|]. split; [apply FCHc; apply in_or_app; right; exact VIN|].

  intros m' MU WM PC' ST'.
  assert (ECA : cache_alloc P c = (mkPRIM (set_nth (Z.to_nat c) (pop_cls k) (pr_cls P)) true (pr_calloc P + class_size c) (pr_cmapped P + (p_mu (pop_cls k) - p_mu k)), v)).
  { unfold cache_alloc, cache_alloc_cls. fold k. fold cnt. replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite ECA. cbn [fst snd]. split; [| split; [intros X; discriminate| reflexivity]].
  assert (DJ : forall A n, (A + n <= pcl_addr AL c \/ pcl_addr AL c + 4 <= A) -> (A + n <= THR + CSTATS_OFF + 16 \/ THR + CSTATS_OFF + 24 <= A) ->
               disjoint_from [(pcl_addr AL c, pcl_addr AL c + 4); (THR + CSTATS_OFF + 16, THR + CSTATS_OFF + 24)] A n)
    by (intros A n H1 H2; cbn [disjoint_from]; lia).
  split; [cbn [pr_cls]; rewrite set_nth_length; exact LEN|].
  split.
  {   unfold prim_env in *. eapply rw_cells_transport; [exact PENV| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
    apply DJ; unfold pcl_addr; lia. }
  split.
  {
    intros c' Hc'. cbn [pr_inited]. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite get_cls_set_same by (try exact LEN; lia).
      destruct (cls_body_frame AL AO c k Hc WFc _ m m' (conj RIc (conj FAc (conj TLc FCHc))) MU WM (pop_W_miss_body c c k Hc Hc)) as (RI' & FA' & TL' & FCH').
      split; [apply pop_cls_wf; [exact WFc| exact CNT]|].
      split; [exact RI'|]. split; [| split; [exact FA'| split; [exact TL'|]]].
      + split; [exact PC'|]. exists ws. split; [| split; [exact CLc|]].
        * eapply u32arr_transport; [exact CAc| exact MU| exact WM|]. rewrite CLc. apply DJ; unfold pcl_addr; lia.
        * unfold pop_cls. cbn [p_chunks]. rewrite length_firstn, Nat.min_l by lia.
          rewrite <- firstn_map, <- CXc, firstn_firstn. f_equal. lia.
      + intros x Hx. apply FCH'. unfold pop_cls in Hx. cbn [p_fa p_chunks] in Hx.
        apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx| right; exact (in_firstn_in _ _ _ Hx)].
    - assert (EO : get_cls (mkPRIM (set_nth (Z.to_nat c) (pop_cls k) (pr_cls P)) true (pr_calloc P + class_size c) (pr_cmapped P + (p_mu (pop_cls k) - p_mu k))) c' = get_cls P c').
      { unfold get_cls. cbn [pr_cls]. apply nth_set_nth_other. lia. }
      rewrite EO. destruct (CLS c' Hc') as (WFc' & _).
      apply (cls_rep_frame AL AO c' (get_cls P c') Hc' WFc' true _ m m' (CLS c' Hc') MU WM).
      pose proof (pop_W_miss_body c c' (get_cls P c') Hc Hc') as B.
      apply Forall_cons_iff in B as [B1 B2]. apply Forall_cons_iff in B2 as [B2 _].
      repeat (apply Forall_cons || apply Forall_nil); (split; [cbn [fst snd]; unfold pcl_addr; lia| assumption]). }
  split.
  { unfold pop_cls. cbn [p_mu]. rewrite Z.sub_diag, Z.add_0_r. exact ST'. }
  exists ts. eapply rw_cells_transport; [exact TS| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply DJ; unfold pcl_addr; lia.
Qed.
End PL.
