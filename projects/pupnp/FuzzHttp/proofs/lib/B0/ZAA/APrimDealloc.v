(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim APrimLem LJ APrimPop APrimPopR APrimSpec APrimSpec2 APrimQ AFrame APrimFrame APrimPopLens.
Import ListNotations.
Open Scope Z_scope.

Definition drain_cls (k : pclass) (c : Z) : pclass :=
  let h := max_count c / 2 in
  let kr := return_to_allocator k (skipn (Z.to_nat (p_cnt k - h)) (p_chunks k)) in
  mkPCL (p_nf kr) (p_mfa kr) (p_au kr) (p_mu kr) (p_nalloc kr) (p_nfreed kr) (p_fa kr) (p_cnt k - h) (firstn (Z.to_nat (p_cnt k - h)) (p_chunks k)).

Definition push_cls (k : pclass) (v : Z) : pclass :=
  mkPCL (p_nf k) (p_mfa k) (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k + 1) (p_chunks k ++ [v]).

Lemma cache_dealloc_cls_eq : forall k c v,
  cache_dealloc_cls k c v = push_cls (if p_cnt k =? max_count c then drain_cls k c else k) v.
Proof. intros. unfold cache_dealloc_cls, push_cls, drain_cls. destruct (p_cnt k =? max_count c); reflexivity. Qed.

Lemma nodup_slots : forall (l : list Z) (sz au : Z), 0 < sz -> 0 <= au -> List.NoDup l ->
  Forall (fun v => 0 <= v /\ 16 * v + sz <= au /\ (16 * v) mod sz = 0) l -> Z.of_nat (length l) * sz <= au.
Proof.
  intros l sz au Hsz Hau ND FA.
  set (f := fun v : Z => Z.to_nat (16 * v / sz)).
  assert (SLOT : forall v, In v l -> 16 * v = sz * (16 * v / sz) /\ 0 <= 16 * v / sz < au / sz).
  { intros v Hv. pose proof (proj1 (Forall_forall _ _) FA v Hv) as (V0 & V1 & V2). cbv beta in V0, V1, V2.
    pose proof (Z_div_exact_full_2 (16 * v) sz ltac:(lia) V2) as E. split; [exact E|].
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    assert (sz * (16 * v / sz + 1) <= au) by lia.
    pose proof (Z.mul_div_le au sz Hsz). pose proof (Z.mod_pos_bound au sz Hsz). pose proof (Z.div_mod au sz ltac:(lia)). nia. }
  assert (NDm : List.NoDup (map f l)).
  { apply NoDup_map_NoDup_ForallPairs; [| exact ND]. intros x y Hx Hy E. unfold f in E.
    destruct (SLOT x Hx) as (Ex & Bx & _). destruct (SLOT y Hy) as (Ey & By & _).
    apply Z2Nat.inj in E; [| lia | lia]. rewrite E in Ex. lia. }
  assert (INC : incl (map f l) (seq 0 (Z.to_nat (au / sz)))).
  { intros n Hn. apply in_map_iff in Hn as (v & <- & Hv). apply in_seq. destruct (SLOT v Hv) as (_ & B0 & B1). unfold f. lia. }
  pose proof (NoDup_incl_length NDm INC) as L. rewrite length_map, length_seq in L.
  pose proof (Z.mul_div_le au sz Hsz). pose proof (Z.div_pos au sz Hau Hsz). nia.
Qed.

Lemma pfa_bound : forall c k, 1 <= c <= 31 -> pclass_wf c k -> (p_nf k + p_cnt k) * 32 <= FA_OFF.
Proof.
  intros c k Hc (Lnf & Lcnt & _ & _ & _ & _ & AU & MUF & _ & _ & _ & ND & FB & _).
  pose proof (class_size_pos c Hc) as CS. apply NoDup_ListNoDup in ND.
  pose proof (nodup_slots _ (class_size c) (p_au k) ltac:(lia) ltac:(lia) ND FB) as B.
  rewrite length_app, Nat2Z.inj_add, <- Lnf, <- Lcnt in B.
  assert (0 <= p_nf k + p_cnt k) by lia. nia.
Qed.

Lemma drain_budget_wf : forall c k, 1 <= c <= 31 -> pclass_wf c k -> drain_budget c k.
Proof.
  intros c k Hc WF. pose proof (pfa_bound c k Hc WF) as B. pose proof WF as (_ & _ & CNT & _).
  pose proof (max_count_range c Hc) as (MR & _). unfold drain_budget.
  assert (max_count c / 2 <= 8) by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma in_skipn_in : forall {A} (n : nat) (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

Lemma drain_cls_perm : forall k c, Permutation (p_fa (drain_cls k c) ++ p_chunks (drain_cls k c)) (p_fa k ++ p_chunks k).
Proof.
  intros k c. unfold drain_cls. cbn [p_fa p_chunks return_to_allocator].
  set (n := Z.to_nat (p_cnt k - max_count c / 2)).
  rewrite <- (firstn_skipn n (p_chunks k)) at 3. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma drain_cls_free : forall k c x, In x (p_fa (drain_cls k c) ++ p_chunks (drain_cls k c)) <-> In x (p_fa k ++ p_chunks k).
Proof. intros k c x. split; intros H; [exact (Permutation_in _ (drain_cls_perm k c) H)| exact (Permutation_in _ (Permutation_sym (drain_cls_perm k c)) H)]. Qed.

Lemma efa_new_range : forall k tot, 0 <= p_mfa k <= K_FA_SIZE -> p_mfa k mod K_MAP = 0 -> 4 * tot <= K_FA_SIZE ->
  p_mfa k <= efa_new k tot <= K_FA_SIZE /\ efa_new k tot mod K_MAP = 0 /\ 4 * tot <= efa_new k tot.
Proof.
  intros k tot MFA MFAM TB. unfold efa_new. destruct (Z.leb_spec (4 * tot) (p_mfa k)) as [LE|GT]; [lia|].
  pose proof (rup_ge (4 * tot) K_MAP ltac:(lia)). pose proof (rup_mod (4 * tot) K_MAP ltac:(lia)).
  pose proof (rup_le (4 * tot) K_FA_SIZE K_MAP ltac:(lia) ltac:(lia) ltac:(reflexivity)). lia.
Qed.

Lemma drain_cls_wf : forall c k, 1 <= c <= 31 -> pclass_wf c k -> max_count c / 2 <= p_cnt k -> pclass_wf c (drain_cls k c).
Proof.
  intros c k Hc WF HCNT. pose proof (drain_budget_wf c k Hc WF) as DB. unfold drain_budget in DB.
  pose proof (max_count_range c Hc) as (MR & MR2).
  pose proof WF as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
  set (h := max_count c / 2) in *. assert (Hh : 1 <= h <= 8) by (unfold h; Z.div_mod_to_equations; lia).
  assert (LS : Z.of_nat (length (skipn (Z.to_nat (p_cnt k - h)) (p_chunks k))) = h) by (rewrite length_skipn; lia).
  pose proof (efa_new_range k (p_nf k + h) MFA MFAM ltac:(lia)) as (E1 & E2 & E3).
  unfold pclass_wf, drain_cls. fold h. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks return_to_allocator ensure_fa]. rewrite LS.
  split; [rewrite length_app, Nat2Z.inj_add, LS; lia|]. split; [rewrite length_firstn; lia|]. split; [lia|].
  split; [exact E3|]. split; [lia|]. split; [exact E2|].
  split; [exact AU|]. split; [exact MUF|]. split; [exact MUM|]. split; [exact AUS|]. split; [exact GAP|].
  pose proof (drain_cls_perm k c) as PM. unfold drain_cls in PM. fold h in PM. cbn [p_fa p_chunks return_to_allocator] in PM.
  split; [apply NoDup_ListNoDup; apply NoDup_ListNoDup in ND; exact (Permutation_NoDup (Permutation_sym PM) ND)|].
  split; [| lia].
  apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) FB). exact (Permutation_in _ PM Hx).
Qed.

Lemma push_cls_wf : forall c k v, pclass_wf c k -> p_cnt k < max_count c ->
  0 <= v -> 16 * v + class_size c <= p_au k -> (16 * v) mod class_size c = 0 -> ~ In v (p_fa k ++ p_chunks k) ->
  pclass_wf c (push_cls k v).
Proof.
  intros c k v (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA) LT V0 V1 V2 NI.
  unfold pclass_wf, push_cls. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks].
  split; [exact Lnf|]. split; [rewrite length_app; cbn [length]; lia|]. split; [lia|]. split; [exact NF4|]. split; [exact MFA|]. split; [exact MFAM|].
  split; [exact AU|]. split; [exact MUF|]. split; [exact MUM|]. split; [exact AUS|]. split; [exact GAP|].
  assert (PM : Permutation (p_fa k ++ p_chunks k ++ [v]) (v :: (p_fa k ++ p_chunks k))).
  { rewrite app_assoc. apply Permutation_sym. apply Permutation_cons_append. }
  split.
  - apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND. apply (Permutation_NoDup (Permutation_sym PM)). constructor; assumption.
  - split; [| exact NA]. apply Forall_forall. intros x Hx. apply (Permutation_in _ PM) in Hx. destruct Hx as [<-|Hx].
    + cbv beta. repeat split; assumption.
    + exact (proj1 (Forall_forall _ _) FB x Hx).
Qed.

Lemma push_cls_free : forall k v x, In x (p_fa (push_cls k v) ++ p_chunks (push_cls k v)) <-> In x (p_fa k ++ p_chunks k) \/ x = v.
Proof.
  intros k v x. unfold push_cls. cbn [p_fa p_chunks]. rewrite !in_app_iff. cbn [In]. intuition (auto; try congruence).
Qed.

Section DL.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
Notation THR := (at_thr (al_thread AL)).

Definition drain_W (lo q c : Z) (k k' : pclass) : list (Z * Z) :=
  [(lo, q); (ri_addr AL c, ri_addr AL c + 128); (fa_base AL c + 4 * p_nf k, fa_base AL c + p_mfa k');
   (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa k) + (p_mfa k' - p_mfa k) / 8);
   (swlo (fa_base AL c + p_mfa k), swhi (fa_base AL c + p_mfa k) (p_mfa k' - p_mfa k));
   (THR + TSTATS_OFF, THR + TSTATS_OFF + 368); (pcl_addr AL c, pcl_addr AL c + 4)].

#[using="AO"] Lemma dl_geom : forall c, 1 <= c <= 31 ->
  17594333495296 <= al_space AL /\ al_space AL + (137438953472 + 4096) <= alloc_ceiling
  /\ ((0 < THR /\ THR + 4096 <= 65536) \/ (6328320 <= THR /\ THR + 4096 <= 2147446784) \/ 17594333495296 <= THR)
  /\ THR + 4096 <= alloc_ceiling
  /\ (al_space AL + (137438953472 + 4096) <= THR \/ THR + 4096 <= al_space AL)
  /\ al_space AL + K_REGION <= region AL c /\ region AL c + K_REGION <= al_space AL + K_SPACE
  /\ 2147450880 <= sh (region AL c) /\ sh (region AL c + K_REGION) <= 17594333495296
  /\ (forall x, region AL c <= x <= region AL c + K_REGION -> sh (region AL c) <= sh x <= sh (region AL c + K_REGION)).
Proof.
  intros c Hc.
  layout_facts AO 0%nat SPF. destruct SPF as (S1 & S2 & _ & _ & S5 & _ & S7).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_apart_fact AO 0%nat 3%nat LP03.
  pose proof (region_range AL c Hc) as [R1 R2].
  pose proof (sh_le 0 (region AL c) ltac:(lia)) as L0. change (sh 0) with 2147450880 in L0.
  pose proof (sh_le (region AL c + K_REGION) (2^47) ltac:(lia)) as U0. change (sh (2^47)) with 17594333495296 in U0.
  split; [exact S1|]. split; [exact S2|]. split; [exact (proj1 T3)|]. split; [exact T4|]. split; [exact LP03|].
  split; [exact R1|]. split; [exact R2|]. split; [exact L0|]. split; [exact U0|].
  intros x Hx. split; apply sh_le; lia.
Qed.

#[using="HC AO"] Lemma fa_sw_exact : forall c mfa mfa', 1 <= c <= 31 -> mfa mod K_MAP = 0 -> mfa' mod K_MAP = 0 ->
  swlo (fa_base AL c + mfa) = sh (fa_base AL c + mfa) /\ swhi (fa_base AL c + mfa) (mfa' - mfa) = sh (fa_base AL c + mfa')
  /\ sh (fa_base AL c + mfa') = sh (fa_base AL c + mfa) + (mfa' - mfa) / 8.
Proof.
  intros c mfa mfa' Hc M1 M2. pose proof (REG_mod32768 AL AO c) as RM.
  assert (A1 : (fa_base AL c + mfa) mod 32768 = 0) by (unfold fa_base; clear - RM M1; Z.div_mod_to_equations; lia).
  assert (A2 : (mfa' - mfa) mod 32768 = 0) by (clear - M1 M2; Z.div_mod_to_equations; lia).
  pose proof (sw_exact _ _ A1 A2) as (E1 & E2 & E3).
  replace (fa_base AL c + mfa + (mfa' - mfa)) with (fa_base AL c + mfa') in E2, E3 by lia.
  split; [exact E1|]. split; [exact E2| exact E3].
Qed.

#[using="AO"] Lemma drain_W_miss : forall lo q c c' (k k' k0 : pclass),
  1 <= c <= 31 -> 1 <= c' <= 31 -> c' <> c ->
  0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
  0 <= p_nf k -> 0 <= p_mfa k -> p_mfa k <= p_mfa k' -> p_mfa k' <= K_FA_SIZE -> p_mfa k mod K_MAP = 0 -> p_mfa k' mod K_MAP = 0 ->
  Forall (cls_miss AL c' k0) (drain_W lo q c k k').
Proof.
  intros lo q c c' k k' k0 Hc Hc' NE LOH CLO LQ NF0 MF0 MFK MFB M1 M2.
  pose proof (dl_geom c Hc) as (S1 & S2 & T3 & T4 & LP03 & R1 & R2 & L0 & U0 & SHS).
  pose proof (dl_geom c' Hc') as (_ & _ & _ & _ & _ & R1' & R2' & L0' & U0' & _).
  pose proof (SHS (fa_base AL c + p_mfa k) ltac:(unfold fa_base; lia)) as X3. pose proof (SHS (fa_base AL c + p_mfa k') ltac:(unfold fa_base; lia)) as X4.
  clear SHS.
  pose proof (fa_sw_exact c (p_mfa k) (p_mfa k') Hc M1 M2) as (E1 & E2 & E3).
  assert (ORD : sh (region AL c + K_REGION) <= sh (region AL c') \/ sh (region AL c' + K_REGION) <= sh (region AL c)).
  { destruct (Z_lt_le_dec c c') as [LT|GE]; [left| right]; apply sh_le; unfold region; lia. }
  assert (ORB : region AL c + K_REGION <= region AL c' \/ region AL c' + K_REGION <= region AL c) by (unfold region; lia).
  unfold drain_W. rewrite E1, E2, <- E3.
  unfold cls_miss, cls_miss_body, pcl_addr, ri_addr, RIB, fa_base in *.
  repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| split; [lia| left; lia]]).
Qed.

#[using="AO"] Lemma drain_close : forall (P : prim) (mA mD : mem) (lo q c : Z),
  1 <= c <= 31 -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
  pr_inited P = true -> RPRIM AL P mA -> max_count c / 2 <= p_cnt (get_cls P c) ->
  munch (drain_W lo q c (get_cls P c) (drain_cls (get_cls P c) c)) mA mD -> wmono asegs mA mD ->
  prim_env AL mD -> ri_rep AL mD c (drain_cls (get_cls P c) c) -> pcl_rep AL mD true c (drain_cls (get_cls P c) c) ->
  fa_rep AL mD c (drain_cls (get_cls P c) c) ->
  (exists ts, rw_cells asegs mD (THR + TSTATS_OFF) [CB 368 ts]) ->
  RPRIM AL (mkPRIM (set_nth (Z.to_nat c) (drain_cls (get_cls P c) c) (pr_cls P)) true (pr_calloc P) (pr_cmapped P)) mD.
Proof.
  intros P mA mD lo q c Hc LOH CLO LQ INI RP HCNT MU WM PENV' RI' PCL' FA' TS'.
  set (k := get_cls P c) in *. set (kd := drain_cls k c) in *.
  pose proof RP as (LEN & PENV & CLS & STAT & _). rewrite INI in CLS.
  destruct (CLS c Hc) as (WF & RIc & PCc & FAc & TLc & FCHc). fold k in WF, RIc, PCc, FAc, TLc, FCHc.
  pose proof (drain_cls_wf c k Hc WF HCNT) as WFd. fold kd in WFd.
  pose proof WF as (Lnf & _ & _ & NF4 & MFA & MFAM & AU & MUF & _).
  pose proof WFd as (_ & _ & _ & _ & MFAd & MFAMd & _).
  assert (MFK : p_mfa k <= p_mfa kd).
  { unfold kd, drain_cls. cbn [p_mfa return_to_allocator ensure_fa]. unfold efa_new. destruct (Z.leb_spec (4 * (p_nf k + Z.of_nat (length (skipn (Z.to_nat (p_cnt k - max_count c / 2)) (p_chunks k))))) (p_mfa k)) as [LE|GT]; [lia|].
    pose proof (rup_ge (4 * (p_nf k + Z.of_nat (length (skipn (Z.to_nat (p_cnt k - max_count c / 2)) (p_chunks k))))) K_MAP ltac:(lia)). lia. }
  pose proof (dl_geom c Hc) as (S1 & S2 & T3 & T4 & LP03 & R1 & R2 & L0 & U0 & SHS).
  pose proof (SHS (fa_base AL c + p_mfa k) ltac:(unfold fa_base; lia)) as X3. pose proof (SHS (fa_base AL c + p_mfa kd) ltac:(unfold fa_base; lia)) as X4.
  pose proof (SHS (region AL c + p_au k) ltac:(lia)) as X5. pose proof (SHS (region AL c + p_mu k) ltac:(lia)) as X6.
  assert (X7 : sh (region AL c + p_mu k) <= sh (fa_base AL c + p_mfa k)) by (apply sh_le; unfold fa_base; lia).
  assert (X8 : sh (region AL c + p_au k) <= sh (region AL c + p_mu k)) by (apply sh_le; lia).
  clear SHS.
  pose proof (fa_sw_exact c (p_mfa k) (p_mfa kd) Hc MFAM MFAMd) as (E1 & E2 & E3).
  pose proof MU as MU0. unfold drain_W in MU0. rewrite E1, E2, <- E3 in MU0.
  split; [cbn [pr_cls]; rewrite set_nth_length; exact LEN|].
  split; [exact PENV'|].
  split.
  { intros c' Hc'. cbn [pr_inited]. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite get_cls_set_same by (try exact LEN; lia). fold kd.
      split; [exact WFd|]. split; [exact RI'|]. split; [exact PCL'|]. split; [exact FA'|].
      split.
      +
        destruct TLc as [(jt & TL) TSH]. unfold tail_rep.
        replace (p_au kd) with (p_au k) by reflexivity. replace (p_mu kd) with (p_mu k) by reflexivity.
        assert (SHT : sh (region AL c + p_au k) + (p_mu k - p_au k) / 8 <= sh (region AL c + p_mu k)) by (unfold sh; clear; Z.div_mod_to_equations; lia).
        split; [exists jt|].
        * eapply rw_cells_transport; [exact TL| exact MU0| exact WM|]. cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
          unfold pcl_addr, ri_addr, RIB, fa_base in *. clear - S1 S2 T3 T4 LP03 R1 R2 L0 U0 X3 X4 X5 X6 X7 X8 AU MUF Lnf MFA CLO LOH LQ Hc. lia.
        * eapply rw_cells_transport; [exact TSH| exact MU0| exact WM|]. cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
          unfold pcl_addr, ri_addr, RIB, fa_base in *. clear - SHT S1 S2 T3 T4 LP03 R1 R2 L0 U0 X3 X4 X5 X6 X7 X8 AU MUF Lnf MFA CLO LOH LQ Hc. lia.
      + intros v Hv. apply (drain_cls_free k c v) in Hv.
        eapply (free_chunks_frame AL AO c k Hc WF _ mA mD MU0 WM); [| exact FCHc| exact Hv].
        unfold carved_clear, pcl_addr, ri_addr, RIB, fa_base in *.
        clear - S1 S2 T3 T4 LP03 R1 R2 L0 U0 X3 X4 X5 X6 X7 X8 AU MUF Lnf MFA CLO LOH LQ Hc.
        repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd]; repeat split; lia.
    - assert (EO : get_cls (mkPRIM (set_nth (Z.to_nat c) kd (pr_cls P)) true (pr_calloc P) (pr_cmapped P)) c' = get_cls P c').
      { unfold get_cls. cbn [pr_cls]. apply nth_set_nth_other. lia. }
      rewrite EO. destruct (CLS c' Hc') as (WFc' & _).
      apply (cls_rep_frame AL AO c' (get_cls P c') Hc' WFc' true _ mA mD (CLS c' Hc') MU WM).
      apply drain_W_miss; try assumption; lia. }
  split; [| exact TS'].
  cbn [pr_calloc pr_cmapped]. eapply rw_cells_transport; [exact STAT| exact MU0| exact WM|]. cbn [disjoint_from cells_size csize Nat.add].
  unfold pcl_addr, ri_addr, RIB, fa_base in *. clear - S1 S2 T3 T4 LP03 R1 R2 L0 U0 X3 X4 AU MUF Lnf MFA MFAd MFK CLO LOH LQ Hc. lia.
Qed.

Definition push_W (c cnt : Z) : list (Z * Z) :=
  [(pcl_addr AL c, pcl_addr AL c + 4); (pcl_addr AL c + 16 + 4 * cnt, pcl_addr AL c + 16 + 4 * cnt + 4);
   (THR + CSTATS_OFF + 16, THR + CSTATS_OFF + 24)].

#[using="HC AO"] Lemma push_W_miss_body : forall c cnt c' k', 1 <= c <= 31 -> 0 <= cnt < 16 -> 1 <= c' <= 31 ->
  Forall (cls_miss_body AL c' k') (push_W c cnt).
Proof.
  intros c cnt c' k' Hc Hcnt Hc'.
  pose proof (dl_geom c' Hc') as (S1 & S2 & T3 & T4 & LP03 & R1 & R2 & L0 & U0 & _).
  unfold push_W, cls_miss_body, pcl_addr, ri_addr, RIB.
  repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| left; lia]).
Qed.

#[using="Type"] Lemma firstn_upd_snoc : forall {X} (ws : list X) (n : nat) (x : X), (n < length ws)%nat ->
  firstn (S n) (upd ws n x) = firstn n ws ++ [x].
Proof.
  intros X ws n x Hn. rewrite (upd_firstn_skipn ws n x Hn).
  rewrite firstn_app, length_firstn, Nat.min_l by lia.
  replace (S n - n)%nat with 1%nat by lia. rewrite firstn_all2 by (rewrite length_firstn; lia). reflexivity.
Qed.

Definition push_prim (P : prim) (c v : Z) : prim :=
  mkPRIM (set_nth (Z.to_nat c) (push_cls (get_cls P c) v) (pr_cls P)) true (pr_calloc P - class_size c) (pr_cmapped P).

#[using="HC AO"] Theorem RPRIM_push : forall (P : prim) (m : mem) (c v : Z),
  RPRIM AL P m -> pr_inited P = true -> 1 <= c <= 31 -> p_cnt (get_cls P c) < max_count c ->
  0 <= v -> 16 * v + class_size c <= p_au (get_cls P c) -> (16 * v) mod class_size c = 0 ->
  ~ In v (p_fa (get_cls P c) ++ p_chunks (get_cls P c)) -> free_chunk AL m c v ->
  let cnt := p_cnt (get_cls P c) in
  0 <= cnt < 16 /\ prim_env AL m
  /\ rw_cells asegs m (pcl_addr AL c) [C4 (wz cnt); C4 (wz (max_count c)); C8 (wz (class_size c))]
  /\ rw_cells asegs m (THR + CSTATS_OFF + 16) [C8 (wz (pr_calloc P)); C8 (wz (pr_cmapped P))]
  /\ exists ws, u32arr asegs m (pcl_addr AL c + 16) ws /\ length ws = 16%nat
     /\ (forall m', munch (push_W c cnt) m m' -> wmono asegs m m' ->
           rw_cells asegs m' (pcl_addr AL c) [C4 (wz (cnt + 1)); C4 (wz (max_count c)); C8 (wz (class_size c))] ->
           u32arr asegs m' (pcl_addr AL c + 16) (upd ws (Z.to_nat cnt) (wz v)) ->
           rw_cells asegs m' (THR + CSTATS_OFF + 16) [C8 (wz (pr_calloc P - class_size c)); C8 (wz (pr_cmapped P))] ->
           RPRIM AL (push_prim P c v) m').
Proof.
  intros P m c v RP INI Hc LT V0 V1 V2 NI FCv. cbv zeta.
  set (k := get_cls P c) in *. set (cnt := p_cnt k) in *.
  pose proof RP as (LEN & PENV & CLS & STAT & (ts & TS)). rewrite INI in CLS.
  destruct (CLS c Hc) as (WFc & RIc & (PCc & (ws & CAc & CLc & CXc)) & FAc & TLc & FCHc). fold k in WFc, RIc, PCc, CXc, FAc, TLc, FCHc.
  pose proof WFc as (Lnf & Lcnt & CR & _ & _ & _ & AU & MUF & _ & _ & _ & _ & FB & _). fold cnt in Lcnt, CR.
  pose proof (max_count_range c Hc) as (MR & _).
  assert (CB : 0 <= cnt < 16) by lia.
  split; [exact CB|]. split; [exact PENV|]. split; [exact PCc|]. split; [exact STAT|].
  exists ws. split; [exact CAc|]. split; [exact CLc|].
  intros m' MU WM PC' CA' ST'.
  pose proof (dl_geom c Hc) as (S1 & S2 & T3 & T4 & LP03 & R1 & R2 & L0 & U0 & SHS).
  pose proof (class_size_pos c Hc) as CS.
  assert (DJ : forall A n, (A + n <= THR + 208 \/ THR + 2800 <= A) -> disjoint_from (push_W c cnt) A n)
    by (intros A n HA; unfold push_W, pcl_addr; cbn [disjoint_from]; lia).
  unfold push_prim. fold k.
  split; [cbn [pr_cls]; rewrite set_nth_length; exact LEN|].
  split.
  { unfold prim_env in *. eapply rw_cells_transport; [exact PENV| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply DJ. lia. }
  split.
  { intros c' Hc'. cbn [pr_inited]. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite get_cls_set_same by (try exact LEN; lia).
      destruct (cls_body_frame AL AO c k Hc WFc _ m m' (conj RIc (conj FAc (conj TLc FCHc))) MU WM (push_W_miss_body c cnt c k Hc CB Hc)) as (RI' & FA' & TL' & FCH').
      split; [apply push_cls_wf; assumption|].
      split; [exact RI'|]. split; [| split; [exact FA'| split; [exact TL'|]]].
      + split; [unfold push_cls; cbn [p_cnt]; exact PC'|]. exists (upd ws (Z.to_nat cnt) (wz v)). split; [exact CA'|]. split; [rewrite upd_length; exact CLc|].
        unfold push_cls. cbn [p_chunks]. rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
        replace (length (p_chunks k)) with (Z.to_nat cnt) by lia.
        rewrite firstn_upd_snoc by lia. rewrite map_app. cbn [map]. f_equal.
        replace (Z.to_nat cnt) with (length (p_chunks k)) by lia. exact CXc.
      + intros x Hx. apply push_cls_free in Hx as [Hx| ->]; [exact (FCH' x Hx)|].

        destruct FCv as [(jv & FV) FS].
        pose proof (SHS (region AL c + 16 * v) ltac:(lia)) as Y1.
        assert (Y2 : sh (region AL c + 16 * v) + class_size c / 8 <= sh (region AL c + K_REGION)).
        { pose proof (SHS (region AL c + 16 * v + class_size c) ltac:(lia)) as Y3.
          assert (sh (region AL c + 16 * v) + class_size c / 8 <= sh (region AL c + 16 * v + class_size c)) by (unfold sh; clear; Z.div_mod_to_equations; lia). lia. }
        split; [exists jv|].
        * eapply rw_cells_transport; [exact FV| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
          unfold push_W, pcl_addr. cbn [disjoint_from]. lia.
        * eapply rw_cells_transport; [exact FS| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
          unfold push_W, pcl_addr. cbn [disjoint_from]. lia.
    - assert (EO : get_cls (mkPRIM (set_nth (Z.to_nat c) (push_cls k v) (pr_cls P)) true (pr_calloc P - class_size c) (pr_cmapped P)) c' = get_cls P c').
      { unfold get_cls. cbn [pr_cls]. apply nth_set_nth_other. lia. }
      rewrite EO. destruct (CLS c' Hc') as (WFc' & _).
      apply (cls_rep_frame AL AO c' (get_cls P c') Hc' WFc' true _ m m' (CLS c' Hc') MU WM).
      pose proof (push_W_miss_body c cnt c' (get_cls P c') Hc CB Hc') as B. unfold push_W in B |- *.
      apply Forall_cons_iff in B as [B1 B2]. apply Forall_cons_iff in B2 as [B2 B3]. apply Forall_cons_iff in B3 as [B3 _].
      repeat (apply Forall_cons || apply Forall_nil); (split; [cbn [fst snd]; unfold pcl_addr; lia| assumption]). }
  split; [cbn [pr_calloc pr_cmapped]; exact ST'|].
  exists ts. eapply rw_cells_transport; [exact TS| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply DJ. lia.
Qed.
End DL.
