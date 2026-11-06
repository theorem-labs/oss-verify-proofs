(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: cut-free (knode_cf) twins of Q/YW01.v's knode_mremap and knode_mremap_cases. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06 YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YW00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM06_cf YO0d_cf YN02_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YW01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import PlaceCapW YM01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require RoomShapesDraft AgreeLim Uniform PolicyFit.
From Stdlib Require Import Classical_Prop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* With empty lazy and materialized ledgers, mremap's two budget readings (the post-state of
   the in-place resolution and the destination-free move charge) are each bounded by the
   live bytes of vm_maps plus the new length. *)
Lemma kcfm_live_bytes_filter_le : forall f l, State.live_bytes (List.filter f l) <= State.live_bytes l.
Proof.
  intros f l. induction l as [|[x sz] r IH]; cbn [List.filter State.live_bytes]; [lia|].
  pose proof (bv_unsigned_in_range 64 sz). destruct (f (x, sz)); cbn [State.live_bytes]; lia.
Qed.

Lemma kcfm_map_remove_le : forall l a, State.live_bytes (map_remove l a) <= State.live_bytes l.
Proof. intros l a. unfold map_remove. apply kcfm_live_bytes_filter_le. Qed.

Lemma kcfm_next_vml : forall m old old_n dst new_n,
  vm_limit (m_vmmaps (mremap_model_next m old old_n dst new_n)) = vm_limit (m_vmmaps m).
Proof. reflexivity. Qed.

Lemma kcfm_next_backing : forall m old old_n dst new_n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used (mremap_model_next m old old_n dst new_n)
  <= bv_unsigned new_n + State.live_bytes (vm_maps (m_vmmaps m)).
Proof.
  intros m old old_n dst new_n Hl Hm. rewrite (mremap_next_with_vmmaps m old old_n dst new_n Hl Hm).
  pose proof (kcf_backing_le_maps (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n) m) Hl Hm) as Hb.
  assert (E : State.live_bytes (vm_maps (m_vmmaps (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n) m)))
              = bv_unsigned new_n + State.live_bytes (map_remove (vm_maps (m_vmmaps m)) old)) by reflexivity.
  pose proof (kcfm_map_remove_le (vm_maps (m_vmmaps m)) old). lia.
Qed.

Lemma kcfm_move_charge_le : forall m old old_n new_n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  mremap_move_charge m old old_n new_n <= bv_unsigned new_n + State.live_bytes (vm_maps (m_vmmaps m)).
Proof.
  intros m old old_n new_n Hl Hm. unfold mremap_move_charge, mremap_source_lazy_b. cbv zeta. rewrite Hl, Hm.
  cbn [map_contains existsb maps_subtract maps_subtract_all List.filter List.length Nat.add Z.of_nat Z.mul].
  pose proof (live_bytes_maps_subtract_all_le (vm_noaccess (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) old)).
  pose proof (kcfm_map_remove_le (vm_maps (m_vmmaps m)) old). lia.
Qed.

Lemma kcfm_region_free_sub : forall (l1 l2 : list (word * word)) (a n : word),
  region_free l2 a n = true -> (forall q, In q l1 -> In q l2) -> region_free l1 a n = true.
Proof.
  intros l1 l2 a n H Hs. apply State.region_free_intro. intros b sz Hin.
  exact (State.region_free_In _ _ _ _ _ H (Hs _ Hin)).
Qed.

(* A range free of the ledger is free of every range some ledger entry contains. *)
Lemma kcfm_region_free_within : forall (L N : list (word * word)) (a n : word),
  region_free L a n = true ->
  (forall e, In e N -> exists E, In E L /\ bv_unsigned (fst E) <= bv_unsigned (fst e) /\
     bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst E) + bv_unsigned (snd E)) ->
  region_free N a n = true.
Proof.
  intros L N a n Hf Hc. apply State.region_free_intro. intros b sz Hin.
  destruct (Hc (b, sz) Hin) as ([B S] & HE & H1 & H2). cbn [fst snd] in H1, H2.
  pose proof (State.region_free_In _ _ _ _ _ Hf HE) as Hov. unfold iv_overlap in *.
  apply andb_false_iff in Hov. apply andb_false_iff.
  destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; [left | right]; apply Z.ltb_ge; lia.
Qed.

Lemma kcfm_listNN_refl : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

Lemma kcfm_listCopy_refl : forall l, listCopy_eqb l l = true.
Proof. intros l. apply listCopy_eqb_eq. reflexivity. Qed.

Section b.
Variable segs : list Segment.

(* An answer below the errno range is no spurious refusal of mremap. *)
Lemma kcfm_not_spurious : forall regs pc mem rom model eff,
  mremap_args regs model -> bv_unsigned (eff_ret eff) <= two_pow_64 - 4096 ->
  ~ spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model eff.
Proof.
  intros regs pc mem rom model eff HA Hb (_ & Hr & _).
  rewrite refusal_b_216 in Hr by (rewrite si_sysno; exact (ma_sysno _ _ HA)).
  change (ret_in_errnos mremap_errnos (eff_ret eff)) with (errno_ret_in mremap_errnos (eff_ret eff)) in Hr.
  rewrite errno_ret_in_below in Hr; [discriminate Hr | reflexivity | exact Hb].
Qed.

Lemma kcfm_nx_ret : forall regs pc mem rom model (j : mremap_J segs regs pc mem rom model) eff m'',
  mremap_nx segs regs pc mem rom model j = mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) eff)) m'' ->
  eff_ret eff = eff_ret (fst (proj1_sig j)).
Proof.
  intros regs pc mem rom model j eff m'' E. unfold mremap_nx in E.
  apply (f_equal cfg_ms) in E. cbn [cfg_ms] in E.
  rewrite <- (adv_pend regs pc mem rom (fst (proj1_sig j))) in E.
  symmetry. exact (PolicyFit.ret_of_adv _ _ _ _ _ _ E).
Qed.

(* The placement policy's step at an mremap node: the old address when the policy keeps the mapping in place,
   else a fresh address the policy picks, which lps may return as the move's destination. *)
Lemma kcfm_mremap_fit : forall regs pc mem rom model snap (r : nat) (ol nl : Z),
  m_halted model = None ->
  mremap_args regs model ->
  m_vm_materialized model = [] ->
  State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
  bv_unsigned (getr regs 12) <= nl ->
  Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) <= nslots snap + KRES ->
  ivs_bytes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= live_bytes snap + 2 ^ 30 ->
  140735332483072 <= alloc_top (m_vmmaps model) ->
  (forall e, In e (vm_maps (m_vmmaps model)) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64) ->
  (forall e, In e (vm_noaccess (m_vmmaps model)) -> exists E, In E (vm_maps (m_vmmaps model)) /\
     bv_unsigned (fst E) <= bv_unsigned (fst e) /\
     bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst E) + bv_unsigned (snd E)) ->
  (charged (KMremap r ol nl) = true ->
     live_bytes snap + req_len (KMremap r ol nl) <= vml (mkCfg (pend_at regs pc mem rom) model)) ->
  (slotted (KMremap r ol nl) = true -> vml (mkCfg (pend_at regs pc mem rom) model) <= AgreeLim.LIM_AG ->
     slot_room (vml (mkCfg (pend_at regs pc mem rom) model)) snap (KMremap r ol nl)) ->
  Uniform.canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof.
intros regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl Hcnt Hbyt Hceil H64 Hna Hroom Hslot
  p s st Hp Hst Hlim x8 len _ _.
cbn [cfg_model] in Hst, Hlim.
specialize (Hroom eq_refl). cbn [req_len] in Hroom. unfold vml in Hroom. cbn [cfg_model] in Hroom.
pose proof (ma_lazy _ _ HA) as Hlz. pose proof (ma_sysno _ _ HA) as Hno.
pose proof (ma_ceiling _ _ HA) as Hce. pose proof (ma_neq _ _ HA) as Hne.
pose proof (ma_oldn_pos _ _ HA) as Hop. pose proof (ma_newn_pos _ _ HA) as Hnp.
destruct (page_align_is0_b_false (getr regs 12) Hnp (ma_newn_al _ _ HA)) as [_ Hr2].
destruct (page_align_is0_b_false (getr regs 11) Hop (ma_oldn_al _ _ HA)) as [_ Hr1].
pose proof (alloc_top_lt63 (m_vmmaps model)) as Hat. pose proof stack_max_size_val as Hsm.
pose proof (u64_range (getr regs 10)) as U10. pose proof (u64_range (getr regs 11)) as U11.
pose proof (u64_range (getr regs 12)) as U12.
destruct (node_mremap segs regs pc mem rom model Hh HA) as [Hs _].
destruct (classic (RoomShapesDraft.mremap_in_place p s (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model))
  as [Hin | Hnin].
- (* in place: lps's in-place answer is a step of the node *)
  pose proof Hin as ((eff & m' & evs & Hsp & Hret) & _).
  apply check_syscall_ok_iff in Hsp. rewrite (mremap_chk segs regs pc mem rom model eff HA) in Hsp.
  pose proof (mremap_chk_events _ _ _ _ _ _ _ Hsp) as E. subst evs.
  assert (Hns : ~ spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model eff).
  { apply kcfm_not_spurious; [exact HA|]. rewrite Hret, si_arg0. unfold two_pow_64. lia. }
  apply (PolicyFit.canon_step_of_sstep segs p s st regs pc mem rom model _ _ (Hs (exist _ (eff, m') (conj Hsp Hns))));
    [reflexivity|].
  intros eff0 m'' E. rewrite (kcfm_nx_ret _ _ _ _ _ _ eff0 m'' E). cbn [proj1_sig fst].
  right. right. left. split; [rewrite si_sysno; exact Hno|].
  left. split; [exact Hret | exact Hin].
- assert (Herr0 : errno_ret_in mremap_errnos (getr regs 10) = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64. lia. }
  destruct (Z.lt_total (bv_unsigned (getr regs 12)) (bv_unsigned (getr regs 11))) as [Hlt | [Heq | Hgt]];
    [| exfalso; exact (Hne (eq_sym Heq)) |].
  + (* a shrink is always in place *)
    exfalso. apply Hnin. split.
    * exists (mkEffectU (getr regs 10) [] []
        [(bv_add (getr regs 10) (getr regs 12), Z_to_bv 64 (bv_unsigned (getr regs 11) - bv_unsigned (getr regs 12)))] [] []),
        (mremap_model_next model (getr regs 10) (getr regs 11) (getr regs 10) (getr regs 12)), [].
      split; [|rewrite si_arg0; reflexivity].
      apply check_syscall_ok_iff. rewrite (mremap_chk segs regs pc mem rom model _ HA).
      cbv beta iota zeta delta [mremap_chk_body].
      rewrite Herr0, bv_eqb_refl, (proj2 (Z.ltb_lt _ _) Hlt), !kcfm_listNN_refl, kcfm_listCopy_refl.
      reflexivity.
    * left. rewrite si_arg2, si_arg1, Hr2, Hr1. lia.
  + (* a grow the policy does not keep in place moves to the policy's fresh address *)
    destruct (Hslot eq_refl Hlim) as (Hlv & Hsl & Hrq). cbn [req_len] in Hsl, Hrq.
    change (vml (mkCfg (pend_at regs pc mem rom) model)) with (vm_limit (m_vmmaps model)) in Hlv.
    assert (Hw : PolicyFit.win_room (m_vmmaps model) p st (bv_unsigned (getr regs 12))).
    { apply (win_room_of_slots _ p st (bv_unsigned (getr regs 12)) (nslots snap + KRES) (live_bytes snap + 2 ^ 30)
        Hp Hst Hceil Hcnt Hbyt).
      - lia.
      - lia.
      - exact Hr2.
      - pose proof (slot_capW_anti (bv_unsigned (getr regs 12)) nl ltac:(lia)). lia. }
    destruct (PolicyFit.policy_fresh_exists (m_vmmaps model) p s st (bv_unsigned (getr regs 12)) Hp Hnp Hw)
      as (a & Hfa & F1 & F2 & F3 & F4).
    rewrite Z_to_bv_bv_unsigned in F4.
    pose proof (u64_range a) as Ua.
    assert (Hold : In (getr regs 10, getr regs 11) (vm_maps (m_vmmaps model))).
    { pose proof (ma_has _ _ HA) as Hhas. unfold map_has in Hhas. apply existsb_exists in Hhas.
      destruct Hhas as ([a0 s0] & Hin0 & Hp0). apply andb_prop in Hp0 as [Ha0 Hs0].
      apply bv_eqb_eq in Ha0. apply bv_eqb_eq in Hs0. cbn [fst snd] in Ha0, Hs0. subst a0 s0. exact Hin0. }
    pose proof (State.region_free_In _ _ _ _ _ F4 (in_or_app _ _ _ (or_intror Hold))) as Hov.
    unfold iv_overlap in Hov. apply andb_false_iff in Hov.
    assert (Hao : a <> getr regs 10) by (intros ->; destruct Hov as [Hc | Hc]; apply Z.ltb_ge in Hc; lia).
    assert (Hmaps : region_free (vm_maps (m_vmmaps model)) a (getr regs 12) = true).
    { apply (kcfm_region_free_sub _ _ _ _ F4). intros q Hq. apply in_or_app. right. exact Hq. }
    assert (Hfin : mremap_final_budget_b model (getr regs 10) (getr regs 11) a (getr regs 12) = true).
    { unfold mremap_final_budget_b, vm_backing_within_limit. apply Z.leb_le. rewrite kcfm_next_vml.
      rewrite (mremap_move_charge_at_fresh model (getr regs 10) (getr regs 11) a (getr regs 12) F1 (ma_newn_al _ _ HA) Hnp).
      - pose proof (kcfm_move_charge_le model (getr regs 10) (getr regs 11) (getr regs 12) Hlz Hmat). lia.
      - unfold two_pow_64. lia.
      - intros a0 sz0 Hin0. unfold map_remove in Hin0. apply filter_In in Hin0 as [Hin0 _].
        exact (H64 (a0, sz0) Hin0).
      - apply (kcfm_region_free_sub _ _ _ _ Hmaps). intros q Hq. unfold map_remove in Hq.
        apply filter_In in Hq. exact (proj1 Hq).
      - exact (kcfm_region_free_within _ _ _ _ Hmaps Hna).
      - rewrite Hlz. reflexivity.
      - rewrite Hmat. reflexivity. }
    assert (Hfr : mremap_fresh_b model (bv_unsigned (getr regs 11)) (bv_unsigned (getr regs 12))
                    (getr regs 10) (getr regs 11) a (getr regs 12) = true).
    { unfold mremap_fresh_b. cbv zeta. rewrite (bv_eqb_neq a (getr regs 10) Hao), F4, Hfin.
      rewrite (proj2 (Z.eqb_eq _ _) F1), (proj2 (Z.ltb_lt _ _) F2), (proj2 (Z.leb_le _ _) F3). reflexivity. }
    assert (Herr : errno_ret_in mremap_errnos a = false).
    { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64. lia. }
    assert (Hk : mremap_chk_body (getr regs 10) (getr regs 11) (getr regs 12) model
        (mkEffectU a [] (mremap_tail a (getr regs 11) (bv_unsigned (getr regs 11)) (bv_unsigned (getr regs 12)))
           [(getr regs 10, getr regs 11)] [mkCopy (getr regs 10) a (getr regs 11)] [])
        = CheckOk (mremap_model_next model (getr regs 10) (getr regs 11) a (getr regs 12)) []).
    { cbv beta iota zeta delta [mremap_chk_body].
      rewrite Herr, (bv_eqb_neq a (getr regs 10) Hao), (proj2 (Z.ltb_lt _ _) Hgt), Hfr.
      rewrite !kcfm_listNN_refl, kcfm_listCopy_refl. reflexivity. }
    assert (Hns : ~ spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model
        (mkEffectU a [] (mremap_tail a (getr regs 11) (bv_unsigned (getr regs 11)) (bv_unsigned (getr regs 12)))
           [(getr regs 10, getr regs 11)] [mkCopy (getr regs 10) a (getr regs 11)] [])).
    { apply kcfm_not_spurious; [exact HA|]. cbn [eff_ret]. unfold two_pow_64. lia. }
    apply (PolicyFit.canon_step_of_sstep segs p s st regs pc mem rom model _ _ (Hs (exist _ (_, _) (conj Hk Hns))));
      [reflexivity|].
    intros eff0 m'' E. rewrite (kcfm_nx_ret _ _ _ _ _ _ eff0 m'' E). cbn [proj1_sig fst eff_ret].
    right. right. left. split; [rewrite si_sysno; exact Hno|].
    right. split; [exact Hnin|]. rewrite si_arg2, Hr2. exact Hfa.
Qed.

(* The cut-free clauses of knode_cf at an mremap node. *)
Lemma kcfm_mremap_rest : forall regs pc mem rom model snap (r : nat) (ol nl : Z),
  m_halted model = None ->
  mremap_args regs model ->
  m_vm_materialized model = [] ->
  State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
  bv_unsigned (getr regs 12) <= nl ->
  Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) <= nslots snap + KRES ->
  ivs_bytes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= live_bytes snap + 2 ^ 30 ->
  140735332483072 <= alloc_top (m_vmmaps model) ->
  (forall e, In e (vm_maps (m_vmmaps model)) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64) ->
  (forall e, In e (vm_noaccess (m_vmmaps model)) -> exists E, In E (vm_maps (m_vmmaps model)) /\
     bv_unsigned (fst E) <= bv_unsigned (fst e) /\
     bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst E) + bv_unsigned (snd E)) ->
  ((charged (KMremap r ol nl) = true -> live_bytes snap + req_len (KMremap r ol nl) <= vml (mkCfg (pend_at regs pc mem rom) model)) ->
   ~ budget_refused_at segs (mkCfg (pend_at regs pc mem rom) model)) /\
  (forall e c2, sstep_cfg segs ACFG (mkCfg (pend_at regs pc mem rom) model) e (SNext c2) ->
   vml c2 = vml (mkCfg (pend_at regs pc mem rom) model)) /\
  ms_svc_pending (cfg_ms (mkCfg (pend_at regs pc mem rom) model)) <> None /\
  ((charged (KMremap r ol nl) = true -> live_bytes snap + req_len (KMremap r ol nl) <= vml (mkCfg (pend_at regs pc mem rom) model)) ->
   (slotted (KMremap r ol nl) = true -> vml (mkCfg (pend_at regs pc mem rom) model) <= AgreeLim.LIM_AG ->
    slot_room (vml (mkCfg (pend_at regs pc mem rom) model)) snap (KMremap r ol nl)) ->
   Uniform.canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model)).
Proof.
intros regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl Hcnt Hbyt Hceil H64 Hna.
pose proof (ma_lazy _ _ HA) as Hlz.
split; [|split; [|split]].
- intros Hroom. specialize (Hroom eq_refl). cbn [req_len] in Hroom. unfold vml in Hroom. cbn [cfg_model] in Hroom.
  apply (kcf_not_refused segs (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hsp. apply check_syscall_ok_iff in Hsp.
    rewrite (mremap_chk segs regs pc mem rom model eff HA) in Hsp.
    pose proof (mremap_chk_events _ _ _ _ _ _ _ Hsp) as ->.
    exact (proj2 (mremap_ok_model _ _ _ _ _ _ (ma_neq _ _ HA) Hsp) Hlz).
  + assert (Hfin : mremap_final_budget_b model (getr regs 10) (getr regs 11) (getr regs 10) (getr regs 12) = true).
    { unfold mremap_final_budget_b, vm_backing_within_limit. apply Z.leb_le. rewrite kcfm_next_vml.
      pose proof (kcfm_next_backing model (getr regs 10) (getr regs 11) (getr regs 10) (getr regs 12) Hlz Hmat). lia. }
    assert (Hmove : mremap_move_budget_b model (getr regs 10) (getr regs 11) (getr regs 12) = true).
    { unfold mremap_move_budget_b. apply Z.leb_le.
      pose proof (kcfm_move_charge_le model (getr regs 10) (getr regs 11) (getr regs 12) Hlz Hmat). lia. }
    unfold alloc_budget_refused_b. cbv zeta. rewrite si_sysno, (ma_sysno _ _ HA). cbn [Z.eqb Pos.eqb].
    rewrite si_arg0, si_arg1, si_arg2, si_arg3.
    unfold mremap_budget_refused_b. cbv zeta.
    rewrite (ma_flags _ _ HA). change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite MREMAP_MAYMOVE_val.
    cbn [Z.eqb Pos.eqb negb].
    rewrite (proj2 (Z.eqb_eq _ _) (ma_old_al _ _ HA)). cbn [negb].
    destruct (page_align_is0_b_false (getr regs 12) (ma_newn_pos _ _ HA) (ma_newn_al _ _ HA)) as [-> Hr2].
    destruct (page_align_is0_b_false (getr regs 11) (ma_oldn_pos _ _ HA) (ma_oldn_al _ _ HA)) as [-> Hr1].
    rewrite Hr1, Hr2, !Z_to_bv_bv_unsigned, Hfin, Hmove. cbn [andb negb].
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
- apply (kcf_vml_node segs _ _ _ _ (node_mremap segs regs pc mem rom model Hh HA)).
  intros [[eff m'] [Hk Hns]]. unfold vml, mremap_nx. cbn [proj1_sig fst snd cfg_model].
  destruct (mremap_ok_cases _ _ _ model eff m' (ma_neq _ _ HA) Hk)
  as [(e & _ & _ & ->) | (_ & [(_ & _ & ->) | [(_ & _ & _ & ->) | (dst & _ & _ & _ & _ & ->)]])];
  reflexivity.
- cbn [cfg_ms pend_at]. discriminate.
- exact (kcfm_mremap_fit regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl Hcnt Hbyt Hceil H64 Hna).
Qed.

Lemma knode_cf_mremap : forall regs pc mem rom model snap (r : nat) (ol nl : Z) (Kont : Z -> config -> Prop),
m_halted model = None ->
mremap_args regs model ->
(forall e, In e mremap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall eff m',
mremap_chk_body (getr regs 10) (getr regs 11) (getr regs 12) model eff = CheckOk m' [] ->
errno_ret_in mremap_errnos (eff_ret eff) = false ->
Kont 1 (mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4) (effmem mem eff) rom) m')) ->
m_vm_materialized model = [] ->
State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
bv_unsigned (getr regs 12) <= nl ->
Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) <= nslots snap + KRES ->
ivs_bytes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= live_bytes snap + 2 ^ 30 ->
140735332483072 <= alloc_top (m_vmmaps model) ->
(forall e, In e (vm_maps (m_vmmaps model)) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64) ->
(forall e, In e (vm_noaccess (m_vmmaps model)) -> exists E, In E (vm_maps (m_vmmaps model)) /\
bv_unsigned (fst E) <= bv_unsigned (fst e) /\
bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst E) + bv_unsigned (snd E)) ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMremap r ol nl) snap Kont.
Proof.
intros regs pc mem rom model snap r ol nl Kont Hh HA HK0 HK1 Hmat Hlb Hnl Hcnt Hbyt Hceil H64 Hna.
split; [exact (knode_mremap segs regs pc mem rom model snap r ol nl Kont Hh HA HK0 HK1)|].
exact (kcfm_mremap_rest regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl Hcnt Hbyt Hceil H64 Hna).
Qed.

Lemma knode_cf_mremap_cases : forall regs pc mem rom model snap (r : nat) (ol nl : Z) (Kont : Z -> config -> Prop),
m_halted model = None ->
mremap_args regs model ->
let old := getr regs 10 in let old_n := getr regs 11 in let new_n := getr regs 12 in
(forall e, In e mremap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall mem',
mremap_post_mem mem mem' (bv_unsigned old) (bv_unsigned old_n) (bv_unsigned old) (bv_unsigned new_n) ->
bv_unsigned old + bv_unsigned new_n <= alloc_top (m_vmmaps model) ->
region_free (vm_reserved (m_vmmaps model) ++ map_remove (vm_maps (m_vmmaps model)) old) old new_n = true
\/ bv_unsigned new_n < bv_unsigned old_n ->
Kont 1 (mkCfg (mkst (regupd regs 10 old) (v_addi pc 4) mem' rom)
(mremap_model_next model old old_n old new_n))) ->
(forall dst mem',
bv_unsigned old_n < bv_unsigned new_n ->
mremap_fresh_b model (bv_unsigned old_n) (bv_unsigned new_n) old old_n dst new_n = true ->
mremap_post_mem mem mem' (bv_unsigned old) (bv_unsigned old_n) (bv_unsigned dst) (bv_unsigned new_n) ->
Kont 1 (mkCfg (mkst (regupd regs 10 dst) (v_addi pc 4) mem' rom)
(mremap_model_next model old old_n dst new_n))) ->
m_vm_materialized model = [] ->
State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
bv_unsigned (getr regs 12) <= nl ->
Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) <= nslots snap + KRES ->
ivs_bytes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= live_bytes snap + 2 ^ 30 ->
140735332483072 <= alloc_top (m_vmmaps model) ->
(forall e, In e (vm_maps (m_vmmaps model)) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64) ->
(forall e, In e (vm_noaccess (m_vmmaps model)) -> exists E, In E (vm_maps (m_vmmaps model)) /\
bv_unsigned (fst E) <= bv_unsigned (fst e) /\
bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst E) + bv_unsigned (snd E)) ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMremap r ol nl) snap Kont.
Proof.
intros regs pc mem rom model snap r ol nl Kont Hh HA old old_n new_n HK0 HKin HKmv Hmat Hlb Hnl Hcnt Hbyt Hceil H64 Hna.
split; [exact (knode_mremap_cases segs regs pc mem rom model snap r ol nl Kont Hh HA HK0 HKin HKmv)|].
exact (kcfm_mremap_rest regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl Hcnt Hbyt Hceil H64 Hna).
Qed.
End b.
End a.
