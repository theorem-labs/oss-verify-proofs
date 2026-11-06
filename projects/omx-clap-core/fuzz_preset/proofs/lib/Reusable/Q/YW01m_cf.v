(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: cut-free (knode_cf) twins of Q/YW01.v's knode_mremap and knode_mremap_cases. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM06_cf YO0d_cf YN02_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW01.
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

Section b.
Variable segs : list Segment.

(* The cut-free clauses of knode_cf at an mremap node. *)
Lemma kcfm_mremap_rest : forall regs pc mem rom model snap (r : nat) (ol nl : Z),
  m_halted model = None ->
  mremap_args regs model ->
  m_vm_materialized model = [] ->
  State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
  bv_unsigned (getr regs 12) <= nl ->
  ((charged (KMremap r ol nl) = true -> live_bytes snap + req_len (KMremap r ol nl) <= vml (mkCfg (pend_at regs pc mem rom) model)) ->
   ~ budget_refused_at segs (mkCfg (pend_at regs pc mem rom) model)) /\
  (forall e c2, sstep_cfg segs ACFG (mkCfg (pend_at regs pc mem rom) model) e (SNext c2) ->
   vml c2 = vml (mkCfg (pend_at regs pc mem rom) model)) /\
  ms_svc_pending (cfg_ms (mkCfg (pend_at regs pc mem rom) model)) <> None.
Proof.
intros regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl.
pose proof (ma_lazy _ _ HA) as Hlz.
split; [|split].
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
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMremap r ol nl) snap Kont.
Proof.
intros regs pc mem rom model snap r ol nl Kont Hh HA HK0 HK1 Hmat Hlb Hnl.
split; [exact (knode_mremap segs regs pc mem rom model snap r ol nl Kont Hh HA HK0 HK1)|].
exact (kcfm_mremap_rest regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl).
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
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMremap r ol nl) snap Kont.
Proof.
intros regs pc mem rom model snap r ol nl Kont Hh HA old old_n new_n HK0 HKin HKmv Hmat Hlb Hnl.
split; [exact (knode_mremap_cases segs regs pc mem rom model snap r ol nl Kont Hh HA HK0 HKin HKmv)|].
exact (kcfm_mremap_rest regs pc mem rom model snap r ol nl Hh HA Hmat Hlb Hnl).
Qed.
End b.
End a.
