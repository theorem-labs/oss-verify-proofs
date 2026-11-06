(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodesC
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra AsanNodesLibE.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxNodesLibE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Noacc.
Variable segs : list Segment.

Lemma crz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  crz segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  crz segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (fun eff => mmap_fixedin_check segs ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Hce Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
    pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  pose (effs := fun i : three => match i with
                           | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | T2 => fixedin_ok_eff prot addr n
                           | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : three => match i with
                          | T1 => model
                          | T2 => fixedin_ok_model prot flags addr n model
                          | T3 => fixedin_destroyed_model addr n model end).
  assert (Herr : forall e, In e mmap_errnos -> e = ENOMEM) by (intros e [<-|[]]; reflexivity).
  assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
  assert (Hsys : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 216%Z \/ bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222%Z
                 \/ bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 226%Z) by (rewrite in_sysno_sys_input, Hno; auto).
  assert (Hnode : node_ok segs (mkCfg ms model) three (fun _ => []) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { apply (node_chk_noacc segs ms model (getr regs 17) three effs ms' Hh eq_refl).
    + intros [| |]; cbn [effs ms'].
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk, Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (Herr e He).
        destruct zs; [|discriminate]. destruct us.
        -- injection Hc as <- <-. exists T1. repeat split; reflexivity.
        -- destruct (listNN_eqb (p :: us) [(addr, n)]) eqn:Hl; [|discriminate].
           apply listNN_eqb_eq in Hl. rewrite Hl. injection Hc as <- <-. exists T3. repeat split; reflexivity.
      * destruct (Z.eqb prot 0) eqn:Ep.
        -- destruct zs; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
        -- destruct us; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + intros [| |]; cbn [ms']; [exact Hh | unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh
                              | unfold fixedin_destroyed_model; rewrite with_mmap_destroyed_halted'; cbn; exact Hh].
    + intros [| |]; cbn [effs]; unfold fixedin_ok_eff; [reflexivity | destruct (Z.eqb prot 0); reflexivity | reflexivity]. }
  apply (crz_conseq segs _ (t_alt (fun _ : unit => KB)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists tt; exact Ht]].
  eapply (crz_cases_filter segs ms model (getr regs 17) three unit _ (fun _ => T2) (fun _ => KB) tt eq_refl).
  - rewrite Hno. reflexivity.
  - exact Hnode.
  - intros [| |]; cbn [cfg_model ms']; [exact Hh | unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh
                              | unfold fixedin_destroyed_model; rewrite with_mmap_destroyed_halted'; cbn; exact Hh].
  - intros _. cbn [cfg_ms]. rewrite ms_gpr0_apply_effect, (refusal_b_enomem_arm _ _ _ Hsys). cbn [effs]. unfold fixedin_ok_eff.
    destruct (Z.eqb prot 0); cbn [eff_ret]; apply not_enomem_page_aligned; exact Hal.
  - intros [| |]; [right | left; exists tt; reflexivity | right]; cbn [cfg_ms]; rewrite ms_gpr0_apply_effect, (refusal_b_enomem_arm _ _ _ Hsys); cbn [effs eff_ret]; apply bv_eqb_refl.
  - intros _. cbn [effs ms']. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.
