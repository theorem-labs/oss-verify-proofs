(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim AsanAcct AsanAcctShape AsanPlacement BackingAlgebra MmapSim RefNodes. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import NoReserve.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanCeil. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import VmGap. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesMmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_noreplace_flags_core : forall flags,
  mmap_noreplace_flags_b flags = true ->
  mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626.
Proof.
  intros flags H. unfold mmap_noreplace_flags_b in H. apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H;
  [left|right]; exact H.
Qed.

(* [comment removed for export] *)
Lemma mmap_noreplace_flags_b_104022 : mmap_noreplace_flags_b (Z_to_bv 64 1064994) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreplace_flags_b_100022 : mmap_noreplace_flags_b (Z_to_bv 64 1048610) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreplace_flags_b_104032 : mmap_noreplace_flags_b (Z_to_bv 64 1065010) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreplace_flags_b_100032 : mmap_noreplace_flags_b (Z_to_bv 64 1048626) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104022 : mmap_noreserve_b (Z_to_bv 64 1064994) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104032 : mmap_noreserve_b (Z_to_bv 64 1065010) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_100022 : mmap_noreserve_b (Z_to_bv 64 1048610) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_100032 : mmap_noreserve_b (Z_to_bv 64 1048626) = false.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma mmap_noreserve_backed_ok_of_noreserve : forall flags m nZ,
  mmap_noreserve_b flags = true -> mmap_noreserve_backed_ok flags m nZ = true.
Proof. intros flags m nZ H. unfold mmap_noreserve_backed_ok. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_gates_noreplace : forall flags prot,
  mmap_noreplace_flags_b flags = true ->
  mmap_anon_b flags = true
  /\ mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hn.
  split.
  { destruct (mmap_noreplace_flags_core flags Hn) as [Hc|Hc];
      [exact (mmap_anon_b_of_core flags _ Hc eq_refl)|exact (mmap_anon_b_of_core flags _ Hc eq_refl)]. }
  unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b, mmap_noreplace_noaccess_b, mmap_noreplace_rw_b.
  rewrite Hn.
  destruct (mmap_noreplace_flags_core flags Hn) as [Hc|Hc]; rewrite Hc;
    repeat split; try (vm_compute; reflexivity);
    destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

Section OurSpecNodesN.
Context {fx : FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)

Lemma mmap_noreplace_rw_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> mmap_noreplace_flags_b flags = true ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hnrp H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_noreplace flags (Z_to_bv 64 3) Hnrp) as (Ga & Gm & Gn & Gfn & Gfr & _ & Gnn & Gnr).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn, Gnr. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  Ltac kill_armN zs r := first [ reflexivity | destruct zs; reflexivity
                             | match goal with |- context [errno_ret_in ?l r] =>
                                 destruct (errno_ret_in l r); first [reflexivity | destruct zs; reflexivity] end ].
  destruct us; [|kill_armN zs r].
  destruct cs; [|kill_armN zs r]. destruct ci; [|kill_armN zs r].
  unfold mmap_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_noreplace_rw1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_noreplace_flags_b flags = true ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hnrp H14 H15
         nZ n Hrf Hbk HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_noreplace_rw_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hnrp
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk. rewrite Hbk in Hchk.
  assert (Hne : errno_ret_in mmap_errnos addr = false) by (rewrite errno_ret_in_eq; apply ret_in_errnos_ENOMEM_aligned; exact Hal).
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [(addr, n)] [] [] [])))
                  (with_mmap_backing flags addr n (mmap_model addr n model)))).
  - apply (node_chk_ev_mat_mm segs ms model (getr regs 17) unit
             (fun _ => mkEffectU addr [] [(addr, n)] [] [] [])
             (fun _ => with_mmap_backing flags addr n (mmap_model addr n model)) (fun _ => []) tt Hh eq_refl
             (family_off_mmap segs ms _ Hno)).
    + intros []; rewrite Hchk.
      rewrite Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []; cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model addr Hno). exact Hne.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      { left. cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model r Hno). split; [exact Er|]. destruct zs; [|discriminate]. injection Hc as <- <-. reflexivity. }
      right.
      destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros []; rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)

Lemma mmap_noreplace_none_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags -> mmap_noreplace_flags_b flags = true ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hnrp H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_noreplace flags (Z_to_bv 64 0) Hnrp) as (Ga & Gm & Gn & Gfn & Gfr & Gnn & _ & _).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  unfold noaccess_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_noreplace_none1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_noreplace_flags_b flags = true ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hnrp H14 H15
         nZ n Hrf HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_noreplace_none_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hnrp
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  assert (Hne : errno_ret_in mmap_errnos addr = false) by (rewrite errno_ret_in_eq; apply ret_in_errnos_ENOMEM_aligned; exact Hal).
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                  (with_mmap_backing flags addr n (noaccess_model addr n model)))).
  - apply (node_chk_ev_mat_mm segs ms model (getr regs 17) unit
             (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
             (fun _ => with_mmap_backing flags addr n (noaccess_model addr n model)) (fun _ => []) tt Hh eq_refl
             (family_off_mmap segs ms _ Hno)).
    + intros []; rewrite Hchk. rewrite Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []; cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model addr Hno). exact Hne.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      { left. cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model r Hno). split; [exact Er|]. destruct us; [|discriminate]. injection Hc as <- <-. reflexivity. }
      right.
      destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros []; rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

End OurSpecNodesN.
