(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the advised range is shown free of the reserved list through the tracked mapping it lies in, which the runtime invariant keeps apart from the vDSO pair; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/A/RT_sys_madvise.v, lines 50-57. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA NodesA_mm NodesA_madv ImageA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct BackingAlgebra.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout RT_iface D_defs RT_state RT_rep RT_facts0 RT_init RT_sys_stmt RT_sys_fixed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Theorem madvise_ok : madvise_node.
Proof.
  intros Σ PMc Pm K PB PE HPMc HPMs HL HPBal HPEal HPBE Hwin Hcov Hm.
  unfold ASTA. cbn [rt_allow ARTM RTA].
  unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hwin.
  set (len := PE - PB) in *.
  assert (Hlen : 0 < len) by (unfold len; lia).
  assert (Hlal : len mod 4096 = 0)
    by (unfold len; apply Z.mod_divide in HPBal, HPEal; try lia; apply Z.mod_divide; [lia|]; apply Z.divide_sub_r; assumption).
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (maps0_shadow _ HL) as (HE2 & HE4).
  apply (ast_madvise_dontneed_ms asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
           K (fun mo => ARTM_A Σ mo /\ PMc mo) PB len).
  - lia.
  - lia.
  - unfold page_size. exact HPBal.
  - rewrite Hrd. unfold len. lia.
  - intros p H1 H2. rewrite Hrd in H2. apply Hcov; [exact H1| unfold len in H2; lia].
  - apply mat_stable_and; [apply rta_mat_stable| exact HPMs].
  - intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4 & S5). rewrite Hrd. repeat (split; [assumption|]). exact S5.
  - intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
    rewrite Hrd. split; [|split; [exact HA| exact HPc]].
    assert (Eua : bv_unsigned (Z_to_bv 64 PB) = PB) by (apply unsigned_lit; lia).
    assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    assert (Hin : exists e, In e (vm_maps (m_vmmaps mo)) /\ bv_unsigned (fst e) <= PB /\ PB + len <= bv_unsigned (fst e) + bv_unsigned (snd e)).
    { destruct Hwin as [W|W].
      - exists (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000). split; [exact (artm_in_maps Σ mo _ HA (l_maps0_in_rt_maps Σ _ HE2))|].
        cbn [fst snd]. rewrite !unsigned_lit by lia. unfold len. lia.
      - exists (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000). split; [exact (artm_in_maps Σ mo _ HA (l_maps0_in_rt_maps Σ _ HE4))|].
        cbn [fst snd]. rewrite !unsigned_lit by lia. unfold len. lia. }
    destruct Hin as (e & He & He1 & He2).
    apply (madvise_dontneed_ok_intro _ _ _ e He); rewrite ?Eua, ?Eul; [exact He1| exact He2| |].
    (* LPS 75d69e00: [Eres] is no longer a bare equality -- the launch's vDSO pair follows
       the image's reservations in the ledger.  The range being advised lies inside the
       shadow mapping [e] that the runtime already tracks, and ARTM_A's reserved clause
       puts every tracked mapping apart from the tail, which is what carves the pair out. *)
    + apply (artm_res_free_in_maps mo _ _ _ Eres He);
        [ rewrite Eua; exact He1
        | rewrite Eua, Eul; exact He2
        | apply reserved_free_above; rewrite Eua; unfold SEGTOP_A; lia ].
    + apply region_free_noaccess_of_uncovered; [exact Hnp| rewrite Eul; exact Hlen| rewrite Eua, Eul; unfold len; lia|].
      intros a Ha. rewrite Eua, Eul in Ha.
      refine (proj2 (Hsl a _)). unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi. unfold len in Ha. lia.
Qed.

End GWIN.
