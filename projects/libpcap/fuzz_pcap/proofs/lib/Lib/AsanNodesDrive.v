(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmB AsanNodesLibE. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require StdioSymDrive. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asannodesdrive_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma grant_visible_of_hidden_mapped : forall (H : word -> bool) model (a : word) nZ,
  (forall x : word, H x = true ->
     exists r, In r (vm_maps (m_vmmaps model)) /\ bv_unsigned (fst r) <= bv_unsigned x < bv_unsigned (fst r) + bv_unsigned (snd r)) ->
  0 <= nZ -> grant_ok_na_pin model a nZ = true -> range_visible H a nZ.
Proof.
  intros H model a nZ Hhid HnZ Hg x Hx.
  destruct (grant_ok_na_pin_unpack _ _ _ Hg) as (_ & _ & Htop & Hrf).
  pose proof (alloc_top_room (m_vmmaps model)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  destruct (H x) eqn:EH; [|reflexivity]. exfalso.
  destruct (Hhid x EH) as ([b s] & Hin & Hb). cbn [fst snd] in Hb.
  pose proof (u64_range a) as Ra.
  pose proof (grant_na_disjoint_of_In model a nZ b s ltac:(lia) Hg ltac:(apply in_app_iff; right; exact Hin)) as Hd.
  lia.
Qed.

Section Drive.
Variable segs : list Segment.
Variable H : word -> bool.
Variable A : list (Z * Z).
Hypothesis HA : A_wf A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem srz_mmap_rw_pin_d : forall vals ebs sr R M rom model kn pc w (len : Z) ds KB,
  let E := Env (vals_ev vals) ebs in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  let ia := length vals in
  regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
  sr_vars_lt ia sr = true -> kn_vars_lt ia kn = true -> ds_vars_lt ia ds = true ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None ->
  edenot E (sr_get sr 17) = Z_to_bv 64 222 ->
  edenot E (sr_get sr 11) = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  edenot E (sr_get sr 12) = Z_to_bv 64 3 -> edenot E (sr_get sr 13) = Z_to_bv 64 34 ->
  edenot E (sr_get sr 14) = Z_to_bv 64 (-1) -> edenot E (sr_get sr 15) = Z_to_bv 64 0 ->
  (exists a, grant_ok_na_pin model a nZ = true) ->
  vm_backing_used model + nZ <= vm_limit (m_vmmaps model) ->
  (forall a, grant_ok_na_pin model a nZ = true -> range_visible H a nZ) ->
  dsj_claims E (fun a => grant_ok_na_pin model a nZ = true) nZ ds ->
  (forall (a : word) R2,
     grant_ok_na_pin model a nZ = true ->
     let E' := Env (vals_ev (vals ++ [a])) ebs in
     regs_ok E' (sr_upd sr (ridx 10) (EVar ia)) R2 ->
     know_ok segs E' (mrestrict H (zfill a n M))
       ([KZero (SA (EVar ia) 0) (ELit nZ); KWr (SA (EVar ia) 0) (ELit nZ);
         KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)]
        ++ dsj_entries ia nZ ds
        ++ kn_keep MGrow ([KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)]
                          ++ dsj_entries ia nZ ds ++ kn) kn (EVar ia) 0 (ELit nZ)) ->
     srealizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (zfill a n M) rom) (mmap_model a n model)) KB) ->
  srealizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) KB.
Proof.
  intros vals ebs sr R M rom model kn pc w len ds KB E nZ n ia HR HK Hsr Hkn Hds HF HE Hpc0 Hpc4 Hh
         H17 H11 Hlen H12 H13 H14 H15 Hex Hbud Hvis Hdsj HKB.
  assert (HnZ : 0 < nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
  eapply (srz_mmap_rw_pin segs R (Z_to_bv 64 pc) M rom model w len (Z_to_bv 64 34) KB HF HE Hh);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  - exact Hlen.
  - reflexivity.
  - exact Hex.
  - unfold mmap_noreserve_backed_ok. cbn. apply Z.leb_le. exact Hbud.
  - intros a Ha. rewrite pc_lit_add4 by lia.
    rewrite with_mmap_backing_eager by reflexivity.
    destruct (grant_ok_na_pin_unpack _ _ _ Ha) as (Hal & Hpos & Htop & Hrf).
    pose proof (alloc_top_room (m_vmmaps model)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
    pose proof (u64_range a) as Har.
    assert (Hev : edenot (Env (vals_ev (vals ++ [a])) ebs) (EVar ia) = a).
    { cbn [edenot ev]. unfold ia. rewrite <- (Nat.add_0_r (length vals)), vals_ev_app_r. reflexivity. }
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; lia).
    apply HKB; [exact Ha| |].
    + apply regs_ok_set; [| discriminate | exact Hev].
      apply env_app_regs; [exact Hsr | exact HR].
    + rewrite (mrestrict_zfill H a n M) by (rewrite Hun; exact (Hvis a Ha)).
      assert (KF : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) (mrestrict H M)
                    [KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)])
        by (apply kfacts_grant; try assumption; unfold stack_max_size; lia).
      assert (KD : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) (mrestrict H M) (dsj_entries ia nZ ds)).
      { apply (dsj_entries_ok segs vals ebs (mrestrict H M) _ nZ ds a ltac:(lia) ltac:(lia) Hdsj Ha).
        apply ds_vars_lt_Forall. exact Hds. }
      assert (KO' : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) (mrestrict H M) kn) by (apply env_app_know; [exact Hkn | exact HK]).
      apply (proj2 (know_ok_app segs _ _ _ _)); split; [|apply (proj2 (know_ok_app segs _ _ _ _)); split].
      * rewrite <- Hun. constructor; [apply kzero_zfill; [exact Hev | lia | lia]|].
        constructor; [apply kwr_zfill; [exact Hev | lia | lia]|].
        rewrite Hun. apply kfacts_grant; try assumption; unfold stack_max_size; lia.
      * apply (dsj_entries_ok segs vals ebs (zfill a n (mrestrict H M)) _ nZ ds a ltac:(lia) ltac:(lia) Hdsj Ha).
        apply ds_vars_lt_Forall. exact Hds.
      * apply (kn_keep_sound segs _ (mrestrict H M) (zfill a n (mrestrict H M)) MGrow).
        -- apply (proj2 (know_ok_app segs _ _ _ _)); split; [exact KF|].
           apply (proj2 (know_ok_app segs _ _ _ _)); split; [exact KD | exact KO'].
        -- exact KO'.
        -- unfold estart, elenZ. cbn [a_base a_off]. rewrite Hev. cbn [edenot]. rewrite u_small by lia.
           rewrite Z.add_0_r, <- Hun. apply mem_change_zfill.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem srz_mmap_fixedin_spin_d : forall vals ebs sr R M rom model kn pc w (addr : word) (eb : expr) (eo len flags : Z) KB,
  let E := Env (vals_ev vals) ebs in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None ->
  edenot E (sr_get sr 17) = Z_to_bv 64 222 ->
  edenot E (sr_get sr 10) = addr -> bv_unsigned (edenot E eb) + eo = bv_unsigned addr ->
  bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
  edenot E (sr_get sr 11) = Z_to_bv 64 len -> 0 < len ->
  bv_unsigned addr + nZ <= alloc_top (m_vmmaps model) ->
  edenot E (sr_get sr 12) = Z_to_bv 64 3 -> edenot E (sr_get sr 13) = Z_to_bv 64 flags ->
  mmap_flags_core (Z_to_bv 64 flags) = 50 ->
  edenot E (sr_get sr 14) = Z_to_bv 64 (-1) -> edenot E (sr_get sr 15) = Z_to_bv 64 0 ->
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) model addr n = true ->
  range_visible H addr nZ ->
  (forall R2, regs_ok E sr R2 ->
     know_ok segs E (mrestrict H (zfill addr n M))
       ([KZero (SA eb eo) (ELit nZ); KWr (SA eb eo) (ELit nZ)] ++ kn_keep MGrow kn kn eb eo (ELit nZ)) ->
     srealizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (zfill addr n M) rom)
                          (fixedin_ok_model 3 (Z_to_bv 64 flags) addr n model)) KB) ->
  srealizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) KB.
Proof.
  intros vals ebs sr R M rom model kn pc w addr eb eo len flags KB E nZ n HR HK HF HE Hpc0 Hpc4 Hh
         H17 H10 Hea Hal Hpos H11 Hlen Htop H12 H13 Hcore H14 H15 Hrf Hmc Hbud Hvis HKB.
  assert (HnZ : 0 < nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
  pose proof (u64_range addr) as Har. pose proof (alloc_top_room (m_vmmaps model)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; lia).
  eapply (srz_mmap_fixedin_spin segs R (Z_to_bv 64 pc) M rom model w 3 (Z_to_bv 64 flags) addr len KB HF HE Hh);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  - right; reflexivity.
  - exact Hcore.
  - exact Hal.
  - exact Hpos.
  - exact Hlen.
  - exact Htop.
  - exact Hrf.
  - exact Hmc.
  - intros _. exact Hbud.
  - cbn [Z.eqb]. rewrite pc_lit_add4 by lia. apply HKB.
    + apply (AsanNodesMmB.regs_ok_regupd_same E sr R _ addr HR); [| discriminate].
      exact (eq_trans (HR _) H10).
    + rewrite (mrestrict_zfill H addr n M) by (rewrite Hun; exact Hvis).
      rewrite <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | lia]|].
      apply (kn_keep_sound segs _ (mrestrict H M) (zfill addr n (mrestrict H M)) MGrow); [exact HK | exact HK|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia.
      apply mem_change_zfill.
Qed.
End Drive.
