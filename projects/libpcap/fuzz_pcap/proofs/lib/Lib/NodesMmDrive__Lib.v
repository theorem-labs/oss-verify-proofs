(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk MmapSim AllocSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module NodesMmDrive.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require StdioSymDrive. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance nodesmmdrive_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pc_lit_add4 : forall pc, 0 <= pc -> pc + 4 < 2 ^ 64 ->
  v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof. intros. apply v_addi_pc4; assumption. Qed.

Lemma getr_of_sr : forall E sr R (r : reg) (w : word),
  regs_ok E sr R -> edenot E (sr_get sr r) = w -> getr R r = w.
Proof. intros E sr R r w HR He. rewrite (HR r). exact He. Qed.

(* [comment removed for export] *)
Definition dsj_claims (E : env) (P : word -> Prop) (nZ : Z) (ds : list (saddr * expr)) : Prop :=
  Forall (fun d => forall a : word, P a ->
            bv_unsigned a + nZ <= estart E (fst d) \/ estart E (fst d) + elenZ E (snd d) <= bv_unsigned a) ds.

Definition dsj_entries (ia : nat) (nZ : Z) (ds : list (saddr * expr)) : list kentry :=
  map (fun d => KDisj (SA (EVar ia) 0) (ELit nZ) (fst d) (snd d)) ds.

Lemma dsj_entries_ok : forall segs vals ebs M P nZ ds (a : word),
  let E := Env (vals_ev vals) ebs in
  let E' := Env (vals_ev (vals ++ [a])) ebs in
  0 <= nZ -> bv_unsigned a + nZ < 2 ^ 64 ->
  dsj_claims E P nZ ds -> P a ->
  Forall (fun d => saddr_vars_lt (length vals) (fst d) = true /\ expr_vars_lt (length vals) (snd d) = true) ds ->
  know_ok segs E' M (dsj_entries (length vals) nZ ds).
Proof.
  intros segs vals ebs M P nZ ds a E E' HnZ Hnw Hds Ha Hlt.
  unfold dsj_entries. unfold dsj_claims in Hds.
  induction ds as [|[r l] ds IH]; [constructor|].
  apply Forall_cons_iff in Hds as [Hd Hds]. apply Forall_cons_iff in Hlt as [[Hr Hl] Hlt].
  cbn [map fst snd] in *. constructor; [|apply IH; assumption].
  specialize (Hd a Ha).
  cbn [kentry_ok]. unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
  unfold E'. cbn [ev].
  rewrite <- (Nat.add_0_r (length vals)), vals_ev_app_r. cbn [vals_ev nth].
  rewrite u_small by (pose proof (u64_range a); lia).
  subst E.
  rewrite <- (env_app_edenot vals [a] ebs (a_base r)) in Hd by (destruct r; exact Hr).
  rewrite <- (env_app_edenot vals [a] ebs l) in Hd by exact Hl.
  lia.
Qed.

Definition ds_vars_lt (b : nat) (ds : list (saddr * expr)) : bool :=
  forallb (fun d => saddr_vars_lt b (fst d) && expr_vars_lt b (snd d)) ds.

Lemma ds_vars_lt_Forall : forall b ds, ds_vars_lt b ds = true ->
  Forall (fun d => saddr_vars_lt b (fst d) = true /\ expr_vars_lt b (snd d) = true) ds.
Proof.
  intros b ds H. unfold ds_vars_lt in H. apply Forall_forall. intros d Hd.
  pose proof (proj1 (forallb_forall _ _) H d Hd) as Hb. apply andb_prop in Hb. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma grant_disjoint_of_In : forall hint m a nZ (b s : word),
  0 <= nZ < 2 ^ 64 ->
  grant_ok hint m a nZ = true ->
  In (b, s) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  bv_unsigned a + nZ <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a.
Proof.
  intros hint m a nZ b s HnZ Hg Hin.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & _ & Hrf & _).
  pose proof (region_free_In _ _ _ b s Hrf Hin) as H. rewrite u_small in H by lia. exact H.
Qed.

Lemma grant_below_alloc_top : forall hint m a nZ,
  grant_ok hint m a nZ = true -> bv_unsigned a + nZ <= alloc_top (m_vmmaps m).
Proof. intros hint m a nZ Hg. destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & H & _). exact H. Qed.

Lemma grant_na_disjoint_of_In : forall m a nZ (b s : word),
  0 <= nZ < 2 ^ 64 ->
  grant_ok_na_pin m a nZ = true ->
  In (b, s) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  bv_unsigned a + nZ <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a.
Proof.
  intros m a nZ b s HnZ Hg Hin.
  destruct (grant_ok_na_pin_unpack _ _ _ Hg) as (_ & _ & _ & Hrf).
  pose proof (region_free_In _ _ _ b s Hrf Hin) as H. rewrite u_small in H by lia. exact H.
Qed.

Lemma grant_na_below_alloc_top : forall m a nZ,
  grant_ok_na_pin m a nZ = true -> bv_unsigned a + nZ <= alloc_top (m_vmmaps m).
Proof. intros m a nZ Hg. destruct (grant_ok_na_pin_unpack _ _ _ Hg) as (_ & _ & H & _). exact H. Qed.

(* [comment removed for export] *)
Lemma kfacts_grant : forall segs vals ebs M (a : word) nZ,
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + nZ <= 2 ^ 64 - stack_max_size -> 0 <= nZ ->
  know_ok segs (Env (vals_ev (vals ++ [a])) ebs) M
    [KAlign (EVar (length vals)) 4096; KRange (EVar (length vals)) 4096 (2 ^ 64 - stack_max_size - nZ)].
Proof.
  intros segs vals ebs M a nZ Hal Hpos Htop HnZ.
  assert (Hev : edenot (Env (vals_ev (vals ++ [a])) ebs) (EVar (length vals)) = a).
  { cbn [edenot ev]. rewrite <- (Nat.add_0_r (length vals)), vals_ev_app_r. reflexivity. }
  unfold page_size in Hal.
  constructor; [apply kalign_intro; [lia | rewrite Hev; exact Hal]|].
  constructor; [apply krange_intro; rewrite Hev|constructor].
  split; [|lia].
  (* [comment removed for export] *)
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as Hdm. rewrite Hal, Z.add_0_r in Hdm.
  assert (1 <= bv_unsigned a / 4096) by (apply Z.div_le_lower_bound; lia || nia). nia.
Qed.

Section Drive.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem rz_mmap_anon_d : forall vals ebs sr R M rom model kn pc w (len : Z) ds KB,
  let E := Env (vals_ev vals) ebs in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  let ia := length vals in
  regs_ok E sr R -> know_ok segs E M kn ->
  sr_vars_lt ia sr = true -> kn_vars_lt ia kn = true -> ds_vars_lt ia ds = true ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 222 ->
  edenot E (sr_get sr 11) = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  edenot E (sr_get sr 12) = Z_to_bv 64 3 -> edenot E (sr_get sr 13) = Z_to_bv 64 34 ->
  edenot E (sr_get sr 14) = Z_to_bv 64 (-1) -> edenot E (sr_get sr 15) = Z_to_bv 64 0 ->
  (exists a, grant_ok (getr R 10) model a nZ = true) ->
  dsj_claims E (fun a => grant_ok (getr R 10) model a nZ = true) nZ ds ->
  (forall (a : word) R2,
     grant_ok (getr R 10) model a nZ = true ->
     let E' := Env (vals_ev (vals ++ [a])) ebs in
     regs_ok E' (sr_upd sr (ridx 10) (EVar ia)) R2 ->
     know_ok segs E' (zfill a n M)
       ([KZero (SA (EVar ia) 0) (ELit nZ); KWr (SA (EVar ia) 0) (ELit nZ);
         KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)]
        ++ dsj_entries ia nZ ds
        ++ kn_keep MGrow ([KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)]
                          ++ dsj_entries ia nZ ds ++ kn) kn (EVar ia) 0 (ELit nZ)) ->
     realizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (zfill a n M) rom) (mmap_model a n model)) KB) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) KB.
Proof.
  intros vals ebs sr R M rom model kn pc w len ds KB E nZ n ia HR HK Hsr Hkn Hds HF HE Hpc0 Hpc4 Hh Hlazy
         H17 H11 Hlen H12 H13 H14 H15 Hex Hdsj HKB.
  assert (HnZ : 0 < nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
  eapply (rz_mmap_anon segs R (Z_to_bv 64 pc) M rom model w len KB HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  - exact Hlen.
  - exact Hex.
  - intros a Ha. rewrite pc_lit_add4 by lia.
    destruct (grant_ok_unpack _ _ _ _ Ha) as (Hal & Hpos & Htop & Hrf & Hbud).
    pose proof (alloc_top_room (m_vmmaps model)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
    pose proof (u64_range a) as Har.
    assert (Hev : edenot (Env (vals_ev (vals ++ [a])) ebs) (EVar ia) = a).
    { cbn [edenot ev]. unfold ia. rewrite <- (Nat.add_0_r (length vals)), vals_ev_app_r. reflexivity. }
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; lia).
    apply HKB; [exact Ha| |].
    + apply regs_ok_set; [| discriminate | exact Hev].
      apply env_app_regs; [exact Hsr | exact HR].
    + assert (KF : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) M
                    [KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)])
        by (apply kfacts_grant; try assumption; unfold stack_max_size; lia).
      assert (KD : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) M (dsj_entries ia nZ ds)).
      { apply (dsj_entries_ok segs vals ebs M _ nZ ds a ltac:(lia) ltac:(lia) Hdsj Ha).
        apply ds_vars_lt_Forall. exact Hds. }
      assert (KO' : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) M kn) by (apply env_app_know; [exact Hkn | exact HK]).
      apply (proj2 (know_ok_app segs _ _ _ _)); split; [|apply (proj2 (know_ok_app segs _ _ _ _)); split].
      * rewrite <- Hun. constructor; [apply kzero_zfill; [exact Hev | lia | lia]|].
        constructor; [apply kwr_zfill; [exact Hev | lia | lia]|].
        rewrite Hun. apply kfacts_grant; try assumption; unfold stack_max_size; lia.
      * apply (dsj_entries_ok segs vals ebs (zfill a n M) _ nZ ds a ltac:(lia) ltac:(lia) Hdsj Ha).
        apply ds_vars_lt_Forall. exact Hds.
      * apply (kn_keep_sound segs _ M (zfill a n M) MGrow).
        -- apply (proj2 (know_ok_app segs _ _ _ _)); split; [exact KF|].
           apply (proj2 (know_ok_app segs _ _ _ _)); split; [exact KD | exact KO'].
        -- exact KO'.
        -- unfold estart, elenZ. cbn [a_base a_off]. rewrite Hev. cbn [edenot]. rewrite u_small by lia.
           rewrite Z.add_0_r, <- Hun. apply mem_change_zfill.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem rz_mmap_noaccess_d : forall vals ebs sr R M rom model kn pc w (len : Z) ds KB,
  let E := Env (vals_ev vals) ebs in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  let ia := length vals in
  regs_ok E sr R -> know_ok segs E M kn ->
  sr_vars_lt ia sr = true -> kn_vars_lt ia kn = true -> ds_vars_lt ia ds = true ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 222 ->
  edenot E (sr_get sr 11) = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  edenot E (sr_get sr 12) = Z_to_bv 64 0 -> edenot E (sr_get sr 13) = Z_to_bv 64 34 ->
  edenot E (sr_get sr 14) = Z_to_bv 64 (-1) -> edenot E (sr_get sr 15) = Z_to_bv 64 0 ->
  (exists a, grant_ok_na_pin model a nZ = true) ->
  dsj_claims E (fun a => grant_ok_na_pin model a nZ = true) nZ ds ->
  (forall (a : word) R2,
     grant_ok_na_pin model a nZ = true ->
     let E' := Env (vals_ev (vals ++ [a])) ebs in
     regs_ok E' (sr_upd sr (ridx 10) (EVar ia)) R2 ->
     know_ok segs E' (unfill a n M)
       ([KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)]
        ++ dsj_entries ia nZ ds
        ++ kn_keep MUnmap ([KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)]
                           ++ dsj_entries ia nZ ds ++ kn) kn (EVar ia) 0 (ELit nZ)) ->
     realizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (unfill a n M) rom) (noaccess_model a n model)) KB) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) KB.
Proof.
  intros vals ebs sr R M rom model kn pc w len ds KB E nZ n ia HR HK Hsr Hkn Hds HF HE Hpc0 Hpc4 Hh Hlazy
         H17 H11 Hlen H12 H13 H14 H15 Hex Hdsj HKB.
  assert (HnZ : 0 < nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
  eapply (rz_mmap_noaccess segs R (Z_to_bv 64 pc) M rom model w len KB HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  - exact Hlen.
  - exact Hex.
  - intros a Ha. rewrite pc_lit_add4 by lia.
    destruct (grant_ok_na_pin_unpack _ _ _ Ha) as (Hal & Hpos & Htop & Hrf).
    pose proof (alloc_top_room (m_vmmaps model)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
    pose proof (u64_range a) as Har.
    assert (Hev : edenot (Env (vals_ev (vals ++ [a])) ebs) (EVar ia) = a).
    { cbn [edenot ev]. unfold ia. rewrite <- (Nat.add_0_r (length vals)), vals_ev_app_r. reflexivity. }
    assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; lia).
    apply HKB; [exact Ha| |].
    + apply regs_ok_set; [| discriminate | exact Hev].
      apply env_app_regs; [exact Hsr | exact HR].
    + assert (KF : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) M
                    [KAlign (EVar ia) 4096; KRange (EVar ia) 4096 (2 ^ 64 - stack_max_size - nZ)])
        by (apply kfacts_grant; try assumption; unfold stack_max_size; lia).
      assert (KD : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) M (dsj_entries ia nZ ds)).
      { apply (dsj_entries_ok segs vals ebs M _ nZ ds a ltac:(lia) ltac:(lia) Hdsj Ha).
        apply ds_vars_lt_Forall. exact Hds. }
      assert (KO' : know_ok segs (Env (vals_ev (vals ++ [a])) ebs) M kn) by (apply env_app_know; [exact Hkn | exact HK]).
      apply (proj2 (know_ok_app segs _ _ _ _)); split; [|apply (proj2 (know_ok_app segs _ _ _ _)); split].
      * apply kfacts_grant; try assumption; unfold stack_max_size; lia.
      * apply (dsj_entries_ok segs vals ebs (unfill a n M) _ nZ ds a ltac:(lia) ltac:(lia) Hdsj Ha).
        apply ds_vars_lt_Forall. exact Hds.
      * apply (kn_keep_sound segs _ M (unfill a n M) MUnmap).
        -- apply (proj2 (know_ok_app segs _ _ _ _)); split; [exact KF|].
           apply (proj2 (know_ok_app segs _ _ _ _)); split; [exact KD | exact KO'].
        -- exact KO'.
        -- unfold estart, elenZ. cbn [a_base a_off]. rewrite Hev. cbn [edenot]. rewrite u_small by lia.
           rewrite Z.add_0_r, <- Hun. apply mem_change_unfill.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem rz_mprotect_lit_d : forall vals ebs sr R M rom model kn pc w (addr : word) (eb : expr) (eo len : Z) KA KB,
  let E := Env (vals_ev vals) ebs in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  regs_ok E sr R -> know_ok segs E M kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 226 ->
  edenot E (sr_get sr 10) = addr -> bv_unsigned (edenot E eb) + eo = bv_unsigned addr ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  edenot E (sr_get sr 11) = Z_to_bv 64 len -> 0 < len ->
  (bv_unsigned addr + nZ < two_pow_64)%Z ->
  edenot E (sr_get sr 12) = Z_to_bv 64 3 ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (forall R1, mprotect_budget_ok model addr n = false ->
     regs_ok E (sr_upd sr (ridx 10) (ELit (2 ^ 64 - 12))) R1 ->
     know_ok segs E M kn ->
     realizes segs (mkCfg (mkst R1 (Z_to_bv 64 (pc + 4)) M rom) model) KA) ->
  (forall R2, mprotect_budget_ok model addr n = true ->
     regs_ok E (sr_upd sr (ridx 10) (ELit 0)) R2 ->
     know_ok segs E (zfill addr n M)
       ([KZero (SA eb eo) (ELit nZ); KWr (SA eb eo) (ELit nZ)] ++ kn_keep MGrow kn kn eb eo (ELit nZ)) ->
     realizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (zfill addr n M) rom) (mprotect_model addr n model)) KB) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) (t_if_adm (mprotect_budget_ok model addr n) KA KB).
Proof.
  intros vals ebs sr R M rom model kn pc w addr eb eo len KA KB E nZ n HR HK HF HE Hpc0 Hpc4 Hh Hlazy
         H17 H10 Hea Hal H11 Hlen Hnw H12 Hna Hma HKA HKB.
  assert (HnZ : 0 < nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
  pose proof (u64_range addr) as Har. unfold two_pow_64 in Hnw.
  assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; lia).
  eapply (rz_mprotect_lit segs R (Z_to_bv 64 pc) M rom model w addr len KA KB HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  - exact Hal.
  - exact Hlen.
  - unfold two_pow_64. lia.
  - exact Hna.
  - exact Hma.
  - intros Hbud. rewrite pc_lit_add4 by lia. apply HKA; [exact Hbud | |exact HK].
    apply regs_ok_set; [exact HR | discriminate |].
    cbn [edenot]. unfold errno_ret, ENOMEM. apply bv_eq. reflexivity.
  - intros Hbud. rewrite pc_lit_add4 by lia. apply HKB; [exact Hbud | |].
    + apply regs_ok_set; [exact HR | discriminate | reflexivity].
    + rewrite <- Hun. constructor; [apply kzero_zfill_off; [exact Hea | lia | lia]|].
      constructor; [apply kwr_zfill_off; [exact Hea | lia | lia]|].
      apply (kn_keep_sound segs _ M (zfill addr n M) MGrow); [exact HK | exact HK|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia.
      apply mem_change_zfill.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem rz_munmap_d : forall vals ebs sr R M rom model kn pc w (a : word) (eb : expr) (eo len : Z) K,
  let E := Env (vals_ev vals) ebs in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  regs_ok E sr R -> know_ok segs E M kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 215 ->
  edenot E (sr_get sr 10) = a -> bv_unsigned (edenot E eb) + eo = bv_unsigned a ->
  (bv_unsigned a mod page_size = 0)%Z ->
  edenot E (sr_get sr 11) = Z_to_bv 64 len -> 0 < len ->
  (bv_unsigned a + nZ <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a n = true ->
  (forall R1, regs_ok E (sr_upd sr (ridx 10) (ELit 0)) R1 ->
     know_ok segs E (unfill a n M) (kn_keep MUnmap kn kn eb eo (ELit nZ)) ->
     realizes segs (mkCfg (mkst R1 (Z_to_bv 64 (pc + 4)) (unfill a n M) rom) (munmap_model a n model)) K) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) K.
Proof.
  intros vals ebs sr R M rom model kn pc w a eb eo len K E nZ n HR HK HF HE Hpc0 Hpc4 Hh Hlazy
         H17 H10 Hea Hal H11 Hlen Hts Hhas HK1.
  assert (HnZ : 0 < nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
  pose proof (u64_range a) as Har. unfold TASK_SIZE in Hts.
  assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; lia).
  eapply (rz_munmap segs R (Z_to_bv 64 pc) M rom model w a len K HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  - exact Hal.
  - exact Hlen.
  - unfold TASK_SIZE. lia.
  - exact Hhas.
  - rewrite pc_lit_add4 by lia. apply HK1.
    + apply regs_ok_set; [exact HR | discriminate | reflexivity].
    + apply (kn_keep_sound segs _ M (unfill a n M) MUnmap); [exact HK | exact HK|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia.
      rewrite <- Hun. apply mem_change_unfill.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem rz_brk_query_d : forall vals ebs sr R M rom model kn pc w K,
  let E := Env (vals_ev vals) ebs in
  let ia := length vals in
  regs_ok E sr R -> know_ok segs E M kn ->
  sr_vars_lt ia sr = true -> kn_vars_lt ia kn = true ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 214 ->
  edenot E (sr_get sr 10) = Z_to_bv 64 0 ->
  (forall R1,
     let E' := Env (vals_ev (vals ++ [vm_brk (m_vmmaps model)])) ebs in
     regs_ok E' (sr_upd sr (ridx 10) (EVar ia)) R1 ->
     know_ok segs E' M kn ->
     realizes segs (mkCfg (mkst R1 (Z_to_bv 64 (pc + 4)) M rom) model) K) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) K.
Proof.
  intros vals ebs sr R M rom model kn pc w K E ia HR HK Hsr Hkn HF HE Hpc0 Hpc4 Hh Hlazy H17 H10 HK1.
  eapply (rz_brk_query segs R (Z_to_bv 64 pc) M rom model w K HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  rewrite pc_lit_add4 by lia. apply HK1.
  - apply regs_ok_set; [| discriminate |].
    + apply env_app_regs; [exact Hsr | exact HR].
    + cbn [edenot ev]. unfold ia. rewrite <- (Nat.add_0_r (length vals)), vals_ev_app_r. reflexivity.
  - apply env_app_know; [exact Hkn | exact HK].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rz_brk_grow_lit_d : forall vals ebs sr R M rom model kn pc w (eb : expr) (d : Z) KA KB,
  let E := Env (vals_ev vals) ebs in
  let h := m_vmmaps model in
  let b := vm_brk h in
  regs_ok E sr R -> know_ok segs E M kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 214 ->
  edenot E eb = b ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  edenot E (sr_get sr 10) = Z_to_bv 64 (bv_unsigned b + d) ->
  (forall R1, brk_grow_adm d model = false ->
     regs_ok E (sr_upd sr (ridx 10) eb) R1 ->
     know_ok segs E M kn ->
     realizes segs (mkCfg (mkst R1 (Z_to_bv 64 (pc + 4)) M rom) model) KA) ->
  (forall R2, brk_grow_adm d model = true ->
     regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD eb (ELit d))) R2 ->
     know_ok segs E (zfill b (Z_to_bv 64 d) M)
       ([KZero (SA eb 0) (ELit d); KWr (SA eb 0) (ELit d)] ++ kn_keep MGrow kn kn eb 0 (ELit d)) ->
     realizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (zfill b (Z_to_bv 64 d) M) rom) (brk_grown_model d model)) KB) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) (t_if_adm (brk_grow_adm d model) KA KB).
Proof.
  intros vals ebs sr R M rom model kn pc w eb d KA KB E h b HR HK HF HE Hpc0 Hpc4 Hh Hlazy
         H17 Heb Hbal Hdal Hd Hb0 Hnw Hs H10 HKA HKB.
  pose proof (u64_range b) as Hbr.
  assert (Hud : bv_unsigned (Z_to_bv 64 d) = d) by (apply u_small; lia).
  eapply (rz_brk_grow_lit segs R (Z_to_bv 64 pc) M rom model w d KA KB HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption); try assumption.
  - intros Hadm. rewrite pc_lit_add4 by lia. apply HKA; [exact Hadm| |exact HK].
    apply regs_ok_set; [exact HR | discriminate | exact Heb].
  - intros Hadm. rewrite pc_lit_add4 by lia. apply HKB; [exact Hadm| |].
    + apply regs_ok_set; [exact HR | discriminate |].
      rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off]. rewrite Heb. reflexivity.
    + pose proof (kzero_zfill segs E M eb b (Z_to_bv 64 d) Heb ltac:(rewrite Hud; lia) ltac:(rewrite Hud; lia)) as K1.
      pose proof (kwr_zfill segs E M eb b (Z_to_bv 64 d) Heb ltac:(rewrite Hud; lia) ltac:(rewrite Hud; lia)) as K2.
      rewrite Hud in K1, K2.
      constructor; [exact K1|]. constructor; [exact K2|].
      apply (kn_keep_sound segs _ M (zfill b (Z_to_bv 64 d) M) MGrow); [exact HK | exact HK|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Heb, u_small by lia.
      rewrite Z.add_0_r. rewrite <- Hud.
      replace (zfill b (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 d))) M) with (zfill b (Z_to_bv 64 d) M) by (rewrite Hud; reflexivity).
      apply (mem_change_zfill M b (Z_to_bv 64 d)).
Qed.

(* [comment removed for export] *)
Definition dsb_entries (eb : expr) (d : Z) (ds : list (saddr * expr)) : list kentry :=
  map (fun dd => KDisj (SA eb 0) (ELit d) (fst dd) (snd dd)) ds.

#[using="Type"] Lemma dsb_entries_ok : forall E M eb (b : word) d ds,
  edenot E eb = b -> 0 <= d -> bv_unsigned b + d < 2 ^ 64 ->
  dsj_claims E (fun a => a = b) d ds ->
  know_ok segs E M (dsb_entries eb d ds).
Proof.
  intros E M eb b d ds Heb Hd Hnw Hds. pose proof (u64_range b).
  unfold dsb_entries. unfold dsj_claims in Hds.
  induction ds as [|[r l] ds IH]; [constructor|].
  apply Forall_cons_iff in Hds as [Hd1 Hds]. cbn [map fst snd] in *.
  constructor; [|apply IH; exact Hds].
  specialize (Hd1 b eq_refl).
  cbn [kentry_ok]. unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
  rewrite Heb, (u_small d) by lia. lia.
Qed.

#[using="Type"] Theorem rz_brk_grow_lit_ds_d : forall vals ebs sr R M rom model kn pc w (eb : expr) (d : Z) ds KA KB,
  let E := Env (vals_ev vals) ebs in
  let h := m_vmmaps model in
  let b := vm_brk h in
  regs_ok E sr R -> know_ok segs E M kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 214 ->
  edenot E eb = b ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  edenot E (sr_get sr 10) = Z_to_bv 64 (bv_unsigned b + d) ->
  (brk_grow_adm d model = true -> dsj_claims E (fun a => a = b) d ds) ->
  (forall R1, brk_grow_adm d model = false ->
     regs_ok E (sr_upd sr (ridx 10) eb) R1 ->
     know_ok segs E M kn ->
     realizes segs (mkCfg (mkst R1 (Z_to_bv 64 (pc + 4)) M rom) model) KA) ->
  (forall R2, brk_grow_adm d model = true ->
     regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD eb (ELit d))) R2 ->
     know_ok segs E (zfill b (Z_to_bv 64 d) M)
       ([KZero (SA eb 0) (ELit d); KWr (SA eb 0) (ELit d)] ++ dsb_entries eb d ds
        ++ kn_keep MGrow (dsb_entries eb d ds ++ kn) kn eb 0 (ELit d)) ->
     realizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (zfill b (Z_to_bv 64 d) M) rom) (brk_grown_model d model)) KB) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) (t_if_adm (brk_grow_adm d model) KA KB).
Proof.
  intros vals ebs sr R M rom model kn pc w eb d ds KA KB E h b HR HK HF HE Hpc0 Hpc4 Hh Hlazy
         H17 Heb Hbal Hdal Hd Hb0 Hnw Hs H10 Hds HKA HKB.
  pose proof (u64_range b) as Hbr.
  assert (Hud : bv_unsigned (Z_to_bv 64 d) = d) by (apply u_small; lia).
  eapply (rz_brk_grow_lit segs R (Z_to_bv 64 pc) M rom model w d KA KB HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption); try assumption.
  - intros Hadm. rewrite pc_lit_add4 by lia. apply HKA; [exact Hadm | |exact HK].
    apply regs_ok_set; [exact HR | discriminate | exact Heb].
  - intros Hadm. rewrite pc_lit_add4 by lia.
    assert (KD : forall M', know_ok segs E M' (dsb_entries eb d ds))
      by (intros M'; apply (dsb_entries_ok E M' eb b d ds Heb ltac:(lia) Hnw (Hds Hadm))).
    apply HKB; [exact Hadm| |].
    + apply regs_ok_set; [exact HR | discriminate |].
      rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off]. rewrite Heb. reflexivity.
    + pose proof (kzero_zfill segs E M eb b (Z_to_bv 64 d) Heb ltac:(rewrite Hud; lia) ltac:(rewrite Hud; lia)) as K1.
      pose proof (kwr_zfill segs E M eb b (Z_to_bv 64 d) Heb ltac:(rewrite Hud; lia) ltac:(rewrite Hud; lia)) as K2.
      rewrite Hud in K1, K2.
      constructor; [exact K1|]. constructor; [exact K2|].
      apply (proj2 (know_ok_app segs _ _ _ _)). split; [apply KD|].
      apply (kn_keep_sound segs _ M (zfill b (Z_to_bv 64 d) M) MGrow);
        [apply (proj2 (know_ok_app segs _ _ _ _)); split; [apply KD | exact HK] | exact HK|].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Heb, u_small by lia.
      rewrite Z.add_0_r. rewrite <- Hud.
      replace (zfill b (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 d))) M) with (zfill b (Z_to_bv 64 d) M) by (rewrite Hud; reflexivity).
      apply (mem_change_zfill M b (Z_to_bv 64 d)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem rz_mmap_fixed_noaccess_d : forall vals ebs sr R M rom model kn pc w (addr : word) (eb : expr) (eo len : Z) KB,
  let E := Env (vals_ev vals) ebs in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  regs_ok E sr R -> know_ok segs E M kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  edenot E (sr_get sr 17) = Z_to_bv 64 222 ->
  edenot E (sr_get sr 10) = addr -> bv_unsigned (edenot E eb) + eo = bv_unsigned addr ->
  (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  edenot E (sr_get sr 11) = Z_to_bv 64 len -> 0 < len ->
  (bv_unsigned addr + nZ <= alloc_top (m_vmmaps model))%Z ->
  edenot E (sr_get sr 12) = Z_to_bv 64 0 -> edenot E (sr_get sr 13) = Z_to_bv 64 50 ->
  edenot E (sr_get sr 14) = Z_to_bv 64 (-1) -> edenot E (sr_get sr 15) = Z_to_bv 64 0 ->
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (forall R2, regs_ok E (sr_upd sr (ridx 10) (sr_get sr 10)) R2 ->
     know_ok segs E (unfill addr n M) (kn_keep MUnmap kn kn eb eo (ELit nZ)) ->
     realizes segs (mkCfg (mkst R2 (Z_to_bv 64 (pc + 4)) (unfill addr n M) rom) (fixed_noaccess_model addr n model)) KB) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) KB.
Proof.
  intros vals ebs sr R M rom model kn pc w addr eb eo len KB E nZ n HR HK HF HE Hpc0 Hpc4 Hh Hlazy
         H17 H10 Hea Hal Hpos H11 Hlen Htop H12 H13 H14 H15 Hrf Hmc HKB.
  assert (HnZ : 0 < nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
  pose proof (u64_range addr) as Har. pose proof (alloc_top_lt (m_vmmaps model)) as Htl. unfold two_pow_64 in Htl.
  assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; lia).
  assert (KU : know_ok segs E (unfill addr n M) (kn_keep MUnmap kn kn eb eo (ELit nZ))).
  { apply (kn_keep_sound segs _ M (unfill addr n M) MUnmap); [exact HK | exact HK|].
    unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hea, u_small by lia.
    rewrite <- Hun. apply mem_change_unfill. }
  eapply (rz_mmap_fixed_noaccess segs R (Z_to_bv 64 pc) M rom model w addr len KB HF HE Hh Hlazy);
    try (eapply getr_of_sr; [exact HR|]; eassumption).
  - exact Hal.
  - exact Hpos.
  - exact Hlen.
  - exact Htop.
  - exact Hrf.
  - exact Hmc.
  - rewrite pc_lit_add4 by lia. apply HKB; [|exact KU].
    apply regs_ok_set; [exact HR | discriminate | exact H10].
Qed.

End Drive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_grow_adm_unpack : forall d m,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  brk_grow_adm d m = true ->
  bv_unsigned b + d <= alloc_top h
  /\ region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true
  /\ vm_backing_used m + d <= vm_limit h.
Proof.
  intros d m h b Hbal Hdal Hd Hb0 Hnw Hadm.
  pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold brk_grow_adm, Mmap.brk_grow_ok, Mmap.brk_budget_ok in Hadm. fold h b in Hadm. rewrite Hureq in Hadm.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in Hadm by lia. cbn [andb] in Hadm.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in Hadm by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in Hadm
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) in Hadm by lia.
  apply andb_prop in Hadm as [Hadm Hlive]. apply andb_prop in Hadm as [Htop Hrf].
  apply Z.leb_le in Htop. apply Z.leb_le in Hlive.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in Hrf by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z in Hrf by lia.
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d in Hlive.
  2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma region_free_shrink : forall l (lo : word) (n m : Z),
  0 <= m <= n -> bv_unsigned lo + n < 2 ^ 64 ->
  region_free l lo (Z_to_bv 64 n) = true -> region_free l lo (Z_to_bv 64 m) = true.
Proof.
  intros l lo n m Hmn Hnw Hrf. pose proof (u64_range lo).
  apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (RefNodes.region_free_In _ _ _ b s Hrf Hin) as D. rewrite !u_small in * by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kzero_sub : forall segs E M (b : expr) (k n k' n' : Z),
  kentry_ok segs E M (KZero (SA b k) (ELit n)) ->
  k <= k' -> 0 < n' -> k' + n' <= k + n -> 0 <= n < 2 ^ 64 ->
  kentry_ok segs E M (KZero (SA b k') (ELit n')).
Proof.
  intros segs E M b k n k' n' [Hfl Hz] H1 H2 H3 H4. cbn [kentry_ok].
  unfold flat, estart, elenZ in *. cbn [a_base a_off edenot] in *.
  pose proof (u64_range (edenot E b)). rewrite (u_small n) in * by lia. rewrite (u_small n') by lia.
  split; [lia|]. intros i Hi.
  replace (bv_unsigned (edenot E b) + k' + i) with (bv_unsigned (edenot E b) + k + (k' - k + i)) by lia.
  apply Hz. lia.
Qed.

Lemma kwr_sub : forall segs E M (b : expr) (k n k' n' : Z),
  kentry_ok segs E M (KWr (SA b k) (ELit n)) ->
  k <= k' -> 0 < n' -> k' + n' <= k + n -> 0 <= n < 2 ^ 64 ->
  kentry_ok segs E M (KWr (SA b k') (ELit n')).
Proof.
  intros segs E M b k n k' n' [Hfl Hst] H1 H2 H3 H4. cbn [kentry_ok].
  unfold flat, estart, elenZ in *. cbn [a_base a_off edenot] in *.
  pose proof (u64_range (edenot E b)). rewrite (u_small n) in * by lia. rewrite (u_small n') by lia.
  split; [lia|]. intros d m Hd Hm.
  replace (bv_unsigned (edenot E b) + k' + d) with (bv_unsigned (edenot E b) + k + (k' - k + d)) by lia.
  apply Hst; lia.
Qed.
End NodesMmDrive.

(* [comment removed for export] *)
Module AsanBootKn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive.
Import ListNotations.
Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sivs : Type := list (expr * Z).

(* [comment removed for export] *)
Definition DS_maps (ms : sivs) : list (saddr * expr) := List.map (fun p => (SA (fst p) 0, ELit (snd p))) ms.

Definition GF (v : nat) (nZ : Z) : list kentry :=
  [KZero (SA (EVar v) 0) (ELit nZ); KWr (SA (EVar v) 0) (ELit nZ); KAlign (EVar v) 4096;
   KRange (EVar v) 4096 (2 ^ 64 - stack_max_size - nZ)].

Definition kn_grant_d (ds : list (saddr * expr)) (v : nat) (nZ : Z) (kn : list kentry) : list kentry :=
  GF v nZ ++ dsj_entries v nZ ds
  ++ kn_keep MGrow ([KAlign (EVar v) 4096; KRange (EVar v) 4096 (2 ^ 64 - stack_max_size - nZ)]
                    ++ dsj_entries v nZ ds ++ kn) kn (EVar v) 0 (ELit nZ).

(* [comment removed for export] *)
Definition GF_none (v : nat) (nZ : Z) : list kentry :=
  [KAlign (EVar v) 4096; KRange (EVar v) 4096 (2 ^ 64 - stack_max_size - nZ)].
Definition kn_grant_none_d (ds : list (saddr * expr)) (v : nat) (nZ : Z) (kn : list kentry) : list kentry :=
  GF_none v nZ ++ dsj_entries v nZ ds ++ kn_keep MUnmap (GF_none v nZ ++ dsj_entries v nZ ds ++ kn) kn (EVar v) 0 (ELit nZ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gc_keep_stack (spoff : Z) (k : kentry) : bool :=
  match k with
  | KWord (SA (EVar 0) off) w _ => negb (off + Z.of_nat w <=? spoff)
  | KZero (SA (EVar 0) off) (ELit n) => negb ((off + n <=? spoff) && (- 0x400000 <? off))
  | KFill (SA (EVar 0) off) (ELit n) _ => negb ((off + n <=? spoff) && (- 0x400000 <? off))
  | _ => true
  end.
Definition gc_keep_base (v : nat) (k : kentry) : bool :=
  match k with
  | KWord (SA (EVar b) _) _ _ => negb (Nat.eqb b v)
  | _ => true
  end.
Definition gc_keep_lits (lo hi : Z) (k : kentry) : bool :=
  match k with
  | KWord (SA (ELit 0) off) _ _ => negb ((lo <=? off) && (off <? hi))
  | _ => true
  end.
End AsanBootKn.
