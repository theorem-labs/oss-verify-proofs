(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (new Section DrvRT: the drivers over the run's segment list asegs ++ rt_tail from the configuration with that list's read-only backing, for the run's driver-law record asan_driver_laws_run, with the pair facts vs_nw, for a window above the image, and vs_inv, that a step keeps the invariant vcm2 of each of the vDSO pair's two entries, the rewrapping lemma back_rt and the whole-walk lift rz_lift_rt). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SReach RegsEquivM MainEqv HeapCeil
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsLazyRun AsPrintfFirst.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Scfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomBase RunTail PairCleanAll RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import LazyTail.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section Drv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom asegs.

  (* [comment removed for export] *)
  Definition same_vm (mo mo' : Model) : Prop := m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo.

  Lemma same_vm_refl : forall mo, same_vm mo mo.
  Proof. intros mo. split; reflexivity. Qed.
  Lemma same_vm_trans : forall a b c, same_vm a b -> same_vm b c -> same_vm a c.
  Proof. intros a b c [H1 H2] [H3 H4]. split; congruence. Qed.
  Lemma same_vm_sb : forall mo mo', same_but_materialized mo mo' -> same_vm mo mo'.
  Proof.
    intros mo mo' SB. destruct (same_but_materialized_fields _ _ SB) as (_ & A & B & _). split; [exact A | exact B].
  Qed.
  Lemma same_vm_with_fds : forall f mo, same_vm mo (with_fds f mo).
  Proof. intros f [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma drv_lazy : forall s msF mo R pc M (T : TSet),
    as_VIS H s msF = mkst R pc M rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall L S Zr,
       lzok asegs L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R pc M rom ->
       (forall msF' mo' ms', lzok asegs L S Zr (mkCfg msF' mo') -> same_vm mo mo' -> restrict L S msF' = ms' ->
          as_VIS H s msF' = ms' /\ as_AKREL H s (mkCfg msF' mo')) ->
       realizes asegs (mkCfg msF mo) T) ->
    realizes asegs (mkCfg msF mo) T.
  Proof.
    intros s msF mo R pc M T HV HA HK.
    destruct (adl_lazy H DL s) as (L & S & Zr & HVIS & HLZ & HTR).
    apply (HK L S Zr); [apply HLZ; exact HA | rewrite <- HVIS; exact HV |].
    intros msF' mo' ms' OK' [SV1 SV2] RS'. split; [rewrite HVIS; exact RS'|].
    exact (HTR msF mo msF' mo' HA OK' SV1 SV2).
  Qed.

  (* [comment removed for export] *)
  Theorem drv_run_lf : forall s fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R msF mo T,
    sym_exec asegs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok asegs E M kn ->
    scs_denot asegs M E scs -> scs_denot asegs M E scs2 ->
    as_VIS H s msF = mkst R (Z_to_bv 64 pc) M rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall R' M' msF' mo', regs_ok E (s_regs ss') R' -> know_ok asegs E M' kn' ->
       M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
       as_VIS H s msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') T) ->
    realizes asegs (mkCfg msF mo) T.
  Proof.
    intros s fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R msF mo T Hex Hc HR HK Hsc Hsc2 HV HA Hcont.
    apply (drv_lazy s msF mo R _ M T HV HA). intros L S Zr OK RS BACK.
    eapply (rz_run_lf_lazy asegs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF mo T Hex Hc HR HK Hsc Hsc2 OK RS).
    intros R' M' msF' mo' HR' HK' EQ LF OK' SB HS RS'.
    destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB) RS') as [HV' HA'].
    exact (Hcont R' M' msF' mo' HR' HK' EQ LF HV' HA' SB).
  Qed.

  (* [comment removed for export] *)
  Theorem drv_close : forall s msF regs (pc : word) mem mo w fd e K,
    fetch_word asegs pc = Some w -> is_ecall w = true ->
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 17 = Z_to_bv 64 57 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds mo) fd = Some e ->
    (forall msF', as_VIS H s msF' = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom ->
       as_AKREL H s (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) ->
       realizes asegs (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF regs pc mem mo w fd e K HF HE HV HA H17 H10 Hfd32 Hlk Hc.
    apply (drv_lazy s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
    eapply (rz_close_lazy asegs L S Zr msF regs pc mem mo w fd e K HF HE OK RS H17 H10 Hfd32 Hlk).
    intros msF' OK' RS' HS'. destruct (BACK msF' _ _ OK' (same_vm_with_fds _ _) RS') as [HV' HA'].
    exact (Hc msF' HV' HA').
  Qed.

  (* [comment removed for export] *)
  Theorem drv_read_file : forall s msF regs (pc : word) mem mo w fd p off data (cnt : Z) K,
    fetch_word asegs pc = Some w -> is_ecall w = true ->
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 17 = Z_to_bv 64 63 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds mo) fd = Some (FdFile p off) ->
    fs_lookup (m_fs mo) p = Some data ->
    getr regs 12 = Z_to_bv 64 cnt ->
    (1 <= cnt)%Z -> (cnt <= MAX_RW_COUNT)%Z -> (cnt < 2 ^ 64)%Z ->
    (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
    store_ok asegs mem (getr regs 11) (Z.to_nat cnt) = true ->
    let bs := file_read data off (getr regs 12) in
    let mo1 := with_fds (fd_insert (m_fds mo) fd (FdFile p (off + len_word bs))) mo in
    (forall msF' mo',
       as_VIS H s msF' = mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (wbytes mem (getr regs 11) bs) rom ->
       as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo1 mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF regs pc mem mo w fd p off data cnt K HF HE HV HA H17 H10 Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Htask Hso bs mo1 Hc.
    apply (drv_lazy s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
    eapply (rz_read_file_lazy asegs L S Zr msF regs pc mem mo w fd p off data cnt K HF HE OK RS H17 H10 Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Htask Hso).
    intros msF' mo' OK' SB' RS' HS'.
    destruct (BACK msF' mo' _ OK' (same_vm_trans _ _ _ (same_vm_with_fds _ _) (same_vm_sb _ _ SB')) RS') as [HV' HA'].
    exact (Hc msF' mo' HV' HA' SB').
  Qed.
End Drv.

(** * The drivers over the run's segment list (LPS 727298f3)

    The main phase is a walk over [asegs ++ RunTail.rt_tail] (the binary's segments, then the
    launch's vDSO/vvar pair) from the configuration with that list's read-only backing
    ([arz], As/AsDriverLaws.v).  Each driver below is the one of Section Drv with its walks so
    stated; the lazy view stays over [asegs], and the invariant carried through every step is
    the pair's [vcm2 vlo vb vhi] (As/AsDriverLaws.v): [PairCleanAll.vcm_cfg] of the vvar entry
    [vlo, vb) and of the text entry [vb, vhi). *)
Section DrvRT.
  Context {HCEIL : HeapCeil} {RT : RunTail.RunTail}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Context {vlo vb vhi : Z}.
  Hypothesis DLR : asan_driver_laws_run RunTail.rt_tail vlo vb vhi H.

  Let rom := seg_rom asegs.
  Local Notation rV := (seg_rom (asegs ++ RunTail.rt_tail)) (only parsing).

  (* no segment of the run's list that holds a byte of a window above the binary's image is
     writable: the binary's segments end below it (asegs_find_none), and the tail is not
     writable *)
  Lemma vs_nw : forall wlo whi : Z, (AIMG_TOP <= wlo)%Z -> forall (x : word) s, (wlo <= bv_unsigned x < whi)%Z ->
    find_segment (asegs ++ RunTail.rt_tail) (bv_unsigned x) 1%Z = Some s -> seg_writable s = false.
  Proof.
    intros wlo whi Htop x s Hx Hf.
    rewrite RomStable.find_segment_app in Hf.
    rewrite (asegs_find_none (bv_unsigned x)) in Hf by lia.
    cbv beta iota in Hf.
    exact (RunTail.rt_nw s (RomStable.find_segment_in _ _ _ _ Hf)).
  Qed.

  (* every step over the run's list keeps the pair's invariant, one entry at a time: both
     entries lie above the binary's image (adlr_top, adlr_ord) *)
  Lemma vs_inv : forall c evs c', vcm2 vlo vb vhi c ->
    sstep_cfg (asegs ++ RunTail.rt_tail) Scfg.the_scfg c evs (SNext c') -> vcm2 vlo vb vhi c'.
  Proof.
    intros c evs c' [V1 V2] Hs.
    pose proof (adlr_top _ _ _ _ H DLR) as Htop. pose proof (adlr_ord _ _ _ _ H DLR) as Hord.
    assert (Htop' : (AIMG_TOP <= vb)%Z) by lia.
    split.
    - exact (PairCleanAll.pc_step_clean (asegs ++ RunTail.rt_tail) vlo vb (vs_nw vlo vb Htop) Scfg.the_scfg c evs c' Hs V1).
    - exact (PairCleanAll.pc_step_clean (asegs ++ RunTail.rt_tail) vb vhi (vs_nw vb vhi Htop') Scfg.the_scfg c evs c' Hs V2).
  Qed.

  (* the view keeps the read-only backing (the view is a restriction, adlr_lazy) *)
  Lemma vis_rom_rt : forall s msF ms, as_VIS H s msF = ms -> ms_rom ms = ms_rom msF.
  Proof.
    intros s msF ms HV. subst ms.
    destruct (adlr_lazy _ _ _ _ H DLR s) as (L & S & Zr & HVIS & _ & _).
    rewrite HVIS. exact (ms_rom_restrict L S msF).
  Qed.

  (* rewrap a configuration that carries the run's backing into the binary-backed state the
     main phase names.  The kernel relation of the new state comes from adlr_lazy's third
     conjunct for the same L S Zr, so that conjunct is a premise next to the view's. *)
  Lemma back_rt : forall s msF mo L S Zr msF'' mo' R' pc' M',
    (forall x, as_VIS H s x = restrict L S x) ->
    (forall ms mo0 ms' mo0', as_AKREL H s (mkCfg ms mo0) -> lzok asegs L S Zr (mkCfg ms' mo0') ->
       m_vmmaps mo0' = m_vmmaps mo0 -> m_vm_lazy mo0' = m_vm_lazy mo0 ->
       vcm2 vlo vb vhi (mkCfg ms' mo0') -> as_AKREL H s (mkCfg ms' mo0')) ->
    as_AKREL H s (mkCfg msF mo) -> lzok asegs L S Zr (mkCfg msF'' mo') ->
    m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo ->
    restrict L S msF'' = mkst R' pc' M' rV -> vcm2 vlo vb vhi (mkCfg msF'' mo') ->
    exists msF', mkCfg msF'' mo' = RomBase.cwrom (mkCfg msF' mo') rV
      /\ as_VIS H s msF' = mkst R' pc' M' rom /\ as_AKREL H s (mkCfg msF' mo').
  Proof.
    intros s msF mo L S Zr msF'' mo' R' pc' M' HVIS HTR HA OK' SV1 SV2 RS' VC'.
    assert (ER : ms_rom msF'' = rV).
    { rewrite <- (ms_rom_restrict L S msF''), RS'. reflexivity. }
    exists (RomBase.wrom msF'' rom). split; [|split].
    - change (mkCfg msF'' mo' = mkCfg (RomBase.wrom msF'' rV) mo').
      rewrite <- ER, RomBase.wrom_eta. reflexivity.
    - rewrite HVIS, restrict_wrom, RS'. reflexivity.
    - (* the pair's invariant reads the overlay and the model, not the backing *)
      exact (HTR msF mo (RomBase.wrom msF'' rom) mo' HA (lzok_wrom asegs L S Zr msF'' mo' rom OK') SV1 SV2 VC').
  Qed.

  (* drv_lazy over the run's list: the lazy facts at the state with the run's backing, the
     pair's invariant there, and a way back to a binary-backed state after each step *)
  Lemma drv_lazy_rt : forall s msF mo R pc M (T : TSet),
    as_VIS H s msF = mkst R pc M rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall L S Zr,
       lzok asegs L S Zr (mkCfg (RomBase.wrom msF rV) mo) -> restrict L S (RomBase.wrom msF rV) = mkst R pc M rV ->
       vcm2 vlo vb vhi (mkCfg (RomBase.wrom msF rV) mo) ->
       (forall msF'' mo' R' pc' M', lzok asegs L S Zr (mkCfg msF'' mo') -> same_vm mo mo' ->
          restrict L S msF'' = mkst R' pc' M' rV -> vcm2 vlo vb vhi (mkCfg msF'' mo') ->
          exists msF', mkCfg msF'' mo' = RomBase.cwrom (mkCfg msF' mo') rV
            /\ as_VIS H s msF' = mkst R' pc' M' rom /\ as_AKREL H s (mkCfg msF' mo')) ->
       realizes (asegs ++ RunTail.rt_tail) (mkCfg (RomBase.wrom msF rV) mo) T) ->
    arz (mkCfg msF mo) T.
  Proof.
    intros s msF mo R pc M T HV HA HK.
    destruct (adlr_lazy _ _ _ _ H DLR s) as (L & S & Zr & HVIS & HLZ & HTR).
    change (realizes (asegs ++ RunTail.rt_tail) (mkCfg (RomBase.wrom msF rV) mo) T).
    apply (HK L S Zr).
    - exact (lzok_wrom asegs L S Zr msF mo rV (HLZ _ HA)).
    - rewrite restrict_wrom, <- HVIS, HV. reflexivity.
    - (* the pair's invariant reads the overlay and the model, not the backing *)
      exact (adlr_vcm _ _ _ _ H DLR s (mkCfg msF mo) HA).
    - intros msF'' mo' R' pc' M' OK' [SV1 SV2] RS' VC'.
      exact (back_rt s msF mo L S Zr msF'' mo' R' pc' M' HVIS HTR HA OK' SV1 SV2 RS' VC').
  Qed.

  (* a whole walk over the binary's own segments (a branch that never calls time()) *)
  Lemma rz_lift_rt : forall s msF mo R pc M T,
    as_VIS H s msF = mkst R pc M rom -> realizes asegs (mkCfg msF mo) T -> arz (mkCfg msF mo) T.
  Proof.
    intros s msF mo R pc M T HV HR.
    apply (RomStable.realizes_app_tail asegs RunTail.rt_tail RunTail.rt_nx RunTail.rt_nw vdso_image_asegs).
    apply (RomStable.realizes_wrom asegs vdso_image_asegs (mkCfg msF mo) T HR).
    cbn [cfg_ms]. rewrite <- (vis_rom_rt s msF _ HV).
    exact (RunTail.rom_ext_app_tail asegs RunTail.rt_tail).
  Qed.

  Lemma drv_lazy_whole_rt : forall s msF mo R pc M (T : TSet),
    as_VIS H s msF = mkst R pc M rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall L S Zr, lzok asegs L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R pc M rom ->
       realizes asegs (mkCfg msF mo) T) ->
    arz (mkCfg msF mo) T.
  Proof.
    intros s msF mo R pc M T HV HA HK.
    apply (rz_lift_rt s msF mo R pc M T HV).
    destruct (adlr_lazy _ _ _ _ H DLR s) as (L & S & Zr & HVIS & HLZ & _).
    apply (HK L S Zr); [exact (HLZ _ HA) | rewrite <- HVIS; exact HV].
  Qed.

  Theorem drv_run_lf_rt : forall s fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R msF mo T,
    sym_exec asegs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok asegs E M kn ->
    scs_denot asegs M E scs -> scs_denot asegs M E scs2 ->
    as_VIS H s msF = mkst R (Z_to_bv 64 pc) M rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall R' M' msF' mo', regs_ok E (s_regs ss') R' -> know_ok asegs E M' kn' ->
       M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
       as_VIS H s msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       arz (mkCfg msF' mo') T) ->
    arz (mkCfg msF mo) T.
  Proof.
    intros s fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R msF mo T Hex Hc HR HK Hsc Hsc2 HV HA Hcont.
    apply (drv_lazy_rt s msF mo R _ M T HV HA). intros L S Zr OK RS VC BACK.
    eapply (rz_run_lf_lazy_tail asegs RunTail.rt_tail RunTail.rt_nx RunTail.rt_nw (vcm2 vlo vb vhi) vs_inv
              L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rV R (RomBase.wrom msF rV) mo T
              Hex Hc HR HK Hsc Hsc2 OK VC RS).
    intros R' M' msF'' mo' HR' HK' EQ LF OK' SB HS RS' VC'.
    destruct (BACK msF'' mo' _ _ _ OK' (same_vm_sb _ _ SB) RS' VC') as (msF' & EQc & HV' & HA').
    rewrite EQc. exact (Hcont R' M' msF' mo' HR' HK' EQ LF HV' HA' SB).
  Qed.

  Theorem drv_close_rt : forall s msF regs (pc : word) mem mo w fd e K,
    fetch_word asegs pc = Some w -> is_ecall w = true ->
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 17 = Z_to_bv 64 57 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds mo) fd = Some e ->
    (forall msF', as_VIS H s msF' = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom ->
       as_AKREL H s (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) ->
       arz (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) K) ->
    arz (mkCfg msF mo) K.
  Proof.
    intros s msF regs pc mem mo w fd e K HF HE HV HA H17 H10 Hfd32 Hlk Hc.
    apply (drv_lazy_rt s msF mo regs pc mem K HV HA). intros L S Zr OK RS VC BACK.
    eapply (rz_close_lazy_tail asegs RunTail.rt_tail RunTail.rt_nx RunTail.rt_nw (vcm2 vlo vb vhi) vs_inv
              L S Zr (RomBase.wrom msF rV) regs pc mem mo w fd e K HF HE OK VC RS H17 H10 Hfd32 Hlk).
    intros msF'' OK' RS' HS' VC'.
    destruct (BACK msF'' _ _ _ _ OK' (same_vm_with_fds _ _) RS' VC') as (msF' & EQc & HV' & HA').
    rewrite EQc. exact (Hc msF' HV' HA').
  Qed.

  Theorem drv_read_file_rt : forall s msF regs (pc : word) mem mo w fd p off data (cnt : Z) K,
    fetch_word asegs pc = Some w -> is_ecall w = true ->
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 17 = Z_to_bv 64 63 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds mo) fd = Some (FdFile p off) ->
    fs_lookup (m_fs mo) p = Some data ->
    getr regs 12 = Z_to_bv 64 cnt ->
    (1 <= cnt)%Z -> (cnt <= MAX_RW_COUNT)%Z -> (cnt < 2 ^ 64)%Z ->
    (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
    store_ok asegs mem (getr regs 11) (Z.to_nat cnt) = true ->
    let bs := file_read data off (getr regs 12) in
    let mo1 := with_fds (fd_insert (m_fds mo) fd (FdFile p (off + len_word bs))) mo in
    (forall msF' mo',
       as_VIS H s msF' = mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (wbytes mem (getr regs 11) bs) rom ->
       as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo1 mo' ->
       arz (mkCfg msF' mo') K) ->
    arz (mkCfg msF mo) K.
  Proof.
    intros s msF regs pc mem mo w fd p off data cnt K HF HE HV HA H17 H10 Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Htask Hso bs mo1 Hc.
    apply (drv_lazy_rt s msF mo regs pc mem K HV HA). intros L S Zr OK RS VC BACK.
    eapply (rz_read_file_lazy_tail asegs RunTail.rt_tail RunTail.rt_nx RunTail.rt_nw (vcm2 vlo vb vhi) vs_inv
              L S Zr (RomBase.wrom msF rV) regs pc mem mo w fd p off data cnt K HF HE OK VC RS
              H17 H10 Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Htask Hso).
    intros msF'' mo' OK' SB' RS' HS' VC'.
    destruct (BACK msF'' mo' _ _ _ OK' (same_vm_trans _ _ _ (same_vm_with_fds _ _) (same_vm_sb _ _ SB')) RS' VC')
      as (msF' & EQc & HV' & HA').
    rewrite EQc. exact (Hc msF' mo' HV' HA' SB').
  Qed.
End DrvRT.
