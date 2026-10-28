(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BHoare BFrame BShapeLaws BpecConsts BAgentLib BFileSim BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BMemSplit BSpec BLibTail BRefPrintfLib BRefMemcpyLib BReach BegsEquivM BainEqv BeapCeil BazyRestrict BazySR BazyFdNodes BainWalk_defs BainSegs BainMem BainOpen.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BArr BStep BLFrame BMState BSysStep BExec BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 DvB_CXXAs BRefExitBase BsPrintfFirst BsExitDefs BsHdrErr BsDrvHeap BsDrvRun BsDrvIO BsDrvOpen BsDrvRead BsDrvMem BsDrvDefs BsTRSegs BsTargetRun BsMainWalk_defs BsMainSegs BsMainPre BsMainOpen BsMainLoop BsMainRet BsMainExit B9_read BsDrvCells RtB_Iface DvB_ExitCells DvB_FuzzStmt.
Import ListNotations.
Import BSymExec2.SX2. Import BSymExec2Sound.SX2S.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac kept K r E := rewrite (K r ltac:(unfold aheap_kept; cbn [In]; repeat (first [left; reflexivity | right]))); exact E.

Section TailStmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable FZP : fuzz_params.

  Definition atail_usage_stmt : Prop :=
    forall (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF0 : machine_state) (mo0 : Model)
           (regs0 : bvmap 5 word) (mem0 : word -> option byte) (B tid can : Z)
           (s : as_St H) (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte),
      valid_argv argv -> AMpre H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can -> length argv <> 2%nat ->
      as_VIS H s msF = mkst regs (Z_to_bv 64 0xe858c) mem (seg_rom asegs) -> as_AKREL H s (mkCfg msF mo) ->
      getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 8 = Z_to_bv 64 2 ->
      getr regs 10 = Z_to_bv 64 (Z.of_nat (length argv)) -> getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
      mstatics H sp0 tid can mem0 mem -> (exists TB, ahm_ok mem TB) ->
      m_fds mo = m_fds mo0 ->
      realizes asegs (mkCfg msF mo) (t_die (msg_usage (hd [] argv)) (m_fs mo)).

  Definition atail_open_stmt : Prop :=
    forall (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF0 : machine_state) (mo0 : Model)
           (regs0 : bvmap 5 word) (mem0 : word -> option byte) (B tid can : Z) (a0s path : list byte) (pp : Z)
           (s : as_St H) (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte),
      valid_argv argv -> AMpre H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can -> argv = [a0s; path] ->
      rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned sp0 + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pp)) -> astr_at mem0 sp0 pp path ->
      as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8684) mem (seg_rom asegs) -> as_AKREL H s (mkCfg msF mo) ->
      getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 18 = Z_to_bv 64 pp ->
      mstatics H sp0 tid can mem0 mem -> (exists TB, ahm_ok mem TB) ->
      fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
      realizes asegs (mkCfg msF mo) (t_die (msg_cannot_open path) (m_fs mo)).

  Definition atail_rderr_stmt : Prop :=
    forall (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF0 : machine_state) (mo0 : Model)
           (regs0 : bvmap 5 word) (mem0 : word -> option byte) (B tid can : Z) (a0s path : list byte) (pp : Z)
           (s : as_St H) (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte),
      valid_argv argv -> AMpre H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can -> argv = [a0s; path] ->
      rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned sp0 + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pp)) -> astr_at mem0 sp0 pp path ->
      as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8620) mem (seg_rom asegs) -> as_AKREL H s (mkCfg msF mo) ->
      getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 18 = Z_to_bv 64 pp ->
      mstatics H sp0 tid can mem0 mem -> (exists TB, ahm_ok mem TB) ->
      fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
      realizes asegs (mkCfg msF mo) (t_die (msg_read_error path) (m_fs mo)).
End TailStmts.

Section ATop.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable FZP : fuzz_params.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis AHM : RHEAP_ahm H.
  Hypothesis FPO : fz_params_ok FZP.
  Hypothesis DL : asan_driver_laws H.
  Hypothesis TR : as_target_run_stmt H FZP.
  Hypothesis LIVE : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H.
  Hypothesis TUS : atail_usage_stmt H FZP.
  Hypothesis TOP : atail_open_stmt H FZP.
  Hypothesis TRD : atail_rderr_stmt H FZP.
  Variables (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF0 : machine_state) (mo0 : Model)
            (regs0 : bvmap 5 word) (mem0 : word -> option byte) (B tid can : Z).
  Hypothesis Hva : valid_argv argv.
  Hypothesis PRE : AMpre H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can.

  Let rom := seg_rom asegs.
  Let Hvsp : valid_sp sp0. Proof. exact (am_vsp _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
  Let HCE : hceil + 8388608 <= bv_unsigned sp0. Proof. exact (am_ceil _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
  Let Htid : 0 < tid < 2 ^ 22. Proof. exact (proj2 (am_tid _ _ _ _ _ _ _ _ _ _ _ _ PRE)). Qed.
  Let TRC : adrv_traces H FZP. Proof. exact (am_tr _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
  Let SPlo : 0x7fff80000000 <= bv_unsigned sp0. Proof. exact (proj1 Hvsp). Qed.
  Let SPhi : bv_unsigned sp0 <= 0x800000000000. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Let SP16 : bv_unsigned sp0 mod 16 = 0. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Let lo : Z := bv_unsigned sp0 - 128 - ATR_STACK.
  Let Elo : lo = bv_unsigned sp0 - 128 - 69632. Proof. reflexivity. Qed.
  Let COSTS : cost_laws H. Proof. exact (ah_costs H HH). Qed.

  Lemma aceil_loT : aceil + 4096 <= lo.
  Proof. pose proof Elo. pose proof HCE. acb. lia. Qed.

  Lemma amst_at_win : forall M (a n : Z), frame_mod mem0 M [(Z_to_bv 64 a, n)] ->
    lo <= a -> a + n <= bv_unsigned sp0 -> 0 <= n -> amframe sp0 M -> mstatics H sp0 tid can mem0 M.
  Proof.
    intros M wa' wn FM Wlo Whi Wn FA. pose proof SPlo. pose proof SPhi. pose proof Elo. pose proof aceil_loT as HCL. acb.
    destruct PRE as [_ _ _ _ _ _ _ _ _ STK SH0 _ INV RELRO GLB AC CELLS OUT TID ERR CAN RFS LATCH RH AUX _ _ _ DST].
    pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
    unfold ivls in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _]. unfold AIMG_TOP in F1.
    assert (T : forall (a : Z) n bs, rdn RSEGS mem0 (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= AIMG_TOP -> rdn RSEGS M (Z_to_bv 64 a) n = Some bs).
    { intros a n bs RD Ha Hn. unfold AIMG_TOP in Hn. eapply ardn_frame; [exact FM | exact RD | lia | lia |].
      intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia. }
    split.
    - eapply amem_inv_frame; [exact INV | exact FM |]. constructor; [|constructor]. cbn [fst snd]. rewrite u_small by lia. lia.
    - apply (astk_grows mem0 M); [exact STK | unfold AMLO, ATR_STACK; lia | lia | exact (proj2 FM)].
    - eapply ACONST_frame; [exact AC | exact MU | exact WM |]. constructor; [|constructor]. apply aconst_ok_hi. cbn [fst]. unfold AHI_LO. lia.
    - intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. cbn. lia.
    - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq; apply MU;
        rewrite wa_eq, u_small by lia; cbn; lia.
    - eapply cells_ok_munchW; [apply adrv_cells_wf | exact CELLS | exact MU |].
      eapply Forall_impl; [| apply adrv_cells_range]. intros [[a w] v] Ra. cbn. lia.
    - eapply cells_ok_munchW; [apply astdout0_wf | exact OUT | exact MU |].
      eapply Forall_impl; [| apply astdout0_range]. intros [[a w] v] Ra. cbn. lia.
    - destruct TID as [TID Ht]. split; [|exact Ht]. apply T; [exact TID | lia | unfold AIMG_TOP; cbn; lia].
    - destruct CAN as [CAN Hc]. split; [|exact Hc]. apply T; [exact CAN | lia | unfold AIMG_TOP; cbn; lia].
    - eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM |].
      constructor; [|constructor]. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. lia.
    - destruct LATCH as [ib Hib]. exists ib. apply T; [exact Hib | lia | unfold AIMG_TOP; cbn; lia].
    - destruct SH0 as [shi [SH0 Hshi]]. exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
      constructor; [|constructor]. apply stack0_ok_app. cbn [fst]. unfold AHI_LO. lia.
    - intros x Hx. apply (proj1 FM). cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia.
    - exact FA.
    - destruct AUX as [AUX HB]. exists B. split; [|exact HB]. eapply (ah_rauxv_frame H HH []); [exact AUX | exact MU | exact WM |].
      constructor; [|constructor]. left. cbn [fst]. lia.
    - eapply adstat_eq; [exact DST|]. intros x Hx. unfold adstat_win in Hx. apply MU. rewrite wa_eq, u_small by lia. cbn. lia.
  Qed.

  Lemma amst_at_open : forall M, frame_mod mem0 M (regA_w sp0) -> amframe sp0 M -> mstatics H sp0 tid can mem0 M.
  Proof.
    intros M FM FA. pose proof SPlo. pose proof Elo. unfold regA_w in FM. eapply (amst_at_win M _ _ FM); [lia | lia | lia | exact FA].
  Qed.

  Lemma arh_at_open : forall M, frame_mod mem0 M (regA_w sp0) -> as_RHEAP H s0 [] M.
  Proof.
    intros M FM. pose proof SPlo. pose proof SPhi. pose proof Elo. pose proof aceil_loT as HCL. acb.
    pose proof (frame_mod_munch _ _ _ FM) as MU. unfold regA_w, ivls in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    eapply (ah_RHEAP_frame H HH); [exact (am_heap _ _ _ _ _ _ _ _ _ _ _ _ PRE) | exact MU | exact (aframe_mod_wmono _ _ _ FM) |].
    constructor; [|constructor]. left. cbn [fst]. lia.
  Qed.

  Lemma ahm_of_heap : forall s LB m, as_RHEAP H s LB m -> exists TB, ahm_ok m TB.
  Proof. intros s LB m RH. exact (AHM s LB m RH). Qed.
  Lemma rheap_win : forall s LB m M (a n : Z), as_RHEAP H s LB m -> frame_mod m M [(Z_to_bv 64 a, n)] ->
    lo <= a -> a + n <= bv_unsigned sp0 -> 0 <= n -> as_RHEAP H s LB M.
  Proof.
    intros s LB m M a n RH FM Hlo Hhi Hn. pose proof SPlo. pose proof SPhi. pose proof Elo. pose proof aceil_loT as HCL. acb.
    pose proof (frame_mod_munch _ _ _ FM) as MU. unfold ivls in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact (aframe_mod_wmono _ _ _ FM) |].
    constructor; [|constructor]. left. cbn [fst]. lia.
  Qed.

  Lemma aleft0_of_main : forall AL AL1, AMAIN_COST H FZP <= AL -> AL1 >= AL - as_Cm H 65536 -> aleft H FZP 0 <= AL1.
  Proof.
    intros AL AL1 H0 H1. unfold AMAIN_COST in H0. unfold aleft, CU26, TRC26.
    destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6).
    pose proof (C1 65536 ltac:(lia)). pose proof (C2 65536 (2 ^ 26) ltac:(lia)). pose proof (C1 (2 ^ 26) ltac:(lia)). pose proof (C3 (2 ^ 26) ltac:(lia)).
    nia.
  Qed.
  Lemma Cm_main : forall AL, AMAIN_COST H FZP <= AL -> as_Cm H 65536 <= AL.
  Proof.
    intros AL H0. unfold AMAIN_COST in H0. destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6).
    pose proof (C1 65536 ltac:(lia)). pose proof (C2 65536 (2 ^ 26) ltac:(lia)). pose proof (C1 (2 ^ 26) ltac:(lia)). pose proof (C3 (2 ^ 26) ltac:(lia)).
    pose proof (fuzz_cost_mono FZP FPO sp0 (2 ^ 26) (2 ^ 26) ltac:(lia)). nia.
  Qed.

  Section TwoArgs.
    Variables a0s path : list byte.
    Hypothesis Hargv : argv = [a0s; path].
    Variables (p0 pp : Z).
    Hypothesis Hp0 : rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p0)) /\ astr_at mem0 sp0 p0 a0s.
    Hypothesis Hpp : rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned sp0 + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pp)) /\ astr_at mem0 sp0 pp path.
    Let ppw : word := Z_to_bv 64 pp.
    Let E0 := AENV (avals0 sp0 p0 pp tid can regs0).

    Lemma first_alloc : forall R M msF mo K,
      as_VIS H s0 msF = mkst R (Z_to_bv 64 AMALLOC_STUB) M rom -> as_AKREL H s0 (mkCfg msF mo) ->
      getr R 1 = Z_to_bv 64 0xe8448 -> getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 4 = Z_to_bv 64 0x6c5858 ->
      getr R 8 = Z_to_bv 64 2 -> getr R 10 = Z_to_bv 64 0x10000 -> getr R 18 = ppw -> getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 0x10000 ->
      mstatics H sp0 tid can mem0 M -> as_RHEAP H s0 [] M -> AMAIN_COST H FZP <= as_AL H s0 ->
      (forall regs' mem' msF' mo' A p s,
         as_VIS H s msF' = mkst regs' (Z_to_bv 64 AREAD_STUB) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
         aread_call_regs sp0 regs' ppw A 0 65536 65536 -> as_RHEAP H s [(p, A, 65536)] mem' ->
         (exists junk, rw_cells asegs mem' A [CB (Z.to_nat 65536) junk]) -> addressable mem' A 65536 ->
         mstatics H sp0 tid can mem0 mem' -> aleft H FZP 0 <= as_AL H s ->
         m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
         realizes asegs (mkCfg msF' mo') K) ->
      realizes asegs (mkCfg msF mo) K.
    Proof.
      intros R M msF mo K HV HA Q1 Q2 Q4 Q8 Q10 Q18 Q20 Q21 ST RH HAL HK.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo. pose proof aceil_loT as HCL. acb.
      destruct (aerrno_rw_any M) as [errv ERR]. destruct (mst_aux H sp0 tid can mem0 _ ST) as [B' [AUXB HB']].
      assert (STKlo : stk asegs M lo (bv_unsigned sp0 - 128)).
      { destruct (mst_stk H sp0 tid can mem0 _ ST) as (S1 & S2 & S3). split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia. }
      eapply (amalloc_call H HH DL R M msF mo s0 [] 65536 lo B' errv 0xe8448 [] K HV HA Q1);
        [ lia | reflexivity | exact Q4 | exact Q10 | lia | exact RH
        | apply (ah_alloc H HH s0 [] M 65536 RH); [lia | cbn [lb_bytes fold_right]; unfold ADRV_LIVE in LIVE; lia | cbn [length]; unfold ADRV_CNT in LIVE; lia]
        | apply Cm_main; exact HAL
        | exact AUXB | rewrite Q2, u_small by lia; lia
        | rewrite Q2, u_small by lia; exact STKlo | lia | rewrite Q2, u_small by lia; unfold AMALLOC_STACK; lia
        | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
        | rewrite Q4, u_small by lia; exact ERR | exact (mst_inv H sp0 tid can mem0 _ ST) | exact (mst_ac H sp0 tid can mem0 _ ST)
        | apply (ah_chain_nil H HH); rewrite Q8, u_small by lia; lia
        | cbn [map]; destruct TRC as (T1 & _); exact T1 |].
      rewrite Q2, !u_small by lia.
      intros regsC memC msFC moC A p s1 errv1 junk HVC HAC MPC KEPTC R10 INVC STKC ERRC AUXC HPC BR RHC CBC ADC ACC HALC.
      pose proof (mo_mp H DL _ _ MPC) as EQC.
      assert (STC : mstatics H sp0 tid can mem0 memC).
      { eapply (mstatics_apres H HH sp0 tid can mem0 Hvsp M memC); [exact ST | exact HPC | exact INVC | exact STKC | exact ACC | exact AUXC | exact HB']. }
      pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold AIMG_TOP in B4.

      assert (S2 : getr regsC 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)) by (kept KEPTC (2:reg)%bv Q2).
      assert (S4 : getr regsC 4 = Z_to_bv 64 0x6c5858) by (kept KEPTC (4:reg)%bv Q4).
      assert (S8 : getr regsC 8 = Z_to_bv 64 2) by (kept KEPTC (8:reg)%bv Q8).
      assert (S18 : getr regsC 18 = ppw) by (kept KEPTC (18:reg)%bv Q18).
      assert (S20 : getr regsC 20 = Z_to_bv 64 3) by (kept KEPTC (20:reg)%bv Q20).
      assert (S21 : getr regsC 21 = Z_to_bv 64 0x10000) by (kept KEPTC (21:reg)%bv Q21).
      eapply (aseg_E H DL sp0 Hvsp s1 msFC moC regsC memC ppw A K);
        [ split; [exact S2 | split; [exact S4 | split; [exact S8 | split; [exact S18 | exact S20]]]]
        | exact R10 | lia | exact S21
        | exact (mst_stk_ok H sp0 tid can mem0 Hvsp _ STC) | exact (mst_ro H sp0 tid can mem0 _ STC) | exact (mst_relro H sp0 tid can mem0 _ STC) | | exact HVC | exact HAC ].
      intros regsD memD msFD moD HVD HAD SBD NRD FMD STKD.
      pose proof (mstatics_frameL H HH sp0 tid can mem0 Hvsp HCE _ _ STC FMD) as STD.
      pose proof (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RHC FMD) as RHD.
      destruct (blkR_frameL H sp0 Hvsp HCE A 65536 memC memD junk 0%nat [] BR FMD CBC ADC ltac:(reflexivity) ltac:(lia)) as (CBD & ADD & _).

      eapply (aseg_N H DL sp0 Hvsp s1 msFD moD regsD memD ppw A 0 65536 K NRD); [lia | lia
        | exact STKD | exact (mst_ro H sp0 tid can mem0 _ STD) | exact (mst_relro H sp0 tid can mem0 _ STD) | | exact HVD | exact HAD].
      intros regsE memE msFE moE HVE HAE SBE RCE FME STKE.
      pose proof (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RHD FME) as RHE.
      destruct (blkR_frameL H sp0 Hvsp HCE A 65536 memD memE junk 0%nat [] BR FME CBD ADD ltac:(reflexivity) ltac:(lia)) as (CBE & ADE & _).
      pose proof (mo_tr _ _ _ EQC (mo_tr _ _ _ (mo_sb _ _ SBD) (mo_sb _ _ SBE))) as [EFS EFDS].
      change (Z_to_bv 64 0xa36a4) with (Z_to_bv 64 AREAD_STUB) in HVE.
      apply (HK regsE memE msFE moE A p s1 HVE HAE).
      - change (65536 - 0) with 65536 in RCE. exact RCE.
      - exact RHE.
      - exists junk. exact CBE.
      - exact ADE.
      - eapply (mstatics_frameL H HH sp0 tid can mem0 Hvsp HCE); [exact STD | exact FME].
      - apply (aleft0_of_main (as_AL H s0)); [exact HAL | exact HALC].
      - exact EFS.
      - exact EFDS.
    Qed.

    Lemma ARInv0 : forall data fs0 mo regs' mem' mo' A p s,
      m_fs mo = fs0 -> m_fds mo = fd_insert (m_fds mo0) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)) ->
      aread_call_regs sp0 regs' ppw A 0 65536 65536 -> as_RHEAP H s [(p, A, 65536)] mem' ->
      (exists junk, rw_cells asegs mem' A [CB (Z.to_nat 65536) junk]) -> addressable mem' A 65536 ->
      mstatics H sp0 tid can mem0 mem' -> aleft H FZP 0 <= as_AL H s ->
      m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
      ARInv H FZP sp0 pp tid can path data fs0 mem0 0 65536 A s p regs' mem' mo'.
    Proof.
      intros data fs0 mo regs' mem' mo' A p s FS FDS RC RH HCB AD ST HAL FS' FDS'.
      pose proof (am_fds _ _ _ _ _ _ _ _ _ _ _ _ PRE) as FDS0.
      split; try assumption.
      - lia.
      - lia.
      - exists 0. split; [lia|]. split; [reflexivity | exact HAL].
      - reflexivity.
      - rewrite FS'. exact FS.
      - rewrite FDS', FDS. apply fd_lookup_insert_eq.
      - rewrite FDS', FDS, fd_lookup_insert_neq, FDS0; [reflexivity | intros E; apply (f_equal bv_unsigned) in E; discriminate].
      - rewrite FDS', FDS, fd_lookup_insert_neq, FDS0; [reflexivity | intros E; apply (f_equal bv_unsigned) in E; discriminate].
    Qed.

    Lemma t_body_split : forall (data : list byte) fs,
      Z.of_nat (length data) < MAX_INPUT ->
      t_body data fs =
        if (length data <? 6)%nat then t_die msg_short fs
        else if (length data <? 6 + Z.to_nat (hdr_cfg data))%nat then t_die msg_overrun fs
        else t_emit (W 1 (zero_lines (hdr_calls data))) (t_exit (exit_code 0) fs).
    Proof.
      intros data fs Hlen. unfold t_body. cbv zeta.
      replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
      unfold hdr_calls, hdr_cfg, hdr_b. reflexivity.
    Qed.

    Lemma Cf_of_aleft : forall k AL cap, 0 <= k <= 10 -> aleft H FZP k <= AL -> 0 <= cap <= 2 ^ 26 -> as_Cf H cap <= AL.
    Proof.
      intros k AL cap Hk HAL Hcap. pose proof (aleft_final H FZP HH sp0 Hvsp k AL Hk HAL) as X. unfold TRC26 in X.
      pose proof (Cf_le26 H HH sp0 cap Hcap). pose proof (Cf_le26 H HH sp0 (2 ^ 26) ltac:(lia)). pose proof (Cm_le26 H HH sp0 (2 ^ 26) ltac:(lia)).
      pose proof (fuzz_cost_mono FZP FPO sp0 (2 ^ 26) (2 ^ 26) ltac:(lia)). lia.
    Qed.
    Lemma TR_of_aleft : forall k AL (d : list byte), 0 <= k <= 10 -> aleft H FZP k <= AL ->
      Z.of_nat (length d) < MAX_INPUT -> 6 + hdr_cfg d <= Z.of_nat (length d) -> atr_cost H FZP d <= AL /\ forall AL2 cap, AL2 >= AL - atr_cost H FZP d -> 0 <= cap <= 2 ^ 26 -> as_Cf H cap <= AL2.
    Proof.
      intros k AL d Hk HAL Hd H6. pose proof (aleft_final H FZP HH sp0 Hvsp k AL Hk HAL) as X.
      pose proof (atr_cost_le H FZP FPO HH sp0 Hvsp d Hd H6) as Y.
      pose proof (Cf_le26 H HH sp0 (2 ^ 26) ltac:(lia)) as Z1.
      split; [lia|]. intros AL2 cap H2 Hcap. pose proof (Cf_le26 H HH sp0 cap Hcap). lia.
    Qed.

    Lemma k_le_10 : forall k cap, 0 <= k -> cap = 65536 * 2 ^ k -> cap <= 67108864 -> k <= 10.
    Proof.
      intros k cap Hk E Hc. destruct (Z_lt_le_dec 10 k) as [Hgt|]; [|lia]. exfalso.
      pose proof (Z.pow_le_mono_r 2 11 k ltac:(lia) ltac:(lia)) as X. change (2 ^ 11) with 2048 in X. lia.
    Qed.

    Lemma Permutation_single : forall {A : Type} (a : A) (l : list A), Permutation l [a] -> l = [a].
    Proof. intros A0 a l P. apply Permutation_sym in P. apply Permutation_length_1_inv in P. exact P. Qed.

    Lemma hf_after : forall m regs regs' m' s p A cap junk,
      mstatics H sp0 tid can mem0 m -> hfPost regs m (Z_to_bv 64 (bv_unsigned sp0 - 128)) can regs' m' ->
      as_RHEAP H s [(p, A, cap)] m -> rw_cells asegs m A [CB (Z.to_nat cap) junk] -> addressable m A cap ->
      xstat H sp0 m' /\ ostate [] m' /\ as_RHEAP H s [(p, A, cap)] m'
      /\ rw_cells asegs m' A [CB (Z.to_nat cap) junk] /\ addressable m' A cap.
    Proof.
      intros m regs regs' m' s p A cap junk ST PO RH HCB AD.
      pose proof SPlo. pose proof SPhi. pose proof Elo. pose proof aceil_loT as HCL. acb.
      destruct ST as [INV STK AC RELRO [G1 G2] CELLS OUT [TID Ht] [CAN Hc] RFS LATCH [shi [SH0 Hshi]] ABOVE [FRa FRs] [B' [AUX HB']]].
      destruct PO as [P_sp P_a0 P_cs FM P_flags P_rpos P_rend P_wend P_wpos P_wbase P_mode P_lock P_buf P_bsz P_lbf P_can P_stk].
      rewrite u_small in FM by lia.
      pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
      unfold ivls, HF_FR in MU. cbn [map fst snd] in MU. rewrite !u_small in MU by lia.
      pose proof (ah_blocks H HH _ _ _ (p, A, cap) RH ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in B4.
      assert (T : forall (a : Z) n bs, rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= AIMG_TOP ->
                 (a + Z.of_nat n <= 0x189920 \/ 0x189a08 <= a) -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
      { intros a n bs RD Ha Hn Hd. unfold AIMG_TOP in Hn. eapply rdn_munchW; [exact MU | exact RD | lia | lia |]. intros x Hx. cbn. lia. }
      split; [|split; [|split; [|split]]].
      - split.
        + eapply amem_inv_frame; [exact INV | exact FM |]. unfold HF_FR. constructor; [|constructor; [|constructor]]; cbn [fst snd]; rewrite u_small by lia; lia.
        + apply (astk_grows m m'); [exact STK | lia | lia | exact (proj2 FM)].
        + eapply ACONST_frame; [exact AC | exact MU | exact WM |]. constructor; [apply aconst_ok_hi; cbn [fst]; unfold AHI_LO; lia | constructor; [|constructor]].
          apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
            AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP in *;
            rewrite ?ASHADOW_BASE_val; cbn [fst snd]; lia.
        + intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. cbn. lia.
        + split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq; apply MU; rewrite wa_eq, u_small by lia; cbn; lia.
        + eapply cells_ok_munchW; [apply xdrv2_wf | apply xdrv2_of; exact CELLS | exact MU |].
          eapply Forall_impl; [| apply xdrv2_range]. intros [[a w] v] Ra. cbn. lia.
        + exists tid. split; [|exact Ht]. apply T; [exact TID | lia | unfold AIMG_TOP; cbn; lia | cbn; lia].
        + exists can. split; [|exact Hc]. apply T; [exact CAN | lia | unfold AIMG_TOP; cbn; lia | cbn; lia].
        + split.
          * eapply rdn_munchW; [exact MU | exact FRa | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
          * intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w. eapply rdn_munchW; [exact MU | exact Hw | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
        + exists B'. split; [|exact HB']. eapply (ah_rauxv_frame H HH []); [exact AUX | exact MU | exact WM |].
          constructor; [left; cbn [fst]; lia | constructor; [|constructor]]. right; left. unfold aimg_client_w. cbn [fst snd]. lia.
        + exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
          constructor; [apply stack0_ok_app; cbn [fst]; unfold AHI_LO; lia | constructor; [| constructor]].
          right. cbn [snd]. unfold sh. rewrite ASHADOW_BASE_val. clear - ACEILB. Z.div_mod_to_equations. lia.
      - left. split; [reflexivity|]. split; [|split].
        + unfold xk_stderr2, cells_ok. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
        + eapply cells_ok_munchW; [apply astdout0_wf | exact OUT | exact MU |].
          eapply Forall_impl; [| apply astdout0_range]. intros [[a w] v] Ra. cbn. lia.
        +
          eapply cells_ok_munchW; [apply xk_atxU_wf | apply xk_atxU_of; exact CELLS | exact MU |].
          eapply Forall_impl; [| apply xk_atxU_range]. intros [[a w] v] Ra. cbn. lia.
      - eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM |].
        constructor; [left; cbn [fst]; lia | constructor; [|constructor]]. right; left. unfold aimg_client_w. cbn [fst snd]. lia.
      - eapply rw_cells_transport; [exact HCB | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia.
      - eapply addressable_transport; [exact AD | exact MU | exact WM |]. cbn.
        pose proof (sh_aapp_range A cap B7 B3) as (X1 & X2 & X3). unfold AHI_LO in X3. change (sh AIMG_TOP) with 0x800d5000 in X1. lia.
    Qed.

    Lemma xstat_after_tr : forall (fx' : DFP) m A cap data p s LB mo regs m' regs' msF' mo' s',
      mstatics H sp0 tid can mem0 m ->
      ATRpost H FZP fx' (Z_to_bv 64 (bv_unsigned sp0 - 128)) A cap data p s LB mo regs m regs' m' msF' mo' s' ->
      xstat H sp0 m'.
    Proof.
      intros fx' m A cap data p s LB mo regs m' regs' msF' mo' s' ST PO. pose proof SPlo. pose proof SPhi. pose proof Elo.
      destruct ST as [INV STK AC RELRO GLB CELLS OUT TID CAN RFS LATCH SH0 ABOVE [FRa FRs] AUX].
      destruct PO as [_ _ _ _ _ _ _ QAB QSTK QSTKC _ _ [B2 [AUX2 HB2]] _ _ _ [INV' AC' RELRO' GLB' CELLS' TID' ERR' CAN' RFS' SH0'] _ _ _ _].
      rewrite !u_small in * by lia.
      assert (T : forall (a : Z) n bs, rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> bv_unsigned sp0 - 128 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                 rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
      { intros a n bs RD Ha Hn. destruct n as [|n']; [cbn in *; exact RD|].
        rewrite (rdn_ext RSEGS (S n') m' m); [exact RD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia. apply QAB. lia. }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct QSTKC as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp0 - 128)) as [L|L]; [apply S3'; unfold ATR_STACK; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply QAB; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - apply xdrv2_ofT. exact CELLS'.
      - split.
        + apply T; [exact FRa | lia | cbn; lia].
        + intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w. apply T; [exact Hw | lia | cbn; lia].
      - exists B2. split; [exact AUX2 | lia].
    Qed.

    Lemma abuf_bytes_of_rdn : forall m (A : Z) (data : list byte),
      rdn RSEGS m (Z_to_bv 64 A) (length data) = Some data -> 0 <= A -> A + Z.of_nat (length data) < 2 ^ 64 -> abuf_bytes m A data.
    Proof.
      intros m A data HD HA HAn i Hi. pose proof (rdn_nth RSEGS m (length data) (Z_to_bv 64 A) data i HD Hi) as R.
      unfold nat_to_word in R. rewrite Z_to_bv_add64 in R. exact R.
    Qed.

    Section File.
      Variable data : list byte.
      Hypothesis Hdata : fs_lookup (m_fs mo0) path = Some data.

      Lemma after_tr : forall (fx' : DFP) A cap p s mo regs mem regs2 mem2 msF2 mo2 s2 k,
        mstatics H sp0 tid can mem0 mem ->
        ATRpost H FZP fx' (Z_to_bv 64 (bv_unsigned sp0 - 128)) A cap data p s [(p, A, cap)] mo regs mem regs2 mem2 msF2 mo2 s2 ->
        getr regs 9 = Z_to_bv 64 A ->
        0 <= k <= 10 -> aleft H FZP k <= as_AL H s -> Z.of_nat (length data) < MAX_INPUT -> 6 + hdr_cfg data <= Z.of_nat (length data) ->
        0 <= cap <= 2 ^ 26 ->
        realizes asegs (mkCfg msF2 mo2) (t_emit (W 1 (zero_lines (Nat.pred (hdr_calls data)))) (t_exit (exit_code 0) (m_fs mo))).
      Proof.
        intros fx' A cap p s mo regs mem regs2 mem2 msF2 mo2 s2 k ST PO R9 Hk HAL HLT H6 Hcap.
        pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (hdr_calls_range data) as HCR.
        pose proof (xstat_after_tr fx' _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST PO) as XS2.
        destruct PO as [HV2 HA2 MP2 Q2 Q4 Q10 QCS QAB QSTK QSTKC [LB' [RH' PERM]] QAL QAUX QDATA QADDR [junk QCB] QST QOUT QFS QFD1 QFD2].
        rewrite (Permutation_single _ _ PERM) in RH'.
        destruct (amain_ret_0 regs2 mem2 (seg_rom asegs) Q10) as (regs3 & RUN & E8 & E10 & KEEP).
        lazymatch type of RUN with _ _ (mkst _ ?pc _ _) (mkst _ ?pc' _ _) =>
          replace (Z_to_bv 64 0xe8568) with pc in HV2 by (apply bv_eq; reflexivity) end.
        eapply (drv_msteps H DL s2 msF2 regs2 _ mem2 regs3 _ mem2 mo2 _ HV2 HA2 RUN).
        intros msF3 mo3 HV3 HA3 SB3.
        lazymatch type of HV3 with _ = mkst _ ?pc' _ _ => replace pc' with (Z_to_bv 64 0xe85e8) in HV3 by (apply bv_eq; reflexivity) end.
        assert (NE : forall r : reg, In r [2; 4; 9]%bv -> r <> 1%bv /\ r <> 8%bv /\ r <> 10%bv /\ r <> 11%bv).
        { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; repeat split; intros E; apply (f_equal bv_unsigned) in E; discriminate. }
        assert (K2 : getr regs3 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
        { destruct (NE 2%bv ltac:(in_solve)) as (N1 & N2 & N3 & N4). rewrite (KEEP _ N1 N2 N3 N4). exact Q2. }
        assert (K4 : getr regs3 4 = Z_to_bv 64 ATP).
        { destruct (NE 4%bv ltac:(in_solve)) as (N1 & N2 & N3 & N4). rewrite (KEEP _ N1 N2 N3 N4). exact Q4. }
        assert (K9 : getr regs3 9 = Z_to_bv 64 A).
        { destruct (NE 9%bv ltac:(in_solve)) as (N1 & N2 & N3 & N4). rewrite (KEEP _ N1 N2 N3 N4), (QCS 9%bv ltac:(in_solve)). exact R9. }
        rewrite <- QFS, <- (same_but_materialized_fs _ _ SB3). rewrite <- (exit_code_and_255 0) by lia. unfold exit_code. rewrite <- E8.
        eapply (free_exit H FZP HH AHM DL sp0 tid Hvsp HCE Htid TRC s2 msF3 mo3 regs3 mem2 p A cap (getr regs3 8) _ junk HV3 HA3 K2 K4 eq_refl K9);
          [ rewrite E8, u_small by lia; lia | exact RH' | exact QCB | exact QADDR
          | destruct (TR_of_aleft k (as_AL H s) data Hk HAL HLT H6) as [_ X]; apply (X _ cap QAL); lia
          | exact XS2
          | right; exists (Nat.pred (hdr_calls data)); split; [lia|]; split; [exact QOUT|];
            split; [apply xk_err0_ofT; destruct QST; assumption |];
            split; [apply xk_atxT_of; destruct QST; assumption | reflexivity]
          | rewrite (same_but_materialized_fds _ _ SB3); exact QFD1 ].
      Qed.

      Lemma hfH_of : forall regs m, mstatics H sp0 tid can mem0 m -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) ->
        hfH regs m (Z_to_bv 64 (bv_unsigned sp0 - 128)) can.
      Proof.
        intros regs m ST R2. pose proof SPlo. pose proof SPhi. pose proof SP16. pose proof Elo.
        destruct ST as [INV STK AC RELRO GLB CELLS OUT TID [CAN Hc] RFS LATCH SH0 ABOVE FR AUX].
        split.
        - exact R2.
        - rewrite u_small by lia. rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
        - unfold ASP_LO. rewrite u_small by lia. lia.
        - unfold ASP_HI. rewrite u_small by lia. lia.
        - eapply astk_stk_ok; [exact STK | unfold HF_FR; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold HF_FR; lia | lia].
        - exact (amem_inv_ro_none _ INV).
        - exact RELRO.
        - apply hf_cells_of; assumption.
        - exact CAN.
        - exact Hc.
      Qed.

      Lemma x_header : forall s msF mo regs mem p A cap,
        as_VIS H s msF = mkst regs (Z_to_bv 64 0x177adc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
        AXInv H FZP sp0 pp tid can data (m_fs mo0) mem0 cap A s p regs mem mo ->
        realizes asegs (mkCfg msF mo) (t_body data (m_fs mo0)).
      Proof.
        intros s msF mo regs mem p A cap HV HA [R1 R2 R4 R8 R9 R10 R17 R18 R19 R20 R21 R22 XCAP XLT [k (Hk & HPOW & HAL)] RH [junk HCB] AD XDATA ST XRA XFS XFD1 XFD2].
        pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SP16. pose proof Elo. pose proof aceil_loT as HCL. acb.
        pose proof (hdr_cfg_range data) as Hcr. pose proof (hdr_calls_range data) as HCR. unfold MAX_INPUT in XLT.
        pose proof (k_le_10 k cap Hk HPOW ltac:(lia)) as Hk10.
        pose proof (ah_blocks H HH _ _ _ (p, A, cap) RH ltac:(left; reflexivity)) as BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
        cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in B4.
        rewrite t_body_split by (unfold MAX_INPUT; lia).
        assert (RC : aclose_ret_regs sp0 regs ppw A (Z.of_nat (length data)) cap) by (repeat split; assumption).
        assert (STK0 : stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK) by exact (mst_stk_ok H sp0 tid can mem0 Hvsp _ ST).
        assert (RO : aro_none mem) by exact (mst_ro H sp0 tid can mem0 _ ST).
        assert (BB : abuf_bytes mem A data) by (apply abuf_bytes_of_rdn; [exact XDATA | lia | lia]).
        destruct (Nat.ltb_spec (length data) 6) as [L6|L6].
        -
          eapply (aseg_Hs H DL sp0 Hvsp s msF mo regs mem ppw A (Z.of_nat (length data)) cap _ RC ltac:(lia) STK0 RO (mst_relro H sp0 tid can mem0 _ ST) XRA);
            [| exact HV | exact HA].
          intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 (Q2 & Q4 & Q8 & Q18 & Q20) Q9 FM1 STK1.
          pose proof (mstatics_frameL H HH sp0 tid can mem0 Hvsp HCE _ _ ST FM1) as ST1.
          pose proof (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RH FM1) as RH1.
          destruct (blkR_frameL H sp0 Hvsp HCE A cap mem mem1 junk 0%nat [] BR FM1 HCB AD ltac:(reflexivity) ltac:(lia)) as (CB1 & AD1 & _).
          unfold t_die.
          eapply (drv_hdr_short H DL s msF1 mo1 regs1 mem1 _ can (t_exit (exit_code 2) (m_fs mo0)) (hfH_of regs1 mem1 ST1 Q2) HV1 HA1);
            [ rewrite (same_but_materialized_fds _ _ SB1); exact XFD2 | apply t_exit_has_nil |].
          intros regs2 mem2 msF2 mo2 PO HV2 HA2 SB2.
          destruct (hf_after _ _ _ _ s p A cap junk ST1 PO RH1 CB1 AD1) as (XS2 & OS2 & RH2 & CB2 & AD2).
          pose proof PO as [P_sp _ P_cs _ _ _ _ _ _ _ _ _ _ _].
          rewrite <- XFS, <- (same_but_materialized_fs _ _ SB1), <- (same_but_materialized_fs _ _ SB2).
          rewrite <- (exit_code_and_255 2) by lia.
          eapply rz_conseq; [| apply t_emit_W_nil; apply t_exit_has_nil].
          rewrite <- Q8, <- (P_cs 8%bv ltac:(in_solve)).
          eapply (free_exit H FZP HH AHM DL sp0 tid Hvsp HCE Htid TRC s msF2 mo2 regs2 mem2 p A cap (getr regs2 8) [] junk HV2 HA2 P_sp);
            [ rewrite (P_cs 4%bv ltac:(in_solve)); exact Q4 | reflexivity | rewrite (P_cs 9%bv ltac:(in_solve)); exact Q9
            | rewrite (P_cs 8%bv ltac:(in_solve)), Q8, u_small by lia; lia
            | exact RH2 | exact CB2 | exact AD2
            | apply (Cf_of_aleft k (as_AL H s) cap); [lia | exact HAL | lia]
            | exact XS2 | exact OS2
            | rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1); exact XFD1 ].
        - destruct (Nat.ltb_spec (length data) (6 + Z.to_nat (hdr_cfg data))) as [LO|LO].
          +
            eapply (aseg_Ho H DL sp0 Hvsp s msF mo regs mem ppw A cap data _ RC L6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold MSTK; lia) BB STK0 RO (mst_relro H sp0 tid can mem0 _ ST) XRA);
              [| exact HV | exact HA].
            intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 Q2 Q4 Q8 Q20 Q9 FM1 STK1.
            pose proof (mstatics_frameL H HH sp0 tid can mem0 Hvsp HCE _ _ ST FM1) as ST1.
            pose proof (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RH FM1) as RH1.
            destruct (blkR_frameL H sp0 Hvsp HCE A cap mem mem1 junk 0%nat [] BR FM1 HCB AD ltac:(reflexivity) ltac:(lia)) as (CB1 & AD1 & _).
            unfold t_die.
            eapply (drv_hdr_overrun H DL s msF1 mo1 regs1 mem1 _ can (t_exit (exit_code 2) (m_fs mo0)) (hfH_of regs1 mem1 ST1 Q2) HV1 HA1);
              [ rewrite (same_but_materialized_fds _ _ SB1); exact XFD2 | apply t_exit_has_nil |].
            intros regs2 mem2 msF2 mo2 PO HV2 HA2 SB2.
            destruct (hf_after _ _ _ _ s p A cap junk ST1 PO RH1 CB1 AD1) as (XS2 & OS2 & RH2 & CB2 & AD2).
            pose proof PO as [P_sp _ P_cs _ _ _ _ _ _ _ _ _ _ _].
            rewrite <- XFS, <- (same_but_materialized_fs _ _ SB1), <- (same_but_materialized_fs _ _ SB2).
            rewrite <- (exit_code_and_255 2) by lia.
            eapply rz_conseq; [| apply t_emit_W_nil; apply t_exit_has_nil].
            rewrite <- Q8, <- (P_cs 8%bv ltac:(in_solve)).
            eapply (free_exit H FZP HH AHM DL sp0 tid Hvsp HCE Htid TRC s msF2 mo2 regs2 mem2 p A cap (getr regs2 8) [] junk HV2 HA2 P_sp);
              [ rewrite (P_cs 4%bv ltac:(in_solve)); exact Q4 | reflexivity | rewrite (P_cs 9%bv ltac:(in_solve)); exact Q9
              | rewrite (P_cs 8%bv ltac:(in_solve)), Q8, u_small by lia; lia
              | exact RH2 | exact CB2 | exact AD2
              | apply (Cf_of_aleft k (as_AL H s) cap); [lia | exact HAL | lia]
              | exact XS2 | exact OS2
              | rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1); exact XFD1 ].
          +
            eapply (aseg_Hk H DL sp0 Hvsp s msF mo regs mem ppw A cap data _ RC ltac:(lia) ltac:(lia) ltac:(lia) BB STK0 RO (mst_relro H sp0 tid can mem0 _ ST) XRA);
              [| exact HV | exact HA].
            intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 TC K22 FM1 STK1.
            pose proof (mstatics_frameL H HH sp0 tid can mem0 Hvsp HCE _ _ ST FM1) as ST1.
            pose proof (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RH FM1) as RH1.
            destruct (blkR_frameL H sp0 Hvsp HCE A cap mem mem1 junk (length data) data BR FM1 HCB AD XDATA ltac:(lia)) as (CB1 & AD1 & XDATA1).

            destruct (hdr_calls data) as [|calls'] eqn:EC; [lia|].
            rewrite zero_lines_S. eapply rz_conseq; [| apply t_emit_W_app].
            pose proof TC as (T1 & T2 & T4 & T8 & T9 & T10 & T11 & T12 & T13 & T18 & T19 & T20 & T21).
            destruct (TR_of_aleft k (as_AL H s) data ltac:(lia) HAL ltac:(unfold MAX_INPUT; lia) ltac:(lia)) as [HALT _].
            eapply (TR (Z_to_bv 64 (bv_unsigned sp0 - 128)) A cap data p s [(p, A, cap)] msF1 mo1 regs1 mem1).
            * destruct ST1 as [INV1 STK1' AC1 RELRO1 GLB1 CELLS1 OUT1 TID1 CAN1 RFS1 LATCH1 [shi [SH1 Hshi]] ABOVE1 FR1 [B1' [AUX1 HB1]]].
              assert (ATS : atr_statics H adrv_cells (Z_to_bv 64 (bv_unsigned sp0 - 128)) mem1).
              { split; try assumption; [exists tid; exact TID1 | apply aerrno_rw_any | exists can; exact CAN1 |].
                exists shi. rewrite u_small by lia. split; [exact SH1 | lia]. }
              assert (SOK : stk_ok RSEGS mem1 (Z_to_bv 64 (bv_unsigned sp0 - 128)) ATR_STACK).
              { eapply astk_stk_ok; [exact STK1' | rewrite u_small by lia; unfold ATR_STACK; lia | rewrite u_small by lia; lia | unfold ATR_STACK; lia | lia]. }
              assert (SCJ : stk asegs mem1 (bv_unsigned sp0 - 128 - ATR_STACK) (bv_unsigned sp0 - 128)).
              { destruct STK1' as (S1 & S2 & S3). split; [lia|]. split; [lia|]. intros a Ha. apply S3. unfold ATR_STACK in Ha. lia. }
              split; try assumption; rewrite ?u_small by lia; try lia.
              all: first
                [ unfold hdr_payload_len; assumption
                | rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
                | left; reflexivity
                | cbn [lb_bytes fold_right blk_size snd length Z.of_nat Pos.of_succ_nat]; lia
                | exists B1'; split; [exact AUX1 | lia]
                | exists junk; exact CB1
                | exact TRC | exact LIVE
                | rewrite (same_but_materialized_fds _ _ SB1); assumption ].
            * apply t_emit_has_nil.
            * intros fx2 regs2 mem2 msF2 mo2 s2 PO. replace calls' with (Nat.pred (hdr_calls data)) by (rewrite EC; reflexivity).
              rewrite <- XFS, <- (same_but_materialized_fs _ _ SB1).
              eapply (after_tr fx2 A cap p s mo1 regs1 mem1 regs2 mem2 msF2 mo2 s2 k ST1 PO T9 ltac:(lia) HAL ltac:(unfold MAX_INPUT; lia) ltac:(lia) ltac:(lia)).
      Qed.

      Theorem as_file :
        (length path <= 4095)%nat -> path <> [] -> path_has_slash path = false -> path_is_dirref path = false ->
        realizes asegs (mkCfg msF0 mo0) (t_alt2 (t_die (msg_cannot_open path) (m_fs mo0)) (t_opened data (m_fs mo0))).
      Proof.
        intros Hlen Hne Hsl Hnd. pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo.
        pose proof (am_fds _ _ _ _ _ _ _ _ _ _ _ _ PRE) as FDS0.
        apply (aseg_A H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE a0s path Hargv p0 pp Hp0 Hpp).
        intros R M msF mo HV HA SB HR HK FM FA.
        pose proof (amst_at_open M FM FA) as ST. pose proof (arh_at_open M FM) as RH.
        destruct (aopenat_regs sp0 regs0 tid can p0 pp R HR) as (H17 & H10 & H11 & Hfl).
        pose proof (apath_at_A H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE path p0 pp Hpp M R FM HR Hlen) as PA.
        destruct (mo_sb _ _ SB) as [EFS EFDS].
        assert (Hfree : fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None) by (rewrite EFDS, FDS0; reflexivity).
        unfold t_opened. rewrite <- EFS.
        eapply (drv_openat_file H DL s0 msF R (Z_to_bv 64 0x177ad8) M mo ECALLW AECALL2 is_ecall_ECALLW HV HA H17 H10 Hfl Hfree path data);
          [ exact PA | exact Hne | exact Hsl | exact Hnd | rewrite EFS; exact Hdata | |].
        -
          intros e msF' mo' He HV' HA' SB'. rewrite BAgentLib.v_addi_lit in HV' by lia. change (0x177ad8 + 4)%Z with 0x177adc%Z in HV'.
          eapply (aseg_F H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE p0 pp e R M msF' mo' _ HV' HA' (openat_errnos_range e He) (scF_openat e He) HR HK).
          intros R' M' msF2 mo2 HV2 HA2 SB2 Q2 Q4 Q8 Q18 FM2.
          rewrite <- (same_but_materialized_fs _ _ SB'), <- (same_but_materialized_fs _ _ SB2).
          eapply (TOP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s0 msF2 mo2 R' M' Hva PRE Hargv (proj1 Hpp) (proj2 Hpp) HV2 HA2 Q2 Q4 Q18).
          +
            pose proof (frame_mod_munch _ _ _ FM2) as MU2. unfold aregF_w, ivls in MU2. cbn [map fst snd] in MU2. rewrite !u_small in MU2 by lia.
            eapply (mstatics_munch H HH sp0 tid can mem0 Hvsp HCE M M' _ [] ST MU2 (aframe_mod_wmono _ _ _ FM2)).
            * constructor; [left; cbn [fst snd]; lia | constructor; [right; left; reflexivity | constructor]].
            * eapply amem_inv_frame; [exact (mst_inv H sp0 tid can mem0 _ ST) | exact FM2 |].
              unfold aregF_w. constructor; [| constructor; [|constructor]]; cbn [fst snd]; rewrite u_small by lia; lia.
            * apply (astk_grows M M'); [exact (mst_stk_spm H sp0 tid can mem0 Hvsp _ ST) | lia | lia | exact (proj2 FM2)].
            * eapply ACONST_frame; [exact (mst_ac H sp0 tid can mem0 _ ST) | exact MU2 | exact (aframe_mod_wmono _ _ _ FM2) |].
              constructor; [apply aconst_ok_hi; cbn [fst]; unfold AHI_LO; lia | constructor; [exact aconst_ok_errno | constructor]].
          +
            pose proof (frame_mod_munch _ _ _ FM2) as MU2. unfold aregF_w, ivls in MU2. cbn [map fst snd] in MU2. rewrite !u_small in MU2 by lia.
            apply (ahm_of_heap s0 []). eapply (ah_RHEAP_frame H HH); [exact RH | exact MU2 | exact (aframe_mod_wmono _ _ _ FM2) |].
            constructor; [left; cbn [fst]; acb; lia | constructor; [right; left; unfold aimg_client_w, ATLS_PRIV_LO, ATP; cbn [fst snd]; lia | constructor]].
          + rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB'), EFDS, FDS0. reflexivity.
        -
          intros msF' mo' HV' HA' SB'. rewrite BAgentLib.v_addi_lit in HV' by lia. change (0x177ad8 + 4)%Z with 0x177adc%Z in HV'.
          replace (alloc_fd (m_fds mo)) with (Z_to_bv 64 3) in HV', SB' by (rewrite EFDS, FDS0; reflexivity).
          eapply (aseg_C H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE p0 pp R M msF' mo' _ HV' HA' HR HK).
          intros R' msF2 mo2 HV2 HA2 SB2 Q1 Q2 Q4 Q8 Q10 Q18 Q20 Q21.
          change (Z_to_bv 64 0xba108) with (Z_to_bv 64 AMALLOC_STUB) in HV2.
          eapply (first_alloc R' M msF2 mo2 _ HV2 HA2 Q1 Q2 Q4 Q8 Q10 Q18 Q20 Q21 ST RH (am_al _ _ _ _ _ _ _ _ _ _ _ _ PRE)).
          intros regs3 mem3 msF3 mo3 A p s HV3 HA3 RC RH3 CB3 AD3 ST3 HAL3 FS3 FDS3.
          eapply (loop_sound H FZP FPO HH DL sp0 pp tid can path data (m_fs mo) mem0 Hvsp HCE ltac:(rewrite EFS; exact Hdata) Htid TRC LIVE
                    (length data) 0 65536 A s p regs3 mem3 msF3 mo3).
          + lia.
          + exact HV3.
          + exact HA3.
          + eapply (ARInv0 data (m_fs mo) mo2); try eassumption.
            * rewrite (same_but_materialized_fs _ _ SB2), (same_but_materialized_fs _ _ SB'). reflexivity.
            * rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB'), with_fds_fds, EFDS. reflexivity.
          + intros cap' A' s' p' regs4 mem4 msF4 mo4 HV4 HA4 CI.
            eapply (close_step H FZP DL sp0 pp tid can data (m_fs mo) mem0); [exact HV4 | exact HA4 | exact CI |].
            intros regs5 msF5 mo5 HV5 HA5 XI. rewrite EFS. eapply x_header; [exact HV5 | exact HA5 | rewrite <- EFS; exact XI].
          + intros Hbig A' s' p' regs4 mem4 msF4 mo4 HV4 HA4 RF.
            unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; lia).
            eapply (refuse_exit H AHM DL sp0 tid can Hvsp HCE mem0 pp); [exact HV4 | exact HA4 | exact RF].
      Qed.
    End File.

    Lemma open_fail : forall e R M msF' mo',
      In e openat_errnos \/ e = ENAMETOOLONG \/ e = ENOENT ->
      regs_ok E0 srA R -> know_ok RSEGS E0 M knA -> mstatics H sp0 tid can mem0 M -> frame_mod mem0 M (regA_w sp0) ->
      as_VIS H s0 msF' = mkst (regupd R 10 (errno_ret e)) (Z_to_bv 64 0x177adc) M rom -> as_AKREL H s0 (mkCfg msF' mo') ->
      m_fds mo' = m_fds mo0 ->
      realizes asegs (mkCfg msF' mo') (t_die (msg_cannot_open path) (m_fs mo')).
    Proof.
      intros e R M msF' mo' He HR HK ST FMA HV' HA' EFDS. pose proof (arh_at_open M FMA) as RH. pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo. pose proof aceil_loT as HCL. acb.
      pose proof (am_fds _ _ _ _ _ _ _ _ _ _ _ _ PRE) as FDS0.
      assert (HeR : 1 <= e <= 4095 /\ scF e).
      { destruct He as [He|[->| ->]]; [split; [apply openat_errnos_range | apply scF_openat]; exact He
          | split; [unfold ENAMETOOLONG; lia | exact scF_ENAMETOOLONG] | split; [unfold ENOENT; lia | exact scF_ENOENT]]. }
      destruct HeR as [HeR HSC].
      eapply (aseg_F H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE p0 pp e R M msF' mo' _ HV' HA' HeR HSC HR HK).
      intros R' M' msF2 mo2 HV2 HA2 SB2 Q2 Q4 Q8 Q18 FM2.
      rewrite <- (same_but_materialized_fs _ _ SB2).
      eapply (TOP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s0 msF2 mo2 R' M' Hva PRE Hargv (proj1 Hpp) (proj2 Hpp) HV2 HA2 Q2 Q4 Q18).
      - pose proof (frame_mod_munch _ _ _ FM2) as MU2. unfold aregF_w, ivls in MU2. cbn [map fst snd] in MU2. rewrite !u_small in MU2 by lia.
        eapply (mstatics_munch H HH sp0 tid can mem0 Hvsp HCE M M' _ [] ST MU2 (aframe_mod_wmono _ _ _ FM2)).
        + constructor; [left; cbn [fst snd]; lia | constructor; [right; left; reflexivity | constructor]].
        + eapply amem_inv_frame; [exact (mst_inv H sp0 tid can mem0 _ ST) | exact FM2 |].
          unfold aregF_w. constructor; [| constructor; [|constructor]]; cbn [fst snd]; rewrite u_small by lia; lia.
        + apply (astk_grows M M'); [exact (mst_stk_spm H sp0 tid can mem0 Hvsp _ ST) | lia | lia | exact (proj2 FM2)].
        + eapply ACONST_frame; [exact (mst_ac H sp0 tid can mem0 _ ST) | exact MU2 | exact (aframe_mod_wmono _ _ _ FM2) |].
          constructor; [apply aconst_ok_hi; cbn [fst]; unfold AHI_LO; lia | constructor; [exact aconst_ok_errno | constructor]].
      -
        pose proof (frame_mod_munch _ _ _ FM2) as MU2. unfold aregF_w, ivls in MU2. cbn [map fst snd] in MU2. rewrite !u_small in MU2 by lia.
        apply (ahm_of_heap s0 []). eapply (ah_RHEAP_frame H HH); [exact RH | exact MU2 | exact (aframe_mod_wmono _ _ _ FM2) |].
        constructor; [left; cbn [fst]; acb; lia | constructor; [right; left; unfold aimg_client_w, ATLS_PRIV_LO, ATP; cbn [fst snd]; lia | constructor]].
      - rewrite (same_but_materialized_fds _ _ SB2), EFDS, FDS0. reflexivity.
    Qed.

    Theorem as_open_fail_toolong :
      (4096 <= length path)%nat ->
      realizes asegs (mkCfg msF0 mo0) (t_die (msg_cannot_open path) (m_fs mo0)).
    Proof.
      intros Hlong. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      apply (aseg_A H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE a0s path Hargv p0 pp Hp0 Hpp).
      intros R M msF mo HV HA SB HR HK FM FA.
      pose proof (amst_at_open M FM FA) as ST. destruct (mo_sb _ _ SB) as [EFS EFDS].
      destruct (aopenat_regs sp0 regs0 tid can p0 pp R HR) as (H17 & H10 & H11 & Hfl).
      destruct Hpp as [_ (S1a & S1b & S1c & S1d & S1e)]. pose proof (u64_range (Z_to_bv 64 pp)).
      eapply (drv_openat_toolong H DL s0 msF R (Z_to_bv 64 0x177ad8) M mo ECALLW AECALL2 is_ecall_ECALLW HV HA H17 H10 Hfl (firstn 4096 path)).
      - rewrite H11.
        replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
          by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
        apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
        rewrite <- S1d. apply rdn_agree. intros j Hj. apply (above_A H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE M FM). rewrite (u_small pp) by lia. rewrite u_small by lia. lia.
      - intros Hin. apply S1c. rewrite <- (firstn_skipn 4096 path). apply in_app_iff. left. exact Hin.
      - intros msF' mo' HV' HA' SB'. rewrite BAgentLib.v_addi_lit in HV' by lia. change (0x177ad8 + 4)%Z with 0x177adc%Z in HV'.
        rewrite <- EFS, <- (same_but_materialized_fs _ _ SB').
        apply (open_fail ENAMETOOLONG R M msF' mo' ltac:(right; left; reflexivity) HR HK ST FM HV' HA').
        rewrite (same_but_materialized_fds _ _ SB'). exact EFDS.
    Qed.

    Theorem as_open_fail_empty :
      path = [] ->
      realizes asegs (mkCfg msF0 mo0) (t_die (msg_cannot_open path) (m_fs mo0)).
    Proof.
      intros Hnil. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      apply (aseg_A H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE a0s path Hargv p0 pp Hp0 Hpp).
      intros R M msF mo HV HA SB HR HK FM FA.
      pose proof (amst_at_open M FM FA) as ST. destruct (mo_sb _ _ SB) as [EFS EFDS].
      destruct (aopenat_regs sp0 regs0 tid can p0 pp R HR) as (H17 & H10 & H11 & Hfl).
      pose proof (apath_at_A H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE path p0 pp Hpp M R FM HR ltac:(rewrite Hnil; cbn; lia)) as PA.
      eapply (drv_openat_empty H DL s0 msF R (Z_to_bv 64 0x177ad8) M mo ECALLW AECALL2 is_ecall_ECALLW HV HA H17 H10 Hfl).
      - rewrite Hnil in PA. exact PA.
      - intros msF' mo' HV' HA' SB'. rewrite BAgentLib.v_addi_lit in HV' by lia. change (0x177ad8 + 4)%Z with 0x177adc%Z in HV'.
        rewrite <- EFS, <- (same_but_materialized_fs _ _ SB').
        apply (open_fail ENOENT R M msF' mo' ltac:(right; right; reflexivity) HR HK ST FM HV' HA').
        rewrite (same_but_materialized_fds _ _ SB'). exact EFDS.
    Qed.

    Theorem as_open_fail_absent :
      (length path <= 4095)%nat -> path <> [] -> path_has_slash path = false -> path_is_dirref path = false ->
      fs_lookup (m_fs mo0) path = None ->
      realizes asegs (mkCfg msF0 mo0) (t_die (msg_cannot_open path) (m_fs mo0)).
    Proof.
      intros Hlen Hne Hsl Hnd Hfs. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      apply (aseg_A H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE a0s path Hargv p0 pp Hp0 Hpp).
      intros R M msF mo HV HA SB HR HK FM FA.
      pose proof (amst_at_open M FM FA) as ST. destruct (mo_sb _ _ SB) as [EFS EFDS].
      destruct (aopenat_regs sp0 regs0 tid can p0 pp R HR) as (H17 & H10 & H11 & Hfl).
      pose proof (apath_at_A H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE path p0 pp Hpp M R FM HR Hlen) as PA.
      eapply (drv_openat_absent H DL s0 msF R (Z_to_bv 64 0x177ad8) M mo ECALLW AECALL2 is_ecall_ECALLW HV HA H17 H10 Hfl path);
        [exact PA | exact Hne | exact Hsl | exact Hnd | rewrite EFS; exact Hfs |].
      intros msF' mo' HV' HA' SB'. rewrite BAgentLib.v_addi_lit in HV' by lia. change (0x177ad8 + 4)%Z with 0x177adc%Z in HV'.
      rewrite <- EFS, <- (same_but_materialized_fs _ _ SB').
      apply (open_fail ENOENT R M msF' mo' ltac:(right; right; reflexivity) HR HK ST FM HV' HA').
      rewrite (same_but_materialized_fds _ _ SB'). exact EFDS.
    Qed.

    Theorem as_dir :
      path = dot_path ->
      realizes asegs (mkCfg msF0 mo0) (t_alt2 (t_die (msg_cannot_open path) (m_fs mo0)) (t_opened_dir path (m_fs mo0))).
    Proof.
      intros Hdot. pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo. pose proof aceil_loT as HCL. acb.
      pose proof (am_fds _ _ _ _ _ _ _ _ _ _ _ _ PRE) as FDS0.
      assert (Hlen : (length path <= 4095)%nat) by (rewrite Hdot; cbn; lia).
      apply (aseg_A H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE a0s path Hargv p0 pp Hp0 Hpp).
      intros R M msF mo HV HA SB HR HK FM FA.
      pose proof (amst_at_open M FM FA) as ST. pose proof (arh_at_open M FM) as RH. destruct (mo_sb _ _ SB) as [EFS EFDS].
      destruct (aopenat_regs sp0 regs0 tid can p0 pp R HR) as (H17 & H10 & H11 & Hfl).
      pose proof (apath_at_A H FZP sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE path p0 pp Hpp M R FM HR Hlen) as PA.
      assert (Hfree : fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None) by (rewrite EFDS, FDS0; reflexivity).
      unfold t_opened_dir. rewrite <- EFS.
      eapply (drv_openat_dot H DL s0 msF R (Z_to_bv 64 0x177ad8) M mo ECALLW AECALL2 is_ecall_ECALLW HV HA H17 H10 Hfl Hfree path);
        [ exact PA | rewrite Hdot; reflexivity | |].
      - intros e msF' mo' He HV' HA' SB'. rewrite BAgentLib.v_addi_lit in HV' by lia. change (0x177ad8 + 4)%Z with 0x177adc%Z in HV'.
        rewrite <- (same_but_materialized_fs _ _ SB').
        apply (open_fail e R M msF' mo' ltac:(left; exact He) HR HK ST FM HV' HA').
        rewrite (same_but_materialized_fds _ _ SB'). exact EFDS.
      - intros msF' mo' HV' HA' SB'. rewrite BAgentLib.v_addi_lit in HV' by lia. change (0x177ad8 + 4)%Z with 0x177adc%Z in HV'.
        replace (alloc_fd (m_fds mo)) with (Z_to_bv 64 3) in HV', SB' by (rewrite EFDS, FDS0; reflexivity).
        eapply (aseg_C H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE p0 pp R M msF' mo' _ HV' HA' HR HK).
        intros R' msF2 mo2 HV2 HA2 SB2 Q1 Q2 Q4 Q8 Q10 Q18 Q20 Q21.
        change (Z_to_bv 64 0xba108) with (Z_to_bv 64 AMALLOC_STUB) in HV2.
        eapply (first_alloc R' M msF2 mo2 _ HV2 HA2 Q1 Q2 Q4 Q8 Q10 Q18 Q20 Q21 ST RH (am_al _ _ _ _ _ _ _ _ _ _ _ _ PRE)).
        intros regs3 mem3 msF3 mo3 A p s HV3 HA3 RC RH3 [junk CB3] AD3 ST3 HAL3 FS3 FDS3.
        destruct RC as (R1 & R2 & R4 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & R20 & R21 & R22).
        pose proof (ah_blocks H HH _ _ _ (p, A, 65536) RH3 ltac:(left; reflexivity)) as BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
        cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in B4.
        destruct (aerrno_rw_any mem3) as [errv ERR].

        eapply (aread_stage_dir H HH DL s msF3 mo3 regs3 mem3 3 65536 lo errv 0xe84dc _ HV3 HA3 R1);
          [ lia | reflexivity | exact R4 | exact R10 | exact R11 | exact R12 | lia | lia
          | rewrite R2, u_small by lia; exact (mst_stk_spm H sp0 tid can mem0 Hvsp _ ST3) | lia | rewrite R2, u_small by lia; unfold AREAD_STACK; lia
          | exact (mst_inv H sp0 tid can mem0 _ ST3) | exact (mst_ac H sp0 tid can mem0 _ ST3) | exact ERR
          | rewrite FDS3, (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB'), with_fds_fds; apply fd_lookup_insert_eq |].
        rewrite R2, !u_small by lia.
        intros regs4 mem4 msF4 mo4 HV4 HA4 KEPT4 U10 MU4 WM4 INV4 STK4 AC4 ERR4 FS4 FDS4.
        assert (ST4 : mstatics H sp0 tid can mem0 mem4).
        { eapply (mstatics_munch H HH sp0 tid can mem0 Hvsp HCE mem3 mem4 _ [] ST3 MU4 WM4); [| exact INV4 | exact STK4 | exact AC4].
          constructor; [right; left; reflexivity | constructor; [left; cbn [fst snd]; unfold AREAD_STACK; lia | constructor]]. }
        assert (RR4 : aread_ret_regs sp0 regs4 ppw A 0 65536 (Z_to_bv 64 (2 ^ 64 - 1))).
        { unfold aread_ret_regs, albase_regs, abase_regs.
          repeat split; first [ kept KEPT4 (2:reg)%bv R2 | kept KEPT4 (4:reg)%bv R4 | kept KEPT4 (8:reg)%bv R8
                              | kept KEPT4 (18:reg)%bv R18 | kept KEPT4 (20:reg)%bv R20 | kept KEPT4 (22:reg)%bv R22
                              | kept KEPT4 (9:reg)%bv R9 | kept KEPT4 (19:reg)%bv R19 | kept KEPT4 (21:reg)%bv R21
                              | apply bv_eq; rewrite U10, u_small by lia; reflexivity ]. }
        eapply (aseg_L5c H DL sp0 Hvsp s msF4 mo4 regs4 mem4 ppw A 0 65536 _ RR4 (mst_stk_ok H sp0 tid can mem0 Hvsp _ ST4)
                  (mst_ro H sp0 tid can mem0 _ ST4) (mst_relro H sp0 tid can mem0 _ ST4)); [| exact HV4 | exact HA4].
        intros regs5 mem5 msF5 mo5 HV5 HA5 SB5 (T2 & T4 & T8 & T18 & T20) T9 FM5 STK5.
        replace (m_fs mo) with (m_fs mo5) by
          (rewrite (same_but_materialized_fs _ _ SB5), FS4, FS3, (same_but_materialized_fs _ _ SB2), (same_but_materialized_fs _ _ SB'), with_fds_fs; reflexivity).
        eapply (TRD sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s msF5 mo5 regs5 mem5 Hva PRE Hargv (proj1 Hpp) (proj2 Hpp) HV5 HA5 T2 T4 T18).
        + eapply (mstatics_frameL H HH sp0 tid can mem0 Hvsp HCE); [exact ST4 | exact FM5].
        +
          assert (RH4 : as_RHEAP H s [(p, A, 65536)] mem4).
          { eapply (ah_RHEAP_frame H HH); [exact RH3 | exact MU4 | exact WM4 |].
            constructor; [right; left; unfold aimg_client_w, AERRNO, ATLS_PRIV_LO, ATP; cbn [fst snd]; lia | constructor; [| constructor]].
            left. cbn [fst snd]. unfold AREAD_STACK in *. rewrite ?R2, ?u_small by lia. lia. }
          apply (ahm_of_heap s [(p, A, 65536)]). exact (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RH4 FM5).
        + rewrite (same_but_materialized_fds _ _ SB5), FDS4, FDS3, (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB'), with_fds_fds,
            fd_lookup_insert_neq, EFDS, FDS0; [reflexivity | intros E; apply (f_equal bv_unsigned) in E; discriminate].
    Qed.
  End TwoArgs.

  Section Usage.
    Hypothesis Hargc : length argv <> 2%nat.

    Theorem as_usage : realizes asegs (mkCfg msF0 mo0) (t_die (msg_usage (hd [] argv)) (m_fs mo0)).
    Proof.
      pose proof SPlo. pose proof SPhi. pose proof Elo.
      apply (aseg_U H FZP DL sp0 argv s0 msF0 mo0 regs0 mem0 B tid can Hva PRE Hargc). intros R M msF mo HV HA SB Q2 Q4 Q8 Q10 Q11 FM FA.
      rewrite <- (same_but_materialized_fs _ _ SB).
      eapply (TUS sp0 argv s0 msF0 mo0 regs0 mem0 B tid can s0 msF mo R M Hva PRE Hargc HV HA Q2 Q4 Q8 Q10 Q11).
      - unfold regU_w in FM. eapply (amst_at_win M _ _ FM); [lia | lia | lia | exact FA].
      -
        unfold regU_w in FM. apply (ahm_of_heap s0 []).
        eapply (rheap_win s0 [] mem0 M _ _ (am_heap _ _ _ _ _ _ _ _ _ _ _ _ PRE) FM); lia.
      - exact (same_but_materialized_fds _ _ SB).
    Qed.
  End Usage.
End ATop.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; intros [|b q]; cbn; try (split; [discriminate|congruence]).
  - split; reflexivity.
  - rewrite andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
    + intros [Hab ->]. f_equal. apply bv_eq. exact Hab.
    + intros E. injection E as -> ->. split; reflexivity.
Qed.

Section Main.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable FZP : fuzz_params.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis AHM : RHEAP_ahm H.
  Hypothesis FPO : fz_params_ok FZP.
  Hypothesis DL : asan_driver_laws H.
  Hypothesis TR : as_target_run_stmt H FZP.
  Hypothesis LIVE : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H.
  Hypothesis TUS : atail_usage_stmt H FZP.
  Hypothesis TOP : atail_open_stmt H FZP.
  Hypothesis TRD : atail_rderr_stmt H FZP.

  Theorem as_main_realizes : as_main_realizes_stmt H FZP.
  Proof.
    intros sp0 argv s0 msF mo regs mem B tid can Hva Hvfs PRE.
    destruct argv as [|a0s [|path [|x l]]].
    - exact (as_usage H FZP HH AHM DL TUS sp0 [] s0 msF mo regs mem B tid can Hva PRE ltac:(cbn; lia)).
    - exact (as_usage H FZP HH AHM DL TUS sp0 [a0s] s0 msF mo regs mem B tid can Hva PRE ltac:(cbn; lia)).
    - cbn [spec].
      pose proof Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|x l [Hsl Hdd] _]; subst.
      destruct (am_args _ _ _ _ _ _ _ _ _ _ _ _ PRE 0%nat a0s ltac:(lia) eq_refl) as [p0 Hp0].
      destruct (am_args _ _ _ _ _ _ _ _ _ _ _ _ PRE 1%nat path ltac:(lia) eq_refl) as [pp Hpp].
      change (8 * Z.of_nat 0) with 0 in Hp0. change (8 * Z.of_nat 1) with 8 in Hpp.
      replace (bv_unsigned sp0 + 8 + 0) with (bv_unsigned sp0 + 8) in Hp0 by lia.
      replace (bv_unsigned sp0 + 8 + 8) with (bv_unsigned sp0 + 16) in Hpp by lia.
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + exact (as_open_fail_toolong H FZP HH AHM DL TOP sp0 [a0s; path] s0 msF mo regs mem B tid can Hva PRE a0s path eq_refl p0 pp Hp0 Hpp Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply list_byte_eqb_eq in Hemp.
          exact (as_open_fail_empty H FZP HH AHM DL TOP sp0 [a0s; path] s0 msF mo regs mem B tid can Hva PRE a0s path eq_refl p0 pp Hp0 Hpp Hemp).
        * assert (Hne : path <> []) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- apply list_byte_eqb_eq in Hdot.
             exact (as_dir H FZP HH AHM FPO DL LIVE TOP TRD sp0 [a0s; path] s0 msF mo regs mem B tid can Hva PRE a0s path eq_refl p0 pp Hp0 Hpp Hdot).
          -- assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
             assert (Hdr : path_is_dirref path = false).
             { unfold path_is_dirref. rewrite Hdd, orb_false_r.
               match goal with |- ?b = false => destruct b eqn:E; [|reflexivity] end.
               apply path_eqb_eq in E. exfalso. apply Hnd. exact E. }
             destruct (fs_lookup (m_fs mo) path) as [data|] eqn:Hlk.
             ++ exact (as_file H FZP HH AHM FPO DL TR LIVE TOP sp0 [a0s; path] s0 msF mo regs mem B tid can Hva PRE a0s path eq_refl p0 pp Hp0 Hpp data Hlk
                        ltac:(lia) Hne Hsl Hdr).
             ++ exact (as_open_fail_absent H FZP HH AHM DL TOP sp0 [a0s; path] s0 msF mo regs mem B tid can Hva PRE a0s path eq_refl p0 pp Hp0 Hpp
                        ltac:(lia) Hne Hsl Hdr Hlk).
    - exact (as_usage H FZP HH AHM DL TUS sp0 (a0s :: path :: x :: l) s0 msF mo regs mem B tid can Hva PRE ltac:(cbn; lia)).
  Qed.
End Main.
