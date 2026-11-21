(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec StdModel ShapeAlg ShapeLaws ModelAmb DrawDefs Spec S8ReadBase S8ReadStage S8World
  S8Startup S8MainEntry S8MainEntryN S8PilotOOM S8OpenFailBranch SymDriveX.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS8 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrRulesS8.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP8 Require Import S8HeapPre S8HBase S8HConv S8TrTail S8RdLib S8RdInv S8RdRules S8RdLoop S8RdEnd S8RdFrontA S8RdFrontB
  S8LfBase S8LfOom S8RdLeaf S8LfDirRd.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* kitfix4 alias stage: Module OSp := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec expanded *)
(* kitfix4 alias stage: Module OW := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8World expanded *)
(* kitfix4 alias stage: Module ORB := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8ReadBase expanded *)
(* kitfix4 alias stage: Module OPO := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8PilotOOM expanded *)
(* kitfix4 alias stage: Module OME := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8MainEntry expanded *)
(* kitfix4 alias stage: Module OMN := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8MainEntryN expanded *)

Section GDIR.
Context {RCa1 : RunCtx}.
Variables (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word).

Definition modelDir (V : VmMaps) : Model := ModelAmb.mkModelA (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8PilotOOM.fds1g FdDir) V stdin0 fs0 None (Some tid) None.
Definition G_dir : PState -> Model -> Prop := fun _ mo => mo = modelDir (m_vmmaps mo).

Lemma frame_ok_G_dir : frame_ok G_dir.
Proof. unfold G_dir, modelDir, ModelAmb.mkModelA. apply frame_ok_G_shape. Qed.

Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
(* Lib/Nodes' minv ends with the channel reader; mkModelA reads it off the AmbIn. *)
Hypothesis Hrdr : ModelAmb.ia_channel_reader stdin0 = true.

Lemma minv_modelDir : forall V, sp_window_lo <= bv_unsigned (vm_init_sp V) <= sp_window_hi -> minv (modelDir V).
Proof.
  intros V Hsp. unfold minv.
  change (m_fds (modelDir V)) with
    [(Z_to_bv 64 3, FdDir); (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
     (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  change (m_tid (modelDir V)) with (Some tid).
  change (m_vm_lazy (modelDir V)) with (@nil (word * word)).
  change (m_vm_materialized (modelDir V)) with (@nil word).
  change (m_vmmaps (modelDir V)) with V.
  cbn [fd_lookup].
  repeat split; try reflexivity; try lia; try exact Hrdr.
  - intros k c H.
    destruct (bv_eqb (Z_to_bv 64 3) k) eqn:E3; [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off' H.
    destruct (bv_eqb (Z_to_bv 64 3) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H.
    destruct (bv_eqb (Z_to_bv 64 3) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. lia.
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. unfold Fork.PID_MAX_ENVELOPE. lia.
Qed.

Lemma dir_model : forall X s mo, OWN X G_dir s mo ->
  m_halted mo = None /\ m_vm_lazy mo = []
  /\ fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))
  /\ fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some FdDir /\ m_fs mo = fs0
  /\ m_channel_reader mo = true.
Proof.
  intros X s mo HOWN. pose proof HOWN as [(L & _ & HKL & _) [_ HG]].
  split; [exact (kl_halt _ _ _ HKL)|].
  split; [exact (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL))|].
  split; [|split; [|split; [|exact (minv_reader _ (kl_minv _ _ _ HKL))]]];
    unfold G_dir in HG; rewrite HG; reflexivity.
Qed.
End GDIR.

Section DIR.
Context {rc : runConstT}.
(* as RdTop, over the launch input (argv = [a0s; dot_path] by Hav): VLAUNCH + LOK and the
   channel reader replace entry_stack_fits; the AmbIn and file system are the launch's. *)
Variables (sp0 : word) (a0s : list byte) (inp : ProcInput) (rdraw : EntryDraw) (tid : word).
Local Notation envv := (in_envp inp) (only parsing).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word).
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
Local Notation stdin0 := (ModelAmb.amb_of inp (vdso_run_init (ed_vdso rdraw))) (only parsing).
Local Notation fs0 := (in_fs inp) (only parsing).
Hypothesis Hav : in_argv inp = [a0s; OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.dot_path].
Hypothesis Hva : valid_argv [a0s; OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.dot_path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Hypothesis Hcr : in_channel_reader inp = true.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
Hypothesis ME : S8Startup.main_entry sp0 inp mbase rdraw tid regs0 mem0.
Hypothesis Hbrk : valid_brk psegs brk.
Hypothesis HCAN : CAN = DrawDefs.canary_w rdraw.
Hypothesis HSEC : SECRET = bv_unsigned (DrawDefs.secret_w rdraw).
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.
Variable AI : nat -> list bptr -> PState -> Model -> Prop.
Hypothesis RMF : rule_malloc_first AI 10.

Let SP : Z := bv_unsigned sp0.
Abbreviation GDIR := (G_dir stdin0 fs0 tid).
Abbreviation MODELD := (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8PilotOOM.model1g sp0 inp rdraw tid brk mbase FdDir).

Lemma model1_G_dir : forall s, GDIR s MODELD.
Proof. intros s. unfold G_dir. reflexivity. Qed.

Theorem dir_phase_h :
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) regs0 (Z_to_bv 64 0x148d4) mem0 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
                        (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8PilotOOM.model0 sp0 inp rdraw tid brk mbase))
           (ShapeAlg.t_alt2 (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.t_die (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.msg_cannot_open OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.dot_path) fs0) (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.t_opened_dir OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.dot_path fs0)).
Proof.
  pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
  assert (Hva' : valid_argv (in_argv inp)) by (rewrite Hav; exact Hva).
  set (pp := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8MainEntry.p1 inp rdraw).
  (* argv[1]'s string sits at the launch's cat_argv_ptr (StackLayout's block top). *)
  edestruct (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.S8MainEntryN.main_strN sp0 inp mbase brk rdraw tid regs0 mem0 Hva' Hvl Hlau Hvsp ME 1%nat) as (Sr & Slo & Shi & Slen & t8 & Ht8);
    [rewrite Hav; cbn; lia|].
  change (CatExec.cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1) with pp in Sr, Slo, Shi, Ht8.
  rewrite Hav in Sr, Slen, Ht8.
  cbn [nth length Nat.add OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.dot_path app] in Sr, Slo, Shi, Slen, Ht8.
  change (Z.of_nat 1) with 1 in Ht8.
  pose proof (bv_unsigned_in_range _ pp) as Hppr. change (bv_modulus 64) with (2 ^ 64) in Hppr.
  unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.t_opened_dir.
  (* RdFrontA's front_to_malloc_dot and the carried open-fail branch take the launch
     premises of this section. *)
  eapply (front_to_malloc_dot sp0 a0s inp rdraw tid regs0 mem0 brk mbase); try eassumption.
  - eapply S8OpenFailBranch.open_err_branch_cannot_open; eassumption.
  - intros R M G1 G2 G3 G4 G8 G10 G18 G20 G21 FM MF.
    assert (MINV : minv MODELD).
    { apply (minv_modelDir stdin0 fs0 tid Htid Hcr). cbn [vm_init_sp]. exact (conj (proj1 Hvsp) (proj1 (proj2 Hvsp))). }
    eapply (first_malloc_gen sp0 inp mbase rdraw tid regs0 mem0 Hva' Hve Hvsp ME HCAN HSEC HATOP brk Hvl Hlau []
              Hbrk Hcr AI 10%nat RMF FdDir GDIR (frame_ok_G_dir stdin0 fs0 tid) model1_G_dir MINV
              (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.t_die OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.msg_oom fs0) (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.t_die (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.msg_read_error OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.dot_path) fs0) R M pp);
      try eassumption.
    + apply ShapeLaws.t_emit_has_nil.
    + apply ShapeLaws.t_emit_has_nil.
    +
      intros M' s' mo' y1 y5 y6 y7 x8 x9 y11 y12 y13 y14 y15 y16 y17 x18 x19 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31 BASE HH HOWN.
      destruct (dir_model stdin0 fs0 tid _ _ _ HOWN) as (Hh & Hl & FD2 & _ & FS & Hrdr).
      rewrite <- FS.
      lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
        exact (ref_oom_tail sp0 [] mo' Hvsp Hh Hl FD2 Hrdr (bv_unsigned tid) RR M' eq_refl eq_refl eq_refl
                 (lf_stack sp0 Hvsp tid [] M' BASE) (lf_img sp0 tid Htid M' BASE)
                 (lf_tid sp0 tid M' BASE) Htid (bv_unsigned CAN) (lf_got _ _ _ HH) (lf_guard _ _ _ HH) (lf_need_locks _ _ _ HH)
                 0x14b7c (or_intror eq_refl)) end.
    +
      intros pb buf M' s' mo' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 RI HAI ABOVE.
      pose proof (ri_base _ _ _ _ _ _ _ _ _ _ _ RI) as BASE. pose proof (ri_heap _ _ _ _ _ _ _ _ _ _ _ RI) as HH.
      destruct (dir_model stdin0 fs0 tid _ _ _ (ri_own _ _ _ _ _ _ _ _ _ _ _ RI)) as (Hh & Hl & FD2 & FD3 & FS & Hrdr).
      rewrite <- FS.
      lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
        refine (dir_read_leaf sp0 pp (bv_unsigned tid) (bv_unsigned CAN) t8 RR M' mo' Hvsp _ Hh Hl FD3 FD2 Hrdr) end.
      constructor; try reflexivity.
      * exact (lf_stack sp0 Hvsp tid [] M' BASE).
      * exact (lf_img sp0 tid Htid M' BASE).
      * exact (lf_tid sp0 tid M' BASE).
      * exact Htid.
      * exact (lf_got _ _ _ HH).
      * exact (lf_guard _ _ _ HH).
      * exact (lf_need_locks _ _ _ HH).
      * exact Slo.
      * lia.
      * rewrite <- Sr. apply OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveX.rdn_agree. intros j Hj. apply ABOVE. unfold SP. rewrite unsigned_lit by lia. lia.
      * rewrite <- Ht8. apply OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveX.rdn_agree. intros j Hj. apply ABOVE. unfold SP.
        rewrite (unsigned_lit (bv_unsigned pp + 1)) by lia. rewrite unsigned_lit by lia. lia.
Qed.
End DIR.
