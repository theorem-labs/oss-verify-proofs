(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from MainTop.v: the argc <> 2 arm of main (ref_usage) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib SymExec2 SymExec2Sound SymRun SymDriveX MemSplit MuslStrlen
  Spec RefNodes LibTail LibDiagKn LibDiagKnMain RefStartup RefStartupFacts RefMainEntry RefMainEntryN
  RefStartupDefs RefUsageCS_defs RefUsageCS RefOpenFailCS_defs RefOpenFailCS RefReadErr_defs RefReadErr RefRefused RefHdrErr
  RefStdioDefs RefExitBase RefMainExit LibMainRet HeapCeil
  RegsEquivM MainEqv MainDefs MainArith MainWalk_defs MainMem MainHeap MainSegs MainOpen MainLoop.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import MainTop.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb AgentNodesB NodesB LibWritevB RefNodesB SymDriveB.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import MainOpenB RefUsageCSB.
Open Scope bv_scope.
Open Scope Z_scope.

  Section UsageTop.
    Context {AMB : Amb}.
    Variable sp0 : word.
    Variables av envv : list (list byte).
    Variable rdraw : EntryDraw.
    Variable tid : word.
    Variable regs0 : bvmap 5 word.
    Variable mem0 : word -> option byte.
    Variables (brk mbase : word) (lim : Z) (fs0 : Fs) (stdin0 : InputStream).
    Hypothesis Hva : valid_argv av.
    Hypothesis Hve : valid_envp envv.
    Hypothesis Hvsp : valid_sp sp0.
    Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
    (* as MainTop.v's Section UsageTop: [main_entry] is over the run's input, the entry is
       the image's, and the launch facts are over the same input and entry. *)
    Let inp : ProcInput := mkProcInputC av envv fs0 stdin0.
    Let entryw : word := (0x2ab1c : word).
    Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
    Hypothesis Hvl  : valid_launch inp.
    Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
    Hypothesis Hargc : length av <> 2%nat.
    Hypothesis Hfit : entry_stack_fits sp0 av envv.
    Let model0 : Model := MainDefs.model0 tid brk mbase sp0 rdraw lim inp.
    (* the launch's stdout/stderr reader, as in MainTop.v's Section UsageTop; the caller has it
       from [Run.valid_input] *)
    Hypothesis Hrd0 : m_channel_reader model0 = true.

    Theorem ref_usage_b :
      rzb RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x2ac68) mem0 (seg_rom RSEGS)) model0) (t_die (msg_usage (hd [] av)) (fsC fs0)).
    Proof.
      pose proof (proj1 Hvsp : 0x7fff80000000 <= bv_unsigned sp0) as Hlo. pose proof (proj1 (proj2 Hvsp) : bv_unsigned sp0 <= 0x800000000000) as Hhi.
      assert (Hh : m_halted model0 = None) by reflexivity. assert (Hlazy : m_vm_lazy model0 = []) by reflexivity.
      (* [seg_U_b] takes [inp]/[mbase]/[brk]/[entryw] with [av]/[envv] tied by
         [Hargv]/[Henvp] (MainOpenB.v); here [inp] IS that term, so both are [eq_refl]. *)
      apply (seg_U_b sp0 av envv rdraw tid regs0 mem0 model0 inp mbase brk entryw
               Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME Hargc Hh Hlazy).
      intros R M Q2 Q4 Q8 Q11 FM (Fra & [s0v Fs0] & F1 & F2 & F3 & F4 & F5 & F6 & F7) Margv.
      assert (RS : forall r, In r (regU_w sp0) -> bv_unsigned (fst r) = bv_unsigned sp0 - 128 /\ snd r = 80).
      { intros r Hr. unfold regU_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. split; reflexivity. }
      assert (ABOVE : forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M x = mem0 x).
      { intros x Hx. apply (proj1 FM). apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia. }
      destruct (arg0_facts sp0 av envv rdraw tid regs0 mem0 inp mbase brk entryw
                  Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME) as (Sr & Slo & Shi & Slen & [t8 Ht8] & Sfit & Snul).
      set (pp := cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) in *. set (a0s := nth 0 av []) in *.
      pose proof (u64_range pp) as Hpr.
      replace (hd [] av) with a0s by (subst a0s; destruct av; reflexivity).
      change (fsC fs0) with (m_fs model0).
      refine (ref_usage_cs_b sp0 model0 Hvsp Hh Hlazy eq_refl Hrd0 pp (bv_unsigned tid) (bv_unsigned (canary_w rdraw)) s0v R M Q2 Q4 Q8 Q11
                _ _ _ _ Htid _ Margv Slo Fra Fs0 F1 F2 F3 F4 F5 F6 F7 a0s t8 Snul Slen _ _ _ _).
      - intros a n Ha Hn. rewrite u_small in Ha, Hn by lia. eapply frame_mod_store_ok; [exact FM|].
        apply (main_entry_store_ok_win _ _ _ sp0 rdraw tid regs0 mem0 ME);
          unfold RefUsageCS_defs.US_STK, wok_lo, stack_window_reach, stack_max_size in *; lia.
      - intros i Hi. rewrite (proj1 FM (Z_to_bv 64 i)); [apply (main_entry_ro_none _ _ _ sp0 rdraw tid regs0 mem0 Hvsp ME); exact Hi |].
        apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2, u_small by lia. lia.
      - eapply cells_ok_frame; [apply diag_cells_wf | exact (cells_ok_main_entry _ _ _ sp0 rdraw tid regs0 mem0 Hvsp ME) | exact FM |].
        eapply Forall_impl; [| apply diag_cells_range]. intros [[a w] v] [R1 R2] r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - eapply rdn_frame; [exact FM | | unorm; lia |].
        + rewrite Z_to_bv_bv_unsigned. apply (RefStartupFacts.main_entry_tid _ sp0 rdraw tid Hlo _ _ regs0 mem0 ME).
        + intros r Hr. unorm. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - split; [| apply u64_range]. eapply rdn_frame; [exact FM | exact (proj1 (canary_ok_main_entry _ _ _ sp0 rdraw tid regs0 mem0 Hvsp ME)) | unfold CANARY; unorm; lia |].
        intros r Hr. unfold CANARY. unorm. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - lia.
      - specialize (Sfit Hfit). lia.
      - rewrite <- Sr. apply rdn_ext; [lia|]. intros x Hx. apply ABOVE. lia.
      - rewrite <- Ht8. apply rdn_ext; [unorm; lia|]. intros x Hx. apply ABOVE. revert Hx. unorm. intros Hx. lia.
    Qed.
  End UsageTop.
