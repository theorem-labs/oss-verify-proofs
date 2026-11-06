(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit MonadF AExit AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AIos_iface AExitU_fini AExitU_tail AExitU_head3 AExitU_head4 AExitU_kit AExitU_head6 AExitU2.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma client_exit_none : forall (s : APS) (K : MA Empty_set), aps_cl s = None -> (client_exitA AAllocAsan ;;; K) s = K s.
Proof. intros s K H. unfold client_exitA, HarnessM.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma client_exit_some : forall (s : APS) p (K : MA Empty_set), aps_cl s = Some p ->
  (client_exitA AAllocAsan ;;; K) s = ((HarnessM.opdelete afree_M p ;;; mupd (aset_cl None)) ;;; K) s.
Proof. intros s p K H. unfold client_exitA, HarnessM.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.

Section Asm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables MDPRE ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Variables SLO SHI : Z.
  Hypothesis MDTOR : module_dtor_stmt MDPRE.
  Hypothesis MDPRE_frame : forall W m m', MDPRE m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> MDPRE m'.
  Hypothesis ICPT_frame : forall W m m', ICPT m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> ICPT m'.
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis WCR : wcrtomb0_stmt ICPT ICPTR SLO SHI.
  Hypothesis FW0 : fwrite0_out_stmt ICPT ICPTR.
  Hypothesis FW0E : fwrite0_err_stmt ICPT ICPTR.
  Hypothesis FFL : fflush_out_stmt ICPT ICPTR aps_so aset_so.
  Hypothesis FFLS : fflush_out_stmt ICPT ICPTR (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt ICPT ICPTR.
  Hypothesis AVD : avdtor_stmt AI.
  Hypothesis EXIT_CI : forall iv, In iv exit_ci_need -> In iv CI.
  Hypothesis INCB_CI : In (0x6afad0, 0x6afd18) CI.      (* [comment removed for export] *)
  Hypothesis MDPRE_pres : forall L RNG st LB LB' SP m m', vdtor_pres CI LB SP m m' -> AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> MDPRE m -> MDPRE m'.
  Hypothesis ICPT_pres : forall L RNG st LB LB' RNG0 st0 LB0 SP m m', vdtor_pres CI LB SP m m' -> AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> ICPT m ->
    AHEAP AI L RNG0 st0 LB0 m (* [comment removed for export] *) -> ICPT m'.
  Hypothesis ICPTR_mono : forall RNG RNG', fp_le RNG RNG' -> ICPTR RNG -> ICPTR RNG'.

  Theorem aexitU2_proof : aexitU2_stmt AI MDPRE ICPT ICPTR SLO SHI.
  Proof.
    intros code s RNG ms Q H.
    destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                   s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                   cdt & thr & sec & tm1 & dso & guard & tbl & L & LB & rstk & -> & H).
    destruct H as (HMD & IC & RI & IOS & AH & HBO & HINV & APOK & ST & TID & EXL & LIBC & ATX & CASE & INCB & FLG & COV & FA & FINZ & DSO & OFL & SIN & SINF & SOU & SEU
                   & SOF & SEF & GU & MI & FRM & Htp & Ha0 & Ht & LO & ATL & SLOK & SHIK & KH & AL & SPTOP & RCL & RLO & RHI & RRLO & HUXL & RTOP & RSTK & RIMG & RSH
                   & RRNG & RW & RG0 & SP47).
    pose proof (exit_relro_of_aheap AI _ _ _ _ _ AH) as (GFL & GF & GCX & GG).
    assert (GLO : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; unfold KHIGH in KH; lia).
    unfold AEXITU2_STACK in LO.
    destruct ATX as (fj & aj & FIN & ALK & SLOT & HEAD & NEXT & FFall & AAall & _ & _).
    unfold ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A in *.
    (* [comment removed for export] *)
    unfold aincb in INCB.
    destruct CASE as [[CLN [-> | ->]] | (p & V & CLS & -> & INB & VEC & VCELL)].
    - (* [comment removed for export] *)
      unfold TBL_MAIN in FFall, AAall, SLOT. cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ] in FFall, AAall, SLOT.
      match type of FFall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] rest) FFall)) as FF end.
      match type of AAall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] rest) AAall)) as AA end.
      unfold implMA. rewrite (client_exit_none s _ CLN). change (ioA AAllocAsan) with (io_S (St := APS) aps_so aset_so).
      eapply implF_epost_mono.
      + eapply (exit_head3_spec aps_so aset_so MDPRE ICPT ICPTR SLO SHI MDTOR MDPRE_frame ICPT_frame SE WCR FW0 FW0E FFL FFLS FFLE RNG s
                  (fun (e : Empty_set) _ _ => match e with end)) with (lo := lo) (t := t) (so_x := aps_so s) (guard := guard);
          try first [ eassumption | reflexivity | (intros _; reflexivity) | exact GLO | exact SLOK | exact SHIK | exact KH | exact AL | exact SP47
                    | (unfold EXIT_TAIL_DEPTH; clear - LO; lia) | (clear - ATL; lia) ].
      + intros [e ?] RNG' ms'. destruct e.
    - (* [comment removed for export] *)
      unfold TBL_REG, TBL_MAIN in FFall, AAall, SLOT. cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ] in FFall, AAall, SLOT.
      match type of FFall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: rest)) FFall)) as FF;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: rest)) FFall)) as FR1;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in FR1;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m _ [c4] rest) FR1)) as F3; clear FR1 end.
      match type of AAall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: rest)) AAall)) as AA;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: rest)) AAall)) as AR1;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in AR1;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m _ [c4] rest) AR1)) as A3; clear AR1 end.
      match type of F3 with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in F3 end.
      match type of A3 with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in A3 end.
      unfold implMA. rewrite (client_exit_none s _ CLN). change (ioA AAllocAsan) with (io_S (St := APS) aps_so aset_so).
      eapply implF_epost_mono.
      + eapply (exit_head4_spec aps_so aset_so MDPRE ICPT ICPTR SLO SHI MDTOR MDPRE_frame ICPT_frame SE WCR FW0 FW0E FFL FFLS FFLE RNG s
                  (fun (e : Empty_set) _ _ => match e with end)) with (lo := lo) (t := t) (so_x := aps_so s) (guard := guard);
          try first [ eassumption | reflexivity | (intros _; reflexivity) | exact GLO | exact SLOK | exact SHIK | exact KH | exact AL | exact SP47
                    | (unfold EXIT_TAIL_DEPTH; clear - LO; lia) | (clear - ATL; lia) ].
      + intros [e ?] RNG' ms'. destruct e.
    - (* [comment removed for export] *)
      unfold TBL_RUN, TBL_REG, TBL_MAIN, ADTOR_THUNK in FFall, AAall, SLOT. cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ] in FFall, AAall, SLOT.
      match type of FFall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: c5 :: c6 :: rest)) FFall)) as FF;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: c5 :: c6 :: rest)) FFall)) as FR1;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in FR1;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m _ [c4] (c5 :: c6 :: rest)) FR1)) as F3;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m _ [c4] (c5 :: c6 :: rest)) FR1)) as FR2;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in FR2;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m _ [c5; c6] rest) FR2)) as F45; clear FR1 FR2 end.
      match type of AAall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: c5 :: c6 :: rest)) AAall)) as AA;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m A [c1; c2; c3] (c4 :: c5 :: c6 :: rest)) AAall)) as AR1;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in AR1;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m _ [c4] (c5 :: c6 :: rest)) AR1)) as A3;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m _ [c4] (c5 :: c6 :: rest)) AR1)) as AR2;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in AR2;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m _ [c5; c6] rest) AR2)) as A45; clear AR1 AR2 end.
      match type of F3 with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in F3 end.
      match type of A3 with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in A3 end.
      match type of F45 with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in F45 end.
      match type of A45 with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in A45 end.
      unfold implMA. rewrite (client_exit_some s p _ CLS). fold (implMA RNG ((HarnessM.opdelete afree_M p ;;; mupd (aset_cl None)) ;;; exit_model (ioA AAllocAsan) code) s Q).
      eapply (exit_head6_spec AI MDPRE ICPT ICPTR SLO SHI MDTOR MDPRE_frame ICPT_frame SE WCR FW0 FW0E FFL FFLS FFLE AVD EXIT_CI INCB_CI MDPRE_pres ICPT_pres ICPTR_mono RNG s Q)
        with (lo := lo) (t := t) (guard := guard) (L := L) (LB := LB) (V := V) (rstk := rstk);
        try first [ eassumption | reflexivity | exact GLO | exact SLOK | exact SHIK | exact KH | exact AL | exact SP47 | exact LO ].
  Qed.
End Asm.
End CANSEC1.
