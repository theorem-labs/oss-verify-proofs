(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit MonadF AExit F_module_dtor_pre F_module_dtor F_stdio_exit AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AIos_iface AExitU_wr AExitU_kit AExitU2 ADriver_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Lemma aps_set_get' : forall (s : APS), aset_so (aps_so s) s = s.
Proof. intros [st so rv tp cl]. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition XP0 : ExitParams.
Proof.
  refine {| xp_ICPT := fun _ => True; xp_ICPTR := fun _ => True; xp_SLO := 0; xp_SHI := 2^64; xp_addr := fun _ => False |};
    intros; cbn beta in *; first [exact I | contradiction].
Defined.
Lemma XP0_SLO : @xp_SLO rc XP0 <= ATOP + 4096.
Proof. pose proof atop_range as AR. cbn. lia. Qed.
Lemma XP0_SHI : ATOP + 8388608 <= @xp_SHI rc XP0.
Proof. pose proof atop_range as AR. cbn. lia. Qed.

Section Closed.
  Context {XP : ExitParams}.
  Variable AI : AMallocIface.

  (* [comment removed for export] *)
  Theorem aexit_closed : forall code (s : APS) RNG ms (Q : Empty_set -> APS -> footprint -> machine_state -> Prop),
    aat_exit AI code s RNG ms -> implMA RNG (mbind (client_exitA AAllocAsan) (fun _ => exit_model (ioA AAllocAsan) code)) s Q ms.
  Proof.
    intros code s RNG ms Q H. unfold aat_exit, aat_exitU2 in H.
    destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                   s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                   cdt & thr & sec & tm1 & dso & guard & tbl & L & LB & rstk & -> & H).
    destruct H as (HMD & IC & RI & IOS & AH & HBO & HINV & APOK & ST & TID & EXL & LIBC & ATX & CLN & FLG & COV & FA & FINZ & DSO & OFL & SIN & SINF & SOU & SEU
                   & SOF & SEF & GU & MI & FRM & Htp & Ha0 & Ht & LO & ATL & SLOK & SHIK & KH & AL & SPTOP & RCL & RLO & RHI & RRLO & HUXL & RTOP & RSTK & RIMG & RSH
                   & RRNG & RW & RG0 & SP47).
    pose proof (exit_relro_of_aheap AI _ _ _ _ _ AH) as (GFL & GF & GCX & GG).
    unfold AEXITU2_STACK in LO.
    destruct ATX as (ATX & INH & TB). unfold aincb in INH.
    destruct ATX as (fj & aj & FIN & ALK & SLOT & HEAD & NEXT & FFall & AAall & _ & _).
    unfold ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A in *.
    assert (CE : (mbind (client_exitA AAllocAsan) (fun _ => exit_model (ioA AAllocAsan) code)) s = exit_model (ioA AAllocAsan) code s)
      by (unfold client_exitA, HarnessP.client_exit, mbind, mret; cbn; reflexivity).
    unfold implMA. rewrite CE. change (ioA AAllocAsan) with (io_S (St := APS) aps_so aset_so).
    destruct TB as [-> | ->].
    - unfold TBL_MAIN in FFall, AAall, SLOT. cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ] in FFall, AAall, SLOT.
      match type of FFall with rw_cells _ _ ?A (?c1 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1] rest) FFall)) as FF end.
      match type of AAall with rw_cells _ _ ?A (?c1 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1] rest) AAall)) as AA end.
      eapply implF_epost_mono.
      + eapply (aexit_spec_closed aps_so aset_so aps_get_set' aps_set_set' aps_set_get' RNG s (fun (e : Empty_set) _ _ => match e with end))
          with (lo := lo) (t := t) (guard := guard);
          try first [ eassumption | reflexivity | exact KH | exact SP47 | (unfold MDTOR_DEPTH; clear - LO; lia) ].
      + intros [e ?] RNG' ms'. destruct e.
    - unfold TBL_REG, TBL_MAIN in FFall, AAall, SLOT. cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ] in FFall, AAall, SLOT.
      match type of FFall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1] (c2 :: rest)) FFall)) as FF0;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m A [c1] (c2 :: rest)) FFall)) as FFr end.
      match type of FFr with rw_cells _ _ ?A (?c1 :: ?rest) =>
        let A' := eval vm_compute in A in change A with A' in FFr;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A' [c1] rest) FFr)) as FF1 end.
      match type of AAall with rw_cells _ _ ?A (?c1 :: ?c2 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A [c1] (c2 :: rest)) AAall)) as AA0;
        pose proof (proj2 (proj1 (rw_cells_app bsegs m A [c1] (c2 :: rest)) AAall)) as AAr end.
      match type of AAr with rw_cells _ _ ?A (?c1 :: ?rest) =>
        let A' := eval vm_compute in A in change A with A' in AAr;
        pose proof (proj1 (proj1 (rw_cells_app bsegs m A' [c1] rest) AAr)) as AA1 end.
      clear FFall AAall FFr AAr.
      eapply implF_epost_mono.
      + eapply (aexit_spec2 aps_so aset_so mdtor_pre module_dtor_proof mdtor_pre_frame
                  (F_stdio_exit.stdio_exit_proof aps_so aset_so aps_get_set' aps_set_set' aps_set_get') RNG s (fun (e : Empty_set) _ _ => match e with end))
          with (lo := lo) (t := t) (guard := guard);
          try first [ eassumption | reflexivity | exact KH | exact SP47 | (unfold MDTOR_DEPTH; clear - LO; lia) ].
      + intros [e ?] RNG' ms'. destruct e.
  Qed.
End Closed.
End CANSEC1.
