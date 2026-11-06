(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_target_runA F_main_AA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA ExitAllA ExitHeapA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require MainEntryA__A3D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit DrvStatA.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AInstanceF__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_S__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_init__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ComposeA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto MonadF. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_target_runA F_main_AA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA ExitAllA ExitHeapA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_target_runA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Compose.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation PS := (PState H hptr).
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation USP := (bv_unsigned sp0).
  Notation SBK := (build_stack_bytes a_phdrs sp0 argv envp uid hw rnd).
  Variables (L : alayout) (LO : Z).
  (* [comment removed for export] *)
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SBK.
  Hypothesis GA : gia_atx_laws GIOA.              (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt_d HO GIOA.
  Hypothesis FREE : free_stmt_d HO GIOA.
  Hypothesis EPR_USAGE : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage.
  Hypothesis EPR_OPEN : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt_o GIOA.
  Hypothesis SITE_RS : sites SiteReadStage = READ_STAGE.
  Hypothesis TRUN : target_run_stmt_o HO FO sites GIOA TP.
  Hypothesis LO_lo : (ATOP + 4096 <= LO)%Z.
  Hypothesis LO_hi : (LO + MAIN_STACK <= USP - 128)%Z.
  Hypothesis USP16 : (USP mod 16 = 0)%Z.
  Hypothesis TOP_lo : (USP - 160 <= al_top L)%Z.
  Hypothesis TOP47 : (al_top L <= 2^47)%Z.
  Hypothesis USP47 : (USP + Z.of_nat (length SBK) <= 2^47)%Z.
  Hypothesis TRD : traces_drv L.
  Hypothesis TRF : traces_fuzz_one TP L RA_FUZZ [].
  (* [comment removed for export] *)
  Variable SX : PS -> footprint -> mem -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Hypothesis stdio_exit_fits : 48 + MDTOR_DEPTH + stdio_exit_frame <= MAIN_STACK.
  Hypothesis SX_frame : forall s RNG sp m m', SX s RNG m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m m' -> wmono asegs m m' -> SX s RNG m'.
  Hypothesis STDIO_EXIT : stdio_exit_stmtA (@s_stdio_exit H hptr) SX stdio_exit_frame.
  (* [comment removed for export] *)
  Hypothesis GX : forall RNG s CL FB m, GIOA L RNG s CL FB [] m ->
    (exists t, exit_ci t m) /\ (exists (Hh : aholes) st LB, AHEAP_P Hh L RNG st LB m) /\ SX s RNG m.

  #[using="argv envp uid hw rnd GA LO_lo USP47 stdio_exit_fits GX"] Lemma at_exit_of_gioa : forall (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (s : PS) (CL FB : list (@cblock hptr)) (code : Z),
    GIOA L RNG s CL FB [] m -> mem_inv asegs m -> stk asegs m LO (bv_unsigned sp) -> (LO + MAIN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= USP - 48)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> rngs sp0 L LO RNG ->
    at_exit_closedA SX stdio_exit_frame code s RNG
      (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_ENTRY) fc None m (seg_rom asegs)).
  Proof.
    intros until code. intros G MI ST SPLO SPHI ALN (R1 & R2 & R3 & R4 & R5).
    (nd_pre (GX RNG s CL FB m G) 3%nat; intros [t EC] (Hh & st & LB & AH) HSX; nd_post).
    destruct (ga_get _ GA _ _ _ _ _ _ _ G) as [reg ATXC].
    destruct (exit_statics_of_heap Hh L RNG st LB m t reg AH EC ATXC) as ([t' [reg' EC']] & MP).
    unfold at_exit_closedA, at_exitA.
    exists ra, sp, gp, t0, t1, t2, s0, s1, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6, F, fc, m, LO, t', reg'.
    split; [reflexivity|]. split; [exact ST|]. split; [exact EC'|]. split; [exact MP|]. split; [exact HSX|]. split; [exact MI|].
    split; [generalize stdio_exit_fits; lia|]. split; [exact LO_lo|].
    split; [generalize USP47; pose proof (Nat2Z.is_nonneg (length SBK)); lia|]. split; [exact ALN|].
    split; [eapply rng_sub'; [exact R2| lia]|]. split; [exact R3|]. split; [exact R4| exact R5].
  Qed.

  #[using="TP fflagA GL GD GA MALLOC FREE EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF SX stdio_exit_frame stdio_exit_frame_nonneg stdio_exit_fits SX_frame STDIO_EXIT GX"] Theorem prog_main_impl : forall (s : PS) (RNG : footprint) (Q : Empty_set -> PS -> footprint -> machine_state -> Prop) (ms : machine_state),
    main_entry GIOA sp0 argv envp uid hw rnd L LO s RNG ms ->
    implMG RNG (prog_main HO FO sites (argv_Z argv)) s Q ms.
  Proof.
    intros s RNG Q ms ME. unfold prog_main.
    eapply implMG_bind.
    - (* [comment removed for export] *)
      eapply (main_spec HO FO sites GIOA TP fflagA sp0 argv envp uid hw rnd L LO (at_exit_closedA SX stdio_exit_frame));
        [ exact GL | exact GD | exact MALLOC | exact FREE | exact EPR_USAGE | exact EPR_OPEN | exact EPR_READ | exact EPR_BIG | exact EFW | exact SITE_RS | exact TRUN | exact LO_lo | exact LO_hi | exact USP16 | exact TOP_lo | exact TOP47 | exact USP47 | exact TRD | exact TRF | exact at_exit_of_gioa | exact ME ].
    - intros code s' RNG' ms' AE. unfold main_post in AE.
      eapply (exit_closedA (@s_stdio_exit H hptr) SX stdio_exit_frame stdio_exit_frame_nonneg SX_frame STDIO_EXIT). exact AE.
  Qed.
End Compose.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_target_runA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Compose.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation PS := (PState H hptr).
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation USP := (bv_unsigned sp0).
  Notation SBK := (build_stack_bytes a_phdrs sp0 argv envp uid hw rnd).
  Variables (L : alayout) (LO : Z).
  (* [comment removed for export] *)
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SBK.
  Hypothesis GA : gia_atx_laws GIOA.              (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt_d HO GIOA.
  Hypothesis FREE : free_stmt_d HO GIOA.
  Hypothesis EPR_USAGE : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage.
  Hypothesis EPR_OPEN : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt_o GIOA.
  Hypothesis SITE_RS : sites SiteReadStage = READ_STAGE.
  Hypothesis TRUN : target_run_stmt_o HO FO sites GIOA TP.
  Hypothesis LO_lo : (ATOP + 4096 <= LO)%Z.
  Hypothesis LO_hi : (LO + MAIN_STACK <= USP - 128)%Z.
  Hypothesis USP16 : (USP mod 16 = 0)%Z.
  Hypothesis TOP_lo : (USP - 160 <= al_top L)%Z.
  Hypothesis TOP47 : (al_top L <= 2^47)%Z.
  Hypothesis USP47 : (USP + Z.of_nat (length SBK) <= 2^47)%Z.
  Hypothesis TRD : traces_drv L.
  Hypothesis TRF : traces_fuzz_one TP L RA_FUZZ [].
  (* [comment removed for export] *)
  Variable SX : PS -> footprint -> mem -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Hypothesis stdio_exit_fits : 48 + MDTOR_DEPTH + stdio_exit_frame <= MAIN_STACK.
  Hypothesis SX_frame : forall s RNG sp m m', SX s RNG m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m m' -> wmono asegs m m' -> SX s RNG m'.
  Hypothesis STDIO_EXIT : stdio_exit_stmtA (@s_stdio_exit H hptr) SX stdio_exit_frame.
  (* [comment removed for export] *)
  Hypothesis GX : forall RNG s CL FB m, GIOA L RNG s CL FB [] m ->
    (exists t, exit_ci t m) /\ (exists (Hh : aholes) st LB, AHEAP_P Hh L RNG st LB m) /\ SX s RNG m.

  #[using="argv envp uid hw rnd GA LO_lo USP47 stdio_exit_fits GX"] Lemma at_exit_of_gioa : forall (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (s : PS) (CL FB : list (@cblock hptr)) (code : Z),
    GIOA L RNG s CL FB [] m -> mem_inv asegs m -> stk asegs m LO (bv_unsigned sp) -> (LO + MAIN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= USP - 48)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> rngs sp0 L LO RNG ->
    at_exit_closedA SX stdio_exit_frame code s RNG
      (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_ENTRY) fc None m (seg_rom asegs)).
  Proof.
    intros until code. intros G MI ST SPLO SPHI ALN (R1 & R2 & R3 & R4 & R5).
    (nd_pre (GX RNG s CL FB m G) 3%nat; intros [t EC] (Hh & st & LB & AH) HSX; nd_post).
    destruct (ga_get _ GA _ _ _ _ _ _ _ G) as [reg ATXC].
    destruct (exit_statics_of_heap Hh L RNG st LB m t reg AH EC ATXC) as ([t' [reg' EC']] & MP).
    unfold at_exit_closedA, at_exitA.
    exists ra, sp, gp, t0, t1, t2, s0, s1, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6, F, fc, m, LO, t', reg'.
    split; [reflexivity|]. split; [exact ST|]. split; [exact EC'|]. split; [exact MP|]. split; [exact HSX|]. split; [exact MI|].
    split; [generalize stdio_exit_fits; lia|]. split; [exact LO_lo|].
    split; [generalize USP47; pose proof (Nat2Z.is_nonneg (length SBK)); lia|]. split; [exact ALN|].
    split; [eapply rng_sub'; [exact R2| lia]|]. split; [exact R3|]. split; [exact R4| exact R5].
  Qed.

  #[using="TP fflagA GL GD GA MALLOC FREE EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF SX stdio_exit_frame stdio_exit_frame_nonneg stdio_exit_fits SX_frame STDIO_EXIT GX"] Theorem prog_main_impl : forall (s : PS) (RNG : footprint) (Q : Empty_set -> PS -> footprint -> machine_state -> Prop) (ms : machine_state),
    main_entry GIOA sp0 argv envp uid hw rnd L LO s RNG ms ->
    implMG RNG (prog_main HO FO sites (argv_Z argv)) s Q ms.
  Proof.
    intros s RNG Q ms ME. unfold prog_main.
    eapply implMG_bind.
    - (* [comment removed for export] *)
      eapply (main_spec HO FO sites GIOA TP fflagA sp0 argv envp uid hw rnd L LO (at_exit_closedA SX stdio_exit_frame));
        [ exact GL | exact GD | exact MALLOC | exact FREE | exact EPR_USAGE | exact EPR_OPEN | exact EPR_READ | exact EPR_BIG | exact EFW | exact SITE_RS | exact TRUN | exact LO_lo | exact LO_hi | exact USP16 | exact TOP_lo | exact TOP47 | exact USP47 | exact TRD | exact TRF | exact at_exit_of_gioa | exact ME ].
    - intros code s' RNG' ms' AE. unfold main_post in AE.
      eapply (exit_closedA (@s_stdio_exit H hptr) SX stdio_exit_frame stdio_exit_frame_nonneg SX_frame STDIO_EXIT). exact AE.
  Qed.
End Compose.
End CANSEC1.
End TwB.
End ComposeA.

(* [comment removed for export] *)
Module ExitInitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA ExitAllA ExitHeapA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

#[using="Type"] Lemma gd_shw_of_window : forall (m : amem) gs, Forall gd_ok gs -> wr_at asegs m SHW_LO SHW_LEN -> Forall (gd_shw m) gs.
Proof.
  intros m gs OK WR. eapply Forall_impl; [| exact OK]. intros ((((beg, sz), swr), nm), md) (AL & SWR & BLO & BHI). unfold gd_shw.
  assert (SWRf : swr mod 8 = 0 /\ 0 < swr) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
  destruct SWRf as [SL SZ]. (pose proof (shadow_window beg swr AL SL SZ BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
  eapply Shadow.wr_at_sub; [exact WR| lia| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Local Lemma gd69_cells : forall (V : nat -> Z) (m : amem), Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m 0xa9db0 (flat_map gd_cells GD69).
Proof.
  intros V m HM. eapply (img_chunk V m _ 0xa9db0 (flat_map gd_cells GD69) HM); [vm_compute; reflexivity | | vm_compute; reflexivity | lia | vm_compute; discriminate].
  vm_compute. repeat split.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma atx_init : forall (V : nat -> Z) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts -> atx_cells false 0 m.
Proof.
  intros V m HM. unfold atx_cells. cbn [Z.b2z]. change (1 + 0)%Z with 1%Z.
  aimg V m HM 0x5e0c50 [C1 (Z_to_bv 8 0)] IFL.
  aimg V m HM 0x5e0c54 [C1 (Z_to_bv 8 0)] CBC.
  aimg V m HM 0x601608 [C1 (Z_to_bv 8 0)] FIN.
  aimg V m HM 0x60160c [C4 (Z_to_bv 64 0)] ALK.
  mf V m HM (MCell (ZLit 6297104) 4 (ZLit 1)) SLOT.
  mf V m HM (MCell (ZLit 6297112) 8 (ZLit 6297120)) HEAD.
  aimg V m HM 0x601620 [C8 (Z_to_bv 64 0)] NEXT.
  mf V m HM (MCell (ZLit 6297128) 8 (ZLit 608112)) F0.
  aimg V m HM 0x601630 [C8 (Z_to_bv 64 0)] F1.
  mf V m HM (MCell (ZLit 6297384) 8 (ZLit 473984)) A0.
  aimg V m HM 0x601730 [C8 (Z_to_bv 64 0)] A1.
  mf V m HM (MCell (ZLit 6297672) 1 (ZLit 1)) LB0.
  aimg V m HM 0x601849 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] LB1.
  split; [exact IFL|]. split; [exact CBC|]. split; [exact FIN|]. split; [exact ALK|]. split; [exact SLOT|]. split; [exact HEAD|].
  split; [exact NEXT|]. split; [exact F0|]. split; [exact F1|]. split; [exact A0|]. split; [exact A1|].
  exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0). apply rw_cells_cons; [exact LB0| exact LB1].
Qed.

#[using="Type"] Lemma exit_statics_init : forall (V : nat -> Z) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> tls_at V ->
  exit_statics m.
Proof.
  intros V m HM HP HTLS. pose proof (tls_at_tp V HTLS) as HTP.
  split.
  - (* [comment removed for export] *)
    exists (V 44%nat), false. unfold exit_cells.
    mf V m HM (MCell (ZLit 6165776) 4 (ZV 44)) TID. replace 6165776 with (ATPv + -168) in TID by (rewrite HTP; reflexivity).
    aimg V m HM 0x601828 [C4 (Z_to_bv 64 0)] EXL.
    pose proof (atx_init V m HM) as ATXC.
    aimg V m HM 0x1404a0 [C1 (Z_to_bv 8 0)] COV.
    aimg V m HM 0xa6190 [C8 (Z_to_bv 64 0xa4f40); C8 (Z_to_bv 64 0xa4f30)] GF.
    aimg V m HM 0xa4f30 [C8 (Z_to_bv 64 0x84c10); C8 (Z_to_bv 64 0x32a80)] FA.
    aimg V m HM 0xaaf90 [C1 (Z_to_bv 8 0)] FINZ.
    aimg V m HM 0xa5480 [C8 (Z_to_bv 64 0x946a8); C8 (Z_to_bv 64 0)] GCX.
    aimg V m HM 0xa71d0 [C8 (Z_to_bv 64 0xa71d0)] DSO.
    pf V HP (PVar 44 1 4194303) P44.
    split; [exact TID|]. split; [exact EXL|]. split; [exact ATXC|].
    split; [exact COV|]. split; [exact GF|]. split; [exact FA|]. split; [exact FINZ|]. split; [exact GCX|].
    split; [exists (Z_to_bv 64 0xa71d0); exact DSO| lia].
  - (* [comment removed for export] *)
    unfold mdtor_pre.
    aimg V m HM 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] PGC.
    aimg V m HM 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                         C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] GOT.
    aimg V m HM 0xa54d0 [C8 (Z_to_bv 64 0xa7360)] GOT80.
    aimg V m HM 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)] REAL.
    mf V m HM (MCell (ZLit 714232) 8 (ZLit 2147450880)) SHB.
    mf V m HM (MCell (ZLit 717528) 1 (ZLit 1)) INI0. mf V m HM (MCell (ZLit 717529) 1 (ZLit 1)) INI1.
    mf V m HM (MCell (ZLit 712284) 1 (ZLit 1)) CANP.
    mf8 V m HM 0x1401a0 18446744073709551615 THR.
    mf V m HM (MCell (ZLit 704016) 8 (ZLit 72340168526266369)) RGL8.
    assert (RGL : rw_cells asegs m 0xabe10 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0x01010100)]) by recast RGL8.
    apply rw_cells_hd in RGL.
    aimg V m HM 0xa6148 [C8 (Z_to_bv 64 0xa9db0); C8 (Z_to_bv 64 0xaaf30)] GSS.
    mf V m HM (MCell (ZLit 700224) 8 (ZLit 1)) FLG.
    mf V m HM (MCell (ZLit 704176) 8 (ZLit 0)) MTX.
    aimg V m HM 700144 [C8 (Z_to_bv 64 0x5e0c80); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                         C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e0ca0)] D69.
    mf V m HM (MCell (ZLit 6163616) 1 (ZLit 1)) OD.
    mwr V m HM (ZLit 2147459072) 779776 WR.
    split. { unfold mdtor_rt. split; [exact PGC|]. split; [exact GOT|]. split; [exact GOT80|]. split; [exact REAL|]. split; [exact SHB|].
             split; [apply rw_cells_cons; [exact INI0| exact INI1]|]. split; [exact CANP|]. split; [exact THR| exact RGL]. }
    split; [exact GSS|]. split; [exact FLG|]. split; [exact MTX|].
    split. { apply descs_at_of_flat.
             exact (gd69_cells V m HM). }   (* [comment removed for export] *)
    split; [exact D69|]. split; [exists (Z_to_bv 8 1); exact OD|].
    split. { apply gd_shw_of_window; [exact GD69_ok| exact WR]. }
    split; (eapply Shadow.wr_at_sub; [exact WR| vm_compute; discriminate| vm_compute; discriminate]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma exit_ci_init : forall (V : nat -> Z) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> tls_at V ->
  exit_ci (V 44%nat) m.
Proof.
  intros V m HM HP HTLS. pose proof (tls_at_tp V HTLS) as HTP. unfold exit_ci.
  mf V m HM (MCell (ZLit 6165776) 4 (ZV 44)) TID. replace 6165776 with (ATPv + -168) in TID by (rewrite HTP; reflexivity).
  aimg V m HM 0x601828 [C4 (Z_to_bv 64 0)] EXL.
  aimg V m HM 0x1404a0 [C1 (Z_to_bv 8 0)] COV.
  aimg V m HM 0xaaf90 [C1 (Z_to_bv 8 0)] FINZ.
  aimg V m HM 0xa71d0 [C8 (Z_to_bv 64 0xa71d0)] DSO.
  pf V HP (PVar 44 1 4194303) P44.
  mf V m HM (MCell (ZLit 704016) 8 (ZLit 72340168526266369)) RGL8.
  assert (RGL : rw_cells asegs m 0xabe10 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0x01010100)]) by recast RGL8.
  apply rw_cells_hd in RGL.
  mf V m HM (MCell (ZLit 700224) 8 (ZLit 1)) FLG.
  mf V m HM (MCell (ZLit 704176) 8 (ZLit 0)) MTX.
  aimg V m HM 700144 [C8 (Z_to_bv 64 0x5e0c80); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                       C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e0ca0)] D69.
  mf V m HM (MCell (ZLit 6163616) 1 (ZLit 1)) OD.
  mwr V m HM (ZLit 2147459072) 779776 WR.
  split; [exact TID|]. split; [exact EXL|].
  split; [exact COV|]. split; [exact FINZ|]. split; [exists (Z_to_bv 64 0xa71d0); exact DSO|]. split; [lia|].
  split; [exact RGL|]. split; [exact FLG|]. split; [exact MTX|].
  split. { apply descs_at_of_flat.
           exact (gd69_cells V m HM). }   (* [comment removed for export] *)
  split; [exact D69|]. split; [exists (Z_to_bv 8 1); exact OD|].
  split. { apply gd_shw_of_window; [exact GD69_ok| exact WR]. }
  split; (eapply Shadow.wr_at_sub; [exact WR| vm_compute; discriminate| vm_compute; discriminate]).
Qed.
End CANSEC1.

(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

#[using="Type"] Lemma gd_shw_of_window : forall (m : amem) gs, Forall gd_ok gs -> wr_at asegs m SHW_LO SHW_LEN -> Forall (gd_shw m) gs.
Proof.
  intros m gs OK WR. eapply Forall_impl; [| exact OK]. intros ((((beg, sz), swr), nm), md) (AL & SWR & BLO & BHI). unfold gd_shw.
  assert (SWRf : swr mod 8 = 0 /\ 0 < swr) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
  destruct SWRf as [SL SZ]. (pose proof (shadow_window beg swr AL SL SZ BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
  eapply Shadow.wr_at_sub; [exact WR| lia| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Local Lemma gd69_cells : forall (V : nat -> Z) (m : amem), Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m 0xaa190 (flat_map gd_cells GD69).
Proof.
  intros V m HM. eapply (img_chunk V m _ 0xaa190 (flat_map gd_cells GD69) HM); [vm_compute; reflexivity | | vm_compute; reflexivity | lia | vm_compute; discriminate].
  vm_compute. repeat split.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma atx_init : forall (V : nat -> Z) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts -> atx_cells false 0 m.
Proof.
  intros V m HM. unfold atx_cells. cbn [Z.b2z]. change (1 + 0)%Z with 1%Z.
  aimg V m HM 0x5e1050 [C1 (Z_to_bv 8 0)] IFL.
  aimg V m HM 0x5e1054 [C1 (Z_to_bv 8 0)] CBC.
  aimg V m HM 0x601a08 [C1 (Z_to_bv 8 0)] FIN.
  aimg V m HM 0x601a0c [C4 (Z_to_bv 64 0)] ALK.
  mf V m HM (MCell (ZLit 6298128) 4 (ZLit 1)) SLOT.
  mf V m HM (MCell (ZLit 6298136) 8 (ZLit 6298144)) HEAD.
  aimg V m HM 0x601a20 [C8 (Z_to_bv 64 0)] NEXT.
  mf V m HM (MCell (ZLit 6298152) 8 (ZLit 609108)) F0.
  aimg V m HM 0x601a30 [C8 (Z_to_bv 64 0)] F1.
  mf V m HM (MCell (ZLit 6298408) 8 (ZLit 474088)) A0.
  aimg V m HM 0x601b30 [C8 (Z_to_bv 64 0)] A1.
  mf V m HM (MCell (ZLit 6298696) 1 (ZLit 1)) LB0.
  aimg V m HM 0x601c49 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] LB1.
  split; [exact IFL|]. split; [exact CBC|]. split; [exact FIN|]. split; [exact ALK|]. split; [exact SLOT|]. split; [exact HEAD|].
  split; [exact NEXT|]. split; [exact F0|]. split; [exact F1|]. split; [exact A0|]. split; [exact A1|].
  exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0). apply rw_cells_cons; [exact LB0| exact LB1].
Qed.

#[using="Type"] Lemma exit_statics_init : forall (V : nat -> Z) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> tls_at V ->
  exit_statics m.
Proof.
  intros V m HM HP HTLS. pose proof (tls_at_tp V HTLS) as HTP.
  split.
  - (* [comment removed for export] *)
    exists (V 44%nat), false. unfold exit_cells.
    mf V m HM (MCell (ZLit 6166800) 4 (ZV 44)) TID. replace 6166800 with (ATPv + -168) in TID by (rewrite HTP; reflexivity).
    aimg V m HM 0x601c28 [C4 (Z_to_bv 64 0)] EXL.
    pose proof (atx_init V m HM) as ATXC.
    aimg V m HM 0x1408a0 [C1 (Z_to_bv 8 0)] COV.
    aimg V m HM 0xa6570 [C8 (Z_to_bv 64 0xa5320); C8 (Z_to_bv 64 0xa5310)] GF.
    aimg V m HM 0xa5310 [C8 (Z_to_bv 64 0x84c9c); C8 (Z_to_bv 64 0x32ae8)] FA.
    aimg V m HM 0xab390 [C1 (Z_to_bv 8 0)] FINZ.
    aimg V m HM 0xa5860 [C8 (Z_to_bv 64 0x94a8c); C8 (Z_to_bv 64 0)] GCX.
    aimg V m HM 0xa75b0 [C8 (Z_to_bv 64 0xa75b0)] DSO.
    pf V HP (PVar 44 1 4194303) P44.
    split; [exact TID|]. split; [exact EXL|]. split; [exact ATXC|].
    split; [exact COV|]. split; [exact GF|]. split; [exact FA|]. split; [exact FINZ|]. split; [exact GCX|].
    split; [exists (Z_to_bv 64 0xa75b0); exact DSO| lia].
  - (* [comment removed for export] *)
    unfold mdtor_pre.
    aimg V m HM 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] PGC.
    aimg V m HM 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                         C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] GOT.
    aimg V m HM 0xa58b0 [C8 (Z_to_bv 64 0xa7740)] GOT80.
    aimg V m HM 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)] REAL.
    mf V m HM (MCell (ZLit 715256) 8 (ZLit 2147450880)) SHB.
    mf V m HM (MCell (ZLit 718552) 1 (ZLit 1)) INI0. mf V m HM (MCell (ZLit 718553) 1 (ZLit 1)) INI1.
    mf V m HM (MCell (ZLit 713308) 1 (ZLit 1)) CANP.
    mf8 V m HM 0x1405a0 18446744073709551615 THR.
    mf V m HM (MCell (ZLit 705040) 8 (ZLit 72340168526266369)) RGL8.
    assert (RGL : rw_cells asegs m 0xac210 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0x1010100)]) by recast RGL8.
    apply rw_cells_hd in RGL.
    aimg V m HM 0xa6528 [C8 (Z_to_bv 64 0xaa190); C8 (Z_to_bv 64 0xab310)] GSS.
    mf V m HM (MCell (ZLit 701248) 8 (ZLit 1)) FLG.
    mf V m HM (MCell (ZLit 705200) 8 (ZLit 0)) MTX.
    aimg V m HM 0xab2d0 [C8 (Z_to_bv 64 0x5e1080); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                         C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e10a0)] D69.
    mf V m HM (MCell (ZLit 6164640) 1 (ZLit 1)) OD.
    mwr V m HM (ZLit 2147459072) 780288 WR.
    split. { unfold mdtor_rt. split; [exact PGC|]. split; [exact GOT|]. split; [exact GOT80|]. split; [exact REAL|]. split; [exact SHB|].
             split; [apply rw_cells_cons; [exact INI0| exact INI1]|]. split; [exact CANP|]. split; [exact THR| exact RGL]. }
    split; [exact GSS|]. split; [exact FLG|]. split; [exact MTX|].
    split. { apply descs_at_of_flat.
             exact (gd69_cells V m HM). }   (* [comment removed for export] *)
    split; [exact D69|]. split; [exists (Z_to_bv 8 1); exact OD|].
    split. { apply gd_shw_of_window; [exact GD69_ok| exact WR]. }
    split; (eapply Shadow.wr_at_sub; [exact WR| vm_compute; discriminate| vm_compute; discriminate]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma exit_ci_init : forall (V : nat -> Z) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> tls_at V ->
  exit_ci (V 44%nat) m.
Proof.
  intros V m HM HP HTLS. pose proof (tls_at_tp V HTLS) as HTP. unfold exit_ci.
  mf V m HM (MCell (ZLit 6166800) 4 (ZV 44)) TID. replace 6166800 with (ATPv + -168) in TID by (rewrite HTP; reflexivity).
  aimg V m HM 0x601c28 [C4 (Z_to_bv 64 0)] EXL.
  aimg V m HM 0x1408a0 [C1 (Z_to_bv 8 0)] COV.
  aimg V m HM 0xab390 [C1 (Z_to_bv 8 0)] FINZ.
  aimg V m HM 0xa75b0 [C8 (Z_to_bv 64 0xa75b0)] DSO.
  pf V HP (PVar 44 1 4194303) P44.
  mf V m HM (MCell (ZLit 705040) 8 (ZLit 72340168526266369)) RGL8.
  assert (RGL : rw_cells asegs m 0xac210 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0x1010100)]) by recast RGL8.
  apply rw_cells_hd in RGL.
  mf V m HM (MCell (ZLit 701248) 8 (ZLit 1)) FLG.
  mf V m HM (MCell (ZLit 705200) 8 (ZLit 0)) MTX.
  aimg V m HM 0xab2d0 [C8 (Z_to_bv 64 0x5e1080); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                       C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e10a0)] D69.
  mf V m HM (MCell (ZLit 6164640) 1 (ZLit 1)) OD.
  mwr V m HM (ZLit 2147459072) 780288 WR.
  split; [exact TID|]. split; [exact EXL|].
  split; [exact COV|]. split; [exact FINZ|]. split; [exists (Z_to_bv 64 0xa75b0); exact DSO|]. split; [lia|].
  split; [exact RGL|]. split; [exact FLG|]. split; [exact MTX|].
  split. { apply descs_at_of_flat.
           exact (gd69_cells V m HM). }   (* [comment removed for export] *)
  split; [exact D69|]. split; [exists (Z_to_bv 8 1); exact OD|].
  split. { apply gd_shw_of_window; [exact GD69_ok| exact WR]. }
  split; (eapply Shadow.wr_at_sub; [exact WR| vm_compute; discriminate| vm_compute; discriminate]).
Qed.
End CANSEC1.
End TwB.
End ExitInitA.

(* [comment removed for export] *)
Module DrvStatInitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_main_AA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require MainEntryA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ExitHeapA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit DrvStatA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.ExitInitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis VI : valid_input inp.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  Notation USP := (bv_unsigned (en_sp en)).
  Notation L := (mkALayout (LV V) w U).
  Notation RNG := (fp_ok lz AL).
  Notation SBK := (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  Let HMP := me_facts en inp lim w V m ms mo AM.

  (* [comment removed for export] *)
  #[using="en inp lim w V ms mo AM HTLS U HU HMP"] Lemma errno_init : exists e : word, rw_cells asegs m (ATP + -164) [C4 e].
  Proof.
    destruct HMP as [HM HP]. pose proof (tls_at_tp V HTLS) as HTP.
    aimg V m HM 0x5e1514 [C4 (Z_to_bv 64 0)] EZ.
    exists (Z_to_bv 64 0). unfold ATP. rewrite HTP. replace (0x5e15b8 + -164) with 0x5e1514 by reflexivity.
    exact EZ.
  Qed.

  (* [comment removed for export] *)
  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma unp_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), unp_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. destruct HMP as [HM HP].
    mf V m HM (MZero (ZLit 2147459072) 8708) Z1. mf V m HM (MZero (ZLit 2147538406) 682923) Z2.
    split.
    - eapply (unpoisoned_of_zero m 2147459072 (2147459072 + 8708) (fun _ => 0)).
      + apply shadow_bytes_of_pointwise; [exact Z1| lia| lia].
      + intros; reflexivity.
      + unfold DRV_RODATA_LO. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold DRV_RODATA_HI. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold DRV_RODATA_LO. lia.
      + unfold DRV_RODATA_HI. lia.
    - eapply (unpoisoned_of_zero m 2147538406 (2147538406 + 682923) (fun _ => 0)).
      + apply shadow_bytes_of_pointwise; [exact Z2| lia| lia].
      + intros; reflexivity.
      + unfold READ_STAGE. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold READ_STAGE. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold READ_STAGE. lia.
      + unfold READ_STAGE. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI lim w V ms mo AM HAT HTLS U HU A0I VSP FITS HMP"] Lemma args_init : forall (L0 : alayout) (s : PS) (FB : list cblk), args_P USP (Z.of_nat (length SBK) - 16) L0 RNG s FB m.
  Proof.
    intros L0 s FB. destruct HMP as [HM HP]. (pose proof AM as ndP__; nd_pre ndP__ 11%nat; intros _ _ _ _ _ _ _ _ _ _ SH1; nd_post).
    pose proof (me_atop _ _ _ _ _ _ _ _ AM HAT U HU) as A.
    (nd_pre (me_geometry _ _ _ _ _ _ _ _ AM HAT U HU VSP FITS) 6%nat; intros _ _ U16 _ _ B47; nd_post). pose proof atop_range as AR.
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    (pose proof (ao_res L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ RESHI _; nd_post). (pose proof (ao_ctx L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ CTXHI _; nd_post).
    change (al_res L) with (4096 * V 208%nat) in RESHI. rewrite LV_ctx in CTXHI.
    pose proof (tls_at_tp V HTLS) as HTP. pose proof ATPv_hi as THI. rewrite HTP in THI.
    pf V HP (PVar 209 0 15) P209.
    pose proof (raw_len_nonneg a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as RN.
    pose proof (build_stack_bytes_length a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as BL.
    set (n := Z.of_nat (length SBK) - 16) in *.
    assert (N8 : 8 <= n) by (subst n; rewrite BL; unfold raw_len, struct_size, InitMem.argc, InitMem.envc; clear - RN; lia).
    change (2^47) with 140737488355328 in B47.
    destruct (args_sh USP n) as [E1 E2]. unfold args_P. rewrite E1, E2.
    assert (LEN : 0 < 2147450880 + 8 * ((USP + n + 63) / 64) - (2147450880 + 8 * (USP / 64))) by (clear - N8; Z.div_mod_to_equations; lia).
    destruct (shadow_zero_run V m (2147450880 + 8 * (USP / 64)) (2147450880 + 8 * ((USP + n + 63) / 64) - (2147450880 + 8 * (USP / 64))) SH1 HM HP LEN) as (Z0 & WR & _).
    { intros a Ha. right. subst n. clear - Ha A AR B47. Z.div_mod_to_equations. lia. }
    { intros a Ha. unfold ASHOFF. subst n.
      split; [clear - Ha A AR; Z.div_mod_to_equations; lia|].
      split; [clear - Ha A AR RESHI P209; Z.div_mod_to_equations; lia|].
      clear - Ha A AR CTXHI; Z.div_mod_to_equations; lia. }
    split.
    { eapply (unpoisoned_of_zero m (2147450880 + 8 * (USP / 64)) (2147450880 + 8 * ((USP + n + 63) / 64)) (fun _ => 0)).
      - replace (2147450880 + 8 * ((USP + n + 63) / 64)) with (2147450880 + 8 * (USP / 64) + (2147450880 + 8 * ((USP + n + 63) / 64) - (2147450880 + 8 * (USP / 64)))) by lia.
        apply shadow_bytes_of_pointwise; [exact Z0| clear - A AR; Z.div_mod_to_equations; lia| subst n; clear - A AR B47; Z.div_mod_to_equations; lia].
      - intros; reflexivity.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. clear - A AR. Z.div_mod_to_equations. lia.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. clear - A AR N8. Z.div_mod_to_equations. lia.
      - clear - A AR. lia.
      - subst n. clear - B47. lia. }
    split.
    { eapply (vis_rng lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; subst n; clear - HAT A AR B47 N8; lia. }
    split; [exact WR|].
    eapply (vis_rng_sh lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; subst n; clear - HAT A AR B47 N8; Z.div_mod_to_equations; lia.
  Qed.
End Init.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.ExitInitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Init.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis VI : valid_input inp.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  Notation USP := (bv_unsigned (en_sp en)).
  Notation L := (mkALayout (LV V) w U).
  Notation RNG := (fp_ok lz AL).
  Notation SBK := (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  Let HMP := me_facts en inp lim w V m ms mo AM.

  (* [comment removed for export] *)
  #[using="en inp lim w V ms mo AM HTLS U HU HMP"] Lemma errno_init : exists e : word, rw_cells asegs m (ATP + -164) [C4 e].
  Proof.
    destruct HMP as [HM HP]. pose proof (tls_at_tp V HTLS) as HTP.
    aimg V m HM 0x5e1914 [C4 (Z_to_bv 64 0)] EZ.
    exists (Z_to_bv 64 0). unfold ATP. rewrite HTP. replace (0x5e19b8 + -164) with 0x5e1914 by reflexivity.
    exact EZ.
  Qed.

  (* [comment removed for export] *)
  #[using="rc en inp lim w V ms mo AM U HU HMP"] Lemma unp_init : forall (L0 : alayout) (R0 : footprint) (s : PS) (FB : list cblk), unp_P L0 R0 s FB m.
  Proof.
    intros L0 R0 s FB. destruct HMP as [HM HP].
    mf V m HM (MZero (ZLit 2147459072) 8708) Z1. mf V m HM (MZero (ZLit 2147538530) 682927) Z2.
    split.
    - eapply (unpoisoned_of_zero m 2147459072 (2147459072 + 8708) (fun _ => 0)).
      + apply shadow_bytes_of_pointwise; [exact Z1| lia| lia].
      + intros; reflexivity.
      + unfold DRV_RODATA_LO. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold DRV_RODATA_HI. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold DRV_RODATA_LO. lia.
      + unfold DRV_RODATA_HI. lia.
    - eapply (unpoisoned_of_zero m 2147538530 (2147538530 + 682927) (fun _ => 0)).
      + apply shadow_bytes_of_pointwise; [exact Z2| lia| lia].
      + intros; reflexivity.
      + unfold READ_STAGE. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold READ_STAGE. rewrite shad_div. unfold ASHOFF. vm_compute. discriminate.
      + unfold READ_STAGE. lia.
      + unfold READ_STAGE. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI lim w V ms mo AM HAT HTLS U HU A0I VSP FITS HMP"] Lemma args_init : forall (L0 : alayout) (s : PS) (FB : list cblk), args_P USP (Z.of_nat (length SBK) - 16) L0 RNG s FB m.
  Proof.
    intros L0 s FB. destruct HMP as [HM HP]. (pose proof AM as ndP__; nd_pre ndP__ 11%nat; intros _ _ _ _ _ _ _ _ _ _ SH1; nd_post).
    pose proof (me_atop _ _ _ _ _ _ _ _ AM HAT U HU) as A.
    (nd_pre (me_geometry _ _ _ _ _ _ _ _ AM HAT U HU VSP FITS) 6%nat; intros _ _ U16 _ _ B47; nd_post). pose proof atop_range as AR.
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    (pose proof (ao_res L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ RESHI _; nd_post). (pose proof (ao_ctx L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ CTXHI _; nd_post).
    change (al_res L) with (4096 * V 208%nat) in RESHI. rewrite LV_ctx in CTXHI.
    pose proof (tls_at_tp V HTLS) as HTP. pose proof ATPv_hi as THI. rewrite HTP in THI.
    pf V HP (PVar 209 0 15) P209.
    pose proof (raw_len_nonneg a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as RN.
    pose proof (build_stack_bytes_length a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as BL.
    set (n := Z.of_nat (length SBK) - 16) in *.
    assert (N8 : 8 <= n) by (subst n; rewrite BL; unfold raw_len, struct_size, InitMem.argc, InitMem.envc; clear - RN; lia).
    change (2^47) with 140737488355328 in B47.
    destruct (args_sh USP n) as [E1 E2]. unfold args_P. rewrite E1, E2.
    assert (LEN : 0 < 2147450880 + 8 * ((USP + n + 63) / 64) - (2147450880 + 8 * (USP / 64))) by (clear - N8; Z.div_mod_to_equations; lia).
    destruct (shadow_zero_run V m (2147450880 + 8 * (USP / 64)) (2147450880 + 8 * ((USP + n + 63) / 64) - (2147450880 + 8 * (USP / 64))) SH1 HM HP LEN) as (Z0 & WR & _).
    { intros a Ha. right. subst n. clear - Ha A AR B47. Z.div_mod_to_equations. lia. }
    { intros a Ha. unfold ASHOFF. subst n.
      split; [clear - Ha A AR; Z.div_mod_to_equations; lia|].
      split; [clear - Ha A AR RESHI P209; Z.div_mod_to_equations; lia|].
      clear - Ha A AR CTXHI; Z.div_mod_to_equations; lia. }
    split.
    { eapply (unpoisoned_of_zero m (2147450880 + 8 * (USP / 64)) (2147450880 + 8 * ((USP + n + 63) / 64)) (fun _ => 0)).
      - replace (2147450880 + 8 * ((USP + n + 63) / 64)) with (2147450880 + 8 * (USP / 64) + (2147450880 + 8 * ((USP + n + 63) / 64) - (2147450880 + 8 * (USP / 64)))) by lia.
        apply shadow_bytes_of_pointwise; [exact Z0| clear - A AR; Z.div_mod_to_equations; lia| subst n; clear - A AR B47; Z.div_mod_to_equations; lia].
      - intros; reflexivity.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. clear - A AR. Z.div_mod_to_equations. lia.
      - rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880. clear - A AR N8. Z.div_mod_to_equations. lia.
      - clear - A AR. lia.
      - subst n. clear - B47. lia. }
    split.
    { eapply (vis_rng lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; subst n; clear - HAT A AR B47 N8; lia. }
    split; [exact WR|].
    eapply (vis_rng_sh lz AL V U A0I HU 13); [reflexivity| | | |]; cbn [fst snd zv nth_error asan_vis asan_vis_app app]; subst n; clear - HAT A AR B47 N8; Z.div_mod_to_equations; lia.
  Qed.
End Init.
End CANSEC1.
End TwB.
End DrvStatInitA.

(* [comment removed for export] *)
Module GioaMainA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AInstanceF__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_S__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_init__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_S__A3W.ARepInit_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ARepInit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.AResv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require MainEntryA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.DrvStatInitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AtMain.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis LU : (length U <= 4096)%nat.
  Hypothesis FU : Forall (fun u => (length u <= 254)%nat) U.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
     shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p.

  Notation L := (mkALayout (LV V) w U).
  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  #[using="en inp lim ms mo AM HAT HTLS LU FU A0I ASH0"] Lemma aheap_main : AHEAP_I L RNG (ST0 V) [] m.
  Proof.
    (pose proof AM as ndP__; nd_pre ndP__ 11%nat; intros _ _ _ HMall HPall _ _ _ SH0 _ SH1; nd_post).
    apply Forall_app in HMall as [HM HMW]. apply Forall_app in HPall as [HP _].
    assert (HU : (length U <= Z.to_nat AUMAX)%nat) by (unfold AUMAX; lia).
    apply (AHEAP_P_init_qdf ASEC_of V w U m lz AL); try assumption.
    apply (ASEC_of_init V w U m HM HP HU HAT HTLS SH0 SH1).
  Qed.

  Variable CI : list (Z * Z).
  Hypothesis CIB : ci_okb CI = true.
  Variable cs : list gcomp.
  Variables (libc0 : libc_st aptr) (of0 : option aptr) (tls0 : Z).
  Notation s0 := (mkPS (aheap_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V)) libc0 of0 tls0).

  #[using="en inp lim ms mo AM HAT HTLS LU FU A0I ASH0"] Theorem gioa_at_main : gconj cs L RNG s0 [] m -> GIOA_real (AI_of CI CIB) (GSTAT_of cs) L RNG s0 [] [] [] m.
  Proof.
    intros GC. (pose proof AM as ndP__; nd_pre ndP__ 6%nat; intros _ _ _ _ HPall _; nd_post). apply Forall_app in HPall as [HP _].
    assert (HU : (length U <= Z.to_nat AUMAX)%nat) by (unfold AUMAX; lia).
    split; [exact aheap_main|].
    split; [exact (aresv_ok_handoff V w U HP)|].
    split; [intros b Hb; destruct Hb|].
    split; [reflexivity|]. split; [constructor|]. split; [constructor|].
    split; [exact (errno_init _ _ _ _ _ _ _ _ AM HTLS U HU)| exact GC].
  Qed.
End AtMain.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_S__A3W.ARepInit_S.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ARepInit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.AResv.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.DrvStatInitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AtMain.
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis LU : (length U <= 4096)%nat.
  Hypothesis FU : Forall (fun u => (length u <= 254)%nat) U.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
     shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p.

  Notation L := (mkALayout (LV V) w U).
  Notation RNG := (fp_ok lz AL).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  #[using="en inp lim ms mo AM HAT HTLS LU FU A0I ASH0"] Lemma aheap_main : AHEAP_I L RNG (ST0 V) [] m.
  Proof.
    (pose proof AM as ndP__; nd_pre ndP__ 11%nat; intros _ _ _ HMall HPall _ _ _ SH0 _ SH1; nd_post).
    apply Forall_app in HMall as [HM HMW]. apply Forall_app in HPall as [HP _].
    assert (HU : (length U <= Z.to_nat AUMAX)%nat) by (unfold AUMAX; lia).
    apply (AHEAP_P_init_qdf ASEC_of V w U m lz AL); try assumption.
    apply (ASEC_of_init V w U m HM HP HU HAT HTLS SH0 SH1).
  Qed.

  Variable CI : list (Z * Z).
  Hypothesis CIB : ci_okb CI = true.
  Variable cs : list gcomp.
  Variables (libc0 : libc_st aptr) (of0 : option aptr) (tls0 : Z).
  Notation s0 := (mkPS (aheap_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V)) libc0 of0 tls0).

  #[using="en inp lim ms mo AM HAT HTLS LU FU A0I ASH0"] Theorem gioa_at_main : gconj cs L RNG s0 [] m -> GIOA_real (AI_of CI CIB) (GSTAT_of cs) L RNG s0 [] [] [] m.
  Proof.
    intros GC. (pose proof AM as ndP__; nd_pre ndP__ 6%nat; intros _ _ _ _ HPall _; nd_post). apply Forall_app in HPall as [HP _].
    assert (HU : (length U <= Z.to_nat AUMAX)%nat) by (unfold AUMAX; lia).
    split; [exact aheap_main|].
    split; [exact (aresv_ok_handoff V w U HP)|].
    split; [intros b Hb; destruct Hb|].
    split; [reflexivity|]. split; [constructor|]. split; [constructor|].
    split; [exact (errno_init _ _ _ _ _ _ _ _ AM HTLS U HU)| exact GC].
  Qed.
End AtMain.
End CANSEC1.
End TwB.
End GioaMainA.
