(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad PcapTypes Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA F_next_exA F_offline_readA.
From Stdlib Require NArith Lia Bool.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt StdioCore Stdio PcapPrelim PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ITreeA Shadow StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells I_asan_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AProto AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require HeapRulesS GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AccFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UnwLowerB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_next_ex_allA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad PcapTypes Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA F_next_exA F_offline_readA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_exA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_offline_readA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[using="Type"] Theorem pcap_next_ex_closedA :
    gia_laws FO GIOA fflagA -> fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1 -> fret_inline_law FO GIOA fflagA ->
    pcap_next_packet_stmt HO FO sites GIOA TP -> pcap_ng_next_packet_stmt HO FO sites GIOA TP -> oneshot_stmt ->
    pcap_next_ex_stmt HO FO sites GIOA TP.
  Proof.
    intros GL FENTER1 FRET NP_PCAP NP_NG ONESHOT.
    exact (next_ex_proofA HO FO sites GIOA TP fflagA GL FENTER1 FRET
             (offline_read_proofA HO FO sites GIOA TP fflagA GL FENTER1 FRET NP_PCAP NP_NG ONESHOT)).
  Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_exA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_offline_readA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[using="Type"] Theorem pcap_next_ex_closedA :
    gia_laws FO GIOA fflagA -> fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1 -> fret_inline_law FO GIOA fflagA ->
    pcap_next_packet_stmt HO FO sites GIOA TP -> pcap_ng_next_packet_stmt HO FO sites GIOA TP -> oneshot_stmt ->
    pcap_next_ex_stmt HO FO sites GIOA TP.
  Proof.
    intros GL FENTER1 FRET NP_PCAP NP_NG ONESHOT.
    exact (next_ex_proofA HO FO sites GIOA TP fflagA GL FENTER1 FRET
             (offline_read_proofA HO FO sites GIOA TP fflagA GL FENTER1 FRET NP_PCAP NP_NG ONESHOT)).
  Qed.
End CANSEC1.
End TwB.
End F_next_ex_allA.

(* [comment removed for export] *)
Module F_oneshotA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase RtCells AMalloc_iface I_asan_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

  Definition oneshot_proofA__stmt : Prop := oneshot_stmt.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc : ltac2:(SecDiet.SzSec.tyM 'oneshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="Type"] Lemma oneshot_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'oneshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros -> -> HU HSRC HHD HPK Hpk D1 D2 D3 D4 D5 MI ST BU LO RT OU OS OH OP TU TS TH TPK AU AK AH AS RSTK RIMG RISH RTLS.
 qfold.
    pose proof OS as OS0. pose proof OH as OH0. pose proof RT as RT0.
    destruct OU as (U0 & _ & UUNP & URNG & URSH & UAR & UBAND). destruct OS as (S0 & _ & SUNP & SRNG & SRSH & SAR & SBAND).
    destruct OH as (H0 & _ & HUNP & HRNG & HRSH & HAR & HBAND). destruct OP as (K0 & _ & KUNP & KRNG & KRSH & KAR & KBAND).
    replace (U - U mod 8)%Z with U in URSH by lia. replace (24 + U mod 8)%Z with 24%Z in URSH by lia.
    replace (PKT - PKT mod 8)%Z with PKT in KRSH by lia. replace (8 + PKT mod 8)%Z with 8%Z in KRSH by lia.
    pose proof (ablk_app_blk _ _ SBAND ltac:(lia)) as SAPP. pose proof (ablk_app_blk _ _ HBAND ltac:(lia)) as HAPP.
    band_ind UBAND bU. band_ind SBAND bS. band_ind HBAND bH. band_ind KBAND bK.
    disj_ind D1 k1. disj_ind D2 k2. disj_ind D3 k3. disj_ind D4 k4. disj_ind D5 k5.
    destruct RT as (_ & GOT & GRIC & RMEM & SHB & _ & INI & LAY & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    unfold ONESHOT_STACK in *.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    destruct (rw_cells_forget _ _ _ _ HHD) as [hdj HDc]. clear HHD. cbn [cells_size csize Nat.add] in HDc.
    pose proof (rw_cells_bytes_at _ _ _ _ HSRC) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
    unfold PK; cbn [pk_oneshot].
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (HD, HD + 24); (PKT, PKT + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 10 zstep.
    ck0 UUNP; ck_go.
    do 3 zstep.
    call_sp (asan_memcpy_specZ RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo HD SRC 24%Z (le8 w0 ++ le8 w1 ++ le8 w2) hdj);
      [ reflexivity | reflexivity | reflexivity | assumption | exact ST | lia | lia
      | eapply (artcells_munch _ _ _ RT0 MU WM); repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil
      | exact SRCB | reflexivity | lia | exact HDc | lia
      | apply aobjA_mobjA; [eapply aobjA_wmono; [exact OS0 | exact WM | exact SUNP] | lia]
      | apply aobjA_mobjA; [eapply aobjA_wmono; [exact OH0 | exact WM | exact HUNP] | lia]
      | lia | lia | ].
    zstep.
    ck0 UUNP; ck_go.
    zstep.
    ck0 KUNP; ck_go.
    do 7 zstep.
    release_frame FR PC (bv_unsigned sp).
    assert (HD3 : rw_cells asegs m0 HD [C8 w0; C8 w1; C8 w2])
      by (eapply rw_cells_recell; [exact PC0 | cbn; repeat split; exact I | cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]).
    apply evtF_done. do 16 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|].
    split; [exact HU|]. split; [exact HSRC|]. split; [exact HD3| exact HPc].
  Qed.
  End Sz1.
  #[using="Type"] Theorem oneshot_proofA : ltac:(let t := eval cbv delta [oneshot_proofA__stmt] in oneshot_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc. ltac2:(SecDiet.SzSec.closeP 'oneshot_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_asan_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

  Definition oneshot_proofA__stmt : Prop := oneshot_stmt.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc : ltac2:(SecDiet.SzSec.tyM 'oneshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="Type"] Lemma oneshot_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'oneshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros -> -> HU HSRC HHD HPK Hpk D1 D2 D3 D4 D5 MI ST BU LO RT OU OS OH OP TU TS TH TPK AU AK AH AS RSTK RIMG RISH RTLS.
 qfold.
    pose proof OS as OS0. pose proof OH as OH0. pose proof RT as RT0.
    destruct OU as (U0 & _ & UUNP & URNG & URSH & UAR & UBAND). destruct OS as (S0 & _ & SUNP & SRNG & SRSH & SAR & SBAND).
    destruct OH as (H0 & _ & HUNP & HRNG & HRSH & HAR & HBAND). destruct OP as (K0 & _ & KUNP & KRNG & KRSH & KAR & KBAND).
    replace (U - U mod 8)%Z with U in URSH by lia. replace (24 + U mod 8)%Z with 24%Z in URSH by lia.
    replace (PKT - PKT mod 8)%Z with PKT in KRSH by lia. replace (8 + PKT mod 8)%Z with 8%Z in KRSH by lia.
    pose proof (ablk_app_blk _ _ SBAND ltac:(lia)) as SAPP. pose proof (ablk_app_blk _ _ HBAND ltac:(lia)) as HAPP.
    band_ind UBAND bU. band_ind SBAND bS. band_ind HBAND bH. band_ind KBAND bK.
    disj_ind D1 k1. disj_ind D2 k2. disj_ind D3 k3. disj_ind D4 k4. disj_ind D5 k5.
    destruct RT as (_ & GOT & GRIC & RMEM & SHB & _ & INI & LAY & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    unfold ONESHOT_STACK in *.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    destruct (rw_cells_forget _ _ _ _ HHD) as [hdj HDc]. clear HHD. cbn [cells_size csize Nat.add] in HDc.
    pose proof (rw_cells_bytes_at _ _ _ _ HSRC) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
    unfold PK; cbn [pk_oneshot].
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (HD, HD + 24); (PKT, PKT + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 5 zstep. ub_null.                  (* [comment removed for export] *)
    do 2 zstep. ub_al 7%Z ltac:(al8 AU). zstep. if_false.
    do 3 zstep.
    ck0 UUNP; ck_go.
    do 4 zstep.                           (* [comment removed for export] *)
    call_sp (asan_memcpy_specZ RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo HD SRC 24%Z (le8 w0 ++ le8 w1 ++ le8 w2) hdj);
      [ reflexivity | reflexivity | reflexivity | assumption | exact ST | lia | lia
      | eapply (artcells_munch _ _ _ RT0 MU WM); repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil
      | exact SRCB | reflexivity | lia | exact HDc | lia
      | apply aobjA_mobjA; [eapply aobjA_wmono; [exact OS0 | exact WM | exact SUNP] | lia]
      | apply aobjA_mobjA; [eapply aobjA_wmono; [exact OH0 | exact WM | exact HUNP] | lia]
      | lia | lia | ].
    zstep.
    ck0 UUNP; ck_go.
    zstep. ub_null.                       (* [comment removed for export] *)
    zstep. ub_al 7%Z ltac:(al8 AK). zstep. if_false.
    ck0 KUNP; ck_go.
    do 7 zstep.
    release_frame FR PC (bv_unsigned sp).
    assert (HD3 : rw_cells asegs m0 HD [C8 w0; C8 w1; C8 w2])
      by (eapply rw_cells_recell; [exact PC0 | cbn; repeat split; exact I | cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]).
    apply evtF_done. do 16 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|].
    split; [exact HU|]. split; [exact HSRC|]. split; [exact HD3| exact HPc].
  Qed.
  End Sz1.
  #[using="Type"] Theorem oneshot_proofA : ltac:(let t := eval cbv delta [oneshot_proofA__stmt] in oneshot_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc. ltac2:(SecDiet.SzSec.closeP 'oneshot_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_oneshotA.

(* [comment removed for export] *)
Module GioaFake.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto AMalloc_iface AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_arep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.AFake_free7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA HeapRulesS GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.HeapRulesS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section GioaFake.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Variable GSTAT : alayout -> footprint -> PState aheap aptr -> list (@cblock aptr) -> mem -> Prop.
  #[local] Notation GIOA := (GIOA_real AI GSTAT).
  #[local] Notation FOA := (asan_fo site_frameA).
  Hypothesis GS_pres : forall L RNG RNG' s s' FB (LB : list ablock) SP (m m' : mem),
      GSTAT L RNG s FB m -> fp_le RNG RNG' -> aheap_pres (aci AI) LB SP m m' -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP ->
      ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> GSTAT L RNG' s' FB m'.

  (* [comment removed for export] *)
  #[using="rc"] Lemma fk_count_LBof : forall c (CL FB : list (@cblock aptr)) FL, fk_count c (LBof CL FB FL) <= Z.of_nat (length FL).
  Proof.
    intros c CL FB FL. unfold fk_count, LBof. rewrite List.filter_app, length_app.
    assert (E : List.filter (is_fake_cls c) (map hb_of (CL ++ FB)) = []).
    { induction (CL ++ FB) as [|b l IH]; [reflexivity|]. cbn [map List.filter hb_of is_fake_cls ab_kind]. exact IH. }
    rewrite E. cbn [length]. pose proof (List.filter_length_le (is_fake_cls c) (map fkb_of FL)) as LE. rewrite length_map in LE. lia.
  Qed.
  #[using="Type"] Lemma frames_le9 : forall (FL : list fblock), List.NoDup (map fb_fn FL) -> (length FL <= 9)%nat.
  Proof.
    intros FL ND. rewrite <- (length_map fb_fn).
    apply (NoDup_incl_length (l' := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_NEXT_PACKET; FF_OFFLINE_READ; FF_NEXT_EX; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK; FF_FUZZ_ONE_INPUT]) ND).
    intros f _. destruct f; cbn; tauto.
  Qed.

  #[using="AF GS_pres"] Theorem fenter_real : forall k SYM, (k = 0 /\ SYM = STACK_MALLOC_0) \/ (k = 1 /\ SYM = STACK_MALLOC_1) -> fenter_stmt_o FOA GIOA fflagA_real k SYM.
  Proof.
    intros k SYM KS. red. intros until Q. intros PRE -> REQ NIN CLS KONT.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). unfold FAKE_STACK in BU.
    assert (KS' : (k = 0 /\ SYM = ASTKMALLOC0) \/ (k = 1 /\ SYM = ASTKMALLOC1)) by exact KS.
    assert (FSZ : ff_size f = fk_fsize k) by (rewrite <- CLS; unfold ff_size, fk_fsize; destruct f; reflexivity).
    eapply implMG_evtF.
    - eapply (AF_sm _ AF k SYM KS' L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 req) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo);
        [ exact AH
        | pose proof (fk_count_LBof k CL FB FL) as C1; pose proof (frames_le9 FL ND) as C2; destruct KS as [[-> _]|[-> _]]; [replace (fk_nframes 0) with 16384 by reflexivity| replace (fk_nframes 1) with 8192 by reflexivity]; lia
        | exact MI | exact ST | exact LO | unfold SM_STACK; lia | lia | exact TPE | exact RSTK | exact RIMG | exact RTLS | exact (AF_rng _ AF _ _ _ _ _ AH) ].
    - cbv beta. intros ms' PO. destruct_exs PO.
      destruct PO as (-> & MI' & ST' & HP & AH' & F64 & F0 & FBAND & FTOP & LJ & FRC & SHC).
      rename x into Fb. pose proof (ablk_lin _ _ FBAND) as (_ & _ & _ & FT47).
      assert (EA : a0_of (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 Fb) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = Fb)
        by (unfold a0_of; etransitivity; [| apply (unsigned_lit Fb); lia]; reflexivity).
      assert (KP : 0 < fk_fsize k) by (apply fk_fsize_pos; destruct KS as [[-> _]|[-> _]]; lia).
      unfold implMG. eapply implS_fo_enter0; rewrite EA; [lia|].
        eapply (KONT Fb _ x14 x15 x16 x17 x18 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13);
          [ | reflexivity | reflexivity | reflexivity | exact MI' | exact ST'
            | eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb] | exact F0 | rewrite FSZ; exact LJ
            | rewrite FSZ; unfold fflagA_real; rewrite CLS; exact FRC
            | rewrite FSZ; replace (Z.shiftr Fb 3 + 2147450880) with (shad Fb) by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia); exact SHC ].
        (* [comment removed for export] *)
        split.
        { eapply (AI_perm AI); [| exact AH']. unfold LBof. cbn [map]. unfold fkb_of at 2. cbn [fb_fn fb_addr fb_size fst snd]. rewrite CLS, FSZ. apply Permutation.Permutation_middle. }
        cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
        split; [exact RV|]. split; [exact AD|]. split; [cbn [map fb_fn fb_addr fst snd]; rewrite EF; reflexivity|].
        split; [apply Forall_cons; [reflexivity| exact SZ]|]. split; [cbn [map fb_fn fst snd]; apply List.NoDup_cons; assumption|].
        eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="AF GS_pres"] Theorem fret_real : fret_inline_law FOA GIOA fflagA_real.
  Proof.
    red. intros L RNG s CL FB FL f Fb m m' A x Q ms G CLS MU WM FLC KONT.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    assert (PM : Permutation.Permutation (LBof CL FB ((f, Fb, ff_size f) :: FL)) (FKB (ff_class f) Fb (ff_size f) :: LBof CL FB FL))
      by (unfold LBof; cbn [map]; unfold fkb_of at 1; cbn [fb_fn fb_addr fb_size fst snd]; symmetry; apply Permutation.Permutation_middle).
    pose proof (AI_perm AI _ _ _ _ _ _ PM AH) as AH1. atop_facts.
    assert (SPZ : ATOP <= ATOP + 4096) by (clear; lia).
    destruct (AF_release _ AF _ _ _ _ _ _ _ _ _ (ATOP + 4096) AH1 SPZ MU WM FLC) as [AH2 HP].
    unfold implMG. apply implS_fo_ret0. cbn [fst snd]. apply KONT; [| reflexivity | reflexivity | reflexivity].
    split; [exact AH2|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
    split; [exact RV|]. split; [exact AD|]. split; [rewrite EF; reflexivity|].
    split; [exact (Forall_inv_tail SZ)|]. split; [cbn [map] in ND; apply List.NoDup_cons_iff in ND as [_ ND']; exact ND'|].
    eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="AF GS_pres"] Theorem fenter7_real : fenter7_stmt_o FOA GIOA fflagA_real.
  Proof.
    red. intros until Q. intros PRE -> REQ REQ8 NIN CLS KONT.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). unfold FAKE_STACK in BU.
    assert (FSZ : ff_size f = 8192) by (unfold ff_size; rewrite CLS; reflexivity).
    eapply implMG_evtF.
    - change STACK_MALLOC_7 with ASTKMALLOC7.
      eapply (AF_sm7 _ AF L RNG req ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 req) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo);
        [ exact AH
        | pose proof (fk_count_LBof 7 CL FB FL) as C1; pose proof (frames_le9 FL ND) as C2; replace (fk_nframes 7) with 128 by reflexivity; lia
        | reflexivity | lia | exact REQ8
        | exact MI | exact ST | exact LO | unfold SM_STACK; lia | lia | exact TPE | exact RSTK | exact RIMG | exact RTLS | exact (AF_rng _ AF _ _ _ _ _ AH) ].
    - cbv beta. intros ms' PO. destruct_exs PO.
      destruct PO as (-> & MI' & ST' & HP & AH' & F64 & F0 & FBAND & FTOP & LJ & FRC & LSJ & SHC).
      rename x into Fb. pose proof (ablk_lin _ _ FBAND) as (_ & _ & _ & FT47).
      assert (EA : a0_of (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 Fb) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = Fb)
        by (unfold a0_of; etransitivity; [| apply (unsigned_lit Fb); lia]; reflexivity).
      unfold implMG. eapply implS_fo_enter0; rewrite EA; [lia|].
      eapply (KONT Fb _ x14 x15 x16 x17 x18 x19 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13);
        [ | reflexivity | reflexivity | reflexivity | exact MI' | exact ST'
          | eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb] | exact F0 | rewrite FSZ; exact LJ | rewrite FSZ; exact LSJ
          | rewrite FSZ; unfold fflagA_real; rewrite CLS; exact FRC
          | rewrite FSZ; replace (Z.shiftr Fb 3 + 2147450880) with (shad Fb) by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia); exact SHC ].
      split.
      { eapply (AI_perm AI); [| exact AH']. unfold LBof. cbn [map]. unfold fkb_of at 2. cbn [fb_fn fb_addr fb_size fst snd]. rewrite CLS, FSZ. apply Permutation.Permutation_middle. }
      cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
      split; [exact RV|]. split; [exact AD|]. split; [cbn [map fb_fn fb_addr fst snd]; rewrite EF; reflexivity|].
      split; [apply Forall_cons; [reflexivity| exact SZ]|]. split; [cbn [map fb_fn fst snd]; apply List.NoDup_cons; assumption|].
      eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.

  #[using="AF GS_pres"] Theorem ffree7_real : ffree7_stmt_o FOA GIOA fflagA_real.
  Proof.
    red. intros until Q. intros PRE CLS -> -> REQ REQ8 LAST KONT.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). unfold FAKE_STACK in BU.
    assert (FSZ : ff_size f = 8192) by (unfold ff_size; rewrite CLS; reflexivity). rewrite FSZ in *.
    assert (PM : Permutation.Permutation (LBof CL FB ((f, Fb, 8192) :: FL)) (FKB 7 Fb 8192 :: LBof CL FB FL))
      by (unfold LBof; cbn [map]; unfold fkb_of at 1; cbn [fb_fn fb_addr fb_size fst snd]; rewrite CLS; symmetry; apply Permutation.Permutation_middle).
    pose proof (AI_perm AI _ _ _ _ _ _ PM AH) as AH1.
    eapply implMG_evtF.
    - change STACK_FREE_7 with ASTKFREE7.
      eapply (AF_sf7 _ AF L RNG req ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fb) (Z_to_bv 64 req) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo Fb);
        [ exact AH1 | reflexivity | reflexivity | lia | exact REQ8
        | unfold fflagA_real in LAST; rewrite CLS in LAST; replace (Fb + 8184) with (Fb + 8192 - 8) by lia; exact LAST
        | exact MI | exact ST | exact LO | unfold SM_STACK; lia | lia | exact RSTK | exact RIMG | exact RTLS | exact (AF_rng _ AF _ _ _ _ _ AH) ].
    - cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MI' & ST' & HP & AH').
      unfold implMG. apply implS_fo_ret0. cbn [fst snd].
      eapply KONT; [ | reflexivity | reflexivity | reflexivity | exact MI' | exact ST'
                     | eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb] ].
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
      split; [exact RV|]. split; [exact AD|]. split; [rewrite EF; reflexivity|].
      split; [exact (Forall_inv_tail SZ)|]. split; [cbn [map] in ND; apply List.NoDup_cons_iff in ND as [_ ND']; exact ND'|].
      eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.
End GioaFake.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.AFake_sm7.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.AFake_free7.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.HeapRulesS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section GioaFake.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Variable GSTAT : alayout -> footprint -> PState aheap aptr -> list (@cblock aptr) -> mem -> Prop.
  #[local] Notation GIOA := (GIOA_real AI GSTAT).
  #[local] Notation FOA := (asan_fo site_frameA).
  Hypothesis GS_pres : forall L RNG RNG' s s' FB (LB : list ablock) SP (m m' : mem),
      GSTAT L RNG s FB m -> fp_le RNG RNG' -> aheap_pres (aci AI) LB SP m m' -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP ->
      ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> GSTAT L RNG' s' FB m'.

  (* [comment removed for export] *)
  #[using="rc"] Lemma fk_count_LBof : forall c (CL FB : list (@cblock aptr)) FL, fk_count c (LBof CL FB FL) <= Z.of_nat (length FL).
  Proof.
    intros c CL FB FL. unfold fk_count, LBof. rewrite List.filter_app, length_app.
    assert (E : List.filter (is_fake_cls c) (map hb_of (CL ++ FB)) = []).
    { induction (CL ++ FB) as [|b l IH]; [reflexivity|]. cbn [map List.filter hb_of is_fake_cls ab_kind]. exact IH. }
    rewrite E. cbn [length]. pose proof (List.filter_length_le (is_fake_cls c) (map fkb_of FL)) as LE. rewrite length_map in LE. lia.
  Qed.
  #[using="Type"] Lemma frames_le9 : forall (FL : list fblock), List.NoDup (map fb_fn FL) -> (length FL <= 9)%nat.
  Proof.
    intros FL ND. rewrite <- (length_map fb_fn).
    apply (NoDup_incl_length (l' := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_NEXT_PACKET; FF_OFFLINE_READ; FF_NEXT_EX; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK; FF_FUZZ_ONE_INPUT]) ND).
    intros f _. destruct f; cbn; tauto.
  Qed.

  #[using="AF GS_pres"] Theorem fenter_real : forall k SYM, (k = 0 /\ SYM = STACK_MALLOC_0) \/ (k = 1 /\ SYM = STACK_MALLOC_1) -> fenter_stmt_o FOA GIOA fflagA_real k SYM.
  Proof.
    intros k SYM KS. red. intros until Q. intros PRE -> REQ NIN CLS KONT.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). unfold FAKE_STACK in BU.
    assert (KS' : (k = 0 /\ SYM = ASTKMALLOC0) \/ (k = 1 /\ SYM = ASTKMALLOC1)) by exact KS.
    assert (FSZ : ff_size f = fk_fsize k) by (rewrite <- CLS; unfold ff_size, fk_fsize; destruct f; reflexivity).
    eapply implMG_evtF.
    - eapply (AF_sm _ AF k SYM KS' L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 req) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo);
        [ exact AH
        | pose proof (fk_count_LBof k CL FB FL) as C1; pose proof (frames_le9 FL ND) as C2; destruct KS as [[-> _]|[-> _]]; [replace (fk_nframes 0) with 16384 by reflexivity| replace (fk_nframes 1) with 8192 by reflexivity]; lia
        | exact MI | exact ST | exact LO | unfold SM_STACK; lia | lia | exact TPE | exact RSTK | exact RIMG | exact RTLS | exact (AF_rng _ AF _ _ _ _ _ AH) ].
    - cbv beta. intros ms' PO. destruct_exs PO.
      destruct PO as (-> & MI' & ST' & HP & AH' & F64 & F0 & FBAND & FTOP & LJ & FRC & SHC).
      rename x into Fb. pose proof (ablk_lin _ _ FBAND) as (_ & _ & _ & FT47).
      assert (EA : a0_of (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 Fb) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = Fb)
        by (unfold a0_of; etransitivity; [| apply (unsigned_lit Fb); lia]; reflexivity).
      assert (KP : 0 < fk_fsize k) by (apply fk_fsize_pos; destruct KS as [[-> _]|[-> _]]; lia).
      unfold implMG. eapply implS_fo_enter0; rewrite EA; [lia|].
        eapply (KONT Fb _ x14 x15 x16 x17 x18 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13);
          [ | reflexivity | reflexivity | reflexivity | exact MI' | exact ST'
            | eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb] | exact F0 | rewrite FSZ; exact LJ
            | rewrite FSZ; unfold fflagA_real; rewrite CLS; exact FRC
            | rewrite FSZ; replace (Z.shiftr Fb 3 + 2147450880) with (shad Fb) by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia); exact SHC ].
        (* [comment removed for export] *)
        split.
        { eapply (AI_perm AI); [| exact AH']. unfold LBof. cbn [map]. unfold fkb_of at 2. cbn [fb_fn fb_addr fb_size fst snd]. rewrite CLS, FSZ. apply Permutation.Permutation_middle. }
        cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
        split; [exact RV|]. split; [exact AD|]. split; [cbn [map fb_fn fb_addr fst snd]; rewrite EF; reflexivity|].
        split; [apply Forall_cons; [reflexivity| exact SZ]|]. split; [cbn [map fb_fn fst snd]; apply List.NoDup_cons; assumption|].
        eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="AF GS_pres"] Theorem fret_real : fret_inline_law FOA GIOA fflagA_real.
  Proof.
    red. intros L RNG s CL FB FL f Fb m m' A x Q ms G CLS MU WM FLC KONT.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    assert (PM : Permutation.Permutation (LBof CL FB ((f, Fb, ff_size f) :: FL)) (FKB (ff_class f) Fb (ff_size f) :: LBof CL FB FL))
      by (unfold LBof; cbn [map]; unfold fkb_of at 1; cbn [fb_fn fb_addr fb_size fst snd]; symmetry; apply Permutation.Permutation_middle).
    pose proof (AI_perm AI _ _ _ _ _ _ PM AH) as AH1. atop_facts.
    assert (SPZ : ATOP <= ATOP + 4096) by (clear; lia).
    destruct (AF_release _ AF _ _ _ _ _ _ _ _ _ (ATOP + 4096) AH1 SPZ MU WM FLC) as [AH2 HP].
    unfold implMG. apply implS_fo_ret0. cbn [fst snd]. apply KONT; [| reflexivity | reflexivity | reflexivity].
    split; [exact AH2|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
    split; [exact RV|]. split; [exact AD|]. split; [rewrite EF; reflexivity|].
    split; [exact (Forall_inv_tail SZ)|]. split; [cbn [map] in ND; apply List.NoDup_cons_iff in ND as [_ ND']; exact ND'|].
    eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="AF GS_pres"] Theorem fenter7_real : fenter7_stmt_o FOA GIOA fflagA_real.
  Proof.
    red. intros until Q. intros PRE -> REQ REQ8 NIN CLS KONT.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). unfold FAKE_STACK in BU.
    assert (FSZ : ff_size f = 8192) by (unfold ff_size; rewrite CLS; reflexivity).
    eapply implMG_evtF.
    - change STACK_MALLOC_7 with ASTKMALLOC7.
      eapply (AF_sm7 _ AF L RNG req ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 req) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo);
        [ exact AH
        | pose proof (fk_count_LBof 7 CL FB FL) as C1; pose proof (frames_le9 FL ND) as C2; replace (fk_nframes 7) with 128 by reflexivity; lia
        | reflexivity | lia | exact REQ8
        | exact MI | exact ST | exact LO | unfold SM_STACK; lia | lia | exact TPE | exact RSTK | exact RIMG | exact RTLS | exact (AF_rng _ AF _ _ _ _ _ AH) ].
    - cbv beta. intros ms' PO. destruct_exs PO.
      destruct PO as (-> & MI' & ST' & HP & AH' & F64 & F0 & FBAND & FTOP & LJ & FRC & LSJ & SHC).
      rename x into Fb. pose proof (ablk_lin _ _ FBAND) as (_ & _ & _ & FT47).
      assert (EA : a0_of (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 Fb) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = Fb)
        by (unfold a0_of; etransitivity; [| apply (unsigned_lit Fb); lia]; reflexivity).
      unfold implMG. eapply implS_fo_enter0; rewrite EA; [lia|].
      eapply (KONT Fb _ x14 x15 x16 x17 x18 x19 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13);
        [ | reflexivity | reflexivity | reflexivity | exact MI' | exact ST'
          | eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb] | exact F0 | rewrite FSZ; exact LJ | rewrite FSZ; exact LSJ
          | rewrite FSZ; unfold fflagA_real; rewrite CLS; exact FRC
          | rewrite FSZ; replace (Z.shiftr Fb 3 + 2147450880) with (shad Fb) by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia); exact SHC ].
      split.
      { eapply (AI_perm AI); [| exact AH']. unfold LBof. cbn [map]. unfold fkb_of at 2. cbn [fb_fn fb_addr fb_size fst snd]. rewrite CLS, FSZ. apply Permutation.Permutation_middle. }
      cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
      split; [exact RV|]. split; [exact AD|]. split; [cbn [map fb_fn fb_addr fst snd]; rewrite EF; reflexivity|].
      split; [apply Forall_cons; [reflexivity| exact SZ]|]. split; [cbn [map fb_fn fst snd]; apply List.NoDup_cons; assumption|].
      eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.

  #[using="AF GS_pres"] Theorem ffree7_real : ffree7_stmt_o FOA GIOA fflagA_real.
  Proof.
    red. intros until Q. intros PRE CLS -> -> REQ REQ8 LAST KONT.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). unfold FAKE_STACK in BU.
    assert (FSZ : ff_size f = 8192) by (unfold ff_size; rewrite CLS; reflexivity). rewrite FSZ in *.
    assert (PM : Permutation.Permutation (LBof CL FB ((f, Fb, 8192) :: FL)) (FKB 7 Fb 8192 :: LBof CL FB FL))
      by (unfold LBof; cbn [map]; unfold fkb_of at 1; cbn [fb_fn fb_addr fb_size fst snd]; rewrite CLS; symmetry; apply Permutation.Permutation_middle).
    pose proof (AI_perm AI _ _ _ _ _ _ PM AH) as AH1.
    eapply implMG_evtF.
    - change STACK_FREE_7 with ASTKFREE7.
      eapply (AF_sf7 _ AF L RNG req ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fb) (Z_to_bv 64 req) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo Fb);
        [ exact AH1 | reflexivity | reflexivity | lia | exact REQ8
        | unfold fflagA_real in LAST; rewrite CLS in LAST; replace (Fb + 8184) with (Fb + 8192 - 8) by lia; exact LAST
        | exact MI | exact ST | exact LO | unfold SM_STACK; lia | lia | exact RSTK | exact RIMG | exact RTLS | exact (AF_rng _ AF _ _ _ _ _ AH) ].
    - cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MI' & ST' & HP & AH').
      unfold implMG. apply implS_fo_ret0. cbn [fst snd].
      eapply KONT; [ | reflexivity | reflexivity | reflexivity | exact MI' | exact ST'
                     | eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb] ].
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_frames].
      split; [exact RV|]. split; [exact AD|]. split; [rewrite EF; reflexivity|].
      split; [exact (Forall_inv_tail SZ)|]. split; [cbn [map] in ND; apply List.NoDup_cons_iff in ND as [_ ND']; exact ND'|].
      eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| lia| reflexivity| reflexivity| reflexivity].
  Qed.
End GioaFake.
End CANSEC1.
End TwB.
End GioaFake.

(* [comment removed for export] *)
Module F_pcap_openA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AccFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac acc_hint ::= acc_hint_cheap.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Open.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis CPC : (~ (ACLIENT_LO <= tp_cpc TP < ACLIENT_HI))%Z.
  Hypothesis CALLOC : calloc_stmt_o HO GIOA TP.

  Definition open_offline_common_proofA__stmt : Prop := open_offline_common_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo EB total ej : ltac2:(SecDiet.SzSec.tyM 'open_offline_common_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma open_offline_common_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_common_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CALLOC CPC GL.
    intros PRE UC TR NF -> -> -> Htot HEB CR E8.
 destruct TR as (UTR & _). destruct CR as (CR & EBO).
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    unfold PCAP_L1B_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    assert (TOT : 0 <= total < 2^32) by (unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia).
    assert (BLW : forall a, in_block CL a -> 0 < a < ATOP).
    { intros a Ha. apply (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G). apply in_block_app. left. exact Ha. }
    unfold Pcap.pcapint_open_offline_common, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_calloc e_last_errno prims]. unfold PCAP_OPEN_OFFLINE_COMMON_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    hide HEB.
    ienterG. carve_frame 32%nat ST. do 13 zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIOA L RNG s CL FB FL mm)
        by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|[Ha|[Ha|Ha]]] Hn]; cbn [outside]; [lia| | |];
            [pose proof (BLW a Ha); lia | pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha); lia
            | pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha); lia]);
      unhide HEB; assert (HEB1 : rw_cells asegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB |];
            intros a Ha; cbn [outside cells_size csize Nat.add] in *;
            pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G CR) as (ELO & EHI); lia)
    end.
    clear MU WM HEB.
    name_sp sp (-32)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply CALLOC; [| reflexivity | reflexivity | lia | lia | unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia |].
      - split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - eapply unw_of_ucaller; [eapply (ucaller_data 0%nat _ _ _ _ _ 0x85d04%Z); [rewrite Hsp; unfold PCAP_PRIV_OFF; rewrite unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                               | exact CPC | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR | exact RSTK]. }
    intros [q|] s' RNG1 ms' PO; cbv beta iota in PO; [| destruct PO as (_ & av & m2 & _ & _ & _ & _ & _ & []) ].
    destruct PO as (FP1 & av & m2 & E & OF1 & MI1 & ST1 & AG1 & (A & -> & G1 & NEW)).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    rewrite Z.mul_1_r in G1, NEW.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(left; reflexivity)) as ((ABAND & A3 & ATOPb & A2) & A1 & AUNP & ARNG & ARSH & AAR).
    cbn [cb_addr cb_size fst snd] in ABAND, A3, ATOPb, A2, A1, AUNP, ARNG, ARSH, AAR. band_ind ABAND bA.
    replace (ret_pc (Z_to_bv 64 548100)) with (Z_to_bv 64 548100) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      eapply clocA_keeps; [exact CR| lia]. }
    clear HEB1.
    assert (NB : forall a, in_block CL a -> ~ (A <= a < A + total)).
    { intros a Ha Hin. apply in_block_In in Ha as (b & Hb & Hr).
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G1) as BA. cbn [app blocks_apart] in BA. destruct BA as [BA _].
      pose proof (proj1 (Forall_forall _ _) BA b ltac:(apply in_or_app; left; exact Hb)) as Ap.
      unfold apart in Ap. cbn [cb_addr cb_size fst snd] in Ap. lia. }
    assert (NF2 : forall a, in_frames FL a -> ~ (A <= a < A + total)).
    { intros a Ha Hin. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G1 Ha). apply in_block_app. left. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Hin. }
    pose proof (munch_refl [(A, A + 200)]%Z m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    unfold PCAP_PRIV_OFF. apply implMG_ret. hide HEB2.
    destruct Htot as [-> | ->]; unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in *.
    all: lazymatch type of NEW with context [Z.to_nat ?z] => let n := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with n in NEW end.
    all: zstep; if_false_by (eqz_false A ltac:(lia)).
    all: zstep.                       (* [comment removed for export] *)
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 3 zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 2 zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 2 zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 3 zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 7 zstep.
    all: lazymatch type of NEW with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] =>
           pose proof (rw_cells_merge asegs mm AA [c0; c1; c2; c3] [c4; c5; c6] [c7; c8; c9; c10] NEW) as NEW2;
           cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW2 end.
    all: lazymatch type of NEW2 with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
           pose proof (rw_cells_merge asegs mm AA [c0; c1; c2; c3; c4; c5] [c6; c7; c8] [] NEW2) as NEW3;
           cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW3 end.
    all: clear NEW NEW2.
    all: release_frame FR ST1 (bv_unsigned sp).
    all: apply evtF_done; subst POSTQ; unfold open_common_post.
    all: split; [exact FP1|].
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 A), mm end.
    all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    all: split; [solve [assumption | congruence] |].
    all: split; [assumption|]; split; [assumption|].
    all: split; [eapply agrees_on_trans; [exact AGa|]; eapply agrees_on_trans;
                  [eapply agrees_on_weaken; [exact AG1|]; intros a [[Ha|[Ha|[Ha|Ha]]] Hn];
                     [left; lia| right; left; exact Ha| right; right; left; exact Ha| right; right; right; exact Ha]
                  |eapply agrees_on_of_munch; [exact MU2 | exact WM2|]; intros a _ [[Ha|[Ha|[Ha|Ha]]] Hn]; cbn [outside]; [lia| | |];
                   (split; [|exact I]; intros Hin;
                    first [apply (NB a Ha); lia | apply (NF2 a Ha); lia | pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G1 Ha); lia])]|].
    all: exists A; split; [reflexivity|].
    all: split; [eapply (gl_client_frame _ _ _ GL); [exact G1 | exact MU2 | exact WM2|];
                 apply Forall_cons; [right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]|].
    all: unhide HEB2.
    all: split; [| eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU2| exact WM2| intros a _ Ho; exact Ho] | exact HEB2 |];
                  intros a Ha; cbn [outside cells_size csize Nat.add] in *; split; [|exact I];
                  destruct CR as [(b0 & Hb0 & Hb1 & Hb2)|(fr0 & Hf0 & Hf1 & Hf2)];
                  [intros Hin; apply (NB a ltac:(apply in_block_In; exists b0; split; [exact Hb0| lia])); lia
                  |intros Hin; apply (NF2 a ltac:(apply in_frames_In; exists fr0; split; [exact Hf0| lia])); lia]].
    all: assumption.
  Qed.
  End Sz1.
  Theorem open_offline_common_proofA : ltac:(let t := eval cbv delta [open_offline_common_proofA__stmt] in open_offline_common_proofA__stmt in exact t).
  Proof using CALLOC CPC GL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo EB total ej. ltac2:(SecDiet.SzSec.closeP 'open_offline_common_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Open.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB UnwLowerB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UnwLowerB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac acc_hint ::= acc_hint_cheap.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Open.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis CPC : (~ (ACLIENT_LO <= tp_cpc TP < ACLIENT_HI))%Z.
  Hypothesis CALLOC : calloc_stmt_o HO GIOA TP.

  Definition open_offline_common_proofA__stmt : Prop := open_offline_common_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo EB total ej : ltac2:(SecDiet.SzSec.tyM 'open_offline_common_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma open_offline_common_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_common_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CALLOC CPC GL.
 intros PRE UC TR NF S0HI -> -> -> Htot HEB CR E8. destruct TR as (UTR & _). destruct CR as (CR & EBO).
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    unfold PCAP_L1B_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    assert (TOT : 0 <= total < 2^32) by (unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia).
    assert (BLW : forall a, in_block CL a -> 0 < a < ATOP).
    { intros a Ha. apply (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G). apply in_block_app. left. exact Ha. }
    unfold Pcap.pcapint_open_offline_common, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_calloc e_last_errno prims]. unfold PCAP_OPEN_OFFLINE_COMMON_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    hide HEB.
    ienterG. carve_frame 48%nat ST. do 14 zstep.        (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIOA L RNG s CL FB FL mm)
        by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|[Ha|[Ha|Ha]]] Hn]; cbn [outside]; [lia| | |];
            [pose proof (BLW a Ha); lia | pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha); lia
            | pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha); lia]);
      (* [comment removed for export] *)
      assert (UCm : ucallerA depth_open_offline_common L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC | lia |]; intros a Ha;
            assert (AGU : agrees_on (fun a0 => bv_unsigned sp <= a0)%Z m mm)
              by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a0 _ Ha0; cbn [outside fst snd]; split; [lia | exact I]);
            exact (proj1 (AGU a ltac:(lia) (proj1 Ha))));
      unhide HEB; assert (HEB1 : rw_cells asegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB |];
            intros a Ha; cbn [outside cells_size csize Nat.add] in *;
            pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G CR) as (ELO & EHI); lia)
    end.
    clear MU WM HEB.
    name_sp sp (-48)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply CALLOC; [| reflexivity | reflexivity | lia | lia | unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia |].
      - split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - eapply unw_of_ucaller; [eapply (ucaller_lower _ _ _ _ _ _ _ _ _ 0x85e68%Z); [exact UCm | rewrite Hsp; lia | exact S0HI | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia]
                               | exact CPC | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR | exact RSTK]. }
    intros [q|] s' RNG1 ms' PO; cbv beta iota in PO; [| destruct PO as (_ & av & m2 & _ & _ & _ & _ & _ & []) ].
    destruct PO as (FP1 & av & m2 & E & OF1 & MI1 & ST1 & AG1 & (A & -> & G1 & NEW)).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    rewrite Z.mul_1_r in G1, NEW.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(left; reflexivity)) as ((ABAND & A3 & ATOPb & A2) & A1 & AUNP & ARNG & ARSH & AAR).
    cbn [cb_addr cb_size fst snd] in ABAND, A3, ATOPb, A2, A1, AUNP, ARNG, ARSH, AAR. band_ind ABAND bA.
    replace (ret_pc (Z_to_bv 64 548456)) with (Z_to_bv 64 548456) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      eapply clocA_keeps; [exact CR| lia]. }
    clear HEB1.
    assert (NB : forall a, in_block CL a -> ~ (A <= a < A + total)).
    { intros a Ha Hin. apply in_block_In in Ha as (b & Hb & Hr).
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G1) as BA. cbn [app blocks_apart] in BA. destruct BA as [BA _].
      pose proof (proj1 (Forall_forall _ _) BA b ltac:(apply in_or_app; left; exact Hb)) as Ap.
      unfold apart in Ap. cbn [cb_addr cb_size fst snd] in Ap. lia. }
    assert (NF2 : forall a, in_frames FL a -> ~ (A <= a < A + total)).
    { intros a Ha Hin. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G1 Ha). apply in_block_app. left. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Hin. }
    pose proof (munch_refl [(A, A + 200)]%Z m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    unfold PCAP_PRIV_OFF. apply implMG_ret. hide HEB2.
    destruct Htot as [-> | ->]; unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in *.
    all: lazymatch type of NEW with context [Z.to_nat ?z] => let n := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with n in NEW end.
    all: do 2 zstep; if_false_by (eqz_false A ltac:(lia)).
    all: zstep; ub_al 7%Z ltac:(al16 A2).      (* [comment removed for export] *)
    all: zstep; if_false.
    all: zstep.                       (* [comment removed for export] *)
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 3 zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 2 zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 3 zstep.                  (* [comment removed for export] *)
    all: ub_not; ub_ltu.
    all: zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 3 zstep.
    all: ck0 AUNP; ck_go.             (* [comment removed for export] *)
    all: do 10 zstep.                 (* [comment removed for export] *)
    all: lazymatch type of NEW with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] =>
           pose proof (rw_cells_merge asegs mm AA [c0; c1; c2; c3] [c4; c5; c6] [c7; c8; c9; c10] NEW) as NEW2;
           cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW2 end.
    all: lazymatch type of NEW2 with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
           pose proof (rw_cells_merge asegs mm AA [c0; c1; c2; c3; c4; c5] [c6; c7; c8] [] NEW2) as NEW3;
           cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW3 end.
    all: clear NEW NEW2.
    all: release_frame FR ST1 (bv_unsigned sp).
    all: apply evtF_done; subst POSTQ; unfold open_common_post.
    all: split; [exact FP1|].
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 A), mm end.
    all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    all: split; [solve [assumption | congruence] |].
    all: split; [assumption|]; split; [assumption|].
    all: split; [eapply agrees_on_trans; [exact AGa|]; eapply agrees_on_trans;
                  [eapply agrees_on_weaken; [exact AG1|]; intros a [[Ha|[Ha|[Ha|Ha]]] Hn];
                     [left; lia| right; left; exact Ha| right; right; left; exact Ha| right; right; right; exact Ha]
                  |eapply agrees_on_of_munch; [exact MU2 | exact WM2|]; intros a _ [[Ha|[Ha|[Ha|Ha]]] Hn]; cbn [outside]; [lia| | |];
                   (split; [|exact I]; intros Hin;
                    first [apply (NB a Ha); lia | apply (NF2 a Ha); lia | pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G1 Ha); lia])]|].
    all: exists A; split; [reflexivity|].
    all: split; [eapply (gl_client_frame _ _ _ GL); [exact G1 | exact MU2 | exact WM2|];
                 apply Forall_cons; [right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]|].
    all: unhide HEB2.
    all: split; [| eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU2| exact WM2| intros a _ Ho; exact Ho] | exact HEB2 |];
                  intros a Ha; cbn [outside cells_size csize Nat.add] in *; split; [|exact I];
                  destruct CR as [(b0 & Hb0 & Hb1 & Hb2)|(fr0 & Hf0 & Hf1 & Hf2)];
                  [intros Hin; apply (NB a ltac:(apply in_block_In; exists b0; split; [exact Hb0| lia])); lia
                  |intros Hin; apply (NF2 a ltac:(apply in_frames_In; exists fr0; split; [exact Hf0| lia])); lia]].
    all: assumption.
  Qed.
  End Sz1.
  Theorem open_offline_common_proofA : ltac:(let t := eval cbv delta [open_offline_common_proofA__stmt] in open_offline_common_proofA__stmt in exact t).
  Proof using CALLOC CPC GL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo EB total ej. ltac2:(SecDiet.SzSec.closeP 'open_offline_common_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Open.
End CANSEC1.
End TwB.
End F_pcap_openA.
