(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB AiAuxB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AccFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiEA_disp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_aiEA_body.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac msg_ok := vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]].
(* [comment removed for export] *)
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AccFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= plia.
Local Ltac flia ::= first [ sassumption | plia | assumption ].
Local Ltac acc_hint ::= acc_hint_cheap.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  Hypothesis UTS : (0 < ng_user_tsresol s < 2^64)%Z.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis P2 : (P mod 16 = 0)%Z.
  Hypothesis B2 : (B mod 16 = 0)%Z.
  Hypothesis IDB0 : (0 <= idb_off)%Z.
  Hypothesis IDB4 : (idb_off mod 4 = 0)%Z.
  Hypothesis COFF : (cur_off c = idb_off + 8)%Z.
  Hypothesis CREM : (0 <= cur_remaining c)%Z.
  Hypothesis CEND : (cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)))%Z.
  Hypothesis CBT : (0 <= cur_block_type c < 2^32)%Z.
  Hypothesis CUR8 : (CUR mod 8 = 0)%Z.
  Hypothesis APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z.
  Hypothesis EBP2 : (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z.
  Hypothesis HPV : rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].

  #[local] Abbreviation ai_snap := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap idb_off p).
  #[local] Abbreviation ai_slot0 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot0 idb_off p).
  #[local] Abbreviation ai_result := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c).

  (* [comment removed for export] *)
  Variables (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte).
  Hypothesis FP3 : fp_le RNG RNG3.
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap < 2^32)%Z.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Variable hj0 : list byte.
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd P EB hj0).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  #[local] Abbreviation pio_body := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
  #[local] Abbreviation pio_value := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value.
  #[local] Abbreviation le8val := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val.

  Section Sz7.
  Variables fuel a3' a5' x25 io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4 : ltac2:(SecDiet.SzSec.tyM 'ai_body__stmt "vhvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ai_body__gen : loop_facts__stmt -> ai_disp__stmt -> ltac2:(SecDiet.SzSec.bodyP 'ai_body__stmt "vhvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel a3' a5' x25 io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4.
    intros loop_facts ai_disp LK.
 intros IV FUEL GE4 SW Ebuf Lpre Ebs PFXr c0 c1 l0 l1 code olen MI4 MU WM CC4 HOPT4.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & OFF4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    set (padded := ((olen + 3) / 4 * 4)%Z).
    assert (LBS : length bs3 = Z.to_nat (pc_bufalloc p)) by (destruct BUF3 as [[WF _] _]; cbn in WF; lia).
    assert (OFF0 : (8 <= cur_off c')%Z) by lia.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf'))%Z) by lia.
    assert (Lpost : (Z.of_nat (length post) = Z.of_nat (length buf') - cur_off c' - 4)%Z) by (subst buf'; rewrite length_app in *; cbn [length] in *; lia).
    assert (GRh : (0 <= u0 < 256 /\ 0 <= u1 < 256 /\ 0 <= u2 < 256 /\ 0 <= u3 < 256)%Z /\ Forall (fun z => 0 <= z < 256)%Z pre /\ Forall (fun z => 0 <= z < 256)%Z post).
    { subst buf'. apply Forall_app in GR3 as [GA GB]. inversion GB as [|x0 l0' B0 GB1]; subst. inversion GB1 as [|x1 l1' B1x GB2]; subst.
      inversion GB2 as [|x2 l2' B2x GB3]; subst. inversion GB3 as [|x3 l3' B3 GB4]; subst. repeat split; try assumption; lia. }
    destruct GRh as ((B0 & B1x & B2x & B3) & GRpre & GRpost).
    assert (HC : (0 <= c0 < 256 /\ 0 <= c1 < 256 /\ 0 <= l0 < 256 /\ 0 <= l1 < 256)%Z) by (subst c0 c1 l0 l1; destruct sw; lia).
    destruct HC as (HC0 & HC1 & HL0 & HL1).
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; lia).
    set (buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post) in *.
    assert (LB5 : length buf5 = length buf') by (subst buf5 buf'; rewrite !length_app; reflexivity).
    remember (B + cur_off c')%Z as D eqn:HDd.
    (* [comment removed for export] *)
    assert (G4 : GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m4).
    { eapply (gl_client_frame _ _ _ GL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [| apply Forall_nil].
      right; left. unfold iv_in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_buffer p, B, pc_bufalloc p). split; [exact HinB|]. cbn [cb_addr cb_size fst snd]. lia. }
    assert (HinB4 : In (pc_buffer p, B, pc_bufalloc p) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 HinB4) as ((BBAND & B3x & BTOP & _) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in BBAND, B3x, BTOP, B1, BUNP, BRNG, BRSH.
    band_ind BBAND bB.
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3.
    destruct (gia_stack_sobjA FO GIOA fflagA GL _ _ _ _ _ _ _ lo (bv_unsigned sp) CUR 24 G4 LO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RSTK3) as (_ & _ & CUNP & CRNG & CRSH).
    replace (CUR - CUR mod 8)%Z with CUR in CRSH by lia. replace (24 + CUR mod 8)%Z with 24%Z in CRSH by lia.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    assert (DM4 : (D mod 4 = 0)%Z) by (subst D; clear - B2 OFF4; Z.div_mod_to_equations; lia).
    assert (INB : (B <= D /\ D + 4 <= B + pc_bufalloc p)%Z) by lia.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd in HD3. unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide CC3. hide HEB3.
    pose proof (munch_refl [(CUR, CUR + 16)]%Z m4) as MU45. pose proof (wmono_refl asegs m4) as WM45.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS.
    eapply evtF_cut.
    { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB.opt_lenA RNG3) with (code := code) (olen := olen) (Bq := B) (alloc := pc_bufalloc p) (bB := bB) (D := D);
        [exact HCODE | exact HOLEN | exact HOPT4 | exact MI4 | exact BUNP | lia | lia | exact DM4 | lia | exact B2 | lia | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
    cbv beta. intros ms' ->.
    fold padded.
    zstep.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type]. fold padded.
    destruct (Z.le_gt_cases padded (cur_remaining c' - 4)) as [FIT|NOFIT].
    2:{ (* [comment removed for export] *)
      replace (bv_ltu (Z_to_bv 64 (cur_remaining c' - 4)) (Z_to_bv 64 padded)) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota.
      rewrite (proj2 (Z.ltb_lt (cur_remaining c' - 4) padded)) by lia. cbv beta iota. rewrite ai_result_inl.
      zstep. ck0 CUNP; ck_go.
      zstep.
      rewrite (sx32_s32 (cur_block_type c')) by lia.
      do 3 zstep.
      destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m4 c0 c1 l0 l1 D _ ltac:(subst buf' bs3; exact IV) GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI4 MU WM ltac:(subst code olen; exact HOPT4) CC4 eq_refl)
        as (ST4 & AG4 & HD4 & FR4 & NG4 & AR14 & SL4 & AR24 & _ & BUF4 & PFX4 & LB4 & GR4 & _ & HEB4 & _ & RESTF4).
      assert (MSG : fmt_at m4 0x22520 "block of type %u in pcapng dump file is too short"%string) by (fmt_at_tac MI4 0x22520%Z "block of type %u in pcapng dump file is too short"%string).
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd in HD4.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_snp_b with (m3 := m4) (args := [AInt (s32 (cur_block_type c'))]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
        [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
        | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
        | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs;
          replace (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
          apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil]
        | vm_compute; reflexivity | apply args_ok_ints1 ]. }
    replace (bv_ltu (Z_to_bv 64 (cur_remaining c' - 4)) (Z_to_bv 64 padded)) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota.
    rewrite (proj2 (Z.ltb_ge (cur_remaining c' - 4) padded)) by lia. cbv beta iota.
    zstep. ub_not. zstep. ub_ltu.            (* [comment removed for export] *)
    ck0_at CUNP CUR; ck_go.
    zstep. zstep.
    ck0_at CUNP (CUR + 8)%Z; ck_go.
    zstep. zstep.
  eapply evtF_cut.
  { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB.opt_codeA RNG3) with (code := code) (olen := olen) (Bq := B) (alloc := pc_bufalloc p) (bB := bB) (D := D);
      [exact HCODE | exact HOLEN | exact HOPT4 | exact MI4 | exact BUNP | lia | lia | exact DM4 | lia | exact B2 | lia | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
  cbv beta. intros ms' (s0v & ->).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
    (* [comment removed for export] *)
    subst bs3. subst buf'.
    destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D _ IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI4 MU WM ltac:(subst code olen; exact HOPT4) CC4 eq_refl)
      as (ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5' & GR5' & _ & HEB5 & HB2 & RESTF5).
    set (bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr) in *.
    set (c2 := mkCursor (cur_off c' + 4 + padded) (cur_remaining c' - 4 - padded) (cur_block_type c')).
    assert (AIM5 : forall io', (0 < io_tsresol io' < 2^64)%Z -> AIM io' c2 buf5 m5 bs5 cpad3).
    { intros io' TS'. split; [exact TS'|]. split; [exact MI4|]. split; [exact ST5|]. split; [exact AG5|]. split; [exact HD5|]. split; [exact FR5|].
      split; [exact NG5|]. split; [exact AR15|]. split; [exact SL5|]. split; [exact AR25|]. split; [exact G5|]. split; [exact BUF5|]. split; [exact PFX5|].
      split; [exact LB5'|]. split; [exact GR5'|]. split; [unfold cursor_cells; subst c2 D; cbn [cur_off cur_remaining cur_block_type]; replace (B + cur_off c' + 4 + padded)%Z with (B + (cur_off c' + 4 + padded))%Z in CC4 by lia; exact CC4|].
      subst c2; cbn [cur_off cur_remaining cur_block_type]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CR4|]. split; [exact HEB5|]. clear - OFF4 HPAD. Z.div_mod_to_equations. lia. }
    fold c2.
    assert (LEN5 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf5))%Z) by (rewrite LB5; exact LEN4).
    eapply (ai_disp fuel LK _ _ _ io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D AIM5 TSR SW FUEL GE4 FIT OFF0 OFF4 LEN5 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2).
  Qed.
  End Sz7.
  End AIX.
  End CANSEC1.
End F_aiEA_body.

(* [comment removed for export] *)
Module F_aiEA_loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac msg_ok := vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]].
(* [comment removed for export] *)
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiEA_disp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  Hypothesis UTS : (0 < ng_user_tsresol s < 2^64)%Z.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis P2 : (P mod 16 = 0)%Z.
  Hypothesis B2 : (B mod 16 = 0)%Z.
  Hypothesis IDB0 : (0 <= idb_off)%Z.
  Hypothesis IDB4 : (idb_off mod 4 = 0)%Z.
  Hypothesis COFF : (cur_off c = idb_off + 8)%Z.
  Hypothesis CREM : (0 <= cur_remaining c)%Z.
  Hypothesis CEND : (cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)))%Z.
  Hypothesis CBT : (0 <= cur_block_type c < 2^32)%Z.
  Hypothesis CUR8 : (CUR mod 8 = 0)%Z.
  Hypothesis APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z.
  Hypothesis EBP2 : (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z.
  Hypothesis HPV : rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].

  #[local] Abbreviation ai_snap := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap idb_off p).
  #[local] Abbreviation ai_slot0 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot0 idb_off p).
  #[local] Abbreviation ai_result := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c).

  (* [comment removed for export] *)
  Variables (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte).
  Hypothesis FP3 : fp_le RNG RNG3.
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap < 2^32)%Z.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Variable hj0 : list byte.
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd P EB hj0).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  Section Sz7.
  Variables fuel a3' a5' x25 io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4 : ltac2:(SecDiet.SzSec.tyM 'ai_body__stmt "vhvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ai_body__body : ltac2:(SecDiet.SzSec.bodyP 'ai_body__stmt "vhvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel a3' a5' x25 io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4. exact (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiEA_body__B3P.F_aiEA_body.ai_body__gen rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel a3' a5' x25 io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4 (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA_facts.loop_facts rc tlsI H hptr FO GIOA fflagA GL ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej LO BU GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG hj0) (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiEA_disp.ai_disp rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0)). Qed.
  End Sz7.
  #[using="rc tlsI FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_body : ltac:(let t := eval hnf in ai_body__stmt in exact t).
  Proof. intros fuel LK a3' a5' x25 io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4. ltac2:(SecDiet.SzSec.closeP 'ai_body__body "vhvvvvvvvvvvvvvvvvvv"). Qed.

  Section Sz9.
  Variables fuel t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3 : ltac2:(SecDiet.SzSec.tyM 'ai_iter__stmt "vhvvvvvvvvvvvvvv" @fuel).
  Lemma ai_iter__body : ltac2:(SecDiet.SzSec.bodyP 'ai_iter__stmt "vhvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3. exact (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA_iter.ai_iter__gen rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3 ai_body). Qed.
  End Sz9.
  #[using="rc tlsI FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_iter : ltac:(let t := eval hnf in ai_iter__stmt in exact t).
  Proof. intros fuel LK t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3. ltac2:(SecDiet.SzSec.closeP 'ai_iter__body "vhvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Theorem ai_loop : forall fuel, LOOPK fuel.
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0. induction fuel as [|fuel IH]; [apply ai_loop0 | apply ai_loop_step, ai_iter, IH]. Qed.
  End AIX.
  End CANSEC1.
End F_aiEA_loop.

(* [comment removed for export] *)
Module F_ngnSA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnS0A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac apA lem := eapply lem; try eassumption.
(* [comment removed for export] *)
Ltac exit_sides FIN :=
  lazymatch goal with
  | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FIN
  | |- is_ng _ = true => reflexivity
  | |- cells_size _ = _ => reflexivity
  | |- length (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes _) = _ => rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes_length; reflexivity
  | |- In _ client_globals => unfold client_globals; repeat (first [left; reflexivity | right])
  | |- fmt_ok _ _ = true => reflexivity
  | |- (length _ <= _)%nat => cbn; lia
  | |- Forall2 _ _ _ => cbn [length firstn]; repeat (constructor; [reflexivity|]); constructor
  | |- _ => lia
  end.
Ltac name_field data off a b c d DRNG :=
  set (a := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0%Z) in *; set (b := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1%Z) in *; set (c := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 2%Z) in *; set (d := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 3%Z) in *;
  let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
  fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

(* [comment removed for export] *)
Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Section Sz1.
Variables data bs k off : ltac2:(SecDiet.SzSec.tyM 'firstn2_q8__stmt "vvvv" @data).
#[using="Type"] Lemma firstn2_q8__body : ltac2:(SecDiet.SzSec.bodyP 'firstn2_q8__stmt "vvvv").
Proof.
  intros PFX Hk H1.
 subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.
End Sz1.
Lemma firstn2_q8 : ltac:(let t := eval cbv delta [firstn2_q8__stmt] in firstn2_q8__stmt in exact t).
Proof. intros data bs k off. ltac2:(SecDiet.SzSec.closeP 'firstn2_q8__body "vvvv"). Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HALO : (0x604000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x604000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis HLOC : clocA FL CLc HA 24.
  Hypothesis DLOC : clocA FL CLc DA 8.
  Variable trC : list Z.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (A3P.F_ngnEA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_shbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_shbK H hptr).
  #[local] Abbreviation ngn_headA := (A3P.F_ngnEA.TwB.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  #[using="rc sp"] Lemma fmt_too_short : forall mx, mem_inv asegs mx -> fmt_at mx NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string.
  Proof.
    intros mx MIx. unfold NGN_FMT_TOO_SHORT_A.
    split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mx 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                             MIx ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
    split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]).
  Qed.

  Definition ng_reset (sx : pcap_ng_sf) : pcap_ng_sf := mkNg (ng_user_tsresol sx) (ng_max_blocksize sx) 0 (ng_ifaces_size sx) [].

  (* [comment removed for export] *)
  Definition PCAPR_reset__stmt : Prop := forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr)
                             (m6 m7 : mem) (Afx B I : Z) (j : pcap_junk) (pad bs : list byte),
    GIOA Lx RNGx ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6 ->
    In (f, Afx, FILE_BLOCK) FB ->
    pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix = pcap_blocks (pv bq alloc data eb sx ix) P B I ->
    rw_cells asegs m7 P (pcap_cells (pv bq alloc data eb sx ix) P B Afx j) ->
    rw_cells asegs m7 (P + 648) (ng_cells (ng_reset sx) I pad) ->
    rw_cells asegs m7 B [CB (Z.to_nat alloc) bs] -> firstn (length data) bs = map b8 data ->
    ifaces_ok (pv bq alloc data eb sx ix) I m6 ->
    agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m6 m7 ->
    pcap_wf (pv bq alloc data eb sx ix) ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7.
  Section Sz5.
  Variables Lx RNGx ps bq Bq Ix alloc data eb sx ix m6 m7 Afx B I j pad bs : ltac2:(SecDiet.SzSec.tyM 'PCAPR_reset__stmt "vvvvvvvvvvvvvvvvvvv" @Lx).
  #[using="rc tlsI FO fflagA GL sp lo LO BU"] Lemma PCAPR_reset__body : ltac2:(SecDiet.SzSec.bodyP 'PCAPR_reset__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G Hin EPB CELLS PRIV BUF PFX IFS AG WF.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G eq_refl) as [APB API].
    exists Afx. split; [exact Hin|]. exists B, I, j, pad, bs.
    split; [exact EPB|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [exact BUF|]. split; [exact PFX|].
    split.
    - unfold ifaces_ok in IFS |- *. unfold A3P.F_ngnEA.TwB.pv in IFS, API |- *. cbn [pc_priv] in IFS, API |- *. destruct ix as [q|].
      + destruct IFS as (js & tail & Ljs & CE & E1 & E2 & E3 & E4).
        rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail]), app_assoc in CE.
        apply (rw_cells_merge asegs m6 I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
        cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
        destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
        pose proof EPB as EPB'. unfold pcap_blocks, A3P.F_ngnEA.TwB.pv, psize, is_ng in EPB'. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB'.
        injection EPB' as EB EI.
        exists [], (cells_bytes (ifs_cells (rev (ng_ifaces sx)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail])).
        unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size length rev ifs_cells app Z.of_nat].
        split; [reflexivity|]. split.
        * replace (Z.to_nat (40 * (ng_ifaces_size sx - 0))) with (40 * length (ng_ifaces sx) + (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx)) + 0))%nat by lia.
          eapply agrees_rw_cells; [exact AG | exact CE |]. intros a Ha. cbn [cells_size csize Nat.add outside fst snd] in Ha |- *. clear - Ha X1 E1 E2 E3 EI. lia.
        * split; [reflexivity|]. split; [lia|]. split; [lia| apply Forall_nil].
      + unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size]. clear - IFS. tauto.
    - unfold pcap_wf, ng_reset, A3P.F_ngnEA.TwB.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv
           ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in WF |- *.
      clear - WF. lia.
  Qed.
  End Sz5.
  #[using="rc tlsI FO fflagA GL sp lo LO BU"] Lemma PCAPR_reset : ltac:(let t := eval cbv delta [PCAPR_reset__stmt] in PCAPR_reset__stmt in exact t).
  Proof. intros Lx RNGx ps bq Bq Ix alloc data eb sx ix m6 m7 Afx B I j pad bs. ltac2:(SecDiet.SzSec.closeP 'PCAPR_reset__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_shb_tail__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a2' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (ccs : list cell),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (16 <= rem)%Z ->
      ps_outfile ps = o ->
      implMG RNG5 (mbind (let bom := get_le32 data 8 in
                          if bom =? BYTE_ORDER_MAGIC then
                            let major := get_le16 data 12 in
                            if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) (pv bq alloc data eb sx ix))
                            else LOOP (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix))
                          else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order (pv bq alloc data eb sx ix))
                          else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic (pv bq alloc data eb sx ix))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 (Bq + 12)) a2' (Z_to_bv 64 (Z.shiftr (Bq + 8) 3)) a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 2) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d094) fc None m5 (seg_rom asegs)).
  Section Sz6.
  Variables LOOP ra' t0' t1' t2' a2' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix hcs dw ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_shb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  #[using="rc tlsI FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP trC TR"] Lemma ngn_shb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros HLOOP.
 intros FP5 ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold A3P.F_ngnEA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    unfold A3P.F_ngnEA.TwB.pv in Hin. cbn [pc_rfile] in Hin.
    unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 8) by lia. rewrite (get_le16_q8' data 12) by lia.
    name_field data 8%Z b0 b1 b2 b3 DRNG.
    set (k0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 0) in *. set (k1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 1) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 0 DRNG ltac:(lia)) as Rk0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 1 DRNG ltac:(lia)) as Rk1. fold k0 in Rk0. fold k1 in Rk1.
    pose proof BUF as BUF0.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
    fold b0 b1 b2 b3 k0 k1 in BUF.
    assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val b0 b1 b2 b3)); C2 (Z_to_bv 64 (k0 + 256 * k1)); CB (Z.to_nat alloc - 14) (firstn (Z.to_nat alloc - 14) (skipn 14 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit b0 b1 b2 b3), (le2_lit k0 k1) by lia. reflexivity. }
    clear BUF.
    pose proof PRIV as PRIVJ. unfold priv_cells, A3P.F_ngnEA.TwB.pv, PCAP_PRIV_OFF in PRIVJ. cbn [pc_priv] in PRIVJ. unfold ng_cells in PRIVJ.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxu_range' (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as SR. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as (_ & SX2 & SX3).
    hide FR5. hide CELLS. hide PRIV. hide IFS. hide HH. hide HD. hide BUF0.
    pose proof (munch_refl [(P + 660, P + 664)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    ck0_at BUNP (Bq + 8)%Z; ck_go.
    zstep.
    replace (sx32 (Z_to_bv 64 (le4val b0 b1 b2 b3))) with (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu (le4val b0 b1 b2 b3)))
      by (rewrite <- (Z_to_bv_bv_unsigned (sx32 _)), OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.unsigned_sx32' by (unfold le4val; lia); reflexivity).
    zstep.
  zstep. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
  - (* [comment removed for export] *)
    assert (NB : le4val b0 b1 b2 b3 <> 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | lia]).
    unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with false by (symmetry; apply Z.eqb_neq; exact NB). cbv iota.
    zstep. zstep.
    zstep. if_cases BR3; zify_cond BR3; rewrite ?unsigned_lit in BR3 by lia.
    + (* [comment removed for export] *)
      assert (NS : le4val b0 b1 b2 b3 <> 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | lia]).
      unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with false by (symmetry; apply Z.eqb_neq; exact NS). cbv iota.
      do 3 zstep.
      unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (SRC : bytes_at asegs m5 0x22b00 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has a section with a bad byte order magic field"))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22b00 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has a section with a bad byte order magic field") MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_mcp with (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs); try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
    + (* [comment removed for export] *)
      assert (ES : le4val b0 b1 b2 b3 = 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | specialize (SX3 ltac:(lia)); lia]).
      unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with true by (symmetry; apply Z.eqb_eq; exact ES). cbv iota.
      do 4 zstep.
      unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (SRC : bytes_at asegs m5 0x22aa0 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has sections with different byte orders"))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22aa0 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has sections with different byte orders") MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_mcp with (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs); try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
  - (* [comment removed for export] *)
    assert (EB : le4val b0 b1 b2 b3 = 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | specialize (SX3 ltac:(lia)); lia]).
    unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with true by (symmetry; apply Z.eqb_eq; exact EB). cbv iota. cbv zeta.
    ck0 BUNP; ck_go.
    zstep. rewrite (zx16_lit (k0 + 256 * k1)) by lia.
    zstep. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
    + (* [comment removed for export] *)
      replace (k0 + 256 * k1 =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      do 4 zstep.
      unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (MSG : fmt_at m5 0x22b60 "unknown pcapng savefile major version number %u"%string).
      { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22b60 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "unknown pcapng savefile major version number %u"%string) ++ [Z_to_bv 8 0])
                               MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_snp_b8 with (fs := "unknown pcapng savefile major version number %u"%string) (args := [AInt (k0 + 256 * k1)%Z]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
  + (* [comment removed for export] *)
    replace (k0 + 256 * k1 =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
    zstep. zstep. if_false.   (* [comment removed for export] *)
    ck0 PUNP; ck_go.
    zstep. zstep.
  assert (AGP : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m5 m0) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
  unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
  apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in CELLS; [| intros a Ha; rewrite pcap_cells_gen_size in Ha by reflexivity; cbn [outside fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in BUF0; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
  assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(P + 660, P + 664)]%Z).
  { apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, A3P.F_ngnEA.TwB.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
  assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m0) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
  assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m0).
  { eapply (PCAPR_reset _ _ ps bq Bq Ix alloc data eb sx ix m5 m0 Afx Bq Ix' jx' padx bsx');
      [exact G5 | exact Hin | exact EPB | exact CELLS | exact PRIVJ | exact BUF0 | exact PFX | exact IFS | exact AGP | exact WF]. }
  assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
  { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
    eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
    apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, A3P.F_ngnEA.TwB.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
  assert (G6' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB FL m0) by exact G6.
  assert (PC6' : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB m0) by exact PC6.
  apply evtF_done.
  change (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix)) with (pv bq alloc data eb (ng_reset sx) ix).
  unfold A3P.F_ngnEA.TwB.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
  eapply HLOOP; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | assumption | exact G6' | exact PC6' | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact OF5 | apply (A3P.F_ngnEA.TwB.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
  Qed.
  End Sz6.
  #[using="rc tlsI FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP trC TR"] Lemma ngn_shb_tail : ltac:(let t := eval cbv delta [ngn_shb_tail__stmt] in ngn_shb_tail__stmt in exact t).
  Proof. intros LOOP HLOOP ra' t0' t1' t2' a2' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix hcs dw ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_shb_tail__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition ngn_shb__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (ngn_shbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (s32 bt)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 2) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8ce54) fc None m5 (seg_rom asegs)).
  Section Sz7.
  Variables LOOP ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_shb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  #[using="rc tlsI FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC TR"] Lemma ngn_shb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros HLOOP.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_shbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA, A3P.F_ngnEA.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep.
    zstep.
  zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
  - (* [comment removed for export] *)
    replace (rem <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    do 6 zstep.
    unhide FR5. unhide HH. unhide HD. apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
    eapply ngn_snp_b8 with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 168627466]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix);
      try eassumption; [ reflexivity | | reflexivity | apply fmt_too_short; exact MI5 | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
    split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
    split; [exact HD|]. split; [exact Hd| exact OF5].
  - (* [comment removed for export] *)
    replace (rem <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold A3P.F_ngnEA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    name_field data 8%Z g0 g1 g2 g3 DRNG.
    set (j0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 0) in *. set (j1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 1) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 0 DRNG ltac:(lia)) as Rj0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 1 DRNG ltac:(lia)) as Rj1. fold j0 in Rj0. fold j1 in Rj1.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
    fold g0 g1 g2 g3 j0 j1 in BUF.
    replace (firstn (Z.to_nat alloc - 14) (skipn 14 bsx')) with (skipn 14 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
    assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3), (le2_lit j0 j1) by lia. reflexivity. }
    clear BUF.
    hide PRIV. hide IFS.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases G1; zify_cond G1. { exfalso. rewrite ?unsigned_lit in G1 by lia. lia. }
    zstep.
    zstep. if_cases G2; zify_cond G2. { exfalso. rewrite ?unsigned_lit in G2 by lia. lia. }
    do 4 zstep.
    assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z a) m5 m1) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
    apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, A3P.F_ngnEA.TwB.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside fst snd]; lia].
    assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m1) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m1).
    { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
    assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m1).
    { eapply ifaces_ok_agree; [exact AGF | | exact IFS]. intros sg q Hq a Ha. unfold A3P.F_ngnEA.TwB.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
      assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
        by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5e HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1. cbn [outside fst snd]. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m1).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
      eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
      apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
    clear MU WM AGF G5 PC5 AG5 IFS G5e.
    ck0_at PUNP (P + 56)%Z; ck_go.
    zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    do 3 zstep.
  assert (FR6 : rw_cells asegs m1 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 24)); C8 (Z_to_bv 64 (rem + -16)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
  assert (L7 : Z.land (Bq + 8) 7 = 0%Z) by (rewrite land7_mod; Z.div_mod_to_equations; lia). rewrite L7.
  zstep. if_cases BRS; zify_cond BRS.
    + (* [comment removed for export] *)
      zstep. if_false.
      lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite BRS; reflexivity) end.
      cbv zeta.
      change (ng_of (pv bq alloc data eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data eb sx ix)) with ix.
      change (pc_bufdata (pv bq alloc data eb sx ix)) with data. fold (ng_reset sx).
      apply evtF_done.
  eapply (ngn_shb_tail LOOP HLOOP) with (rem := rem) (hcs := hcs) (dw := dw);
          [exact FP5 | assumption | exact FR6 | reflexivity | assumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG
          | exact LEN | exact L30 | lia | exact OF5].
    + (* [comment removed for export] *)
      lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite BRS; reflexivity) end.
      cbv zeta.
      change (set_bufdata (swap_field 2 12 (swap_field 4 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 2 12 (swap_field 4 8 data)) eb sx ix).
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.shb_swap_data' data) by lia. fold g0 g1 g2 g3 j0 j1.
      set (data' := firstn 8 data ++ [g3; g2; g1; g0; j1; j0] ++ skipn 14 data).
      change (ng_of (pv bq alloc data' eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data' eb sx ix)) with ix.
      change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'. fold (ng_reset sx).
      assert (FRC : rw_cells asegs m1 (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)]).
      { lazymatch type of FRJ with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?tl) =>
          pose proof (proj2 (proj1 (rw_cells_app asegs m1 _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] (c13 :: tl)) FRJ)) as X;
          pose proof (proj1 (proj1 (rw_cells_app asegs m1 _ [c13] tl) X)) as X2 end.
        cbn [cells_size csize Nat.add] in X2. replace (bv_unsigned sp + -240 + Z.of_nat 104) with (bv_unsigned sp + -136) in X2 by lia. exact X2. }
      assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kH & kHr & kH1 & kH2).
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kD & kDr & kD1 & kD2).
      cbn [cb_addr cb_size fst snd] in kH1, kH2, kD1, kD2.
      zstep. if_false.   (* [comment removed for export] *)
      ck0_at BUNP (Bq + 8)%Z; ck_go.
      ck0_at BUNP (Bq + 8)%Z; ck_go.
      rewrite (sx32_lit g0 g1 g2 g3) by lia.
      hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
      eapply evtF_cut.
      { eapply (ngn_shb_swapA RNG5 sp gp tp F fc lo) with (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (j0 := j0) (j1 := j1) (Bq := Bq) (alloc := alloc) (bB := bB);
          [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | exact FRC | assumption | exact LO | exact BU | lia | exact RSPW | exact BUNP | exact BTOP
          | lia | exact B2 | exact B1 | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
      cbv beta. intros ms' (a4v & a5v & a6v & w4 & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E2).
  assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 14)]%Z a) m1 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk asegs m1 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
        assert (FW7 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(Bq + 8, Bq + 14)]%Z).
        { apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold A3P.F_ngnEA.TwB.pv. cbn [pc_buffer pc_bufalloc]. lia. }
        assert (G7 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m7) by (eapply (gl_frame _ _ _ GL); [exact G6 | exact MU7 | exact WM7 | exact FW7]).
  (* [comment removed for export] *)
        assert (BUF7 : rw_cells asegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx')]).
        { assert (R7 : rw_cells asegs m7 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C2 (Z_to_bv 64 (j1 + 256 * j0)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 w4 (le4val g3 g2 g1 g0) E1), (le2_of_val a4v j1 j0 j1) by lia. rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0) by lia. reflexivity. }
          pose proof (rw_cells_merge asegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_length. cbn [length]. lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') = map b8 data').
        { subst data'. change ([b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') with (map b8 [g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) bsx').
          change ([g3; g2; g1; g0; j1; j0] ++ skipn 14 data) with ([g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) data).
          apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_pfx; [exact PFX | cbn [length]; lia | lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 14)]%Z a) by (intros a _ Hn; cbn [outside fst snd]; lia).
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7).
      { eapply (@A3P.F_ngnEA.TwB.PCAPR_bufdata rc tlsI H hptr FO GIOA fflagA GL) with (m5 := m1) (data := data) (Q := fun a => outside [(Bq + 8, Bq + 14)]%Z a);
          [exact G6 | exact PC6 | exact AGP | exact HQ7 | exact BUF7 | exact PFX7 | exact LEN']. }
      assert (G7' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB FL m7) by exact G7.
      assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G6 | exact MU7 | exact WM7 | | lia].
        apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold A3P.F_ngnEA.TwB.pv. cbn [pc_buffer pc_bufalloc]. lia. }
      assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
      { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_Forall; [exact DRNG|].
        repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
      zstep.   (* [comment removed for export] *)
      apply evtF_done.
      eapply (ngn_shb_tail LOOP HLOOP) with (rem := rem) (hcs := hcs) (dw := dw);
        [exact FP5 | exact ST7 | exact FR6 | reflexivity | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
        | rewrite LEN'; exact LEN | exact L30 | lia | exact OF5].
  Qed.
  End Sz7.
  #[using="rc tlsI FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC TR"] Lemma ngn_shb : ltac:(let t := eval cbv delta [ngn_shb__stmt] in ngn_shb__stmt in exact t).
  Proof. intros LOOP HLOOP ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_shb__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.
End CANSEC1.
End F_ngnSA.
