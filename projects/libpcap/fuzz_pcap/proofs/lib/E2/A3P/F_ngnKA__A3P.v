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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Mem.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_ngnKA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgnK.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_epbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_epbK H hptr).
  #[local] Abbreviation ngn_spbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_spbK H hptr).
  #[local] Abbreviation ngn_pbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_pbK H hptr).

  Definition ngn_idbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 8 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p else p in
      let lt := get_le16 (pc_bufdata p') off in
      let sl := get_le32 (pc_bufdata p') (off + 4) in
      if negb (pc_linktype p' =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) p')
      else if negb (pc_snapshot p' =? pcapint_adjust_snapshot (pc_linktype p') sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) p')
      else mbind (add_interface MOps (prims HO FO sites) p' off c') (fun r => let '(ok, c, p, m) := r in
             if ok then LOOP p else mret (inl (-1)%Z, set_errbuf m p))
    end.
  Definition ngn_shbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 16 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 2 (off + 4) (swap_field 4 off (pc_bufdata p))) p else p in
      let bom := get_le32 (pc_bufdata p') off in
      if bom =? BYTE_ORDER_MAGIC then
        let major := get_le16 (pc_bufdata p') (off + 4) in
        if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) p')
        else LOOP (set_ng (mkNg (ng_user_tsresol (ng_of p')) (ng_max_blocksize (ng_of p')) 0 (ng_ifaces_size (ng_of p')) []) (ng_ifaces_ptr_of p') p')
      else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order p')
      else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic p')
    end.
  Definition ngn_blkK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    if cur_block_type c =? BT_EPB then ngn_epbK c p
    else if cur_block_type c =? BT_SPB then ngn_spbK c p
    else if cur_block_type c =? BT_PB then ngn_pbK c p
    else if cur_block_type c =? BT_IDB then ngn_idbK LOOP c p
    else if cur_block_type c =? BT_SHB then ngn_shbK LOOP c p
    else LOOP p.
  Definition ngn_body (LOOP : pcapT -> MR) (rb : block_result) : MR :=
    match rb with
    | RB_Eof p => mret (inl 0%Z, p)
    | RB_Err m p => mret (inl (-1)%Z, set_errbuf m p)
    | RB_Ok c p => ngn_blkK LOOP c p
    end.

  #[using="Type"] Lemma ng_scan_blocks_S : forall fuel (p : pcapT),
    ng_scan_blocks MOps (prims HO FO sites) (S fuel) p
    = mbind (read_block MOps (prims HO FO sites) (DStack SiteBhdrNextPacket 0) p) (ngn_body (ng_scan_blocks MOps (prims HO FO sites) fuel)).
  Proof. intros. reflexivity. Qed.

  #[using="Type"] Lemma pcap_ng_next_packet_KF : forall fuel (p : pcapT),
    pcap_ng_next_packet MOps (prims HO FO sites) fuel p = mbind (ng_scan_blocks MOps (prims HO FO sites) fuel p) ngn_KF.
  Proof. intros. reflexivity. Qed.

  #[using="Type"] Lemma site_bhdr_frame : site_frameA SiteBhdrNextPacket = Some (FF_READ_BLOCK, 32%Z).
  Proof. reflexivity. Qed.
End NgnK.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnK.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_epbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_epbK H hptr).
  #[local] Abbreviation ngn_spbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_spbK H hptr).
  #[local] Abbreviation ngn_pbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_pbK H hptr).

  Definition ngn_idbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 8 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p else p in
      let lt := get_le16 (pc_bufdata p') off in
      let sl := get_le32 (pc_bufdata p') (off + 4) in
      if negb (pc_linktype p' =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) p')
      else if negb (pc_snapshot p' =? pcapint_adjust_snapshot (pc_linktype p') sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) p')
      else mbind (add_interface MOps (prims HO FO sites) p' off c') (fun r => let '(ok, c, p, m) := r in
             if ok then LOOP p else mret (inl (-1)%Z, set_errbuf m p))
    end.
  Definition ngn_shbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 16 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 2 (off + 4) (swap_field 4 off (pc_bufdata p))) p else p in
      let bom := get_le32 (pc_bufdata p') off in
      if bom =? BYTE_ORDER_MAGIC then
        let major := get_le16 (pc_bufdata p') (off + 4) in
        if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) p')
        else LOOP (set_ng (mkNg (ng_user_tsresol (ng_of p')) (ng_max_blocksize (ng_of p')) 0 (ng_ifaces_size (ng_of p')) []) (ng_ifaces_ptr_of p') p')
      else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order p')
      else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic p')
    end.
  Definition ngn_blkK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    if cur_block_type c =? BT_EPB then ngn_epbK c p
    else if cur_block_type c =? BT_SPB then ngn_spbK c p
    else if cur_block_type c =? BT_PB then ngn_pbK c p
    else if cur_block_type c =? BT_IDB then ngn_idbK LOOP c p
    else if cur_block_type c =? BT_SHB then ngn_shbK LOOP c p
    else LOOP p.
  Definition ngn_body (LOOP : pcapT -> MR) (rb : block_result) : MR :=
    match rb with
    | RB_Eof p => mret (inl 0%Z, p)
    | RB_Err m p => mret (inl (-1)%Z, set_errbuf m p)
    | RB_Ok c p => ngn_blkK LOOP c p
    end.

  #[using="Type"] Lemma ng_scan_blocks_S : forall fuel (p : pcapT),
    ng_scan_blocks MOps (prims HO FO sites) (S fuel) p
    = mbind (read_block MOps (prims HO FO sites) (DStack SiteBhdrNextPacket 0) p) (ngn_body (ng_scan_blocks MOps (prims HO FO sites) fuel)).
  Proof. intros. reflexivity. Qed.

  #[using="Type"] Lemma pcap_ng_next_packet_KF : forall fuel (p : pcapT),
    pcap_ng_next_packet MOps (prims HO FO sites) fuel p = mbind (ng_scan_blocks MOps (prims HO FO sites) fuel p) ngn_KF.
  Proof. intros. reflexivity. Qed.

  #[using="Type"] Lemma site_bhdr_frame : site_frameA SiteBhdrNextPacket = Some (FF_READ_BLOCK, 32%Z).
  Proof. reflexivity. Qed.
End NgnK.
End CANSEC1.
End TwB.
End F_ngnKA.

(* [comment removed for export] *)
Module F_ngnI0A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

  Definition ngn_idb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
           (ra' t0' t1' t2' x8 a1' a2' a3' a4' a5' a6' a7' x19 x20 x21 x22 x23 x24 x25 x26 t3' t4' t5' t6' : word) (mx : mem)
           (l0 l1 n0 n1 n2 n3 : Z) (Bq alloc bB : Z) (pre r2 : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [l0; l1; n0; n1; n2; n3] ->
      rw_cells asegs mx Bq ([CB 8 pre; C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 r2; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      rw_cells asegs mx (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)] ->
      mem_inv asegs mx ->
      (ATOP + 4096 <= lo)%Z -> (lo + 57344 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2^47)%Z -> rng RNGx lo (bv_unsigned sp - lo) ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (16 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (a1v a2v a3v lv : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (Bq + 8) 3)) a1v a2v a3v
                       (Z_to_bv 64 65280) a5' a6' a7' (Z_to_bv 64 (Bq + 12)) x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (Bq + 8)) t3' t4' t5' t6')
                   F (Z_to_bv 64 0x8ce40) fc None m' (seg_rom asegs)
          /\ munch [(Bq + 8, Bq + 16)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' Bq ([CB 8 pre; C2 lv; CB 2 r2; C4 a1v] ++ rest)
          /\ (bv_unsigned lv = l1 + 256 * l0 + 65536 * l1)%Z /\ (bv_unsigned a1v mod 2^32 = le4val n3 n2 n1 n0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (Bq + 8) 3)) a1' a2' a3' a4'
                 a5' a6' a7' (Z_to_bv 64 (Bq + 12)) x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (Bq + 8)) t3' t4' t5' t6')
            F (Z_to_bv 64 0x8cdd0) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 a1' a2' a3' a4' a5' a6' a7' x19 x20 x21 x22 x23 x24 x25 x26 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq alloc bB pre r2 rest : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ngn_idb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros GR HB FRC MI LO BU SP47 RSPW BUNP BTOP AL16 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH.
 qfold.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 16)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck0_at BUNP (Bq + 8)%Z; ck_go.
    ck0_at BUNP (Bq + 8)%Z; ck_go.
  rewrite (zx16_lit (l0 + 256 * l1)) by lia.
  do 4 zstep. zstep.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  rewrite (sx32_lit n0 n1 n2 n3) by lia.
  do 10 zstep. zstep.
  apply evtF_done. cbv beta.
  lazymatch goal with HX : rw_cells asegs ?mm Bq (CB 8 pre :: C2 ?w1 :: CB 2 r2 :: C4 ?w0 :: _) |- _ =>
    exists w0; do 2 eexists; exists w1, mm; split; [reflexivity|];
    split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
  split.
  - replace (l0 + 256 * l1) with (le_of_bytes [l0; l1]) by (cbn [le_of_bytes]; lia).
    repeat lanes_step. rewrite unsigned_lit by (cbn [le_of_bytes]; lia). cbn [le_of_bytes]. lia.
  - rewrite unsigned_lit_wrap. change (2^64) with 18446744073709551616.
    rewrite Z.mod_mod_divide by (exists (2^32); reflexivity).
    replace (sxv n0 n1 n2 n3 mod 18446744073709551616) with (bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [n0; n1; n2; n3])))).
    2:{ replace (le_of_bytes [n0; n1; n2; n3]) with (le4val n0 n1 n2 n3) by (unfold le4val; cbn [le_of_bytes]; lia).
        rewrite unsigned_sx32 by lia. symmetry. apply Z.mod_small. unfold sxv, le4val. Z.div_mod_to_equations; lia. }
    unfold le4val. bswap_arith.
  Qed.
  End Sz1.
  #[using="Type"] Lemma ngn_idb_swapA : ltac:(let t := eval cbv delta [ngn_idb_swapA__stmt] in ngn_idb_swapA__stmt in exact t).
  Proof. intros RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 a1' a2' a3' a4' a5' a6' a7' x19 x20 x21 x22 x23 x24 x25 x26 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq alloc bB pre r2 rest. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

  Definition ngn_idb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
           (ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x22 x23 x24 x25 x26 t3' t4' t5' t6' : word) (mx : mem)
           (l0 l1 n0 n1 n2 n3 : Z) (Bq alloc bB : Z) (pre r2 : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [l0; l1; n0; n1; n2; n3] ->
      rw_cells asegs mx Bq ([CB 8 pre; C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 r2; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      rw_cells asegs mx (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)] ->
      mem_inv asegs mx ->
      (ATOP + 4096 <= lo)%Z -> (lo + 57344 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2^47)%Z -> rng RNGx lo (bv_unsigned sp - lo) ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (16 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (a2v a3v a4v lv w4 : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (Z.shiftr (Bq + 8) 3)) a1' a2v a3v a4v
                       (Z_to_bv 64 65280) a6' a7' x18 x19 (Z_to_bv 64 (Bq + 12)) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 (Bq + 8)) t3' t4' t5' t6')
                   F (Z_to_bv 64 0x8cfd0) fc None m' (seg_rom asegs)
          /\ munch [(Bq + 8, Bq + 16)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' Bq ([CB 8 pre; C2 lv; CB 2 r2; C4 w4] ++ rest)
          /\ (bv_unsigned lv = l1 + 256 * l0 + 65536 * l1)%Z /\ (bv_unsigned w4 mod 2^32 = le4val n3 n2 n1 n0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (Z.shiftr (Bq + 8) 3)) a1' a2' a3' a4'
                 a5' a6' a7' x18 x19 (Z_to_bv 64 (Bq + 12)) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 (Bq + 8)) t3' t4' t5' t6')
            F (Z_to_bv 64 0x8cf60) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x22 x23 x24 x25 x26 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq alloc bB pre r2 rest : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ngn_idb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros GR HB FRC MI LO BU SP47 RSPW BUNP BTOP AL16 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH.
 qfold.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 16)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck0_at BUNP (Bq + 8)%Z; ck_go.
    ck0_at BUNP (Bq + 8)%Z; ck_go.
  rewrite (zx16_lit (l0 + 256 * l1)) by lia.
  do 4 zstep. zstep.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  rewrite (sx32_lit n0 n1 n2 n3) by lia.
  do 10 zstep. zstep.
  apply evtF_done. cbv beta.
  lazymatch goal with HX : rw_cells asegs ?mm Bq (CB 8 pre :: C2 ?w1 :: CB 2 r2 :: C4 ?w0 :: _) |- _ =>
    do 3 eexists; exists w1, w0, mm; split; [reflexivity|];
    split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
  split.
  - replace (l0 + 256 * l1) with (le_of_bytes [l0; l1]) by (cbn [le_of_bytes]; lia).
    repeat lanes_step. rewrite unsigned_lit by (cbn [le_of_bytes]; lia). cbn [le_of_bytes]. lia.
  - rewrite unsigned_lit_wrap. change (2^64) with 18446744073709551616.
    rewrite Z.mod_mod_divide by (exists (2^32); reflexivity).
    replace (sxv n0 n1 n2 n3 mod 18446744073709551616) with (bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [n0; n1; n2; n3])))).
    2:{ replace (le_of_bytes [n0; n1; n2; n3]) with (le4val n0 n1 n2 n3) by (unfold le4val; cbn [le_of_bytes]; lia).
        rewrite unsigned_sx32 by lia. symmetry. apply Z.mod_small. unfold sxv, le4val. Z.div_mod_to_equations; lia. }
    unfold le4val. bswap_arith.
  Qed.
  End Sz1.
  #[using="Type"] Lemma ngn_idb_swapA : ltac:(let t := eval cbv delta [ngn_idb_swapA__stmt] in ngn_idb_swapA__stmt in exact t).
  Proof. intros RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x22 x23 x24 x25 x26 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq alloc bB pre r2 rest. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_ngnI0A.

(* [comment removed for export] *)
Module F_ngnQA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.
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
Lemma firstn2_q8 : forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Proof.
  intros data bs k off PFX Hk H1. subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma sxv_lanes : forall g0 g1 g2 g3, (0 <= g0 < 256 -> 0 <= g1 < 256 -> 0 <= g2 < 256 -> 0 <= g3 < 256 ->
  sxv g0 g1 g2 g3 mod 18446744073709551616 = bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [g0; g1; g2; g3]))))%Z.
Proof.
  intros g0 g1 g2 g3 H0 H1 H2 H3.
  replace (le_of_bytes [g0; g1; g2; g3]) with (le4val g0 g1 g2 g3) by (unfold le4val; cbn [le_of_bytes]; lia).
  rewrite unsigned_sx32 by lia. apply Z.mod_small. unfold sxv, le4val. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma bswap32s_sxv : forall g0 g1 g2 g3, (0 <= g0 < 256 -> 0 <= g1 < 256 -> 0 <= g2 < 256 -> 0 <= g3 < 256 ->
  Z_to_bv 64 (Z.lor (Z.lor ((bv_swrap 32 (Z.shiftl (sxv g0 g1 g2 g3 mod 18446744073709551616) 24)) mod 18446744073709551616)
                           ((Z.shiftl (Z.land (sxv g0 g1 g2 g3 mod 18446744073709551616) 65280) 8) mod 18446744073709551616))
                    (Z.lor (Z.land (Z.shiftr (sxv g0 g1 g2 g3 mod 18446744073709551616) 8) 65280)
                           ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv g0 g1 g2 g3 mod 18446744073709551616)) 24)) mod 18446744073709551616)))
  = Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu (le4val g3 g2 g1 g0)))%Z.
Proof.
  intros g0 g1 g2 g3 H0 H1 H2 H3. f_equal. rewrite (sxv_lanes g0 g1 g2 g3) by lia.
  repeat lanes_step. cbn [le_of_bytes]. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu, le4val, sx_lane.
  destruct (Z.ltb_spec g0 128); destruct (Z.ltb_spec (g3 + 256 * g2 + 65536 * g1 + 16777216 * g0) (2^31)); lia.
Qed.

(* [comment removed for export] *)
Lemma bswap32_sxv_mod32 : forall g0 g1 g2 g3, (0 <= g0 < 256 -> 0 <= g1 < 256 -> 0 <= g2 < 256 -> 0 <= g3 < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (Z.lor ((Z.shiftl (sxv g0 g1 g2 g3 mod 18446744073709551616) 24) mod 18446744073709551616)
                                        ((Z.shiftl (Z.land (sxv g0 g1 g2 g3 mod 18446744073709551616) 65280) 8) mod 18446744073709551616))
                                 (Z.lor (Z.land (Z.shiftr (sxv g0 g1 g2 g3 mod 18446744073709551616) 8) 65280)
                                        ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv g0 g1 g2 g3 mod 18446744073709551616)) 24)) mod 18446744073709551616)))) mod 2^32
  = le4val g3 g2 g1 g0)%Z.
Proof.
  intros g0 g1 g2 g3 H0 H1 H2 H3. rewrite unsigned_lit_wrap. change (2^64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_mod_divide by (exists (2^32)%Z; reflexivity).
  rewrite (sxv_lanes g0 g1 g2 g3) by lia. unfold le4val. bswap_arith.
Qed.

(* [comment removed for export] *)
Lemma ts_swap_wordA : forall h0 h1 h2 h3 l0 l1 l2 l3,
  (0 <= h0 < 256 -> 0 <= h1 < 256 -> 0 <= h2 < 256 -> 0 <= h3 < 256 -> 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64
    (Z.lor
       (Z.lor
          (Z.lor ((Z.shiftl (le4val h0 h1 h2 h3 mod 18446744073709551616) 56) mod 18446744073709551616)
                 ((Z.shiftl (Z.land (le4val h0 h1 h2 h3 mod 18446744073709551616) 65280) 40) mod 18446744073709551616))
          (Z.lor
             (Z.lor (Z.shiftr ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 56) mod 18446744073709551616) 32)
                    (Z.land ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 8) mod 18446744073709551616) 16711680))
             (Z.lor (Z.land (Z.shiftr (sxv l0 l1 l2 l3 mod 18446744073709551616) 8) 65280)
                    ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv l0 l1 l2 l3 mod 18446744073709551616)) 24)) mod 18446744073709551616))))
       (Z.lor
          ((Z.shiftl (Z.land (Z.lor ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 32) mod 18446744073709551616) (le4val h0 h1 h2 h3 mod 18446744073709551616)) 16711680) 24) mod 18446744073709551616)
          ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 32) mod 18446744073709551616) (le4val h0 h1 h2 h3 mod 18446744073709551616))) 24)) mod 18446744073709551616) 32) mod 18446744073709551616)))
  = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0))%Z.
Proof.
  intros h0 h1 h2 h3 l0 l1 l2 l3 A0 A1 A2 A3 B0 B1 B2 B3. f_equal.
  rewrite (sxv_lanes l0 l1 l2 l3) by lia.
  replace (le4val h0 h1 h2 h3 mod 18446744073709551616)%Z with (le_of_bytes [h0; h1; h2; h3]) by (unfold le4val; cbn [le_of_bytes]; rewrite Z.mod_small by lia; lia).
  repeat lanes_step. cbn [le_of_bytes]. unfold le4val. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Lemma firstn2_q8 : forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Proof.
  intros data bs k off PFX Hk H1. subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma sxv_lanes : forall g0 g1 g2 g3, (0 <= g0 < 256 -> 0 <= g1 < 256 -> 0 <= g2 < 256 -> 0 <= g3 < 256 ->
  sxv g0 g1 g2 g3 mod 18446744073709551616 = bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [g0; g1; g2; g3]))))%Z.
Proof.
  intros g0 g1 g2 g3 H0 H1 H2 H3.
  replace (le_of_bytes [g0; g1; g2; g3]) with (le4val g0 g1 g2 g3) by (unfold le4val; cbn [le_of_bytes]; lia).
  rewrite unsigned_sx32 by lia. apply Z.mod_small. unfold sxv, le4val. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma bswap32s_sxv : forall g0 g1 g2 g3, (0 <= g0 < 256 -> 0 <= g1 < 256 -> 0 <= g2 < 256 -> 0 <= g3 < 256 ->
  Z_to_bv 64 (Z.lor (Z.lor ((bv_swrap 32 (Z.shiftl (sxv g0 g1 g2 g3 mod 18446744073709551616) 24)) mod 18446744073709551616)
                           ((Z.shiftl (Z.land (sxv g0 g1 g2 g3 mod 18446744073709551616) 65280) 8) mod 18446744073709551616))
                    (Z.lor (Z.land (Z.shiftr (sxv g0 g1 g2 g3 mod 18446744073709551616) 8) 65280)
                           ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv g0 g1 g2 g3 mod 18446744073709551616)) 24)) mod 18446744073709551616)))
  = Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu (le4val g3 g2 g1 g0)))%Z.
Proof.
  intros g0 g1 g2 g3 H0 H1 H2 H3. f_equal. rewrite (sxv_lanes g0 g1 g2 g3) by lia.
  repeat lanes_step. cbn [le_of_bytes]. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu, le4val, sx_lane.
  destruct (Z.ltb_spec g0 128); destruct (Z.ltb_spec (g3 + 256 * g2 + 65536 * g1 + 16777216 * g0) (2^31)); lia.
Qed.

(* [comment removed for export] *)
Lemma bswap32_sxv_mod32 : forall g0 g1 g2 g3, (0 <= g0 < 256 -> 0 <= g1 < 256 -> 0 <= g2 < 256 -> 0 <= g3 < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (Z.lor ((Z.shiftl (sxv g0 g1 g2 g3 mod 18446744073709551616) 24) mod 18446744073709551616)
                                        ((Z.shiftl (Z.land (sxv g0 g1 g2 g3 mod 18446744073709551616) 65280) 8) mod 18446744073709551616))
                                 (Z.lor (Z.land (Z.shiftr (sxv g0 g1 g2 g3 mod 18446744073709551616) 8) 65280)
                                        ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv g0 g1 g2 g3 mod 18446744073709551616)) 24)) mod 18446744073709551616)))) mod 2^32
  = le4val g3 g2 g1 g0)%Z.
Proof.
  intros g0 g1 g2 g3 H0 H1 H2 H3. rewrite unsigned_lit_wrap. change (2^64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_mod_divide by (exists (2^32)%Z; reflexivity).
  rewrite (sxv_lanes g0 g1 g2 g3) by lia. unfold le4val. bswap_arith.
Qed.

(* [comment removed for export] *)
Lemma ts_swap_wordA : forall h0 h1 h2 h3 l0 l1 l2 l3,
  (0 <= h0 < 256 -> 0 <= h1 < 256 -> 0 <= h2 < 256 -> 0 <= h3 < 256 -> 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64
    (Z.lor
       (Z.lor
          (Z.lor ((Z.shiftl (le4val h0 h1 h2 h3 mod 18446744073709551616) 56) mod 18446744073709551616)
                 ((Z.shiftl (Z.land (le4val h0 h1 h2 h3 mod 18446744073709551616) 65280) 40) mod 18446744073709551616))
          (Z.lor
             (Z.lor (Z.shiftr ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 56) mod 18446744073709551616) 32)
                    (Z.land ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 8) mod 18446744073709551616) 16711680))
             (Z.lor (Z.land (Z.shiftr (sxv l0 l1 l2 l3 mod 18446744073709551616) 8) 65280)
                    ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv l0 l1 l2 l3 mod 18446744073709551616)) 24)) mod 18446744073709551616))))
       (Z.lor
          ((Z.shiftl (Z.land (Z.lor ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 32) mod 18446744073709551616) (le4val h0 h1 h2 h3 mod 18446744073709551616)) 16711680) 24) mod 18446744073709551616)
          ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl (sxv l0 l1 l2 l3 mod 18446744073709551616) 32) mod 18446744073709551616) (le4val h0 h1 h2 h3 mod 18446744073709551616))) 24)) mod 18446744073709551616) 32) mod 18446744073709551616)))
  = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0))%Z.
Proof.
  intros h0 h1 h2 h3 l0 l1 l2 l3 A0 A1 A2 A3 B0 B1 B2 B3. f_equal.
  rewrite (sxv_lanes l0 l1 l2 l3) by lia.
  replace (le4val h0 h1 h2 h3 mod 18446744073709551616)%Z with (le_of_bytes [h0; h1; h2; h3]) by (unfold le4val; cbn [le_of_bytes]; rewrite Z.mod_small by lia; lia).
  repeat lanes_step. cbn [le_of_bytes]. unfold le4val. lia.
Qed.
End TwB.
End F_ngnQA.

(* [comment removed for export] *)
Module F_aiCA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Mem.


From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
(* [comment removed for export] *) From Ltac2 Require Ltac2.
#[local] Ltac2 Set StepFast.sf_fold_goal := Ltac2.Init.false.
(* [comment removed for export] *)
Definition le8_lorA__stmt : Prop := forall v0 v1 v2 v3 v4 v5 v6 v7, (0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> 0 <= v4 < 256 -> 0 <= v5 < 256 -> 0 <= v6 < 256 -> 0 <= v7 < 256 ->
  Z.lor (Z.shiftl (Z.lor (Z.lor ((Z.shiftl v7 24) mod 18446744073709551616) ((Z.shiftl v6 16) mod 18446744073709551616)) (Z.lor ((Z.shiftl v5 8) mod 18446744073709551616) v4)) 32 mod 18446744073709551616)
        (Z.lor (Z.lor ((Z.shiftl v3 24) mod 18446744073709551616) ((Z.shiftl v2 16) mod 18446744073709551616)) (Z.lor ((Z.shiftl v1 8) mod 18446744073709551616) v0))
  = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val v0 v1 v2 v3 v4 v5 v6 v7)%Z.
Section Sz1.
Variables v0 v1 v2 v3 v4 v5 v6 v7 : ltac2:(SecDiet.SzSec.tyM 'le8_lorA__stmt "vvvvvvvv" @v0).
#[using="Type"] Lemma le8_lorA__body : ltac2:(SecDiet.SzSec.bodyP 'le8_lorA__stmt "vvvvvvvv").
Proof.
  intros A0 A1 A2 A3 A4 A5 A6 A7.
  qfold.
  replace v0 with (le_of_bytes [v0]) at 1 by (cbn [le_of_bytes]; lia). replace v1 with (le_of_bytes [v1]) at 1 by (cbn [le_of_bytes]; lia).
  replace v2 with (le_of_bytes [v2]) at 1 by (cbn [le_of_bytes]; lia). replace v3 with (le_of_bytes [v3]) at 1 by (cbn [le_of_bytes]; lia).
  replace v4 with (le_of_bytes [v4]) at 1 by (cbn [le_of_bytes]; lia). replace v5 with (le_of_bytes [v5]) at 1 by (cbn [le_of_bytes]; lia).
  replace v6 with (le_of_bytes [v6]) at 1 by (cbn [le_of_bytes]; lia). replace v7 with (le_of_bytes [v7]) at 1 by (cbn [le_of_bytes]; lia).
  repeat lanes_step. cbn [le_of_bytes]. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val. lia.
Qed.
End Sz1.
Lemma le8_lorA : ltac:(let t := eval cbv delta [le8_lorA__stmt] in le8_lorA__stmt in exact t).
Proof. intros v0 v1 v2 v3 v4 v5 v6 v7. ltac2:(SecDiet.SzSec.closeP 'le8_lorA__body "vvvvvvvv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

  (* [comment removed for export] *)
  Definition ldu64A__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (A : Z) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
      mem_inv asegs m -> (0 < A)%Z -> (A + 8 < 2^47)%Z -> rng RNGx A 8 ->
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
      rw_cells asegs m A [CB 8 (map b8 [u0; u1; u2; u3; u4; u5; u6; u7])] ->
      evtF asegs RNGx (fun ms' => exists (a0' a3' a4' a5' s0' : word),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1 a2 a3' a4' a5' a6 a7 s2 s3 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3
                       (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7)) t5 t6)
                   F (Z_to_bv 64 0x8c548) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 A) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8c4ec) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'ldu64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ldu64A__body : ltac2:(SecDiet.SzSec.bodyP 'ldu64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI HA1 HA2 RA B0 B1 B2 B3 B4 B5 B6 B7 HV.
 qfold.
    cbn [map] in HV.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 23 zstep.
    cbn [firstn skipn app]. rewrite ?zext_extract_byte. change (b8 u0) with (Z_to_bv 8 u0). change (b8 u1) with (Z_to_bv 8 u1). change (b8 u2) with (Z_to_bv 8 u2). change (b8 u3) with (Z_to_bv 8 u3).
    change (b8 u4) with (Z_to_bv 8 u4). change (b8 u5) with (Z_to_bv 8 u5). change (b8 u6) with (Z_to_bv 8 u6). change (b8 u7) with (Z_to_bv 8 u7).
    rewrite !zxb_lit by lia. rewrite !unsigned_lit by lia.
    rewrite (le8_lorA u0 u1 u2 u3 u4 u5 u6 u7) by lia.
    apply evtF_done. do 5 eexists. reflexivity.
  Qed.
  End Sz2.
  #[using="Type"] Lemma ldu64A : ltac:(let t := eval cbv delta [ldu64A__stmt] in ldu64A__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'ldu64A__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition bswap64A__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (SPF : Z) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
      mem_inv asegs m -> sp = Z_to_bv 64 SPF -> (0 < SPF)%Z -> (SPF + 24 < 2^47)%Z -> rng RNGx (SPF + 16) 8 ->
      rw_cells asegs m (SPF + 16) [C8 (Z_to_bv 64 65280)] ->
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
      evtF asegs RNGx (fun ms' => exists (a0' a3' a4' a5' s0' s3' : word),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1 a2 a3' a4' a5' a6 a7 s2 s3' s4 s5 s6 s7 s8 s9 s10 s11 t3
                       (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u7 u6 u5 u4 u3 u2 u1 u0)) t5 t6)
                   F (Z_to_bv 64 0x8c3c0) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
                 (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7)) t5 t6)
            F (Z_to_bv 64 0x8c54c) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6 F fc m SPF u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'bswap64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma bswap64A__body : ltac2:(SecDiet.SzSec.bodyP 'bswap64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI -> HS1 HS2 RS HF B0 B1 B2 B3 B4 B5 B6 B7.
 qfold.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 25 zstep.
    replace (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7 mod 18446744073709551616)%Z with (le_of_bytes [u0; u1; u2; u3; u4; u5; u6; u7])
      by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val; cbn [le_of_bytes]; rewrite Z.mod_small by lia; lia).
    match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
      replace (Z.lor a b) with (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u7 u6 u5 u4 u3 u2 u1 u0) by (repeat lanes_step; cbn [le_of_bytes]; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val; lia) end.
    apply evtF_done. do 6 eexists. reflexivity.
  Qed.
  End Sz3.
  #[using="Type"] Lemma bswap64A : ltac:(let t := eval cbv delta [bswap64A__stmt] in bswap64A__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6 F fc m SPF u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'bswap64A__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma pow10A : forall (n : nat) (k acc : Z) (RNGx : footprint)
      (ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      k = Z.of_nat (S n) -> (k <= 19)%Z -> (0 <= acc)%Z -> (acc * 10 ^ k < 2^64)%Z ->
      evtF asegs RNGx (fun ms' => ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (acc * 10 ^ k)) t2 s0 s1 a0 a1 a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 10) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x8c5f8) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 (Z_to_bv 64 acc) t2 s0 s1 a0 a1 a2 (Z_to_bv 64 k) a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 10) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8c5ec) fc None m (seg_rom asegs)).
  Proof.
    induction n as [|n IH]; intros until m; intros Hk K19 A0 AB.
    - subst k. change (Z.of_nat 1) with 1%Z in *.
      assert (A1 : (acc * 10 < 2^64)%Z) by (rewrite Z.pow_1_r in AB; exact AB).
      pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
      zstep. zstep. zstep.
      if_false. apply evtF_done. reflexivity.
    - pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
      zstep. zstep.
      rewrite (bv_swrap32_small (k + -1)) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia).
      assert (P1 : (0 < 10 ^ (k - 1))%Z) by (apply Z.pow_pos_nonneg; lia).
      assert (E : (acc * 10 ^ k = (acc * 10) * 10 ^ (k - 1))%Z).
      { replace k with (k - 1 + 1)%Z at 1 by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
      zstep. rewrite (eqb_lits_false (k + -1) 0) by lia. cbv beta iota delta [negb].
      rewrite E. replace (k + -1)%Z with (k - 1)%Z by lia.
      apply (IH (k - 1)%Z (acc * 10)%Z); [lia | lia | lia | rewrite <- E; exact AB].
  Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition le8_lorA__stmt : Prop := forall v0 v1 v2 v3 v4 v5 v6 v7, (0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> 0 <= v4 < 256 -> 0 <= v5 < 256 -> 0 <= v6 < 256 -> 0 <= v7 < 256 ->
  Z.lor (Z.shiftl (Z.lor (Z.lor ((Z.shiftl v7 24) mod 18446744073709551616) ((Z.shiftl v6 16) mod 18446744073709551616)) (Z.lor ((Z.shiftl v5 8) mod 18446744073709551616) v4)) 32 mod 18446744073709551616)
        (Z.lor (Z.lor ((Z.shiftl v3 24) mod 18446744073709551616) ((Z.shiftl v2 16) mod 18446744073709551616)) (Z.lor ((Z.shiftl v1 8) mod 18446744073709551616) v0))
  = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val v0 v1 v2 v3 v4 v5 v6 v7)%Z.
Section Sz1.
Variables v0 v1 v2 v3 v4 v5 v6 v7 : ltac2:(SecDiet.SzSec.tyM 'le8_lorA__stmt "vvvvvvvv" @v0).
#[using="Type"] Lemma le8_lorA__body : ltac2:(SecDiet.SzSec.bodyP 'le8_lorA__stmt "vvvvvvvv").
Proof.
  intros A0 A1 A2 A3 A4 A5 A6 A7.
  qfold.
  replace v0 with (le_of_bytes [v0]) at 1 by (cbn [le_of_bytes]; lia). replace v1 with (le_of_bytes [v1]) at 1 by (cbn [le_of_bytes]; lia).
  replace v2 with (le_of_bytes [v2]) at 1 by (cbn [le_of_bytes]; lia). replace v3 with (le_of_bytes [v3]) at 1 by (cbn [le_of_bytes]; lia).
  replace v4 with (le_of_bytes [v4]) at 1 by (cbn [le_of_bytes]; lia). replace v5 with (le_of_bytes [v5]) at 1 by (cbn [le_of_bytes]; lia).
  replace v6 with (le_of_bytes [v6]) at 1 by (cbn [le_of_bytes]; lia). replace v7 with (le_of_bytes [v7]) at 1 by (cbn [le_of_bytes]; lia).
  repeat lanes_step. cbn [le_of_bytes]. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val. lia.
Qed.
End Sz1.
Lemma le8_lorA : ltac:(let t := eval cbv delta [le8_lorA__stmt] in le8_lorA__stmt in exact t).
Proof. intros v0 v1 v2 v3 v4 v5 v6 v7. ltac2:(SecDiet.SzSec.closeP 'le8_lorA__body "vvvvvvvv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

  (* [comment removed for export] *)
  Definition ldu64A__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (A : Z) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
      mem_inv asegs m -> (0 < A)%Z -> (A + 8 < 2^47)%Z -> rng RNGx A 8 ->
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
      rw_cells asegs m A [CB 8 (map b8 [u0; u1; u2; u3; u4; u5; u6; u7])] ->
      evtF asegs RNGx (fun ms' => exists (a0' a3' a4' a5' t0' : word),
          ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1 a2 a3' a4' a5' a6 a7 s2 s3 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3
                       (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7)) t5 t6)
                   F (Z_to_bv 64 0x8c6cc) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 A) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8c670) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'ldu64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ldu64A__body : ltac2:(SecDiet.SzSec.bodyP 'ldu64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI HA1 HA2 RA B0 B1 B2 B3 B4 B5 B6 B7 HV.
 qfold.
    cbn [map] in HV.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 23 zstep.
    cbn [firstn skipn app]. rewrite ?zext_extract_byte. change (b8 u0) with (Z_to_bv 8 u0). change (b8 u1) with (Z_to_bv 8 u1). change (b8 u2) with (Z_to_bv 8 u2). change (b8 u3) with (Z_to_bv 8 u3).
    change (b8 u4) with (Z_to_bv 8 u4). change (b8 u5) with (Z_to_bv 8 u5). change (b8 u6) with (Z_to_bv 8 u6). change (b8 u7) with (Z_to_bv 8 u7).
    rewrite !zxb_lit by lia. rewrite !unsigned_lit by lia.
    rewrite (le8_lorA u0 u1 u2 u3 u4 u5 u6 u7) by lia.
    apply evtF_done. do 5 eexists. reflexivity.
  Qed.
  End Sz2.
  #[using="Type"] Lemma ldu64A : ltac:(let t := eval cbv delta [ldu64A__stmt] in ldu64A__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'ldu64A__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition bswap64A__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (SPF : Z) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
      mem_inv asegs m -> sp = Z_to_bv 64 SPF -> (0 < SPF)%Z -> (SPF + 32 < 2^47)%Z -> rng RNGx (SPF + 24) 8 ->
      rw_cells asegs m (SPF + 24) [C8 (Z_to_bv 64 65280)] ->
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
      evtF asegs RNGx (fun ms' => exists (a0' a3' a4' a5' t0' s0' : word),
          ms' = MS (mkR ra sp gp tp t0' t1 t2 s0' s1 a0' a1 a2 a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
                       (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u7 u6 u5 u4 u3 u2 u1 u0)) t5 t6)
                   F (Z_to_bv 64 0x8c51c) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
                 (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7)) t5 t6)
            F (Z_to_bv 64 0x8c6d0) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6 F fc m SPF u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'bswap64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma bswap64A__body : ltac2:(SecDiet.SzSec.bodyP 'bswap64A__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI -> HS1 HS2 RS HF B0 B1 B2 B3 B4 B5 B6 B7.
 qfold.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 25 zstep.
    replace (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7 mod 18446744073709551616)%Z with (le_of_bytes [u0; u1; u2; u3; u4; u5; u6; u7])
      by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val; cbn [le_of_bytes]; rewrite Z.mod_small by lia; lia).
    match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
      replace (Z.lor a b) with (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u7 u6 u5 u4 u3 u2 u1 u0) by (repeat lanes_step; cbn [le_of_bytes]; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val; lia) end.
    apply evtF_done. do 6 eexists. reflexivity.
  Qed.
  End Sz3.
  #[using="Type"] Lemma bswap64A : ltac:(let t := eval cbv delta [bswap64A__stmt] in bswap64A__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6 F fc m SPF u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'bswap64A__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma pow10A : forall (n : nat) (k acc : Z) (RNGx : footprint)
      (ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      k = Z.of_nat (S n) -> (k <= 19)%Z -> (0 <= acc)%Z -> (acc * 10 ^ k < 2^64)%Z ->
      evtF asegs RNGx (fun ms' => ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (acc * 10 ^ k)) t2 s0 s1 a0 a1 a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 10) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x8c77c) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 (Z_to_bv 64 acc) t2 s0 s1 a0 a1 a2 (Z_to_bv 64 k) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 10) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8c770) fc None m (seg_rom asegs)).
  Proof.
    induction n as [|n IH]; intros until m; intros Hk K19 A0 AB.
    - subst k. change (Z.of_nat 1) with 1%Z in *.
      assert (A1 : (acc * 10 < 2^64)%Z) by (rewrite Z.pow_1_r in AB; exact AB).
      pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
      zstep. zstep. zstep.
      if_false. apply evtF_done. reflexivity.
    - pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
      zstep. zstep.
      rewrite (bv_swrap32_small (k + -1)) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia).
      assert (P1 : (0 < 10 ^ (k - 1))%Z) by (apply Z.pow_pos_nonneg; lia).
      assert (E : (acc * 10 ^ k = (acc * 10) * 10 ^ (k - 1))%Z).
      { replace k with (k - 1 + 1)%Z at 1 by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
      zstep. rewrite (eqb_lits_false (k + -1) 0) by lia. cbv beta iota delta [negb].
      rewrite E. replace (k + -1)%Z with (k - 1)%Z by lia.
      apply (IH (k - 1)%Z (acc * 10)%Z); [lia | lia | lia | rewrite <- E; exact AB].
  Qed.
End CANSEC1.
End TwB.
End F_aiCA.

(* [comment removed for export] *)
Module F_aiC2A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Mem.


From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (574572%Z, 574572%Z) => idtac | (574572%Z, 575032%Z) => idtac | (574632%Z, 574632%Z) => idtac | (574632%Z, 575048%Z) => idtac | (574680%Z, 574680%Z) => idtac | (574680%Z, 575128%Z) => idtac | (574700%Z, 574700%Z) => idtac | (574700%Z, 575140%Z) => idtac | (574924%Z, 574924%Z) => idtac | (574924%Z, 575152%Z) => idtac | (574992%Z, 574992%Z) => idtac | (574992%Z, 575460%Z) => idtac | (575060%Z, 575060%Z) => idtac | (575060%Z, 575476%Z) => idtac | (575108%Z, 575108%Z) => idtac | (575108%Z, 575556%Z) => idtac | (575128%Z, 575128%Z) => idtac | (575128%Z, 575568%Z) => idtac | (575352%Z, 575352%Z) => idtac | (575352%Z, 575580%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

  (* [comment removed for export] *)
  Definition opt_lenA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (code olen : Z) (Bq alloc bB D : Z),
      (0 <= code < 65536)%Z -> (0 <= olen < 65536)%Z ->
      rw_cells asegs mx D [Cells.C2 (Z_to_bv 64 code); Cells.C2 (Z_to_bv 64 olen)] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= D)%Z -> (D + 4 <= Bq + alloc)%Z -> (D mod 4 = 0)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 olen) a4 (Z_to_bv 64 (olen + 3)) a6 a7
                       s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 (Z_to_bv 64 ((olen + 3) / 4 * 4)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c478) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (D + 2)) a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c45c) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'opt_lenA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma opt_lenA__body : ltac2:(SecDiet.SzSec.bodyP 'opt_lenA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HC HL HOPT MIx BUNP INB1 INB2 DM4 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join BUNP 2%Z 0x8c46c%Z [15%Z; 25%Z].
    zstep. rewrite (zx16_lit olen) by lia.
    zstep. zstep.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_m4w (olen + 3)) by lia.
    apply evtF_done. reflexivity.
  Qed.
  End Sz1.
  #[using="Type"] Lemma opt_lenA : ltac:(let t := eval cbv delta [opt_lenA__stmt] in opt_lenA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D. ltac2:(SecDiet.SzSec.closeP 'opt_lenA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition opt_codeA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (code olen : Z) (Bq alloc bB D : Z),
      (0 <= code < 65536)%Z -> (0 <= olen < 65536)%Z ->
      rw_cells asegs mx D [Cells.C2 (Z_to_bv 64 code); Cells.C2 (Z_to_bv 64 olen)] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= D)%Z -> (D + 4 <= Bq + alloc)%Z -> (D mod 4 = 0)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists s0v : word,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1 (Z_to_bv 64 D) a1 a2 a3 a4 (Z_to_bv 64 code) a6 a7
                       s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c4ac) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.shiftr D 3)) s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c49c) fc None mx (seg_rom asegs)).
  Section Sz2.
  Variables RNGx ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'opt_codeA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma opt_codeA__body : ltac2:(SecDiet.SzSec.bodyP 'opt_codeA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HC HL HOPT MIx BUNP INB1 INB2 DM4 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join_at BUNP D 2%Z 0x8c4a8%Z [8%Z; 15%Z].
    zstep. rewrite (zx16_lit code) by lia.
    apply evtF_done. eexists. reflexivity.
  Qed.
  End Sz2.
  #[using="Type"] Lemma opt_codeA : ltac:(let t := eval cbv delta [opt_codeA__stmt] in opt_codeA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D. ltac2:(SecDiet.SzSec.closeP 'opt_codeA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition tsres_ldA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (v : Z) (Bq alloc bB A : Z),
      (0 <= v < 256)%Z ->
      rw_cells asegs mx A [CB 1 [b8 v]] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= A)%Z -> (A + 1 <= Bq + alloc)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists a3v : word,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sxb (Z_to_bv 8 v)) a1 a2 a3v (Z_to_bv 64 A) a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c5d0) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 A) a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c5bc) fc None mx (seg_rom asegs)).
  Section Sz3.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx v Bq alloc bB A : ltac2:(SecDiet.SzSec.tyM 'tsres_ldA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma tsres_ldA__body : ltac2:(SecDiet.SzSec.bodyP 'tsres_ldA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HV HB MIx BUNP INB1 INB2 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join BUNP 1%Z 0x8c5cc%Z [10%Z; 13%Z].
    zstep. change (b8 v) with (Z_to_bv 8 v).
    apply evtF_done. eexists. reflexivity.
  Qed.
  End Sz3.
  #[using="Type"] Lemma tsres_ldA : ltac:(let t := eval cbv delta [tsres_ldA__stmt] in tsres_ldA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx v Bq alloc bB A. ltac2:(SecDiet.SzSec.closeP 'tsres_ldA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ldu64ckA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (u0 u1 u2 u3 u4 u5 u6 u7 : Z) (Bq alloc bB A : Z),
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
      rw_cells asegs mx A [CB 8 (map b8 [u0; u1; u2; u3; u4; u5; u6; u7])] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= A)%Z -> (A + 8 <= Bq + alloc)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (a0' a3' a4' a5' s0' : word),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1 a2 a3' a4' a5' a6 a7 s2 s3 (Z_to_bv 64 1) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3
                       (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7)) t5 t6)
                   F (Z_to_bv 64 0x8c548) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 A) a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c4c8) fc None mx (seg_rom asegs)).
  Section Sz4.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx u0 u1 u2 u3 u4 u5 u6 u7 Bq alloc bB A : ltac2:(SecDiet.SzSec.tyM 'ldu64ckA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ldu64ckA__body : ltac2:(SecDiet.SzSec.bodyP 'ldu64ckA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros B0 B1 B2 B3 B4 B5 B6 B7 HV8 MIx BUNP INB1 INB2 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join BUNP 1%Z 0x8c4d8%Z [10%Z; 13%Z].
    zstep.
    ck_join BUNP 1%Z 0x8c4ec%Z [10%Z; 15%Z].
    eapply evtF_cut.
    { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.ldu64A with (A := A) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7);
        [exact MIx | lia | lia | eapply rng_sub; [exact BRNG | lia | lia] | exact B0 | exact B1 | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact HV8]. }
    cbv beta. intros ms' (a0x & a3x & a4x & a5x & s0x & ->).
    apply evtF_done. do 5 eexists. reflexivity.
  Qed.
  End Sz4.
  #[using="Type"] Lemma ldu64ckA : ltac:(let t := eval cbv delta [ldu64ckA__stmt] in ldu64ckA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx u0 u1 u2 u3 u4 u5 u6 u7 Bq alloc bB A. ltac2:(SecDiet.SzSec.closeP 'ldu64ckA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem.


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (574532%Z, 574532%Z) => idtac | (574532%Z, 574992%Z) => idtac | (574592%Z, 574592%Z) => idtac | (574592%Z, 575008%Z) => idtac | (574640%Z, 574640%Z) => idtac | (574640%Z, 575088%Z) => idtac | (574660%Z, 574660%Z) => idtac | (574660%Z, 575100%Z) => idtac | (574884%Z, 574884%Z) => idtac | (574884%Z, 575112%Z) => idtac | (574952%Z, 574952%Z) => idtac | (574952%Z, 575420%Z) => idtac | (575020%Z, 575020%Z) => idtac | (575020%Z, 575436%Z) => idtac | (575068%Z, 575068%Z) => idtac | (575068%Z, 575516%Z) => idtac | (575088%Z, 575088%Z) => idtac | (575088%Z, 575528%Z) => idtac | (575312%Z, 575312%Z) => idtac | (575312%Z, 575540%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

  (* [comment removed for export] *)
  Definition opt_lenA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (code olen : Z) (Bq alloc bB D : Z),
      (0 <= code < 65536)%Z -> (0 <= olen < 65536)%Z ->
      rw_cells asegs mx D [Cells.C2 (Z_to_bv 64 code); Cells.C2 (Z_to_bv 64 olen)] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= D)%Z -> (D + 4 <= Bq + alloc)%Z -> (D mod 4 = 0)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 olen) a4 (Z_to_bv 64 (olen + 3)) (Z_to_bv 64 ((olen + 3) / 4 * 4)) a7
                       s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c5f4) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (D + 2)) a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c5d8) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'opt_lenA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma opt_lenA__body : ltac2:(SecDiet.SzSec.bodyP 'opt_lenA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HC HL HOPT MIx BUNP INB1 INB2 DM4 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join BUNP 2%Z 0x8c5e8%Z [13%Z; 15%Z].
    zstep. rewrite (zx16_lit olen) by lia.
    zstep. zstep.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_m4w (olen + 3)) by lia.
    apply evtF_done. reflexivity.
  Qed.
  End Sz1.
  #[using="Type"] Lemma opt_lenA : ltac:(let t := eval cbv delta [opt_lenA__stmt] in opt_lenA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D. ltac2:(SecDiet.SzSec.closeP 'opt_lenA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition opt_codeA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (code olen : Z) (Bq alloc bB D : Z),
      (0 <= code < 65536)%Z -> (0 <= olen < 65536)%Z ->
      rw_cells asegs mx D [Cells.C2 (Z_to_bv 64 code); Cells.C2 (Z_to_bv 64 olen)] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= D)%Z -> (D + 4 <= Bq + alloc)%Z -> (D mod 4 = 0)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists t0v : word,
          ms' = MS (mkR ra sp gp tp t0v t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 (Z_to_bv 64 code) a6 a7
                       s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c630) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.shiftr D 3)) t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c620) fc None mx (seg_rom asegs)).
  Section Sz2.
  Variables RNGx ra sp gp tp t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'opt_codeA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma opt_codeA__body : ltac2:(SecDiet.SzSec.bodyP 'opt_codeA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HC HL HOPT MIx BUNP INB1 INB2 DM4 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join_at BUNP D 2%Z 0x8c62c%Z [5%Z; 15%Z].
    zstep. rewrite (zx16_lit code) by lia.
    apply evtF_done. eexists. reflexivity.
  Qed.
  End Sz2.
  #[using="Type"] Lemma opt_codeA : ltac:(let t := eval cbv delta [opt_codeA__stmt] in opt_codeA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx code olen Bq alloc bB D. ltac2:(SecDiet.SzSec.closeP 'opt_codeA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition tsres_ldA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (v : Z) (Bq alloc bB A : Z),
      (0 <= v < 256)%Z ->
      rw_cells asegs mx A [CB 1 [b8 v]] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= A)%Z -> (A + 1 <= Bq + alloc)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists a3v : word,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sxb (Z_to_bv 8 v)) a1 a2 a3v (Z_to_bv 64 A) a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c754) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 A) a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c740) fc None mx (seg_rom asegs)).
  Section Sz3.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx v Bq alloc bB A : ltac2:(SecDiet.SzSec.tyM 'tsres_ldA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma tsres_ldA__body : ltac2:(SecDiet.SzSec.bodyP 'tsres_ldA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HV HB MIx BUNP INB1 INB2 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join BUNP 1%Z 0x8c750%Z [10%Z; 13%Z].
    zstep. change (b8 v) with (Z_to_bv 8 v).
    apply evtF_done. eexists. reflexivity.
  Qed.
  End Sz3.
  #[using="Type"] Lemma tsres_ldA : ltac:(let t := eval cbv delta [tsres_ldA__stmt] in tsres_ldA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx v Bq alloc bB A. ltac2:(SecDiet.SzSec.closeP 'tsres_ldA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ldu64ckA__stmt : Prop := forall (RNGx : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (mx : mem) (u0 u1 u2 u3 u4 u5 u6 u7 : Z) (Bq alloc bB A : Z),
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
      rw_cells asegs mx A [CB 8 (map b8 [u0; u1; u2; u3; u4; u5; u6; u7])] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= A)%Z -> (A + 8 <= Bq + alloc)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (a0' a3' a4' a5' t0' : word),
          ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1 a2 a3' a4' a5' a6 a7 s2 s3 (Z_to_bv 64 1) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3
                       (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val u0 u1 u2 u3 u4 u5 u6 u7)) t5 t6)
                   F (Z_to_bv 64 0x8c6cc) fc None mx (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 A) a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8c64c) fc None mx (seg_rom asegs)).
  Section Sz4.
  Variables RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx u0 u1 u2 u3 u4 u5 u6 u7 Bq alloc bB A : ltac2:(SecDiet.SzSec.tyM 'ldu64ckA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ldu64ckA__body : ltac2:(SecDiet.SzSec.bodyP 'ldu64ckA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros B0 B1 B2 B3 B4 B5 B6 B7 HV8 MIx BUNP INB1 INB2 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck_join BUNP 1%Z 0x8c65c%Z [10%Z; 13%Z].
    zstep.
    ck_join BUNP 1%Z 0x8c670%Z [10%Z; 15%Z].
    eapply evtF_cut.
    { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB.ldu64A with (A := A) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7);
        [exact MIx | lia | lia | eapply rng_sub; [exact BRNG | lia | lia] | exact B0 | exact B1 | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact HV8]. }
    cbv beta. intros ms' (a0x & a3x & a4x & a5x & t0x & ->).
    apply evtF_done. do 5 eexists. reflexivity.
  Qed.
  End Sz4.
  #[using="Type"] Lemma ldu64ckA : ltac:(let t := eval cbv delta [ldu64ckA__stmt] in ldu64ckA__stmt in exact t).
  Proof. intros RNGx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx u0 u1 u2 u3 u4 u5 u6 u7 Bq alloc bB A. ltac2:(SecDiet.SzSec.closeP 'ldu64ckA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_aiC2A.

(* [comment removed for export] *)
Module F_ngnD0A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
(* [comment removed for export] *)
Local Ltac ck_branch :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then first [ if_false | if_true ]
      else (let v := eval vm_compute in c in
            lazymatch v with true => first [ if_true | if_false ] | false => first [ if_false | if_true ] | _ => first [ if_false | if_true ] end)
  | _ => first [ if_false | if_true ]
  end.
Local Ltac ck_go ::= ck_steps 8%nat; ck_branch.
(* [comment removed for export] *)
Local Ltac ck_sh_small A1 A2 := first [ clear - A1 A2; sh_lia | sh_lia ].
Local Ltac ck0_at UNP P ::=
  ck_clear;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in let A1 := fresh "CKlo" in let A2 := fresh "CKhi" in
        assert (A1 : (lo <= P)%Z) by ck_lia;
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by ck_lia;
        pose proof (ck_full_rd m lo hi P UNP A1 A2) as RD;
        first [ let ACC := fresh "ACCsh" in
                match goal with
                | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(ck_sh_small A1 A2) ltac:(ck_sh_small A1 A2)) as ACC
                end
              | clear A1 A2; ck_fp_at lo P ];
        try clear A1 A2
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac plia_B := once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers.
Local Ltac flia ::= first [ sassumption | plia_B | assumption ].
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

  Definition ngn_epb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
           (ra' t0' t1' t2' x8 a3' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t4' t5' t6' : word) (mx : mem)
           (i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq alloc bB HA bH kHB : Z) (pre : list byte) (hj1 hj2 hj3 hj4 : list byte),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; i2; i3; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells asegs mx Bq [CB 8 pre; C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
      rw_cells asegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] -> mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (32 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      unpoisoned mx HA (HA + 24) -> (HA + 24 <= ATOP)%Z -> (HA mod 8 = 0)%Z -> (0 < HA)%Z ->
      (0 <= bH <= 1)%Z -> (HA + 24 <= 2147446784 + bH * 140737479966720)%Z -> (17594333495296 * bH <= HA)%Z -> (6303744 <= HA)%Z ->
      rng RNGx HA 24 -> rng RNGx (shad HA) (nshad 24) ->
      (0 <= kHB <= 1)%Z -> (HA + 24 <= Bq + kHB * 18446744073709551616)%Z -> (Bq + alloc <= HA + (1 - kHB) * 18446744073709551616)%Z ->
      evtF asegs RNGx (fun ms' => exists (a0v a1v a2v a4v a5v a6v a7v t0v t1v capw lenw : word) (m' : mem),
          ms' = MS (mkR ra' sp gp tp t0v t1v t2' x8 (Z_to_bv 64 2147450880) a0v a1v a2v a3' a4v a5v a6v a7v
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x8d67c) fc None m' (seg_rom asegs)
          /\ munch [(HA + 16, HA + 24)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' HA [CB 8 hj1; CB 8 hj2; C4 capw; C4 lenw]
          /\ (bv_unsigned a7v mod 2^32 = le4val i3 i2 i1 i0)%Z /\ (bv_unsigned capw mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lenw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a2v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' sp gp tp t0' t1' t2' x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 (HA + 20)) (Z_to_bv 64 (Bq + 24)) a3' (Z_to_bv 64 (HA + 16))
                 (Z_to_bv 64 (Bq + 20)) (Z_to_bv 64 1) (Z_to_bv 64 (sxv i0 i1 i2 i3))
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x8d250) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx sp gp tp F fc ra' t0' t1' t2' x8 a3' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB pre hj1 hj2 hj3 hj4 : ltac2:(SecDiet.SzSec.tyM 'ngn_epb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  Lemma ngn_epb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using .
 intros GR HB HH MI BUNP BTOP AL32 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH HUNP HTOP HA8 HA1 bHr bHhi bHlo bHimg HRNG HRSH kHBr kHB1 kHB2.
 qfold.
    pose proof atop_range as AR.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA + 16, HA + 24)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck0 BUNP; ck_go.
    ck0 HUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
    do 12 zstep. zstep.
  (* [comment removed for export] *)
  ck0_at BUNP (Bq + 24)%Z; ck_go.
  ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
  do 13 zstep. zstep.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  zstep. ck0 BUNP; ck_go. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
  do 4 zstep. zstep. rewrite (sx32_lit l0 l1 l2 l3) by lia.
    do 32 zstep.
    apply evtF_done. cbv beta.
    lazymatch goal with HX : rw_cells asegs ?mm HA [_; _; C4 ?cw; C4 ?lw] |- _ =>
      do 9 eexists; exists cw, lw, mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.bswap32_sxv_mod32; assumption|]. split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.bswap32_sxv_mod32; assumption|].
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.bswap32_sxv_mod32; assumption|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.ts_swap_wordA; assumption.
  Qed.
  End Sz1.
  Lemma ngn_epb_swapA : ltac:(let t := eval cbv delta [ngn_epb_swapA__stmt] in ngn_epb_swapA__stmt in exact t).
  Proof using . intros RNGx sp gp tp F fc ra' t0' t1' t2' x8 a3' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB pre hj1 hj2 hj3 hj4. ltac2:(SecDiet.SzSec.closeP 'ngn_epb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
(* [comment removed for export] *)
Local Ltac ck_branch :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then first [ if_false | if_true ]
      else (let v := eval vm_compute in c in
            lazymatch v with true => first [ if_true | if_false ] | false => first [ if_false | if_true ] | _ => first [ if_false | if_true ] end)
  | _ => first [ if_false | if_true ]
  end.
Local Ltac ck_go ::= ck_steps 8%nat; ck_branch.
(* [comment removed for export] *)
Local Ltac ck_sh_small A1 A2 := first [ clear - A1 A2; sh_lia | sh_lia ].
Local Ltac ck0_at UNP P ::=
  ck_clear;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in let A1 := fresh "CKlo" in let A2 := fresh "CKhi" in
        assert (A1 : (lo <= P)%Z) by ck_lia;
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by ck_lia;
        pose proof (ck_full_rd m lo hi P UNP A1 A2) as RD;
        first [ let ACC := fresh "ACCsh" in
                match goal with
                | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(ck_sh_small A1 A2) ltac:(ck_sh_small A1 A2)) as ACC
                end
              | clear A1 A2; ck_fp_at lo P ];
        try clear A1 A2
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac plia_B := once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers.
Local Ltac flia ::= first [ sassumption | plia_B | assumption ].
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

  Definition ngn_epb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
           (ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' : word) (mx : mem)
           (i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq alloc bB HA bH kHB PS : Z) (pre : list byte) (hj1 hj2 hj3 hj4 : list byte),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; i2; i3; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells asegs mx Bq [CB 8 pre; C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
      rw_cells asegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] ->
      rw_cells asegs mx (bv_unsigned sp + -200) [C8 (Z_to_bv 64 PS); C8 (Z_to_bv 64 HA)] ->      (* [comment removed for export] *)
      mem_inv asegs mx ->
      (ATOP + 4096 <= lo)%Z -> (lo + 57344 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2^47)%Z -> rng RNGx lo (bv_unsigned sp - lo) ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (32 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      unpoisoned mx HA (HA + 24) -> (HA + 24 <= ATOP)%Z -> (HA mod 8 = 0)%Z -> (0 < HA)%Z ->
      (0 <= bH <= 1)%Z -> (HA + 24 <= 2147446784 + bH * 140737479966720)%Z -> (17594333495296 * bH <= HA)%Z -> (6307840 <= HA)%Z ->
      rng RNGx HA 24 -> rng RNGx (shad HA) (nshad 24) ->
      (0 <= kHB <= 1)%Z -> (HA + 24 <= Bq + kHB * 18446744073709551616)%Z -> (Bq + alloc <= HA + (1 - kHB) * 18446744073709551616)%Z ->
      evtF asegs RNGx (fun ms' => exists (a0v a1v a2v a3v a4v a5v a6v a7v t0v capw lenw : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0v (Z_to_bv 64 PS) t2' x8 x9 a0v a1v a2v a3v a4v a5v a6v a7v
                       x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8d958) fc None m' (seg_rom asegs)
          /\ munch [(HA + 16, HA + 24)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' HA [CB 8 hj1; CB 8 hj2; C4 capw; C4 lenw]
          /\ (bv_unsigned a5v mod 2^32 = le4val i3 i2 i1 i0)%Z /\ (bv_unsigned capw mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lenw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a2v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (Bq + 8)) a1' a2' a3' a4' a5' a6' a7'
                 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8d500) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB PS pre hj1 hj2 hj3 hj4 : ltac2:(SecDiet.SzSec.tyM 'ngn_epb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  Lemma ngn_epb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using .
 intros GR HB HH FRC MI LO BU SP47 RSPW BUNP BTOP AL32 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH HUNP HTOP HA8 HA1 bHr bHhi bHlo bHimg HRNG HRSH kHBr kHB1 kHB2.
 qfold.
    pose proof atop_range as AR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA + 16, HA + 24)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    (* [comment removed for export] *)
    zstep.
    ck0 BUNP; ck_go.
    ck0 BUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
    zstep.
    ck0 HUNP; ck_go. rewrite (sx32_lit i0 i1 i2 i3) by lia.
    do 13 zstep. zstep.
    (* [comment removed for export] *)
    ck0_at BUNP (Bq + 24)%Z; ck_go.
    zstep.
    ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 13 zstep. zstep.
    (* [comment removed for export] *)
    ck0_at BUNP (Bq + 12)%Z; ck_go.
    zstep. ck0 BUNP; ck_go. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
    do 4 zstep. zstep. rewrite (sx32_lit l0 l1 l2 l3) by lia.
    do 32 zstep.
    apply evtF_done. cbv beta.
    lazymatch goal with HX : rw_cells asegs ?mm HA [_; _; C4 ?cw; C4 ?lw] |- _ =>
      do 9 eexists; exists cw, lw, mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.bswap32_sxv_mod32; assumption|]. split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.bswap32_sxv_mod32; assumption|].
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.bswap32_sxv_mod32; assumption|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.ts_swap_wordA; assumption.
  Qed.
  End Sz1.
  Lemma ngn_epb_swapA : ltac:(let t := eval cbv delta [ngn_epb_swapA__stmt] in ngn_epb_swapA__stmt in exact t).
  Proof using . intros RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB PS pre hj1 hj2 hj3 hj4. ltac2:(SecDiet.SzSec.closeP 'ngn_epb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_ngnD0A.

(* [comment removed for export] *)
Module F_ngnD1A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac plia_B := once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers.
Local Ltac flia ::= first [ sassumption | plia_B | assumption ].
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
(* [comment removed for export] *)
Lemma bswap16_lorA : forall a b, (0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor ((Z.shiftl (a + 256 * b) 8) mod 18446744073709551616) (Z.shiftr (a + 256 * b) 8) mod 65536 = b + 256 * a)%Z.
Proof. intros a b Ha Hb. replace (a + 256 * b)%Z with (le_of_bytes [a; b]) by (cbn [le_of_bytes]; lia). bswap_arith. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

  Definition ngn_pb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
           (ra' t0' t1' t2' x8 a3' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t4' t5' t6' : word) (mx : mem)
           (i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq alloc bB HA bH kHB : Z) (pre : list byte) (hj1 hj2 hj3 hj4 : list byte),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; d0; d1; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells asegs mx Bq [CB 8 pre; C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
      rw_cells asegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] -> mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (32 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      unpoisoned mx HA (HA + 24) -> (HA + 24 <= ATOP)%Z -> (HA mod 8 = 0)%Z -> (0 < HA)%Z ->
      (0 <= bH <= 1)%Z -> (HA + 24 <= 2147446784 + bH * 140737479966720)%Z -> (17594333495296 * bH <= HA)%Z -> (6303744 <= HA)%Z ->
      rng RNGx HA 24 -> rng RNGx (shad HA) (nshad 24) ->
      (0 <= kHB <= 1)%Z -> (HA + 24 <= Bq + kHB * 18446744073709551616)%Z -> (Bq + alloc <= HA + (1 - kHB) * 18446744073709551616)%Z ->
      evtF asegs RNGx (fun ms' => exists (a0v a1v a2v a4v a5v a6v a7v t0v t1v t2v capw lenw : word) (m' : mem),
          ms' = MS (mkR ra' sp gp tp t0v t1v t2v x8 (Z_to_bv 64 2147450880) a0v a1v a2v a3' a4v a5v a6v a7v
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x8d67c) fc None m' (seg_rom asegs)
          /\ munch [(HA + 16, HA + 24)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' HA [CB 8 hj1; CB 8 hj2; C4 capw; C4 lenw]
          /\ (bv_unsigned a7v mod 2^32 = i1 + 256 * i0)%Z /\ (bv_unsigned capw mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lenw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a2v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' sp gp tp t0' t1' t2' x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 (Bq + 16)) (Z_to_bv 64 (Bq + 12)) a3' (Z_to_bv 64 (Bq + 24))
                 (Z_to_bv 64 (Bq + 20)) (Z_to_bv 64 1) (Z_to_bv 64 (i0 + 256 * i1))
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x8d40c) fc None mx (seg_rom asegs)).
  Section Sz2.
  Variables RNGx sp gp tp F fc ra' t0' t1' t2' x8 a3' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB pre hj1 hj2 hj3 hj4 : ltac2:(SecDiet.SzSec.tyM 'ngn_pb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  Lemma ngn_pb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc RNGx sp gp tp F fc ra' t0' t1' t2' x8 a3' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB pre hj1 hj2 hj3 hj4.
 intros GR HB HH MI BUNP BTOP AL32 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH HUNP HTOP HA8 HA1 bHr bHhi bHlo bHimg HRNG HRSH kHBr kHB1 kHB2.
 qfold.
    pose proof atop_range as AR.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA + 16, HA + 24)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck0 BUNP; ck_go.
  zstep. ck0 HUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
  do 12 zstep. zstep.
  ck0_at BUNP (Bq + 24)%Z; ck_go.
  zstep. ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
  do 12 zstep. zstep.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  ck0 BUNP; ck_go. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
  do 2 zstep. zstep. rewrite (sx32_lit l0 l1 l2 l3) by lia.
  do 30 zstep.
    apply evtF_done. cbv beta.
    lazymatch goal with HX : rw_cells asegs ?mm HA [_; _; C4 ?cw; C4 ?lw] |- _ =>
      do 10 eexists; exists cw, lw, mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [rewrite (bswap16_lorA i0 i1) by lia; rewrite unsigned_lit by lia; apply Z.mod_small; lia|].
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.bswap32_sxv_mod32; assumption|].
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.bswap32_sxv_mod32; assumption|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.ts_swap_wordA; assumption.
  Qed.
  End Sz2.
  Lemma ngn_pb_swapA : ltac:(let t := eval cbv delta [ngn_pb_swapA__stmt] in ngn_pb_swapA__stmt in exact t).
  Proof using rc. intros RNGx sp gp tp F fc ra' t0' t1' t2' x8 a3' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB pre hj1 hj2 hj3 hj4. ltac2:(SecDiet.SzSec.closeP 'ngn_pb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac plia_B := once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers.
Local Ltac flia ::= first [ sassumption | plia_B | assumption ].
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bswap16_lorA : forall a b, (0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor ((Z.shiftl (a + 256 * b) 8) mod 18446744073709551616) (Z.shiftr (a + 256 * b) 8) mod 65536 = b + 256 * a)%Z.
Proof. intros a b Ha Hb. replace (a + 256 * b)%Z with (le_of_bytes [a; b]) by (cbn [le_of_bytes]; lia). bswap_arith. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

  Definition ngn_pb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
           (ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' : word) (mx : mem)
           (i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq alloc bB HA bH kHB PS : Z) (pre : list byte) (hj1 hj2 hj3 hj4 : list byte),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; d0; d1; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells asegs mx Bq [CB 8 pre; C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
      rw_cells asegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] ->
      rw_cells asegs mx (bv_unsigned sp + -200) [C8 (Z_to_bv 64 PS); C8 (Z_to_bv 64 HA)] ->      (* [comment removed for export] *)
      mem_inv asegs mx ->
      (ATOP + 4096 <= lo)%Z -> (lo + 57344 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2^47)%Z -> rng RNGx lo (bv_unsigned sp - lo) ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (32 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      unpoisoned mx HA (HA + 24) -> (HA + 24 <= ATOP)%Z -> (HA mod 8 = 0)%Z -> (0 < HA)%Z ->
      (0 <= bH <= 1)%Z -> (HA + 24 <= 2147446784 + bH * 140737479966720)%Z -> (17594333495296 * bH <= HA)%Z -> (6307840 <= HA)%Z ->
      rng RNGx HA 24 -> rng RNGx (shad HA) (nshad 24) ->
      (0 <= kHB <= 1)%Z -> (HA + 24 <= Bq + kHB * 18446744073709551616)%Z -> (Bq + alloc <= HA + (1 - kHB) * 18446744073709551616)%Z ->
      evtF asegs RNGx (fun ms' => exists (a0v a1v a2v a3v a4v a5v a6v a7v capw lenw : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' (Z_to_bv 64 PS) t2' x8 x9 a0v a1v a2v a3v a4v a5v a6v a7v
                       x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8d958) fc None m' (seg_rom asegs)
          /\ munch [(HA + 16, HA + 24)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' HA [CB 8 hj1; CB 8 hj2; C4 capw; C4 lenw]
          /\ (bv_unsigned a5v mod 2^32 = i1 + 256 * i0)%Z /\ (bv_unsigned capw mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lenw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a2v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (Bq + 8)) a1' a2' a3' a4' a5' a6' a7'
                 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8d334) fc None mx (seg_rom asegs)).
  Section Sz2.
  Variables RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB PS pre hj1 hj2 hj3 hj4 : ltac2:(SecDiet.SzSec.tyM 'ngn_pb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  Lemma ngn_pb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB PS pre hj1 hj2 hj3 hj4.
 intros GR HB HH FRC MI LO BU SP47 RSPW BUNP BTOP AL32 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH HUNP HTOP HA8 HA1 bHr bHhi bHlo bHimg HRNG HRSH kHBr kHB1 kHB2.
 qfold.
    pose proof atop_range as AR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA + 16, HA + 24)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    (* [comment removed for export] *)
    zstep.
    ck0 BUNP; ck_go.
    ck0 BUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
    zstep.
    ck0 HUNP; ck_go. rewrite (zx16_lit (i0 + 256 * i1)) by lia.
    do 13 zstep. zstep.
    (* [comment removed for export] *)
    ck0_at BUNP (Bq + 24)%Z; ck_go.
    zstep.
    ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 13 zstep. zstep.
    (* [comment removed for export] *)
    ck0_at BUNP (Bq + 12)%Z; ck_go.
    zstep. ck0 BUNP; ck_go. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
    do 2 zstep. zstep. rewrite (sx32_lit l0 l1 l2 l3) by lia.
    do 31 zstep.
    apply evtF_done. cbv beta.
    lazymatch goal with HX : rw_cells asegs ?mm HA [_; _; C4 ?cw; C4 ?lw] |- _ =>
      do 8 eexists; exists cw, lw, mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [rewrite (bswap16_lorA i0 i1) by lia; rewrite unsigned_lit by lia; apply Z.mod_small; lia|].
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.bswap32_sxv_mod32; assumption|].
    split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.bswap32_sxv_mod32; assumption|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.ts_swap_wordA; assumption.
  Qed.
  End Sz2.
  Lemma ngn_pb_swapA : ltac:(let t := eval cbv delta [ngn_pb_swapA__stmt] in ngn_pb_swapA__stmt in exact t).
  Proof using rc. intros RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq alloc bB HA bH kHB PS pre hj1 hj2 hj3 hj4. ltac2:(SecDiet.SzSec.closeP 'ngn_pb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_ngnD1A.

(* [comment removed for export] *)
Module F_ngnQ2A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.
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

(* [comment removed for export] *)
Lemma ts_wordA : forall h0 h1 h2 h3 l0 l1 l2 l3,
  (0 <= h0 < 256 -> 0 <= h1 < 256 -> 0 <= h2 < 256 -> 0 <= h3 < 256 -> 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64 (Z.lor ((Z.shiftl (sxv h0 h1 h2 h3 mod 18446744073709551616) 32) mod 18446744073709551616) (le4val l0 l1 l2 l3 mod 18446744073709551616))
  = Z_to_bv 64 (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3))%Z.
Proof.
  intros h0 h1 h2 h3 l0 l1 l2 l3 A0 A1 A2 A3 B0 B1 B2 B3. f_equal.
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.sxv_lanes h0 h1 h2 h3) by lia.
  replace (le4val l0 l1 l2 l3 mod 18446744073709551616)%Z with (le_of_bytes [l0; l1; l2; l3]) by (unfold le4val; cbn [le_of_bytes]; rewrite Z.mod_small by lia; lia).
  repeat lanes_step. cbn [le_of_bytes]. unfold le4val. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ts_wordA : forall h0 h1 h2 h3 l0 l1 l2 l3,
  (0 <= h0 < 256 -> 0 <= h1 < 256 -> 0 <= h2 < 256 -> 0 <= h3 < 256 -> 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64 (Z.lor ((Z.shiftl (sxv h0 h1 h2 h3 mod 18446744073709551616) 32) mod 18446744073709551616) (le4val l0 l1 l2 l3 mod 18446744073709551616))
  = Z_to_bv 64 (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3))%Z.
Proof.
  intros h0 h1 h2 h3 l0 l1 l2 l3 A0 A1 A2 A3 B0 B1 B2 B3. f_equal.
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.sxv_lanes h0 h1 h2 h3) by lia.
  replace (le4val l0 l1 l2 l3 mod 18446744073709551616)%Z with (le_of_bytes [l0; l1; l2; l3]) by (unfold le4val; cbn [le_of_bytes]; rewrite Z.mod_small by lia; lia).
  repeat lanes_step. cbn [le_of_bytes]. unfold le4val. lia.
Qed.
End TwB.
End F_ngnQ2A.

(* [comment removed for export] *)
Module F_ngnS0A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

  Definition ngn_shb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
           (ra' t0' t1' t2' x8 a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' : word) (mx : mem)
           (g0 g1 g2 g3 j0 j1 : Z) (Bq alloc bB : Z) (pre : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; j0; j1] ->
      rw_cells asegs mx Bq ([CB 8 pre; C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1))] ++ rest) ->
      rw_cells asegs mx (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)] ->
      mem_inv asegs mx ->
      (ATOP + 4096 <= lo)%Z -> (lo + 57344 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2^47)%Z -> rng RNGx lo (bv_unsigned sp - lo) ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (16 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (a1v a2v a3v a4v : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Bq + 12)) a1v a2v a3v a4v
                       (Z_to_bv 64 65280) a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8cd54) fc None m' (seg_rom asegs)
          /\ munch [(Bq + 8, Bq + 14)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' Bq ([CB 8 pre; C4 a2v; C2 a1v] ++ rest)
          /\ (bv_unsigned a2v mod 2^32 = le4val g3 g2 g1 g0)%Z /\ (bv_unsigned a1v = j1 + 256 * j0 + 65536 * j1)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Bq + 12)) (Z_to_bv 64 (Bq + 8))
                 (Z_to_bv 64 (sxv g0 g1 g2 g3)) (Z_to_bv 64 (Z.shiftr (Bq + 8) 3 + 2147450880)) a4'
                 a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8ccf4) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq alloc bB pre rest : ltac2:(SecDiet.SzSec.tyM 'ngn_shb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ngn_shb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros GR HB FRC MI LO BU SP47 RSPW BUNP BTOP AL16 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH.
 qfold.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 14)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ck0_at BUNP (Bq + 8)%Z; ck_go.
  do 11 zstep.
  zstep.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  ck0_at BUNP (Bq + 12)%Z; ck_go.
  rewrite (zx16_lit (j0 + 256 * j1)) by lia.
  do 3 zstep. zstep.
  apply evtF_done. cbv beta.
  lazymatch goal with HX : rw_cells asegs ?mm Bq (CB 8 pre :: C4 ?w1 :: C2 ?w2 :: _) |- _ =>
    exists w2, w1; do 2 eexists; exists mm; split; [reflexivity|];
    split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
  split.
  - rewrite unsigned_lit_wrap. change (2^64) with 18446744073709551616.
    rewrite Z.mod_mod_divide by (exists (2^32); reflexivity).
    replace (sxv g0 g1 g2 g3 mod 18446744073709551616) with (bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [g0; g1; g2; g3])))).
    2:{ replace (le_of_bytes [g0; g1; g2; g3]) with (le4val g0 g1 g2 g3) by (unfold le4val; cbn [le_of_bytes]; lia).
        rewrite unsigned_sx32 by lia. symmetry. apply Z.mod_small. unfold sxv, le4val. Z.div_mod_to_equations; lia. }
    unfold le4val. bswap_arith.
  - replace (j0 + 256 * j1) with (le_of_bytes [j0; j1]) by (cbn [le_of_bytes]; lia).
    repeat lanes_step. rewrite unsigned_lit by (cbn [le_of_bytes]; lia). cbn [le_of_bytes]. lia.
  Qed.
  End Sz1.
  #[using="Type"] Lemma ngn_shb_swapA : ltac:(let t := eval cbv delta [ngn_shb_swapA__stmt] in ngn_shb_swapA__stmt in exact t).
  Proof. intros RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq alloc bB pre rest. ltac2:(SecDiet.SzSec.closeP 'ngn_shb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

  Definition ngn_shb_swapA__stmt : Prop := forall (RNGx : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
           (ra' t0' t1' t2' x8 x9 a2' a3' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' : word) (mx : mem)
           (g0 g1 g2 g3 j0 j1 : Z) (Bq alloc bB : Z) (pre : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; j0; j1] ->
      rw_cells asegs mx Bq ([CB 8 pre; C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1))] ++ rest) ->
      rw_cells asegs mx (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)] ->
      mem_inv asegs mx ->
      (ATOP + 4096 <= lo)%Z -> (lo + 57344 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2^47)%Z -> rng RNGx lo (bv_unsigned sp - lo) ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq + alloc <= ATOP)%Z -> (16 <= alloc)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (a4v a5v a6v w4 : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 (Bq + 12)) a2' a3' a4v
                       a5v a6v (Z_to_bv 64 65280) x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8cf10) fc None m' (seg_rom asegs)
          /\ munch [(Bq + 8, Bq + 14)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' Bq ([CB 8 pre; C4 w4; C2 a4v] ++ rest)
          /\ (bv_unsigned w4 mod 2^32 = le4val g3 g2 g1 g0)%Z /\ (bv_unsigned a4v = j1 + 256 * j0 + 65536 * j1)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 (Bq + 12)) a2' a3'
                 (Z_to_bv 64 (sxv g0 g1 g2 g3)) a5' a6' a7'
                 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F (Z_to_bv 64 0x8ceb8) fc None mx (seg_rom asegs)).
  Section Sz1.
  Variables RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a2' a3' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq alloc bB pre rest : ltac2:(SecDiet.SzSec.tyM 'ngn_shb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma ngn_shb_swapA__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb_swapA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros GR HB FRC MI LO BU SP47 RSPW BUNP BTOP AL16 B2 B1 bBr bBhi bBlo bBimg BRNG BRSH.
 qfold.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 14)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    do 11 zstep.
    zstep.
    ck0_at BUNP (Bq + 12)%Z; ck_go.
    ck0_at BUNP (Bq + 12)%Z; ck_go.
    rewrite (zx16_lit (j0 + 256 * j1)) by lia.
    do 3 zstep. zstep.
    apply evtF_done. cbv beta.
    lazymatch goal with HX : rw_cells asegs ?mm Bq (CB 8 pre :: C4 ?w1 :: C2 ?w2 :: _) |- _ =>
      exists w2; do 2 eexists; exists w1, mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split.
    - rewrite unsigned_lit_wrap. change (2^64) with 18446744073709551616.
      rewrite Z.mod_mod_divide by (exists (2^32); reflexivity).
      replace (sxv g0 g1 g2 g3 mod 18446744073709551616) with (bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [g0; g1; g2; g3])))).
      2:{ replace (le_of_bytes [g0; g1; g2; g3]) with (le4val g0 g1 g2 g3) by (unfold le4val; cbn [le_of_bytes]; lia).
          rewrite unsigned_sx32 by lia. symmetry. apply Z.mod_small. unfold sxv, le4val. Z.div_mod_to_equations; lia. }
      unfold le4val. bswap_arith.
    - replace (j0 + 256 * j1) with (le_of_bytes [j0; j1]) by (cbn [le_of_bytes]; lia).
      repeat lanes_step. rewrite unsigned_lit by (cbn [le_of_bytes]; lia). cbn [le_of_bytes]. lia.
  Qed.
  End Sz1.
  #[using="Type"] Lemma ngn_shb_swapA : ltac:(let t := eval cbv delta [ngn_shb_swapA__stmt] in ngn_shb_swapA__stmt in exact t).
  Proof. intros RNGx sp gp tp F fc lo ra' t0' t1' t2' x8 x9 a2' a3' a5' a6' a7' x18 x19 x20 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq alloc bB pre rest. ltac2:(SecDiet.SzSec.closeP 'ngn_shb_swapA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_ngnS0A.

(* [comment removed for export] *)
Module F_sfnp_swapA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition np_swap_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (HB : Z) (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 : Z),
    mem_inv asegs m -> (0 <= HB)%Z -> (HB + 16 < 2^64)%Z -> rng RNG HB 16 ->
    Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15] ->
    rw_cells asegs m HB [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))] ->
    evtF asegs RNG (fun ms' => exists cw sw uw a3v lw a5v a6v a7v t0v : word,
        ms' = MS (mkR ra sp gp tp t0v t1 t2 s0 s1 cw sw uw a3v lw a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 HB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x88448) fc None m (seg_rom asegs)
        /\ (bv_unsigned cw mod 2^32 = le4val g11 g10 g9 g8)%Z /\ (bv_unsigned sw mod 2^32 = le4val g3 g2 g1 g0)%Z
        /\ (bv_unsigned uw mod 2^32 = le4val g7 g6 g5 g4)%Z /\ (bv_unsigned lw mod 2^32 = le4val g15 g14 g13 g12)%Z)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sx32 (Z_to_bv 64 (le4val g8 g9 g10 g11))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 HB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x883a4) fc None m (seg_rom asegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 : ltac2:(SecDiet.SzSec.tyM 'np_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma np_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI HB0 HBT RH GR FRH.
  qfold.
  pose proof GR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 41 zstep.
  apply evtF_done. do 9 eexists. split; [reflexivity|].
  assert (SW : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
    (bv_unsigned (Z_to_bv 64
      (Z.lor (Z.lor (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 (le4val a b c d)))) 24 mod 18446744073709551616)
                    (Z.shiftl (Z.land (bv_unsigned (sx32 (Z_to_bv 64 (le4val a b c d)))) 65280) 8 mod 18446744073709551616))
             (Z.lor (Z.land (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 (le4val a b c d)))) 8) 65280)
                    (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 (Z_to_bv 64 (le4val a b c d))))) 24) mod 18446744073709551616)))) mod 2^32
     = le4val d c b a)%Z).
  { intros a b c d Ha Hb Hc Hd.
    rewrite (swap32_valA (sx32 (Z_to_bv 64 (le4val a b c d))) a b c d ((d / 128) * 4294967295));
      [ unfold le4val; Z.div_mod_to_equations; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia
      | rewrite unsigned_sx32 by (unfold le4val; lia); unfold sxv, le4val; lia ]. }
  repeat split; apply SW; lia.
Qed.
End Sz1.
#[using="Type"] Lemma np_swap_seq : ltac:(let t := eval cbv delta [np_swap_seq__stmt] in np_swap_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15. ltac2:(SecDiet.SzSec.closeP 'np_swap_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.
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

Section CANSEC1. Context {rc : runConstT}.
Definition np_swap_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (HB HA bH : Z) (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 : Z) (hj1 hj2 hj3 hj4 : list byte),
    mem_inv asegs m -> (0 <= HB)%Z -> (HB + 16 < 2^64)%Z -> rng RNG HB 16 ->
    Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15] ->
    rw_cells asegs m HB [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))] ->
    rw_cells asegs m HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] ->
    unpoisoned m HA (HA + 24) -> (HA + 24 <= ATOP)%Z -> (HA mod 8 = 0)%Z -> (0 < HA)%Z ->
    (0 <= bH <= 1)%Z -> (HA + 24 <= 2147446784 + bH * 140737479966720)%Z -> (17594333495296 * bH <= HA)%Z -> (6307840 <= HA)%Z ->
    rng RNG HA 24 -> rng RNG (shad HA) (nshad 24) ->
    (HA + 24 <= HB \/ HB + 16 <= HA)%Z ->
    evtF asegs RNG (fun ms' => exists (a1v a3v a4v a5v a6v capw lenw : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (HA + 20)) a1v (Z_to_bv 64 0) a3v a4v a5v a6v a7
                      (Z_to_bv 64 (HA + 16)) s3 s4 s5 (Z_to_bv 64 HB) s7 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x888f8) fc None m' (seg_rom asegs)
        /\ munch [(HA, HA + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' HA [C8 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C8 (Z_to_bv 64 (le4val g7 g6 g5 g4)); C4 capw; C4 lenw]
        /\ (bv_unsigned capw mod 2^32 = le4val g11 g10 g9 g8)%Z /\ (bv_unsigned lenw mod 2^32 = le4val g15 g14 g13 g12)%Z)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (HA + 20)) (Z_to_bv 64 (sxv g8 g9 g10 g11)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
               (Z_to_bv 64 (HA + 16)) s3 s4 s5 (Z_to_bv 64 HB) s7 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x887e0) fc None m (seg_rom asegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s7 s10 s11 t3 t4 t5 t6 F fc m RNG HB HA bH g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 hj1 hj2 hj3 hj4 : ltac2:(SecDiet.SzSec.tyM 'np_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma np_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI HB0 HBT RH GR FRH HH HUNP HTOP HA8 HA1 bHr bHhi bHlo bHimg HRNG HRSH DHB.
 qfold.
  pose proof atop_range as AR.
  pose proof GR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
  pose proof (munch_refl [(HA, HA + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SW : forall (w : word) a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z -> bv_unsigned w = sxv a b c d ->
    (bv_unsigned (Z_to_bv 64
      (Z.lor (Z.lor (Z.shiftl (bv_unsigned w) 24 mod 18446744073709551616)
                    (Z.shiftl (Z.land (bv_unsigned w) 65280) 8 mod 18446744073709551616))
             (Z.lor (Z.land (Z.shiftr (bv_unsigned w) 8) 65280)
                    (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24) mod 18446744073709551616)))) mod 2^32
     = le4val d c b a)%Z).
  { intros w a b c d Ha Hb Hc Hd E.
    rewrite (swap32_valA w a b c d ((d / 128) * 4294967295));
      [ unfold le4val; Z.div_mod_to_equations; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia
      | rewrite E; unfold sxv, le4val; lia ]. }
  remember (Z_to_bv 64 (sxv g8 g9 g10 g11)) as w2 eqn:Ew2.
  assert (U2 : bv_unsigned w2 = sxv g8 g9 g10 g11) by (subst w2; apply unsigned_lit; unfold sxv, le4val; Z.div_mod_to_equations; lia).
  clear Ew2.
  ub_null.
  zstep. if_false.
  ck0 HUNP; ck_go.
  do 12 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] =>
    remember (Z_to_bv 64 (Z.lor (Z.lor a b) (Z.lor c d))) as W2 eqn:EW2 end.
  assert (SW2 : (bv_unsigned W2 mod 2^32 = le4val g11 g10 g9 g8)%Z) by (subst W2; apply SW; [lia|lia|lia|lia|exact U2]).
  clear EW2.
  zstep.
  ck0_at HUNP (HA + 20)%Z; ck_go.
  remember (sx32 (Z_to_bv 64 (le4val g12 g13 g14 g15))) as w3 eqn:Ew3.
  assert (U3 : bv_unsigned w3 = sxv g12 g13 g14 g15) by (subst w3; apply unsigned_sx32; lia).
  clear Ew3.
  do 10 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] =>
    remember (Z_to_bv 64 (Z.lor (Z.lor a b) (Z.lor c d))) as W3 eqn:EW3 end.
  assert (SW3 : (bv_unsigned W3 mod 2^32 = le4val g15 g14 g13 g12)%Z) by (subst W3; apply SW; [lia|lia|lia|lia|exact U3]).
  clear EW3.
  zstep.
  ck0_at HUNP HA; ck_go.
  zstep.
  remember (sx32 (Z_to_bv 64 (le4val g0 g1 g2 g3))) as w0 eqn:Ew0.
  assert (U0 : bv_unsigned w0 = sxv g0 g1 g2 g3) by (subst w0; apply unsigned_sx32; lia).
  clear Ew0.
  do 12 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] =>
    remember (Z_to_bv 64 (Z.lor (Z.lor a b) (Z.lor c d))) as W0 eqn:EW0 end.
  assert (SW0 : (bv_unsigned W0 mod 2^32 = le4val g3 g2 g1 g0)%Z) by (subst W0; apply SW; [lia|lia|lia|lia|exact U0]).
  clear EW0.
  do 3 zstep. zstep.
  ck0_at HUNP (HA + 8)%Z; ck_go.
  zstep.
  remember (sx32 (Z_to_bv 64 (le4val g4 g5 g6 g7))) as w1 eqn:Ew1.
  assert (U1 : bv_unsigned w1 = sxv g4 g5 g6 g7) by (subst w1; apply unsigned_sx32; lia).
  clear Ew1.
  do 9 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] =>
    remember (Z_to_bv 64 (Z.lor (Z.lor a b) (Z.lor c d))) as W1 eqn:EW1 end.
  assert (SW1 : (bv_unsigned W1 mod 2^32 = le4val g7 g6 g5 g4)%Z) by (subst W1; apply SW; [lia|lia|lia|lia|exact U1]).
  clear EW1.
  do 2 zstep. zstep.
  change (2 ^ 32)%Z with 4294967296%Z in SW0, SW1, SW2, SW3.
  rewrite SW0, SW1 in HH.
  apply evtF_done. do 8 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HH|]. split; [exact SW2 | exact SW3].
Qed.
End Sz1.
#[using="Type"] Lemma np_swap_seq : ltac:(let t := eval cbv delta [np_swap_seq__stmt] in np_swap_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s7 s10 s11 t3 t4 t5 t6 F fc m RNG HB HA bH g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 hj1 hj2 hj3 hj4. ltac2:(SecDiet.SzSec.closeP 'np_swap_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_sfnp_swapA.
