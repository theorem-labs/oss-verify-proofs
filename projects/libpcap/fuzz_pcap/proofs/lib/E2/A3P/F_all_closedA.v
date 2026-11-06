(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA Pcap_iface_ngA Pcap_iface_ppA Fuzz_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pp_mainA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_next_ex_allA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fmt_errmsgA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_failA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_hdrA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_aiKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnIA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_fsegA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_fopenA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_btfA__A3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ALL.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  (* [comment removed for export] *)
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOL : fo_leaf_laws FO.
  (* [comment removed for export] *)
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.
  Hypothesis SETSH00 : set_shadow_stmt 0x58268 0x00.
  (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis CALLOC : calloc_stmt_o HO GIOA TP.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis CPC : (~ (ACLIENT_LO <= tp_cpc TP < ACLIENT_HI))%Z.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  (* [comment removed for export] *)
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FILENO : fileno_stmt_o HO GIOA.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis CLOSE : close_stmt_o GIOA.
  Hypothesis MKSTEMP : mkstemp_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis VSNPRINTF : vsnprintf_spec_stmt GIOA.
  Hypothesis STRLEN : strlen_stmt GIOA.
  Hypothesis STRERROR_R : strerror_r_stmt GIOA.

  Local Ltac close thm := eapply thm; eassumption.
  (* [comment removed for export] *)
  Local Ltac close_s thm := eapply thm; first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].

  Let PP : post_process_stmt := F_pp_mainA.post_process_proof.
  Let MAXSNAP : max_snaplen_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_pureA.max_snaplen_proofA.
  Let ADJSNAP : adjust_snapshot_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_pureA.adjust_snapshot_proofA.
  Let LT2DLT : linktype_to_dlt_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_pureA.linktype_to_dlt_proofA.
  Let ONESHOT : oneshot_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.F_oneshotA.oneshot_proofA.
  Let STRERROR : pcap_strerror_stmt GIOA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_errA.pcap_strerror_proofA. Qed.
  Let FMT : fmt_errmsg_stmt FO GIOA. Proof. close @F_fmt_errmsgA.fmt_errmsg_proofA. Qed.
  Let OPEN_COMMON : open_offline_common_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.F_pcap_openA.open_offline_common_proofA. Qed.
  Let CHK_PCAP : pcap_check_header_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfpcap_chk_allA.pcap_check_header_allA. Qed.
  Let RBLK : read_block_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_mainA.read_block_proofA. Qed.
  Let ADDIF : add_interface_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiKA__A3P.F_aiMA.add_interface_proofA. Qed.
  Let RBYTES : read_bytes_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngrbA.read_bytes_proofA. Qed.
  Let CHK_NG : pcap_ng_check_header_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_allA.pcap_ng_check_header_proofA. Qed.
  Let NP_NG : pcap_ng_next_packet_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnMA.pcap_ng_next_packet_proofA. Qed.
  Let NP_PCAP : pcap_next_packet_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_mainA.pcap_next_packet_proofA. Qed.
  Let FOPEN_OFFLINE : fopen_offline_stmt HO FO sites GIOA TP. Proof. close @F_pcap_fopenA.fopen_offline_proofA. Qed.
  Let POPEN : pcap_open_offline_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A.open_offline_proofA. Qed.
  Let PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.F_next_ex_allA.pcap_next_ex_closedA. Qed.
  Let PSTATS : pcap_stats_stmt GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.pcap_stats_proofA. Qed.
  Let PCLOSE : pcap_close_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_close_allA.pcap_close_closedA. Qed.

  Theorem fuzz_one_closedA : fuzz_one_stmt HO FO sites GIOA TP.
  Proof using CLOSE EQB FOL FPRINTF_DD FPRINTF_S FWRITE MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE UNLINK. close_s @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_mainA.fuzz_one_proofA. Qed.
End ALL.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_ngnMA.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ALL.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  (* [comment removed for export] *)
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOL : fo_leaf_laws FO.
  (* [comment removed for export] *)
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt SET_SHADOW_F8 0xf8.
  Hypothesis SETSH00 : set_shadow_stmt SET_SHADOW_00 0x00.
  (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis CALLOC : calloc_stmt_o HO GIOA TP.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis CPC : (~ (ACLIENT_LO <= tp_cpc TP < ACLIENT_HI))%Z.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  (* [comment removed for export] *)
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FILENO : fileno_stmt_o HO GIOA.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis CLOSE : close_stmt_o GIOA.
  Hypothesis MKSTEMP : mkstemp_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis VSNPRINTF : vsnprintf_spec_stmt GIOA.
  Hypothesis STRLEN : strlen_stmt GIOA.
  Hypothesis STRERROR_R : strerror_r_stmt GIOA.

  Local Ltac close thm := eapply thm; eassumption.
  (* [comment removed for export] *)
  Local Ltac close_s thm := eapply thm; first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].

  Let PP : post_process_stmt := A3P.F_pp_mainA.TwB.post_process_proof.
  Let MAXSNAP : max_snaplen_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_pureA.TwB.max_snaplen_proofA.
  Let ADJSNAP : adjust_snapshot_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_pureA.TwB.adjust_snapshot_proofA.
  Let LT2DLT : linktype_to_dlt_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_pureA.TwB.linktype_to_dlt_proofA.
  Let ONESHOT : oneshot_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.F_oneshotA.TwB.oneshot_proofA.
  Let STRERROR : pcap_strerror_stmt GIOA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_errA.TwB.pcap_strerror_proofA. Qed.
  Let FMT : fmt_errmsg_stmt FO GIOA. Proof. close @A3P.F_fmt_errmsgA.TwB.fmt_errmsg_proofA. Qed.
  Let OPEN_COMMON : open_offline_common_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.F_pcap_openA.TwB.open_offline_common_proofA. Qed.
  Let CHK_PCAP : pcap_check_header_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfpcap_chk_allA.TwB.pcap_check_header_allA. Qed.
  Let RBLK : read_block_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_mainA.TwB.read_block_proofA. Qed.
  Let ADDIF : add_interface_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiKA__A3P.F_aiMA.TwB.add_interface_proofA. Qed.
  Let RBYTES : read_bytes_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngrbA.TwB.read_bytes_proofA. Qed.
  Let CHK_NG : pcap_ng_check_header_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_allA.TwB.pcap_ng_check_header_proofA. Qed.
  Let NP_NG : pcap_ng_next_packet_stmt HO FO sites GIOA TP. Proof. close @B3P.F_ngnMA.pcap_ng_next_packet_proofA. Qed.
  Let NP_PCAP : pcap_next_packet_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_mainA.TwB.pcap_next_packet_proofA. Qed.
  Let FOPEN_OFFLINE : fopen_offline_stmt HO FO sites GIOA TP. Proof. close @A3P.F_pcap_fopenA.TwB.fopen_offline_proofA. Qed.
  Let POPEN : pcap_open_offline_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A.TwB.open_offline_proofA. Qed.
  Let PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.F_next_ex_allA.TwB.pcap_next_ex_closedA. Qed.
  Let PSTATS : pcap_stats_stmt GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB.pcap_stats_proofA. Qed.
  Let PCLOSE : pcap_close_stmt HO FO sites GIOA TP. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_close_allA.TwB.pcap_close_closedA. Qed.

  Theorem fuzz_one_closedA : fuzz_one_stmt HO FO sites GIOA TP.
  Proof using CLOSE EQB FOL FPRINTF_DD FPRINTF_S FWRITE MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE UNLINK. close_s @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_mainA.TwB.fuzz_one_proofA. Qed.
End ALL.
End CANSEC1.
End TwB.
