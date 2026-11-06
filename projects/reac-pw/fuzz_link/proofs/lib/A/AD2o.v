(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the driver-part bindings of cgif c8557374ad2e lib/A/AD2o.v:28-60; the closing (tfib_srealizesX_rc, TFIB_T) is lib/A/PcapClose.v (comp). Ported for libreac/fuzz_pcap's ASan build: module paths changed; B := PcapB and HB := PcapB_syms (A/AD2l.v, donor AD2o.v:30-31); the driver's stdio parts are bound as the donor binds them (AD2o.v:41, 49-62), to A/AD1k.v xst / est / tfib_xst_frame / tfib_est_img / tfib_est_frame (a Theorem Labs lane's generated data half), A/AD1kSites.v tfib_fwrite_site / tfib_refused_site, A/AD1o.v tfib_printf_first / tfib_printf_next, A/AD1l.v tfib_fprintf_open_site / _rderr_site / _usage_site at fuzz_pcap's formats 0x1d858 / 0x1d86d / 0x15903 (donor 0x1d961 / 0x1d73c / 0x15935) and A/AD1j.v tfib_exit_site; they are applied to A/PcapDriver.v DRV_MAINX (donor AD1q.v:77-78), whose program contract is pcap's (PcapEntryA.tfib_lib_contract_x_all_A at SK := pcap_drv_SK, KS := pcap_KS). What the donor closes here from cgif's own program and allocator (AD2o.v:33-39 wfn / TNEWGIFX / TADDFX / TCLOSEX, AD2o.v:42-46 AMALLOC / AFREE / AICPY / LIBX := tfib_lib_x_all) is not fuzz_pcap's: these four parts are the premises of pcap_H_DRIVER, in the shape of PcapClose.v's H_DRIVER (rows 8-11). RLO / RHI / RO_IN (AD2o.v:45, 47) are fixed inside pcap's program contract (PCAP_RLO / PCAP_RHI) and MT_FREE (AD2o.v:49) is bound in PcapDriver.v. HD (AD2o.v:32) served only the allocator closings and is not needed. ARDCHK is the donor's Let (AD2o.v:48 tfib_ARDCHK B HB), from lib/A/AD2m.v (handed from a Theorem Labs lane to this lane 2026-10-29), so pcap_H_DRIVER has PcapClose.v's H_DRIVER premises only. rule 24: no function proved anew. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK15 YK18 YA02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1h.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1kSites AD1l AD1o AD1j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD1u.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import LinkDriver AD2m LinkDrvDepot LinkDrvExitF LinkDrvExitFT LinkDrvExitFH2 LinkDrvExitFP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance ZTraceSpec.checksum_shape.
Open Scope Z_scope.
Section b.
Let B : asyms := PcapB.
Let HB : PcapSyms B := PcapB_syms.
(* donor AD2o.v:48 Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB (lib/A/AD2m.v). *)
Let ARDCHK : forall rc : YM05.RunCeil, aread_check_stmt (rc:=rc) B := fun rc => tfib_ARDCHK (rc:=rc) B HB.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : forall fx : YK11.FPState, printf_first_tfa (fx := fx) B xst := fun fx => tfib_printf_first (fx := fx) B HB LAWS HB.
Let PFN : forall fx : YK11.FPState, printf_next_tfa (fx := fx) B xst := fun fx => tfib_printf_next (fx := fx) B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d858 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d86d (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x15903 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : forall fx : YK11.FPState, exit_site_tfa (fx := fx) B est xst := fun fx => tfib_exit_site (fx := fx) B HB LAWS.
(* donor AD2o.v:63-73 tfib_srealizesX_rc, cut at the driver: AD1q.v:77-78 DRV_MAINX at the parts above, with the
   four parts the donor closes from cgif's program and allocator taken as premises. *)
Lemma link_drv_mainX_rc :
  (forall fx : YK11.FPState, @amalloc_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc tfibsegs PcapB OCpy (pc_wrap_memcpy (as_code PcapB))) ->
  tfib_lib_contract_xf_all_A (rc:=rc) link_drv_SK PcapB ameter_triv (fun _ => 0) (fun _ => 0) ->
  drv_mainX_stmt (rc:=rc).
Proof.
intros AMALLOC AFREE AICPY LIBX.
exact (DRV_MAINX B HB (AMALLOC _) AFREE (AICPY _) (ARDCHK rc) LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
(fun fx => tfib_exit_file (fx := fx) B xst (exf_head_link (fx := fx)) (exf_loop_pend_link (fx := fx)) (exf_tail_link (fx := fx) B)) link_wroom).
Qed.
End RC.
(* PcapClose.v:163-170 H_DRIVER at B := PcapB, SK := pcap_drv_SK, KS := pcap_KS, HS_TBL := HS_tfib, TFIB_TBL := TFIB
   (its drv_mainA is PcapDriver.v drv_mainX_stmt there). *)
Theorem link_H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc tfibsegs PcapB OCpy (pc_wrap_memcpy (as_code PcapB))) ->
  tfib_lib_contract_xf_all_A (rc:=rc) link_drv_SK PcapB ameter_triv (fun _ => 0) (fun _ => 0) ->
  drv_mainX_stmt (rc:=rc).
Proof. intros rc. exact (@link_drv_mainX_rc rc). Qed.
End b.
