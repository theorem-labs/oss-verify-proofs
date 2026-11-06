From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the driver-part bindings of cgif c8557374ad2e lib/YD2o.v:24-57 (the twin of lib/A/AD2o.v:28-60); the closing (tfib_srealizesX_rc, TFIB_T) is the closing side's (lib/A/PcapClose.v on a working branch is its asan form). It is the asan-ubsan twin of a Theorem Labs lane's lib/A/AD2o.v (a working branch 9700d736a50; commits a6de9c745b9, 9700d736a50), every hunk mirrored, for libreac/fuzz_pcap's asan-ubsan build (pinned image fuzz_pcap.asan-ubsan sha256 9e66f771f22a, symbols from its unstripped twin fuzz_pcap.asan-ubsan sha256 c969d83cdd59): module paths changed; B := PcapB and HB := TfibB_syms (Reusable/YD2l.v, which keeps the donor's name TfibB_syms for the theorem a Theorem Labs lane's A/AD2l.v calls PcapB_syms; donor YD2o.v:25-26); the driver's stdio parts are bound as the donor binds them (YD2o.v:45-57), to Reusable/YD1k.v xst / est / tfib_xst_frame / tfib_est_img / tfib_est_frame (a Theorem Labs lane's generated data half), Reusable/YD1kSites.v tfib_fwrite_site / tfib_refused_site, YD1o.v tfib_printf_first / tfib_printf_next, YD1l.v tfib_fprintf_open_site / _rderr_site / _usage_site at fuzz_pcap's formats 0x1d631 / 0x1d646 / 0x1581c (.rodata, the same addresses and bytes in both builds; donor 0x1d6e9 / 0x1d6fe / 0x15859) and YD1j.v tfib_exit_site; they are applied to lib/B/PcapDriver.v DRV_MAINX (donor YD1q.v), whose program contract is pcap's (lib/B/Prog/PcapEntry.v tfib_lib_contract_x_all_B at SK := pcap_drv_SK = PcapSinkHeads.asan_ubsan_sink_head, KS := pcap_KS of lib/B/Stdio/PSourceK.v). What the donor closes here from cgif's own program and allocator (YD2o.v:28-41 wfn / TNEWGIFX / TADDFX / TCLOSEX, AMALLOC / AFREE / AICPY / LIBX := tfib_lib_x_all) is not fuzz_pcap's: these four parts are the premises of pcap_H_DRIVER, in the shape of the closing side's H_DRIVER (rows 8-11). RLO / RHI / RO_IN (YD2o.v:40, 42) are fixed inside pcap's program contract (PCAP_RLO / PCAP_RHI of lib/B/Prog/PcapRelro.v) and MT_FREE (YD2o.v:44) is bound in PcapDriver.v. HD (YD2o.v:27) served only the allocator closings and is not needed. ARDCHK is the donor's Let (YD2o.v:43 tfib_ARDCHK B HB), from Reusable/YD2m.v (over Reusable/YE33.v's aread_check_realizes), so pcap_H_DRIVER has the H_DRIVER premises only, no foreign premise. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YA02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1h.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapRelro PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD2l YCeg YD1v YD1w YD1x YD1i YD1k YD1kSites YD1l YD1o YD1j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1u.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require Import PcapDriver.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD2m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AgreePcap.ag_out_shape.
Open Scope Z_scope.
Section b.
Let B : asyms := PcapB.
Let HB : PcapSyms B := TfibB_syms.
(* donor YD2o.v:43 Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB (Reusable/YD2m.v). *)
Let ARDCHK : forall rc : YM05.RunCeil, aread_check_stmt (rc:=rc) B := fun rc => tfib_ARDCHK (rc:=rc) B HB.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd351)%Z) (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd366)%Z) (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x553c)%Z) (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
(* donor YD2o.v:58-68 tfib_srealizesX_rc, cut at the driver: YD1q.v DRV_MAINX at the parts above, with the
   four parts the donor closes from cgif's program and allocator taken as premises. *)
Lemma pcap_drv_mainX_rc :
  (forall fx : YK11.FPState, @amalloc_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc tfibsegs PcapB OCpy (pc_wrap_memcpy (as_code PcapB))) ->
  tfib_lib_contract_x_all_B (rc:=rc) pcap_drv_SK PcapB ameter_triv (fun _ => 0) (fun _ => 0) pcap_KS ->
  drv_mainX_stmt (rc:=rc).
Proof.
intros AMALLOC AFREE AICPY LIBX.
exact (DRV_MAINX B HB (AMALLOC _) (AFREE _) (AICPY _) (ARDCHK rc) LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS).
Qed.
End RC.
(* H_DRIVER (the asan form: lib/A/PcapClose.v:163-170) at B := PcapB, SK := pcap_drv_SK, KS := pcap_KS, HS_TBL :=
   HS_tfib, TFIB_TBL := TFIB (its drv_mainA is lib/B/PcapDriver.v drv_mainX_stmt there). *)
Theorem pcap_H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc tfibsegs PcapB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc tfibsegs PcapB OCpy (pc_wrap_memcpy (as_code PcapB))) ->
  tfib_lib_contract_x_all_B (rc:=rc) pcap_drv_SK PcapB ameter_triv (fun _ => 0) (fun _ => 0) pcap_KS ->
  drv_mainX_stmt (rc:=rc).
Proof. intros rc. exact (@pcap_drv_mainX_rc rc). Qed.
End b.
