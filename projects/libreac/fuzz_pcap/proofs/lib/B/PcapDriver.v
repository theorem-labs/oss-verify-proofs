From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan-ubsan twin of a Theorem Labs lane's lib/A/PcapDriver.v (a working branch
   9700d736a50; commit a6de9c745b9), every hunk mirrored: the H_DRIVER obligation of the closing side (the porter's
   OBLIGATIONS.md (sha256 781e8f81f164; internal record) row 13; lib/A/PcapClose.v drv_mainA on a working branch is its asan form),
   for libreac/fuzz_pcap's asan-ubsan build, in the form the donor states it: proofs/cgif/cgif_file_fuzzer/lib/YD1q.v
   (the twin of lib/A/AD1q.v:40-78, origin/ossv/recipes c8557374ad2e), drv_mainX_stmt and DRV_MAINX =
   Reusable/YD1p.v tfib_drv_main applied to the parts. The parts stay Section hypotheses, so H_DRIVER splits into them:
     HB      PcapSyms B                        core (Reusable/YD2l.v TfibB_syms at B := PcapB)
     AMALLOC / AFREE                           rows 8 / 9 (the allocator twins)
     AICPY, ARDCHK                             Reusable/YD2m.v tfib_AICPY / tfib_ARDCHK
     LIBX    pcap's program contract           row 11 (lib/B/Prog/PcapEntry.v tfib_lib_contract_x_all_B)
     xst/XFR/PF1/PFN, est/ESTI/ESTF/FWS/RFS/FPO/FPR/FPU/EXS   the driver's stdio sites (Reusable/YD1j.v, YD1l.v,
             YD1o.v over the generated Reusable/YD1k.v xst / est, YD1kSites.v; donor YD2o.v:45-57)
   What is fuzz_pcap's here: the program contract is the image-free lib/A/Prog/PcapEntry.v's at the asan-ubsan
   instance lib/B/Prog/PcapEntry.v (SK EXPLICIT: PcapSinkHeads.asan_ubsan_sink_head, the asan-ubsan image's ofl_head
   0x5f4e88, MEASURED: .symtab ofl_head 0x5f4e88 in fuzz_pcap.asan-ubsan sha256 c969d83cdd59;
   the source record pcap_KS of lib/B/Stdio/PSourceK.v; the harness globals G_HARNESS_U; PCAP_RLO / PCAP_RHI of
   lib/B/Prog/PcapRelro.v), MT = ameter_triv and XM_LIB = XN_LIB = fun _ => 0 (the donor's binding), the output shape
   AgreePcap.ag_out_shape, and the start-up tables HS_tfib (Reusable/YB01.v) / TFIB (Reusable/YB12.v), a Theorem Labs lane's
   GENERATED asan-ubsan start-up data (a working branch, WIP: not gated, values not claimed here).
   The fprintf formats are .rodata 0x1d631 / 0x1d646 / 0x1581c ("cli: cannot open ", "cli: read error on ",
   "usage: "; the same addresses and bytes in both builds, checked in the asan-ubsan pin 9e66f771f22a). The donor's
   tfib_srealizesX (start-up + driver + spec link) is the closing side's; the donor's ff_unl / ff_libk lemmas are
   cgif's program shape and are not ported. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB12 YB1h YB01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapRelro PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YF0m YCeg YD1v YD1w YD1x YD1i YD1u YD1p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AgreePcap.ag_out_shape.
(* The asan-ubsan image's sink head, passed by name (the porter, 2026-10-28: "tfib_sink_head ->
   PcapSinkHeads.asan_sink_head passed explicitly; never rely on an inferred sink_head"; the asan-ubsan value is
   PcapSinkHeads.asan_ubsan_sink_head; PcapSinkHeads.v has no instance). *)
(* Fully qualified: AgreePcap loads lib/U's twin of YI16, so the short qualifier `YI16` is ambiguous here. *)
Definition pcap_drv_SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head := PcapSinkHeads.asan_ubsan_sink_head.
#[local] Instance pcap_drv_head : @pcap_head pcap_drv_SK := eq_refl.
Section b. Context {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
(* donor YD1q.v LIBX (lib/A/AD1q.v:50), at pcap's program contract (obligation row 11, lib/B/Prog/PcapEntry.v's instance). *)
Hypothesis LIBX : tfib_lib_contract_x_all_B pcap_drv_SK B ameter_triv (fun _ => 0) (fun _ => 0) pcap_KS.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd351)%Z) (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd366)%Z) (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x553c)%Z) (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
(* donor YD1q.v drv_mainX_stmt (lib/A/AD1q.v:64-76); the asan form is lib/A/PcapClose.v:136-148 drv_mainA at HS_TBL := HS_tfib, TFIB_TBL := TFIB. *)
Definition drv_mainX_stmt : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
(* donor YD1q.v DRV_MAINX (lib/A/AD1q.v:77-78). *)
Lemma DRV_MAINX : drv_mainX_stmt.
Proof.
exact (tfib_drv_main (SK:=pcap_drv_SK) B HB AMALLOC AFREE AICPY ARDCHK ameter_triv (fun _ => 0) (fun _ => 0) (fun _ _ => I) (LIBX _)
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS).
Qed.
End d.
End b.
