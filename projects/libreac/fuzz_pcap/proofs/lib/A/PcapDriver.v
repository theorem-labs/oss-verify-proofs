From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: new file for libreac/fuzz_pcap's ASan driver: the H_DRIVER obligation of the closing side
   (the porter's OBLIGATIONS.md (sha256 781e8f81f164; internal record) row 13; lib/A/PcapClose.v drv_mainA on a working branch), in the
   form the donor states it: proofs/cgif/cgif_file_fuzzer/lib/A/AD1q.v:40-78 (origin/ossv/recipes c8557374ad2e),
   drv_mainX_stmt and DRV_MAINX = AD1p.v:84 tfib_drv_main applied to the parts AD1q.v:41-63. The parts stay Section
   hypotheses, each with its owner, so H_DRIVER splits into them (OBLIGATIONS.md (sha256 781e8f81f164; internal record) 'Still folded into H_DRIVER'):
     HB      PcapSyms B                        core (lib/A/AD2l.v PcapB_syms at B := PcapB)
     AMALLOC / AFREE                           rows 8 / 9 (lib/A/AF0w.v / AF0q.v)
     AICPY, ARDCHK                             runtime a Theorem Labs lane (lib/A/AD2m.v tfib_AICPY / tfib_ARDCHK)
     LIBX    pcap's program contract           row 11 (lib/A/Prog/PcapEntryA.v tfib_lib_contract_x_all_A)
     xst/XFR/PF1/PFN, est/ESTI/ESTF/FWS/RFS/FPO/FPR/FPU/EXS   the driver's stdio sites (lib/A/AD1j.v, AD1l.v,
             AD1o.v over the generated lib/A/AD1k.v xst / est; donor AD2o.v:48-60)
   What is fuzz_pcap's here: the program contract is PcapEntry's (SK EXPLICIT: PcapSinkHeads.asan_sink_head, the
   ASan image's ofl_head 0x5f4f88; the source record pcap_KS; the harness globals G_HARNESS; PCAP_RLO / PCAP_RHI),
   MT = ameter_triv and XM_LIB = XN_LIB = fun _ => 0 (the donor's binding AD2o.v:45, PcapClose.v:124), the output
   shape AgreePcap.ag_out_shape (= PcapAsanTop.pcap_shape), and the start-up tables HS_tfib (A/AB01.v) / TFIB
   (A/AB12.v), a Theorem Labs lane's GENERATED start-up data (gated PASS A+B at c061542723f / 731386609e0, values not
   claimed here). The donor's tfib_srealizesX (AD1q.v:79-98, start-up + driver + spec link) is the closing side's
   (PcapClose.v:197 pcap_srealizesX_rc); the donor's ff_unl / ff_libk lemmas (AD1q.v:25-36) are cgif's program
   shape (YI0a.v ff_lib_shape) and are not ported. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB12 AB1h AB01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapRelro PcapEntry PcapEntryA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0m ACeg AD1v AD1w AD1x AD1i AD1u AD1p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AgreePcap.ag_out_shape.
(* The ASan image's sink head, passed by name (the porter, 2026-10-28: "tfib_sink_head -> PcapSinkHeads.asan_sink_head
   passed explicitly; never rely on an inferred sink_head"; PcapSinkHeads.v has no instance). *)
(* Fully qualified: AgreePcap loads lib/U's twin of YI16, so the short qualifier `YI16` is ambiguous here. *)
Definition pcap_drv_SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head := PcapSinkHeads.asan_sink_head.
#[local] Instance pcap_drv_head : @pcap_head pcap_drv_SK := eq_refl.
Section b. Context {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
(* donor AD1q.v:50 LIBX, at pcap's program contract (obligation row 11, PcapClose.v:123-124's form). *)
Hypothesis LIBX : PcapEntryA.tfib_lib_contract_x_all_A pcap_drv_SK B ameter_triv (fun _ => 0) (fun _ => 0) pcap_KS.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est (symaddr (Symbols.Asan.Sec.s_rodata + 0xd351)%Z) (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est (symaddr (Symbols.Asan.Sec.s_rodata + 0xd366)%Z) (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est (symaddr (Symbols.Asan.Sec.s_rodata + 0x553c)%Z) (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
(* donor AD1q.v:64-76 drv_mainX_stmt; = PcapClose.v:136-148 drv_mainA at HS_TBL := HS_tfib, TFIB_TBL := TFIB. *)
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
(* donor AD1q.v:77-78 DRV_MAINX. *)
Lemma DRV_MAINX : drv_mainX_stmt.
Proof.
exact (tfib_drv_main (SK:=pcap_drv_SK) B HB AMALLOC AFREE AICPY ARDCHK ameter_triv (fun _ => 0) (fun _ => 0) (fun _ _ => I) (LIBX _)
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS).
Qed.
End d.
End b.
