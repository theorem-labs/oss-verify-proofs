(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, with its module paths, module names and addresses changed; 26 of its 78 lines of code are new or changed and 30 lines of the source are left out. *)
(* fuzz_manifest's ASan side TFIB_T (FMTfibT.v) from the relocated runtime core of cgif_file_fuzzer, in the form
   of cgif_file_fuzzer's A/AD2o.v (TFIB_T_of_partsXF). The program part is a library invariant LI (a Section
   variable) and three Section hypotheses: LIBX_ALL, the ASan contract of fm's LLVMFuzzerTestOneInput
   (A_LLVMF = 0x8091c, A/ACfn.v tfib_lib_contract_xI_all: call ci needs LI ci and gives LI (ci + 1)), at fm's
   library shape checksum_shape (ZTraceSpec.v), the trivial meter, the zero per-call budgets XL0, and fm's
   read-only GOT window [0x99450, 0x9a6a8) (A/ACeg.v in_ro_tfa); LIK, LI is kept when the bytes of fuzz/alloc.c's
   statics (A/FMPstat.v FM_PSTAT_FP) are kept; LI0, LI 0 holds when those bytes are the image's (A/AD1w.v
   lib_inv_stable, lib_inv_init). Every other part (allocator, intrinsics, read checks, printf/fprintf/fwrite/exit
   sites of the driver, start-up) is a proved lemma of the relocated core. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK15 YK18 YA02 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1h.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import ACfn AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AE2k AD1u ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AD1q FMTfibT.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Open Scope Z_scope.

(* The per-call meter budgets of the library contract (cgif_file_fuzzer A/ACfi.v:56). *)
Definition XL0 : Z -> Z := fun _ => 0.

Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Section b.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* The program part: a library invariant and the ASan contract of fm's LLVMFuzzerTestOneInput. *)
Variable LI : Z -> world tfibsegs -> (word -> option byte) -> Prop.
Hypothesis LIBX_ALL : forall rc : YM05.RunCeil,
  @tfib_lib_contract_xI_all rc checksum_shape TfibB ameter_triv XL0 XL0 0x99450 0x9a6a8 LI.
Hypothesis LIK : lib_inv_stable LI.
Hypothesis LI0 : lib_inv_init LI.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let LIBX : tfib_lib_contract_xI_all TfibB ameter_triv XL0 XL0 0x99450 0x9a6a8 LI := LIBX_ALL rc.
Let RO_IN : forall a, 0x99450 <= a < 0x9a6a8 -> in_ro_tfa a := fun a H => or_intror H.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d638 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d64d (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x15805 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma fm_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 0x99450 0x9a6a8 MT_FREE RO_IN LI LIBX LIK LI0 xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
  sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem fm_srealizesX_top : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@fm_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
Theorem TFIB_T_of_lib : TFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (fm_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
