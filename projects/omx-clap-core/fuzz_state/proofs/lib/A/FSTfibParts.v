(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, with its module paths, module names and addresses changed; 43 of its 95 lines of code are new or changed and 30 lines of the source are left out. *)
(* fuzz_state's ASan side TFIB_T (COMP-A's lib/A/FSTfib.v:19-26) from the relocated runtime core of
   cgif_file_fuzzer, in the form of cgif_file_fuzzer's A/AD2o.v (TFIB_T_of_partsXF).  The program part is a
   library invariant LI (a Section variable) and three Section hypotheses: LIBX_ALL, the ASan contract of fs's
   LLVMFuzzerTestOneInput (A_LLVMF = 0x80f1c, A/ACfn.v tfib_lib_contract_xI_all: call ci needs LI ci and gives
   LI (ci + 1)), at fs's library shape ag_shape checksum_shape (lib/AgreeShape.v over lib/ZTraceSpec.v), the
   trivial meter, the zero per-call budgets XL0, and fs's read-only GOT window [0x9f190, 0xa03e8) (FSH_Base.v
   FS_RLO / FS_RHI, A/ACeg.v in_ro_tfa); LIK, LI is kept when the bytes of fuzz/alloc.c's statics
   (A/FSPstat.v FS_PSTAT_FP) are kept; LI0, LI 0 holds when those bytes are the image's (A/AD1w.v
   lib_inv_stable, lib_inv_init).  Every other part (allocator, intrinsics, read checks,
   printf/fprintf/fwrite/exit sites of the driver, start-up) is a proved lemma of the relocated core.
   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMTfibParts.v (a working branch aeb12aaa12b),
   with fs's module paths, fs's RLO / RHI, fs's shape and fs's conclusion.
   FSTFIB_T below is COMP-A's TFIB_T (a working branch lib/A/FSTfib.v:19-26) restated, because
   lib/A/FSTfib.v is not on this branch: A/AB1h.v's TSEGS and TPH are Asan.M.loaded_segments and
   Asan.M.phdrs, which is what COMP-A calls fssegs0 and Asan.M.phdrs, so the two are convertible.
   rule 24: no function proved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK15 YK18 YA02 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1h.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import ACfn AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AE2k AD1u ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import ZTraceSpec AgreeShape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AD1q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
(* fs's library shape: the agreement shape over the plain checksum shape (lib/AgreeShape.v ag_shape,
   lib/ZTraceSpec.v checksum_shape), the shape COMP-A's TFIB_T is stated at.  Declared here so that every
   implicit {LS : lib_shape} of the relocated core resolves to fs's shape and not to ZTraceSpec's global
   checksum_shape; every site that names the shape names it with @ as well. *)
#[local] Instance fs_lib_shape : lib_shape := ag_shape checksum_shape.
Open Scope Z_scope.
(* SINK GUARD. This file's Require closure loads, through the plain side it composes with (lib/ZTraceSpec.v,
   lib/AgreeShape.v), the UBSan plain twins lib/U/Reusable/YI5b.v (`#[global] Instance src0_sink_head`) and
   lib/U/Reusable/YI5c.v (`src0_sink`, `src0_sink_laws`). It also loads A's own A/AE2k.v `tfib_sink_head`. FSH_Gen.v's
   removal of lib/Reusable/YI5b's instance is not in this closure (a Theorem Labs lane 06:55Z reverse walk). So all four are removed
   here, #[global] so the removal holds wherever this file is loaded. Nothing in this file uses an implicit sink
   argument: `Set Printing All` over TFIB_T_of_lib's statement and fs_srealizesX_rc's proof term names no sink_head /
   sink_syms constant (a Theorem Labs lane 06:53Z, (internal path)). Every A sink use is
   written `@... AE2k.tfib_sink_head`. The two `Fail` lines below check that no instance of A's classes is left;
   they use the full paths, because inside this file the short `Reusable.YI14` can resolve to lib.U.Reusable.YI14.
   Port-from: lib/A/FSH_Gen.v:48-52 (the same guard over lib/Reusable/YI5b). *)
#[global] Remove Hints
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.YI5c.src0_sink_laws
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.AE2k.tfib_sink_head : typeclass_instances.
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* The per-call meter budgets of the library contract (cgif_file_fuzzer A/ACfi.v:56). *)
Definition XL0 : Z -> Z := fun _ => 0.

Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* COMP-A's lib/A/FSTfib.v:19-26 TFIB_T. *)
Definition FSTFIB_T : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS
(init_config TSEGS Asan.M.init_pc TPH sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS := ag_shape checksum_shape) inp).

Section b.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* The program part: a library invariant and the ASan contract of fs's LLVMFuzzerTestOneInput. *)
Variable LI : Z -> world tfibsegs -> (word -> option byte) -> Prop.
Hypothesis LIBX_ALL : forall rc : YM05.RunCeil,
  @tfib_lib_contract_xI_all rc (ag_shape checksum_shape) TfibB ameter_triv XL0 XL0 0x9f190 0xa03e8 LI.
Hypothesis LIK : lib_inv_stable LI.
Hypothesis LI0 : lib_inv_init LI.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let LIBX : @tfib_lib_contract_xI_all rc (ag_shape checksum_shape) TfibB ameter_triv XL0 XL0 0x9f190 0xa03e8 LI := LIBX_ALL rc.
Let RO_IN : forall a, 0x9f190 <= a < 0xa03e8 -> in_ro_tfa a := fun a H => or_intror H.
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
Let FPO : fprintf_s_site_tfa B est 0x1d7d3 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d7e8 (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x1588f (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma fs_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS := ag_shape checksum_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (@tfib_srealizesX rc (ag_shape checksum_shape) B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 0x9f190 0xa03e8 MT_FREE RO_IN
  LI LIBX LIK LI0 xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
  sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem fs_srealizesX_top : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS := ag_shape checksum_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@fs_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
Theorem TFIB_T_of_lib : FSTFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (fs_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
