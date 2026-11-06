(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, with its module paths, module names and addresses changed; 45 of its 95 lines of code are new or changed and 32 lines of the source are left out. *)
(* fuzz_state's ASan+UBSan side TFIB_T (COMP-B's lib/B/FSTfibB.v TFIB_T_B, a working branch
   df45f86112f) from the relocated runtime core of cgif_file_fuzzer at image B (fs.asan-ubsan), in the form of
   lib/A/FSTfibParts.v (S0 a9edd281227), of which this file is the image-B twin (a Theorem Labs lane, F11 / obligation B11,
   statement agreed with ENTRY a Theorem Labs lane 2026-10-29T09:29Z). The program part is a library invariant LI (a Section
   variable) and three Section hypotheses: LIBX_ALL, the ASan contract of fs's LLVMFuzzerTestOneInput at image B
   (lib/B/YCfn.v tfib_lib_contract_xI_all), at fs's library shape ag_shape checksum_shape, the trivial meter, the
   zero per-call budgets XL0, and image B's read-only GOT window [0x9f6b0, 0xa0908) (lib/B/FSH_Base.v FS_RLO /
   FS_RHI, lib/B/YCeg.v in_ro_tfa); LIK and LI0 over lib/B/FSPstat.v's statics (lib/B/YD1w.v lib_inv_stable,
   lib_inv_init). Every other part is a proved lemma of the relocated B core, one per Let below.
   arodata (obligation B11) is not a hypothesis: lib/B/YD1w.v:98 lib_site_x's arodata_ok premise is met inside the
   driver walk (lib/B/YD1r.v:646 tfib_loop_L, handed on at lib/B/YD1m.v:55), and lib/B/YD1q.v:71 tfib_srealizesX
   takes none.
   Changes from the A file: lib/B module paths (YB1h YCfn YB1v YF0m YD2l YCeg YD1v YD1w YD1x YD1i YD1k YD1l YD1o
   YD1j YD2m YF0w YF0q YE2k YD1u YCej YD1q), TfibBU / TfibBU_syms, AsanUbsan.M, RLO / RHI 0x9f6b0 / 0xa0908, the three
   driver strings at B's addresses (0x1d7d8, 0x1d7ed, 0x15897, lib/B/YD1q.v:52-54), and the sink guard's Remove
   Hints list, measured in THIS closure with Print Instances (lib/B/YE2k.tfib_sink_head, not A's AE2k).
   FSTFIB_T_B below is COMP-B's TFIB_T_B restated (lib/B/FSTfibB.v is not in S0): YB1h's TSEGS / TPH are
   AsanUbsan.M.loaded_segments / AsanUbsan.M.phdrs, COMP-B's fsbsegs0 / AsanUbsan.M.phdrs.
   rule 24: proves no function (kind: start-up facts - composition of proved core lemmas and the program part). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK15 YK18 YA02 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1h.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YD2l YCeg YD1v YD1w YD1x YD1i YD1k YD1l YD1o YD1j YD2m YF0w YF0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YE2k YD1u YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import ZTraceSpec AgreeShape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YD1q.
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
(* SINK GUARD. Measured in this file's Require closure (Print Instances, build-20261029T093139Z on S0 a9edd281227):
   lib.Reusable.YI16.sink_head has the instance lib/B/YE2k.tfib_sink_head; lib.U.Reusable.YI16.sink_head has
   lib/U/Reusable/YI5b.src0_sink_head; lib.U.Reusable.YI14.sink_syms has lib/U/Reusable/YI5c.src0_sink (and
   sink_laws src0_sink_laws); lib.Reusable.YI14.sink_syms has none. All four are removed, #[global], as in the A
   file; the two Fail lines check that no instance of S0's classes is left (full paths). *)
#[global] Remove Hints
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.YI5c.src0_sink_laws
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YE2k.tfib_sink_head : typeclass_instances.
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* The per-call meter budgets of the library contract (cgif_file_fuzzer A/ACfi.v:56). *)
Definition XL0 : Z -> Z := fun _ => 0.

Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* COMP-B's lib/B/FSTfibB.v TFIB_T_B (a working branch df45f86112f). *)
Definition FSTFIB_T_B : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS
(init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS := ag_shape checksum_shape) inp).

Section b.
Let B : asyms := TfibBU.
Let HB : TfibSyms B := TfibBU_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* The program part: a library invariant and the ASan contract of fs's LLVMFuzzerTestOneInput. *)
Variable LI : Z -> world tfibsegs -> (word -> option byte) -> Prop.
Hypothesis LIBX_ALL : forall rc : YM05.RunCeil,
  @tfib_lib_contract_xI_all rc (ag_shape checksum_shape) TfibBU ameter_triv XL0 XL0 0x9f6b0 0xa0908 LI.
Hypothesis LIK : lib_inv_stable LI.
Hypothesis LI0 : lib_inv_init LI.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let LIBX : @tfib_lib_contract_xI_all rc (ag_shape checksum_shape) TfibBU ameter_triv XL0 XL0 0x9f6b0 0xa0908 LI := LIBX_ALL rc.
Let RO_IN : forall a, 0x9f6b0 <= a < 0xa0908 -> in_ro_tfa a := fun a H => or_intror H.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d7d8 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d7ed (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x15897 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma fs_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS := ag_shape checksum_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (@tfib_srealizesX rc (ag_shape checksum_shape) B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 0x9f6b0 0xa0908 MT_FREE RO_IN
  LI LIBX LIK LI0 xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
  sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem fs_srealizesX_top : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS := ag_shape checksum_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@fs_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
Theorem TFIB_T_of_lib_B : FSTFIB_T_B.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (fs_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
