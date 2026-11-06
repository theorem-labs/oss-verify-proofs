(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v (TFIB_T_of_partsXF) for
   plugin-hostd/fuzz_reply.asan: the library shape is checksum_shape (lib/ZTraceSpec.v); cgif's three function
   hypotheses TNEWGIFX/TADDFX/TCLOSEX and their assembly A/ACfi.v tfib_lib_x_all are replaced by ONE Section hypothesis,
   the donor's program interface tfib_lib_contract_x (A/ACfn.v:59) at fuzz_reply's LLVMFuzzerTestOneInput
   (A_LLVMF 0x840b0, return address RA_LLVMF 0x821e8 after target_run's call); the read-only range is fuzz_reply.asan's
   .data.rel.ro start .. .got end (A/ACeg.v in_ro_tfa); the meter bounds of the trivial meter are zero; module paths
   changed. *)
(* The milestone of the RelocA lane: TFIB_T (lib/A/ReplyTFIB.v) from the program contract alone. Everything else - the
   start-up from Asan.M.init_pc to main, the driver (main, target_run, the input read, the printf/fwrite/fprintf/exit
   sites), the allocator, the intrinsics and the read check - is the relocated donor walk (A/AD1q.v tfib_srealizesX and
   its closure), closed. The runtime entries the program reaches beyond the donor's (realloc, strndup, strncmp,
   strrchr, strlen, strcmp, snprintf, the general strnlen/memchr, __asan_memmove, __asan_stack_malloc_0, the pthread
   mutex) are premises of the program contract's proof (lib/A/W_sites.v and the allocator parameter), not of this one. *)
(* Modified by Theorem Labs, 2026-10: fuzz_reply's Reusable/YM05.v RunCeil carries the plain lineage's rc_lim field, so the
   run ceiling is built with RunCeilOf's third argument, target_alloc_limit (the limit init_config takes here); no lemma
   on this path reads rc_lim. lib/A/ReplyGuard.v is Required, so no sink instance is inferred in this file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YA02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k AD1u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1q ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AD1g AD2i AD2k ReplyGuard.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Open Scope Z_scope.
(* The trivial meter's bounds (cgif's A/ACfi.v XL0). *)
Definition XR0 : Z -> Z := fun _ => 0.
(* fuzz_reply.asan's .data.rel.ro start and .got end (section headers of the unstripped twin: .data.rel.ro 0x9d470,
   .got 0x9d970 + 0xd58), the second disjunct of in_ro_tfa (A/ACeg.v). *)
Definition REPLY_RO_LO : Z := 0x9d470.
Definition REPLY_RO_HI : Z := 0x9e6c8.
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
(* errno is tp-relative in fuzz_reply.asan: __errno_location is `mv a0,tp ; addi a0,a0,-164 ; ret` (0x8c9a8); the
   instance's cells agree (TFIB_ERRNO 0x5d93cc = TFIB_TP 0x5d9470 - 164, A/AF0m.v). *)
Lemma TfibB_errno_tp : as_errno TfibB = as_tp TfibB - 164.
Proof. reflexivity. Qed.
Section b.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* (a) The program contract: fuzz_reply's LLVMFuzzerTestOneInput in the donor's interface form. *)
Hypothesis TLLVMF : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
@tfib_lib_contract_x fx rc checksum_shape TfibB ameter_triv XR0 XR0 REPLY_RO_LO REPLY_RO_HI.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let LIBX : tfib_lib_contract_x_all TfibB ameter_triv XR0 XR0 REPLY_RO_LO REPLY_RO_HI := fun fx => TLLVMF rc fx.
Let RO_IN : forall a, REPLY_RO_LO <= a < REPLY_RO_HI -> in_ro_tfa a := fun a H => or_intror H.
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
Let FPO : fprintf_s_site_tfa B est 0x1d72f (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d744 (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x15877 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma reply_srealizesX_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XR0 XR0 REPLY_RO_LO REPLY_RO_HI MT_FREE RO_IN LIBX
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem reply_srealizesX_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@reply_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp) target_alloc_limit) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
(* The milestone: TFIB_T from the program contract. *)
Theorem reply_TFIB_T_of_parts : TFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (reply_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
