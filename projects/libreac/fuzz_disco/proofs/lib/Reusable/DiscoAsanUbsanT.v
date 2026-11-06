(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD2o.v (ossv/recipes c8557374ad2) for
   fuzz_disco, the asan-ubsan twin of lib/A/DiscoAsanT.v (fuzz_grant's lib/A/AGrantT.v shape): TFIB_T
   (lib/Reusable/YZ03.v) over the landed asan-ubsan core, with cgif's three program parts replaced by ONE named
   hypothesis, LIBX_ALL, the contract of fuzz_disco's program part (LLVMFuzzerTestOneInput). *)
(* The closing side of fuzz_disco's asan-ubsan obligation (rule 24: no function proved; this file is assembly).

   Every other input of lib/Reusable/YD1q.v tfib_srealizesX is a Let over the landed core, as cgif's YD2o.v does:
   the symbol table TfibB (YD2l), the allocator (YF0w / YF0q), the memcpy interceptor and the read check (YD2m), the
   driver's stdio sites (YD1k / YD1j / YD1l / YD1o) and the read-only arm of in_ro_tfa (YCeg). The read-only facts
   the part's walks take are PROVED here (YRoClose.tfib_ro_hyps), so LIBX_ALL is the only hypothesis. The three
   fprintf sites are at the asan-ubsan image's own strings (pin cee6f04ad3d4): 0x1d868 "cli: cannot open %s\n",
   0x1d87d "cli: read error on %s\n", 0x1583b "usage: %s INPUT\n". *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_disco.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK15 YK18 YA02 YB1h YG0f YG00 YG01 YG0n YG0d
YG05 YG0q YI16 YC5d YCbp YCfn YB1v YF0m YF0p YD2l YCeg
YD1v YD1w YD1x YD1i YD1k YD1l YD1o YD1j YD2m
YF0w YF0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import DiscoShape YD1q YZ03.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YB1w YRo YRoClose.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance disco_lib_shape.
Open Scope Z_scope.

Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The read-only facts the part's walks take (a Theorem Labs lane's lib/Y/Prog/DiscoYEntBodyStmt.v d_ro_hyps at TfibB):
   YRo.tfib_ro_unowned, YRo.globs_marked over YRo.tfib_globs and YRo.img_shadow_vis. Proved, not assumed. *)
Definition H_RO_stmt (rc : YM05.RunCeil) : Prop :=
  YRo.tfib_ro_unowned TfibB
  /\ YRo.globs_marked (rc := rc) tfibsegs TfibB YRo.tfib_globs
  /\ YRo.img_shadow_vis (rc := rc) tfibsegs TfibB.
Lemma H_RO : forall rc : YM05.RunCeil, H_RO_stmt rc.
Proof. intros rc. exact (YRoClose.tfib_ro_hyps (rc := rc)). Qed.

Section b.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* THE PART: the contract of fuzz_disco's program part (the asan-ubsan twin of lib/A/Prog/DiscoLibX.v disco_lib_x_all),
   given the read-only facts, with cgif's XL0 (fun _ => 0), ameter_triv and the image's relro range
   (lib/Reusable/YB1w.v .data.rel.ro start .. .got end). *)
Hypothesis LIBX_ALL : forall rc : YM05.RunCeil,
  H_RO_stmt rc ->
  tfib_lib_contract_x_all (rc := rc) B ameter_triv (fun _ => 0) (fun _ => 0) YB1w.tfib_data_rel_ro_lo YB1w.tfib_got_hi.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) tfibsegs B := fun fq => @afree_realizes_closed fq rc B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let RO_IN : forall a, YB1w.tfib_data_rel_ro_lo <= a < YB1w.tfib_got_hi -> in_ro_tfa a := fun a H => or_intror H.
Let LIBX : tfib_lib_contract_x_all B ameter_triv (fun _ => 0) (fun _ => 0) YB1w.tfib_data_rel_ro_lo YB1w.tfib_got_hi :=
  LIBX_ALL rc (H_RO rc).
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : forall fq : YK11.FPState, printf_first_tfa (fx := fq) B xst := fun fq => @tfib_printf_first fq rc B HB LAWS HB.
Let PFN : forall fq : YK11.FPState, printf_next_tfa (fx := fq) B xst := fun fq => @tfib_printf_next fq rc B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d868 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d87d (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x1583b (strB "usage: "%string) (strB " INPUT"%string ++ nlB) :=
  tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : forall fq : YK11.FPState, exit_site_tfa (fx := fq) B est xst := fun fq => @tfib_exit_site fq rc B HB LAWS.
Lemma disco_srealizesXU_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  change target_alloc_limit with YA02.LIMIT.
  exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv (fun _ => 0) (fun _ => 0)
    YB1w.tfib_data_rel_ro_lo YB1w.tfib_got_hi MT_FREE RO_IN LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
    sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem disco_srealizesXU_top : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@disco_srealizesXU_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
Theorem TFIB_TB_of_lib : TFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (disco_srealizesXU_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
