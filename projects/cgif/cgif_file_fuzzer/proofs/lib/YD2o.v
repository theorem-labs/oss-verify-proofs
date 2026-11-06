(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YA02 YB1h YG0f YG00 YG01 YG0n YG0d
YG05 YG0q YI16 YC5d YCbp YCfn YB1v YF0m YF0p YD2l YCeg
YD1v YD1w YD1x YD1i YD1k YD1l YD1o YD1j YD2m
YF0w YF0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE2k YD1u YC20 YC7y YC7x YC21 YCej YCei YCfh YCfi.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0a YD1q YZ03.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance ff_lib_shape.
Open Scope Z_scope.
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
Section b.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
Variable wfn : Z.
Hypothesis TNEWGIFX : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
@tnewgif_x fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_newgif CTX_cgif_newgif wfn 0x9dca8 0x9ef18.
Hypothesis TADDFX : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
@taddframe_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_addframe CTX_cgif_addframe wfn 0x9dca8 0x9ef18.
Hypothesis TCLOSEX : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
@tclose_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_close CTX_cgif_close wfn 0x9dca8 0x9ef18.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let LIBX : tfib_lib_contract_x_all TfibB ameter_triv XL0 XL0 0x9dca8 0x9ef18 :=
tfib_lib_x_all (fun fx => @tfib_amalloc_realizes fx rc B HB HD) (fun fx => @afree_realizes_closed fx rc B HB HD) (tfib_AIL B HB) wfn (TNEWGIFX rc) (TADDFX rc) (TCLOSEX rc).
Let RO_IN : forall a, 0x9dca8 <= a < 0x9ef18 -> in_ro_tfa a := fun a H => or_intror H.
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
Let FPO : fprintf_s_site_tfa B est 0x1d6e9 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d6fe (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x15859 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma tfib_srealizesX_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 0x9dca8 0x9ef18 MT_FREE RO_IN LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem tfib_srealizesX_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@tfib_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
Theorem TFIB_T_of_partsXF : TFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (tfib_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
