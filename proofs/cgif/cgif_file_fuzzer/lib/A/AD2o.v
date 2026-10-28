(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YA02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn AB1v AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YF0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20 YC7y YC7x YC21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACej ACei ACfh ACfi.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1q AZ03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
@tnewgif_x fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_newgif CTX_cgif_newgif wfn 0x9da38 0x9eca8.
Hypothesis TADDFX : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
@taddframe_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_addframe CTX_cgif_addframe wfn 0x9da38 0x9eca8.
Hypothesis TCLOSEX : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
@tclose_specX fx rc tfib_sink_head tfibsegs tfib_K TfibB ameter_triv XN0 A_cgif_close CTX_cgif_close wfn 0x9da38 0x9eca8.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let LIBX : tfib_lib_contract_x_all TfibB ameter_triv XL0 XL0 0x9da38 0x9eca8 :=
tfib_lib_x_all (fun fx => @tfib_amalloc_realizes fx rc B HB HD) (fun fx => @afree_realizes_closed fx rc B HB HD) (tfib_AIL B HB) wfn (TNEWGIFX rc) (TADDFX rc) (TCLOSEX rc).
Let RO_IN : forall a, 0x9da38 <= a < 0x9eca8 -> in_ro_tfa a := fun a H => or_intror H.
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
Let FPO : fprintf_s_site_tfa B est 0x1d727 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d73c (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x15859 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma tfib_srealizesX_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 0x9da38 0x9eca8 MT_FREE RO_IN LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem tfib_srealizesX_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@tfib_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
Theorem TFIB_T_of_partsXF : TFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (tfib_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
