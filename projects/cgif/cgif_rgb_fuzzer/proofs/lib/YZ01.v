(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YK18 YN0a YN09 YN05 YN0b YH04 YZ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0d YK0a YA0c YA0e YA01 YA02 YB11 YB1g YB01
YG0h YG00 YG01 YG0u YG0d YG0w YG05
YQ0i YQ0a YQ04 YK05 YA0i YA0l
YB1u YF9j YF9i YF9m YCeb YCcz YCrd YCe8 YCe9
YD1e YD1d YD1c YD2e YD1p YD1q YD1r YD1s YD1f YD1j YD1l YD2g YD2h
YCfv YD1h YD1i YD1k YD1g YF9z YF9o YF9s YF9u
YK0p YCie YCi1 YCph YCpi YCrc YCql
YG0e YF9x YF9w YFa2 YCjr YCi7 YCp4 YCi3 YCqm YG0f YFa0 YCpj YCq4 YCq5 YCq6 YCnk YCni YCod YCnn YCpd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Import AX2. Import APG. Import APSG.
Open Scope Z_scope.
Section a.
Context {rc : YN05.RunCeil}.
Let B : asyms := TrbB.
Let HB : TrbSyms B := TrbB_syms.
Let TL : TrbLib B := TrbB_lib.
Let HD : forall t, as_dhash B t = trb_dhash t := fun t => eq_refl.
Let LAWS : AR_laws trbsegs B := AR_laws_ok trbsegs B.
Let AMALLOC_A : forall fx : YK11.FPState, @amalloc_realizes fx rc trbsegs B := fun fx => trb_amalloc_realizes (fx:=fx) B HB HD.
Let AMALLOC : amalloc_realizes trbsegs B := AMALLOC_A _.
Let AFREE_A : forall fx : YK11.FPState, @afree_realizes fx rc trbsegs B := fun fx => afree_realizes_closed (fx:=fx) B HB HD.
Let ASM1_A : forall fx : YK11.FPState, @astack_malloc_realizes fx rc trbsegs B 1 := fun fx => stack_malloc1_contract (fx:=fx) B LAWS HB.
Let ASM2_A : forall fx : YK11.FPState, @astack_malloc_realizes fx rc trbsegs B 2 := fun fx => stack_malloc2_contract (fx:=fx) B LAWS HB.
Let AICPY : aintrin_realizes trbsegs B OCpy (pc_wrap_memcpy (as_code B)) := trb_AICPY B HB.
Let ARDCHK : aread_check_stmt B := trb_ARDCHK B HB.
Let ASM7_A : forall fx : YK11.FPState, @astack_malloc_sz_realizes fx rc trbsegs B A_stack_malloc_7 7 := fun fx => trb_stack_malloc_7 (fx:=fx) B LAWS HB.
Let ASF7_A : forall fx : YK11.FPState, @astack_free_realizes fx rc trbsegs B A_stack_free_7 7 := fun fx => trb_stack_free_7 (fx:=fx) B LAWS HB.
Let ASS00_A : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_00 0 := fun fx => trb_set_shadow_00 (fx:=fx) B LAWS HB.
Let ASSF8_A : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_f8 248 := fun fx => trb_set_shadow_f8 (fx:=fx) B LAWS HB.
Let AREALLOC_A : forall fx : YK11.FPState, @arealloc_realizes fx rc trbsegs B 0x533cc 0x53904 := fun fx => trb_arealloc (fx:=fx) B HB HD.
Let LIBCV : trb_rlibV_contract_all B := trb_RLIBCV2 B HB TL AMALLOC_A AFREE_A ASM1_A ASM2_A ASM7_A ASF7_A ASS00_A ASSF8_A TrbB_fp_consts TrbB_rol_const AREALLOC_A.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1h.xst.
Let XFR : xst_frame_tfa xst := trb_xst_frame.
Let PF1_A : forall fx : YK11.FPState, @printf_first_tfa fx rc B xst := fun fx => trb_printf_first (fx:=fx) B HB LAWS HB.
Let PFN_A : forall fx : YK11.FPState, @printf_next_tfa fx rc B xst := fun fx => trb_printf_next (fx:=fx) B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1h.est.
Let ESTI : est_img_tfa est := trb_est_img.
Let ESTF : est_frame_tfa est := trb_est_frame.
Let FWS : fwrite_site_tfa B est := trb_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := trb_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d7c4 (strB "cli: cannot open "%string) nlB := trb_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d7d9 (strB "cli: read error on "%string) nlB := trb_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x1591f (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := trb_fprintf_usage_site B HB LAWS HB.
Let EXS_A : forall fx : YK11.FPState, @exit_site_tfa fx rc B est xst := fun fx => trb_exit_site (fx:=fx) B HB LAWS.
Lemma trb_srealizes_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (CLOSED inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (trb_srealizes B HB AMALLOC AFREE_A AICPY ARDCHK LIBCV xst XFR PF1_A PFN_A est ESTI ESTF FWS RFS FPO FPR FPU EXS_A
sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End a.
Theorem trb_srealizes_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (CLOSED inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@trb_srealizes_rc (YN05.RunCeilOf (bv_unsigned sp) (valid_sp_window36 sp Hsp))
sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YN05.ceil_of_top_run _)).
Qed.
Theorem cgif_rgb_fuzzer_both_equiv_lim : forall ls : Z, (SRC_LIM_MIN <= ls)%Z ->
forall en_s en_t inp,
valid_entry (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) en_s inp ->
valid_entry (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) en_t inp ->
valid_input inp ->
strong_equiv_error_free_budgets ls target_alloc_limit
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) en_s en_t inp.
Proof.
intros ls Hls [sp brk mb rnd] [sp' brk' mb' rnd'] inp Hens Hent Hinp.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hsp [Hbrk [Hmb Hfit]]]. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
eapply (shape_strong_equiv_efs_budgets ls target_alloc_limit src2segs _ _ sp brk mb rnd TSEGS _ _ sp' brk' mb' rnd' (SPEC inp) (CLOSED inp) inp).
- apply src2_realizes; assumption.
- apply trb_srealizes_top; assumption.
- apply spec_closed_eq.
Qed.
Theorem cgif_rgb_fuzzer_both_equiv :
strong_universal_error_free_T
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. intros en_s en_t inp Hs Ht Hv. exact (cgif_rgb_fuzzer_both_equiv_lim source_alloc_limit SRC_LIM_MIN_le_source en_s en_t inp Hs Ht Hv). Qed.
Theorem cgif_rgb_fuzzer_both_equiv_sanitizer :
strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. intros en_s en_t inp Hs Ht Hv _. exact (cgif_rgb_fuzzer_both_equiv_lim _ SRC_LIM_MIN_le_sanitizer en_s en_t inp Hs Ht Hv). Qed.
