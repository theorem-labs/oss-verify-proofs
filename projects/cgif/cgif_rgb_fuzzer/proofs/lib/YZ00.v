(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YK18 YN0a YN09 YN05 YN0b YH04 YZ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0d YK0a YA0c YA0e YA01 YA02 YB06 YB0l YB00
YG0h YG00 YG01 YG0u YG0d YG0w YG05
YQ0i YQ0a YQ04 YK05 YA0i YA0l
YB0z YF90 YF8z YF93 YC1d YC04 YCce YC1a YC1b
YD04 YD03 YD02 YD14 YD0f YD0g YD0h YD0i YD05 YD09 YD0b YD16 YD18
YC2s YD07 YD08 YD0a YD06 YF9e YF95 YF97 YF99
YK0p YG0e YG0f YCcx YCcy YC6j YCcd YCbp YD17
YF9f YF9c YF9b YF9h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Import AX2. Import APG. Import APSG.
Open Scope Z_scope.
Section a.
Context {rc : YN05.RunCeil}.
Variable xs : list (list Z).
Hypothesis HUX : universe_ok (Tra_universe ++ xs).
Let B : asyms := TraBx xs.
Let HB : TraSyms B := TraBx_syms xs HUX.
Let TL : TraLib B := TraBx_lib xs.
Let HD : forall t, as_dhash B t = tra_dhash t := fun t => eq_refl.
Let LAWS : AR_laws trasegs B := AR_laws_ok trasegs B.
Let AMALLOC_A : forall fx : YK11.FPState, @amalloc_realizes fx rc trasegs B := fun fx => tra_amalloc_realizes (fx:=fx) B HB HD.
Let AMALLOC : amalloc_realizes trasegs B := AMALLOC_A _.
Let AFREE_A : forall fx : YK11.FPState, @afree_realizes fx rc trasegs B := fun fx => afree_realizes_closed (fx:=fx) B HB HD.
Let ASM1_A : forall fx : YK11.FPState, @astack_malloc_realizes fx rc trasegs B 1 := fun fx => stack_malloc1_contract (fx:=fx) B LAWS HB.
Let ASM2_A : forall fx : YK11.FPState, @astack_malloc_realizes fx rc trasegs B 2 := fun fx => stack_malloc2_contract (fx:=fx) B LAWS HB.
Let AICPY : aintrin_realizes trasegs B OCpy (pc_wrap_memcpy (as_code B)) := tra_AICPY B HB.
Let ARDCHK : aread_check_stmt B := tra_ARDCHK B HB.
Let AREALLOC_A : forall fx : YK11.FPState, @arealloc_realizes fx rc trasegs B 0x53108 0x53640 := fun fx => tra_arealloc (fx:=fx) B HB HD.
Let ASM7_A : forall fx : YK11.FPState, @astack_malloc_sz_realizes fx rc trasegs B A_stack_malloc_7 7 := fun fx => tra_stack_malloc_7 (fx:=fx) B LAWS HB.
Let ASF7_A : forall fx : YK11.FPState, @astack_free_realizes fx rc trasegs B A_stack_free_7 7 := fun fx => tra_stack_free_7 (fx:=fx) B LAWS HB.
Let ASS00_A : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trasegs B A_set_shadow_00 0 := fun fx => tra_set_shadow_00 (fx:=fx) B LAWS HB.
Let ASSF8_A : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trasegs B A_set_shadow_f8 248 := fun fx => tra_set_shadow_f8 (fx:=fx) B LAWS HB.
Let LIBCV : tra_rlibV_contract_all B := tra_RLIBCV B HB TL AMALLOC_A AFREE_A ASM1_A ASM2_A AREALLOC_A ASM7_A ASF7_A ASS00_A ASSF8_A.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD07.xst.
Let XFR : xst_frame_tfa xst := tra_xst_frame.
Let PF1_A : forall fx : YK11.FPState, @printf_first_tfa fx rc B xst := fun fx => tra_printf_first (fx:=fx) B HB LAWS HB.
Let PFN_A : forall fx : YK11.FPState, @printf_next_tfa fx rc B xst := fun fx => tra_printf_next (fx:=fx) B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD07.est.
Let ESTI : est_img_tfa est := tra_est_img.
Let ESTF : est_frame_tfa est := tra_est_frame.
Let FWS : fwrite_site_tfa B est := tra_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tra_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d7cd (strB "cli: cannot open "%string) nlB := tra_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d7e2 (strB "cli: read error on "%string) nlB := tra_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x158ff (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tra_fprintf_usage_site B HB LAWS HB.
Let EXS_A : forall fx : YK11.FPState, @exit_site_tfa fx rc B est xst := fun fx => tra_exit_site (fx:=fx) B HB LAWS.
Lemma tra_srealizes_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(forall a0 p data, in_argv inp = [a0; p] -> fs_lookup (in_fs inp) p = Some data -> rrfc_universe B (payload_len data)) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (CLOSED inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil HRU.
change target_alloc_limit with YA02.LIMIT.
exact (tra_srealizes B HB AMALLOC AFREE_A AICPY ARDCHK LIBCV xst XFR PF1_A PFN_A est ESTI ESTF FWS RFS FPO FPR FPU EXS_A
sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil HRU).
Qed.
End a.
Definition xs_of_inp (inp : ProcInput) : list (list Z) :=
match in_argv inp with
| [a0; p] => match fs_lookup (in_fs inp) p with Some data => run_xs (payload_len data) | None => [] end
| _ => []
end.
Lemma xs_of_inp_ok : forall inp, universe_ok (Tra_universe ++ xs_of_inp inp).
Proof.
intros inp. unfold xs_of_inp. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (rewrite app_nil_r; exact Tra_universe_ok).
destruct (fs_lookup (in_fs inp) p) as [data|]; [apply run_universe_ok | rewrite app_nil_r; exact Tra_universe_ok].
Qed.
Theorem tra_srealizes_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (CLOSED inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
apply (@tra_srealizes_rc (YN05.RunCeilOf (bv_unsigned sp) (valid_sp_window36 sp Hsp)) (xs_of_inp inp) (xs_of_inp_ok inp)
sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YN05.ceil_of_top_run _)).
intros a0 p data Hargv Hlk. unfold xs_of_inp. rewrite Hargv, Hlk. apply run_rrfc_universe.
Qed.
Theorem cgif_rgb_fuzzer_asan_equiv_lim : forall ls : Z, (SRC_LIM_MIN <= ls)%Z ->
forall en_s en_t inp,
valid_entry (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) en_s inp ->
valid_entry (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) en_t inp ->
valid_input inp ->
strong_equiv_error_free_budgets ls target_alloc_limit
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) en_s en_t inp.
Proof.
intros ls Hls [sp brk mb rnd] [sp' brk' mb' rnd'] inp Hens Hent Hinp.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hsp [Hbrk [Hmb Hfit]]]. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
eapply (shape_strong_equiv_efs_budgets ls target_alloc_limit src2segs _ _ sp brk mb rnd TSEGS _ _ sp' brk' mb' rnd' (SPEC inp) (CLOSED inp) inp).
- apply src2_realizes; assumption.
- apply tra_srealizes_top; assumption.
- apply spec_closed_eq.
Qed.
Theorem cgif_rgb_fuzzer_asan_equiv :
strong_universal_error_free_T
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. intros en_s en_t inp Hs Ht Hv. exact (cgif_rgb_fuzzer_asan_equiv_lim source_alloc_limit SRC_LIM_MIN_le_source en_s en_t inp Hs Ht Hv). Qed.
Theorem cgif_rgb_fuzzer_asan_equiv_sanitizer :
strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. intros en_s en_t inp Hs Ht Hv _. exact (cgif_rgb_fuzzer_asan_equiv_lim _ SRC_LIM_MIN_le_sanitizer en_s en_t inp Hs Ht Hv). Qed.
