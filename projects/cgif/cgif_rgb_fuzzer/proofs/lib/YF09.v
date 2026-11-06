(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YK11 YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YB0d YB18.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac rwH := YB0d.rwH.
Ltac unorm := YB0d.unorm.
Ltac mnorm := YB0d.mnorm.
Ltac cond_lia := YB0d.cond_lia.
Notation TSEGS := tfxsegs (only parsing).
Notation memk := YB0d.memk (only parsing).
Notation sb_ := YB0d.sb_ (only parsing).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil} {imgk : img}.
Definition mcH := match imgk with K_tra => YB0d.mcH | K_trb => YB18.mcH end.
End a.
Ltac img_gen_typeMemcpyBase_ty_k imgk T :=
let F := eval pattern YB0z.traguard_count, YB0z.traguard_start, YB0z.tramusl_tbl, YB0z.tramusl_text_count, YB0z.tramusl_text_start, YB0z.trasegs, YB0u.tratbl_rtA, YB0u.tratbl_rtA_build, YB0u.tratbl_rtB, YB0u.tratbl_rtB_build, YB0u.tratbl_rtC, YB0u.tratbl_rtC_build, YB0u.tratbl_rtD, YB0u.tratbl_rtD_build, YB0x.tratbl_rtF, YB0x.tratbl_rtF_build, YB0x.tratbl_rtG, YB0x.tratbl_rtG_build, YB0x.tratbl_rtK, YB0x.tratbl_rtK_build, YB0x.tratbl_rtM, YB0x.tratbl_rtM_build, YB10.tra_A_musl_memchr, YB10.tra_A_musl_memcmp, YB10.tra_A_musl_memcpy, YB10.tra_A_musl_memset, YB10.tra_A_musl_strnlen, YF8z.Tra_code, YF90.DRV_TRACES, YF90.TRA_DEPOT, YF90.TRA_ERRNO, YF90.TRA_GP, YF90.TRA_HASH, YF90.TRA_IAL_FLAG, YF90.TRA_IAL_HI, YF90.TRA_IAL_LO, YF90.TRA_IAL_W, YF90.TRA_INST, YF90.TRA_MAIN, YF90.TRA_MAIN_RA, YF90.TRA_OOM, YF90.TRA_STORE, YF90.TRA_TP, YF90.TRA_TR0, YF90.TRA_TSD, YF90.Tra_const, YF90.Tra_const_abs, YF90.Tra_const_shadow, YF90.Tra_const_sym, YF90.Tra_owned_static, YF90.Tra_zero_shadow, Asan.Asan_segment_000, Asan.Asan_segment_001, Asan.Asan_segment_002, Asan.Asan_segment_003, YF90.TraSyms, Asan.M.loaded_segments, YB0d.mcH in T in
lazymatch F with
| ?f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eval cbv beta in (f (@tfxguard_count imgk) (@tfxguard_start imgk) (@tfxmusl_tbl imgk) (@tfxmusl_text_count imgk) (@tfxmusl_text_start imgk) (@tfxsegs imgk) (@tfxtbl_rtA imgk) (@tfxtbl_rtA_build imgk) (@tfxtbl_rtB imgk) (@tfxtbl_rtB_build imgk) (@tfxtbl_rtC imgk) (@tfxtbl_rtC_build imgk) (@tfxtbl_rtD imgk) (@tfxtbl_rtD_build imgk) (@tfxtbl_rtF imgk) (@tfxtbl_rtF_build imgk) (@tfxtbl_rtG imgk) (@tfxtbl_rtG_build imgk) (@tfxtbl_rtK imgk) (@tfxtbl_rtK_build imgk) (@tfxtbl_rtM imgk) (@tfxtbl_rtM_build imgk) (@tfx_A_musl_memchr imgk) (@tfx_A_musl_memcmp imgk) (@tfx_A_musl_memcpy imgk) (@tfx_A_musl_memset imgk) (@tfx_A_musl_strnlen imgk) (@Tfx_code imgk) (@DRV_TRACES imgk) (@TFX_DEPOT imgk) (@TFX_ERRNO imgk) TFX_GP (@TFX_HASH imgk) (@TFX_IAL_FLAG imgk) (@TFX_IAL_HI imgk) (@TFX_IAL_LO imgk) (@TFX_IAL_W imgk) (@TFX_INST imgk) (@TFX_MAIN imgk) (@TFX_MAIN_RA imgk) (@TFX_OOM imgk) (@TFX_STORE imgk) (@TFX_TP imgk) (@TFX_TR0 imgk) (@TFX_TSD imgk) (@Tfx_const imgk) (@Tfx_const_abs imgk) (@Tfx_const_shadow imgk) (@Tfx_const_sym imgk) (@Tfx_owned_static imgk) (@Tfx_zero_shadow imgk) (@tfx_segment_000 imgk) (@tfx_segment_001 imgk) (@tfx_segment_002 imgk) (@tfx_segment_003 imgk) (@TfxSyms imgk) (@tfxsegs imgk) (mcH (imgk:=imgk)))
end.
Ltac img_gen_typeMemcpyBase_k imgk c := let T := type of c in let T' := img_gen_typeMemcpyBase_ty_k imgk T in exact T'.
Ltac img_gen_typeMemcpyBase c := lazymatch goal with imgk : img |- _ => img_gen_typeMemcpyBase_k imgk c end.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil} {imgk : img}.
Lemma Hn : ltac:(img_gen_typeMemcpyBase YB0d.Hn).
Proof. destruct imgk; [(exact YB0d.Hn) | (exact YB18.Hn)]. Qed.
Lemma Hnwd : ltac:(img_gen_typeMemcpyBase YB0d.Hnwd).
Proof. destruct imgk; [(exact YB0d.Hnwd) | (exact YB18.Hnwd)]. Qed.
Lemma Hnws : ltac:(img_gen_typeMemcpyBase YB0d.Hnws).
Proof. destruct imgk; [(exact YB0d.Hnws) | (exact YB18.Hnws)]. Qed.
Lemma MCH : ltac:(img_gen_typeMemcpyBase YB0d.MCH).
Proof. destruct imgk; [(exact YB0d.MCH) | (exact YB18.MCH)]. Qed.
Lemma mc_lw : ltac:(img_gen_typeMemcpyBase YB0d.mc_lw).
Proof. destruct imgk; [(exact YB0d.mc_lw) | (exact YB18.mc_lw)]. Qed.
Lemma mc_sw : ltac:(img_gen_typeMemcpyBase YB0d.mc_sw).
Proof. destruct imgk; [(exact YB0d.mc_sw) | (exact YB18.mc_sw)]. Qed.
Lemma memk_n : ltac:(img_gen_typeMemcpyBase YB0d.memk_n).
Proof. destruct imgk; [(exact YB0d.memk_n) | (exact YB18.memk_n)]. Qed.
Lemma sw_val_plain : ltac:(img_gen_typeMemcpyBase YB0d.sw_val_plain).
Proof. destruct imgk; [(exact YB0d.sw_val_plain) | (exact YB18.sw_val_plain)]. Qed.
End b.
