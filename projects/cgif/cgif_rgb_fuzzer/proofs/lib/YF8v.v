(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YK11 YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YE2q YE3r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac ftac := YE2q.ftac.
Ltac msteps_done := YE2q.msteps_done.
Ltac gr := YE2q.gr.
Ltac stepbt F D tac := YE2q.stepbt F D tac.
Ltac stepbf F D tac := YE2q.stepbf F D tac.
Ltac stepld F D vv rdtac := YE2q.stepld F D vv rdtac.
Ltac stepov F D vv tac := YE2q.stepov F D vv tac.
Ltac stepsubw F D vv tac := YE2q.stepsubw F D vv tac.
Ltac steplw F D vv rdtac valtac := YE2q.steplw F D vv rdtac valtac.
Ltac stepsd F D aa vv atac vtac oktac := YE2q.stepsd F D aa vv atac vtac oktac.
Notation inW := YE2q.inW (only parsing).
Notation wl_kept := YE2q.wl_kept (only parsing).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil} {imgk : img}.
Definition iov_mem :=
ltac:(let b := eval cbv delta [YE2q.iov_mem] in YE2q.iov_mem in
let F := eval pattern YB0z.traguard_count, YB0z.traguard_start, YB0z.tramusl_tbl, YB0z.tramusl_text_count, YB0z.tramusl_text_start, YB0z.trasegs, YB0u.tratbl_rtA, YB0u.tratbl_rtA_build, YB0u.tratbl_rtB, YB0u.tratbl_rtB_build, YB0u.tratbl_rtC, YB0u.tratbl_rtC_build, YB0u.tratbl_rtD, YB0u.tratbl_rtD_build, YB0x.tratbl_rtF, YB0x.tratbl_rtF_build, YB0x.tratbl_rtG, YB0x.tratbl_rtG_build, YB0x.tratbl_rtK, YB0x.tratbl_rtK_build, YB0x.tratbl_rtM, YB0x.tratbl_rtM_build, YB10.tra_A_musl_memchr, YB10.tra_A_musl_memcmp, YB10.tra_A_musl_memcpy, YB10.tra_A_musl_memset, YB10.tra_A_musl_strnlen, YF8z.Tra_code, YF90.DRV_TRACES, YF90.TRA_DEPOT, YF90.TRA_ERRNO, YF90.TRA_GP, YF90.TRA_HASH, YF90.TRA_IAL_FLAG, YF90.TRA_IAL_HI, YF90.TRA_IAL_LO, YF90.TRA_IAL_W, YF90.TRA_INST, YF90.TRA_MAIN, YF90.TRA_MAIN_RA, YF90.TRA_OOM, YF90.TRA_STORE, YF90.TRA_TP, YF90.TRA_TR0, YF90.TRA_TSD, YF90.Tra_const, YF90.Tra_const_abs, YF90.Tra_const_shadow, YF90.Tra_const_sym, YF90.Tra_owned_static, YF90.Tra_zero_shadow, Asan.Asan_segment_000, Asan.Asan_segment_001, Asan.Asan_segment_002, Asan.Asan_segment_003, YF90.TraSyms, Asan.M.loaded_segments in b in
lazymatch F with ?f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => let b2 := eval cbv beta in (f (@tfxguard_count imgk) (@tfxguard_start imgk) (@tfxmusl_tbl imgk) (@tfxmusl_text_count imgk) (@tfxmusl_text_start imgk) (@tfxsegs imgk) (@tfxtbl_rtA imgk) (@tfxtbl_rtA_build imgk) (@tfxtbl_rtB imgk) (@tfxtbl_rtB_build imgk) (@tfxtbl_rtC imgk) (@tfxtbl_rtC_build imgk) (@tfxtbl_rtD imgk) (@tfxtbl_rtD_build imgk) (@tfxtbl_rtF imgk) (@tfxtbl_rtF_build imgk) (@tfxtbl_rtG imgk) (@tfxtbl_rtG_build imgk) (@tfxtbl_rtK imgk) (@tfxtbl_rtK_build imgk) (@tfxtbl_rtM imgk) (@tfxtbl_rtM_build imgk) (@tfx_A_musl_memchr imgk) (@tfx_A_musl_memcmp imgk) (@tfx_A_musl_memcpy imgk) (@tfx_A_musl_memset imgk) (@tfx_A_musl_strnlen imgk) (@Tfx_code imgk) (@DRV_TRACES imgk) (@TFX_DEPOT imgk) (@TFX_ERRNO imgk) TFX_GP (@TFX_HASH imgk) (@TFX_IAL_FLAG imgk) (@TFX_IAL_HI imgk) (@TFX_IAL_LO imgk) (@TFX_IAL_W imgk) (@TFX_INST imgk) (@TFX_MAIN imgk) (@TFX_MAIN_RA imgk) (@TFX_OOM imgk) (@TFX_STORE imgk) (@TFX_TP imgk) (@TFX_TR0 imgk) (@TFX_TSD imgk) (@Tfx_const imgk) (@Tfx_const_abs imgk) (@Tfx_const_shadow imgk) (@Tfx_const_sym imgk) (@Tfx_owned_static imgk) (@Tfx_zero_shadow imgk) (@tfx_segment_000 imgk) (@tfx_segment_001 imgk) (@tfx_segment_002 imgk) (@tfx_segment_003 imgk) (@TfxSyms imgk) (@tfxsegs imgk)) in exact b2 end).
Definition body_pre :=
ltac:(let b := eval cbv delta [YE2q.body_pre] in YE2q.body_pre in
let F := eval pattern YB0z.traguard_count, YB0z.traguard_start, YB0z.tramusl_tbl, YB0z.tramusl_text_count, YB0z.tramusl_text_start, YB0z.trasegs, YB0u.tratbl_rtA, YB0u.tratbl_rtA_build, YB0u.tratbl_rtB, YB0u.tratbl_rtB_build, YB0u.tratbl_rtC, YB0u.tratbl_rtC_build, YB0u.tratbl_rtD, YB0u.tratbl_rtD_build, YB0x.tratbl_rtF, YB0x.tratbl_rtF_build, YB0x.tratbl_rtG, YB0x.tratbl_rtG_build, YB0x.tratbl_rtK, YB0x.tratbl_rtK_build, YB0x.tratbl_rtM, YB0x.tratbl_rtM_build, YB10.tra_A_musl_memchr, YB10.tra_A_musl_memcmp, YB10.tra_A_musl_memcpy, YB10.tra_A_musl_memset, YB10.tra_A_musl_strnlen, YF8z.Tra_code, YF90.DRV_TRACES, YF90.TRA_DEPOT, YF90.TRA_ERRNO, YF90.TRA_GP, YF90.TRA_HASH, YF90.TRA_IAL_FLAG, YF90.TRA_IAL_HI, YF90.TRA_IAL_LO, YF90.TRA_IAL_W, YF90.TRA_INST, YF90.TRA_MAIN, YF90.TRA_MAIN_RA, YF90.TRA_OOM, YF90.TRA_STORE, YF90.TRA_TP, YF90.TRA_TR0, YF90.TRA_TSD, YF90.Tra_const, YF90.Tra_const_abs, YF90.Tra_const_shadow, YF90.Tra_const_sym, YF90.Tra_owned_static, YF90.Tra_zero_shadow, Asan.Asan_segment_000, Asan.Asan_segment_001, Asan.Asan_segment_002, Asan.Asan_segment_003, YF90.TraSyms, Asan.M.loaded_segments, YE2q.iov_mem in b in
lazymatch F with ?f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => let b2 := eval cbv beta in (f (@tfxguard_count imgk) (@tfxguard_start imgk) (@tfxmusl_tbl imgk) (@tfxmusl_text_count imgk) (@tfxmusl_text_start imgk) (@tfxsegs imgk) (@tfxtbl_rtA imgk) (@tfxtbl_rtA_build imgk) (@tfxtbl_rtB imgk) (@tfxtbl_rtB_build imgk) (@tfxtbl_rtC imgk) (@tfxtbl_rtC_build imgk) (@tfxtbl_rtD imgk) (@tfxtbl_rtD_build imgk) (@tfxtbl_rtF imgk) (@tfxtbl_rtF_build imgk) (@tfxtbl_rtG imgk) (@tfxtbl_rtG_build imgk) (@tfxtbl_rtK imgk) (@tfxtbl_rtK_build imgk) (@tfxtbl_rtM imgk) (@tfxtbl_rtM_build imgk) (@tfx_A_musl_memchr imgk) (@tfx_A_musl_memcmp imgk) (@tfx_A_musl_memcpy imgk) (@tfx_A_musl_memset imgk) (@tfx_A_musl_strnlen imgk) (@Tfx_code imgk) (@DRV_TRACES imgk) (@TFX_DEPOT imgk) (@TFX_ERRNO imgk) TFX_GP (@TFX_HASH imgk) (@TFX_IAL_FLAG imgk) (@TFX_IAL_HI imgk) (@TFX_IAL_LO imgk) (@TFX_IAL_W imgk) (@TFX_INST imgk) (@TFX_MAIN imgk) (@TFX_MAIN_RA imgk) (@TFX_OOM imgk) (@TFX_STORE imgk) (@TFX_TP imgk) (@TFX_TR0 imgk) (@TFX_TSD imgk) (@Tfx_const imgk) (@Tfx_const_abs imgk) (@Tfx_const_shadow imgk) (@Tfx_const_sym imgk) (@Tfx_owned_static imgk) (@Tfx_zero_shadow imgk) (@tfx_segment_000 imgk) (@tfx_segment_001 imgk) (@tfx_segment_002 imgk) (@tfx_segment_003 imgk) (@TfxSyms imgk) (@tfxsegs imgk) iov_mem) in exact b2 end).
Definition body_post := match imgk with K_tra => YE2q.body_post | K_trb => YE3r.body_post end.
Definition wl_inv :=
ltac:(let b := eval cbv delta [YE2q.wl_inv] in YE2q.wl_inv in
let F := eval pattern YB0z.traguard_count, YB0z.traguard_start, YB0z.tramusl_tbl, YB0z.tramusl_text_count, YB0z.tramusl_text_start, YB0z.trasegs, YB0u.tratbl_rtA, YB0u.tratbl_rtA_build, YB0u.tratbl_rtB, YB0u.tratbl_rtB_build, YB0u.tratbl_rtC, YB0u.tratbl_rtC_build, YB0u.tratbl_rtD, YB0u.tratbl_rtD_build, YB0x.tratbl_rtF, YB0x.tratbl_rtF_build, YB0x.tratbl_rtG, YB0x.tratbl_rtG_build, YB0x.tratbl_rtK, YB0x.tratbl_rtK_build, YB0x.tratbl_rtM, YB0x.tratbl_rtM_build, YB10.tra_A_musl_memchr, YB10.tra_A_musl_memcmp, YB10.tra_A_musl_memcpy, YB10.tra_A_musl_memset, YB10.tra_A_musl_strnlen, YF8z.Tra_code, YF90.DRV_TRACES, YF90.TRA_DEPOT, YF90.TRA_ERRNO, YF90.TRA_GP, YF90.TRA_HASH, YF90.TRA_IAL_FLAG, YF90.TRA_IAL_HI, YF90.TRA_IAL_LO, YF90.TRA_IAL_W, YF90.TRA_INST, YF90.TRA_MAIN, YF90.TRA_MAIN_RA, YF90.TRA_OOM, YF90.TRA_STORE, YF90.TRA_TP, YF90.TRA_TR0, YF90.TRA_TSD, YF90.Tra_const, YF90.Tra_const_abs, YF90.Tra_const_shadow, YF90.Tra_const_sym, YF90.Tra_owned_static, YF90.Tra_zero_shadow, Asan.Asan_segment_000, Asan.Asan_segment_001, Asan.Asan_segment_002, Asan.Asan_segment_003, YF90.TraSyms, Asan.M.loaded_segments, YE2q.iov_mem, YE2q.body_pre, YE2q.body_post in b in
lazymatch F with ?f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => let b2 := eval cbv beta in (f (@tfxguard_count imgk) (@tfxguard_start imgk) (@tfxmusl_tbl imgk) (@tfxmusl_text_count imgk) (@tfxmusl_text_start imgk) (@tfxsegs imgk) (@tfxtbl_rtA imgk) (@tfxtbl_rtA_build imgk) (@tfxtbl_rtB imgk) (@tfxtbl_rtB_build imgk) (@tfxtbl_rtC imgk) (@tfxtbl_rtC_build imgk) (@tfxtbl_rtD imgk) (@tfxtbl_rtD_build imgk) (@tfxtbl_rtF imgk) (@tfxtbl_rtF_build imgk) (@tfxtbl_rtG imgk) (@tfxtbl_rtG_build imgk) (@tfxtbl_rtK imgk) (@tfxtbl_rtK_build imgk) (@tfxtbl_rtM imgk) (@tfxtbl_rtM_build imgk) (@tfx_A_musl_memchr imgk) (@tfx_A_musl_memcmp imgk) (@tfx_A_musl_memcpy imgk) (@tfx_A_musl_memset imgk) (@tfx_A_musl_strnlen imgk) (@Tfx_code imgk) (@DRV_TRACES imgk) (@TFX_DEPOT imgk) (@TFX_ERRNO imgk) TFX_GP (@TFX_HASH imgk) (@TFX_IAL_FLAG imgk) (@TFX_IAL_HI imgk) (@TFX_IAL_LO imgk) (@TFX_IAL_W imgk) (@TFX_INST imgk) (@TFX_MAIN imgk) (@TFX_MAIN_RA imgk) (@TFX_OOM imgk) (@TFX_STORE imgk) (@TFX_TP imgk) (@TFX_TR0 imgk) (@TFX_TSD imgk) (@Tfx_const imgk) (@Tfx_const_abs imgk) (@Tfx_const_shadow imgk) (@Tfx_const_sym imgk) (@Tfx_owned_static imgk) (@Tfx_zero_shadow imgk) (@tfx_segment_000 imgk) (@tfx_segment_001 imgk) (@tfx_segment_002 imgk) (@tfx_segment_003 imgk) (@TfxSyms imgk) (@tfxsegs imgk) iov_mem body_pre body_post) in exact b2 end).
End a.
Goal forall {fx : YK11.FPState} {rc : YN05.RunCeil}, iov_mem (imgk := K_trb) = YE3r.iov_mem. Proof. intros; reflexivity. Qed.
Goal forall {fx : YK11.FPState} {rc : YN05.RunCeil}, body_pre (imgk := K_trb) = YE3r.body_pre. Proof. intros; reflexivity. Qed.
Goal forall {fx : YK11.FPState} {rc : YN05.RunCeil}, wl_inv (imgk := K_trb) = YE3r.wl_inv. Proof. intros; reflexivity. Qed.
Ltac img_gen_type_stdio_wloop_ty_k imgk T :=
let F := eval pattern YB0z.traguard_count, YB0z.traguard_start, YB0z.tramusl_tbl, YB0z.tramusl_text_count, YB0z.tramusl_text_start, YB0z.trasegs, YB0u.tratbl_rtA, YB0u.tratbl_rtA_build, YB0u.tratbl_rtB, YB0u.tratbl_rtB_build, YB0u.tratbl_rtC, YB0u.tratbl_rtC_build, YB0u.tratbl_rtD, YB0u.tratbl_rtD_build, YB0x.tratbl_rtF, YB0x.tratbl_rtF_build, YB0x.tratbl_rtG, YB0x.tratbl_rtG_build, YB0x.tratbl_rtK, YB0x.tratbl_rtK_build, YB0x.tratbl_rtM, YB0x.tratbl_rtM_build, YB10.tra_A_musl_memchr, YB10.tra_A_musl_memcmp, YB10.tra_A_musl_memcpy, YB10.tra_A_musl_memset, YB10.tra_A_musl_strnlen, YF8z.Tra_code, YF90.DRV_TRACES, YF90.TRA_DEPOT, YF90.TRA_ERRNO, YF90.TRA_GP, YF90.TRA_HASH, YF90.TRA_IAL_FLAG, YF90.TRA_IAL_HI, YF90.TRA_IAL_LO, YF90.TRA_IAL_W, YF90.TRA_INST, YF90.TRA_MAIN, YF90.TRA_MAIN_RA, YF90.TRA_OOM, YF90.TRA_STORE, YF90.TRA_TP, YF90.TRA_TR0, YF90.TRA_TSD, YF90.Tra_const, YF90.Tra_const_abs, YF90.Tra_const_shadow, YF90.Tra_const_sym, YF90.Tra_owned_static, YF90.Tra_zero_shadow, Asan.Asan_segment_000, Asan.Asan_segment_001, Asan.Asan_segment_002, Asan.Asan_segment_003, YF90.TraSyms, Asan.M.loaded_segments, YE2q.body_post, YE2q.body_pre, YE2q.iov_mem, YE2q.wl_inv in T in
lazymatch F with
| ?f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eval cbv beta in (f (@tfxguard_count imgk) (@tfxguard_start imgk) (@tfxmusl_tbl imgk) (@tfxmusl_text_count imgk) (@tfxmusl_text_start imgk) (@tfxsegs imgk) (@tfxtbl_rtA imgk) (@tfxtbl_rtA_build imgk) (@tfxtbl_rtB imgk) (@tfxtbl_rtB_build imgk) (@tfxtbl_rtC imgk) (@tfxtbl_rtC_build imgk) (@tfxtbl_rtD imgk) (@tfxtbl_rtD_build imgk) (@tfxtbl_rtF imgk) (@tfxtbl_rtF_build imgk) (@tfxtbl_rtG imgk) (@tfxtbl_rtG_build imgk) (@tfxtbl_rtK imgk) (@tfxtbl_rtK_build imgk) (@tfxtbl_rtM imgk) (@tfxtbl_rtM_build imgk) (@tfx_A_musl_memchr imgk) (@tfx_A_musl_memcmp imgk) (@tfx_A_musl_memcpy imgk) (@tfx_A_musl_memset imgk) (@tfx_A_musl_strnlen imgk) (@Tfx_code imgk) (@DRV_TRACES imgk) (@TFX_DEPOT imgk) (@TFX_ERRNO imgk) TFX_GP (@TFX_HASH imgk) (@TFX_IAL_FLAG imgk) (@TFX_IAL_HI imgk) (@TFX_IAL_LO imgk) (@TFX_IAL_W imgk) (@TFX_INST imgk) (@TFX_MAIN imgk) (@TFX_MAIN_RA imgk) (@TFX_OOM imgk) (@TFX_STORE imgk) (@TFX_TP imgk) (@TFX_TR0 imgk) (@TFX_TSD imgk) (@Tfx_const imgk) (@Tfx_const_abs imgk) (@Tfx_const_shadow imgk) (@Tfx_const_sym imgk) (@Tfx_owned_static imgk) (@Tfx_zero_shadow imgk) (@tfx_segment_000 imgk) (@tfx_segment_001 imgk) (@tfx_segment_002 imgk) (@tfx_segment_003 imgk) (@TfxSyms imgk) (@tfxsegs imgk) (body_post (imgk:=imgk)) (body_pre (imgk:=imgk)) (iov_mem (imgk:=imgk)) (wl_inv (imgk:=imgk)))
end.
Ltac img_gen_type_stdio_wloop_k imgk c := let T := type of c in let T' := img_gen_type_stdio_wloop_ty_k imgk T in exact T'.
Ltac img_gen_type_stdio_wloop c := lazymatch goal with imgk : img |- _ => img_gen_type_stdio_wloop_k imgk c end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil} {imgk : img}.

Lemma F_17c1c :
ltac:(let T := type of YE2q.F_17c1c in
let F := eval pattern (0x96ff8%bv : word) in T in
lazymatch F with ?f _ =>
let T1 := eval cbv beta in (f (Z_to_bv 64 (0x96ff8 + @D_10ec imgk))) in
let T2 := img_gen_type_stdio_wloop_ty_k imgk T1 in exact T2 end).
Proof.
destruct imgk.
- pose proof YE2q.F_17c1c as H_.
replace (0x96ff8%bv : word) with (Z_to_bv 64 (0x96ff8 + @D_10ec K_tra)) in H_ by (apply bv_eq; reflexivity).
(exact H_).
- pose proof YE3r.F_17c1c as H_.
replace (0x980e4%bv : word) with (Z_to_bv 64 (0x96ff8 + @D_10ec K_trb)) in H_ by (apply bv_eq; reflexivity).
(exact H_).
Qed.
Lemma after_w1 :
ltac:(let T := type of YE2q.after_w1 in
let F := eval pattern (0x96f74)%Z, (0x96f7c)%Z, (0x97008)%Z in T in
lazymatch F with ?f _ _ _ =>
let T1 := eval cbv beta in (f (0x96f74 + @D_10ec imgk)%Z (0x96f7c + @D_10ec imgk)%Z (0x97008 + @D_10ec imgk)%Z) in
let T2 := img_gen_type_stdio_wloop_ty_k imgk T1 in exact T2 end).
Proof.
destruct imgk.
- pose proof YE2q.after_w1 as H_.
(exact H_).
- pose proof YE3r.after_w1 as H_.
(exact H_).
Qed.
Lemma after_w2 :
ltac:(let T := type of YE2q.after_w2 in
let F := eval pattern (0x96ffc)%Z, (0x96f7c)%Z, (0x97008)%Z in T in
lazymatch F with ?f _ _ _ =>
let T1 := eval cbv beta in (f (0x96ffc + @D_10ec imgk)%Z (0x96f7c + @D_10ec imgk)%Z (0x97008 + @D_10ec imgk)%Z) in
let T2 := img_gen_type_stdio_wloop_ty_k imgk T1 in exact T2 end).
Proof.
destruct imgk.
- pose proof YE2q.after_w2 as H_.
(exact H_).
- pose proof YE3r.after_w2 as H_.
(exact H_).
Qed.
Lemma body_A : ltac:(img_gen_type_stdio_wloop YE2q.body_A).
Proof. destruct imgk; [(exact YE2q.body_A) | (exact YE3r.body_A)]. Qed.
Lemma body_B : ltac:(img_gen_type_stdio_wloop YE2q.body_B).
Proof. destruct imgk; [(exact YE2q.body_B) | (exact YE3r.body_B)]. Qed.
Lemma body_C : ltac:(img_gen_type_stdio_wloop YE2q.body_C).
Proof. destruct imgk; [(exact YE2q.body_C) | (exact YE3r.body_C)]. Qed.
Lemma ms_read_bytes_of_rdn : ltac:(img_gen_type_stdio_wloop YE2q.ms_read_bytes_of_rdn).
Proof. destruct imgk; [(exact YE2q.ms_read_bytes_of_rdn) | (exact YE3r.ms_read_bytes_of_rdn)]. Qed.
Lemma ms_read_u64_of_rdn : ltac:(img_gen_type_stdio_wloop YE2q.ms_read_u64_of_rdn).
Proof. destruct imgk; [(exact YE2q.ms_read_u64_of_rdn) | (exact YE3r.ms_read_u64_of_rdn)]. Qed.
Lemma rdn_advance : ltac:(img_gen_type_stdio_wloop YE2q.rdn_advance).
Proof. destruct imgk; [(exact YE2q.rdn_advance) | (exact YE3r.rdn_advance)]. Qed.
Lemma rdn_agree : ltac:(img_gen_type_stdio_wloop YE2q.rdn_agree).
Proof. destruct imgk; [(exact YE2q.rdn_agree) | (exact YE3r.rdn_agree)]. Qed.
Lemma t_alt_wall' : ltac:(img_gen_type_stdio_wloop YE2q.t_alt_wall').
Proof. destruct imgk; [(exact YE2q.t_alt_wall') | (exact YE3r.t_alt_wall')]. Qed.
Lemma wl_entry_pend :
ltac:(let T := type of YE2q.wl_entry_pend in
let F := eval pattern (0x96f7c)%Z, (0x96f70)%Z in T in
lazymatch F with ?f _ _ =>
let T1 := eval cbv beta in (f (0x96f7c + @D_10ec imgk)%Z (0x96f70 + @D_10ec imgk)%Z) in
let T2 := img_gen_type_stdio_wloop_ty_k imgk T1 in exact T2 end).
Proof.
destruct imgk.
- pose proof YE2q.wl_entry_pend as H_.
(exact H_).
- pose proof YE3r.wl_entry_pend as H_.
(exact H_).
Qed.
End d.
Notation skipn_all_nil := YE2q.skipn_all_nil (only parsing).
Goal True. Proof. let T1 := type of @YE2q.skipn_all_nil in let T2 := type of @YE3r.skipn_all_nil in constr_eq T1 T2. exact I. Qed.
Notation word_to_nat_zv := YE2q.word_to_nat_zv (only parsing).
Goal True. Proof. let T1 := type of @YE2q.word_to_nat_zv in let T2 := type of @YE3r.word_to_nat_zv in constr_eq T1 T2. exact I. Qed.
