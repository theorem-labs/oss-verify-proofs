(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACel ACer ACfm ACf5 ACf9 ACf7 ACf8 ACf6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Variable PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis PXK : forall ly bl (W : world tfibsegs) (m m' : word -> option byte) (md : Model) mat,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
PX ly bl W m md -> PX ly bl W m' (with_vm_backing (m_vm_lazy md) mat md).
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac add_flag_regionRT HS AG E87 Hp HFLrng HFLown HnoF :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 87%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E87, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoF fl); [lia | exact HFLown] | match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac wrangeRT AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; lazymatch goal with FFS : LLVMF_STK = _ |- _ => clear - Hr FFS; lia end
| left; right; right; right; exists 2, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeRT" ]
| ]);
destruct Hin.
Lemma rt_XP_aux : True -> rt_from B MT FP (rt_postP B MT FP PX) ss_X (INV_XP B MT PX).
Proof.
intros _. rt_prelude.
pose proof HINV as (Hk3 & Hacc & HPerm3 & HPX). cbn [c_ly c_S] in HPerm3. cbn [c_T] in Hacc.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJ3) Hfin3) as (HFLpres' & HFLown' & HFLrng'). rewrite ?EFL3 in HFLpres'. rewrite ?EFL3 in HFLown'. rewrite ?EFL3 in HFLrng'. fold FL in HFLpres', HFLown', HFLrng'.
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HFpres3 a Ha))).
fs_rwF HS E88 HFSpres3.
add_flag_regionRT HS AG E87 HFLpres' HFLrng' HFLown' HnoF.
aj_run_flag_sh tfibtbl_lib_ok HS HJ3; [clear; lia | wrangeRT AG fpos F EFA3 EFL3 | flag0 E87 EFL3 |].
rreg HS (1%bv : bv 5) Rra. rreg HS (10%bv : bv 5) Ra0.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold rt_postP. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T].
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ ?kx =>
lazymatch goal with |- exists ly' S' regs' mem' md' k', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx, kx end end.
split.
{ unfold cfg_at. rewrite Rra. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 1%nat) by lia.
rewrite (EE 1%nat 1%bv eq_refl). rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
rewrite Hra1. unfold raZ in Hra. unfold w64. rewrite <- Hra, Z_to_bv_bv_unsigned. reflexivity. }
split; [cbn [ms_mem]; apply (ajournal_materialize tfibsegs _ LAWS tfib_segs_low); exact HJ3|].
split; [exact Hk3|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [rewrite Ra0; reflexivity|].
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); exact HPerm3|].
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact (mo_le_mono MT MTL _ _ _ _ HMLE Hacc)|].
lazymatch goal with HFrx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ ?m1) |- _ =>
unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3);
eapply PXK; [| first [exact HPX | eapply PXK; [intros; reflexivity | exact HPX]]];
intros a Ha; apply aview_eq_of; apply HFrx;
pose proof (tfib_img_range a Ha) as Har; rewrite unsigned_lit_small by (clear - Har; lia);
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first [ clear - Hrg Har Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img HFLrng'; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia
| match goal with |- ?g => idtac "PXK-FAIL" g end ]
|]);
destruct Hin end.
Qed.
Lemma rt_XP : rt_from B MT FP (rt_postP B MT FP PX) ss_X (INV_XP B MT PX).
Proof. exact (rt_XP_aux I). Qed.
End c.
Lemma rt_X (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) :
ameter_laws MT -> TfibLib B -> AR_laws tfibsegs B -> model_laws (as_universe B) -> astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B ->
ameter_fs_laws MT -> rt_from B MT FP (rt_post B MT FP) ss_X (INV_X B MT).
Proof.
intros MTL TL LAWS ML ASF FFL MTF cx.
exact (rt_XP B MT MTL FP TL LAWS ML ASF FFL MTF (fun _ _ _ _ _ => hdr_fail cx) ltac:(intros; assumption) cx).
Qed.
End b.
