(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1 :=
lazymatch goal with |- getr _ ?r = _ =>
let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q;
lazymatch goal with
| |- alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew ?Ex ?n) + ?c)) (Z_to_bv 64 3)) (ew _ 38) = _ =>
unfold w64; apply (shq_word Ex n 38 c _ SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia
| |- context [alu64] => idtac "REGVE-ALU" r; fail
| |- _ =>
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| idtac "REGVE-FAIL" r; fail ]
end end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition AF_E2 : Z := 0xf9c.
Definition AF_E3 : Z := 0x103c.
Definition af_regs_atE (B : asyms) (regs regs1 : bvmap 5 word) (g : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 224) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (g + 88) /\ getr regs1 21 = w64 SB /\ getr regs1 22 = w64 (SB + (g + 88) / 8).
Definition af_regs_at0 (B : asyms) (regs regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (spZ regs - 224) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B).
Definition AF_RET0_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1,
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at0 B regs regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_RET)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_E3_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at0 B regs regs1 -> getr regs1 8 = w64 (g + 88) -> getr regs1 22 = w64 SB -> af_s1_at regs1 g -> getr regs1 16 = w64 cfp ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = Some fn -> fr_ptr fn = nw ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_E3)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_E2_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw ->
getr regs1 16 = w64 cfp -> getr regs1 17 = w64 (cfp + 16) ->
getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = Some fn -> fr_ptr fn = nw -> cg_ihead s1 = i ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_E2)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Lemma tcgif_vals_upd_frame : forall s i f f',
nth_error (cg_frames s) i = Some (Some f) -> fr_ptr f' = fr_ptr f -> tcgif_vals hw (upd_frame s i f') = tcgif_vals hw s.
Proof.
intros s i f f' Hi Hp. unfold upd_frame. rewrite tcgif_vals_set_frames. unfold tcgif_vals.
assert (E : forall k, frame_ptr (nth k (list_set (cg_frames s) i (Some f')) None) = frame_ptr (nth k (cg_frames s) None)).
{ intros k. destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite nth_list_set_same by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
rewrite (nth_error_nth _ _ _ Hi). cbn. exact Hp.
- rewrite YI5v.nth_list_set_other by lia. reflexivity. }
rewrite !E. reflexivity.
Qed.
Lemma tcgif_vals_ins_frame : forall s i f', (i < 3)%nat -> length (cg_frames s) = 3%nat ->
tcgif_vals hw (upd_frame s i f') = list_set (tcgif_vals hw s) i (fr_ptr f').
Proof.
intros s i f' Hi Hlen. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]] eqn:Hfr; cbn in Hlen; try discriminate.
unfold upd_frame. rewrite Hfr. unfold tcgif_vals, set_frames. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead].
rewrite Hfr. destruct i as [|[|[|i]]]; try lia; reflexivity.
Qed.
Lemma tcgif_vals_set_ihead_ls : forall s ih, tcgif_vals hw (set_ihead s ih) = list_set (tcgif_vals hw s) 16 ih.
Proof. intros. reflexivity. Qed.
Lemma tcgif_vals_set_cur_ls : forall s c, tcgif_vals hw (cl_set_cur s c) = list_set (tcgif_vals hw s) 15 c.
Proof. intros. reflexivity. Qed.
Lemma traw_vals_upd_frame : forall g s i f', traw_vals wfn g (upd_frame s i f') = traw_vals wfn g s.
Proof. intros. reflexivity. Qed.
Lemma traw_vals_set_ihead : forall g s ih, traw_vals wfn g (set_ihead s ih) = traw_vals wfn g s.
Proof. intros. reflexivity. Qed.
Lemma traw_vals_set_cur : forall g s c, traw_vals wfn g (cl_set_cur s c) = traw_vals wfn g s.
Proof. intros. reflexivity. Qed.
Lemma tframes_at_upd : forall m m' s i (f : option frame_st) f',
(forall x, In (Some x) (cg_frames s) -> obj_at SEGS m (fr_ptr x) LAY_Frame (frame_vals x)) ->
nth_error (cg_frames s) i = Some f ->
obj_at SEGS m' (fr_ptr f') LAY_Frame (frame_vals f') ->
(forall j x, nth_error (cg_frames s) j = Some (Some x) -> j <> i ->
forall k, 0 <= k < 40 -> mbyte SEGS m' (fr_ptr x + k) = mbyte SEGS m (fr_ptr x + k)) ->
forall x, In (Some x) (cg_frames (upd_frame s i f')) -> obj_at SEGS m' (fr_ptr x) LAY_Frame (frame_vals x).
Proof.
intros m m' s i f f' Hfr Hi Hnew Hkept x Hx. unfold upd_frame, set_frames in Hx. cbn [cg_frames] in Hx.
destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hne)].
- injection Hx' as ->. exact Hnew.
- apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hfr x ltac:(eapply nth_error_In; exact Hj)) lay_inside_Frame).
intros k Hk. apply (Hkept j x Hj Hne k Hk).
Qed.
Lemma tframes_at_upd2 : forall m m' s i1 i2 (f1 : option frame_st) f1' (f2 : option frame_st) f2',
(forall x, In (Some x) (cg_frames s) -> obj_at SEGS m (fr_ptr x) LAY_Frame (frame_vals x)) ->
nth_error (cg_frames s) i1 = Some f1 -> nth_error (cg_frames s) i2 = Some f2 -> i1 <> i2 ->
obj_at SEGS m' (fr_ptr f1') LAY_Frame (frame_vals f1') ->
obj_at SEGS m' (fr_ptr f2') LAY_Frame (frame_vals f2') ->
(forall j x, nth_error (cg_frames s) j = Some (Some x) -> j <> i1 -> j <> i2 ->
forall k, 0 <= k < 40 -> mbyte SEGS m' (fr_ptr x + k) = mbyte SEGS m (fr_ptr x + k)) ->
forall x, In (Some x) (cg_frames (upd_frame (upd_frame s i1 f1') i2 f2')) -> obj_at SEGS m' (fr_ptr x) LAY_Frame (frame_vals x).
Proof.
intros m m' s i1 i2 f1 f1' f2 f2' Hfr H1 H2 Hne Ho1 Ho2 Hkept x Hx.
unfold upd_frame, set_frames in Hx. cbn [cg_frames] in Hx.
destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hj2)]; [injection Hx' as ->; exact Ho2|].
destruct (Nat.eq_dec j i1) as [->|Hj1].
- rewrite YI5v.nth_error_list_set_same in Hj by (apply (proj1 (nth_error_Some _ _)); rewrite H1; discriminate).
injection Hj as ->. exact Ho1.
- rewrite YI5v.nth_error_list_set_other in Hj by lia.
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hfr x ltac:(eapply nth_error_In; exact Hj)) lay_inside_Frame).
intros k Hk. apply (Hkept j x Hj Hj1 Hj2 k Hk).
Qed.
Lemma af_obj_ok_upd_frame : forall s s1 N i f f',
af_obj_ok s s1 N -> nth_error (cg_frames s1) i = Some (Some f) -> frame_wf (cg_attr s1) f' -> af_obj_ok s (upd_frame s1 i f') N.
Proof.
intros s s1 N i f f' (HWF & H) Hi Hf. split; [exact (cgif_wf_upd_frame s1 N i f f' HWF Hi Hf) | exact H].
Qed.
Lemma af_obj_ok_set_cur : forall s s1 N c, af_obj_ok s s1 N -> af_obj_ok s (cl_set_cur s1 c) N.
Proof. intros s s1 N c (HWF & H). split; [exact HWF | exact H]. Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma af_frames_sep : forall ly S W mem md g s1 N cb j1 j2 f1 f2,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ cb) -> length (cg_frames s1) = 3%nat ->
nth_error (cg_frames s1) j1 = Some (Some f1) -> nth_error (cg_frames s1) j2 = Some (Some f2) -> (j1 < j2)%nat ->
fr_ptr f1 + 40 <= fr_ptr f2 \/ fr_ptr f2 + 40 <= fr_ptr f1.
Proof.
intros ly S W mem md g s1 N cb j1 j2 f1 f2 HAR HP Hlen H1 H2 Hlt.
destruct (cg_frames s1) as [|o0 [|o1 [|o2 [|x l]]]] eqn:Hfr; cbn in Hlen; try discriminate.
unfold cgif_blocks in HP. rewrite Hfr, frames_blocks_3 in HP.
assert (FB : forall f, In (fr_ptr f, FRAME_SIZE) (frames_blocks N [Some f])) by (intros f; rewrite frames_blocks_some; left; reflexivity).
assert (D : forall l1 l2, Permutation (ablocks B ly S) (l1 ++ l2) -> In (fr_ptr f1, FRAME_SIZE) l1 -> In (fr_ptr f2, FRAME_SIZE) l2 ->
fr_ptr f1 + 40 <= fr_ptr f2 \/ fr_ptr f2 + 40 <= fr_ptr f1).
{ intros l1 l2 HP' Ha Hb. pose proof (sep_app B LAWS ly S W mem md _ _ l1 l2 HAR HP' Ha Hb) as X.
unfold zdisjoint, block_rng in X. cbn [fst snd] in X. change (req_size FRAME_SIZE) with 40 in X. lia. }
destruct j1 as [|[|[|j1]]]; destruct j2 as [|[|[|j2]]]; cbn in H1, H2; try lia; try (destruct j2; discriminate); try (destruct j1; discriminate);
injection H1 as ->; injection H2 as ->.
- apply (D (((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1) ++ frames_blocks N [Some f1]) (frames_blocks N [Some f2] ++ frames_blocks N [o2] ++ cb)).
+ eapply Permutation_trans; [exact HP|]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. apply Permutation_refl.
+ apply in_app_iff. right. apply FB.
+ apply in_app_iff. left. apply FB.
- apply (D (((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1) ++ frames_blocks N [Some f1] ++ frames_blocks N [o1]) (frames_blocks N [Some f2] ++ cb)).
+ eapply Permutation_trans; [exact HP|]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. apply Permutation_refl.
+ apply in_app_iff. right. apply in_app_iff. left. apply FB.
+ apply in_app_iff. left. apply FB.
- apply (D (((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1) ++ frames_blocks N [o0] ++ frames_blocks N [Some f1]) (frames_blocks N [Some f2] ++ cb)).
+ eapply Permutation_trans; [exact HP|]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. apply Permutation_refl.
+ apply in_app_iff. right. apply in_app_iff. right. apply FB.
+ apply in_app_iff. left. apply FB.
Qed.
Lemma af_frames_sep2 : forall ly S W mem md g s1 N cb j1 j2 f1 f2,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ cb) -> length (cg_frames s1) = 3%nat ->
nth_error (cg_frames s1) j1 = Some (Some f1) -> nth_error (cg_frames s1) j2 = Some (Some f2) -> j1 <> j2 ->
fr_ptr f1 + 40 <= fr_ptr f2 \/ fr_ptr f2 + 40 <= fr_ptr f1.
Proof.
intros ly S W mem md g s1 N cb j1 j2 f1 f2 HAR HP Hlen H1 H2 Hne.
destruct (Nat.lt_ge_cases j1 j2) as [Hlt | Hge].
- exact (af_frames_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HP Hlen H1 H2 Hlt).
- pose proof (af_frames_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HP Hlen H2 H1 ltac:(lia)) as X. lia.
Qed.
End d.
Lemma mod8_of_16 : forall g k, g mod 16 = 0 -> (g + 8 * k) mod 8 = 0.
Proof. intros g k Hg. pose proof (Z.div_mod g 16 ltac:(lia)) as E. replace (g + 8 * k) with ((2 * (g / 16) + k) * 8) by lia. apply Z_mod_mult. Qed.
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_lcE_ok : forall E (m : word -> option byte) sp0 g cfp a4v,
af_locsE m sp0 g cfp a4v ->
ew E 32 = Z_to_bv 64 g -> ew E 38 = Z_to_bv 64 SB -> ew E 46 = Z_to_bv 64 cfp -> ew E 67 = Z_to_bv 64 a4v ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling -> 0 <= a4v < 2 ^ 64 ->
Forall (YP09.chunk_ok SEGS E m (sp0 - 224 - 0)) af_lcE.
Proof.
intros E m sp0 g cfp a4v (L1 & L3 & L4 & L5 & L6 & L7 & L8 & L9) E32 E38 E46 E67 Hg0 Hgc Hc0 Hcc Ha4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (D1 : forall o, 0 <= o <= 96 -> sv_denot E (shq 32 o) = Z_to_bv 64 (SB + (g + o) / 8) /\ 0 <= SB + (g + o) / 8 < 2 ^ 64).
{ intros o Ho. split; [apply (denot_shx E 32 38 o g SB E32 E38); unfold SB; lia|].
assert (Hd : 0 <= (g + o) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia. }
assert (D2 : sv_denot E (shq 46 16) = Z_to_bv 64 (SB + (cfp + 16) / 8) /\ 0 <= SB + (cfp + 16) / 8 < 2 ^ 64).
{ split; [apply (denot_shx E 46 38 16 cfp SB E46 E38); unfold SB; lia|].
assert (Hd : 0 <= (cfp + 16) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia. }
replace (sp0 - 224 - 0) with (sp0 - 224) by lia. unfold af_lcE. change (2 ^ 64) with (2 ^ (8 * Z.of_N 8)) in D1, D2, Ha4.
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 ?e)) =>
lazymatch e with
| shq 32 ?o => destruct (D1 o ltac:(lia)) as [Dd Dr]; apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e _ Dd Dr); [cbn; lia | assumption]
| shq 46 16 => destruct D2 as [Dd Dr]; apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e _ Dd Dr); [cbn; lia | assumption]
| SOff 32 ?o => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e (g + o));
[ cbn [sv_denot]; rewrite E32, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | assumption ]
| SOff 46 0 => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e cfp);
[ cbn [sv_denot]; rewrite E46, unsigned_lit_small, Z.add_0_r by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | assumption ]
| SOff 46 ?o => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e (cfp + o));
[ cbn [sv_denot]; rewrite E46, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | assumption ]
| SOff 67 0 => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e a4v);
[ cbn [sv_denot]; rewrite E67, unsigned_lit_small, Z.add_0_r by exact Ha4; reflexivity | exact Ha4 | cbn; lia | assumption ]
end end.
Qed.
End e.
End b.
End a.
