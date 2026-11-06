(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCjp YCh9 YChb YCj1 YCjr YCj3 YCgw YCh0 YCgy YCgx.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition AF_E2 : Z := 0x1180.
Definition AF_E3 : Z := 0x1234.
Definition af_regs_atE (B : asyms) (regs regs1 : bvmap 5 word) (g : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 224) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (g + 88) /\ getr regs1 21 = w64 SB /\ getr regs1 22 = w64 (SB + (g + 88) / 8).
Definition af_lcE : list YP09.chunk := [YP09.mkChunk 56 (CVal 8 (SOff 67 0))].
Definition AF_E3_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_atE B regs regs1 g -> getr regs1 9 = w64 cfp -> getr regs1 23 = w64 nw -> getr regs1 11 = w64 (g + 8 * i) ->
getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 224 + 56) 8 (Z.land fattr 4) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = Some fn -> fr_ptr fn = nw ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_E3)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_E2_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_atE B regs regs1 g -> getr regs1 18 = w64 g -> getr regs1 9 = w64 cfp -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw ->
getr regs1 19 = w64 (cfp + 16) -> getr regs1 25 = w64 (SB + (cfp + 16) / 8) -> getr regs1 11 = w64 (g + 8 * i) ->
getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 224 + 56) 8 (Z.land fattr 4) ->
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
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_lcE_ok : forall E (m : word -> option byte) sp0 a4v,
val_mem SEGS m (sp0 - 224 + 56) 8 a4v -> ew E 67 = Z_to_bv 64 a4v -> 0 <= a4v < 2 ^ 64 ->
Forall (YP09.chunk_ok SEGS E m (sp0 - 224 - 0)) af_lcE.
Proof.
intros E m sp0 a4v HL E67 Ha4. change (2 ^ 64) with (2 ^ (8 * Z.of_N 8)) in Ha4. replace (sp0 - 224 - 0) with (sp0 - 224) by lia.
unfold af_lcE. apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E m (sp0 - 224) 56 8 (SOff 67 0) a4v);
[ cbn [sv_denot]; rewrite E67, unsigned_lit_small, Z.add_0_r by exact Ha4; reflexivity | exact Ha4 | cbn; lia | exact HL ].
Qed.
Lemma af_reseedE : forall pc sregs wlo whi ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 more,
let a4v := Z.land fattr 4 in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 ->
getr regs1 2 = w64 (spZ regs - 224) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 224 + 56) 8 a4v ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regions 0 true af_lcE (cg_ihead s1) wlo whi) = true ->
st_ok_pi SEGS VAL E (ss_af pc sregs 0 true af_lcE (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 more a4v E
CX MID Rsp HL Hwlo Hwhi HREG HWFR.
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof (proj1 HJ) as HAR1. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing1 : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _).
change (req_size CGIF_SIZE) with 96 in Hgceil, HgP.
pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO) as HFO1.
assert (Rsp' : bv_unsigned (getr regs1 2) = sp0 - 224 - 0) by (rewrite Rsp; rewrite unsigned_lit_small by lia; lia).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more)) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67. cbn [Nat.sub nth af_extra map app firstn repeat] in E67.
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
assert (Ha4 : 0 <= a4v < 2 ^ 64) by (subst a4v; pose proof (land_small_r fattr 4 ltac:(clear - Rfattr; lia) ltac:(clear - PBASE PBLO; lia)) as Xl; cbn in Xl; clear - Xl; lia).
pose proof (af_lcE_ok E _ sp0 a4v HL E67 Ha4) as HLX.
exact (af_seed B TL LAWS pc sregs 0 true af_lcE (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR HLX
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF)).
Qed.
End e.
End b.
End a.
