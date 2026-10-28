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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a YC80 YC1f YC81 YC4b YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh9 AChc ACh8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c YC5d YC7z YC7x YC21 YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh7 ACh6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma rc_int_range : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= rc_int v < 2 ^ 31.
Proof. intros v Hv. unfold rc_int. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma rc_int_mod32 : forall c, - 2 ^ 31 <= c < 2 ^ 31 -> rc_int (c mod 2 ^ 32) = c.
Proof.
intros c Hc. unfold rc_int. destruct (Z_lt_le_dec c 0).
- replace (c mod 2 ^ 32) with (c + 2 ^ 32) by (symmetry; rewrite <- (Z.mod_add c 1 (2 ^ 32)) by lia; apply Z.mod_small; lia).
destruct (Z.ltb_spec (c + 2 ^ 32) (2 ^ 31)); lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec c (2 ^ 31)); lia.
Qed.
Lemma reg_of_code : forall r code, 0 <= r < 2 ^ 64 -> - 2 ^ 63 <= code < 2 ^ 63 -> Z_to_bv 64 r = Z_to_bv 64 code -> r = code mod 2 ^ 64.
Proof.
intros r code Hr Hc E. rewrite <- (Z_to_bv64_mod code) in E. apply (f_equal bv_unsigned) in E.
rewrite !unsigned_lit_small in E by (try exact Hr; apply Z.mod_pos_bound; lia). exact E.
Qed.
Lemma code_zero_iff : forall r code, 0 <= r < 2 ^ 64 -> - 2 ^ 63 <= code < 2 ^ 63 -> Z_to_bv 64 r = Z_to_bv 64 code -> (r = 0 <-> code = 0).
Proof.
intros r code Hr Hc E. rewrite (reg_of_code r code Hr Hc E). split; intros H.
- pose proof (Z.div_mod code (2 ^ 64) ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
assert (code / 2 ^ 64 = 0) by lia. rewrite D. lia.
- subst code. reflexivity.
Qed.
Lemma cl_alu64_addwX : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma cl_srl3X : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 64) ltac:(lia) ltac:(lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. symmetry. apply unsigned_lit_small. lia.
Qed.
Lemma cl_shx_incX : forall x sb k, 0 <= x < 2 ^ 63 -> alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 sb)) (Z_to_bv 64 k) = Z_to_bv 64 (sb + x / 8 + k).
Proof. intros x sb k Hx. rewrite cl_srl3X by lia. rewrite !cl_alu64_addwX. f_equal. lia. Qed.
Lemma cl_shx_eqX : forall x y sb, 0 <= x < 2 ^ 63 -> x = y -> alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 sb) = w64 (sb + y / 8).
Proof. intros x y sb Hx <-. rewrite cl_srl3X by lia. rewrite cl_alu64_addwX. unfold w64. f_equal. lia. Qed.
Lemma cl_shx_eqX' : forall x y sb, 0 <= x < 2 ^ 63 -> x = y -> alu64 ALU_ADD (Z_to_bv 64 sb) (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) = w64 (sb + y / 8).
Proof. intros x y sb Hx <-. rewrite cl_srl3X by lia. rewrite cl_alu64_addwX. reflexivity. Qed.
Lemma cl_shx_succX : forall x y sb, 0 <= x < 2 ^ 63 -> x + 8 = y -> alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 sb)) (Z_to_bv 64 1) = w64 (sb + y / 8).
Proof. intros x y sb Hx <-. rewrite cl_shx_incX by lia. unfold w64. f_equal. replace (x + 8) with (x + 1 * 8) by lia. rewrite Z.div_add by lia. lia. Qed.
Lemma flush_code_range : forall G rcur cur bef code bytes,
YO07.flush_frame G rcur cur bef = (code, bytes) -> - 2 ^ 31 <= rcur < 2 ^ 31 -> - 2 ^ 31 <= code < 2 ^ 31.
Proof.
intros G rcur cur bef code bytes H Hr. destruct (flush_frame_code G rcur cur bef code bytes H) as [-> | [-> | [-> | ->]]];
[exact Hr | | |]; unfold YO07.R_ERROR, YO07.R_EINDEX, YO07.R_OK; lia.
Qed.
Lemma cl_slot1_none : forall G (gs : YO07.gif_st), YO07.s_q1 gs = None ->
cl_bytes G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) = [] /\
cl_code G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) = YO07.C_OK /\ cl_rcur1 G gs = YO07.s_rcur gs.
Proof. intros G gs H. unfold cl_bytes, cl_code, cl_rcur1. rewrite H. repeat split. Qed.
Lemma cl_slot1_some : forall G (gs : YO07.gif_st) cur1 code bytes, YO07.s_q1 gs = Some cur1 ->
YO07.flush_frame G (YO07.s_rcur gs) cur1 (YO07.s_q0 gs) = (code, bytes) ->
cl_bytes G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) = bytes /\
cl_code G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) = code /\ cl_rcur1 G gs = code.
Proof. intros G gs cur1 code bytes H F. unfold cl_bytes, cl_code, cl_rcur1. rewrite H, F. repeat split. Qed.
Lemma close_gif_fail1 : forall G (gs : YO07.gif_st), YO07.s_cur gs = YO07.C_OK ->
cl_code G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) <> YO07.C_OK ->
concat (YO07.close_gif G gs) = concat (YO07.s_out gs) ++ cl_bytes G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs).
Proof. intros G gs Hc Hne. rewrite (close_gif_ok G gs Hc). rewrite (proj2 (Z.eqb_neq _ _) Hne). rewrite app_nil_r. reflexivity. Qed.
Lemma close_gif_none2 : forall G (gs : YO07.gif_st), YO07.s_cur gs = YO07.C_OK ->
cl_code G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) = YO07.C_OK -> YO07.s_q2 gs = None ->
concat (YO07.close_gif G gs) = concat (YO07.s_out gs) ++ cl_bytes G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs).
Proof. intros G gs Hc H1 H2. rewrite (close_gif_ok G gs Hc). rewrite H1, Z.eqb_refl, H2. cbn [cl_bytes]. rewrite app_nil_r. reflexivity. Qed.
Lemma close_gif_some2 : forall G (gs : YO07.gif_st) cur2 code bytes, YO07.s_cur gs = YO07.C_OK ->
cl_code G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) = YO07.C_OK -> YO07.s_q2 gs = Some cur2 ->
YO07.flush_frame G (cl_rcur1 G gs) cur2 (YO07.s_q1 gs) = (code, bytes) ->
concat (YO07.close_gif G gs) = (concat (YO07.s_out gs) ++ cl_bytes G (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs)) ++ bytes.
Proof.
intros G gs cur2 code bytes Hc H1 H2 F. rewrite (close_gif_ok G gs Hc). rewrite H1, Z.eqb_refl, H2. unfold cl_bytes at 2. rewrite F. cbn [snd].
rewrite app_assoc. reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
Lemma frame_relbA_set_gen : forall (m : word -> option byte) N f fr gen,
frame_relbA SEGS true m N f fr -> frame_relbA SEGS false m N (set_fr_gen f gen) fr.
Proof. intros m N f fr gen (A1 & A2 & H). split; [exact A1|]. split; [exact I | exact H]. Qed.
Definition cl_wblocks (g : Z) (s : cgif_st) : list (Z * Z) :=
(g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: flat_map (fun o => match o with Some f => [(fr_ptr f, FRAME_SIZE)] | None => [] end) (cg_frames s).
Lemma frames_blocks_wvC : forall N l,
Permutation (frames_blocks N l)
(flat_map (fun o => match o with Some f => [(fr_ptr f, FRAME_SIZE)] | None => [] end) l ++ flat_map (af_xfvb N) l).
Proof.
intros N l. induction l as [|o l IH]; [reflexivity|]. unfold frames_blocks in *. cbn [flat_map].
destruct o as [f|]; [|exact IH]. unfold frame_blocks, af_xfvb at 1.
set (V := (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)])).
change (Permutation (((fr_ptr f, FRAME_SIZE) :: V) ++ flat_map (fun o : option frame_st => match o with Some f0 => (fr_ptr f0, FRAME_SIZE) :: (fr_img f0, N) :: (if Z.land (fr_attr f0) 1 =? 0 then [] else [(fr_lpal f0, 3 * fr_nlp f0)]) | None => [] end) l)
(([(fr_ptr f, FRAME_SIZE)] ++ flat_map (fun o : option frame_st => match o with Some f0 => [(fr_ptr f0, FRAME_SIZE)] | None => [] end) l) ++ (V ++ flat_map (af_xfvb N) l))).
cbn [app]. apply perm_skip.
eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma cgif_blocks_wvC : forall g s N, Permutation (cgif_blocks g s N) (cl_wblocks g s ++ af_xvblocks s N).
Proof.
intros g s N. unfold cgif_blocks, cl_wblocks. rewrite af_xvblocks_eq. cbn [app]. do 2 apply perm_skip.
eapply Permutation_trans; [apply Permutation_app_head; apply frames_blocks_wvC|].
rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma cl_wblocks_frame : forall g s f, In (Some f) (cg_frames s) -> In (fr_ptr f, FRAME_SIZE) (cl_wblocks g s).
Proof. intros g s f Hf. unfold cl_wblocks. right. right. apply in_flat_map. exists (Some f). split; [exact Hf | left; reflexivity]. Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma asep_appC : forall ly S W mem md (l1 l2 : list (Z * Z)) x y,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In y l2 -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md l1 l2 x y HAR HP Hx Hy. destruct (in_split _ _ Hx) as (a1 & a2 & ->). destruct (in_split _ _ Hy) as (b1 & b2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y ((a1 ++ a2) ++ b1 ++ b2) HAR).
eapply Permutation_trans; [exact HP|].
eapply Permutation_trans; [apply (Permutation_app (Permutation_sym (Permutation_middle a1 a2 x)) (Permutation_sym (Permutation_middle b1 b2 y)))|].
cbn [app]. apply perm_skip. exact (Permutation_sym (Permutation_middle (a1 ++ a2) (b1 ++ b2) y)).
Qed.
Lemma cl_values_apart : forall ly S W mem md g s1 N restc a n b m,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ restc) ->
In (a, n) (af_xvblocks s1 N) -> In (b, m) (cl_wblocks g s1 ++ restc) ->
(b + req_size m <= a \/ a + req_size n <= b) /\ 4096 <= a /\ a + req_size n <= alloc_ceiling /\ In (a, n) (ablocks B ly S).
Proof.
intros ly S W mem md g s1 N restc a n b m HAR HP Ha Hb.
assert (HP' : Permutation (ablocks B ly S) ((cl_wblocks g s1 ++ restc) ++ af_xvblocks s1 N)).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_tail; apply cgif_blocks_wvC|].
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
assert (Hlive : In (a, n) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP'|]; apply in_app_iff; right; exact Ha).
destruct (al_blocks _ _ LAWS _ _ _ _ _ a n HAR Hlive) as (_ & Ha4096 & Haceil & _).
pose proof (asep_appC ly S W mem md _ _ (b, m) (a, n) HAR HP' Hb Ha) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
split; [exact D|]. split; [exact Ha4096|]. split; [exact Haceil | exact Hlive].
Qed.
Definition cl_vkept (m m' : word -> option byte) (s1 : cgif_st) (N : Z) : Prop :=
forall a n k, In (a, n) (af_xvblocks s1 N) -> 0 <= k < n -> mbyte SEGS m' (a + k) = mbyte SEGS m (a + k).
Lemma cl_vkept_trans : forall (m1 m2 m3 : word -> option byte) s1 N, cl_vkept m1 m2 s1 N -> cl_vkept m2 m3 s1 N -> cl_vkept m1 m3 s1 N.
Proof. intros m1 m2 m3 s1 N H12 H23 a n k Hin Hk. rewrite (H23 a n k Hin Hk). exact (H12 a n k Hin Hk). Qed.
Lemma cl_vkept_ext : forall (m m' : word -> option byte) s1 s2 N,
cg_frames s2 = cg_frames s1 -> cg_attr s2 = cg_attr s1 -> cg_pal s2 = cg_pal s1 -> cg_ngp s2 = cg_ngp s1 ->
cl_vkept m m' s1 N -> cl_vkept m m' s2 N.
Proof.
intros m m' s1 s2 N Hf Ha Hp Hn H a n k Hin Hk. apply (H a n k); [| exact Hk].
unfold af_xvblocks, pal_blocks in *. rewrite Hf, Ha, Hp, Hn in Hin. exact Hin.
Qed.
Lemma cl_vkept_stretch : forall ly S W mem md (m' : word -> option byte) g s1 N restc,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ restc) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) ->
cl_vkept (mrestrict (w_H W) mem) (mrestrict (w_H W) m') s1 N.
Proof.
intros ly S W mem md m' g s1 N restc HAR HP UN a n k Hin Hk. pose proof asan_consts as (C1 & _).
destruct (cl_values_apart ly S W mem md g s1 N restc a n g CGIF_SIZE HAR HP Hin ltac:(left; reflexivity)) as (D & H4096 & Hceil & _).
change (req_size CGIF_SIZE) with 96 in D.
destruct (Z_lt_ge_dec n 0) as [Hn|Hn]; [lia|]. pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
apply (mbyte_of_aview SEGS). apply UN; lia.
Qed.
Lemma cl_vkept_stretchA : forall ly S W mem md (m' : word -> option byte) g s1 N restc lo hi,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ restc) -> alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi \/ g + 88 <= a < g + 92) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) ->
cl_vkept (mrestrict (w_H W) mem) (mrestrict (w_H W) m') s1 N.
Proof.
intros ly S W mem md m' g s1 N restc lo hi HAR HP Hlo UN a n k Hin Hk. pose proof asan_consts as (C1 & _).
destruct (cl_values_apart ly S W mem md g s1 N restc a n g CGIF_SIZE HAR HP Hin ltac:(left; reflexivity)) as (D & H4096 & Hceil & _).
change (req_size CGIF_SIZE) with 96 in D.
destruct (Z_lt_ge_dec n 0) as [Hn|Hn]; [lia|]. pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
apply (mbyte_of_aview SEGS). apply UN; lia.
Qed.
Lemma cl_vkept_flush : forall STK1 sp1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 g s1 N pf rest f,
AR SEGS B lyc Sc W memc mdc ->
ajournal SEGS B STK1 sp1 ((fr_ptr f + 20, fr_ptr f + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ (pf, FILE_BLOCK) :: rest) ->
Permutation (ablocks B ly2 S2) (cgif_blocks g s1 N ++ (pf, FILE_BLOCK) :: rest) ->
In (Some f) (cg_frames s1) ->
cl_vkept (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) s1 N.
Proof.
intros STK1 sp1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 g s1 N pf rest f HARc HJ HP HP2 Hf a n k Hin Hk.
pose proof (proj1 HJ) as HAR2.
destruct (cl_values_apart lyc Sc W memc mdc g s1 N _ a n (fr_ptr f) FRAME_SIZE HARc HP Hin
ltac:(apply in_app_iff; left; apply cl_wblocks_frame; exact Hf)) as (Df & H4096 & Hceil & Hlive).
destruct (cl_values_apart lyc Sc W memc mdc g s1 N _ a n (cg_raw s1) RAW_SIZE HARc HP Hin
ltac:(apply in_app_iff; left; right; left; reflexivity)) as (Dr & _).
destruct (cl_values_apart lyc Sc W memc mdc g s1 N _ a n pf FILE_BLOCK HARc HP Hin
ltac:(apply in_app_iff; right; left; reflexivity)) as (Dp & _).
destruct (cl_values_apart ly2 S2 W2 mem2 md2 g s1 N _ a n pf FILE_BLOCK HAR2 HP2 Hin
ltac:(apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & Hlive2).
change (req_size FRAME_SIZE) with 40 in Df. change (req_size RAW_SIZE) with 48 in Dr. change (req_size FILE_BLOCK) with 1264 in Dp.
destruct (Z_lt_ge_dec n 0) as [Hn|Hn]; [lia|]. pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
apply (mbyte_of_aview SEGS).
apply (blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ a n HJ Hlive Hlive2); [| exact Hk].
intros i Hi (r & Hrin & Hrr). cbn [In] in Hrin. destruct Hrin as [<- | [<- | Hrin]]; cbn [fst snd] in Hrr; [lia | lia |].
assert (Hs : inFP (asink_fp pf) (a + i)) by (exists r; split; [exact Hrin | exact Hrr]).
apply in_asink_fp in Hs. unfold FILE_BLOCK in Hs. lia.
Qed.
Lemma gpal_vkept : forall (m m' : word -> option byte) s1 N GPAL,
cl_vkept m m' s1 N ->
(Z.land (cg_attr s1) 4 = 0 -> garr8 SEGS m (cg_pal s1) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s1) ->
(Z.land (cg_attr s1) 4 = 0 -> garr8 SEGS m' (cg_pal s1) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s1).
Proof.
intros m m' s1 N GPAL K R4 Hz. destruct (R4 Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s1 + (a - cg_pal s1)) by lia. apply (K (cg_pal s1) (3 * cg_ngp s1)); [| lia].
unfold af_xvblocks. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
Qed.
Lemma oframe_relbA_vkept : forall wg (m m' : word -> option byte) s1 N j q,
cl_vkept m m' s1 N -> oframe_relbA SEGS wg m N (nth j (cg_frames s1) None) q -> oframe_relbA SEGS wg m' N (nth j (cg_frames s1) None) q.
Proof.
intros wg m m' s1 N j q K H. destruct (nth j (cg_frames s1) None) as [f|] eqn:Hn; destruct q as [fr|]; cbn [oframe_relbA] in H |- *; try exact H.
assert (Hin : In (Some f) (cg_frames s1)).
{ rewrite <- Hn. apply nth_In. destruct (Nat.lt_ge_cases j (length (cg_frames s1))) as [Hl|Hl]; [exact Hl|]. rewrite (nth_overflow _ _ Hl) in Hn. discriminate Hn. }
apply (frame_relb_kept SEGS wg m m' N f fr); [| | exact H].
- intros k Hk. apply (K (fr_img f) N k); [| exact Hk]. unfold af_xvblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
- intros Hz k Hk. apply (K (fr_lpal f) (3 * fr_nlp f) k); [| exact Hk]. unfold af_xvblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin|].
right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
Qed.
Lemma af_xlive_vkept : forall (m m' : word -> option byte) s1 N GPAL gs,
cl_vkept m m' s1 N -> af_xlive SEGS m s1 N GPAL gs -> af_xlive SEGS m' s1 N GPAL gs.
Proof.
intros m m' s1 N GPAL gs K (R1 & R2 & R3 & R4 & F0 & F1 & F2).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact (gpal_vkept m m' s1 N GPAL K R4)|].
split; [exact (oframe_relbA_vkept false m m' s1 N 0 _ K F0)|]. split; [exact (oframe_relbA_vkept true m m' s1 N 1 _ K F1) | exact (oframe_relbA_vkept true m m' s1 N 2 _ K F2)].
Qed.
Lemma flush_upd_nth_same : forall s i gen rw f, (i < length (cg_frames s))%nat -> nth i (cg_frames s) None = Some f ->
nth i (cg_frames (flush_upd s i gen rw)) None = Some (set_fr_gen f gen).
Proof. intros s i gen rw f Hi Hn. cbn [cg_frames flush_upd]. rewrite nth_list_set_same by exact Hi. rewrite Hn. reflexivity. Qed.
Lemma flush_upd_nth_other : forall s i j gen rw, i <> j -> nth j (cg_frames (flush_upd s i gen rw)) None = nth j (cg_frames s) None.
Proof. intros s i j gen rw Hij. cbn [cg_frames flush_upd]. apply nth_list_set_other. exact Hij. Qed.
Lemma af_xvblocks_flush_upd : forall s i gen rw N, length (cg_frames s) = 3%nat -> af_xvblocks (flush_upd s i gen rw) N = af_xvblocks s N.
Proof.
intros s i gen rw N Hlen. unfold af_xvblocks, pal_blocks. cbn [cg_frames cg_attr cg_pal cg_ngp flush_upd]. f_equal.
destruct (cg_frames s) as [|o0 [|o1 [|o2 [|? ?]]]]; try discriminate Hlen.
destruct i as [|[|[|i]]]; cbn [list_set nth option_map flat_map]; [destruct o0 | destruct o1 | destruct o2 |]; reflexivity.
Qed.
Lemma cl_vkept_flush_upd : forall (m m' : word -> option byte) s i gen rw N, length (cg_frames s) = 3%nat ->
cl_vkept m m' s N -> cl_vkept m m' (flush_upd s i gen rw) N.
Proof. intros m m' s i gen rw N Hlen H a n k Hin Hk. rewrite (af_xvblocks_flush_upd s i gen rw N Hlen) in Hin. exact (H a n k Hin Hk). Qed.
Lemma cl_x2_of_null1 : forall (m m' : word -> option byte) s s1 N GPAL gs c,
nth 1 (cg_frames s1) None = None -> gcfg_of s1 GPAL = gcfg_of s GPAL ->
af_xlive SEGS m s1 N GPAL gs -> cl_vkept m m' s1 N ->
YO07.s_q1 gs = None /\ cl_x2 m' s (cl_set_cur s1 c) N GPAL gs.
Proof.
intros m m' s s1 N GPAL gs c Hn HG (R1 & R2 & R3 & R4 & F0 & F1 & F2) K.
assert (Hq1 : YO07.s_q1 gs = None) by (rewrite Hn in F1; destruct (YO07.s_q1 gs); [destruct F1 | reflexivity]).
split; [exact Hq1|]. unfold cl_x2. cbn [rw_cur rw_attr cg_attr cg_pal cg_ngp cg_frames cl_set_cur].
split; [rewrite (proj2 (proj2 (cl_slot1_none (gcfg_of s GPAL) gs Hq1))); exact R1|]. split; [exact R2|].
split; [exact (gpal_vkept m m' s1 N GPAL K R4)|].
split; [rewrite Hn, Hq1; exact I | exact (oframe_relbA_vkept true m m' s1 N 2 _ K F2)].
Qed.
Lemma cl_x2_of_flush1 : forall (m m' : word -> option byte) s s1 N GPAL gs f cur1 gen' code bytes c1 c3,
length (cg_frames s1) = 3%nat -> nth 1 (cg_frames s1) None = Some f -> gcfg_of s1 GPAL = gcfg_of s GPAL ->
af_xlive SEGS m s1 N GPAL gs -> cl_vkept m m' s1 N -> 0 <= rw_cur s1 < 2 ^ 32 ->
YO07.s_q1 gs = Some cur1 ->
YO07.flush_frame (gcfg_of s GPAL) (YO07.s_rcur gs) cur1 (YO07.s_q0 gs) = (code, bytes) ->
cl_x2 m' s (cl_set_cur (flush_upd (cl_set_cur s1 c1) 1 gen' (code mod 2 ^ 32)) c3) N GPAL gs.
Proof.
intros m m' s s1 N GPAL gs f cur1 gen' code bytes c1 c3 Hlen Hn HG (R1 & R2 & R3 & R4 & F0 & F1 & F2) K Rrc Hq1 F.
unfold cl_x2. cbn [rw_cur rw_attr cg_attr cg_pal cg_ngp cl_set_cur flush_upd].
split.
{ rewrite (proj2 (proj2 (cl_slot1_some (gcfg_of s GPAL) gs cur1 code bytes Hq1 F))). apply rc_int_mod32.
apply (flush_code_range _ _ _ _ _ _ F). rewrite <- R1. exact (rc_int_range _ Rrc). }
split; [exact R2|]. split; [exact (gpal_vkept m m' s1 N GPAL K R4)|].
change (cg_frames (cl_set_cur (flush_upd (cl_set_cur s1 c1) 1 gen' (code mod 2 ^ 32)) c3)) with (cg_frames (flush_upd s1 1 gen' (code mod 2 ^ 32))).
split.
- rewrite (flush_upd_nth_same s1 1 gen' _ f ltac:(rewrite Hlen; lia) Hn), Hq1. cbn [oframe_relbA].
pose proof (oframe_relbA_vkept true m m' s1 N 1 _ K F1) as F1'. rewrite Hn, Hq1 in F1'. cbn [oframe_relbA] in F1'.
exact (frame_relbA_set_gen m' N f cur1 gen' F1').
- rewrite (flush_upd_nth_other s1 1 2 gen' _ ltac:(lia)). exact (oframe_relbA_vkept true m m' s1 N 2 _ K F2).
Qed.
End h.
End e.
End d.
