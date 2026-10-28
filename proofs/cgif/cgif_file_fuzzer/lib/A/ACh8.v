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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh9 AChc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Definition cl_set_cur (s1 : cgif_st) (c : Z) : cgif_st :=
mkCgif (cg_frames s1) (cg_pal s1) (cg_attr s1) (cg_gen s1) (cg_W s1) (cg_H s1) (cg_ngp s1) (cg_loops s1) (cg_raw s1) c (cg_ihead s1)
(rw_gct s1) (rw_attr s1) (rw_loops s1) (rw_cur s1).
Lemma tcgif_vals_set_cur_nth : forall {hw : Z} s1 c j, j <> 15%nat -> nth_error (tcgif_vals hw (cl_set_cur s1 c)) j = nth_error (tcgif_vals hw s1) j.
Proof.
intros hw s1 c j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; lia] |]). reflexivity.
Qed.
Lemma obj_cgif_setcur : forall {hw : Z} (m m' : word -> option byte) g s1 c,
obj_at SEGS m g LAY_CGIF (tcgif_vals hw s1) ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS m' (g + i) = mbyte SEGS m (g + i)) ->
val_mem SEGS m' (g + 88) 4 c -> 0 <= c < 2 ^ 32 ->
obj_at SEGS m' g LAY_CGIF (tcgif_vals hw (cl_set_cur s1 c)).
Proof.
intros hw m m' g s1 c HO HK Vc Rc.
apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct (Nat.eq_dec j 15) as [-> | Hne].
- cbn in Hf. injection Hf as <-. cbn in Hv. injection Hv as <-. split; [exact Vc | cbn; lia].
- rewrite (tcgif_vals_set_cur_nth s1 c j Hne) in Hv.
pose proof (obj_at_nth SEGS _ _ _ _ j f v HO Hf Hv) as [V R]. split; [|exact R].
assert (HIN : In f LAY_CGIF) by (eapply nth_error_In; exact Hf).
assert (Hoff : 0 <= fst f /\ fst f + Z.of_N (snd f) <= 96 /\ (fst f + Z.of_N (snd f) <= 88 \/ 92 <= fst f)).
{ assert (Hj : (j < 17)%nat) by (apply (proj1 (nth_error_Some LAY_CGIF j)); rewrite Hf; discriminate).
do 17 (destruct j as [|j]; [cbn in Hf; injection Hf as <-; cbn; lia|]). lia. }
intros kk Hkk. rewrite <- (V kk Hkk). pose proof (N_nat_Z (snd f)).
replace (g + fst f + Z.of_nat kk) with (g + (fst f + Z.of_nat kk)) by lia. apply HK; lia.
Qed.
Lemma denot_shx' : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m c v sb Hn Hm Hv Hc0 Hc Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))))). f_equal.
change (U E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (YP0m.zcanon_small (v + c)) by lia. rewrite (YP0m.zcanon_small ((v + c) / 8)) by lia. rewrite (YP0m.zcanon_small sb) by lia. rewrite YP0m.zcanon_small by lia. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes SEGS B.
Variable hw : Z.
Variable CTX : list (list Z).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Lemma frames_blocks_map : forall N (fs fs' : list (option frame_st)),
map (option_map (frame_blocks N)) fs = map (option_map (frame_blocks N)) fs' -> frames_blocks N fs = frames_blocks N fs'.
Proof.
intros N fs. induction fs as [|o fs IH]; intros [|o' fs'] H; cbn [map] in H; try discriminate; [reflexivity|].
injection H as Ho Hfs.
change (frames_blocks N (o :: fs)) with (match o with Some f => frame_blocks N f | None => [] end ++ frames_blocks N fs).
change (frames_blocks N (o' :: fs')) with (match o' with Some f => frame_blocks N f | None => [] end ++ frames_blocks N fs').
rewrite (IH fs' Hfs). f_equal.
pose proof (f_equal (fun x : option (list (Z * Z)) => match x with Some l => l | None => [] end) Ho) as Ho'. cbn beta iota in Ho'.
destruct o as [f|], o' as [f'|]; cbn [option_map] in Ho'; exact Ho'.
Qed.
Lemma cgif_blocks_obj_ok : forall g s s1 N, cl_obj_ok g s s1 N -> cgif_blocks g s1 N = cgif_blocks g s N.
Proof.
intros g s s1 N (_ & Hraw & Hattr & Hpal & Hngp & Hfrm). unfold cgif_blocks, pal_blocks.
rewrite Hraw, Hattr, Hpal, Hngp, (frames_blocks_map N _ _ Hfrm). reflexivity.
Qed.
Lemma cl_obj_ok_setcur : forall g s s1 N c, cl_obj_ok g s s1 N -> cl_obj_ok g s (cl_set_cur s1 c) N.
Proof. intros g s s1 N c H. exact H. Qed.
Lemma cl_obj_ok_flush : forall g s s1 N i gen' rwcur',
cl_obj_ok g s s1 N -> cgif_wf (flush_upd s1 i gen' rwcur') N -> cl_obj_ok g s (flush_upd s1 i gen' rwcur') N.
Proof.
intros g s s1 N i gen' rwcur' (HWF1 & Hraw & Hattr & Hpal & Hngp & Hfrm) HWF'. split; [exact HWF'|].
cbn [cg_raw cg_attr cg_pal cg_ngp cg_frames flush_upd]. split; [exact Hraw|]. split; [exact Hattr|]. split; [exact Hpal|]. split; [exact Hngp|].
rewrite <- Hfrm. generalize (cg_frames s1) as fs. clear. induction i as [|i IH]; intros [|o fs]; cbn; [reflexivity| |reflexivity|].
- f_equal. destruct o; reflexivity.
- f_equal. apply IH.
Qed.
Lemma tcgif_at_stretchA : forall ly1 S1 (W1 : world SEGS) mem1 md1 (m' : word -> option byte) g s s1 N rest cur',
AR SEGS B ly1 S1 W1 mem1 md1 -> Permutation (ablocks B ly1 S1) (cgif_blocks g s N ++ rest) -> cl_obj_ok g s s1 N ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) mem1) g s1 ->
(forall a, 0 <= a < alloc_ceiling -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) mem1 a) ->
val_mem SEGS (mrestrict (w_H W1) m') (g + 88) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) m') g (cl_set_cur s1 cur').
Proof.
intros ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK (Hg & Hr & Hf) UN Vc Rc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cgif_blocks_obj_ok g s s1 N HOK) as EB. rewrite <- EB in HPerm.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly1 S1)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (_ & Hg4096 & Hgceil & _). change (req_size CGIF_SIZE) with 96 in Hgceil.
assert (HPerm' : Permutation (ablocks B ly1 S1) ((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1) ++ rest))
by (unfold cgif_blocks in HPerm; cbn [app] in HPerm; rewrite <- app_assoc in HPerm; exact HPerm).
assert (SEP : forall b n, In (b, n) ((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1) ++ rest) ->
4096 <= b /\ b + req_size n <= alloc_ceiling /\ (g + 96 <= b \/ b + req_size n <= g)).
{ intros b n Hbn.
assert (Hb : In (b, n) (ablocks B ly1 S1)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm'|]; right; exact Hbn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_hd_in B LAWS ly1 S1 W1 mem1 md1 (g, CGIF_SIZE) (b, n) _ HAR HPerm' Hbn) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. clear - D Hb4096 Hbceil. lia. }
split; [|split].
- apply (obj_cgif_setcur _ _ g s1 cur' Hg); [| exact Vc | exact Rc].
intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hg4096 Hgceil C1 C3; lia.
- cbn [cg_raw cl_set_cur]. change (traw_vals WFN_ADDR g (cl_set_cur s1 cur')) with (traw_vals WFN_ADDR g s1).
destruct (SEP (cg_raw s1) RAW_SIZE ltac:(left; reflexivity)) as (Hr4096 & Hrceil & Dgr). change (req_size RAW_SIZE) with 48 in Hrceil, Dgr.
apply (obj_at_kept _ _ (cg_raw s1) LAY_Raw _ 48 Hr lay_inside_Raw).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgr Hr4096 Hrceil Hg4096 Hgceil C1 C3; lia.
- cbn [cg_frames cl_set_cur]. intros f Hin.
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (cg_frames s1))).
{ apply in_split in Hin as (l1 & l2 & El). rewrite El. unfold frames_blocks. rewrite flat_map_app. cbn [flat_map app].
apply in_or_app. right. left. reflexivity. }
destruct (SEP (fr_ptr f) FRAME_SIZE ltac:(right; apply in_or_app; right; apply in_or_app; left; exact Hfb)) as (Hf4096 & Hfceil & Dgf).
change (req_size FRAME_SIZE) with 40 in Hfceil, Dgf.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf Hf4096 Hfceil Hg4096 Hgceil C1 C3; lia.
Qed.
Lemma tcgif_at_stretch : forall ly1 S1 (W1 : world SEGS) mem1 md1 (m' : word -> option byte) g s s1 N rest cur',
AR SEGS B ly1 S1 W1 mem1 md1 -> Permutation (ablocks B ly1 S1) (cgif_blocks g s N ++ rest) -> cl_obj_ok g s s1 N ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) mem1) g s1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) mem1 a) ->
val_mem SEGS (mrestrict (w_H W1) m') (g + 88) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) m') g (cl_set_cur s1 cur').
Proof.
intros ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK HT UN Vc Rc. pose proof asan_consts as (C1 & _).
apply (tcgif_at_stretchA ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK HT); [| exact Vc | exact Rc].
intros a Ha Hna. apply UN; [clear - Ha C1; lia | exact Hna].
Qed.
End h.
End e.
End d.
