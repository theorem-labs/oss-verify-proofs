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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_flushFrame : Z := AF_asan3_flushFrame.
Definition A_cgif_close : Z := AF_asan3_cgif_close.
Definition WFN_OFF : Z := AF_asan3_cgif_writecb_or_freeCGIF.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Lemma st_ok_pi_region_nth : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.
Lemma st_ok_pi_add_cond : forall E ss ms c a b,
st_ok_pi SEGS VAL E ss ms -> branch_taken c (sv_denot E a) (sv_denot E b) = true -> st_ok_pi SEGS VAL E (add_cond ss (mkAC c a b)) ms.
Proof. intros E ss ms c a b HS Hb. exact (st_ok_add_cond SEGS E (abs_ss VAL ss) ms c a b HS Hb). Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Variable hw : Z.
Definition tcgif_at2 (m : word -> option byte) (g : Z) (s1 : cgif_st) : Prop :=
obj_at SEGS m g LAY_CGIF (tcgif_vals hw s1) /\
(forall f, In (Some f) (cg_frames s1) -> obj_at SEGS m (fr_ptr f) LAY_Frame (frame_vals f)).
Lemma obj_at_kept : forall (m m' : word -> option byte) p lay vals sz,
obj_at SEGS m p lay vals -> lay_inside lay sz = true ->
(forall i, 0 <= i < sz -> mbyte SEGS m' (p + i) = mbyte SEGS m (p + i)) -> obj_at SEGS m' p lay vals.
Proof. intros m m' p lay vals sz H Hl Hk. exact (obj_at_transport_range SEGS m m' p lay vals sz H Hl Hk). Qed.
Lemma lay_inside_CGIF : lay_inside LAY_CGIF 96 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lay_inside_Frame : lay_inside LAY_Frame 40 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lay_inside_Raw : lay_inside LAY_Raw 48 = true. Proof. vm_compute. reflexivity. Qed.
Definition blk_kept (H H' : word -> bool) (m m' : word -> option byte) (b n : Z) : Prop :=
forall i, 0 <= i < n -> aview SEGS H' m' (b + i) = aview SEGS H m (b + i).
Lemma obj_at_blk_kept : forall H H' m m' p lay vals sz,
obj_at SEGS (mrestrict H m) p lay vals -> lay_inside lay sz = true -> blk_kept H H' m m' p sz ->
obj_at SEGS (mrestrict H' m') p lay vals.
Proof.
intros H H' m m' p lay vals sz Ho Hl Hk. apply (obj_at_kept _ _ p lay vals sz Ho Hl).
intros i Hi. apply (mbyte_of_aview SEGS). apply Hk. exact Hi.
Qed.
Lemma tcgif_at2_kept : forall H H' m m' g s1,
tcgif_at2 (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 ->
(forall f, In (Some f) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_at2 (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 [Hg Hf] Kg Kf. split.
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- intros f Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame (Kf f Hin)).
Qed.
Lemma tcgif_at_kept : forall H H' m m' g s1,
tcgif_at SEGS WFN_ADDR hw (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 -> blk_kept H H' m m' (cg_raw s1) 48 ->
(forall f, In (Some f) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_at SEGS WFN_ADDR hw (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 (Hg & Hr & Hf) Kg Kr Kf. split; [|split].
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- exact (obj_at_blk_kept H H' m m' (cg_raw s1) LAY_Raw _ 48 Hr lay_inside_Raw Kr).
- intros f Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame (Kf f Hin)).
Qed.
Lemma tcgif_at_2 : forall m g s1, tcgif_at SEGS WFN_ADDR hw m g s1 -> tcgif_at2 m g s1.
Proof. intros m g s1 (Hg & _ & Hf). exact (conj Hg Hf). Qed.
Lemma blk_kept_call : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 b n,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B ly2 S2) -> (forall i, 0 <= i < n -> ~ inFP FP1 (b + i)) ->
blk_kept (w_H W) (w_H W2) memc mem2 b n.
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 b n HJ1 Hin Hin2 HnF i Hi.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
destruct (Z_lt_ge_dec n 0) as [Hn|Hn]; [lia|]. pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
apply (G2 b n i Hin Hin2); [lia | apply HnF; exact Hi].
Qed.
Lemma cl_U_sext32 : forall E a r, U E a = r -> 0 <= r < 2 ^ 32 ->
U E (SExt true 32 a) = (if r <? 2 ^ 31 then r else r - 2 ^ 32 + 2 ^ 64).
Proof.
intros E a r Ha Hr. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec r (2 ^ 31)) as [Hl | Hh].
- rewrite (Z.mod_small (r + 2 ^ 31)) by lia. replace (r + 2 ^ 31 - 2 ^ 31) with r by lia. apply zcanon_id. unfold M64. lia.
- replace ((r + 2 ^ 31) mod 2 ^ 32) with (r + 2 ^ 31 - 2 ^ 32).
2:{ replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
unfold zcanon, M64. replace (r + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((r - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma achain_data : forall ly rd sp v, (v < alloc_ceiling \/ ly_top ly - 16 <= v) -> achain ly rd sp v [].
Proof. intros ly rd sp v [H|H]; left; (split; [|reflexivity]); [left; exact H | right; left; exact H]. Qed.
Lemma sep_hd_in : forall ly S W mem md x y l,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: l) -> In y l -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y l HAR HP Hy. apply in_split in Hy as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma obj_at_of_fields : forall m a lay vals,
length vals = length lay ->
(forall j f v, nth_error lay j = Some f -> nth_error vals j = Some v -> field_ok SEGS m a f v) ->
obj_at SEGS m a lay vals.
Proof.
intros m a lay. induction lay as [|f lay IH]; intros [|v vals] HL HF; cbn in HL |- *; try discriminate; [exact I|].
split; [exact (HF 0%nat f v eq_refl eq_refl)|]. apply IH; [lia|]. intros j f' v' Hf Hv. exact (HF (S j) f' v' Hf Hv).
Qed.
Lemma obj_cgif_rebuild : forall (m m' : word -> option byte) g vals cur,
obj_at SEGS m g LAY_CGIF vals ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS m' (g + i) = mbyte SEGS m (g + i)) ->
nth_error vals 15 = Some cur -> val_mem SEGS m' (g + 88) 4 cur ->
obj_at SEGS m' g LAY_CGIF vals.
Proof.
intros m m' g vals cur HO HK Hcur Vcur. pose proof (obj_at_length _ _ _ _ _ HO) as HL.
apply obj_at_of_fields; [exact HL|]. intros j f v Hf Hv.
pose proof (obj_at_nth SEGS _ _ _ _ j f v HO Hf Hv) as [V R]. split; [|exact R].
destruct (Nat.eq_dec j 15) as [-> | Hne].
- cbn in Hf. injection Hf as <-. rewrite Hcur in Hv. injection Hv as <-. exact Vcur.
- assert (HIN : In f LAY_CGIF) by (eapply nth_error_In; exact Hf).
assert (Hoff : 0 <= fst f /\ fst f + Z.of_N (snd f) <= 96 /\ (fst f + Z.of_N (snd f) <= 88 \/ 92 <= fst f)).
{ assert (Hj : (j < 17)%nat) by (apply (proj1 (nth_error_Some LAY_CGIF j)); rewrite Hf; discriminate).
do 17 (destruct j as [|j]; [cbn in Hf; injection Hf as <-; cbn; lia|]). lia. }
intros kk Hkk. rewrite <- (V kk Hkk). pose proof (N_nat_Z (snd f)).
replace (g + fst f + Z.of_nat kk) with (g + (fst f + Z.of_nat kk)) by lia. apply HK; lia.
Qed.
Lemma sep_app : forall ly S W mem md x y l1 l2,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In y l2 -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y l1 l2 HAR HP Hx Hy. apply in_split in Hx as (a1 & a2 & ->). apply in_split in Hy as (b1 & b2 & ->).
assert (P1 : Permutation (a1 ++ x :: a2) (x :: a1 ++ a2)) by (apply Permutation_sym, Permutation_middle).
assert (P2 : Permutation (b1 ++ y :: b2) (y :: b1 ++ b2)) by (apply Permutation_sym, Permutation_middle).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y ((a1 ++ a2) ++ (b1 ++ b2)) HAR).
eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app; [exact P1 | exact P2]|].
cbn [app]. apply perm_skip. apply Permutation_sym. apply (Permutation_middle (a1 ++ a2) (b1 ++ b2) y).
Qed.
Lemma frames3 : forall sx N, cgif_wf sx N -> cg_frames sx = [nth 0 (cg_frames sx) None; nth 1 (cg_frames sx) None; nth 2 (cg_frames sx) None].
Proof. intros sx N HW. pose proof (proj1 HW) as HL. destruct (cg_frames sx) as [|a [|b [|c [|]]]]; cbn in HL; try discriminate. reflexivity. Qed.
End h.
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
Lemma cl_alu64_addw : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.
End e.
End d.
