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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACja.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj1 ACj0 ACja ACj6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC7x.
Import ListNotations.
Open Scope Z_scope.
Lemma U_front1 : forall E b ga fa, ew E 12 = Z_to_bv 64 b -> ew E 38 = Z_to_bv 64 ga -> ew E 52 = Z_to_bv 64 fa ->
0 <= b < 2 ^ 64 -> 0 <= ga < 2 ^ 32 -> 0 <= fa < 2 ^ 32 ->
U E (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 12 0) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))) (SLit 1))
= if (b =? 0) || negb ((Z.land ga 8 =? 0) && (Z.land fa 2 =? 0)) then 1 else 0.
Proof.
intros E b ga fa E12 E38 E52 Rb Rga Rfa.
rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E 12 b E12 Rb), (U_atom E 52 fa E52 ltac:(lia)).
rewrite U_zext, (U_atom E 38 ga E38 ltac:(lia)). change (2 ^ Z.of_N 8) with 256.
pose proof (Z.land_nonneg (ga mod 256) 8) as L1. pose proof (Z_land_upper (ga mod 256) 8 ltac:(lia)) as L1'.
pose proof (Z.land_nonneg fa 2) as L2. pose proof (Z_land_upper fa 2 ltac:(lia)) as L2'.
assert (Hm : 0 <= ga mod 256 < 256) by (apply Z.mod_pos_bound; lia).
rewrite !(zcanon_id 8), !(zcanon_id 2), !(zcanon_id 1), !(zcanon_id 0) by (rewrite M64_val; lia).
rewrite (zcanon_id (Z.land (ga mod 256) 8)) by (rewrite M64_val; lia). rewrite (zcanon_id (Z.land fa 2)) by (rewrite M64_val; lia).
assert (E8 : Z.land (ga mod 256) 8 = Z.land ga 8).
{ change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 8) 8). change (Z.land 8 (Z.ones 8)) with 8. reflexivity. }
rewrite E8 in *.
set (t := Z.lor (Z.land ga 8) (Z.land fa 2)).
assert (Ht : t = 0 <-> Z.land ga 8 = 0 /\ Z.land fa 2 = 0) by (apply Z.lor_eq_0_iff).
assert (Ht0 : 0 <= t) by (subst t; apply Z.lor_nonneg; lia).
assert (Htz : zcanon t = t).
{ apply zcanon_id. rewrite M64_val. subst t.
pose proof (Z.add_lor_land (Z.land ga 8) (Z.land fa 2)) as AL. pose proof (Z.land_nonneg (Z.land ga 8) (Z.land fa 2)) as LN. lia. }
rewrite Htz.
destruct (Z.ltb_spec b 1); destruct (Z.ltb_spec 0 t); destruct (Z.eqb_spec b 0); destruct (Z.eqb_spec (Z.land ga 8) 0); destruct (Z.eqb_spec (Z.land fa 2) 0);
cbn [orb negb andb]; try reflexivity; try lia.
Qed.
Lemma U_hasalpha : forall E ga fa, ew E 38 = Z_to_bv 64 ga -> ew E 52 = Z_to_bv 64 fa -> 0 <= ga < 2 ^ 32 -> 0 <= fa < 2 ^ 32 ->
U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))
= if negb ((Z.land ga 8 =? 0) && (Z.land fa 2 =? 0)) then 1 else 0.
Proof.
intros E ga fa E38 E52 Rga Rfa.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E 52 fa E52 ltac:(lia)).
rewrite U_zext, (U_atom E 38 ga E38 ltac:(lia)). change (2 ^ Z.of_N 8) with 256.
pose proof (Z.land_nonneg (ga mod 256) 8) as L1. pose proof (Z_land_upper (ga mod 256) 8 ltac:(lia)) as L1'.
pose proof (Z.land_nonneg fa 2) as L2. pose proof (Z_land_upper fa 2 ltac:(lia)) as L2'.
assert (Hm : 0 <= ga mod 256 < 256) by (apply Z.mod_pos_bound; lia).
rewrite !(zcanon_id 8), !(zcanon_id 2), !(zcanon_id 0) by (rewrite M64_val; lia).
rewrite (zcanon_id (Z.land (ga mod 256) 8)) by (rewrite M64_val; lia). rewrite (zcanon_id (Z.land fa 2)) by (rewrite M64_val; lia).
assert (E8 : Z.land (ga mod 256) 8 = Z.land ga 8).
{ change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 8) 8). change (Z.land 8 (Z.ones 8)) with 8. reflexivity. }
rewrite E8 in *.
set (t := Z.lor (Z.land ga 8) (Z.land fa 2)).
assert (Ht : t = 0 <-> Z.land ga 8 = 0 /\ Z.land fa 2 = 0) by (apply Z.lor_eq_0_iff).
assert (Ht0 : 0 <= t) by (subst t; apply Z.lor_nonneg; lia).
assert (Htz : zcanon t = t).
{ apply zcanon_id. rewrite M64_val. subst t.
pose proof (Z.add_lor_land (Z.land ga 8) (Z.land fa 2)) as AL. pose proof (Z.land_nonneg (Z.land ga 8) (Z.land fa 2)) as LN. lia. }
rewrite Htz.
destruct (Z.ltb_spec 0 t); destruct (Z.eqb_spec (Z.land ga 8) 0); destruct (Z.eqb_spec (Z.land fa 2) 0);
cbn [orb negb andb]; try reflexivity; try lia.
Qed.
Lemma U_and_atom : forall E n v m, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= m < 2 ^ 63 -> U E (SAlu ALU_AND (SOff n 0) (SLit m)) = Z.land v m.
Proof. intros E n v m En Rv Rm. rewrite U_and_lit by lia. rewrite (U_atom E n v En Rv). reflexivity. Qed.
Lemma U_transtest : forall E gen fa, ew E 621 = Z_to_bv 64 gen -> ew E 52 = Z_to_bv 64 fa -> 0 <= gen < 2 ^ 32 -> 0 <= fa < 2 ^ 32 ->
U E (SAlu ALU_OR (SAlu ALU_AND (SOff 621 0) (SLit 1)) (SAlu ALU_AND (SOff 52 0) (SLit 4))) = Z.lor (Z.land gen 1) (Z.land fa 4).
Proof.
intros E gen fa E621 E52 Rg Rfa.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_and_atom E 621 gen 1 E621) by lia. rewrite (U_and_atom E 52 fa 4 E52) by lia.
pose proof (Z.land_nonneg gen 1) as L1. pose proof (Z_land_upper gen 1 ltac:(lia)) as L1'.
pose proof (Z.land_nonneg fa 4) as L2. pose proof (Z_land_upper fa 4 ltac:(lia)) as L2'.
apply zcanon_id. rewrite M64_val.
pose proof (Z.add_lor_land (Z.land gen 1) (Z.land fa 4)) as AL. pose proof (Z.land_nonneg (Z.land gen 1) (Z.land fa 4)) as LN.
pose proof (Z.lor_nonneg (Z.land gen 1) (Z.land fa 4)) as LO. lia.
Qed.
Lemma fptr_range : forall s (i : nat), (i = 1%nat \/ i = 2%nat) ->
0 <= frame_ptr (nth 0 (cg_frames s) None) < 2 ^ 64 -> 0 <= frame_ptr (nth 1 (cg_frames s) None) < 2 ^ 64 ->
0 <= frame_ptr (nth (i - 1) (cg_frames s) None) < 2 ^ 64.
Proof. intros s i [-> | ->] R0 R1; [exact R0 | exact R1]. Qed.
Lemma if01_zero : forall c : bool, (if c then 1 else 0) = 0 -> c = false.
Proof. intros [|]; [discriminate | reflexivity]. Qed.
Lemma if01_nonzero : forall c : bool, (if c then 1 else 0) <> 0 -> c = true.
Proof. intros [|]; [reflexivity | intros H; exfalso; apply H; reflexivity]. Qed.
Lemma zbv_inj64 : forall a b, Z_to_bv 64 a = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
intros a b H Ha Hb. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
change (bv_modulus 64) with (2 ^ 64) in H. rewrite !Z.mod_small in H by lia. exact H.
Qed.
Ltac xt_npal :=
lazymatch goal with H : branch_taken BC_NE (sv_denot ?Ev (SOff ?a 0)) (sv_denot _ (SLit 256)) = ?b |- _ =>
lazymatch goal with En : ew _ a = Z_to_bv 64 ?v |- _ =>
lazymatch goal with Rv : 0 <= v < _ |- _ =>
let T := fresh "XT3" in pose proof H as T; rewrite branch_ne_U, U_lit in T by lia;
rewrite (U_atom Ev a v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact En) ltac:(clear - Rv; lia)) in T
end end end.
Lemma ldiff_low_mask : forall x k, 0 <= x -> 0 <= k -> Z.land x (Z.lnot (Z.ones k)) = x - x mod 2 ^ k.
Proof.
intros x k Hx Hk.
replace (x - x mod 2 ^ k) with ((x / 2 ^ k) * 2 ^ k) by (pose proof (Z.div_mod x (2 ^ k) ltac:(lia)); lia).
rewrite <- Z.ldiff_land. apply Z.bits_inj'. intros n Hn.
rewrite Z.ldiff_spec. destruct (Z_lt_le_dec n k) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. rewrite Z.ones_spec_low by lia. apply Bool.andb_false_r.
- rewrite Z.ones_spec_high by lia. rewrite Bool.andb_true_r.
rewrite Z.mul_pow2_bits by lia. rewrite Z.div_pow2_bits by lia. f_equal. lia.
Qed.
Lemma clr_3 : forall x, 0 <= x -> YO07.clr x 3 = x - x mod 4.
Proof. intros x Hx. unfold YO07.clr. change 3 with (Z.ones 2). change 4 with (2 ^ 2). apply ldiff_low_mask; lia. Qed.
Lemma clr_1 : forall x, 0 <= x -> YO07.clr x 1 = x - x mod 2.
Proof. intros x Hx. unfold YO07.clr. change (Z.lnot 1) with (Z.lnot (Z.ones 1)). change (x mod 2) with (x mod 2 ^ 1). apply ldiff_low_mask; lia. Qed.
Lemma clr_range : forall x m, 0 <= x -> (m = 1 \/ m = 3) -> 0 <= YO07.clr x m <= x.
Proof.
intros x m Hx [-> | ->]; [rewrite clr_1 by lia; pose proof (Z.mod_pos_bound x 2 ltac:(lia)); pose proof (Z.mod_le x 2 Hx ltac:(lia)) | rewrite clr_3 by lia; pose proof (Z.mod_pos_bound x 4 ltac:(lia)); pose proof (Z.mod_le x 4 Hx ltac:(lia))]; lia.
Qed.
Lemma fl_gen3_range : forall g cur bef, 0 <= YO07.f_gen cur ->
0 <= YI0f.fl_gen3 g cur bef <= YO07.f_gen cur.
Proof.
intros g cur bef Hg.
assert (G1 : 0 <= YI0f.fl_gen1 g cur bef <= YO07.f_gen cur).
{ unfold YI0f.fl_gen1. destruct bef; [destruct (YI0f.fl_hasAlpha g cur)|]; try (pose proof (clr_range (YO07.f_gen cur) 3 Hg ltac:(lia))); lia. }
assert (G2 : 0 <= YI0f.fl_gen2 g cur bef <= YO07.f_gen cur).
{ unfold YI0f.fl_gen2. destruct (YI0f.fl_hasSet cur); [pose proof (clr_range _ 1 (proj1 G1) ltac:(lia))|]; lia. }
unfold YI0f.fl_gen3. destruct (_ =? 256); [pose proof (clr_range _ 1 (proj1 G2) ltac:(lia))|]; lia.
Qed.
Lemma fl_gen3_first : forall g cur, 0 <= YO07.f_gen cur -> Z.land (YI0f.fl_gen3 g cur None) 3 = 0.
Proof.
intros g cur Hg.
assert (C4 : forall x, 0 <= x -> (YO07.clr x 3) mod 4 = 0).
{ intros x Hx. rewrite clr_3 by lia. replace (x - x mod 4) with (x / 4 * 4) by (pose proof (Z.div_mod x 4 ltac:(lia)); lia). apply Z_mod_mult. }
assert (C2 : forall x, 0 <= x -> x mod 4 = 0 -> (YO07.clr x 1) mod 4 = 0).
{ intros x Hx H4. rewrite clr_1 by lia. replace (x mod 2) with 0; [rewrite Z.sub_0_r; exact H4|].
pose proof (Z.div_mod x 4 ltac:(lia)) as D. rewrite H4, Z.add_0_r in D. rewrite D, Z.mul_comm. symmetry.
replace (x / 4 * 4) with ((x / 4 * 2) * 2) by lia. apply Z_mod_mult. }
assert (M : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 3 = 0).
{ intros x Hx H4. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H4. }
assert (G1 : 0 <= YI0f.fl_gen1 g cur None /\ YI0f.fl_gen1 g cur None mod 4 = 0).
{ unfold YI0f.fl_gen1. split; [pose proof (clr_range (YO07.f_gen cur) 3 Hg ltac:(lia)); lia | apply C4; exact Hg]. }
assert (G2 : 0 <= YI0f.fl_gen2 g cur None /\ YI0f.fl_gen2 g cur None mod 4 = 0).
{ unfold YI0f.fl_gen2. destruct (YI0f.fl_hasSet cur); [|exact G1].
split; [pose proof (clr_range _ 1 (proj1 G1) ltac:(lia)); lia | apply C2; [exact (proj1 G1) | exact (proj2 G1)]]. }
apply M.
- unfold YI0f.fl_gen3. destruct (_ =? 256); [pose proof (clr_range _ 1 (proj1 G2) ltac:(lia)); lia | exact (proj1 G2)].
- unfold YI0f.fl_gen3. destruct (_ =? 256); [apply C2; [exact (proj1 G2) | exact (proj2 G2)] | exact (proj2 G2)].
Qed.
Lemma land_bit_of3' : forall x m, (m = 1 \/ m = 2) -> Z.land x 3 = 0 -> Z.land x m = 0.
Proof.
intros x m Hm H3. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
apply (f_equal (fun z => Z.testbit z n)) in H3. rewrite Z.land_spec, Z.bits_0 in H3.
destruct Hm as [-> | ->].
- destruct (Z.eq_dec n 0) as [-> | Hn0]; [exact H3|]. rewrite (Z.bits_above_log2 1 n) by (cbn; lia). apply Bool.andb_false_r.
- destruct (Z.eq_dec n 1) as [-> | Hn1]; [exact H3|].
replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. change 2 with (2 ^ 1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma fl_diff_some : forall g cur bef, 0 <= YO07.f_gen cur -> YO07.flag (YI0f.fl_gen3 g cur bef) 2 = true -> exists b, bef = Some b.
Proof.
intros g cur [b|] Hg H; [exists b; reflexivity|]. exfalso. unfold YO07.flag in H.
rewrite (land_bit_of3' _ 2 ltac:(lia) (fl_gen3_first g cur Hg)) in H. discriminate H.
Qed.
Lemma fl_trans_some : forall g cur bef, 0 <= YO07.f_gen cur -> YO07.flag (YI0f.fl_gen3 g cur bef) 1 = true -> exists b, bef = Some b.
Proof.
intros g cur [b|] Hg H; [exists b; reflexivity|]. exfalso. unfold YO07.flag in H.
rewrite (land_bit_of3' _ 1 ltac:(lia) (fl_gen3_first g cur Hg)) in H. discriminate H.
Qed.
Lemma fl_dims_nodiff : forall g cur bef, YO07.flag (YI0f.fl_gen3 g cur bef) 2 = false ->
YI0f.fl_dims g cur bef = (YO07.g_w g, YO07.g_h g, 0, 0).
Proof. intros g cur [b|] H; unfold YI0f.fl_dims; [rewrite H|]; reflexivity. Qed.
Lemma fl_tmp_nodiff : forall g cur bef, YO07.flag (YI0f.fl_gen3 g cur bef) 2 = false -> YI0f.fl_tmp g cur bef = YO07.f_img cur.
Proof. intros g cur [b|] H; unfold YI0f.fl_tmp; [rewrite H|]; reflexivity. Qed.
Lemma fl_img_notrans : forall g cur bef, YO07.flag (YI0f.fl_gen3 g cur bef) 1 = false -> YI0f.fl_img g cur bef = YI0f.fl_tmp g cur bef.
Proof. intros g cur [b|] H; unfold YI0f.fl_img; [rewrite H | unfold YI0f.fl_tmp]; reflexivity. Qed.
Lemma fl_tidx_notrans : forall g cur bef, YO07.flag (YI0f.fl_gen3 g cur bef) 1 = false -> YI0f.fl_tidx g cur bef = YO07.f_trans cur.
Proof. intros g cur [b|] H; unfold YI0f.fl_tidx; [rewrite H|]; reflexivity. Qed.
Lemma fl_trans_on_flag : forall g cur bef, 0 <= YO07.f_gen cur -> YI0f.fl_trans_on g cur bef = YO07.flag (YI0f.fl_gen3 g cur bef) 1.
Proof.
intros g cur [b|] Hg; unfold YI0f.fl_trans_on; [reflexivity|].
unfold YO07.flag. rewrite (land_bit_of3' _ 1 ltac:(lia) (fl_gen3_first g cur Hg)). reflexivity.
Qed.
Lemma isfirst_of_opt : forall (o : option frame_st) (q : option YO07.frame),
(match o, q with None, None => True | Some _, Some _ => True | _, _ => False end) ->
(forall fb, o = Some fb -> fr_ptr fb <> 0) ->
(frame_ptr o =? 0) = match q with None => true | Some _ => false end.
Proof.
intros [fb|] [b|] Hm Hnz; cbn [frame_ptr]; try contradiction; [|reflexivity].
apply Z.eqb_neq. apply (Hnz fb eq_refl).
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Lemma fl_gen123_range : forall cx, 0 <= fr_gen (c_f cx) ->
0 <= ACj6.fl_gen1 cx <= fr_gen (c_f cx) /\ 0 <= ACj6.fl_gen2 cx <= fr_gen (c_f cx) /\ 0 <= ACj6.fl_gen3 cx <= fr_gen (c_f cx).
Proof.
intros cx Hg.
assert (G1 : 0 <= ACj6.fl_gen1 cx <= fr_gen (c_f cx)).
{ unfold ACj6.fl_gen1. destruct (_ || _); [pose proof (clr4_range _ Hg); lia | lia]. }
assert (G2 : 0 <= ACj6.fl_gen2 cx <= fr_gen (c_f cx)).
{ unfold ACj6.fl_gen2. destruct (fl_settr cx); [pose proof (clr2_range _ (proj1 G1)); lia | lia]. }
split; [exact G1|]. split; [exact G2|].
unfold ACj6.fl_gen3. destruct (_ =? _); [pose proof (clr2_range _ (proj1 G2)); lia | lia].
Qed.
Lemma fl_front_model : forall (cx : flcx) GPAL (cur : YO07.frame) (bef : option YO07.frame),
fr_attr (c_f cx) = YO07.f_attr cur -> fr_gen (c_f cx) = YO07.f_gen cur -> fr_nlp (c_f cx) = YO07.f_nlp cur -> 0 <= fr_gen (c_f cx) ->
ACj6.fl_isfirst cx = match bef with None => true | Some _ => false end ->
ACj6.fl_npal cx = YI0f.fl_npal (gcfg_of (c_s cx) GPAL) cur /\
ACj6.fl_uselct cx = YI0f.fl_useLCT cur /\
ACj6.fl_hasalpha cx = YI0f.fl_hasAlpha (gcfg_of (c_s cx) GPAL) cur /\
ACj6.fl_settr cx = YI0f.fl_hasSet cur /\
ACj6.fl_gen3 cx = YI0f.fl_gen3 (gcfg_of (c_s cx) GPAL) cur bef.
Proof.
intros cx GPAL cur bef Ea Eg En Hg Hfirst.
assert (U : ACj6.fl_uselct cx = YI0f.fl_useLCT cur) by (unfold ACj6.fl_uselct, YI0f.fl_useLCT, YO07.flag; rewrite Ea; reflexivity).
assert (A : ACj6.fl_hasalpha cx = YI0f.fl_hasAlpha (gcfg_of (c_s cx) GPAL) cur).
{ unfold ACj6.fl_hasalpha, YI0f.fl_hasAlpha, YO07.flag. cbn [YO07.g_attr gcfg_of]. rewrite Ea. apply Bool.negb_andb. }
assert (T : ACj6.fl_settr cx = YI0f.fl_hasSet cur) by (unfold ACj6.fl_settr, YI0f.fl_hasSet, YO07.flag; rewrite Ea; reflexivity).
assert (N : ACj6.fl_npal cx = YI0f.fl_npal (gcfg_of (c_s cx) GPAL) cur).
{ unfold ACj6.fl_npal, YI0f.fl_npal. rewrite U, En. cbn [YO07.g_ngp gcfg_of]. reflexivity. }
assert (G1 : ACj6.fl_gen1 cx = YI0f.fl_gen1 (gcfg_of (c_s cx) GPAL) cur bef).
{ unfold ACj6.fl_gen1, YI0f.fl_gen1. rewrite Hfirst, A, Eg. unfold clr4. rewrite clr_3 by lia.
destruct bef; [reflexivity|]. reflexivity. }
assert (G2 : ACj6.fl_gen2 cx = YI0f.fl_gen2 (gcfg_of (c_s cx) GPAL) cur bef).
{ unfold ACj6.fl_gen2, YI0f.fl_gen2. rewrite T, G1. unfold clr2.
rewrite clr_1 by (pose proof (fl_gen123_range cx Hg) as R; rewrite G1 in R; lia). reflexivity. }
split; [exact N|]. split; [exact U|]. split; [exact A|]. split; [exact T|].
unfold ACj6.fl_gen3, YI0f.fl_gen3. rewrite N, G2. unfold clr2.
rewrite clr_1 by (pose proof (fl_gen123_range cx Hg) as R; rewrite G2 in R; lia). reflexivity.
Qed.
End e.
End d.
