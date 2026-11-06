(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals Lra.
From Flocq Require Import Core.Raux Core.Defs.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK1b YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ0i YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YI02 YI01 YP14 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04 YM01 YM02 YM06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition nlp (pal fr : list Z) (imin i d : Z) : list (Z * Z) := node_list pal fr imin (i - 1) d.
Lemma nlp_nil : forall pal fr imin d, nlp pal fr imin imin d = [].
Proof. intros. unfold nlp, node_list. replace (imin - 1 - imin + 1) with 0 by lia. reflexivity. Qed.
Lemma nlp_snoc : forall pal fr imin i d, imin <= i ->
nlp pal fr imin (i + 1) d = nlp pal fr imin i d ++ [(getz fr i, getz pal (3 * i + d))].
Proof.
intros pal fr imin i d Hi. unfold nlp, node_list.
replace (i + 1 - 1 - imin + 1) with ((i - 1 - imin + 1) + 1) by lia.
rewrite zseq_succ by lia. rewrite map_app. cbn [map]. f_equal. f_equal. f_equal; f_equal; lia.
Qed.
Lemma nlp_full : forall pal fr imin imax d, nlp pal fr imin (imax + 1) d = node_list pal fr imin imax d.
Proof. intros. unfold nlp. f_equal. lia. Qed.
Lemma wsum_snoc : forall l f p, wsum (l ++ [(f, p)]) = wsum l + f.
Proof. intros. rewrite wsum_app. cbn. lia. Qed.
Lemma wdot_snoc : forall l f p, wdot (l ++ [(f, p)]) = wdot l + f * p.
Proof. intros. rewrite wdot_app. cbn. lia. Qed.
Lemma wsum_nlp_dim : forall pal fr imin i d d', wsum (nlp pal fr imin i d) = wsum (nlp pal fr imin i d').
Proof.
intros pal fr imin i d d'. unfold nlp, node_list. generalize (zseq imin (i - 1 - imin + 1)). intros l.
induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Section c.
Variables (pal fr : list Z) (imin imax : Z).
Hypothesis Hii : 0 <= imin <= imax.
Hypothesis Hpal : forall j, (j < length pal)%nat -> 0 <= nth j pal 0 < 256.
Hypothesis Hfr1 : forall i, imin <= i <= imax -> 1 <= getz fr i.
Hypothesis Hfr32 : forall j, (j < length fr)%nat -> 0 <= nth j fr 0 < 2 ^ 32.
Hypothesis Hlenp : 3 * (imax + 1) <= zlen pal.
Hypothesis Hlenf : imax + 1 <= zlen fr.
Hypothesis Hsum : wsum (node_list pal fr imin imax 0) <= RGB_NMAX.
Lemma pal_byte : forall k, 0 <= k < zlen pal -> 0 <= getz pal k < 256.
Proof. intros k Hk. unfold getz. apply Hpal. unfold zlen in Hk. lia. Qed.
Lemma fr_word : forall k, 0 <= k < zlen fr -> 0 <= getz fr k < 2 ^ 32.
Proof. intros k Hk. unfold getz. apply Hfr32. unfold zlen in Hk. lia. Qed.
Lemma nlp_node_ok : forall i d, imin <= i <= imax + 1 -> 0 <= d <= 2 -> node_ok (nlp pal fr imin i d).
Proof.
intros i d Hi Hd. unfold node_ok, nlp. apply Forall_forall. intros x Hx.
apply In_node_list in Hx as (k & Hk & ->). cbn [fst snd].
split; [apply Hfr1; lia|]. pose proof (pal_byte (3 * k + d) ltac:(lia)). lia.
Qed.
Lemma wsum_nlp_le : forall i d, imin <= i <= imax + 1 -> 0 <= wsum (nlp pal fr imin i d) <= RGB_NMAX.
Proof.
intros i d Hi. rewrite (wsum_nlp_dim pal fr imin i d 0).
assert (Hmono : forall j, imin <= j <= imax + 1 -> 0 <= wsum (nlp pal fr imin j 0) /\
(j <= imax -> wsum (nlp pal fr imin j 0) + 1 <= wsum (nlp pal fr imin (imax + 1) 0))).
{ intros j Hj.
assert (Hgen : forall n, 0 <= Z.of_nat n -> j + Z.of_nat n <= imax + 1 ->
wsum (nlp pal fr imin j 0) + Z.of_nat n <= wsum (nlp pal fr imin (j + Z.of_nat n) 0)).
{ intros n. induction n as [|n IH]; intros Hn0 Hn.
- change (Z.of_nat 0) with 0. rewrite !Z.add_0_r. lia.
- replace (j + Z.of_nat (S n)) with (j + Z.of_nat n + 1) by lia. rewrite nlp_snoc by lia. rewrite wsum_snoc.
pose proof (Hfr1 (j + Z.of_nat n) ltac:(lia)). specialize (IH ltac:(lia) ltac:(lia)). lia. }
assert (H0 : forall n, imin + Z.of_nat n <= imax + 1 -> 0 <= wsum (nlp pal fr imin (imin + Z.of_nat n) 0)).
{ intros n. induction n as [|n IH]; intros Hn.
- change (Z.of_nat 0) with 0. rewrite Z.add_0_r, nlp_nil. cbn. lia.
- replace (imin + Z.of_nat (S n)) with (imin + Z.of_nat n + 1) by lia. rewrite nlp_snoc by lia. rewrite wsum_snoc.
pose proof (Hfr1 (imin + Z.of_nat n) ltac:(lia)). specialize (IH ltac:(lia)). lia. }
split.
- specialize (H0 (Z.to_nat (j - imin)) ltac:(lia)). replace (imin + Z.of_nat (Z.to_nat (j - imin))) with j in H0 by lia. exact H0.
- intros Hle. specialize (Hgen (Z.to_nat (imax + 1 - j)) ltac:(lia) ltac:(lia)).
replace (j + Z.of_nat (Z.to_nat (imax + 1 - j))) with (imax + 1) in Hgen by lia. lia. }
pose proof (Hmono i Hi) as [H1 H2]. rewrite nlp_full in H2.
destruct (Z_le_gt_dec i imax); [specialize (H2 ltac:(lia)); lia|].
replace i with (imax + 1) by lia. rewrite nlp_full. split; [|exact Hsum].
pose proof (Hmono (imax + 1) ltac:(lia)) as [H3 _]. rewrite nlp_full in H3. exact H3.
Qed.
Lemma wdot_nlp_le : forall i d, imin <= i <= imax + 1 -> 0 <= d <= 2 -> 0 <= wdot (nlp pal fr imin i d) <= 255 * RGB_NMAX.
Proof.
intros i d Hi Hd. pose proof (wdot_bounds _ (nlp_node_ok i d Hi Hd)) as [H1 _].
pose proof (wsum_nlp_le i d Hi). lia.
Qed.
End c.
Local Abbreviation D := fmt_double.
Lemma u64_rangeN : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma val_cvt_wu : forall E (a : sv) (v : Z),
bv_unsigned (sv_denot E a) = v -> 0 <= v < 2 ^ 32 ->
is_intd (bv_unsigned (sv_denot E (SF1 (FP1_cvt FC_D FC_WU RNE) a))) v.
Proof.
intros E a v Ha Hv. cbn [sv_denot]. rewrite <- fp_arg_D, fp_arg_fcvt_d_wu, Ha.
rewrite <- (Z.mod_small v (2 ^ 32)) at 2 by lia. apply (proj1 (is_intd_of_int_wu RNE v)).
Qed.
Lemma val_cvt_mul : forall E (a b : sv) (f p : Z),
bv_unsigned (sv_denot E a) = f -> bv_unsigned (sv_denot E b) = p -> 0 <= f -> 0 <= p -> f * p < 2 ^ 32 ->
is_intd (bv_unsigned (sv_denot E (SF1 (FP1_cvt FC_D FC_WU RNE) (SMd M_MUL a b)))) (f * p).
Proof.
intros E a b f p Ha Hb Hf Hp Hfp. apply val_cvt_wu; [|nia].
change (bv_unsigned (sv_denot E (SMd M_MUL a b))) with (U E (SMd M_MUL a b)). rewrite U_SMd. cbn [zmd_raw].
unfold U. rewrite Ha, Hb. apply zcanon_id. unfold M64. nia.
Qed.
Lemma val_fadd : forall E (a b : sv) (m n : Z),
is_intd (bv_unsigned (sv_denot E a)) m -> is_intd (bv_unsigned (sv_denot E b)) n -> Z.abs (m + n) <= 2 ^ 53 ->
is_intd (bv_unsigned (sv_denot E (SF2 (FP2_ari F_ADD FMT_D RNE) a b))) (m + n).
Proof.
intros E a b m n Ha Hb Hmn. cbn [sv_denot]. rewrite <- fp_arg_D, fp_arg_ari. cbn [fari_sem fp_format]. rewrite !fp_arg_D.
apply (proj1 (is_intd_add RNE _ _ _ _ Ha Hb Hmn)).
Qed.
Lemma val_fdiv : forall E (a b : sv),
bv_unsigned (sv_denot E (SF2 (FP2_ari F_DIV FMT_D RNE) a b)) = fst (fp_div D RNE (bv_unsigned (sv_denot E a)) (bv_unsigned (sv_denot E b))).
Proof. intros. cbn [sv_denot]. rewrite <- fp_arg_D, fp_arg_ari. cbn [fari_sem fp_format]. rewrite !fp_arg_D. reflexivity. Qed.
Lemma val_vstep : forall E (ep ef emean eacc : sv),
let t1 := SF2 (FP2_ari F_SUB FMT_D RNE) (SF1 (FP1_cvt FC_D FC_WU RNE) ep) emean in
let t2 := SF2 (FP2_ari F_MUL FMT_D RNE) t1 (SF1 (FP1_cvt FC_D FC_WU RNE) ef) in
bv_unsigned (sv_denot E (SF3 (FP3_fma F_MADD FMT_D RNE) t2 t1 eacc)) =
let xp := bv_unsigned (sv_denot E (SF1 (FP1_cvt FC_D FC_WU RNE) ep)) in
let xf := bv_unsigned (sv_denot E (SF1 (FP1_cvt FC_D FC_WU RNE) ef)) in
let mean := bv_unsigned (sv_denot E emean) in
let u1 := fst (fp_sub D RNE xp mean) in
let u2 := fst (fp_mul D RNE u1 xf) in
fst (fp_fma D RNE u2 u1 (bv_unsigned (sv_denot E eacc))).
Proof.
intros E ep ef emean eacc t1 t2. subst t2 t1. cbn [sv_denot]. rewrite <- !fp_arg_D. rewrite fp_arg_fmadd. cbn [fp_format].
rewrite !fp_arg_ari. cbn [fari_sem fp_format]. rewrite ?fp_arg_ari. cbn [fari_sem fp_format]. reflexivity.
Qed.
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Lemma val_mem_byte : forall segs m a v, mbyte segs m a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> val_mem segs m a 1 v.
Proof.
intros segs m a v H Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma neq_meanb_snoc : forall s m l f p, neq_meanb s m (l ++ [(f, p)]) = (neq_meanb s m l || negb (p * s =? m))%bool.
Proof. intros. rewrite neq_meanb_app. cbn. rewrite Bool.orb_false_r. reflexivity. Qed.
Lemma argmax_pick : forall (w0 w1 w2 : Z) (v0 v1 v2 : R) (p0 p1 p2 b1 b2 b3 : bool),
dval w0 v0 -> dval w1 v1 -> dval w2 v2 -> (0 <= v0)%R -> (0 <= v1)%R -> (0 <= v2)%R ->
(if p0 then (0 < v0)%R else v0 = 0%R) -> (if p1 then (0 < v1)%R else v1 = 0%R) -> (if p2 then (0 < v2)%R else v2 = 0%R) ->
fst (fp_lt D 0 w0) = b1 ->
fst (fp_lt D (if b1 then w0 else 0) w1) = b2 ->
fst (fp_lt D (if b2 then w1 else if b1 then w0 else 0) w2) = b3 ->
p0 = true \/ p1 = true \/ p2 = true ->
(if b3 then p2 else if b2 then p1 else p0) = true.
Proof.
intros w0 w1 w2 v0 v1 v2 p0 p1 p2 b1 b2 b3 D0 D1 D2 H0 H1 H2 P0 P1 P2 C1 C2 C3 Hex.
rewrite (dval_flt _ _ _ _ dval_zero D0) in C1. cbn [fst] in C1.
set (m1 := if b1 then v0 else 0%R).
assert (C2' : Rlt_bool m1 v1 = b2).
{ subst m1. destruct b1; [rewrite (dval_flt _ _ _ _ D0 D1) in C2 | rewrite (dval_flt _ _ _ _ dval_zero D1) in C2]; exact C2. }
set (m2 := if b2 then v1 else m1).
assert (C3' : Rlt_bool m2 v2 = b3).
{ subst m2 m1. destruct b2; [rewrite (dval_flt _ _ _ _ D1 D2) in C3 | destruct b1; [rewrite (dval_flt _ _ _ _ D0 D2) in C3 | rewrite (dval_flt _ _ _ _ dval_zero D2) in C3]]; exact C3. }
clear C2 C3.
assert (M1 : (0 <= m1)%R /\ (v0 <= m1)%R /\ (b1 = false -> m1 = 0%R)).
{ subst m1. destruct (Rlt_bool_spec 0 v0) as [Hb|Hb]; rewrite <- C1;
(split; [lra|]); (split; [lra|]); intros HH; [discriminate HH | reflexivity]. }
assert (M2 : (0 <= m2)%R /\ (v1 <= m2)%R /\ (m1 <= m2)%R /\ (b2 = false -> m2 = m1)).
{ subst m2. destruct (Rlt_bool_spec m1 v1) as [Hb|Hb]; rewrite <- C2';
(split; [lra|]); (split; [lra|]); (split; [lra|]); intros HH; [discriminate HH | reflexivity]. }
destruct b3.
- destruct (Rlt_bool_spec m2 v2) as [Hb|Hb]; [|discriminate C3']. destruct p2; [reflexivity|]. exfalso. lra.
- destruct (Rlt_bool_spec m2 v2) as [Hb3|Hb3]; [discriminate C3'|].
destruct b2.
+ destruct (Rlt_bool_spec m1 v1) as [Hb|Hb]; [|discriminate C2']. destruct p1; [reflexivity|]. exfalso. lra.
+ destruct (Rlt_bool_spec m1 v1) as [Hb2|Hb2]; [discriminate C2'|].
destruct b1.
* destruct (Rlt_bool_spec 0 v0) as [Hb|Hb]; [|discriminate C1]. destruct p0; [reflexivity|]. exfalso. lra.
* destruct (Rlt_bool_spec 0 v0) as [Hb1|Hb1]; [discriminate C1|].
destruct M1 as (_ & _ & M1z). specialize (M1z eq_refl).
destruct M2 as (_ & _ & _ & M2z). specialize (M2z eq_refl).
exfalso. destruct Hex as [Hx|[Hx|Hx]]; rewrite Hx in *; lra.
Qed.
Lemma flt_taken : forall E (x y : sv) (b : bool),
branch_taken BC_NE (sv_denot E (SF2 (FP2_cmp F_LT FMT_D) x y)) (sv_denot E (SLit 0)) = b ->
fst (fp_lt D (bv_unsigned (sv_denot E x)) (bv_unsigned (sv_denot E y))) = b.
Proof.
intros E x y b H. cbn [sv_denot] in H. rewrite fcmp_denot in H. cbn [fcmp_sem fp_format] in H. rewrite !fp_arg_D in H.
destruct (fst (fp_lt D _ _)); destruct b; try reflexivity; vm_compute in H; discriminate H.
Qed.
Lemma sv_fmv_d : forall E (x : sv), sv_denot E (SF2 (FP2_sgnj F_SGNJ FMT_D) x x) = sv_denot E x.
Proof. intros E x. cbn [sv_denot]. apply fmv_d_denot. Qed.
Lemma denot_lit0 : forall E, bv_unsigned (sv_denot E (SLit 0)) = 0.
Proof. intros E. vm_compute. reflexivity. Qed.
Lemma le_byte_of_sum8 : forall (u : nat -> Z) k, (forall j, 0 <= u j < 256) -> (k < 8)%nat ->
le_byte (u 0%nat + 256 * (u 1%nat + 256 * (u 2%nat + 256 * (u 3%nat + 256 * (u 4%nat + 256 * (u 5%nat + 256 * (u 6%nat + 256 * u 7%nat))))))) 8 k = u k.
Proof.
intros u k Hu Hk.
pose proof (Hu 0%nat). pose proof (Hu 1%nat). pose proof (Hu 2%nat). pose proof (Hu 3%nat).
pose proof (Hu 4%nat). pose proof (Hu 5%nat). pose proof (Hu 6%nat). pose proof (Hu 7%nat).
unfold le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616.
rewrite (Z.mod_small _ 18446744073709551616) by lia.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]. 9: lia.
all: cbn -[Z.add Z.mul Z.modulo Z.div].
all: clear Hu Hk.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
all: nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma val_mem_of_present8 : forall segs mem a,
(forall i, 0 <= i < 8 -> exists b, mbyte segs mem (a + i) = Some b) ->
exists v, 0 <= v < 2 ^ 64 /\ val_mem segs mem a 8 v.
Proof.
intros segs mem a H.
set (u := fun j : nat => match mbyte segs mem (a + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end).
assert (Hu : forall j, 0 <= u j < 256 /\ ((j < 8)%nat -> mbyte segs mem (a + Z.of_nat j) = Some (Z_to_bv 8 (u j)))).
{ intros j. subst u. cbv beta. destruct (mbyte segs mem (a + Z.of_nat j)) as [b|] eqn:Hb.
- pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [lia|]. intros _. rewrite Z_to_bv_bv_unsigned. reflexivity.
- split; [lia|]. intros Hj. destruct (H (Z.of_nat j) ltac:(lia)) as [b Hb']. rewrite Hb' in Hb. discriminate Hb. }
exists (u 0%nat + 256 * (u 1%nat + 256 * (u 2%nat + 256 * (u 3%nat + 256 * (u 4%nat + 256 * (u 5%nat + 256 * (u 6%nat + 256 * u 7%nat))))))).
pose proof (proj1 (Hu 0%nat)). pose proof (proj1 (Hu 1%nat)). pose proof (proj1 (Hu 2%nat)). pose proof (proj1 (Hu 3%nat)).
pose proof (proj1 (Hu 4%nat)). pose proof (proj1 (Hu 5%nat)). pose proof (proj1 (Hu 6%nat)). pose proof (proj1 (Hu 7%nat)).
split; [lia|].
intros k Hk. rewrite (proj2 (Hu k) Hk). f_equal. f_equal. symmetry. apply le_byte_of_sum8; [intros j; apply (proj1 (Hu j)) | exact Hk].
Qed.
Lemma val_mem_kept : forall segs m m' a n v,
val_mem segs m a n v -> (forall k, a <= k < a + Z.of_nat n -> mbyte segs m' k = mbyte segs m k) -> val_mem segs m' a n v.
Proof. intros segs m m' a n v H Hk j Hj. rewrite Hk by lia. apply H. exact Hj. Qed.
Lemma mbyte_of_present : forall segs m a, present m a -> exists b, mbyte segs m a = Some b.
Proof. intros segs m a [b Hb]. exists b. unfold mbyte. rewrite Hb. reflexivity. Qed.
