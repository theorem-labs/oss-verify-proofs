(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.

Definition mem := word -> option byte.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia. Qed.

Lemma zlength_map_unsigned : forall bs : list byte, zlength (map bv_unsigned bs) = Z.of_nat (length bs).
Proof. intros. unfold zlength. rewrite length_map. reflexivity. Qed.

Lemma znth_map_unsigned : forall (bs : list byte) i, 0 <= i -> (Z.to_nat i < length bs)%nat ->
znth (map bv_unsigned bs) i = bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
intros bs i Hi Hlt. unfold znth. destruct (Z.ltb_spec i 0); [lia|].
rewrite <- (map_nth bv_unsigned). f_equal.
Qed.

Lemma unsigned_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros. unfold zxb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (byte_range b). unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia. Qed.

Lemma zxb_nth_model : forall (bs : list byte) (data : list Z) i, data = map bv_unsigned bs ->
0 <= i -> (Z.to_nat i < length bs)%nat ->
zxb (nth (Z.to_nat i) bs (Z_to_bv 8 0)) = Z_to_bv 64 (znth data i).
Proof. intros bs data i -> Hi Hlt. unfold zxb. rewrite znth_map_unsigned by assumption. reflexivity. Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun z => 0 <= z < 256) (map bv_unsigned bs).
Proof. intros bs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz. destruct Hz as (b & <- & _). apply byte_range. Qed.

Lemma byte_list_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma map_Z_to_bv_unsigned : forall bs : list byte, map (fun z => Z_to_bv 8 z) (map bv_unsigned bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Definition int31 (z : Z) : Prop := 0 <= z < 2^31.

Lemma unsigned_lit64 : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia. Qed.

Lemma sx32_small : forall v, int31 v -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v [H0 H1]. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64).
change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
rewrite (Z.mod_small v (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zx32_small : forall v, 0 <= v < 2^32 -> zx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold zx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (Z.mod_small v (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_lit_small : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2^64) in *. change (bv_half_modulus 64) with (2^63) in *.
rewrite Zplus_mod_idemp_l.
destruct (Z.lt_ge_cases z 0).
- replace ((z + 2 ^ 63) mod 2 ^ 64) with (z + 2^63); [lia|]. symmetry. apply Z.mod_small. lia.
- rewrite Z.mod_small by lia. lia.
Qed.

Lemma le4_eqm : forall v1 v2 : word, bv_unsigned v1 mod 2^32 = bv_unsigned v2 mod 2^32 -> le4 v1 = le4 v2.
Proof.
intros v1 v2 E. unfold le4.
rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v1) 32) by (cbn; lia).
rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v2) 32) by (cbn; lia).
rewrite E. reflexivity.
Qed.

Lemma mod64_mod32 : forall x, (x mod 2^64) mod 2^32 = x mod 2^32.
Proof.
intros x. change (2^64) with (2^32 * 2^32). rewrite Z.rem_mul_r by lia.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma le4_lit_eqm : forall x y, x mod 2^32 = y mod 2^32 -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 y).
Proof.
intros x y E. apply le4_eqm. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite !mod64_mod32. exact E.
Qed.

Lemma rw_cells_samebytes : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split|].
- exact Hwf'.
- rewrite Eb. exact Hb.
- rewrite Es. exact Hw.
Qed.

Lemma swrap32_eqm : forall x y, x mod 2^32 = y mod 2^32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
intros x y E. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
rewrite (Z.add_mod x), (Z.add_mod y) by lia. rewrite E. reflexivity.
Qed.
Lemma swrap32_plus_mod64 : forall a b, bv_swrap 32 (a + b mod 2^64) = bv_swrap 32 (a + b).
Proof. intros. apply swrap32_eqm. rewrite Z.add_mod, mod64_mod32, <- Z.add_mod by lia. reflexivity. Qed.
Lemma swrap32_mod64_plus : forall a b, bv_swrap 32 (a mod 2^64 + b) = bv_swrap 32 (a + b).
Proof. intros. apply swrap32_eqm. rewrite Z.add_mod, mod64_mod32, <- Z.add_mod by lia. reflexivity. Qed.
Lemma swrap32_mod64 : forall a, bv_swrap 32 (a mod 2^64) = bv_swrap 32 a.
Proof. intros. apply swrap32_eqm. apply mod64_mod32. Qed.
Lemma swrap32_swrap32_plus : forall a b, bv_swrap 32 (bv_swrap 32 a + b) = bv_swrap 32 (a + b).
Proof.
intros. apply swrap32_eqm. rewrite Z.add_mod, (Z.add_mod a b) by lia. f_equal. f_equal.
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
rewrite Zminus_mod_idemp_l. replace (a + 2^31 - 2^31) with a by lia. reflexivity.
Qed.
Lemma swrap32_plus_swrap32 : forall a b, bv_swrap 32 (a + bv_swrap 32 b) = bv_swrap 32 (a + b).
Proof. intros. rewrite (Z.add_comm a (bv_swrap 32 b)), swrap32_swrap32_plus. f_equal. lia. Qed.

Lemma mod64_mod8 : forall x, (x mod 2^64) mod 8 = x mod 8.
Proof.
intros x. change (2^64) with (8 * 2^61). rewrite Z.rem_mul_r by lia.
rewrite (Z.mul_comm 8). rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma land7_mod64 : forall v, Z.land (v mod 2^64) 7 = v mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. apply mod64_mod8. Qed.
Lemma land7_mod8 : forall v, Z.land v 7 = v mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma adv_char_eqm : forall c v, -2^63 <= v < 2^63 ->
((v mod 2^64) / 8 + c) mod 2^32 = (c + v / 8) mod 2^32.
Proof.
intros c v Hv. destruct (Z.lt_ge_cases v 0).
- replace (v mod 2^64) with (v + 2^61 * 8).
2:{ rewrite <- (Z.mod_add v 1) by lia. rewrite Z.mod_small; lia. }
rewrite Z.div_add by lia.
replace (v / 8 + 2^61 + c) with ((c + v / 8) + 2^29 * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
- rewrite (Z.mod_small v (2^64)) by lia. f_equal. lia.
Qed.

Ltac nswrap :=
rewrite ?swrap32_plus_mod64, ?swrap32_mod64_plus, ?swrap32_mod64, ?swrap32_swrap32_plus, ?swrap32_plus_swrap32, ?Z.add_0_r;
repeat (rewrite swrap32_small by lia).

Lemma wrap32_small : forall x, 0 <= x < 2^32 -> bv_wrap 32 x = x.
Proof. intros. unfold bv_wrap. change (bv_modulus 32) with (2^32). apply Z.mod_small. lia. Qed.
Lemma shiftr_byte_range : forall x k, 0 <= x < 256 -> 0 <= k -> 0 <= Z.shiftr x k < 256.
Proof.
intros x k Hx Hk. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with x; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma bit_at_code : forall (bs : list byte) (data : list Z) c bp,
data = map bv_unsigned bs -> 0 <= c -> (Z.to_nat c < length bs)%nat -> 0 <= bp < 8 ->
Z.land (Z.shiftr (bv_unsigned (nth (Z.to_nat c) bs (Z_to_bv 8 0))) (7 - bp)) 1 = bit_at data (c * 8 + bp).
Proof.
intros bs data c bp -> Hc Hlt Hbp. unfold bit_at.
replace ((c * 8 + bp) / 8) with c by lia. replace ((c * 8 + bp) mod 8) with bp by lia.
rewrite znth_map_unsigned by assumption. reflexivity.
Qed.

Section Rep.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition BITS_SIZEOF : Z := 48.

Definition BITS_BUF_MAX : Z := 2^24.

Definition bits_cells (D : Z) b (rj : list byte) : list cell :=
[C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sb_nbBits b)); C4 (Z_to_bv 64 (sb_charPtr b)); C4 (Z_to_bv 64 (sb_bitPtr b));
C4 (Z_to_bv 64 (sb_owner b)); C4 (Z_to_bv 64 (sb_overflow b)); C4 (Z_to_bv 64 (sb_buf_size b)); CB 16 rj].

#[using="Type"] Lemma bits_cells_size : forall D b rj, length rj = 16%nat -> cells_size (bits_cells D b rj) = 48%nat.
Proof. intros. reflexivity. Qed.

Definition bits_side (A D : Z) b : Prop :=
A mod 8 = 0 /\ 0 < A /\ 0 < D /\ sb_buf_size b < BITS_BUF_MAX /\ 0 <= sb_owner b <= 1 /\
(D + sb_buf_size b <= A \/ A + BITS_SIZEOF <= D).

Definition bits_rep (segs : list Segment) (m : mem) (A D : Z) b : Prop :=
(exists rj, length rj = 16%nat /\ rw_cells segs m A (bits_cells D b rj))
/\ (exists bs, u8arr segs m D bs /\ sb_data b = map bv_unsigned bs)
/\ bits_side A D b.

#[using="Type"] Lemma bits_ints : forall A D b, bits_ok b -> bits_side A D b ->
int31 (sb_nbBits b) /\ int31 (sb_charPtr b) /\ int31 (sb_bitPtr b) /\ int31 (sb_owner b) /\
int31 (sb_overflow b) /\ int31 (sb_buf_size b) /\
0 <= sb_charPtr b <= sb_buf_size b /\ 0 <= sb_bitPtr b < 8 /\ bits_pos b <= sb_nbBits b /\
sb_nbBits b <= sb_buf_size b * 8 /\ sb_buf_size b < BITS_BUF_MAX /\ 1 <= sb_buf_size b /\
(sb_overflow b = 0 \/ sb_overflow b = 1).
Proof.
intros A D b OK SD. unfold bits_ok, bits_pos in OK. unfold bits_side, BITS_BUF_MAX in SD. unfold int31, bits_pos, BITS_BUF_MAX.
repeat split; try lia.
Qed.

#[using="Type"] Lemma bits_rep_frame : forall segs m m' A D b W,
bits_rep segs m A D b -> bits_ok b ->
munch W m m' -> wmono segs m m' ->
disjoint_from W A BITS_SIZEOF ->
disjoint_from W D (sb_buf_size b) ->
bits_rep segs m' A D b.
Proof.
intros segs m m' A D b W (S1 & S2 & S3) OK MU WM WA WD.
destruct S1 as (rj & Lrj & OBJ). destruct S2 as (bs & ARR & Hbs).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ unfold bits_ok in OK. rewrite Hbs, zlength_map_unsigned in OK. lia. }
split; [|split; [|exact S3]].
- exists rj. split; [exact Lrj|].
eapply rw_cells_transport; [exact OBJ| exact MU| exact WM|].
rewrite bits_cells_size by exact Lrj. exact WA.
- exists bs. split; [|exact Hbs].
eapply u8arr_transport; [exact ARR| exact MU| exact WM|]. rewrite Lbs. exact WD.
Qed.

End Rep.

Fixpoint in_ivs (X : list (Z * Z)) (a : Z) : Prop :=
match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ in_ivs X' a end.

Definition pres_except (segs : list Segment) (client : Z -> Prop) (X : list (Z * Z)) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> client a -> ~ in_ivs X a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Lemma pres_except_refl : forall segs client X m, pres_except segs client X m m.
Proof. intros segs client X m a _ _ _. auto. Qed.

Lemma pres_except_trans : forall segs client X m1 m2 m3,
pres_except segs client X m1 m2 -> pres_except segs client X m2 m3 -> pres_except segs client X m1 m3.
Proof.
intros segs client X m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
split; [congruence| auto].
Qed.

Lemma pres_except_weaken : forall segs (client client' : Z -> Prop) X X' m m',
pres_except segs client X m m' -> (forall a, client' a -> client a) -> (forall a, in_ivs X a -> in_ivs X' a) ->
pres_except segs client' X' m m'.
Proof. intros segs client client' X X' m m' H HC HX a Ha Hc Hx. apply H; auto. Qed.

Lemma pres_except_of_munch : forall segs client X W m m',
munch W m m' -> wmono segs m m' ->
(forall a, 0 <= a < 2^64 -> client a -> ~ in_ivs X a -> outside W a) ->
pres_except segs client X m m'.
Proof.
intros segs client X W m m' MU WM OUT a Ha Hc Hx. split.
- apply MU. rewrite wa_unsigned by lia. exact (OUT a Ha Hc Hx).
- apply WM.
Qed.

Lemma in_ivs_app : forall X Y a, in_ivs (X ++ Y) a <-> in_ivs X a \/ in_ivs Y a.
Proof. induction X as [|iv X IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma pres_except_bytes_at : forall segs client X m m' A bs,
pres_except segs client X m m' -> bytes_at segs m A bs ->
(forall a, A <= a < A + Z.of_nat (length bs) -> client a /\ ~ in_ivs X a) ->
bytes_at segs m' A bs.
Proof.
intros segs client X m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HR (A + Z.of_nat i) ltac:(lia)) as [Hc Hx].
destruct (HP (A + Z.of_nat i) ltac:(lia) Hc Hx) as [E _]. rewrite E. reflexivity.
Qed.

Lemma pres_except_wr_at : forall segs client X m m' A n,
pres_except segs client X m m' -> wr_at segs m A n ->
(forall a, A <= a < A + n -> client a /\ ~ in_ivs X a) -> wr_at segs m' A n.
Proof.
intros segs client X m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HR (A + i) ltac:(lia)) as [Hc Hx].
destruct (HP (A + i) ltac:(lia) Hc Hx) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma pres_except_rw_cells : forall segs client X m m' A cs,
pres_except segs client X m m' -> rw_cells segs m A cs ->
(forall a, A <= a < A + Z.of_nat (cells_size cs) -> client a /\ ~ in_ivs X a) ->
rw_cells segs m' A cs.
Proof.
intros segs client X m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply pres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply pres_except_wr_at; eauto.
Qed.

Lemma pres_except_u8arr : forall segs client X m m' A xs,
pres_except segs client X m m' -> u8arr segs m A xs ->
(forall a, A <= a < A + Z.of_nat (length xs) -> client a /\ ~ in_ivs X a) ->
u8arr segs m' A xs.
Proof.
intros segs client X m m' A xs HP [HB HW] HR. split.
- eapply pres_except_bytes_at; eauto.
- eapply pres_except_wr_at; eauto.
Qed.

Lemma pres_except_stk : forall segs client X m m' lo hi,
pres_except segs client X m m' -> stk segs m lo hi ->
(forall a, lo <= a < hi -> client a /\ ~ in_ivs X a) -> stk segs m' lo hi.
Proof.
intros segs client X m m' lo hi HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros a Ha. destruct (HR a Ha) as [Hc Hx]. destruct (HP a ltac:(lia) Hc Hx) as [E W]. destruct (HW a Ha) as [W0 [b0 Hb]].
split; [apply W, W0|]. exists b0. unfold mrd in *. rewrite E. exact Hb.
Qed.
