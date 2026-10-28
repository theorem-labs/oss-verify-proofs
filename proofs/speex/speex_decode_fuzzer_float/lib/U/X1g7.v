(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition A_speex_bits_unpack_unsigned : Z := 0x1cc58.
Definition A_unpack_loop : Z := 0x1ccd0.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.

Definition speex_bits_unpack_unsigned_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D : Z) (b : bits_st ptr) (n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + BITS_SIZEOF)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ a0 = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b n))
/\ bits_rep rsegs m' A D (snd (speex_bits_unpack_unsigned b n)).

Variables (A D : Z) (b : bits_st ptr) (n : Z).
Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.
Hypothesis REP : bits_rep rsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis Hn : 0 <= n <= 24.

Lemma lxor_sign_lit : forall x, 0 <= x < 2^64 -> Z.lxor x 9223372036854775808 = (x + 2^63) mod 2^64.
Proof. intros x Hx. change 9223372036854775808 with (2^63). apply zb_lxor_sign. exact Hx. Qed.
Local Notation POST := (speex_bits_unpack_unsigned_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc A D b n m).

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac ntf := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [clear K | exfalso; lia].
Ltac bdec := repeat match goal with
| |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_sign_lit x) by lia
| |- context [?x <? ?y] => first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
| |- context [?x =? ?y] => first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia) | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
end; cbn [Z.b2z];
repeat match goal with |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v end.

#[using="REP OK Hn"] Lemma unpack_fin : forall rj bs m1 (b1 : bits_st ptr) (v : Z) x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5,
length rj = 16%nat -> sb_data b = map bv_unsigned bs -> u8arr rsegs m1 D bs ->
(v, b1) = speex_bits_unpack_unsigned b n ->
rw_cells rsegs m1 A (bits_cells D b1 rj) -> munch [(A, A + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
evt rsegs POST
(MS (mkR ra sp gp tp y0 y1 y2 s0 s1 (Z_to_bv 64 v) x1 x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)).
Proof.
intros rj bs m1 b1 v x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 Lrj Hbs ARR E OBJ1 MU1 WM1 MI1.
pose proof REP as (_ & _ & SIDE). pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos _ _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & _ & _ & SEP) ]. unfold BITS_SIZEOF in SEP.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (speex_bits_unpack_unsigned_ok b n v b1 OK ltac:(lia) (eq_sym E)) as sfP_; first [ sf_destruct 8%nat sfP_ as _ _ Hd _ Hbuf _ Hown _ | sf_fb; destruct sfP_ as (_ & _ & Hd & _ & Hbuf & _ & Hown & _) ].
unfold speex_bits_unpack_unsigned_post. finish.
- rewrite <- E. reflexivity.
- rewrite <- E. cbn [snd].
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
split.
+ exists bs. split; [exact ARR| rewrite Hd; exact Hbs].
+ unfold bits_side in *. rewrite Hbuf, Hown. tauto.
Qed.

#[using="REP OK Hn"] Lemma unpack_loop : forall (k : nat) (kz : Z) rj bs (c bp d : Z) (y2 y3 y4 y5 : word) m1,
kz = Z.of_nat k -> length rj = 16%nat -> sb_data b = map bv_unsigned bs -> u8arr rsegs m1 D bs ->
sb_overflow b = 0 -> bits_pos b + n <= sb_nbBits b ->
(0 < k)%nat -> Z.of_nat k <= n -> c * 8 + bp + Z.of_nat k = bits_pos b + n -> 0 <= bp < 8 -> 0 <= c ->
0 <= d < 2 ^ (n - Z.of_nat k) ->
getbits_acc (sb_data b) (c * 8 + bp) k d = getbits (sb_data b) (bits_pos b) n ->
rw_cells rsegs m1 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sb_nbBits b)); C4 (Z_to_bv 64 c); C4 (Z_to_bv 64 bp);
C4 (Z_to_bv 64 (sb_owner b)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (sb_buf_size b)); CB 16 rj] ->
munch [(A, A + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
evt rsegs POST
(MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 8) y2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 kz) (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 bp)
(Z_to_bv 64 D) (Z_to_bv 64 7) (Z_to_bv 64 31) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 t6)
F (Z_to_bv 64 A_unpack_loop) fc None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros kz rj bs c bp d y2 y3 y4 y5 m1 Hkz Lrj Hbs ARR OV0 POSN Hk Hkn Hpos Hbp Hc Hd Hacc OBJ MU WM MI; [lia|]. subst kz.
pose proof REP as (_ & _ & SIDE). pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos _ _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & _ & _ & SEP) ].
pose proof (bits_ints A D b OK SIDE) as sfP_; first [ sf_destruct 13%nat sfP_ as In Ic Ib Io Iv Is Rc Rb Rp Rn Rs R1 Rov | sf_fb; destruct sfP_ as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov) ].
unfold bits_pos in *. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
unfold A_unpack_loop.
assert (Hnth : nth_error bs (Z.to_nat c) = Some (nth (Z.to_nat c) bs (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8arr_read _ _ _ _ c _ _ ARR Hnth ltac:(lia) eq_refl) as RD.
pose proof (byte_range (nth (Z.to_nat c) bs (Z_to_bv 8 0))) as BR.
pose proof (shiftr_byte_range _ (7 - bp) BR ltac:(lia)) as SR.
pose proof (bit_at_range (sb_data b) (c * 8 + bp)) as BITR.
assert (Hd2 : 0 <= d * 2 + 1 < 2 ^ (n - Z.of_nat k)).
{ rewrite Nat2Z.inj_succ in Hd. replace (n - Z.of_nat k) with (Z.succ (n - Z.succ (Z.of_nat k))) by lia.
rewrite Z.pow_succ_r by lia. lia. }
assert (Hd3 : 2 ^ (n - Z.of_nat k) <= 2 ^ 24) by (apply Z.pow_le_mono_r; lia).
assert (BIT : Z.land (Z.shiftr (bv_unsigned (nth (Z.to_nat c) bs (Z_to_bv 8 0))) (7 - bp)) 1 = bit_at (sb_data b) (c * 8 + bp)).
{ apply (bit_at_code bs); [exact Hbs| lia| lia| lia]. }
assert (ACC' : getbits_acc (sb_data b) (c * 8 + bp + 1) k (d * 2 + bit_at (sb_data b) (c * 8 + bp)) = getbits (sb_data b) (sb_charPtr b * 8 + sb_bitPtr b) n).
{ rewrite <- Hacc. reflexivity. }
zstep. nswrap.
zstep. zstep.
bdec. zstep. ntk.
zstep. zstep. zstep. zstep.
bdec. zstep. ntk.
zstep. ntk.
zstep. zstep. nswrap. zstep. ntk.
zstep. nswrap. zstep. ntk.
zstep. nswrap. zstep. ntk.
zstep. zstep.
Ltac utail kk :=
zstep; nswrap; replace (Z.of_nat (S kk) + -1) with (Z.of_nat kk) by lia;
zstep; ntk;
zstep; rewrite Z.shiftl_mul_pow2, swrap32_small by lia; change (2^1) with 2;
zstep; zstep; rewrite wrap32_small by lia;
zstep; zstep.
Ltac ubit bpv BIT :=
rewrite (Z.mod_small (7 - bpv) 32) by lia; rewrite (swrap32_small (_ ≫ (7 - bpv))) by lia;
rewrite (Z.mod_small (_ ≫ (7 - bpv))) by lia;
rewrite BIT, Z.lor_comm, lor_double_bit by (apply bit_at_range).
zstep. if_cases K; zify_cond K.
-
zstep.
utail k. ubit bp BIT.
zstep. if_cases K2; zify_cond K2.
+
apply (IH _ rj bs c (bp + 1) (d * 2 + bit_at (sb_data b) (c * 8 + bp))); try assumption; try lia.
replace (c * 8 + (bp + 1)) with (c * 8 + bp + 1) by lia. exact ACC'.
+
zstep. zstep.
lazymatch type of OBJ with rw_cells _ _ _ ?cs =>
replace cs with (bits_cells D (set_pos b (bits_pos b + n)) rj) in OBJ
by (unfold bits_cells, set_pos, bits_pos; cbn; rewrite OV0; repeat first [reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => lia | nat => lia end | |- _ => lia end | progress f_equal | lia]) end.
eapply (unpack_fin rj bs _ (set_pos b (bits_pos b + n)) (d * 2 + bit_at (sb_data b) (c * 8 + bp)));
[ exact Lrj | exact Hbs | exact ARR | | exact OBJ | exact MU | exact WM | exact MI ].
assert (k = 0%nat) as -> by lia. cbn [getbits_acc] in ACC'. rewrite ACC'.
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite OV0. cbn [Z.eqb negb orb]. reflexivity.
-
zstep. nswrap. zstep. zstep. ntk.
zstep. zstep. zstep.
utail k. ubit bp BIT.
zstep. if_cases K2; zify_cond K2.
+ apply (IH _ rj bs (c + 1) 0 (d * 2 + bit_at (sb_data b) (c * 8 + bp))); try assumption; try lia.
replace ((c + 1) * 8 + 0) with (c * 8 + bp + 1) by lia. exact ACC'.
+ zstep. zstep.
lazymatch type of OBJ with rw_cells _ _ _ ?cs =>
replace cs with (bits_cells D (set_pos b (bits_pos b + n)) rj) in OBJ
by (unfold bits_cells, set_pos, bits_pos; cbn; rewrite OV0; repeat first [reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => lia | nat => lia end | |- _ => lia end | progress f_equal | lia]) end.
eapply (unpack_fin rj bs _ (set_pos b (bits_pos b + n)) (d * 2 + bit_at (sb_data b) (c * 8 + bp)));
[ exact Lrj | exact Hbs | exact ARR | | exact OBJ | exact MU | exact WM | exact MI ].
assert (k = 0%nat) as -> by lia. cbn [getbits_acc] in ACC'. rewrite ACC'.
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite OV0. cbn [Z.eqb negb orb]. reflexivity.
Qed.

#[using="REP OK Hn"] Lemma speex_bits_unpack_unsigned_spec :
mem_inv rsegs m ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_unpack_unsigned) fc None m (seg_rom rsegs)).
Proof.
intros MI. unfold A_speex_bits_unpack_unsigned.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as sfP_; first [ sf_destruct 13%nat sfP_ as In Ic Ib Io Iv Is Rc Rb Rp Rn Rs R1 Rov | sf_fb; destruct sfP_ as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov) ].
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos _ _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & _ & _ & SEP) ].
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
unfold bits_cells in OBJ.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (munch_refl [(A, A + 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
zstep. ntk.
zstep. rewrite land7_mod8, AL.
zstep. ntk.
zstep. rewrite zx32_small by lia.
zstep. rewrite (Z.shiftr_div_pow2 _ 28), (Z.div_small _ (2^28)) by lia.
zstep. ntk.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite swrap32_small by lia.
zstep. zstep. nswrap.
zstep. ntk.
zstep. nswrap.
zstep. zstep. nswrap.
zstep. ntk.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. nswrap.
zstep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. zstep. if_cases K2; zify_cond K2.
+
zstep. zstep.
eapply (unpack_fin rj bs _ (set_overflow b) 0);
[ exact Lrj | exact Hbs | exact ARR | | unfold bits_cells, set_overflow; cbn; replace (sb_overflow b) with 1 in OBJ by lia; exact OBJ | exact MU | exact WM | exact MI ].
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
+ zstep. if_cases K3; zify_cond K3.
*
zstep. zstep.
eapply (unpack_fin rj bs _ (set_pos b (bits_pos b + n)) 0);
[ exact Lrj | exact Hbs | exact ARR | | | exact MU | exact WM | exact MI ].
-- unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite K2. cbn [orb negb Z.eqb]. replace n with 0 by lia. unfold getbits. cbn [Z.to_nat getbits_acc]. reflexivity.
-- unfold bits_cells, set_pos, bits_pos; cbn. replace n with 0 by lia.
replace ((sb_charPtr b * 8 + sb_bitPtr b + 0) / 8) with (sb_charPtr b) by lia.
replace ((sb_charPtr b * 8 + sb_bitPtr b + 0) mod 8) with (sb_bitPtr b) by lia. exact OBJ.
*
zstep. zstep. zstep. zstep. zstep. zstep. bdec.
rewrite K2 in OBJ.
apply (unpack_loop (Z.to_nat n) n rj bs (sb_charPtr b) (sb_bitPtr b) 0);
try assumption; try (unfold bits_pos; lia).
unfold getbits, bits_pos. reflexivity.
-
zstep. zstep. zstep. rewrite sx32_small by (unfold int31; lia).
zstep. zstep. ntf.
zstep. zstep.
eapply (unpack_fin rj bs _ (set_overflow b) 0);
[ exact Lrj | exact Hbs | exact ARR | | unfold bits_cells, set_overflow; cbn; exact OBJ | exact MU | exact WM | exact MI ].
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [|lia].
cbn [orb]. reflexivity.
Qed.

End F.
