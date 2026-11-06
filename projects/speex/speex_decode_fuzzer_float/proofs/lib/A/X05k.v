(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1ch X1cg X1dk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_unpack_unsigned : Z := 0x981f0.
Definition A_unpack_loop : Z := 0x9831c.
Definition A_unpack_exit : Z := 0x98400.

Section F.
Context {ptr : Type}.

Definition unpack_unsigned_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A D usp lo : Z) (b : bits_st ptr) (n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -48, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ a0 = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b n))
/\ bits_rep bsegs m' A D (snd (speex_bits_unpack_unsigned b n)).

Variables (A D usp lo : Z) (b : bits_st ptr) (n : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.
Hypothesis REP : bits_rep bsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis Hn : 0 <= n <= 24.

Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis OBD : aobj bsegs m D (sb_buf_size b).
Hypothesis OFA : A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A.
Hypothesis LO : lo <= usp - 48.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.

Local Notation POST := (unpack_unsigned_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A D usp lo b n m).
Local Notation W := [(A, A + 48); (usp + -48, usp)].

Lemma unpack_fin : forall rj bs m1 (b1 : bits_st ptr) (v : Z) (j0 : list byte) x0 x1 x2 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 z0 z1 z2 z3 zra,
length rj = 16%nat -> sb_data b = map bv_unsigned bs -> u8arr bsegs m1 D bs ->
(v, b1) = speex_bits_unpack_unsigned b n ->
rw_cells bsegs m1 A (bits_cells D b1 rj) -> munch W m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -48) -> rw_cells bsegs m1 (usp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt bsegs POST
(MS (mkR zra (Z_to_bv 64 (usp + -48)) gp tp y0 y1 y2 z0 z1 x0 x1 x2 (Z_to_bv 64 v) x4 x5 x6 x7 z2 z3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F (Z_to_bv 64 A_unpack_exit) fc None m1 (seg_rom bsegs)).

Proof.
intros rj bs m1 b1 v j0 x0 x1 x2 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 z0 z1 z2 z3 zra Lrj Hbs ARR E OBJ1 MU1 WM1 MI1 ST1 FR.
pose proof REP as (_ & _ & SIDE). pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP). unfold BITS_SIZEOF in SEP.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (speex_bits_unpack_unsigned_ok b n v b1 OK ltac:(lia) (eq_sym E)) as (_ & _ & Hd & _ & Hbuf & _ & Hown & _).
pose proof ST1 as (STa & STb & _).
unfold A_unpack_exit.
do 7 astep. release_frame FR ST1 usp. astep.
unfold unpack_unsigned_post, BITS_SIZEOF. finish.
- rewrite <- E. reflexivity.
- rewrite <- E. cbn [snd].
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
split.
+ exists bs. split; [exact ARR| rewrite Hd; exact Hbs].
+ unfold bits_side in *. rewrite Hbuf, Hown. tauto.
Qed.

Lemma unpack_loop : forall (k : nat) (kz : Z) rj bs (c bp d : Z) (j0 : list byte) (zra y4 z1 z2 z3 : word) m1,
kz = Z.of_nat k -> length rj = 16%nat -> sb_data b = map bv_unsigned bs -> u8arr bsegs m1 D bs ->
sb_overflow b = 0 -> bits_pos b + n <= sb_nbBits b ->
(0 < k)%nat -> Z.of_nat k <= n -> c * 8 + bp + Z.of_nat k = bits_pos b + n -> 0 <= bp < 8 -> 0 <= c ->
0 <= d < 2 ^ (n - Z.of_nat k) ->
getbits_acc (sb_data b) (c * 8 + bp) k d = getbits (sb_data b) (bits_pos b) n ->
rw_cells bsegs m1 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sb_nbBits b)); C4 (Z_to_bv 64 c); C4 (Z_to_bv 64 bp);
C4 (Z_to_bv 64 (sb_owner b)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (sb_buf_size b)); CB 16 rj] ->
munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -48) -> rw_cells bsegs m1 (usp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt bsegs POST
(MS (mkR zra (Z_to_bv 64 (usp + -48)) gp tp (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 7) (Z_to_bv 64 c) z1
(Z_to_bv 64 (A + 12)) (Z_to_bv 64 kz) (Z_to_bv 64 (A + 16)) (Z_to_bv 64 d) y4 (Z_to_bv 64 SHB)
(Z_to_bv 64 (Z.shiftr (A + 12) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (A + 16) 3 + SHB))
z2 z3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (Z.land (A + 16) 7 + 3)) (Z_to_bv 64 31) (Z_to_bv 64 8) (Z_to_bv 64 (Z.land (A + 12) 7 + 3)))
F (Z_to_bv 64 A_unpack_loop) fc None m1 (seg_rom bsegs)).

Proof.
induction k as [|k IH]; intros kz rj bs c bp d j0 zra y4 z1 z2 z3 m1 Hkz Lrj Hbs ARR OV0 POSN Hk Hkn Hpos Hbp Hc Hd Hacc OBJ MU OF WM MI ST1 FR; [lia|]. subst kz.
pose proof REP as (_ & _ & SIDE). pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
unfold bits_pos in *. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof ST1 as (STa & STb & _).
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

ato 0x98324. replace (D + c <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
ato 0x98338. rewrite (ub_ptr_guard_nonneg D c) by lia.
ato 0x9833c. astep. sh_if.

ato 0x9834c. astep. chk_merge OBD 1.
ato 0x98360. rewrite sx32_small by (unfold int31; lia).
ato 0x98368. rewrite (swrap32_small (7 - bp)) by lia. astep. sh_if.
ato 0x98370. rewrite Z.add_0_r, (swrap32_small (7 - bp)) by lia. astep. sh_if.
ato 0x98378. nswrap. astep. sh_if.
Ltac tailB d bp :=
ato 0x983b4; nswrap; astep; sh_if;
ato 0x983cc;
rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2; rewrite (swrap32_small (d * 2)) by lia;
rewrite wrap32_small by lia; rewrite (Z.mod_small (7 - bp) 32) by lia; rewrite swrap32_small by lia; rewrite !Z.mod_small by lia.
ato 0x98388. astep. if_cases K; zify_cond K.
-
tailB d bp.
rewrite BIT, Z.lor_comm, lor_double_bit by (apply bit_at_range).
astep. if_cases K2; zify_cond K2.
+ apply (IH _ rj bs c (bp + 1) (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0); try assumption; try lia.
replace (c * 8 + (bp + 1)) with (c * 8 + bp + 1) by lia. exact ACC'.
+ astep.
lazymatch type of OBJ with rw_cells _ _ _ ?cs =>
replace cs with (bits_cells D (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) rj) in OBJ
by (unfold bits_cells, set_pos, bits_pos; cbn; rewrite OV0; repeat first [reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => lia | nat => lia end | |- _ => lia end | progress f_equal | lia]) end.
eapply (unpack_fin rj bs _ (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0);
[ exact Lrj | exact Hbs | exact ARR | | exact OBJ | exact MU | exact WM | exact MI | exact ST1 | exact FR ].
assert (k = 0%nat) as -> by lia. cbn [getbits_acc] in ACC'. rewrite ACC'.
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite OV0. cbn [Z.eqb negb orb]. reflexivity.
-
ato 0x9839c. nswrap. astep. sh_if.
ato 0x983b0.
tailB d bp.
rewrite BIT, Z.lor_comm, lor_double_bit by (apply bit_at_range).
astep. if_cases K2; zify_cond K2.
+ apply (IH _ rj bs (c + 1) 0 (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0); try assumption; try lia.
replace ((c + 1) * 8 + 0) with (c * 8 + bp + 1) by lia. exact ACC'.
+ astep.
lazymatch type of OBJ with rw_cells _ _ _ ?cs =>
replace cs with (bits_cells D (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) rj) in OBJ
by (unfold bits_cells, set_pos, bits_pos; cbn; rewrite OV0; repeat first [reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => lia | nat => lia end | |- _ => lia end | progress f_equal | lia]) end.
eapply (unpack_fin rj bs _ (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0);
[ exact Lrj | exact Hbs | exact ARR | | exact OBJ | exact MU | exact WM | exact MI | exact ST1 | exact FR ].
assert (k = 0%nat) as -> by lia. cbn [getbits_acc] in ACC'. rewrite ACC'.
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite OV0. cbn [Z.eqb negb orb]. reflexivity.
Qed.

Lemma speex_bits_unpack_unsigned_walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
stk bsegs m lo usp -> client_constsB m -> mem_inv bsegs m ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_unpack_unsigned) fc None m (seg_rom bsegs)).

Proof.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST (G1 & G2 & _) MI.
unfold A_unpack_unsigned, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
unfold bits_cells in OBJ.
pose proof LOS as LOS'. pose proof OFA as OFA'. unfold SH_LO, SH_HI in LOS', OFA'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 48%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x98208. astep. sh_if.
ato 0x98214. astep. sh_if.
ato 0x9823c. rewrite zx32_small by lia.
assert (CP28 : Z.shiftr (sb_charPtr b) 28 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
ato 0x98240. astep. sh_if.
ato 0x9825c. rewrite sx32_small by (unfold int31; lia).
ato 0x98268. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !(swrap32_small (sb_charPtr b * 8)) by lia. rewrite !Z.mod_small by lia. rewrite swrap32_small by lia.
astep. sh_if.
ato 0x98278. rewrite Z.add_0_r. rewrite !(swrap32_small (sb_charPtr b * 8 + sb_bitPtr b)) by lia.
rewrite !Z.mod_small by lia. rewrite swrap32_small by lia.
astep. sh_if.
ato 0x98294. rewrite sx32_small by (unfold int31; lia).
ato 0x9829c. rewrite swrap32_small by lia.
astep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
ato 0x982cc. rewrite sx32_small by (unfold int31; lia).
astep. astep. if_cases K2; zify_cond K2.
+
eapply (unpack_fin rj bs _ (set_overflow b) 0);
[ exact Lrj | exact Hbs | exact ARR | | unfold bits_cells, set_overflow; cbn; replace (sb_overflow b) with 1 in OBJ by lia; exact OBJ
| exact MU | exact WM | exact MI | exact ST | exact FR ].
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
+ astep. if_cases K3; zify_cond K3.
*
eapply (unpack_fin rj bs _ (set_pos b (bits_pos b + n)) 0);
[ exact Lrj | exact Hbs | exact ARR | | | exact MU | exact WM | exact MI | exact ST | exact FR ].
-- unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite K2. cbn [orb negb Z.eqb]. replace n with 0 by lia. unfold getbits. cbn [Z.to_nat getbits_acc]. reflexivity.
-- unfold bits_cells, set_pos, bits_pos; cbn. replace n with 0 by lia.
replace ((sb_charPtr b * 8 + sb_bitPtr b + 0) / 8) with (sb_charPtr b) by lia.
replace ((sb_charPtr b * 8 + sb_bitPtr b + 0) mod 8) with (sb_bitPtr b) by lia. exact OBJ.
*
ato 0x98300. rewrite sx32_small by (unfold int31; lia).
ato 0x9831c. replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
rewrite K2 in OBJ.
apply (unpack_loop (Z.to_nat n) n rj bs (sb_charPtr b) (sb_bitPtr b) 0 (firstn 8 junk));
try assumption; try (unfold bits_pos; lia).
unfold getbits, bits_pos. reflexivity.
-
ato 0x982cc. rewrite sx32_small by (unfold int31; lia). ato 0x98400.
eapply (unpack_fin rj bs _ (set_overflow b) 0);
[ exact Lrj | exact Hbs | exact ARR | | unfold bits_cells, set_overflow; cbn; exact OBJ | exact MU | exact WM | exact MI | exact ST | exact FR ].
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [|lia].
cbn [orb]. reflexivity.
Qed.

End F.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_unpack_unsigned : Z := 0x97dc0.
Definition A_unpack_loop : Z := 0x97ebc.
Definition A_unpack_exit : Z := 0x97f50.

Section F.
Context {ptr : Type}.

Definition unpack_unsigned_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A D usp lo : Z) (b : bits_st ptr) (n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -32, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ a0 = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b n))
/\ bits_rep asegs m' A D (snd (speex_bits_unpack_unsigned b n)).

Variables (A D usp lo : Z) (b : bits_st ptr) (n : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.
Hypothesis REP : bits_rep asegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis Hn : 0 <= n <= 24.

Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBD : aobj asegs m D (sb_buf_size b).
Hypothesis OFA : A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A.
Hypothesis LO : lo <= usp - 32.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.

Local Notation POST := (unpack_unsigned_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A D usp lo b n m).
Local Notation W := [(A, A + 48); (usp + -32, usp)].

Lemma unpack_fin : forall rj bs m1 (b1 : bits_st ptr) (v : Z) (j0 : list byte) x0 x1 x2 x3 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 z0 z1 zra,
length rj = 16%nat -> sb_data b = map bv_unsigned bs -> u8arr asegs m1 D bs ->
(v, b1) = speex_bits_unpack_unsigned b n ->
rw_cells asegs m1 A (bits_cells D b1 rj) -> munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -32) -> rw_cells asegs m1 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra] ->
evt asegs POST
(MS (mkR zra (Z_to_bv 64 (usp + -32)) gp tp y0 y1 y2 z0 z1 x0 x1 x2 x3 (Z_to_bv 64 v) x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F (Z_to_bv 64 A_unpack_exit) fc None m1 (seg_rom asegs)).
Proof.
intros rj bs m1 b1 v j0 x0 x1 x2 x3 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 z0 z1 zra Lrj Hbs ARR E OBJ1 MU1 WM1 MI1 ST1 FR.
pose proof REP as (_ & _ & SIDE). pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP). unfold BITS_SIZEOF in SEP.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (speex_bits_unpack_unsigned_ok b n v b1 OK ltac:(lia) (eq_sym E)) as (_ & _ & Hd & _ & Hbuf & _ & Hown & _).
pose proof ST1 as (STa & STb & _).
unfold A_unpack_exit.
do 5 astep. release_frame FR ST1 usp. astep.
unfold unpack_unsigned_post, BITS_SIZEOF. finish.
- rewrite <- E. reflexivity.
- rewrite <- E. cbn [snd].
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
split.
+ exists bs. split; [exact ARR| rewrite Hd; exact Hbs].
+ unfold bits_side in *. rewrite Hbuf, Hown. tauto.
Qed.

Lemma unpack_loop : forall (k : nat) (kz : Z) rj bs (c bp d : Z) (j0 : list byte) (zra y3 z0 z1 : word) m1,
kz = Z.of_nat k -> length rj = 16%nat -> sb_data b = map bv_unsigned bs -> u8arr asegs m1 D bs ->
sb_overflow b = 0 -> bits_pos b + n <= sb_nbBits b ->
(0 < k)%nat -> Z.of_nat k <= n -> c * 8 + bp + Z.of_nat k = bits_pos b + n -> 0 <= bp < 8 -> 0 <= c ->
0 <= d < 2 ^ (n - Z.of_nat k) ->
getbits_acc (sb_data b) (c * 8 + bp) k d = getbits (sb_data b) (bits_pos b) n ->
rw_cells asegs m1 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sb_nbBits b)); C4 (Z_to_bv 64 c); C4 (Z_to_bv 64 bp);
C4 (Z_to_bv 64 (sb_owner b)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (sb_buf_size b)); CB 16 rj] ->
munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -32) -> rw_cells asegs m1 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra] ->
evt asegs POST
(MS (mkR zra (Z_to_bv 64 (usp + -32)) gp tp (Z_to_bv 64 D) (Z_to_bv 64 c) (Z_to_bv 64 7) z0 z1
(Z_to_bv 64 (A + 12)) (Z_to_bv 64 kz) (Z_to_bv 64 (A + 16)) y3 (Z_to_bv 64 d) (Z_to_bv 64 SHB)
(Z_to_bv 64 (Z.shiftr (A + 12) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (A + 16) 3 + SHB))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (Z.land (A + 16) 7 + 3)) (Z_to_bv 64 8) (Z_to_bv 64 bp) (Z_to_bv 64 (Z.land (A + 12) 7 + 3)))
F (Z_to_bv 64 A_unpack_loop) fc None m1 (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros kz rj bs c bp d j0 zra y3 z0 z1 m1 Hkz Lrj Hbs ARR OV0 POSN Hk Hkn Hpos Hbp Hc Hd Hacc OBJ MU OF WM MI ST1 FR; [lia|]. subst kz.
pose proof REP as (_ & _ & SIDE). pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
unfold bits_pos in *. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof ST1 as (STa & STb & _).
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

do 5 astep. chk_merge OBD 1.

ato 0x97ee0. nswrap. astep. astep.
Ltac tail :=
astep; rewrite Z.shiftl_mul_pow2, swrap32_small by lia; change (2^1) with 2;
astep; nswrap;
astep; rewrite ?wrap32_small by lia; repeat (rewrite Z.mod_small by lia); nswrap; repeat (rewrite Z.mod_small by lia);
astep; astep; nswrap; astep; astep.
if_cases K; zify_cond K.
-
tail.
rewrite BIT, Z.lor_comm, lor_double_bit by (apply bit_at_range).
astep. if_cases K2; zify_cond K2.
+ apply (IH _ rj bs c (bp + 1) (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0); try assumption; try lia.
replace (c * 8 + (bp + 1)) with (c * 8 + bp + 1) by lia. exact ACC'.
+ astep.
lazymatch type of OBJ with rw_cells _ _ _ ?cs =>
replace cs with (bits_cells D (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) rj) in OBJ
by (unfold bits_cells, set_pos, bits_pos; cbn; rewrite OV0; repeat first [reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => lia | nat => lia end | |- _ => lia end | progress f_equal | lia]) end.
eapply (unpack_fin rj bs _ (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0);
[ exact Lrj | exact Hbs | exact ARR | | exact OBJ | exact MU | exact WM | exact MI | exact ST1 | exact FR ].
assert (k = 0%nat) as -> by lia. cbn [getbits_acc] in ACC'. rewrite ACC'.
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite OV0. cbn [Z.eqb negb orb]. reflexivity.
-
ato 0x97f04. nswrap. astep.
tail.
rewrite BIT, Z.lor_comm, lor_double_bit by (apply bit_at_range).
astep. if_cases K2; zify_cond K2.
+ apply (IH _ rj bs (c + 1) 0 (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0); try assumption; try lia.
replace ((c + 1) * 8 + 0) with (c * 8 + bp + 1) by lia. exact ACC'.
+ astep.
lazymatch type of OBJ with rw_cells _ _ _ ?cs =>
replace cs with (bits_cells D (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) rj) in OBJ
by (unfold bits_cells, set_pos, bits_pos; cbn; rewrite OV0; repeat first [reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => lia | nat => lia end | |- _ => lia end | progress f_equal | lia]) end.
eapply (unpack_fin rj bs _ (set_pos b (sb_charPtr b * 8 + sb_bitPtr b + n)) (d * 2 + bit_at (sb_data b) (c * 8 + bp)) j0);
[ exact Lrj | exact Hbs | exact ARR | | exact OBJ | exact MU | exact WM | exact MI | exact ST1 | exact FR ].
assert (k = 0%nat) as -> by lia. cbn [getbits_acc] in ACC'. rewrite ACC'.
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite OV0. cbn [Z.eqb negb orb]. reflexivity.
Qed.

Lemma speex_bits_unpack_unsigned_walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
stk asegs m lo usp -> client_consts m -> mem_inv asegs m ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_unpack_unsigned) fc None m (seg_rom asegs)).
Proof.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST (G1 & G2 & _) MI.
unfold A_unpack_unsigned, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
unfold bits_cells in OBJ.
pose proof LOS as LOS'. pose proof OFA as OFA'. unfold SH_LO, SH_HI in LOS', OFA'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x97e08. rewrite sx32_small by (unfold int31; lia).
ato 0x97e20. rewrite sx32_small by (unfold int31; lia).
ato 0x97e28. rewrite sx32_small by (unfold int31; lia).
astep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
astep. astep. nswrap. astep. astep.
if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
ato 0x97e68. rewrite sx32_small by (unfold int31; lia).
astep. astep. if_cases K2; zify_cond K2.
+
eapply (unpack_fin rj bs _ (set_overflow b) 0);
[ exact Lrj | exact Hbs | exact ARR | | unfold bits_cells, set_overflow; cbn; replace (sb_overflow b) with 1 in OBJ by lia; exact OBJ
| exact MU | exact WM | exact MI | exact ST | exact FR ].
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
+ astep. if_cases K3; zify_cond K3.
*
eapply (unpack_fin rj bs _ (set_pos b (bits_pos b + n)) 0);
[ exact Lrj | exact Hbs | exact ARR | | | exact MU | exact WM | exact MI | exact ST | exact FR ].
-- unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
rewrite K2. cbn [orb negb Z.eqb]. replace n with 0 by lia. unfold getbits. cbn [Z.to_nat getbits_acc]. reflexivity.
-- unfold bits_cells, set_pos, bits_pos; cbn. replace n with 0 by lia.
replace ((sb_charPtr b * 8 + sb_bitPtr b + 0) / 8) with (sb_charPtr b) by lia.
replace ((sb_charPtr b * 8 + sb_bitPtr b + 0) mod 8) with (sb_bitPtr b) by lia. exact OBJ.
*
ato 0x97e9c. rewrite sx32_small by (unfold int31; lia).
ato 0x97eac. rewrite sx32_small by (unfold int31; lia).
ato 0x97ebc.
rewrite K2 in OBJ.
apply (unpack_loop (Z.to_nat n) n rj bs (sb_charPtr b) (sb_bitPtr b) 0 (firstn 8 junk));
try assumption; try (unfold bits_pos; lia).
unfold getbits, bits_pos. reflexivity.
-
ato 0x97e68. astep. astep.
eapply (unpack_fin rj bs _ (set_overflow b) 0);
[ exact Lrj | exact Hbs | exact ARR | | unfold bits_cells, set_overflow; cbn; exact OBJ | exact MU | exact WM | exact MI | exact ST | exact FR ].
unfold speex_bits_unpack_unsigned, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [|lia].
cbn [orb]. reflexivity.
Qed.

End F.
