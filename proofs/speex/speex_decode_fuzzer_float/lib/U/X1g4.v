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

Definition A_speex_bits_peek : Z := 0x1cd68.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.

Definition speex_bits_peek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D : Z) (b : bits_st ptr) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + BITS_SIZEOF)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ a0 = Z_to_bv 64 (fst (speex_bits_peek b))
/\ bits_rep rsegs m' A D (snd (speex_bits_peek b)).

Variables (A D : Z) (b : bits_st ptr).
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac bdec := repeat match goal with
| |- context [?x <? ?y] => first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
| |- context [?x =? ?y] => first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia) | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
end; cbn [Z.b2z Z.lxor].

#[using="Type"] Lemma speex_bits_peek_spec :
bits_rep rsegs m A D b -> bits_ok b -> mem_inv rsegs m ->
evt rsegs (speex_bits_peek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D b m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_peek) fc None m (seg_rom rsegs)).
Proof.
intros REP OK MI. unfold A_speex_bits_peek.
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

assert (FIN : forall m1 (b1 : bits_st ptr) (v : Z) x1 x2 x3 x4,
(v, b1) = speex_bits_peek b ->
rw_cells rsegs m1 A (bits_cells D b1 rj) -> munch [(A, A + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
evt rsegs (speex_bits_peek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D b m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) x1 x2 x3 x4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs))).
{ intros m1 b1 v x1 x2 x3 x4 E OBJ1 MU1 WM1 MI1.
unfold speex_bits_peek_post. finish.
- rewrite <- E. reflexivity.
- rewrite <- E. cbn [snd].
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
assert (Hb1 : b1 = b \/ b1 = set_overflow b).
{ unfold speex_bits_peek in E. destruct (_ || _); injection E as _ <-; auto. }
split.
+ exists bs. split.
* eapply u8arr_transport; [exact ARR| exact MU1| exact WM1|]. cbn. lia.
* destruct Hb1 as [-> | ->]; [exact Hbs| unfold set_overflow; cbn; exact Hbs].
+ unfold bits_side in *. destruct Hb1 as [-> | ->]; [tauto| unfold set_overflow; cbn; tauto]. }
zstep. ntk.
zstep. rewrite land7_mod8, AL.
zstep. ntk.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. rewrite wrap32_small, (Z.shiftr_div_pow2 _ 28), (Z.div_small _ (2^28)), swrap32_small by lia.
zstep. ntk.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite swrap32_small by lia.
zstep. zstep. nswrap.
zstep. ntk.
zstep. nswrap.
zstep. nswrap.
zstep. ntk.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. if_cases K2; zify_cond K2.
+
assert (Hnth : nth_error bs (Z.to_nat (sb_charPtr b)) = Some (nth (Z.to_nat (sb_charPtr b)) bs (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8arr_read _ _ _ _ (sb_charPtr b) _ _ ARR Hnth ltac:(lia) eq_refl) as RD.
pose proof (byte_range (nth (Z.to_nat (sb_charPtr b)) bs (Z_to_bv 8 0))) as BR.
pose proof (shiftr_byte_range _ (7 - sb_bitPtr b) BR ltac:(lia)) as SR.
zstep. zstep.
zstep. ntk.
zstep. zstep. zstep.
bdec. zstep. ntk.
zstep. ntk.
zstep. zstep. zstep. nswrap.
zstep. ntk.
zstep. nswrap. zstep.
zstep. ntk.
zstep. zstep.
rewrite wrap32_small by lia. repeat (rewrite Z.mod_small by lia). nswrap. repeat (rewrite Z.mod_small by lia).
zstep. zstep.
eapply (FIN _ b); [| unfold bits_cells; exact OBJ| exact MU| exact WM| exact MI].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [lia|].
rewrite K2. cbn [orb negb Z.eqb]. f_equal. apply (bit_at_code bs); [exact Hbs| lia| lia| lia].
+
zstep. zstep.
eapply (FIN _ (set_overflow b) 0); [| unfold bits_cells, set_overflow; cbn; replace (sb_overflow b) with 1 in OBJ by lia; exact OBJ| exact MU| exact WM| exact MI].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
-
zstep. zstep. zstep. rewrite sx32_small by (unfold int31; lia).
zstep. ntk.
zstep. zstep.
eapply (FIN _ (set_overflow b) 0); [| unfold bits_cells, set_overflow; cbn; exact OBJ| exact MU| exact WM| exact MI].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [|lia].
cbn [orb]. reflexivity.
Qed.
End F.
