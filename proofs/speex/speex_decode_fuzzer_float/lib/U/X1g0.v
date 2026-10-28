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

Definition A_speex_bits_advance : Z := 0x1ce10.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.

Definition speex_bits_advance_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(a0 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D : Z) (b : bits_st ptr) (n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3 a4 a5 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + BITS_SIZEOF)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ bits_rep rsegs m' A D (speex_bits_advance b n).

Variables (A D : Z) (b : bits_st ptr) (n : Z).
Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; lia | clear K].

#[using="Type"] Lemma speex_bits_advance_spec :
bits_rep rsegs m A D b -> bits_ok b -> mem_inv rsegs m ->
- 2^20 <= n <= 2^20 ->
evt rsegs (speex_bits_advance_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 A) a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D b n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_advance) fc None m (seg_rom rsegs)).
Proof.
intros REP OK MI Hn. unfold A_speex_bits_advance.
pose proof REP as ((rj & Lrj & OBJ) & DAT & SIDE).
pose proof (bits_ints A D b OK SIDE) as sfP_; first [ sf_destruct 13%nat sfP_ as In Ic Ib Io Iv Is Rc Rb Rp Rn Rs R1 Rov | sf_fb; destruct sfP_ as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov) ].
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos _ _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & _ & _ & SEP) ].
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
unfold bits_cells in OBJ.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
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

assert (FIN : forall m1 (b1 : bits_st ptr) x1 x2 x3 x4 x5,
b1 = speex_bits_advance b n ->
rw_cells rsegs m1 A (bits_cells D b1 rj) -> munch [(A, A + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
evt rsegs (speex_bits_advance_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 A) a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D b n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) x1 x2 x3 x4 x5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs))).
{ intros m1 b1 x1 x2 x3 x4 x5 -> OBJ1 MU1 WM1 MI1.
pose proof (speex_bits_advance_ok b n OK) as AOK.
unfold speex_bits_advance_post. finish.
destruct DAT as (bs & ARR & Hbs).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
split.
- exists bs. split.
+ eapply u8arr_transport; [exact ARR| exact MU1| exact WM1|]. cbn. unfold BITS_SIZEOF in SEP. lia.
+ unfold speex_bits_advance, set_overflow, set_pos. destruct (_ || _); cbn; exact Hbs.
- unfold bits_side in *. unfold speex_bits_advance, set_overflow, set_pos. destruct (_ || _); cbn; tauto. }
zstep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
zstep. zstep. zstep.
eapply (FIN _ (set_overflow b)); [| unfold bits_cells, set_overflow; cbn; exact OBJ| exact MU| exact WM| exact MI].
unfold speex_bits_advance, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [|lia].
cbn [orb]. reflexivity.
- zstep. rewrite sx32_small by (unfold int31; lia).
zstep. if_cases K2; zify_cond K2.
+
zstep. zstep. nswrap.
zstep. ntk.
zstep. rewrite swrap32_mod64, (swrap32_small (sb_bitPtr b + n)), Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite (swrap32_small ((sb_bitPtr b + n) / 8)) by lia.
zstep. rewrite land7_mod64.
zstep. zstep. zstep. zstep.
eapply (FIN _ (set_pos b (bits_pos b + n))); [| | exact MU| exact WM| exact MI].
* unfold speex_bits_advance. destruct (Z.ltb_spec (sb_nbBits b) (bits_pos b + n)); [unfold bits_pos in *; lia|].
rewrite K2. cbn [orb negb Z.eqb]. reflexivity.
* unfold set_pos, bits_cells; cbn.
eapply rw_cells_samebytes; [exact OBJ| cbn; tauto| | reflexivity].
pose proof (advance_C_arith (sb_charPtr b) (sb_bitPtr b) n) as [E1 E2]. unfold bits_pos.
replace ((sb_bitPtr b + n) / 8 + sb_charPtr b) with ((sb_charPtr b * 8 + sb_bitPtr b + n) / 8) by lia.
rewrite E2.
reflexivity.
+
zstep. zstep. zstep.
eapply (FIN _ (set_overflow b)); [| unfold bits_cells, set_overflow; cbn; exact OBJ| exact MU| exact WM| exact MI].
unfold speex_bits_advance, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
Qed.
End F.
