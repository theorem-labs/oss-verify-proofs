(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma f32_snoc1 : forall segs m A done v, rw_cells segs m A (f32 done ++ [C4 v]) -> rw_cells segs m A (f32 (done ++ [v])).
Proof. intros segs m A done v H. rewrite f32_app, f32_cons, f32_nil. exact H. Qed.

Section Seg.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable notify : list Z -> X1qx.M PState unit.
Variable STR_TOP : Z.
Variable X : nbinv ptr.
Hypothesis NH : nb_hyps notify STR_TOP X.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation ISV := (x_isv X). Local Notation lo := (x_lo X).
Local Notation st0 := (x_st0 X). Local Notation b0 := (x_b0 X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X). Local Notation canary := (x_canary X).
Local Notation usp := (bv_unsigned (x_sp X)).

#[using="Type"] Lemma exc_split3 : forall m eb, rw_cells rsegs m (ST + 32) (f32 eb) -> length eb = 500%nat ->
rw_cells rsegs m (ST + 32) (f32 (firstn 334 eb)) /\ rw_cells rsegs m (ST + 1368) (f32 (firstn 160 (skipn 334 eb)))
/\ rw_cells rsegs m (ST + 2008) (f32 (skipn 494 eb))
/\ length (firstn 334 eb) = 334%nat /\ length (firstn 160 (skipn 334 eb)) = 160%nat /\ length (skipn 494 eb) = 6%nat.
Proof.
intros m eb H L.
destruct (f32_split rsegs m _ eb 334 ltac:(lia) H) as [H1 H2].
destruct (f32_split rsegs m _ (skipn 334 eb) 160 ltac:(rewrite length_skipn; lia) H2) as [H3 H4].
rewrite skipn_skipn in H4. cbn [Nat.add] in H4.
replace (ST + 32 + 4 * Z.of_nat 334) with (ST + 1368) in H3, H4 by lia.
replace (ST + 1368 + 4 * Z.of_nat 160) with (ST + 2008) in H4 by lia.
split; [exact H1|]. split; [exact H3|]. split; [exact H4|].
rewrite !length_firstn, !length_skipn. lia.
Qed.
#[using="Type"] Lemma exc_join3 : forall m e1 e2 e3,
rw_cells rsegs m (ST + 32) (f32 e1) -> rw_cells rsegs m (ST + 1368) (f32 e2) -> rw_cells rsegs m (ST + 2008) (f32 e3) ->
length e1 = 334%nat -> length e2 = 160%nat -> length e3 = 6%nat ->
rw_cells rsegs m (ST + 32) (f32 (e1 ++ e2 ++ e3)) /\ length (e1 ++ e2 ++ e3) = 500%nat.
Proof.
intros m e1 e2 e3 H1 H2 H3 L1 L2 L3. split; [| rewrite !length_app; lia].
apply f32_join; [exact H1|]. rewrite L1. replace (ST + 32 + 4 * Z.of_nat 334) with (ST + 1368) by lia.
apply f32_join; [exact H2|]. rewrite L2. replace (ST + 1368 + 4 * Z.of_nat 160) with (ST + 2008) by lia. exact H3.
Qed.

Definition at_N1 (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xs5 xs6 xs7 xs8 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR (Z_to_bv 64 0x20ffc) (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 1013904223) (Z_to_bv 64 8388607) (Z_to_bv 64 (ST + 1368))
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 1664525) (Z_to_bv 64 160) (Z_to_bv 64 ST) xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21038) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m (set_nb_submodeID st0 0) b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v120 fr = Z_to_bv 64 0 /\ j_exc j = ST + 1368
/\ c_a2 k = Z_to_bv 64 1065353216 /\ c_a3 k = Z_to_bv 64 1 /\ c_a4 k = Z_to_bv 64 1
/\ c_a5 k = Z_to_bv 64 (ST + 1368) /\ c_a6 k = Z_to_bv 64 (ST + 1368).

#[using="notify STR_TOP NH"] Lemma nbN1 : forall b ms, at_N X b ms -> evt rsegs (at_N1 b) ms.
Proof.
intros b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m k xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.

pose proof (h_stal _ _ _ NH) as STAL. pose proof (h_sthi _ _ _ NH) as STHI. unfold NBSTATE_SIZEOF in STHI.
pose proof (h_sp16 _ _ _ NH) as SP16.
do 7 zstep. rewrite E48. do 6 zstep.
pose proof (f32_split rsegs _ _ (f_inn fr) 10 ltac:(rewrite Lfinn; lia) FI) as [FI1 FI2]. clear FI.
replace (usp + -416 + 4 * Z.of_nat 10) with (usp + -376) in FI2 by lia.
assert (LFI2 : length (skipn 10 (f_inn fr)) = 30%nat) by (rewrite length_skipn; lia).
call ((h_bwlpc _ _ _ NH) (ST + 2080) (usp + -416) (j_interp_qlpc j) (firstn 10 (f_inn fr)));
[ exact P4 | exact Liq | exact FI1 | rewrite length_firstn; lia
| unfold apart; pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia
| lia | clear - STAL; Z.div_mod_to_equations; lia | lia | clear - SP16; Z.div_mod_to_equations; lia
| reflexivity | reflexivity | reflexivity | exact MI | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI.
match goal with H : rw_cells _ _ (usp + -416) (f32 ?ws), L : length ?ws = 10%nat |- _ => rename H into FI1; rename L into Llpc end.

zstep. rewrite E88. zstep. rewrite JEXC. zstep. zstep. zstep.
first [ pose proof (exc_split3 _ _ P1 Lexc) as sfP_; sf_destruct 6%nat sfP_ as PE1 PE2 PE3 LE1 LE2 LE3 | sf_fb; destruct (exc_split3 _ _ P1 Lexc) as (PE1 & PE2 & PE3 & LE1 & LE2 & LE3) ]. clear P1.
call ((h_rms _ _ _ NH) (ST + 1368) 160 (firstn 160 (skipn 334 (j_excbuf j))));
[ exact PE2 | exact LE2 | lia | lia | clear - STAL; Z.div_mod_to_equations; lia | reflexivity | reflexivity | exact MI | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI.
clear PE2 LE2.
match goal with H : rw_cells _ _ (ST + 1368) (f32 ?ws), L : length ?ws = _ |- _ => rename H into PE2; rename L into LE2; cbn in LE2 end.

step. zstep. zstep. rewrite JEXC. zstep. zstep. step. zstep. zstep. zstep. step. zstep. zstep. step. zstep. zstep.
replace ((ST + 1368) mod 18446744073709551616) with (ST + 1368) by (symmetry; apply Z.mod_small; lia).
replace (0 <? ST + 1368) with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z.land (ST + 1368) 3 <? 1) with true
by (symmetry; apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
cbn [Z.b2z]. change (Z.land 1 1) with 1.

destruct (exc_join3 _ _ _ _ PE1 PE2 PE3 LE1 LE2 LE3) as [P1 Lexc1]. clear PE1 PE2 PE3.
lazymatch type of FI1 with rw_cells _ ?mm _ (f32 ?lpc) =>
assert (FI : rw_cells rsegs mm (usp + -416) (f32 (lpc ++ skipn 10 (f_inn fr))))
by (apply f32_join; [exact FI1 | rewrite Llpc; replace (usp + -416 + 4 * Z.of_nat 10) with (usp + -376) by lia; exact FI2]);
assert (Lfinn2 : length (lpc ++ skipn 10 (f_inn fr)) = 40%nat) by (rewrite length_app, Llpc, LFI2; reflexivity)
end.
clear FI1 FI2.
apply evt_done. close_cut 6.
Qed.
End Seg.
