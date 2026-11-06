(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X09e X0bo.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X0z5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Notation mem := (word -> option byte).

Definition A_speex_decode_stereo : Z := 0x98edc.

Definition decode_stereo_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(usp lo D ST : Z) (N : nat) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (ws' sw' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(D, D + 4 * Z.of_nat N); (ST, ST + 24); (usp + -64, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc'
/\ rw_cells bsegs m' D (f32 ws') /\ length ws' = N /\ rw_cells bsegs m' ST (f32 sw') /\ length sw' = 6%nat.

Lemma zext_shr30 fs : 0 <= fs < 2^32 -> Z.shiftr (Z.shiftl fs 32 mod 18446744073709551616) 30 = 4 * fs.
Proof.
intros H. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
replace (fs * 2 ^ 32) with (4 * fs * 2 ^ 30) by lia. apply Z.div_mul. lia.
Qed.
Lemma zext_shr29 fs : 0 <= fs < 2^32 -> Z.shiftr (Z.shiftl fs 32 mod 18446744073709551616) 29 = 8 * fs.
Proof.
intros H. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
replace (fs * 2 ^ 32) with (8 * fs * 2 ^ 29) by lia. apply Z.div_mul. lia.
Qed.

Ltac out_store D idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with XA : u32arr bsegs mc D ?ws, LW : length ?ws = _ |- _ =>
let SOK := fresh "SOK" in
pose proof (u32arr_store_ok bsegs mc D ws idx _ XA ltac:(rewrite LW; lia) ltac:(f_equal; lia)) as SOK;
astep;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
let LW2 := fresh "LW" in let XA2 := fresh "XA" in
assert (LW2 : length (upd ws (Z.to_nat idx) v) = length ws) by (apply upd_length);
rewrite LW in LW2;
pose proof (u32arr_write bsegs mc D ws idx v XA ltac:(rewrite LW; lia)) as XA2;
match goal with |- context [write_to_mem mc ?a (le4 v)] =>
replace (write_to_mem mc a (le4 v)) with (write_to_mem mc (wa (D + 4 * idx)) (le4 v)) by (f_equal; f_equal; lia) end;
clear XA LW; store_done; try clear SOK; rename XA2 into XA; rename LW2 into LW
end end end.

Section S.
Variables (D ST usp lo : Z) (N : nat).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation NZ := (4 * Z.of_nat N).
Hypothesis OBD : aobj bsegs m D NZ.
Hypothesis OBS : aobj bsegs m ST 24.
Hypothesis D4 : D mod 4 = 0.
Hypothesis S4 : ST mod 4 = 0.
Hypothesis NB : Z.of_nat N < 2^28.
Hypothesis LO : lo <= usp - 64.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis DSH : D + NZ <= SH_LO \/ SH_HI <= D.
Hypothesis SSH : ST + 24 <= SH_LO \/ SH_HI <= ST.
Hypothesis DLO : D + NZ <= lo.
Hypothesis SLO : ST + 24 <= lo.
Hypothesis SEP : D + NZ <= ST \/ ST + 24 <= D.
Local Notation POST := (decode_stereo_postA ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo D ST N m).
Local Notation W := [(D, D + NZ); (ST, ST + 24); (usp + -64, usp)].

Lemma stereo_loopB : forall (k : nat) (i : Z) (ws : list word) (q0 q1 q2 q3 q4 q5 : word)
(wt0 wt2 wa3 wt3 wt5 ya1 ys4 ys5 ys6 : word) (G : bvmap 5 word) fc mc,
wt0 = Z_to_bv 64 (8589934592 * i) -> wt2 = Z_to_bv 64 (2 * i + 1) -> wa3 = Z_to_bv 64 (D + 4 * i) -> wt3 = Z_to_bv 64 (D + 4 * i) ->
wt5 = Z_to_bv 64 (i + 1073741824) ->
Z.of_nat k = i -> 2 * i + 2 <= Z.of_nat N -> length ws = N -> 0 < D ->
frm0 fc -> munch W m mc -> offsh W -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -64) -> rw_cells bsegs mc (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
u32arr bsegs mc D ws -> rw_cells bsegs mc ST (f32 [q0; q1; q2; q3; q4; q5]) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp wt0 (Z_to_bv 64 1073741824) wt2 (Z_to_bv 64 (Z.land (ST + 8) 7 + 3)) (Z_to_bv 64 (Z.shiftr (ST + 12) 3 + SHB))
(Z_to_bv 64 D) ya1 (Z_to_bv 64 (ST + 12)) wa3 (Z_to_bv 64 (ST + 8)) (Z_to_bv 64 i) (Z_to_bv 64 SHB) (Z_to_bv 64 1)
(Z_to_bv 64 (Z.land (ST + 12) 7 + 3)) (Z_to_bv 64 18446744065119617024) ys4 ys5 ys6 s7 s8 s9 s10 s11
wt3 (Z_to_bv 64 1) wt5 (Z_to_bv 64 (Z.shiftr (ST + 8) 3 + SHB)))
G (Z_to_bv 64 0x99000) fc None mc (seg_rom bsegs)).
Proof using OBD OBS D4 S4 NB LO LOS SPH DSH SSH DLO SLO SEP.
induction k as [|k IH]; intros i ws q0 q1 q2 q3 q4 q5 wt0 wt2 wa3 wt3 wt5 ya1 ys4 ys5 ys6 G fc mc E0 E2 E3 ET3 E5 Hk HI LW DPOS FRM MU OF WM MI ST0 FR XA XS;
subst wt0 wt2 wa3 wt3 wt5;
pose proof OBD as (OD0 & OD1 & _); pose proof OBS as (OS0 & OS1 & _); unfold APP_TOP in *;
pose proof ST0 as (STa & STb & _);
rewrite !f32_cons, f32_nil in XS; hide_disj.
- assert (E0 : i = 0) by lia. clear Hk. subst i.
bato 0x99024. astep. chk_merge OBD 4.
pose proof (u32arr_read_nth bsegs mc D ws 0 _ XA ltac:(rewrite LW; lia) ltac:(f_equal; lia)) as RD.
bato 0x99030. astep. chk_merge OBS 4. clear RD.
bato 0x9903c. astep. chk_merge OBS 4.
bato 0x9904c. astep. chk_merge OBS 4.
bato 0x99058. astep. chk_merge OBS 4.
bato 0x9908c.
rewrite Z.add_0_l.
bato 0x99098. astep. chk_merge OBD 4.
bato 0x990a8. out_store D (2 * 0).
bato 0x990c8.
astep. chk_merge OBS 4.
bato 0x990cc. replace (4 + D) with (D + 4) by lia.
bato 0x990dc. astep. chk_merge OBD 4.
bato 0x990e4. out_store D (2 * 0 + 1).
bato 0x99100. astep. try sh_if.
bato 0x99184. release_frame FR ST0 usp. astep. astep.
pose proof (f32_of_u32arr bsegs _ D _ XA) as XF.
lazymatch goal with XS : rw_cells _ ?mf ST [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
change (rw_cells bsegs mf ST (f32 [a; b; c; d; e; f])) in XS end.
unfold decode_stereo_postA. finish; first [ exact XF | exact LW | exact XS | reflexivity ].
- assert (I1 : 1 <= i) by lia.
bato 0x99024. astep. chk_merge OBD 4.
pose proof (u32arr_read_nth bsegs mc D ws i _ XA ltac:(rewrite LW; lia) ltac:(f_equal; lia)) as RD.
bato 0x99030. astep. chk_merge OBS 4. clear RD.
bato 0x9903c. astep. chk_merge OBS 4.
bato 0x9904c. astep. chk_merge OBS 4.
bato 0x99058. astep. chk_merge OBS 4.
bato 0x99070.
rewrite signed_small64 by lia.
replace (Z.shiftr (8589934592 * i) 30 + D) with (D + 8 * i) by (rewrite Z.shiftr_div_pow2 by lia; replace (8589934592 * i) with (8 * i * 2^30) by lia; rewrite Z.div_mul by lia; lia).
bato 0x99088.
assert (LAND : Z.land i 1073741824 = 0).
{ rewrite <- (Z.mod_small i (2^30)) by lia. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 30) 1073741824) with 0. apply Z.land_0_r. }
rewrite LAND.
bato 0x99098. astep. chk_merge OBD 4.
bato 0x990a8. out_store D (2 * i).
bato 0x990c8.
astep. chk_merge OBS 4.
bato 0x990cc. replace ((2 * i + 1) * 4 + D) with (D + 8 * i + 4) by lia.
bato 0x990dc. astep. chk_merge OBD 4.
bato 0x990e4. out_store D (2 * i + 1).
bato 0x99100.
astep. sh_if. bnorm.
replace (Z_to_bv 64 (8589934592 * i + 18446744065119617024)) with (Z_to_bv 64 (8589934592 * (i - 1)))
by (apply Z_to_bv_eqm; replace (8589934592 * i + 18446744065119617024) with (8589934592 * (i - 1) + 1 * 18446744073709551616) by lia;
change (2^64) with 18446744073709551616; rewrite Z_mod_plus_full; reflexivity).
lazymatch goal with XS : rw_cells _ ?mf ST [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
change (rw_cells bsegs mf ST (f32 [a; b; c; d; e; f])) in XS end.
eapply (IH (i - 1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try lia.
Qed.

Lemma speex_decode_stereo_walk : forall (fs : Z) (ws : list word) (q0 q1 q2 q3 q4 q5 : word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells bsegs m D (f32 ws) -> length ws = N -> rw_cells bsegs m ST (f32 [q0; q1; q2; q3; q4; q5]) ->
0 <= fs -> 2 * fs <= Z.of_nat N ->
IMG_TOP_B <= D -> IMG_TOP_B <= ST ->
client_constsB m -> stk bsegs m lo usp -> mem_inv bsegs m -> frm0 fc ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 fs) (Z_to_bv 64 ST) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decode_stereo) fc None m (seg_rom bsegs)).
Proof.
intros fs ws q0 q1 q2 q3 q4 q5 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc X LX XS FS0 FS2 DTOP STOP CC ST0 MI FRM.
pose proof CC as (G1 & G2 & _).
unfold A_speex_decode_stereo, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof OBD as (OD0 & OD1 & _). pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *. unfold IMG_TOP_B in DTOP, STOP.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof DSH as DSH'. pose proof SSH as SSH'. unfold SH_LO, SH_HI in DSH', SSH'.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
hide_disj.
carve_frame 64%nat ST0.
apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
rewrite !f32_cons, f32_nil in XS.
bato 0x98f24. astep. chk_merge OBS 4.
bato 0x98f3c. astep. chk_merge OBS 4.
bato 0x98f48.
destruct (Z.eq_dec fs 0) as [F0|F1].
- subst fs. astep. try sh_if.
bato 0x99184. release_frame FR ST0 usp. astep. astep.
lazymatch goal with XS : rw_cells _ ?mf ST [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
change (rw_cells bsegs mf ST (f32 [a; b; c; d; e; f])) in XS end.
unfold decode_stereo_postA. finish.
all: first [ exact X | exact LX | exact XS | reflexivity ].
- astep. sh_if.
bato 0x99000.
rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?(Z.mod_small (fs * 2 ^ 1)) by lia. bnorm.
rewrite ?(land3_al D D4). replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. alits.
pose proof (u32arr_of_f32 bsegs _ D ws X) as XA. clear X.
lazymatch goal with XS : rw_cells _ ?mf ST [C4 ?a; C4 ?b; C4 ?c; C4 ?d; C4 ?e; C4 ?f] |- _ =>
change (rw_cells bsegs mf ST (f32 [a; b; c; d; e; f])) in XS end.
eapply (stereo_loopB (Z.to_nat (fs - 1)) (fs + -1)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try lia.
Qed.
End S.

