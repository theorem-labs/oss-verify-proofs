(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0aq X0au X0av.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1ct X1d5.
Ltac tlia_strict := olia ltac:(
sf_clear_big;
first [ Zify.zify; xlia zchecker
| match goal with H : hid (_ \/ _) |- _ => unfold hid in H; Zify.zify; xlia zchecker end ]).
Local Ltac tlia ::= tlia_strict.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition A_H0 : Z := 0x27000.
Definition qmf_frame (z0 top x1 x2 g0 : word) (j1 j2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[C8 z0; C8 x1; C8 x2; C8 g0; C8 top; CB 8 j1; CB 8 j2; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Definition h0_bytes : list byte := match image_bytes asegs A_H0 256 with Some bs => bs | None => [] end.
Lemma h0_len : length h0_bytes = 256%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma h0_ro : forall m, mem_inv asegs m -> exists al, length al = 64%nat /\ ro_cells asegs m A_H0 (f32 al).
Proof.
intros m MI.
pose proof (ro_cells_image asegs m A_H0 h0_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold A_H0; lia) ltac:(rewrite h0_len; unfold A_H0; lia)) as [WF BA].
cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
destruct (bytes_are_f32 64 h0_bytes h0_len) as (ws & Lws & Ews).
exists ws. split; [exact Lws|]. split; [apply cells_wf_f32|]. rewrite Ews. exact BA.
Qed.

Tactic Notation "callc" uconstr(SPEC) tactic3(clr) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | clr; post_call segs m ]
end.

Lemma zext_mul4 : forall x, 0 <= x < 2^31 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = 4 * x.
Proof.
intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by lia.
replace (x * 2 ^ 32) with (4 * x * 2 ^ 30) by lia. apply Z.div_mul. lia.
Qed.

Definition qmf_body_stmt : Prop :=
forall (FB lo X1 X2 S8 Y G0 G1 HN : Z) (s0w top : word)
(ys g0l g1l xa1 xb1 xa2 xb2 : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (FB + 8) [C8 (Z_to_bv 64 Y); C8 (Z_to_bv 64 (Y + 8 * HN)); C8 (Z_to_bv 64 G0); C8 top] ->
rw_cells asegs m Y (f32 ys) -> Z.of_nat (length ys) = 4 * HN ->
rw_cells asegs m G0 (f32 g0l) -> length g0l = 64%nat -> rw_cells asegs m G1 (f32 g1l) -> length g1l = 64%nat ->
rw_cells asegs m X1 (f32 xa1) -> Z.of_nat (length xa1) = 2 * HN -> rw_cells asegs m (X1 + 8 * HN) (f32 xb1) -> length xb1 = 32%nat ->
rw_cells asegs m X2 (f32 xa2) -> Z.of_nat (length xa2) = 2 * HN -> rw_cells asegs m (X2 + 8 * HN) (f32 xb2) -> length xb2 = 32%nat ->
aobj asegs m Y (16 * HN) -> aobj asegs m G0 256 -> aobj asegs m G1 256 -> aobj asegs m X1 (8 * HN + 128) -> aobj asegs m X2 (8 * HN + 128) -> aobj asegs m A_H0 256 ->
S8 = X2 + -32 -> 1 <= HN <= 160 -> Y mod 4 = 0 -> G0 mod 4 = 0 -> G1 mod 4 = 0 -> X1 mod 32 = 0 -> X2 mod 32 = 0 ->

IMG_TOP <= Y -> 0 < G0 -> 0 < G1 -> Y + 16 * HN <= lo -> G0 + 256 <= lo -> G1 + 256 <= lo ->
(Y + 16 * HN <= G0 \/ G0 + 256 <= Y) -> (Y + 16 * HN <= G1 \/ G1 + 256 <= Y) -> (G0 + 256 <= G1 \/ G1 + 256 <= G0) ->
(Y + 16 * HN <= SH_LO \/ SH_HI <= Y) -> (G0 + 256 <= SH_LO \/ SH_HI <= G0) -> (G1 + 256 <= SH_LO \/ SH_HI <= G1) ->
SH_HI <= lo -> lo <= X2 + -32 -> X2 + (8 * HN + 128) + 32 <= X1 + -32 -> X1 + (8 * HN + 128) + 32 <= FB -> FB + 40 < 2^63 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' t3' t4' t5' t6' : word)
(F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ys' g0' g1' x1' x2' : list word),
ms' = MS (mkR ra' (Z_to_bv 64 S8) gp tp t0' t1' t2' s0w (Z_to_bv 64 FB) a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' s4' s5' s6' s7' s8' s9' s10' (Z_to_bv 64 SHB) t3' t4' t5' t6')
F' (Z_to_bv 64 0xa52b4) fc' None m' (seg_rom asegs)
/\ munch [(FB + 32, FB + 40); (X1, X1 + (8 * HN + 128)); (X2, X2 + (8 * HN + 128)); (Y, Y + 16 * HN); (G0, G0 + 256); (G1, G1 + 256)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ frm0 fc'
/\ rw_cells asegs m' (FB + 8) [C8 (Z_to_bv 64 Y); C8 (Z_to_bv 64 (Y + 8 * HN)); C8 (Z_to_bv 64 G0); C8 (Z_to_bv 64 S8)]
/\ rw_cells asegs m' Y (f32 ys') /\ Z.of_nat (length ys') = 4 * HN
/\ rw_cells asegs m' G0 (f32 g0') /\ length g0' = 64%nat /\ rw_cells asegs m' G1 (f32 g1') /\ length g1' = 64%nat
/\ rw_cells asegs m' X1 (f32 x1') /\ Z.of_nat (length x1') = 2 * HN + 32 /\ rw_cells asegs m' X2 (f32 x2') /\ Z.of_nat (length x2') = 2 * HN + 32)
(MS (mkR (Z_to_bv 64 0xa4c6c) (Z_to_bv 64 S8) gp tp t0 t1 t2 s0w (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 X2) (Z_to_bv 64 X1) (Z_to_bv 64 32) (Z_to_bv 64 (2 * HN)) (Z_to_bv 64 Y) (Z_to_bv 64 A_H0) (Z_to_bv 64 S8) (Z_to_bv 64 G1)
s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 0xa4c6c)) fc None m (seg_rom asegs)).

Lemma qmf_body : qmf_body_stmt.
Proof.
intros FB lo X1 X2 S8 Y G0 G1 HN s0w top ys g0l g1l xa1 xb1 xa2 xb2
gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 F fc m
FR XY LY XG0 LG0 XG1 LG1 XA1 LA1 XB1 LB1 XA2 LA2 XB2 LB2 OBY OBG0 OBG1 OB1 OB2 OBA -> HHN Y4 G04 G14 X132 X232
YI G0I G1I YLO G0LO G1LO SYG0 SYG1 SG01 SHY SHG0 SHG1 LOS LOX2 X2X1 X1FR SPH MI FRM.
replace (ret_pc (Z_to_bv 64 0xa4c6c)) with (Z_to_bv 64 0xa4c6c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold APP_TOP in *.
pose proof YI as YI'. unfold IMG_TOP in YI'.
set (W := [(FB + 32, FB + 40); (X1, X1 + (8 * HN + 128)); (X2, X2 + (8 * HN + 128)); (Y, Y + 16 * HN); (G0, G0 + 256); (G1, G1 + 256)]).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (subst W; cbn; unfold SH_LO, SH_HI in *; lia).
subst W.
assert (X14 : X1 mod 4 = 0) by (clear - X132; Z.div_mod_to_equations; lia).
assert (X24 : X2 mod 4 = 0) by (clear - X232; Z.div_mod_to_equations; lia).
pose proof (rw_cells_bound _ _ _ _ XY) as BY; rewrite cells_size_f32 in BY.
assert (SEP1 : Y + 4 * Z.of_nat (length ys) <= X1 \/ X1 + (8 * HN + 128) <= Y) by lia.
assert (SEP2 : Y + 4 * Z.of_nat (length ys) <= X2 \/ X2 + (8 * HN + 128) <= Y) by lia.
assert (SEPG01 : G0 + 256 <= X1 \/ X1 + (8 * HN + 128) <= G0) by lia.
assert (SEPG12 : G1 + 256 <= X2 \/ X2 + (8 * HN + 128) <= G1) by lia.
assert (XI1 : IMG_TOP <= X1) by (unfold IMG_TOP; lia).
assert (XI2 : IMG_TOP <= X2) by (unfold IMG_TOP; lia).
assert (OF1a : offsh [(X1, X1 + 4 * (2 * HN))]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OF2a : offsh [(X2, X2 + 4 * (2 * HN))]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OF1b : offsh [(X1 + 4 * (2 * HN), X1 + 4 * (2 * HN) + 4 * 32)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OF2b : offsh [(X2 + 4 * (2 * HN), X2 + 4 * (2 * HN) + 4 * 32)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OFY : offsh [(Y, Y + 16 * HN)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OFG0 : offsh [(G0, G0 + 256)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OFG1 : offsh [(G1, G1 + 256)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (SEPO1 : Y + 16 * HN <= X1 \/ X1 + (8 * HN + 128) <= Y) by lia.
assert (SEPO2 : Y + 16 * HN <= X2 \/ X2 + (8 * HN + 128) <= Y) by lia.
assert (SEPG0X : G0 + 256 <= X1 \/ X1 + (8 * HN + 128) <= G0) by lia.
assert (SEPG1X : G1 + 256 <= X2 \/ X2 + (8 * HN + 128) <= G1) by lia.
hide_disj.
destruct xa1 as [|cw1 rest1]; [cbn [length] in LA1; lia|]. cbn [length] in LA1.
destruct xa2 as [|cw2 rest2]; [cbn [length] in LA2; lia|]. cbn [length] in LA2.

astep. astep. astep. astep. sh_if.
ato 0xa4c98.
pose proof (aobj_munch asegs _ m _ Y (16 * HN) OBY MU (shfree_of_aobj asegs _ m Y (16 * HN) OF OBY)) as OBYc.
pose proof (aobj_munch asegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj asegs _ m X1 (8 * HN + 128) OF OB1)) as OB1c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X1, X1 + 4 * (2 * HN))] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc X1 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XA1 as XC0; replace X1 with (X1 + 4 * 0) in XC0 at 1 by lia;
callc (qmf_L1 Y X1 (2 * HN) (8 * HN + 128) ys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y4 X14 SEP1 XI1 ltac:(lia) mc rest1 [] cw1 (2 * HN - 1) 0 _ _ _ _ _ _ _ mc)
(clear XA1 XC0 XD0);
[ lia | rewrite Z.shiftl_mul_pow2 by lia; lia | lia | reflexivity | lia | lia
| replace (4 * Z.of_nat (length ys)) with (16 * HN) by lia; exact OBYc | exact OB1c | exact OF1a | eassumption | exact MU0 | exact WM0 | exact XY | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBYc OB1c. rename MI0 into MI. unfold RV.
match goal with H : rw_cells _ _ X1 (f32 ?l), H2 : Z.of_nat (length ?l) = 2 * HN |- _ => rename H into XA1; rename H2 into LA1' end.

destruct xb1 as [|cb1 restb1]; [cbn [length] in LB1; lia|]. cbn [length] in LB1.
ato 0xa4d20.
pose proof (aobj_munch asegs _ m _ G0 256 OBG0 MU (shfree_of_aobj asegs _ m G0 256 OF OBG0)) as OBGc.
pose proof (aobj_munch asegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj asegs _ m X1 (8 * HN + 128) OF OB1)) as OB1c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X1 + 4 * (2 * HN), X1 + 4 * (2 * HN) + 4 * 32)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc (X1 + 4 * (2 * HN)) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XB1 as XC0; replace (X1 + 8 * HN) with (X1 + 4 * (2 * HN + 0)) in XC0 by lia;
callc (qmf_L2 G0 X1 (2 * HN) 32 (8 * HN + 128) g0l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G04 X14 LG0 SEPG01 XI1 ltac:(lia) mc restb1 [] cb1 0 _ _ _ _ _ _ _ _ mc)
(clear XB1 XC0 XD0);
[ lia | rewrite Z.shiftl_mul_pow2 by lia; lia | replace (G0 + 8 * 0 + 4) with (G0 + 4) by lia; lia | lia | reflexivity | lia | lia
| exact OBGc | exact OB1c | exact OF1b | eassumption | exact MU0 | exact WM0 | exact XG0 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB1c. rename MI0 into MI. unfold RM.
match goal with H : rw_cells _ _ (X1 + 4 * (2 * HN)) (f32 ?l), H2 : Z.of_nat (length ?l) = 32 |- _ => rename H into XB1; rename H2 into LB1' end.

ato 0xa4d84. astep. sh_if. ato 0xa4da4.
pose proof (aobj_munch asegs _ m _ Y (16 * HN) OBY MU (shfree_of_aobj asegs _ m Y (16 * HN) OF OBY)) as OBYc.
pose proof (aobj_munch asegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj asegs _ m X2 (8 * HN + 128) OF OB2)) as OB2c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X2, X2 + 4 * (2 * HN))] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc X2 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XA2 as XC0; replace X2 with (X2 + 4 * 0) in XC0 at 1 by lia;
callc (qmf_L3 Y X2 (2 * HN) (8 * HN + 128) ys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y4 X24 SEP2 XI2 ltac:(lia) mc rest2 [] cw2 (4 * HN - 1) 0 _ _ _ _ _ _ _ mc)
(clear XA2 XC0 XD0);
[ lia | rewrite Z.shiftl_mul_pow2 by lia; lia | lia | reflexivity | lia | lia
| replace (4 * Z.of_nat (length ys)) with (16 * HN) by lia; exact OBYc | exact OB2c | exact OF2a | eassumption | exact MU0 | exact WM0 | exact XY | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBYc OB2c. rename MI0 into MI. unfold RV.
match goal with H : rw_cells _ _ X2 (f32 ?l), H2 : Z.of_nat (length ?l) = 2 * HN |- _ => rename H into XA2; rename H2 into LA2' end.

destruct xb2 as [|cb2 restb2]; [cbn [length] in LB2; lia|]. cbn [length] in LB2.
ato 0xa4e28.
pose proof (aobj_munch asegs _ m _ G1 256 OBG1 MU (shfree_of_aobj asegs _ m G1 256 OF OBG1)) as OBGc.
pose proof (aobj_munch asegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj asegs _ m X2 (8 * HN + 128) OF OB2)) as OB2c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X2 + 4 * (2 * HN), X2 + 4 * (2 * HN) + 4 * 32)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc (X2 + 4 * (2 * HN)) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XB2 as XC0; replace (X2 + 8 * HN) with (X2 + 4 * (2 * HN + 0)) in XC0 by lia;
callc (qmf_L4 G1 X2 (2 * HN) 32 (8 * HN + 128) g1l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G14 X24 LG1 SEPG12 XI2 ltac:(lia) mc restb2 [] cb2 0 _ _ _ _ _ _ _ _ mc)
(clear XB2 XC0 XD0);
[ lia | rewrite Z.shiftl_mul_pow2 by lia; lia | replace (G1 + 8 * 0 + 4) with (G1 + 4) by lia; lia | lia | reflexivity | lia | lia
| exact OBGc | exact OB2c | exact OF2b | eassumption | exact MU0 | exact WM0 | exact XG1 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB2c. rename MI0 into MI. unfold RM.
match goal with H : rw_cells _ _ (X2 + 4 * (2 * HN)) (f32 ?l), H2 : Z.of_nat (length ?l) = 32 |- _ => rename H into XB2; rename H2 into LB2' end.

ato 0xa4e8c. astep. sh_if. ato 0xa4ed0.
replace (X1 + Z.shiftl (2 * HN) 2) with (X1 + 4 * (2 * HN - 1 + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (X2 + Z.shiftl (2 * HN) 2) with (X2 + 4 * (2 * HN - 1 + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (2 * HN + -2) with (2 * HN - 1 - 1) by lia.
replace (SHB + Z.shiftr (A_H0 mod 18446744073709551616) 3) with (Z.shiftr A_H0 3 + SHB) by (unfold A_H0; reflexivity).
rewrite (zext_mul4 (2 * HN + -1)) by lia. replace (4 * (2 * HN + -1)) with (4 * (2 * HN - 1)) by lia.
rewrite <- LA1' in XB1. pose proof (f32_join asegs _ X1 _ _ XA1 XB1) as XL1. clear XA1 XB1.
rewrite <- LA2' in XB2. pose proof (f32_join asegs _ X2 _ _ XA2 XB2) as XL2. clear XA2 XB2.
destruct ys as [|y0 [|y1 [|y2 [|y3 yrest]]]]; try (cbn [length] in LY; lia). cbn [length] in LY.
destruct (h0_ro _ MI) as (al & LAL & RAL).
pose proof (aobj_munch asegs _ m _ Y (16 * HN) OBY MU (shfree_of_aobj asegs _ m Y (16 * HN) OF OBY)) as OBYc.
pose proof (aobj_munch asegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj asegs _ m X1 (8 * HN + 128) OF OB1)) as OB1c.
pose proof (aobj_munch asegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj asegs _ m X2 (8 * HN + 128) OF OB2)) as OB2c.
pose proof (aobj_munch asegs _ m _ A_H0 256 OBA MU (shfree_of_aobj asegs _ m A_H0 256 OF OBA)) as OBAc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(Y, Y + 16 * HN)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc Y (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XY as XC0; replace Y with (Y + 16 * 0) in XC0 at 1 by lia;
lazymatch type of XL1 with rw_cells _ _ _ (f32 ?xl1) => lazymatch type of XL2 with rw_cells _ _ _ (f32 ?xl2) =>
callc (qmf_outer A_H0 X1 X2 (8 * HN + 128) Y HN al xl1 xl2 _ _ _ _ _ _ _
ltac:(unfold A_H0; reflexivity) X14 X24 Y4 LAL ltac:(rewrite length_app; lia) ltac:(rewrite length_app; lia) ltac:(lia) HHN SEPO1 SEPO2 YI ltac:(unfold A_H0, IMG_TOP; lia)
mc (Z.to_nat (HN - 1)) yrest [] y0 y1 y2 y3 0 _ _ _ _ _ _ _ _ _ mc)
(clear XY XC0 XD0 RAL) end end;
[ lia | reflexivity | lia | exact OBAc | exact OB1c | exact OB2c | exact OBYc | exact OFY | eassumption | eassumption | exact MU0 | exact WM0
| exact RAL | exact XL1 | exact XL2 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBYc OB1c OB2c OBAc. rename MI0 into MI. unfold RO.
match goal with H : rw_cells _ _ Y (f32 ?l), H2 : Z.of_nat (length ?l) = 4 * HN |- _ => rename H into XY; rename H2 into LY' end.
match goal with H : frm0 _ |- _ => clear FRM; rename H into FRM end.

destruct g0l as [|ge0 [|go0 grest0]]; try (cbn [length] in LG0; lia). cbn [length] in LG0.
ato 0xa51dc.
pose proof (aobj_munch asegs _ m _ G0 256 OBG0 MU (shfree_of_aobj asegs _ m G0 256 OF OBG0)) as OBGc.
pose proof (aobj_munch asegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj asegs _ m X1 (8 * HN + 128) OF OB1)) as OB1c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(G0, G0 + 256)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc G0 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XG0 as XC0; replace G0 with (G0 + 8 * 0) in XC0 at 1 by lia;
lazymatch type of XL1 with rw_cells _ _ _ (f32 ?xl1) =>
callc (qmf_L5 G0 X1 (8 * HN + 128) xl1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G04 X14 ltac:(rewrite length_app; lia) SEPG0X _ _
mc 31%nat grest0 [] ge0 go0 0 _ _ _ _ _ _ _ mc)
(clear XG0 XC0 XD0) end;
[ lia | lia | reflexivity | lia | reflexivity | lia
| exact OBGc | exact OB1c | exact OFG0 | eassumption | exact MU0 | exact WM0 | exact XL1 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB1c. rename MI0 into MI. unfold R5.
match goal with H : rw_cells _ _ G0 (f32 ?l), H2 : length ?l = 64%nat |- _ => rename H into XG0; rename H2 into LG0' end.

destruct g1l as [|ge1 [|go1 grest1]]; try (cbn [length] in LG1; lia). cbn [length] in LG1.
ato 0xa5250.
pose proof (aobj_munch asegs _ m _ G1 256 OBG1 MU (shfree_of_aobj asegs _ m G1 256 OF OBG1)) as OBGc.
pose proof (aobj_munch asegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj asegs _ m X2 (8 * HN + 128) OF OB2)) as OB2c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(G1, G1 + 256)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc G1 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XG1 as XC0; replace G1 with (G1 + 8 * 0) in XC0 at 1 by lia;
lazymatch type of XL2 with rw_cells _ _ _ (f32 ?xl2) =>
callc (qmf_L6 G1 X2 (8 * HN + 128) xl2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G14 X24 ltac:(rewrite length_app; lia) SEPG1X _ _
mc 31%nat grest1 [] ge1 go1 0 _ _ _ _ _ _ _ mc)
(clear XG1 XC0 XD0) end;
[ lia | lia | reflexivity | lia | reflexivity | lia
| exact OBGc | exact OB2c | exact OFG1 | eassumption | exact MU0 | exact WM0 | exact XL2 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB2c. rename MI0 into MI. unfold R6.
match goal with H : rw_cells _ _ G1 (f32 ?l), H2 : length ?l = 64%nat |- _ => rename H into XG1; rename H2 into LG1' end.
apply evt_done. do 33 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FR|].
split; [exact XY|]. split; [exact LY'|]. split; [exact XG0|]. split; [exact LG0'|]. split; [exact XG1|]. split; [exact LG1'|].
split; [exact XL1|]. split; [rewrite length_app; lia|]. split; [exact XL2|]. rewrite length_app; lia.
Qed.
