(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yq X0yp X11b X11e X11f.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_strict.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition h0B_bytes : list byte := match image_bytes bsegs 0x27000 256 with Some bs => bs | None => [] end.
Lemma h0B_len : length h0B_bytes = 256%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma h0B_ro : forall m, mem_inv bsegs m -> exists al, length al = 64%nat /\ ro_cells bsegs m 0x27000 (f32 al).
Proof.
intros m MI.
pose proof (ro_cells_image bsegs m 0x27000 h0B_bytes MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite h0B_len; lia)) as [WF BA].
cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
destruct (bytes_are_f32 64 h0B_bytes h0B_len) as (ws & Lws & Ews).
exists ws. split; [exact Lws|]. split; [apply cells_wf_f32|]. rewrite Ews. exact BA.
Qed.

Ltac rs_solve :=
unfold mkR;
repeat match goal with
| |- TNode _ _ _ = TNode _ _ _ => f_equal
| |- Some _ = Some _ => f_equal
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
| |- _ = _ => reflexivity
end.
Tactic Notation "rshape" uconstr(T) tactic3(unf) :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let H := fresh "RS" in
eassert (H : R = T) by (unf; rs_solve);
rewrite H; clear H
end.

Definition qmf_body16B_stmt : Prop :=
forall (FB lo X1 X2 S8 Y G0 G1 HN : Z) (s0w top : word) (j1 : list byte)
(ys g0l g1l xa1 xb1 xa2 xb2 : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (FB + 8) [CB 8 j1; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (4 * (32 + 2 * HN))); C8 (Z_to_bv 64 G1); C8 (Z_to_bv 64 G0); C8 (Z_to_bv 64 Y);
C8 (Z_to_bv 64 32); C8 top] ->
rw_cells bsegs m Y (f32 ys) -> Z.of_nat (length ys) = 4 * HN ->
rw_cells bsegs m G0 (f32 g0l) -> length g0l = 64%nat -> rw_cells bsegs m G1 (f32 g1l) -> length g1l = 64%nat ->
rw_cells bsegs m X1 (f32 xa1) -> Z.of_nat (length xa1) = 2 * HN -> rw_cells bsegs m (X1 + 8 * HN) (f32 xb1) -> length xb1 = 32%nat ->
rw_cells bsegs m X2 (f32 xa2) -> Z.of_nat (length xa2) = 2 * HN -> rw_cells bsegs m (X2 + 8 * HN) (f32 xb2) -> length xb2 = 32%nat ->
aobj bsegs m Y (16 * HN) -> aobj bsegs m G0 256 -> aobj bsegs m G1 256 -> aobj bsegs m X1 (8 * HN + 128) -> aobj bsegs m X2 (8 * HN + 128) -> aobj bsegs m 0x27000 256 ->
S8 = X2 + -32 -> 1 <= HN <= 160 -> Y mod 4 = 0 -> G0 mod 4 = 0 -> G1 mod 4 = 0 -> X1 mod 32 = 0 -> X2 mod 32 = 0 ->

IMG_TOP_B <= Y -> 0 < G0 -> 0 < G1 -> Y + 16 * HN <= lo -> G0 + 256 <= lo -> G1 + 256 <= lo ->
(Y + 16 * HN <= G0 \/ G0 + 256 <= Y) -> (Y + 16 * HN <= G1 \/ G1 + 256 <= Y) -> (G0 + 256 <= G1 \/ G1 + 256 <= G0) ->
(Y + 16 * HN <= SH_LO \/ SH_HI <= Y) -> (G0 + 256 <= SH_LO \/ SH_HI <= G0) -> (G1 + 256 <= SH_LO \/ SH_HI <= G1) ->
SH_HI <= lo -> lo <= X2 + -32 -> X2 + (8 * HN + 128) + 32 <= X1 + -32 -> X1 + (8 * HN + 128) + 32 <= FB -> FB + 208 < 2^62 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
(F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (w8 w16 : word) (ys' g0' g1' x1' x2' : list word),
ms' = MS (mkR ra' (Z_to_bv 64 S8) gp tp t0' t1' t2' s0w (Z_to_bv 64 FB) a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
F' (Z_to_bv 64 0xa8eb8) fc' None m' (seg_rom bsegs)
/\ munch [(FB + 8, FB + 72); (X1, X1 + (8 * HN + 128)); (X2, X2 + (8 * HN + 128)); (Y, Y + 16 * HN); (G0, G0 + 256); (G1, G1 + 256)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ frm0 fc'
/\ rw_cells bsegs m' (FB + 8) [C8 w8; C8 w16; C8 (Z_to_bv 64 (4 * (32 + 2 * HN))); C8 (Z_to_bv 64 G1); C8 (Z_to_bv 64 G0); C8 (Z_to_bv 64 Y);
C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 S8)]
/\ rw_cells bsegs m' Y (f32 ys') /\ Z.of_nat (length ys') = 4 * HN
/\ rw_cells bsegs m' G0 (f32 g0') /\ length g0' = 64%nat /\ rw_cells bsegs m' G1 (f32 g1') /\ length g1' = 64%nat
/\ rw_cells bsegs m' X1 (f32 x1') /\ Z.of_nat (length x1') = 2 * HN + 32 /\ rw_cells bsegs m' X2 (f32 x2') /\ Z.of_nat (length x2') = 2 * HN + 32)
(MS (mkR (Z_to_bv 64 0xa8618) (Z_to_bv 64 S8) gp tp t0 t1 t2 s0w (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (2 * HN)) (Z_to_bv 64 (32 + 2 * HN)) (Z_to_bv 64 X2) (Z_to_bv 64 X1) s6 (Z_to_bv 64 S8) (Z_to_bv 64 0x27000)
(Z_to_bv 64 (Y + 8 * HN)) (Z_to_bv 64 Y) (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 0xa8618)) fc None m (seg_rom bsegs)).

Lemma qmf_body16B : qmf_body16B_stmt.
Proof.
intros FB lo X1 X2 S8 Y G0 G1 HN s0w top j1 ys g0l g1l xa1 xb1 xa2 xb2
gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 F fc m
FR XY LY XG0 LG0 XG1 LG1 XA1 LA1 XB1 LB1 XA2 LA2 XB2 LB2 OBY OBG0 OBG1 OB1 OB2 OBA -> HHN Y4 G04 G14 X132 X232
YI G0I G1I YLO G0LO G1LO SYG0 SYG1 SG01 SHY SHG0 SHG1 LOS LOX2 X2X1 X1FR SPH MI FRM.
replace (ret_pc (Z_to_bv 64 0xa8618)) with (Z_to_bv 64 0xa8618) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold APP_TOP in *.
pose proof YI as YI'. unfold IMG_TOP_B in YI'.
set (W := [(FB + 8, FB + 72); (X1, X1 + (8 * HN + 128)); (X2, X2 + (8 * HN + 128)); (Y, Y + 16 * HN); (G0, G0 + 256); (G1, G1 + 256)]).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (subst W; cbn; unfold SH_LO, SH_HI in *; lia).
subst W.
assert (X14 : X1 mod 4 = 0) by (clear - X132; Z.div_mod_to_equations; lia).
assert (X24 : X2 mod 4 = 0) by (clear - X232; Z.div_mod_to_equations; lia).
pose proof (rw_cells_bound _ _ _ _ XY) as BY; rewrite cells_size_f32 in BY.
pose proof OBY as (OY0 & OY1 & _). pose proof OB1 as (O10 & O11 & _). pose proof OB2 as (O20 & O21 & _).
pose proof OBG0 as (OG00 & OG01 & _). pose proof OBG1 as (OG10 & OG11 & _).
assert (SEP1 : Y + 4 * Z.of_nat (length ys) <= X1 \/ X1 + (8 * HN + 128) <= Y) by lia.
assert (SEP2 : Y + 4 * Z.of_nat (length ys) <= X2 \/ X2 + (8 * HN + 128) <= Y) by lia.
assert (XI1 : IMG_TOP_B <= X1) by (unfold IMG_TOP_B; lia).
assert (XI2 : IMG_TOP_B <= X2) by (unfold IMG_TOP_B; lia).
assert (OF1a : offsh [(X1, X1 + 4 * (2 * HN))]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OF2a : offsh [(X2, X2 + 4 * (2 * HN))]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OF1b : offsh [(X1 + 4 * (2 * HN), X1 + 4 * (2 * HN) + 128)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OF2b : offsh [(X2 + 4 * (2 * HN), X2 + 4 * (2 * HN) + 128)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
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

bato 0xa863c.

replace (0 <? Y) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. rewrite zb_lxor_ones by lia.
rshape (R1 Y X1 (2 * HN) (32 + 2 * HN) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _) (unfold R1).
pose proof (aobj_munch bsegs _ m _ Y (16 * HN) OBY MU (shfree_of_aobj bsegs _ m Y (16 * HN) OF OBY)) as OBYc.
pose proof (aobj_munch bsegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj bsegs _ m X1 (8 * HN + 128) OF OB1)) as OB1c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X1, X1 + 4 * (2 * HN))] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc X1 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XA1 as XC0; replace X1 with (X1 + 4 * 0) in XC0 at 1 by lia;
callc (qmf_cp1 Y X1 (2 * HN) (8 * HN + 128) (32 + 2 * HN) ys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y4 X14 ltac:(lia) ltac:(lia) SEP1 XI1 ltac:(lia)
mc rest1 [] cw1 0 _ _ _ _ _ mc)
(clear XA1 XC0 XD0);
[ reflexivity | cbn [length] in *; lia
| replace (4 * Z.of_nat (length ys)) with (16 * HN) by lia; exact OBYc | exact OB1c | exact OF1a | eassumption | exact MU0 | exact WM0 | exact XY | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBYc OB1c. rename MI0 into MI.
rename POST into XA1. rename PC into LA1'. unfold R1.

destruct xb1 as [|cb1 restb1]; [cbn [length] in LB1; lia|]. cbn [length] in LB1.
bato 0xa8720.

replace (bv_swrap 32 (32 + 2 * HN - 2 * HN)) with 32 by (rewrite swrap32_small by lia; lia).
replace (32 + 2 * HN <? 32 mod 18446744073709551616) with false by (symmetry; apply Z.ltb_ge; cbn; lia). cbn [Z.b2z].
rewrite (land3_al G0 G04).
rshape (RM2 G0 X1 (2 * HN) FB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _) (unfold RM2).
pose proof (aobj_munch bsegs _ m _ G0 256 OBG0 MU (shfree_of_aobj bsegs _ m G0 256 OF OBG0)) as OBGc.
pose proof (aobj_sub bsegs _ _ _ (X1 + 4 * (2 * HN)) 128 (aobj_munch bsegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj bsegs _ m X1 (8 * HN + 128) OF OB1)) ltac:(lia) ltac:(lia)) as OB1c.
pose proof FR as S40. chunk_uncons S40 as S8c. chunk_uncons S40 as S16c. chunk_uncons S40 as S24c. chunk_uncons S40 as S32c. clear S8c S16c S24c S32c.
chunk_uncons S40 as S40c. clear S40. rename S40c into S40. replace (FB + 8 + 8 + 8 + 8 + 8) with (FB + 40) in S40 by lia.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X1 + 4 * (2 * HN), X1 + 4 * (2 * HN) + 128)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc (X1 + 4 * (2 * HN)) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XB1 as XC0; replace (X1 + 8 * HN) with (X1 + 4 * (2 * HN) + 4 * 0) in XC0 by lia;
callc (qmf_cp2 G0 X1 (2 * HN) FB g0l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G04 X14 LG0 ltac:(lia) ltac:(lia) ltac:(lia) XI1 ltac:(lia) ltac:(lia)
mc restb1 [] cb1 0 _ _ _ _ _ mc)
(clear XB1 XC0 XD0 S40);
[ reflexivity | cbn [length] in *; lia
| exact OBGc | exact OB1c | exact OF1b | eassumption | exact MU0 | exact WM0 | exact S40 | exact XG0 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB1c. rename MI0 into MI.
rename POST into XB1. rename PC into LB1'. unfold RM2.

destruct (f32_winB _ Y ys (2 * HN) (Z.to_nat (2 * HN)) XY ltac:(lia) ltac:(lia)) as (ys2 & LYS2 & XY2).
replace (Y + 4 * (2 * HN)) with (Y + 8 * HN) in XY2 by lia.
bato 0xa87dc.
replace (0 <? Y + 8 * HN) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. rewrite zb_lxor_ones by lia.
rshape (R3 (Y + 8 * HN) X2 (2 * HN) (32 + 2 * HN) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _) (unfold R3).
assert (Y84 : (Y + 8 * HN) mod 4 = 0) by (clear - Y4; Z.div_mod_to_equations; lia).
assert (SEP3 : Y + 8 * HN + 4 * Z.of_nat (length ys2) <= X2 \/ X2 + (8 * HN + 128) <= Y + 8 * HN) by (unfold hid in SEPO2; lia).
pose proof (aobj_sub bsegs _ _ _ (Y + 8 * HN) (4 * Z.of_nat (length ys2)) (aobj_munch bsegs _ m _ Y (16 * HN) OBY MU (shfree_of_aobj bsegs _ m Y (16 * HN) OF OBY)) ltac:(lia) ltac:(lia)) as OBYc.
pose proof (aobj_munch bsegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj bsegs _ m X2 (8 * HN + 128) OF OB2)) as OB2c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X2, X2 + 4 * (2 * HN))] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc X2 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XA2 as XC0; replace X2 with (X2 + 4 * 0) in XC0 at 1 by lia;
callc (qmf_cp3 (Y + 8 * HN) X2 (2 * HN) (8 * HN + 128) (32 + 2 * HN) ys2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y84 X24 ltac:(lia) ltac:(lia) SEP3 XI2 ltac:(lia)
mc rest2 [] cw2 0 _ _ _ _ _ mc)
(clear XA2 XC0 XD0 XY2);
[ reflexivity | cbn [length] in *; lia
| exact OBYc | exact OB2c | exact OF2a | eassumption | exact MU0 | exact WM0 | exact XY2 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBYc OB2c SEP3 Y84. rename MI0 into MI.
rename POST into XA2. rename PC into LA2'. unfold R3.

destruct xb2 as [|cb2 restb2]; [cbn [length] in LB2; lia|]. cbn [length] in LB2.
bato 0xa88bc.
replace (32 + 2 * HN <? 32) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
rewrite (land3_al G1 G14).
rshape (RM4 G1 X2 (2 * HN) FB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _) (unfold RM4).
pose proof (aobj_munch bsegs _ m _ G1 256 OBG1 MU (shfree_of_aobj bsegs _ m G1 256 OF OBG1)) as OBGc.
pose proof (aobj_sub bsegs _ _ _ (X2 + 4 * (2 * HN)) 128 (aobj_munch bsegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj bsegs _ m X2 (8 * HN + 128) OF OB2)) ltac:(lia) ltac:(lia)) as OB2c.
pose proof FR as S32. chunk_uncons S32 as S8c. chunk_uncons S32 as S16c. chunk_uncons S32 as S24c. clear S8c S16c S24c.
chunk_uncons S32 as S32c. clear S32. rename S32c into S32. replace (FB + 8 + 8 + 8 + 8) with (FB + 32) in S32 by lia.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(X2 + 4 * (2 * HN), X2 + 4 * (2 * HN) + 128)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc (X2 + 4 * (2 * HN)) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XB2 as XC0; replace (X2 + 8 * HN) with (X2 + 4 * (2 * HN) + 4 * 0) in XC0 by lia;
callc (qmf_cp4 G1 X2 (2 * HN) FB g1l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G14 X24 LG1 ltac:(lia) ltac:(lia) ltac:(lia) XI2 ltac:(lia) ltac:(lia)
mc restb2 [] cb2 0 _ _ _ _ _ mc)
(clear XB2 XC0 XD0 S32);
[ reflexivity | cbn [length] in *; lia
| exact OBGc | exact OB2c | exact OF2b | eassumption | exact MU0 | exact WM0 | exact S32 | exact XG1 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB2c. rename MI0 into MI.
rename POST into XB2. rename PC into LB2'. unfold RM4.

bato 0xa8990.
replace (0 <? Y) with true by (symmetry; apply Z.ltb_lt; lia). rewrite (land3_al Y Y4). alits. rewrite zb_lxor_ones by lia.
cbn [Z.b2z].
bato 0xa89a0.

rshape (ROB 159744 X1 X2 Y (2 * HN) FB _ _ _ _ _ _ 0 _ _ _ _ _ _ _ _ _) (unfold ROB).
rewrite <- LA1' in XB1. pose proof (f32_join bsegs _ X1 _ _ XA1 XB1) as XL1. clear XA1 XB1.
rewrite <- LA2' in XB2. pose proof (f32_join bsegs _ X2 _ _ XA2 XB2) as XL2. clear XA2 XB2.
destruct ys as [|y0 [|y1 [|y2 [|y3 yrest]]]]; try (cbn [length] in LY; lia). cbn [length] in LY.
destruct (h0B_ro _ MI) as (al & LAL & RAL).
pose proof FR as F8. chunk_uncons F8 as F8a. chunk_uncons F8 as F8b. chunk_cat F8a F8b. clear F8. rename F8a into F8.
pose proof FR as F48. chunk_uncons F48 as F48a. chunk_uncons F48 as F48b. chunk_uncons F48 as F48c. chunk_uncons F48 as F48d. chunk_uncons F48 as F48e.
chunk_uncons F48 as F48f. chunk_uncons F48 as F48g. chunk_cat F48f F48g. clear F48 F48a F48b F48c F48d F48e. rename F48f into F48.
replace (FB + 8 + 8 + 8 + 8 + 8 + 8) with (FB + 48) in F48 by lia.
pose proof (aobj_munch bsegs _ m _ Y (16 * HN) OBY MU (shfree_of_aobj bsegs _ m Y (16 * HN) OF OBY)) as OBYc.
pose proof (aobj_munch bsegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj bsegs _ m X1 (8 * HN + 128) OF OB1)) as OB1c.
pose proof (aobj_munch bsegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj bsegs _ m X2 (8 * HN + 128) OF OB2)) as OB2c.
pose proof (aobj_munch bsegs _ m _ 159744 256 OBA MU (shfree_of_aobj bsegs _ m 159744 256 OF OBA)) as OBAc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(Y, Y + 16 * HN)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc Y (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XY as XC0; replace Y with (Y + 16 * 0) in XC0 at 1 by lia;
lazymatch type of XL1 with rw_cells _ _ _ (f32 ?xl1) => lazymatch type of XL2 with rw_cells _ _ _ (f32 ?xl2) =>
callc (qmf_outerB 159744 X1 X2 (8 * HN + 128) Y HN (2 * HN) FB al xl1 xl2 _ _ _ _ _ _
ltac:(reflexivity) ltac:(lia) X14 X24 Y4 ltac:(lia) ltac:(lia) ltac:(lia) LAL ltac:(rewrite length_app; lia) ltac:(rewrite length_app; lia) ltac:(lia)
eq_refl HHN SEPO1 SEPO2 YI ltac:(unfold IMG_TOP_B; lia) ltac:(lia) ltac:(lia)
mc (Z.to_nat (HN - 1)) yrest [] y0 y1 y2 y3 0 _ _ _ _ _ _ _ _ _ _ _ mc)
(clear XY XC0 XD0 RAL F8 F48) end end;
[ lia | reflexivity | lia | exact OBAc | exact OB1c | exact OB2c | exact OBYc | exact OFY | eassumption | eassumption | exact MU0 | exact WM0
| exact RAL | exact XL1 | exact XL2 | exact F8 | exact F48 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBYc OB1c OB2c OBAc. rename MI0 into MI.
clear FRM. rename PC into FRM. rename PC0 into LY'. rename POST into XY. unfold ROB.

destruct g0l as [|ge0 [|go0 grest0]]; try (cbn [length] in LG0; lia). cbn [length] in LG0.
bato 0xa8da8.
rshape (RW1 G0 X1 FB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _) (unfold RW1).
pose proof FR as S24. chunk_uncons S24 as S8c. chunk_uncons S24 as S16c. clear S8c S16c. chunk_uncons S24 as S24c.
chunk_uncons S24 as S32c. chunk_uncons S24 as S40c. clear S24 S32c. rename S24c into S24.
replace (FB + 8 + 8 + 8) with (FB + 24) in S24 by lia. replace (FB + 8 + 8 + 8 + 8 + 8) with (FB + 40) in S40c by lia.
pose proof (aobj_munch bsegs _ m _ G0 256 OBG0 MU (shfree_of_aobj bsegs _ m G0 256 OF OBG0)) as OBGc.
pose proof (aobj_munch bsegs _ m _ X1 (8 * HN + 128) OB1 MU (shfree_of_aobj bsegs _ m X1 (8 * HN + 128) OF OB1)) as OB1c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(G0, G0 + 256)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc G0 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XG0 as XC0; replace G0 with (G0 + 8 * 0) in XC0 at 1 by lia;
lazymatch type of XL1 with rw_cells _ _ _ (f32 ?xl1) =>
callc (qmf_wb1 G0 X1 (8 * HN + 128) (4 * (32 + 2 * HN)) FB xl1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
G04 X14 ltac:(rewrite length_app; lia) ltac:(lia) ltac:(lia) SEPG0X ltac:(lia) ltac:(lia) ltac:(lia)
mc 31%nat grest0 [] ge0 go0 0 _ _ _ _ _ mc)
(clear XG0 XC0 XD0 S24 S40c) end;
[ lia | reflexivity | lia | exact OBGc | exact OB1c | exact OFG0 | eassumption | exact MU0 | exact WM0 | exact S24 | exact S40c | exact XL1 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB1c. rename MI0 into MI.
rename POST into XG0. rename PC into LG0'. unfold RW1.

destruct g1l as [|ge1 [|go1 grest1]]; try (cbn [length] in LG1; lia). cbn [length] in LG1.
bato 0xa8e34.
rshape (RW2 G1 X2 FB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _) (unfold RW2).
pose proof FR as S24. chunk_uncons S24 as S8c. chunk_uncons S24 as S16c. clear S8c S16c. chunk_uncons S24 as S24c.
chunk_uncons S24 as S32c. clear S24. rename S24c into S24.
replace (FB + 8 + 8 + 8) with (FB + 24) in S24 by lia. replace (FB + 8 + 8 + 8 + 8) with (FB + 32) in S32c by lia.
pose proof (aobj_munch bsegs _ m _ G1 256 OBG1 MU (shfree_of_aobj bsegs _ m G1 256 OF OBG1)) as OBGc.
pose proof (aobj_munch bsegs _ m _ X2 (8 * HN + 128) OB2 MU (shfree_of_aobj bsegs _ m X2 (8 * HN + 128) OF OB2)) as OB2c.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(G1, G1 + 256)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc G1 (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XG1 as XC0; replace G1 with (G1 + 8 * 0) in XC0 at 1 by lia;
lazymatch type of XL2 with rw_cells _ _ _ (f32 ?xl2) =>
callc (qmf_wb2 G1 X2 (8 * HN + 128) (4 * (32 + 2 * HN)) FB xl2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
G14 X24 ltac:(rewrite length_app; lia) ltac:(lia) ltac:(lia) SEPG1X ltac:(lia) ltac:(lia) ltac:(lia)
mc 31%nat grest1 [] ge1 go1 0 _ _ _ _ _ mc)
(clear XG1 XC0 XD0 S24 S32c) end;
[ lia | reflexivity | lia | exact OBGc | exact OB2c | exact OFG1 | eassumption | exact MU0 | exact WM0 | exact S24 | exact S32c | exact XL2 | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 OBGc OB2c. rename MI0 into MI.
rename POST into XG1. rename PC into LG1'. unfold RW2.

apply evt_done. do 36 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FR|].
split; [exact XY|]. split; [exact LY'|]. split; [exact XG0|]. split; [exact LG0'|]. split; [exact XG1|]. split; [exact LG1'|].
split; [exact XL1|]. split; [rewrite length_app; lia|]. split; [exact XL2|]. rewrite length_app; lia.
Qed.

