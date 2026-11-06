(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X12a X0z0 X0z1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma land_m4_al8 : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof.
intros x Hx H. change 18446744073709551612 with (Z.ldiff (Z.ones 64) (Z.ones 2)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
Section XF.
Variables (IQ XF : Z).
Variables rav spv gp tp t2 s0v s1v s2v s3v s4v s7v s9v s10v s11 t3 t4 t5 t6 : word.
Hypothesis Q4 : IQ mod 4 = 0.
Hypothesis X4 : XF mod 4 = 0.
Hypothesis Q0 : 0 < IQ.
Hypothesis SEPQX : IQ + 32 <= XF \/ XF + 32 <= IQ.

Definition RX8 (i : Z) (t0v t1v : word) (kz : Z) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2 s0v s1v (Z_to_bv 64 (XF + 4 * i)) (Z_to_bv 64 (IQ + 4 * i)) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 1) (Z_to_bv 64 kz)
(Z_to_bv 64 (18446744073709551615 - XF)) (Z_to_bv 64 (XF + 4 * i)) (Z_to_bv 64 (IQ + 4 * i))
s2v s3v s4v (Z_to_bv 64 XF) (Z_to_bv 64 IQ) s7v (Z_to_bv 64 SHB) s9v s10v s11 t3 t4 t5 t6.

Definition xf8_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' F' fc' m' (xs' : list word),
ms' = MS (RX8 8 t0' t1' 0) F' (Z_to_bv 64 0xae96c) fc' None m' (seg_rom bsegs)
/\ munch [(XF, XF + 32)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ length xs' = 8%nat /\ rw_cells bsegs m' XF (f32 xs').

Lemma l2l8_xf : forall (mI : mem) (qrest xrest xdone : list word) (q x : word) (i : Z) (t0v t1v : word) F1 fc mc,
i = Z.of_nat (length xdone) -> length qrest = length xrest -> i + 1 + Z.of_nat (length qrest) = 8 ->
aobj bsegs mI IQ 32 -> aobj bsegs mI XF 32 -> offsh [(XF, XF + 32)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(XF, XF + 32)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (IQ + 4 * i) (f32 (q :: qrest)) ->
rw_cells bsegs mc XF (f32 xdone) -> rw_cells bsegs mc (XF + 4 * i) (f32 (x :: xrest)) ->
evt bsegs (xf8_post mI)
(MS (RX8 i t0v t1v (Z.of_nat (S (length qrest)))) F1 (Z_to_bv 64 0xae8ac) fc None mc (seg_rom bsegs)).
Proof using Q4 X4 Q0 SEPQX.
intros mI qrest.
induction qrest as [|q' qrest IH]; intros xrest xdone q x i t0v t1v F1 fc mc Hi LQ HN OBQ OBX OF FRM MI MU WM QC XD XC;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ QC) as BQ; rewrite cells_size_f32 in BQ; cbn [length] in BQ;
pose proof (rw_cells_bound _ _ _ _ XC) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ XD) as BXD; rewrite cells_size_f32 in BXD;
unfold RX8; rewrite !f32_cons in XC;
pose proof QC as QH; chunk_split_f32 QH at 1%nat as Q1; rewrite ?f32_cons, ?f32_nil in Q1; clear QH;
assert (QA4 : (IQ + 4 * i) mod 4 = 0) by (clear - Q4; Z.div_mod_to_equations; lia).
-
destruct xrest; [|cbn in LQ; lia]. cbn [length] in HN. rewrite f32_nil in XC.
assert (K : forall (F2 : bvmap 5 word) (t0' t1' : word) fc2, frm0 fc2 ->
evt bsegs (xf8_post mI) (MS (RX8 i t0' t1' (Z.of_nat 1)) F2 (Z_to_bv 64 0xae914) fc2 None mc (seg_rom bsegs))).
{ intros F2 t0' t1' fc2 FRM2. unfold RX8.
bato 0xae924.
astep. chk_merge OBX 4.
bato 0xae944. rewrite ?swrap32_small by lia. astep. sh_if. astep.
chunk_snoc XD XC. rewrite <- f32_nil, <- f32_cons, <- f32_app in XD.
replace (IQ + 4 * i + 4) with (IQ + 4 * 8) by lia. replace (XF + 4 * i + 4) with (XF + 4 * 8) by lia. replace (4 * i + 4) with (4 * 8) by lia.
replace (Z.of_nat 1 + -1) with 0 by lia.
unfold xf8_post, RX8. finish; [ | exact XD ].
rewrite length_app. cbn [length]. lia. }
bato 0xae8d0. astep. chk_merge OBQ 4.
bato 0xae8e0. astep. if_cases KB.
+ bato 0xae914. apply K. assumption.
+ bato 0xae914. apply K. assumption.
-
destruct xrest as [|x' xrest]; [cbn in LQ; lia|]. cbn [length] in HN, LQ, BQ, BX.
assert (K : forall (F2 : bvmap 5 word) (t0' t1' : word) fc2, frm0 fc2 ->
evt bsegs (xf8_post mI) (MS (RX8 i t0' t1' (Z.of_nat (S (S (length qrest))))) F2 (Z_to_bv 64 0xae914) fc2 None mc (seg_rom bsegs))).
{ intros F2 t0' t1' fc2 FRM2. unfold RX8.
bato 0xae924. astep. chk_merge OBX 4.
bato 0xae944. rewrite ?swrap32_small by lia. astep. sh_if.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in XD.
chunk_split_f32 QC at 1%nat as QX0. clear QX0 Q1.
rewrite <- ?f32_cons in XC.
replace (IQ + 4 * i + 4) with (IQ + 4 * (i + 1)) in * by lia. replace (XF + 4 * i + 4) with (XF + 4 * (i + 1)) in * by lia.
replace (4 * i + 4) with (4 * (i + 1)) by lia.
replace (Z.of_nat (S (S (length qrest))) + -1) with (Z.of_nat (S (length qrest))) by lia.
eapply (IH xrest _ q' x' (i + 1)); try eassumption; try reflexivity.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia). }
bato 0xae8d0. astep. chk_merge OBQ 4.
bato 0xae8e0. astep. if_cases KB.
+ bato 0xae914. apply K. assumption.
+ bato 0xae914. apply K. assumption.
Qed.
End XF.

Section IN.
Variables (XF WP : Z).
Variables rav spv gp tp t0v s0v s1v s3v a6v s6v s7v t6v : word.
Hypothesis X8 : XF mod 8 = 0.
Hypothesis W8 : WP mod 8 = 0.
Hypothesis SEPXW : XF + 32 <= WP \/ WP + 72 <= XF.

Definition RN8 (i : Z) (a0v a1v a2v a3v a4v t2v t3v s11v : word) (r : Z) : bvmap 5 word :=
mkR (Z_to_bv 64 r) spv gp tp t0v (Z_to_bv 64 (-4)) t2v s0v s1v
a0v a1v a2v a3v a4v (Z_to_bv 64 (18446744073709551615 - XF)) a6v (Z_to_bv 64 (18446744073709551615 - WP))
(Z_to_bv 64 8) s3v (Z_to_bv 64 WP) (Z_to_bv 64 XF) s6v s7v (Z_to_bv 64 SHB) (Z_to_bv 64 (16 * i)) (Z_to_bv 64 (8 * i + 4)) s11v
t3v (Z_to_bv 64 64) (Z_to_bv 64 (2 ^ 33)) t6v.

Definition in8_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a1' a2' a3' a4' t2' t3' s11' F' fc' m' (wd : list word),
ms' = MS (RN8 4 a0' a1' a2' a3' a4' t2' t3' s11' 8) F' (Z_to_bv 64 0xaeb60) fc' None m' (seg_rom bsegs)
/\ munch [(WP, WP + 64)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ length wd = 16%nat /\ rw_cells bsegs m' WP (f32 wd).

Lemma l2l8_in : forall (mI : mem) (k : nat) (xrest wrest wdone : list word) (xa xb n1 n2 n3 n4 : word) (i : Z)
(a0v a1v a2v a3v a4v t2v t3v s11v : word) F1 fc mc,
4 * i = Z.of_nat (length wdone) -> length xrest = (2 * k)%nat -> length wrest = (4 * k)%nat -> i + 1 + Z.of_nat k = 4 ->
aobj bsegs mI XF 32 -> aobj bsegs mI WP 72 -> offsh [(WP, WP + 64)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(WP, WP + 64)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (XF + 8 * i) (f32 (xa :: xb :: xrest)) ->
rw_cells bsegs mc WP (f32 wdone) -> rw_cells bsegs mc (WP + 16 * i) (f32 [n1; n2; n3; n4]) -> rw_cells bsegs mc (WP + 16 * i + 16) (f32 wrest) ->
evt bsegs (in8_post mI)
(MS (RN8 i a0v a1v a2v a3v a4v t2v t3v s11v (2 * i)) F1 (Z_to_bv 64 0xae9d4) fc None mc (seg_rom bsegs)).
Proof using X8 W8 SEPXW.
intros mI k.
induction k as [|k IH]; intros xrest wrest wdone xa xb n1 n2 n3 n4 i a0v a1v a2v a3v a4v t2v t3v s11v F1 fc mc
Hi LX LW HN OBX OBW OF FRM MI MU WM XC WD W4 WR;
pose proof OBX as (OX0 & OX1 & _); pose proof OBW as (OW0 & OW1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ XC) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ WD) as BWD; rewrite cells_size_f32 in BWD;
unfold RN8; rewrite !f32_cons, f32_nil in W4;
pose proof XC as XH; chunk_split_f32 XH at 2%nat as X2; rewrite ?f32_cons, ?f32_nil in X2; clear XH;
hide_disj.
-
destruct xrest; [|cbn in LX; lia]. destruct wrest; [|cbn in LW; lia].
bato 0xaea0c.
astep. chk_merge OBW 4.
bato 0xaea28.
assert (X4' : XF mod 4 = 0) by (clear - X8; Z.div_mod_to_equations; lia).
pose proof X2 as X2c. chunk_uncons X2c as XAc.
replace (XF + 8 * i) with (XF + (8 * i + 4) + -4) in XAc by lia. replace (XF + 8 * i + 4) with (XF + (8 * i + 4)) in X2c by lia.
astep. chk_merge OBX 4.
bato 0xaea3c. astep. chk_merge OBW 4.
bato 0xaea5c. astep. chk_merge OBX 4.
bato 0xaea70. astep. chk_merge OBW 4.
bato 0xaea88. astep. chk_merge OBW 4.
bato 0xaea94. astep. chk_merge OBW 4.
bato 0xaeaa4. astep. chk_merge OBW 4.
bato 0xaead8. astep. sh_if. astep.
chunk_cat WD W4. rewrite <- f32_nil, <- !f32_cons, <- f32_app in WD.
replace (16 * i + 16) with (16 * 4) by lia. replace (8 * i + 12) with (8 * 4 + 4) by lia. replace (2 * i + 2) with 8 by lia.
unfold in8_post, RN8. finish; [ | exact WD ].
rewrite length_app. cbn [length]. lia.
-
destruct xrest as [|xa' [|xb' xrest]]; try (cbn in LX; lia).
destruct wrest as [|n1' [|n2' [|n3' [|n4' wrest]]]]; try (cbn in LW; lia).
cbn [length] in LX, LW, BX.
bato 0xaea0c. astep. chk_merge OBW 4.
assert (X4' : XF mod 4 = 0) by (clear - X8; Z.div_mod_to_equations; lia).
pose proof X2 as X2c. chunk_uncons X2c as XAc.
replace (XF + 8 * i) with (XF + (8 * i + 4) + -4) in XAc by lia. replace (XF + 8 * i + 4) with (XF + (8 * i + 4)) in X2c by lia.
bato 0xaea28. astep. chk_merge OBX 4.
bato 0xaea3c. astep. chk_merge OBW 4.
bato 0xaea5c. astep. chk_merge OBX 4.
bato 0xaea70. astep. chk_merge OBW 4.
bato 0xaea88. astep. chk_merge OBW 4.
bato 0xaea94. astep. chk_merge OBW 4.
bato 0xaeaa4. astep. chk_merge OBW 4.
bato 0xaead8. astep. sh_if.
try clear XAc. try clear X2c.
chunk_cat WD W4. rewrite <- f32_nil, <- !f32_cons, <- f32_app in WD.
chunk_split_f32 XC at 2%nat as X0. clear X0. try clear X2.
chunk_split_f32 WR at 4%nat as W4'.
replace (XF + 8 * i + 4 * Z.of_nat 2) with (XF + 8 * (i + 1)) in * by lia. replace (XF + 8 * i + 8) with (XF + 8 * (i + 1)) in * by lia.
replace (WP + 16 * i + 16 + 4 * Z.of_nat 4) with (WP + 16 * (i + 1) + 16) in * by lia.
replace (WP + 16 * i + 16) with (WP + 16 * (i + 1)) in * by lia.
replace (16 * i + 16) with (16 * (i + 1)) by lia. replace (8 * i + 12) with (8 * (i + 1) + 4) by lia. replace (2 * i + 2) with (2 * (i + 1)) by lia.
cbn [firstn skipn] in W4', WR. rewrite ?f32_cons, ?f32_nil in W4'.
eapply (IH xrest wrest _ xa' xb' n1' n2' n3' n4' (i + 1)); try eassumption; try reflexivity.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia).
Qed.
End IN.

Lemma list4_8 : forall (l : list word), length l = 4%nat -> exists a b c d, l = [a; b; c; d].
Proof. intros l H. destruct l as [|a [|b [|c [|d [|? ?]]]]]; cbn in H; try lia. eauto. Qed.
Lemma list2_8 : forall (l : list word), length l = 2%nat -> exists a b, l = [a; b].
Proof. intros l H. destruct l as [|a [|b [|? ?]]]; cbn in H; try lia. eauto. Qed.
Lemma skipn_cons8 : forall (l : list word) (n : nat), (n < length l)%nat -> exists a r, skipn n l = a :: r /\ length r = (length l - n - 1)%nat.
Proof.
intros l n H. destruct (skipn n l) as [|a r] eqn:E.
- pose proof (length_skipn n l) as L. rewrite E in L. cbn in L. lia.
- exists a, r. split; [reflexivity|]. pose proof (length_skipn n l) as L. rewrite E in L. cbn [length] in L. lia.
Qed.

Section OUT.
Variables (XF WP AK : Z).
Variables rav spv gp tp s0v s1v : word.
Hypothesis X8 : XF mod 8 = 0.
Hypothesis W8 : WP mod 8 = 0.
Hypothesis A4 : AK mod 4 = 0.
Hypothesis AK0 : 0 < AK.
Hypothesis SEPXW : XF + 32 <= WP \/ WP + 72 <= XF.
Hypothesis SEPAW : AK + 32 <= WP \/ WP + 72 <= AK.
Hypothesis SEPAX : AK + 32 <= XF \/ XF + 32 <= AK.

Definition RO8 (jz : Z) (ra a0v a1v a2v a3v a4v t2v s9v s10v s11v t3v : word) : bvmap 5 word :=
mkR ra spv gp tp (Z_to_bv 64 1) (Z_to_bv 64 (-4)) t2v s0v s1v
a0v a1v a2v a3v a4v (Z_to_bv 64 (18446744073709551615 - XF)) (Z_to_bv 64 jz) (Z_to_bv 64 (18446744073709551615 - WP))
(Z_to_bv 64 8) (Z_to_bv 64 AK) (Z_to_bv 64 WP) (Z_to_bv 64 XF) (Z_to_bv 64 2147483647) (Z_to_bv 64 4) (Z_to_bv 64 SHB) s9v s10v s11v
t3v (Z_to_bv 64 64) (Z_to_bv 64 (2 ^ 33)) (Z_to_bv 64 1).

Definition out8_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists ra' a0' a1' a2' a3' a4' t2' s9' s10' s11' t3' F' fc' m' (ws' aks' : list word),
ms' = MS (RO8 9 ra' a0' a1' a2' a3' a4' t2' s9' s10' s11' t3') F' (Z_to_bv 64 0xaeccc) fc' None m' (seg_rom bsegs)
/\ munch [(WP, WP + 72); (AK, AK + 32)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ length ws' = 18%nat /\ rw_cells bsegs m' WP (f32 ws') /\ length aks' = 8%nat /\ rw_cells bsegs m' AK (f32 aks').

Ltac out8_prefix jz mI mc xs ws WC LW XC LX OBX OBW MU OF a0v a1v a2v a3v a4v t2v t3v s11v :=
let W20 := fresh "W20" in let W2 := fresh "W2" in let W4 := fresh "W4" in let WR := fresh "WR" in
destruct (f32_split bsegs mc WP ws 16 ltac:(lia) WC) as [W20 W2];
destruct (f32_split bsegs mc WP (firstn 16 ws) 4 ltac:(rewrite length_firstn; lia) W20) as [W4 WR];
let n1 := fresh "n1" in let n2 := fresh "n2" in let n3 := fresh "n3" in let n4 := fresh "n4" in let E4 := fresh "E4" in
destruct (list4_8 (firstn 4 (firstn 16 ws)) ltac:(rewrite !length_firstn; lia)) as (n1 & n2 & n3 & n4 & E4); rewrite E4 in W4;
let w20 := fresh "w20" in let w21 := fresh "w21" in let E2 := fresh "E2" in
destruct (list2_8 (skipn 16 ws) ltac:(rewrite length_skipn; lia)) as (w20 & w21 & E2); rewrite E2 in W2;
let LWR := fresh "LWR" in
assert (LWR : length (skipn 4 (firstn 16 ws)) = (4 * 3)%nat) by (rewrite length_skipn, length_firstn; lia);
let xa := fresh "xa" in let xb := fresh "xb" in let xrest := fresh "xrest" in
destruct xs as [|xa [|xb xrest]]; try (cbn in LX; lia); cbn [length] in LX;
clear W20 WC; unfold RO8;
bato 0xae9d4;
(lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (RN8 XF WP spv gp tp (Z_to_bv 64 1) s0v s1v (Z_to_bv 64 AK) (Z_to_bv 64 jz) (Z_to_bv 64 2147483647) (Z_to_bv 64 4) (Z_to_bv 64 1)
0 a0v a1v a2v a3v a4v t2v t3v s11v (2 * 0))
by (unfold RN8; reflexivity) end);
let OBXc := fresh "OBXc" in let OBWc := fresh "OBWc" in let OFc := fresh "OFc" in let MU0 := fresh "MU0" in let WM0 := fresh "WM0" in
let WD0 := fresh "WD0" in let XC0 := fresh "XC0" in
pose proof (aobj_munch bsegs _ mI mc XF 32 OBX MU (shfree_of_aobj bsegs _ mI XF 32 OF OBX)) as OBXc;
pose proof (aobj_munch bsegs _ mI mc WP 72 OBW MU (shfree_of_aobj bsegs _ mI WP 72 OF OBW)) as OBWc;
assert (OFc : offsh [(WP, WP + 64)]) by (cbn in OF |- *; unfold hid in *; unfold SH_LO, SH_HI in *; lia);
pose proof (munch_refl [(WP, WP + 64)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (WD0 : rw_cells bsegs mc WP (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XC as XC0; replace XF with (XF + 8 * 0) in XC0 at 1 by lia;
replace WP with (WP + 16 * 0) in W4 at 1 by lia;
replace (WP + 4 * Z.of_nat 4) with (WP + 16 * 0 + 16) in WR by lia;
call (l2l8_in XF WP spv gp tp (Z_to_bv 64 1) s0v s1v (Z_to_bv 64 AK) (Z_to_bv 64 jz) (Z_to_bv 64 2147483647) (Z_to_bv 64 4) (Z_to_bv 64 1) X8 W8 SEPXW
mc 3%nat xrest (skipn 4 (firstn 16 ws)) [] xa xb n1 n2 n3 n4 0);
[ reflexivity | cbn [length] in *; lia | exact LWR | reflexivity | exact OBXc | exact OBWc | exact OFc
| eassumption | eassumption | exact MU0 | exact WM0 | exact XC0 | exact WD0 | exact W4 | exact WR | ];
clear MU0 WM0 OBXc OBWc OFc; try clear WD0; try clear XC0;
unfold RN8; change (16 * 4) with 64; change (4 * Z.of_nat 16) with 64 in W2; rewrite !f32_cons, f32_nil in W2;
let WA80 := fresh "WA80" in
assert (WA80 : (WP + 64) mod 4 = 0) by (clear - W8; Z.div_mod_to_equations; lia);
bato 0xaeb9c; rewrite (land_m4_al8 (WP + 60)) by (lia || (clear - W8; Z.div_mod_to_equations; lia));
bato 0xaebac.

Ltac out8_ak jz aks AC OBA :=
bato 0xaebd0; replace (jz * 4 + AK + -4) with (AK + -4 + 4 * jz) by lia;
bato 0xaebf0; astep; chk_merge OBA 4;
let A1 := fresh "A1" in let A2 := fresh "A2" in
destruct (f32_split bsegs _ AK aks (Z.to_nat (jz - 1)) ltac:(lia) AC) as [A1 A2];
let av := fresh "av" in let ar := fresh "ar" in let EA := fresh "EA" in let LAR := fresh "LAR" in
destruct (skipn_cons8 aks (Z.to_nat (jz - 1)) ltac:(lia)) as (av & ar & EA & LAR); rewrite EA in A2; rewrite f32_cons in A2;
let L1 := fresh "L1" in
assert (L1 : length (firstn (Z.to_nat (jz - 1)) aks) = Z.to_nat (jz - 1)) by (rewrite length_firstn; lia);
let A2h := fresh "A2h" in
chunk_uncons A2 as A2h;
replace (AK + 4 * Z.of_nat (Z.to_nat (jz - 1))) with (AK + -4 + 4 * jz) in * by lia;
clear AC;
bato 0xaec08;
chunk_snoc A1 A2h;
bato 0xaec44.
Ltac out8_join :=
(match goal with A1 : rw_cells _ _ AK _, A2 : rw_cells _ _ (AK + -4 + 4 * _ + 4) _ |- _ =>
chunk_cat A1 A2; rewrite <- (f32_nil), <- f32_cons, <- !f32_app in A1 end);
(match goal with W2 : rw_cells _ _ (WP + 64) _ |- _ => rewrite <- f32_nil, <- !f32_cons in W2 end);
(match goal with WD : rw_cells _ _ WP (f32 ?l), PL : length ?l = 16%nat, W2 : rw_cells _ _ (WP + 64) _ |- _ =>
pose proof (f32_join bsegs _ WP l _ WD ltac:(rewrite PL; exact W2)) as WJ end).

Lemma l2l8_out : forall (mI : mem) (k : nat) (jz : Z) (xs ws aks : list word) ra a0v a1v a2v a3v a4v t2v s9v s10v s11v t3v F1 fc mc,
jz + Z.of_nat k = 8 -> 0 <= jz ->
length xs = 8%nat -> length ws = 18%nat -> length aks = 8%nat ->
aobj bsegs mI XF 32 -> aobj bsegs mI WP 72 -> aobj bsegs mI AK 32 -> offsh [(WP, WP + 72); (AK, AK + 32)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(WP, WP + 72); (AK, AK + 32)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc XF (f32 xs) -> rw_cells bsegs mc WP (f32 ws) -> rw_cells bsegs mc AK (f32 aks) ->
evt bsegs (out8_post mI)
(MS (RO8 jz ra a0v a1v a2v a3v a4v t2v s9v s10v s11v t3v) F1 (Z_to_bv 64 0xae9c0) fc None mc (seg_rom bsegs)).
Proof using X8 W8 A4 AK0 SEPXW SEPAW SEPAX.
intros mI k.
induction k as [|k IH]; intros jz xs ws aks ra a0v a1v a2v a3v a4v t2v s9v s10v s11v t3v F1 fc mc
HJ J0 LX LW LA OBX OBW OBA OF FRM MI MU WM XC WC AC;
pose proof OBX as (OX0 & OX1 & _); pose proof OBW as (OW0 & OW1 & _); pose proof OBA as (OA0 & OA1 & _); unfold APP_TOP in *;
hide_disj.
-
out8_prefix jz mI mc xs ws WC LW XC LX OBX OBW MU OF a0v a1v a2v a3v a4v t2v t3v s11v.
astep. sh_if.
out8_ak jz aks AC OBA.
bato 0xaec50. rewrite ?swrap32_small by lia. astep. sh_if. astep.
out8_join.
replace (jz + 1) with 9 by lia.
unfold out8_post, RO8. finish; [ | exact WJ | | exact A1 ].
+ rewrite length_app. cbn [length]. lia.
+ rewrite !length_app. cbn [length]. lia.
- out8_prefix jz mI mc xs ws WC LW XC LX OBX OBW MU OF a0v a1v a2v a3v a4v t2v t3v s11v.
astep. if_cases KJ; zify_cond KJ.
+
bato 0xaec50. rewrite ?swrap32_small by lia. astep. sh_if.
rewrite <- f32_nil, <- !f32_cons in W2.
match goal with WD : rw_cells _ _ WP (f32 ?l), PL : length ?l = 16%nat |- _ =>
pose proof (f32_join bsegs _ WP l _ WD ltac:(rewrite PL; exact W2)) as WJ end.
match goal with XC' : rw_cells _ _ XF (f32 ?xl), WJ' : rw_cells _ _ WP (f32 ?wl), AC' : rw_cells _ _ AK (f32 ?al) |- _ =>
eapply (IH (jz + 1) xl wl al); try eassumption; try reflexivity end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
+
out8_ak jz aks AC OBA.
bato 0xaec50. rewrite ?swrap32_small by lia. astep. sh_if.
out8_join.
match goal with XC' : rw_cells _ _ XF (f32 ?xl), WJ' : rw_cells _ _ WP (f32 ?wl), AC' : rw_cells _ _ AK (f32 ?al) |- _ =>
eapply (IH (jz + 1) xl wl al); try eassumption; try reflexivity end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End OUT.

Definition l2l8_body_stmt : Prop :=
forall (IQ AK usp lo : Z) (qs aks ws : list word) (jx : list byte) (j1 j2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells bsegs m (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m (usp + -256) (f32 ws) -> length ws = 18%nat -> rw_cells bsegs m (usp + -352) [CB 32 jx] ->
rw_cells bsegs m IQ (f32 qs) -> length qs = 8%nat -> rw_cells bsegs m AK (f32 aks) -> length aks = 8%nat ->
aobj bsegs m (usp + -256) 72 -> aobj bsegs m (usp + -352) 32 -> aobj bsegs m IQ 32 -> aobj bsegs m AK 32 ->
(IQ + 32 <= lo \/ usp <= IQ) -> (AK + 32 <= lo \/ usp <= AK) -> (AK + 32 <= IQ \/ IQ + 32 <= AK) ->
(AK + 32 <= SH_LO \/ SH_HI <= AK) -> IQ mod 4 = 0 -> AK mod 4 = 0 -> usp mod 32 = 0 -> 0 < IQ -> 0 < AK -> IQ + 32 <= APP_TOP -> AK + 32 <= APP_TOP ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> X1cn.frm0 fc ->
evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
(F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (aks' : list word) (jw jx' : list byte),
ms' = MS (mkR ra' (Z_to_bv 64 (usp + -384)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
F' (Z_to_bv 64 A_l2l_epi) fc' None m' (seg_rom bsegs)
/\ munch [(usp + -352, usp + -320); (usp + -256, usp + -184); (usp + -128, usp + -120); (AK, AK + 32)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ X1cn.frm0 fc'
/\ rw_cells bsegs m' (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -384)) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m' (usp + -256) [CB 72 jw] /\ rw_cells bsegs m' (usp + -352) [CB 32 jx']
/\ rw_cells bsegs m' IQ (f32 qs) /\ rw_cells bsegs m' AK (f32 aks') /\ length aks' = 8%nat)
(MS (mkR (Z_to_bv 64 RA_l2l_pois2) (Z_to_bv 64 (usp + -384)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 AK) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -352)) (Z_to_bv 64 IQ) (Z_to_bv 64 4) (Z_to_bv 64 SHB)
(Z_to_bv 64 (usp + -384)) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_l2l_pois2)) fc None m (seg_rom bsegs)).

Lemma l2l8_body : l2l8_body_stmt.
Proof.
intros IQ AK usp lo qs aks ws jx j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 F fc m
FR WP LWS XF X LQ A LA OBW OBX OBQ OBA APQ APA SEP ASH Q4 A4 U32 IQ0 AK0 IQT AKT LO LOS SPH MI FRM.
unfold RA_l2l_pois2, A_l2l_epi, l2l_frame in *.
replace (ret_pc (Z_to_bv 64 0xae858)) with (Z_to_bv 64 0xae858) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold APP_TOP in *.
pose proof (munch_refl [(usp + -352, usp + -320); (usp + -256, usp + -184); (usp + -128, usp + -120); (AK, AK + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -352, usp + -320); (usp + -256, usp + -184); (usp + -128, usp + -120); (AK, AK + 32)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (SEPQX : IQ + 32 <= usp + -352 \/ usp + -352 + 32 <= IQ) by lia.
assert (X4 : (usp + -352) mod 4 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (X8 : (usp + -352) mod 8 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (W8 : (usp + -256) mod 8 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (SEPXW : usp + -352 + 32 <= usp + -256 \/ usp + -256 + 72 <= usp + -352) by lia.
assert (SEPAW : AK + 32 <= usp + -256 \/ usp + -256 + 72 <= AK) by lia.
assert (SEPAX : AK + 32 <= usp + -352 \/ usp + -352 + 32 <= AK) by lia.
destruct (rw_cells_CB_f32 bsegs _ _ 8%nat _ XF) as (xf & Lxf & XF'); clear XF.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. destruct xf as [|x0 xf]; [cbn in Lxf; lia|]. cbn [length] in LQ, Lxf.
assert (E9 : Z.of_nat (S (length qs)) = 8) by lia.
hide_disj.
bato 0xae8ac.
replace (0 <? IQ) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. rewrite zb_lxor_ones by lia.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (RX8 IQ (usp + -352) (Z_to_bv 64 0xae858) (Z_to_bv 64 (usp + -384)) gp tp t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 8) (Z_to_bv 64 AK) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 4) (Z_to_bv 64 (usp + -384)) s10 s11 t3 t4 t5 t6
0 t0 t1 (Z.of_nat (S (length qs))))
by (unfold RX8; rewrite E9, !Z.mul_0_r, !Z.add_0_r; reflexivity) end.
pose proof (aobj_munch bsegs _ m _ IQ 32 OBQ MU (shfree_of_aobj bsegs _ m IQ 32 OF OBQ)) as OBQc.
pose proof (aobj_munch bsegs _ m _ (usp + -352) 32 OBX MU (shfree_of_aobj bsegs _ m (usp + -352) 32 OF OBX)) as OBXc.
assert (OFc : offsh [(usp + -352, usp + -352 + 32)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(usp + -352, usp + -352 + 32)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc (usp + -352) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia) end.
pose proof X as QC0. replace IQ with (IQ + 4 * 0) in QC0 at 1 by lia.
replace (usp + -352) with (usp + -352 + 4 * 0) in XF' at 1 by lia.
lazymatch type of MU with munch _ _ ?mc =>
call (l2l8_xf IQ (usp + -352) (Z_to_bv 64 0xae858) (Z_to_bv 64 (usp + -384)) gp tp t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
(Z_to_bv 64 8) (Z_to_bv 64 AK) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 4) (Z_to_bv 64 (usp + -384)) s10 s11 t3 t4 t5 t6
Q4 X4 IQ0 SEPQX mc qs xf [] q0 x0 0);
[ reflexivity | lia | lia | exact OBQc | exact OBXc | exact OFc | eassumption | eassumption | exact MU0 | exact WM0 | exact QC0 | exact XD0 | exact XF' | ] end.
clear MU0 WM0 OBQc OBXc OFc; try clear XD0; try clear QC0.
unfold RX8. bato 0xae9c0.
replace (0 <? AK) with true by (symmetry; apply Z.ltb_lt; lia). rewrite (land3_al AK A4). cbn [Z.b2z]. alits.
rewrite zb_lxor_ones by lia.
pose proof (aobj_munch bsegs _ m _ (usp + -352) 32 OBX MU (shfree_of_aobj bsegs _ m (usp + -352) 32 OF OBX)) as OBXc.
pose proof (aobj_munch bsegs _ m _ (usp + -256) 72 OBW MU (shfree_of_aobj bsegs _ m (usp + -256) 72 OF OBW)) as OBWc.
pose proof (aobj_munch bsegs _ m _ AK 32 OBA MU (shfree_of_aobj bsegs _ m AK 32 OF OBA)) as OBAc.
assert (OFc : offsh [(usp + -256, usp + -256 + 72); (AK, AK + 32)]) by (cbn in OF |- *; unfold hid in *; unfold SH_LO, SH_HI in *; lia).
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(usp + -256, usp + -256 + 72); (AK, AK + 32)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
match goal with XP : rw_cells _ mc (usp + -352) (f32 ?xl), LXP : length ?xl = 8%nat |- _ =>
call (l2l8_out (usp + -352) (usp + -256) AK (Z_to_bv 64 (usp + -384)) gp tp (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
X8 W8 A4 AK0 SEPXW SEPAW SEPAX mc 8%nat 0 xl ws aks);
[ reflexivity | lia | exact LXP | exact LWS | exact LA | exact OBXc | exact OBWc | exact OBAc | exact OFc
| eassumption | eassumption | exact MU0 | exact WM0 | exact XP | exact WP | exact A | ] end end.
clear MU0 WM0 OBXc OBWc OBAc OFc.
match goal with WF : rw_cells _ _ (usp + -256) (f32 ?wl), LWF : length ?wl = 18%nat, XF2 : rw_cells _ _ (usp + -352) (f32 ?xl), LXF : length ?xl = 8%nat |- _ =>
apply rw_cells_f32_CB in WF; rewrite LWF in WF; change (4 * 18)%nat with 72%nat in WF;
apply rw_cells_f32_CB in XF2; rewrite LXF in XF2; change (4 * 8)%nat with 32%nat in XF2 end.
unfold RO8.
apply evt_done. do 32 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
