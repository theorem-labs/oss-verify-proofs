(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X089.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Section XF.
Variables (IQ XF : Z).
Variables rav spv gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2v s3v s4v s5v s8v s10v s11 t3 t4 t5 t6 : word.
Hypothesis Q4 : IQ mod 4 = 0.
Hypothesis X4 : XF mod 4 = 0.
Hypothesis SEPQX : IQ + 40 <= XF \/ XF + 40 <= IQ.

Definition RX (i : Z) (a3v a4v : word) (kz : Z) : bvmap 5 word :=
mkR rav spv gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (IQ + 4 * i)) (Z_to_bv 64 (XF + 4 * i)) (Z_to_bv 64 (XF + 4 * i)) a3v a4v a5 a6 a7
s2v s3v s4v s5v (Z_to_bv 64 (IQ + 4 * i)) (Z_to_bv 64 SHB) s8v (Z_to_bv 64 kz) s10v s11 t3 t4 t5 t6.

Definition xf_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a3' a4' F' fc' m' (xs' : list word),
ms' = MS (RX 10 a3' a4' 0) F' (Z_to_bv 64 0xa9840) fc' None m' (seg_rom asegs)
/\ munch [(XF, XF + 40)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ length xs' = 10%nat /\ rw_cells asegs m' XF (f32 xs').

Lemma l2l_xf : forall (mI : mem) (qrest xrest xdone : list word) (q x : word) (i : Z) (a3v a4v : word) F1 fc mc,
i = Z.of_nat (length xdone) -> length qrest = length xrest -> i + 1 + Z.of_nat (length qrest) = 10 ->
aobj asegs mI IQ 40 -> aobj asegs mI XF 40 -> offsh [(XF, XF + 40)] ->
frm0 fc -> mem_inv asegs mc -> munch [(XF, XF + 40)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc (IQ + 4 * i) (f32 (q :: qrest)) ->
rw_cells asegs mc XF (f32 xdone) -> rw_cells asegs mc (XF + 4 * i) (f32 (x :: xrest)) ->
evt asegs (xf_post mI)
(MS (RX i a3v a4v (Z.of_nat (S (length qrest)))) F1 (Z_to_bv 64 0xa979c) fc None mc (seg_rom asegs)).
Proof using Q4 X4 SEPQX.
intros mI qrest.
induction qrest as [|q' qrest IH]; intros xrest xdone q x i a3v a4v F1 fc mc Hi LQ HN OBQ OBX OF FRM MI MU WM QC XD XC;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ QC) as BQ; rewrite cells_size_f32 in BQ; cbn [length] in BQ;
pose proof (rw_cells_bound _ _ _ _ XC) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ XD) as BXD; rewrite cells_size_f32 in BXD;
unfold RX; rewrite !f32_cons in XC;
pose proof QC as QH; chunk_split_f32 QH at 1%nat as Q1; rewrite ?f32_cons, ?f32_nil in Q1; clear QH.
-
destruct xrest; [|cbn in LQ; lia]. cbn [length] in HN. rewrite f32_nil in XC.
assert (K : forall (F2 : bvmap 5 word) (a3' a4' : word) fc2, frm0 fc2 ->
evt asegs (xf_post mI) (MS (RX i a3' a4' (Z.of_nat 1)) F2 (Z_to_bv 64 0xa97ec) fc2 None mc (seg_rom asegs))).
{ intros F2 a3' a4' fc2 FRM2. unfold RX.
ato 0xa97f8. astep. chk_merge OBX 4.
ato 0xa9814. astep. sh_if.
chunk_snoc XD XC. rewrite <- f32_nil, <- f32_cons, <- f32_app in XD.
replace (IQ + 4 * i + 4) with (IQ + 4 * 10) by lia. replace (XF + 4 * i + 4) with (XF + 4 * 10) by lia.
unfold xf_post, RX. finish; [ | exact XD ].
rewrite length_app. cbn [length]. lia. }
ato 0xa97a8. astep. chk_merge OBQ 4.
ato 0xa97b8. astep. if_cases KB.
+ ato 0xa97ec. apply K. assumption.
+ ato 0xa97ec. apply K. assumption.
-
destruct xrest as [|x' xrest]; [cbn in LQ; lia|]. cbn [length] in HN, LQ, BQ, BX.
assert (K : forall (F2 : bvmap 5 word) (a3' a4' : word) fc2, frm0 fc2 ->
evt asegs (xf_post mI) (MS (RX i a3' a4' (Z.of_nat (S (S (length qrest))))) F2 (Z_to_bv 64 0xa97ec) fc2 None mc (seg_rom asegs))).
{ intros F2 a3' a4' fc2 FRM2. unfold RX.
ato 0xa97f8. astep. chk_merge OBX 4.
ato 0xa9814. astep. sh_if.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in XD.
chunk_split_f32 QC at 1%nat as Q0. clear Q0 Q1.
rewrite <- ?f32_cons in XC.
astep.
replace (IQ + 4 * i + 4) with (IQ + 4 * (i + 1)) in * by lia. replace (XF + 4 * i + 4) with (XF + 4 * (i + 1)) in * by lia.
replace (Z.of_nat (S (S (length qrest))) + -1) with (Z.of_nat (S (length qrest))) by lia.
eapply (IH xrest _ q' x' (i + 1)); try eassumption; try reflexivity.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia). }
ato 0xa97a8. astep. chk_merge OBQ 4.
ato 0xa97b8. astep. if_cases KB.
+ ato 0xa97ec. apply K. assumption.
+ ato 0xa97ec. apply K. assumption.
Qed.
End XF.

Section IN.
Variables (XF WP : Z).
Variables rav spv gp tp s0v s1v a5v s5v : word.
Hypothesis X8 : XF mod 8 = 0.
Hypothesis W8 : WP mod 8 = 0.
Hypothesis SEPXW : XF + 40 <= WP \/ WP + 88 <= XF.

Definition RN (i : Z) (a1v a2v a3v a4v s6v s8v s9v s10v s11v : word) (kz : Z) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 5) (Z_to_bv 64 (Z.shiftr XF 3 + SHB)) (Z_to_bv 64 11) s0v s1v
(Z_to_bv 64 (XF + 8 * i)) a1v a2v a3v a4v a5v (Z_to_bv 64 (XF + 4)) (Z_to_bv 64 2)
(Z_to_bv 64 10) (Z_to_bv 64 WP) (Z_to_bv 64 XF) s5v s6v (Z_to_bv 64 SHB) s8v s9v s10v s11v
(Z_to_bv 64 (16 * i)) (Z_to_bv 64 kz) (Z_to_bv 64 (Z.shiftr (XF + 8 * i) 3 + SHB)) (Z_to_bv 64 (XF + 8 * i + 4)).

Definition in_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' a2' a3' a4' s6' s8' s9' s10' s11' F' fc' m' (wd : list word),
ms' = MS (RN 5 a1' a2' a3' a4' s6' s8' s9' s10' s11' 0) F' (Z_to_bv 64 0xa9a28) fc' None m' (seg_rom asegs)
/\ munch [(WP, WP + 80)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ length wd = 20%nat /\ rw_cells asegs m' WP (f32 wd).

Ltac in_checks OBX OBW :=
ato 0xa98b8; astep; chk_merge OBX 4;
ato 0xa98d0; astep; chk_merge OBW 4;
ato 0xa98e8; astep; chk_merge OBW 4;
ato 0xa9900; astep; chk_merge OBX 4;
ato 0xa9918; astep; chk_merge OBW 4;
ato 0xa9930; astep; chk_merge OBW 4;
ato 0xa993c; astep; chk_merge OBW 4;
ato 0xa994c; astep; chk_merge OBW 4;
ato 0xa9958; astep; chk_merge OBW 4.

Lemma l2l_in : forall (mI : mem) (k : nat) (xrest wrest wdone : list word) (xa xb n1 n2 n3 n4 : word) (i : Z)
(a1v a2v a3v a4v s6v s8v s9v s10v s11v : word) F1 fc mc,
4 * i = Z.of_nat (length wdone) -> length xrest = (2 * k)%nat -> length wrest = (4 * k)%nat -> i + 1 + Z.of_nat k = 5 ->
aobj asegs mI XF 40 -> aobj asegs mI WP 88 -> offsh [(WP, WP + 80)] ->
frm0 fc -> mem_inv asegs mc -> munch [(WP, WP + 80)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc (XF + 8 * i) (f32 (xa :: xb :: xrest)) ->
rw_cells asegs mc WP (f32 wdone) -> rw_cells asegs mc (WP + 16 * i) (f32 [n1; n2; n3; n4]) -> rw_cells asegs mc (WP + 16 * i + 16) (f32 wrest) ->
evt asegs (in_post mI)
(MS (RN i a1v a2v a3v a4v s6v s8v s9v s10v s11v (Z.of_nat (S k))) F1 (Z_to_bv 64 0xa98b4) fc None mc (seg_rom asegs)).
Proof using X8 W8 SEPXW.
intros mI k.
induction k as [|k IH]; intros xrest wrest wdone xa xb n1 n2 n3 n4 i a1v a2v a3v a4v s6v s8v s9v s10v s11v F1 fc mc
Hi LX LW HN OBX OBW OF FRM MI MU WM XC WD W4 WR;
pose proof OBX as (OX0 & OX1 & _); pose proof OBW as (OW0 & OW1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ XC) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ WD) as BWD; rewrite cells_size_f32 in BWD;
unfold RN; rewrite !f32_cons, f32_nil in W4;
pose proof XC as XH; chunk_split_f32 XH at 2%nat as X2; rewrite ?f32_cons, ?f32_nil in X2; clear XH;
hide_disj.
-
destruct xrest; [|cbn in LX; lia]. destruct wrest; [|cbn in LW; lia].
in_checks OBX OBW.
ato 0xa9990. astep. sh_if. astep.
chunk_cat WD W4. rewrite <- f32_nil, <- !f32_cons, <- f32_app in WD.
replace (XF + 8 * i + 8) with (XF + 8 * 5) by lia. replace (16 * i + 16) with (16 * 5) by lia.
replace (Z.shiftr (XF + 8 * i) 3 + SHB + 1) with (Z.shiftr (XF + 8 * 5) 3 + SHB)
by (replace (XF + 8 * 5) with (XF + 8 * i + 8 * 1) by lia; rewrite shiftr3_add; lia).
replace (XF + 8 * i + 12) with (XF + 8 * 5 + 4) by lia.
unfold in_post, RN. finish; [ | exact WD ].
rewrite length_app. cbn [length]. lia.
-
destruct xrest as [|xa' [|xb' xrest]]; try (cbn in LX; lia).
destruct wrest as [|n1' [|n2' [|n3' [|n4' wrest]]]]; try (cbn in LW; lia).
cbn [length] in LX, LW, BX.
in_checks OBX OBW.
ato 0xa9990. astep. sh_if.
chunk_cat WD W4. rewrite <- f32_nil, <- !f32_cons, <- f32_app in WD.
chunk_split_f32 XC at 2%nat as X0. clear X0. try clear X2.
chunk_split_f32 WR at 4%nat as W4'.
replace (XF + 8 * i + 8) with (XF + 8 * (i + 1)) in * by lia. replace (16 * i + 16) with (16 * (i + 1)) in * by lia.
replace (Z.shiftr (XF + 8 * i) 3 + SHB + 1) with (Z.shiftr (XF + 8 * (i + 1)) 3 + SHB)
by (replace (XF + 8 * (i + 1)) with (XF + 8 * i + 8 * 1) by lia; rewrite shiftr3_add; lia).
replace (XF + 8 * i + 12) with (XF + 8 * (i + 1) + 4) by lia.
replace (WP + 16 * i + 16) with (WP + 16 * (i + 1)) in * by lia.
replace (Z.of_nat (S (S k)) + -1) with (Z.of_nat (S k)) by lia.
eapply (IH xrest wrest _ xa' xb' n1' n2' n3' n4' (i + 1)); try eassumption; try reflexivity.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia).
Qed.
End IN.

Lemma list4 : forall (l : list word), length l = 4%nat -> exists a b c d, l = [a; b; c; d].
Proof. intros l H. destruct l as [|a [|b [|c [|d [|? ?]]]]]; cbn in H; try lia. eauto. Qed.
Lemma list2 : forall (l : list word), length l = 2%nat -> exists a b, l = [a; b].
Proof. intros l H. destruct l as [|a [|b [|? ?]]]; cbn in H; try lia. eauto. Qed.

Lemma skipn_cons : forall (l : list word) (n : nat), (n < length l)%nat -> exists a r, skipn n l = a :: r /\ length r = (length l - n - 1)%nat.
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
Hypothesis SEPXW : XF + 40 <= WP \/ WP + 88 <= XF.
Hypothesis SEPAW : AK + 40 <= WP \/ WP + 88 <= AK.
Hypothesis SEPAX : AK + 40 <= XF \/ XF + 40 <= AK.

Definition RO (jz : Z) (a0v a1v a2v a3v a4v s6v s8v s9v s10v s11v t3v t4v t5v t6v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 5) (Z_to_bv 64 (Z.shiftr XF 3 + SHB)) (Z_to_bv 64 11) s0v s1v
a0v a1v a2v a3v a4v (Z_to_bv 64 jz) (Z_to_bv 64 (XF + 4)) (Z_to_bv 64 2)
(Z_to_bv 64 10) (Z_to_bv 64 WP) (Z_to_bv 64 XF) (Z_to_bv 64 (AK + -4)) s6v (Z_to_bv 64 SHB) s8v s9v s10v s11v
t3v t4v t5v t6v.

Ltac out_prefix jz mI mc xs ws WC LW XC LX OBX OBW MU OF a1v a2v a3v a4v s6v s8v s9v s10v s11v :=
let W20 := fresh "W20" in let W2 := fresh "W2" in let W4 := fresh "W4" in let WR := fresh "WR" in
destruct (f32_split asegs mc WP ws 20 ltac:(lia) WC) as [W20 W2];
destruct (f32_split asegs mc WP (firstn 20 ws) 4 ltac:(rewrite length_firstn; lia) W20) as [W4 WR];
let n1 := fresh "n1" in let n2 := fresh "n2" in let n3 := fresh "n3" in let n4 := fresh "n4" in let E4 := fresh "E4" in
destruct (list4 (firstn 4 (firstn 20 ws)) ltac:(rewrite !length_firstn; lia)) as (n1 & n2 & n3 & n4 & E4); rewrite E4 in W4;
let w20 := fresh "w20" in let w21 := fresh "w21" in let E2 := fresh "E2" in
destruct (list2 (skipn 20 ws) ltac:(rewrite length_skipn; lia)) as (w20 & w21 & E2); rewrite E2 in W2;
let LWR := fresh "LWR" in
assert (LWR : length (skipn 4 (firstn 20 ws)) = (4 * 4)%nat) by (rewrite length_skipn, length_firstn; lia);
let xa := fresh "xa" in let xb := fresh "xb" in let xrest := fresh "xrest" in
destruct xs as [|xa [|xb xrest]]; try (cbn in LX; lia); cbn [length] in LX;
clear W20 WC; unfold RO;
ato 0xa98b4;
(lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (RN XF WP rav spv gp tp s0v s1v (Z_to_bv 64 jz) (Z_to_bv 64 (AK + -4)) 0 a1v a2v a3v a4v s6v s8v s9v s10v s11v (Z.of_nat 5))
by (unfold RN; rewrite !Z.mul_0_r, !Z.add_0_r; reflexivity) end);
let OBXc := fresh "OBXc" in let OBWc := fresh "OBWc" in let OFc := fresh "OFc" in let MU0 := fresh "MU0" in let WM0 := fresh "WM0" in
let WD0 := fresh "WD0" in let XC0 := fresh "XC0" in
pose proof (aobj_munch asegs _ mI mc XF 40 OBX MU (shfree_of_aobj asegs _ mI XF 40 OF OBX)) as OBXc;
pose proof (aobj_munch asegs _ mI mc WP 88 OBW MU (shfree_of_aobj asegs _ mI WP 88 OF OBW)) as OBWc;
assert (OFc : offsh [(WP, WP + 80)]) by (cbn in OF |- *; unfold hid in *; unfold SH_LO, SH_HI in *; lia);
pose proof (munch_refl [(WP, WP + 80)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (WD0 : rw_cells asegs mc WP (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XC as XC0; replace XF with (XF + 8 * 0) in XC0 at 1 by lia;
replace WP with (WP + 16 * 0) in W4 at 1 by lia;
replace (WP + 4 * Z.of_nat 4) with (WP + 16 * 0 + 16) in WR by lia;
call (l2l_in XF WP rav spv gp tp s0v s1v (Z_to_bv 64 jz) (Z_to_bv 64 (AK + -4)) X8 W8 SEPXW mc 4%nat xrest (skipn 4 (firstn 20 ws)) [] xa xb n1 n2 n3 n4 0);
[ reflexivity | cbn [length] in *; lia | exact LWR | reflexivity | exact OBXc | exact OBWc | exact OFc
| eassumption | eassumption | exact MU0 | exact WM0 | exact XC0 | exact WD0 | exact W4 | exact WR | ];
clear MU0 WM0 OBXc OBWc OFc; try clear WD0; try clear XC0;
unfold RN; change (16 * 5) with 80; change (4 * Z.of_nat 20) with 80 in W2; rewrite !f32_cons, f32_nil in W2.

Ltac out_ak jz aks AC OBA :=
ato 0xa9a64; replace (Z.shiftl jz 2) with (4 * jz) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
ato 0xa9a78; astep; chk_merge OBA 4;
let A1 := fresh "A1" in let A2 := fresh "A2" in
destruct (f32_split asegs _ AK aks (Z.to_nat (jz - 1)) ltac:(lia) AC) as [A1 A2];
let av := fresh "av" in let ar := fresh "ar" in let EA := fresh "EA" in let LAR := fresh "LAR" in
destruct (skipn_cons aks (Z.to_nat (jz - 1)) ltac:(lia)) as (av & ar & EA & LAR); rewrite EA in A2; rewrite f32_cons in A2;
let L1 := fresh "L1" in
assert (L1 : length (firstn (Z.to_nat (jz - 1)) aks) = Z.to_nat (jz - 1)) by (rewrite length_firstn; lia);
let A2h := fresh "A2h" in
chunk_uncons A2 as A2h;
replace (AK + 4 * Z.of_nat (Z.to_nat (jz - 1))) with (AK + -4 + 4 * jz) in * by lia;
clear AC;
ato 0xa9a90;
chunk_snoc A1 A2h.
Ltac out_join :=
(match goal with A1 : rw_cells _ _ AK _, A2 : rw_cells _ _ (AK + -4 + 4 * _ + 4) _ |- _ =>
chunk_cat A1 A2; rewrite <- (f32_nil), <- f32_cons, <- !f32_app in A1 end);
(match goal with W2 : rw_cells _ _ (WP + 80) _ |- _ => rewrite <- f32_nil, <- !f32_cons in W2 end);
(match goal with WD : rw_cells _ _ WP (f32 ?l), PL : length ?l = 20%nat, W2 : rw_cells _ _ (WP + 80) _ |- _ =>
pose proof (f32_join asegs _ WP l _ WD ltac:(rewrite PL; exact W2)) as WJ end).

Definition out_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a1' a2' a3' a4' s6' s8' s9' s10' s11' t3' t4' t5' t6' F' fc' m' (ws' aks' : list word),
ms' = MS (RO 11 a0' a1' a2' a3' a4' s6' s8' s9' s10' s11' t3' t4' t5' t6') F' (Z_to_bv 64 0xa9b14) fc' None m' (seg_rom asegs)
/\ munch [(WP, WP + 88); (AK, AK + 40)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ length ws' = 22%nat /\ rw_cells asegs m' WP (f32 ws') /\ length aks' = 10%nat /\ rw_cells asegs m' AK (f32 aks').

Lemma l2l_out : forall (mI : mem) (k : nat) (jz : Z) (xs ws aks : list word) a0v a1v a2v a3v a4v s6v s8v s9v s10v s11v t3v t4v t5v t6v F1 fc mc,
jz + Z.of_nat k = 10 -> 0 <= jz ->
length xs = 10%nat -> length ws = 22%nat -> length aks = 10%nat ->
aobj asegs mI XF 40 -> aobj asegs mI WP 88 -> aobj asegs mI AK 40 -> offsh [(WP, WP + 88); (AK, AK + 40)] ->
frm0 fc -> mem_inv asegs mc -> munch [(WP, WP + 88); (AK, AK + 40)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc XF (f32 xs) -> rw_cells asegs mc WP (f32 ws) -> rw_cells asegs mc AK (f32 aks) ->
evt asegs (out_post mI)
(MS (RO jz a0v a1v a2v a3v a4v s6v s8v s9v s10v s11v t3v t4v t5v t6v) F1 (Z_to_bv 64 0xa9890) fc None mc (seg_rom asegs)).
Proof using X8 W8 A4 SEPXW SEPAW SEPAX.
intros mI k.
induction k as [|k IH]; intros jz xs ws aks a0v a1v a2v a3v a4v s6v s8v s9v s10v s11v t3v t4v t5v t6v F1 fc mc
HJ J0 LX LW LA OBX OBW OBA OF FRM MI MU WM XC WC AC;
pose proof OBX as (OX0 & OX1 & _); pose proof OBW as (OW0 & OW1 & _); pose proof OBA as (OA0 & OA1 & _); unfold APP_TOP in *;
hide_disj.
-
out_prefix jz mI mc xs ws WC LW XC LX OBX OBW MU OF a1v a2v a3v a4v s6v s8v s9v s10v s11v.
ato 0xa9a40. astep. sh_if.
out_ak jz aks AC OBA.
ato 0xa9ab8. astep. sh_if. astep.
out_join.
replace (jz + 1) with 11 by lia.
unfold out_post, RO. finish; [ | exact WJ | | exact A1 ].
+ rewrite length_app. cbn [length]. lia.
+ rewrite !length_app. cbn [length]. lia.
- out_prefix jz mI mc xs ws WC LW XC LX OBX OBW MU OF a1v a2v a3v a4v s6v s8v s9v s10v s11v.
ato 0xa9a40. astep. if_cases KJ; zify_cond KJ.
+
ato 0xa9ab8. astep. sh_if.
rewrite <- f32_nil, <- !f32_cons in W2.
match goal with WD : rw_cells _ _ WP (f32 ?l), PL : length ?l = 20%nat |- _ =>
pose proof (f32_join asegs _ WP l _ WD ltac:(rewrite PL; exact W2)) as WJ end.
match goal with XC' : rw_cells _ _ XF (f32 ?xl), WJ' : rw_cells _ _ WP (f32 ?wl), AC' : rw_cells _ _ AK (f32 ?al) |- _ =>
eapply (IH (jz + 1) xl wl al); try eassumption; try reflexivity end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
+
out_ak jz aks AC OBA.
ato 0xa9ab8. astep. sh_if.
out_join.
match goal with XC' : rw_cells _ _ XF (f32 ?xl), WJ' : rw_cells _ _ WP (f32 ?wl), AC' : rw_cells _ _ AK (f32 ?al) |- _ =>
eapply (IH (jz + 1) xl wl al); try eassumption; try reflexivity end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End OUT.

Definition l2l_body_stmt : Prop :=
forall (IQ AK usp lo : Z) (qs aks : list word) (jx : list byte) (j1 j2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rw_cells asegs m (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m (usp + -256) [CB 88 (repeat z8 88)] -> rw_cells asegs m (usp + -384) [CB 40 jx] ->
rw_cells asegs m IQ (f32 qs) -> length qs = 10%nat -> rw_cells asegs m AK (f32 aks) -> length aks = 10%nat ->
aobj asegs m (usp + -256) 88 -> aobj asegs m (usp + -384) 40 -> aobj asegs m IQ 40 -> aobj asegs m AK 40 ->
(IQ + 40 <= lo \/ usp <= IQ) -> (AK + 40 <= lo \/ usp <= AK) -> (AK + 40 <= IQ \/ IQ + 40 <= AK) ->
(AK + 40 <= SH_LO \/ SH_HI <= AK) -> IQ mod 4 = 0 -> AK mod 4 = 0 -> usp mod 32 = 0 -> 0 < IQ -> 0 < AK -> IQ + 40 <= APP_TOP -> AK + 40 <= APP_TOP ->
lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> X1cn.frm0 fc ->
evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
(F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (aks' : list word) (jw jx' : list byte),
ms' = MS (mkR ra' (Z_to_bv 64 (usp + -416)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
F' (Z_to_bv 64 A_l2l_epi) fc' None m' (seg_rom asegs)
/\ munch [(usp + -384, usp + -344); (usp + -256, usp + -168); (usp + -128, usp + -120); (AK, AK + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ X1cn.frm0 fc'
/\ rw_cells asegs m' (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -416)) j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells asegs m' (usp + -256) [CB 88 jw] /\ rw_cells asegs m' (usp + -384) [CB 40 jx']
/\ rw_cells asegs m' IQ (f32 qs) /\ rw_cells asegs m' AK (f32 aks') /\ length aks' = 10%nat)
(MS (mkR (Z_to_bv 64 RA_l2l_pois2) (Z_to_bv 64 (usp + -416)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 10) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -384)) (Z_to_bv 64 AK) (Z_to_bv 64 IQ) (Z_to_bv 64 SHB) (Z_to_bv 64 5)
(Z_to_bv 64 10) (Z_to_bv 64 (usp + -416)) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_l2l_pois2)) fc None m (seg_rom asegs)).

Lemma l2l_body : l2l_body_stmt.
Proof.
intros IQ AK usp lo qs aks jx j1 j2 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 F fc m
FR WP XF X LQ A LA OBW OBX OBQ OBA APQ APA SEP ASH Q4 A4 U32 IQ0 AK0 IQT AKT LO LOS SPH MI FRM.
unfold RA_l2l_pois2, A_l2l_epi, l2l_frame in *.
replace (ret_pc (Z_to_bv 64 0xa9758)) with (Z_to_bv 64 0xa9758) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold APP_TOP in *.
pose proof (munch_refl [(usp + -384, usp + -344); (usp + -256, usp + -168); (usp + -128, usp + -120); (AK, AK + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -384, usp + -344); (usp + -256, usp + -168); (usp + -128, usp + -120); (AK, AK + 40)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (SEPQX : IQ + 40 <= usp + -384 \/ usp + -384 + 40 <= IQ) by lia.
assert (X4 : (usp + -384) mod 4 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (X8 : (usp + -384) mod 8 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (W8 : (usp + -256) mod 8 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (SEPXW : usp + -384 + 40 <= usp + -256 \/ usp + -256 + 88 <= usp + -384) by lia.
assert (SEPAW : AK + 40 <= usp + -256 \/ usp + -256 + 88 <= AK) by lia.
assert (SEPAX : AK + 40 <= usp + -384 \/ usp + -384 + 40 <= AK) by lia.
destruct (rw_cells_CB_f32 asegs _ _ 10%nat _ XF) as (xf & Lxf & XF'); clear XF.
change 88%nat with (4 * 22)%nat in WP. destruct (rw_cells_CB_f32 asegs _ _ 22%nat _ WP) as (wp & Lwp & WP'); clear WP.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. destruct xf as [|x0 xf]; [cbn in Lxf; lia|]. cbn [length] in LQ, Lxf.
assert (E9 : Z.of_nat (S (length qs)) = 10) by lia.
hide_disj.
ato 0xa979c.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (RX IQ (usp + -384) (Z_to_bv 64 0xa9758) (Z_to_bv 64 (usp + -416)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a5 a6 a7
(Z_to_bv 64 10) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -384)) (Z_to_bv 64 AK) (Z_to_bv 64 5) (Z_to_bv 64 (usp + -416)) s11 t3 t4 t5 t6
0 a3 a4 (Z.of_nat (S (length qs))))
by (unfold RX; rewrite E9, !Z.mul_0_r, !Z.add_0_r; reflexivity) end.
pose proof (aobj_munch asegs _ m _ IQ 40 OBQ MU (shfree_of_aobj asegs _ m IQ 40 OF OBQ)) as OBQc.
pose proof (aobj_munch asegs _ m _ (usp + -384) 40 OBX MU (shfree_of_aobj asegs _ m (usp + -384) 40 OF OBX)) as OBXc.
assert (OFc : offsh [(usp + -384, usp + -384 + 40)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(usp + -384, usp + -384 + 40)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc (usp + -384) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia) end.
pose proof X as QC0. replace IQ with (IQ + 4 * 0) in QC0 at 1 by lia.
replace (usp + -384) with (usp + -384 + 4 * 0) in XF' at 1 by lia.
lazymatch type of MU with munch _ _ ?mc =>
call (l2l_xf IQ (usp + -384) (Z_to_bv 64 0xa9758) (Z_to_bv 64 (usp + -416)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128)) a5 a6 a7
(Z_to_bv 64 10) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -384)) (Z_to_bv 64 AK) (Z_to_bv 64 5) (Z_to_bv 64 (usp + -416)) s11 t3 t4 t5 t6
Q4 X4 SEPQX mc qs xf [] q0 x0 0);
[ reflexivity | lia | lia | exact OBQc | exact OBXc | exact OFc | eassumption | eassumption | exact MU0 | exact WM0 | exact QC0 | exact XD0 | exact XF' | ] end.
clear MU0 WM0 OBQc OBXc OFc; try clear XD0; try clear QC0.
unfold RX. ato 0xa9890. alits.
replace (SHB + Z.shiftr (usp + -384) 3) with (Z.shiftr (usp + -384) 3 + SHB) by lia.
replace (usp + -380) with (usp + -384 + 4) by lia.
pose proof (aobj_munch asegs _ m _ (usp + -384) 40 OBX MU (shfree_of_aobj asegs _ m (usp + -384) 40 OF OBX)) as OBXc.
pose proof (aobj_munch asegs _ m _ (usp + -256) 88 OBW MU (shfree_of_aobj asegs _ m (usp + -256) 88 OF OBW)) as OBWc.
pose proof (aobj_munch asegs _ m _ AK 40 OBA MU (shfree_of_aobj asegs _ m AK 40 OF OBA)) as OBAc.
assert (OFc : offsh [(usp + -256, usp + -256 + 88); (AK, AK + 40)]) by (cbn in OF |- *; unfold hid in *; unfold SH_LO, SH_HI in *; lia).
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(usp + -256, usp + -256 + 88); (AK, AK + 40)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
match goal with XP : rw_cells _ mc (usp + -384) (f32 ?xl), LXP : length ?xl = 10%nat |- _ =>
call (l2l_out (usp + -384) (usp + -256) AK (Z_to_bv 64 0xa9758) (Z_to_bv 64 (usp + -416)) gp tp (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
X8 W8 A4 SEPXW SEPAW SEPAX mc 10%nat 0 xl wp aks);
[ reflexivity | lia | exact LXP | exact Lwp | exact LA | exact OBXc | exact OBWc | exact OBAc | exact OFc
| eassumption | eassumption | exact MU0 | exact WM0 | exact XP | exact WP' | exact A | ] end end.
clear MU0 WM0 OBXc OBWc OBAc OFc.
match goal with WF : rw_cells _ _ (usp + -256) (f32 ?wl), LWF : length ?wl = 22%nat, XF2 : rw_cells _ _ (usp + -384) (f32 ?xl), LXF : length ?xl = 10%nat |- _ =>
apply rw_cells_f32_CB in WF; rewrite LWF in WF; change (4 * 22)%nat with 88%nat in WF;
apply rw_cells_f32_CB in XF2; rewrite LXF in XF2; change (4 * 10)%nat with 40%nat in XF2 end.
unfold RO.
apply evt_done. do 32 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
