(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yq X0yp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma f32_win1B : forall m B (l : list word) (n : Z), rw_cells bsegs m B (f32 l) -> 0 <= n -> n + 1 <= Z.of_nat (length l) ->
exists y0, rw_cells bsegs m (B + 4 * n) (f32 [y0]).
Proof.
intros m B l n X Hn Hn2.
pose proof (rw_cells_f32_mid bsegs m B l (Z.to_nat n) 1 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 1 (skipn (Z.to_nat n) l)) as w eqn:Hw.
assert (Lw : length w = 1%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|? ?]]; try (cbn in Lw; lia). exists y0. exact W.
Qed.

Section REV1.
Variables (Y X N2 XN M2N2 : Z) (ys : list word).
Variables rav spv gp tp t2v s0v s1v s4v s6v s7v s8v s9v t3v t4v t5v t6v : word.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis YR : 0 < Y /\ Y + 4 * Z.of_nat (length ys) < 2^62.
Hypothesis NR : 1 <= N2 <= Z.of_nat (length ys) /\ N2 < M2N2 < 2^30.
Hypothesis SEP : Y + 4 * Z.of_nat (length ys) <= X \/ X + XN <= Y.
Hypothesis XI : IMG_TOP_B <= X.
Hypothesis XNW : 4 * N2 <= XN.

Definition R1 (i : Z) (a1v t0v t1v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 (X + 4 * i)) a1v (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (N2 - 1))
(Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 (X + 4 * i))
(Z_to_bv 64 N2) (Z_to_bv 64 M2N2) s4v (Z_to_bv 64 X) s6v s7v s8v s9v (Z_to_bv 64 Y) (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition rev1_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' t0' t1' F' m' (xs' : list word),
ms' = MS (R1 N2 a1' t0' t1') F' (Z_to_bv 64 0xa86e4) fc None m' (seg_rom bsegs)
/\ munch [(X, X + 4 * N2)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ Z.of_nat (length xs') = N2 /\ rw_cells bsegs m' X (f32 xs').

Lemma qmf_cp1 : forall (mI : mem) (rest done : list word) (cw : word) (i : Z) (a1v t0v t1v : word) F1 fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = N2 ->
aobj bsegs mI Y (4 * Z.of_nat (length ys)) -> aobj bsegs mI X XN -> offsh [(X, X + 4 * N2)] ->
mem_inv bsegs mc -> munch [(X, X + 4 * N2)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc Y (f32 ys) -> rw_cells bsegs mc X (f32 done) -> rw_cells bsegs mc (X + 4 * i) (f32 (cw :: rest)) ->
evt bsegs (rev1_post fc mI) (MS (R1 i a1v t0v t1v) F1 (Z_to_bv 64 0xa863c) fc None mc (seg_rom bsegs)).
Proof using Y4 X4 YR NR SEP XI XNW.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i a1v t0v t1v F1 fc mc Hi HN OBY OBX OF MI MU WM XY XD XC;
pose proof OBY as (OY0 & OY1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof XI as XI'; unfold IMG_TOP_B in XI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1B mc Y ys (N2 - 1 - i) XY ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
unfold R1; rewrite !f32_cons in XC; cbn [length] in *;
assert (YA4 : (Y + 4 * (N2 - 1 - i)) mod 4 = 0) by (clear - Y4; Z.div_mod_to_equations; lia);
assert (XA4 : (X + 4 * i) mod 4 = 0) by (clear - X4; Z.div_mod_to_equations; lia);
hide_disj.
- rewrite f32_nil in XC.
bato 0xa8644.

rewrite swrap32_small by lia.
bato 0xa8654. rewrite !swrap32_small by lia. rewrite !Z.add_0_r. rewrite (Z.mod_small (N2 - 1 - i)) by lia. replace (Y + Z.shiftl (N2 - 1 - i) 2) with (Y + 4 * (N2 - 1 - i)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
bato 0xa8688. astep. chk_merge OBY 4.
bato 0xa86a4. astep. chk_merge OBX 4.
clear WIN.
bato 0xa86bc. rewrite swrap32_small by lia. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (X + 4 * i + 4) with (X + 4 * N2) by lia. replace (4 * i + 4) with (4 * N2) by lia. replace (i + 1) with N2 by lia.
unfold rev1_post, R1. finish; [ | exact XD ]; rewrite length_app; cbn [length]; lia.
- bato 0xa8644. rewrite swrap32_small by lia.
bato 0xa8654. rewrite !swrap32_small by lia. rewrite !Z.add_0_r. rewrite (Z.mod_small (N2 - 1 - i)) by lia. replace (Y + Z.shiftl (N2 - 1 - i) 2) with (Y + 4 * (N2 - 1 - i)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
bato 0xa8688. astep. chk_merge OBY 4.
bato 0xa86a4. astep. chk_merge OBX 4.
clear WIN.
bato 0xa86bc. rewrite swrap32_small by lia. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c); rewrite f32_snoc in XD; rewrite <- ?f32_cons in XC.
replace (X + 4 * i + 4) with (X + 4 * (i + 1)) in * by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia.
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End REV1.

Section REV3.
Variables (Y X N2 XN M2N2 : Z) (ys : list word).
Variables rav spv gp tp s0v s1v a2v a3v a5v s5v s6v s7v s8v s10v t5v t6v : word.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis YR : 0 < Y /\ Y + 4 * Z.of_nat (length ys) < 2^62.
Hypothesis NR : 1 <= N2 <= Z.of_nat (length ys) /\ N2 < M2N2 < 2^30.
Hypothesis SEP : Y + 4 * Z.of_nat (length ys) <= X \/ X + XN <= Y.
Hypothesis XI : IMG_TOP_B <= X.
Hypothesis XNW : 4 * N2 <= XN.

Definition R3 (i : Z) (a1v t3v t4v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 (X + 4 * i)) s0v s1v (Z_to_bv 64 (X + 4 * i)) a1v a2v a3v (Z_to_bv 64 (N2 - 1))
a5v (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (4 * i))
(Z_to_bv 64 N2) (Z_to_bv 64 M2N2) (Z_to_bv 64 X) s5v s6v s7v s8v (Z_to_bv 64 Y) s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition rev3_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' t3' t4' F' m' (xs' : list word),
ms' = MS (R3 N2 a1' t3' t4') F' (Z_to_bv 64 0xa8884) fc None m' (seg_rom bsegs)
/\ munch [(X, X + 4 * N2)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ Z.of_nat (length xs') = N2 /\ rw_cells bsegs m' X (f32 xs').

Lemma qmf_cp3 : forall (mI : mem) (rest done : list word) (cw : word) (i : Z) (a1v t3v t4v : word) F1 fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = N2 ->
aobj bsegs mI Y (4 * Z.of_nat (length ys)) -> aobj bsegs mI X XN -> offsh [(X, X + 4 * N2)] ->
mem_inv bsegs mc -> munch [(X, X + 4 * N2)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc Y (f32 ys) -> rw_cells bsegs mc X (f32 done) -> rw_cells bsegs mc (X + 4 * i) (f32 (cw :: rest)) ->
evt bsegs (rev3_post fc mI) (MS (R3 i a1v t3v t4v) F1 (Z_to_bv 64 0xa87dc) fc None mc (seg_rom bsegs)).
Proof using Y4 X4 YR NR SEP XI XNW.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i a1v t3v t4v F1 fc mc Hi HN OBY OBX OF MI MU WM XY XD XC;
pose proof OBY as (OY0 & OY1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof XI as XI'; unfold IMG_TOP_B in XI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1B mc Y ys (N2 - 1 - i) XY ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
unfold R3; rewrite !f32_cons in XC; cbn [length] in *;
assert (YA4 : (Y + 4 * (N2 - 1 - i)) mod 4 = 0) by (clear - Y4; Z.div_mod_to_equations; lia);
assert (XA4 : (X + 4 * i) mod 4 = 0) by (clear - X4; Z.div_mod_to_equations; lia);
hide_disj.
- rewrite f32_nil in XC.
bato 0xa87e4.
rewrite swrap32_small by lia.
bato 0xa87f4. rewrite !swrap32_small by lia. rewrite !Z.add_0_r. rewrite (Z.mod_small (N2 - 1 - i)) by lia. replace (Y + Z.shiftl (N2 - 1 - i) 2) with (Y + 4 * (N2 - 1 - i)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
bato 0xa8828. astep. chk_merge OBY 4.
bato 0xa8844. astep. chk_merge OBX 4.
clear WIN.
bato 0xa885c. rewrite swrap32_small by lia. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (X + 4 * i + 4) with (X + 4 * N2) by lia. replace (4 * i + 4) with (4 * N2) by lia. replace (i + 1) with N2 by lia.
unfold rev3_post, R3. finish; [ | exact XD ]; rewrite length_app; cbn [length]; lia.
- bato 0xa87e4. rewrite swrap32_small by lia.
bato 0xa87f4. rewrite !swrap32_small by lia. rewrite !Z.add_0_r. rewrite (Z.mod_small (N2 - 1 - i)) by lia. replace (Y + Z.shiftl (N2 - 1 - i) 2) with (Y + 4 * (N2 - 1 - i)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
bato 0xa8828. astep. chk_merge OBY 4.
bato 0xa8844. astep. chk_merge OBX 4.
clear WIN.
bato 0xa885c. rewrite swrap32_small by lia. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c); rewrite f32_snoc in XD; rewrite <- ?f32_cons in XC.
replace (X + 4 * i + 4) with (X + 4 * (i + 1)) in * by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia.
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End REV3.

Section MEMCP2.
Variables (G X N2 FB : Z) (gs : list word).
Variables rav spv gp tp t4v t5v t6v s0v s3v s4v s6v s7v s8v s9v s10v : word.
Hypothesis G4 : G mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis LG : length gs = 64%nat.
Hypothesis GR : 0 < G /\ G + 256 < 2^62.
Hypothesis NR : 1 <= N2 < 2^20.
Hypothesis SEP : G + 256 <= X + 4 * N2 \/ X + 4 * N2 + 128 <= G.
Hypothesis XI : IMG_TOP_B <= X.
Hypothesis FBR : 0 <= FB /\ FB + 208 < 2^63.
Hypothesis SEPF : X + 4 * N2 + 128 <= FB.

Definition RM2 (i : Z) (a1v t2v t3v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 (32 - i)) (Z_to_bv 64 (32 - i)) t2v s0v (Z_to_bv 64 FB) (Z_to_bv 64 (G + 4 + 8 * i)) a1v (Z_to_bv 64 32) (Z_to_bv 64 (18446744073709551615 - X))
(Z_to_bv 64 (N2 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 i) (Z_to_bv 64 (G + 4 + 8 * i))
(Z_to_bv 64 N2) s3v s4v (Z_to_bv 64 X) s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition memcp2_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' t2' t3' F' m' (xs' : list word),
ms' = MS (RM2 32 a1' t2' t3') F' (Z_to_bv 64 0xa87c0) fc None m' (seg_rom bsegs)
/\ munch [(X + 4 * N2, X + 4 * N2 + 128)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ length xs' = 32%nat /\ rw_cells bsegs m' (X + 4 * N2) (f32 xs').

Lemma qmf_cp2 : forall (mI : mem) (rest done : list word) (cw : word) (i : Z) (a1v t2v t3v : word) F1 fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = 32 ->
aobj bsegs mI G 256 -> aobj bsegs mI (X + 4 * N2) 128 -> offsh [(X + 4 * N2, X + 4 * N2 + 128)] ->
mem_inv bsegs mc -> munch [(X + 4 * N2, X + 4 * N2 + 128)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (FB + 40) [C8 (Z_to_bv 64 G)] ->
rw_cells bsegs mc G (f32 gs) -> rw_cells bsegs mc (X + 4 * N2) (f32 done) -> rw_cells bsegs mc (X + 4 * N2 + 4 * i) (f32 (cw :: rest)) ->
evt bsegs (memcp2_post fc mI) (MS (RM2 i a1v t2v t3v) F1 (Z_to_bv 64 0xa8720) fc None mc (seg_rom bsegs)).
Proof using G4 X4 LG GR NR SEP XI FBR SEPF.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i a1v t2v t3v F1 fc mc Hi HN OBG OBX OF MI MU WM SL XG XD XC;
pose proof OBG as (OG0 & OG1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof XI as XI'; unfold IMG_TOP_B in XI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1B mc G gs (2 * i + 1) XG ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
replace (G + 4 * (2 * i + 1)) with (G + 4 + 8 * i) in WIN by lia;
unfold RM2; rewrite !f32_cons in XC; cbn [length] in *;
assert (GA4 : (G + 4 + 8 * i) mod 4 = 0) by (clear - G4; Z.div_mod_to_equations; lia);
assert (XA4 : (X + 4 * N2 + 4 * i) mod 4 = 0) by (clear - X4; Z.div_mod_to_equations; lia);
hide_disj.
- rewrite f32_nil in XC.
bato 0xa8744. astep. chk_merge OBG 4.
bato 0xa8768. replace (X + (N2 + i + 0) * 4) with (X + 4 * N2 + 4 * i) by lia.
chk_hint OBX.
bato 0xa8778. astep. chk_merge OBX 4.
clear WIN.
bato 0xa8794. rewrite swrap32_small by lia. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * 32) by lia. replace (32 - i + -1) with (32 - 32) by lia. replace (i + 1) with 32 by lia.
unfold memcp2_post, RM2. finish; [ | exact XD ]; rewrite length_app; cbn [length]; lia.
- bato 0xa8744. astep. chk_merge OBG 4.
bato 0xa8768. replace (X + (N2 + i + 0) * 4) with (X + 4 * N2 + 4 * i) by lia.
chk_hint OBX.
bato 0xa8778. astep. chk_merge OBX 4.
clear WIN.
bato 0xa8794. rewrite swrap32_small by lia. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c); rewrite f32_snoc in XD; rewrite <- ?f32_cons in XC.
replace (X + 4 * N2 + 4 * i + 4) with (X + 4 * N2 + 4 * (i + 1)) in * by lia.
replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * (i + 1)) by lia. replace (32 - i + -1) with (32 - (i + 1)) by lia.
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End MEMCP2.

Section MEMCP4.
Variables (G X N2 FB : Z) (gs : list word).
Variables rav spv gp tp a3v a4v a5v t5v t6v s0v s3v s5v s6v s7v s8v s9v s10v : word.
Hypothesis G4 : G mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis LG : length gs = 64%nat.
Hypothesis GR : 0 < G /\ G + 256 < 2^62.
Hypothesis NR : 1 <= N2 < 2^20.
Hypothesis SEP : G + 256 <= X + 4 * N2 \/ X + 4 * N2 + 128 <= G.
Hypothesis XI : IMG_TOP_B <= X.
Hypothesis FBR : 0 <= FB /\ FB + 208 < 2^63.
Hypothesis SEPF : X + 4 * N2 + 128 <= FB.

Definition RM4 (i : Z) (a1v t3v t4v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 i) (Z_to_bv 64 (32 - i)) (Z_to_bv 64 (32 - i)) s0v (Z_to_bv 64 FB) (Z_to_bv 64 (G + 4 + 8 * i)) a1v (Z_to_bv 64 (G + 4 + 8 * i)) a3v a4v a5v
(Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 0)
(Z_to_bv 64 N2) s3v (Z_to_bv 64 X) s5v s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition memcp4_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' t3' t4' F' m' (xs' : list word),
ms' = MS (RM4 32 a1' t3' t4') F' (Z_to_bv 64 0xa895c) fc None m' (seg_rom bsegs)
/\ munch [(X + 4 * N2, X + 4 * N2 + 128)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ length xs' = 32%nat /\ rw_cells bsegs m' (X + 4 * N2) (f32 xs').

Lemma qmf_cp4 : forall (mI : mem) (rest done : list word) (cw : word) (i : Z) (a1v t3v t4v : word) F1 fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = 32 ->
aobj bsegs mI G 256 -> aobj bsegs mI (X + 4 * N2) 128 -> offsh [(X + 4 * N2, X + 4 * N2 + 128)] ->
mem_inv bsegs mc -> munch [(X + 4 * N2, X + 4 * N2 + 128)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (FB + 32) [C8 (Z_to_bv 64 G)] ->
rw_cells bsegs mc G (f32 gs) -> rw_cells bsegs mc (X + 4 * N2) (f32 done) -> rw_cells bsegs mc (X + 4 * N2 + 4 * i) (f32 (cw :: rest)) ->
evt bsegs (memcp4_post fc mI) (MS (RM4 i a1v t3v t4v) F1 (Z_to_bv 64 0xa88bc) fc None mc (seg_rom bsegs)).
Proof using G4 X4 LG GR NR SEP XI FBR SEPF.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i a1v t3v t4v F1 fc mc Hi HN OBG OBX OF MI MU WM SL XG XD XC;
pose proof OBG as (OG0 & OG1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof XI as XI'; unfold IMG_TOP_B in XI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1B mc G gs (2 * i + 1) XG ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
replace (G + 4 * (2 * i + 1)) with (G + 4 + 8 * i) in WIN by lia;
unfold RM4; rewrite !f32_cons in XC; cbn [length] in *;
assert (GA4 : (G + 4 + 8 * i) mod 4 = 0) by (clear - G4; Z.div_mod_to_equations; lia);
assert (XA4 : (X + 4 * N2 + 4 * i) mod 4 = 0) by (clear - X4; Z.div_mod_to_equations; lia);
hide_disj.
- rewrite f32_nil in XC.
bato 0xa88e0. astep. chk_merge OBG 4.
bato 0xa8904. replace (X + (N2 + i + 0) * 4) with (X + 4 * N2 + 4 * i) by lia.
chk_hint OBX.
bato 0xa8914. astep. chk_merge OBX 4.
clear WIN.
bato 0xa8930. rewrite swrap32_small by lia. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * 32) by lia. replace (32 - i + -1) with (32 - 32) by lia. replace (i + 1) with 32 by lia.
unfold memcp4_post, RM4. finish; [ | exact XD ]; rewrite length_app; cbn [length]; lia.
- bato 0xa88e0. astep. chk_merge OBG 4.
bato 0xa8904. replace (X + (N2 + i + 0) * 4) with (X + 4 * N2 + 4 * i) by lia.
chk_hint OBX.
bato 0xa8914. astep. chk_merge OBX 4.
clear WIN.
bato 0xa8930. rewrite swrap32_small by lia. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c); rewrite f32_snoc in XD; rewrite <- ?f32_cons in XC.
replace (X + 4 * N2 + 4 * i + 4) with (X + 4 * N2 + 4 * (i + 1)) in * by lia.
replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * (i + 1)) by lia. replace (32 - i + -1) with (32 - (i + 1)) by lia.
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End MEMCP4.

Section WB1.
Variables (G X XN VS FB : Z) (xs : list word).
Variables rav spv gp tp s0v a2v a6v a7v s2v s3v s4v s6v s7v s8v s9v s10v t4v t5v t6v : word.
Hypothesis G4 : G mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis LX : 32 <= Z.of_nat (length xs) /\ 4 * Z.of_nat (length xs) <= XN.
Hypothesis GR : 0 < G /\ G + 256 < 2^62.
Hypothesis XR : 0 < X /\ X + XN < 2^62.
Hypothesis SEP : G + 256 <= X \/ X + XN <= G.
Hypothesis VSR : 128 <= VS < 2^62.
Hypothesis FBR : 0 <= FB /\ FB + 208 < 2^63.
Hypothesis SEPF : G + 256 <= FB.

Definition RW1 (i : Z) (a1v t1v t3v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 (G + 8 * i + 4)) t1v (Z_to_bv 64 128) s0v (Z_to_bv 64 FB) (Z_to_bv 64 (G + 8 * i + 4)) a1v a2v (Z_to_bv 64 (18446744073709551615 - X))
(Z_to_bv 64 (4 * i)) (Z_to_bv 64 0) a6v a7v s2v s3v s4v (Z_to_bv 64 X) s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition wb1_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' t1' t3' F' m' (gs' : list word),
ms' = MS (RW1 32 a1' t1' t3') F' (Z_to_bv 64 0xa8e2c) fc None m' (seg_rom bsegs)
/\ munch [(G, G + 256)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ length gs' = 64%nat /\ rw_cells bsegs m' G (f32 gs').

Lemma qmf_wb1 : forall (mI : mem) (k : nat) (rest done : list word) (ge go : word) (i : Z) (a1v t1v t3v : word) F1 fc mc,
length rest = (2 * k)%nat -> 2 * i = Z.of_nat (length done) -> i + 1 + Z.of_nat k = 32 ->
aobj bsegs mI G 256 -> aobj bsegs mI X XN -> offsh [(G, G + 256)] ->
mem_inv bsegs mc -> munch [(G, G + 256)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (FB + 24) [C8 (Z_to_bv 64 VS)] -> rw_cells bsegs mc (FB + 40) [C8 (Z_to_bv 64 G)] ->
rw_cells bsegs mc X (f32 xs) -> rw_cells bsegs mc G (f32 done) -> rw_cells bsegs mc (G + 8 * i) (f32 (ge :: go :: rest)) ->
evt bsegs (wb1_post fc mI) (MS (RW1 i a1v t1v t3v) F1 (Z_to_bv 64 0xa8da8) fc None mc (seg_rom bsegs)).
Proof using G4 X4 LX GR XR SEP VSR FBR SEPF.
intros mI k.
induction k as [|k IH]; intros rest done ge go i a1v t1v t3v F1 fc mc LR Hi HN OBG OBX OF MI MU WM SV SG XX XD XC;
pose proof OBG as (OG0 & OG1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1B mc X xs i XX ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
unfold RW1; rewrite !f32_cons in XC;
assert (GA4 : (G + 8 * i + 4) mod 4 = 0) by (clear - G4; Z.div_mod_to_equations; lia);
assert (XA4 : (X + 4 * i) mod 4 = 0) by (clear - X4; Z.div_mod_to_equations; lia);
hide_disj.
- destruct rest; [| cbn in LR; lia]. rewrite f32_nil in XC.
bato 0xa8dc4. astep. chk_merge OBX 4.
bato 0xa8df0. astep. chk_merge OBG 4.
clear WIN.
bato 0xa8e04. astep. sh_if. astep.
(let C1 := fresh "C1" in chunk_uncons XC as C1; chunk_snoc XD C1); chunk_snoc XD XC; rewrite !f32_snoc in XD.
replace (G + 8 * i + 12) with (G + 8 * 32 + 4) by lia. replace (4 * i + 4) with (4 * 32) by lia.
unfold wb1_post, RW1. finish; [ | exact XD ]; rewrite !length_app; cbn [length]; lia.
- destruct rest as [|ge' [|go' rest]]; try (cbn in LR; lia). rewrite ?f32_cons in XC.
bato 0xa8dc4. astep. chk_merge OBX 4.
bato 0xa8df0. astep. chk_merge OBG 4.
clear WIN.
bato 0xa8e04. astep. sh_if.
(let C1 := fresh "C1" in chunk_uncons XC as C1; chunk_snoc XD C1);
(let C2 := fresh "C2" in chunk_uncons XC as C2; chunk_snoc XD C2); rewrite !f32_snoc in XD; rewrite <- ?f32_cons in XC.
replace (G + 8 * i + 4 + 4) with (G + 8 * (i + 1)) in * by lia.
replace (G + 8 * i + 12) with (G + 8 * (i + 1) + 4) by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia.
eapply (IH rest _ ge' go' (i + 1)); try eassumption; try reflexivity;
try (rewrite !length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End WB1.

Section WB2.
Variables (G X XN VS FB : Z) (xs : list word).
Variables rav spv gp tp t0v t1v s0v s2v s3v s5v s6v s7v s8v s9v s10v t3v t4v t5v t6v : word.
Hypothesis G4 : G mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis LX : 32 <= Z.of_nat (length xs) /\ 4 * Z.of_nat (length xs) <= XN.
Hypothesis GR : 0 < G /\ G + 256 < 2^62.
Hypothesis XR : 0 < X /\ X + XN < 2^62.
Hypothesis SEP : G + 256 <= X \/ X + XN <= G.
Hypothesis VSR : 128 <= VS < 2^62.
Hypothesis FBR : 0 <= FB /\ FB + 208 < 2^63.
Hypothesis SEPF : G + 256 <= FB.

Definition RW2 (i : Z) (a1v a4v a5v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v (Z_to_bv 64 128) s0v (Z_to_bv 64 FB) (Z_to_bv 64 (G + 8 * i + 4)) a1v (Z_to_bv 64 (G + 8 * i + 4)) (Z_to_bv 64 (4 * i)) a4v a5v
(Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 0) s2v s3v (Z_to_bv 64 X) s5v s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition wb2_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' a4' a5' F' m' (gs' : list word),
ms' = MS (RW2 32 a1' a4' a5') F' (Z_to_bv 64 0xa8eb8) fc None m' (seg_rom bsegs)
/\ munch [(G, G + 256)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ length gs' = 64%nat /\ rw_cells bsegs m' G (f32 gs').

Lemma qmf_wb2 : forall (mI : mem) (k : nat) (rest done : list word) (ge go : word) (i : Z) (a1v a4v a5v : word) F1 fc mc,
length rest = (2 * k)%nat -> 2 * i = Z.of_nat (length done) -> i + 1 + Z.of_nat k = 32 ->
aobj bsegs mI G 256 -> aobj bsegs mI X XN -> offsh [(G, G + 256)] ->
mem_inv bsegs mc -> munch [(G, G + 256)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (FB + 24) [C8 (Z_to_bv 64 VS)] -> rw_cells bsegs mc (FB + 32) [C8 (Z_to_bv 64 G)] ->
rw_cells bsegs mc X (f32 xs) -> rw_cells bsegs mc G (f32 done) -> rw_cells bsegs mc (G + 8 * i) (f32 (ge :: go :: rest)) ->
evt bsegs (wb2_post fc mI) (MS (RW2 i a1v a4v a5v) F1 (Z_to_bv 64 0xa8e34) fc None mc (seg_rom bsegs)).
Proof using G4 X4 LX GR XR SEP VSR FBR SEPF.
intros mI k.
induction k as [|k IH]; intros rest done ge go i a1v a4v a5v F1 fc mc LR Hi HN OBG OBX OF MI MU WM SV SG XX XD XC;
pose proof OBG as (OG0 & OG1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1B mc X xs i XX ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
unfold RW2; rewrite !f32_cons in XC;
assert (GA4 : (G + 8 * i + 4) mod 4 = 0) by (clear - G4; Z.div_mod_to_equations; lia);
assert (XA4 : (X + 4 * i) mod 4 = 0) by (clear - X4; Z.div_mod_to_equations; lia);
hide_disj.
- destruct rest; [| cbn in LR; lia]. rewrite f32_nil in XC.
bato 0xa8e50. astep. chk_merge OBX 4.
bato 0xa8e7c. astep. chk_merge OBG 4.
clear WIN.
bato 0xa8e90. astep. sh_if. astep.
(let C1 := fresh "C1" in chunk_uncons XC as C1; chunk_snoc XD C1); chunk_snoc XD XC; rewrite !f32_snoc in XD.
replace (G + 8 * i + 12) with (G + 8 * 32 + 4) by lia. replace (4 * i + 4) with (4 * 32) by lia.
unfold wb2_post, RW2. finish; [ | exact XD ]; rewrite !length_app; cbn [length]; lia.
- destruct rest as [|ge' [|go' rest]]; try (cbn in LR; lia). rewrite ?f32_cons in XC.
bato 0xa8e50. astep. chk_merge OBX 4.
bato 0xa8e7c. astep. chk_merge OBG 4.
clear WIN.
bato 0xa8e90. astep. sh_if.
(let C1 := fresh "C1" in chunk_uncons XC as C1; chunk_snoc XD C1);
(let C2 := fresh "C2" in chunk_uncons XC as C2; chunk_snoc XD C2); rewrite !f32_snoc in XD; rewrite <- ?f32_cons in XC.
replace (G + 8 * i + 4 + 4) with (G + 8 * (i + 1)) in * by lia.
replace (G + 8 * i + 12) with (G + 8 * (i + 1) + 4) by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia.
eapply (IH rest _ ge' go' (i + 1)); try eassumption; try reflexivity;
try (rewrite !length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End WB2.

