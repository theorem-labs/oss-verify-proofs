(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yq X0yp X11e.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Section OUTERB.
Variables (A X1 X2 XN Y HN N2 FB : Z) (al xl1 xl2 : list word).
Variables spv gp tp s0v a5v a7v : word.
Hypothesis A8 : A mod 8 = 0.
Hypothesis AR : 0 < A /\ A + 256 < 2^62.
Hypothesis X14 : X1 mod 4 = 0.
Hypothesis X24 : X2 mod 4 = 0.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis X1R : 0 < X1 /\ X1 + XN < 2^62.
Hypothesis X2R : 0 < X2 /\ X2 + XN < 2^62.
Hypothesis YR : 0 < Y /\ Y + 16 * HN < 2^62.
Hypothesis LA : length al = 64%nat.
Hypothesis L1 : Z.of_nat (length xl1) = N2 + 32.
Hypothesis L2 : Z.of_nat (length xl2) = N2 + 32.
Hypothesis LXN : 4 * (N2 + 32) <= XN.
Hypothesis EN : N2 = 2 * HN.
Hypothesis HHN : 1 <= HN <= 160.
Hypothesis SEP1 : Y + 16 * HN <= X1 \/ X1 + XN <= Y.
Hypothesis SEP2 : Y + 16 * HN <= X2 \/ X2 + XN <= Y.
Hypothesis YI : IMG_TOP_B <= Y.
Hypothesis AI : A + 256 <= IMG_TOP_B.
Hypothesis FBR : 0 <= FB /\ FB + 208 < 2^63.
Hypothesis SEPF : Y + 16 * HN <= FB.

Definition ROB (h : Z) (rav t0v a0v a1v a2v s6v s7v s10v t3v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v (Z_to_bv 64 (N2 - 2)) (Z_to_bv 64 1) s0v (Z_to_bv 64 FB) a0v a1v a2v (Z_to_bv 64 (18446744073709551615 - X1)) (Z_to_bv 64 (N2 - 1)) a5v
(Z_to_bv 64 (18446744073709551615 - X2)) a7v (Z_to_bv 64 N2) (Z_to_bv 64 (32 + N2)) (Z_to_bv 64 X2) (Z_to_bv 64 X1) s6v s7v (Z_to_bv 64 A) (Z_to_bv 64 (2 * h))
s10v (Z_to_bv 64 SHB) t3v (Z_to_bv 64 (18446744073709551615 - A)) (Z_to_bv 64 (18446744073709551615 - Y)) (Z_to_bv 64 1).

Definition outerB_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists ra' t0' a0' a1' a2' s6' s7' s10' t3' F' fc' m' (ys' : list word),
ms' = MS (ROB HN ra' t0' a0' a1' a2' s6' s7' s10' t3') F' (Z_to_bv 64 0xa8d84) fc' None m' (seg_rom bsegs)
/\ munch [(Y, Y + 16 * HN)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ Z.of_nat (length ys') = 4 * HN /\ rw_cells bsegs m' Y (f32 ys').

Ltac outer_iterB h mI mc OBA OB1 OB2 OBY OF MU RA RX1 RX2 FS MI FRM :=
destruct (f32_winB mc X2 xl2 (N2 - 2 - 2 * h) 1%nat RX2 ltac:(lia) ltac:(lia)) as (w2 & Lw2 & U2);
destruct w2 as [|u2 [|? ?]]; try (cbn in Lw2; lia); clear Lw2; rewrite !f32_cons, f32_nil in U2;
destruct (f32_winB mc X1 xl1 (N2 - 2 - 2 * h) 1%nat RX1 ltac:(lia) ltac:(lia)) as (w1 & Lw1 & U1);
destruct w1 as [|u1 [|? ?]]; try (cbn in Lw1; lia); clear Lw1; rewrite !f32_cons, f32_nil in U1;
bato 0xa89b8; replace ((N2 - 2 - 2 * h) * 4) with (4 * (N2 - 2 - 2 * h)) by lia;
bato 0xa89c4; astep; chk_merge OB1 4;
bato 0xa89f8; astep; chk_merge OB2 4;
bato 0xa8a1c; clear U1 U2;
let FSc := fresh "FSc" in let FSy := fresh "FSy" in
pose proof FS as FSc; chunk_uncons FSc as FSy; clear FSy; replace (FB + 48 + 8) with (FB + 56) in FSc by lia;
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ _ _) =>
eapply evt_cut; [eapply (qmf_innerB mc A X1 X2 XN N2 (2 * h) FB al xl1 xl2 spv gp tp (Z_to_bv 64 (N2 - 2)) (Z_to_bv 64 (18446744073709551615 - Y)) s0v a5v a7v
(aobj_munch bsegs _ mI mc A 256 OBA MU (shfree_of_aobj bsegs _ mI A 256 OF OBA))
(aobj_munch bsegs _ mI mc X1 XN OB1 MU (shfree_of_aobj bsegs _ mI X1 XN OF OB1))
(aobj_munch bsegs _ mI mc X2 XN OB2 MU (shfree_of_aobj bsegs _ mI X2 XN OF OB2))
A8 AR X14 X24 X1R X2R LA L1 L2 LXN ltac:(lia) ltac:(lia) FBR RA RX1 RX2 FSc) with (k := 15%nat) (j := 0) (F1 := G0) (fc := fc0);
[lia | lia | assumption | exact MI] | ] end;
clear FRM FSc; intros ms' (t0' & a0' & a1' & a2' & s6' & s7' & F' & fc' & -> & FRM); unfold RIB;
bato 0xa8c74; replace (Y + 2 * h * 8) with (Y + 16 * h) by lia;
bato 0xa8c80; astep; chk_merge OBY 4;
bato 0xa8ca8; replace (Y + Z.shiftl (2 * h * 2 + 1) 2) with (Y + 16 * h + 4) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
bato 0xa8cb4; astep; chk_merge OBY 4;
bato 0xa8cd4; replace (Y + Z.shiftl (2 * h * 2 + 2) 2) with (Y + 16 * h + 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
bato 0xa8ce0; astep; chk_merge OBY 4;
bato 0xa8d00; replace (Y + Z.shiftl (2 * h * 2 + 3) 2) with (Y + 16 * h + 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
bato 0xa8d0c; astep; chk_merge OBY 4;
bato 0xa8d18; astep.

Lemma qmf_outerB : forall (mI : mem) (k : nat) (rest done : list word) (c0 c1 c2 c3 : word) (h : Z) (rav t0v a0v a1v a2v s6v s7v s10v t3v : word) F1 fc mc,
length rest = (4 * k)%nat -> 4 * h = Z.of_nat (length done) -> h + 1 + Z.of_nat k = HN ->
aobj bsegs mI A 256 -> aobj bsegs mI X1 XN -> aobj bsegs mI X2 XN -> aobj bsegs mI Y (16 * HN) -> offsh [(Y, Y + 16 * HN)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(Y, Y + 16 * HN)] mI mc -> wmono bsegs mI mc ->
ro_cells bsegs mc A (f32 al) -> rw_cells bsegs mc X1 (f32 xl1) -> rw_cells bsegs mc X2 (f32 xl2) ->
rw_cells bsegs mc (FB + 8) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1)] -> rw_cells bsegs mc (FB + 48) [C8 (Z_to_bv 64 Y); C8 (Z_to_bv 64 32)] ->
rw_cells bsegs mc Y (f32 done) -> rw_cells bsegs mc (Y + 16 * h) (f32 (c0 :: c1 :: c2 :: c3 :: rest)) ->
evt bsegs (outerB_post mI) (MS (ROB h rav t0v a0v a1v a2v s6v s7v s10v t3v) F1 (Z_to_bv 64 0xa89a0) fc None mc (seg_rom bsegs)).
Proof using A8 AR X14 X24 Y4 X1R X2R YR LA L1 L2 LXN EN HHN SEP1 SEP2 YI AI FBR SEPF.
intros mI k.
induction k as [|k IH]; intros rest done c0 c1 c2 c3 h rav t0v a0v a1v a2v s6v s7v s10v t3v F1 fc mc LR Hh HN' OBA OB1 OB2 OBY OF FRM MI MU WM RA RX1 RX2 FL FS XD XC;
pose proof OBA as (OA0 & OA1 & _); pose proof OB1 as (O10 & O11 & _); pose proof OB2 as (O20 & O21 & _); pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *;
pose proof YI as YI'; unfold IMG_TOP_B in YI'; pose proof AI as AI'; unfold IMG_TOP_B in AI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
assert (YA4 : (Y + 16 * h) mod 4 = 0) by (clear - Y4; Z.div_mod_to_equations; lia);
unfold ROB; rewrite !f32_cons in XC;
hide_disj.
- destruct rest; [| cbn in LR; lia]. rewrite f32_nil in XC.
outer_iterB h mI mc OBA OB1 OB2 OBY OF MU RA RX1 RX2 FS MI FRM.
sh_if. astep.
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). (let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C).
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). chunk_snoc XD XC. rewrite !f32_snoc in XD.
replace (2 * h + 2) with (2 * HN) by lia.
unfold outerB_post, ROB. finish; [ | exact XD ]. rewrite !length_app. cbn [length]. lia.
- destruct rest as [|c0' [|c1' [|c2' [|c3' rest]]]]; try (cbn in LR; lia). rewrite ?f32_cons in XC.
outer_iterB h mI mc OBA OB1 OB2 OBY OF MU RA RX1 RX2 FS MI FRM.
sh_if.
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). (let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C).
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). (let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C).
rewrite !f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (Y + 16 * h + 4 + 4 + 4 + 4) with (Y + 16 * (h + 1)) in * by lia.
replace (2 * h + 2) with (2 * (h + 1)) by lia.
eapply (IH rest _ c0' c1' c2' c3' (h + 1)); try eassumption;
try (rewrite !length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End OUTERB.
