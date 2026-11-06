(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0aq X0au.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Section OUTER.
Variables (A X1 X2 XN Y HN : Z) (al xl1 xl2 : list word).
Variables rav spv gp tp t2v s0v s1v : word.
Local Notation n1 := (2 * HN - 1).
Hypothesis A8 : A mod 8 = 0.
Hypothesis X14 : X1 mod 4 = 0.
Hypothesis X24 : X2 mod 4 = 0.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis LA : length al = 64%nat.
Hypothesis L1 : Z.of_nat (length xl1) = n1 + 33.
Hypothesis L2 : Z.of_nat (length xl2) = n1 + 33.
Hypothesis LXN : 4 * (n1 + 33) <= XN.
Hypothesis HHN : 1 <= HN <= 160.
Hypothesis SEP1 : Y + 16 * HN <= X1 \/ X1 + XN <= Y.
Hypothesis SEP2 : Y + 16 * HN <= X2 \/ X2 + XN <= Y.
Hypothesis YI : IMG_TOP <= Y.
Hypothesis AI : A + 256 <= IMG_TOP.

Definition RO (h : Z) (a0v a1v a2v s8v s9v s10v t6v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 (A + 8)) (Z_to_bv 64 (X1 + 4 * (n1 + 1))) t2v s0v s1v a0v a1v a2v (Z_to_bv 64 (-8 * h)) (Z_to_bv 64 (2 * h)) (Z_to_bv 64 (-2 * h))
(Z_to_bv 64 (n1 - 1)) (Z_to_bv 64 (X2 + 4 * (n1 + 1)))
(Z_to_bv 64 X2) (Z_to_bv 64 X1) (Z_to_bv 64 32) (Z_to_bv 64 (2 * HN)) (Z_to_bv 64 Y) (Z_to_bv 64 A) s8v s9v s10v (Z_to_bv 64 SHB)
(Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 (X1 + 4 * n1)) (Z_to_bv 64 (X2 + 4 * n1)) t6v.

Definition outer_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a1' a2' s8' s9' s10' t6' F' fc' m' (ys' : list word),
ms' = MS (RO HN a0' a1' a2' s8' s9' s10' t6') F' (Z_to_bv 64 0xa51c0) fc' None m' (seg_rom asegs)
/\ munch [(Y, Y + 16 * HN)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ Z.of_nat (length ys') = 4 * HN /\ rw_cells asegs m' Y (f32 ys').

Ltac outer_iter h mI mc OBA OB1 OB2 OBY OF MU RA RX1 RX2 MI FRM :=
destruct (f32_win1 mc X2 xl2 (n1 - 1 - 2 * h) RX2 ltac:(lia) ltac:(lia)) as (u2 & U2); rewrite f32_cons, f32_nil in U2;
destruct (f32_win1 mc X1 xl1 (n1 - 1 - 2 * h) RX1 ltac:(lia) ltac:(lia)) as (u1 & U1); rewrite f32_cons, f32_nil in U1;
ato 0xa4ef0; replace (X2 + Z.shiftl (-2 * h + (n1 - 1)) 2) with (X2 + 4 * (n1 - 1 - 2 * h)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
ato 0xa4efc; astep; chk_merge OB2 4;
ato 0xa4f04; replace (X1 + Z.shiftl (-2 * h + (n1 - 1)) 2) with (X1 + 4 * (n1 - 1 - 2 * h)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
ato 0xa4f14; astep; chk_merge OB1 4;
ato 0xa4f3c; clear U1 U2;
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ _ _) =>
eapply evt_cut; [eapply (qmf_inner mc A X1 X2 XN n1 (n1 - 2 * h) al xl1 xl2) with (k := 15%nat) (jz := 0) (off := -8 * h) (F1 := G0) (fc := fc0);
[ exact (aobj_munch asegs _ mI mc A 256 OBA MU (shfree_of_aobj asegs _ mI A 256 OF OBA))
| exact (aobj_munch asegs _ mI mc X1 XN OB1 MU (shfree_of_aobj asegs _ mI X1 XN OF OB1))
| exact (aobj_munch asegs _ mI mc X2 XN OB2 MU (shfree_of_aobj asegs _ mI X2 XN OF OB2))
| exact A8 | exact X14 | exact X24 | exact LA | exact L1 | exact L2 | exact LXN | lia | exact RA | exact RX1 | exact RX2
| lia | lia | lia | lia | lia | exact FRM | exact MI ] | ] end;
clear FRM; intros ms' (a1' & a2' & s10' & F' & fc' & -> & FRM); unfold RI;
ato 0xa50e0; replace (Y + Z.shiftl (2 * h) 3) with (Y + 16 * h) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
ato 0xa50ec; astep; chk_merge OBY 4;
ato 0xa5100; replace (Y + Z.shiftl (Z.shiftl (2 * h) 1 mod 18446744073709551616) 2) with (Y + 16 * h) by (rewrite !Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia; lia);
ato 0xa5110; astep; chk_merge OBY 4;
ato 0xa5128; astep; chk_merge OBY 4;
ato 0xa5140; astep; chk_merge OBY 4;
ato 0xa5154; astep.

Lemma qmf_outer : forall (mI : mem) (k : nat) (rest done : list word) (c0 c1 c2 c3 : word) (h : Z) (a0v a1v a2v s8v s9v s10v t6v : word) F1 fc mc,
length rest = (4 * k)%nat -> 4 * h = Z.of_nat (length done) -> h + 1 + Z.of_nat k = HN ->
aobj asegs mI A 256 -> aobj asegs mI X1 XN -> aobj asegs mI X2 XN -> aobj asegs mI Y (16 * HN) -> offsh [(Y, Y + 16 * HN)] ->
frm0 fc -> mem_inv asegs mc -> munch [(Y, Y + 16 * HN)] mI mc -> wmono asegs mI mc ->
ro_cells asegs mc A (f32 al) -> rw_cells asegs mc X1 (f32 xl1) -> rw_cells asegs mc X2 (f32 xl2) ->
rw_cells asegs mc Y (f32 done) -> rw_cells asegs mc (Y + 16 * h) (f32 (c0 :: c1 :: c2 :: c3 :: rest)) ->
evt asegs (outer_post mI) (MS (RO h a0v a1v a2v s8v s9v s10v t6v) F1 (Z_to_bv 64 0xa4ed0) fc None mc (seg_rom asegs)).
Proof using A8 X14 X24 Y4 LA L1 L2 LXN HHN SEP1 SEP2 YI AI.
intros mI k.
induction k as [|k IH]; intros rest done c0 c1 c2 c3 h a0v a1v a2v s8v s9v s10v t6v F1 fc mc LR Hh HN' OBA OB1 OB2 OBY OF FRM MI MU WM RA RX1 RX2 XD XC;
pose proof OBA as (OA0 & OA1 & _); pose proof OB1 as (O10 & O11 & _); pose proof OB2 as (O20 & O21 & _); pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *;
pose proof YI as YI'; unfold IMG_TOP in YI'; pose proof AI as AI'; unfold IMG_TOP in AI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold RO; rewrite !f32_cons in XC;
hide_disj.
- destruct rest; [| cbn in LR; lia]. rewrite f32_nil in XC.
outer_iter h mI mc OBA OB1 OB2 OBY OF MU RA RX1 RX2 MI FRM.
sh_if. astep.
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). (let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C).
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). chunk_snoc XD XC. rewrite !f32_snoc in XD.
replace (2 * h + 2) with (2 * HN) by lia. replace (-2 * h + -2) with (-2 * HN) by lia. replace (-8 * h + -8) with (-8 * HN) by lia.
unfold outer_post, RO. finish; [ | exact XD ]. rewrite !length_app. cbn [length]. lia.
- destruct rest as [|c0' [|c1' [|c2' [|c3' rest]]]]; try (cbn in LR; lia). rewrite ?f32_cons in XC.
outer_iter h mI mc OBA OB1 OB2 OBY OF MU RA RX1 RX2 MI FRM.
sh_if.
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). (let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C).
(let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C). (let C := fresh "C" in chunk_uncons XC as C; chunk_snoc XD C).
rewrite !f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (Y + 16 * h + 4 + 4 + 4 + 4) with (Y + 16 * (h + 1)) in * by lia.
replace (2 * h + 2) with (2 * (h + 1)) by lia. replace (-2 * h + -2) with (-2 * (h + 1)) by lia. replace (-8 * h + -8) with (-8 * (h + 1)) by lia.
eapply (IH rest _ c0' c1' c2' c3' (h + 1)); try eassumption;
try (rewrite !length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End OUTER.
