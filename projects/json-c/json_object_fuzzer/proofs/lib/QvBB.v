(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q2qa Qy5Y Q4J3 QPjm QJE4 Qiw1 QX7A QIsN QiMA_c1 QObY QQjK QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import Q2qa.Mq0 Qy5Y.Mq0 Qy5Y.Mq3 Q4J3 QPjm QJE4.
Import Qiw1 QX7A QIsN QiMA_c1 QObY QQjK.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Section Walk.
Variables (sp sgw w6 : word).
Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation sgn := (bv_unsigned sgw).
Notation bLo := (bv_unsigned w6).

Ltac hyp :=
match goal with
| H : mem_inv _ ?m |- mem_inv _ ?m => exact H
| H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
| H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
| H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
| H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
| H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
| H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
| |- (_ <= _ <= _)%Z => lia
| |- (0 <= _ < _)%Z => first [zrange2 | lia]
end.
Ltac join L := eapply L; try hyp.

Ltac flag_join n G body K :=
set (G := body);
let w := getreg n in
lazymatch w with Z_to_bv 64 ?e =>
replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
end;
let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

#[using="Type"] Lemma L6r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wE q1Hi q1Lo resHi resLo aDHi aDLo bHi : Z)
y1 y5 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv rsegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= q1Hi < 2^64)%Z -> (0 <= q1Lo < 2^64)%Z -> (0 <= resHi < 2^64)%Z -> (0 <= resLo < 2^64)%Z ->
(0 <= aDHi < 2^64)%Z -> (0 <= aDLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
(-869160 <= wE <= 32766)%Z ->
R = DC6 sgn wE q1Hi q1Lo resHi resLo aDHi aDLo bHi bLo ->
evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp y5 (Z_to_bv 64 resLo) (Z_to_bv 64 resHi) y8 y9 y10 sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 aDLo)
(Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aDHi)
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q1Hi) (Z_to_bv 64 wE) (Z_to_bv 64 q1Lo) y31)
F (Z_to_bv 64 0xd0e48) fc None m1 (seg_rom rsegs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 RwE HR.
pose_word_ranges.
zstep. if_cases K; zify_cond K; sgn_cond K.
-
do 2 zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
+ join Lzero. rewrite HR. apply DC6_tiny. lia.
+ do 6 zstep. rewrite !subw_amt by lia. unland. rewrite !landM32_id by lia.
zstep. if_cases K3; zify_cond K3; sgn_cond K3.
*
do 5 zstep. unland.
model_reg 10 absLo (Z.lor (Z.shiftr q1Lo (Z.land (1 - wE) 63))
(Z.land (Z.shiftl (Z.land (Z.shiftl q1Hi 1) 18446744073709551615) (Z.land (Z.lxor (1 - wE) 18446744073709551615) 63)) 18446744073709551615)).
rng absLo.
zstep. unland. model_reg 15 absHi0 (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absHi0.
zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
zstep. rewrite (srai63_mask (1 - wE + -64)) by lia. decide_ifs. rewrite land_ones_l by zrange2.
zstep. if_cases K4; zify_cond K4; sgn_cond K4.
--
do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
(Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
--
do 2 zstep. unland. model_reg 17 aSHi (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615). rng aSHi.
zstep. change (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615) with aSHi.
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (shr63_nonneg (wE + 48)), ?Z.land_0_l by lia.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (0 <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (0 - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
*
do 2 zstep. unland. model_reg 10 absLo (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absLo.
zstep. unland.
zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
zstep. rewrite (shr63_nonneg (1 - wE + -64)), ?Z.land_0_l by lia.
zstep. if_cases K4; zify_cond K4; sgn_cond K4; [ | exfalso; lia ].
do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
(Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * 0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
-
assert (K' : 0 < wE) by (rewrite land_W64 in K0, K1; Z.div_mod_to_equations; lia). clear K0 K1.
do 2 zstep. unland.
model_reg 14 fracHi (Z.land q1Hi 281474976710655).
do 4 zstep. unland. model_reg 15 absHi (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi). rng absHi.
zstep. model_reg 16 r2Hi (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)). rng r2Hi.
zstep. model_reg 14 r2Lo (Z.land (Z.shiftl resLo 1) 18446744073709551615).
zstep. model_reg 17 odd (Z.land q1Lo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ zstep | do 2 zstep ];
flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1;
(join Lround;
rewrite HR, DC6_normal, div_round_DRr by lia; unland;
change (Z.land q1Hi 281474976710655) with fracHi;
change (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi) with absHi;
change (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) with r2Hi;
change (Z.land (Z.shiftl resLo 1) 18446744073709551615) with r2Lo;
fold_model_lets2; reflexivity).
Time Qed.

#[using="Type"] Lemma L5r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (w4 : word) (expM1 q_hi q_lo aSigHiI bSigHiI aHi2 aLoTop a2Lo : Z)
y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv rsegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= q_hi < 2^64)%Z -> (0 <= q_lo < 2^64)%Z -> (0 <= aSigHiI < 2^64)%Z -> (0 <= bSigHiI < 2^64)%Z ->
(0 <= aHi2 < 2^64)%Z -> (0 <= aLoTop < 2^64)%Z -> (0 <= a2Lo < 2^64)%Z ->
(-20000 <= expM1 <= 60000)%Z ->
R = divc_tail sgn expM1 q_hi q_lo (bv_unsigned w4) aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo ->
evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 expM1) (Z_to_bv 64 aLoTop) (Z_to_bv 64 aHi2) y8 y9 w4 sgw w6
(Z_to_bv 64 bSigHiI) (Z_to_bv 64 a2Lo) (Z_to_bv 64 (Z.shiftr q_hi 49)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aSigHiI)
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q_hi) (Z_to_bv 64 (expM1 + 1)) (Z_to_bv 64 q_lo) y31)
F (Z_to_bv 64 0xd0d0c) fc None m1 (seg_rom rsegs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 Rexp HR.
pose_word_ranges.
zstep. if_cases K; zify_cond K.
-
do 3 zstep. model_reg 28 q1Hi (Z.shiftr q_hi 1). rng q1Hi.
zstep. model_reg 5 aTop (Z.land (Z.shiftl (bv_unsigned w4) 48) 18446744073709551615).
zstep. model_reg 30 q1Lo (Z.lor (Z.shiftr q_lo 1) (Z.land (Z.shiftl q_hi 63) 18446744073709551615)). rng q1Lo.
zstep. model_reg 14 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 14 d1 (Z.land (aTop - pq1) 18446744073709551615).
zstep. model_reg 5 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 15 sh (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 14 d2 (Z.land (d1 - sh) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+ rewrite <- (Z_to_bv_bv_unsigned w4). join L6r. all: try lia.
rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
-
assert (Rbit : 0 <= Z.shiftr q_hi 48 <= 1).
{ rewrite !Z.shiftr_div_pow2 in * by lia. Z.div_mod_to_equations. lia. }
zstep. name_as bit112 (Z.shiftr q_hi 48).
zstep. zstep. rewrite (ltb1_eqb0 bit112) by lia. model_reg 31 sh (Z.b2z (bit112 =? 0)).
assert (Rsh' : 0 <= sh <= 1) by (cbv delta [sh]; destruct (bit112 =? 0); cbn; lia).
zstep. rewrite (land63_id sh) by lia.
zstep. zstep.
assert (Hamt : Z.land (Z.lxor sh 63) 63 = Z.lxor sh 63) by (cbv delta [sh]; destruct (bit112 =? 0); reflexivity).
rewrite Hamt.
zstep. unland. model_reg 28 q1Hi (Z.lor (Z.land (Z.shiftl q_hi sh) 18446744073709551615) (Z.shiftr (Z.shiftr q_lo 1) (Z.lxor sh 63))). rng q1Hi.
zstep. rewrite (land63_id sh) by lia. model_reg 30 q1Lo (Z.land (Z.shiftl q_lo sh) 18446744073709551615).
zstep. if_cases Kb; zify_cond Kb.
*
zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+  join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
*
zstep.
zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+  join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
Time Qed.

#[using="Type"] Lemma divtf3_core : forall ra gp tp (w3 w4 w5 : word) (scale ea eb : Z) s0 s1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 y1
y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv rsegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
R = div_core sgn ea eb (bv_unsigned w3) (bv_unsigned w4) (bv_unsigned w5) bLo scale ->
evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) y8 y9 w4 sgw w6 a3 a4 a5 (Z_to_bv 64 281474976710655) w3
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 scale) t4 t5 t6)
F (Z_to_bv 64 0xd0a3c) fc None m1 (seg_rom rsegs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO Ra Rb Rsc HR.
pose_word_ranges.
eapply evt_cut. { eapply (divtf3_core12 w3 w4 w5 w6 ea eb scale); eauto. }
intros ms' P.
destruct P as (q_hi & q_lo & z1 & z8 & z9 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z31 & EQ & Rqh & Rql & ->).
rewrite EQ in HR.
eapply L5r; try eassumption; try exact HR.
all: try (cbv beta delta [E_aSigHiI E_bSigHiI E_aHi2 E_aLoTop E_a2Lo]; zrange).
cbv beta delta [E_expM1]. lia.
Qed.
End Walk.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QqdR QnDM_c1 QwyL QWlT QN1y Q48O QGmo QHpk QQWe QTCB QQbX QhY6 QCwx Qb01 Qn2i QGuF Qbf8 Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QZAi.Mq1 QZAi QqdR.
Import QnDM_c1.
Import QwyL QWlT QN1y Q48O QGmo QHpk QQWe QTCB QQbX.Mq0 QX7A QhY6 QIsN QCwx.Mq0 Qb01 Qn2i QGuF Qbf8 Q98Z.Mq0.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Ltac norm_rsegs :=
cbv delta [rsegs rsegs rsegs rsegs rsegs rsegs
rsegs rsegs rsegs rsegs rsegs rsegs] in *;
fold rsegs in *.

Local Open Scope Z_scope.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.

Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.

Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. intros. unfold canon. apply lo64_words. apply lo64_range. Qed.
Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. intros. unfold canon. apply hi64_words; [apply lo64_range | apply hi64_range]. Qed.
Lemma mk128_canon : forall x, mk128 (hi64 x) (lo64 x) = canon x.
Proof.
intros. unfold mk128, canon. pose proof (lo64_range x). pose proof (hi64_range x).
rewrite Z.shiftl_mul_pow2 by lia. rewrite lor_disjoint_add; [lia|].
- apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.mul_pow2_bits_low by lia. reflexivity.
+ replace (Z.testbit (lo64 x) i) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec (lo64 x) 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma canon_small : forall x, 0 <= x < 2^128 -> canon x = x.
Proof.
intros x Hx. unfold canon, lo64, hi64, wrap64, ONES64. rewrite !land_W64, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (x / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.div_mod x (2^64) ltac:(lia)). lia.
Qed.
Lemma canon_range : forall x, 0 <= canon x < 2^128.
Proof. intros. unfold canon. pose proof (lo64_range x). pose proof (hi64_range x). lia. Qed.

Lemma f128_mul_canon : forall a b, f128_mul (canon a) (canon b) = f128_mul a b.
Proof. intros. unfold f128_mul. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_div_canon : forall a b, f128_div (canon a) (canon b) = f128_div a b.
Proof. intros. unfold f128_div. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon : forall a b, f128_add (canon a) (canon b) = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon_l : forall a b, f128_add (canon a) b = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_sub_canon : forall a b, f128_sub (canon a) (canon b) = f128_sub a b.
Proof. intros. unfold f128_sub. rewrite !lo64_canon, !hi64_canon. apply f128_add_canon_l. Qed.
Lemma f128_le_canon : forall a b, f128_le (canon a) (canon b) = f128_le a b.
Proof. intros. unfold f128_le. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma fixunstfsi_a0_canon : forall a, fixunstfsi_a0 (canon a) = fixunstfsi_a0 a.
Proof. intros. unfold fixunstfsi_a0. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.

Lemma ulit_lo64 : forall x, bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. intros. apply unsigned_lit. apply lo64_range. Qed.
Lemma ulit_hi64 : forall x, bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. intros. apply unsigned_lit. apply hi64_range. Qed.

Local Open Scope bv_scope.

Definition leaf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Definition leaf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma letf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
mem_inv rsegs m ->
evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf5e4) fc None m (seg_rom rsegs)).
Proof.
intros until Y. intros MI. eapply evt_mono. { eapply letf2_spec. exact MI. }
intros ms' P. unfold letf2_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_le_canon in P. exact P.
Qed.

Lemma letf2_callv0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv rsegs m ->
evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X F128_ZERO) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf5e4) fc None m (seg_rom rsegs)).
Proof. intros. change (Z_to_bv 64 0) with (Z_to_bv 64 (lo64 0)) at 1. change (Z_to_bv 64 0) with (Z_to_bv 64 (hi64 0)) at 1. apply letf2_callv. assumption. Qed.

Lemma fixunstfsi_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv rsegs m ->
evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fixunstfsi_a0 X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd6114) fc None m (seg_rom rsegs)).
Proof.
intros until X. intros MI. eapply evt_mono. { eapply fixunstfsi_spec. exact MI. }
intros ms' P. unfold fixunstfsi_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fixunstfsi_a0_canon in P. exact P.
Qed.

Lemma floatsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (v i : Z),
mem_inv rsegs m -> (0 <= v < 2^64)%Z -> v = sext32 i ->
evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd08ac) fc None m (seg_rom rsegs)).
Proof.
intros until i. intros MI Hv Hi. eapply evt_mono. { eapply floatsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hi. }
intros ms' P. exact P.
Qed.

Lemma floatsitf_callp : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
mem_inv rsegs m -> (0 <= i < 2^31)%Z ->
evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd08ac) fc None m (seg_rom rsegs)).
Proof. intros until i. intros MI Hi. apply floatsitf_callv; [exact MI | lia |]. rewrite sext32_small by lia. reflexivity. Qed.

Lemma floatunsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (v u : Z),
mem_inv rsegs m -> (0 <= v < 2^64)%Z -> v = sext32 u ->
evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd61a8) fc None m (seg_rom rsegs)).
Proof.
intros until u. intros MI Hv Hu. eapply evt_mono. { eapply floatunsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hu. }
intros ms' P. exact P.
Qed.

Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. intros. apply sext32_congr. apply sext32_low. Qed.
Lemma floatunsitf_callfix : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (Y : Z),
mem_inv rsegs m ->
evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 (f128_to_u32 Y)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fixunstfsi_a0 Y)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd61a8) fc None m (seg_rom rsegs)).
Proof.
intros until Y. intros MI. apply floatunsitf_callv; [exact MI | |].
- unfold fixunstfsi_a0. apply sext32_range.
- unfold f128_to_u32, M32. rewrite sext32_landM32. unfold fixunstfsi_a0. symmetry. apply sext32_idem.
Qed.

Lemma extenddftf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
mem_inv rsegs m -> (0 <= D < 2^64)%Z ->
evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 0xcb77c) fc None m (seg_rom rsegs)).
Proof.
intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
intros ms' P. unfold extenddftf2_post in P. rewrite freg_get_same, unsigned_lit in P by lia. exact P.
Qed.

Definition call2_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(K : Z) (R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - K, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - K) q.

Lemma multf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk rsegs m (q - 80) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf768) fc None m (seg_rom rsegs)).
Proof.
intros until Y. intros ST MI Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (multf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold multf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_mul_canon in P. exact P.
Qed.

Lemma divtf3_callq : divtf3_stmt -> forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk rsegs m (q - 112) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd09b4) fc None m (seg_rom rsegs)).
Proof.
intros DS. intros until Y. intros ST MI Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (DS ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold divtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_div_canon in P. exact P.
Qed.

Definition calla_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(q - 48, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ stk rsegs m' (q - 48) q.

Lemma addtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0094) fc None m (seg_rom rsegs)).
Proof.
intros until Y. intros ST MI FRM Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (addtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_add_canon in P. exact P.
Qed.

Lemma subtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd089c) fc None m (seg_rom rsegs)).
Proof.
intros until Y. intros ST MI FRM Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (subtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_sub_canon in P. exact P.
Qed.

Definition frexpl_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P x E : Z) (rest : list cell) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 32, q); (P, P + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 32) q
/\ rw_cells rsegs m' P (C4 (Z_to_bv 64 e') :: rest)
/\ frexpl FREXPL_FUEL x E = Some (x', e').

Lemma frexpl_callq : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell),
stk rsegs m (q - 32) q -> mem_inv rsegs m ->
rw_cells rsegs m P (C4 (Z_to_bv 64 E) :: rest) ->
(P + 4 + Z.of_nat (cells_size rest) <= q - 32 \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
(Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
evt rsegs (frexpl_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf50c) fc None m (seg_rom rsegs)).
Proof.
intros until rest. intros ST MI CE SEP Hq HP PRE.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (Ep : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
pose proof (rw_cells_bound _ _ _ _ CE) as BR. cbn [cells_size csize] in BR.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in CE. destruct CE as [CE CR]. cbn [cells_size csize Nat.add] in CR.
change (Z.of_nat 4) with 4%Z in CR.
eapply evt_mono.
{ eapply (frexpl_spec ra (Z_to_bv 64 q)); rewrite ?Eq, ?Ep, ?ulit_lo64, ?ulit_hi64; eauto; try lia.
cbv zeta. change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X). rewrite hi64_canon.
unfold F128_ZERO in *. rewrite <- (f128_le_canon X 0) in PRE. replace (canon 0) with 0%Z in PRE by reflexivity. exact PRE. }
intros ms' Q. unfold frexpl_post in Q. rewrite !Eq, !Ep, !ulit_lo64, !ulit_hi64 in Q.
destruct Q as (x' & e' & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & CE' & HF).
unfold frexpl_postq. exists x', e'. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [|exact HF].
apply (proj2 (rw_cells_app rsegs _ _ [_] _)). split; [exact CE'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4%Z.
eapply rw_cells_transport; [exact CR | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia|]. split; [lia|exact I].
Qed.

Lemma signbitl_canon : forall x, signbitl (canon x) = signbitl x.
Proof. intros. unfold signbitl. rewrite hi64_canon. reflexivity. Qed.
Lemma fpclassifyl_canon : forall x, fpclassifyl (canon x) = fpclassifyl x.
Proof. intros. unfold fpclassifyl. rewrite lo64_canon, hi64_canon. reflexivity. Qed.

Definition signbitl_postv (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma signbitl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv rsegs m ->
evt rsegs (signbitl_postv ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (signbitl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd610c) fc None m (seg_rom rsegs)).
Proof.
intros until X. intros MI. eapply evt_mono. { eapply signbitl_spec. exact MI. }
intros ms' P. unfold signbitl_post, signbitl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite signbitl_canon in P. exact P.
Qed.

Definition fpclassifyl_postv (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma fpclassifyl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv rsegs m ->
evt rsegs (fpclassifyl_postv ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (fpclassifyl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0050) fc None m (seg_rom rsegs)).
Proof.
intros until X. intros MI. eapply evt_mono. { eapply fpclassifyl_spec. exact MI. }
intros ms' P. unfold fpclassifyl_post, fpclassifyl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fpclassifyl_canon in P. exact P.
Qed.

Lemma lo64_flip_sign : forall x, lo64 (Z.lxor x F128_SIGNBIT) = lo64 x.
Proof.
intros. unfold lo64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
change 0x80000000000000000000000000000000%Z with (2^127)%Z.
apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.lxor_spec, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 127 i); [lia|]. now rewrite Bool.xorb_false_r.
- rewrite Z.ones_spec_high by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma hi64_flip_sign : forall x, hi64 (Z.lxor x F128_SIGNBIT) = Z.lxor (hi64 x) 9223372036854775808.
Proof.
intros. unfold hi64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
change 0x80000000000000000000000000000000%Z with (2^127)%Z. change 9223372036854775808%Z with (2^63)%Z.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !Z.land_spec, !Z.shiftr_spec, Z.lxor_spec, !Z.pow2_bits_eqb by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite !Bool.andb_true_r.
destruct (Z.eqb_spec 127 (i + 64)), (Z.eqb_spec 63 i); try lia; reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite !Bool.andb_false_r. destruct (Z.eqb_spec 63 i); [lia|reflexivity].
Qed.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFef QOaC Qra5 Q7ap QRsj Q0aA Q1m9 QkAv QvVw QNtS QbN3 Q4tl QFqQ QeTw QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QZAi.Mq1 QZAi QqdR.
Import QnDM_c1.
Import QFef QOaC QCwx Qra5 Q7ap QRsj Q0aA Q1m9 QQbX.Mq4 QkAv QvVw QNtS QCwx.Mq2 QbN3 Q4tl QFqQ QeTw Q98Z.Mq3.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Ltac norm_rsegs :=
cbv delta [usegs usegs usegs usegs usegs usegs
usegs usegs usegs usegs usegs usegs] in *;
fold usegs in *.

Local Open Scope Z_scope.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.

Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.

Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. intros. unfold canon. apply lo64_words. apply lo64_range. Qed.
Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. intros. unfold canon. apply hi64_words; [apply lo64_range | apply hi64_range]. Qed.
Lemma mk128_canon : forall x, mk128 (hi64 x) (lo64 x) = canon x.
Proof.
intros. unfold mk128, canon. pose proof (lo64_range x). pose proof (hi64_range x).
rewrite Z.shiftl_mul_pow2 by lia. rewrite lor_disjoint_add; [lia|].
- apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.mul_pow2_bits_low by lia. reflexivity.
+ replace (Z.testbit (lo64 x) i) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec (lo64 x) 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma canon_small : forall x, 0 <= x < 2^128 -> canon x = x.
Proof.
intros x Hx. unfold canon, lo64, hi64, wrap64, ONES64. rewrite !land_W64, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (x / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.div_mod x (2^64) ltac:(lia)). lia.
Qed.
Lemma canon_range : forall x, 0 <= canon x < 2^128.
Proof. intros. unfold canon. pose proof (lo64_range x). pose proof (hi64_range x). lia. Qed.

Lemma f128_mul_canon : forall a b, f128_mul (canon a) (canon b) = f128_mul a b.
Proof. intros. unfold f128_mul. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_div_canon : forall a b, f128_div (canon a) (canon b) = f128_div a b.
Proof. intros. unfold f128_div. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon : forall a b, f128_add (canon a) (canon b) = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon_l : forall a b, f128_add (canon a) b = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_sub_canon : forall a b, f128_sub (canon a) (canon b) = f128_sub a b.
Proof. intros. unfold f128_sub. rewrite !lo64_canon, !hi64_canon. apply f128_add_canon_l. Qed.
Lemma f128_le_canon : forall a b, f128_le (canon a) (canon b) = f128_le a b.
Proof. intros. unfold f128_le. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma fixunstfsi_a0_canon : forall a, fixunstfsi_a0 (canon a) = fixunstfsi_a0 a.
Proof. intros. unfold fixunstfsi_a0. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.

Lemma ulit_lo64 : forall x, bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. intros. apply unsigned_lit. apply lo64_range. Qed.
Lemma ulit_hi64 : forall x, bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. intros. apply unsigned_lit. apply hi64_range. Qed.

Local Open Scope bv_scope.

Definition leaf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Definition leaf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma letf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
mem_inv usegs m ->
evt usegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1ca8) fc None m (seg_rom usegs)).
Proof.
intros until Y. intros MI. eapply evt_mono. { eapply letf2_spec. exact MI. }
intros ms' P. unfold letf2_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_le_canon in P. exact P.
Qed.

Lemma letf2_callv0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv usegs m ->
evt usegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X F128_ZERO) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1ca8) fc None m (seg_rom usegs)).
Proof. intros. change (Z_to_bv 64 0) with (Z_to_bv 64 (lo64 0)) at 1. change (Z_to_bv 64 0) with (Z_to_bv 64 (hi64 0)) at 1. apply letf2_callv. assumption. Qed.

Lemma fixunstfsi_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv usegs m ->
evt usegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fixunstfsi_a0 X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd87d8) fc None m (seg_rom usegs)).
Proof.
intros until X. intros MI. eapply evt_mono. { eapply fixunstfsi_spec. exact MI. }
intros ms' P. unfold fixunstfsi_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fixunstfsi_a0_canon in P. exact P.
Qed.

Lemma floatsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (v i : Z),
mem_inv usegs m -> (0 <= v < 2^64)%Z -> v = sext32 i ->
evt usegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2f70) fc None m (seg_rom usegs)).
Proof.
intros until i. intros MI Hv Hi. eapply evt_mono. { eapply floatsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hi. }
intros ms' P. exact P.
Qed.

Lemma floatsitf_callp : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
mem_inv usegs m -> (0 <= i < 2^31)%Z ->
evt usegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2f70) fc None m (seg_rom usegs)).
Proof. intros until i. intros MI Hi. apply floatsitf_callv; [exact MI | lia |]. rewrite sext32_small by lia. reflexivity. Qed.

Lemma floatunsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (v u : Z),
mem_inv usegs m -> (0 <= v < 2^64)%Z -> v = sext32 u ->
evt usegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd886c) fc None m (seg_rom usegs)).
Proof.
intros until u. intros MI Hv Hu. eapply evt_mono. { eapply floatunsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hu. }
intros ms' P. exact P.
Qed.

Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. intros. apply sext32_congr. apply sext32_low. Qed.
Lemma floatunsitf_callfix : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (Y : Z),
mem_inv usegs m ->
evt usegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 (f128_to_u32 Y)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fixunstfsi_a0 Y)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd886c) fc None m (seg_rom usegs)).
Proof.
intros until Y. intros MI. apply floatunsitf_callv; [exact MI | |].
- unfold fixunstfsi_a0. apply sext32_range.
- unfold f128_to_u32, M32. rewrite sext32_landM32. unfold fixunstfsi_a0. symmetry. apply sext32_idem.
Qed.

Lemma extenddftf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
mem_inv usegs m -> (0 <= D < 2^64)%Z ->
evt usegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 0xcde40) fc None m (seg_rom usegs)).
Proof.
intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
intros ms' P. unfold extenddftf2_post in P. rewrite freg_get_same, unsigned_lit in P by lia. exact P.
Qed.

Definition call2_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(K : Z) (R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - K, q)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - K) q.

Lemma multf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk usegs m (q - 80) q -> mem_inv usegs m -> (4096 <= q < 2^64)%Z ->
evt usegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1e2c) fc None m (seg_rom usegs)).
Proof.
intros until Y. intros ST MI Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (multf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold multf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_mul_canon in P. exact P.
Qed.

Lemma divtf3_callq : divtf3_stmt -> forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk usegs m (q - 112) q -> mem_inv usegs m -> (4096 <= q < 2^64)%Z ->
evt usegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3078) fc None m (seg_rom usegs)).
Proof.
intros DS. intros until Y. intros ST MI Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (DS ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold divtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_div_canon in P. exact P.
Qed.

Definition calla_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m' (seg_rom usegs)
/\ munch [(q - 48, q)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ frm0 fc'
/\ stk usegs m' (q - 48) q.

Lemma addtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk usegs m (q - 48) q -> mem_inv usegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
evt usegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2758) fc None m (seg_rom usegs)).
Proof.
intros until Y. intros ST MI FRM Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (addtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_add_canon in P. exact P.
Qed.

Lemma subtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk usegs m (q - 48) q -> mem_inv usegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
evt usegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2f60) fc None m (seg_rom usegs)).
Proof.
intros until Y. intros ST MI FRM Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (subtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_sub_canon in P. exact P.
Qed.

Definition frexpl_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P x E : Z) (rest : list cell) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - 32, q); (P, P + 4)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - 32) q
/\ rw_cells usegs m' P (C4 (Z_to_bv 64 e') :: rest)
/\ frexpl FREXPL_FUEL x E = Some (x', e').

Lemma frexpl_callq : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell),
stk usegs m (q - 32) q -> mem_inv usegs m ->
rw_cells usegs m P (C4 (Z_to_bv 64 E) :: rest) ->
(P + 4 + Z.of_nat (cells_size rest) <= q - 32 \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
(Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
evt usegs (frexpl_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1bd0) fc None m (seg_rom usegs)).
Proof.
intros until rest. intros ST MI CE SEP Hq HP PRE.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (Ep : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
pose proof (rw_cells_bound _ _ _ _ CE) as BR. cbn [cells_size csize] in BR.
apply (proj1 (rw_cells_app usegs _ _ [_] _)) in CE. destruct CE as [CE CR]. cbn [cells_size csize Nat.add] in CR.
change (Z.of_nat 4) with 4%Z in CR.
eapply evt_mono.
{ eapply (frexpl_spec ra (Z_to_bv 64 q)); rewrite ?Eq, ?Ep, ?ulit_lo64, ?ulit_hi64; eauto; try lia.
cbv zeta. change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X). rewrite hi64_canon.
unfold F128_ZERO in *. rewrite <- (f128_le_canon X 0) in PRE. replace (canon 0) with 0%Z in PRE by reflexivity. exact PRE. }
intros ms' Q. unfold frexpl_post in Q. rewrite !Eq, !Ep, !ulit_lo64, !ulit_hi64 in Q.
destruct Q as (x' & e' & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & CE' & HF).
unfold frexpl_postq. exists x', e'. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [|exact HF].
apply (proj2 (rw_cells_app usegs _ _ [_] _)). split; [exact CE'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4%Z.
eapply rw_cells_transport; [exact CR | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia|]. split; [lia|exact I].
Qed.

Lemma signbitl_canon : forall x, signbitl (canon x) = signbitl x.
Proof. intros. unfold signbitl. rewrite hi64_canon. reflexivity. Qed.
Lemma fpclassifyl_canon : forall x, fpclassifyl (canon x) = fpclassifyl x.
Proof. intros. unfold fpclassifyl. rewrite lo64_canon, hi64_canon. reflexivity. Qed.

Definition signbitl_postv (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs)
/\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m.
Lemma signbitl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv usegs m ->
evt usegs (signbitl_postv ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (signbitl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd87d0) fc None m (seg_rom usegs)).
Proof.
intros until X. intros MI. eapply evt_mono. { eapply signbitl_spec. exact MI. }
intros ms' P. unfold signbitl_post, signbitl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite signbitl_canon in P. exact P.
Qed.

Definition fpclassifyl_postv (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs)
/\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m.
Lemma fpclassifyl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv usegs m ->
evt usegs (fpclassifyl_postv ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (fpclassifyl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2714) fc None m (seg_rom usegs)).
Proof.
intros until X. intros MI. eapply evt_mono. { eapply fpclassifyl_spec. exact MI. }
intros ms' P. unfold fpclassifyl_post, fpclassifyl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fpclassifyl_canon in P. exact P.
Qed.

Lemma lo64_flip_sign : forall x, lo64 (Z.lxor x F128_SIGNBIT) = lo64 x.
Proof.
intros. unfold lo64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
change 0x80000000000000000000000000000000%Z with (2^127)%Z.
apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.lxor_spec, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 127 i); [lia|]. now rewrite Bool.xorb_false_r.
- rewrite Z.ones_spec_high by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma hi64_flip_sign : forall x, hi64 (Z.lxor x F128_SIGNBIT) = Z.lxor (hi64 x) 9223372036854775808.
Proof.
intros. unfold hi64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
change 0x80000000000000000000000000000000%Z with (2^127)%Z. change 9223372036854775808%Z with (2^63)%Z.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !Z.land_spec, !Z.shiftr_spec, Z.lxor_spec, !Z.pow2_bits_eqb by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite !Bool.andb_true_r.
destruct (Z.eqb_spec 127 (i + 64)), (Z.eqb_spec 63 i); try lia; reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite !Bool.andb_false_r. destruct (Z.eqb_spec 63 i); [lia|reflexivity].
Qed.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUrT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUrT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkAv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkAv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNtS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNtS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgeq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgeq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Jo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Jo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvs9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvs9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Section Walk.
Variables (sp sgw w6 : word).
Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation sgn := (bv_unsigned sgw).
Notation bLo := (bv_unsigned w6).

Ltac hyp :=
match goal with
| H : mem_inv _ ?m |- mem_inv _ ?m => exact H
| H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
| H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
| H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
| H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
| H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
| H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
| |- (_ <= _ <= _)%Z => lia
| |- (0 <= _ < _)%Z => first [zrange2 | lia]
end.
Ltac join L := eapply L; try hyp.

Ltac flag_join n G body K :=
set (G := body);
let w := getreg n in
lazymatch w with Z_to_bv 64 ?e =>
replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
end;
let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

#[using="Type"] Lemma L6r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wE q1Hi q1Lo resHi resLo aDHi aDLo bHi : Z)
y1 y5 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv usegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
stk usegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells usegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= q1Hi < 2^64)%Z -> (0 <= q1Lo < 2^64)%Z -> (0 <= resHi < 2^64)%Z -> (0 <= resLo < 2^64)%Z ->
(0 <= aDHi < 2^64)%Z -> (0 <= aDLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
(-869544 <= wE <= 32766)%Z ->
R = DC6 sgn wE q1Hi q1Lo resHi resLo aDHi aDLo bHi bLo ->
evt usegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp y5 (Z_to_bv 64 resLo) (Z_to_bv 64 resHi) y8 y9 y10 sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 aDLo)
(Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aDHi)
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q1Hi) (Z_to_bv 64 wE) (Z_to_bv 64 q1Lo) y31)
F (Z_to_bv 64 0xd350c) fc None m1 (seg_rom usegs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 RwE HR.
pose_word_ranges.
zstep. if_cases K; zify_cond K; sgn_cond K.
-
do 2 zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
+ join Lzero. rewrite HR. apply DC6_tiny. lia.
+ do 6 zstep. rewrite !subw_amt by lia. unland. rewrite !landM32_id by lia.
zstep. if_cases K3; zify_cond K3; sgn_cond K3.
*
do 5 zstep. unland.
model_reg 10 absLo (Z.lor (Z.shiftr q1Lo (Z.land (1 - wE) 63))
(Z.land (Z.shiftl (Z.land (Z.shiftl q1Hi 1) 18446744073709551615) (Z.land (Z.lxor (1 - wE) 18446744073709551615) 63)) 18446744073709551615)).
rng absLo.
zstep. unland. model_reg 15 absHi0 (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absHi0.
zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
zstep. rewrite (srai63_mask (1 - wE + -64)) by lia. decide_ifs. rewrite land_ones_l by zrange2.
zstep. if_cases K4; zify_cond K4; sgn_cond K4.
--
do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
(Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
--
do 2 zstep. unland. model_reg 17 aSHi (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615). rng aSHi.
zstep. change (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615) with aSHi.
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (shr63_nonneg (wE + 48)), ?Z.land_0_l by lia.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (0 <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (0 - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
*
do 2 zstep. unland. model_reg 10 absLo (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absLo.
zstep. unland.
zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
zstep. rewrite (shr63_nonneg (1 - wE + -64)), ?Z.land_0_l by lia.
zstep. if_cases K4; zify_cond K4; sgn_cond K4; [ | exfalso; lia ].
do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
(Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * 0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
-
assert (K' : 0 < wE) by (rewrite land_W64 in K0, K1; Z.div_mod_to_equations; lia). clear K0 K1.
do 2 zstep. unland.
model_reg 14 fracHi (Z.land q1Hi 281474976710655).
do 4 zstep. unland. model_reg 15 absHi (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi). rng absHi.
zstep. model_reg 16 r2Hi (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)). rng r2Hi.
zstep. model_reg 14 r2Lo (Z.land (Z.shiftl resLo 1) 18446744073709551615).
zstep. model_reg 17 odd (Z.land q1Lo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ zstep | do 2 zstep ];
flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1;
(join Lround;
rewrite HR, DC6_normal, div_round_DRr by lia; unland;
change (Z.land q1Hi 281474976710655) with fracHi;
change (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi) with absHi;
change (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) with r2Hi;
change (Z.land (Z.shiftl resLo 1) 18446744073709551615) with r2Lo;
fold_model_lets2; reflexivity).
Time Qed.

#[using="Type"] Lemma L5r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (w4 : word) (expM1 q_hi q_lo aSigHiI bSigHiI aHi2 aLoTop a2Lo : Z)
y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv usegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
stk usegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells usegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= q_hi < 2^64)%Z -> (0 <= q_lo < 2^64)%Z -> (0 <= aSigHiI < 2^64)%Z -> (0 <= bSigHiI < 2^64)%Z ->
(0 <= aHi2 < 2^64)%Z -> (0 <= aLoTop < 2^64)%Z -> (0 <= a2Lo < 2^64)%Z ->
(-20000 <= expM1 <= 60000)%Z ->
R = divc_tail sgn expM1 q_hi q_lo (bv_unsigned w4) aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo ->
evt usegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 expM1) (Z_to_bv 64 aLoTop) (Z_to_bv 64 aHi2) y8 y9 w4 sgw w6
(Z_to_bv 64 bSigHiI) (Z_to_bv 64 a2Lo) (Z_to_bv 64 (Z.shiftr q_hi 49)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aSigHiI)
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q_hi) (Z_to_bv 64 (expM1 + 1)) (Z_to_bv 64 q_lo) y31)
F (Z_to_bv 64 0xd33d0) fc None m1 (seg_rom usegs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 Rexp HR.
pose_word_ranges.
zstep. if_cases K; zify_cond K.
-
do 3 zstep. model_reg 28 q1Hi (Z.shiftr q_hi 1). rng q1Hi.
zstep. model_reg 5 aTop (Z.land (Z.shiftl (bv_unsigned w4) 48) 18446744073709551615).
zstep. model_reg 30 q1Lo (Z.lor (Z.shiftr q_lo 1) (Z.land (Z.shiftl q_hi 63) 18446744073709551615)). rng q1Lo.
zstep. model_reg 14 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 14 d1 (Z.land (aTop - pq1) 18446744073709551615).
zstep. model_reg 5 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 15 sh (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 14 d2 (Z.land (d1 - sh) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+ rewrite <- (Z_to_bv_bv_unsigned w4). join L6r. all: try lia.
rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
-
assert (Rbit : 0 <= Z.shiftr q_hi 48 <= 1).
{ rewrite !Z.shiftr_div_pow2 in * by lia. Z.div_mod_to_equations. lia. }
zstep. name_as bit112 (Z.shiftr q_hi 48).
zstep. zstep. rewrite (ltb1_eqb0 bit112) by lia. model_reg 31 sh (Z.b2z (bit112 =? 0)).
assert (Rsh' : 0 <= sh <= 1) by (cbv delta [sh]; destruct (bit112 =? 0); cbn; lia).
zstep. rewrite (land63_id sh) by lia.
zstep. zstep.
assert (Hamt : Z.land (Z.lxor sh 63) 63 = Z.lxor sh 63) by (cbv delta [sh]; destruct (bit112 =? 0); reflexivity).
rewrite Hamt.
zstep. unland. model_reg 28 q1Hi (Z.lor (Z.land (Z.shiftl q_hi sh) 18446744073709551615) (Z.shiftr (Z.shiftr q_lo 1) (Z.lxor sh 63))). rng q1Hi.
zstep. rewrite (land63_id sh) by lia. model_reg 30 q1Lo (Z.land (Z.shiftl q_lo sh) 18446744073709551615).
zstep. if_cases Kb; zify_cond Kb.
*
zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+  join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
*
zstep.
zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+  join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
Time Qed.

#[using="Type"] Lemma divtf3_core : forall ra gp tp (w3 w4 w5 : word) (scale ea eb : Z) s0 s1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 y1
y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv usegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
stk usegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells usegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
R = div_core sgn ea eb (bv_unsigned w3) (bv_unsigned w4) (bv_unsigned w5) bLo scale ->
evt usegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) y8 y9 w4 sgw w6 a3 a4 a5 (Z_to_bv 64 281474976710655) w3
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 scale) t4 t5 t6)
F (Z_to_bv 64 0xd3100) fc None m1 (seg_rom usegs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO Ra Rb Rsc HR.
pose_word_ranges.
eapply evt_cut. { eapply (divtf3_core12 w3 w4 w5 w6 ea eb scale); eauto. }
intros ms' P.
destruct P as (q_hi & q_lo & z1 & z8 & z9 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z31 & EQ & Rqh & Rql & ->).
rewrite EQ in HR.
eapply L5r; try eassumption; try exact HR.
all: try (cbv beta delta [E_aSigHiI E_bSigHiI E_aHi2 E_aLoTop E_a2Lo]; zrange).
cbv beta delta [E_expM1]. lia.
Qed.
End Walk.
