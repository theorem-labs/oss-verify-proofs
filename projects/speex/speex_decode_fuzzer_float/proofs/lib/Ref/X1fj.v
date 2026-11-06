(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho X1hm X1ev X1ex X1fh X1fi.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Section Post.
Context {RCEIL : RunCeiling}.
Variables (EB eoff ne pitch lo : Z) (eb : list word) (m0 : mem).

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.

Variables z0 f24 f23 f22 f21 f20 f19 f18 f9 f8 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis EOFF : eoff = 294 \/ eoff = 374.
Hypothesis HP : 17 <= pitch <= 144.
Hypothesis LOW : lo + 4352 <= bv_unsigned sp.
Hypothesis GLO : NB_GLOBALS_TOP <= lo.
Hypothesis SP63 : bv_unsigned sp < 2^63.
Hypothesis AEB : apart EB 2000 lo (bv_unsigned sp - lo).
Hypothesis ANE : apart ne 320 lo (bv_unsigned sp - lo).
Hypothesis ANEB : apart ne 320 EB 2000.
Local Notation exc := (EB + 4 * eoff).
Local Notation usp := (bv_unsigned sp).
Local Notation FRAME := [C8 z0; C8 f24; C8 f23; C8 f22; C8 f21; C8 f20; C8 f19; C8 f18; C8 f9; C8 f8;
C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac unk := cbv delta [callR]; match goal with k : iclob |- _ =>
destruct k;
cbn [X1ho.c_t0 X1ho.c_t1 X1ho.c_t2 X1ho.c_a1 X1ho.c_a2 X1ho.c_a3 X1ho.c_a4
X1ho.c_a5 X1ho.c_a6 X1ho.c_a7 X1ho.c_t3 X1ho.c_t4 X1ho.c_t5 X1ho.c_t6] end.

#[using="LEB EOFF HP LOW GLO AEB ANE ANEB"] Lemma mc_post : forall (ip1 ip2 ns : list word) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(G : bvmap 5 word) (fc : bv 32) (m : mem),
length ip1 = 80%nat -> length ip2 = 80%nat -> length ns = 80%nat ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp); (ne, ne + 320)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m ne (f32 ns) ->
rw_cells rsegs m (usp + -800) (f32 ip1) -> rw_cells rsegs m (usp + -480) (f32 ip2) ->
rw_cells rsegs m (usp + -160) FRAME -> stk rsegs m lo (usp + -800) ->
evt rsegs (multicomb_post ne lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0)
(MS (mkR xra (Z_to_bv 64 (usp + -800)) gp tp t0 t1 t2 sp (Z_to_bv 64 ne) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 exc) (Z_to_bv 64 (usp + -800)) (Z_to_bv 64 (usp + -480))
(Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 320) s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x21564) fc None m (seg_rom rsegs)).
Proof.
intros ip1 ip2 ns xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 G fc m LIP1 LIP2 LNS FRM MI MU WM XEB XNE IE1 IE2 FR ST.
pose proof AEB as AEB'. pose proof ANE as ANE'. pose proof ANEB as ANEB'. unfold apart in AEB', ANE', ANEB'.
pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO'.
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB.
pose proof (rw_cells_bound _ _ _ _ XNE) as BNE; rewrite cells_size_f32, LNS in BNE.
assert (R3 : eoff + 80 <= 500) by lia. assert (R4 : 0 <= eoff) by lia.

do 4 zstep.
call (inner_prod_spec ip1 ip1 20 (usp + -800) (usp + -800));
[ exact MI | lia | rewrite LIP1; reflexivity | rewrite LIP1; reflexivity | exact IE1 | exact IE1 | exact FRM | ].
rename MI0 into MI || idtac.
do 7 zstep.
call (inner_prod_spec ip2 ip2 20 (usp + -480) (usp + -480));
[ exact MI | lia | rewrite LIP2; reflexivity | rewrite LIP2; reflexivity | exact IE2 | exact IE2 | assumption | ].
rename MI0 into MI || idtac.
destruct (eb_window _ EB eb eoff XEB LEB ltac:(lia) ltac:(lia)) as [WY LY].
do 5 zstep.
call (inner_prod_spec (firstn 80 (skipn (Z.to_nat eoff) eb)) (firstn 80 (skipn (Z.to_nat eoff) eb)) 20 exc exc);
[ exact MI | lia | exact LY | exact LY | exact WY | exact WY | assumption | ].
rename MI0 into MI || idtac. clear WY.
destruct (eb_window _ EB eb eoff XEB LEB ltac:(lia) ltac:(lia)) as [WY _].
do 7 zstep.
call (inner_prod_spec ip1 (firstn 80 (skipn (Z.to_nat eoff) eb)) 20 (usp + -800) exc);
[ exact MI | lia | rewrite LIP1; reflexivity | exact LY | exact IE1 | exact WY | assumption | ].
rename MI0 into MI || idtac. clear WY.

match goal with H : frm0 _ |- _ => rename H into FRMx end.
assert (HI2 : usp + -480 = usp + -800 + 320) by lia.
call (mc_mid EB eoff ne (usp + -800) (usp + -480) pitch eb ip2 (Z_to_bv 64 (usp + -800)) gp tp sp (Z_to_bv 64 320) s9 s10 s11 LEB LIP2 R3 R4 HP);
[ exact FRMx | exact MI | exact XEB | exact IE2 | ].
rename MI0 into MI || idtac. clear FRMx.

destruct ns as [|n0 nrest]; [cbn in LNS; lia|]. cbn [length] in LNS.
match goal with H : frm0 _ |- _ => rename H into FRMx end.
assert (ANI : apart ne 320 (usp + -800) 640) by (unfold apart; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (loop1 EB eoff ne (usp + -800) (usp + -480) eb ip1 ip2 mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
LEB LIP1 LIP2 R3 R4 HI2 ANEB ANI 79%nat [] nrest 0 ne exc (usp + -800) (usp + -480) n0);
[ lia | reflexivity | reflexivity | lia | lia | lia | lia | exact FRMx | exact MI
| apply munch_refl | apply wmono_refl | exact XEB | exact IE1 | exact IE2 | apply rw_cells_nil; lia | exact XNE | ] end.
rename MI0 into MI || idtac. clear FRMx.
match goal with H : frm0 _, H2 : rw_cells _ _ ne (f32 ?c), H3 : length ?c = 80%nat |- _ =>
rename H into FRMx; rename H2 into XN1; rename H3 into LN1 end.

do 5 zstep.
lazymatch goal with |- evt _ _ (MS _ ?GG _ ?fcx _ ?mc _) =>
eapply evt_cut; [eapply (loop2 ne _ mc) with (k := 79%nat) (i := 0) (G := GG) (fc := fcx);
[exact LN1 | lia | lia | lia | assumption | exact MI | exact XN1] | ] end.
try clear FRMx. intros ms' PO; first [ sf_destruct 4%nat PO as GL2 fcl2 -> FRMx | sf_fb; destruct PO as (GL2 & fcl2 & -> & FRMx) ].

do 8 zstep. if_false_x. do 2 zstep.
lazymatch goal with |- evt _ _ (MS _ ?GG _ ?fcx _ ?mc _) =>
eapply evt_cut; [eapply (loop3 EB eoff eb mc) with (k := 79%nat) (i := 0) (G := GG) (fc := fcx);
[exact LEB | lia | lia | lia | lia | lia | assumption | exact MI | exact XEB] | ] end.
try match goal with H : frm0 _ |- _ => clear H end. intros ms' PO; first [ sf_destruct 4%nat PO as GL3 fcl3 -> FRM | sf_fb; destruct PO as (GL3 & fcl3 & -> & FRM) ].

do 11 zstep. join 0x217f8 0 1.
do 2 zstep. join 0x21804 0 1.
do 3 zstep. join 0x21814 0 1.
zstep. if_false_x. do 2 zstep.

match type of XN1 with rw_cells _ _ _ (f32 ?c) =>
destruct c as [|n1 nrest1]; [cbn in LN1; lia|]; cbn [length] in LN1 end.
match goal with H : frm0 _ |- _ => rename H into FRMx end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (loop4 ne mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 79%nat [] nrest1 0 ne n1);
[ lia | reflexivity | reflexivity | lia | exact FRMx | exact MI | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia | exact XN1 | ] end.
rename MI0 into MI || idtac. clear FRMx.
match goal with H : frm0 _, H2 : rw_cells _ _ ne (f32 ?c), H3 : length ?c = 80%nat |- _ =>
rename H into FRM; rename H2 into XN2; rename H3 into LN2 end.

zstep. do 19 zstep. zstep. zstep.

match type of IE1 with rw_cells _ _ _ (f32 ?l) => pose proof (rw_cells_f32_CB rsegs _ _ l IE1) as J1 end. clear IE1.
match type of IE2 with rw_cells _ _ _ (f32 ?l) => pose proof (rw_cells_f32_CB rsegs _ _ l IE2) as J2 end. clear IE2.
rewrite LIP1 in J1. change (4 * 80)%nat with 320%nat in J1.
match type of J2 with rw_cells _ _ _ [CB (4 * length ?l) _] =>
match goal with H : length l = 80%nat |- _ => rewrite H in J2 end end. change (4 * 80)%nat with 320%nat in J2.
chunk_cat J1 J2. chunk_cat J1 FR.
release_frame J1 ST (bv_unsigned sp).
apply evt_done; unfold multicomb_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _. split; [reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [exact MI|]. split; [exact FRM|].
split; [exact ST|]. split; [exact XN2| exact LN2].
Qed.
End Post.
