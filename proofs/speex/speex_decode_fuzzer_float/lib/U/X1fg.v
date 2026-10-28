(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1f0 X1ex X1ew X1fj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma lts_ge_false a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.

Definition JP (pc : Z) (m : mem) (P2 : Z -> Prop)
(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
: machine_state -> Prop :=
fun ms => exists (p2 : Z) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 p2) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F' (Z_to_bv 64 pc) fc' None m (seg_rom rsegs)
/\ frm0 fc' /\ P2 p2.

Ltac unk := cbv delta [callR]; match goal with k : iclob |- _ =>
destruct k;
cbn [X1ho.c_t0 X1ho.c_t1 X1ho.c_t2 X1ho.c_a1 X1ho.c_a2 X1ho.c_a3 X1ho.c_a4
X1ho.c_a5 X1ho.c_a6 X1ho.c_a7 X1ho.c_t3 X1ho.c_t4 X1ho.c_t5 X1ho.c_t6] end.

Section M.
Context {RCEIL : RunCeiling}.

Lemma multicomb_proof : multicomb_stmt.
Proof.
intros EB eoff ne AK pitch lo eb ns ak stk8. intros until m.
intros XEB LEB EOFF XNE LNS XAK LAK HP ST LOW GLO SP63 AEB ANE AAK ANEB ANEA EB0 EBA NEA NEP SPA -> -> -> -> -> -> -> -> MI FRM.
pose proof AEB as AEB'. pose proof ANE as ANE'. pose proof AAK as AAK'. pose proof ANEB as ANEB'. pose proof ANEA as ANEA'.
unfold apart in AEB', ANE', AAK', ANEB', ANEA'.
unfold MULTICOMB_DEPTH in LOW. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO'. unfold A_multicomb.
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB.
pose proof (rw_cells_bound _ _ _ _ XNE) as BNE; rewrite cells_size_f32, LNS in BNE.
pose proof (rw_cells_bound _ _ _ _ XAK) as BAK; rewrite cells_size_f32, LAK in BAK.
pose proof (munch_refl [(lo, bv_unsigned sp); (ne, ne + 320)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.

zstep. carve_frame 176%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 22%nat _ FR) as (fw & Lfw & FR'); clear FR.
destruct fw as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [|w21 [|? ?]]]]]]]]]]]]]]]]]]]]]]];
cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
lstep. do 22 zstep.
do 5 zstep. ub_dec. do 3 zstep. ub_dec.
do 8 zstep. replace (bv_unsigned sp + -176 - 640) with (bv_unsigned sp + -816) by lia.

carve_frame 640%nat ST. rename FR0 into IEXC.
carve_frame 3448%nat ST. rename FR0 into J1.
carve_frame 8%nat ST. rename FR0 into P1.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ P1) as (pw1 & Lp1 & P1'); clear P1. destruct pw1 as [|p1w [|? ?]]; cbn in Lp1; try lia. cbn [map] in P1'. rename P1' into P1.
zstep. zstep. replace (bv_unsigned sp + -176 - 4096) with (bv_unsigned sp + -4272) by lia.
lstep. zstep. unshelve epose proof (lts_ge_false (bv_unsigned sp + -816) (bv_unsigned sp + -4272) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB. zstep.
chunk_cat P1 J1. release_frame P1 ST (bv_unsigned sp + -816).
destruct (rw_cells_CB_f32 rsegs _ _ 160%nat _ IEXC) as (ie & Lie & IE); clear IEXC.
destruct (f32_split rsegs _ _ ie 80%nat ltac:(lia) IE) as [IE1 IE2]; clear IE.
replace (bv_unsigned sp + -816 + 4 * Z.of_nat 80) with (bv_unsigned sp + -496) in IE2 by lia.

do 4 zstep.
remember (Z_to_bv 64 (bv_unsigned sp + -816)) as spw eqn:Hspw.
assert (USPW : bv_unsigned spw = bv_unsigned sp + -816) by (subst spw; apply unsigned_lit; lia).
call (interp_pitch_spec EB eoff pitch (bv_unsigned sp + -816) lo eb (firstn 80 ie));
[ exact XEB | exact LEB | lia | lia | lia | lia | exact IE1 | rewrite firstn_length_le by lia; reflexivity
| rewrite USPW; exact ST | rewrite USPW; unfold IP_DEPTH; lia | exact GLO | rewrite USPW; lia | unfold NB_GLOBALS_TOP; lia
| rewrite USPW; unfold apart; lia | rewrite USPW; unfold apart; lia | unfold apart; lia
| lia | exact EB0 | exact EBA | lia
| reflexivity | exact Hspw | reflexivity | exact MI | exact FRM | ].
rename MI0 into MI || idtac. clear FRM.
match goal with H : frm0 _, H2 : rw_cells _ _ (bv_unsigned sp + -816) (f32 ?c), H3 : length ?c = 80%nat, H4 : stk _ _ _ _ |- _ =>
rename H into FRM; rename H2 into IP1; rename H3 into LIP1; rename H4 into ST end.
subst spw. rewrite USPW in ST. clear USPW. unk.

zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut rsegs (JP 0x247c4 mc (fun p2 => (p2 = 2 * pitch /\ 40 < pitch) \/ (p2 = - pitch /\ pitch <= 40))
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
end;
[ | clear FRM; intros ? PO; first [ sf_destruct 6%nat PO as p2 ? ? -> FRM HP2 | sf_fb; destruct PO as (p2 & ? & ? & -> & FRM & HP2) ] ].
{ if_cases B40; zify_cond B40; rewrite zb_signed_small in B40 by lia.
- zstep. ub_dec. zstep. zstep. zstep. ub_dec. zstep. zstep. zstep. ub_dec. zstep. zstep. zstep.
match goal with |- context [bv_swrap 32 ((0 - pitch) mod ?M + 0)] =>
replace (bv_swrap 32 ((0 - pitch) mod M + 0)) with (- pitch) by (rewrite swrap32_modl_k, Z.add_0_r, swrap32_small_k by lia; lia) end.
apply evt_done; sf_eexists 3%nat; split; [reflexivity|]; split; [assumption| right; lia].
- zstep. ub_dec. zstep. zstep. zstep. ub_dec. zstep. zstep. zstep. ub_dec. zstep. zstep. zstep. zstep.
replace (bv_swrap 32 (Z.shiftl pitch 1)) with (2 * pitch) by (rewrite Z.shiftl_mul_pow2, swrap32_small by lia; lia).
apply evt_done; sf_eexists 3%nat; split; [reflexivity|]; split; [assumption| left; lia]. }

zstep.
remember (Z_to_bv 64 (bv_unsigned sp + -816)) as spw eqn:Hspw.
assert (USPW : bv_unsigned spw = bv_unsigned sp + -816) by (subst spw; apply unsigned_lit; lia).
call (interp_pitch_spec EB eoff p2 (bv_unsigned sp + -496) lo eb (skipn 80 ie));
[ exact XEB | exact LEB | lia | lia | lia | lia | exact IE2 | rewrite skipn_length; lia
| rewrite USPW; exact ST | rewrite USPW; unfold IP_DEPTH; lia | exact GLO | rewrite USPW; lia | unfold NB_GLOBALS_TOP; lia
| rewrite USPW; unfold apart; lia | rewrite USPW; unfold apart; lia | unfold apart; lia
| lia | exact EB0 | exact EBA | lia
| reflexivity | first [ reflexivity | f_equal; lia ] | reflexivity | exact MI | exact FRM | ].
rename MI0 into MI || idtac. clear FRM.
match goal with H : frm0 _, H2 : rw_cells _ _ (bv_unsigned sp + -496) (f32 ?c), H3 : length ?c = 80%nat, H4 : stk _ _ _ _ |- _ =>
rename H into FRM; rename H2 into IP2; rename H3 into LIP2; rename H4 into ST end.
subst spw. rewrite USPW in ST. clear USPW. unk.

eapply (mc_post EB eoff ne pitch lo eb m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
[ exact LEB | exact EOFF | exact HP | exact LOW | exact GLO | exact SP63 | exact AEB | exact ANE | exact ANEB
| exact EBA | exact NEA | exact NEP | exact SPA
| exact LIP1 | exact LIP2 | exact LNS | exact FRM | exact MI | exact MU | exact WM | exact XEB | exact XNE
| exact IP1 | exact IP2 | exact FR | exact ST ].
Qed.
End M.
