(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Ja0RegionPoisoned Ja0AsanMemset Ja0AsanMemcpy Ja0StrlenIcpt Ja0TlsGetAddr Ja0FakeStack1 Ja0FakeStackGC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0Fsm4Core () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0Fsm4Core.FPX_1.CORE4."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nat"; "1nil"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0Mx"; "5msteps"; "6core4_mem"; "6p4_inv"; "6p4_keeps"; "7keeps_but"; "8getr"]; ["8mkst"; "9loaded_segments"; ":add"; ":divide"; ":land"; ":le"; ":lt"; ":modulo"; ":of_nat"; ":pow"; ":sub"; "0a"; "0c"; "0ff"; "0fs"; "0fx"]; ["0i"; "0j"; "0m"; "0q"; "0r18"; "0r8"; "0r9"; "0ra8"; "0regs"; "0regs'"; "0rom"; "0s"; ";BV"; ";Z_to_bv"; ";bv"; ";bv_unsigned"]; ["0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac wv2 := gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
try change (2 ^ 10)%Z with 1024%Z; first [reflexivity | f_equal; lia].
#[local] Ltac stepsdq F D aa vv oktac :=
chain_step; [reflexivity
| eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wv2 | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
| step_simpl].
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
Lemma zbv_add : ltac2:(TCodec.tc2 tcn__Ja0Fsm4Core "C'7'5'Q>yR0%211&Q=&B&Q?r2%4261%3271r1%6221%82:1%8263%:2<1%?3<31pQJA1pS2B1").
Proof. intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma zbv_mod : ltac2:(TCodec.tc2 tcn__Ja0Fsm4Core "L'7&Fzr1%3221&Cr2&I+2+R0%3221%6251'5&G&Q?yR0&Q=r4%2231%5241r3%8221%9252%;3G21p0=1p0E1pR6J1pS2K1").
Proof. intros x m Hm D. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. symmetry. apply Znumtheory.Zmod_div_mod; [exact Hm | lia | exact D]. Qed.
Lemma div_8192 : ltac2:(TCodec.tc2 tcn__Ja0Fsm4Core "7&C+QP0&I+2+R0%3221%6251"). Proof. exists (2 ^ 54)%Z. reflexivity. Qed.
Lemma land_mask4 : ltac2:(TCodec.tc2 tcn__Ja0Fsm4Core ";'7'5&Dr1+oO%3221&G+QP0%2251%83941pQH:1").
Proof. intros a. change 1023%Z with (Z.ones 10). rewrite Z.land_ones by lia. reflexivity. Qed.
Section CORE4.
Variable Mx : word -> option byte.
Variable rom : word -> option byte.
Variables s fs h j pos ff : Z.
Variables ra8 r8 r9 r18 : word.
Hypothesis Hret : ret_ok ra8.
Hypothesis Hs : (0x1000000 <= s - 32)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hfs : (0x691000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 32 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
Hypothesis Hh : (0 <= h < 2 ^ 64)%Z.
Hypothesis Hj : (0 <= j < 1024)%Z.
Hypothesis Hpos_def : pos = ((h + j) mod 1024)%Z.
Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 4194304 + 1024 * pos)%Z.
Hypothesis Hhint : rdn ASEGS Mx (Z_to_bv 64 (fs + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
Hypothesis Hprobe : forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 30720 + (h + i) mod 1024)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z.
Hypothesis Hflag : rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 30720 + pos)) 1%nat = Some [Z_to_bv 8 0].
Hypothesis Hwfs : store_ok ASEGS Mx (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
Hypothesis HG : rt_layout_globs Mx.
Hypothesis Happ : in_app ff.
Hypothesis Hshadow_ok : store_ok ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) 128%nat = true.
Hypothesis Hshadow_dj : (SB + ff / 8 + 128 <= s - 32 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 128 <= 0x132638 \/ 0x13b9f8 <= SB + ff / 8)%Z.
Hypothesis Hslots : rdn ASEGS Mx (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra8) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 r8)
/\ rdn ASEGS Mx (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 r9) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 r18).
Definition core4_mem : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mx
(Z_to_bv 64 (fs + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1))))
(Z_to_bv 64 (fs + 4096 + 30720 + pos)) [Z_to_bv 8 1])
(Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
(Z_to_bv 64 (ff + 1016)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 30720 + pos))))
(Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 64)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 72)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 80)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 96)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 104)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 112)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 120)) (word_to_le_bytes 8 (Z_to_bv 64 0)).
Definition p4_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 12 = Z_to_bv 64 (h + i) /\ getr rg 10 = Z_to_bv 64 (1024 - i) /\ getr rg 13 = Z_to_bv 64 (fs + 4096 + 30720) /\ getr rg 14 = Z_to_bv 64 1023.
Definition p4_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 15%bv -> r <> 17%bv -> r <> 5%bv -> getr regs' r = getr regs r.
#[local] Ltac kp := intros r N10 N12 N15 N17 N5; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.
Lemma probe4_loop : ltac2:(TCodec.tc2 tcn__Ja0Fsm4Core "QF'1&8y5'Q>yR0%211%5241'7&<r2r1%3221&Ez%2215'5&Br3&Hr5%211%5241vQ1%83@21'6'4':&A&@vOr6(Q<+[fX<(3%33N21/01Nv9vQ:%:598321%;5:M432%>3=21%Q12OC&=%12=Q1%C231%D251qRDQ81%G2Q91p0I1p0Q31p0Q71pR2Q<1pRBQ>1pR8QE1").
Proof.
induction q as [|q IH]; intros regs i (H12 & H10 & H13 & H14) Hi Hq.
- exists regs. replace j with i by lia. split; [apply mst_refl|]. split; [repeat split; assumption | intros r _ _ _ _ _; reflexivity].
- destruct (Hprobe i ltac:(lia)) as (b & Fi & Bi). destruct Hfs as (Fs1 & Fs2 & Fs3).
pose proof (Z.mod_pos_bound (h + i) 1024 ltac:(lia)) as Pb.
assert (STEP : exists r1, msteps ASEGS (mkst regs (0x5d90c : word) Mx rom) (mkst r1 (0x5d90c : word) Mx rom) /\ p4_inv r1 (i + 1) /\ p4_keeps regs r1).
{ eexists. split.
- stepov (ltac:(oF' 0x5d90c%Z)) (ltac:(oD' 0x5d90c%Z)) (Z_to_bv 64 ((h + i) mod 1024)) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 1023) by lia; rewrite land_mask4, (zbv_mod (h + i) 1024 ltac:(lia) div_8192); reflexivity).
stepiv (ltac:(oF' 0x5d910%Z)) (ltac:(oD' 0x5d910%Z)) (Z_to_bv 64 (fs + 4096 + 30720 + (h + i) mod 1024)) ltac:(wv2).
chain_step; [reflexivity | eapply step_lbu; [exact (ltac:(oF' 0x5d914%Z)) | reflexivity | exact (ltac:(oD' 0x5d914%Z))
| match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 30720 + (h + i) mod 1024)) by (symmetry; wv2) end; exact Fi] | step_simpl; vnorm].
stepb_ft (ltac:(oF' 0x5d918%Z)) (ltac:(oD' 0x5d918%Z)) ltac:(rewrite (u_Z2bv8 b) by lia; cond).
stepiv (ltac:(oF' 0x5d91c%Z)) (ltac:(oD' 0x5d91c%Z)) (Z_to_bv 64 (1024 - (i + 1))) ltac:(gres; rwH; unfold v_addiw; imm_norm; unorm; rewrite swrap32_small by lia; f_equal; lia).
stepiv (ltac:(oF' 0x5d920%Z)) (ltac:(oD' 0x5d920%Z)) (Z_to_bv 64 (h + (i + 1))) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).
stepb_tk (ltac:(oF' 0x5d924%Z)) (ltac:(oD' 0x5d924%Z)) ltac:(cond).
apply mst_refl.
- split; [unfold p4_inv; post | kp]. }
destruct STEP as (r1 & RUN1 & INV1 & KP1).
destruct (IH r1 (i + 1)%Z INV1 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & INV2 & KP2).
exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact INV2|].
intros r N10 N12 N15 N17 N5. rewrite (KP2 r N10 N12 N15 N17 N5). apply KP1; assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_fsm4_core_run := (ltac2:(TCodec.tc2 tcn__Ja0Fsm4Core "S7&8y5'Q>yR0%211%5241'5&?r1(Q<+9(3%33;21%6251&Q=vN%22=1%;3=41r2+B%;3C19%>231+D%92D1%B3D31r3+8%B3J1@%E231vQ;%@2K1%I3K31r4+2%I3Q11G%L231&J+Q0%2291%I2Q41%Q23Q451'6'4':&A&@vOr6+[fUL%Q83Q>1Q6/01Q>v9vQ:%8576321vQ7&;%;5:Q@214%>3=41+:%QB3QJ1Q@%QE2QD1vM%Q@2QK1%QI3QK31%QI2QHN%QK3QM1Q3+1%QJ3R21QH%QM2QL1%QO3R11?%QO2QNQ;vQ5%R23R421vQ6%R43R6QM1%R42R3QGvQ4%R73R921&>(0%R>1R?(2%112%433QO1%534R81%635QJ1%736QD1%837D1%:31Q9R@%Q?2<1%Q@2@1%QA2C1%QB2G1%QC2L1%QD2O1%QE2Q61qRDRK1%QH2RL1p0QJ1p0R41p0R<1p0RD1pRBS11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_fsm4_core_run) 0%nat 0%nat).
Theorem fsm4_core_run : ltac:(sec_stmt2 constr:(SEC_T_fsm4_core_run) 1%nat 0%nat).
Proof.
intros H9 H18 H8 H2.
destruct Hfs as (Fs1 & Fs2 & Fs3).
pose proof (Z.mod_pos_bound (h + j) 1024 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
assert (Hffb : (fs + 4096 + 32768 + 2 ^ 20 <= ff /\ ff + 1024 <= fs + 4096 + 32768 + 5242880)%Z) by (rewrite Hff_def; lia).
assert (Hrb : ret_ok (0x5d9c4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (SBb : (0 <= SB + ff / 8 /\ SB + ff / 8 + 128 < 2 ^ 64)%Z).
{ unfold in_app, LOWEND, HIGHBEG, HIGHEND, SB in *. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
assert (ff / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with 17592186044416%Z in H. lia. }
assert (GL : forall M, (forall x : word, (bv_unsigned x < 0x691000)%Z -> M x = Mx x) -> rt_layout_globs M).
{ intros M HM. destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
rewrite !(rdn_ext ASEGS _ M Mx) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia | intros x Hx; apply HM; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; lia]).
repeat split; assumption. }
set (N1 := wbytes Mx (Z_to_bv 64 (fs + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))).
set (N2 := wbytes N1 (Z_to_bv 64 (fs + 4096 + 30720 + pos)) [Z_to_bv 8 1]).
set (N3 := wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))).
set (N4 := wbytes N3 (Z_to_bv 64 (ff + 1016)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 30720 + pos)))).
set (N5 := wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N6 := wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N7 := wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N8 := wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N9 := wbytes N8 (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N10 := wbytes N9 (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N11 := wbytes N10 (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N12 := wbytes N11 (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N13 := wbytes N12 (Z_to_bv 64 (SB + ff / 8 + 64)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N14 := wbytes N13 (Z_to_bv 64 (SB + ff / 8 + 72)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N15 := wbytes N14 (Z_to_bv 64 (SB + ff / 8 + 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N16 := wbytes N15 (Z_to_bv 64 (SB + ff / 8 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N17 := wbytes N16 (Z_to_bv 64 (SB + ff / 8 + 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N18 := wbytes N17 (Z_to_bv 64 (SB + ff / 8 + 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N19 := wbytes N18 (Z_to_bv 64 (SB + ff / 8 + 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
set (N20 := wbytes N19 (Z_to_bv 64 (SB + ff / 8 + 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
assert (GN4 : mem_grows Mx N4) by (unfold N4, N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
assert (WFS : forall M (a : Z) (k : nat), mem_grows Mx M -> (fs <= a)%Z -> (a + Z.of_nat k <= fs + 4096 + 32768 + 11 * 2 ^ 20)%Z ->
store_ok ASEGS M (Z_to_bv 64 a) k = true).
{ intros M a k HM Ha Hk. apply (store_ok_mono _ _ Mx M _ HM).
apply (store_ok_sub ASEGS Mx (Z_to_bv 64 fs) _ (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)));
[unorm; rewrite Z2Nat.id by lia; lia | exact Hwfs | unorm; lia | unorm; rewrite Z2Nat.id by lia; lia]. }
assert (GLN4 : rt_layout_globs N4).
{ apply GL. intros x Hx. pose proof (u64_range x). unfold N4, N3, N2, N1.
rewrite !wbytes_below; first [reflexivity | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]. }
assert (SA : exists ra_, msteps ASEGS (mkst regs (0x5d8bc : word) Mx rom) (mkst ra_ (0x5d90c : word) Mx rom)
/\ p4_inv ra_ 0 /\ (getr ra_ 11 = Z_to_bv 64 (fs + 4096) /\ getr ra_ 9 = Z_to_bv 64 fs /\ getr ra_ 18 = Z_to_bv 64 20 /\ getr ra_ 8 = Z_to_bv 64 s
/\ getr ra_ 2 = Z_to_bv 64 (s - 32) /\ keeps_but [1; 2; 8; 9; 18]%bv regs ra_)).
{ eexists. split.
-
stepiv (ltac:(oF' 0x5d8bc%Z)) (ltac:(oD' 0x5d8bc%Z)) (Z_to_bv 64 10) ltac:(wv2).
stepn (ltac:(oF' 0x5d8c0%Z)) (ltac:(oD' 0x5d8c0%Z)).
stepn (ltac:(oF' 0x5d8c4%Z)) (ltac:(oD' 0x5d8c4%Z)).
stepn (ltac:(oF' 0x5d8c8%Z)) (ltac:(oD' 0x5d8c8%Z)).
stepb (ltac:(oF' 0x5d8cc%Z)) (ltac:(oD' 0x5d8cc%Z)).
stepn (ltac:(oF' 0x5d8d0%Z)) (ltac:(oD' 0x5d8d0%Z)).
stepiv (ltac:(oF' 0x5d8d4%Z)) (ltac:(oD' 0x5d8d4%Z)) (Z_to_bv 64 5) ltac:(wv2).
stepn (ltac:(oF' 0x5d8d8%Z)) (ltac:(oD' 0x5d8d8%Z)).
stepn (ltac:(oF' 0x5d8dc%Z)) (ltac:(oD' 0x5d8dc%Z)).
stepn (ltac:(oF' 0x5d8e0%Z)) (ltac:(oD' 0x5d8e0%Z)).
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact (ltac:(oF' 0x5d8e4%Z)) | reflexivity | exact (ltac:(oD' 0x5d8e4%Z))
| match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 32)) by (symmetry; wv2) end; exact Hhint | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].
stepn (ltac:(oF' 0x5d8e8%Z)) (ltac:(oD' 0x5d8e8%Z)).
stepn (ltac:(oF' 0x5d8ec%Z)) (ltac:(oD' 0x5d8ec%Z)).
stepiv (ltac:(oF' 0x5d8f0%Z)) (ltac:(oD' 0x5d8f0%Z)) (Z_to_bv 64 (fs + 4096)) ltac:(wv2).
stepiv (ltac:(oF' 0x5d8f4%Z)) (ltac:(oD' 0x5d8f4%Z)) (Z_to_bv 64 (fs + 4096 + 30720)) ltac:(wv2).
stepn (ltac:(oF' 0x5d8f8%Z)) (ltac:(oD' 0x5d8f8%Z)).
stepn (ltac:(oF' 0x5d8fc%Z)) (ltac:(oD' 0x5d8fc%Z)).
stepn (ltac:(oF' 0x5d900%Z)) (ltac:(oD' 0x5d900%Z)).
stepiv (ltac:(oF' 0x5d904%Z)) (ltac:(oD' 0x5d904%Z)) (Z_to_bv 64 (h + 1023)) ltac:(wv2).
stepiv (ltac:(oF' 0x5d908%Z)) (ltac:(oD' 0x5d908%Z)) (Z_to_bv 64 (h + 1024)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).
apply mst_refl.
- split; [unfold p4_inv; repeat split; gres; rwH; try reflexivity; f_equal; lia|]. repeat split; gres; rwH; try reflexivity. solve_keeps_but. }
destruct SA as (ra_ & RUNA & INVA & A11 & A9 & A18 & A8 & A2 & KA).
destruct (probe4_loop (Z.to_nat j) ra_ 0%Z INVA ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (rb & RUNB & (B12 & B10 & B13 & B14) & KB).
assert (B11 : getr rb 11 = Z_to_bv 64 (fs + 4096)) by (rewrite (KB 11%bv) by (intros X; discriminate X); exact A11).
assert (B9 : getr rb 9 = Z_to_bv 64 fs) by (rewrite (KB 9%bv) by (intros X; discriminate X); exact A9).
assert (B18 : getr rb 18 = Z_to_bv 64 20) by (rewrite (KB 18%bv) by (intros X; discriminate X); exact A18).
assert (B8 : getr rb 8 = Z_to_bv 64 s) by (rewrite (KB 8%bv) by (intros X; discriminate X); exact A8).
assert (B2 : getr rb 2 = Z_to_bv 64 (s - 32)) by (rewrite (KB 2%bv) by (intros X; discriminate X); exact A2).
assert (SC : exists r3, msteps ASEGS (mkst rb (0x5d90c : word) Mx rom) (mkst r3 (0x5da44 : word) N4 rom)
/\ (getr r3 10 = Z_to_bv 64 ff /\ getr r3 9 = Z_to_bv 64 ff /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32)
/\ getr r3 1 = (0x5d9c4 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv rb r3)).
{ eexists. split.
- stepov (ltac:(oF' 0x5d90c%Z)) (ltac:(oD' 0x5d90c%Z)) (Z_to_bv 64 pos) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 1023) by lia; rewrite land_mask4, (zbv_mod (h + j) 1024 ltac:(lia) div_8192), <- Hpos_def; reflexivity).
stepiv (ltac:(oF' 0x5d910%Z)) (ltac:(oD' 0x5d910%Z)) (Z_to_bv 64 (fs + 4096 + 30720 + pos)) ltac:(wv2).
chain_step; [reflexivity | eapply step_lbu; [exact (ltac:(oF' 0x5d914%Z)) | reflexivity | exact (ltac:(oD' 0x5d914%Z))
| match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 30720 + pos)) by (symmetry; wv2) end; exact Hflag] | step_simpl; vnorm].
stepb (ltac:(oF' 0x5d918%Z)) (ltac:(oD' 0x5d918%Z)).
stepiv (ltac:(oF' 0x5d984%Z)) (ltac:(oD' 0x5d984%Z)) (Z_to_bv 64 (h + j + 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).
stepn (ltac:(oF' 0x5d988%Z)) (ltac:(oD' 0x5d988%Z)).
stepiv (ltac:(oF' 0x5d98c%Z)) (ltac:(oD' 0x5d98c%Z)) (Z_to_bv 64 15) ltac:(wv2).
stepsdq (ltac:(oF' 0x5d990%Z)) (ltac:(oD' 0x5d990%Z)) (Z_to_bv 64 (fs + 32)) (Z_to_bv 64 (h + j + 1)) ltac:(apply WFS; [apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).
change (wbytes Mx (Z_to_bv 64 (fs + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))) with N1.
chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 4096 + 30720 + pos)) (b := Z_to_bv 8 1);
[exact (ltac:(oF' 0x5d994%Z)) | reflexivity | exact (ltac:(oD' 0x5d994%Z)) | wv2 | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
| apply WFS; [unfold N1; eapply mem_grows_trans; [apply mem_grows_refl | apply wbytes_grows] | lia | cbn [Z.of_nat Pos.to_nat]; lia] ] | step_simpl; vnorm].
change (wbytes N1 (Z_to_bv 64 (fs + 4096 + 30720 + pos)) [Z_to_bv 8 1]) with N2.
stepn (ltac:(oF' 0x5d998%Z)) (ltac:(oD' 0x5d998%Z)).
stepn (ltac:(oF' 0x5d99c%Z)) (ltac:(oD' 0x5d99c%Z)).
stepiv (ltac:(oF' 0x5d9a0%Z)) (ltac:(oD' 0x5d9a0%Z)) (Z_to_bv 64 (1024 * pos)) ltac:(wv2).
stepsv (ltac:(oF' 0x5d9a4%Z)) (ltac:(oD' 0x5d9a4%Z)) (Z_to_bv 64 (4 * 2 ^ 20)) ltac:(gres; rwH; rewrite v_sll_lit by lia; reflexivity).
stepiv (ltac:(oF' 0x5d9a8%Z)) (ltac:(oD' 0x5d9a8%Z)) (Z_to_bv 64 (fs + 4096 + 32768)) ltac:(wv2).
stepiv (ltac:(oF' 0x5d9ac%Z)) (ltac:(oD' 0x5d9ac%Z)) (Z_to_bv 64 (4194304 + 1024 * pos)) ltac:(wv2).
stepiv (ltac:(oF' 0x5d9b0%Z)) (ltac:(oD' 0x5d9b0%Z)) (Z_to_bv 64 ff) ltac:(wv2).
stepsd (ltac:(oF' 0x5d9b4%Z)) (ltac:(oD' 0x5d9b4%Z)) (Z_to_bv 64 (ff + 24)) (Z_to_bv 64 s)
ltac:(apply WFS; [unfold N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).
change (wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with N3.
stepsd (ltac:(oF' 0x5d9b8%Z)) (ltac:(oD' 0x5d9b8%Z)) (Z_to_bv 64 (ff + 1016)) (Z_to_bv 64 (fs + 4096 + 30720 + pos))
ltac:(apply WFS; [unfold N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).
change (wbytes N3 (Z_to_bv 64 (ff + 1016)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 30720 + pos)))) with N4.
stepiv (ltac:(oF' 0x5d9bc%Z)) (ltac:(oD' 0x5d9bc%Z)) (Z_to_bv 64 ff) ltac:(wv2).
stepn (ltac:(oF' 0x5d9c0%Z)) (ltac:(oD' 0x5d9c0%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct SC as (r3 & RUN3 & U10 & U9 & U8 & U2 & U1 & K3).
destruct (memtoshadow47_run r3 N4 rom (0x5d9c4 : word) ff GLN4 Happ U10 U1 Hrb) as (r4 & RUN4 & V10 & K4).
assert (V9 : getr r4 9 = Z_to_bv 64 ff) by (rewrite (K4 9%bv) by (cbv; tauto); exact U9).
assert (V8 : getr r4 8 = Z_to_bv 64 s) by (rewrite (K4 8%bv) by (cbv; tauto); exact U8).
assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (cbv; tauto); exact U2).
destruct Hshadow_dj as [SD1 SD2]. destruct Hslots as (SL8 & SL16 & SL24 & SL32).
assert (ESB : SB = 2147450880%Z) by reflexivity.
assert (SL : forall k v, rdn ASEGS Mx (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v) -> (8 <= k <= 32)%Z ->
rdn ASEGS N20 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
{ intros k v R Hk. rewrite (rdn_ext ASEGS 8 N20 Mx); [exact R | unorm; cbn; lia |].
intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
unfold N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5, N4, N3, N2, N1.
assert (OUT : forall (m : word -> option byte) (a : Z) (l : list byte), (0 <= a)%Z -> (a + Z.of_nat (length l) < 2 ^ 64)%Z ->
(a + Z.of_nat (length l) <= s - 32 \/ s <= a)%Z -> wbytes m (Z_to_bv 64 a) l x = m x).
{ intros m a l Ha Hl Hd. destruct Hd as [Hd|Hd].
- apply wbytes_above. unorm. lia.
- apply wbytes_below; unorm; lia. }
rewrite !OUT by (first [rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; lia | lia]). reflexivity. }
eexists. split.
- eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
stepiv (ltac:(oF' 0x5d9c4%Z)) (ltac:(oD' 0x5d9c4%Z)) (Z_to_bv 64 (SB + ff / 8)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepiv (ltac:(oF' 0x5d9c8%Z)) (ltac:(oD' 0x5d9c8%Z)) (Z_to_bv 64 ff) ltac:(wv2).
stepn (ltac:(oF' 0x5d9cc%Z)) (ltac:(oD' 0x5d9cc%Z)).
stepsd (ltac:(oF' 0x5d9d0%Z)) (ltac:(oD' 0x5d9d0%Z)) (Z_to_bv 64 (SB + ff / 8)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N5.
stepsd (ltac:(oF' 0x5d9d4%Z)) (ltac:(oD' 0x5d9d4%Z)) (Z_to_bv 64 (SB + ff / 8 + 8)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N5; do 1 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N6.
stepsd (ltac:(oF' 0x5d9d8%Z)) (ltac:(oD' 0x5d9d8%Z)) (Z_to_bv 64 (SB + ff / 8 + 16)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N6, N5; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N7.
stepsd (ltac:(oF' 0x5d9dc%Z)) (ltac:(oD' 0x5d9dc%Z)) (Z_to_bv 64 (SB + ff / 8 + 24)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N7, N6, N5; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N8.
stepsd (ltac:(oF' 0x5d9e0%Z)) (ltac:(oD' 0x5d9e0%Z)) (Z_to_bv 64 (SB + ff / 8 + 32)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N8, N7, N6, N5; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N8 (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N9.
stepsd (ltac:(oF' 0x5d9e4%Z)) (ltac:(oD' 0x5d9e4%Z)) (Z_to_bv 64 (SB + ff / 8 + 40)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N9, N8, N7, N6, N5; do 5 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N9 (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N10.
stepsd (ltac:(oF' 0x5d9e8%Z)) (ltac:(oD' 0x5d9e8%Z)) (Z_to_bv 64 (SB + ff / 8 + 48)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N10, N9, N8, N7, N6, N5; do 6 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N10 (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N11.
stepsd (ltac:(oF' 0x5d9ec%Z)) (ltac:(oD' 0x5d9ec%Z)) (Z_to_bv 64 (SB + ff / 8 + 56)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N11, N10, N9, N8, N7, N6, N5; do 7 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N11 (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N12.
stepsd (ltac:(oF' 0x5d9f0%Z)) (ltac:(oD' 0x5d9f0%Z)) (Z_to_bv 64 (SB + ff / 8 + 64)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N12, N11, N10, N9, N8, N7, N6, N5; do 8 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N12 (Z_to_bv 64 (SB + ff / 8 + 64)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N13.
stepsd (ltac:(oF' 0x5d9f4%Z)) (ltac:(oD' 0x5d9f4%Z)) (Z_to_bv 64 (SB + ff / 8 + 72)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N13, N12, N11, N10, N9, N8, N7, N6, N5; do 9 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N13 (Z_to_bv 64 (SB + ff / 8 + 72)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N14.
stepsd (ltac:(oF' 0x5d9f8%Z)) (ltac:(oD' 0x5d9f8%Z)) (Z_to_bv 64 (SB + ff / 8 + 80)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 10 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N14 (Z_to_bv 64 (SB + ff / 8 + 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N15.
stepsd (ltac:(oF' 0x5d9fc%Z)) (ltac:(oD' 0x5d9fc%Z)) (Z_to_bv 64 (SB + ff / 8 + 88)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 11 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N15 (Z_to_bv 64 (SB + ff / 8 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N16.
stepsd (ltac:(oF' 0x5da00%Z)) (ltac:(oD' 0x5da00%Z)) (Z_to_bv 64 (SB + ff / 8 + 96)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 12 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N16 (Z_to_bv 64 (SB + ff / 8 + 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N17.
stepsd (ltac:(oF' 0x5da04%Z)) (ltac:(oD' 0x5da04%Z)) (Z_to_bv 64 (SB + ff / 8 + 104)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 13 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N17 (Z_to_bv 64 (SB + ff / 8 + 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N18.
stepsd (ltac:(oF' 0x5da08%Z)) (ltac:(oD' 0x5da08%Z)) (Z_to_bv 64 (SB + ff / 8 + 112)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 14 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N18 (Z_to_bv 64 (SB + ff / 8 + 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N19.
stepsd (ltac:(oF' 0x5da0c%Z)) (ltac:(oD' 0x5da0c%Z)) (Z_to_bv 64 (SB + ff / 8 + 120)) (Z_to_bv 64 0)
ltac:(apply (store_ok_mono _ _ Mx); [unfold N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 15 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 128%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
change (wbytes N19 (Z_to_bv 64 (SB + ff / 8 + 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N20.
stepld (ltac:(oF' 0x5da10%Z)) (ltac:(oD' 0x5da10%Z)) ra8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; [exact SL8 | lia]).
stepld (ltac:(oF' 0x5da14%Z)) (ltac:(oD' 0x5da14%Z)) r8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; [exact SL16 | lia]).
stepld (ltac:(oF' 0x5da18%Z)) (ltac:(oD' 0x5da18%Z)) r9 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; [exact SL24 | lia]).
stepld (ltac:(oF' 0x5da1c%Z)) (ltac:(oD' 0x5da1c%Z)) r18 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; [exact SL32 | lia]).
stepiv (ltac:(oF' 0x5da20%Z)) (ltac:(oD' 0x5da20%Z)) (Z_to_bv 64 s) ltac:(wv2).
stepret (ltac:(oF' 0x5da24%Z)) (ltac:(oD' 0x5da24%Z)) ra8 ltac:(rwH; reflexivity).
unfold N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5, N4, N3, N2, N1. fold core4_mem.
apply mst_refl.
- split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
assert (KBB : keeps_but [1; 2; 8; 9; 18]%bv regs r4).
{ eapply keeps_but_trans; [exact KA|]. eapply keeps_but_trans; [|eapply keeps_but_trans; [exact K3 | apply keeps_but_cs; exact K4]].
intros r Hcs Hn. apply KB; intros ->; cbv in Hcs; clear - Hcs; intuition discriminate. }
intros r Hcs Hn. repeat (rewrite getr_other; [| intros ->; first [cbv in Hn; clear - Hn; intuition congruence | cbv in Hcs; clear - Hcs; intuition discriminate]]).
apply KBB; assumption.
Qed.
End SE.
End CORE4.
End FPX_1.
