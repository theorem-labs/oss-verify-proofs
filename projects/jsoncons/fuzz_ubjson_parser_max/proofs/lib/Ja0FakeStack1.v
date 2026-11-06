(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Ja0RegionPoisoned Ja0AsanMemset Ja0AsanMemcpy Ja0StrlenIcpt Ja0TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0FakeStack1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "5msteps"; "6ret_ok"; "7SB"; "7in_app"; "7rt_layout_globs"; "8getr"; "8mkst"; "9keeps_cs"]; [":loaded_segments"; ";add"; ";div"; ";land"; ";modulo"; "0a"; "0fx"; "0p"; "0regs"; "0regs'"; "0ret"; "0rom"; "0s"; "0sp"; "<BV"; "<Z_to_bv"]; ["<bv"]]).
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
Section SE.
Local Abbreviation SEC_T_memtoshadow47_run := (ltac2:(TCodec.tc2 tcn__Ja0FakeStack1 "R@&6y5'Q0yR0%211%5241'0y8%611%311p061'5&<r4%211&;r2%211'3&=r7(N+:(1%33G21%6251&Or3%22I1%;3I41r8+1%;3O19%>231r5%A3O21&9r6%211'4'2'8&@&>vFr;+[fb4%J3Q<1H/01Q<r:r9%8576321r1%:591G43%=3<31%Q423O&A&B+8%22Q71&:%5221%Q42QK1%Q=3QK81&?%12D=%J231%K2=1qQDQO1%N2R01p0Q01p0Q41p0Q;1p0QH1p0QL1pQ@R01pQFR81pQHR31p@R41pQBR:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_memtoshadow47_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_memtoshadow47_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_memtoshadow47_run) 2%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_memtoshadow47_run) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_memtoshadow47_run) 4%nat 0%nat).
Lemma memtoshadow47_run : ltac:(sec_stmt2 constr:(SEC_T_memtoshadow47_run) 5%nat 0%nat).
Proof.
intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
destruct Hp as [Hlow|Hhigh].
- eexists. split.
+ stepn (ltac:(oF' 0x5da44%Z)) (ltac:(oD' 0x5da44%Z)).
mld (ltac:(oF' 0x5da48%Z)) (ltac:(oD' 0x5da48%Z)) (0x132638 : word) G1.
mld (ltac:(oF' 0x5da4c%Z)) (ltac:(oD' 0x5da4c%Z)) (0x13acf8 : word) G2.
stepn (ltac:(oF' 0x5da50%Z)) (ltac:(oD' 0x5da50%Z)).
stepn (ltac:(oF' 0x5da54%Z)) (ltac:(oD' 0x5da54%Z)).
stepn (ltac:(oF' 0x5da58%Z)) (ltac:(oD' 0x5da58%Z)).
stepn (ltac:(oF' 0x5da5c%Z)) (ltac:(oD' 0x5da5c%Z)).
stepb_tk (ltac:(oF' 0x5da60%Z)) (ltac:(oD' 0x5da60%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5daa4%Z)) (ltac:(oD' 0x5daa4%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x5daa8%Z)) (ltac:(oD' 0x5daa8%Z)) (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
stepret (ltac:(oF' 0x5daac%Z)) (ltac:(oD' 0x5daac%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ split; [gres; reflexivity | solve_keeps_cs].
- eexists. split.
+ stepn (ltac:(oF' 0x5da44%Z)) (ltac:(oD' 0x5da44%Z)).
mld (ltac:(oF' 0x5da48%Z)) (ltac:(oD' 0x5da48%Z)) (0x132638 : word) G1.
mld (ltac:(oF' 0x5da4c%Z)) (ltac:(oD' 0x5da4c%Z)) (0x13acf8 : word) G2.
stepn (ltac:(oF' 0x5da50%Z)) (ltac:(oD' 0x5da50%Z)).
stepn (ltac:(oF' 0x5da54%Z)) (ltac:(oD' 0x5da54%Z)).
stepn (ltac:(oF' 0x5da58%Z)) (ltac:(oD' 0x5da58%Z)).
stepn (ltac:(oF' 0x5da5c%Z)) (ltac:(oD' 0x5da5c%Z)).
stepb_ft (ltac:(oF' 0x5da60%Z)) (ltac:(oD' 0x5da60%Z)) ltac:(cond).
stepn (ltac:(oF' 0x5da64%Z)) (ltac:(oD' 0x5da64%Z)).
mld (ltac:(oF' 0x5da68%Z)) (ltac:(oD' 0x5da68%Z)) (0x132640 : word) G3.
stepn (ltac:(oF' 0x5da6c%Z)) (ltac:(oD' 0x5da6c%Z)).
mld (ltac:(oF' 0x5da70%Z)) (ltac:(oD' 0x5da70%Z)) (0x132648 : word) G5.
mld (ltac:(oF' 0x5da74%Z)) (ltac:(oD' 0x5da74%Z)) (0x13b9e8 : word) G4.
mld (ltac:(oF' 0x5da78%Z)) (ltac:(oD' 0x5da78%Z)) (0x13b9f0 : word) G6.
stepn (ltac:(oF' 0x5da7c%Z)) (ltac:(oD' 0x5da7c%Z)).
stepb_tk (ltac:(oF' 0x5da80%Z)) (ltac:(oD' 0x5da80%Z)) ltac:(cond).
stepn (ltac:(oF' 0x5da88%Z)) (ltac:(oD' 0x5da88%Z)).
mld (ltac:(oF' 0x5da8c%Z)) (ltac:(oD' 0x5da8c%Z)) (0x132650 : word) G7.
mld (ltac:(oF' 0x5da90%Z)) (ltac:(oD' 0x5da90%Z)) (0x13b9e0 : word) G8.
stepn (ltac:(oF' 0x5da94%Z)) (ltac:(oD' 0x5da94%Z)).
stepn (ltac:(oF' 0x5da98%Z)) (ltac:(oD' 0x5da98%Z)).
stepb_ft (ltac:(oF' 0x5da9c%Z)) (ltac:(oD' 0x5da9c%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x5daa0%Z)) (ltac:(oD' 0x5daa0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5daa4%Z)) (ltac:(oD' 0x5daa4%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x5daa8%Z)) (ltac:(oD' 0x5daa8%Z)) (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
stepret (ltac:(oF' 0x5daac%Z)) (ltac:(oD' 0x5daac%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ split; [gres; reflexivity | solve_keeps_cs].
Qed.
End SE.
Lemma land_8191 : ltac2:(TCodec.tc2 tcn__Ja0FakeStack1 ";'5'3&Cr1+WoO%3221&D+XP0%2251%83941pQ<:1").
Proof. intros a. change 8191%Z with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.
Section FSM1.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra a0v : word.
Variables s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
Variables fs h pos ff : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hret : ret_ok ra.
Hypothesis Hs : (0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true.
Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
Hypothesis Hmd : (0 <= md < 255)%Z.
Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
Hypothesis Hverb : (0 <= verb < 3)%Z.
Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
tls_cells tpv 0x133430 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.
Hypothesis Hfs : (0x691000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
Hypothesis Hh : (0 <= h < 2 ^ 62)%Z.
Hypothesis Hpos_def : pos = (h mod 8192)%Z.
Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 2 ^ 20 + 128 * pos)%Z.
Definition tls_r : Z := tls_res off ent.
Hypothesis Hr : (0 <= tls_r /\ tls_r + 8 < 2 ^ 64)%Z /\ (tls_r + 8 <= s - 208 \/ s <= tls_r)%Z /\ (tls_r + 8 <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= tls_r)%Z.
Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 tls_r) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 0].
Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
Hypothesis Hflag : rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 16384 + pos)) 1%nat = Some [Z_to_bv 8 0].
Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
Hypothesis HG : rt_layout_globs mem0.
Hypothesis Happ : in_app ff.
Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 16%nat = true.
Hypothesis Hshadow_dj : (SB + ff / 8 + 16 <= s - 208 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 16 <= 0x132638 \/ 0x13b9f8 <= SB + ff / 8)%Z.
#[local] Ltac hide_dj := try hide Hfs; try hide Hr; try hide Hshadow_dj.
Definition F4 (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)).
Definition fsm1_mem (Mj : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mj
(Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1))))
(Z_to_bv 64 (fs + 4096 + 16384 + pos)) [Z_to_bv 8 1])
(Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
(Z_to_bv 64 (ff + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 16384 + pos))))
(Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).
Lemma sp_s1 : ltac2:(TCodec.tc2 tcn__Ja0FakeStack1 "9'3'Q0yR0%211vM&OvL%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
End FSM1.
End FPX_1.
