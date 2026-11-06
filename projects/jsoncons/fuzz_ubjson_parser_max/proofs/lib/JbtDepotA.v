(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtDepotA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtDepotA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtDepotA.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "4Z"; "5bytes_le_to_Z"; "6Segment"; "7bvmap"]; ["0M"; "0M'"; "0N"; "8apart"; "8cell"; "8wr"; "9msteps"; ":ret_ok"; ";DEP"; "<dp_frame"; "<dp_lock_mem"; "<dp_nodes"; ";MAP1"; ";rcell"; "=c_lts"; "=getr"]; ["=mkst"; "=rdn"; "=v_or"; "=v_srliw"; "=v_xor"; ">mem_grows"; "?loaded_segments"; "@add"; "@le"; "@lor"; "@lt"; "@ltb"; "@lxor"; "@modulo"; "@mul"; "@of_nat"]; ["@pow"; "@sub"; "@to_nat"; "0X"; "0a"; "0adr"; "0b"; "0bs"; "0bs'"; "0cur"; "0e"; "0fx"; "0h"; "0h'"; "0h0"; "0hN"]; ["0i"; "0id"; "0j"; "0k"; "0k1"; "0k2"; "0l2"; "0m"; "0mC"; "0q"; "0r"; "0raw"; "0regs"; "0regs'"; "0regs0"; "0rom"]; ["0s"; "0segs"; "0size"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_signed"; "Abv_unsigned"; "0trp"; "0u"; "0v"; "0x"; "0y"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition DEP : Z := 0x21e918.
Definition NID : Z := 0x61e918.
Definition MAP1 : Z := 0x61e928.
Definition STO : Z := 0x20e908.
Lemma lxor_range64 : ltac2:(TCodec.tc2 tcn__JbtDepotA "H'<'6&Q8zr2%3221&Q:&Q@+2+R0%3221%5271%;271&Q<r4r3%3221%?2>1%<228%B221p081p091pUJF1pUHG1").
Proof.
intros x y Hx Hy. split. apply Z.lxor_nonneg; lia.
destruct (Z.eq_dec (Z.lxor x y) 0) as [E|NZ]; [rewrite E; lia|].
assert (Hl : Z.log2 (Z.lxor x y) < 64).
{ eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt.
- destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
- destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lxor_nonneg x y). lia.
Qed.
Lemma art_zb_xor : ltac2:(TCodec.tc2 tcn__JbtDepotA "Q0'<'6&Q8zr2%3221&Q:&Q@+2+R0%3221%5271%;271'7'REyR0%211&Q4&RDr4%2251r3%4271%6231&Q<%1264%82;1%>3;41p0@1p0A1pUJN1pUHO1").
Proof. intros x y Hx Hy. unfold v_xor. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma art_zb_or : ltac2:(TCodec.tc2 tcn__JbtDepotA "Q0'<'6&Q8zr2%3221&Q:&Q@+2+R0%3221%5271%;271'7'REyR0%211&Q2&RDr4%2251r3%4271%6231&Q9%1264%82;1%>3;41p0@1p0A1pUJN1pUHO1").
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma zb_fresh : ltac2:(TCodec.tc2 tcn__JbtDepotA "K'<'8'6&Q8zr1%3221&Q:&Q@+2+R0%3221%5271%;271'7'REyR0%211&RDr2%2241%325@%83521%E2:1qUDH1%H2I1pSFJ1").
Proof.
intros e. exists (e mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
apply art_zb_eq. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Ltac zfresh u :=
lazymatch goal with |- msteps _ (mkst (regupd _ _ (Z_to_bv 64 ?e)) _ _ _) _ =>
let R := fresh "R" u in let E := fresh "E" u in
destruct (zb_fresh e) as [u [R E]]; rewrite E; clear E
end.
Lemma rdn_grows : ltac2:(TCodec.tc2 tcn__JbtDepotA "Q='2'>%211'3'REyR0%211'4y8%511%311p051%<13&Q5r4r3%3221'7%;16&Q1r7r5r6%443281(0r2%22>1%:3941'8r9r8%<429:1r1%92E1%A3@31qSBG1%82H1p0:1p0F1pS@K1pS:Q21pQ4N1pQ2O1pT8Q81pU4Q:1").
Proof.
intros segs k. induction k as [|k IH]; intros M M' a bs G R; [exists []%list; reflexivity|].
cbn [rdn] in R |- *.
destruct (M a) as [b|] eqn:Ma.
- assert (M'a : M' a <> None) by (apply G; congruence). destruct (M' a) as [b'|]; [|congruence].
destruct (rdn segs M (a + 1) k) as [rest|] eqn:Rk; [|discriminate].
destruct (IH M M' (a + 1)%bv rest G Rk) as [rest' ->]. eexists; reflexivity.
- destruct (seg_rom segs a) as [b|]; [|discriminate].
destruct (rdn segs M (a + 1) k) as [rest|] eqn:Rk; [|discriminate].
destruct (IH M M' (a + 1)%bv rest G Rk) as [rest' ->].
destruct (M' a); eexists; reflexivity.
Qed.
Definition rcell (M : word -> option byte) (a : Z) : Prop := exists bs, rdn ASEGS M (Z_to_bv 64 a) 8%nat = Some bs.
Lemma rcell_grows : ltac2:(TCodec.tc2 tcn__JbtDepotA "F'REyR0%211'4y8%511%311p051'<&Q5r3r2%3221&Mr4%2214%3226p021p061pS:;1pQ4=1pQ2>1").
Proof. intros M M' a G (bs & R). destruct (rdn_grows _ _ _ _ _ _ G R) as [bs' R']. exists bs'. exact R'. Qed.
Lemma art_bytes8_range : ltac2:(TCodec.tc2 tcn__JbtDepotA "Q7'REyR0%211'4y8%511%311p051'2%114'7%812&Q1&Q6r3r2u8%544321(0r1%22;1%;3:41'6&Q8z&=%11;%4231&Q:&Q@+2+R0%3221%5271%<271p0>1pS@K1pS:Q31pQ2O1").
Proof.
intros M a bs H. pose proof (rdn_length _ _ _ _ _ H) as L. pose proof (bytes_le_to_Z_bound bs) as B.
pose proof (bytes_le_to_Z_nonneg bs). rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B. lia.
Qed.
Ltac zldr F D a R :=
chain_step; [reflexivity
| eapply step_ld with (v := Z_to_bv 64 (bytes_le_to_Z _)); [exact F | reflexivity | exact D | zaddr a; exact R | rewrite art_u_lit; [reflexivity | eapply art_bytes8_range; exact R] ]
| step_simpl; vnorm].
Lemma art_signed_small : ltac2:(TCodec.tc2 tcn__JbtDepotA "G'<'6&Q8zr1%3221&Q:&Q@+2+QO%3221%5271%;271'7&RFyR0&RDr2%2231%5241%73D13p091pULF1").
Proof.
intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma art_c_lts_zb : ltac2:(TCodec.tc2 tcn__JbtDepotA "N'<'6&Q8zr2%3221&Q:&Q@+2+QO%3221%5271%;271'7'1&N&RDyR0r4%3221r3%5241%7231&Q;%1264%<3;31p0>1p0?1pUJL1pUHM1").
Proof. intros x y Hx Hy. unfold c_lts, bv_lts. rewrite !art_signed_small by lia. reflexivity. Qed.
Lemma art_srliw_small : ltac2:(TCodec.tc2 tcn__JbtDepotA "Q0'<'6&Q8zr2%3221&Q:&Q@+2r1%3221%5271%;271+O%<2:1%>2:1'7'REyR0%211&Q3&RDr4%2251r3%5221%528G%;3821p0=1p0A1pT8N1pUHO1").
Proof.
intros x k Hx Hk. unfold v_srliw. rewrite art_u_lit by (assert (2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia); lia).
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
assert (2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Ltac zconds := rwH; rewrite ?art_c_eq_zb, ?art_c_ltu_zb, ?art_c_lts_zb by lia;
first [ apply Z.eqb_neq; lia | apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ].
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma dp_hash_loop : ltac2:(TCodec.tc2 tcn__JbtDepotA "U='3&?y5'REyR0%211%5241'4y8%611%311p061'<'6&Q8zr1%3221&Q:r5%2241%8241&Mr9&Q7r7&Q>+8r2%3221%6251%9281p0;1pT6E1r6%E2D1%:292%=2<1&Q@+2+R0%3221%H251%I292%O291%O2NJ%L2K5%Q2221%Q22Q1G'7r8&Q?r?%211%N241+1%Q0221r:%93Q>21&O(RC+;(5%33QM21%52<1&RDr<%Q92Q8Q<%Q<221%42R11%E3R161r@+>%=3R71;%?231r=%QB2QA:%QE221%=2R:1%N3R:51rA+:%F3R@1D%H231%C2R@B%Q43R@21rB+<%L3RF1J%N231r;%J2RG1%Q;3RG31'8'F&Q6&Q0vQKrE+cV_<%Q83S01Q6/01S0rDrC%8576321+cV`@%Q>3S61Q</01S6%<5;R@165%?3>51%QC2RBQ?%RE2RDO%RH2J1%Q@2S=1%R13S=41%QH2RGK%QC2S@S4%R43S@21%S42S6R=%S:2S61%SE1SF&9%R932S:QK%211%R;34S0Q4%411r3+?%R43SN1R2%R@3931%911r4+@%R93T31R7%RE3>31%>11%R=2S?SErJ%R?21SG%RJ3T631p051p0;1p0A1p0D1pTFH1%T42J1%T52M1%T62Q11%T72Q71qSLT91%QI2T:1qTLTA1%QK2TB1p0QM1p0R51p0R<1p0RF1p0S31p0S>1p0S@1p0SD1p0SG1p0SO1p0T21pSJTH1pT2TI1pTBTJ1pU6TK1pUBTL1pU0TN1pQ2TO1pTJU51pTDU<1").
Proof.
induction q as [|q IH]; intros regs M rom trp size mC i h RC Ht1 Ht2 HmC Hh Hi Hq H11 H14 H10 H12.
- destruct (RC i ltac:(lia)) as (bs & Rb). pose proof (art_bytes8_range _ _ _ Rb) as Bb.
destruct (zb_fresh (bytes_le_to_Z bs * mC)) as [u1 [R1 E1]].
pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)).
destruct (zb_fresh (Z.lxor (u1 / 2 ^ 47) u1)) as [u2 [R2 E2]].
destruct (zb_fresh (u2 * mC)) as [u3 [R3 E3]].
destruct (zb_fresh (Z.lxor u3 h)) as [u4 [R4 E4]].
destruct (zb_fresh (u4 * mC)) as [u5 [R5 E5]].
eexists _, _. split; [|split; [|split; [|split]]].
+ zldr (ltac:(oF' 0x999ec%Z)) (ltac:(oD' 0x999ec%Z)) (trp + 8 * i) Rb.
zstep (ltac:(oF' 0x999f0%Z)) (ltac:(oD' 0x999f0%Z)).
zstep (ltac:(oF' 0x999f4%Z)) (ltac:(oD' 0x999f4%Z)). rewrite E1.
stepn (ltac:(oF' 0x999f8%Z)) (ltac:(oD' 0x999f8%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x999fc%Z)) (ltac:(oD' 0x999fc%Z)). rwH. rewrite art_zb_xor by lia. rewrite E2.
zstep (ltac:(oF' 0x99a00%Z)) (ltac:(oD' 0x99a00%Z)). rewrite E3.
stepn (ltac:(oF' 0x99a04%Z)) (ltac:(oD' 0x99a04%Z)). rwH. rewrite art_zb_xor by lia. rewrite E4.
zstep (ltac:(oF' 0x99a08%Z)) (ltac:(oD' 0x99a08%Z)). rewrite E5.
zbft (ltac:(oF' 0x99a0c%Z)) (ltac:(oD' 0x99a0c%Z)).
apply mst_refl.
+ kept_solve.
+ kept_solve.
+ lia.
+ intros r N11 N12 N15 N16. kept_solve.
- destruct (RC i ltac:(lia)) as (bs & Rb). pose proof (art_bytes8_range _ _ _ Rb) as Bb.
destruct (zb_fresh (bytes_le_to_Z bs * mC)) as [u1 [R1 E1]].
pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)).
destruct (zb_fresh (Z.lxor (u1 / 2 ^ 47) u1)) as [u2 [R2 E2]].
destruct (zb_fresh (u2 * mC)) as [u3 [R3 E3]].
destruct (zb_fresh (Z.lxor u3 h)) as [u4 [R4 E4]].
destruct (zb_fresh (u4 * mC)) as [u5 [R5 E5]].
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x999ec : word) M rom) (mkst r1 (0x999ec : word) M rom)
/\ (getr r1 11 = Z_to_bv 64 (trp + 8 * (i + 1)) /\ getr r1 14 = Z_to_bv 64 (trp + 8 * size) /\ getr r1 10 = Z_to_bv 64 mC
/\ getr r1 12 = Z_to_bv 64 u5
/\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> getr r1 r = getr regs r))).
{ eexists. split.
- zldr (ltac:(oF' 0x999ec%Z)) (ltac:(oD' 0x999ec%Z)) (trp + 8 * i) Rb.
zstep (ltac:(oF' 0x999f0%Z)) (ltac:(oD' 0x999f0%Z)).
zstep (ltac:(oF' 0x999f4%Z)) (ltac:(oD' 0x999f4%Z)). rewrite E1.
stepn (ltac:(oF' 0x999f8%Z)) (ltac:(oD' 0x999f8%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x999fc%Z)) (ltac:(oD' 0x999fc%Z)). rwH. rewrite art_zb_xor by lia. rewrite E2.
zstep (ltac:(oF' 0x99a00%Z)) (ltac:(oD' 0x99a00%Z)). rewrite E3.
stepn (ltac:(oF' 0x99a04%Z)) (ltac:(oD' 0x99a04%Z)). rwH. rewrite art_zb_xor by lia. rewrite E4.
zstep (ltac:(oF' 0x99a08%Z)) (ltac:(oD' 0x99a08%Z)). rewrite E5.
zbtk (ltac:(oF' 0x99a0c%Z)) (ltac:(oD' 0x99a0c%Z)).
apply mst_refl.
- split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. intros r N11 N12 N15 N16. kept_solve. }
destruct S1 as (r1 & RUN1 & Q11 & Q14 & Q10 & Q12 & K1).
destruct (IH r1 M rom trp size mC (i + 1) u5 RC Ht1 Ht2 HmC R5 ltac:(lia) ltac:(lia) Q11 Q14 Q10 Q12) as (r2 & h2 & RUN2 & P11 & P12 & Rh2 & K2).
exists r2, h2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
split; [exact P11|]. split; [exact P12|]. split; [exact Rh2|].
intros r N11 N12 N15 N16. rewrite (K2 r N11 N12 N15 N16). apply K1; assumption.
Qed.
Definition dp_nodes (M : word -> option byte) (l2 N : Z) : Prop :=
forall id, 1 <= id <= N -> exists hv lk, 0 <= hv < 2 ^ 64 /\ cellA M (l2 + 16 * id) 8 hv /\ cellA M (l2 + 16 * id + 8) 4 lk /\ 0 <= lk < id.
#[using="Type"] Lemma dp_find_loop : ltac2:(TCodec.tc2 tcn__JbtDepotA "U>'3&?y5'REyR0%211%5241'4y8%611%311p061'<';&QBr1%211r8%5221&D&Q6r7&Lu8r5%6554321&Q8+TP0r6%3221&Q:&Q7&Q@+2+D%3221%52?1+R0%6251%9231'7&Q=+@%22J1z%53Q121'6%E23N%@2?6%C2Q01%4231&Kr<r:r9%43321%N2Q73%;2:1%Q02>5%M26E%>221&Or@(RC+;(5%33R021%6251&RD%12R1@%N3R131rA+C%:3R718%=231%72R7G%Q43R721rB+H%@3R=1>%C231%=2R=QK%Q:3R=21rC+F%F3RC1D%I231+QooO%D2RD1%QA3RD31'8':'F&Q0vQKrE+cVcL%Q23RM1Q0/01RMrD%756521A+cVfD%Q73S21Q5/01S2%;5:RI15E%=3RE51%Q=2RKQ8%Q72S7QO%R43S721%QO241+cVl0%Q@3S;1Q>/01S;%D5CS21>N%F3RN>1+1%RJ21S5%RK2S6Q8%R8221r2+:%QJ3SG1QH%QM231%QG2SGS<%RD3SG21%R?271qT4SB1%Q52SC1%RB2>1%Q62D1%SO1T0&9%RL32SE;%211%RN34?R4%411r3+<%R;3T81R9%S33931%911r4%RA2SF1rI%RC213%S93T<31p061p0<1p0?1pTFC1%S82E1qTLTA1%QN2TB1p0R01p0R81p0R?1p0RF1p0S11p0S51p0S81p0S>1p0SD1p0SK1p0T61p0T;1p0TC1pSDTJ1pSJTK1pQ6TL1pT>TM1pU0TO1pQ2U01pTJU61pT@U=1").
Proof.
induction m as [|m IH]; intros regs M rom l2 N h cur Hm CM Hl2 Hl2' Hl16 HN ND Hcur Hh H11 H19 H24 H22.
- assert (cur = 0) by lia. subst cur.
eexists. split; [left; split|].
+ zbtk (ltac:(oF' 0x99a7c%Z)) (ltac:(oD' 0x99a7c%Z)). apply mst_refl.
+ exact H11.
+ intros; reflexivity.
- destruct (Z.eq_dec cur 0) as [->|NZ].
{ eexists. split; [left; split|].
+ zbtk (ltac:(oF' 0x99a7c%Z)) (ltac:(oD' 0x99a7c%Z)). apply mst_refl.
+ exact H11.
+ intros; reflexivity. }
destruct (ND cur ltac:(lia)) as (hv & lk & Rhv & Chv & Clk & Rlk).
unfold MAP1 in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x99a7c : word) M rom) (mkst r1 (0x99ab4 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 cur /\ getr r1 11 = Z_to_bv 64 lk /\ getr r1 12 = Z_to_bv 64 hv /\ getr r1 19 = Z_to_bv 64 h
/\ getr r1 24 = Z_to_bv 64 6416680 /\ getr r1 22 = Z_to_bv 64 65535
/\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr r1 r = getr regs r))).
{ eexists. split.
- zbft (ltac:(oF' 0x99a7c%Z)) (ltac:(oD' 0x99a7c%Z)).
zstep (ltac:(oF' 0x99a80%Z)) (ltac:(oD' 0x99a80%Z)).
stepn (ltac:(oF' 0x99a84%Z)) (ltac:(oD' 0x99a84%Z)). rwH. rewrite art_srliw_small by lia.
zstep (ltac:(oF' 0x99a88%Z)) (ltac:(oD' 0x99a88%Z)).
zstep (ltac:(oF' 0x99a8c%Z)) (ltac:(oD' 0x99a8c%Z)).
zld (ltac:(oF' 0x99a90%Z)) (ltac:(oD' 0x99a90%Z)) 6416680 CM.
zbft (ltac:(oF' 0x99a94%Z)) (ltac:(oD' 0x99a94%Z)).
zstep (ltac:(oF' 0x99a98%Z)) (ltac:(oD' 0x99a98%Z)).
stepn (ltac:(oF' 0x99a9c%Z)) (ltac:(oD' 0x99a9c%Z)). rwH. rewrite (art_zb_srli_exact (cur * 2 ^ 32) 32 cur) by lia.
stepn (ltac:(oF' 0x99aa0%Z)) (ltac:(oD' 0x99aa0%Z)). rwH. rewrite art_zb_and by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
rewrite (Z.mod_small cur (2 ^ 16)) by lia.
zstep (ltac:(oF' 0x99aa4%Z)) (ltac:(oD' 0x99aa4%Z)).
zstep (ltac:(oF' 0x99aa8%Z)) (ltac:(oD' 0x99aa8%Z)).
zld (ltac:(oF' 0x99aac%Z)) (ltac:(oD' 0x99aac%Z)) (l2 + 16 * cur) Chv.
zlw (ltac:(oF' 0x99ab0%Z)) (ltac:(oD' 0x99ab0%Z)) (l2 + 16 * cur + 8) Clk.
apply mst_refl.
- repeat (split; [kept_solve|]). intros r N10 N11 N12. kept_solve. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q19 & Q24 & Q22 & K1).
destruct (Z.eq_dec h hv) as [EQ|NE].
+
eexists. split; [right; split|].
* eapply msteps_trans; [exact RUN1|].
zbft (ltac:(oF' 0x99ab4%Z)) (ltac:(oD' 0x99ab4%Z)).
stepn (ltac:(oF' 0x99ab8%Z)) (ltac:(oD' 0x99ab8%Z)).
apply mst_refl.
* exists cur. split; [lia|]. kept_solve.
* intros r N10 N11 N12. kept_solve || (gres; apply K1; assumption).
+
assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x99ab4 : word) M rom) (mkst r2 (0x99a7c : word) M rom)
/\ (getr r2 11 = Z_to_bv 64 lk /\ getr r2 19 = Z_to_bv 64 h /\ getr r2 24 = Z_to_bv 64 6416680 /\ getr r2 22 = Z_to_bv 64 65535
/\ (forall r : reg, getr r2 r = getr r1 r))).
{ eexists. split.
- zbtk (ltac:(oF' 0x99ab4%Z)) (ltac:(oD' 0x99ab4%Z)). apply mst_refl.
- repeat (split; [kept_solve|]). intros; reflexivity. }
destruct S2 as (r2 & RUN2 & P11 & P19 & P24 & P22 & K2).
destruct (IH r2 M rom l2 N h lk ltac:(lia) CM Hl2 Hl2' Hl16 HN ND ltac:(lia) Hh P11 P19 P24 P22) as (r3 & ALT & K3).
exists r3. split.
* destruct ALT as [[RUN3 A]|[RUN3 A]]; [left|right]; split; try exact A;
(eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3).
* intros r N10 N11 N12. rewrite (K3 r N10 N11 N12), (K2 r). apply K1; assumption.
Qed.
Definition dp_lock_mem (M : word -> option byte) (s adr v : Z) (raw : word) (x8 x9 x18 x19 : word) : word -> option byte :=
Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) (U raw)) (s - 16) (U x8)) (s - 24) (U x9)) (s - 32) (U x18)) (s - 40) (U x19))
adr (Z.lor v 18446744071562067968).
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
Section SE.
Local Abbreviation SEC_T_dp_lock_run := (ltac2:(TCodec.tc2 tcn__JbtDepotA "U@&?y5'REyR0%211%5241'4y8%611%311p061'<'7&Or7(RC+2(5%33A21%6251&RDr3%22C1%;3C41r8+:%;3I19%>231%@3H16r9+1%@3N1>%C231r6%F3N21&G%11F&Q8+TP0&QA+Q@%22K1%5241&Q:&Q@+R0%22N1%42G1%;2:H&Q7+4%22F1%9216&Q=r:%2215z%Q=3Q>21'6%F235+O%A2Q=1%C281%5241&D&Q6r@r<u4r;%6554321&ErAr=%34921HrBr?%Q621Q5%74=31Q6&C%Q92>Q8%245O1Q9'8'F&Q0vQKrF+cXV@%R93RE1R7/01RErErD%8576321r1rC&J+8%RB3S01R@%RE2<1+9%RE3S31RC%RH2?1+B%RH3S61RF%RK2B1+C%RK3S91RI%RN2E1%=9BQ1Q4Q:>:741%I5H@?1B%K3Q=B1%S22BRE%RL2S=Q>%S53S=21%S52ES0%RO2S@Q8%S83S@21%SC1SD&9%S;32JRM%211r2+;%S<3SJ1S:%S@3731%711+<%S@3SN1S>%SD3;S;1%;11r4+=%SE3T31SC%SI3@31%@11r5+>%SJ3T81SH%SN3E31%E11%SO2SNS;rL%T121S=%T33T;31p051p0;1p0A1p0F1p0L1pTFQ01%RL2Q21%RM2Q61%RN2Q:1qTLTD1%R82TE1p0R:1p0R>1p0RC1p0RH1p0S01p0S71p0S=1p0SB1p0SD1p0SJ1p0T11p0T41p0T;1p0TA1pUFTN1pS<TO1pU2U01pTHU81pU0U31pQ2U41pTJU:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_dp_lock_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_dp_lock_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_dp_lock_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_dp_lock_run) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_dp_lock_run) 4%nat 0%nat).
Variable adr : ltac:(sec_ty2 constr:(SEC_T_dp_lock_run) 5%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_dp_lock_run) 6%nat 0%nat).
Lemma dp_lock_run : ltac:(sec_stmt2 constr:(SEC_T_dp_lock_run) 7%nat 0%nat).
Proof using Type regs M rom raw s adr v.
intros H2 H10 H1 Hret Hs Hs' Ha Ha' Ha4 Hv Cv Wv Wf AP.
unfold dp_lock_mem.
eexists. split; [|split; [|split]].
- zstep (ltac:(oF' 0x9a0d0%Z)) (ltac:(oD' 0x9a0d0%Z)).
zsd (ltac:(oF' 0x9a0d4%Z)) (ltac:(oD' 0x9a0d4%Z)) (s - 8) (U raw) ltac:(rewok Wf).
zsd (ltac:(oF' 0x9a0d8%Z)) (ltac:(oD' 0x9a0d8%Z)) (s - 16) (U (getr regs 8)) ltac:(rewok Wf).
zsd (ltac:(oF' 0x9a0dc%Z)) (ltac:(oD' 0x9a0dc%Z)) (s - 24) (U (getr regs 9)) ltac:(rewok Wf).
zsd (ltac:(oF' 0x9a0e0%Z)) (ltac:(oD' 0x9a0e0%Z)) (s - 32) (U (getr regs 18)) ltac:(rewok Wf).
zsd (ltac:(oF' 0x9a0e4%Z)) (ltac:(oD' 0x9a0e4%Z)) (s - 40) (U (getr regs 19)) ltac:(rewok Wf).
zstep (ltac:(oF' 0x9a0e8%Z)) (ltac:(oD' 0x9a0e8%Z)).
zstep (ltac:(oF' 0x9a0ec%Z)) (ltac:(oD' 0x9a0ec%Z)).
stepn (ltac:(oF' 0x9a0f0%Z)) (ltac:(oD' 0x9a0f0%Z)).
zstep (ltac:(oF' 0x9a0f4%Z)) (ltac:(oD' 0x9a0f4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cv' : cellA X adr 4 v) by recell Cv; assert (Wv' : wok AsanUbsan.M.loaded_segments X adr 4) by (rewok Wv) end.
zlw (ltac:(oF' 0x9a0f8%Z)) (ltac:(oD' 0x9a0f8%Z)) adr Cv'.
stepb_tk (ltac:(oF' 0x9a0fc%Z)) (ltac:(oD' 0x9a0fc%Z)) ltac:(zconds).
stepn (ltac:(oF' 0x9a110%Z)) (ltac:(oD' 0x9a110%Z)). rwH.
match goal with |- context [v_or (Z_to_bv 64 v) ?L] =>
replace (v_or (Z_to_bv 64 v) L) with (Z_to_bv 64 (Z.lor v 18446744071562067968) : word)
by (symmetry; replace L with (Z_to_bv 64 18446744071562067968 : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_or; lia) end.
chain_step; [reflexivity
| eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 adr) _ (Z_to_bv 64 v));
[exact (ltac:(oF' 0x9a114%Z)) | reflexivity | exact (ltac:(oD' 0x9a114%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Ha4
| exact Cv' | apply art_bytes4; lia ]
| ]. wpc. rewrite art_v_lw_small by lia.
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x9a118%Z)) | reflexivity | exact (ltac:(oD' 0x9a118%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity
| eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 adr));
[exact (ltac:(oF' 0x9a11c%Z)) | reflexivity | exact (ltac:(oD' 0x9a11c%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Ha4 | gres; rwH; reflexivity
| exact Wv' ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 adr) (word_to_le_bytes 4 (Z_to_bv 64 (Z.lor v 18446744071562067968)))) with (Wn 4 M0 adr (Z.lor v 18446744071562067968)).
zbft (ltac:(oF' 0x9a120%Z)) (ltac:(oD' 0x9a120%Z)).
stepb_tk (ltac:(oF' 0x9a124%Z)) (ltac:(oD' 0x9a124%Z)) ltac:(zconds).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (L1 : cellA X (s - 8) 8 (U raw)) by zcell;
assert (L2 : cellA X (s - 16) 8 (U (getr regs 8))) by zcell;
assert (L3 : cellA X (s - 24) 8 (U (getr regs 9))) by zcell;
assert (L4 : cellA X (s - 32) 8 (U (getr regs 18))) by zcell;
assert (L5 : cellA X (s - 40) 8 (U (getr regs 19))) by zcell end.
zld (ltac:(oF' 0x9a144%Z)) (ltac:(oD' 0x9a144%Z)) (s - 8) L1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a148%Z)) (ltac:(oD' 0x9a148%Z)) (s - 16) L2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a14c%Z)) (ltac:(oD' 0x9a14c%Z)) (s - 24) L3. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a150%Z)) (ltac:(oD' 0x9a150%Z)) (s - 32) L4. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9a154%Z)) (ltac:(oD' 0x9a154%Z)) (s - 40) L5. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x9a158%Z)) (ltac:(oD' 0x9a158%Z)).
stepret (ltac:(oF' 0x9a15c%Z)) (ltac:(oD' 0x9a15c%Z)) raw ltac:(rwH; reflexivity).
replace (s - 48 + 48) with s by lia. apply mst_refl.
- kept_solve.
- kept_solve.
- intros r N10 N11 N12 N13 N14. kept_solve.
Qed.
End SE.
Definition dp_frame (M : word -> option byte) (s trp szt : Z) (raw : word) (rg : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
(s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19)))
(s - 48) (U (getr rg 20))) (s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24)))
(s - 88) (U (getr rg 25))) (s - 104) trp) (s - 96) szt.
#[using="Type"] Lemma mod_mul_pow44 : ltac2:(TCodec.tc2 tcn__JbtDepotA "H'<&Q8zr1%3221'7&Q=&Q>r2&Q@+2+Q<%3221%6251+R0%6251%:231+D%9281%=2;1%=218%@3E51p0B1pSJG1").
Proof. intros h Hh. change (2 ^ 64) with (2 ^ 20 * 2 ^ 44). rewrite Z.mul_mod_distr_r by lia. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_dp_pro_run := (ltac2:(TCodec.tc2 tcn__JbtDepotA "VE&?y5'REyR0%211%5241'4y8%611%311p061'<'7&Or:(RC+2(5%33A21%6251&RDr6%22C1%;3C41r;+:%;3I19%>231%@3H16r<+;%@3N1>%C231%E3M1;r=+1%E3Q31C%H231%J3Q21H&Q8+Vb\P0&QA+W0%22M1%5241&Q:&Q@+R0%22Q01%42I1+TP0%<21K&Q7&Q>+8%221O%42K1%<219'6%D2HN+N%F2Q01%4231z%I21Q3%D2Q4A%8221&D&Q6rE+RPg8u8r?%6554321rF+RPi0%9582154rG+RPoH%<5;2187&ErH%Q92=Q8%34?21Q9'8'F&Q0vQKrL+cVYL%R;3RG1R9/01RGrKrJ%8576321r2+cV_<%RB3RN1R@/01RN&IrI%269DHK1=%@5?7419%B3Q391%RK29R9%RE2S6L%RN3S621+>%RM3S;1RK%S02>1%QI2QHQ4%QK2Q21%RL2S=1%S53S=41%S52CRH%RO2S@Q>%S83S@21+<%S73SE1S5%S:2H1r1%S52SF1%S>3SF31%RD2QL3%R?24R<%R3221+=%S@3SN1S>%SC2Q11%S=2SNR2%SF3SN21%SD3T2R=SB%SG2Q51%SI3T114+9%SH3T61SF%SK2Q91&H%SF2T71%SO3T731%SO2Q=SJ+S@%S52QM1%SK2T<1%T43T<41%T?1T@&9%T732KT1%211%T934QFB%411r3%T<371A%711&RGr4%22TK1%SF2T41+@%SH231%S6231%?11r7r5%TG221rQ1%TI213%TK3U331p071p0@1p0D1p0G1pTFK1%SC2M1%SD2Q31%SE2Q:1%SF2Q>1%SG2QD1%SH2QH1%SI2QO1%SJ2R31%SK2R;1%SL2R?1qSNU<1%S42U=1qTLUD1%S62UE1p0S81p0S=1p0SA1p0SE1p0SM1p0SN1p0SO1p0T41p0T:1p0TA1p0TD1p0TJ1p0U11p0U71p0U=1p0UC1pT<V01pT:V11pTBV21pU6V31pUBV41pU2V51pTHV=1pU0V81pQ2V91pTJV?1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 4%nat 0%nat).
Variable trp : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 5%nat 0%nat).
Variable size : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 6%nat 0%nat).
Variable mC : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 7%nat 0%nat).
Variable k1 : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 8%nat 0%nat).
Variable k2 : ltac:(sec_ty2 constr:(SEC_T_dp_pro_run) 9%nat 0%nat).
Lemma dp_pro_run : ltac:(sec_stmt2 constr:(SEC_T_dp_pro_run) 10%nat 0%nat).
Proof using Type regs M rom raw s trp size mC k1 k2.
intros H2 H10 H11 H1 Hs Hs' Ht Ht' Hsz HmC Hk1 Hk2 CmC Ck1 Ck2 W.
destruct (zb_fresh (size * k1)) as [u1 [R1 E1]].
destruct (zb_fresh (Z.lxor u1 k2)) as [h0 [R0 E0]].
unfold dp_frame, DEP.
eexists _, h0. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
- zstep (ltac:(oF' 0x9993c%Z)) (ltac:(oD' 0x9993c%Z)).
stepn (ltac:(oF' 0x99940%Z)) (ltac:(oD' 0x99940%Z)).
stepn (ltac:(oF' 0x99944%Z)) (ltac:(oD' 0x99944%Z)).
zstep (ltac:(oF' 0x99948%Z)) (ltac:(oD' 0x99948%Z)).
zstep (ltac:(oF' 0x9994c%Z)) (ltac:(oD' 0x9994c%Z)).
zstep (ltac:(oF' 0x99950%Z)) (ltac:(oD' 0x99950%Z)).
zstep (ltac:(oF' 0x99954%Z)) (ltac:(oD' 0x99954%Z)).
stepn (ltac:(oF' 0x99958%Z)) (ltac:(oD' 0x99958%Z)).
zstep (ltac:(oF' 0x9995c%Z)) (ltac:(oD' 0x9995c%Z)).
zsd (ltac:(oF' 0x99960%Z)) (ltac:(oD' 0x99960%Z)) (s - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x99964%Z)) (ltac:(oD' 0x99964%Z)) (s - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x99968%Z)) (ltac:(oD' 0x99968%Z)) (s - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x9996c%Z)) (ltac:(oD' 0x9996c%Z)) (s - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x99970%Z)) (ltac:(oD' 0x99970%Z)) (s - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x99974%Z)) (ltac:(oD' 0x99974%Z)) (s - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x99978%Z)) (ltac:(oD' 0x99978%Z)) (s - 56) (U (getr regs 21)) ltac:(rewok W).
zsd (ltac:(oF' 0x9997c%Z)) (ltac:(oD' 0x9997c%Z)) (s - 64) (U (getr regs 22)) ltac:(rewok W).
zsd (ltac:(oF' 0x99980%Z)) (ltac:(oD' 0x99980%Z)) (s - 72) (U (getr regs 23)) ltac:(rewok W).
zsd (ltac:(oF' 0x99984%Z)) (ltac:(oD' 0x99984%Z)) (s - 80) (U (getr regs 24)) ltac:(rewok W).
zsd (ltac:(oF' 0x99988%Z)) (ltac:(oD' 0x99988%Z)) (s - 88) (U (getr regs 25)) ltac:(rewok W).
zstep (ltac:(oF' 0x9998c%Z)) (ltac:(oD' 0x9998c%Z)).
zstep (ltac:(oF' 0x99990%Z)) (ltac:(oD' 0x99990%Z)).
zsd (ltac:(oF' 0x99994%Z)) (ltac:(oD' 0x99994%Z)) (s - 104) trp ltac:(rewok W).
zsd (ltac:(oF' 0x99998%Z)) (ltac:(oD' 0x99998%Z)) (s - 96) size ltac:(rewok W).
zbtk (ltac:(oF' 0x9999c%Z)) (ltac:(oD' 0x9999c%Z)).
stepn (ltac:(oF' 0x999a4%Z)) (ltac:(oD' 0x999a4%Z)). rwH. unfold v_addiw. rewrite art_u_lit by lia.
replace (bv_swrap 32 (size + 0)) with size by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).
zstep (ltac:(oF' 0x999a8%Z)) (ltac:(oD' 0x999a8%Z)).
zbft (ltac:(oF' 0x999ac%Z)) (ltac:(oD' 0x999ac%Z)).
zbft (ltac:(oF' 0x999b0%Z)) (ltac:(oD' 0x999b0%Z)).
stepn (ltac:(oF' 0x999b4%Z)) (ltac:(oD' 0x999b4%Z)). rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small size (2 ^ 32)) by lia.
stepn (ltac:(oF' 0x999b8%Z)) (ltac:(oD' 0x999b8%Z)).
stepn (ltac:(oF' 0x999bc%Z)) (ltac:(oD' 0x999bc%Z)).
stepn (ltac:(oF' 0x999c0%Z)) (ltac:(oD' 0x999c0%Z)).
stepn (ltac:(oF' 0x999c4%Z)) (ltac:(oD' 0x999c4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (C1 : cellA X 0x10320 8 k1) by zcell; assert (C2 : cellA X 0x103f8 8 k2) by zcell; assert (C0 : cellA X 0x102e8 8 mC) by zcell end.
zld (ltac:(oF' 0x999c8%Z)) (ltac:(oD' 0x999c8%Z)) 0x10320 C1.
stepn (ltac:(oF' 0x999cc%Z)) (ltac:(oD' 0x999cc%Z)). rwH.
match goal with |- context [v_and (Z_to_bv 64 size) ?L] =>
replace (v_and (Z_to_bv 64 size) L) with (Z_to_bv 64 size : word)
by (symmetry; replace L with (Z_to_bv 64 (Z.ones 32) : word) by (apply bv_eq; vm_compute; reflexivity);
rewrite art_zb_and by (change (Z.ones 32) with 4294967295; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
stepn (ltac:(oF' 0x999d0%Z)) (ltac:(oD' 0x999d0%Z)).
zld (ltac:(oF' 0x999d4%Z)) (ltac:(oD' 0x999d4%Z)) 0x103f8 C2.
zld (ltac:(oF' 0x999d8%Z)) (ltac:(oD' 0x999d8%Z)) 0x102e8 C0.
zstep (ltac:(oF' 0x999dc%Z)) (ltac:(oD' 0x999dc%Z)). rewrite E1.
zstep (ltac:(oF' 0x999e0%Z)) (ltac:(oD' 0x999e0%Z)).
stepn (ltac:(oF' 0x999e4%Z)) (ltac:(oD' 0x999e4%Z)). rwH. rewrite art_zb_xor by lia. rewrite E0.
zstep (ltac:(oF' 0x999e8%Z)) (ltac:(oD' 0x999e8%Z)).
replace (trp + size * 2 ^ 3) with (trp + 8 * size) by lia.
apply mst_refl.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- exact R0.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- intros r N2 N8 N9 NR.
destruct (decide (r = 10%bv)) as [->|N10]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 11%bv)) as [->|N11]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 12%bv)) as [->|N12]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 13%bv)) as [->|N13]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 14%bv)) as [->|N14]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 15%bv)) as [->|N15]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
destruct (decide (r = 16%bv)) as [->|N16]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_dp_mid_run := (ltac2:(TCodec.tc2 tcn__JbtDepotA "W7&?y5'REyR0%211%5241'4y8%611%311p061'<'7&Or6(RC+<(5%33A21%6251&RDr3%22C1%;3C41r7+=%;3I19%>231z%92J1%B3J31r8+:%B3Q01@%E231r4%@2Q11%I3Q131r9+9%I3Q71G%L231&H%G2Q81%Q03Q831'6&Q8%12CG&Q:&Q@+2+R0%3221%52M1%9271+@%7261%92Q11%=2;1r1%>2Q01+D%=2<1%?241%C241'8&D&Q6r?&Q7&Q>+4%221QC%42O1u4%958721@r;%O2B1%Q12B1%Q2241qUFR51%@2R61p0B1pS>R81'F&Q0vQKrB+cV`@%R:3RF1R8/01RFrAr@%8576321+cVcL%R@3RL1R>/01RL%<5;QN165%>3O51%QE2R7R>%QD2R?Q@%QH221r2%QI2R;1%QH22Q:%QL221%Q42Q34%Q62R11%Q:5Q9A1Q2QAr=%R02QC1%R22QC1+C%S23S@1S0%S52R?1%S73S?1RM+B%S63SD1S4%S92RC1%S32SD<%S<3SD21+;%S;3SI1S9%S>2RH1%S82SIR1%SA3SI21+I%S@3SN1S>%SC2RM1%SE3SM15+H%SD3T21SB%SG2S11&L%SB2T31%SK3T331%SI3T7R;SG%SL2S61+TPPP8%R62S11%SH2T91%T13T941+F%T03T>1SN%T32S=1+QooO%SN2T?1%T73T?31+G%T63TD1T4%T92SC1+QoooooO%T42TE1%T=3TE31%T=2SGSB%T?3TG1S@%TJ1TK&9%TB32S3SM%211%TD34QJQ6%411%TF36T=T@%611%TH38T1T:%811r5+>%TI3U71TG%TM3=31%=11&RG%12U;TN%SO2QI1%T022SA%T2221%C11%62U@TI%T42Q41%T522QE%T7221%H11r<%U:21THrJ%U<21TJ%U>3UF31p061p0<1p0C1p0I1p0L1p0O1p0Q21pTFQ61%TF2Q81%TG2Q;1%TH2QB1%TI2QI1%TJ2R01%TK2R71%TL2R<1%TM2RB1%TN2RH1%TO2RM1%U02S11%U12S51%U22S:1%U32S>1qUFV61%TA2V71qS>V81%TC2V91qSJV:1%TE2V;1qTLVB1%TG2VC1p0T61p0U01p0U51p0U61p0UA1p0UI1p0V11p0V91pQ6VF1pTBVG1pT0VH1pU0VJ1pQ2VK1pTJW11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_dp_mid_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_dp_mid_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_dp_mid_run) 2%nat 0%nat).
Variable hN : ltac:(sec_ty2 constr:(SEC_T_dp_mid_run) 3%nat 0%nat).
Variable mC : ltac:(sec_ty2 constr:(SEC_T_dp_mid_run) 4%nat 0%nat).
Variable N : ltac:(sec_ty2 constr:(SEC_T_dp_mid_run) 5%nat 0%nat).
Lemma dp_mid_run : ltac:(sec_stmt2 constr:(SEC_T_dp_mid_run) 6%nat 0%nat).
Proof using Type regs M rom hN mC N.
intros H12 H13 H10 H9 HhN HmC HN BK.
destruct (zb_fresh (0 * mC)) as [u1 [R1 E1]].
pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)) as D1. pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D1'.
destruct (zb_fresh (Z.lxor (u1 / 2 ^ 47) u1)) as [u2 [R2 E2]].
destruct (zb_fresh (u2 * mC)) as [u3 [R3 E3]].
destruct (zb_fresh (Z.lxor u3 hN)) as [u4 [R4 E4]].
destruct (zb_fresh (u4 * mC)) as [u5 [R5 E5]].
pose proof (Z.div_pos u5 (2 ^ 47) ltac:(lia) ltac:(lia)) as D5. pose proof (Z.div_lt_upper_bound u5 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D5'.
destruct (zb_fresh (Z.lxor (u5 / 2 ^ 47) u5)) as [u6 [R6 E6]].
destruct (zb_fresh (u6 * mC)) as [u7 [R7 E7]].
pose proof (Z.div_pos u7 (2 ^ 47) ltac:(lia) ltac:(lia)) as D7. pose proof (Z.div_lt_upper_bound u7 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D7'.
destruct (zb_fresh (Z.lxor (u7 / 2 ^ 47) u7)) as [h [Rh Eh]].
set (b := h mod 2 ^ 20). pose proof (Z.mod_pos_bound h (2 ^ 20) ltac:(lia)) as Rb.
destruct (BK b ltac:(lia)) as (v & Cv & Rv).
unfold DEP, MAP1 in *.
eexists _, h, b, v. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]].
- stepn (ltac:(oF' 0x99a10%Z)) (ltac:(oD' 0x99a10%Z)).
stepn (ltac:(oF' 0x99a14%Z)) (ltac:(oD' 0x99a14%Z)).
zstep (ltac:(oF' 0x99a18%Z)) (ltac:(oD' 0x99a18%Z)). rewrite E1.
stepn (ltac:(oF' 0x99a1c%Z)) (ltac:(oD' 0x99a1c%Z)).
stepn (ltac:(oF' 0x99a20%Z)) (ltac:(oD' 0x99a20%Z)).
stepn (ltac:(oF' 0x99a24%Z)) (ltac:(oD' 0x99a24%Z)).
stepn (ltac:(oF' 0x99a28%Z)) (ltac:(oD' 0x99a28%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x99a2c%Z)) (ltac:(oD' 0x99a2c%Z)). rwH. rewrite art_zb_xor by lia. rewrite E2.
zstep (ltac:(oF' 0x99a30%Z)) (ltac:(oD' 0x99a30%Z)). rewrite E3.
stepn (ltac:(oF' 0x99a34%Z)) (ltac:(oD' 0x99a34%Z)). rwH. rewrite art_zb_xor by lia. rewrite E4.
zstep (ltac:(oF' 0x99a38%Z)) (ltac:(oD' 0x99a38%Z)). rewrite E5.
stepn (ltac:(oF' 0x99a3c%Z)) (ltac:(oD' 0x99a3c%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x99a40%Z)) (ltac:(oD' 0x99a40%Z)). rwH. rewrite art_zb_xor by lia. rewrite E6.
zstep (ltac:(oF' 0x99a44%Z)) (ltac:(oD' 0x99a44%Z)). rewrite E7.
stepn (ltac:(oF' 0x99a48%Z)) (ltac:(oD' 0x99a48%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x99a4c%Z)) (ltac:(oD' 0x99a4c%Z)). rwH. rewrite art_zb_xor by lia. rewrite Eh.
zstep (ltac:(oF' 0x99a50%Z)) (ltac:(oD' 0x99a50%Z)).
replace (Z_to_bv 64 (h * 2 ^ 44) : word) with (Z_to_bv 64 (b * 2 ^ 44) : word)
by (apply art_zb_eq; rewrite (mod_mul_pow44 h) by lia; subst b; rewrite Z.mod_small; [reflexivity | nia]).
stepn (ltac:(oF' 0x99a54%Z)) (ltac:(oD' 0x99a54%Z)). rwH. rewrite (art_zb_srli_exact (b * 2 ^ 44) 42 (4 * b)) by lia.
zstep (ltac:(oF' 0x99a58%Z)) (ltac:(oD' 0x99a58%Z)).
zlw (ltac:(oF' 0x99a5c%Z)) (ltac:(oD' 0x99a5c%Z)) (2222360 + 4 * b) Cv.
stepn (ltac:(oF' 0x99a60%Z)) (ltac:(oD' 0x99a60%Z)).
zstep (ltac:(oF' 0x99a64%Z)) (ltac:(oD' 0x99a64%Z)).
stepfence (ltac:(oF' 0x99a68%Z)) (ltac:(oD' 0x99a68%Z)).
stepn (ltac:(oF' 0x99a6c%Z)) (ltac:(oD' 0x99a6c%Z)). rwH.
match goal with |- context [v_and (Z_to_bv 64 v) ?L] =>
replace (v_and (Z_to_bv 64 v) L) with (Z_to_bv 64 v : word)
by (symmetry; replace L with (Z_to_bv 64 (Z.ones 31) : word) by (apply bv_eq; vm_compute; reflexivity);
rewrite art_zb_and by (change (Z.ones 31) with 2147483647; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
stepn (ltac:(oF' 0x99a70%Z)) (ltac:(oD' 0x99a70%Z)).
zstep (ltac:(oF' 0x99a74%Z)) (ltac:(oD' 0x99a74%Z)).
zstep (ltac:(oF' 0x99a78%Z)) (ltac:(oD' 0x99a78%Z)).
apply mst_refl.
- exact Rh.
- lia.
- exact Cv.
- exact Rv.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- intros r N10 N11 N12 N13 N14 NA NB.
destruct (decide (r = 18%bv)) as [->|N18]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 19%bv)) as [->|N19]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 20%bv)) as [->|N20]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 22%bv)) as [->|N22]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
destruct (decide (r = 23%bv)) as [->|N23]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
destruct (decide (r = 24%bv)) as [->|N24]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
destruct (decide (r = 25%bv)) as [->|N25]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
kept_solve.
Qed.
End SE.
Section SE.
Variables (regs0 regs : bvmap 5 word).
Variables (X rom : word -> option byte).
Variables (raw : word).
Variables (s : Z).
Lemma dp_epi_run : getr regs 2 = Z_to_bv 64 (s - 112) -> ret_ok raw -> 4096 <= s - 112 -> s < 2 ^ 64 ->
cellA X (s - 8) 8 (U raw) -> cellA X (s - 16) 8 (U (getr regs0 8)) -> cellA X (s - 24) 8 (U (getr regs0 9)) ->
cellA X (s - 32) 8 (U (getr regs0 18)) -> cellA X (s - 40) 8 (U (getr regs0 19)) -> cellA X (s - 48) 8 (U (getr regs0 20)) ->
cellA X (s - 56) 8 (U (getr regs0 21)) -> cellA X (s - 64) 8 (U (getr regs0 22)) -> cellA X (s - 72) 8 (U (getr regs0 23)) ->
cellA X (s - 80) 8 (U (getr regs0 24)) -> cellA X (s - 88) 8 (U (getr regs0 25)) ->
exists regs',
msteps ASEGS (mkst regs (0x99b80 : word) X rom) (mkst regs' raw X rom)
/\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = raw
/\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18 /\ getr regs' 19 = getr regs0 19
/\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21 /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23
/\ getr regs' 24 = getr regs0 24 /\ getr regs' 25 = getr regs0 25
/\ (forall r : reg, r <> 1%bv -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> ~ (18 <= U r <= 25) -> getr regs' r = getr regs r).
Proof using Type regs0 regs X rom raw s.
intros H2 Hret Hs Hs' L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11.
eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]].
- zld (ltac:(oF' 0x99b80%Z)) (ltac:(oD' 0x99b80%Z)) (s - 8) L1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99b84%Z)) (ltac:(oD' 0x99b84%Z)) (s - 16) L2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99b88%Z)) (ltac:(oD' 0x99b88%Z)) (s - 24) L3. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99b8c%Z)) (ltac:(oD' 0x99b8c%Z)) (s - 32) L4. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99b90%Z)) (ltac:(oD' 0x99b90%Z)) (s - 40) L5. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99b94%Z)) (ltac:(oD' 0x99b94%Z)) (s - 48) L6. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99b98%Z)) (ltac:(oD' 0x99b98%Z)) (s - 56) L7. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99b9c%Z)) (ltac:(oD' 0x99b9c%Z)) (s - 64) L8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99ba0%Z)) (ltac:(oD' 0x99ba0%Z)) (s - 72) L9. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99ba4%Z)) (ltac:(oD' 0x99ba4%Z)) (s - 80) L10. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x99ba8%Z)) (ltac:(oD' 0x99ba8%Z)) (s - 88) L11. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x99bac%Z)) (ltac:(oD' 0x99bac%Z)).
stepret (ltac:(oF' 0x99bb0%Z)) (ltac:(oD' 0x99bb0%Z)) raw ltac:(rwH; reflexivity).
replace (s - 112 + 112) with s by lia. apply mst_refl.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- kept_solve.
- intros r N1 N2 N8 N9 NA.
destruct (decide (r = 18%bv)) as [->|N18]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 19%bv)) as [->|N19]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 20%bv)) as [->|N20]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 21%bv)) as [->|N21]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 22%bv)) as [->|N22]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 23%bv)) as [->|N23]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 24%bv)) as [->|N24]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
destruct (decide (r = 25%bv)) as [->|N25]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
kept_solve.
Qed.
End SE.
End FPX.
