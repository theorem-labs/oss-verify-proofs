(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Jb0MemIsZero Jb0RegionPoisoned Jb0AsanMemset.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagWritev () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagWritev.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagWritev.FPX_1.WVE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4Segment"]; ["5MachineOk"; "5fetch_word"; "5is_ecall"; "5machine_result"; "5machine_state"; "5step"; "5store_ok"; "5word_to_le_bytes"; "6decode_any"; "7ALU_SUB"; "7Op32"; "7instr"; "8bv_eqb"; "8bvmap"; "0M"; "9msteps"]; [":ret_ok"; ";W64"; "<wve_cnt"; "<wve_iov"; "<wve_mem"; "=keeps_but"; ">getr"; ">mkst"; ">rdn"; ">regupd"; ">v_addi"; ">v_lw"; ">v_subw"; "?keeps_cs"; "@loaded_segments"; "Aadd"]; ["Ale"; "Alt"; "Alxor"; "Apow"; "Asub"; "0a"; "0b"; "0b1"; "0b2"; "0buf"; "0c"; "0f"; "0fd"; "0fx"; "0k"; "0l1"]; ["0l2"; "0len"; "0mem"; "0pc"; "0q"; "0rd"; "0regs"; "0regs'"; "0rem"; "0ret"; "0rom"; "0rs1"; "0rs2"; "0segs"; "0sp"; "BBV"]; ["BZ_to_bv"; "Bbv"; "0v"; "0w"; "0wbase"; "0wpos"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub; imm_norm; unorm; first [reflexivity | f_equal; lia].
Lemma ret_ok_11d144 : ltac2:(TCodec.tc2 tcn__Jb0DiagWritev ":&Q0(R?yR0+QSdZ4(:%43321'RA%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ret_ok_11d1cc : ltac2:(TCodec.tc2 tcn__Jb0DiagWritev ":&Q0(R?yR0+QSd^<(:%43321'RA%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma syscall_ret_ok : ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "R>&My5'RAyR0%211%5241'6y8%611%311p061'>'<&Q6r5(R?+1(:%33A21%6251r2%93A21&Q0r3%211r7+:%<3J1:%?231&R@%12K7%C3K31';&Q@zr4%3221&QA&QC+2+QO%3221%5271%;271'='O&Q>&Q7vQMr:+QRfeD%Q43Q@1Q2/01Q@r9r8%8576321r1%:591Q043%=3<31%Q>23Q0r6%Q02QJ1%QB3QJ31&Q=%12?8%Q1231%Q2281qT@QN1%H2QO1p0J1p0Q71p0Q?1p0QC1pSNQN1pTDR61pTFR11pQNR21pT>R81").
Proof.
intros regs M rom ret k H1 Hret H10 Hk.
eexists. split.
- stepn (ltac:(oF' 0x115ab4%Z)) (ltac:(oD' 0x115ab4%Z)).
stepiv (ltac:(oF' 0x115ab8%Z)) (ltac:(oD' 0x115ab8%Z)) (Z_to_bv 64 (2 ^ 64 - 4095)) ltac:(gres; apply bv_eq; vm_compute; reflexivity).
stepb_tk (ltac:(oF' 0x115abc%Z)) (ltac:(oD' 0x115abc%Z)) ltac:(cond).
stepret (ltac:(oF' 0x115ae8%Z)) (ltac:(oD' 0x115ae8%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; rwH; reflexivity | solve_keeps_cs].
Qed.
Lemma step_subw_at' : ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "S4'4'?%211&My5'RAyR0%211%5241'6y8%611%311p061yQ0%:11%;1<'<%913&Ar:r8%3221(0r5%22:1%93841'1&Br6%211(3%?3521'8'K'>%3221%L11&Hr7%211(7(J(Ir4%342@E1+4%64=<21%I2<1%Q03<91&L(R?z(:%33QB21%53QC@1%Q73M1I&Q<&Q6r=%221E%322Q0%5221%Q>3QH1Q7'C'D%211&Er?&Q7vQMr>r<r;%5543?21%8271(@&Q9r9%2381QB&Q:%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pU6RC1pTJR;1pTHR<1pT<R=1pU8R?1pTFRB1pT6RC1pT8RJ1pT>RJ1pTLS11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma v_lw_small' : ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "I'>';&Q@zr1%3221&QA&QC+2+O%3221%5271%;271'<'RAyR0%211&Q;&R@r2%2251%411%93612p0;1pU>H1").
Proof.
intros z Hz. unfold v_lw. rewrite u_Z2bv by lia. f_equal. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma v_subw_small : ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "Q2'>';&Q@zr1%3221r2%5231%7231&QAr3&QC+2+O%3221%6251'<'RAyR0%211&Q<&R@r4%2251%326>%5221&QD%125A%72:1%=3:41p0?1p0G1pS>Q01pS<Q11").
Proof.
intros a b H1 H2. unfold v_subw. rewrite !u_Z2bv by lia. f_equal. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma lxor_bound64 : ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "H'>';&Q@zr2%3221&QA&QC+2+R0%3221%5271%;271&QBr4r3%3221%?2>1%<228%B221p081p091pS>F1pS<G1").
Proof.
intros a b Ha Hb. assert (Hnn : (0 <= Z.lxor a b)%Z) by (apply Z.lxor_nonneg; lia). split; [exact Hnn|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [E|NE]; [lia|].
apply Z.log2_lt_pow2; [lia|]. pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as L.
assert (Z.log2 a < 64)%Z by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
assert (Z.log2 b < 64)%Z by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]). lia.
Qed.
Definition W64 (M : word -> option byte) (a v : Z) : word -> option byte := wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v)).
Section WV.
Variable M rom : word -> option byte.
Variables f q c rem k : Z.
Hypothesis Hk : (0 <= k < 2 ^ 63)%Z.
Hypothesis Hrem : (0 <= rem < 2 ^ 63)%Z.
Hypothesis Hq : (0 <= q)%Z /\ (q + 32 < 2 ^ 63)%Z.
Lemma wv_ret_A : forall regs,
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
exists regs',
msteps ASEGS (mkst regs (0x11d140 : word) M rom) (mkst regs' (if Z.eqb k rem then (0x11d148 : word) else (0x11d1d4 : word)) M rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ keeps_but [1]%bv regs regs'.
Proof.
intros regs H10 H22.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x11d140 : word) M rom) (mkst r1 (0x115ab4 : word) M rom)
/\ getr r1 1 = (0x11d144 : word) /\ getr r1 10 = Z_to_bv 64 k /\ getr r1 22 = Z_to_bv 64 rem /\ keeps_but [1]%bv regs r1).
{ eexists. split; [stepn (ltac:(oF' 0x11d140%Z)) (ltac:(oD' 0x11d140%Z)); apply mst_refl|].
repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & R1 & R10 & R22 & K1).
destruct (syscall_ret_ok r1 M rom (0x11d144 : word) k R1 ret_ok_11d144 R10 Hk) as (r2 & RUN2 & V10 & K2).
assert (V22 : getr r2 22 = Z_to_bv 64 rem) by (rewrite (K2 22%bv) by (cbv; tauto); exact R22).
destruct (Z.eqb_spec k rem) as [E|NE].
- eexists. split; [|split].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepb_ft (ltac:(oF' 0x11d144%Z)) (ltac:(oD' 0x11d144%Z)) ltac:(cond).
apply mst_refl.
+ exact V10.
+ eapply keeps_but_trans; [exact K1 | apply keeps_but_cs; exact K2].
- eexists. split; [|split].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepb_tk (ltac:(oF' 0x11d144%Z)) (ltac:(oD' 0x11d144%Z)) ltac:(cond).
apply mst_refl.
+ exact V10.
+ eapply keeps_but_trans; [exact K1 | apply keeps_but_cs; exact K2].
Qed.
Lemma wv_ret_B : forall regs,
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem -> getr regs 20 = Z_to_bv 64 q ->
exists regs',
msteps ASEGS (mkst regs (0x11d1c8 : word) M rom) (mkst regs' (if Z.eqb k rem then (0x11d148 : word) else (0x11d1d4 : word)) M rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = Z_to_bv 64 q /\ keeps_but [1; 19]%bv regs regs'.
Proof.
intros regs H10 H22 H20.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x11d1c8 : word) M rom) (mkst r1 (0x115ab4 : word) M rom)
/\ getr r1 1 = (0x11d1cc : word) /\ getr r1 10 = Z_to_bv 64 k /\ getr r1 22 = Z_to_bv 64 rem /\ getr r1 20 = Z_to_bv 64 q /\ keeps_but [1; 19]%bv regs r1).
{ eexists. split; [stepn (ltac:(oF' 0x11d1c8%Z)) (ltac:(oD' 0x11d1c8%Z)); apply mst_refl|].
repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & R1 & R10 & R22 & R20 & K1).
destruct (syscall_ret_ok r1 M rom (0x11d1cc : word) k R1 ret_ok_11d1cc R10 Hk) as (r2 & RUN2 & V10 & K2).
assert (V22 : getr r2 22 = Z_to_bv 64 rem) by (rewrite (K2 22%bv) by (cbv; tauto); exact R22).
assert (V20 : getr r2 20 = Z_to_bv 64 q) by (rewrite (K2 20%bv) by (cbv; tauto); exact R20).
destruct (Z.eqb_spec k rem) as [E|NE].
- eexists. split; [|split; [|split]].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x11d1cc%Z)) (ltac:(oD' 0x11d1cc%Z)) (Z_to_bv 64 q) ltac:(wval).
stepb_tk (ltac:(oF' 0x11d1d0%Z)) (ltac:(oD' 0x11d1d0%Z)) ltac:(cond).
apply mst_refl.
+ gres; rwH; reflexivity.
+ gres; reflexivity.
+ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
- eexists. split; [|split; [|split]].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x11d1cc%Z)) (ltac:(oD' 0x11d1cc%Z)) (Z_to_bv 64 q) ltac:(wval).
stepb_ft (ltac:(oF' 0x11d1d0%Z)) (ltac:(oD' 0x11d1d0%Z)) ltac:(cond).
apply mst_refl.
+ gres; rwH; reflexivity.
+ gres; reflexivity.
+ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
Qed.
Variables b1 l1 fd : Z.
Hypothesis Hf : (0 <= f)%Z /\ (f + 124 <= q \/ q + 32 <= f + 120)%Z /\ (f + 124 < 2 ^ 63)%Z.
Hypothesis Hfd : (0 <= fd < 2 ^ 31)%Z.
Hypothesis HFD : rdn ASEGS M (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
Hypothesis Hc : (1 <= c <= 2)%Z.
Hypothesis Hk0 : (0 < k)%Z.
#[local] Ltac slt_ft := rwH; unfold c_lts, bv_lts; rewrite !signed64_small by lia; first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.leb_le | apply Z.leb_gt]; lia.
#[local] Ltac rdw a := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 a) by (symmetry; wval) end.
#[local] Ltac peel := rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
Section SE.
Local Abbreviation SEC_T_wv_body_lo := (ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "UB&My5'RAyR0%211%5241';&Q@vQNvQO%3221&QA&QC+2+QO%3221%5271%;271zvQG%=221&Q?%123>+R0%<2;1%>231'<'6'4y8%L11%311%511&Q8&Q>vN&R@vR4%22Q31u8%746521(0&G%72Q8H%2251%42>1%D3>61+8%K2;1%=2Q>1%A4@?1;%?2Q@Q:%:2=1%<2F1%L3F41'1&Fu@%24HGD1(9%Q23521&Q6r7(R?+:(:%33R121%6251%Q02R1QL%Q;3R121r8+C%93R717%<231%Q@3R61Q4r9+B%>3R<1<%A231vQJ%Q<2R=1%QG3R=31r:+F%E3RC1C%H231vR8%QC2RD1%QN3RD31r;+9%L3RJ1J%O231vQK%QJ2RK1%R53RK31%RI2RH:'='O&Q7vQMr>+QSd^D%Q83S41Q6/01S4vR:%75652R71r1+QSd^4%Q>3S:1Q</01S:&Q1%13R=R;RJ&QD%12S9S:%433R31%A5@961;%C3RC;1+A%QH3SF1QF%QK2=1+R2%RF2SG1%S13SG31%QO2AQJvQL%RJ2SK1%S53SK31+;%R23T01R0%R52G1%S93SO1RM+<%R63T41R4%R92K1%S=3T31QG+D%R:3T81R8%R=2O1%SA3T71S5%R?2Q1QO%SC3T91QM%RA2Q3QJ%N2QIT7%S<2T=1%SG3T=31&Q5(2%TB1TC(5%112%433R31%534?1%635R<1%831QEQ?%TE2:1%TF2?1%TG2B1%TH2G1%TI2L1%TJ2Q11%TK2Q61%TL2Q=1qT@TN1%R32TO1p0R51p0R71p0R?1p0RG1p0RO1p0S51p0S?1p0SF1p0SO1p0TE1p0TK1p0TO1pT>U<1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_wv_body_lo) 0%nat 0%nat).
Lemma wv_body_lo : ltac:(sec_stmt2 constr:(SEC_T_wv_body_lo) 1%nat 0%nat).
Proof.
intros Hl1 Hb1 Hb1k R0 R8 SOK H10 H19 H18 H22 H9 Hkr.
destruct Hq as (Hq0 & Hq1). destruct Hf as (Hf0 & Hfq & Hf1).
assert (SOK0 : store_ok ASEGS M (Z_to_bv 64 q) 8%nat = true).
{ apply (store_ok_sub ASEGS M (Z_to_bv 64 q) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
assert (SOK8 : store_ok ASEGS (W64 M q (b1 + k)) (Z_to_bv 64 (q + 8)) 8%nat = true).
{ unfold W64. apply (store_ok_mono _ _ M); [apply wbytes_grows|].
apply (store_ok_sub ASEGS M (Z_to_bv 64 q) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
assert (R8' : rdn ASEGS (W64 M q (b1 + k)) (Z_to_bv 64 (q + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 l1))).
{ unfold W64. peel. exact R8. }
assert (HFD' : rdn ASEGS (W64 M q (b1 + k)) (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))).
{ unfold W64. peel. exact HFD. }
eexists. split.
- stepb_ft (ltac:(oF' 0x11d1d4%Z)) (ltac:(oD' 0x11d1d4%Z)) ltac:(slt_ft).
stepld (ltac:(oF' 0x11d1d8%Z)) (ltac:(oD' 0x11d1d8%Z)) (Z_to_bv 64 l1) ltac:(rdw (q + 8)%Z; exact R8).
stepov (ltac:(oF' 0x11d1dc%Z)) (ltac:(oD' 0x11d1dc%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (l1 <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepiv (ltac:(oF' 0x11d1e0%Z)) (ltac:(oD' 0x11d1e0%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
stepiv (ltac:(oF' 0x11d1e4%Z)) (ltac:(oD' 0x11d1e4%Z)) (Z_to_bv 64 q) ltac:(wval).
stepld (ltac:(oF' 0x11d1e8%Z)) (ltac:(oD' 0x11d1e8%Z)) (Z_to_bv 64 b1) ltac:(rdw q; exact R0).
stepiv (ltac:(oF' 0x11d1ec%Z)) (ltac:(oD' 0x11d1ec%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
stepov (ltac:(oF' 0x11d1f0%Z)) (ltac:(oD' 0x11d1f0%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_and; unorm; rewrite Z.land_0_l; reflexivity).
stepiv (ltac:(oF' 0x11d1f4%Z)) (ltac:(oD' 0x11d1f4%Z)) (Z_to_bv 64 k) ltac:(wval).
stepiv (ltac:(oF' 0x11d1f8%Z)) (ltac:(oD' 0x11d1f8%Z)) (Z_to_bv 64 (b1 + k)) ltac:(wval).
stepsd (ltac:(oF' 0x11d1fc%Z)) (ltac:(oD' 0x11d1fc%Z)) (Z_to_bv 64 q) (Z_to_bv 64 (b1 + k)) ltac:(exact SOK0).
stepb_tk (ltac:(oF' 0x11d200%Z)) (ltac:(oD' 0x11d200%Z)) ltac:(cond).
stepn (ltac:(oF' 0x11d198%Z)) (ltac:(oD' 0x11d198%Z)).
stepiv (ltac:(oF' 0x11d19c%Z)) (ltac:(oD' 0x11d19c%Z)) (Z_to_bv 64 q) ltac:(wval).
stepiv (ltac:(oF' 0x11d1a0%Z)) (ltac:(oD' 0x11d1a0%Z)) (Z_to_bv 64 (q + 8)) ltac:(wval).
stepld (ltac:(oF' 0x11d1a4%Z)) (ltac:(oD' 0x11d1a4%Z)) (Z_to_bv 64 l1) ltac:(rdw (q + 8)%Z; exact R8').
stepiv (ltac:(oF' 0x11d1a8%Z)) (ltac:(oD' 0x11d1a8%Z)) (Z_to_bv 64 (rem - k)) ltac:(wval).
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
[exact (ltac:(oF' 0x11d1ac%Z)) | reflexivity | exact (ltac:(oD' 0x11d1ac%Z)) | rdw (f + 120)%Z; exact HFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].
chain_step; [reflexivity | eapply step_subw_at' with (v := Z_to_bv 64 c); [exact (ltac:(oF' 0x11d1b0%Z)) | reflexivity | exact (ltac:(oD' 0x11d1b0%Z)) | reflexivity
| gres; rwH; rewrite v_subw_small by lia; f_equal; lia] | step_simpl].
stepiv (ltac:(oF' 0x11d1b4%Z)) (ltac:(oD' 0x11d1b4%Z)) (Z_to_bv 64 (l1 - k)) ltac:(wval).
stepsd (ltac:(oF' 0x11d1b8%Z)) (ltac:(oD' 0x11d1b8%Z)) (Z_to_bv 64 (q + 8)) (Z_to_bv 64 (l1 - k)) ltac:(exact SOK8).
stepn (ltac:(oF' 0x11d1bc%Z)) (ltac:(oD' 0x11d1bc%Z)).
stepiv (ltac:(oF' 0x11d1c0%Z)) (ltac:(oD' 0x11d1c0%Z)) (Z_to_bv 64 c) ltac:(wval).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
Qed.
End SE.
Variables b2 l2 : Z.
Section SE.
Local Abbreviation SEC_T_wv_body_hi := (ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "V9&My5'RAyR0%211%5241'<'>vQJ+2%43321';&Q@zvQO%3221&QAvQN%2241%8241&QD%1247vR0%;221&QC+QO%22A1%;251%A251vQH%B2A1&Q?%123;+R0%:2I1%C231'6'4y8%Q511%311%511&Q8&Q>vN&R@vR4+8%A221%42Q>1u8%948721(0&G%92QCQ8%2251%42@1%QC3@61+@%L2=1%?2QI1%C4BA1;%A2QKQ1%:2=1%<2H1%QK3H41+H%Q42E1%G2R11%K4JI1C%I2R3Q@%B2E1%D2Q01%R33Q041'1&Fu@%24Q2Q1A1(9%R93521&Q6r:(R?+:(:%33RD21%6251%Q:2RDR6%RB3RD21r;+C%93RJ17%<231%Q@2RJQ?%RH3RJ21r<+B%?3S01=%B231%QF2S0RK%RN3S021r=+F%E3S61C%H231vR8%QM2S71%S53S731r>+9%L3S=1J%O231vQK%R42S>1%S<3S>31%S72S2:'='O&Q7vQMrA+QSd^D%Q83SG1Q6/01SGvR:%75652RA1r1+QSd^4%Q>3SM1Q</01SM&Q1%13RGR8S3%S@2S>S?%332R21%@5?851:%B3RL:1+A%QG3T81QE%QJ2<1+R2%RO2T91%T73T931%QN2@QIvQL%S32T=1%T;3T=31+;%R13TB1QO%R42F1%T?3TA1RI+<%R53TF1R3%R82J1+1%S=2TG1%TE3TG31+D%R;3TL1R9%R>2Q01%TI3TK1S3%R@2Q2QO%TK3TM17%RB2Q4QK%T?2QJTB%SG2U11%TO3U131&Q5(2%U61U7(5%112%433R41%534?1%635R<1%831QFQ@%U42:1%U52?1%U62B1%U72G1%U82N1%U92Q31%U:2Q81%U;2Q?1qT@UB1%R42UC1p0R61p0R81p0R@1p0RH1p0RO1p0S61p0S@1p0SG1p0T01p0T91p0U01p0U61p0U91p0UC1p0UM1pT>V31")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_wv_body_hi) 0%nat 0%nat).
Lemma wv_body_hi : ltac:(sec_stmt2 constr:(SEC_T_wv_body_hi) 1%nat 0%nat).
Proof.
intros Hc2 Hl1 Hl2 Hb2 Hb2k R8 R16 R24 SOK H10 H19 H18 H22 H9 Hkr.
destruct Hq as (Hq0 & Hq1). destruct Hf as (Hf0 & Hfq & Hf1).
assert (SOK0 : store_ok ASEGS M (Z_to_bv 64 (q + 16)) 8%nat = true).
{ apply (store_ok_sub ASEGS M (Z_to_bv 64 (q + 16)) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
assert (SOK8 : store_ok ASEGS (W64 M (q + 16) (b2 + (k - l1))) (Z_to_bv 64 (q + 24)) 8%nat = true).
{ unfold W64. apply (store_ok_mono _ _ M); [apply wbytes_grows|].
apply (store_ok_sub ASEGS M (Z_to_bv 64 (q + 16)) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
assert (R24' : rdn ASEGS (W64 M (q + 16) (b2 + (k - l1))) (Z_to_bv 64 (q + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 l2))).
{ unfold W64. peel. exact R24. }
assert (HFD' : rdn ASEGS (W64 M (q + 16) (b2 + (k - l1))) (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))).
{ unfold W64. peel. exact HFD. }
eexists. split.
- stepb_ft (ltac:(oF' 0x11d1d4%Z)) (ltac:(oD' 0x11d1d4%Z)) ltac:(slt_ft).
stepld (ltac:(oF' 0x11d1d8%Z)) (ltac:(oD' 0x11d1d8%Z)) (Z_to_bv 64 l1) ltac:(rdw (q + 8)%Z; exact R8).
stepov (ltac:(oF' 0x11d1dc%Z)) (ltac:(oD' 0x11d1dc%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (l1 <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepiv (ltac:(oF' 0x11d1e0%Z)) (ltac:(oD' 0x11d1e0%Z)) (Z_to_bv 64 16) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
stepiv (ltac:(oF' 0x11d1e4%Z)) (ltac:(oD' 0x11d1e4%Z)) (Z_to_bv 64 (q + 16)) ltac:(wval).
stepld (ltac:(oF' 0x11d1e8%Z)) (ltac:(oD' 0x11d1e8%Z)) (Z_to_bv 64 b2) ltac:(rdw (q + 16)%Z; exact R16).
stepiv (ltac:(oF' 0x11d1ec%Z)) (ltac:(oD' 0x11d1ec%Z)) (Z_to_bv 64 (2 ^ 64 - 1)) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
stepov (ltac:(oF' 0x11d1f0%Z)) (ltac:(oD' 0x11d1f0%Z)) (Z_to_bv 64 l1) ltac:(gres; rwH; unfold v_and; unorm; change (2 ^ 64 - 1)%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
stepiv (ltac:(oF' 0x11d1f4%Z)) (ltac:(oD' 0x11d1f4%Z)) (Z_to_bv 64 (k - l1)) ltac:(wval).
stepiv (ltac:(oF' 0x11d1f8%Z)) (ltac:(oD' 0x11d1f8%Z)) (Z_to_bv 64 (b2 + (k - l1))) ltac:(wval).
stepsd (ltac:(oF' 0x11d1fc%Z)) (ltac:(oD' 0x11d1fc%Z)) (Z_to_bv 64 (q + 16)) (Z_to_bv 64 (b2 + (k - l1))) ltac:(exact SOK0).
stepb_ft (ltac:(oF' 0x11d200%Z)) (ltac:(oD' 0x11d200%Z)) ltac:(cond).
stepn (ltac:(oF' 0x11d204%Z)) (ltac:(oD' 0x11d204%Z)).
stepn (ltac:(oF' 0x11d208%Z)) (ltac:(oD' 0x11d208%Z)).
stepiv (ltac:(oF' 0x11d19c%Z)) (ltac:(oD' 0x11d19c%Z)) (Z_to_bv 64 (q + 16)) ltac:(wval).
stepiv (ltac:(oF' 0x11d1a0%Z)) (ltac:(oD' 0x11d1a0%Z)) (Z_to_bv 64 (q + 24)) ltac:(wval).
stepld (ltac:(oF' 0x11d1a4%Z)) (ltac:(oD' 0x11d1a4%Z)) (Z_to_bv 64 l2) ltac:(rdw (q + 24)%Z; exact R24').
stepiv (ltac:(oF' 0x11d1a8%Z)) (ltac:(oD' 0x11d1a8%Z)) (Z_to_bv 64 (rem - k)) ltac:(wval).
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
[exact (ltac:(oF' 0x11d1ac%Z)) | reflexivity | exact (ltac:(oD' 0x11d1ac%Z)) | rdw (f + 120)%Z; exact HFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].
chain_step; [reflexivity | eapply step_subw_at' with (v := Z_to_bv 64 1); [exact (ltac:(oF' 0x11d1b0%Z)) | reflexivity | exact (ltac:(oD' 0x11d1b0%Z)) | reflexivity
| gres; rwH; rewrite Hc2; rewrite v_subw_small by lia; reflexivity] | step_simpl].
stepiv (ltac:(oF' 0x11d1b4%Z)) (ltac:(oD' 0x11d1b4%Z)) (Z_to_bv 64 (l2 - (k - l1))) ltac:(wval).
stepsd (ltac:(oF' 0x11d1b8%Z)) (ltac:(oD' 0x11d1b8%Z)) (Z_to_bv 64 (q + 24)) (Z_to_bv 64 (l2 - (k - l1))) ltac:(exact SOK8).
stepn (ltac:(oF' 0x11d1bc%Z)) (ltac:(oD' 0x11d1bc%Z)).
stepiv (ltac:(oF' 0x11d1c0%Z)) (ltac:(oD' 0x11d1c0%Z)) (Z_to_bv 64 1) ltac:(wval).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
Qed.
End SE.
End WV.
Section WVE.
Variable M rom : word -> option byte.
Variables f sp buf len wpos wbase fd : Z.
Hypothesis Hsp : (0 <= sp)%Z /\ (sp + 40 < 2 ^ 63)%Z.
Hypothesis Hf : (0 <= f)%Z /\ (f + 124 <= sp + 8 \/ sp + 40 <= f)%Z /\ (f + 124 < 2 ^ 63)%Z.
Hypothesis Hw : (0 <= wbase <= wpos)%Z /\ (wpos < 2 ^ 63)%Z.
Hypothesis Hlen : (0 <= len < 2 ^ 62)%Z.
Hypothesis Hbuf : (0 <= buf < 2 ^ 64)%Z.
Hypothesis Hfd : (0 <= fd < 2 ^ 31)%Z.
Hypothesis RWP : rdn ASEGS M (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wpos)).
Hypothesis RWB : rdn ASEGS M (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wbase)).
Hypothesis RFD : rdn ASEGS M (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
Hypothesis SOK : store_ok ASEGS M (Z_to_bv 64 (sp + 8)) 32%nat = true.
Definition wve_mem : word -> option byte := W64 (W64 (W64 (W64 M (sp + 8) wbase) (sp + 16) (wpos - wbase)) (sp + 24) buf) (sp + 32) len.
Definition wve_iov : Z := if Z.eqb wpos wbase then (sp + 24)%Z else (sp + 8)%Z.
Definition wve_cnt : Z := if Z.eqb wpos wbase then 1%Z else 2%Z.
#[local] Ltac rdw a := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 a) by (symmetry; wval) end.
#[local] Ltac peel := rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
#[local] Ltac mysd F D aa vv oktac :=
chain_step; [reflexivity | eapply step_sd_at with (a := aa) (v := vv);
[exact F | reflexivity | exact D | wval | (gres; rwH; reflexivity) | oktac] | step_simpl].
#[local] Ltac grows := first [apply mem_grows_refl | (eapply mem_grows_trans; [ | apply wbytes_grows ]; grows)].
#[local] Ltac sok := apply (store_ok_mono _ _ M); [grows|];
apply (store_ok_sub ASEGS M (Z_to_bv 64 (sp + 8)) _ 32%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia].
Section SE.
Local Abbreviation SEC_T_wv_entry := (ltac2:(TCodec.tc2 tcn__Jb0DiagWritev "SK&My5'RAyR0%211%5241'<&Q6r1(R?+9(:%33;21%6251&R@vQK%22=1%;3=41r2+2%;3C19%>231vR>%92D1%B3D31r3+;%B3J1@%E231vQI%@2K1%I3K31r4+8%I3Q11G%L231vR1%G2Q21%Q03Q231'=';'O&Q>&Q7vQMr6+QSdW@%Q63Q<1Q4/01Q<vNvR:%8576321+QSdYL%Q<3QB1Q:/01QB&Q4%=5<Q@216%@3?61+A%QB3QJ1Q@%QE2QD1+R2%Q@2QK1%QI3QK31+:%QH3R01QF%QK2QJ1vQL%QF2R11%QO3R131%QO2QNQ;&Q3%QJ2R51%R33R531+<%R23R:1R0%R52R41&Q2%R02R;1%R93R;31+B%R83R@1R6%R;2R:1%R=3R?15+C%R<3RD1R:%R?2R>1%RA3RC1?+F%R@3RH1R>%RC2RB1&Q?&QDvREvRD%3221%521QL%RC2RN1%RL3RN81&Q5(2%S31S4(5%112%433?1%534D1%635I1%831QNS3%R42:1%R52F1%R62K1%R72Q01%R82Q71%R92Q<1%R:2QC1%R;2QJ1qT@S?1%R>2S@1p0R@1p0RH1p0S01p0S81pT>SE1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_wv_entry) 0%nat 0%nat).
Lemma wv_entry : ltac:(sec_stmt2 constr:(SEC_T_wv_entry) 1%nat 0%nat).
Proof.
intros H9 H2 H11 H8.
destruct Hsp as (Hs0 & Hs1). destruct Hf as (Hf0 & Hfs & Hf1). destruct Hw as (Hw0 & Hw1).
assert (RFD' : rdn ASEGS wve_mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))).
{ unfold wve_mem, W64. peel. peel. peel. peel. exact RFD. }
pose proof (lxor_bound64 wpos wbase ltac:(lia) ltac:(lia)) as XB.
unfold wve_iov, wve_cnt. unfold wve_mem, W64 in *. destruct (Z.eqb_spec wpos wbase) as [E|NE].
- eexists. split.
+ stepld (ltac:(oF' 0x11d0f0%Z)) (ltac:(oD' 0x11d0f0%Z)) (Z_to_bv 64 wpos) ltac:(rdw (f + 40)%Z; exact RWP).
stepld (ltac:(oF' 0x11d0f4%Z)) (ltac:(oD' 0x11d0f4%Z)) (Z_to_bv 64 wbase) ltac:(rdw (f + 56)%Z; exact RWB).
stepiv (ltac:(oF' 0x11d0f8%Z)) (ltac:(oD' 0x11d0f8%Z)) (Z_to_bv 64 (wpos - wbase)) ltac:(wval).
stepn (ltac:(oF' 0x11d0fc%Z)) (ltac:(oD' 0x11d0fc%Z)).
mysd (ltac:(oF' 0x11d100%Z)) (ltac:(oD' 0x11d100%Z)) (Z_to_bv 64 (sp + 8)) (Z_to_bv 64 wbase) ltac:(sok).
mysd (ltac:(oF' 0x11d104%Z)) (ltac:(oD' 0x11d104%Z)) (Z_to_bv 64 (sp + 16)) (Z_to_bv 64 (wpos - wbase)) ltac:(sok).
mysd (ltac:(oF' 0x11d108%Z)) (ltac:(oD' 0x11d108%Z)) (Z_to_bv 64 (sp + 24)) (Z_to_bv 64 buf) ltac:(sok).
mysd (ltac:(oF' 0x11d10c%Z)) (ltac:(oD' 0x11d10c%Z)) (Z_to_bv 64 (sp + 32)) (Z_to_bv 64 len) ltac:(sok).
stepiv (ltac:(oF' 0x11d110%Z)) (ltac:(oD' 0x11d110%Z)) (Z_to_bv 64 (wpos - wbase + len)) ltac:(wval).
stepov (ltac:(oF' 0x11d114%Z)) (ltac:(oD' 0x11d114%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu, v_xor; rewrite E, Z.lxor_nilpotent; reflexivity).
stepb_tk (ltac:(oF' 0x11d118%Z)) (ltac:(oD' 0x11d118%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x11d124%Z)) (ltac:(oD' 0x11d124%Z)) (Z_to_bv 64 (sp + 24)) ltac:(wval).
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
[exact (ltac:(oF' 0x11d128%Z)) | reflexivity | exact (ltac:(oD' 0x11d128%Z)) | rdw (f + 120)%Z; exact RFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].
stepiv (ltac:(oF' 0x11d12c%Z)) (ltac:(oD' 0x11d12c%Z)) (Z_to_bv 64 1) ltac:(wval).
stepn (ltac:(oF' 0x11d130%Z)) (ltac:(oD' 0x11d130%Z)).
stepiv (ltac:(oF' 0x11d134%Z)) (ltac:(oD' 0x11d134%Z)) (Z_to_bv 64 (sp + 24)) ltac:(wval).
stepiv (ltac:(oF' 0x11d138%Z)) (ltac:(oD' 0x11d138%Z)) (Z_to_bv 64 1) ltac:(wval).
apply mst_refl.
+ repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
- eexists. split.
+ stepld (ltac:(oF' 0x11d0f0%Z)) (ltac:(oD' 0x11d0f0%Z)) (Z_to_bv 64 wpos) ltac:(rdw (f + 40)%Z; exact RWP).
stepld (ltac:(oF' 0x11d0f4%Z)) (ltac:(oD' 0x11d0f4%Z)) (Z_to_bv 64 wbase) ltac:(rdw (f + 56)%Z; exact RWB).
stepiv (ltac:(oF' 0x11d0f8%Z)) (ltac:(oD' 0x11d0f8%Z)) (Z_to_bv 64 (wpos - wbase)) ltac:(wval).
stepn (ltac:(oF' 0x11d0fc%Z)) (ltac:(oD' 0x11d0fc%Z)).
mysd (ltac:(oF' 0x11d100%Z)) (ltac:(oD' 0x11d100%Z)) (Z_to_bv 64 (sp + 8)) (Z_to_bv 64 wbase) ltac:(sok).
mysd (ltac:(oF' 0x11d104%Z)) (ltac:(oD' 0x11d104%Z)) (Z_to_bv 64 (sp + 16)) (Z_to_bv 64 (wpos - wbase)) ltac:(sok).
mysd (ltac:(oF' 0x11d108%Z)) (ltac:(oD' 0x11d108%Z)) (Z_to_bv 64 (sp + 24)) (Z_to_bv 64 buf) ltac:(sok).
mysd (ltac:(oF' 0x11d10c%Z)) (ltac:(oD' 0x11d10c%Z)) (Z_to_bv 64 (sp + 32)) (Z_to_bv 64 len) ltac:(sok).
stepiv (ltac:(oF' 0x11d110%Z)) (ltac:(oD' 0x11d110%Z)) (Z_to_bv 64 (wpos - wbase + len)) ltac:(wval).
stepov (ltac:(oF' 0x11d114%Z)) (ltac:(oD' 0x11d114%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu, v_xor; unorm;
assert (Z.lxor wpos wbase <> 0)%Z by (rewrite Z.lxor_eq_0_iff; exact NE);
replace (0 <? Z.lxor wpos wbase)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepb_ft (ltac:(oF' 0x11d118%Z)) (ltac:(oD' 0x11d118%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x11d11c%Z)) (ltac:(oD' 0x11d11c%Z)) (Z_to_bv 64 (sp + 8)) ltac:(wval).
stepn (ltac:(oF' 0x11d120%Z)) (ltac:(oD' 0x11d120%Z)).
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
[exact (ltac:(oF' 0x11d128%Z)) | reflexivity | exact (ltac:(oD' 0x11d128%Z)) | rdw (f + 120)%Z; exact RFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].
stepiv (ltac:(oF' 0x11d12c%Z)) (ltac:(oD' 0x11d12c%Z)) (Z_to_bv 64 2) ltac:(wval).
stepn (ltac:(oF' 0x11d130%Z)) (ltac:(oD' 0x11d130%Z)).
stepiv (ltac:(oF' 0x11d134%Z)) (ltac:(oD' 0x11d134%Z)) (Z_to_bv 64 (sp + 8)) ltac:(wval).
stepiv (ltac:(oF' 0x11d138%Z)) (ltac:(oD' 0x11d138%Z)) (Z_to_bv 64 2) ltac:(wval).
apply mst_refl.
+ repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
Qed.
End SE.
End WVE.
End FPX_1.
