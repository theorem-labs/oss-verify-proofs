(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
Scfg ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk AgentLib AgentNodes SpecConsts RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import MState ITree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Nodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_BrNodes () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"]; ["3Z"; "0K"; "4machine_state"; "4ms_gpr"; "5mkCfg"; "6MemCopy"; "6Model"; "6TASK_SIZE"; "6VmMaps"; "6alloc_top"; "6m_halted"; "6m_vm_lazy"; "6m_vmmaps"; "6map_contains"; "6map_has"; "6mkEffectU"]; ["6mkVmMapsFull"; "6page_round_up_Z"; "6page_size"; "6region_free"; "6two_pow_64"; "6vm_brk"; "6vm_init_sp"; "6vm_limit"; "6vm_maps"; "6vm_mmap_base"; "6vm_noaccess"; "6vm_reserved"; "6vm_start_brk"; "6with_vmmaps"; "7brk_grow_ok"; "8mprotect_budget_ok"]; ["9nret"; ":NBrk"; ":NMmap"; ":NMprotect"; ":NMunmap"; ":areg"; ":at_node"; ";grant_ok"; ";mmap_model"; ";munmap_model"; "<fixed_noaccess_model"; "<grant_ok_na"; "<mprotect_model"; "<noaccess_model"; "=TSet"; ">srealizes"]; ["?add"; "?le"; "?lt"; "?modulo"; "?pow"; "0a"; "0addr"; "0b"; "0d"; "0h"; "0len"; "0model"; "0ms"; "0n"; "0scfg"; "0segs"]; ["@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0z"]]).
Notation cjnode := OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes.node.
Notation cj_at_node := OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes.at_node.
Import OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes (NBrk, NMmap, NMunmap, NMprotect, areg).
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Lemma gpr_areg0 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "B'B'='RByR0%211&Cr1(1%3221&QE(R@y5+:(;%43321%6291%?3<81pTJA1"). Proof. reflexivity. Qed.
Lemma gpr_areg1 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "B'B'='RByR0%211&Cr1u1%3221&QE(R@y5+;(;%43321%6291%?3<81pTJA1"). Proof. reflexivity. Qed.
Lemma gpr_areg2 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "B'B'='RByR0%211&Cr1u2%3221&QE(R@y5+<(;%43321%6291%?3<81pTJA1"). Proof. reflexivity. Qed.
Lemma gpr_areg3 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "B'B'='RByR0%211&Cr1u3%3221&QE(R@y5+=(;%43321%6291%?3<81pTJA1"). Proof. reflexivity. Qed.
Lemma gpr_areg4 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "B'B'='RByR0%211&Cr1u4%3221&QE(R@y5+>(;%43321%6291%?3<81pTJA1"). Proof. reflexivity. Qed.
Lemma gpr_areg5 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "B'B'='RByR0%211&Cr1u5%3221&QE(R@y5+?(;%43321%6291%?3<81pTJA1"). Proof. reflexivity. Qed.
Lemma u214 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "9'='@&RCyR0&RA+VF%2231%5241%83713"). Proof. reflexivity. Qed.
Lemma u215 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "9'='@&RCyR0&RA+VG%2231%5241%83713"). Proof. reflexivity. Qed.
Lemma u222 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "9'='@&RCyR0&RA+VN%2231%5241%83713"). Proof. reflexivity. Qed.
Lemma u226 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "9'='@&RCyR0&RA+W2%2231%5241%83713"). Proof. reflexivity. Qed.
Lemma lit_ne0 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "I'@'<&R2zr1%3221&R4+2+R0%3221%8261%:261&?'='RByR0%211&RAr2%2241%325A%83521%:11p0<1pU:H1").
Proof.
intros z Hz Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.
Lemma bn_brk_query : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "R3'B'F&QN'='7'RByR0%211%411&Jr2%211(0%116%;3631'4'9%12::%311&Kr3%211(6%116%E3631&QFvR?(QAz%211r5%63521'QOvR>(D&Q@r6(O&Q5&L%11:%311y8%Q611%M11%M2Q61%H11'E%J11'5%Q22Q;1%M11%?6;6MM41%B2A1%D21Hr4%H4NG21r7%H21F%K4Q1J1Mp041p0N1p0Q61p0QA1pQ4QN1pTHR01pTJR21").
Proof.
intros ms model K Hh Hlazy [Hsvc H10] Hc.
apply (srz_brk_query_at segs scfg ms model (Z_to_bv 64 214) K Hh Hlazy Hsvc u214); [| exact Hc].
rewrite gpr_areg0. exact H10.
Qed.
Lemma bn_brk_grow : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "TN'B'F'@&QN'='7'RByR0%211%411&Jr3%211(0%116%;3631'4'9%12::%311&Kr4%211(6%116%E3631'H&Lr5%211&Q5r1%211&QFvR?(QA&R0&RC%12O7r6%4221%611r8%:3921&R3r2%92Q71&Q2%4221z%Q>3Q@21%7294%Q@3QB13&R2r9%2261%C2QAL%4281%E2QCCr;%H221&R4+2+R0%3221%<251&R1&Q<%11J%Q02QN1r7%Q22R01r<%Q5221%8251'QOvR>(D&Q@r?(Oy8%R<11%R311%R32R<1%QN11'E%R011'5%R82RA1%R311%;6QA6R3R341%>2=1r>%A221%D4QMC1G'2&Q>&RA%QN2RLQ=%R0217%32RN1%53G11(:%S43821rAr:%R62S41%R821M%;2S61(3(8%>2S9Q1%24S9S971%43S01RJ%Q366N1RKLI%Q62;1&Q=(Q0&Q;%11QM&Q8%11QO%=3S9:1&Q:%11R2%QK1R3&Q7%11R5&Q9%11R7&Q6%11R9%?8=:87H531r@%B221%QK2D1%QN4S7QM1Q<p0Q21%QN2Q25%R14S:R01Q?p031p0Q?1p0R51p0R?1p0RH1p0RK1p0RO1p0S21p0S:1tT@T>SF1tTDSMSJ1p0SO1p0T:1pQ4TG1pTBTI1pTHTK1pTJTM1").
Proof.
intros ms model d K Hh Hlazy h b [Hsvc H10] Hbal Hdal Hd Hb0 Hnw Hs HA HB.
apply (srz_brk_grow_at segs scfg ms model (Z_to_bv 64 214) d K Hh Hlazy Hsvc u214 Halloc Hbal Hdal Hd Hb0 Hnw Hs);
[rewrite gpr_areg0; exact H10 | intros _; exact HA | exact HB].
Qed.
Lemma bn_mmap_rw : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "S;'B'F'@&QN'='7'RByR0%211%411&Jr3%211(0%116%;3631'4'9%12::%311&Kr4%211(6%116%E3631&QFvR?(QBz+3+Q2%443;21r6%83721'<&R2r5%2291&R4+2+R0%3221%7261%9261&Q1%11='>'2&QG&RA%12Q<Fr9r1r2%644321(:%QE3921qT<QB1%<2QC1r:%<4:18QB%QJ3>16'QOvR>(D&Q@r<(Oy8%R011%QG11%QG2R01%QB11(3(8%J2R5QG%24R5R5G1%43QL1QF'E%QI11'5%R12R:1%QL11%@6N;6QL41%C2B1&QHr;%23Q2<1%H241%K4QOJ1Q6p0M1pT<RD1%L26Q1r8%Q04R4O21p041p0Q61tTLS0QD1p0QG1p0R21p0R<1p0RG1pQ4S41pTFS61pTHS81pTJS:1").
Proof.
intros ms model len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hlen n Hex HB.
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n) by (unfold page_round_up; rewrite Hu1; reflexivity).
assert (Hargs : mmap_args_ok ms).
{ unfold mmap_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
repeat split; try reflexivity. apply lit_ne0. lia. }
assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (rewrite gpr_areg0; exact H10).
eapply (srz_mmap segs scfg ms model (Z_to_bv 64 222) K Hh Hlazy Hsvc u222 Hargs Halloc).
- intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. apply HB. exact Ha.
- rewrite H0, Hu1. exact Hex.
Qed.
Lemma bn_mmap_none : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "S:'B'F'@&QN'='7'RByR0%211%411&Jr3%211(0%116%;3631'4'9%12::%311&Kr4%211(6%116%E3631&QFvR?(QBz+Q2%342:21r6%73621'<&R2r5%2281&R4+2+R0%3221%7261%9261&Q1%11='>'2&QK&RA%12Q;Er9r1r2%644321(:%QD3921qT<QA1%<2QB1r:%<4:18QA%QI3>16'QOvR>(D&Q@r<(Oy8%QO11%QF11%QF2QO1%QA11(3(8%J2R4QF%24R4R4G1%43QK1QE'E%QH11'5%R02R91%QK11%@6N;QK641%C2B1&QMr;%23Q2<1%H241%K4QNJ1Q6p0M1pT<RC1%L26Q1r8%Q04R3O21p041p0Q61tTLROQD1p0QG1p0R21p0R;1p0RF1pQ4S31pTFS51pTHS71pTJS91").
Proof.
intros ms model len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hlen n Hex HB.
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
assert (Hargs : mmap_noaccess_args_ok ms).
{ unfold mmap_noaccess_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
repeat split; try reflexivity. apply lit_ne0. lia. }
assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (rewrite gpr_areg0; exact H10).
apply (srz_mmap_noaccess_at segs scfg ms model (Z_to_bv 64 222) K Hh Hlazy Hsvc u222 Hargs Halloc);
rewrite H0, Hu1; [exact Hex | exact HB].
Qed.
Lemma bn_mmap_fixed : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "SN'B'F'@&QN'='7'RByR0%211%411&Jr4%211(0%116%;3631'4'9%12::%311&Kr5%211(6%116%E3631&QFvR?(QBz+QB%34:D21r7%73621&R3r6&Q2%3221%Q23Q419&R2%12;8&R1&R0r9&Q1r8%211%5241&I&Lr:%211%411%<261&RA%;1<%22QA1'2&Q3&Q;r<%<11%311r;%:2QI1r1%83421(:%R03;21&M&Q8r=%G11%311%D2R3>r2%73321%R93D1:'QOvR>(D&Q@r?(O%N2R==y8%R@11%R711%R72R@1%R211(3(8r3%24RERE91%43R<1R6'E%R911'5%RA2RJ1%R<11%A6@;R<641%D2C1&QJr>%23D<1%I241%L4R?K1Q;r@%L21J%O4RBN1QAp041p0Q21p0Q<1tTLS9QI1p0QM1p0R;1p0R<1p0R?1p0RE1p0RN1p0S91pQ4SF1pTFSH1pT>SI1pTHSK1pTJSM1").
Proof.
intros ms model addr len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hal Hpos Hlen Htop n Hrf Hmc HB.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hprb.
assert (Htop' : alloc_top (m_vmmaps model) < 2 ^ 64) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
assert (Haddr : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; lia).
assert (Hargs : mmap_fixed_args_ok ms).
{ unfold mmap_fixed_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
repeat split; try reflexivity. apply lit_ne0. lia. }
apply (srz_mmap_fixed_noaccess_at segs scfg ms model (Z_to_bv 64 222) (Z_to_bv 64 addr) len K Hh Hlazy Hsvc u222 Hargs Halloc);
rewrite ?gpr_areg0, ?gpr_areg1, ?Haddr; first [exact H10 | exact H11 | exact HB | assumption | lia].
Qed.
Lemma bn_mprotect : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "T2'B'F'@&QN'='7'RByR0%211%411&Jr4%211(0%116%;3631'4'9%12::%311&Kr5%211(6%116%E3631&QFvR?(QC+3%239C1r7%63521&R3r6&Q2%3221z%Q23Q421&R2%1236&R1r8%2261&R0r9&Q1%115%4231&Q4%;221&RA%617%22Q>1'2&M&Q:&Lr<%211%411r;%;2QG1r1%93421(:%QN3<21&Q8r=%<11%311%D2R0=r2%B3321%R63D19&Q?r>%J2R69r3%43321%R<3J1?'QOvR>(D&Q@r@(O%Q42R@QBy8%RC11%R:11%R:2RC1%R511(3(8%Q<2RHC%24RHRH1RE%43R?1R9'E%R<11'5%RD2RM1%R?11%A6@;6R?41%D2C1&QLr?%23<S01%I241%L4RBK1QCrA%L21J%O4REN1Q<p041p0Q21p0Q91p0QB1tTLS=R01p0R41p0R<1p0R@1p0RC1p0RJ1p0S21p0S=1pQ4SJ1pTFSL1pT>SM1pTHSO1pTJT11").
Proof.
intros ms model addr len K Hh Hlazy (Hsvc & H10 & H11 & H12) Hal Hlen Ha0 Hnw n Hna Hma Hbud HB.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
assert (Haddr : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; unfold two_pow_64 in Hnw; lia).
apply (srz_mprotect_at segs scfg ms model (Z_to_bv 64 226) (Z_to_bv 64 addr) len K Hh Hlazy Hsvc u226 Halloc);
rewrite ?gpr_areg0, ?gpr_areg1, ?gpr_areg2, ?Haddr; first [exact H10 | exact H11 | exact H12 | exact HB | assumption | lia].
Qed.
Lemma bn_munmap : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrNodes "SA'B'F'@&QN'='7'RByR0%211%411&Jr4%211(0%116%;3631'4'9%12::%311&Kr5%211(6%116%E3631&QFvR?(QD%128Br7%53421&R3r6&Q2%3221z%Q13Q321&R1%1239&R2%125;&R0r9&Q1r8%211%5241&G%;221'2&N&Q8&Lr;%211%411&RAr:%22QD1%@1A%42QF1%;3631(:%QL3>21'QOvR>(D&Q@r=(O%>2R0Q3y8%R311%QJ11%QJ2R31%QE11(3(8%F2R8I%Q41F%H2R:1%44R:R:31%63R11QK'E%QN11'5%R62R?1%R111%C6B=R1641%F2E1&QIr<%23><1%K241%N4R4M1QDr>%N21L%Q14R7Q01Q8p041p0Q41p0QD1p0QM1p0R01p0R31p0R:1p0RA1p0RL1pQ4S91pTFS;1pT<S<1pTHS>1pTJS@1").
Proof.
intros ms model a len K Hh Hlazy (Hsvc & H10 & H11) Hal Ha0 Hlen Hnw Hhas Hc.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
assert (HTS : TASK_SIZE < 2 ^ 64) by (unfold TASK_SIZE; lia).
assert (Haddr : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
assert (Hprr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)) by (unfold page_round_up; rewrite Hu1; reflexivity).
assert (H0 : ms_gpr ms 0 = Z_to_bv 64 a) by (rewrite gpr_areg0; exact H10).
assert (Hargs : munmap_args_ok ms model).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hprr, Haddr. repeat split; try assumption.
intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
eapply (SpinAlg.srz_munmap segs scfg ms model (Z_to_bv 64 215) K Hh Hlazy Hsvc u215 Hargs).
unfold munmap_eff. rewrite H0, Hprr. exact Hc.
Qed.
End WithSegs.
