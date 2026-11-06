(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From Stdlib Require Permutation.
From stdpp Require list.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.

(* [comment removed for export] *)
Module SpineMallocQ7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SAlu"; "ss_next"; "eval"; "SVar"; "ss_facts"; "swf"; "valuation"; "SPNot"; "holds"; "ss_lenient"; "SPBranch"; "SPUle"; "rw"; "SMd"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "nil"; "pair"; "prod"; "Some"; "option"; "andb"; "false"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cP2"; "GR"; "vMU"; "HINT_map"; "cPa"; "cPb"; "req_e"; "vAU"; "vK"; "vNF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "mul"; "sub"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "ALU_SRA"; "ALU_XOR"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7"; "F_mu0"; "F_hi"; "size_e_hi"; "size_e_lo"; "x19_e0"; "x19_e1"; "popfacts"; "total_e"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_free_array"; "cs_allocated_user"; "cs_mapped_user"; "AA"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "ph0"; "gh_nf"; "ghosts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "tab1_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws PrimCredit PrimCreditLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.PrimRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition size_e_hi : sv := ltac2:(tb__ "0|4|
SbS37SbS38SbS3cSbS39SeS40A1M0SaZ3fA1M1A3G1A3SbS3aSbS39SaZ200A1SbS3aSbS37G0SaN10A1A3SaZ1A1M2A3A3M3G2A3A3G3A3").
Definition size_e_lo : sv := ltac2:(tb__ "0|0|
SbS39SeS40A1SaZ5A1A3").
Definition tabS_okb : bool := ltac2:(tb__ "0|0|
S22S22S22S61S40S45S51Z11UeA5S60S40S45A2A2S61S40S46S51Z1U10A5A2S60S40S46A2A2").
Lemma tabS_ok : tabS_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Definition F_hi : sprop := ltac2:(tb__ "0|0|
S15S3bSaZ10A1SeS40A1A3").

Definition total_e : sv := ltac2:(tb__ "0|0|
SbS37S2dS18S3eSeS41A1S2cA3A3").
Definition x19_e0 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSaN1A1A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition x19_e1 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSbS3dS28SaZffffffffffffffffA1A3A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition F_mu0 : sprop := SPBranch BC_EQ vMU (SLit 0).

Definition popfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|1|
S4eQ40S17Vrb;PcA2A2S25S5dR1A1S25S5eVA;R2A2S57S6S31S33S24S25S53R1A1A2A1S52R2A1A2S6S30S32S55R1A1Z40000A2S65R2A1M0A2S30G0Ze0000000A2A2A2Tcs;Tc;Tnv;").

Lemma entry_popfacts : ltac2:(tb__ "0|1|
S56S11S1cS4dQ40M0A1A1S62S1cS63A1S64S11S5fR7R6R5R4R3R2R1A7S31S5bR8R7A2S52S5dS4eG0S17R7PcA2A2A1A1A2S49R9R8A2F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE HNP. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as ((_ & _ & _ & Hroom) & _). unfold popfacts. cbn zeta. unfold gh_nf in HNP. split; [exact HNP|].

  destruct (cap_facts _ C1) as (_ & _ & MCU & _).
  assert (NP : needs_populate (cls_of (bv_unsigned (rw rb 12%positive))) (cst_of A (bv_unsigned (rw rb 12%positive))) = true) by (unfold needs_populate; apply Z.ltb_lt; exact HNP).
  specialize (Hroom NP).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in *. unfold cst_of in *. split; [exact Hroom | exact MCU].
Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S66VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S5cVA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma size_hi_val : ltac2:(tb__ "0|0|
S13Vr;S44A2S5S4dQ40A1SdVr;S45A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. apply Z.ltb_lt in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T _]. apply andb_prop in T as [T _]. apply andb_prop in T as [T1 T2].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_hi Size 17 14 r c T1 T2 E158 ltac:(clear -C1 HF; lia)).
Qed.
Lemma size_lo_val : ltac2:(tb__ "0|0|
S7S13Vr;S44A2A1S5S4dQ40A1SdVr;S46A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  assert (C16 : c <= 16) by (destruct (Z.ltb_spec 16 c) as [X|X]; [exfalso; apply HF; reflexivity | exact X]).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_lo Size 1 16 r c T3 T4 E158 ltac:(clear -C1 C16; lia)).
Qed.

Lemma pop_nums : ltac2:(tb__ "0|4|
S51Vc;A1S25S52Vc;A1S25S33S24S25S53Vcs;A1A2A1S25S54Vcs;A1S25S55Vcs;A1S25S6S6S30Z20R5A2S30R5Z10000M0A2A2S6S6S30Z1R4A2S30R4Z8A2A2S6S6S30Z0M1R3A2S31R3R4A2A2S6S6S30G1R2A2S30R2R1A2A2S6S30R1Zdffc0000A2S6S31R1S32R2R5A2A2S6S6S31G1S34R5S35R4R3A2A2M2A2S30G2G0A2A2S6S31R1S32R2G2A2M3A2S30G3S32R1G0A2A2A2A2A2A2A2A2A2A2Tmu;Tau;Tnf;Tk;TS;").
Proof.
  intros S k nf au mu.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. fold S k nf au mu in CF.
  destruct CF as ((_ & _ & S1 & _) & (K1 & _ & K3) & (_ & AU0 & _ & _ & TI0) & _).
  destruct PF as (NP & RM & RC). fold nv c cs in NP, RM, RC. fold k nf mu in NP, RM.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. fold nf in NF0.
  clear -S1 K1 K3 AU0 TI0 NP RM RC NF0.
  assert (B1 : 0 < S * (k - nf)) by nia. assert (B2 : S * (k - nf) <= S * k) by nia. assert (B3 : S <= S * (k - nf)) by nia. lia.
Qed.

Lemma total_val : ltac2:(tb__ "0|0|
S5S25S4eQ40SdVr;S4aA2A2S32S54Vcs;A1S34S51Vc;A1S35S52Vc;A1S33S24S25S53Vcs;A1A2A1A2A2A2A3").
Proof.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & Q221 & _ & Q223 & _ & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q227.
  unfold total_e, req_e, vAU, vK, vNF, V_SIZE. cbn [eval]. rewrite add_val, mul_val, sub_val, E148, Q221, Q223, Q227.
  rewrite !u64_lit by (clear -N1 N2 N3 N4 N5; lia).
  rewrite (Z.mod_small (kchunks c - _)) by (clear -N2 N3; lia). rewrite (Z.mod_small (Size c * _)) by (clear -N7; lia).
  rewrite Z.mod_small by (clear -N4 N5 N7; lia). reflexivity.
Qed.

Lemma F_pop_hold : Forall (holds r) F_pop.
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227.
  unfold F_pop. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. unfold branch_taken, bv_ltu, vNF, vK. cbn [eval]. rewrite Q221, Q227. rewrite !u64_lit by (clear -N2 N3; lia). apply Z.ltb_lt. exact (proj2 N3).
  - unfold HINT_map. cbn [holds]. unfold branch_taken, bv_ltu. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224. rewrite u64_lit by (clear -N4 N5; lia).
    apply Z.ltb_lt. exact (proj1 N8).
  - cbn [holds]. unfold vMU. cbn [eval]. rewrite Q224. rewrite !u64_lit by (clear -N4 N5; lia). exact N5.
Qed.

Lemma x19_val1 : ltac2:(tb__ "0|0|
S5S4dQ40A1SdVr;S48A2SdVr;SaZ40000A1A2A3").
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  unfold x19_e1. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val, xor_val. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224.
  rewrite !u64_lit by (clear -N4 N5; lia).
  rewrite lxor_ones64 by (clear -N4 N5; lia).
  replace ((tot + (18446744073709551615 - cs_mapped_user cs)) mod 2 ^ 64) with (tot - cs_mapped_user cs - 1).
  2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N5 N8; lia. }
  rewrite land_m18_small by (clear -N8; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
Qed.
Lemma x19_val0 : ltac2:(tb__ "0|1|
S13Vr;S43A2S6S5S4dQ40A1M0SdVr;S47A2SdVr;SaZ40000A1A2A3S5G0SdVr;SaZ0A1A2SdVr;S28A2A3A2F_;").
Proof.
  intros HF. pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  unfold F_mu0 in HF. cbn [holds] in HF. unfold branch_taken, bv_eqb, vMU in HF. cbn [eval] in HF. rewrite Q224 in HF. rewrite !u64_lit in HF by (clear -N4 N5; lia). apply Z.eqb_eq in HF.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  split.
  - unfold x19_e0. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val. fold total_e. rewrite TV.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by reflexivity. rewrite !u64_lit by (clear; lia).
    replace ((tot + 18446744073709551615) mod 2 ^ 64) with (tot - 1).
    2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N8 HF; lia. }
    rewrite land_m18_small by (clear -N4 N8 HF; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
  - unfold vMU. cbn [eval]. rewrite Q224, HF. reflexivity.
Qed.
End VALS.

Section POP1.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S5fVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable F : nat.
Variables (E3 : axst) (LP : axst) (La Lb La0 La1 Lb0 Lb1 : leafA) (CP2C : axst) (sa0 sa1 sb0 sb1 : wsub).
Let FR : list sprop := factsQ E3.
Let CPA : axst := ltac2:(tb__ "0|0|
S2aVFR;S1VLa;A1A2").
Let CPB : axst := ltac2:(tb__ "0|0|
S2bVFR;S1VLb;A1A2").
Hypothesis FP_in : ltac2:(tb__ "0|0|
S36S9S15S3bS2fS2eA3SfS0VLP;A1A1A3").
Hypothesis R_p1 : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z415c0S1bS25Z41600S1dS25A1A3A3VLP;S1aA5S20G0S1bS2VLa;S1bS2VLb;S1dS2A1A3A3A2A3").
Hypothesis LN_p : ltac2:(tb__ "0|0|
S5S19S14S0VLP;A1A1S23A3").
Hypothesis NX_p : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VLP;A1A1A2S1aA3").
Hypothesis Fa_in : ltac2:(tb__ "0|0|
S36S9S44SfS0S1VLa;A1A1A1A3").
Hypothesis Fb_in : ltac2:(tb__ "0|0|
S36S9S12S44A1SfS0S1VLb;A1A1A1A3").
Hypothesis W_pa : ltac2:(tb__ "0|0|
S5S19S10S0VCPA;A1A1S1aA3").
Hypothesis D_pa : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa;A1A1S0VCPA;A1A2S20G3S1eG1G2S1bG0S1eS8S8S45SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pa : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPA;A1A1ScS0S1VLa;A1A1A1A2S1aA3").
Hypothesis W_pb : ltac2:(tb__ "0|0|
S5S19S10S0VCPB;A1A1S1aA3").
Hypothesis D_pb : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb;A1A1S0VCPB;A1A2S20G3S1eG1G2S1bG0S1eS8S8S46SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pb : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPB;A1A1ScS0S1VLb;A1A1A1A2S1aA3").
Hypothesis R_p2a : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41630S1dS25A1A3VCPA;S1aA5S20G0S1bS2VLa0;S1bS2VLa1;S1dS2A1A3A3A2A3").
Hypothesis LN_pa : ltac2:(tb__ "0|0|
S5S19S14S0VCPA;A1A1S23A3").
Hypothesis NXr_pa : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPA;A1A1A2S1aA3").
Hypothesis R_p2b : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41630S1dS25A1A3VCPB;S1aA5S20G0S1bS2VLb0;S1bS2VLb1;S1dS2A1A3A3A2A3").
Hypothesis LN_pb : ltac2:(tb__ "0|0|
S5S19S14S0VCPB;A1A1S23A3").
Hypothesis NXr_pb : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPB;A1A1A2S1aA3").

Section LEAF.
Variables (L : leafA) (s : wsub) (mu0 : bool).
Let C2 : axst := ltac2:(tb__ "0|0|
S26VFR;S1VL;A1A2").
Hypothesis F_in : ltac2:(tb__ "0|0|
S36S9S19S9Lmu0;Vmu0;S43S12S43A1X19x2SfS0S1VL;A1A1A1A3").
Hypothesis W_2 : ltac2:(tb__ "0|0|
S5S19S10S0VC2;A1A1S1aA3").
Hypothesis D_2 : ltac2:(tb__ "0|6|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VL;A1A1S0VC2;A1A2S20G3S1eG1G2S19G1Lmu0;Vmu0;S1bG0S1eS8S8S47SaZ40000A1M4A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1M5A3A3S1bG0S1eS8S8S48G4A4G5A3X19x2S1dS9A1A4A2A3").
Hypothesis NX_2 : ltac2:(tb__ "0|0|
S5S19S4bScS0VC2;A1A1ScS0S1VL;A1A1A1A2S1aA3").
Hypothesis ENT_2 : ltac2:(tb__ "0|0|
S5S19S3VC2;VCP2C;Vs;A3S1aA3").
Hypothesis SID_2 : ltac2:(tb__ "0|0|
S5S19S4fVs;S27A2S1aA3").

Lemma join_leaf : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5aA6M0VCP2C;R1R4A5R3A2Fr';VTR;S50S42G0S1VL;A1R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q PF HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L) (ax_S C2) _ _ ph0 r tp Q W_2 D_2 NX_2).
  { intros tr md (HFz & HGh & _) HF. split; [|constructor].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    pose proof (proj1 (Forall_forall _ _) HF _ F_in) as HB.
    unfold diffs_ok. destruct mu0.
    - destruct (x19_val0 A rb r CF PF RG HGh HB) as [X1 X2]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (x19_val1 A rb r CF PF RG HGh). }
  change (ax_setS (la_state L) (ax_S C2)) with C2.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph0) CP2C (rho_sub r s) tp)); [|exact (HC _)].
  intros w Hw. apply (SPA_entails_J (JRp ph0) (JRp ph0) C2 CP2C s r tp w ENT_2); [|exact Hw].
  intros HJ. eapply (JR_stable A Kc rb tp0 md0 ph0 GR HKc ltac:(lia)); [exact (rho_sub_agree s GR r SID_2) | apply mat_equiv_refl | exact HJ].
Qed.
End LEAF.

Hypothesis Fa0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLa0;A1A1A1A3").
Hypothesis Fa1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLa1;A1A1A1A3").
Hypothesis Fb0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLb0;A1A1A1A3").
Hypothesis Fb1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLb1;A1A1A1A3").
Hypothesis W_a0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa0;A1A2A1A1S1aA3").
Hypothesis W_a1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa1;A1A2A1A1S1aA3").
Hypothesis W_b0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb0;A1A2A1A1S1aA3").
Hypothesis W_b1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb1;A1A2A1A1S1aA3").
Hypothesis D_a0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_a1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis D_b0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_b1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis NX_a0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_a1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis ENT_a0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa0;A1A2VCP2C;Vsa0;A3S1aA3").
Hypothesis ENT_a1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa1;A1A2VCP2C;Vsa1;A3S1aA3").
Hypothesis ENT_b0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb0;A1A2VCP2C;Vsb0;A3S1aA3").
Hypothesis ENT_b1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb1;A1A2VCP2C;Vsb1;A3S1aA3").
Hypothesis SID_a0 : ltac2:(tb__ "0|0|
S5S19S4fVsa0;S27A2S1aA3").
Hypothesis SID_a1 : ltac2:(tb__ "0|0|
S5S19S4fVsa1;S27A2S1aA3").
Hypothesis SID_b0 : ltac2:(tb__ "0|0|
S5S19S4fVsb0;S27A2S1aA3").
Hypothesis SID_b1 : ltac2:(tb__ "0|0|
S5S19S4fVsb1;S27A2S1aA3").

Theorem populate_head : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5aA6M0VCP2C;R1R4A5R3A2Fr';F_;VTR;S50S42G0VLP;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.

  apply (tr_facts Kc TR KIT). intros HF0. pose proof (proj1 (Forall_forall _ _) HF0 _ FP_in) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (popfacts A rb)).
  { intros w [_ (HFz & HGh & _)]. apply (entry_popfacts _ _ _ _ _ _ _ HE).
    destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. apply Z.ltb_lt in BF. exact BF. }
  intros PF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x415c0; 0x41600] LP [La; Lb] ph0 r tp Q R_p1 LN_p NX_p).
  intros L r1 [<-|[<-|[]]] _.
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state La) (ax_S CPA) _ _ ph0 r1 tp Q W_pa D_pa NX_pa).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_hi_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fa_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state La) (ax_S CPA)) with CPA.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41630] CPA [La0; La1] ph0 r1 tp Q R_p2a LN_pa NXr_pa).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf La0 sa0 true Fa0_in W_a0 D_a0 NX_a0 ENT_a0 SID_a0 r2 tp Q PF (HC PF)).
    + exact (join_leaf La1 sa1 false Fa1_in W_a1 D_a1 NX_a1 ENT_a1 SID_a1 r2 tp Q PF (HC PF)).
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state Lb) (ax_S CPB) _ _ ph0 r1 tp Q W_pb D_pb NX_pb).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_lo_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fb_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state Lb) (ax_S CPB)) with CPB.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41630] CPB [Lb0; Lb1] ph0 r1 tp Q R_p2b LN_pb NXr_pb).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf Lb0 sb0 true Fb0_in W_b0 D_b0 NX_b0 ENT_b0 SID_b0 r2 tp Q PF (HC PF)).
    + exact (join_leaf Lb1 sb1 false Fb1_in W_b1 D_b1 NX_b1 ENT_b1 SID_b1 r2 tp Q PF (HC PF)).
Qed.
End POP1.
End SpineMallocQ7.

(* [comment removed for export] *)
Module SpineMallocQ3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "SLit"; "SVar"; "SAlu"; "rm"; "cell"; "ss_objs"; "sprop"; "ss_facts"; "SPBranch"; "eval"; "mkCell"; "obj_range"; "ss_lenient"; "ss_next"; "SExt"; "SPNot"; "ext_low"; "smatch"; "sstate"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "sub"; "to_nat"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "bool"; "true"; "pair"; "prod"; "false"; "nat"; "option"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "PV4"; "PV6"; "PV7"; "keepn"; "GR"; "O_cell"; "PNX"; "O_pcm"; "O_ri"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3.POP"; "JRpop"; "phK"; "O_dstc"; "O_srcc"; "e_end"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "FAb"; "PCE"; "ph_fill"; "frozen"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_pop"; "ph_ri"; "ph_u"; "phase"; "rmlink"; "gh_new"; "gh_nf"; "rlink"; "zoneR"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "map"; "skipn"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "view"; "acell"; "c_addr"; "c_w"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "pc_base"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_thread"; "cs_cache"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sext32_small : ltac2:(tb__ "0|2|
S0S3S1fZ0R1A2S20R1S25Z2Z1fA2A2A2S2S35Q40M0A1S1aS2aQ20S36G0R2A2M1A3G1A3F_;Fz;").
Proof.
  intros z Hz. unfold ext_low. apply bv_eq.
  assert (E : bv_unsigned (bv_extract 0 32 (Z_to_bv 64 z)) = z).
  { rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.shiftr_0_r.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_small. lia. }
  rewrite sext64_32_small by (rewrite E; lia). rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry. apply Z.mod_small. lia.
Qed.

Lemma view_absorb_out : ltac2:(tb__ "0|1|
S7S27S6A1S6eS0S6S67S6R1R4A3S4S3S1fS32S0S0S15R6R2A2M0A3R3A2S20R3S33S0S0G0A3A2A2A1F_;Fo;S2S2fS35Q8A1A1S73S34SdS6cR5R4R3A3A1R2A3S73S34SdR5A1R2A3A3F_;Fz;Fms;FR;Frho;").
Proof.
  intros rho R ms z Hout. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold rd_of. rewrite rm_absorb_out; [reflexivity|].
  intros (o & Ho & Hr). apply (Hout o Ho). rewrite u64_lit in Hr by lia. exact Hr.
Qed.

Lemma rmlink_absorb : ltac2:(tb__ "0|1|
S35Q40A1S2fS35Q8A1A1F_;S7S27S6A1S6eS5eR4SdR3A1A2S6S67S6R1R4A3S5S1fS33S0S0S15R6R2A2M0A3S85A2S1fS84S32S0S0G0A3A2A2F_;Fo;S5eR6SdS6cR5R4R3A3A1A2F_;F_;Fms;FR;Frho;Ff0;").
Proof.
  intros f0 rho R ms H HR a Ha. rewrite rm_absorb_out; [exact (H a Ha)|].
  intros (o & Ho & Hr). rewrite u64_lit in Hr by (unfold IMG_LO, IMG_HI in Ha; lia). destruct (HR o Ho); lia.
Qed.

Lemma cell_ok_agree_range : ltac2:(tb__ "0|1|
S71S71S74S0S3S1fS75R2A1M0R1A2S20R1S1eG0S24S76R2A1A1A2A2A2S2S2fS35Q8A1A1R4R2A1R5R2A1A3F_;Fz;S72R4R2A2S72R4R3A2F_;F_;Fcc;Fm';Fm;").
Proof. intros m m' cc H Hc j Hj. rewrite H by lia. exact (Hc j Hj). Qed.

Lemma ph_eta : ltac2:(tb__ "0|0|
S5dS2S5dR1S57S5cR1A1S59R1A1S54R1A1S5aR1A1S58R1A1S5bR1A1A6A3Fp;").
Proof. intros p. destruct p. reflexivity. Qed.

Lemma nth_skipn_Z : ltac2:(tb__ "0|0|
S27S0A1S2eS2eS0S2S0S63S0R2S66S0R3R4A3R1A4S63S0S81R3R2A2R4R1A4A3Fd;Fi;Fn;Fl;").
Proof. intros l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|]. destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH. Qed.

Section POP.

Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S2S7dVst;S7cA3S2S27S7bA1VW;S28S7bA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S8fVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.

Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S3S2S0S5aVph;A1Z0A3S3S2S29S58Vph;A1S2dA3S2S29S5bVph;A1S2dA3A2A2").
Definition phK (i : Z) : phase := ltac2:(tb__ "0|0|
S57S5cVph;A1S59Vph;A1S54Vph;A1Vi;S2dS2dA6").
Variable faP : list Z.
Let nfP : Z := Z.of_nat (length faP).
Hypothesis HSRC : ltac2:(tb__ "0|1|
S0S71S3S1fZ0M0R2A2S1fR2Vk;A2A2S61VA;Vrb;S4aR3A1S73S34SdVrb;A1A2R2A5S0S3S1fG0R1A2S20R1VnfP;A2A2S72R5S77S1eS52VA;Vrb;A2S21Z4R2A2A2U4S63S0S23R2A1VfaP;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Hypothesis HKF : k <= nfP.
Hypothesis HNFP : 4 * nfP <= 536870912.
Hypothesis HFILLR : ltac2:(tb__ "0|4|
S20Z0M0S54Vph;A1M1A2S3S1fG0S60VA;Vrb;A2M2A2S3S2S0S1eG2S5fVA;Vrb;A2M3A2VnfP;A3S1fG1G3A2A2A2F_;").
Hypothesis HIDS : ltac2:(tb__ "0|0|
S0S67S0R1VfaP;A3S3S1fZ0R2A2S20R2S25Z2Z1cA2A2A2F_;Fx;").
Hypothesis HCACHE : ltac2:(tb__ "0|0|
S2S27S0A1S89S8aVc;S8cVA;Vnv;A2A2A1S66S0S23S22VnfP;Vk;A2A1VfaP;A3A3").

Lemma zone_thread : ltac2:(tb__ "0|2|
S0S0S3S1fS1eS88S87VA;A1A1M0Z120A2R1A2S20R1S1eG0Zc60A2A2A2S62VA;Vrb;S4aR3A1R2A4S3S1fS1eS53VA;Vrb;A2Z10A2M1R3A2S20R3S1eG1S21Z4R4A2A2A2A2F_;F_;Fz;Fi;").
Proof.
  intros i z Hz HZ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A nv)))) as NF0.
  unfold zoneR, phK in HZ. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in HZ. fold nv c in HZ.
  unfold U0, F0, FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ. fold nv c in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; try exact X; exfalso.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFILLR X2) as (F1 & F2 & F3). unfold gh_nf, gh_new in *. fold nv c in F1, F2, F3, X.
    clear -X Hz F1 F2 F3 HNFP C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Definition JRpop (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6aA1S69S3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVi;A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRpop_K : ltac2:(tb__ "0|0|
S0S8bVKc;S49R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRpop_stable : ltac2:(tb__ "0|0|
S0S1S2S29S7fS43R1A2S2aA3S48S34R2S49R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H4 & H6). apply Pos.leb_le in Hn. unfold PNX in Hn.
  split; [|split].
  - eapply (JR_stable A Kc rb tp0 md0 (phK i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw PV4) by (unfold PV4; lia). exact H4.
  - destruct Hag as (Hw & _). rewrite <- (Hw PV6) by (unfold PV6; lia). exact H6.
Qed.

Definition O_srcc : sobj := ltac2:(tb__ "0|0|
S42S3eS26SeS14SaZ0A1Z4SbS3fA1A3S28SeA1A3A2").
Definition O_dstc : sobj := ltac2:(tb__ "0|0|
S42S3dS26SeS14SaZ0A1Z4S18S2aQ20SbS3fA1A3A3S28SeA1A3A2").

Lemma pop_release : ltac2:(tb__ "0|6|
S1cS27S6A1M0S7S27S35Q40M1A1M2A1S27S6aA1M3S6eS69S69S0S3S1fZ0M4R1A2S20R1Vk;A2A2S2G0SfRaA1S30S6R9S26S6S4cS26S6S4bS28S6A1A3A3M5A3A3S1bS34R9RbS2bG3S82R7S83R6R5A2A4A4S2G2S9RaS3fA2S36G1S63S0S23S1eS22VnfP;Vk;A2R4A2A1VfaP;G4A4A2A3S49R5RbRaR9R6A5S6cRcG5R9A3S7S3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eR7Z1A2A1R1RcRbR8AaS3S2G2S9R1S3dA2S9RdS3dA2A3S2G2S9R1S3eA2S9RdS3eA2A3A2A2Tr3;F_;F_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FS;").
Proof.
  intros S K r2 tp tr ms md mdJ i Hi HO Hsm H7 ((HFz & HGh & HKc' & HM & HR & HRM) & H4 & H6) r3.
  split; [|split; reflexivity].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & _ & (_ & N6) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (Hid : 0 <= idv < 2 ^ 28).
  { apply HIDS. unfold idv. apply nth_In. unfold nfP in *. lia. }
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  idtac "pr:1".
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RS : obj_range r2 O_srcc = (Si, Si + 4)).
  { unfold O_srcc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H6, u64_lit by (unfold Si in *; lia). f_equal; lia. }
  assert (RD : obj_range r2 O_dstc = (Di, Di + 4)).
  { unfold O_dstc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H4, u64_lit by (unfold Di in *; lia). f_equal; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).

  assert (M3S : forall j, (j < 4)%nat -> m3 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_srcc Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SVar PV7)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_srcc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H6, soff_lit_small, u64_lit in ASb by (unfold Si in *; lia).
    rewrite H7 in ASb. unfold m3. rewrite view_in by (unfold Si in *; lia). fold Si in ASb. replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M3D : forall j, (j < 4)%nat -> m3 (Di + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_dstc Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SExt true 32 (SVar PV7))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_dstc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H4, soff_lit_small, u64_lit in ASb by (unfold Di in *; lia).
    rewrite H7, sext32_small in ASb by lia. unfold m3. rewrite view_in by (unfold Di in *; lia). fold Di in ASb. replace (Di + 0 + Z.of_nat j) with (Di + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M2S : forall j, (j < 4)%nat -> m2 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m2 ltac:(lia) HR (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    unfold Si. exact Hc. }
  assert (AGR : forall z, ~ (Di <= z < Di + 4) -> m3 z = m2 z).
  { intros z Hz. destruct (Z_le_dec Si z) as [H1|H1]; [destruct (Z_lt_dec z (Si + 4)) as [H2|H2]|].
    - replace z with (Si + Z.of_nat (Z.to_nat (z - Si))) by lia. rewrite M3S, M2S by lia. reflexivity.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia. }
  idtac "pr:2".
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r2 [O_srcc; O_dstc] ms HRM); intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd];
           unfold IMG_LO, IMG_HI, Si, Di; rewrite ?FAr, ?PCr; unfold nfP in *; lia].
  fold m3. unfold rlink in HR |- *. fold m2 in HR.
  destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (ZI : forall z, zoneR A rb (phK (i + 1)) z <-> (zoneR A rb (phK i) z \/ Di <= z < Di + 4)).
  { intros z. unfold zoneR, phK. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. fold nv c. unfold Di. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)); [left; right; right; right; right; right; left; lia | right; lia].
      + left; right; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; lia.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; left; lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec Di z) as [H1|H1]; [destruct (Z_lt_dec z (Di + 4)) as [H2|H2]|].
    + replace z with (Di + Z.of_nat (Z.to_nat (z - Di))) by lia. rewrite M3D by lia. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill phK] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLR ltac:(lia)) as (F1 & F2 & F3). unfold Di. rewrite PCr. rewrite FAr in Hz. change (Z.of_nat 4) with 4 in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj Hi K1 HNFP F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop phK] in Hi'. destruct (Z.eq_dec i' i) as [->|Hne].
    + intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold Di. rewrite M3D by exact Hj. do 3 f_equal. fold nv c. rewrite HCACHE, nth_skipn_Z.
      unfold idv. replace (Z.to_nat (nfP - k) + Z.to_nat i)%nat with (Z.to_nat (nfP - k + i)) by (clear -HKF Hi; lia). reflexivity.
    + eapply cell_ok_agree_range; [|exact (L4 i' ltac:(cbn [ph_pop phK]; lia))]. cbn [c_addr c_w]. intros z Hz. apply AGR. unfold Di. lia.
  - intros X. discriminate X.
  - intros X. discriminate X.
Qed.

Variable F : nat.
Variable CT0 : axst.
Variables LB LX : leafA.
Variable nob : nat.
Variable s_bk : wsub.
Let CT1 : axst := cT1 CT0.
Definition e_end : sv := ltac2:(tb__ "0|0|
ScS4eScS4eS78SaZ10A1A3ScS50S46SaZ2A1A3A3").
Definition NPOP : list carve_spec := ltac2:(tb__ "0|9|
S26S2cS2cS2cS8S0A2M0S0A2M1S27S2cS2cS0S2eA2M2S8A2M3A1M4A2M5S2bG1G4S2bG0S0S2bS8S0SbS3eA1Z0M6A4Z4M7A4S26G3S2bG2S8S2bS0S2eG6U4A4SbS3fA1A4S28G3A1M8A3A4S26G5S2bG1G4S2bG0S0S2bS8S0SbS3dA1G6A4G7A4G8A4S28G5A1A3A3").
Hypothesis SK_t : ltac2:(tb__ "0|1|
S2S27S2cS2cS8S8A2S8A2M0A1S65S6G0S7eSfS38VCT0;A1A1A4S65S6G0S7eS30S6S8eVW;A1S26S6S79S26S6S7aS26S6S44S26S6S45S28S6A1A3A3A3A3A3A4A3").
Hypothesis XX_t : ax_X CT0 = [].
Hypothesis XF_t : ltac2:(tb__ "0|0|
S68S10S8dVW;Vst;A2S11S38VCT0;A1A1A3").
Hypothesis NX_t : ltac2:(tb__ "0|0|
S2S29S80S17S38VCT0;A1A1S43A2S2aA3").
Hypothesis W_t1 : ltac2:(tb__ "0|0|
S2S29S1dS38VCT1;A1A1S2aA3").
Hypothesis R_t1 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z413dcS26S0Z413f0S28S0A1A3A3VCT1;S2aA5S31G0S26S3aVLB;S26S3aVLX;S28S3aA1A3A3A2A3").
Hypothesis LN_t1 : ltac2:(tb__ "0|0|
S2S29S16S38VCT1;A1A1S2dA3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLB;A1A1A1M0S30S6S64S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLX;A1A1A1M0S30S6S64S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S2S29S3bS40S39VLB;A1Vnob;A2VCT0;Vs_bk;A3S2aA3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S2S29S6dVs_bk;S41A2S2aA3").
Hypothesis S_bk4 : ltac2:(tb__ "0|0|
S2S8S6bVs_bk;S3dA2ScS4eSbS3dA1SaZ4A1A3A3").
Hypothesis S_bk6 : ltac2:(tb__ "0|0|
S2S8S6bVs_bk;S3eA2ScS4eSbS3eA1SaZ4A1A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S67S10S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3S11S38S39VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S67S10S19S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3A1S11S38S39VLX;A1A1A1A3").

Lemma pop_carve : ltac2:(tb__ "0|5|
S0S7S27S35Q40M0A1M1A1S70S3S1fZ0M2R4A2S20R4Vk;A2A2S47S34S49R5A1VCT0;R4R3R2A6S86R5S26S2cS1G1A2M3S2bS1G1S3fS36G0S63S0S23S1eS22VnfP;Vk;A2M4R6A2A1VfaP;G2A4A2A4S28G3A1A3A2S7S3S47S34S49R7A1VCT1;R1R5R4A6S2G1S9R1S3fA2S36G0S63S0S23S1eG4R7A2A1VfaP;G2A4A2A3A2Tr1;F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H r1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & (_ & MU0 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  split; [|exact E7].
  assert (AG1 : agree_below PNX r r1). { unfold r1. apply agree_below_rho_sets. intros j v [X|[]]. injection X as <- _. unfold PNX, PV7. lia. }
  assert (Erm1 : rm r1 = rm r) by (unfold r1; apply rm_rho_sets).
  assert (H1 : SPA segs (JRpop i) CT0 r1 tp w).
  { destruct H as [Hsm HJ]. split.
    - eapply smatchA_agree; [|exact Hsm]. apply Pos.eqb_eq in NX_t. rewrite NX_t. exact AG1.
    - eapply (JRpop_stable i PNX ltac:(reflexivity)); [exact AG1 | apply mat_equiv_refl | exact HJ]. }
  idtac "pc:1".
  destruct H1 as [HsmA1 HJ1]. pose proof HJ1 as ((HFz & HGh & _ & _ & HR & _) & H4 & H6). pose proof (proj1 HJ1) as HJ1'.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  pose proof (proj1 HsmA1) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CT0) [O_pcc0; O_st; O_pcm; O_ri] r1 _ HW HE HFz Hsm1 SK_t XF_t) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r1 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r1 os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r1 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r1 ori O_ri SKr) in RNr.
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  set (m1 := view segs (rm r1)) in *. unfold rlink in HR. fold m1 in HR.
  assert (ES : bv_unsigned (eval r1 (SVar PV6)) = Si) by (cbn [eval]; rewrite H6; apply u64_lit; unfold Si; lia).
  assert (ED : bv_unsigned (eval r1 (SVar PV4)) = Di) by (cbn [eval]; rewrite H4; apply u64_lit; unfold Di; lia).

  assert (MS : forall j, (j < 4)%nat -> m1 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m1 ltac:(lia) (proj1 (proj2 (proj2 (proj2 (proj2 HJ1'))))) (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc. exact Hc. }
  assert (PD : forall z, Di <= z < Di + 4 -> exists b, m1 z = Some b).
  { intros z Hz. destruct HR as (L1 & L2 & _).
    assert (ZD : zoneR A rb (phK i) z \/ ~ zoneR A rb (phK i) z).
    { destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)) as [Y|Y]; [left; unfold zoneR, phK; cbn [ph_pop]; do 5 right; left; unfold Di in Hz; lia|].
      right. intros X. apply (zone_thread i z) in X; [lia|]. unfold Di in Hz. rewrite PCr in Hz. lia. }
    destruct ZD as [ZD|ZD].
    - specialize (L2 z ZD). destruct (m1 z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z ZD). destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
      destruct (pc_entry_facts0Q A rb tp0 md0 nv HA Hnv Hcnt) as (_ & PE & _). cbn zeta in PE. fold c in PE. apply PE. unfold Di in Hz. rewrite PCr in Hz. lia. }
  idtac "pc:2".
  assert (SiR : ag_spacebeg (aa_geom A) <= Si /\ Si + 4 <= ag_spacebeg (aa_geom A) + 137438953472) by (unfold Si; rewrite FAr; lia).
  assert (DiR : ag_thread (aa_geom A) + 288 <= Di /\ Di + 4 <= ag_thread (aa_geom A) + 2656) by (unfold Di; rewrite PCr; lia).
  assert (HS1 : SPA segs (JRpop i) CT0 r1 tp w) by (split; [exact HsmA1 | exact HJ1]).
  apply (SPA_carve_list segs _ r1 CT0 tp w NPOP PNX1 HS1 W_t1).
  - apply Pos.eqb_eq in NX_t. rewrite NX_t. unfold PNX, PNX1. lia.
  - unfold NPOP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite ES. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
      split.
      { intros off Hoff. rewrite Erm1. specialize (MS (Z.to_nat off) ltac:(lia)). replace (Si + Z.of_nat (Z.to_nat off)) with (Si + off) in MS by lia.
        unfold m1 in MS. rewrite Erm1 in MS. rewrite view_in in MS by lia. eapply wok_rd_off_image; [|exact MS]. lia. }
      split; [|unfold xwords_clear; rewrite XX_t; intros rr y j []].
      apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. rewrite E7. specialize (MS j Hj). unfold m1 in MS. rewrite view_in in MS by lia.
      replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) by lia. exact MS.
    + rewrite ED. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply Forall_nil|].
      split.
      { intros off Hoff. destruct (PD (Di + off) ltac:(lia)) as [b Hb]. unfold m1 in Hb. rewrite view_in in Hb by lia.
        eapply wok_rd_off_image2; [| |exact Hb]; lia. }
      split; [apply Forall_nil | unfold xwords_clear; rewrite XX_t; intros rr y j []].
  - cbn [map carve_obj NPOP]. unfold carved.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite obj_range_mk by lia; rewrite ?ES, ?ED; rewrite EO; apply Forall_app; split.
    + apply BZ. right; left. rewrite kSpaceSize_val. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; lia.
    + apply BZ. left. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; unfold Di in *; rewrite ?PCr in *; lia.
  - cbn [map carve_obj NPOP pairwise_disjoint]. unfold carved. split; [|split; [constructor | exact I]].
    apply Forall_cons; [|apply Forall_nil]. rewrite !obj_range_mk by lia. rewrite ES, ED. unfold ranges_disjoint; cbn [fst snd]. lia.
Qed.

Lemma e_end_val : ltac2:(tb__ "0|0|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S0S37Q40S13R3S4dA2A2S1eS1eS53VA;Vrb;A2Z10A2S21Z4Vk;A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  unfold e_end, vK. cbn [eval]. rewrite add_val, add_val, sll_val. rewrite EB, Q227, !u64_lit by lia. change (2 mod 64) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite (Z.mod_small (PCE A rb + 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition JRrel (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6aA1S69S3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eVi;Z1A2A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").

Lemma pop_iter : ltac2:(tb__ "0|1|
S0S7S27S35Q40A1A1S6fS3S1fZ0R4A2S20R4Vk;A2A2S20S1eR5Z1M0A2Vk;A2S7VTR;S47S34S49S1eR7G0A2A1VCT0;R1R5A5R4A2Fr';F_;S2S0S1eR6G0A2Vk;A3S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R6A5R5A2Fr';F_;VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx.
  assert (NUM : 0 <= PCE A rb /\ PCE A rb + 16 + 4 * k + 8 < 2 ^ 62 /\ 1 <= k <= 8).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & _ & (T1 & T2 & _) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia. }
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0).
  set (r1 := rho_sets r [(PV7, Z_to_bv 64 idv)]).
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop i) CT1 r1 tp)); [intros w Hw; exact (proj1 (pop_carve i r tp w Hi Hw))|].
  apply (tr_run Kc TR KIT F [0x413dc; 0x413f0] CT1 [LB; LX] (JRpop i) r1 tp Q (JRpop_K i) (JRpop_stable i (ss_next (ax_S CT1)) eq_refl) R_t1 LN_t1).
  intros L r2 HL Hag.
  assert (NX1 : ss_next (ax_S CT1) = PNX1) by reflexivity. rewrite NX1 in Hag.
  assert (E72 : rw r2 PV7 = Z_to_bv 64 idv) by (destruct Hag as (Hw & _); rewrite <- (Hw PV7) by (unfold PV7, PNX1; lia); exact E7).

  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nob (ss_objs (ax_S (la_state LL))) ++ [O_srcc; O_dstc] ->
            forall w, SPA segs (JRpop i) (la_state LL) r2 tp w -> exists r3, SPA segs (JRrel i) (keepn (la_state LL) nob) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_srcc; O_dstc] (vms md tp ms)).
    apply (SPA_unobj_J (JRpop i) (JRrel i) r2 (la_state LL) _ [O_srcc; O_dstc] tp tr ms md HO Hw).
    intros Hsm HJ. pose proof HJ as (_ & H4 & H6).
    destruct (pop_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm E72 HJ) as (P1 & P2 & P3). cbn zeta in P1, P2, P3.
    split; [exact P1|]. split; [rewrite P2; exact H4 | rewrite P3; exact H6]. }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply negb_true_iff in BF. apply Z.eqb_neq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Hlt.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LB) nob) r3 tp) Q (REL LB OB_b)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRpop (i + 1)) CT0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J (JRrel i) (JRpop (i + 1)) _ CT0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & H4 & H6). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs.
    split; [|split].
    + eapply (JR_stable A Kc rb tp0 md0 (phK (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk4. cbn [eval]. rewrite H4. apply bv_eq. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
    + cbn [rho_sub rw]. rewrite S_bk6. cbn [eval]. rewrite H6. apply bv_eq.
      assert (FAR : 0 <= FAb A rb /\ FAb A rb + 536870912 + 8 < 2 ^ 62).
      { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
        destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
        unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
      rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply not_true_is_false in BF. apply negb_false_iff in BF. apply Z.eqb_eq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LX) nob) r3 tp) Q (REL LX OB_x)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phK k)) (keepn (la_state LX) nob) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J (JRrel i) (JRp (phK k)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma pop_loop : ltac2:(tb__ "0|0|
S2eS0S7S27S35Q40A1A1S6fS2S0S22Vk;R4A2S24R5A1A3S3S1fZ0R5A2S20R5Vk;A2A2S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R5A5R4A2Fr';VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [lia|].
  apply (pop_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [lia | lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variable J0 : axst.
Variable LT0 : leafA.
Variable s_in : wsub.
Variable e_src : sv.
Hypothesis R_t0 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z413dcS26S0Z413f0S28S0A1A3A3VJ0;S2aA5S31G0S26S3aVLT0;S28S3aA1A3A2A3").
Hypothesis LN_t0 : ltac2:(tb__ "0|0|
S2S29S16S38VJ0;A1A1S2dA3").
Hypothesis NX_t0 : ltac2:(tb__ "0|0|
S2S29S7fS41S17S38VJ0;A1A1A2S2aA3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S2S29S3bS39VLT0;A1VCT0;Vs_in;A3S2aA3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S2S29S6dVs_in;S41A2S2aA3").
Hypothesis S_in4 : ltac2:(tb__ "0|0|
S2S8S6bVs_in;S3dA2ScS4eS78SaZ10A1A3A3").
Hypothesis S_in6 : ltac2:(tb__ "0|0|
S2S8S6bVs_in;S3eA2Ve_src;A3").
Hypothesis HSRCP : ltac2:(tb__ "0|1|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S35Q40M0A1S13R3Ve_src;A2S36G0S1eS52VA;Vrb;A2S21Z4S22VnfP;Vk;A2A2A2A2A3F_;F_;Fr;").

Lemma phK0 : phK 0 = ph.
Proof.
  destruct PH0 as (P1 & P2 & P3).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phK; rewrite P1, P2, P3; reflexivity | symmetry; apply ph_eta].
Qed.

Lemma pop_all : ltac2:(tb__ "0|0|
S7S27S35Q40A1A1S6fS7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R3A5R2A2Fr';VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VJ0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x413dc; 0x413f0] J0 [LT0] ph r tp Q R_t0 LN_t0 NX_t0).
  intros L r1 [<-|[]] _.
  assert (K1 : 1 <= k).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1. lia. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop 0) CT0 (rho_sub r1 s_in) tp)); [|apply (pop_loop (Z.to_nat k) 0 _ tp Q); [lia | lia | exact HX]].
  intros w Hw. apply (SPA_entails_J (JRp ph) (JRpop 0) _ CT0 s_in r1 tp w ENT_in); [|exact Hw].
  intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
  split; [|split].
  - rewrite phK0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
  - cbn [rho_sub rw]. rewrite S_in4. cbn [eval].
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & _).
    apply bv_eq. rewrite add_val, EB, !u64_lit.
    + rewrite Z.mod_small; [lia|]. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + lia.
  - cbn [rho_sub rw]. rewrite S_in6. rewrite (HSRCP r1 HFz HGh). f_equal. lia.
Qed.
End POP.
End SpineMallocQ3.

(* [comment removed for export] *)
Module SpineCallocR5.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cls_keptA"; "cs_cache"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cls"; "aa_fs_busy"; "aa_geom"; "aa_live"; "class_fresh"; "class_state"; "ageom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "prod"; "true"; "nat"; "orb"; "cons"; "nil"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "sv"; "SVar"; "mkVal"; "rl"; "sv_eqb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "KcA"; "JL_malloc_ok"; "AE_A"; "JL_malloc_null"; "client_addrA"; "client_shadowA"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "rho_after"; "same_client"; "posts_conv"; "sx_okb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "rhoM_of"; "chk_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "refill_cs"; "kchunks"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "vCHX"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "of_nat"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "to_nat"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5.PCONV"; "PF_malloc"; "PF_ok"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition sx_okb (s : wsub) : bool := ltac2:(tb__ "0|0|
S5dS18S18S53R1A1S12S19S19S25S34Vs;R1A2S22R1A1A2S51R1P95A2A2S51R1P9fA2A2Ti;Ln;S59U1U9fA2A3").
Lemma sx_ok_id : ltac2:(tb__ "0|0|
S35S12S0S15S3cR2A1S17A3S52R2S29A2S2S0S12R3P95A3A1S2S0S12R4P9fA3A1S0S21S34R6R5A2S22R5A1A3F_;F_;F_;F_;Fi;Fs;").
Proof.
  intros s i H Hi H1 H2. unfold sx_okb in H.
  pose proof (proj1 (forallb_forall _ _) H (Pos.to_nat i) ltac:(apply in_seq; unfold GW in Hi; lia)) as X. cbv beta zeta in X. rewrite Pos2Nat.id in X.
  apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|].
  - apply sv_eqb_sound in X. exact X.
  - apply Pos.eqb_eq in X. contradiction.
  - apply Pos.eqb_eq in X. contradiction.
Qed.

Definition rho_after (rho r : valuation) : valuation := ltac2:(tb__ "0|0|
S23S20Vrho;A1S24Vrho;A1S1fVr;A1A3").

Lemma rhoM_refill : ltac2:(tb__ "0|0|
S4S1eS1eS11S12S2S0S12R1P95A3A1S2S0S12R2P9fA3A1S0S26Q40A1S20S43S48R7R4A2S39R6R5A2A2R3A2S20S43R7R6A2R3A2A3F_;F_;Fi;Fc;Fr;Frho;FA;").
Proof.
  intros A rho r c i H1 H2. unfold rhoM_of, rho_sets. cbn [rw rho_set_rw rho_after aa_geom refillA aa_ptr_committed aa_sec].
  repeat match goal with |- context [Pos.eqb i ?kk] => destruct (Pos.eqb_spec i kk); [try reflexivity; try contradiction|] end.
  reflexivity.
Qed.

Lemma cnt_of_refill : ltac2:(tb__ "0|1|
S4S11S4bS56S41R1A1A1S14SfSaR2A1A2A2S0S11S45S48R3S41R2A1M0A2R2A2S55S14S11S6S49G0S42R3R2A2A2A1A2A1A3F_;Fn;FA;").
Proof. intros A n H. unfold cnt_of, cst_of, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact H. reflexivity. Qed.
Lemma chk_of_refill : ltac2:(tb__ "0|1|
S4S11S4bS56S41R1A1A1S14SfSaR2A1A2A2S0S11S44S48R3S41R2A1M0A2R2A2S6S49G0S42R3R2A2A2A1S13S11A1S58S11S57S14S11R1A2U1A2R1Z0A4Tl;A3F_;Fn;FA;").
Proof. intros A n H. unfold chk_of, cst_of, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact H. reflexivity. Qed.

Definition same_client (A Ar : AA) : Prop := ltac2:(tb__ "0|1|
S1S0S10ScVAr;A1ScVA;A1A3S1S0S13S16S11S11A2A1M0SdVAr;A1SdVA;A1A3S1S0S13G0A1SbVAr;A1SbVA;A1A3S1S0S11S9VAr;A1S9VA;A1A3S1S0S11S8VAr;A1S8VA;A1A3S0S11S7VAr;A1S7VA;A1A3A2A2A2A2A2").

Definition posts_conv (CST XGL : list (Z * Z)) (PFam : AA -> KcA -> list (axst * jpostA)) : Prop := ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1G1S4cS3aR8R7A2S2aVCST;VXGL;R9R8S1fR6A1S1fR5A1A6S4S5RaR1S27G0S20R8PcM2A2A2A3S5RcR2S27G0S20R9G2A2A2A3F_;FA';S37S28S33S39R8R7A2R6VPFam;RaR9A2R4A6S37S28S33R9R6VPFam;RcRaA2R5A6F_;F_;F_;F_;Fw;Ftp0;Ftp;Fr;Frho;FKc;FAr;FA;").

Section PCONV.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (W : list ulink) (st : ustop).

Lemma client_same : ltac2:(tb__ "0|0|
S4S4S3aR2R1A2S11S3S2fVCST;R3R1A3S2fVCST;R4R1A3A2Fa;F_;FAr;FA;").
Proof.
  intros A Ar (EG & EL & EF & _) a. unfold client_addrA, client_mut_addrA, aa_frames. rewrite EG, EL, EF. reflexivity.
Qed.
Lemma shadow_same : ltac2:(tb__ "0|0|
S4S4S3aR2R1A2S11S3S30VCST;VXGL;R3R1A4S30VCST;VXGL;R4R1A4A2Fa;F_;FAr;FA;").
Proof.
  intros A Ar HS a. unfold client_shadowA. split; (intros [(x & Hx & E)|H]; [left; exists x; split; [apply (client_same A Ar HS); exact Hx | exact E] | right; exact H]).
Qed.

Lemma mem_kept_trans : ltac2:(tb__ "0|2|
S4S4S4S26Q40A1S1cS26Q8A1A1F_;M0G0G0S3aR6R5A2S2aVCST;VXGL;R7R6R4R3A6M1G1S2aVCST;VXGL;R9R7R6R4A6F_;F_;F_;Fm2;Fm1;Fm0;FA';FAr;FA;").
Proof.
  intros A Ar A' m0 m1 m2 HS [K1 K2] [K1' K2']. split.
  - intros a Ha [(H1 & H2 & H3)|(H1 & H2 & H3)].
    + pose proof (proj2 (client_same A Ar HS a) H1) as H1r.
      rewrite (K1' a Ha (or_introl (conj H1r (conj H2 H3)))). exact (K1 a Ha (or_introl (conj H1 (conj H1r H3)))).
    + pose proof (proj2 (shadow_same A Ar HS a) H1) as H1r.
      assert (E1 : m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) by exact (K1 a Ha (or_intror (conj H1 (conj H1r H3)))).
      assert (D1 : m1 (Z_to_bv 64 a) <> None) by (rewrite E1; exact H3).
      rewrite (K1' a Ha (or_intror (conj H1r (conj H2 D1)))). exact E1.
  - intros x j Hx Hj Hd.
    assert (Hxr : client_addrA CST A x /\ client_addrA CST Ar x \/ in_rangesZ XGL x).
    { destruct Hx as [[X1 X2]|X]; [left; split; [exact X1 | apply (client_same A Ar HS); exact X1] | right; exact X]. }
    apply (K2' x j); [destruct Hx as [[X1 X2]|X]; [left; split; [apply (client_same A Ar HS); exact X1 | exact X2] | right; exact X] | exact Hj|].
    exact (K2 x j Hxr Hj Hd).
Qed.

Lemma conv_null : ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1S1eG1S13S3eA1S3dS3aRaR9A2S2aVCST;VXGL;RbRaS1fR8A1S1fR7A1A6S4S5RcR1S27G0S20RaPcM2A2A2A3S5ReR2S27G0S20RbG2A2A2A3F_;FA';G1S2eVAInv;VCST;VXGL;RdRcS39RbRaA2R1R8R7R6R5AbS2eVAInv;VCST;VXGL;RfRdRcRaR9R8R7R6AbF_;Ftpx;F_;F_;F_;Fmd;Ftr;Ftp';Frho';Ftp0;Fr;Frho;FKc;FAr;FA;").
Proof.
  intros A Ar Kc rho r tp0 rho' tp' tr md HS HM0 HCK tpx (A' & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10).
  pose proof HS as (EG & EL & EF & EV & EKm & EKf). cbn [rho_after rw rm] in J4, J8, J10.
  exists A'. split; [exact J1|]. split; [rewrite J2; exact EL|]. split; [rewrite J3; unfold aa_frames; rewrite EF; reflexivity|].
  split; [rewrite J4, EV; reflexivity|]. split; [rewrite J5, EKm; reflexivity|]. split; [rewrite J6; exact EKf|]. split; [rewrite J7; exact EG|].
  split; [exact (mem_kept_trans A Ar A' _ _ _ HS HM0 J8)|]. split; [exact J9 | exact (HCK A' J10)].
Qed.
Lemma conv_ok : ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1S1eG1S13S3eA1S3dS3aRaR9A2S2aVCST;VXGL;RbRaS1fR8A1S1fR7A1A6S4S5RcR1S27G0S20RaPcM2A2A2A3S5ReR2S27G0S20RbG2A2A2A3F_;FA';G1S2cVAInv;VCST;VXGL;RdRcS39RbRaA2R1R8R7R6R5AbS2cVAInv;VCST;VXGL;RfRdRcRaR9R8R7R6AbF_;Ftpx;F_;F_;F_;Fmd;Ftr;Ftp';Frho';Ftp0;Fr;Frho;FKc;FAr;FA;").
Proof.
  intros A Ar Kc rho r tp0 rho' tp' tr md HS HM0 HCK tpx (A' & l1 & l2 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
  pose proof HS as (EG & EL & EF & EV & EKm & EKf). cbn [rho_after rw rm] in J2, J5, J9, J11.
  exists A', l1, l2. split; [exact J1|]. split; [exact J2|]. split; [rewrite <- EL; exact J3|]. split; [rewrite J4; unfold aa_frames; rewrite EF; reflexivity|].
  split; [rewrite J5, EV; reflexivity|]. split; [rewrite J6, EKm; reflexivity|]. split; [rewrite J7; exact EKf|]. split; [rewrite J8; exact EG|].
  split; [exact (mem_kept_trans A Ar A' _ _ _ HS HM0 J9)|]. split; [exact J10 | exact (HCK A' J11)].
Qed.

Definition PF_malloc : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|0|
S4S2bS32S2dVAInv;VCST;VXGL;VW;Vst;R2R1A8LKc;LA;").
Definition PF_ok : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|1|
S4S2bS1aS16S46S38A2M0S1dS46S38S31S2dVW;Vst;A3S2cVAInv;VCST;VXGL;R2R1A5A4S1bG0A1A3LKc;LA;").
Lemma posts_conv_malloc : ltac2:(tb__ "0|0|
S3bVCST;VXGL;S5bA3").
Proof.
  intros A Ar Kc rho r tp tp0 w HS HM0 HCK (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PF_malloc, Posts_malloc in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
  - exists (L_malloc_null AE_A W st), (JL_malloc_null AInv CST XGL A Kc), rho', tp'.
    split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_null A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
  - exists (L_malloc_ok AE_A W st), (JL_malloc_ok AInv CST XGL A Kc), rho', tp'.
    split; [right; left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_ok A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
Qed.
Lemma posts_conv_ok : ltac2:(tb__ "0|0|
S3bVCST;VXGL;S5cA3").
Proof.
  intros A Ar Kc rho r tp tp0 w HS HM0 HCK (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PF_ok in Hin. destruct Hin as [E|[]]; injection E as <- <-.
  exists (L_malloc_ok AE_A W st), (JL_malloc_ok AInv CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_ok A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
Qed.
End PCONV.

Section FINAL.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S4S2bS13S16S46S38A2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S3bVCST;VXGL;VPFam;A3").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S40VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let Ar : AA := refillA A c.
Variable phF : phase.

Hypothesis HREB : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S13S3eA1S3dS3fVA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS5aS28VAr;R5R4R2A5F_;Fmd;Ftr;Ftp;Fr;").
Hypothesis HMK : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S13S3eA1S3dS3fVA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS2aVCST;VXGL;VA;VAr;S1fVrb;A1S1fR5A1A6F_;Fmd;Ftr;Ftp;Fr;").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S11S55S14S11S6S49Vc;S42VA;Vnv;A2A2A1A2A1S4aVc;A1A3").

Lemma refill_fresh : ltac2:(tb__ "0|0|
S11S1S54Z1R1A2S54R1Z1eA2A2S2S0S11R2Vc;A3A1SeVA;R3A2SeVAr;R4A2F_;F_;F_;Fc';").
Proof.
  intros c' Hc' Hne Hf. unfold class_fresh, Ar, refillA in *. cbn [aa_cls].
  rewrite nth_list_upd_other; [exact Hf|]. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _). lia.
Qed.

Lemma JG_after : ltac2:(tb__ "0|0|
S35S1eS13S26Q40A1A1S13S3eA1S3dS0S15S3cR5A1S17A3S0S21S34R6P95A2S4fA3S0S21S34R7P9fA2S4eA3S3fVA;VKc;Vrb;Vtp0;Vmd0;VphF;R7R6R5R4AaS50VW;Vst;VAr;VKc;S39Vrho;R8A2S36R8R9A2R7R6R5A9F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fs_x;").
Proof.
  intros s_x r tp tr md HSX H149 H159 HJ. pose proof HJ as (HFz & HGh & HK' & _ & _).
  pose proof HE as (Hag & HA & Htp & HU & HB & Hnv & Htop & Hcnt & _). destruct Hag as (Hagw & Hagl & Hagm). destruct HFz as [Fw Fl].
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (RWid : forall i, (i < GW)%positive -> i <> 149%positive -> i <> 159%positive -> rw (rho_sub r s_x) i = rw (rhoM_of A rho) i).
  { intros i Hi H1 H2. cbn [rho_sub rw]. rewrite (sx_ok_id s_x i HSX Hi H1 H2). cbn [eval]. rewrite <- (Fw i) by (unfold GW in Hi; lia). symmetry. apply Hagw. exact Hi. }
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _ & Q229). fold nv c in Q227.
  assert (HL32 : (Z.to_nat (cls_of nv) < length (aa_cls A))%nat).
  { pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (L32 & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv in CF. destruct CF as ((_ & C1 & _) & _). rewrite L32. lia. }
  split.
  -
    split; [|split].
    + intros i Hi. destruct (Pos.eq_dec i 149) as [->|N1]; [|destruct (Pos.eq_dec i 159) as [->|N2]].
      * cbn [rho_sub rw]. rewrite H149. unfold vK. cbn [eval]. rewrite Q227.
        change (rw (rhoM_of Ar (rho_after rho r)) 149%positive) with (Z_to_bv 64 (cnt_of Ar (bv_unsigned (rw rho 12%positive)))).
        rewrite <- E12. fold nv. unfold Ar, c. rewrite (cnt_of_refill A nv HL32). fold c. rewrite HLEN. reflexivity.
      * cbn [rho_sub rw]. rewrite H159. unfold vCHX. cbn [eval]. rewrite Q229.
        change (rw (rhoM_of Ar (rho_after rho r)) 159%positive) with (Z_to_bv 64 (chk_of Ar (bv_unsigned (rw rho 12%positive)))).
        rewrite <- E12. fold nv. unfold Ar, c. rewrite (chk_of_refill A nv HL32). reflexivity.
      * rewrite (RWid i Hi N1 N2). apply rhoM_refill; assumption.
    + intros l. unfold rhoM_of. rewrite rl_rho_sets. cbn [rho_after rl rho_sub]. rewrite <- Fl. rewrite <- Hagl. unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
    + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
  -
    assert (R12 : rw (rho_sub r s_x) 12%positive = rw rb 12%positive) by (rewrite (RWid 12%positive) by (unfold GW; lia); apply Hagw; unfold GW; lia).
    split; [|split; [exact HK'|split; [|split; [|split; [|split]]]]].
    + apply (AInvA_view Ar r (rho_sub r s_x) tp md (HREB r tp tr md HJ)). intros a. reflexivity.
    + unfold tp_ok in *. rewrite (RWid 24%positive) by (unfold GW; lia). rewrite (Hagw 24%positive) by (unfold GW; lia). exact Htp.
    + apply (HW rb (rho_sub r s_x)); [|exact HU]. intros i Hi. assert (Hi' : (i < GW)%positive) by (unfold NF in Hi; unfold GW; lia).
      rewrite (RWid i Hi') by (intros ->; unfold NF in Hi; lia). apply Hagw. exact Hi'.
    + cbn [eval]. rewrite R12. fold nv. exact HB.
    + cbn [eval]. rewrite R12. fold nv. lia.
    + unfold top_high in *. rewrite (RWid 10%positive) by (unfold GW; lia). rewrite (RWid V_DEPTH) by (unfold GW, V_DEPTH; lia).
      rewrite (Hagw 10%positive) by (unfold GW; lia). rewrite (Hagw V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma posts_after : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S4cS2aVCST;VXGL;VA;VAr;S1fVrho;A1S1fR3A1A6S37S28S33S39Vrho;R4A2R3VPFam;VAr;VKc;A2R2A6S37S28S33Vrho;Vtp0;VPFam;VA;VKc;A2R3A6F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w HM0 H.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((Hnv & C1 & _) & _).
  pose proof HE as (HagE & _). destruct HagE as (Hagw & _ & _).
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (Ecls : ClassID (needed (bv_unsigned (rw rho 12%positive))) = c) by (rewrite <- E12; fold nv; exact (proj1 (cls_needed nv Hnv))).
  apply (HPF A Ar Kc rho r tp tp0 w); [repeat split; reflexivity | exact HM0 | | exact H].
  intros A' HCK c' Hc' Hn Hf. apply (HCK c' Hc' Hn). apply refill_fresh; [exact Hc'| |exact Hf].
  destruct Hn as [Hn|Hn]; [rewrite <- E12 in Hn; fold nv in Hn; lia | rewrite Ecls in Hn; exact Hn].
Qed.

Variables (E3P EZ : axst) (s_x : wsub).
Hypothesis ENT_x : ltac2:(tb__ "0|0|
S0S15S47VEZ;VE3P;Vs_x;A3S17A3").
Hypothesis SX_x : sx_okb s_x = true.
Hypothesis S149_x : ltac2:(tb__ "0|0|
S0S21S34Vs_x;P95A2S4fA3").
Hypothesis S159_x : ltac2:(tb__ "0|0|
S0S21S34Vs_x;P9fA2S4eA3").

Hypothesis HPOP : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S1eVTR;S4dS28S50VW;Vst;VAr;VKc;R3A5VE3P;R1R2A5S37S28S33R3R2VPFam;VAr;VKc;A2A5A2FrX;Ftp';Frho';").

Theorem refill_back : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1VTR;S4dS28S3fVA;VKc;Vrb;Vtp0;Vmd0;VphF;A6VEZ;R2R1A5S37S28S33Vrho;Vtp0;VPFam;VA;VKc;A2A5A2Ftp;Fr;").
Proof.
  intros r tp.
  assert (Erm : rm rb = rm rho).
  { destruct HE as ((_ & _ & Hm) & _). apply functional_extensionality. intros a. rewrite <- (Hm a). unfold rhoM_of. rewrite rm_rho_sets. reflexivity. }
  apply (tr_pure Kc TR KIT (mem_keptA CST XGL A Ar (rm rho) (rm r))).
  { intros w [_ HJ]. rewrite <- Erm. exact (HMK r tp _ _ HJ). }
  intros HM0.
  apply (tr_post Kc TR KIT _ _ _ (fun w Hw => posts_after r tp w HM0 Hw)).
  apply (tr_pre Kc TR KIT (SPA segs (JG W st Ar Kc (rho_after rho r)) E3P (rho_sub r s_x) tp)); [|apply HPOP].
  intros w Hw. apply (SPA_entails_J (JRp phF) (JG W st Ar Kc (rho_after rho r)) EZ E3P s_x r tp w ENT_x); [|exact Hw].
  intros HJ. exact (JG_after s_x r tp _ _ SX_x S149_x S159_x HJ).
Qed.
End FINAL.
End SpineCallocR5.

(* [comment removed for export] *)
Module SpineCallocR12.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "div"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "length"; "list"; "nil"; "Some"; "option"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "eval"; "ss_next"; "sv"; "sprop"; "valuation"; "ss_facts"; "ss_lenient"; "SMd"; "SPNot"; "SVar"; "holds"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "gh_new"; "JR"; "entryR"; "ghosts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_free_array"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_mapped_user"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "vNEW"; "GR"; "F_new"; "cD"; "vAU"; "vMFA"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12"; "F_geu"; "need_e"; "new_e"; "facap_okb"; "rup_e"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "CLS30"; "FACAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws PrimCredit PrimCreditLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition new_e : sv := ltac2:(tb__ "0|0|
S25S37S1cS36S1cS33S3fS1dZ40000A1A3S3dA3S27S4eA1A3").
Definition need_e : sv := ltac2:(tb__ "0|0|
S1cS35S1cS33S40S39A3S1dZ2A1A3").
Definition F_geu : sprop := SPBranch BC_GEU vMFA need_e.
Definition rup_e : sv := ltac2:(tb__ "0|0|
S1cS34S1cS33S42S1dZ3ffffA1A3S1dZfffffffffffc0000A1A3").

Definition facap_okb (c : Z) : bool := FACAP c <=? 536608768.
Lemma facap_okb_all : ltac2:(tb__ "0|0|
S2S11S49S0S44S50A3S13A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma facap_room : ltac2:(tb__ "0|0|
S0S1S5Z1R1A2S5R1Z1eA2A2S5S51R2A1Z1ffc0000A2F_;Fc;").
Proof. intros c Hc. pose proof (proj1 (forallb_forall _ _) facap_okb_all c (proj2 (In_CLS30 c) Hc)) as H. apply Z.leb_le in H. exact H. Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S53VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S2dVA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma new_nums : ltac2:(tb__ "0|5|
S4fVc;A1S0S8S14S0S2fVcs;A1A2A1S0S31Vcs;A1S0S32Vcs;A1S0S30Vcs;A1S0S2aVA;Vrb;A2S0S1S1S5Z20R6A2S5R6Z10000A2A2S1S1S5Z0M0R4A2S5R4R3A2A2S1S5R3Zdffc0000A2S1S1S5Z4M1R1A2S5R1Z2001A2A2S1S5S52Vc;A1R1A2S1S5S6R4S7R1R6A2A2M2S6R3Z40000M3A2M4A2S1S9G4S6G2R6A2A2S1S5G0R5A2S1S5S7G1R5A2R2A2S1S5R2Z1ffc0000A2S1S2S0SbR2G3A2G0A3S2S0R1SaScG4R4A2R6A2A3A2A2A2A2A2A2A2A2A2A2A2Tnew;Tmfa;Tmu;Tau;Tnf;TS;").
Proof.
  intros S nf au mu mfa new.
  destruct (pop_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8. fold nv c cs in N1, N2, N3, N4, N5, N6, N7, N8. fold S nf au mu in N1, N2, N3, N4, N5, N6, N7, N8.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as ((_ & C1 & _) & (_ & _ & K3) & _ & (MF0 & MF1) & (_ & FC0 & _) & _). fold S in K3. fold nf mfa in MF0, MF1, FC0.
  pose proof (facap_room c C1) as FR.
  assert (EN : new = (mu + 262144 - au) / S) by (unfold new, gh_new, kUserMapSize; fold nv c cs; reflexivity).
  pose proof (Z.div_mod (mu + 262144 - au) S ltac:(clear -N1; lia)) as DM. pose proof (Z.mod_pos_bound (mu + 262144 - au) S ltac:(clear -N1; lia)) as MB.
  rewrite <- EN in DM. clearbody new.
  assert (Q1 : 262144 - S < new * S <= 262144 + S) by (clear -DM MB N4 N6 N1; nia).
  assert (Q2 : 4 <= new <= 8193) by (clear -Q1 N1; nia).
  assert (Q3 : kchunks c <= new) by (clear -Q1 N1 N2 K3; nia).
  split; [exact N1|]. split; [exact N4|]. split; [exact N5|]. split; [exact Q2|]. split; [exact Q3|].
  split; [clear -DM MB; nia|]. split; [clear -DM MB; nia|]. split; [clear -N3; lia|]. split; [clear -MF1; lia|]. split; [clear -FC0 FR; lia|]. split; [exact MF0 | exact EN].
Qed.

Lemma new_val : ltac2:(tb__ "0|0|
S2S46Q40A1S1eVr;S43A2S1eVr;S39A2A3").
Proof.
  destruct new_nums as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & _ & _ & EN). cbn zeta in N1, N2, N3, N4, EN. fold nv c cs in N1, N2, N3, N4, EN.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & _ & _ & Q223 & Q224 & _ & _ & _ & Q228 & _). fold nv c cs in Q223, Q224.
  unfold new_e, vMU, vAU, vNEW, V_SIZE. cbn [eval]. apply bv_eq. rewrite divu_val by (rewrite E148, u64_lit; clear -N1; lia).
  rewrite sub_val, add_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N3 N4; lia).
  rewrite (Z.mod_small (cs_mapped_user cs + 262144)) by (clear -N2 N3; lia). rewrite Z.mod_small by (clear -N2 N3; lia). symmetry. exact EN.
Qed.

Lemma F_new_hold : Forall (holds r) F_new.
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _ & _ & _ & _ & _ & Q228 & _). fold nv c cs in Q222.
  unfold F_new. repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; unfold vNEW, vMFA; cbn [eval]; rewrite ?Q222, ?Q228, ?u64_lit by (clear -N4 N8 N9 N10; lia).
  - clear -N4; lia.
  - clear -N4; lia.
  - exact N10.
  - split; [clear; lia | change (2 ^ 18) with 262144; exact N11].
Qed.

Lemma need_val : ltac2:(tb__ "0|0|
S2S0S47Q40S1eVr;S42A2A2S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A3").
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N4, N8, N9, N10. fold nv c cs in N4, N8, N9, N10.
  destruct GH as (_ & Q221 & _ & _ & _ & _ & _ & _ & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221.
  unfold need_e, vNF, vNEW. cbn [eval]. rewrite sll_val, add_val, Q221, Q228, !u64_lit by (clear -N4 N8 N9 N10; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ + _)) by (clear -N4 N8 N9 N10; lia).
  rewrite Z.mod_small by (clear -N4 N8 N9 N10; lia). clear; lia.
Qed.

Lemma geu_iff : ltac2:(tb__ "0|0|
S4S28Vr;S41A2S3S9S30Vcs;A1S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A2A1A2").
Proof.
  destruct new_nums as (_ & _ & _ & _ & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N8, N9, N10. fold nv c cs in N8, N9, N10.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  unfold F_geu. cbn [holds]. unfold branch_taken, bv_ltu. rewrite need_val. unfold vMFA. cbn [eval]. rewrite Q222, u64_lit by (clear -N8 N9 N10; lia).
  rewrite negb_true_iff, Z.ltb_ge. clear; lia.
Qed.

Lemma rup_val : ltac2:(tb__ "0|0|
S9S30Vcs;A1S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A2S2S46Q40A1S1eVr;S45A2S1eVr;S1cS33S3eS1dZ40000A1A3A2A3F_;").
Proof.
  intros HLT. pose proof need_val as NV.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  set (need := 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)) in *. set (mfa := cs_mapped_free_array cs) in *.
  unfold rup_e. cbn [eval]. apply bv_eq. rewrite and_val, !add_val, NV. unfold vMFA. cbn [eval]. rewrite Q222.
  replace (bv_unsigned (Z_to_bv 64 18446744073709289472)) with 18446744073709289472 by reflexivity. rewrite !u64_lit by (clear -N9 N10; lia).
  rewrite (Z.mod_small (need + 262143)) by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite land_m18_up by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite (Z.mod_small (mfa + 262144)) by (clear -N9 N10 N8; lia).
  destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) N11) as [q Hq].
  assert (E : (need + 262143) / 262144 = q + 1).
  { symmetry. apply Z.div_unique with (need + 262143 - (q + 1) * 262144); [left; unfold need in *; clear -HLT Hq N4 N9; lia | clear; lia]. }
  rewrite E, Hq. clear; lia.
Qed.
End VALS.

Section POPMID.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S2cVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let cs : class_state := cst_of A nv.
Variable ph : phase.

Variable F : nat.
Variables (E3 RU : axst) (LD LF0 LFm : leafA).
Let FR : list sprop := factsR E3.
Let CD : axst := ltac2:(tb__ "0|0|
S3cVFR;SeVLD;A1A2").
Hypothesis R_d : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2eVF;S12S0Z416f0S16S0A1A3VRU;S13A5S17G0S12SfVLD;S16SfA1A3A2A3").
Hypothesis LN_u : ltac2:(tb__ "0|0|
S2S11S24SdVRU;A1A1S19A3").
Hypothesis NX_u : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVRU;A1A1A2S13A3").
Hypothesis W_d : ltac2:(tb__ "0|0|
S2S11S29SdVCD;A1A1S13A3").
Hypothesis D_d : ltac2:(tb__ "0|4|
S2S18S1bS15S1bS20S20A2M0A1M1S15S21A1M2A2M3A1S4dSdSeVLD;A1A1SdVCD;A1A2S17G3S1aG1G2S12G0S1aS20S20S43S39A4S16G0A1A3S3bA4A2A3").
Hypothesis NX_d : ltac2:(tb__ "0|0|
S2S11S4bS1fSdVCD;A1A1S1fSdSeVLD;A1A1A1A2S13A3").
Hypothesis R_f : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2eVF;S12S0Z3f270S12S0Z4172cS16S0A1A3A3VCD;S13A5S17G0S12SfVLF0;S12SfVLFm;S16SfA1A3A3A2A3").
Hypothesis LN_d : ltac2:(tb__ "0|0|
S2S11S24SdVCD;A1A1S19A3").
Hypothesis NXr_d : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVCD;A1A1A2S13A3").
Hypothesis F0_in : ltac2:(tb__ "0|0|
S48S21S41S23SdSeVLF0;A1A1A1A3").
Hypothesis Fm_in : ltac2:(tb__ "0|0|
S48S21S26S41A1S23SdSeVLFm;A1A1A1A3").

Theorem populate_mid : ltac2:(tb__ "0|2|
S22S15S46Q40A1A1S4cS3S9S30Vcs;A1S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A2M0A1S22VTR;S38S2eS2bVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6M1SeVLF0;A1R1R4A5R3A2Fr';F_;G0S22VTR;S38S2eG1SeVLFm;A1R1R5A5R4A2Fr';F_;VTR;S38S2eG1VRU;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q H0 Hm.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x416f0] RU [LD] ph r tp Q R_d LN_u NX_u).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LD) (ax_S CD) _ _ ph r1 tp Q W_d D_d NX_d).
  { intros tr md (HFz & HGh & _) _. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. split.
    - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (new_val A rb r1 CF PF RG HGh).
    - exact (F_new_hold A rb r1 CF PF HGh). }
  change (ax_setS (la_state LD) (ax_S CD)) with CD.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3f270; 0x4172c] CD [LF0; LFm] ph r1 tp Q R_f LN_d NXr_d).
  intros L r2 [<-|[<-|[]]] _.
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ F0_in) as BF.
    apply (tr_pure Kc TR KIT (~ (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)))).
    { intros w [_ (HFz & HGh & _)]. exact (proj1 (geu_iff A rb r2 CF PF HGh) BF). }
    intros X. exact (H0 X r2).
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ Fm_in) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))).
    { intros w [_ (HFz & HGh & _)].
      destruct (Z_lt_dec (cs_mapped_free_array cs) (4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))) as [X|X]; [exact X|].
      exfalso. apply BF. exact (proj2 (geu_iff A rb r2 CF PF HGh) X). }
    intros X. exact (Hm X r2).
Qed.
End POPMID.
End SpineCallocR12.

(* [comment removed for export] *)
Module InvQ10.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "leb"; "ltb"; "lt"; "of_nat"; "mul"; "modulo"; "sub"; "@Corelib.Init.Datatypes"; "list"; "bool"; "option"; "prod"; "cons"; "false"; "andb"; "nat"; "snd"; "orb"; "app"; "true"; "Some"; "fst"; "length"; "pair"; "None"; "negb"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "AA"; "qbatch"; "sc_map_beg"; "aa_geom"; "aa_sec"; "mkQB"; "sc_map_size"; "ag_pab"; "ageom"; "aa_live"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "class_state"; "sc_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "bview"; "maskv"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "rw"; "mkVal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "AInvQ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "region_free"; "vm_maps"; "m_vm_lazy"; "map_has"; "map_remove"; "page_base"; "page_in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "is_primary"; "PG"; "Sh"; "HIGH_SHADOW_BEG"; "HIGH_SHADOW_END"; "LOW_SHADOW_BEG"; "SHADOW_GAP_BEG"; "kPtrArrayReserve"; "kSpaceSize"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "q_ids"; "qitems"; "@Stdlib.Lists.List"; "In"; "nth_error"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "q_pure"; "set_q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "KQ_sec"; "sec_junk_zone"; "chunk_zone"; "sec_tbl_zone"; "unmap_sec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "inv3"; "secondary_repr"; "class_repr"; "fs_footb"; "geom_ok"; "live_sep"; "model_inv"; "primary_repr"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.InvQ10a"; "L8text"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise"; "madvise_dontneed_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10"; "L8_holds"; "RZb"; "mixv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b"; "RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "apartW"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt SoundA SummaryA MmapFixedA MmapFixedA2 MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.RebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.InvQ10a OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma K0_parts : ltac2:(tb__ "0|2|
S51S25S41S11S3dQ40A1A1S11S48A1S47S45R6R5R4R3R2R1A6S3S71S28R6A1M0A1S3S72R6A1S3S74S3cS70G0A1S38S37S40R5A1A2A2M1R6A2S3S6eG1R6A2S3S64R6A1S3S6dR6A1S73S37R6R4R2A4A2A2A2A2A2A2F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md ((HG & _ & _ & HRest & HM & HI3 & _) & _). cbv zeta in HRest. destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  exact (conj HG (conj R1 (conj R3 (conj R4 (conj R5 (conj HI3 HM)))))).
Qed.

Lemma pab_fs : ltac2:(tb__ "0|1|
S25S3bS71S28R2A1A1S6eR2R3A2S6dR4A1S0S3S9S2cS28R6A1A1M0R1A2ScR1S8G0Z800000A2A2A2S2S12S70S28R7A1R2A2S16A3F_;Fz;F_;F_;F_;Fm;FA;").
Proof.
  intros A m HG HSR HI3 z Hz. destruct (pab_nums A m HSR) as (P1 & P2 & P3 & _).
  pose proof (geom_numsS _ HG) as (_ & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). rewrite FS_total_val in PF. unfold kPtrArrayReserve in PF.
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val, ?FS_kFlagsOffset_val; [lia | lia |].
  destruct (Z_lt_dec z (Sh (ag_fsb (aa_geom A) + 36864))) as [L|L]; [left; exact L | right].
  destruct (Z_le_dec (Sh (ag_fsb (aa_geom A) + 11571200)) z) as [R|R]; [exact R | exfalso].
  pose proof (sh_run_band2 (ag_fsb (aa_geom A) + 36864) (ag_fsb (aa_geom A) + 11571200) z ltac:(lia) ltac:(lia) ltac:(lia)) as B.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B. lia.
Qed.

Theorem K0_ks_repr : ltac2:(tb__ "0|0|
S51S25S41S11S3dQ40A1A1S11S48A1S47S45R6R5R4R3R2R1A6S6eS38S37S40R5A1A2R6A2F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md HK. destruct (K0_parts Kc A rho tp tr md HK) as (HG & HLS & HPR & HSR & HQP & HI3 & HM).
  set (mm := maskv (fs_footb (aa_geom A)) (view segsA (rm rho))) in *.
  assert (UM : forall z, fs_footb (aa_geom A) z = false -> view segsA (rm rho) z = mm z) by (intros z E; unfold mm, maskv; rewrite E; reflexivity).
  assert (CHK : forall j c z, nth_error (aa_sec A) j = Some c -> chunk_zone c z \/ chunk_sh_zone c z -> view segsA (rm rho) z = mm z).
  { intros j c z Hj Hz. apply UM. apply (RZ_fs A mm HG HSR HI3 j c Hj). right. right. exact Hz. }
  destruct (pab_nums A mm HSR) as (P1 & P2 & P3 & P4). pose proof HSR as (S1 & _ & S2 & _). unfold kPtrArrayReserve in S2.
  apply (secondary_repr_agree_gen mm (view segsA (rm rho)) A A eq_refl eq_refl eq_refl); [| | | | exact HSR].
  - intros j c z Hj Hz. apply (CHK j c z Hj). destruct (ch_nums A mm HSR j c Hj) as (_ & N2 & _).
    destruct Hz as [Hz|Hz]; [left; unfold chunk_zone; lia | right; exact Hz].
  - intros z Hz. apply UM. apply (pab_fs A mm HG HSR HI3). lia.
  - intros z Hz. apply UM. apply fs_footb_img; [exact HG | unfold SEC_INST in Hz; lia].
  - intros j c Hj. destruct (S1 j c Hj) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D13 & _).
    intros z Hz Hn. rewrite (CHK j c z Hj (or_introl Hz)). exact (D13 z Hz Hn).
Qed.

Theorem K0_ks_item : ltac2:(tb__ "0|1|
S51S25S41S11S3dQ40A1A1S11S48A1S47S45R6R5R4R3R2R1A6S14S0S0A2M0S60G0R1S5fS5dR7A1A1A3S2S12S53S19S0S0R2A3A1S16A3S6S18S18S6S24S24S3S2S13S24A1S61S24S29RbA1R2A3S1dS24R1A2A3S3S2S0S1eS0S0R5A3S8S8S27R1A1S54A2Z800A2A3S2S0S36R1A1S8S5cS19S0S0R5A3Z8A2Z1000A2A3A2A2Lch;A2Li;A2F_;F_;Fit;F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md HK it Hit EP. destruct (K0_parts Kc A rho tp tr md HK) as (_ & _ & _ & _ & (QF & _) & _).
  unfold qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit).
  pose proof (proj1 (Forall_forall _ _) QF b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (_ & _ & _ & IP4).
  destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi]. exists i, ch. exact (conj Hi (conj Eu Esz)).
Qed.

Theorem K0_ks_sep : ltac2:(tb__ "0|a|
S51S25S41S11S3dQ40A1A1S11S48A1S47S45R6R5R4R3R2R1A6S18S24S2S13S24A1M0S61S24S29R8A1R2A3S1dS24R1A2M1A3S28R9A1S2dS3S5S9S8S27R3A1M2S2bR3A1A2M3S33R1A1M4A2S9S8S8G4S5bA2Z1000M5A2G2A2A2S3S5S9G3S34R1A1M6A2S9S8G6G5A2G2A2A2S3S5S9G3S2cR1A1M7A2S9S8G7S5aA2G2A2A2S3S5S9G3S32R1A1M8A2S9S8G8G5A2G2A2A2S18S24S2G0S61S24S29RcA1R2A3G1A3S4S2S18R7R3A3A1S5S9S8S27R7A1M9S2bR7A1A2G2A2S9G3G9A2A2F_;F_;Fch';Fj;A2A2A2A2TG;F_;Fch;Fi;F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md HK i ch Hi. destruct (K0_parts Kc A rho tp tr md HK) as (_ & _ & _ & _ & _ & HI3 & _).
  destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (X1 & X2 & X3 & _ & X5 & X6 & _). cbv zeta.
  exact (conj X1 (conj X2 (conj X3 (conj X6 X5)))).
Qed.

Theorem K0_ks_nodup : ltac2:(tb__ "0|1|
S51S25S41S11S3dQ40A1A1S11S48A1S47S45R6R5R4R3R2R1A6S81S0S7aS14S0S0A2M0S0S1eS0S0A2S62G0G0S22S53S19S0S0R1A3A1A1Lit;S5fS5dR6A1A1A3A4A2F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md HK. destruct (K0_parts Kc A rho tp tr md HK) as (_ & _ & _ & _ & _ & HI3 & _).
  destruct HI3 as (_ & _ & _ & _ & _ & ND & _). apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & _ & ND). exact ND.
Qed.

Lemma region_free_apart : ltac2:(tb__ "0|2|
S11S14S3dQ40A1M0G0A2M1A1G0G0G1S60G1R1R4A3S80S20G0G0R4R3A4R2A2F_;Fe;S2S12S4aR4R3R2A3S1cA3F_;Fn;Fa;Fl;").
Proof.
  intros l a n H. induction l as [|[b s] l IH]; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e He; apply H; right; exact He). rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
  pose proof (H (b, s) (or_introl eq_refl)) as AP. unfold apartW in AP. cbn [fst snd] in AP. apply andb_false_iff.
  destruct AP as [AP|AP]; [right; apply Z.ltb_ge; lia | left; apply Z.ltb_ge; lia].
Qed.

Section Gates.
Hypothesis HL8 : ltac2:(tb__ "0|0|
S25S41S11S3dQ40A1A1S47S46R4R3R2R1A4S79S49R2A1A1F_;Fmd;Ftp;Frho;FA;").

Theorem K0_ks_munmap_ok : ltac2:(tb__ "0|3|
S51S25S41S11S3dQ40M0A1M1A1S11S48A1S47S45R6R5R4R3R2R1A6S24S60S24R1S29R7A1A3S3eG0S27R2A1A2G1S3eG0S2bR3A1A2G1S3S2S12S4dS4bS49R6A1A1M2R2R1A3S1cA3S3G1S60S14G1G1A2S20G1G1R3R1A4S4bS49R7A1A1A3S2G1R2R3A3F_;Fs;S2S12S4aS4eG2R2A2R2R1A3S1cA3A2A2Tn;Ta;F_;Fch;F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md HK ch Hch. cbv zeta. pose proof HK as (HA & _). destruct (HL8 A rho tp md HA) as (POS & _).
  destruct (K0_parts Kc A rho tp tr md HK) as (_ & _ & _ & _ & _ & _ & HM).
  destruct (In_nth_error _ _ Hch) as [i Hi].
  set (a := Z_to_bv 64 (sc_map_beg ch)). set (n := Z_to_bv 64 (sc_map_size ch)).
  assert (ENT : In (a, n) (vm_maps (m_vmmaps md))) by (destruct HM as ((_ & _ & _ & _ & _ & _ & _ & N8 & _) & _); exact (N8 ch Hch)).
  assert (RA : ranges_apart (vm_maps (m_vmmaps md))).
  { destruct HM as (_ & _ & _ & _ & _ & _ & _ & LI). destruct LI as (_ & _ & L3 & _). unfold maps_disjoint in L3. apply ranges_apart_app in L3 as (_ & R & _). exact R. }
  pose proof (POS a n ENT) as Pn.
  split; [|split].
  - unfold map_has. apply existsb_exists. exists (a, n). split; [exact ENT|]. cbn [fst snd]. unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity.
  - intros s Hs. destruct (entry_at_base _ a n (a, s) RA ENT Hs eq_refl Pn) as [E|Z0]; [injection E as ->; reflexivity|].
    cbn [snd] in Z0. pose proof (POS a s Hs). lia.
  - apply region_free_apart. intros e He. unfold map_remove in He. apply filter_In in He as [He Hb].
    destruct (In_nth_error _ _ ENT) as [k Hk]. destruct (In_nth_error _ _ He) as [j Hj].
    apply (maps_disjoint_in _ k j (a, n) e RA); [|exact Hk | exact Hj]. intros ->. rewrite Hk in Hj. injection Hj as <-.
    cbn [fst] in Hb. unfold bv_eqb in Hb. rewrite Z.eqb_refl in Hb. discriminate Hb.
Qed.

Theorem K0_ks_madvise_ok : ltac2:(tb__ "0|7|
S51S25S41S11S3dQ40M0A1M1A1S11S48A1S47S45R6R5R4R3R2R1A6G1S0S2S0SfS3fG0R2A2S54A2Z0M2A3S2S0SfR2S54A2G2A3ScG2R3A2S5S3S9S58S3fG0R5A2M3A2S9S8G3R4A2M4S59A2A2S3S9S56G3A2S9G4S57A2A2A2S3S2S12S7bS49R8A1R6S3eG0R5A2A3S1cA3G1S3S9S3fG0R7A2M5S3fG0R1A2M6A2ScG6S8G5R6A2A2A2S2S12S50S4fR2A1S4cRaA1A2S1cA3F_;Fx;A2F_;F_;F_;F_;Fn;Fa;F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md HK a n Hal Hnal Hn0 Hband. pose proof HK as (HA & _). destruct (HL8 A rho tp md HA) as (_ & PLO & PHI).
  destruct (K0_parts Kc A rho tp tr md HK) as (_ & _ & _ & _ & _ & _ & HM).
  destruct HM as ((_ & _ & _ & _ & _ & _ & _ & _ & N9) & _ & _ & _ & _ & _ & _ & LI). destruct LI as (L1 & _ & _ & _ & _ & _ & _ & _ & _ & L10).
  pose proof (uR a) as Ra. unfold PG in *.
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64; unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in Hband; lia).

  assert (PAGE : forall z, bv_unsigned a <= z < bv_unsigned a + n ->
            let p := Z_to_bv 64 (z / 4096 * 4096) in bv_unsigned p = z / 4096 * 4096 /\ bv_unsigned p mod 4096 = 0
            /\ ((LOW_SHADOW_BEG <= bv_unsigned p /\ bv_unsigned p + 4096 <= SHADOW_GAP_BEG) \/ (HIGH_SHADOW_BEG <= bv_unsigned p /\ bv_unsigned p + 4096 <= HIGH_SHADOW_END))).
  { intros z Hz. cbv zeta.
    pose proof (Z.div_mod z 4096 ltac:(lia)) as DZ. pose proof (Z.mod_pos_bound z 4096 ltac:(lia)) as MZ.
    pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as DA. rewrite Hal, Z.add_0_r in DA.
    pose proof (Z.div_mod (bv_unsigned a + n) 4096 ltac:(lia)) as DE.
    assert (ME : (bv_unsigned a + n) mod 4096 = 0) by (rewrite Z.add_mod, Hal, Hnal by lia; reflexivity). rewrite ME, Z.add_0_r in DE.
    assert (LOB : bv_unsigned a <= z / 4096 * 4096) by (pose proof (Z.div_le_mono (bv_unsigned a) z 4096 ltac:(lia) ltac:(lia)); lia).
    assert (HIB : z / 4096 * 4096 + 4096 <= bv_unsigned a + n).
    { assert (z / 4096 < (bv_unsigned a + n) / 4096) by (apply Z.div_lt_upper_bound; lia). lia. }
    assert (UP : bv_unsigned (Z_to_bv 64 (z / 4096 * 4096)) = z / 4096 * 4096) by (apply u64; unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in Hband; lia).
    rewrite UP. split; [reflexivity|]. split; [apply Z_mod_mult|]. destruct Hband as [B|B]; [left | right]; lia. }
  split.
  - assert (INM : exists b s, In (b, s) (vm_maps (m_vmmaps md)) /\ bv_unsigned b <= bv_unsigned a /\ bv_unsigned a + n <= bv_unsigned b + bv_unsigned s).
    { destruct Hband as [B|B]; [destruct PLO as ([b s] & He & H1 & H2) | destruct PHI as ([b s] & He & H1 & H2)]; exists b, s; cbn [fst snd] in *; (split; [exact He | lia]). }
    destruct INM as (b & s & He & H1 & H2).
    apply (madvise_dontneed_ok_intro (m_vmmaps md) a (Z_to_bv 64 n) b s); [| exact He | exact H1 | rewrite Un; exact H2 | exact L10 | rewrite Un; exact Hn0 |].
    + rewrite L1. change (segments_reserved segsA) with (segments_reserved ImageFacts.segsA). rewrite segments_reserved_A. apply region_free_apart. intros e He'. unfold apartW. cbn [fst snd]. right.
      unfold LOW_SHADOW_BEG, HIGH_SHADOW_BEG in Hband.
      destruct He' as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite !u64 by lia; lia.
    + rewrite Un. intros z Hz. destruct (PAGE z Hz) as (UP & PAL & PB). cbv zeta in UP, PAL, PB.
      destruct (N9 _ PAL PB) as [_ COV]. pose proof (Z.div_mod z 4096 ltac:(lia)) as DZ. pose proof (Z.mod_pos_bound z 4096 ltac:(lia)) as MZ.
      specialize (COV (z mod 4096) MZ). rewrite UP in COV. replace (z / 4096 * 4096 + z mod 4096) with z in COV by lia. exact COV.
  - intros x Hx. destruct (PAGE (bv_unsigned x) Hx) as (UP & PAL & PB). cbv zeta in UP, PAL, PB.
    assert (EP : page_base x = Z_to_bv 64 (bv_unsigned x / 4096 * 4096)).
    { apply bv_eq. rewrite page_base_val, UP. unfold page_size. reflexivity. }
    rewrite EP. exact (proj1 (N9 _ PAL PB)).
Qed.
End Gates.

Definition mixv (zb : Z -> bool) (rho rho' : valuation) : valuation := ltac2:(tb__ "0|1|
S44S43Vrho;A1S42Vrho;A1S3dQ40M0A1S12S13S3dQ8A1A1L_;Vzb;S3fG0R1A2A1S40Vrho';R1A2S40Vrho;R1A2X12x2La;A3").
Lemma view_mix : ltac2:(tb__ "0|1|
S0S12F_;S41S41S0S2S13S3dQ8A1A1M0S38S37S40S7eR4R3R2A3A1R1A3S12G0L_;R4R1A1S38S37S40R2A1R1A3S38S37S40R3A1R1A3X12x2A3Fz;Frho';Frho;Fzb;").
Proof.
  intros zb rho rho' z. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|destruct (zb z); reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  cbn [rm mixv]. unfold Glue.rd_of. rewrite (u64 z) by lia. destruct (zb z); reflexivity.
Qed.

Lemma held_not_live : ltac2:(tb__ "0|2|
S25S14S0S0A2M0S24S6dR3A1S60G0R3S5fS5dR4A1A1A3S2S12S53S19S0S0R4A3A1S16A3S2S0S1eS0S0R5A3S8S8S27R4A1S54A2Z800M1A2A3S0S0S60G0S20S0S0R2R1A4S2eR9A1A3S2S12S53R2A1S16A3S4S2S0R4S8S8S27R9A1S54A2G1A2A3A1F_;F_;Fn;Fb;F_;F_;F_;F_;Fch;Fit;FA;").
Proof.
  intros A it ch HI3 Hit HPi Eit b n Hin HP Eb. destruct HI3 as (_ & _ & _ & _ & _ & ND & _).
  apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & HD & _). apply (HD b).
  - apply (proj2 (list_elem_of_In _ _)). apply in_map_iff. exists (b, n). split; [reflexivity|]. apply filter_In. split; [exact Hin|]. cbn. rewrite HP. reflexivity.
  - apply (proj2 (list_elem_of_In _ _)). apply in_map_iff. exists it. split; [rewrite Eit, Eb; reflexivity|]. apply filter_In. split; [exact Hit|]. rewrite HPi. reflexivity.
Qed.

Theorem K0_secshadow : ltac2:(tb__ "0|7|
S51S25S41S41S11S3dQ40A1M0A1S11S48A1S47S14S0S0A2M1S18S24S60G1R3S5fS5dR9A1A1A3S2S12S53S19S0S0R4A3A1S16A3S2S13S24A1S61S24S29RbA1R4A3S1dS24R3A2A3S2S0S1eS0S0R6A3S8S8S27R4A1S54A2Z800A2A3S1S2G0S43RcR1A2S43RdR1A2A3Fi0;S1S2S11S3dQ8A1M2A1S42RdR1A2S42ReR1A2A3Fl;S0S4S63R10R1A2A1S4S66R9R2A2A1S2S13G2A1M3S38S37S40R10A1R3A3S38S37S40R11A1M4R3A3M5A3F_;F_;Fz;S0S5S63R11R1A2S66R9R1A2A2S4S2G3S38S37G4R2A3S21G2A1M6A3A1S4S2G3G5G6A3A1F_;F_;Fz;S45R12R11R10ReRdRcA6S45R13R12R10RfReRdA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fch;Fi;Fit;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md it i ch Hit HPi Hi Hu Hw Hl HOUT HIN HK.
  set (zb := fun z => (Sh (sc_map_beg ch) <=? z) && (z <? Sh (sc_map_beg ch + sc_map_size ch))).
  assert (ZB : forall z, zb z = true <-> chunk_sh_zone ch z).
  { intros z. unfold zb, chunk_sh_zone. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. }
  assert (ZBF : forall z, zb z = false <-> ~ chunk_sh_zone ch z).
  { intros z. rewrite <- ZB. destruct (zb z); split; intros H; congruence. }
  set (r1 := mixv zb rho rho').

  assert (K1 : K0 Kc A r1 tp tr md).
  { pose proof HK as (HA & HKc & Htp & Htop & HRG). destruct (K0_parts Kc A rho tp tr md HK) as (HG & HLS & HPR & HSR & HQP & HI3 & HM).
    assert (O1 : forall z, ~ chunk_sh_zone ch z -> view segsA (rm r1) z = view segsA (rm rho) z).
    { intros z Hz. unfold r1. rewrite view_mix. rewrite (proj2 (ZBF z) Hz). reflexivity. }
    assert (I1 : forall z, chunk_sh_zone ch z -> True -> view segsA (rm rho) z <> None -> view segsA (rm r1) z <> None).
    { intros z Hz _ Hd. unfold r1. rewrite view_mix. rewrite (proj2 (ZB z) Hz). exact (HIN z (or_intror Hz) Hd). }
    assert (ZR : forall z, chunk_sh_zone ch z -> RZ A i ch z) by (intros z Hz; right; right; right; exact Hz).
    assert (DEC : forall z, chunk_sh_zone ch z \/ ~ chunk_sh_zone ch z) by (intros z; unfold chunk_sh_zone; lia).
    pose proof (X_all A rho r1 tp md i ch (chunk_sh_zone ch) (fun _ => True) HA Hi (held_not_live A it ch HI3 Hit HPi Hu) ZR DEC O1 I1 (fun _ _ _ => I))
      as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
    pose proof (X_sec_same A rho r1 tp md i ch (chunk_sh_zone ch) (fun _ => True) HA Hi ZR DEC O1 I1 (fun _ H => H) (fun _ _ => I)) as VS.
    split; [|exact (conj HKc (conj Htp (conj Htop HRG)))].
    unfold AInvQ. cbv zeta. split; [exact HG|]. split; [exact V1|]. split; [exact V2|].
    split; [|split; [exact HM | split; [exact HI3 | exact (V10 tp (fun _ H => H))]]].
    split; [exact HLS|]. split; [exact V3|]. split; [exact V4|]. split; [exact VS|]. split; [exact (conj HQP V5)|].
    split; [exact V6|]. split; [exact V7|]. split; [exact V8 | exact V9]. }

  apply (K0_view Kc A r1 rho' tp tr md); [intros i0; exact (Hw i0) | intros l; exact (Hl l) | | | exact K1].
  - intros z NQ. unfold r1. rewrite view_mix. destruct (zb z) eqn:E; [reflexivity|]. exact (HOUT z NQ (proj1 (ZBF z) E)).
  - intros z HQ. unfold r1. rewrite view_mix. destruct (zb z) eqn:E; [intros H; exact H|]. exact (HIN z (or_introl HQ)).
Qed.

Definition RZb (A : AA) (i : nat) (ch : sec_chunk) (z : Z) : bool := ltac2:(tb__ "0|8|
S1aS1aS1aS1aS1aS1aS1aS17SaS8S6cZ40A2M0Vz;A2SbVz;Zee040M1A2A2S17SaZee048Vz;A2SbVz;Zee070A2A2A2S17SaS8S6cZ38A2Vz;A2SbVz;G0A2A2A2S17SaG1Vz;A2SbVz;Zee044A2A2A2S17SaS8S2cS28VA;A1A1SeZ8M2SdVi;A1A2A2M3Vz;A2SbVz;S8G3G2A2A2A2A2S13S24A1S12Lx;S61S24S29VA;A1M4S75S1fS24G4A2U1A2A3S24S17SaS8S27R1A1M5Z18A2Vz;A2SbVz;S8G5Z20A2A2A2Llst;S16X13x2A2S17SaS27Vch;A1M6Vz;A2SbVz;S8G6S2bVch;A1A2M7A2A2A2S17SaS55G6A1Vz;A2SbVz;S55G7A1A2A2A2").
Lemma RZb_spec : ltac2:(tb__ "0|0|
S25S18S24S0S7S2S12S7dR4R3R2R1A4S1cA3S7fR4R3R2R1A4A2Fz;Fch;Fi;FA;").
Proof.
  intros A i ch z. unfold RZb, RZ, sec_junk_zone, sec_tbl_zone, chunk_zone, chunk_sh_zone.
  rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt.
  assert (L : (match nth_error (aa_sec A) (length (aa_sec A) - 1) with Some lst => (sc_map_beg lst + 24 <=? z) && (z <? sc_map_beg lst + 32) | None => false end) = true
              <-> (exists lst, nth_error (aa_sec A) (length (aa_sec A) - 1) = Some lst /\ sc_map_beg lst + 24 <= z < sc_map_beg lst + 32)).
  { destruct (nth_error (aa_sec A) (length (aa_sec A) - 1)) as [lst|].
    - rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. split; [intros H; exists lst; split; [reflexivity | exact H] | intros (l2 & E & H); injection E as <-; exact H].
    - split; [discriminate | intros (l2 & E & _); discriminate E]. }
  rewrite L. tauto.
Qed.

Lemma class_repr_q : ltac2:(tb__ "0|0|
S3bS2dS25S25S0S35S2S11S14S0S0A2A1S2eR3A1S2eR4A1A3S2S12S2fR4A1S2fR5A1A3S2S11S0A1S5eR7S5dR5A1R4A3S5eR7S5dR6A1R4A3A3S6fR9R8R7R5R4A5S6fRaR9R7R6R5A5F_;F_;F_;F_;Fcs;Fc;FA';FA;FG;Fm;").
Proof.
  intros m G A A' c cs EL EC EQ H. unfold class_repr in *. unfold live_ids in *. rewrite EL, EC, EQ. exact H.
Qed.
Lemma q_ids_sec_item : ltac2:(tb__ "0|2|
S2dS11S26A1M0G0S0S14S0S0A2M1S11G1A1S0S0S0S2S12S53S19S0S0R5A3A1S16A3S2S11S0A1S5eRaS1bS26R9S15S26S2aR7R5R3A3R8A3A3R2A3S5eRaS1bS26R9S15S26S2aR7S15G1R6R5A3R4A3R8A3A3R2A3A3F_;Fc;Fs';Fs;Fi2;Fit;Fa;Fg2;Fg1;FG;").
Proof.
  intros G g1 g2 a it i2 s s' c HP. unfold q_ids, qitems. rewrite !flat_map_app. cbn [flat_map qb_items]. rewrite !List.filter_app.
  cbn [List.filter app]. rewrite HP. cbn [andb]. rewrite !map_app. reflexivity.
Qed.

Lemma QW_sec_item : ltac2:(tb__ "0|3|
S25S25S11S26A1M0G0S0S14S0S0A2M1S11G1A1S0S0S0S2S2dS28R9A1S28RaA1A3S2S12S53S19S0S0R6A3A1S16A3S2G0S5dRcA1M2S1bS26RaS15S26S2aR8S15G1R7R6A3R5A3R9A3A3A3S2G0G2S1bS26RbS15S26S2aR9R7R5A3RaA3A3A3S7S63RdR5A2S63ReR5A2A2F_;F_;F_;F_;Fz;Fs';Fs;Fi2;Fit;Fa;Fg2;Fg1;FA';FA;").
Proof.
  intros A A' g1 g2 a it i2 s s' z EG HP E E'. unfold QW, qzone. rewrite EG, E, E'. rewrite !Exists_app, !Exists_cons. cbn [qb_addr qb_items].
  assert (X : Exists (fun it0 : Z * Z => is_primary (snd it0) = true /\ (it_ab it0 <= z < fst it0 \/ Sh (fst it0) <= z < Sh (fst it0) + (snd it0 + 7) / 8)) (it :: i2)
              <-> Exists (fun it0 : Z * Z => is_primary (snd it0) = true /\ (it_ab it0 <= z < fst it0 \/ Sh (fst it0) <= z < Sh (fst it0) + (snd it0 + 7) / 8)) i2).
  { rewrite Exists_cons. split; [intros [[P _]|H]; [rewrite HP in P; discriminate P | exact H] | intros H; right; exact H]. }
  rewrite X. tauto.
Qed.

Theorem K0_unmap : ltac2:(tb__ "0|19|
S51S52R1A1S25S41S41S11S3dQ40M0A1M1A1S11S48A1S47S11S26A1M2G2S0S14S0S0A2M3S11G3A1S0S0S18S24S2G2S31RfA1S23S26A1M4A3S2G2S30R10A1S1bS26RaS15S26S2aR8S15G3R7R6A3R5A3R9A3A3A3S2S12S53S19S0S0R8A3A1S16A3S2S13S24A1M5S61S24S29R12A1R5A3S1dS24R4A2A3S2S0S1eS0S0RaA3S8S8S27R5A1S54A2Z800A2A3S28R14A1S2dSdS1fS24S29R15A1A2A1S0S1S2G1S43R15R1A2S43R16R1A2A3Fi0;S1S2S11S3dQ8A1M6A1S42R16R1A2S42R17R1A2A3Fl;S0S4S63R19R1A2A1S4S68R2A1A1S4S6aR1bReR3A3A1S4S69ReR4A2A1S4S66RfR5A2A1S2S13G6A1M7S38S37S40R1cA1R6A3S38S37S40R1dA1M8R6A3A3F_;F_;F_;F_;F_;Fz;S0S5S63R1aR1A2S5S68R1A1S66RcR1A2A2A2S4S2G7S38S37S40R1aA1M9R2A3S21G6A1MaA3A1S4S2G7S38S37G9R3A3GaA3A1F_;F_;Fz;S39S38S37S40R18A1A2S3aS8S6cZ38A2U8MbS10R5Z1McA2A3A2S39S38S37S40R19A1A2S3aZee040U4Z0A3A2S24S2G5S61S24S29R1dA1MdS75S1fS24GdA2U1A2A3S1dS24R1A2A3S3ScSdR11A1MeS10R9GcA2MfA2S3S39S38S37G8A2M10S3aS8S2cRbA1SeZ8M11SdR12A1M12A2A2GbS27R3A1M13A3A2S39G10S3aS8G13Z18A2GbG12A3A2A2F_;S2S0GeGfA3S0S3S9S8S2cRcA1SeG11SdR13A1A2A2M14R1A2ScR1S8G14G11A2A2A2S2G7S38S37S40R1fA1R2A3S38S37S40R20A1R2A3A3F_;Fz;F_;A2F_;Flst;S9S78S76R18S3eG0S27RfA1M15A2S3eG0S2bRfA1M16A2A3S77G15S8G15G16A2R1aA3A2S78R18R1aA2A2S45R20R1eR1dR1bR1aR19A6S45R21S6bS65R1fG4S1bS26R19S15S26S2aR17R15R13A3R18A3A3A3R12A2R1dS77S27R11A1M17S8G17S2bR11A1M18A2R1cA3R1bS76R1aS3eG0G17A2S3eG0G18A2A3A6F_;F_;F_;F_;F_;F_;F_;F_;F_;Tn;TG;F_;F_;F_;F_;F_;Fch;Fi;Fs';Fs;Fi2;Fit;Fa;Fg2;Fg1;Fmd;Ftr;Ftp;Frho';Frho;FA;F_;FKc;").
Proof.
  intros Kc HKcok A rho rho' tp tr md g1 g2 a it i2 s s' i ch Hth Hgl HPi Hi Hu. cbv zeta.
  intros Hw Hl HOUT HIN CN CM CL HPAID HK.
  set (A' := unmap_sec (set_q A [] (g1 ++ mkQB a i2 s' :: g2)) i).
  set (tp' := tp_forget (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) tp).
  set (md' := munmap_model md (Z_to_bv 64 (sc_map_beg ch)) (Z_to_bv 64 (sc_map_size ch))).
  set (r1 := mixv (RZb A i ch) rho rho').
  pose proof HK as (HA & HKc & Htp & Htop & HRG). destruct (K0_parts Kc A rho tp tr md HK) as (HG & HLS & HPR & HSR & HQP & HI3 & HM).
  assert (EQA : qall A = g1 ++ mkQB a (it :: i2) s :: g2) by (unfold qall; rewrite Hth, Hgl; reflexivity).
  assert (Hit : In it (qitems (qall A))).
  { rewrite EQA. unfold qitems. apply in_flat_map. exists (mkQB a (it :: i2) s). split; [apply in_or_app; right; left; reflexivity | left; reflexivity]. }
  assert (ZT : forall z, RZb A i ch z = true -> view segsA (rm r1) z = view segsA (rm rho') z) by (intros z E; unfold r1; rewrite view_mix, E; reflexivity).
  assert (ZF : forall z, RZb A i ch z = false -> view segsA (rm r1) z = view segsA (rm rho) z) by (intros z E; unfold r1; rewrite view_mix, E; reflexivity).
  assert (NRZ : forall z, ~ RZ A i ch z -> RZb A i ch z = false).
  { intros z Hz. destruct (RZb A i ch z) eqn:E; [exfalso; exact (Hz (proj1 (RZb_spec A i ch z) E)) | reflexivity]. }

  assert (K1 : K0 Kc A' r1 tp' tr md').
  { assert (O1 : forall z, ~ RZ A i ch z -> view segsA (rm r1) z = view segsA (rm rho) z) by (intros z Hz; exact (ZF z (NRZ z Hz))).
    assert (I1 : forall z, sec_junk_zone z \/ chunk_sh_zone ch z -> view segsA (rm rho) z <> None -> view segsA (rm r1) z <> None).
    { intros z Hz Hd. rewrite ZT; [exact (HIN z (or_intror Hz) Hd)|]. apply RZb_spec. destruct Hz as [Hz|Hz]; [left; exact Hz | right; right; right; exact Hz]. }
    assert (CELLR : forall c, (forall k, (k < c_w c)%nat -> RZ A i ch (c_addr c + Z.of_nat k)) -> cell_ok (view segsA (rm rho')) c -> cell_ok (view segsA (rm r1)) c).
    { intros c H Hc k Hk. rewrite (ZT _ (proj2 (RZb_spec A i ch _) (H k Hk))). exact (Hc k Hk). }
    pose proof (X_all A rho r1 tp md i ch (RZ A i ch) (fun z => sec_junk_zone z \/ chunk_sh_zone ch z) HA Hi (held_not_live A it ch HI3 Hit HPi Hu)
                  (fun _ H => H) (RZ_dec A i ch) O1 (fun z _ HP => I1 z HP)
                  (fun z HZ HB => or_intror (RZ_band A (maskv (fs_footb (aa_geom A)) (view segsA (rm rho))) HSR i ch Hi z HZ HB)))
      as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
    assert (VS : secondary_repr (maskv (fs_footb (aa_geom A)) (view segsA (rm r1))) A').
    { apply (X_sec_unmap A rho r1 tp md i ch [] (g1 ++ mkQB a i2 s' :: g2) HA Hi O1 I1).
      - apply CELLR; [|exact CN]. cbn [c_addr c_w]. intros k Hk. right. left. left. lia.
      - apply CELLR; [|exact CM]. cbn [c_addr c_w]. intros k Hk. right. left. right. left. lia.
      - intros lst Hlst. destruct (CL lst Hlst) as [CLa CLb]. split.
        + intros LT. destruct (CLa LT) as [C1 C2]. split.
          * apply CELLR; [|exact C1]. cbn [c_addr c_w]. intros k Hk. right. left. right. right. left. lia.
          * apply CELLR; [|exact C2]. cbn [c_addr c_w]. intros k Hk. right. left. right. right. right. exists lst. split; [exact Hlst | lia].
        + intros EQ z Hz. rewrite ZT; [exact (CLb EQ z Hz)|]. apply RZb_spec. right. left. right. right. left. exact Hz. }
    assert (VP : primary_repr (maskv (fs_footb (aa_geom A)) (view segsA (rm r1))) A').
    { destruct V4 as (Q1 & Q2 & Q3 & P4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. intros c Hc.
      apply (class_repr_q _ (aa_geom A) A A' c _ eq_refl eq_refl); [|exact (P4 c Hc)].
      change (qall A') with ([] ++ (g1 ++ mkQB a i2 s' :: g2)). cbn [app]. rewrite EQA. exact (q_ids_sec_item (aa_geom A) g1 g2 a it i2 s s' c HPi). }
    assert (HCH : forall j c, nth_error (aa_sec A) j = Some c -> 0 < sc_map_size c /\ dyn_in (topG (aa_geom A)) (sc_map_beg c) (sc_map_size c)).
    { intros j c Hj. destruct HSR as (S1 & _). destruct (S1 j c Hj) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _). split; [unfold PG in D8; lia | exact D10]. }
    split; [|split; [|exact (conj Htp (conj Htop HRG))]].
    - unfold AInvQ. cbv zeta. change (aa_geom A') with (aa_geom A).
      split; [exact HG|]. split; [exact V1|]. split; [exact V2|].
      split; [|split; [exact (model_unmap A tp md i ch [] (g1 ++ mkQB a i2 s' :: g2) HM HI3 Hi HCH HPAID) | split]].
      + split; [exact HLS|]. split; [exact V3|]. split; [exact VP|]. split; [exact VS|].
        split; [exact (conj (QP_unmap A g1 g2 a it i2 s s' i ch Hth Hgl HPi Hi Hu HQP HI3) V5)|].
        split; [exact V6|]. split; [exact V7|]. split; [exact V8 | exact V9].
      + exact (I3_unmap A g1 g2 a it i2 s s' i ch Hth Hgl HPi Hi Hu HQP HI3).
      + apply V10. intros p Hp. unfold tp', tp_forget in Hp. apply filter_In in Hp. exact (proj1 Hp).
    - exact (HKcok tr md (m_vm md') HKc). }

  assert (QWE : forall z, QW A' z <-> QW A z).
  { intros z. apply (QW_sec_item A A' g1 g2 a it i2 s s' z eq_refl HPi EQA). reflexivity. }
  apply (K0_view Kc A' r1 rho' tp' tr md'); [intros i0; exact (Hw i0) | intros l; exact (Hl l) | | | exact K1].
  - intros z NQ. destruct (RZb A i ch z) eqn:E; [rewrite (ZT z E); reflexivity|]. rewrite (ZF z E).
    assert (NR : ~ RZ A i ch z) by (intros X; apply RZb_spec in X; rewrite X in E; discriminate E).
    apply HOUT; [intros X; exact (NQ (proj2 (QWE z) X)) | intros X; apply NR; left; exact X | intros X; apply NR; right; left; exact X
                 | intros X; apply NR; right; right; left; exact X | intros X; apply NR; right; right; right; exact X].
  - intros z HQ. destruct (RZb A i ch z) eqn:E; [rewrite (ZT z E); intros H; exact H|]. rewrite (ZF z E). exact (HIN z (or_introl (proj1 (QWE z) HQ))).
Qed.

Definition L8_holds : Prop := ltac2:(tb__ "0|0|
S25S41S11S3dQ40A1A1S47S46R4R3R2R1A4S79S49R2A1A1F_;Fmd;Ftp;Frho;FA;").

Theorem K0_sec_of_L8 : ltac2:(tb__ "0|0|
S7cS51S52R1A1S67S37S45R2A1A2F_;FKc;F_;").
Proof.
  intros HL8 Kc HKc. constructor.
  - exact (K0_ks_repr Kc).
  - exact (K0_ks_item Kc).
  - exact (K0_ks_sep Kc).
  - exact (K0_ks_nodup Kc).
  - exact (K0_ks_munmap_ok HL8 Kc).
  - exact (K0_ks_madvise_ok HL8 Kc).
  - exact (K0_secshadow Kc).
  - exact (K0_unmap Kc HKc).
Qed.

Lemma AInvQ_L8 : L8_holds.
Proof. intros A rho tp md (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & LI). destruct LI as (_ & _ & _ & _ & _ & _ & _ & L8 & _). exact L8. Qed.
Theorem K0_sec : ltac2:(tb__ "0|0|
S51S52R1A1S67S37S45R2A1A2F_;FKc;").
Proof. exact (K0_sec_of_L8 AInvQ_L8). Qed.
End InvQ10.

(* [comment removed for export] *)
Module SegQF_lib.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "None"; "option"; "app"; "cons"; "nat"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rl"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "free_array"; "kFreeArraySize"; "kRegionInfoStride"; "kSpaceSize"; "region_info"; "HIGH_SHADOW_END"; "IMG_HI"; "IMG_LO"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "qbatch"; "ag_spacebeg"; "ag_thread"; "topG"; "AA"; "aa_q_global"; "mkQB"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "CURB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib.DZ"; "bandz"; "DZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "RMEM2"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma K0_blind : ltac2:(tb__ "0|6|
S34S27S12S12SbS11Q40A1M0A1SbS2bA1S2aSaS6G0S15R5R1A2S15R6R1A2A3Fi;SaS6SbS11Q8A1M1A1S13R6R1A2S13R7R1A2A3Fl;S9S2R1S26S22R9A1A1A2S8S33RaR2A2A1S6SdG1A1M2S2dS2cS14R9A1R3A3S2dS2cS14RaA1M3R3A3M4A3F_;F_;Fz;S9S33RaR1A2S8S6G2S2dS2cG3R2A3ScG1A1M5A3A1S8S6G2G4G5A3A1F_;F_;Fz;S2fRbRaR9R7R6R5A6S2fRcRbR9R8R7R6A6F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr';Fr;FA;FKc;").
Proof.
  intros Kc A r r' tp tr md Hw Hl HOUT HIN HK.

  set (mix := fun x : word => if Z_lt_dec (bv_unsigned x) (topG (aa_geom A)) then rm r' x else rm r x).
  set (r1 := set_rm r mix).
  assert (V1 : forall z, view segsA (rm r1) z = if Z_lt_dec z (topG (aa_geom A)) then view segsA (rm r') z else view segsA (rm r) z).
  { intros z. destruct (Z_lt_dec z (topG (aa_geom A))) as [L|L]; apply view_agree; intros Hz; unfold r1, mix; cbn [rm set_rm]; rewrite u64_lit by lia;
      destruct (Z_lt_dec z (topG (aa_geom A))); first [reflexivity | lia]. }
  assert (HK1 : K0 Kc A r1 tp tr md).
  { apply (K0_view Kc A r r1 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | exact HK].
    - intros z NQ. rewrite V1. destruct (Z_lt_dec z (topG (aa_geom A))) as [L|L]; [exact (HOUT z L NQ) | reflexivity].
    - intros z HQ Hd. rewrite V1. destruct (Z_lt_dec z (topG (aa_geom A))) as [L|L]; [exact (HIN z HQ Hd) | exact Hd]. }
  destruct HK1 as (HA & HKc & Htp & Htop & HRG).
  split; [|split; [exact HKc | split; [|split]]].
  - apply (AInvQ_frame_top A r1 r' tp md HA). intros z Hz. rewrite V1. destruct (Z_lt_dec z (topG (aa_geom A))); [reflexivity | lia].
  - unfold tp_ok in *. rewrite (Hw 24%positive). exact Htp.
  - unfold top_high in *. rewrite (Hw 10%positive), (Hw V_DEPTH). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite !Hw. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.

Section DZ.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HSBD : KQ_secband K.
Variables (A : AA) (a s : Z) (its0 : list (Z * Z)) (tmp' rest : list qbatch) (c : Z).
Hypothesis HTH : aa_q_thread A = [].
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HGL : ltac2:(tb__ "0|0|
S6SbS23A1S28VA;A1SfS23S29Va;Vits0;Vs;A3SeS23Vtmp';Vrest;A3A3A3").
Hypothesis Hc : 1 <= c <= 30.

Definition DZ (z : Z) : Prop := ltac2:(tb__ "0|5|
S25S22VA;A1M0A1S9S24G0A1S9S19R1Vc;A2S9S7S5S0S1S1R3Zd0A2S3Z50M1Vc;A2A2M2Vz;A2S2Vz;S1G2G1A2A2A2S7S5S0S1dR2Vc;A2M3Vz;A2S2Vz;S1G3S1bA2A2A2S7S5S0R1Vz;A2S2Vz;S1R1S1aA2M4A2A2S5S0S16R1A1Vz;A2S2Vz;S16G4A1A2A2A2A2A2Tfa;TSB;TT;").
Definition bandz (z : Z) : Prop := ltac2:(tb__ "0|0|
S5S0S18Vz;A2S2Vz;S17A2A2").

Lemma dz_nums : ltac2:(tb__ "0|9|
S12SbS11Q40A1A1SbS2bA1S2aVK;VA;R4R3R2R1A5S25S22VA;A1M0A1S9S24G0A1S9S5S0S1eR1A2S5S0S1S1R1S1cA2Z1000M1A2M2S26G0A1A2S5S7S0S1R2G1A2M3R1A2S0G2R2A2A2S5S7S0G3S20A2S0S1fR2A2A2S5S7S0G3S18A2S0S17R2A2A2S5S9S7S5S0S19R2Vc;A2M4R1A2S2R1S1G4S1aA2M5A2A2S5S0S1dR2Vc;A2M6R1A2S2R1S1G6S1bA2A2A2A2S7S5S0S1S1R3S3Vc;S4Z2Z20A2M7A2A2S21A2R2A2S2R2S1R3S3S1Vc;Z1A2G7A2A2A2A2S5S0S1R3S1cA2M8R2A2S2R2S1G8G1A2A2A2A2F_;Fz;S9S5S0S16G4A1R1A2S2R1S16G5A1A2A2S31R2A1F_;Fz;A2A2A2A2A2A2TSB;TT;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK T SB. destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ HSEP3 _ _].
  destruct (thr_facts K HL A r tp tr md HK) as (T1 & T2 & T3 & SB1 & SB2). cbv zeta in T1, T2, T3. fold T SB in T1, T2, T3, SB1, SB2.
  destruct HSEP3 as (S1 & _). fold T SB in S1. pose proof (topG_range (aa_geom A)) as TG.
  split; [exact SB1|]. split; [exact SB2|]. split; [exact S1|]. split; [exact T2|]. split; [exact T3|]. split.
  - intros z Hz. unfold free_array, region_beg, region_info, kUserSpaceSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *. lia.
  - intros z Hz. unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize in *.
    pose proof (Z.div_pos (SB + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_upper_bound (SB + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + 2 ^ 29) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D1. lia.
Qed.

Lemma CR_drain : ltac2:(tb__ "0|4|
S12SbS11Q40A1A1SbS2bA1S2aS2eS2eS9S10VK;VA;R8R7R6R5A5S9S8S32R1A1A1S6SdS11Q8A1M0A1M1R6R2A1R7R2A1A3F_;Fz;S9S31R1A1S8S6G1R8R2A1ScG0A1M2A3A1S8S6G1R8R3A1G2A3A1F_;F_;Fz;S30R7Va;R5R4Vits0;A5S35R8S22VA;A1Vtmp';Vrest;A4M3S5S30R8Va;R7R6Vits0;A5G3A2F_;F_;F_;F_;F_;Fnd;Fn0;Fv';Fv;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md v v' n0 nd HK HEQ HPRS HCB HRM.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ HQPU _ HSEP _ _ HKSECQ].
  pose proof (benv_of_K K HL A HCI r tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  destruct (dz_nums r tp tr md HK) as (SB1 & SB2 & ST & TI & TB & DSP & DSH). cbv zeta in ST, TI, TB, DSP, DSH.
  assert (QALL : qall A = mkQB a its0 s :: tmp' ++ rest) by (unfold qall; rewrite HTH, HGL; reflexivity).

  assert (OUT_T : forall z, q_foot A z -> ~ bandz z ->
            ~ (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + kUserSpaceSize <= z < ag_spacebeg (aa_geom A) + (c + 1) * 2 ^ 32 \/ ag_spacebeg (aa_geom A) + kSpaceSize <= z < ag_spacebeg (aa_geom A) + kSpaceSize + 4096) -> ~ DZ z).
  { intros z HF NB NS HZ. unfold DZ in HZ. cbv zeta in HZ. destruct HZ as [HZ|[HZ|[HZ|HZ]]].
    - apply (HSEP z HF). lia.
    - apply NS. apply DSP. right. exact HZ.
    - apply NS. apply DSP. left. exact HZ.
    - exact (NB (DSH z HZ)). }
  assert (BW : forall b, In b (qall A) -> Z.of_nat (length (qb_items b)) <= kQuarantineBatchCount /\ forall z, qb_addr b <= z < qb_addr b + 8192 -> ~ DZ z).
  { intros b Hb. destruct (batch_slot A HQPU HAU HG b Hb) as (y & E & Y0 & _ & Y1 & B5 & B6 & _ & BL & _). split; [exact BL|]. intros z Hz.
    apply OUT_T.
    - unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. exact Hz.
    - unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG. lia.
    - pose proof kUserSpaceSize_val as KU. unfold kSpaceSize. rewrite E in Hz. lia. }
  assert (IW : forall it', In it' (qitems (qall A)) ->
            (forall z, it_ab it' <= z < fst it' -> ~ DZ z) /\ (forall z, Sh (fst it') <= z < Sh (fst it') + (snd it' + 7) / 8 -> bandz z)).
  { intros it' Hin. destruct (qitems_In A it' Hin) as (b & Hb & Hib). pose proof (rz_facts (snd it')) as (RZ1 & _).
    assert (HF : forall z, it_ab it' <= z < fst it' -> q_foot A z).
    { intros z Hz. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it'. split; [exact Hib|]. left. unfold it_ab in Hz. exact Hz. }
    destruct (is_primary (snd it')) eqn:EP.
    - pose proof (item_slot A HQPU HAU HG it' Hin EP) as IS'. cbv zeta in IS'. destruct IS' as (C1 & I2 & _ & I4 & _ & I6 & _ & _ & _ & I10 & I11 & I12 & I13 & I14).
      pose proof kUserSpaceSize_val as KU. split.
      + intros z Hz. apply (OUT_T z (HF z Hz)); [unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG; lia|].
        unfold kSpaceSize. lia.
      + intros z Hz. pose proof (topG_range (aa_geom A)) as TG. unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF, kSpaceSize in *.
        pose proof (Z.div_mod (fst it') 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (fst it') 8 ltac:(lia)) as D2.
        pose proof (Z.div_mod (snd it' + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (snd it' + 7) 8 ltac:(lia)) as D4. lia.
    - destruct (HKSECQ it' Hin EP) as [X1 X2]. pose proof (HSBD A r tp tr md HK it' Hin EP) as X3.
      destruct (batch_slot A HQPU HAU HG b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it' Hib) as (U0 & N1 & _). unfold IMG_HI in U0.
      split.
      + intros z Hz. pose proof (HF z Hz) as HFz. unfold it_ab in Hz. pose proof kUserSpaceSize_val as KU. apply (OUT_T z HFz); [unfold bandz; clear - X3 Hz; lia | unfold kSpaceSize in *; clear - X1 Hz Hc KU; lia].
      + intros z Hz. unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
        pose proof (Z.div_mod (fst it') 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (fst it') 8 ltac:(lia)) as D2.
        pose proof (Z.div_mod (snd it' + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (snd it' + 7) 8 ltac:(lia)) as D4. lia. }
  assert (INB : forall b, In b (tmp' ++ rest) -> In b (qall A)) by (intros b Hb; rewrite QALL; right; exact Hb).
  apply (CR_frame v v' (aa_geom A) a n0 nd its0 tmp' rest); try assumption.
  - intros z Hz. apply HEQ. exact (proj2 (BW (mkQB a its0 s) ltac:(rewrite QALL; left; reflexivity)) z Hz).
  - intros b Hb. destruct (BW b (INB b Hb)) as [LB EB]. split; [exact LB|]. intros z Hz. apply HEQ. exact (EB z Hz).
  - intros it' Hin'. assert (Hq : In it' (qitems (qall A))) by (rewrite QALL; unfold qitems; cbn [flat_map qb_items]; exact Hin').
    destruct (IW it' Hq) as [W1 W2]. split; [intros z Hz; apply HEQ; exact (W1 z Hz) | intros z Hz Hd; exact (HPRS z (W2 z Hz) Hd)].
  - intros z Hz. apply HEQ. unfold DZ. cbv zeta. pose proof kUserSpaceSize_val as KU. unfold kSpaceSize in *.
    intros [HZ|[HZ|[HZ|HZ]]]; [clear - HZ Hz Hc; lia | pose proof (DSP z (or_intror HZ)) as X0; clear - X0 Hz ST Hc KU; lia | pose proof (DSP z (or_introl HZ)) as X0; clear - X0 Hz ST Hc KU; lia |].
    pose proof (DSH z HZ) as HB. unfold bandz in HB. clear - HB Hz TB. lia.
  - intros z Hz. apply HEQ. unfold DZ. cbv zeta. pose proof kUserSpaceSize_val as KU. unfold QG, IMG_LO, IMG_HI, HIGH_SHADOW_END, kSpaceSize in *.
    intros [HZ|[HZ|[HZ|HZ]]]; [clear - HZ Hz TI Hc; lia | pose proof (DSP z (or_intror HZ)) as X0; clear - X0 Hz SB1 Hc KU; lia | pose proof (DSP z (or_introl HZ)) as X0; clear - X0 Hz SB1 Hc KU; lia |].
    pose proof (DSH z HZ) as HB. unfold bandz, SHADOW_BAND_LO, LOW_SHADOW_BEG in HB. clear - HB Hz. lia.
Qed.
End DZ.
End SegQF_lib.

