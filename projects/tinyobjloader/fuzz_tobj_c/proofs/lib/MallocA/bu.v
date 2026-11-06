(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ci.

(* [comment removed for export] *)
Module SpineMallocQ13.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "sub"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "SAlu"; "SLit"; "sprop"; "SVar"; "ss_next"; "ss_objs"; "rw"; "ss_facts"; "ss_lenient"; "cell"; "swf"; "SPBranch"; "SPNot"; "eval"; "mkCell"; "rm"; "smatch"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "nil"; "true"; "false"; "option"; "Some"; "app"; "prod"; "pair"; "None"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13.FILL"; "JRfill"; "phL"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "LV0"; "LV2"; "GR"; "LV3"; "keepn"; "LNX"; "HINT_au"; "HINT_k"; "O_cell"; "O_pcm"; "O_ri"; "vAU"; "vNEW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "FAb"; "zoneR"; "frozen"; "ghosts"; "mkPh"; "ph_f"; "ph_u"; "rlink"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "ALU_XOR"; "BC_LTU"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13"; "O_fcell"; "faend_e"; "F_lt"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition faend_e : sv := SAlu ALU_ADD fa_e2 need_e.
Definition O_fcell : sobj := ltac2:(tb__ "0|1|
S48S43S23S18S1dS10Z0A1Z4M0SfS58S12S41A1S10G0A1A3A3S26S18A1A3A2").
Definition F_lt : sprop := ltac2:(tb__ "0|0|
S1aS5aS12S40A1S4cA3").

Section FILL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S68Vst;S67A3S0S24S66A1VW;S26S66A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S7aVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let S : Z := Size c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let au : Z := cs_allocated_user cs.
Let new : Z := gh_new A rb.

Variable ph : phase.
Hypothesis PQ : ph_quiet ph.
Definition phL (i : Z) : phase := ltac2:(tb__ "0|0|
S52S54Vph;A1S53Vph;A1Vi;Z0S28S28A6").
Lemma phL0 : phL 0 = ph.
Proof.
  destruct PQ as (Q1 & Q2 & Q3 & Q4).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phL; rewrite Q1, Q2, Q3, Q4; reflexivity | symmetry; apply ph_eta].
Qed.

Hypothesis HDEF : ltac2:(tb__ "0|3|
S21S76S1S6Z0R2A2S6R2Vnew;A2A2S55VA;Vrb;S39R3A1S77S35S1eVrb;A1A2R2A5S21S1S6S5S4eVA;Vrb;A2M0S7Z4M1Vnf;A2A2R1A2S8R1S5G0S7G1S5Vnf;Vnew;A2A2A2A2A2S3S0S29S3aQ8A1M2A1R5R2A1S2eG2A1A3A1F_;Fz;F_;F_;Fm;Fi;").

Lemma fill_nums : ltac2:(tb__ "0|7|
S1S1S6Z20VS;A2S6VS;Z10000A2A2S1S6Z0M0Vau;A2S1S6S5Vau;S7Vnew;VS;A2A2Ze0000000M1A2S1S1S6Z4M2Vnew;A2S6Vnew;Z2001A2A2S1S6G0Vnf;A2S1S6S7G2S5Vnf;Vnew;A2A2S5Z20000000M3Z8004M4A2A2S1S6G0S4eVA;Vrb;A2M5A2S1S8S5S5S5G5G3A2G4A2Z8A2SbZ2Z3eA2A2S1S0S21G5S5S5S74S73VA;A1A1M6S7Vc;Z100000000A2A2G1A2A3S1S1S6Z1Vc;A2S6Vc;Z1eA2A2S1S6Z100080000000G6A2S6S5S5G6Z2000000000A2Z1000A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  destruct (new_nums A rb CF PF) as (N1 & N2 & N3 & N4 & _ & N6 & _ & N8 & N9 & N10 & _). cbn zeta in N1, N2, N3, N4, N6, N8, N9, N10. fold nv c cs in N1, N2, N3, N4, N6, N8, N9, N10. fold S nf au new in N1, N2, N3, N4, N6, N8, N9, N10.
  unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. clear; lia. }
  split; [exact N1|]. split; [clear -N2; lia|]. split; [clear -N3 N6; lia|]. split; [exact N4|]. split; [exact N8|]. split; [clear -N4 N9 N10; lia|].
  split; [rewrite FAr; clear -C1 G13; lia|]. split; [rewrite FAr; clear -C1 G13 G14 TG; lia|]. split; [exact FAr|]. split; [exact C1|]. split; [exact G13|]. clear -G14 TG; lia.
Qed.

Definition JRfill (i : Z) : jpredA := ltac2:(tb__ "0|3|
SeS24S3aQ40M0A1M1A1S24S5cA1S5bS1S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vi;A1R4R3R2R1AaS1S0G1S15R4S40A2S3bG0S5Vi;Z1M2A2A2A3S1S0G1S15R4S41A2S3bG0S5Vau;S7Vi;VS;A2A2A2A3S0G1S15R4S43A2S3bG0S5S4eVA;Vrb;A2S7Z4S9S9S5Vnf;Vnew;A2G2A2Vi;A2A2A2A2A3A2A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRfill_K : ltac2:(tb__ "0|0|
S21S75VKc;S38R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRfill_stable : ltac2:(tb__ "0|0|
S21S22S0S25S62S45R1A2S27A3S37S35R2S38R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H0 & H2 & H3). apply Pos.leb_le in Hn. unfold LNX in Hn.
  split; [|split; [|split]].
  - eapply (JR_stable A Kc rb tp0 md0 (phL i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw LV0) by (unfold LV0; lia). exact H0.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV2) by (unfold LV2; lia). exact H2.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV3) by (unfold LV3; lia). exact H3.
Qed.

Lemma zone_fill : ltac2:(tb__ "0|3|
S21S21S6Z0R2A2S2S4fVA;Vrb;S39S5R3Z1M0A2A1R2A4S4S4fVA;Vrb;S39R3A1R2A4S1S6S5S4eVA;Vrb;A2S7Z4M1S9S9S5Vnf;Vnew;A2G0A2R3A2A2A2M2R2A2S8R2S5G2G1A2A2A2A2A2F_;Fz;Fi;").
Proof.
  intros i z Hi. unfold zoneR, phL. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. unfold gh_nf. fold nv c cs nf new.
  split.
  - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; try (left; tauto).
    + destruct (Z.eq_dec i 0) as [->|NZ]; [right; clear -H; lia|].
      destruct (Z_lt_dec z (FAb A rb + 4 * (nf + new - 1 - i) + 4)) as [L|G]; [right; clear -H L; lia | left; right; right; right; right; left; clear -H G NZ Hi; lia].
  - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H]; try tauto.
    + right; right; right; right; left. clear -H Hi. lia.
    + right; right; right; right; left. clear -H Hi. lia.
Qed.

Lemma fill_release : ltac2:(tb__ "0|3|
S20S24ScA1M0SeS24S3aQ40A1A1S24S5cA1M1S6cS5bS5bS21S1S6Z0R1A2S8R1Vnew;A2A2S0G0S14RaA1S2bScR9S23ScS5fS26ScA1A3M2A3A3S1fS35R9RbS2dG1S6dR7S6eR6R5A2A4A4S38R4RaR9R8R5A5S4dVA;VKc;Vrb;Vtp0;Vmd0;S39S5R5Z1A2A1S3fRbG2R8A3RaR9R6AaF_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FSt;").
Proof.
  intros St K r2 tp tr ms md mdJ i Hi HO Hsm ((HFz & HGh & HKc' & HM & HR & HRM) & H0 & H2 & H3).
  destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  set (r3 := rho_absorb r2 [O_fcell] ms). set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  assert (RC : obj_range r2 O_fcell = (Ci, Ci + 4)).
  { unfold O_fcell, O_cell. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite H3, u64_lit by (clear -CiR N5 N6 N7 N8; lia). f_equal; clear; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).
  assert (AIS : 0 <= au + i * S /\ au + i * S <= 3758096384) by (clear -Hi N1 N2 N3; nia).
  assert (M3C : cell_ok m3 (mkACell Ci 4 ((au + i * S) / 16))).
  { intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (absorb_obj r2 St tr ms md K [O_fcell] O_fcell Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SAlu ALU_SRL (SVar LV2) (SLit 4))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_fcell O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H3, soff_lit_small, u64_lit in ASb by (clear -CiR N5 N6 N7 N8; lia).
    assert (EV : alu64 ALU_SRL (rw r2 LV2) (Z_to_bv 64 4) = Z_to_bv 64 ((au + i * S) / 16)).
    { apply bv_eq. rewrite srl_val, H2, !u64_lit.
      - change (4 mod 64) with 4. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity.
      - pose proof (Z.div_pos (au + i * S) 16 ltac:(clear -AIS; lia) ltac:(clear; lia)). pose proof (Z.div_le_upper_bound (au + i * S) 16 (2 ^ 30) ltac:(clear; lia) ltac:(clear -AIS; lia)). clear -H H1. lia.
      - clear -AIS. lia. }
    rewrite EV in ASb. unfold m3. rewrite view_in by (clear -CiR N5 N6 N7 N8 Hj; lia). fold Ci in ASb. replace (Ci + 0 + Z.of_nat j) with (Ci + Z.of_nat j) in ASb by (clear; lia). exact ASb. }
  assert (AGR : forall z, ~ (Ci <= z < Ci + 4) -> m3 z = m2 z).
  { intros z Hz. unfold m3, r3. apply view_absorb_out. intros o [<-|[]]. rewrite RC. cbn [fst snd]. exact Hz. }
  pose proof (zone_fill i) as ZI. fold Ci in ZI.
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|].
  split; [unfold mlink, phL in HM |- *; cbn [ph_u ph_f] in HM |- *; exact HM|].
  split.
  - fold m3. unfold rlink in HR |- *. fold m2 in HR. destruct HR as (L1 & L2 & L3 & _).
    split; [intros z Hz; rewrite AGR by (intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); right; exact X); apply L1; intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); left; exact X|].
    split.
    { intros z Hz. apply (ZI z ltac:(clear -Hi; lia)) in Hz.
      assert (D : Ci <= z < Ci + 4 \/ ~ (Ci <= z < Ci + 4)) by (clear; lia).
      destruct D as [D|D].
      - pose proof (M3C (Z.to_nat (z - Ci)) ltac:(cbn [c_w]; clear -D; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
        replace (Ci + Z.of_nat (Z.to_nat (z - Ci))) with z in X by (clear -D; lia). rewrite X. discriminate.
      - rewrite (AGR z D). destruct Hz as [Hz|Hz]; [exact (L2 z Hz) | contradiction]. }
    split.
    { intros j Hj. cbn [ph_fill phL] in Hj |- *. unfold gh_nf. fold nv c cs nf new au S.
      destruct (Z.eq_dec j i) as [->|NE]; [exact M3C|].
      eapply cell_ok_agree_range; [|apply (L3 j); cbn [ph_fill phL]; clear -Hj NE; lia].
      cbn [c_addr c_w]. unfold gh_nf. fold nv c cs nf new. intros z Hz. apply AGR. change (Z.of_nat 4) with 4 in Hz. unfold Ci. clear -Hz Hj NE. lia. }
    cbn [ph_pop ph_cnt ph_ri phL]. split; [intros x Hx; exfalso; clear -Hx; lia|]. split; intros X; discriminate X.
  - apply (rmlink_absorb _ r2 [O_fcell] ms HRM). intros o [<-|[]]. rewrite RC. cbn [fst snd]. right. unfold IMG_HI. clear -CiR N5 FAr C1 G13. lia.
Qed.

Variable F : nat.
Variables (CL0 : axst) (LB LX : leafA) (nobF : nat) (s_bk : wsub).
Let CL1 : axst := cL1 CL0.
Hypothesis SK_l : ltac2:(tb__ "0|1|
S0S24S2cS2cSdSdA2SdA2M0A1S65ScG0S69S14S30VCL0;A1A1A4S65ScG0S69S2bScS79VW;A1S23ScS70S23ScS71S23ScS49S23ScS4aS26ScA1A3A3A3A3A3A4A3").
Hypothesis XX_l : ax_X CL0 = [].
Hypothesis XF_l : ltac2:(tb__ "0|0|
S6bS11S78VW;Vst;A2S16S30VCL0;A1A1A3").
Hypothesis NX_l : ltac2:(tb__ "0|0|
S0S25S63S13S30VCL0;A1A1S45A2S27A3").
Hypothesis W_l1 : ltac2:(tb__ "0|0|
S0S25S19S30VCL1;A1A1S27A3").
Hypothesis R_l1 : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41740S23S21Z4174cS26S21A1A3A3VCL1;S27A5S2aG0S23S32VLB;S23S32VLX;S26S32A1A3A3A2A3").
Hypothesis LN_l1 : ltac2:(tb__ "0|0|
S0S25S17S30VCL1;A1A1S28A3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLB;A1A1A1M0S2bScS64ScVnobF;G0A3S23ScS5fS26ScA1A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLX;A1A1A1M0S2bScS64ScVnobF;G0A3S23ScS5fS26ScA1A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S0S25S34S44S31VLB;A1VnobF;A2VCL0;Vs_bk;A3S27A3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S0S25S3eVs_bk;S42A2S27A3").
Hypothesis S_bk0 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S40A2SfS56S12S40A1S10Z1A1A3A3").
Hypothesis S_bk2 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S41A2SfS56S12S41A1S12S72A1A3A3").
Hypothesis S_bk3 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S43A2SfS56S60SfS57SfS59S12S40A1S10ZffffffffffffffffA1A3S10Z2A1A3A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S6aS11S61S16S30S31VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S6aS11S1bS61A1S16S30S31VLX;A1A1A1A3").

Lemma faend_val : ltac2:(tb__ "0|0|
SeS50Vrb;R1A2S51VA;Vrb;R2A3S0S21S3cQ40S1cR3S60A2A2S5S4eVA;Vrb;A2S7Z4S5Vnf;Vnew;A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (need_val A rb r CF PF HGh) as NV. fold nv c cs nf new in NV.
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). fold nv c in E158.
  unfold faend_e. cbn [eval]. rewrite add_val. fold (eval r need_e). rewrite NV.
  unfold fa_e2, rb_e, vSB, V_CLS. cbn [eval]. rewrite !add_val, sll_val, E155, E158, !u64_lit by (clear -C1 G13 G14; lia).
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 32)) by (clear -C1; lia).
  rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by (clear -C1 G13 G14; lia). rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by (clear -C1 G13 G14; lia).
  rewrite Z.mod_small by (clear -C1 G13 G14 N4 N5 N6; lia). rewrite FAr. clear; lia.
Qed.

Lemma fill_carve : ltac2:(tb__ "0|0|
S21SeS24S3aQ40A1A1S5eS1S6Z0R4A2S8R4Vnew;A2A2S36S35S38R5A1VCL0;R4R3R2A6S36S35S38R6A1VCL1;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof H as [HsmA HJ]. pose proof HJ as ((HFz & HGh & _ & _ & HR & _) & H0 & H2 & H3).
  set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & _ & _ & _ & _ & _ & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CL0) [O_pcc0; O_st; O_pcm; O_ri] r _ HW HE HFz Hsm SK_l XF_l) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  assert (E3 : bv_unsigned (eval r (SVar LV3)) = Ci) by (cbn [eval]; rewrite H3; apply u64_lit; clear -CiR N5 N6 N7 N8; lia).
  apply (SPA_carve_unk segs (JRfill i) r CL0 tp w (SVar LV3) (SLit 0) (SLit 4) LNX H W_l1 ltac:(apply Pos.eqb_eq in NX_l; rewrite NX_l; apply Pos.le_refl));
    rewrite ?E3, ?soff_lit_small by (clear; lia).
  - clear; lia.
  - clear; lia.
  - clear -CiR N5 N7; lia.
  - clear -CiR N5 N6 N7 N8; lia.
  - replace (Ci + 0) with Ci by (clear; lia). rewrite EO. apply Forall_app. split.
    + apply BZ. right; left. rewrite kSpaceSize_val. rewrite FAr in CiR. clear -CiR N5 N6 C1. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; rewrite FAr in CiR; clear -CiR N5 N6 C1 T1 PS1; lia.
  - intros a Ha. assert (Ha64 : 0x646000 <= a < 2 ^ 64) by (rewrite FAr in CiR; clear -Ha CiR N5 N6 C1 G13 G14; lia).
    pose proof (HDEF i (view segs (rm r)) ltac:(clear -Hi; lia) HR a ltac:(clear -Ha CiR; lia)) as D. rewrite view_in in D by (clear -Ha64; lia).
    pose proof (wok_rd_off_image (rm r) a) as WK.
    destruct (rd_of segs (rm r) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
  - unfold xwords_clear. rewrite XX_l. intros rr y j [].
Qed.

Lemma fill_iter : ltac2:(tb__ "0|1|
S21SeS24S3aQ40A1A1S5dS1S6Z0R4A2S8R4Vnew;A2A2S8S5R5Z1M0A2Vnew;A2SeVTR;S36S35S38S5R7G0A2A1VCL0;R1R5A5R4A2Fr';F_;S0S21S5R6G0A2Vnew;A3SeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S44S31VLX;A1VnobF;A2R1R6A5R5A2Fr';F_;VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  apply (tr_pre Kc TR KIT (SPA segs (JRfill i) CL1 r tp)); [intros w Hw; exact (fill_carve i r tp w Hi Hw)|].
  apply (tr_run Kc TR KIT F [0x41740; 0x4174c] CL1 [LB; LX] (JRfill i) r tp Q (JRfill_K i) (JRfill_stable i (ss_next (ax_S CL1)) eq_refl) R_l1 LN_l1).
  intros L r2 HL Hag.
  set (JREL := (fun r' t tr md => JRp (phL (i + 1)) r' t tr md /\ rw r' LV0 = rw r2 LV0 /\ rw r' LV2 = rw r2 LV2) : jpredA).
  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nobF (ss_objs (ax_S (la_state LL))) ++ [O_fcell] ->
            forall w, SPA segs (JRfill i) (la_state LL) r2 tp w ->
              exists r3, SPA segs JREL (keepn (la_state LL) nobF) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_fcell] (vms md tp ms)).
    apply (SPA_unobj_J (JRfill i) JREL r2 (la_state LL) _ [O_fcell] tp tr ms md HO Hw).
    intros Hsm HJ. split; [|split; reflexivity].
    exact (fill_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm HJ). }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < new /\ rw r2 LV0 = Z_to_bv 64 (i + 1) /\ rw r2 LV2 = Z_to_bv 64 (au + i * S))).
    { intros w [_ ((HFz & HGh & _) & H0 & H2 & _)]. split; [|split; [exact H0 | exact H2]].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia). apply Z.ltb_lt in BF. exact BF. }
    intros (Hlt & H0 & H2).
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LB OB_b)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRfill (i + 1)) CL0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J JREL (JRfill (i + 1)) _ CL0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & E0 & E2). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    assert (AIS : 0 <= au + i * S /\ au + (i + 1) * S <= 3758096384) by (clear -Hi Hlt N1 N2 N3; nia).
    split; [|split; [|split]].
    + eapply (JR_stable A Kc rb tp0 md0 (phL (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk0. cbn [eval]. rewrite E0, H0. apply bv_eq. rewrite add_val, !u64_lit by (clear -Hi N4; lia). rewrite Z.mod_small by (clear -Hi N4; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk2. unfold V_SIZE. cbn [eval]. rewrite E2, H2, E148. apply bv_eq. rewrite add_val, !u64_lit by (clear -AIS N1; lia).
      rewrite Z.mod_small by (clear -AIS N1; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk3. cbn [eval]. fold (eval r3 faend_e). apply bv_eq.
      rewrite add_val, (faend_val r3 HFz HGh), sll_val, xor_val, E0, H0.
      replace (bv_unsigned (Z_to_bv 64 18446744073709551615)) with 18446744073709551615 by reflexivity.
      rewrite !u64_lit by (clear -Hi N4 N5 N6 N7 N8; lia). rewrite lxor_ones64 by (clear -Hi N4; lia).
      change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia).
      replace (((18446744073709551615 - (i + 1)) * 2 ^ 2) mod 2 ^ 64) with (2 ^ 64 - 4 * (i + 2)).
      2: { apply (Z.mod_unique_pos _ _ 3); [clear -Hi N4; lia | clear; lia]. }
      rewrite (u64_lit (FAb A rb + 4 * (nf + new - 1 - (i + 1)))) by (clear -Hi Hlt N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -Hi Hlt N4 N5 N6 N7 N8; lia | clear; lia].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = new)).
    { intros w [_ ((HFz & HGh & _) & H0 & _)].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia).
      destruct (Z.ltb_spec (i + 1) new) as [X|X]; [exfalso; apply BF; reflexivity | clear -X Hi; lia]. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LX OB_x)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phL new)) (keepn (la_state LX) nobF) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J JREL (JRp (phL new)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma fill_loop : ltac2:(tb__ "0|0|
S2fS21SeS24S3aQ40A1A1S5dS0S21S9Vnew;R4A2SaR5A1A3S1S6Z0R5A2S8R5Vnew;A2A2SeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S44S31VLX;A1VnobF;A2R1R5A5R4A2Fr';VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [clear -Hn Hi; lia|].
  apply (fill_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [clear -Hn; lia | clear -Hi Hlt; lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variables (E3 LH : axst) (LFL LJP : leafA) (s_in : wsub).
Let FR : list sprop := factsQ E3.
Let XLF : axst := ltac2:(tb__ "0|0|
S44S31VLX;A1VnobF;A2").
Let CXL : axst := cXL FR XLF.
Hypothesis R_h : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41740S26S21A1A3VLH;S27A5S2aG0S23S32VLFL;S26S32A1A3A2A3").
Hypothesis LN_h : ltac2:(tb__ "0|0|
S0S25S17S30VLH;A1A1S28A3").
Hypothesis NX_h : ltac2:(tb__ "0|0|
S0S25S62S42S13S30VLH;A1A1A2S27A3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S0S25S34S31VLFL;A1VCL0;Vs_in;A3S27A3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S0S25S3eVs_in;S42A2S27A3").
Hypothesis S_in0 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S40A2S10Z1A1A3").
Hypothesis S_in2 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S41A2S4bA3").
Hypothesis S_in3 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S43A2SfS56S60S10N4A1A3A3").
Hypothesis W_xl : ltac2:(tb__ "0|0|
S0S25S19S30VCXL;A1A1S27A3").
Hypothesis D_xl : ltac2:(tb__ "0|4|
S0S29S2cS24S2cSdSdA2M0A1M1S24S11A1M2A2M3A1S6fS30VXLF;A1S30VCXL;A1A2S2aG3S2dG1G2S26G0A1S23S11S46S23S11S47S26S11A1A3A3A4A2A3").
Hypothesis NX_xl : ltac2:(tb__ "0|0|
S0S25S63S13S30VCXL;A1A1S13S30VXLF;A1A1A2S27A3").
Hypothesis R_j : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z413ccS26S21A1A3VCXL;S27A5S2aG0S23S32VLJP;S26S32A1A3A2A3").
Hypothesis LN_xl : ltac2:(tb__ "0|0|
S0S25S17S30VCXL;A1A1S28A3").
Hypothesis NXr_xl : ltac2:(tb__ "0|0|
S0S25S62S42S13S30VCXL;A1A1A2S27A3").

Theorem fill_all : ltac2:(tb__ "0|0|
SeS24S3aQ40A1A1S5dSeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S31VLJP;A1R1R3A5R2A2Fr';VTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41740] LH [LFL] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _.
  apply (tr_pre Kc TR KIT (SPA segs (JRfill 0) CL0 (rho_sub r1 s_in) tp)).
  { intros w Hw. apply (SPA_entails_J (JRp ph) (JRfill 0) _ CL0 s_in r1 tp w ENT_in); [|exact Hw].
    intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
    split; [|split; [|split]].
    - rewrite phL0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    - cbn [rho_sub rw]. rewrite S_in0. reflexivity.
    - cbn [rho_sub rw]. rewrite S_in2. unfold vAU. cbn [eval]. destruct HGh as (_ & _ & _ & Q223 & _). fold nv c cs au in Q223. rewrite Q223. f_equal. clear; lia.
    - cbn [rho_sub rw]. rewrite S_in3. cbn [eval]. fold (eval r1 faend_e). apply bv_eq. rewrite add_val, (faend_val r1 HFz HGh).
      replace (bv_unsigned (Z_to_bv 64 (-4))) with 18446744073709551612 by reflexivity. rewrite u64_lit by (clear -N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -N4 N5 N6 N7 N8; lia | clear; lia]. }
  apply (fill_loop (Z.to_nat new) 0 _ tp Q); [clear -N4; lia | clear -N4; lia|].
  intros r2. fold XLF.

  apply (jr_restate A Kc rb tp0 md0 TR KIT XLF (ax_S CXL) _ _ (phL new) r2 tp Q W_xl D_xl NX_xl).
  { intros tr md (HFz & HGh & _) _. split; [constructor|].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    destruct (new_nums A rb CF PF) as (_ & M2 & M3 & _ & M5 & M6 & _). cbn zeta in M2, M3, M5, M6. fold nv c cs in M2, M3, M5, M6. fold S nf au new in M2, M3, M5, M6.
    destruct HGh as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227. fold nf au new in Q221, Q223, Q228.
    destruct (kchunks_facts c C1) as (K1 & _).
    assert (NS : 0 <= new * S <= 3758096384) by (clear -N1 N2 N3 N4; nia).
    repeat apply Forall_cons; try apply Forall_nil.
    - unfold HINT_au. cbn [holds]. unfold branch_taken, bv_ltu, vMU, vAU, vNEW, V_SIZE. cbn [eval]. rewrite !add_val, mul_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N4 M2 M3; lia).
      rewrite (Z.mod_small (new * S)) by (clear -NS; lia). rewrite !Z.mod_small by (clear -NS N2 M2 M3; lia).
      intros X. apply Z.ltb_lt in X. clear -X M6. lia.
    - unfold HINT_k. cbn [holds]. unfold branch_taken, bv_ltu, vNF, vNEW, vK. cbn [eval]. rewrite add_val, Q221, Q227, Q228, !u64_lit by (clear -N4 N5 N6 K1; lia).
      rewrite Z.mod_small by (clear -N4 N5 N6; lia). intros X. apply Z.ltb_lt in X. clear -X M5 N5. lia. }
  change (ax_setS XLF (ax_S CXL)) with CXL.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x413cc] CXL [LJP] (phL new) r2 tp Q R_j LN_xl NXr_xl).
  intros L r3 [<-|[]] _. exact (HX r3).
Qed.
End FILL.
End SpineMallocQ13.

(* [comment removed for export] *)
Module SpineCallocRu0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "valuation"; "rw"; "swf"; "ss_facts"; "ss_lenient"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "axst"; "leafA"; "sym_runA"; "ax_X"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "cons"; "prod"; "app"; "false"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu0"; "r_u1_0"; "r_u2_0"; "e3u"; "cellsf_u"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0"; "W0"; "e3r"; "FUEL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1"; "cU0"; "cU1"; "kU1"; "kU2"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "inclb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineCallocU2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_u1__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5").
Local Strategy expand [R_u1__R].
Definition r_u1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_u1__R).
Definition r_u1_0 := Eval vm_compute in (nth 0 r_u1 (mkLeafA (cU0 e3r) RsCut)).
Definition cu1 := Eval vm_compute in (cU1 (la_state r_u1_0)).
Definition r_u2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41260] cu1 true with Some l => l | None => [] end).
Definition r_u2_0 := Eval vm_compute in (nth 0 r_u2 (mkLeafA cu1 RsCut)).
Definition cellsf_u := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (la_state r_u2_0))) O_pcc0)).
Definition e3u := Eval vm_compute in (eU (la_state r_u2_0)).
Lemma E3u_eq : ltac2:(tb__ "0|0|
S0ScS2cSaS1bA1A1S1cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma WU0 : ltac2:(tb__ "0|0|
S0S10S6SbS24S22A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u1 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5S18G0S14SdS1aS13SdA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_u1__R <: R_u1__R = Some [r_u1_0]). Qed.
Lemma LN_u1 : ltac2:(tb__ "0|0|
S0S10S8SbS24S22A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u1 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS24S22A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM1 : ltac2:(tb__ "0|1|
S0S10S29S32SaS1aA1M0A1S2dG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_s1 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbS2fSaS1aA1M0A1A1A1M1S16S1S31S1S38S32G0A1U2A2G1A3S14S1S3fS14S1S2bS13S1A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_k1 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS26SaS1aA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k1b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS26SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k1 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS26SaS1aA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c1 : ltac2:(tb__ "0|0|
S0S10S6SbS25SaS1aA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u2 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ41260S13S1eA1A3S25SaS1aA1A1S11A5S18G0S14SdS1bS13SdA1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_u2 : ltac2:(tb__ "0|0|
S0S10S8SbS25SaS1aA1A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u2 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS25SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_u2 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbSaS1bA1M0A1A1M1S16S1S31S1S38S32G0A1U1A2G1A3S14S1S2aS1dA1S13S1A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ARR_ok : arr_okb cellsf_u = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_k2 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS27SaS1bA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k2b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS27SaS1bA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k2 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS27SaS1bA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c2 : ltac2:(tb__ "0|0|
S0S10S6SbS28SaS1bA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM2 : ltac2:(tb__ "0|1|
S0S10S29S32S28SaS1bA1A1M0A1S2eG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_uninit_i : ltac2:(tb__ "0|4|
S12S15S1eS1eA2A1M0G0S48R2A1S49R2A1S40S34S12S15ScS3dA2A1F_;F_;S4aR5R4R1A3ScScS0ScR2S22A3S0ScR2S1cA3S40S34S4S12S4cQ40M1A1M2A1S39S39OF_;F_;S47R4R1A2S35R5A1S0S10S41R7A1S17A3S0S1eS4bR8S4dG1S5R6PcA2A2A2Z0A3S4S4S0S1fG2F_;S5R2A1S5R9A1A3R8S3bS20S44S21S33S46RcA1M3RbR3A5RfR2R9A5S3cS20S3aR3R9R12G3RbA2A5A2F_;FrX;Frho1;S4R7S3bS20S44S21S33RbRaR9A5RfR1R8A5S3cS20S3aR9R8R11RbRaA2A5A2FrhoE;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3U;FE3;FHPF;FPFam;FHXGL;FHCST;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL PFam HPF E3 E3U -> ->. rewrite <- E3u_eq.
  intros A Kc rho tp TR KIT HKc Hini Hcnt HCONT.
  exact (refill_uninit CST XGL HCST HXGL PFam HPF 0 UStopLe FUEL e3r r_u1_0 r_u2_0 cellsf_u SK3 XX3 (inclb_incl _ _ XF3b) WU0 R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 (inclb_incl _ _ XF_k1b) XX_k1 W_c1
           R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 (inclb_incl _ _ XF_k2b) XX_k2 W_c2 PERM2 A Kc rho tp TR KIT HKc HW0 Hini Hcnt HCONT).
Qed.
End SpineCallocRu0.

(* [comment removed for export] *)
Module SpineCallocRu1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "valuation"; "rw"; "swf"; "ss_facts"; "ss_lenient"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "axst"; "leafA"; "sym_runA"; "ax_X"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "cons"; "prod"; "app"; "false"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu1"; "r_u1_0"; "r_u2_0"; "e3u"; "cellsf_u"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1"; "W0"; "e3r"; "FUEL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1"; "cU0"; "cU1"; "kU1"; "kU2"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "inclb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineCallocU2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_u1__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5").
Local Strategy expand [R_u1__R].
Definition r_u1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_u1__R).
Definition r_u1_0 := Eval vm_compute in (nth 0 r_u1 (mkLeafA (cU0 e3r) RsCut)).
Definition cu1 := Eval vm_compute in (cU1 (la_state r_u1_0)).
Definition r_u2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41260] cu1 true with Some l => l | None => [] end).
Definition r_u2_0 := Eval vm_compute in (nth 0 r_u2 (mkLeafA cu1 RsCut)).
Definition cellsf_u := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (la_state r_u2_0))) O_pcc0)).
Definition e3u := Eval vm_compute in (eU (la_state r_u2_0)).
Lemma E3u_eq : ltac2:(tb__ "0|0|
S0ScS2cSaS1bA1A1S1cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma WU0 : ltac2:(tb__ "0|0|
S0S10S6SbS24S22A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u1 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ411c4S13S1eA1A3S24S22A1S11A5S18G0S14SdS1aS13SdA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_u1__R <: R_u1__R = Some [r_u1_0]). Qed.
Lemma LN_u1 : ltac2:(tb__ "0|0|
S0S10S8SbS24S22A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u1 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS24S22A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM1 : ltac2:(tb__ "0|1|
S0S10S29S32SaS1aA1M0A1S2dG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_s1 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbS2fSaS1aA1M0A1A1A1M1S16S1S31S1S38S32G0A1U2A2G1A3S14S1S3fS14S1S2bS13S1A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_k1 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS26SaS1aA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k1b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS26SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k1 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS26SaS1aA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c1 : ltac2:(tb__ "0|0|
S0S10S6SbS25SaS1aA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u2 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ41260S13S1eA1A3S25SaS1aA1A1S11A5S18G0S14SdS1bS13SdA1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_u2 : ltac2:(tb__ "0|0|
S0S10S8SbS25SaS1aA1A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u2 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS25SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_u2 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbSaS1bA1M0A1A1M1S16S1S31S1S38S32G0A1U1A2G1A3S14S1S2aS1dA1S13S1A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ARR_ok : arr_okb cellsf_u = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_k2 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS27SaS1bA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k2b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS27SaS1bA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k2 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS27SaS1bA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c2 : ltac2:(tb__ "0|0|
S0S10S6SbS28SaS1bA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM2 : ltac2:(tb__ "0|1|
S0S10S29S32S28SaS1bA1A1M0A1S2eG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_uninit_i : ltac2:(tb__ "0|4|
S12S15S1eS1eA2A1M0G0S48R2A1S49R2A1S40S34S12S15ScS3dA2A1F_;F_;S4aR5R4R1A3ScScS0ScR2S22A3S0ScR2S1cA3S40S34S4S12S4cQ40M1A1M2A1S39S39OF_;F_;S47R4R1A2S35R5A1S0S10S41R7A1S17A3S0S1eS4bR8S4dG1S5R6PcA2A2A2Z0A3S4S4S0S1fG2F_;S5R2A1S5R9A1A3R8S3bS20S44S21S33S46RcA1M3RbR3A5RfR2R9A5S3cS20S3aR3R9R12G3RbA2A5A2F_;FrX;Frho1;S4R7S3bS20S44S21S33RbRaR9A5RfR1R8A5S3cS20S3aR9R8R11RbRaA2A5A2FrhoE;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3U;FE3;FHPF;FPFam;FHXGL;FHCST;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL PFam HPF E3 E3U -> ->. rewrite <- E3u_eq.
  intros A Kc rho tp TR KIT HKc Hini Hcnt HCONT.
  exact (refill_uninit CST XGL HCST HXGL PFam HPF 1 UStopLeOrPc FUEL e3r r_u1_0 r_u2_0 cellsf_u SK3 XX3 (inclb_incl _ _ XF3b) WU0 R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 (inclb_incl _ _ XF_k1b) XX_k1 W_c1
           R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 (inclb_incl _ _ XF_k2b) XX_k2 W_c2 PERM2 A Kc rho tp TR KIT HKc HW0 Hini Hcnt HCONT).
Qed.
End SpineCallocRu1.

(* [comment removed for export] *)
Module SpineMallocQU2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "valuation"; "ss_next"; "sprop"; "ss_facts"; "ss_lenient"; "swf"; "agree_below"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "la_state"; "@Corelib.Init.Datatypes"; "list"; "nil"; "cons"; "bool"; "true"; "prod"; "app"; "false"; "Some"; "option"; "pair"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQU1"; "cU1"; "cU0"; "kU1"; "kU2"; "JU"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "ulinkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"; "@Stdlib.Lists.List"; "incl"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "JRf"; "JLRf"; "L_rf"; "NXR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@Stdlib.ZArith.BinInt.Z"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.RebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQU1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section UCHAIN.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list Iface.ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
SaS40Vst;S3fA3SaS11S3eA1VW;S12S3eA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S38VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis Hini : aa_cache_inited A = false.
Notation JUp := (JU A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let T : Z := ag_thread (aa_geom A).

Lemma ju_run : ltac2:(tb__ "0|1|
S1cS11S1eA1SfS11ScA1M0S14S3S11S3cQ40A1A1S32SaS1aG0A1SdS1dR8R7R6S15A5S19G0R5A2A3SaS14S7SbR7A1A1S18A3SaS14S3bPdcS4SbR8A1A1A2S15A3ScS3S3aScR2RaA3S9S4SbRcA1A1R9R2A3VTR;S21S1dS27VA;VKc;Vrb;Vtp0;Vmd0;RbA6S10R4A1R3R9A5R8A2F_;F_;Fr';FL;VTR;S21S1dS27VA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Fr;Fs;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves s r tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JUp s) r tp Q (JU_K A Kc rb tp0 md0 s)); [|exact Hrun | exact Hl | exact HL].
  apply JU_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Variable F : nat.
Variable E3 : axst.
Variables LU1 LU2 : leafA.
Variable cellsF : list cell.
Let L1 : axst := la_state LU1.
Let L2 : axst := la_state LU2.
Hypothesis R_u1 : ltac2:(tb__ "0|1|
SaS1aS11ScA1M0A1SdS1dVF;S13S1eZ411c4S12S1eA1A3S24VE3;A1S15A5S19G0S13ScVLU1;S12ScA1A3A2A3").
Hypothesis LN_u1 : ltac2:(tb__ "0|0|
SaS14S7SbS24VE3;A1A1A1S18A3").
Hypothesis NX_u1 : ltac2:(tb__ "0|0|
SaS14S3bPdcS4SbS24VE3;A1A1A1A2S15A3").
Hypothesis PERM1 : ltac2:(tb__ "0|0|
SaS14S29S31VL1;A1S2dVL1;A1A2S15A3").
Hypothesis OB_s1 : ltac2:(tb__ "0|1|
SaS11S0A1S2SbS2fVL1;A1A1A1M0S17S0S20S0S3dS31VL1;A1U2A2G0A3S13S0S35S13S0S2bS12S0A1A3A3A3A3").
Hypothesis SK_k1 : ltac2:(tb__ "0|1|
SaS11S16S16S1S1A2S1A2M0A1S1fS0G0S22S2SbS25VL1;A1A1A1A4S1fS0G0S22S17S0S37VW;A1S13S0S34S12S0A1A3A3A4A3").
Hypothesis XF_k1 : ltac2:(tb__ "0|0|
S39S5S36VW;Vst;A2S6SbS25VL1;A1A1A1A3").
Hypothesis XX_k1 : ltac2:(tb__ "0|1|
SaS11S16S1S1A2M0A1SeS25VL1;A1A1S12G0A1A3").
Hypothesis W_c1 : ltac2:(tb__ "0|0|
SaS14S8SbS23VL1;A1A1A1S15A3").
Hypothesis R_u2 : ltac2:(tb__ "0|1|
SaS1aS11ScA1M0A1SdS1dVF;S13S1eZ41260S12S1eA1A3S23VL1;A1S15A5S19G0S13ScVLU2;S12ScA1A3A2A3").
Hypothesis LN_u2 : ltac2:(tb__ "0|0|
SaS14S7SbS23VL1;A1A1A1S18A3").
Hypothesis NX_u2 : ltac2:(tb__ "0|0|
SaS14S3bPdcS4SbS23VL1;A1A1A1A2S15A3").
Hypothesis OB_u2 : ltac2:(tb__ "0|1|
SaS11S0A1S2SbVL2;A1A1M0S17S0S20S0S3dS31VL2;A1U1A2G0A3S13S0S2aVcellsF;A1S12S0A1A3A3A3").
Hypothesis ARR_ok : arr_okb cellsF = true.
Hypothesis SK_k2 : ltac2:(tb__ "0|1|
SaS11S16S16S1S1A2S1A2M0A1S1fS0G0S22S2SbS26VL2;A1A1A1A4S1fS0G0S22S17S0S37VW;A1S13S0S34S12S0A1A3A3A4A3").
Hypothesis XF_k2 : ltac2:(tb__ "0|0|
S39S5S36VW;Vst;A2S6SbS26VL2;A1A1A1A3").
Hypothesis XX_k2 : ltac2:(tb__ "0|1|
SaS11S16S1S1A2M0A1SeS26VL2;A1A1S12G0A1A3").
Hypothesis W_c2 : ltac2:(tb__ "0|0|
SaS14S8SbS28VL2;A1A1A1S15A3").
Hypothesis PERM2 : ltac2:(tb__ "0|1|
SaS14S29S31S28VL2;A1M0A1S2eG0A1A2S15A3").

Lemma u_carve_arr : ltac2:(tb__ "0|1|
S3S11S3cQ40A1A1S33S21S1dS27VA;VKc;Vrb;Vtp0;Vmd0;S18A6M0S25VL1;A1R3R2R1A6S21S1dG0S23VL1;A1R4R3R2A6F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w Hsp. pose proof Hsp as [HsmA HJ]. destruct HJ as (HFz & _ & _ & HR & _). cbn [umem] in HR.
  destruct (u_nums A rb tp0 md0 W st rho HE) as (C1 & T1 & T2 & TG & TI & PCr). fold T in T1, T2, TI.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET.
  pose proof HE as (_ & HA & _). destruct (uninit_frame A rb tp0 md0 HA Hini) as (FZ & PRS). fold T in FZ, PRS.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S (kU1 L1)) [O_st] r _ HW HE HFz Hsm SK_k1 XF_k1) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|os [|? ?]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNs : obj_range r os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }

  assert (PR : forall z, T + 288 <= z < T + 2768 -> exists b, view segs (rm r) z = Some b).
  { intros z Hz. rewrite (HR z). destruct (Z_lt_dec z (T + 2688)) as [LT|GE]; [|apply PRS; clear -Hz GE; lia].
    exists (Z_to_bv 8 0). apply (FZ ((z - T - 208) / 80) z).
    - pose proof (Z.div_le_mono 80 (z - T - 208) 80 ltac:(clear; lia) ltac:(clear -Hz; lia)) as D1. change (80 / 80) with 1 in D1.
      pose proof (Z.div_lt_upper_bound (z - T - 208) 80 31 ltac:(clear; lia) ltac:(clear -LT; lia)) as D2. clear -D1 D2. lia.
    - pose proof (Z.div_mod (z - T - 208) 80 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (z - T - 208) 80 ltac:(clear; lia)) as MB. clear -DM MB. lia. }
  assert (ZB : forall c' j, 1 <= c' <= 30 -> (j < 4)%nat -> rd_of segs (rm r) (Z_to_bv 64 (T + (208 + 80 * c') + Z.of_nat j)) = Some (Z_to_bv 8 0)).
  { intros c' j Hc' Hj. pose proof (FZ c' (T + (208 + 80 * c') + Z.of_nat j) Hc' ltac:(clear -Hj; lia)) as Hb. rewrite <- (HR _) in Hb.
    rewrite view_in in Hb by (clear -Hc' Hj T1 T2 TG; lia). exact Hb. }
  apply (SPA_carve_list segs _ r (kU1 L1) tp w NU1 (nxt L1) Hsp W_c1).
  - apply Pos.le_refl.
  - unfold NU1. apply Forall_cons; [|apply Forall_nil].
    rewrite ET. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -T1; lia|]. split; [clear -T1 T2 TG; lia|].
    split.
    { unfold cells_inside, cnt_spec. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc'). apply In_CLS30 in Hc'. clear -Hc'. lia. }
    split.
    { intros off Hoff. destruct (PR (T + off) ltac:(clear -Hoff; lia)) as [b Hb]. rewrite view_in in Hb by (clear -Hoff T1 T2 TG; lia).
      eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hoff T1 T2 TG; lia | clear -Hoff TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX_k1; intros rr y j []].
    unfold cells_in_view, cnt_spec. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc'). apply In_CLS30 in Hc'.
    intros j Hj. cbn [eval]. rewrite (enc_bytes_zero_nth 4 (Z_to_bv 64 0) j ltac:(apply u64_lit; clear; lia) Hj). exact (ZB c' j Hc' Hj).
  - cbn [map carve_obj NU1]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite ET.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear. lia.
    + apply Forall_cons; [|apply Forall_nil]. rewrite RNs. unfold ranges_disjoint; cbn [fst snd]. clear. lia.
  - cbn [map carve_obj NU1 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma u_carve_cnt : ltac2:(tb__ "0|1|
S3S11S3cQ40A1A1S33S21S1dS27VA;VKc;Vrb;Vtp0;Vmd0;S15A6M0S26VL2;A1R3R2R1A6S21S1dG0S28VL2;A1R4R3R2A6F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w Hsp. pose proof Hsp as [HsmA HJ]. destruct HJ as (HFz & _ & _ & HR & _). cbn [umem] in HR. fold T in HR. destruct HR as (_ & L2' & L3).
  destruct (u_nums A rb tp0 md0 W st rho HE) as (C1 & T1 & T2 & TG & TI & PCr). fold T in T1, T2, TI, PCr. fold nv in C1, PCr. fold c in C1, PCr.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET. pose proof (pc_base_val A rb r CF RG) as EB. rewrite PCr in EB.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S (kU2 L2)) [O_st] r _ HW HE HFz Hsm SK_k2 XF_k2) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|os [|? ?]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNs : obj_range r os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }
  destruct (L3 c C1) as (K1 & _ & _).
  apply (SPA_carve_list segs _ r (kU2 L2) tp w NU2 (nxt L2) Hsp W_c2).
  - apply Pos.le_refl.
  - unfold NU2. apply Forall_cons; [|apply Forall_nil].
    rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 T1; lia|]. split; [clear -C1 T1 T2 TG; lia|].
    split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
    split.
    { intros off Hoff. pose proof (L2' (T + 208 + 80 * c + off) ltac:(unfold ZI, T; clear -Hoff C1; lia)) as D.
      destruct (view segs (rm r) (T + 208 + 80 * c + off)) as [b|] eqn:Eb; [|contradiction]. rewrite view_in in Eb by (clear -Hoff C1 T1 T2 TG; lia).
      eapply wok_rd_off_image2; [| |exact Eb]; [clear -Hoff C1 T1 T2 TG; lia | clear -Hoff C1 TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX_k2; intros rr y j []].
    apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. specialize (K1 j Hj). cbn [c_addr c_w RtCells.c_val] in K1.
    rewrite view_in in K1 by (clear -Hj C1 T1 T2 TG; lia). replace (T + 208 + 80 * c + 0 + Z.of_nat j) with (T + 208 + 80 * c + Z.of_nat j) by (clear; lia). exact K1.
  - cbn [map carve_obj NU2]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite EB.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear -C1. lia.
    + apply Forall_cons; [|apply Forall_nil]. rewrite RNs. unfold ranges_disjoint; cbn [fst snd]. clear -C1. lia.
  - cbn [map carve_obj NU2 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Theorem uninit_chain : ltac2:(tb__ "0|0|
S3S11S3cQ40A1A1S32S3S30VA;Vrb;R1A3VTR;S21S1dS45S49VA;A1VKc;Vc;Vnv;A4S2cVL2;A1R2R4A5R3A2F_;Fr';VTR;S21S1dS27VA;VKc;Vrb;Vtp0;Vmd0;S18A6S24VE3;A1R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  apply (ju_run F [0x411c4] (cU0 E3) [LU1] false r tp Q R_u1 LN_u1 NX_u1). intros L r1 [<-|[]] _. fold L1.

  destruct (perm_okb_sound _ _ PERM1) as (ND1 & LT1 & CV1).
  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (sU1 L1) r1 tp)).
  { intros w Hw. exact (SPA_select segs (JUp false) r1 L1 (idx1 L1) tp w Hw ND1 LT1 CV1). }
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JUp false) (kU1 L1) r2 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r1 [O_pcc0; O_pcmZ] (vms md tp ms)).
    apply (SPA_unobj_J (JUp false) (JUp false) r1 (sU1 L1) _ [O_pcc0; O_pcmZ] tp tr ms md OB_s1 Hw).
    intros Hsm HJ. exact (u_release1 A Kc rb tp0 md0 W st rho HE Hini _ _ r1 tp tr (vms md tp ms) (vmd md) md OB_s1 Hsm HJ). }
  intros r2.

  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (cU1 L1) r2 tp)); [intros w Hw; exact (u_carve_arr r2 tp w Hw)|].
  apply (ju_run F [0x41260] (cU1 L1) [LU2] false r2 tp Q R_u2 LN_u2 NX_u2). intros L r3 [<-|[]] _. fold L2.
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JUp true) (kU2 L2) r4 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_arrF cellsF] (vms md tp ms)).
    apply (SPA_unobj_J (JUp false) (JUp true) r3 L2 _ [O_arrF cellsF] tp tr ms md OB_u2 Hw).
    intros Hsm HJ. exact (u_release2 A Kc rb tp0 md0 W st rho HE _ _ cellsF r3 tp tr (vms md tp ms) (vmd md) md OB_u2 ARR_ok Hsm HJ). }
  intros r4.

  apply (tr_pure Kc TR KIT (ulinkR A rb r4)).
  { intros w [_ HJ]. exact (JU_ulink A Kc rb tp0 md0 r4 tp _ _ HJ). }
  intros HUL.
  apply (tr_pre Kc TR KIT (SPA segs (JRf (initA A) Kc c nv) (eU L2) r4 tp)); [|exact (HC r4 HUL)].
  intros w Hw. destruct (perm_okb_sound _ _ PERM2) as (ND2 & LT2 & CV2).
  apply (SPA_J (JUp true) (JRf (initA A) Kc c nv) (eU L2) r4 tp w).
  { intros HJ. exact (JRf_init CST XGL HCST HXGL A Kc rb tp0 md0 W st rho HE Hini r4 tp _ _ HJ). }
  exact (SPA_select segs (JUp true) r4 (cU2 L2) (idx2 (cU2 L2)) tp w (u_carve_cnt r4 tp w Hw) ND2 LT2 CV2).
Qed.
End UCHAIN.

Section UTOP.
Variable nW : nat. Variable st : ustop.
Let W : list Iface.ulink := Wcan nW.
Variable F : nat.
Variable E3 : axst.
Variables LU1 LU2 : leafA.
Variable cellsF : list cell.
Let L1 : axst := la_state LU1.
Let L2 : axst := la_state LU2.
Hypothesis SK3 : ltac2:(tb__ "0|1|
SaS11S16S16S1S1A2S1A2M0A1S1fS0G0S22S2SbVE3;A1A1A4S1fS0G0S22S17S0S37VW;A1S13S0S35S13S0S34S12S0A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S39S5S36VW;Vst;A2S6SbVE3;A1A1A3").
Hypothesis WU0 : ltac2:(tb__ "0|0|
SaS14S8SbS24VE3;A1A1A1S15A3").
Hypothesis R_u1 : ltac2:(tb__ "0|1|
SaS1aS11ScA1M0A1SdS1dVF;S13S1eZ411c4S12S1eA1A3S24VE3;A1S15A5S19G0S13ScVLU1;S12ScA1A3A2A3").
Hypothesis LN_u1 : ltac2:(tb__ "0|0|
SaS14S7SbS24VE3;A1A1A1S18A3").
Hypothesis NX_u1 : ltac2:(tb__ "0|0|
SaS14S3bPdcS4SbS24VE3;A1A1A1A2S15A3").
Hypothesis PERM1 : ltac2:(tb__ "0|0|
SaS14S29S31VL1;A1S2dVL1;A1A2S15A3").
Hypothesis OB_s1 : ltac2:(tb__ "0|1|
SaS11S0A1S2SbS2fVL1;A1A1A1M0S17S0S20S0S3dS31VL1;A1U2A2G0A3S13S0S35S13S0S2bS12S0A1A3A3A3A3").
Hypothesis SK_k1 : ltac2:(tb__ "0|1|
SaS11S16S16S1S1A2S1A2M0A1S1fS0G0S22S2SbS25VL1;A1A1A1A4S1fS0G0S22S17S0S37VW;A1S13S0S34S12S0A1A3A3A4A3").
Hypothesis XF_k1 : ltac2:(tb__ "0|0|
S39S5S36VW;Vst;A2S6SbS25VL1;A1A1A1A3").
Hypothesis XX_k1 : ltac2:(tb__ "0|1|
SaS11S16S1S1A2M0A1SeS25VL1;A1A1S12G0A1A3").
Hypothesis W_c1 : ltac2:(tb__ "0|0|
SaS14S8SbS23VL1;A1A1A1S15A3").
Hypothesis R_u2 : ltac2:(tb__ "0|1|
SaS1aS11ScA1M0A1SdS1dVF;S13S1eZ41260S12S1eA1A3S23VL1;A1S15A5S19G0S13ScVLU2;S12ScA1A3A2A3").
Hypothesis LN_u2 : ltac2:(tb__ "0|0|
SaS14S7SbS23VL1;A1A1A1S18A3").
Hypothesis NX_u2 : ltac2:(tb__ "0|0|
SaS14S3bPdcS4SbS23VL1;A1A1A1A2S15A3").
Hypothesis OB_u2 : ltac2:(tb__ "0|1|
SaS11S0A1S2SbVL2;A1A1M0S17S0S20S0S3dS31VL2;A1U1A2G0A3S13S0S2aVcellsF;A1S12S0A1A3A3A3").
Hypothesis ARR_ok : arr_okb cellsF = true.
Hypothesis SK_k2 : ltac2:(tb__ "0|1|
SaS11S16S16S1S1A2S1A2M0A1S1fS0G0S22S2SbS26VL2;A1A1A1A4S1fS0G0S22S17S0S37VW;A1S13S0S34S12S0A1A3A3A4A3").
Hypothesis XF_k2 : ltac2:(tb__ "0|0|
S39S5S36VW;Vst;A2S6SbS26VL2;A1A1A1A3").
Hypothesis XX_k2 : ltac2:(tb__ "0|1|
SaS11S16S1S1A2M0A1SeS26VL2;A1A1S12G0A1A3").
Hypothesis W_c2 : ltac2:(tb__ "0|0|
SaS14S8SbS28VL2;A1A1A1S15A3").
Hypothesis PERM2 : ltac2:(tb__ "0|1|
SaS14S29S31S28VL2;A1M0A1S2eG0A1A2S15A3").

Theorem refill_uninit : ltac2:(tb__ "0|3|
S4bS41S1eS1eS3S11S3cQ40A1A1S32S32OF_;F_;S4eR6R1A2S42R7A1SaS40Vst;S3fA3SaS11S3eA1VW;S12S3eA1A3F_;S4fS4dRaA1S4aA2SaS14S4cRbA1S18A3S44S1dS48R8R7S13S16SfS43A2M0S1bSfS43S47S46RcRbRaA3A4S12G0A1M1A3A5S32S3R8S21S1dS45S49ReA1M2RdRcRbA4S2cVL2;A1R1R9A5S44S1dS48R1R9S13G0S1bSfS43S47S46G2RdRcA3A4G1A3A5A2FrX;R8S21S1dS45ReRdRcRbA4VE3;RaR9A5R2A2F_;TQ;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;Fnv0;Fc0;FKc;FA;").
Proof.
  intros A Kc c0 nv0 rho tp TR KIT HKc HW HBUD Hini Q HCONT.
  apply (tr_cutP Kc TR KIT Model _ (fun md0 => (c0 = cls_of (bv_unsigned (rw rho 12%positive)) /\ nv0 = bv_unsigned (rw rho 12%positive)) /\ entryRq A rho tp md0 W st rho)
           (fun md0 => SPA segs (JU A Kc rho tp md0 false) (cU0 E3) rho tp) Q).
  { intros w Hw. exists (cfg_model (w_cfg w)). destruct (uninit_entry nW st E3 SK3 XX3 XF3 WU0 A Kc c0 nv0 rho tp w HW HBUD Hini Hw) as (E0 & HE & HS). exact (conj (conj E0 HE) HS). }
  intros md0 [[E0 E1] HE].
  refine (uninit_chain [] [] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.cst_ok_nil OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.xgl_ok_nil A Kc rho tp md0 TR KIT HKc W st rho HW HE Hini F E3 LU1 LU2 cellsF
            R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 XF_k1 XX_k1 W_c1 R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 XF_k2 XX_k2 W_c2 PERM2 rho tp Q _).
  intros r' HUL.
  apply (tr_post Kc TR KIT _ _ _ (fun w Hw => post_init A Kc rho Hini c0 r' tp w E0 HUL Hw)).
  rewrite <- E0, <- E1. exact (HCONT r').
Qed.
End UTOP.
End SpineMallocQU2.

(* [comment removed for export] *)
Module SpineMallocQu.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "swf"; "ss_facts"; "ss_lenient"; "ss_next"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "axst"; "sym_runA"; "ax_X"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "prod"; "app"; "false"; "Some"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQu"; "r_u1_0"; "r_u2_0"; "e3u"; "cellsf_u"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQU1"; "cU0"; "cU1"; "kU1"; "kU2"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi"; "e3r"; "W0"; "FUEL"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "JLRf"; "JRf"; "L_rf"; "NXR"; "Pre_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQU1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQU2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_u1__R : option (list leafA) := ltac2:(tb__ "0|0|
SdS1fS2eS10S1eZ411c4S11S1eA1A3S20S2cA1S12A5").
Local Strategy expand [R_u1__R].
Definition r_u1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_u1__R).
Definition r_u1_0 := Eval vm_compute in (nth 0 r_u1 (mkLeafA (cU0 e3r) RsCut)).
Definition cu1 := Eval vm_compute in (cU1 (la_state r_u1_0)).
Definition r_u2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41260] cu1 true with Some l => l | None => [] end).
Definition r_u2_0 := Eval vm_compute in (nth 0 r_u2 (mkLeafA cu1 RsCut)).
Definition cellsf_u := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (la_state r_u2_0))) O_pcc0)).
Definition e3u := Eval vm_compute in (eU (la_state r_u2_0)).
Lemma E3u_eq : ltac2:(tb__ "0|0|
S0ScS28S9S1bA1A1S1cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma WU0 : ltac2:(tb__ "0|0|
S0SfS4SaS20S2cA1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u1 : ltac2:(tb__ "0|1|
S0S18S13SbA1M0A1SdS1fS2eS10S1eZ411c4S11S1eA1A3S20S2cA1S12A5S17G0S10SbS1aS11SbA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_u1__R <: R_u1__R = Some [r_u1_0]). Qed.
Lemma LN_u1 : ltac2:(tb__ "0|0|
S0SfS6SaS20S2cA1A1A1S16A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u1 : ltac2:(tb__ "0|0|
S0SfS45PdcS7SaS20S2cA1A1A1A2S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM1 : ltac2:(tb__ "0|1|
S0SfS25S31S9S1aA1M0A1S29G0A1A2S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_s1 : ltac2:(tb__ "0|2|
S0S13S1A1S3SaS2bS9S1aA1M0A1A1A1M1S15S1S30S1S36S31G0A1U2A2G1A3S10S1S3aS10S1S27S11S1A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_k1 : ltac2:(tb__ "0|1|
S0S13S14S14S2S2A2S2A2M0A1S2fS1G0S32S3SaS22S9S1aA1A1A1A1A4S2fS1G0S32S15S1S44S2dA1S10S1S39S11S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k1b : ltac2:(tb__ "0|0|
S0SfS33S43S2dS3bA2S5SaS22S9S1aA1A1A1A1A2S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k1 : ltac2:(tb__ "0|1|
S0S13S14S2S2A2M0A1SeS22S9S1aA1A1A1S11G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c1 : ltac2:(tb__ "0|0|
S0SfS4SaS21S9S1aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u2 : ltac2:(tb__ "0|1|
S0S18S13SbA1M0A1SdS1fS2eS10S1eZ41260S11S1eA1A3S21S9S1aA1A1S12A5S17G0S10SbS1bS11SbA1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_u2 : ltac2:(tb__ "0|0|
S0SfS6SaS21S9S1aA1A1A1A1S16A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u2 : ltac2:(tb__ "0|0|
S0SfS45PdcS7SaS21S9S1aA1A1A1A1A2S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_u2 : ltac2:(tb__ "0|2|
S0S13S1A1S3SaS9S1bA1M0A1A1M1S15S1S30S1S36S31G0A1U1A2G1A3S10S1S26S1dA1S11S1A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ARR_ok : arr_okb cellsf_u = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_k2 : ltac2:(tb__ "0|1|
S0S13S14S14S2S2A2S2A2M0A1S2fS1G0S32S3SaS23S9S1bA1A1A1A1A4S2fS1G0S32S15S1S44S2dA1S10S1S39S11S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k2b : ltac2:(tb__ "0|0|
S0SfS33S43S2dS3bA2S5SaS23S9S1bA1A1A1A1A2S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k2 : ltac2:(tb__ "0|1|
S0S13S14S2S2A2M0A1SeS23S9S1bA1A1A1S11G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c2 : ltac2:(tb__ "0|0|
S0SfS4SaS24S9S1bA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM2 : ltac2:(tb__ "0|1|
S0SfS25S31S24S9S1bA1A1M0A1S2aG0A1A2S12A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_uninit_i : ltac2:(tb__ "0|3|
S47S3cS1eS1eS8S13S4dQ40A1A1S37S37OF_;F_;S4bR6R1A2S3dR7A1S4cS49R9A1S46A2S0SfS48RaA1S16A3S8R6S38S1fS3fS4aRcA1M0RbRaR9A4S1cR1R7A5S35S1fS41R1R7S10S14ScS34A2M1S19ScS34S40S3eG0RbRaA3A4S11G1A1M2A3A5A2FrX;R6S38S1fS3fRcRbRaR9A4S42R8R7A5S35S1fS41R8R7S10G1S19ScS34S40S3eRcRbRaA3A4G2A3A5A2F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;Fnv0;Fc0;FKc;FA;").
Proof.
  rewrite E3r_eq. rewrite <- E3u_eq.
  intros A Kc c0 nv0 rho tp TR KIT HKc HBUD Hini HCONT.
  exact (refill_uninit 0 UStopLe FUEL e3r r_u1_0 r_u2_0 cellsf_u SK3 XX3 (inclb_incl _ _ XF3b) WU0 R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 (inclb_incl _ _ XF_k1b) XX_k1 W_c1
           R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 (inclb_incl _ _ XF_k2b) XX_k2 W_c2 PERM2 A Kc c0 nv0 rho tp TR KIT HKc HW0 HBUD Hini HCONT).
Qed.
End SpineMallocQu.

(* [comment removed for export] *)
Module DrainG4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "SAlu"; "SPUle"; "valuation"; "sobj"; "eval"; "ss_facts"; "ss_next"; "swf"; "cell"; "holds"; "ss_lenient"; "ss_objs"; "@Corelib.Init.Datatypes"; "list"; "nil"; "cons"; "bool"; "prod"; "true"; "nat"; "Some"; "option"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1"; "JDg"; "entryG"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vMFA"; "addobjs"; "nxt"; "ri_e"; "rst"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "frozenD"; "rstD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "XFG"; "cCD"; "rupD_e"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vCTX"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4.GCH"; "mid_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "O_dstD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SMGlue PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillBits DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ci.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ci.DrainG3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition XFG : list sprop := ltac2:(tb__ "0|2|
S14S3S7S2dS4Z1ffc0000A1A2S14S3S7S4S45A1S2cA2S14S3S7S2cS4S3aS3aZ7fffff800000S46A2Z1000M0A2A1A2S14S3S7S4G0A1M1S40A2S14S3S7G1S3fA2S13S3A1A3A3A3A3A3").
Definition cG0 (n : Z) : axst := ltac2:(tb__ "0|1|
S31SbS1dS44Vn;A1M0A1A1G0S13S16S18S5A2A1S36A4").

Definition rupD_e (n : Z) : sv := ltac2:(tb__ "0|0|
S6S26S6S25S6S27S6S25S32S4Vn;A1A3S4Z2A1A3S4Z3ffffA1A3S4Zfffffffffffc0000A1A3").
Definition cCD (n : Z) (E : axst) : axst := ltac2:(tb__ "0|0|
S2eVE;S14S9S43Vn;S13SeA1A2S13S9A1A3S2fVE;A1A3").

Section GCH.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Hypothesis HE : ltac2:(tb__ "0|0|
S29Vn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Notation JDp := (JDg A Kc c rb tp0 md0).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let cs : class_state := SegQ_wf2.cls_of A c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let mfa : Z := cs_mapped_free_array cs.
Let B : Z := F0d A c.

Lemma xfg_holds : ltac2:(tb__ "0|0|
S8S34Vrb;R1A2S3bS3SfR2A1S36A3F_;Fr;").
Proof.
  intros r HFz. destruct (g_nums n A c rb tp0 md0 HE) as (_ & _ & _ & _ & T1 & _ & TG & _ & S1 & S2 & _ & _ & NF0 & NF1 & _ & _ & MC).
  destruct (g_evals n A c rb tp0 md0 HE r HFz) as (_ & _ & _ & _ & _ & ET & _ & E222). fold G in T1, TG, S1, S2, ET. fold T in T1, ET. fold SB in S1, S2. fold cs in E222, MC, NF1. fold mfa in E222, MC, NF1. fold nf in NF0, NF1.
  pose proof HE as (HA & _ & _ & (_ & E152 & E155 & _) & _). pose proof HA as (HG0 & _). fold G in HG0, E152, E155. fold SB in E155.
  pose proof (geom_old _ HG0) as HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & G8 & G9 & _).
  destruct HFz as [Fw _]. rewrite (Fw 152%positive) in E152 by lia. rewrite (Fw 155%positive) in E155 by lia.
  unfold vT in ET. cbn [eval] in ET.
  unfold XFG, HIGH_SHADOW_END, vMFA, vSB, vT, vCTX. rewrite kSpaceSize_val.
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E222, ?E155, ?E152, ?ET, ?u64_lit by lia.
  - lia.
  - exact S1.
  - lia.
  - exact T1.
  - exact G8.
Qed.

Lemma rupD_val : ltac2:(tb__ "0|0|
S8S34Vrb;R1A2S0S2aQ40A1SaR2S38Vn;A1A2SaR2S6S25S2dS4Z40000A1A3A2A3F_;Fr;").
Proof.
  intros r HFz. destruct (g_nums n A c rb tp0 md0 HE) as (_ & _ & K1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & NF0 & NF1 & NF2 & MM & MC).
  destruct (g_evals n A c rb tp0 md0 HE r HFz) as (_ & _ & _ & _ & _ & _ & E221 & E222). fold cs in NF0, NF1, NF2, MM, MC, E221, E222. fold nf in NF0, NF1, NF2, E221. fold mfa in NF1, NF2, MM, MC, E222.
  set (need := 4 * (nf + n)) in *.
  unfold rupD_e, vNF, vMFA. cbn [eval]. apply bv_eq. rewrite and_val, !add_val, sll_val, add_val, E221, E222.
  replace (bv_unsigned (Z_to_bv 64 18446744073709289472)) with 18446744073709289472 by reflexivity. rewrite !u64_lit by lia.
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (nf + n)) by lia. rewrite (Z.mod_small ((nf + n) * 2 ^ 2)) by lia.
  replace ((nf + n) * 2 ^ 2) with need by (unfold need; lia).
  rewrite (Z.mod_small (need + 262143)) by (unfold need; lia).
  rewrite land_m18_up by (unfold need; lia).
  rewrite (Z.mod_small (mfa + 262144)) by lia.
  destruct (proj1 (Z.mod_divide mfa 262144 ltac:(lia)) MM) as [q Hq].
  assert (E : (need + 262143) / 262144 = q + 1).
  { symmetry. apply Z.div_unique with (need + 262143 - (q + 1) * 262144); [left; unfold need in *; lia | lia]. }
  rewrite E, Hq. lia.
Qed.

Definition mid_okG (F : nat) (reg : nat) (cuts : list Z) (next_ok : axst -> Prop) (L : axst) : Prop := ltac2:(tb__ "0|9|
S1S0S15SdS1dS35VL;Vreg;A2M0A1M1A1S17A3S1S0S1aS16S12S16S5S5A2M2A1M3S12S3A1M4A2M5A1S3eS1dVL;A1M6G1A2S19G5S1bG3G4S14G2S1bS5S5S30S33A4S13G2A1A3S13S3A1A4A2A3S1S0S15S49ScG1A1M7ScG6A1A2S17A3S1S0S15S10G1A1S1cA3S1S0S15S4aPf0G7A2S17A3S2S12S1fA1M8G8S1S0S1aG8A1S22S23VF;Vcuts;G0S17A5S19G8R1A2A3S1fS39S1fR1R2A3Vnext_ok;S21R2A1A1F_;FL';A2Lleaves;A2A2A2A2A2A2").

Lemma g_mid : ltac2:(tb__ "0|1|
S18S18S12S3dA1S1eOF_;S1eS18S8S12S2aQ40A1A1M0S2bS42R9R8R7R6R5A5S1eS8G0RaR3A1VTR;S24S23S28VA;VKc;Vc;Vrb;Vtp0;Vmd0;R9A7R4R3R2A5R6A2F_;Ftp';Fr';FL';VTR;S24S23S28VA;VKc;Vc;Vrb;Vtp0;Vmd0;R6A7R7R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Ff;FL;Fnext_ok;Fcuts;Freg;FF;").
Proof.
  intros F reg cuts next_ok L f r tp Q (HW & HD & HNX & HLN & HNL & leaves & HRUN & HNEXT) HC.
  apply (jg_restate A Kc c rb tp0 md0 TR KIT L (ax_S (rstD L reg)) _ _ f r tp Q HW HD HNX).
  { intros tr md (HFz & _) _. split; [|constructor]. unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    exact (proj1 (proj2 (proj2 (g_evals n A c rb tp0 md0 HE r HFz)))). }
  change (ax_setS L (ax_S (rstD L reg))) with (rstD L reg).
  apply (jg_run A Kc c rb tp0 md0 TR KIT HKc F cuts (rstD L reg) leaves f r tp Q HRUN HLN HNL).
  intros L' r' HIn _. exact (HC (la_state L') r' tp (HNEXT L' HIn)).
Qed.

Lemma g_carve_dst : ltac2:(tb__ "0|3|
S1eS8S12S2aQ40A1A1S2bS0S12S16S16S5S5A2M0S5A2M1A1S3cS9G1S48S11S1dR4A1A1A4S41Vn;S13S9A1A2A3S39S3S47SbS1dR5A1A1A3S0S12G0A1S20R6A1S13G0A1A3S0S15SdS1dS37Vn;R7A2A1A1S17A3VTR;S24S23S28VA;VKc;Vc;Vrb;Vtp0;Vmd0;U3A7M2S37Vn;R8A2R7R6A5R5A2VTR;S24S23G2R9R8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Fr;FRL;").
Proof.
  intros RL r tp Q SK XF XX WF HT.
  apply (tr_pre Kc TR KIT _ _ Q) with (2 := HT). intros w Hw.
  pose proof (proj2 Hw) as HJ. pose proof HJ as (HFz & _ & _ & HR).
  destruct (g_nums n A c rb tp0 md0 HE) as (C1 & _ & K1 & _ & _ & _ & TG & _ & S1 & S2 & _ & _ & NF0 & NF1 & NF2 & MM & MC).
  destruct (g_piece n A c rb tp0 md0 HE) as (HB1 & HB2 & _ & FAv).
  destruct (g_evals n A c rb tp0 md0 HE r HFz) as (_ & _ & _ & EDS & _).
  fold G in TG, S1, S2, HB1, HB2, FAv, EDS. fold SB in S1, S2, HB1, HB2, FAv, EDS. fold cs in NF0, NF1, NF2, MM, MC, EDS. fold nf in NF0, NF1, NF2, EDS. fold mfa in NF1, NF2, MM, MC. fold B in HB1, HB2.
  assert (EBv : B = free_array SB c + mfa) by reflexivity.
  set (fa := free_array SB c) in *.
  pose proof (proj1 Hw) as HsmA. pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. destruct w as [tr [ms md]]. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (g_objs_miss n A c rb tp0 md0 HE (ax_S RL) [] r _ (fa + 4 * nf) (fa + 4 * nf + 4 * n) HFz Hsm SK XF
              ltac:(left; fold G SB; rewrite FAv; clear -C1 NF0 NF1 NF2 MC K1; lia)) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|? ?]; [|cbn [map] in SKx; discriminate SKx]. rewrite app_nil_r in EO.
  unfold cCD, addobjs, O_dstD.
  apply (SPA_carve_unk segs (JDp 3%nat) r RL tp _ dst_e (SLit 0) (SLit (4 * n)) (nxt RL) Hw WF ltac:(apply Pos.le_refl)); rewrite ?EDS, ?soff_lit_small by (clear -K1; lia).
  - clear -K1; lia.
  - clear -K1; lia.
  - rewrite FAv. clear -S1 C1 NF0. lia.
  - rewrite FAv. clear -S1 S2 TG C1 NF0 NF1 NF2 MC K1. lia.
  - replace (fa + 4 * nf + 0) with (fa + 4 * nf) by (clear; lia). rewrite EO. exact BZ.
  - intros a Ha. assert (Ha64 : 0x646000 <= a < 2 ^ 64) by (rewrite FAv in Ha; clear -Ha S1 S2 TG C1 NF0 NF1 NF2 MC K1; lia).
    assert (D : view segs (rm r) a <> None).
    { destruct (Z_lt_dec a B) as [LT|GE].
      -
        destruct (piece_numsG n A c rb tp0 md0 HE) as (_ & _ & _ & _ & Q2 & Q3). fold B in Q2, Q3.
        rewrite (rlinkG_view A c rb 3%nat r HR a) by (intros X; apply (zoneG_3 A c) in X; fold B in X; rewrite FAv in Ha; clear -X LT Ha Q3 S1 C1 NF0; lia).
        destruct HE as (HA & _). pose proof HA as (HG0 & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
        unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
        destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR & _).
        destruct (PR a ltac:(fold G SB fa nf mfa; clear -Ha LT EBv; lia)) as [b Hb].
        rewrite maskv_out in Hb; [change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA in Hb; rewrite Hb; discriminate|].
        apply fs_footb_space; [exact HG0|]. rewrite kSpaceSize_val. fold G SB. rewrite FAv in Ha. clear -Ha C1 NF0 NF1 NF2 MC K1. lia.
      - apply (proj2 HR). apply (zoneG_3 A c). right. fold B. clear -GE Ha EBv NF1 NF2 K1. lia. }
    rewrite view_in in D by (clear -Ha64; lia).
    pose proof (wok_rd_off_image (rm r) a) as WK.
    destruct (rd_of segs (rm r) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
  - unfold xwords_clear. rewrite XX. intros rr y j [].
Qed.
End GCH.
End DrainG4.

