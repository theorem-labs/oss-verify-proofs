(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.

(* [comment removed for export] *)
Module UnwT_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "cell"; "SLit"; "SVar"; "mkCell"; "ss_objs"; "sv"; "sv_eqb"; "dflt_writable"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "DUnknown"; "SPBranch"; "SPNot"; "mkObj"; "sprop"; "sprop_eqb"; "ss_facts"; "@Corelib.Init.Datatypes"; "andb"; "bool"; "true"; "list"; "nil"; "orb"; "app"; "cons"; "false"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "cell_eqb"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk.Chk"; "dropped"; "link_okb"; "lastobj"; "eleaf_okb"; "leaf_okb"; "up_okb"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop"; "eleaf_ok"; "leaf_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJAF TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Chk.
Variable segs : list Segment.
Variables LT EX : axst.
Variable p : positive.
Let bFR : sv := SVar p.
Let nx : positive := ss_next (ax_S LT).

Definition lastobj (L : leafA) : sobj := ltac2:(tb__ "0|1|
S29S0S5S21S22VL;A1A1A1S11S2Z0A1M0G0G0S19S1A1SeA5A3").
Definition dropped (L : leafA) : axst := ltac2:(tb__ "0|1|
S34S22VL;A1M0S28S0S5S21G0A1A1A2A2").
Definition link_okb (L : leafA) : bool := ltac2:(tb__ "0|4|
S2cVL;A1S0S15S15S15S15S15S15S1eS18S0A1M0S16Lx;S5S21S22VL;A1A1A1S17S0G0S1dLl;Ls;X18x2A1S7S9R1A1VbFR;A2A2S7SdR1A1S2N10A1M1A2A2S7ScR1A1S2Z0A1A2A2S8SbR1A1A1A2S26S1S23S4G1Z8M2S3Vnx;A1A3A1SaR1A1M3A3A2S26S1S23S4S2N8A1G2S3S30Vnx;A1A1A3A1G3A3A2To;").
Definition leaf_okb (L : leafA) : bool := ltac2:(tb__ "0|1|
S15S2bVL;A1S1aS25S2aVL;A1M0VLT;A2S25G0VEX;A2A2A2").

Definition up_okb (L : leafA) : bool := ltac2:(tb__ "0|0|
S26S12S13S10SfS31VbFR;S33S32S35S21S2aVL;A1A1S21VLT;A1A3Vp;A2A3A1A1S14S21S22VL;A1A1A1A3").
Definition eleaf_okb (L : leafA) : bool := ltac2:(tb__ "0|1|
S15S2bVL;A1S1aS15S25S2aVL;A1M0VLT;A2S2fVL;A1A2S25G0VEX;A2A2A2").

Lemma existsb_cell : ltac2:(tb__ "0|0|
S1S18S1A1S1fS16S26S1S23R2A1R1A3S17A3S27S1R3R2A3F_;Fl;Fc;").
Proof. intros c l H. apply existsb_exists in H as (d & Hd & E). apply StepA.cell_eqb_sound in E. subst. exact Hd. Qed.

Lemma link_okb_sound : ltac2:(tb__ "0|5|
S24S1fS16S2bR1A1S17A3S20S1fS18S0A1S5S21S22R2A1A1A1M0S1bS0S28S0G0A2S1cS0S2cR2A1M1S19S0A1A3A3A3S20S1fS6S9G1A1VbFR;A3S20S1fS6SdG1A1S2N10A1M2A3S20S1fS6ScG1A1S2Z0A1A3S20S1fS16S8SbG1A1A1S17A3S20S27S1S4G2Z8M3S3Vnx;A1A3SaG1A1M4A3S27S1S4S2N8A1G3S3S30Vnx;A1A1A3G4A3A2A2A2A2A2A2F_;FL;").
Proof.
  intros L H. unfold link_okb in H. repeat (apply andb_prop in H as [H ?X]).
  split; [|repeat split].
  - apply app_removelast_last. intros E. rewrite E in H. discriminate H.
  - apply sv_eqb_sound. assumption.
  - apply sv_eqb_sound. assumption.
  - apply sv_eqb_sound. assumption.
  - assumption.
  - apply existsb_cell. assumption.
  - apply existsb_cell. assumption.
Qed.

Lemma leaf_okb_sound : ltac2:(tb__ "0|0|
S24S1fS16S2eR1A1S17A3S37VLT;VEX;VbFR;R2A4F_;FL;").
Proof.
  intros L H. unfold leaf_okb in H. apply andb_prop in H as [HL HE].
  destruct (link_okb_sound L HL) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  exists (removelast (ss_objs (ax_S (la_state L)))), (lastobj L). repeat (split; [assumption|]).
  apply orb_prop in HE. exact HE.
Qed.

Lemma eleaf_okb_sound : ltac2:(tb__ "0|0|
S24S1fS16S2dR1A1S17A3S36VLT;VEX;VbFR;R2A4F_;FL;").
Proof.
  intros L H. unfold eleaf_okb in H. apply andb_prop in H as [HL HE].
  destruct (link_okb_sound L HL) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  exists (removelast (ss_objs (ax_S (la_state L)))), (lastobj L). repeat (split; [assumption|]).
  apply orb_prop in HE as [HE|HE]; [left | right; exact HE].
  apply andb_prop in HE as [HE HU]. split; [exact HE|].
  intros rhoL HF. pose proof (holds_mem _ _ _ HF HU) as HH. apply (proj1 (holds_nbgeu _ _ _)) in HH.
  unfold uval, bFR. cbn [eval rho_sub rw]. exact HH.
Qed.
End Chk.
End UnwT_chk.

(* [comment removed for export] *)
Module SegQ3D_inv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "cons"; "prod"; "length"; "nat"; "nil"; "option"; "None"; "S"; "Some"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "aa_q_global"; "aa_q_thread"; "class_state"; "aa_geom"; "mkQB"; "aa_cls"; "aa_sec"; "class_fresh"; "cs_empty"; "qb_items"; "ageom"; "qb_addr"; "sec_chunk"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "rw"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "sec_foot"; "set_q"; "push_cache"; "QRD"; "batch_mem"; "item_mem"; "qpost"; "same_but_qcs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "present"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "sub"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "CURB"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "FRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv.D"; "JRD"; "JRI"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineBatchCount"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineBatchSize"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "RMEM2"; "JRX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "qitems"; "@Stdlib.Lists.List"; "incl"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CURB (m : bview) (a n0 : Z) (ndone : nat) (its : list (Z * Z)) : Prop := ltac2:(tb__ "0|5|
S1dS32Vm;S33S35Va;Z10M0A2U8M1Vn0;A3A2S1dS1cS0Vn0;S35S37Vndone;A1M2S37S5S4S0S0A2M3Vits;A2A1A2A3S1dS36Vn0;S4aA2S1dS34Vm;S35Va;Z18A2M4S35Va;S4dA2A3S6G3S1cS8G3A1S54G3Vits;R2A3SbG3R1A2A3S1dS32Vm;S33S35G4S39Z8S35G2S37R3A1A2A2A2G1S3aScS0S0R2A3G0A2A3A2S2dVm;R2A2A2F_;Fit;Fj;A2A2A2A2").

Lemma CURB_of_batch_mem : ltac2:(tb__ "0|2|
S31SdS2cR2R1A2S36S37S5S4S0S0A2M0S18R2A1A2A1S4aA2S42R4S1aR3A1S37S5G0S18R3A1M1A2A1U0G1A5F_;F_;Fb;Fm;").
Proof.
  intros m b (H1 & H2 & H3 & H4 & H5) HL. split; [exact H2|]. split; [cbn; lia|]. split; [exact HL|]. split; [exact H4|].
  intros j it Hj. cbn [Z.of_nat]. rewrite Z.add_0_l. exact (H5 j it Hj).
Qed.
Lemma CURB_next : ltac2:(tb__ "0|1|
S31S0S0S6S4S0S0A2M0S2G0A1S42R6R5R4R3S3G0R2R1A3A5S42R7R6R5SaR4A1R2A5F_;Fits;Fit;Fnd;Fn0;Fa;Fm;").
Proof.
  intros m a n0 nd it its (H1 & H2 & H2' & H3 & H4). split; [exact H1|]. split; [cbn [length] in H2; lia|]. split; [exact H2'|]. split; [exact H3|].
  intros j it' Hj. specialize (H4 (S j) it' Hj). replace (Z.of_nat (S nd) + Z.of_nat j) with (Z.of_nat nd + Z.of_nat (S j)) by lia. exact H4.
Qed.

Section D.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Definition JRD (A : AA) (tmp rest : list qbatch) : jpredA := ltac2:(tb__ "0|0|
S23S2S3cQ40A1A1S2S3fA1S3eS1dVK;VA;R4R3R2R1A5S1dS4fS30S21S22R4A1A2S12VA;A1Vtmp;Vrest;A4S44VA0;Vrho0;R4A3A2A2Lmd;Ltr;Ltp;Lrho;").
Definition JRI (A : AA) (a n0 : Z) (ndone : nat) (its : list (Z * Z)) (tmp rest : list qbatch) : jpredA := ltac2:(tb__ "0|1|
S23S2S3cQ40A1A1S2S3fA1S3eS1dVK;VA;R4R3R2R1A5S1dS42S30S21S22R4A1A2M0Va;Vn0;Vndone;Vits;A5S1dS4fG0S12VA;A1Vtmp;Vrest;A4S44VA0;Vrho0;R4A3A2A2A2Lmd;Ltr;Ltp;Lrho;").

Lemma FRM_stable : ltac2:(tb__ "0|1|
S23S23S26S45R2R1A3S44VA0;Vrho0;R3A3M0G0F_;F_;Frho';Frho;").
Proof.
  intros rho rho' Hag ((F1 & F1') & F2 & F3 & F4).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [|rewrite Erm; auto]. split; [intros i Hi; rewrite (F1 i Hi); apply (proj1 Hag); exact Hi | intros l; rewrite (F1' l); apply (proj1 (proj2 Hag))].
Qed.
Lemma JRD_stable : ltac2:(tb__ "0|1|
SeS2SdA1M0G0S41S21S45S46R3R2R1A3A3Frest;Ftmp;FA;").
Proof.
  intros A tmp rest rho rho' tp tr md md' Hag Hme (HK & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A); eauto|]. split; [rewrite Erm; exact HR | exact (FRM_stable rho rho' Hag HF)].
Qed.
Lemma JRI_stable : ltac2:(tb__ "0|1|
SeS0S0S6S2S4S0S0A2A1S2SdA1M0G0S41S21S45S47R7R6R5R4R3R2R1A7A3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Proof.
  intros A a n0 nd its tmp rest rho rho' tp tr md md' Hag Hme (HK & HC & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros x; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A); eauto|]. split; [rewrite Erm; exact HC|]. split; [rewrite Erm; exact HR | exact (FRM_stable rho rho' Hag HF)].
Qed.
Lemma JRD_okf : ltac2:(tb__ "0|1|
S49OF_;SeS2SdA1M0G0SeS40S21R5VK;R1A1A3FA';S40S21R5S46R4R3R2A3A3F_;Frest;Ftmp;FA;Fok;").
Proof. intros ok A tmp rest HOK rho tp tr ms md msv' (HK & _). exact (HOK A rho tp tr ms md msv' HK). Qed.
Lemma JRI_okf : ltac2:(tb__ "0|1|
S49OF_;SeS0S0S6S2S4S0S0A2A1S2SdA1M0G0SeS40S21R9VK;R1A1A3FA';S40S21R9S47R8R7R6R5R4R3R2A7A3F_;Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;Fok;").
Proof. intros ok A a n0 nd its tmp rest HOK rho tp tr ms md msv' (HK & _). exact (HOK A rho tp tr ms md msv' HK). Qed.

Lemma K_FRM_absorb2 : ltac2:(tb__ "0|7|
SeS0S27R2R1A2S27VA0;R2A2F_;Fz;S23S23S2S3cQ40M0A1M1A1S2S3fA1S3eS0OF_;S0S1fR2R1A1M2S1eG2A1A2Fz;S1S1cG1S25R7R1A2S25R8R1A2A3Fi;S1S1cS2S3cQ8A1M3A1S24R8R1A2S24R9R1A2A3Fl;S0R5R1A1S1dS1eS1dS36S4cR2A2S38R2S4bA2A2A1S1fS27RdR2A2S1dS2bVA0;R2A2S1cS8G3A1M4S30S21S22RaA1R2A3S30S21S22RbA1R2A3M5A3A2A2A2F_;Fz;S0S1eR6R1A1A1S1cG4G5S30S21S22RcA1R2A3A3F_;Fz;G1S1eR7S3dG0R1A2A1A1S1cG4S22RcR2A2S22RdR2A2A3F_;Fa;S0R8R1A1S1eS1cG4S30S21S22RdA1R2A3S9G3A1A3A1F_;Fz;VK;RfRdRbRaR9A5S44VA0;Vrho0;ReA3M6S1dVK;R11ReRdRcRbA5G6A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FP;Fmd;Ftr;Ftp;Frho3;Frho;F_;FA1;").
Proof.
  intros A1 HQW rho rho3 tp tr md P PD Hrw Hrl HP FR FRrm PPR HK ((F1 & F1') & F2 & F3 & F4). split.
  - apply (kq_view segsA K HL A1 rho rho3 tp tr md Hrw Hrl); [| | exact HK].
    + intros z NQ. destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [_ [HQ|[_ HE]]]; [exfalso; exact (NQ HQ) | exact HE].
    + intros z _ Hd. destruct (PD z) as [Hp|Np]; [exact (PPR z Hp) | rewrite (FR z Np); exact Hd].
  - split; [split; [intros i Hi; rewrite Hrw; exact (F1 i Hi) | intros l; rewrite Hrl; exact (F1' l)]|]. split; [|split].
    + intros a NQ. rewrite FRrm; [exact (F2 a NQ)|]. intros Hp. apply NQ. destruct (HP _ Hp) as [_ [HQ|[HQ _]]]; [left; left; exact (HQW _ HQ) | exact HQ].
    + intros z NQ. rewrite <- (F3 z NQ). destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [_ [HQ|[_ HE]]]; [exfalso; apply NQ; left; exact (HQW _ HQ) | exact HE].
    + intros a HB Hdef. pose proof (F4 a HB Hdef) as X. destruct (PD (bv_unsigned a)) as [Hp|Np]; [|rewrite (FRrm a Np); exact X].
      exfalso. exact (proj1 (HP _ Hp) HB).
Qed.
Lemma JRX_JRD : ltac2:(tb__ "0|1|
SeS2SdA1M0G0S23S2S3cQ40A1A1S2S3fA1S3eS20S50VK;VA0;Vrho0;R7R6R5R4R3R2R1AaS46R7R6R5R4R3R2R1A7A2Fmd;Ftr;Ftp;Frho;Frest;Ftmp;FA1;").
Proof. intros. unfold JRX, JRD. tauto. Qed.
End D.

Definition QP (A0 A : AA) : Prop := ltac2:(tb__ "0|3|
S1dS2fVA0;VA;A2S1dS1cS6S5S11S14VA;A1M0A2S5S11S14VA0;A1M1A2A3S0S16VA0;R1A2S1cS11S48S11S3bR2A1M2G0S17A4S48S11G2G1S17A4A3F_;Fc;A2A2").
Lemma QP_refl_q : ltac2:(tb__ "0|1|
SeS2SdA1M0G0S43R3S29R3R2R1A3A2Fg;Ft;FA;").
Proof. intros A t g. split; [destruct A; reflexivity|]. split; [reflexivity | intros c _; reflexivity]. Qed.
Lemma QP_push : ltac2:(tb__ "0|1|
SeSeS2SdA1M0G0S0S0S43R6R5A2S36Z0R3A2S1eS16R8R4A2A1S43R9S2aS29R8R7R6A3R5R4A3A2F_;F_;F_;Fx;Fc;Fg;Ft;FA;FA0;").
Proof.
  intros A0 A t g c x (E & EL & EF) Hc NF. split; [|split].
  - unfold same_but_qcs in *. rewrite E. reflexivity.
  - unfold push_cache, set_cls. cbn [aa_cls set_q]. rewrite length_list_upd. exact EL.
  - intros c' Hf. unfold push_cache, set_cls. cbn [aa_cls set_q]. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [En|Nn].
    + exfalso. apply NF. unfold class_fresh in *. rewrite En. exact Hf.
    + rewrite nth_list_upd_other by exact Nn. exact (EF c' Hf).
Qed.
Lemma QP_qpost : ltac2:(tb__ "0|0|
SeSeS43R2R1A2S1cS2SdA1S10R2A1S7SdA1A3S36S55SfR3A1A1S4eA2S2eR5R4A2F_;F_;F_;FA;FA0;").
Proof.
  intros A0 A (E & EL & EF) HT HS. split; [exact E|]. split; [exact HT|]. split; [exact EL|]. split; [|exact HS].
  intros c Hf. unfold class_fresh in *. rewrite (EF c Hf). exact Hf.
Qed.

Lemma QW_push_item : ltac2:(tb__ "0|3|
SeS0S4S0S0A2M0S2G0A1S0S0S2SdA1M1S0S0S0S1cG1S10RaA1S7SdA1M2A3S1cG1SfRbA1S3SdS13RaS3G0R9R8A3R7A3R5A3A3S27S2aS29RcG2S3SdS13RbR9R7A3R6A3A3R5R4A3R3A2S27RdR4A2F_;F_;F_;Fz;Fx;Fc;Fg2;Fs';Fs;Fi2;Fit;Fa;FA;").
Proof.
  intros A a it i2 s s' g2 c x z HT HG [H|H]; [left | right; exact H].
  unfold qzone, qall in *. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app] in H. rewrite HT, HG. cbn [app].
  apply Exists_cons in H as [H|H]; [apply Exists_cons_hd | apply Exists_cons_tl; exact H].
  cbn [qb_addr qb_items] in *. destruct H as [H|H]; [left; exact H | right]. apply Exists_cons_tl. exact H.
Qed.
Lemma QW_push_batch : ltac2:(tb__ "0|2|
SeSdS2SdA1M0S0S0S1cG0S10R5A1S7SdA1M1A3S1cG0SfR6A1S3SdR5R4A3A3S27S2aS29R7G1R5A3Z18R4A3R3A2S27R8R4A2F_;F_;F_;Fz;Fx;Fg2;Fb;FA;").
Proof.
  intros A b g2 x z HT HG [H|H]; [left | right; exact H].
  unfold qzone, qall in *. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app] in H. rewrite HT, HG. cbn [app]. apply Exists_cons_tl. exact H.
Qed.

Lemma sec_foot_mono : ltac2:(tb__ "0|0|
SeSeS0S1cS19S12R2A1S12R3A1A3S53S1bS15R3A1S15R4A1A3S53S4S0S0A2S52S51R4A1A1S52S51R5A1A1A3S28R5R4A2S28R7R5A2F_;F_;F_;F_;Fz;FA';FA;").
Proof.
  intros A A' z EG IS IQ [H|[H|[H|H]]].
  - left. exact H.
  - right; left. rewrite <- EG. exact H.
  - right; right; left. apply Exists_exists in H as (ch & Hch & Hz). apply Exists_exists. exists ch. split; [exact (IS _ Hch) | exact Hz].
  - right; right; right. apply Exists_exists in H as (ch & Hch & (it & Hit & HP & Eit) & Hz). apply Exists_exists. exists ch. split; [exact (IS _ Hch)|].
    split; [exists it; split; [exact (IQ _ Hit) | split; assumption] | exact Hz].
Qed.
Lemma SF_push_item : ltac2:(tb__ "0|3|
SeS0S4S0S0A2M0S2G0A1S0S0S2SdA1M1S0S0S0S1cG1S10RaA1S7SdA1M2A3S1cG1SfRbA1S3SdS13RaS3G0R9R8A3R7A3R5A3A3S28S2aS29RcG2S3SdS13RbR9R7A3R6A3A3R5R4A3R3A2S28RdR4A2F_;F_;F_;Fz;Fx;Fc;Fg2;Fs';Fs;Fi2;Fit;Fa;FA;").
Proof.
  intros A a it i2 s s' g2 c x z HT HG. apply sec_foot_mono; [reflexivity | intros y Hy; exact Hy |].
  unfold qall. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app]. rewrite HT, HG. cbn [app]. unfold qitems. cbn [flat_map qb_items].
  intros y Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app; [left; right; exact Hy | right; exact Hy].
Qed.
Lemma SF_push_batch : ltac2:(tb__ "0|2|
SeSdS2SdA1M0S0S0S1cG0S10R5A1S7SdA1M1A3S1cG0SfR6A1S3SdR5R4A3A3S28S2aS29R7G1R5A3Z18R4A3R3A2S28R8R4A2F_;F_;F_;Fz;Fx;Fg2;Fb;FA;").
Proof.
  intros A b g2 x z HT HG. apply sec_foot_mono; [reflexivity | intros y Hy; exact Hy |].
  unfold qall. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app]. rewrite HT, HG. cbn [app]. unfold qitems. cbn [flat_map].
  intros y Hy. apply in_or_app. right. exact Hy.
Qed.
End SegQ3D_inv.

(* [comment removed for export] *)
Module CertCallocSU.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SVar"; "SLit"; "sprop"; "SPBranch"; "SPNot"; "sv"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "nat"; "prod"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "rstS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section NX.
Variable nx : positive.

Definition F_g4 : list sprop := ltac2:(tb__ "0|1|
SaS5S7S6S1S2S0S3S10A1S2S0S3Vnx;A1M0S4Z1000A1A3A3S2S0S2S0G0S4Z1800A1A3S3PcA1A3A3A1S9S5A1A3").
End NX.

Definition DPENT : Z := 0x7e9e4.
Definition DPRET : Z := 0x3c720.
Definition U4p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S11VE;S9ScSbS8A2A1S13Vnx;A1A3").
Definition runT5 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
SfS14Ufa0SaSeS12S9SeA1A3VT;SdA5").
End CertCallocSU.

(* [comment removed for export] *)
Module CertCallocSN.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "list"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sobj"; "ss_objs"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "ERRNO_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN.W"; "NOBJ"; "stKn"; "stRn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ESn"; "V_NCH"; "V_NRES"; "V_PAB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "kPtrArrayReserve"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_null"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN"; "C_seci"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "stack_win"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymCall SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N_secn : list carve_spec := ltac2:(tb__ "0|11|
S1S3S3S3S9S8A2M0S8A2M1S5S3S3S8S2A2M2S9A2M3A1M4A2M5S0G1G4S0G0S8S0S9S8SaZ0A1M6S17A4S18S17Z40A2M7A4S1G3S0G2S9S0S8S2S17U8M8A4SaS24A1A4S1G3S0G2S9S0S8S2S18S17Z8A2G8A4SbS23A1M9A4S1G3S0G2S9S0S8S2S18S17Z10A2G8A4G9A4S1G3S0G2S9S0S8S2S18S17Z18A2G8A4SaS25A1A4S1G3S0G2S9S0S8S2S18S17Z30A2G8A4SbS22A1A4S1G3S0G2S9S0S8S2S18S17Z38A2G8A4SbS21A1A4S4G3A1MaA3A3A3A3A3A3A4S1G5S0G1G4S0G0S8S0S9S8G6G7A4Zead00MbA4GaA4S1G5S0G1G4S0G0S8S0S9S8G6GbA4Zead04A4S1G3S0G2S9S0S8S2GbU4McA4G6A4GaA3A4S1G5S0G1G4S0G0S8S0S9S8G6Zead08A4Zead30A4GaA4S1G5S0G1G4S0G0S8S0S9S8G6Ze67b8MdA4Ze67c0A4S1G3S0G2S9S0S8S2GdG8A4SaZ1a309A1A4GaA3A4S1G5S0G1G4S0G0S8S0S9S8G6Z170320MeA4Z170322A4S1G3S0G2S9S0S8S2GeU1MfA4SaZ1A1M10A4S1G3S0G2S9S0S8S2Z170321GfA4G10A4GaA3A3A4S1G5S0G1G4S0G0S8S0S9S8G6S1cA4S18S1cZ4A2A4S1G3S0G2S9S0S8S2S1cGcA4SaZcA1A4GaA3A4S1G5S0G1G4S0G0S8S0S9S8S2eZad0A4Zc60A4GaA4S4G5A1A3A3A3A3A3A3A3A3").

Definition N_secc : list carve_spec := ltac2:(tb__ "0|a|
S1S3S3S3S9S8A2M0S8A2M1S5S3S3S8S2A2M2S9A2M3A1M4A2M5S0G1G4S0G0S8S0S9S8SaZ0A1M6Zead00M7A4Zead04A4S1G3S0G2S9S0S8S2G7U4A4G6A4S4G3A1M8A3A4S1G5S0G1G4S0G0S8S0S9S8G6Ze67b8M9A4Ze67c0A4S1G3S0G2S9S0S8S2G9U8A4SaZ1a309A1A4G8A3A4S4G5A1A3A3").
Definition C_seci : list (Z * nat * sv) := ltac2:(tb__ "0|4|
S1S3S3S8S2A2M0S9A2M1S0G0S9S0S8S2S17U8M2A4SaS24A1A4S1G1S0G0S9S0S8S2S18S17Z8A2G2A4SbS23A1M3A4S1G1S0G0S9S0S8S2S18S17Z10A2G2A4G3A4S1G1S0G0S9S0S8S2S18S17Z18A2G2A4SaS25A1A4S1G1S0G0S9S0S8S2S18S17Z30A2G2A4SbS22A1A4S1G1S0G0S9S0S8S2S18S17Z38A2G2A4SbS21A1A4S4G1A1A3A3A3A3A3A3").
Definition K_seci : carve_spec := ltac2:(tb__ "0|1|
S0S3S3S9S8A2M0S8A2S5S3S3S8S2A2S9A2A1S0G0S8S0S9S8SaZ0A1S17A4S18S17Z40A2A4S2dA4").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.

Definition NOBJ : nat := ltac2:(tb__ "0|0|
S7ScS1ScS30S6ScS31VW;A1S2fA3A3A2").

Definition stKn : axst := ltac2:(tb__ "0|1|
S20VW;Vst;Vtmax;A3S1bS1aR1S2bS19R1A1M0S26ScS1dSdG0A1A3A2A2TE;").

Definition stRn_S : sstate := ltac2:(tb__ "0|2|
SeS14S19S1eA1M0A1S29S15G0A1S1S3S2S9A2M1S0S2S9U4SbP18A1A4S4G1A1A3A2S11G0A1S10G0A1S16G0A1SdG0A1SfG0A1S13G0A1S12G0A1A9").
Definition stRn : axst := ax_setS stKn stRn_S.

Definition s_n : wsub := ltac2:(tb__ "0|0|
S2aS28S19S1fA1S19S2cVW;Vst;A2A1A3").

Definition R_n : list sobj := ltac2:(tb__ "0|0|
S27ScS1dSdS19S20VW;Vst;Vtmax;A3A1A1A3").
End W.
End CertCallocSN.

(* [comment removed for export] *)
Module SpineCallocS1i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_callocI"; "@Corelib.Init.Datatypes"; "bool"; "true"; "prod"; "list"; "option"; "app"; "nil"; "pair"; "Some"; "cons"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sprop_below"; "ss_next"; "SLit"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "P0c"; "E_s1"; "F_hi_p"; "F_lo_p"; "E_pre"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "FACTSe"; "F_hi_e"; "F_lo_e"; "P0e"; "sa_c"; "sb_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2"; "s_sw"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1"; "dp_okb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wa_c : ltac2:(tb__ "0|0|
SfS4S13S28S1U0A1S0A2A1S5A3"). Proof. MemoFast.vmc. Qed.
Lemma Da_c : ltac2:(tb__ "0|5|
SfS8S6S7S6S12S12A2M0A1M1S7S11A1M2A2M3A1S21S18S3S2S1U0A1M4S0A3A1S28G4S0A2A2ScG3SbG1G2SdG0SbS12S12S17P18A1S16S2dA1A4SaG0A1A3SaS11A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma Wb_c : ltac2:(tb__ "0|0|
SfS4S13S29S1U0A1S0A2A1S5A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbh_c : ltac2:(tb__ "0|0|
SfS4S2bS11S14S22A1S9S11S24S1U0A1S0A2S25A3A3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbl_c : ltac2:(tb__ "0|0|
SfS4S2bS11S14S22A1S9S11S24S1U0A1S0A2S26A3A3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTh_c : ltac2:(tb__ "0|1|
SfS4S19S27S1U0A1M0S0S25A3S1aG0S0S1cA3S2aA3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTl_c : ltac2:(tb__ "0|1|
SfS4S19S27S1U0A1M0S0S26A3S1aG0S0S1dA3S2aA3S5A3"). Proof. MemoFast.vmc. Qed.
Lemma WE1_c : ltac2:(tb__ "0|0|
S20S10S1fZ0R1A2S1fR1Z8A2A2SfS4S13S18S1bS1U0A1S0Z2R2A4A1A1S5A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DE1_c : ltac2:(tb__ "0|5|
S20S10S1fZ0R1A2S1fR1Z8A2A2SfS4S8S6S7S6S12S12A2A1M0S7S11A1M1A2M2A1S4Lx;S21S18S1eS1U0A1M3S0Z2M4R2A4A1S18S1bG3S0G4R2A4A1A2G2G2S4Lp;R1G0G1S2eR5R2A2Ll;Ld;X6x1Lp;SeX8x2S5A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HSW_c : stopJ_sw (Wcan 0) UStopLe. Proof. apply stopJ_sw_le. Qed.
Lemma HUS_c : stopJ_stable (Wcan 0) UStopLe. Proof. apply stopJ_stable_le. Qed.
Lemma NXhi_c : ltac2:(tb__ "0|0|
S2cS23S15S18S1aS1U0A1S0S1cA3A1A1A2"). Proof. apply Pos.leb_le. MemoFast.vmc. Qed.
Lemma NXlo_c : ltac2:(tb__ "0|0|
S2cS23S15S18S1aS1U0A1S0S1dA3A1A1A2"). Proof. apply Pos.leb_le. MemoFast.vmc. Qed.
End SpineCallocS1i.

(* [comment removed for export] *)
Module SpineCallocS1iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "Wcan"; "AE_A"; "Pre_callocI"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "prod"; "nil"; "app"; "option"; "pair"; "Some"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sprop_below"; "SLit"; "SVar"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "P0c"; "F_hi_p"; "F_lo_p"; "E_s1"; "stop_le"; "stop_pc"; "E_pre"; "s1_cuts_pcs"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "FACTSe"; "F_hi_e"; "F_lo_e"; "P0e"; "sa_c"; "sb_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2"; "s_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1"; "dp_okb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wa_c : ltac2:(tb__ "0|0|
SfS4S13S2dS1U1A1S0A2A1S6A3"). Proof. MemoFast.vmc. Qed.
Lemma Da_c : ltac2:(tb__ "0|5|
SfSbS8S7S8S12S12A2M0A1M1S7S11A1M2A2M3A1S26S18S3S2S1U1A1M4S0A3A1S2dG4S0A2A2SdG3ScG1G2S5G0ScS12S12S16P18A1S15S31A1A4S9G0A1A3S9S11A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma Wb_c : ltac2:(tb__ "0|0|
SfS4S13S2eS1U1A1S0A2A1S6A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbh_c : ltac2:(tb__ "0|0|
SfS4S24S11S14S28A1SaS11S29S1U1A1S0A2S2aA3A3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma Fbl_c : ltac2:(tb__ "0|0|
SfS4S24S11S14S28A1SaS11S29S1U1A1S0A2S2bA3A3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTh_c : ltac2:(tb__ "0|1|
SfS4S1aS2cS1U1A1M0S0S2aA3S1bG0S0S1cA3S2fA3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTl_c : ltac2:(tb__ "0|1|
SfS4S1aS2cS1U1A1M0S0S2bA3S1bG0S0S1dA3S2fA3S6A3"). Proof. MemoFast.vmc. Qed.
Lemma WE1_c : ltac2:(tb__ "0|0|
S27S10S25Z0R1A2S25R1Z8A2A2SfS4S13S18S1eS1U1A1S0Z3R2A4A1A1S6A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DE1_c : ltac2:(tb__ "0|5|
S27S10S25Z0R1A2S25R1Z8A2A2SfS4SbS8S7S8S12S12A2A1M0S7S11A1M1A2M2A1S4Lx;S26S18S21S1U1A1M3S0Z3M4R2A4A1S18S1eG3S0G4R2A4A1A2G2G2S4Lp;R1G0G1S32R5R2A2Ll;Ld;X8x1Lp;SeXbx2S6A3F_;Fk;").
Proof. intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia. destruct C as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HSW_c : stopJ_sw (Wcan 1) UStopLeOrPc. Proof. exact stopJ_sw_1pc. Qed.
Lemma HUS_c : stopJ_stable (Wcan 1) UStopLeOrPc. Proof. exact stopJ_stable_1pc. Qed.
Lemma Est_c : UStopLeOrPc = UStopLeOrPc. Proof. reflexivity. Qed.
Lemma HWne_c : Wcan 1 <> []. Proof. discriminate. Qed.
Lemma WPC_c : ltac2:(tb__ "0|3|
S7S11A1M0G0S23G0R2S5G0S1cS5G0S1dS9G0A1M1A3A3A3S23G0R2S5G0S20S1U1A1M2A1S5G0S1fG2A1G1A3A3A3SfS4S13S18S1bG2S0SaS11R4R3A3A3A1A1S6A3F_;F_;Fsx;Ffx;").
Proof. intros fx sx Hf Hs. destruct Hf as [<-|[<-|[]]]; destruct Hs as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DPC_c : ltac2:(tb__ "0|6|
S7S11A1M0G0S23G0R2S5G0S1cS5G0S1dS9G0A1M1A3A3A3S23G0R2S5G0S20S1U1A1M2A1S5G0S1fG2A1G1A3A3A3SfSbS8S7S8S12S12A2M3A1M4G0A2M5A1S26S18S1bG2S0R4A3A1S18S1bG2S0SaS11R4R3A3A3A1A2SdG5ScG4G0S9G3A1R3A4A2A3F_;F_;Fsx;Ffx;").
Proof. intros fx sx Hf Hs. destruct Hf as [<-|[<-|[]]]; destruct Hs as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXpc_c : ltac2:(tb__ "0|0|
S19S23S19R1S22U1S0A2A3S33S30S17S18R2A1A1A2F_;Fc;").
Proof. intros c Hc. apply Pos.leb_le. unfold s1_cuts_pcs in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End SpineCallocS1iW1.

