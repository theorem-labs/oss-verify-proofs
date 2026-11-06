(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.

(* [comment removed for export] *)
Module F0A_pins.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "iff"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "true"; "list"; "andb"; "nat"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_pins"; "spec_on"; "sv_on"; "sprop_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "holds"; "obj_range"; "sobj"; "eval"; "pairwise_disjoint"; "rl"; "rm"; "rw"; "ob_base"; "ob_hi"; "ob_lo"; "@Stdlib.Lists.List"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "carve_ok"; "spec_zone"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint sv_on (P : positive -> bool) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar i => P i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_on P a && sv_on P b
  | SExt _ _ a => sv_on P a
  | SLBytes _ i _ => sv_on P i
  end.
Fixpoint sprop_on (P : positive -> bool) (f : sprop) : bool :=
  match f with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_on P a && sv_on P b
  | SPNot g => sprop_on P g
  | SPTrue => true
  | SPAlign i _ => P i
  end.
Definition spec_on (P : positive -> bool) (k : carve_spec) : bool := ltac2:(tb__ "0|5|
S3S3S3S13S9A2M0S9A2M1S5S3S3S9S7A2M2S13A2M3A1M4A2S2Lk;Vk;G1G4G1S2Lp;R2G0S9G0S2Lp0;R2S13S9S6S10VP;R2A2S1fG3G3G3S2Lc;R1G2S13G2S2Lp;R2S9S7S10VP;R3A2Ln;Lz;X3x1Le;Lp;X3x1Lc;R5A3A2Lz0;Lb;X3x1Lz;Lp0;X3x1Lcs;Lp;X3x1").

Section Agree.
Variable P : positive -> bool.
Variables r1 r2 : valuation.
Hypothesis HW : ltac2:(tb__ "0|0|
SaS0S2VP;R1A1S4A3S0S20Q40A1S1bVr2;R2A2S1bVr1;R2A2A3F_;Fi;").
Hypothesis HL : ltac2:(tb__ "0|0|
SaS0S5S20Q8A1A1S19Vr2;R1A2S19Vr1;R1A2A3Fl;").
Hypothesis HM : ltac2:(tb__ "0|0|
S0S20Q40A1S8S20Q8A1A1F_;S1aVr2;A1S1aVr1;A1A3").

Lemma eval_on : ltac2:(tb__ "0|0|
S13S0S2S10VP;R1A2S4A3S0S20Q40A1S17Vr2;R2A2S17Vr1;R2A2A3F_;Fe;").
Proof.
  induction e; cbn; intros Hb; try (apply andb_prop in Hb as [Hb1 Hb2]); try rewrite (IHe1 Hb1); try rewrite (IHe2 Hb2); try reflexivity.
  - apply HW. exact Hb.
  - rewrite (IHe Hb). reflexivity.
  - rewrite HL, (IHe Hb). reflexivity.
Qed.
Lemma holds_on : ltac2:(tb__ "0|0|
S12S0S2S11VP;R1A2S4A3S1S14Vr1;R2A2S14Vr2;R2A2A2F_;Ff;").
Proof.
  induction f as [c a b|g IH|a b|a b|a b| |i a]; cbn; intros Hb; try (apply andb_prop in Hb as [Hb1 Hb2]); rewrite ?(eval_on _ Hb1), ?(eval_on _ Hb2); try tauto.
  rewrite (HW _ Hb). tauto.
Qed.
Lemma Forall_holds_on : ltac2:(tb__ "0|0|
S5S12A1S0S2S1fS12S11VP;A1R1A3S4A3SdS12S14Vr1;A1R2A3SdS12S14Vr2;A1R3A3F_;F_;Fl;").
Proof.
  intros l Hb H. apply Forall_forall. intros f Hf. apply (proj1 (holds_on f (proj1 (forallb_forall _ _) Hb f Hf))). exact (proj1 (Forall_forall _ _) H f Hf).
Qed.
Lemma carve_ok_on : ltac2:(tb__ "0|0|
SbS0S2SfVP;R1A2S4A3S21Vr1;R2A2S21Vr2;R3A2F_;F_;Fk;").
Proof.
  intros [[[base lo] hi] cs] Hb. unfold spec_on in Hb. apply andb_prop in Hb as [Hb Hc]. unfold carve_ok. cbn zeta.
  rewrite (eval_on base Hb), HM. intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 _))))))).
  unfold cells_in_view in *. apply Forall_forall. intros [[off k] v] Hin. pose proof (proj1 (Forall_forall _ _) C8 _ Hin) as C. cbn beta iota in C |- *.
  pose proof (proj1 (forallb_forall _ _) Hc _ Hin) as Hv. cbn beta iota in Hv. rewrite (eval_on v Hv). exact C.
Qed.
Lemma Forall_carve_ok_on : ltac2:(tb__ "0|0|
S5SbA1S0S2S1fSbSfVP;A1R1A3S4A3SdSbS21Vr1;A1R2A3SdSbS21Vr2;A1R3A3F_;F_;FN;").
Proof.
  intros N Hb H. apply Forall_forall. intros k Hk. apply (carve_ok_on k (proj1 (forallb_forall _ _) Hb k Hk)). exact (proj1 (Forall_forall _ _) H k Hk).
Qed.
Lemma carve_range_on : ltac2:(tb__ "0|1|
SbS0S2SfVP;R1A2S4A3S0S3S9S9A2S15Vr2;ScR2A1M0A2S15Vr1;G0A2A3F_;Fk;").
Proof.
  intros [[[base lo] hi] cs] Hb. unfold spec_on in Hb. apply andb_prop in Hb as [Hb _]. cbn [carve_obj]. unfold carved, obj_range, obj_lo_of, obj_hi_of, soff. cbn [ob_base ob_lo ob_hi eval].
  rewrite (eval_on base Hb). reflexivity.
Qed.
Lemma spec_zone_on : ltac2:(tb__ "0|0|
S9S9S9SbS0S2SfVP;R1A2S4A3S22Vr1;R5R4R3R2A5S22Vr2;R6R5R4R3A5F_;F_;Fk;Fn8;Fp;Ftop;").
Proof.
  intros top p n8 [[[base lo] hi] cs] Hb. unfold spec_on in Hb. apply andb_prop in Hb as [Hb _]. unfold spec_zone. rewrite (eval_on base Hb). exact (fun H => H).
Qed.
Lemma Forall_spec_zone_on : ltac2:(tb__ "0|0|
S9S9S9S5SbA1S0S2S1fSbSfVP;A1R1A3S4A3SdSbS22Vr1;R5R4R3A4R2A3SdSbS22Vr2;R6R5R4A4R3A3F_;F_;FN;Fn8;Fp;Ftop;").
Proof.
  intros top p n8 N Hb H. apply Forall_forall. intros k Hk. apply (spec_zone_on top p n8 k (proj1 (forallb_forall _ _) Hb k Hk)). exact (proj1 (Forall_forall _ _) H k Hk).
Qed.
Lemma pd_on : ltac2:(tb__ "0|0|
S5SbA1S0S2S1fSbSfVP;A1R1A3S4A3S18Vr1;SeSbS16ScR2A4A2S18Vr2;SeSbS16ScR3A4A2F_;F_;FN;").
Proof.
  induction N as [|k N IH]; intros Hb Hpd; [exact I|]. cbn [forallb] in Hb. apply andb_prop in Hb as [Hk Hb]. cbn [map pairwise_disjoint] in Hpd |- *.
  destruct Hpd as [Hd Hpd]. split; [|exact (IH Hb Hpd)].
  apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k' & <- & Hk').
  rewrite (carve_range_on k Hk), (carve_range_on k' (proj1 (forallb_forall _ _) Hb k' Hk')).
  exact (proj1 (Forall_forall _ _) Hd (carve_obj k') (in_map _ _ _ Hk')).
Qed.
Lemma obj_range_on : ltac2:(tb__ "0|0|
S16S0S2S6S6S10VP;S1cR1A1A2S10VP;S1eR1A1A2A2S10VP;S1dR1A1A2A2S4A3S0S3S9S9A2S15Vr2;R2A2S15Vr1;R2A2A3F_;Fo;").
Proof.
  intros o Hb. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite (eval_on _ H1), (eval_on _ H2), (eval_on _ H3). reflexivity.
Qed.
End Agree.
End F0A_pins.

(* [comment removed for export] *)
Module SpineMallocS8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "pair"; "Some"; "option"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sobj"; "sstate"; "swf"; "SPNot"; "rw"; "sprop_below"; "SAlu"; "eval"; "SPUle"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_CLS"; "E7c1"; "E7c2"; "F_gen"; "C7p"; "E7q1"; "E7q2"; "E7p"; "V_ND"; "n8e"; "upd"; "C8"; "C8p"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "BP"; "C7"; "LPe"; "ube"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "JGb"; "@Stdlib.Lists.List"; "In"; "incl"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "add"; "mul"; "le"; "lt"; "of_nat"; "sub"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "ALU_ADD"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8.S8.B11S"; "E7c1'"; "E7c2'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8.S8.B12S"; "E7q1'"; "E7q2'"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "needed8"; "cnt_of"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8"; "a0e7"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4"; "pvals_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition a0e7 : sv := ltac2:(tb__ "0|0|
S22S5bS22S5cS22S5bS40S35A3S1aZ3A1A3S28A3").

Section PSVals7.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S7eVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S4cS4cVSB;S4dVc;S52Z2Z20A2A2A2S4dZ10Vx;A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_a0e7 : ltac2:(tb__ "0|0|
S0S53Q40A1S23Vrho;S7cA2S23Vrho;S3dA2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ub rho _ _ _ _ _ _ PV) as EUB. cbn zeta in EUB. fold ab in EUB.
  pose proof (pv_bp rho _ _ _ _ _ _ PV) as EBP. cbn zeta in EBP. fold ab in EBP.
  apply bv_eq. rewrite EBP. unfold a0e7, shb. cbn [eval]. fold ube. fold n8e.
  assert (EN8 : bv_unsigned (eval rho n8e) = n - n mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). apply land_M48. lia. }
  rewrite add_val, srl_val, add_val, EUB, EN8, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (B1 : 17594333495296 <= ab + rzv /\ ab + rzv + n <= 140737479966720) by (unfold ab; lia).
  rewrite (Z.mod_small (ab + rzv + _)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small rho _ _ _ _ _ _ PV (ab + rzv + (n - n mod 8)) ltac:(lia)) as (_ & E & _). rewrite E.
  unfold Sh. pose proof (Z.div_mod rzv 16 ltac:(lia)). pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)).
  replace (ab + rzv + (n - n mod 8)) with (ab + rzv + (n / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma pv_lp1 : ltac2:(tb__ "0|0|
S2S0S25S4bVn;Z8A2Z0A3A1S0S25S54Q40S23Vrho;S3fA2A2Z1A3F_;").
Proof. intros Hn. rewrite (pv_lp rho _ _ _ _ _ _ PV). destruct (Z.eq_dec (n mod 8) 0); [contradiction | reflexivity]. Qed.
End PSVals7.

Section S8.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S62VAInv;VW;Vst;VA;VKc;S17PcA1A6").

Lemma class_restate_gen : ltac2:(tb__ "0|7|
S4S1dS15S25S12S63S60S19SdS53Q40M0A1A1S47S19S0S9S65P9dM1R9A2SaA3S0S9S66G1RaS64R9R8A5SaA3S0S9S1eRcA1SaA3S0S11SeSdSeS15S15A2M2A1M3SdS14A1M4A2M5A1S49S3ReA1RdA2S10G5SfG3G4ScG2SfS15S15RcS17S2cA1A4SbG2A1A3SbS14A1A4A2A3S0S26S18ReA1S18S3RfA1A1A3S71S54G0S20R9PcA2A2A1S25S1S1S4eReR1A2S4fR1S4cReS4dZ8M6S50RdA1A2A2A2A2S0S25S4bS51R1ReA2G6A2Z0A3A2Tnd;S29Vsegs;S42VW;Vst;RcRbRaA5R11R7R9R8A6S29Vsegs;S42VW;Vst;RdRcRbA5S6R12R11A2R8RaR9A6F_;F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fcnt;Flo;Fcreg;FES;FE;").
Proof.
  intros E ES creg lo cnt A Kc rho tp w rhoE OV TAB WS DS NX [Hr Hm] Hw.
  destruct w as [tr [ms md]]. pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _).
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  eapply SPA_restate; [exact WS | exact DS | exact NX | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_CLS. cbn [eval]. rewrite E158.
  exact (tab_ok_sound 157 _ ClassID lo cnt rhoE _ TAB OV E157 Hr Hm).
Qed.

Lemma needed_range : ltac2:(tb__ "0|6|
S63S60S19S19SdS53Q40M0A1A1S47S4S9S29Vsegs;S42VW;Vst;R8R7R6A5R2R5R4R3A6S44S14S2fS16S3R3A1A1A3S43S14S9S14Lb;R3S1bS59S1aZ200A1S17S34A1A3M1S1fG1A1X9x2S16S3R4A1A1A3S71S54G0S20R9PcA2A2A1S25S9OLb;R5S1S1S4eZ208M2R1A2S4fR1S4cG2S4dZ8M3S50S6bS6cS55S56S57S55S58A1A1A1A1A1A1A1A2A2A2A2S0S25S4bS51R1G2A2G3A2Z0M4A3A2S1S1S4eZ18M5R1A2S4fR1S4cG5S4dG3S50U3eA1A2A2A2A2S0S25S4bS51R1G5A2G3A2G4A3A2X9x2Tnd;F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *. cbn zeta.
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia. change (2 ^ 3) with 8 in G3.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F1.
  destruct b; cbn [holds eval] in F1; unfold V_ND in F1; rewrite E157 in F1; rewrite bt_ltu_lit in F1 by lia.
  - apply Z.ltb_lt in F1. split; [cbn; lia|]. replace (needed8 nv - 520) with (needed8 nv + (- 65) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
  - assert (needed8 nv <= 512) by (destruct (Z.ltb_spec 512 (needed8 nv)); [exfalso; apply F1; reflexivity | lia]).
    split; [cbn; lia|]. replace (needed8 nv - 24) with (needed8 nv + (- 3) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.

Section B11S.
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S9S6dS6fUfa0ScS25Z3c8bcScS25Z3ca04SbS25A1A3A3S27ScS4S3eVW;Vst;Vtmax;A3SbS4A1M0A3ScS4S2dVW;Vst;Vtmax;A3ScS4S2eVW;Vst;Vtmax;A3ScS4S33VW;Vst;Vtmax;A3G0A3A3A3A6SaA3").
Definition E7c1' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S2dVW;Vst;Vtmax;A3Z3ca04ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Definition E7c2' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S2eVW;Vst;Vtmax;A3Z3ca04ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Hypothesis OV7a : ltac2:(tb__ "0|0|
S0S9S65P9dS39VW;Vst;Vtmax;A3A2SaA3").
Hypothesis OV7b : ltac2:(tb__ "0|0|
S0S9S65P9dS3aVW;Vst;Vtmax;A3A2SaA3").
Hypothesis TAB7a : ltac2:(tb__ "0|0|
S0S9S66P9dS39VW;Vst;Vtmax;A3S64Z208S6bS6cS55S56S57S55S58A1A1A1A1A1A1A5SaA3").
Hypothesis TAB7b : ltac2:(tb__ "0|0|
S0S9S66P9dS3aVW;Vst;Vtmax;A3S64Z18U3eA5SaA3").
Hypothesis W7a : ltac2:(tb__ "0|0|
S0S9S1eS3S67A1A1SaA3").
Hypothesis W7b : ltac2:(tb__ "0|0|
S0S9S1eS3S68A1A1SaA3").
Hypothesis D7a : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S2dVW;Vst;Vtmax;A3A1S3S67A1A2S10G3SfG1G2ScG0SfS15S15S39VW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis D7b : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S2eVW;Vst;Vtmax;A3A1S3S68A1A2S10G3SfG1G2ScG0SfS15S15S3aVW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis NX7a : ltac2:(tb__ "0|0|
S0S26S18S3S67A1A1S18S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7b : ltac2:(tb__ "0|0|
S0S26S18S3S68A1A1S18S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7a : ltac2:(tb__ "0|0|
S44S14S2fS16S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7b : ltac2:(tb__ "0|0|
S44S14S2fS16S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7a : ltac2:(tb__ "0|0|
S43S14S1bS59S1aZ200A1S17S34A1A3S16S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7b : ltac2:(tb__ "0|0|
S43S14S1fS1bS59S1aZ200A1S17S34A1A3A1S16S3S2eVW;Vst;Vtmax;A3A1A1A3").
Variables s8a s8b : wsub.
Hypothesis ENT8a : ltac2:(tb__ "0|0|
S0S9S5S67S37VW;Vst;Vtmax;A3Vs8a;A3SaA3").
Hypothesis ENT8b : ltac2:(tb__ "0|0|
S0S9S5S68S37VW;Vst;Vtmax;A3Vs8b;A3SaA3").
Hypothesis SID8a : ltac2:(tb__ "0|0|
S0S9S4aVs8a;S27A2SaA3").
Hypothesis SID8b : ltac2:(tb__ "0|0|
S0S9S4aVs8b;S27A2SaA3").

Hypothesis G7p : ltac2:(tb__ "0|0|
S44S14S2fS16S3S33VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7p : ltac2:(tb__ "0|0|
S43S14S1fS1bS5aS17PcA1S35A3A1S16S3S33VW;Vst;Vtmax;A3A1A1A3").
Hypothesis W7p : ltac2:(tb__ "0|0|
S0S9S1eS3S30VW;Vst;Vtmax;A3A1A1SaA3").
Hypothesis D7p : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S33VW;Vst;Vtmax;A3A1S3S30VW;Vst;Vtmax;A3A1A2S10G3SfG1G2ScG0SfS15S15S7cS3dA4SbG0A1A3ScS14S24S1aZ1A1S3fA2SbS14A1A3A4A2A3").
Hypothesis NX7p : ltac2:(tb__ "0|0|
S0S26S18S3S30VW;Vst;Vtmax;A3A1A1S18S3S33VW;Vst;Vtmax;A3A1A1A3").

Hypothesis F7an : ltac2:(tb__ "0|0|
S43S14S1bS5aS17PcA1S35A3S16S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7bn : ltac2:(tb__ "0|0|
S43S14S1bS5aS17PcA1S35A3S16S3S2eVW;Vst;Vtmax;A3A1A1A3").

Lemma nmod8_of_fact : ltac2:(tb__ "0|4|
S63S60S19S19SdS53Q40M0A1A1S47S4S9S29Vsegs;S42VW;Vst;R8R7R6A5R2R5R4R3A6S44S14S2fS16S3R3A1A1A3S43S14S9S14Lb;R3S1bS5aS17PcM1A1S35A3M2S1fG2A1X9x2S16S3R4A1A1A3S9OLb;R4S0S25S4bS54G0S20R9G1A2A2Z8A2Z0A3M3S2G3A1X9x2F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (JGb_rigid nW st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & _).
  destruct (JGb_model nW st A Kc rho rhoE tp tr md (proj2 Hw)) as [_ HN]. cbn zeta in HN.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F.
  assert (EV : bv_unsigned (eval rhoE n8e) = bv_unsigned (rw rho 12%positive) - bv_unsigned (rw rho 12%positive) mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, u64_lit by (unfold M48; lia). apply land_M48. pose proof (urange (rw rho 12%positive)). lia. }
  destruct b; cbn [holds eval] in F; fold n8e in F; cbn [branch_taken] in F; unfold bv_eqb in F; rewrite E12, EV in F.
  - apply Z.eqb_eq in F. lia.
  - intros E0. apply F. apply Z.eqb_eq. lia.
Qed.

Theorem spine_s7 : ltac2:(tb__ "0|5|
S47OF_;S63S60S19SdS53Q40M0A1A1S48S70VW;Vst;A2S61R5A1S2bVsegs;R8S2aR6A1A3S4eZ1S72R8S54G0S20R6PcM1A2A2A2A2S0S25S4bS54G0S20R7G1A2A2Z8M2A2Z0M3A3S19S46Vsegs;RcS29Vsegs;S42VW;Vst;RbRaR9A5S37VW;Vst;Vtmax;A3R1R8A5R7A4FrhoX;F_;S2S0S25S4bS54G0S20R8G1A2A2G2A2G3A3A1S19S46Vsegs;RdS29Vsegs;S42VW;Vst;RcRbRaA5M4S30VW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;S19S46Vsegs;RdS29Vsegs;G4S3eVW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC8 HC7p rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c8bc; 0x3ca04] GW [C7 W st tmax] [E7c1 W st tmax; E7c2 W st tmax; E7p W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7a F7an)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8a))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c1' (C8 W st tmax) s8a rhoX tp w ENT8a SID8a); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c1', upd. lazy zeta.
      apply (class_restate_gen (E7c1 W st tmax) _ (creg7a W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7a TAB7a W7a D7a NX7a); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7a F7a).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7b F7bn)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8b))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c2' (C8 W st tmax) s8b rhoX tp w ENT8b SID8b); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c2', upd. lazy zeta.
      apply (class_restate_gen (E7c2 W st tmax) _ (creg7b W st tmax) 24 62%nat A Kc rho tp w rhoX OV7b TAB7b W7b D7b NX7b); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7b F7b).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 <> 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ false Hw G7p F7p)|]. intros Hm8.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7p Hm8 rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G7p Hcnt) as PV. cbn zeta in PV.
      destruct w as [tr [ms md]].
      unfold C7p, upd. lazy zeta. eapply SPA_restate; [exact W7p | exact D7p | exact NX7p | | | exact Hw].
      * unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_a0e7 rhoX _ _ _ _ _ _ PV).
      * apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. fold LPe. rewrite (pv_lp1 rhoX _ _ _ _ _ _ PV Hm8). rewrite u64_lit by lia. lia.
  - left. reflexivity.
Qed.
End B11S.

Section B12S.
Hypothesis Cert7p : ltac2:(tb__ "0|1|
S0S9S6dS6fUfa0ScS25Z3ca04SbS25A1A3S27ScS4S30VW;Vst;Vtmax;A3SbS4A1M0A3ScS4S31VW;Vst;Vtmax;A3ScS4S32VW;Vst;Vtmax;A3G0A3A3A6SaA3").
Definition E7q1' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S31VW;Vst;Vtmax;A3Z3ca04ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Definition E7q2' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S32VW;Vst;Vtmax;A3Z3ca04ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Hypothesis OV7c : ltac2:(tb__ "0|0|
S0S9S65P9dS3bVW;Vst;Vtmax;A3A2SaA3").
Hypothesis OV7d : ltac2:(tb__ "0|0|
S0S9S65P9dS3cVW;Vst;Vtmax;A3A2SaA3").
Hypothesis TAB7c : ltac2:(tb__ "0|0|
S0S9S66P9dS3bVW;Vst;Vtmax;A3S64Z208S6bS6cS55S56S57S55S58A1A1A1A1A1A1A5SaA3").
Hypothesis TAB7d : ltac2:(tb__ "0|0|
S0S9S66P9dS3cVW;Vst;Vtmax;A3S64Z18U3eA5SaA3").
Hypothesis W7c : ltac2:(tb__ "0|0|
S0S9S1eS3S69A1A1SaA3").
Hypothesis W7d : ltac2:(tb__ "0|0|
S0S9S1eS3S6aA1A1SaA3").
Hypothesis D7c : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S31VW;Vst;Vtmax;A3A1S3S69A1A2S10G3SfG1G2ScG0SfS15S15S3bVW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis D7d : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S32VW;Vst;Vtmax;A3A1S3S6aA1A2S10G3SfG1G2ScG0SfS15S15S3cVW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis NX7c : ltac2:(tb__ "0|0|
S0S26S18S3S69A1A1S18S3S31VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7d : ltac2:(tb__ "0|0|
S0S26S18S3S6aA1A1S18S3S32VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7c : ltac2:(tb__ "0|0|
S44S14S2fS16S3S31VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7d : ltac2:(tb__ "0|0|
S44S14S2fS16S3S32VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7c : ltac2:(tb__ "0|0|
S43S14S1bS59S1aZ200A1S17S34A1A3S16S3S31VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7d : ltac2:(tb__ "0|0|
S43S14S1fS1bS59S1aZ200A1S17S34A1A3A1S16S3S32VW;Vst;Vtmax;A3A1A1A3").
Variables s8c s8d : wsub.
Hypothesis ENT8c : ltac2:(tb__ "0|0|
S0S9S5S69S38VW;Vst;Vtmax;A3Vs8c;A3SaA3").
Hypothesis ENT8d : ltac2:(tb__ "0|0|
S0S9S5S6aS38VW;Vst;Vtmax;A3Vs8d;A3SaA3").
Hypothesis SID8c : ltac2:(tb__ "0|0|
S0S9S4aVs8c;S27A2SaA3").
Hypothesis SID8d : ltac2:(tb__ "0|0|
S0S9S4aVs8d;S27A2SaA3").

Theorem spine_s7p : ltac2:(tb__ "0|0|
S47OF_;S63S60S19SdS53Q40A1A1S48S70VW;Vst;A2S61R5A1S2bVsegs;R8S2aR6A1A3S19S46Vsegs;RaS29Vsegs;S42VW;Vst;R9R8R7A5S38VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S19S46Vsegs;RbS29Vsegs;S42VW;Vst;RaR9R8A5S30VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC8 rhoE.
  apply (cfg_soundA segs 4000%nat [0x3ca04] GW [C7p W st tmax] [E7q1 W st tmax; E7q2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7p.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8c))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q1' (C8p W st tmax) s8c rhoX tp w ENT8c SID8c); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q1', upd. lazy zeta.
      apply (class_restate_gen (E7q1 W st tmax) _ (creg7c W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7c TAB7c W7c D7c NX7c); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7c F7c).
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8d))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q2' (C8p W st tmax) s8d rhoX tp w ENT8d SID8d); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q2', upd. lazy zeta.
      apply (class_restate_gen (E7q2 W st tmax) _ (creg7d W st tmax) 24 62%nat A Kc rho tp w rhoX OV7d TAB7d W7d D7d NX7d); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7d F7d).
  - left. reflexivity.
Qed.
End B12S.

Section B13S.

Variables (CC8 CC9 EE8a EE8b CC8ma : axst).
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S9S6dS6fUfa0ScS25Zdb004ScS25Z3ca54SbS25A1A3A3S27ScS4VCC8;SbS4A1M0A3ScS4VEE8a;ScS4VEE8b;G0A3A3A6SaA3").

Hypothesis HCC8ma : ltac2:(tb__ "0|1|
S0S4VCC8ma;S36VW;Vst;Vtmax;VEE8a;S41ScSeS12S15A2M0SfS12S15UaS40A4SbG0A1A3SbS1cA1S13SbS14A1A9A3").
Hypothesis W8a : ltac2:(tb__ "0|0|
S0S9S1eS3VCC8ma;A1A1SaA3").
Hypothesis D8a : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3VEE8a;A1S3VCC8ma;A1A2S10G3SfG1G2SbG0A1SbS14A1A4A2A3").
Hypothesis NX8a : ltac2:(tb__ "0|0|
S0S26S18S3VCC8ma;A1A1S18S3VEE8a;A1A1A3").
Variables (s8 sd8 : wsub) (R8 : list sobj) (T8 : axst).
Hypothesis He8 : ltac2:(tb__ "0|1|
S0S11SdS1cA1M0A1S79VCC8ma;S5dVs8;A3S10G0VR8;A2A3").
Hypothesis Hchk8 : ltac2:(tb__ "0|0|
S0S9S78VCC8ma;S5dVs8;VR8;S73S8S4S7S5eA4A5SaA3").
Hypothesis HT8 : ltac2:(tb__ "0|0|
S0S4S7aVs8;S5dS74S7bS5fA1A1VCC8ma;VR8;A5VT8;A3").
Hypothesis FBC8 : ltac2:(tb__ "0|1|
S0S9S45S14S21S18S3VCC8ma;A1M0A1A1S16G0A1A3SaA3").
Hypothesis FBT8 : ltac2:(tb__ "0|0|
S0S9S45S14S21S18S3VT8;A1A1A1S16S3VCC8ma;A1A1A3SaA3").
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S9S5S77VT8;S16S3VCC8ma;A1A1A2VCC9;Vsd8;A3SaA3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0S9S4aVsd8;S27A2SaA3").
Hypothesis NXC8 : ltac2:(tb__ "0|0|
S7dS27S18S3VCC8ma;A1A1A2").

Variables (i8 : nat) (S8s : sstate).
Hypothesis SPL8 : ltac2:(tb__ "0|0|
S0S11S1dA1S75S3VEE8b;A1Vi8;S1aZ1000A1A3S10S1dVS8s;A2A3").
Let X8b : axst := ax_setS EE8b S8s.
Variables (s8b sd8b : wsub) (R8b : list sobj) (T8b : axst).
Hypothesis He8b : ltac2:(tb__ "0|1|
S0S11SdS1cA1M0A1S79VX8b;S5dVs8b;A3S10G0VR8b;A2A3").
Hypothesis Hchk8b : ltac2:(tb__ "0|0|
S0S9S78VX8b;S5dVs8b;VR8b;S73S8S4S7S5eA4A5SaA3").
Hypothesis HT8b : ltac2:(tb__ "0|0|
S0S4S7aVs8b;S5dS74S7bS5fA1A1VX8b;VR8b;A5VT8b;A3").
Hypothesis FBC8b : ltac2:(tb__ "0|1|
S0S9S45S14S21S18S3VX8b;A1M0A1A1S16G0A1A3SaA3").
Hypothesis FBT8b : ltac2:(tb__ "0|0|
S0S9S45S14S21S18S3VT8b;A1A1A1S16S3VX8b;A1A1A3SaA3").
Hypothesis NXC8b : ltac2:(tb__ "0|0|
S7dS27S18S3VX8b;A1A1A2").

Variables (i9 : nat) (SU SM : sstate).
Let U8b0 : axst := ltac2:(tb__ "0|0|
S6eScS14S1fS1bS59S17PcA1S1aZ1000A1A3A1SbS14A1A3VCC9;A2").
Hypothesis SPLU : ltac2:(tb__ "0|0|
S0S11S1dA1S75S3VU8b0;A1Vi9;S1aZ1000A1A3S10S1dVSU;A2A3").
Let U8b : axst := ax_setS U8b0 SU.
Hypothesis ENTU : ltac2:(tb__ "0|0|
S0S9S5S77VT8b;S16S3VX8b;A1A1A2VU8b;Vsd8b;A3SaA3").
Hypothesis SIDU : ltac2:(tb__ "0|0|
S0S9S4aVsd8b;S27A2SaA3").
Hypothesis MRG : ltac2:(tb__ "0|0|
S0S11S1dA1S76S3VU8b;A1Vi9;A2S10S1dVSM;A2A3").
Variable s9m : wsub.
Hypothesis ENTM : ltac2:(tb__ "0|0|
S0S9S5S6VU8b;VSM;A2VCC9;Vs9m;A3SaA3").
Hypothesis SIDM : ltac2:(tb__ "0|0|
S0S9S4aVs9m;S27A2SaA3").

Theorem spine_s8_gen : ltac2:(tb__ "0|2|
S47OF_;S63S60S19SdS53Q40A1A1M0S48S70VW;Vst;A2S61R5A1S2bVsegs;R8S2aR6A1A3S19G0S46Vsegs;RbS29Vsegs;S42VW;Vst;RaR9R8A5M1VCC9;R2R1A5R6A4FtpX;FrhoX;S19S46Vsegs;RbS29Vsegs;G1VCC8;R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC9 rhoE.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [0xdb004; 0x3ca54] GW [CC8] [EE8a; EE8b] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - exact HST.
  - exact Cert8.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
      2:{ apply (call_gen nW st CC8ma T8 CC9 s8 R8 sd8 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                  eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He8 Hchk8 HT8 FBC8 FBT8 ENT9 SID9 NXC8 eq_refl
                  ok A Kc rho tp rhoX Q HUS HKc Hokf HC9). }
      rewrite HCC8ma. unfold upd. lazy zeta. rewrite HCC8ma in W8a, D8a, NX8a. unfold upd in W8a, D8a, NX8a.
      eapply SPA_restate; [exact W8a | exact D8a | exact NX8a | constructor | constructor | exact Hw].
    +
      eapply triple_conseq; [intros w Hw; exact (SPA_split segs (JGb W st A Kc rho) rhoX EE8b i8 (SLit 4096) S8s tp w SPL8 Hw) | intros w Hw; right; exact Hw |].
      apply (call_gen nW st X8b T8b U8b s8b R8b sd8b Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
               eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He8b Hchk8b HT8b FBC8b FBT8b ENTU SIDU NXC8b eq_refl
               ok A Kc rho tp rhoX Q HUS HKc Hokf).
      intros rhoY tpY.
      eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC9 (rho_sub rhoY s9m) tpY)].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_setS U8b SM) CC9 s9m rhoY tpY w ENTM SIDM HST).
      exact (SPA_merge segs (JGb W st A Kc rho) rhoY U8b i9 SM tpY w MRG Hw).
  - left. reflexivity.
Qed.
End B13S.
End S8.
End SpineMallocS8.

(* [comment removed for export] *)
Module F0A_minst.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "FcsrFrm0"; "mkSS"; "valuation"; "SVar"; "swf"; "rw"; "sprop"; "DUnknown"; "SLit"; "agree_below"; "cell"; "holds"; "mkObj"; "obj_range"; "smatch"; "soff"; "sprop_below"; "ss_objs"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "app"; "nil"; "cons"; "None"; "false"; "list"; "true"; "bool"; "prod"; "Some"; "fst"; "option"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@Stdlib.ZArith.BinInt.Z"; "le"; "div"; "add"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "MIDPC"; "regs_mid"; "stack_win_mid"; "Pre_mid"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NFS"; "O_pad"; "XI"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "A_globals"; "mkA"; "unwind_objs"; "ustop"; "F_sp_high"; "J_free_preT"; "KcA"; "UStopLeOrPc"; "base_sv"; "free_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst"; "PMID_fc"; "sa_m"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "O_sh"; "RT_f"; "VOBJ"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_signed"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.F0A_minst.StatesM"; "sd_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@Stdlib.Lists.List"; "In"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma stack_winm_range : ltac2:(tb__ "0|3|
S1cS57A1S4S14S1fS1cS59A1S58A2S10R4R3R2R1A4S64S0S2fS13R3A1A3SdR5S40A2S25S27Z7fff7f800000S21S15S15SfR6S47A2M0A3M1A2S25S24S15S23S15S15G0A3M2S56Q40S7R6PaA2A2A3S27G1G2A2A2A2F_;F_;F_;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w Hsm Hin Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of, stack_win_mid in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Section StatesM.
Variable khi : bool.
Variables (W : list ulink) (st : ustop) (q : qvar).
Let PREOBJS : list sobj := ltac2:(tb__ "0|0|
S19S0S2fS17S0S3eVW;A1S17S0S19S0SeS5PcA1SaZ0A1S5PdA1S18ScA1S9A5S18S0A1A3S3cA3A3A3").
Let PREFACTS : list sprop := ltac2:(tb__ "0|0|
S17S8S48VW;Vst;A2S46S45A1A3").
Definition sa_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1VPREOBJS;VPREFACTS;S26S1bA9").
Definition sb_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1S17S0VPREOBJS;S31S35S0S34S37Vq;A1A4A3VPREFACTS;S26S1bA9").
Definition sc_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1S17S0S17S0VPREOBJS;S31S35S0S34S37Vq;A1A4A3S19S0S50S18S0A1A3A3VPREFACTS;S26S1bA9").
Definition sd_m : sstate := ltac2:(tb__ "0|1|
S3S2dS2eS2cS2S1aS1A1S17S0S17S0S17S0VPREOBJS;S31S35S0S34S37Vq;A1A4A3S19S0S50S18S0A1M0A3A3S19S0S38G0A3A3VPREFACTS;S26S1bA9").
Definition se_m : axst := ltac2:(tb__ "0|0|
S3dS5bS5dS36Vkhi;VW;Vst;Vq;A4A2S18S1fS1S1A2A1A2").
End StatesM.

Definition PMID_fc (khi : bool) (W : list ulink) (st : ustop) (q : qvar) : axst := ltac2:(tb__ "0|0|
S3dS3S2dS2eS2cS2S1aS1A1S17S0S17S0S19S0S2fS17S0S3eVW;A1S3cA3A3S51A3S52Vq;A1A3S36Vkhi;VW;Vst;Vq;A4S26S1bA9S18S1fS1S1A2A1A2").
Lemma Pre_mid_sa : ltac2:(tb__ "0|0|
S1cS3bA1S3fS24S32S30R2R1A2S33S4bR2R1A2S18S1fS1S1A2A1S44A3A3Fst;FW;").
Proof. reflexivity. Qed.

Section INSTM.
Let segs : list Segment := segsA.
Variable khi : bool.
Variable nW : nat. Variable st : ustop. Variable q : qvar.
Let W : list ulink := Wcan nW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S41VAInv;VW;Vst;VA;VKc;A5").

Hypothesis Wb : ltac2:(tb__ "0|0|
S24S1eS6S4cVW;Vst;Vq;A3A1S1dA3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S24S1eS6S4dVW;Vst;Vq;A3A1S1dA3").
Hypothesis Wd : ltac2:(tb__ "0|0|
S24S1eS6S4eVW;Vst;Vq;A3A1S1dA3").
Hypothesis Fe : ltac2:(tb__ "0|0|
S24S1eS65S8S12S26A1S36Vkhi;VW;Vst;Vq;A4A3S1dA3").
Hypothesis AXI : ltac2:(tb__ "0|0|
S24S22S32A1S5cS4fVkhi;VW;Vst;Vq;A4S39VnW;Vq;A2A2S20S32S4aVkhi;VW;Vst;Vq;A4A2A3").

Lemma bv_signed_small : ltac2:(tb__ "0|1|
S15S25S27Z0R1A2S2aR1S2bZ2Z3fA2A2A2S24S15S55Q40M0S53G0R2A2A2R2A3F_;Fz;").
Proof.
  intros z Hz. rewrite bv_signed_U, u64_lit by lia. unfold Zsigned, H63v, M64v. destruct (Z.ltb_spec z 9223372036854775808); lia.
Qed.
Lemma div8_sum_le : ltac2:(tb__ "0|2|
S15S15S27Z0R2A2M0G0S27S29S28R4Z8M1A2S28R3G1A2A2S28S29R4R3A2G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
  apply Z.div_le_lower_bound; lia.
Qed.
Lemma soff_var : ltac2:(tb__ "0|1|
S4S16S15S24S54Q40M0A1S7R3R2A2S53G0R1A2A3S25S27Z0R2A2S2aR2S2bZ2Z3fA2A2A2S24S15S11R5S5R4A1A2R3A3F_;F_;Fz;Fi;Frho;").
Proof. intros rho i z E Hz. unfold soff. cbn [eval]. rewrite E. apply bv_signed_small. exact Hz. Qed.

Theorem f_instantiate_mid : ltac2:(tb__ "0|0|
S60S42S4S4S1cS54Q40A1A1S5aS15S15S15S24S3fVst;S43A3S24S1cS3bA1VW;S18S3bA1A3F_;S63VW;Vst;A2SbS26R9R8A3S3aVkhi;VW;Vst;Vq;R9R6R5R4S62S61RcA1A1A9S49Vsegs;VJ;RdRcA2S30VW;Vst;A2RbR9R8A6S25S5fRcRbA2S49Vsegs;S5eVnW;Vst;S1dReRdRbA6S4aVkhi;VW;Vst;Vq;A4RbRaR9A6A2F_;F_;F_;F_;F_;Fn8;Fn;Fp;Fw;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp w p n n8 HW HUS Hag2 IFF H.
  assert (Hag : agree_below NF rho rho1) by (eapply agree_below_le; [|exact Hag2]; cbv; discriminate).
  destruct IFF as [E12 E13 E105 E106 Hpn Hcarve Hzone Hpd Hsh Hpadm Hfacts Hrig].
  split; [exact (Hrig rho (agree_below_vals _ _ _ Hag))|]. unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hpn.
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  pose proof HA as (HG & _).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.

  assert (H1 : SPA segs (J A Kc) (Pre_mid W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|exact Hag2]; cbv; discriminate | apply (JFr_agree nW st true A Kc rho rho1); [exact HUS | exact Hag]]. }
  clear H HsmA.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by (symmetry; apply (proj1 Hag); unfold NF; lia).

  pose proof (proj2 H1) as (_ & _ & _ & _ & _ & _ & Htop1).
  assert (TOPlo : TOP <= fst (obj_range rho1 stack_win)) by exact Htop1.

  assert (H2 : SPA segs (J A Kc) (mkAX (sa_m W st) [] base_sv) rho1 tp w) by exact H1.
  clear H1.

  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_m]; apply in_or_app; right; cbn; tauto).
  destruct (stack_winm_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W'] eqn:EW; [constructor|].
    destruct st; [|discriminate (HW eq_refl)].
    assert (HC : Forall (holds rho1) (chain_pre (l :: W'))).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_m]. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }

  pose proof (urange (rw rho1 12%positive)) as U12. pose proof (urange (rw rho1 13%positive)) as U13.
  assert (Ep : bv_unsigned (rw rho1 12%positive) = p) by (rewrite E12; apply u64_lit; lia).
  assert (En : bv_unsigned (rw rho1 13%positive) = n) by (rewrite E13; apply u64_lit; lia).

  assert (H3 : SPA segs (J A Kc) (mkAX (sb_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sb_m W st q) [] base_sv) with
      (ax_setS (mkAX (sa_m W st) [] base_sv) (let S := ax_S (mkAX (sa_m W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj (NFS q)) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as C.
      destruct k as [[[base lo] hi] cs]. unfold carve_ok in C. cbn zeta in C |- *.
      destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 _)))))))). apply xwords_clear_nil.
    -
      apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
      pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
      destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
      destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia.
      set (b := bv_unsigned (eval rho1 base)) in *.
      cbn [ss_objs ax_S sa_m]. unfold A_globals, O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI, IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
      apply Forall_cons.
      { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; lia. }
      apply Forall_app. split.
      { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
      apply Forall_cons.
      { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
        rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
    - exact Hpd. }
  clear H2.

  assert (Hshb : bv_unsigned (eval rho1 shb) = Sh p).
  { unfold shb. rewrite U_add, U_srl_lit, U_lit. cbn [eval]. rewrite Ep. change (3 mod 64) with 3. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF, M64v. change (2147450880 mod 18446744073709551616) with 2147450880.
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound p 8 (2 ^ 47 / 8) ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small; [reflexivity | lia]. }
  assert (SH1 : 2147450880 <= Sh p) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia).
  assert (SH2 : Sh p + n8 / 8 <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (div8_sum_le p n8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + n8) 140737479966720 8 ltac:(lia) ltac:(lia)) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  assert (SH3 : 0 <= n8 / 8) by (apply Z.div_pos; lia).
  assert (H4 : SPA segs (J A Kc) (mkAX (sc_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sc_m W st q) [] base_sv) with
      (ax_setS (mkAX (sb_m W st q) [] base_sv) (let S := ax_S (mkAX (sb_m W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj shb (SLit 0) vN8g [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SLit 0) = 0) by (apply soff_lit_small; lia).
    assert (Ehi : soff rho1 vN8g = n8 / 8).
    { unfold vN8g. apply (soff_var rho1 106%positive (n8 / 8) E106). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w shb (SLit 0) vN8g NW2 H3 Wc (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Hshb; try lia.
    -
      cbn [ss_objs ax_S sb_f]. apply Forall_app. split.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
          rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
    - intros a Ha. destruct (Hsh a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H3.

  assert (H5 : SPA segs (J A Kc) (mkAX (sd_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sd_m W st q) [] base_sv) with
      (ax_setS (mkAX (sc_m W st q) [] base_sv) (let S := ax_S (mkAX (sc_m W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SVar 12) (SVar 13) vN8 [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SVar 13) = n) by (apply (soff_var rho1 13%positive n E13); lia).
    assert (Ehi : soff rho1 vN8 = n8) by (unfold vN8; apply (soff_var rho1 105%positive n8 E105); lia).
    assert (Eb : bv_unsigned (eval rho1 (SVar 12)) = p) by (cbn [eval]; exact Ep).
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w (SVar 12) (SVar 13) vN8 NW2 H4 Wd (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Eb; try lia.
    -
      cbn [ss_objs ax_S sc_f sb_f]. apply Forall_app. split; [apply Forall_app; split|].
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia. rewrite Elo. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; unfold HIGH_SHADOW_END in *; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
      + apply Forall_cons; [|apply Forall_nil]. unfold ranges_disjoint, O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite Hshb, soff_lit_small by lia. unfold vN8g. rewrite (soff_var rho1 106%positive (n8 / 8) E106) by (split; [lia | apply Z.div_lt_upper_bound; lia]). lia.
    - intros a Ha. destruct (Hpadm a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(unfold HIGH_SHADOW_END in *; lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H4.

  assert (H6 : SPA segs (J A Kc) (se_m khi W st q) rho1 tp w).
  { unfold se_m. change (mkA (with_facts (sd_m W st q) (FACTSc khi W st q)) []) with (ax_with_facts (mkAX (sd_m W st q) [] base_sv) (FACTSc khi W st q)).
    eapply SPA_refacts; [exact H5 | exact Fe |].
    intros Hold. unfold FACTSc.
    assert (HP : Forall (holds rho1) (unwind_factsS W st ++ pre_facts free_depth)).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) Hold). cbn [ss_facts ax_S sd_m]. exact Hp. }
    assert (HD : holds rho1 (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))).
    { apply (proj1 (Forall_forall _ _) HP). apply in_or_app. right. unfold pre_facts, F_depth. cbn. tauto. }
    apply Forall_app in Hfacts as [HFg Hrest]. apply Forall_app in Hrest as [HFp Hrest]. apply Forall_app in Hrest as [HFc HFv].
    apply Forall_app; split; [|exact HFv]. apply Forall_app; split; [|exact HFc]. apply Forall_app; split; [apply Forall_app; split; [exact HP | exact HFg]|].
    assert (HFp' : holds rho1 (SPUle (SLit (atop_lo + 4096)) (SVar 10)) -> Forall (holds rho1) (F_pc khi)).
    { intros H0. clear -H0 HFp. destruct khi; (apply Forall_cons; [exact H0 | exact HFp]). }
    apply HFp'. clear HFp'.

    apply (proj2 (holds_ule rho1 _ _)). rewrite U_lit. cbn [eval]. change ((140735332483072 + 4096) mod M64v) with (140735332483072 + 4096).
    apply (proj1 (holds_bge rho1 _ _)) in HD. rewrite U_lit in HD. cbn [eval] in HD. change (Zsigned ((- free_depth) mod M64v)) with (-4096) in HD.
    unfold obj_range, obj_lo_of, stack_win in SW1. cbn [ob_base ob_lo fst] in SW1. unfold soff in SW1. cbn [eval] in SW1. rewrite bv_signed_U in SW1.
    unfold V_DEPTH in *. lia. }
  clear H5.

  pose proof (SPA_axforms segs (J A Kc) (XI nW q) rho1 (se_m khi W st q) (PMID_fc khi W st q) tp w AXI H6) as H7.

  exact (SPA_withG_intro segs (J A Kc) GW (PMID_fc khi W st q) rho1 tp w H7).
Qed.
End INSTM.
End F0A_minst.

(* [comment removed for export] *)
Module SpineCallocS6.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "la_state"; "mkLeafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "Some"; "option"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "sprop"; "valuation"; "ss_next"; "ss_facts"; "sv"; "SLit"; "eval"; "sprop_below"; "SVar"; "rw"; "sobj"; "swf"; "agree_below"; "holds"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "LQA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C5m1"; "C5m2"; "C5d"; "C5e"; "E5m1"; "E5m2"; "ab_e"; "F_gen"; "BR"; "C5c"; "C6"; "E5j"; "LLe"; "LRe"; "V_RZ"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6"; "re8"; "a0e2"; "len1e"; "len2e"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "modulo"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "cnt_of"; "chk_of"; "cls_of"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "pvals_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "rz"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S41S12S12S9S11A1S1dR4R3R2A3S0S7S43S11S18R5A1R2A3S8A3S60S11S1eR5A1M0R3A3S60S11G0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Definition len1e : sv := ltac2:(tb__ "0|1|
S10S21S10S1fS10S20S10S1fS10S1fS2fS19S37A1A3S16N8A1A3S16Z3A1M0A3S16Z1A1A3S10S20S2fG0A3A3").
Definition re8 : sv := ltac2:(tb__ "0|0|
S10S22S10S1fS10S1fS10S1fS2fS19S37A1A3S19PcA1A3S16Z7A1A3S16Zfffffffffffffff8A1A3").
Definition a0e2 : sv := ltac2:(tb__ "0|0|
S10S1fS10S20S4fS16Z3A1A3S3aA3").
Definition len2e : sv := ltac2:(tb__ "0|1|
S10S21S10S1fS10S20S10S1fS10S1fS4fS10S1fS10S21S2fS4fA3S19S38A1A3A3S16N8A1A3S16Z3A1M0A3S16Z1A1A3S10S20S4fG0A3A3").

Section PSVals.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S6bVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S53S53VSB;S55Vc;S57Z2Z20A2A2A2S55Z10Vx;A2A2").
Let r8 : Z := ltac2:(tb__ "0|1|
S58S53Vn;Z7A2M0S56G0Z8A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_len1 : ltac2:(tb__ "0|0|
S0S3eQ40A1S17Vrho;S51A2S17Vrho;S35A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ab rho _ _ _ _ _ _ PV) as EB. cbn zeta in EB.
  apply bv_eq. unfold len1e, LLe. cbn [eval]. fold ab_e. unfold V_RZ. rewrite E150.
  rewrite sub_val, add_val, srl_val, add_val, add_val, srl_val, srl_val, EB, !u64_lit by lia. change (3 mod 64) with 3.
  replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
  rewrite (Z.mod_small (_ + rzv)) by lia.
  replace ((SB + c * 2 ^ 32 + 16 * x + rzv + (2 ^ 64 - 8)) mod 2 ^ 64) with (SB + c * 2 ^ 32 + 16 * x + rzv - 8).
  2:{ replace (SB + c * 2 ^ 32 + 16 * x + rzv + (2 ^ 64 - 8)) with ((SB + c * 2 ^ 32 + 16 * x + rzv - 8) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)).
  set (q := SB / 2 ^ 16) in *. set (r := rzv / 16) in *.
  replace (SB + c * 2 ^ 32 + 16 * x + rzv - 8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r - 1) * 8) by lia.
  replace (SB + c * 2 ^ 32 + 16 * x) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x) * 8) by lia.
  replace rzv with (2 * r * 8) at 3 by lia.
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma pv_re8 : ltac2:(tb__ "0|0|
S0S40S3fQ40S17Vrho;S4fA2A2S53S53Vab;Vrzv;A2Vr8;A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ab rho _ _ _ _ _ _ PV) as EB. cbn zeta in EB. fold ab in EB.
  pose proof (r8_facts rho _ _ _ _ _ _ PV) as (R1 & R2 & R3 & R4). cbn zeta in R1, R2, R3, R4. fold r8 in R1, R2, R3, R4.
  unfold re8. cbn [eval]. fold ab_e. unfold V_RZ. rewrite E150, E12.
  rewrite and_val, add_val, add_val, add_val, EB, !u64_lit by lia.
  change 18446744073709551608 with (2 ^ 64 - 2 ^ 3).
  rewrite (Z.mod_small (ab + rzv)) by (unfold ab; lia). rewrite (Z.mod_small (ab + rzv + n)) by (unfold ab; destruct (Z_lt_dec n 8); lia).
  rewrite Z.mod_small by (unfold ab; destruct (Z_lt_dec n 8); lia).
  rewrite land_high_mask by (unfold ab; destruct (Z_lt_dec n 8); lia). change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)).
  assert (E : (ab + rzv + n + 7) mod 8 = (n + 7) mod 8).
  { unfold ab. replace (SB + c * 2 ^ 32 + 16 * x + rzv + n + 7) with ((n + 7) + (SB / 2 ^ 16 * 2 ^ 13 + c * 2 ^ 29 + 2 * x + rzv / 16 * 2) * 8) by lia.
    apply Z.mod_add; lia. }
  rewrite E. unfold r8. lia.
Qed.

Lemma pv_a0e2 : ltac2:(tb__ "0|0|
S0S3eQ40A1S17Vrho;S50A2S17Vrho;S31A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_br rho _ _ _ _ _ _ PV) as EBR. cbn zeta in EBR. fold ab in EBR.
  pose proof (r8_facts rho _ _ _ _ _ _ PV) as (R1 & R2 & R3 & R4). cbn zeta in R1, R2, R3, R4. fold r8 in R1, R2, R3, R4, EBR.
  apply bv_eq. rewrite EBR. unfold a0e2, shb. cbn [eval]. fold re8. rewrite add_val, srl_val, pv_re8, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Bf : 0 <= ab + rzv + r8 /\ ab + rzv + r8 <= 140737479966720) by (unfold ab; destruct (Z_lt_dec n 8); lia).
  destruct (Sh_small rho _ _ _ _ _ _ PV (ab + rzv + r8) Bf) as (_ & E & _). rewrite E.
  unfold Sh. pose proof (Z.div_mod rzv 16 ltac:(lia)).
  replace (ab + rzv + r8) with (ab + rzv + (r8 / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma pv_len2 : ltac2:(tb__ "0|0|
S0S3eQ40A1S17Vrho;S52A2S17Vrho;S36A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ab rho _ _ _ _ _ _ PV) as EB. cbn zeta in EB. fold ab in EB.
  pose proof (pv_lr rho _ _ _ _ _ _ PV) as [ELR LR0]. cbn zeta in ELR, LR0.
  pose proof (r8_facts rho _ _ _ _ _ _ PV) as (R1 & R2 & R3 & R4). cbn zeta in R1, R2, R3, R4. fold r8 in R1, R2, R3, R4, ELR, LR0.
  apply bv_eq. rewrite ELR. unfold len2e. cbn [eval]. fold re8. fold ab_e. unfold V_SIZE. rewrite E148.
  rewrite sub_val, add_val, srl_val, add_val, add_val, add_val, sub_val, srl_val, pv_re8, EB, !u64_lit by lia. change (3 mod 64) with 3.
  replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
  assert (Bf : 0 <= ab /\ ab + sz <= 140737479966720 /\ rzv + r8 <= sz) by (unfold ab; destruct (Z_lt_dec n 8); lia).
  replace ((ab - (ab + rzv + r8)) mod 2 ^ 64) with (2 ^ 64 - (rzv + r8)) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
  replace ((2 ^ 64 - (rzv + r8) + sz) mod 2 ^ 64) with (sz - rzv - r8) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite (Z.mod_small (ab + rzv + r8 + _)) by lia.
  replace ((ab + sz + (2 ^ 64 - 8)) mod 2 ^ 64) with (ab + sz - 8) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)). pose proof (Z.div_mod sz 16 ltac:(lia)).
  set (q := SB / 2 ^ 16) in *. set (r := rzv / 16) in *. set (t := sz / 16) in *.
  replace (ab + sz - 8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * t - 1) * 8) by (unfold ab; lia).
  replace (ab + rzv + r8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r + r8 / 8) * 8) by (unfold ab; lia).
  replace (sz - rzv - r8) with ((2 * t - 2 * r - r8 / 8) * 8) by lia.
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End PSVals.

Section S6.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S4bVAInv;VW;Vst;VA;VKc;S19PcA1A6").

Lemma JGb_pvals : ltac2:(tb__ "0|3|
S4cS49S12S12S9S3eQ40M0A1A1S3cS2S23Vsegs;S42VW;Vst;R7R6R5A5R1R4R3R2A6S44S11S30S14S1R2A1A1A3S54Z1S5cR9S3fG0S1aR7PcM1A2A2A2A2S3fG0S1aR8G1A2A2S40S6bR8S4eS4dRbA1A1S5eR1A1M2S5dRbR1A2S6eR1A1S6dG2A1R1A7Tnv;F_;F_;F_;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E Hw HG Hcnt. cbn zeta. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E12' : rw rhoE 12%positive = Z_to_bv 64 nv). { rewrite E12. unfold nv. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E150 : rw rhoE 150%positive = Z_to_bv 64 (rz nv)). { rewrite <- (Hagw 150%positive) by (unfold GW; lia). reflexivity. }
  assert (E155 : rw rhoE 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))). { rewrite <- (Hagw 155%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }
  assert (HF : forall p, In p F_gen -> holds rhoE p). { intros p Hp. exact (fact_of_stateB nW st A Kc rho rhoE tp _ E p Hw (HG p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HF (SPUle (SVar 12) (SLit 64512)) ltac:(unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F. rewrite E12', !u64_lit in F by lia. exact F. }
  assert (RZF : 16 <= rz nv <= 1024 /\ rz nv mod 16 = 0).
  { pose proof (HF (SPUle (SLit 16) (SVar V_RZ)) ltac:(unfold F_gen; cbn; tauto)) as F1.
    pose proof (HF (SPUle (SVar V_RZ) (SLit 1024)) ltac:(unfold F_gen; cbn; tauto)) as F2.
    pose proof (HF (SPAlign V_RZ 4) ltac:(unfold F_gen; cbn; tauto)) as F3.
    cbn [holds eval] in F1, F2, F3. unfold V_RZ in F1, F2, F3. rewrite E150 in F1, F2, F3. pose proof (rz_bound nv). rewrite !u64_lit in F1, F2 by lia.
    destruct F3 as [_ F3]. rewrite u64_lit in F3 by lia. change (2 ^ 4) with 16 in F3. lia. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  pose proof (blk_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as BF. cbn zeta in BF. destruct BF as (Bx & Bal & Blo & Bhi & Breg & _ & _).
  pose proof (geom_old _ (proj1 HA)) as HGe. rewrite kSpaceSize_val in HGe. unfold HIGH_SHADOW_END in HGe.
  destruct HGe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G12 & G13 & G14 & _). pose proof (topG_range (aa_geom A)) as TG.
  unfold kUserSpaceSize in Bhi. unfold region_beg, kRegionSize, kFreeArraySize in Blo, Bhi, Breg. rewrite kSpaceSize_val in Breg.
  assert (NFIT : nv + rz nv <= Size (cls_of nv) /\ (nv < 8 -> 8 + rz nv <= Size (cls_of nv))).
  { clear -C2 Hnv HN. unfold needed8, round_up in C2.
    pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.div_mod (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). split; [|intros]; lia. }
  unfold pvals_ok. repeat split; try assumption; clear -C1 C2 C3 Hnv HN Bx RZF NFIT G12 G13 G14 TG Blo Bhi Breg; lia.
Qed.

Section Call.
Variables (Cst T D : axst) (s : wsub) (R : list sobj) (sd : wsub).
Variables (Pre : axst) (Posts : list leafA) (Pret : sstate).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S9S3A1VPosts;SaS3S6S59VPret;A1S6cA2SbS3A1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S3cOF_;S27S12S9S3eQ40A1A1S24S48R4R3A3S28S48S61R4A3S3bS48R6S23S48R5VPre;R4R3A5S26S48R5S61R4R3VPosts;A6A4F_;F_;Ftp;Frho;FJx;Fok;").
Hypothesis He : ltac2:(tb__ "0|1|
S0SdS9S1bA1M0A1S65VCst;VPre;Vs;A3ScG0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S7S64VCst;VPre;Vs;VR;S5fS3S2S5VPosts;A4A5S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S2S66Vs;VPre;S59VPret;A1VCst;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0S7S43S11S18S13S1VCst;A1M0A1A1S14G0A1A3S8A3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0S7S43S11S18S13S1VT;A1A1A1S14S1VCst;A1A1A3S8A3").
Hypothesis ENT : ltac2:(tb__ "0|0|
S0S7S4S63VT;S14S1VCst;A1A1A2VD;Vsd;A3S8A3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0S7S5aVsd;S39A2S8A3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S68S39S13S1VCst;A1A1A2").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S41S13S1VPre;A1A1S61A3").

Lemma call_gen : ltac2:(tb__ "0|1|
S3cOF_;S4cS49S12S9S3eQ40A1A1M0S12S3dS5bVW;Vst;A2S4aR6A1S24Vsegs;R9S25R7A1A3S12G0S3bVsegs;RcS23Vsegs;S42VW;Vst;RbRaR9A5VD;R2R1A5R6A4FtpX;FrhoX;S3bVsegs;RbS23Vsegs;S42VW;Vst;RaR9R8A5VCst;R6R7A5R5A4F_;F_;F_;F_;FQ;FrhoE;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp rhoE Q HUS HKc Hokf HD.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JGb W st A Kc rho rhoE t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segs ok Jf).
  { intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf rhoE t tr ms md msv' HK HMI Hh Hp Hs). }
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }

  apply (triple_pre_pure segs ok _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_soundA segs ok (JGb W st A Kc rho) Jf Jf (JGb W st A Kc rho) Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD (rho_sub rho' sd) tpL)].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_with_facts T (ss_facts (ax_S Cst))) D sd rho' tpL w ENT SID HST).
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC).
Qed.
End Call.

Section B7S.
Hypothesis Cert5c : ltac2:(tb__ "0|1|
S0S7S62S67Ufa0SaS40Zdb004SbS40A1A3S39SaS2S32VW;Vst;Vtmax;A3SbS2A1M0A3SaS2S2dVW;Vst;Vtmax;A3G0A3A6S8A3").
Hypothesis G5m1 : ltac2:(tb__ "0|0|
S44S11S30S14S1S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m1 : ltac2:(tb__ "0|0|
S0S7S1cS1S29VW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D5m1 : ltac2:(tb__ "0|4|
S0SdSfS9SfS15S15A2M0A1M1S9S11A1M2A2M3A1S69S1S2dVW;Vst;Vtmax;A3A1S1S29VW;Vst;Vtmax;A3A1A2ScG3SeG1G2SaG0SeS15S15S51S35A4SbG0A1A3SbS11A1A4A2A3").
Hypothesis NX5m1 : ltac2:(tb__ "0|0|
S0S41S13S1S29VW;Vst;Vtmax;A3A1A1S13S1S2dVW;Vst;Vtmax;A3A1A1A3").
Variables (s51 sd51 : wsub) (R51 : list sobj) (T51 : axst).
Hypothesis He51 : ltac2:(tb__ "0|1|
S0SdS9S1bA1M0A1S65S29VW;Vst;Vtmax;A3S45Vs51;A3ScG0VR51;A2A3").
Hypothesis Hchk51 : ltac2:(tb__ "0|0|
S0S7S64S29VW;Vst;Vtmax;A3S45Vs51;VR51;S5fS3S2S5S46A4A5S8A3").
Hypothesis HT51 : ltac2:(tb__ "0|0|
S0S2S66Vs51;S45S59S6aS47A1A1S29VW;Vst;Vtmax;A3VR51;A5VT51;A3").
Hypothesis FBC51 : ltac2:(tb__ "0|1|
S0S7S43S11S18S13S1S29VW;Vst;Vtmax;A3A1M0A1A1S14G0A1A3S8A3").
Hypothesis FBT51 : ltac2:(tb__ "0|0|
S0S7S43S11S18S13S1VT51;A1A1A1S14S1S29VW;Vst;Vtmax;A3A1A1A3S8A3").
Hypothesis ENT51 : ltac2:(tb__ "0|0|
S0S7S4S63VT51;S14S1S29VW;Vst;Vtmax;A3A1A1A2S2bVW;Vst;Vtmax;A3Vsd51;A3S8A3").
Hypothesis SID51 : ltac2:(tb__ "0|0|
S0S7S5aVsd51;S39A2S8A3").
Hypothesis NXC51 : ltac2:(tb__ "0|0|
S68S39S13S1S29VW;Vst;Vtmax;A3A1A1A2").

Theorem spine_s5c : ltac2:(tb__ "0|3|
S3cOF_;S4cS49S12S9S3eQ40M0A1A1M1S3dS5bVW;Vst;A2S4aR5A1S24Vsegs;R8S25R6A1A3S54Z1S5cR8S3fG0S1aR6PcA2A2A2A2S12G1S3bVsegs;RcS23Vsegs;S42VW;Vst;RbRaR9A5M2S2bVW;Vst;Vtmax;A3R2R1A5R7A4FtpX;FrhoX;S12S3bVsegs;RcS23Vsegs;G2S32VW;Vst;Vtmax;A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC rhoE.
  apply (cfg_soundA segs 4000%nat [0xdb004] GW [C5c W st tmax] [E5m1 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5c.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen (C5m1 W st tmax) T51 (C5d W st tmax) s51 R51 sd51 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He51 Hchk51 HT51 FBC51 FBT51 ENT51 SID51 NXC51 eq_refl
                ok A Kc rho tp rhoX Q HUS HKc Hokf HC). }
    pose proof (JGb_pvals A Kc rho rhoX tp w _ Hw G5m1 Hcnt) as PV. cbn zeta in PV.
    unfold C5m1, upd. lazy zeta. eapply SPA_restate; [exact W5m1 | exact D5m1 | exact NX5m1 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len1 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End B7S.

Section B8S.
Hypothesis Cert5d : ltac2:(tb__ "0|1|
S0S7S62S67Ufa0SaS40Zdb004SbS40A1A3S39SaS2S2bVW;Vst;Vtmax;A3SbS2A1M0A3SaS2S2eVW;Vst;Vtmax;A3G0A3A6S8A3").
Hypothesis G5m2 : ltac2:(tb__ "0|0|
S44S11S30S14S1S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m2 : ltac2:(tb__ "0|0|
S0S7S1cS1S2aVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D5m2 : ltac2:(tb__ "0|4|
S0SdSfS9SfS15S15A2M0A1M1S9S11A1M2A2M3A1S69S1S2eVW;Vst;Vtmax;A3A1S1S2aVW;Vst;Vtmax;A3A1A2ScG3SeG1G2SaG0SeS15S15S50S31A4SaG0SeS15S15S52S36A4SbG0A1A3A3SbS11A1A4A2A3").
Hypothesis NX5m2 : ltac2:(tb__ "0|0|
S0S41S13S1S2aVW;Vst;Vtmax;A3A1A1S13S1S2eVW;Vst;Vtmax;A3A1A1A3").
Variables (s52 sd52 : wsub) (R52 : list sobj) (T52 : axst).
Hypothesis He52 : ltac2:(tb__ "0|1|
S0SdS9S1bA1M0A1S65S2aVW;Vst;Vtmax;A3S45Vs52;A3ScG0VR52;A2A3").
Hypothesis Hchk52 : ltac2:(tb__ "0|0|
S0S7S64S2aVW;Vst;Vtmax;A3S45Vs52;VR52;S5fS3S2S5S46A4A5S8A3").
Hypothesis HT52 : ltac2:(tb__ "0|0|
S0S2S66Vs52;S45S59S6aS47A1A1S2aVW;Vst;Vtmax;A3VR52;A5VT52;A3").
Hypothesis FBC52 : ltac2:(tb__ "0|1|
S0S7S43S11S18S13S1S2aVW;Vst;Vtmax;A3A1M0A1A1S14G0A1A3S8A3").
Hypothesis FBT52 : ltac2:(tb__ "0|0|
S0S7S43S11S18S13S1VT52;A1A1A1S14S1S2aVW;Vst;Vtmax;A3A1A1A3S8A3").
Hypothesis ENT52 : ltac2:(tb__ "0|0|
S0S7S4S63VT52;S14S1S2aVW;Vst;Vtmax;A3A1A1A2S2cVW;Vst;Vtmax;A3Vsd52;A3S8A3").
Hypothesis SID52 : ltac2:(tb__ "0|0|
S0S7S5aVsd52;S39A2S8A3").
Hypothesis NXC52 : ltac2:(tb__ "0|0|
S68S39S13S1S2aVW;Vst;Vtmax;A3A1A1A2").

Theorem spine_s5d : ltac2:(tb__ "0|3|
S3cOF_;S4cS49S12S9S3eQ40M0A1A1M1S3dS5bVW;Vst;A2S4aR5A1S24Vsegs;R8S25R6A1A3S54Z1S5cR8S3fG0S1aR6PcA2A2A2A2S12G1S3bVsegs;RcS23Vsegs;S42VW;Vst;RbRaR9A5M2S2cVW;Vst;Vtmax;A3R2R1A5R7A4FtpX;FrhoX;S12S3bVsegs;RcS23Vsegs;G2S2bVW;Vst;Vtmax;A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC rhoE.
  apply (cfg_soundA segs 4000%nat [0xdb004] GW [C5d W st tmax] [E5m2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5d.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen (C5m2 W st tmax) T52 (C5e W st tmax) s52 R52 sd52 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He52 Hchk52 HT52 FBC52 FBT52 ENT52 SID52 NXC52 eq_refl
                ok A Kc rho tp rhoX Q HUS HKc Hokf HC). }
    pose proof (JGb_pvals A Kc rho rhoX tp w _ Hw G5m2 Hcnt) as PV. cbn zeta in PV.
    unfold C5m2, upd. lazy zeta. eapply SPA_restate; [exact W5m2 | exact D5m2 | exact NX5m2 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact (pv_a0e2 rhoX _ _ _ _ _ _ PV).
    + exact (pv_len2 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End B8S.

Section B9S.
Hypothesis Cert5e : ltac2:(tb__ "0|1|
S0S7S62S67Ufa0SaS40Z3c80cSbS40A1A3S39SaS2S2cVW;Vst;Vtmax;A3SbS2A1M0A3SaS2S34VW;Vst;Vtmax;A3G0A3A6S8A3").
Variable s6j : wsub.
Hypothesis ENT6j : ltac2:(tb__ "0|0|
S0S7S4S34VW;Vst;Vtmax;A3S33VW;Vst;Vtmax;A3Vs6j;A3S8A3").
Hypothesis SID6j : ltac2:(tb__ "0|0|
S0S7S5aVs6j;S39A2S8A3").
Theorem spine_s5e : ltac2:(tb__ "0|0|
S3cOF_;S4cS49S12S9S3eQ40A1A1S3dS5bVW;Vst;A2S4aR5A1S24Vsegs;R8S25R6A1A3S12S3bVsegs;RaS23Vsegs;S42VW;Vst;R9R8R7A5S33VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S12S3bVsegs;RbS23Vsegs;S42VW;Vst;RaR9R8A5S2cVW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c80c] GW [C5e W st tmax] [E5j W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5e.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s6j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5j W st tmax) (C6 W st tmax) s6j rhoX tp w ENT6j SID6j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End B9S.
End S6.
End SpineCallocS6.

(* [comment removed for export] *)
Module DrainSG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "prod"; "nat"; "pair"; "None"; "false"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "SLit"; "SAlu"; "FcsrFrm0"; "cell"; "mkSS"; "valuation"; "DUnknown"; "SPBranch"; "mkCell"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "NXD"; "F_clsD"; "F_ghD"; "JD"; "JLD"; "O_chkD"; "O_cntD"; "O_mcD"; "DH_ENT"; "DH_RET"; "NXDP"; "O_dstD"; "O_riF"; "dst_cells"; "regsD"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vMFA"; "O_ri"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "O_ctx98"; "O_pgb"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "BASEG"; "F_grow"; "L_dh_g"; "O_stG"; "Pre_dh_g"; "dh_depth_g"; "RTG"; "regsG"; "vSTQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mkA"; "pre_facts"; "A_globals"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "budget_bound"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "O_cfb"; "O_cfc"; "O_insta"; "O_insta2"; "O_rms"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition RTG : list sobj := ltac2:(tb__ "0|0|
S0SaS5dS0SaS5eS0SaS5fS0SaS3fS0SaS40S0SaS41S0SaS3dS0SaS3eS0SaS39S0SaS3bS0SaS3cS0SaS3aS0SaS5cS0SaS5bS1SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition BASEG : list sobj := ltac2:(tb__ "0|0|
S0SaS51S2SaS50S49A3A3").

Definition vSTQ : sv := SVar 230.
Definition O_stG : sobj := ltac2:(tb__ "0|0|
S16S42SdZad0A1SdZc60A1S0S10S15SdZae0A1Z8S4bA3S1S10A1A3S13A5").
Definition regsG : list sv := ltac2:(tb__ "0|1|
S2fS29S0S3S4ScA2M0S5S4ScU4SdS38A1A4S1G0A1A3A2").
Definition F_grow (n : Z) : sprop := ltac2:(tb__ "0|0|
S14S2dS35SeS2cSeS2bS37SdVn;A1A3SdZ2A1A3A3").
Definition dh_depth_g : Z := 512.
Definition Pre_dh_g (n : Z) : axst := ltac2:(tb__ "0|0|
S4eS11S23S4aS2eSfS6ScA1S2SaS43S0SaS46S0SaS20Vn;A1S0SaS22Vn;A1S0SaS21S55Z2Vn;A2A1S0SaS36S1SaA1A3A3A3A3A3A3S2SbS4fS48A1S2SbS1cS2SbS1dS0SbS44Vn;A1S1SbA1A3A3A3A3S1bS7A9S1S3ScScA2A1A2").
Definition L_dh_g (n : Z) : axst := ltac2:(tb__ "0|1|
S4eS11S24S2fS30S1bA1S0S3S4ScA2M0S5S4ScU4SdS38A1A4S1G0A1A3A2S2eSfS6ScA1S2SaS43S0SaS46S0SaS20Vn;A1S0SaS22Vn;A1S0SaS21Vn;A1S0SaS27Vn;SeS2bS35SdZ40000A1A3A2S0SaS26Vn;S28Vn;A1A2S1SaA1A3A3A3A3A3A3A3S2SbS4fS48A1S2SbS1cS2SbS1dS0SbS44Vn;A1S1SbA1A3A3A3A3S25S7A9S1S3ScScA2A1A2").

Section DHG.
Variable n : Z.

Definition drain_contract_g : Prop := ltac2:(tb__ "0|1|
S59OF_;S52S4cS2aS12S8S56Q40A1A1S4dR4A1S33S17R7S32R5A1A3S5aS17R8S32R6A1A3S54S53R8A1S34A2S58S17RaS31S17S1eVn;S9R9R8R7A5S47Vn;A1R6R5A5S1aS17S1bR6R5S0S3S18S19A2M0S5S18S19S45Vn;A1S1fR9R8R7A3A4S1G0A1A3A5A4F_;F_;F_;F_;Ftp;Frho;Fc;FKc;FA;Fok;").
Definition drain_contract_gE : Prop := ltac2:(tb__ "0|1|
S52S4cS2aS12S8S56Q40A1A1S4dR4A1S54S53R6A1S34A2S57S17S31S17S1eVn;S9R7R6R5A5S47Vn;A1R4R3A5S1aS17S1bR4R3S0S3S18S19A2M0S5S18S19S45Vn;A1S1fR7R6R5A3A4S1G0A1A3A5A3F_;F_;Ftp;Frho;Fc;FKc;FA;").
End DHG.

Goal swf (ax_S (Pre_dh_g 8)) = true /\ swf (ax_S (L_dh_g 8)) = true. Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End DrainSG.

(* [comment removed for export] *)
Module SpineCallocR2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "div"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "cons"; "pair"; "bool"; "true"; "prod"; "nil"; "app"; "Some"; "option"; "false"; "andb"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rw"; "sobj"; "sprop"; "ss_next"; "obj_range"; "ss_lenient"; "holds"; "ss_facts"; "ss_objs"; "sstate"; "swf"; "agree_below"; "eval"; "ranges_disjoint"; "rm"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "ax_setS"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_thread"; "ag_spacebeg"; "ageom"; "aa_cache_inited"; "ag_ctx"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "PCE"; "phase"; "frozen"; "ghosts"; "ph_fill"; "gh_new"; "gh_nf"; "ph0"; "ph_cnt"; "ph_pop"; "zoneR"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "ustop"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "cR0"; "k_e"; "GR"; "fa_e"; "ri_e"; "vFA"; "vK"; "vRI"; "O_pcm"; "O_ri"; "cR1"; "factsR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "cfacts"; "rigids"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "needed8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "max_count"; "kSpaceSize"; "region_info"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "bview"; "present"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "F_gen"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "FACAP"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1"; "armint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5";
"tab1_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@Stdlib.Lists.List"; "In"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rigids (A : AA) (rb r : valuation) : Prop := ltac2:(tb__ "0|5|
S34Q40M0S1cVrb;PcM1A2M2A2S4S6dR1A1S4S37VA;A1S3aS0S1S32G0A1M3S1cVr;G1A2G2A3S0S1G3S1cVr;P94A2S33G0S71R2A1A2A3S0S1G3S1cVr;P97A2S33G0S38R1A1A2A3S0S1G3S1cVr;P98A2S33G0S3cR1A1A2A3S0S1G3S1cVr;P9bA2S33G0S39R1A1M4A2A3S0S1G3S1cVr;P9cA2S33G0S6G4S73A2A2A3S0S1G3S1cVr;P9dA2S33G0S6fR3A1A2A3S1G3S1cVr;P9eA2S33G0R2A2A3A2A2A2A2A2A2A2TG;Tc;Tnv;").
Lemma entry_rigids : ltac2:(tb__ "0|0|
S36S1aScS32Q40A1A1S51ScS53A1S54S1aS1aS45R8R7R6R5R4R3R2A7S48R8R2A2S69RaR9R3A3F_;F_;Fr;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho r (Hag & _) [Fw _]. destruct Hag as (Hagw & _ & _).
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  unfold rigids. cbn zeta. rewrite E12.
  repeat split; rewrite <- (Fw _) by lia; try reflexivity; rewrite <- (Hagw _) by (unfold GW; lia); reflexivity.
Qed.

Definition cfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|d|
S34Q40S1cVrb;PcA2A2S4S6dR1A1S4S6eVA;R2A2S3dS37VA;A1S3aS39R1A1S4S38R2A1S4S0S0S0S5Z1M0R6A2S5R6Zfc00A2A2S0S0S5G0R5A2S5R5Z1eA2A2S0S0S5Z20S71R5A1M1A2S5G1Z10000M2A2A2S1S4S8G1Z10A2Z0M3A3A2A2A2S0S0S0S5G0S8aR5A1M4A2S5G4Z8A2A2S0S1S4S9Z2G4A2S72R5A1A3S5S9G4G1A2G2A2A2A2S0S0S1S4S8S42R4A1M5Z40000M6A2G3A3S0S0S5G3S3eR4A1M7A2S5G7G5A2A2S0S5G5Ze0000000A2S0S1S4S8G7G1A2G3A3S7G5S6G7G1A2A2A2A2A2A2S0S0S1S4S8S41R4A1M8G6A2G3A3S0S5S9Z4SbS18S4S40R4A1A2A1A2G8A2S5G8Z20000000A2A2A2S0S0S5G5S89R5A1A2S0S5G8S88R5A1A2S1ScS4A1S3fR4A1S12S4A1A3A2A2S0S0S1S4S8R2G2A2G3A3S0S5Z100080000000R2A2S0S5S6S6R2Z2000000000A2Z1000M9A2MaS43R3A1MbA2S5GbZ7fffff800000A2A2A2A2S0S0S5G9R1A2S0S5S6R1G9A2McGbA2S0S2S5GcG2A2S5Z643000R1A2A2S2S5GcR2A2S5GaR1A2A2A2A2A2S2S5GcZ7fff7000A2S5Z10007fff8000R1A2A2A2A2A2A2A2A2A2TT;TSB;TG;Tcs;Tc;Tnv;").
Lemma entry_cfacts : ltac2:(tb__ "0|0|
S36S1aScS32Q40A1A1S51ScS53A1S54S1aS45R7R6R5R4R3R2R1A7S68R8R7A2F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _). unfold cfacts. cbn zeta.
  set (nv := bv_unsigned (rw rb 12%positive)) in *.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4). destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  destruct (cap_facts _ C1) as (S1 & _).
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI10 & _ & MC10 & FC10).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TI, TB.
  pose proof (topG_range (aa_geom A)) as TG. destruct (proj1 HI3) as (PS1 & _). rewrite kSpaceSize_val in PS1.
  assert (Hc0 : cs_cache (cst_of A nv) = []).
  { unfold cnt_of in Hcnt. destruct (cs_cache (cst_of A nv)); [reflexivity | cbn [length] in Hcnt; lia]. }
  unfold cst_of. fold (cst_of A nv).
  split; [repeat split; first [exact C3 | lia]|]. split; [repeat split; lia|].
  split; [unfold cst_of; repeat split; first [exact N1 | exact N4 | lia]|].
  split; [unfold cst_of; repeat split; first [exact N5 | lia]|].
  split; [split; [exact MC10 | split; [exact FC10 | exact Hc0]]|].
  split; [repeat split; first [exact G12 | lia]|]. split; [repeat split; lia | lia].
Qed.

Definition tabK_okb : bool := ltac2:(tb__ "0|2|
S17S8cPdcM0S5dS4SaR1Z2M1A2Lz;G1UfA5S8dG0S5dA2A2").
Lemma tabK_ok : tabK_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma r1_diffs : ltac2:(tb__ "0|1|
S36S1aS1aS68R3R2A2S69R4R3R2A3S49R5R4R3A3S77R4SdS11S1bS1bA2M0SeS1bS1bS60S63A4SdG0SeS1bS1bS5dS62A4SdG0SeS1bS1bS5fS61A4S12G0A1A3A3A3A2F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & K2 & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & _ & _).
  destruct RG as (_ & _ & _ & _ & E155 & E156 & _ & E158). destruct GH as (Q220 & _ & _ & _ & _ & Q225 & Q226 & Q227 & _).
  unfold region_info, kRegionInfoStride in Q225. rewrite kSpaceSize_val in Q225, E156.
  unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Q226.
  unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - unfold ri_e, vRI, vRIS, V_CLS. cbn [eval]. rewrite E156, E158, Q225. apply bv_eq.
    rewrite add_val, sll_val, !u64_lit by lia. change (7 mod 64) with 7. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 7)) by lia. rewrite Z.mod_small by lia. lia.
  - unfold vK. cbn [eval]. rewrite Q227. pose proof tabK_ok as TK. unfold tabK_okb in TK. apply andb_prop in TK as [TK OV].
    rewrite (tab1_ok_sound 220 k_e (fun z => z / 2) 2 15 r (max_count (cls_of (bv_unsigned (rw rb 12%positive)))) TK OV Q220) by lia.
    unfold kchunks. reflexivity.
  - unfold fa_e, vFA, vSB, V_CLS. cbn [eval]. rewrite E155, E158, Q226. apply bv_eq.
    rewrite add_val, add_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + 3758096384)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition BASEO (W : list ulink) : list sobj := ltac2:(tb__ "0|0|
S13S1dSdS1dS80S13S1dS59VW;A1S55A3A3S85A3").
Definition BASEF (W : list ulink) (st : ustop) : list sprop := ltac2:(tb__ "0|0|
S13S1eS13S1eS58VW;Vst;A2S57S56A1A3S81A3").
Lemma arm_base_disj : ltac2:(tb__ "0|3|
S36S1aScS32Q40A1A1S51ScS53A1S54S1aS25ScS1dA1M0S1aS11ScS52A1S7eA2S7fR7R6A2S45RcRbRaR9R8R7R6A7S48RcR4A2S2bS87R5R7R4A4S1ScS11S11S1bS1bA2S1bA2M1A1M2S5aS1dG1S6cS24R8A1A4S5aS1dG1S6cS13S1dS6bRbA1R7A3A4A3S8fS1eS6aRcRbA2S23R9A1A3S3G0G0S3G0G0S0S1G0S24RcA1S13S1dR2R1A3A3S0S1G2S5aS1dG1S6cR1A4S5aS1dG1S6cRbA4A3S4S4S8bS37R15A1R2R1A3S5bS1dS1dS29S20ReR1A2SeS4S4R4R3A4A2Lo';R5A3F_;Fhi;Flo;A2A2Lox;A2Lob;A2F_;F_;F_;F_;F_;F_;Fw;Fr;Fextra;FS;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho S extra r w HW HE HFz Hsm HSK HXF.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as (_ & _ & R151 & R152 & _).
  destruct HE as (_ & HA & _ & _ & _ & _ & Htop & _).
  pose proof HA as (HG & _ & _ & _ & _ & HI3 & _). pose proof (proj1 HI3) as HS3.
  destruct HFz as [Fw _].
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (BASEF W st) -> holds r p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp))).
  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact HSK)) as (ob & ox & EO & SKb & SKx).
  exists ob, ox. split; [exact EO|]. split; [exact SKx|].
  intros lo hi HI.
  apply (base_zone W (aa_geom A) r S w ob lo hi HG HS3 Hsm); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | | exact R151 | exact R152 | exact HI].
  - apply HFX. unfold BASEF. apply in_or_app; left. apply in_or_app; right. cbn; tauto.
  - apply Forall_forall. intros p Hp. apply HFX. unfold BASEF. apply in_or_app; left. apply in_or_app; left.
    destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp).
  - unfold top_high in Htop. rewrite <- (Fw 10%positive) by lia. rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia). exact Htop.
Qed.

Lemma arm_extra_ranges : ltac2:(tb__ "0|4|
S36S1aS1aS68R3R2A2S69R4R3R2A3S49R5R4R3A3S38S37R6A1A1S4S74S39S37R7A1A1S6dS34Q40M0S1cR6PcA2A2A1A2S4S0S1S4S34G0S28R6S84A2A2S46R8R7A2M1A3S0S1S11S4S4A2M2S20R6S82A2SeS4S4G1S6G1Z4A2M3A4A3S0S1G2S20R6S83A2SeS4S4S6R2Zad0A2S6R2Zc60A2A4A3S0S1G2S20R6S64A2SeS4S4G3S6G1Z8A2A4A3S1G2S20R6S65A2SeS4S4R1S6R1Z80A2A4A3A2A2A2A2Tri;TT;F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH T ri. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _). fold T in T1, T2.
  destruct RG as (_ & _ & E151 & _ & _ & _ & _ & E158). fold T in E151. destruct GH as (_ & _ & _ & _ & _ & Q225 & _). fold ri in Q225.
  assert (EB : bv_unsigned (eval r pc_base) = PCE A rb).
  { unfold pc_base, vT, V_CLS, PCE. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. fold T. lia. }
  split; [exact EB|].
  split; [unfold O_pcc0; rewrite obj_range_mk by lia; rewrite EB; f_equal; lia|].
  split; [unfold O_st, vT; rewrite obj_range_mk by lia; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity|].
  split; [unfold O_pcm; rewrite obj_range_mk by lia; rewrite EB; reflexivity|].
  unfold O_ri, vRI. rewrite obj_range_mk by lia. cbn [eval]. rewrite Q225, u64_lit by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia). f_equal; lia.
Qed.

Lemma entry_pc_cells : ltac2:(tb__ "0|2|
S36S1aScS32Q40M0A1A1S51ScS53A1S54S1aS45R7R6R5R4R3R2R1A7S1SfS3bR8A1S10A3S7dS86S2aR8A1A2S7bS6dS34G0S1cR9PcA2A2A1S4S0S79R2S7aS6S46RbRaA2M1Z4A2U4S72R1A1A3A2S0S79R2S7aS6G1Z8A2U8S71R1A1A3A2S7cR2G1S6G1Z50A2A3A2A2Tc;Tm0;F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE Hini m0 c.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold c in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _).
  destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 0x1000 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & D3 & _).
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold c; lia).
  split; [|split].
  - intros j Hj. specialize (D2 j Hj). cbn [c_addr c_w RtCells.c_val] in D2, Hj |- *. rewrite MT in D2 by lia. rewrite PCr. exact D2.
  - intros j Hj. specialize (D3 j Hj). cbn [c_addr c_w RtCells.c_val] in D3, Hj |- *. rewrite MT in D3 by lia. rewrite PCr. exact D3.
  - intros z Hz. rewrite PCr in Hz. destruct (PE z ltac:(lia)) as [b Hb]. exists b. rewrite <- MT by lia. exact Hb.
Qed.

Lemma zone_thread_gen : ltac2:(tb__ "0|7|
S36S1aS47S4S68R4R3A2S7Z0M0S4aR3A1A2S0S5G0S4cR6R5A2M1A2S0S5S9Z4M2S6G1S4bR6R5A2M3A2A2Z20000000A2S5S4aR4A1G3A2A2A2F_;S0S5S6S38S37R6A1A1M4Z120A2R3A2S7R3S6G4Zc60A2A2A2S50R7R6R5R4A4S2S0S5S6S46R8R7A2M5Z10A2M6R5A2S7R5S6G6S9G2S4fR6A1A2A2A2A2S0S1SfS4eR6A1S10A3S0S5G5R5A2S7R5S6G5G2A2A2A2A2A2F_;F_;F_;F_;Fz;Fph;Frb;FA;").
Proof.
  intros A rb ph z CF HFL Hz HZ. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rb 12%positive)))))) as NF0.
  unfold zoneR in HZ.
  unfold U0, F0, FAb, free_array, region_beg, region_info, kRegionInfoStride, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ.
  rewrite kSpaceSize_val in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[X|[_ X]]]]]]]]; [exfalso | exfalso | exfalso | exfalso | exfalso | left; exact X | right; exact X | exfalso].
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFL X2) as (F1 & F2 & F3). clear -X Hz F1 F2 F3 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Section STEPS.
Let segs : list Segment := segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Notation JRp := (JR A Kc rb tp0 md0).

Lemma jr_run : ltac2:(tb__ "0|1|
S19ScS4A1S30ScS2dA1M0S47S1aScS32Q40A1A1S70S1S15G0A1S2fVsegs;R8R7R6S10A5S14G0R5A2A3S1SfS21S2cR7A1A1S16A3S1SfS75S5eS1fS2cR8A1A1A2S10A3S2dS1aS8eS2dR2RaA3S27S1fS2cRcA1A1R9R2A3VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;RbA6S2eR4A1R3R9A5R8A2F_;F_;Frho';FL;VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves ph rho tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JRp ph) rho tp Q (JR_K A Kc rb tp0 md0 ph)); [|exact Hrun | exact Hl | exact HL].
  apply JR_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Lemma jr_restate : ltac2:(tb__ "0|3|
S30S25ScS11S1bS1bA2A1M0ScS1eA1M1S47S1aScS32Q40A1A1S70S1SfS26R7A1S10A3S1S15S11G0G1A2M2A1S78S2cR9A1R8A2S14G2SeG0G1R7R6A4A2A3S1SfS76S1fR9A1S1fS2cRaA1A1A2S10A3ScS52A1S51S44VA;VKc;Vrb;Vtp0;Vmd0;R9R8R7R2R1AaS5bS1eS22R9A1S23S2cReA1A1A3S0S77RaRdA2S5bS1eS22RaA1RcA3A2F_;F_;Fmd;Ftr;VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;R8A6S31RcRbA2R7R6A5R5A2VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;R9A6RdR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fnf;Fd;FS';FE;").
Proof.
  intros E S' d nf ph rho tp Q Hwf Hsd Hnx Hsem HT.
  apply (tr_pre Kc TR KIT _ _ Q) with (2 := HT). intros w Hw.
  pose proof (SPA_facts_hold segs _ rho E tp w Hw) as HF.
  destruct (Hsem _ _ (proj2 Hw) HF) as [Hd Hn].
  apply (SPA_restate segs _ rho E S' tp w d nf Hwf Hsd); [apply Pos.eqb_eq; exact Hnx | exact Hd | exact Hn | exact Hw].
Qed.

Section PREFIX.
Variable F : nat.
Variables (E3 : axst) (L1 LP LJ : leafA).
Let CR1 : axst := ltac2:(tb__ "0|0|
S66S67VE3;A1S2eVL1;A1A2").
Hypothesis R_1 : ltac2:(tb__ "0|1|
S1S15ScS2dA1M0A1S2fVsegs;VF;SdS4Z4147cS12S4A1A3S5cVE3;A1S10A5S14G0SdS2dVL1;S12S2dA1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S1SfS21S2cS5cVE3;A1A1A1S16A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S1SfS75S5eS1fS2cS5cVE3;A1A1A1A2S10A3").
Hypothesis W_r1 : ltac2:(tb__ "0|0|
S1SfS26S2cVCR1;A1A1S10A3").
Hypothesis D_r1 : ltac2:(tb__ "0|4|
S1S15S11ScS11S1bS1bA2M0A1M1ScS1eA1M2A2M3A1S78S2cS2eVL1;A1A1S2cVCR1;A1A2S14G3SeG1G2SdG0SeS1bS1bS60S63A4SdG0SeS1bS1bS5dS62A4SdG0SeS1bS1bS5fS61A4S12G0A1A3A3A3S12S1eA1A4A2A3").
Hypothesis NX_r1 : ltac2:(tb__ "0|0|
S1SfS76S1fS2cVCR1;A1A1S1fS2cS2eVL1;A1A1A1A2S10A3").
Hypothesis R_2 : ltac2:(tb__ "0|1|
S1S15ScS2dA1M0A1S2fVsegs;VF;SdS4Z41704SdS4Z41560S12S4A1A3A3VCR1;S10A5S14G0SdS2dVLP;SdS2dVLJ;S12S2dA1A3A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S1SfS21S2cVCR1;A1A1S16A3").
Hypothesis NX_1 : ltac2:(tb__ "0|0|
S1SfS75S5eS1fS2cVCR1;A1A1A2S10A3").

Lemma refill_prefix : ltac2:(tb__ "0|1|
ScS53A1S54S1aS1aScS32Q40A1A1S70S45VA;Vrb;Vtp0;Vmd0;R6R5R4A7S1aVTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;S4dA6M0S2eVLP;A1R1R4A5R3A2Fr';S1aVTR;S35Vsegs;G0S2eVLJ;A1R1R5A5R4A2Fr';VTR;S35Vsegs;G0S5cVE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;Fst;FW;").
Proof.
  intros W st rho r tp Q HE HP HJ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run F [0x4147c] (cR0 E3) [L1] ph0 r tp Q R_1 LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jr_restate (la_state L1) (ax_S CR1) _ _ ph0 r1 tp Q W_r1 D_r1 NX_r1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    exact (r1_diffs A rb r1 CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh). }
  change (ax_setS (la_state L1) (ax_S CR1)) with CR1.
  apply (jr_run F [0x41704; 0x41560] CR1 [LP; LJ] ph0 r1 tp Q R_2 LN_1 NX_1).
  intros L r2 [<-|[<-|[]]] _; [apply HP | apply HJ].
Qed.
End PREFIX.
End STEPS.
End SpineCallocR2.

