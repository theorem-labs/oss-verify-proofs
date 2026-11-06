(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxArrA.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.

(* [comment removed for export] *)
Module Start4Fail.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "true"; "Some"; "bool"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "sym_runA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Start4FailCut"; "E_spin"; "C2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start4FailStates"; "PC_SPIN"; "F0"; "FUEL1"; "PC_OUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "E_k8x"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start4FailStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Start4FailCut.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma spin_ok : ltac2:(tb__ "0|1|
SdS6S2SaA1M0A1ScS8U2S0S7S12S1S7A1A3SeS3A5S4G0S0SaSbSeS1dA2S1SaA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_s8f : ltac2:(tb__ "0|1|
SdS5S1eS8S14S0S7S15S0S7S12S1S7A1A3A3P1fS0S9S13S0S9SfS1S9A1M0A3A3S0S9SeG0A3A6S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section S8F.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S20S16S2S17Q40A1A1S2S11A1M0S10R5R4R3R2R1A4SdG0R3S1S11A1A3F_;Fmd;Ftr;Ftp;Frho;S21S8Vok;R2A3F_;FJ;").

Theorem s8_fail_safe : ltac2:(tb__ "0|0|
S10S7S16S2S17Q40A1A1S1bS1cS8Vok;S1fS8S18R5R4A2S1aS19A1R3R2A5R1A4FQ;Ftp;Frho;FB;Fm;").
Proof.
  intros m B rho tp Q.
  assert (OKJ : ok_frameA segsA ok (KxA m B)) by (apply OKF; intros; eapply KxA_nil; eassumption).
  change (fail_state E_k8x) with F0.
  apply (cfg_soundA segsA FUEL1 [PC_OUT; PC_SPIN] 31 [F0; C2] [E_spin] (KxA m B) ok Q tp OKJ (stableA_KxA segsA 31 m B) check_s8f).
  - intros E rho' [<-|[]]. apply (triple_spinA ok (KxA m B) E_spin rho' tp); [exact OKJ | apply stableA_KxA | reflexivity | exact spin_ok].
  - left. reflexivity.
Qed.
End S8F.
End Start4Fail.

(* [comment removed for export] *)
Module StartGlueC.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "cell"; "sobj"; "sv"; "valuation"; "mkObj"; "obj_holds"; "odefault"; "ss_objs"; "DImage"; "ob_dflt"; "rom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "cell_eqb"; "shadow_ok"; "@Stdlib.Lists.List"; "In"; "nth_error"; "existsb"; "forallb"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nat"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "obj_to_unknown"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC"; "cells_incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "xshadow_outside"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma obj_holds_img_to_unknown : ltac2:(tb__ "0|0|
S3S25S1SaSbR2A2ScS6S9R2A1S8A3S5SbR5R4R3A4S5SbR6R5S20R4A1A4F_;F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hrom Hd (Hb & Hw & Hc & Hdf & Hi). unfold obj_to_unknown. rewrite Hd in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [exact Hc|]. split; [|exact I].
  cbn [ob_dflt ob_cells ob_lo ob_base]. intros off Hoff Hnc. cbn.
  destruct (Hdf off Hoff Hnc) as [Hnone [b Hb']]. exists b.
  unfold rd, ms_read_byte. rewrite Hnone. rewrite (Hrom _). exact Hb'.
Qed.

Lemma SPA_img_to_unknown : ltac2:(tb__ "0|1|
S1eS3SeS19S1S16S24Q40A1A1S22ScS1bS1A1S13S1S7SdR5A1A1R4A3S1aS1R3A2A3ScS6S9R4A1S8A3ScS17S23SdR7A1M0S1fG0R6S20R5A1A3A2S18A3S1dSbRaR8R9R5R4A6S1dSbRbSfR9S1fSdR9A1R8S20R7A1A3A2RaR6R5A6F_;F_;F_;F_;Fw;Ftp;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o tp w Hn Hd Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms Hrom Ho. apply obj_holds_img_to_unknown; assumption.
Qed.

Lemma obj_holds_cells_equiv : ltac2:(tb__ "0|2|
S3S25S2S2S2S16S0A1M0G0S6S0S12S0R1R3A3S12S0R2R5A3M1F_;Fc;S0S12S0R1R5A3G1F_;Fc;S5SbRaR9S4R8R7R6R5R3A5A4S5SbRbRaS4R9R8R7R5R4A5A4F_;F_;F_;Fd;Fcs';Fcs;Fhi;Flo;Fb;Fms;Frho;").
Proof.
  intros rho ms b lo hi cs cs' d H1 H2 (Hb & Hw & Hc & Hdf & Hi). cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split.
  - apply Forall_forall. intros c Hc'. exact (proj1 (Forall_forall _ _) Hc c (H1 c Hc')).
  - split; [|exact Hi]. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. intros off Hoff Hnc. apply Hdf; [exact Hoff|].
    intros Hcov. apply Hnc. unfold SymState.covered in *. apply Exists_exists in Hcov as (c & Hcin & Hin).
    apply Exists_exists. exists c. split; [apply H2; exact Hcin | exact Hin].
Qed.

Lemma SPA_cells_equiv : ltac2:(tb__ "0|3|
S1eS3SeS19S2S2S2S16S0A1M0G0S6S16S24Q40A1A1S22ScS1bS1A1S13S1S7SdRaA1A1R9A3S1aS1S4R8R7R6R5R3A5A2A3S0S12S0R1R6A3S12S0R2R8A3M1F_;Fc;S0S12S0R1R8A3G1F_;Fc;ScS17S23SdRdA1M2S1fG2RcS4RbRaR9R7R6A5A3A2S18A3S1dSbR10ReRfR6R5A6S1dSbR11SfRfS1fSdRfA1ReS4RdRcRbR9R8A5A3A2R10R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fd;Fcs';Fcs;Fhi;Flo;Fb;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i b lo hi cs cs' d tp w Hn H1 H2 Hsame Hsp.
  apply (SPA_replace_obj J rho A i (mkObj b lo hi cs d)); try assumption.
  - reflexivity.
  - intros ms _ Ho. apply (obj_holds_cells_equiv rho ms b lo hi cs cs' d H1 H2 Ho).
Qed.

Definition cells_incl (cs cs' : list cell) : bool := ltac2:(tb__ "0|0|
S15S0S0S14S0S10R1A1Vcs';A3Lc;Vcs;A3").
Lemma cell_eqb_eq : ltac2:(tb__ "0|0|
S0S0ScS17S10R2R1A2S18A3ScS0R3R2A3F_;Fc';Fc;").
Proof.
  intros [o k v] [o' k' v'] H. unfold cell_eqb in H. cbn in H. apply andb_prop in H as [H Hv]. apply andb_prop in H as [Ho Hk].
  apply sv_eqb_sound in Ho. apply sv_eqb_sound in Hv. apply Z.eqb_eq in Hk. subst. reflexivity.
Qed.
Lemma cells_incl_sound : ltac2:(tb__ "0|1|
S16S0A1M0G0ScS17S27R2R1A2S18A3S0S12S0R1R4A3S12S0R2R4A3F_;Fc;F_;Fcs';Fcs;").
Proof.
  intros cs cs' H c Hc. unfold cells_incl in H. pose proof (proj1 (forallb_forall _ _) H c Hc) as X.
  apply existsb_exists in X as (c' & Hc' & E). apply cell_eqb_eq in E. subst. exact Hc'.
Qed.

Lemma xshadow_outside_incl : ltac2:(tb__ "0|0|
S3SeS16S1A1S1S12S1R1R2A3S12S1R2S7SdR4A1A1A3F_;Fo;S11R4R3A2S28R5R4R3A3F_;F_;Fobjs';FA;Frho;").
Proof.
  intros rho A objs' Hincl Hsh. unfold xshadow_outside, shadow_ok in *. apply Forall_forall. intros [b l] Hr a j Ha Hj.
  pose proof (proj1 (Forall_forall _ _) Hsh _ Hr) as X. unfold xr_ok in X. cbn [fst snd] in X, Ha |- *.
  destruct X as (_ & _ & X). destruct (X a Ha) as (_ & _ & Hwd & _). destruct (Hwd j Hj) as [Hout _].
  unfold outside_all in *. apply Forall_forall. intros o Ho. exact (proj1 (Forall_forall _ _) Hout o (Hincl o Ho)).
Qed.

Lemma SPA_move_lastX : ltac2:(tb__ "0|1|
S1eS3SeS19S16S24Q40A1A1S22S26R3S1cS1S7SdR4A1A1A2A2ScS17S23SdR5A1M0S21G0R4A2A2S18A3S1dSbR8R6R7R4R3A6S1dSbR9SfR7S21SdR7A1R6A2A2R8R5R4A6F_;F_;F_;Fw;Ftp;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i tp w Hi Hsame Hsp.
  destruct (firstn_skipn_split (ss_objs (ax_S A)) i Hi) as (x & H1 & H2).
  apply (SPA_reobj segsA J rho A (move_obj_last (ax_S A) i) tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segsA _ _ _ _ _ S0) as MM.
    unfold move_obj_last. cbn [ss_objs set_objs]. rewrite H1. rewrite H2 in MM.
    apply mem_match_move_last. exact MM.
  - destruct Hsp as [(_ & _ & _ & Hsh & _) _]. apply xshadow_outside_incl; [|exact Hsh].
    intros o Ho. unfold move_obj_last in Ho. cbn [ss_objs set_objs] in Ho.
    rewrite !in_app_iff in Ho. destruct Ho as [Ho|[Ho|Ho]]; [eapply In_firstn_In; exact Ho | eapply In_skipn_In; exact Ho | eapply In_skipn_In; eapply In_firstn_In; exact Ho].
Qed.

Lemma SPA_exJ : forall {T : Type} (P : T -> Prop) (K : T -> jpredA) A rho tp w,
  SPA segsA (fun r t tr md => exists x, P x /\ K x r t tr md) A rho tp w <-> exists x, P x /\ SPA segsA (K x) A rho tp w.
Proof.
  intros T P K A rho tp w. split.
  - intros [Hsm (x & Hx & HK)]. exists x. split; [exact Hx|]. split; assumption.
  - intros (x & Hx & [Hsm HK]). split; [exact Hsm|]. exists x. split; assumption.
Qed.
End StartGlueC.

(* [comment removed for export] *)
Module Lib_fuzz_iface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SPUle"; "sobj"; "SVar"; "DUnknown"; "SAlu"; "cell"; "mkObj"; "valuation"; "FcsrFrm0"; "SPAlign"; "SPBranch"; "mkSS"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nil"; "list"; "app"; "nat"; "None"; "false"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "vDAT"; "vLEN"; "vDp"; "P0_fz"; "spm"; "vTOPfz"; "O_F_fz"; "O_W_fz"; "O_pay"; "Pre_fz"; "X_fz"; "fz_facts"; "nd_fz0"; "PD_fz"; "P_fz"; "X_lits"; "bd_fz"; "nd_fz1"; "two40"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "ANone"; "JA_pre"; "NDA"; "JLA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "BI"; "BXok_d"; "KU"; "bxt"; "uval"; "ASv"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "add"; "div"; "le"; "lt"; "mul"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "D_FZ"; "fz_frame"; "FZ_DEPTH"; "fz_entry"; "fz_ret"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.Stmt"; "Posts_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "aceil"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "CK0"; "CK_DIV"; "CV"; "CV0"; "MAX_INPUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module FZAddr.
  Definition fz_entry : Z := 0x9db38.
  Definition fz_ret : Z := 0x9dfd8.
  Definition fz_frame : Z := 384.

  Definition FZ_DEPTH : Z := 32768.

  Definition D_FZ : Z := 33152.
End FZAddr.
Import FZAddr.

Definition two47 : Z := 2 ^ 47. Definition two40 : Z := 2 ^ 40.
Definition spm (k : Z) : sv := ltac2:(tb__ "0|0|
S7S4dS5PaA1S1S46Vk;A1A1A3").
Definition vDAT : sv := SVar 12. Definition vLEN : sv := SVar 13. Definition vDp : sv := SVar 19.

Definition O_F_fz : sobj := ltac2:(tb__ "0|0|
S9S5PaA1S1S46S50A1A1S1Z0A1S12S8A1S6A5").
Definition O_W_fz : sobj := ltac2:(tb__ "0|0|
S9S23S50A1S21S1Z0A1S12S8A1S6A5").
Definition O_pay : sobj := ltac2:(tb__ "0|0|
S9S1fS1Z0A1S20S12S8A1S6A5").

Definition vTOPfz : sv := SVar 30.
Definition fz_facts : list sprop := ltac2:(tb__ "0|7|
SfS2ScPaM0Z4M1A2SfS2S3S5G0A1M2S1S4cS32Ze0A2A1A2SfS2S3S1S5cA1M3S7S4dS23S50A1M4S21A3M5A2SfS2S3G3G4A2SfS2S3G3G2A2SfS2S3S24G5A2SfS2S3G3S24A2SfS2S3S24S1Z7fffff800000A1M6A2SfS2SdS4eS1S46S51A1A1S21A3SfS2SdS4eS21S1S46S31A1A1A3SfS2ScPcG1A2SfS2S3S1Z1000A1S1fA2SfS2S3S7S4dS1fS20A3G6A2SfS2S3S1fG6A2SfS2S3S20S1S66A1A2SfS2S3S5P1cA1G2A2SfS2S3S1S47S5cS4fA2A1G2A2S12S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_lits : list (sv * sv) := ltac2:(tb__ "0|5|
SfS11S0S0A2M0S10S0S0S1Z22ba0A1S1ZcA1M1A4SfG0S10S0S0S1Z22bc0A1S1Z2A1M2A4SfG0S10S0S0S1Z22be0A1S1Z3A1M3A4SfG0S10S0S0S1Z22c00A1G3A4SfG0S10S0S0S1Z22c20A1G2A4SfG0S10S0S0S1Z22c40A1G2A4SfG0S10S0S0S1Z22c60A1G2A4SfG0S10S0S0S1Z22c80A1G2A4SfG0S10S0S0S1Z22ca0A1G2A4SfG0S10S0S0S1Z22cc0A1S1Z7A1M4A4SfG0S10S0S0S1Z22ce0A1G4A4SfG0S10S0S0S1Z22d00A1G3A4SfG0S10S0S0S1Z22d20A1G2A4SfG0S10S0S0S1Z22d40A1S1Z4A1A4SfG0S10S0S0S1Z22d60A1S1Z2eA1A4SfG0S10S0S0S1Z22dc0A1S1Z2cA1A4SfG0S10S0S0S1Z22e20A1G1A4SfG0S10S0S0S1Z239a0A1S1Zb8A1A4S12G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Fixpoint in_litsL (l : list (sv * sv)) (a : Z) : Prop :=
  match l with
  | [] => False
  | (SLit b, SLit n) :: r => (b <= a < b + n) \/ in_litsL r a
  | _ :: r => in_litsL r a
  end.
Definition in_lits (a : Z) : Prop := in_litsL X_lits a.

Definition X_fz : list (sv * sv) := ltac2:(tb__ "0|1|
S14S11S0S0A2M0SfG0S10S0S0S1fS20A4SfG0S10S0S0S23S4fA1S1S4fA1A4S12G0A1A3A3S2eA3").
Definition Pre_fz : axst := ltac2:(tb__ "0|0|
S1eSeS52S3cS3aSbS16S0A1S14S4SfS4S25SfS4S26SfS4S27S12S4A1A3A3A3S1dA3S2aS39S17A9S29A2").
Definition P_fz : axst := ltac2:(tb__ "0|1|
S1eSeS53S3dS3bS39A1SfS11S15S0A2M0S10S15S0UaS1Z0A1A4S12G0A1A3A2S3aSbS16S0A1S14S4SfS4S25SfS4S26SfS4S27S12S4A1A3A3A3S1dA3S2aS67S17A9S29A2").

Definition bd_fz : list bitem := ltac2:(tb__ "0|5|
SfS3eS40Z1M0Z0M1SfS11S1aS3fA2M2S10S1aS3fS64S45S20A1M3A4S12G2A1M4A3S65A4SfS3eS40G1G0SfG2S10S1aS3fS48S42S63A2G3A4G4A3S4bS42S62A2A4S12S3eA1A3A3").
Definition nd_fz0 : ndesc := ltac2:(tb__ "0|0|
S37S12S11S0S0A2A1S12S11S11S0S1aA2S0A2A1S2fS35A4").
Definition nd_fz1 : ndesc := ltac2:(tb__ "0|0|
S37S12S11S0S0A2A1S12S11S11S0S1aA2S0A2A1S12S3eA1S35A4").

Definition PD_fz : list (axst * ndesc) := ltac2:(tb__ "0|1|
SfS11S1bS33A2M0S10S1bS33S2dS30A4S12G0A1A3").

Definition P0_fz (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S55S1aS55S49S44Vr;S1fA2M0R1A2S4aR1S47G0S44Vr;S20A2A2A2A2S60VCST;Vr;VFB;VFF;R2A5F_;Fa;S1aS56S15S61R1S57S11S11S1aS1aA2M1S1aA2G1S18G1S1aA2VFF;A4A2U0A3Fc;A2").

Section Stmt.
Variable AInv : ltac2:(tb__ "0|0|
S68SaS13S54Q40A1A1S5dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable Kc : KcA.

Definition Posts_fz (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (BX : bxt) : list (axst * jpostA) := ltac2:(tb__ "0|1|
S57S11S1bS33A2M0S11S1bS5bA2G0S10S1bS5bS18S1bS33R1A3S38VAInv;VCST;VXGL;VKc;S22VCST;VFB;VFF;A3VFB;VFF;VBX;S34S19S1bS33R1A3AaA4Ld;S2cA4").

Definition fuzz_one_sumT (ok : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S13S11S1aS1aA2M0A1S13S11G0S1aA2A1S43SaS13S54Q40A1A1S41Z8R3A2S5fS1cVok;S59S1cS36VAInv;VCST;VXGL;VKc;S22VCST;R6R5A3R6R5R4S34S2bAaS28R3R2A5S5aS1cS39R3R2S58R6R5R4A3A5A4F_;Ftp0;Frho0;FBX;FFF;FFB;").
Definition fuzz_one_sumE : Prop := ltac2:(tb__ "0|1|
S13S11S1aS1aA2M0A1S13S11G0S1aA2A1S43SaS13S54Q40A1A1S41Z8R3A2S5eS1cS59S1cS36VAInv;VCST;VXGL;VKc;S22VCST;R6R5A3R6R5R4S34S2bAaS28R3R2A5S5aS1cS39R3R2S58R6R5R4A3A5A3F_;Ftp0;Frho0;FBX;FFF;FFB;").
End Stmt.

Goal swf (ax_S Pre_fz) = true /\ axwf Pre_fz = true /\ swf (ax_S P_fz) = true /\ axwf P_fz = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_fuzz_iface.

(* [comment removed for export] *)
Module Lib_vec_reserveN.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "None"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "sobj"; "SAlu"; "SMd"; "DUnknown"; "mkObj"; "SPAlign"; "FcsrFrm0"; "SVar"; "mkSS"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "tv_factsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "kbytes"; "nd0"; "vK"; "vDt"; "c8"; "vW"; "vDn"; "vKn"; "vE"; "vN"; "vAl"; "vV"; "z0"; "vDp"; "X_vr"; "bdP"; "ndG"; "vC"; "vr_facts"; "B32"; "canon_objs"; "kn15"; "ndN"; "pC"; "spm"; "tv0"; "O_Fv"; "O_W"; "O_alv"; "O_data"; "O_vec"; "Pre_vr"; "T_c8okA"; "T_cW0okA"; "X15"; "pR"; "two47"; "B_EW"; "C_c15"; "C_cW1"; "C_r8"; "C_rW0"; "E_c8"; "E_cW0"; "E_r15"; "E_rW1"; "FUEL_vr"; "KLG"; "N15"; "N8"; "NW0"; "NW1"; "PHI"; "P_fail"; "P_fail_S"; "P_grown"; "P_grown_S"; "P_keep"; "P_keep_S"; "Pre_c"; "Pre_vr_S"; "T_c8n"; "T_c8ok"; "T_c8ok0"; "T_cW0n"; "T_cW0ok"; "T_cW0ok0"; "T_r15f"; "T_r15ok"; "T_r15ok0"; "T_rW1f"; "T_rW1ok"; "T_rW1ok0"; "X8"; "XW0"; "XW1"; "cutpcs_vr"; "grown_facts"; "inj"; "tvP"; "two48"; "vUD"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "drop_obj_at"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "batom"; "bitem"; "ASv"; "BI"; "ALog"; "KU"; "ZK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.VRNAddr"; "vr_ret"; "calloc_pc"; "vr_entry"; "vr_nc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.RA"; "ndR"; "P_fail"; "P_ok"; "Pre_ra"; "tv0"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"; "AE_A"; "Pre_calloc"; "UStopLe"; "ulink"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.RA.ReallocAddr"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "opp"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRNAddr.
  Definition vr_entry : Z := 0x9311c.
  Definition vr_nc : Z := 0x9318c.
  Definition vr_ret : Z := 0x931e4.
  Definition vr_realloc_ret : Z := 0x9321c.
  Definition vr_calloc_ret : Z := 0x932f8.
  Definition calloc_pc : Z := 0x5e064.
End VRNAddr.
Import VRNAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.

Definition FUEL_vr : nat := 400%nat.
Definition two48 : Z := 2 ^ 48.
Definition B_EW : Z := 2863311530.
Definition B32 : Z := 4294967295.

Definition vV : sv := SVar 12. Definition vW : sv := SVar 13. Definition vAl : sv := SVar 14.
Definition vDt : sv := SVar 15. Definition vC : sv := SVar 16. Definition vK : sv := SVar 17. Definition vE : sv := SVar 18.
Definition vDp : sv := SVar 19.
Definition vN : sv := SVar 59.
Definition kbytes (k : sv) : sv := SMd M_MUL vE k.

Definition O_Fv (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11S14PaA1SaN40A1SaZ0A1Vcells;S10A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S11S39Z40A1S2eSaZ0A1S2ScA1S10A5").
Definition O_vec (d c k e : sv) : sobj := ltac2:(tb__ "0|1|
S11S2cSaZ0M0A1SaZ20A1S0ScS25G0Vd;A2S0ScS25Z8Vc;A2S0ScS25Z10Vk;A2S0ScS25Z18Ve;A2S2ScA1A3A3A3A3S10A5").
Definition O_alv : sobj := ltac2:(tb__ "0|2|
S11S2bSaZ0M0A1M1SaZ30A1S0ScS25G0SaSa0A1A2S0ScS25Z8SaSa1A1A2S0ScS25Z10G1A2S0ScS25Z18SaSa2A1A2S0ScS25Z20G1A2S0ScS25Z28S72A2S2ScA1A3A3A3A3A3A3S10A5").
Definition O_data (d bytes : sv) : sobj := ltac2:(tb__ "0|0|
S11Vd;SaZ0A1Vbytes;S2ScA1S10A5").

Definition vr_facts : list sprop := ltac2:(tb__ "0|e|
S0S9S12PaM0Z4M1A2S0S9SbS14G0A1M2SaS45A1M3A2S0S9SbS14P1eA1M4SeS73S39Z40A1M5S2eA3A2S0S9SbG4S39Za0A1A2S0S9SbG4G5A2S0S9SbG4G2A2S0S9S16S75SaN1060A1S2eA3S0S9S16S75S2eSaSa8Sa9Z2Z27A2A1A1A3S0S9S12PcZ3M6A2S0S9SbSaZ1000A1M7S2cA2S0S9SbSeS73S2cSaZ20A1A3G4A2S0S9SbS2cG3A2S0S9S12PeG6A2S0S9SbG7S2bA2S0S9SbSeS73S2bSaZ30A1A3G4A2S0S9SbS2bG3A2S0S9S12PfG1A2S0S9SbS24G4A2S0S9SbSeS73S24S21S23A1M8A3G4A2S0S9SbS24G3A2S0S9SbSaZ1A1S29A2S0S9SbS29G7A2S0S9SbS26SaS71A1A2S0S9SbS32S23A2S0S9SbS23SaS34A1M9A2S0S9SbS21S26A1MaSaS46A1MbA2S0S9SbG8G9A2S0S9SbS26S2aA2S0S9SbGaS21S2aA1McA2S0S9SbGcGbA2S0S9SbSaZ7fff7f800000A1MdG4A2S0S9SbG4SaZ7fffff800000A1A2S0S9SbGdG2A2S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_vr (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S2cSaZ20A1A4S0G0S1S8S8S2bSaZ30A1A4S0G0S1S8S8Vd;S21Vk;A1A4S2G0A1A3A3A3").
Definition Pre_vr_S : sstate := ltac2:(tb__ "0|0|
S15S8fS8cS89S13S5S8A1S6SdS0SdS3bS2ScA1A1S0SdS3cS0SdS3fS24S32S23S29A4S0SdS3dS0SdS3eS24S21S23A1A2S2SdA1A3A3A3A3A3S86A3S33S88S7A9").
Definition Pre_vr : axst := ltac2:(tb__ "0|0|
S85S5dS2fS24S23A2A2").

Definition cutpcs_vr : list Z := ltac2:(tb__ "0|0|
S0S1fS90S0S1fS9fS0S1fS8eS2S1fA1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_vr end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S9eS18Vk;S87S4fS6dVS;Vpc;A4S40A4").

Definition X15 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 0.
Definition XW1 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 1.
Definition XW0 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 2.
Definition X8 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 3.

Definition kn15 : sv := ltac2:(tb__ "0|0|
SeS73SeS76S23SaZ1A1A3S23A3").
Definition inj (kn : sv) : list sprop := ltac2:(tb__ "0|3|
S0S9SbSfS74SaZ4A1M0S21S23A1A3SfS74SaZ3A1S21Vkn;A1M1A3A2S0S9SbSfS74G0G1A3SeS73SfS74SaZ6A1S21S26A1A3SfS74SaZ20A1S29A3A3A2S0S9SbG1SaS34A1M2A2S0S9SbSaZ1A1G1A2S0S9SbVkn;G2A2S2S9A1A3A3A3A3A3").
Definition N15 : axst := ltac2:(tb__ "0|0|
Sa3S6fS36A1S43A2").
Definition NW1 : axst := ax_add_facts (inj vW) XW1.
Definition NW0 : axst := ax_add_facts (inj vW) XW0.
Definition N8 : axst := ax_add_facts (inj (SLit 8)) X8.

Definition E_r15 : axst := Eval vm_compute in leafA_at N15 ra_entry 0.
Definition E_rW1 : axst := Eval vm_compute in leafA_at NW1 ra_entry 0.
Definition C_c15 : axst := Eval vm_compute in leafA_at N15 calloc_pc 0.
Definition C_cW1 : axst := Eval vm_compute in leafA_at NW1 calloc_pc 0.
Definition E_cW0 : axst := Eval vm_compute in leafA_at NW0 calloc_pc 0.
Definition E_c8 : axst := Eval vm_compute in leafA_at N8 calloc_pc 0.
Definition C_rW0 : axst := Eval vm_compute in leafA_at NW0 ra_entry 0.
Definition C_r8 : axst := Eval vm_compute in leafA_at N8 ra_entry 0.

Definition tvf0 : list sprop := ltac2:(tb__ "0|0|
S1eS1S8S8S24S21S23A1A4A1").

Definition xf_rcall : list axform := ltac2:(tb__ "0|2|
S0S78S7dU1M0SaN60M1A1A2S0S78S79G0G1A2S2S78A1A3A3").
Definition E_r15x : axst := Eval vm_compute in optA (apply_axforms E_r15 xf_rcall).
Definition E_rW1x : axst := Eval vm_compute in optA (apply_axforms E_rW1 xf_rcall).
Definition E_r15f : axst := ax_add_facts tvf0 E_r15x.
Definition E_rW1f : axst := ax_add_facts tvf0 E_rW1x.
Definition s_r (E : axst) : wsub := ltac2:(tb__ "0|0|
S0S3S20S8A2S1S20S8P13SeS73S2eSaZ60A1A3A4S97PaS19VE;A1S19S94A1A3A3").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_r15 : list sobj := Eval vm_compute in optR (entails_frA E_r15f RA.Pre_ra (s_r E_r15f)).
Definition R_rW1 : list sobj := Eval vm_compute in optR (entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f)).
Goal entails_frA E_r15f RA.Pre_ra (s_r E_r15f) = Some R_r15 /\ call_checkPA E_r15f RA.Pre_ra (s_r E_r15f) R_r15 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f) = Some R_rW1 /\ call_checkPA E_rW1f RA.Pre_ra (s_r E_rW1f) R_rW1 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_cW0' : axst := E_cW0.
Definition E_c8' : axst := E_c8.
Definition Pre_c : axst := ltac2:(tb__ "0|0|
S9aS99S2S9cA1S9bA3").
Definition s_c (E : axst) : wsub := ltac2:(tb__ "0|0|
S97PaS19VE;A1S19S5cA1A3").
Definition R_cW0 : list sobj := Eval vm_compute in optR (entails_frA E_cW0' Pre_c (s_c E_cW0')).
Definition R_c8 : list sobj := Eval vm_compute in optR (entails_frA E_c8' Pre_c (s_c E_c8')).
Goal entails_frA E_cW0' Pre_c (s_c E_cW0') = Some R_cW0 /\ call_checkPA E_cW0' Pre_c (s_c E_cW0') R_cW0 [L_calloc_null AE_A [] UStopLe; L_calloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_c8' Pre_c (s_c E_c8') = Some R_c8 /\ call_checkPA E_c8' Pre_c (s_c E_c8') R_c8 [L_calloc_null AE_A [] UStopLe; L_calloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition PD_ra : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S3S18S1cA2M0S1S18S1cS92S91S95S2S7fA1M1A2A4S0G0S1S18S1cS93S91S96G1A2A4S2G0A1A3A3").
Definition Xk_r : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S2cSaZ20A1A4S0G0S1S8S8S2bSaZ30A1A4S2G0A1A3A3").
Definition T_r15f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_fail Xk_r.
Definition T_r15ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_ok Xk_r.
Definition T_rW1f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_fail Xk_r.
Definition T_rW1ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_ok Xk_r.
Definition T_cW0n0 : axst := Eval vm_compute in T_afterA Pre_c E_cW0' (s_c E_cW0') R_cW0 (L_calloc_null AE_A [] UStopLe).
Definition T_cW0ok0 : axst := Eval vm_compute in T_afterA Pre_c E_cW0' (s_c E_cW0') R_cW0 (L_calloc_ok AE_A [] UStopLe).
Definition T_c8n0 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_null AE_A [] UStopLe).
Definition T_c8ok0 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_ok AE_A [] UStopLe).

Definition T_cW0n : axst := T_cW0n0.
Definition T_c8n : axst := T_c8n0.
Definition pC (T : axst) : sv := reg_sv (ax_S T) 10.
Definition reshape_blk (T : axst) (kn : sv) : axst := ltac2:(tb__ "0|3|
Sa4S1aVT;Sa5S19VT;A1U1S11S38VT;A1M0SaZ0A1S21Vkn;A1M1S2ScA1S10A5A3A2S6S3S8S8A2M2S9dG2U3S1bVT;A1A3S0G2S1S8S8G0G1A4S2G2A1A3A3A2").
Definition T_cW0okA : axst := reshape_blk T_cW0ok0 vW.
Definition T_c8okA : axst := reshape_blk T_c8ok0 (SLit 8).
Definition T_cW0ok2 : axst := ltac2:(tb__ "0|0|
S1aS42S7aS19S42A1U7A2A2").
Definition T_c8ok2 : axst := ltac2:(tb__ "0|0|
S1aS41S7aS19S41A1U7A2A2").
Definition T_cW0ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_cW0ok0, kbytes vW)) T_cW0ok2.
Definition T_c8ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_c8ok0, kbytes (SLit 8))) T_c8ok2.

Definition xf_rback : list axform := ltac2:(tb__ "0|2|
S0S78S79U1M0Z60A2S0S78S7cS0S4G0S0S4U0M1S0S4U2S0S4U3S0S4U4S0S4U5S0S4U6S0S4U7S2S4A1A3A3A3A3A3A3A3A3A1S0S78S7bG1A1S2S78A1A3A3A3").
Definition T_r15f : axst := Eval vm_compute in optA (apply_axforms T_r15f0 xf_rback).
Definition T_rW1f : axst := Eval vm_compute in optA (apply_axforms T_rW1f0 xf_rback).
Definition T_r15okB : axst := Eval vm_compute in optA (apply_axforms T_r15ok0 xf_rback).
Definition T_rW1okB : axst := Eval vm_compute in optA (apply_axforms T_rW1ok0 xf_rback).
Definition pR (T : axst) : sv := reg_sv (ax_S T) 10.
Definition T_r15ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_r15ok0, kbytes kn15)) T_r15okB.
Definition T_rW1ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_rW1ok0, kbytes vW)) T_rW1okB.

Definition canon_objs (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S6SdS0SdS3bS2ScA1A1S0SdS3cS0SdS3fVd;S32Vk;S29A4S0SdS3dS0SdS3eVd;S21Vk;A1A2S2SdA1A3A3A3A3A3S86A3").
Definition P_keep_S : sstate := ltac2:(tb__ "0|1|
S15S8dS8bS8aS88A1S0S3S4S8A2M0S1S4S8UaSaZ1A1A4S2G0A1A3A2S89S13S5S8A1S35S24S23A2S0S9SbS26S23A2S33A3S98S7A9").
Definition P_keep : axst := ltac2:(tb__ "0|0|
S85S5bS2fS24S23A2A2").
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S15S8dS8bS8aS88A1S0S3S4S8A2M0S1S4S8UaSaZ0A1A4S2G0A1A3A2S89S13S5S8A1S35S24S23A2S33S98S7A9").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S85S57S2fS24S23A2A2").
Definition vDn : sv := SVar 140. Definition vKn : sv := SVar 141.
Definition grown_facts : list sprop := ltac2:(tb__ "0|7|
S0S9SbS26S28A2S0S9S12P8cZ4M0A2S0S9S17S16S77S27SaZ0A1A3A1S0S9SbSaZ1000A1S27A2S0S9SbS27S14P1eA1M1A2S0S9SbSeS73S27S21S28A1M2A3G1A2S0S9SbS27SaS45A1A2S0S9SbSaSa6A1S27A2S0S9SbSfS74SaG0A1G2A3M3SeS73SfS74SaZ6A1M4S21S26A1A3SfS74SaZ20A1S29A3M5A3A2S0S9SbG3SeS73SfS74G4S21S2aA1A3G5A3A2S0S9SbG2SaS34A1M6A2S0S9SbSaZ1A1G2A2S0S9SbS32S28A2S0S9SbS28G6A2S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition P_grown_S : sstate := ltac2:(tb__ "0|1|
S15S8dS8bS8aS88A1S0S3S4S8A2M0S1S4S8UaSaZ1A1A4S2G0A1A3A2S89S13S5S8A1S35S27S28A2S6S9S6eS33A3P8eS7A9").
Definition P_grown : axst := ltac2:(tb__ "0|0|
S85S59S2fS27S28A2A2").

Definition PHI (w k : sv) : bitem := ltac2:(tb__ "0|2|
S81Z1Z0M0S0S3S1fS7eA2M1S1S1fS7eZ6S80S21Vw;A1A1A4S0G1S1S1fS7eN4S80S21Vk;A1A1A4S0G1S1S1fS7eZ20S80S29A1A4S2G1A1A3A3A3G0A4").
Definition KLG (k : sv) : bitem := ltac2:(tb__ "0|1|
S81Z0Sa7Z2S83A2S0S3S1fS7eA2M0S1S1fS7eN1S82Vk;A1A4S2G0A1A3S84A4").
Definition bdP (w k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S7fS55Vw;Vk;A2S0S7fS50Vk;A1S2S7fA1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S24S21S23A1A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S27S21S28A1A4S2G0A1A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS3aS2S3S3S8S1fA2S8A2A1S30S2aS23A2A3").
Definition ndN (kn : sv) : ndesc := ltac2:(tb__ "0|0|
S1dS3aS2S3S3S8S1fA2S8A2A1S30S2aVkn;A2A3").
Definition ndG (p kn : sv) : ndesc := ltac2:(tb__ "0|1|
S1dS0S3S8S8A2M0S1S8S8Vp;S21Vkn;A1A4S2G0A1A3S2S3S3S8S1fA2S8A2A1S30S2aVkn;A2A3").

Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S18S1cA2M0S3S1fS8A2M1A2M2S1G0G1S1S18S1cS40S22A4S1S1fS8Z64S2dA4A4S0G2S1G0G1S1S18S1cS51S22A4S1S1fS8Z50S2dA4M3A4S0G2S1G0G1S1S18S1cS54S22A4G3A4S0G2S1G0G1S1S18S1cS53S22A4G3A4S0G2S1G0G1S1S18S1cS52S22A4G3A4S0G2S1G0G1S1S18S1cS64S37S36A1A4S1S1fS8Z3cS2dA4M4A4S0G2S1G0G1S1S18S1cS65S31S44S66A1S36A2A4G4A4S0G2S1G0G1S1S18S1cS67S37S26A1M5A4G4A4S0G2S1G0G1S1S18S1cS68S31S44S69A1S26A2A4G4A4S0G2S1G0G1S1S18S1cS61G5A4G4A4S0G2S1G0G1S1S18S1cS62S31S38S63A1S26A2A4G4A4S0G2S1G0G1S1S18S1cS5eS37SaZ8A1M6A1A4G4A4S0G2S1G0G1S1S18S1cS5fS31S38S60A1G6A2A4G4A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S18S1cA2M0S3S1fS8A2M1A2M2S1G0G1S1S18S1cS43S22A4S1S1fS8Z5aS2dA4M3A4S0G2S1G0G1S1S18S1cS6cS22A4G3A4S0G2S1G0G1S1S18S1cS6bS22A4G3A4S0G2S1G0G1S1S18S1cS6aS22A4G3A4S0G2S1G0G1S1S18S1cS4dS22A4S1S1fS8Z46S2dA4M4A4S0G2S1G0G1S1S18S1cS4eS22A4G4A4S0G2S1G0G1S1S18S1cS47S22A4G4A4S0G2S1G0G1S1S18S1cS48S22A4G4A4S0G2S1G0G1S1S18S1cS4cS22A4G4A4S0G2S1G0G1S1S18S1cS4bS22A4G4A4S0G2S1G0G1S1S18S1cS4aS22A4G4A4S0G2S1G0G1S1S18S1cS49S22A4G4A4S0G2S1G0G1S1S18S1cS5aS22A4S1S1fS8Z0S2dA4M5A4S0G2S1G0G1S1S18S1cS56S1dS3aS2S3S3S8S1fA2S8A2A1M6S2S7fA1A3A4G5A4S0G2S1G0G1S1S18S1cS58S1dS70G6S30S2aS28A2A3A4G5A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_vec_reserveN.

(* [comment removed for export] *)
Module Lib_realloc_darr.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "list"; "prod"; "nat"; "app"; "false"; "None"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SPUle"; "cell"; "SVar"; "SAlu"; "mkObj"; "SPBranch"; "FcsrFrm0"; "SPAlign"; "mkSS"; "DUnknown"; "ss_regs"; "mkCell"; "ob_base"; "ob_hi"; "ob_lo"; "ss_next"; "tfact"; "DArr"; "SMd"; "SPNot"; "TF2le"; "ob_dflt"; "rw"; "ss_facts"; "ss_fregs"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_realloc_darr"; "kb16"; "vK"; "VQ"; "vKn"; "vQ"; "vP"; "vPn"; "ndR"; "z0"; "c8"; "vA"; "vD"; "X_cp0"; "darr"; "pN"; "eoff"; "tv0"; "O_D"; "O_F"; "O_al"; "bd1"; "ra_facts"; "two47"; "vF0"; "vF1"; "B32"; "E_m"; "FUEL_ra"; "O_old"; "Pre_ra"; "X_step"; "bd0"; "cutpcs_ra"; "pls"; "spm"; "tmpl"; "tv1"; "C_0"; "D_1"; "D_10"; "D_11"; "D_12"; "D_13"; "D_14"; "D_15"; "D_2"; "D_3"; "D_4"; "D_5"; "D_6"; "D_7"; "D_8"; "D_9"; "E_free"; "E_freeT"; "O_new"; "P_fail"; "P_ok"; "P_ok_S"; "Pre_f"; "Pre_m"; "T_free"; "T_mnull"; "T_mok"; "X_cp0f"; "X_f"; "cp_regs"; "cutsE"; "exitsE"; "flds"; "ok_facts"; "pre_regs_ra"; "q_facts"; "src_cells"; "tv2"; "tvP"; "two40"; "vL"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ejcertA"; "tv_factsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "ALU_SUB"; "BC_GE"; "BC_EQ"; "M_MUL"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "BIs"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Init.Logic"; "ex"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "leavesA_at"; "mkA"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "opp"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_realloc_darr.ReallocAddr"; "ra_L"; "ra_ret"; "free_pc"; "malloc_pc"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "tmpl_inst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV CellTile ArrMat.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA CfgGenTA SummaryA3 TobjJA TobjJAM AxXform AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
Module ReallocAddr. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc.ReallocAddr. End ReallocAddr.
Import ReallocAddr.

Definition FUEL_ra : nat := 400%nat.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition B32 : Z := 4294967295.

Definition vA : sv := SVar 12. Definition vP : sv := SVar 13. Definition vK : sv := SVar 14. Definition vKn : sv := SVar 33.
Definition vD : sv := SVar 19. Definition vUD : sv := SVar 52. Definition vL : sv := SVar 53.
Definition spm (k : Z) : sv := ltac2:(tb__ "0|0|
S12S80S11PaA1SeS99Vk;A1A1A3").
Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition flds : list (Z * Z) := ltac2:(tb__ "0|2|
S0S4S29S29A2M0S1S29S29Z0Z8M1A4S0G0S1S29S29G1G1A4S2G0A1A3A3").
Definition tmpl : list tfact := ltac2:(tb__ "0|0|
S0S1fS23S7U0U1S78A4S2S1fA1A3").
Definition darr (c : sv) : odefault := ltac2:(tb__ "0|0|
S20Z10Vc;S70S4eA4").

Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S11PaA1SeN60A1SeZ0A1Vcells;S18A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S13S4dZ60A1S36SeZ0A1S2S10A1S18A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S13S35SeZ0M0A1M1SeZ30A1S0S10S34G0SeSa0A1A2S0S10S34Z8SeSa1A1A2S0S10S34Z10G1A2S0S10S34Z18SeSa2A1A2S0S10S34Z20G1A2S0S10S34Z28S79A2S2S10A1A3A3A3A3A3A3S18A5").
Definition O_old : sobj := ltac2:(tb__ "0|0|
S13S30SeZ0A1S2bS2cA1S2S10A1S38S2cA1A5").

Definition ra_facts : list sprop := ltac2:(tb__ "0|9|
S0SdS16PaM0Z4M1A2S0SdSfS11G0A1M2SeS41A1M3A2S0SdSfS11P1eA1M4S12S80S4dZ60A1M5S36A3A2S0SdSfG4G5A2S0SdSfG4G2A2S0SdS14S83SeN1000A1S36A3S0SdS14S83S36SeS99S77A1A1A3S0SdS16PcZ3A2S0SdSfSeZ1000A1M6S35A2S0SdSfS12S80S35SeZ30A1A3G4A2S0SdSfS35G3A2S0SdS16PdG1A2S0SdSfG6S30A2S0SdSfS12S80S30S2bS2cA1A3G4A2S0SdSfS30G3A2S0SdSfSeZ1A1S2cA2S0SdS14S81S2cS2eA3S0SdSfS2bS2eA1SeS44A1M7A2S0SdSfS2eG7A2S0SdSfSeZ7fff7f800000A1M8G4A2S0SdSfG4SeZ7fffff800000A1A2S0SdSfG8G2A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_ra : list sv := ltac2:(tb__ "0|1|
S8dS8fS0S4S5SbA2M0S1S5SbUcS2bS2cA1A4S0G0S1S5SbUdS2bS2eA1A4S0G0S1S5SbUeSeZ10A1A4S2G0A1A3A3A3A2").
Definition X_ra : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS35SeZ30A1A4S0G0S1SbSbS30S2bS2cA1A4S2G0A1A3A3").
Definition Pre_ra_S : sstate := ltac2:(tb__ "0|0|
S17S9fS72S8cS15S8SbA1S6ScS0ScS3dS2S10A1A1S0ScS3cS0ScS3eS0ScS47S2ScA1A3A3A3A3S93A3S40S8bS7A9").
Definition Pre_ra : axst := mkA Pre_ra_S X_ra.

Definition cutpcs_ra : list Z := ltac2:(tb__ "0|0|
S0S29S9bS0S29S9eS0S29S9dS2S29A1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_ra end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_ra_S end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S86S7aVk;S94S46S4bVS;Vpc;A4S48A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_m : axst := Eval vm_compute in leafA_at Pre_ra malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S4S2aSbA2S1S2aSbPfS36A4Sa3PaS7bS45A1S7bS67A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := pos_add_nat (ss_next (ax_S E_m)) 10.
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := ltac2:(tb__ "0|0|
S7fS1SbSbS11S39A1S2bS2eA1A4A1").
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition X_cp0 : axst := Eval vm_compute in leafA_at T_mok ra_L 0.

Definition vQ : sv := SVar 172.  Definition vF0 : sv := SVar 173.  Definition vF1 : sv := SVar 174.
Definition eoff (j : Z) : sv := ltac2:(tb__ "0|0|
S12S80S2bS2fA1SeVj;A1A3").
Definition pls (b : sv) (o : sv) : sv := SAlu ALU_ADD b o.
Definition cp_regs : list sv := ltac2:(tb__ "0|15|
S3SbA1M0G0Lx;S19S7bS37A1A1S2SbA1M1SbG0G0G0Ll;R1S0SbR2G1A3M2SbG0G0G0Ll0;R1S0SbR4G2A3M3SbG0G0G0Ll1;R1S0SbR6G3A3M4SbG0G0G0Ll2;R1S0SbR8G4A3M5SbG0G0G0Ll3;R1S0SbRaG5A3M6SbG0G0G0Ll4;R1S0SbRcG6A3M7SbG0G0G0Ll5;R1S0SbReG7A3M8SbG0G0G0Ll6;R1S0SbR10G8A3M9SbG0G0G0Ll7;R1S0SbR12G9A3MaSbG0G0G0Ll8;R1S0SbR14GaA3MbSbG0G0G0Ll9;R1S0SbR16GbA3McSbG0G0G0Ll10;R1S0SbR18GcA3MdSbG0G0G0Ll11;R1S0SbR1aGdA3MeSbG0G0G0Ll12;R1S0SbR1cGeA3MfSbG0G0G0Ll13;R1S0SbR1eGfA3M10SbG0G0G0Ll14;R1S0SbR20G10A3M11SbG0G0G0Ll15;R1S0SbR22G11A3SbG0S0SbR24S0SbR22S0SbR20S0SbR1eS0SbR1cS0SbS4cS11S39A1S2bS2fA1M12A2M13S0SbS11PafA1S0SbS11Pb0A1S0SbR14S0SbR12S0SbR10S0SbReS0SbRcS0SbRaS0SbS4cS30G12A2M14S0SbG13S0SbS12S82S2bS2cA1G12A3S0SbG14R1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Lrest;Lr17;X3x2Ll15;Lr16;X3x2Ll14;Lr15;X3x2Ll13;Lr14;X3x2Ll12;Lr13;X3x2Ll11;Lr12;X3x2Ll10;Lr11;X3x2Ll9;Lr10;X3x2Ll8;Lr9;X3x2Ll7;Lr8;X3x2Ll6;Lr7;X3x2Ll5;Lr6;X3x2Ll4;Lr5;X3x2Ll3;Lr4;X3x2Ll2;Lr3;X3x2Ll1;Lr2;X3x2Ll0;Lr1;X3x2Ll;Lr0;X3x2").
Definition src_cells : list cell := ltac2:(tb__ "0|1|
S0S10S1aS2bS2fA1Z8M0S42A3S0S10S1aS3aG0A1G0S43A3S2S10A1A3A3").
Definition q_facts : list sprop := ltac2:(tb__ "0|1|
S6SdS0SdS14S81S2fS2cA3S0SdSfS3aZ10A1M0S2bS2cA1A2S0SdSfG0S2bS2eA1A2S0SdSfS2fSeS44A1A2S2SdA1A3A3A3A3Sa5S0SbS42S0SbS43S2SbA1A3A3S4eA2A3").
Definition C_0c : axst := ltac2:(tb__ "0|9|
S7cS37S17S9bS6dS27S7bS37A1M0A1S15S8SbA1S3ScA1M1G1Lx;S28G0A1S2ScA1M2ScG1G1G1Ll;R1S0ScR2G2A3M3ScG1G1G1Ll0;R1S0ScR4G3A3M4ScG1G1G1Ll1;R1S0ScR6G4A3M5ScG1G1G1Ll2;R1S0ScR8G5A3M6ScG1G1G1Ll3;R1S0ScRaG6A3M7ScG1G1G1Ll4;R1S0ScRcG7A3ScG1G1G1Ll5;R1S0ScReS0ScS13S11S39A1SeZ0A1M8S2bS2eA1S2S10A1S38S2fA1A5S0ScRaS0ScR8S0ScR6S0ScR4S0ScS13S30G8S2bS2cA1S74S38S2cA1A5G2A3A3A3A3A3A3A3ScG1S0ScR10S0ScReS0ScRcS0ScRaS0ScR8S0ScR6S0ScR4S0ScR2R1A3A3A3A3A3A3A3A3Ll6;Ls;X3x2Ll5;Lo6;X3x2Ll4;Lo5;X3x2Ll3;Lo4;X3x2Ll2;Lo3;X3x2Ll1;Lo2;X3x2Ll0;Lo1;X3x2Ll;Lo0;X3x2S6SdS73S26G0A1A3Pb1S7A9A2").
Definition C_0 : axst := Eval vm_compute in C_0c.

Definition stepD (S : axst) : axst := leafA_at S ra_L 0.
Definition D_1 : axst := Eval vm_compute in stepD C_0.
Definition D_2 : axst := Eval vm_compute in stepD D_1.
Definition D_3 : axst := Eval vm_compute in stepD D_2.
Definition D_4 : axst := Eval vm_compute in stepD D_3.
Definition D_5 : axst := Eval vm_compute in stepD D_4.
Definition D_6 : axst := Eval vm_compute in stepD D_5.
Definition D_7 : axst := Eval vm_compute in stepD D_6.
Definition D_8 : axst := Eval vm_compute in stepD D_7.
Definition D_9 : axst := Eval vm_compute in stepD D_8.
Definition D_10 : axst := Eval vm_compute in stepD D_9.
Definition D_11 : axst := Eval vm_compute in stepD D_10.
Definition D_12 : axst := Eval vm_compute in stepD D_11.
Definition D_13 : axst := Eval vm_compute in stepD D_12.
Definition D_14 : axst := Eval vm_compute in stepD D_13.
Definition D_15 : axst := Eval vm_compute in stepD D_14.

Definition X_step : axst := Eval vm_compute in stepD D_15.
Definition E_free : axst := Eval vm_compute in leafA_at D_15 free_pc 0.

Definition tiles2_l : list (nat * sv * Z * sv) := ltac2:(tb__ "0|5|
S0S4S4S4S5SbA2M0S29A2M1SbA2M2S1G1SbS1G0S29S1S5SbU1M3S2bS2fA1A4Z8M4A4S42A4S0G2S1G1SbS1G0S29S1S5SbG3S3aG4A1A4G4A4S43A4S2G2A1A3A3").

Definition step_facts : list sprop := ltac2:(tb__ "0|1|
S0SdS14S81S12S80S2fSeZ1A1A3S2cA3S0SdSfS3aZ20A1M0S2bS2cA1A2S0SdSfG0S2bS2eA1A2S2SdA1A3A3A3").
Definition X_t : axst := Eval vm_compute in ax_setS X_step (optS (tiles_at (ax_S X_step) tiles2_l)).
Definition X_f : axst := ax_add_facts step_facts X_t.
Definition X_m : axst := Eval vm_compute in ax_setS X_f (optS (arr_mat_at (ax_S X_f) 6 (eoff 16) 8)).
Definition s_step : wsub := ltac2:(tb__ "0|4|
S0S4S2aSbA2M0S1S2aSbPacS12S80S2fSeZ1A1A3A4S0G0S1S2aSbPadS11S1eS7bS6cA1A1M1A1A4S0G0S1S2aSbPaeS11Sa4G1A1A1A4S0G0S1S2aSbPafS86SbU6S19S7bS49A1A1M2SeZ0A1M3A4A4S0G0S1S2aSbPb0S86SbU7G2G3A4A4S2G0A1A3A3A3A3A3").

Definition cp0_facts : list sprop := ltac2:(tb__ "0|1|
S0SdS14S81SeZ0A1S2cA3S0SdSfSeZ10A1M0S2bS2cA1A2S0SdSfG0S2bS2eA1A2S2SdA1A3A3A3").
Definition X_cp0f : axst := ax_add_facts cp0_facts X_cp0.
Definition X_cp0m : axst := Eval vm_compute in ax_setS X_cp0f (optS (arr_mat_at (ax_S X_cp0f) 6 (SLit 0) 8)).
Definition s_cp0 : wsub := ltac2:(tb__ "0|4|
S0S4S2aSbA2M0S1S2aSbPacSeZ0A1M1A4S0G0S1S2aSbPadS11S1eS7bS6bA1A1M2A1A4S0G0S1S2aSbPaeS11Sa4G2A1A1A4S0G0S1S2aSbPafS86SbU6S19S7bS37A1A1M3G1A4A4S0G0S1S2aSbPb0S86SbU7G3G1A4A4S2G0A1A3A3A3A3A3").

Definition free_facts : list sprop := ltac2:(tb__ "0|0|
S0SdSfS2cS12S80S2fSeZ1A1A3A2S2SdA1A3").
Definition E_ft : axst := Eval vm_compute in ax_setS E_free (optS (tiles_at (ax_S E_free) tiles2_l)).
Definition E_ff : axst := ax_add_facts free_facts E_ft.
Definition trim_objs (os : list sobj) : list sobj := ltac2:(tb__ "0|2|
S3ScA1M0G0Los;Vos;Vos;ScG0G0G0Ll;R1Vos;ScG0G0G0Ll0;R1Vos;ScG0G0G0Ll1;R1Vos;ScG0G0G0Ll2;R1Vos;ScG0G0G0Ll3;R1Vos;ScG0G0G0Ll4;R1Vos;ScG0G0G0Ll5;R1S0ScReS0ScS13S1bRcA1S1dRcA1S1cRcA1S2S10A1M1S38S2cA1A5S0ScRaS0ScR8S0ScR6S0ScR4S0ScS13S1bR2A1S1dR2A1S1cR2A1G1S24R2A1A5S2ScA1A3A3A3A3A3A3A3ScG0Vos;Ll6;Ls;X3x2Ll5;Lo6;X3x2Ll4;Lo5;X3x2Ll3;Lo4;X3x2Ll2;Lo3;X3x2Ll1;Lo2;X3x2Ll0;Lo1;X3x2Ll;Lo0;X3x2").
Definition E_freeT : axst :=
  Eval vm_compute in mkAX (set_objs (ax_S E_ff) (trim_objs (ss_objs (ax_S E_ff)))) [(vA, SLit 48); (SVar pN, kb16 vKn)] shb.

Definition Pre_f : axst := Pre_free AE_A [] UStopLe.
Definition s_f : wsub := ltac2:(tb__ "0|1|
S0S4S2aSbA2M0S1S2aSbPfS36A4S0G0S1S2aSbPdS2bS2cA1A4Sa3PaS7bS61A1S7bS66A1A3A3A3").
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA E_freeT Pre_f s_f).
Definition T_free : axst := Eval vm_compute in T_afterA Pre_f E_freeT s_f R_f (L_free AE_A [] UStopLe).

Definition vPn : sv := SVar 140.
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S17S9cS8dS8eS8bA1S0S4S5SbA2M0S1S5SbUaSeZ0A1A4S2G0A1A3A2S8cS15S8SbA1S6ScS0ScS3dS2S10A1A1S0ScS3cS0ScS3eS0ScS47S2ScA1A3A3A3A3S93A3S40Sa7S7A9").
Definition P_fail : axst := mkA P_fail_S X_ra.
Definition ok_facts : list sprop := ltac2:(tb__ "0|0|
S0SdS16P8cZ4A2S0SdS22S14S84S31SeZ0A1A3A1S0SdSfSeZ1000A1S31A2S0SdSfS12S80S31S2bS2eA1A3S11P1eA1A2S0SdSfS31SeS41A1A2S0SdSfSeSa6A1S31A2S2SdA1A3A3A3A3A3A3").
Definition O_new : sobj := ltac2:(tb__ "0|0|
S13S31SeZ0A1S2bS2eA1S2S10A1S38S2cA1A5").
Definition P_ok_S : sstate := ltac2:(tb__ "0|1|
S17S9cS8dS8eS8bA1S0S4S5SbA2M0S1S5SbUaS31A4S2G0A1A3A2S8cS15S8SbA1S6ScS0ScS3dS2S10A1A1S0ScS3cS0ScS3eS0ScS62S2ScA1A3A3A3A3S93A3S6SdS71S40A3P8dS7A9").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S95S65S0S4SbSbA2M0S1SbSbS35SeZ30A1A4S0G0S1SbSbS31S2bS2eA1A4S2G0A1A3A3A2").

Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS30S2bS2cA1A4S2G0A1A3").
Definition tv1 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS11S39A1S2bS2eA1A4S0G0S1SbSbS30S2bS2cA1A4S2G0A1A3A3").
Definition tv2 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS11S39A1S2bS2eA1A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS31S2bS2eA1A4S2G0A1A3").
Definition bd0 : list bitem := ltac2:(tb__ "0|2|
S0S87S89Z1M0Z0M1S2bS2eA1A3S0S87S88G1S9aZ2S8aA2G0A3S2S87A1A3A3").
Definition bd1 : list bitem := [BIc 0 KU 1].
Definition ndR (tv : list (sv * sv)) (bd : list bitem) : ndesc := ND tv [] bd.

Definition z0 : sv := SLit 0.

Definition VQ (c : Z) : sv := ltac2:(tb__ "0|0|
S12S82S21S85SeZ20A1S12S82S12S80SeS97S41Z1A2A1S2cA3S2fA3A3SeVc;A1A3").
Definition cutsE : list edescA := ltac2:(tb__ "0|6|
S0S4S4S7aS7dA2M0S4S29SbA2M1A2M2S1G0G1S1S7aS7dS48S32S3bS4aA2A4S1S29SbZ64S33A4A4S0G2S1G0G1S1S7aS7dS69S32S3bS3fA2A4S1S29SbZ50S33A4M3A4S0G2S1G0G1S1S7aS7dS6aS32S4fS3fA2M4A4G3A4S0G2S1G0G1S1S7aS7dS50G4A4S1S29SbZ46M5S2dZ0A1A4A4S0G2S1G0G1S1S7aS7dS51G4A4S1S29SbG5S2dZ1A1A4A4S0G2S1G0G1S1S7aS7dS58G4A4S1S29SbG5S2dZ3A1A4A4S0G2S1G0G1S1S7aS7dS59G4A4S1S29SbG5S2dZ5A1A4A4S0G2S1G0G1S1S7aS7dS5aG4A4S1S29SbG5S2dZ7A1A4A4S0G2S1G0G1S1S7aS7dS5bG4A4S1S29SbG5S2dZ9A1A4A4S0G2S1G0G1S1S7aS7dS5cG4A4S1S29SbG5S2dZbA1A4A4S0G2S1G0G1S1S7aS7dS5dG4A4S1S29SbG5S2dZdA1A4A4S0G2S1G0G1S1S7aS7dS5eG4A4S1S29SbG5S2dZfA1A4A4S0G2S1G0G1S1S7aS7dS5fG4A4S1S29SbG5S2dZ11A1A4A4S0G2S1G0G1S1S7aS7dS52G4A4S1S29SbG5S2dZ13A1A4A4S0G2S1G0G1S1S7aS7dS53G4A4S1S29SbG5S2dZ15A1A4A4S0G2S1G0G1S1S7aS7dS54G4A4S1S29SbG5S2dZ17A1A4A4S0G2S1G0G1S1S7aS7dS55G4A4S1S29SbG5S2dZ19A1A4A4S0G2S1G0G1S1S7aS7dS56G4A4S1S29SbG5S2dZ1bA1A4A4S0G2S1G0G1S1S7aS7dS57G4A4S1S29SbG5S2dZ1dA1A4A4S0G2S1G0G1S1S7aS7dS68S32S75S2S87A1A2A4S1S29SbZ3cS33A4A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S0S4S4S7aS7dA2M0S4S29SbA2M1A2M2S1G0G1S1S7aS7dS45S32S3bS4aA2A4S1S29SbZ5aS33A4A4S0G2S1G0G1S1S7aS7dS37S32S4fS3fA2M3A4S1S29SbZ4bS33A4A4S0G2S1G0G1S1S7aS7dS49G3A4S1S29SbZ46S2dZ1fA1A4A4S0G2S1G0G1S1S7aS7dS60G3A4S1S29SbZ41S33A4A4S0G2S1G0G1S1S7aS7dS63S32S3bS2S87A1M4A2A4S1S29SbZ0S33A4M5A4S0G2S1G0G1S1S7aS7dS64S32S76G4A2A4G5A4S2G2A1A3A3A3A3A3A3").

Definition P0_ra (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S90S29S29S90S29S29S90S29S29S91Sa8S4S4S29S29A2M0S29A2S1G0S29S1S29S29R3R2A4R1A4VFF;A3S91S98R3Sa9Q40S25Vr;PcA2A2M1A2S98S97G1Z30A2S97R3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2").

Goal entailsA X_m C_0 s_step = true /\ entailsA X_cp0m C_0 s_cp0 = true /\ entailsA E_ff E_freeT [] = true
     /\ call_checkPA E_freeT Pre_f s_f R_f [L_free AE_A [] UStopLe] = true /\ length R_f = 3%nat
     /\ call_checkPA E_m Pre_m s_m R_m [L_malloc_null AE_A [] UStopLe; L_malloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S92S9S7eS96S8bS46S4bP64S6eS6fA7SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_realloc_darr.

(* [comment removed for export] *)
Module MuslMalloc40.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sv"; "ss_lenient"; "rw"; "sprop"; "sobj"; "SLit"; "agree_below"; "SAlu"; "SVar"; "rm"; "ss_facts"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "false"; "nil"; "cons"; "pair"; "option"; "app"; "Some"; "nat"; "snd"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "mkLeafA"; "sym_runA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.MuslMalloc40"; "VK"; "okT"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "event"; "vm_reserved"; "Model"; "vm_limit"; "vm_init_sp"; "region_free"; "alloc_top"; "m_vm_lazy"; "vm_brk"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States"; "N18"; "E22f"; "E22g"; "N22g"; "N22f"; "refuse"; "vBRK"; "vRES"; "E18"; "S18"; "S19f"; "S22f"; "S22g"; "U24c"; "cont"; "E18t"; "E19"; "E20f"; "E20g"; "E21f"; "RET0a"; "RET0b"; "RET0f"; "RET0g"; "RETPf"; "RETPg"; "S19g"; "S20f"; "S20g_ko"; "S20g_ok"; "S21f"; "U24"; "vGRPf"; "vGRPg"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes"; "brk0w"; "n8w"; "mf_exp"; "Fgrant"; "n3w"; "objs_clear_M"; "TOP"; "mf_res"; "mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post"; "Posts_M"; "post_sub"; "NA"; "out1_model"; "out1"; "KxM"; "NG"; "out1_ok"; "out1_tp"; "m40_B"; "m40_al"; "m40_band"; "m40_hi"; "m40_lim"; "m40_lo"; "m40_lz"; "m40_res"; "m40_sb"; "m40_top"; "rm_kept_outside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "etriple"; "assn"; "world"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.MuslMalloc40.Assembly"; "SP0"; "grow_out"; "Z8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "Pre_M"; "facts_M"; "D_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "init_sp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "mmap_obj"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "tp_in_maps"; "lazy_in_maps"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import
  Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA MmapA MmapFixedA MmapBrkA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code KxA Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Steps.
Variable ok : assn.

Lemma run1 : ltac2:(tb__ "0|1|
S2cS1fS14S13A1S26S26Sa0S5S14S21Q40A1A1S8dS0S1cS14S27A1M0A1S29S4R8R7R6S16A5S1eG0S1aS27S28R5R4A2S19S27A1A3A2A3S2dS4Vok;RaA3S12S2eS4R1RcA3Fn;S0S15S8S25R9A1A1S18A3S5SdS6S25RbA1A1R8R1A3S8bS4Vok;S2bS4RfRbR2R8A5R7A4F_;Frho';S8bS4Vok;S2bS4ReRbR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fr;FL;FS;Fcuts;Ffuel;FJ;").
Proof.
  intros J fuel cuts S L r rho tp Q Hrun Hok Hst Hlen H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_soundA; [exact Hrun | exact Hok | exact Hlen | apply Hst]|].
  apply triple_LQA_of_leaves. intros L' rho' [<-|[]] Hag. cbn [la_state]. apply H. exact Hag.
Qed.

Lemma erun1 : ltac2:(tb__ "0|1|
S2cS1fS14S13A1S26S26Sa0S5S14S21Q40A1A1S8eOF_;S0S1cS14S27A1M0A1S29S4R8R7R6S16A5S1eG0S1aS27S28R5R4A2S19S27A1A3A2A3S12S2eS4R1RbA3Fn;S0S15S8S25R8A1A1S18A3S5SdS6S25RaA1A1R7R1A3S8cS4S2bS4ReRaR2R7A5R6A3F_;Frho';S8cS4S2bS4RdRaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;Fr;FL;FS;Fcuts;Ffuel;FJ;").
Proof.
  intros J fuel cuts S L r rho tp Q Hrun Hst Hlen H.
  eapply etriple_seq; [eapply sym_run_etripleA; [exact Hlen | apply Hst | exact Hrun]|].
  apply etriple_LQA_of_leaves. intros L' rho' [<-|[]] Hag. cbn [la_state]. apply H. exact Hag.
Qed.

Lemma post_fin : ltac2:(tb__ "0|2|
S2cS26S6dS14S17S26S6dA2M0A1S5S14S21Q40A1A1M1S5G1S8fG0S1bS26S6dR7R6A4R5A3S14S39A1S3bRbR5R4R2R1A4RaR8R7R6R5R3R2A6F_;Fmd;Ftr;S97S24R6R4A3S8bS4Vok;S2bS4RbRaR5R4A5S6cS4S24R7R6R8A5A4F_;F_;F_;Ftp;Frho;Ftp0;Frho0;FPosts;FJL;FP;FJ;").
Proof.
  intros J P JL Posts rho0 tp0 rho tp Hin HJ Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. eapply LQPA_intro; [exact Hin | exact Hw | exact Hag |]. intros HJw. apply HJ. exact HJw.
Qed.

Lemma epost_fin : ltac2:(tb__ "0|2|
S2cS26S6dS14S17S26S6dA2M0A1S5S14S21Q40A1A1M1S5G1S8fG0S1bS26S6dR7R6A4R5A3S14S39A1S3bRbR5R4R2R1A4RaR8R7R6R5R3R2A6F_;Fmd;Ftr;S97S24R6R4A3S8cS4S2bS4RbRaR5R4A5S6cS4S24R7R6R8A5A3F_;F_;F_;Ftp;Frho;Ftp0;Frho0;FPosts;FJL;FP;FJ;").
Proof.
  intros J P JL Posts rho0 tp0 rho tp Hin HJ Hag w Hw. exists w. split; [apply wsteps_refl|].
  eapply LQPA_intro; [exact Hin | exact Hw | exact Hag |]. intros HJw. apply HJ. exact HJw.
Qed.
End Steps.

Definition VK (rho0 : valuation) (lo hi : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1S97S24Vrho0;Vrho;A3S8aVlo;Vhi;Vrho0;Vrho;A4A2").

Lemma VK_refl : ltac2:(tb__ "0|1|
S5S35R1Z0M0G0R1A4Frho;").
Proof. intros rho. split; [apply agree_vals_refl | intros x _; reflexivity]. Qed.

Lemma VK_agree : ltac2:(tb__ "0|0|
S5S13S13S5S5S12S66S24R1A2S35R7R6R5R4A4SdR3R5R4A3S35R9R8R7R5A4F_;F_;F_;Fn;Frho';Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho rho' n Hn [Hav Hrm] (A1 & A2 & A3). split.
  - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; apply A1; lia | exact A2].
  - intros x Hx. rewrite <- A3. apply Hrm. exact Hx.
Qed.

Lemma VK_set_rw : ltac2:(tb__ "0|0|
S5S13S13S5S12S21Q40A1S66S24R2A2S35R7R6R5R4A4S35R8R7R6S9fR5R4R3A3A4F_;F_;Fa;Fv;Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho v a Hv [Hav Hrm]. split.
  - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; rewrite rho_set_rw_other by lia; reflexivity | intros l; reflexivity].
  - intros x Hx. rewrite rho_set_rw_rm. apply Hrm. exact Hx.
Qed.

Lemma VK_sub : ltac2:(tb__ "0|0|
S5S13S13S5S69S0S15S68R1S24A2S16A3S35R6R5R4R3A4S35R7R6R5S6aR4R3A2A4F_;F_;Fs;Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho s Hs [Hav Hrm]. pose proof (rho_sub_agree s NF rho Hs) as (A1 & A2 & A3). split.
  - eapply agree_vals_trans; [exact Hav|]. split; [exact A1 | exact A2].
  - intros x Hx. cbn. apply Hrm. exact Hx.
Qed.

Lemma VK_widen : ltac2:(tb__ "0|0|
S5S13S13S13S13S5S13S1S30R6R1A2S31R1R5A2A2S1S30R5R2A2S31R2R4A2A2F_;Fz;S35R7R6R5R2A4S35R8R5R4R3A4F_;F_;Frho;Fhi';Flo';Fhi;Flo;Frho0;").
Proof. intros rho0 lo hi lo' hi' rho H [Hav Hrm]. split; [exact Hav|]. intros x Hx. apply Hrm. intros Hc. apply Hx. apply H. exact Hc. Qed.

Lemma VK_set_rm : ltac2:(tb__ "0|4|
S5S13S13S5S21Q40M0A1M1S1cS21Q8A1A1M2Fx;S35R5R4R3R2A4G1S3S1S30R6S22G0R1A2M3A2S31G3R5A2A2A1S0G2R4R2A1S10R5R2A2A3F_;Fx;S35R7R6R5Sa6R4R3A2A4F_;F_;Ff;Frho;Fhi;Flo;Frho0;").
Proof.
  intros rho0 lo hi rho f [Hav Hrm] Hf. split.
  - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; reflexivity | intros l; reflexivity].
  - intros x Hx. unfold set_rm. cbn. rewrite (Hf x Hx). apply Hrm. exact Hx.
Qed.

Lemma unmap_range_outside : ltac2:(tb__ "0|5|
S21Q40M0A1M1S1cS21Q8A1A1M2F_;G1G1G1S3S1S30S22G0R3A2M3S22G0R1A2M4A2S31G4S2fG3S22G0R2A2A2A2A2A1S0G2Sa5R5R4R3R2A4R5R2A1A3F_;Fx;Fn;Fa;Fmem;").
Proof.
  intros mem a n x Hx. rewrite unmap_range_at. destruct (in_range a n x) eqn:E; [|reflexivity].
  exfalso. apply Hx. apply in_range_spec. exact E.
Qed.

Lemma rw_sub_other : ltac2:(tb__ "0|0|
S5S69S12S0S15S68R2S65R1A1A2S16A3S0S21Q40A1S9S6aR4R3A2R2A2S9R4R2A2A3F_;Fv;Fs;Frho;").
Proof.
  intros rho s v Hs. pose proof (rho_sub_agree s (Pos.succ v) rho Hs) as (A1 & _ & _). symmetry. apply A1. lia.
Qed.

Lemma VK_sp : ltac2:(tb__ "0|2|
S5S13S13S5S13S35R5R4R3R2A4S30R2S22Q40M0S9R6PaM1A2A2A2S30R3S22G0S9R4G1A2A2A2F_;F_;FT;Frho;Fhi;Flo;Frho0;").
Proof. intros rho0 lo hi rho T [[Hav _] _] H. rewrite <- (Hav 10%positive) by (unfold NF; lia). exact H. Qed.

Ltac plia := unfold NF, N18, N22f, N22g, NA, NG, NP in *; lia.

Definition okT : assn := fun _ => True.
Lemma OKF_triv : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;S2dS4S36R2A3F_;FJ;").
Proof. intros J _ rho tp tr ms md msv' _ _ _ _ _. exact I. Qed.
Lemma OKP_triv : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;Sa1S4S36R2A3F_;FJ;").
Proof. intros J _ rho tp tr ms md x8 _ _ _. exact I. Qed.

Section Assembly.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;S2dS4Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S2cS5S14S21Q40A1A1S14S39A1M0S3bR5R4R3R2R1A4S0G0R3S19S39A1A3F_;Fmd;Ftr;Ftp;Frho;Sa1S4Vok;R2A3F_;FJ;").
Variables (m : Model) (B : Z).
Hypothesis HM : m40_hyps m B.

Let Hres : ltac2:(tb__ "0|1|
S0S14S17S21Q40A1M0G0A2A1S3aS37Vm;A1A1Sa4S4A1A3") := ltac2:(tb__ "0|0|
S87Vm;VB;VHM;A3"). Let Hsb : ltac2:(tb__ "0|1|
S0S21Q40A1S42S37Vm;A1M0A1S41G0A1A3") := ltac2:(tb__ "0|0|
S88Vm;VB;VHM;A3"). Let Hal : ltac2:(tb__ "0|0|
S0S13S32S22Q40S6eVm;A1A2Z1000A2Z0A3") := ltac2:(tb__ "0|0|
S81Vm;VB;VHM;A3"). Let Hlo : ltac2:(tb__ "0|0|
S30Z646000S22Q40S6eVm;A1A2A2") := ltac2:(tb__ "0|0|
S85Vm;VB;VHM;A3").
Let Hhi : ltac2:(tb__ "0|0|
S30S22Q40S6eVm;A1A2Z80646000A2") := ltac2:(tb__ "0|0|
S83Vm;VB;VHM;A3"). Let HB : ltac2:(tb__ "0|0|
S30S2fVB;Z3000A2S3cS37Vm;A1A1A2") := ltac2:(tb__ "0|0|
S80Vm;VB;VHM;A3"). Let Htop : ltac2:(tb__ "0|0|
S9dS37Vm;A1A1") := ltac2:(tb__ "0|0|
S89Vm;VB;VHM;A3"). Let Hband : ltac2:(tb__ "0|2|
S9bS1dS17S21Q40A1M0G0A2S3aS37Vm;A1M1A1S38G1A1A3S9aS99A3") := ltac2:(tb__ "0|0|
S82Vm;VB;VHM;A3").
Let Hlz : ltac2:(tb__ "0|3|
S17S21Q40M0A1M1G1A2M2S8fG2R1S40Vm;A1A3S31Z0S22G0S20G1G1R2A3A2A2F_;Fr;") := ltac2:(tb__ "0|0|
S86Vm;VB;VHM;A3"). Let Hlim : ltac2:(tb__ "0|0|
Sa3Vm;A1") := ltac2:(tb__ "0|0|
S84Vm;VB;VHM;A3").

Definition SP0 (rho0 : valuation) : Prop := ltac2:(tb__ "0|0|
S30S2fS74Vm;A1S95A2S22Q40S9Vrho0;PaA2A2A2").

Lemma OKFx' : ltac2:(tb__ "0|0|
S3bS13S2dS4Vok;S6bR2R1A2A3FBx;Fmx;").
Proof. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma STx : ltac2:(tb__ "0|0|
S3bS13S12S2eS4R1S6bR3R2A2A3Fn;FBx;Fmx;").
Proof. intros. apply stableA_KxA. Qed.

Let brk0 : Z := bv_unsigned (brk0w m).

Lemma mf_res_facts : ltac2:(tb__ "0|5|
S21Q40A1M0S1S0S14S17G0G0A2M1A1M2S3aS37S75Vm;R1A2A1M3A1S3aS37Vm;A1M4A1A3S1S0S13S3cG3A1S3cG4A1A3S1S0G2S38G3A1S1aG1S1bG0G0R1S6fA4S38G4A1A3A3S0G0S3dG3A1S3dG4A1A3A2A2A2Fa;").
Proof. intros a. rewrite mf_res_vmmaps. unfold mmap_none_vm. cbn. repeat split; reflexivity. Qed.

Lemma mf_exp_facts : ltac2:(tb__ "0|5|
S21Q40A1M0S1S0S14S17G0G0A2M1A1M2S3aS37S70Vm;R1A2A1M3A1S3aS37Vm;A1M4A1A3S1S0S13S3cG3A1S3cG4A1A3S1S0G2S38G3A1S1aG1S1bG0G0R1S6fA4S38G4A1A3A3S0G0S3dG3A1S3dG4A1A3A2A2A2Fa;").
Proof.
  intros a. unfold mf_exp, mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_limit vm_maps vm_init_sp].
  rewrite mf_res_vmmaps. unfold mmap_none_vm. cbn. repeat split; reflexivity.
Qed.

Lemma facts_M_in_E22f : ltac2:(tb__ "0|0|
SaS8fSaR1S94A3S8fSaR2S11S25S44A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma objs_clear_E22f : ltac2:(tb__ "0|2|
S0S15S73S1aS17S7S13A2M0S1bS7S13SeS98S4aScZ1000M1A1A3G1A4S19G0A1A3S25S44A1A2S16A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S22f_eq : ltac2:(tb__ "0|1|
S0S26S4eS51S44SfS6S25S44A1A1M0A1S1aSbS9eG0Z1000A2S19SbA1A3S71G0A1S65G0A1A5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RET0f : ltac2:(tb__ "0|1|
S0S15S68S78S59S1aS17S12S7A2M0S1bS12S7S79S4aA4S19G0A1A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RETPf : ltac2:(tb__ "0|1|
S0S15S68S78S5bS1aS17S12S7A2M0S1bS12S7S79S4aA4S1aG0S1bS12S7S7dS63A4S19G0A1A3A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nexts_f : ltac2:(tb__ "0|2|
S1S0S12S6S25S44A1A1S47A3S1S66S24S43A2S1S67S43S47A2S1S0S12S6S25S4eA1M0A1S65S47A1A3S1S0S12S6S25S48S44A1A1M1A1S47A3S1S0S15S8G1A1S18A3S0S15S8G0A1S18A3A2A2A2A2A2A2").
Proof.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [unfold NF, N18; lia|]. split; [unfold N18, N22f; lia|].
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.

Lemma tail_fail : ltac2:(tb__ "0|3|
S5S14S21Q40M0A1M1A1G1S5S90R4A1S9cS23G0Z0A2Vm;S6fR3A4S0G1S9R3S65S43A1A2R4A3S35R7S22G0R5A2M2S2fG2Z2000A2R4A4S8bS4Vok;S2bS4S6bS70Vm;R6A2S2fVB;Z1000A2A2S44R5R7A5S6cS4S24R8R7S77Vm;VB;A2A5A4F_;F_;F_;F_;Frho;Fa;Ftp;Frho0;").
Proof.
  intros rho0 tp a rho HSP0 Hpl Ha HVK. pose proof nexts_f as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls).
  pose proof E22f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  pose proof (mf_exp_facts a) as (Fres & Flim & Fmaps & Finit).
  eapply triple_seq.
  { apply triple1_triple.
    apply (node_rw ok OKF OKP E22f (mf_exp m a) (B + 4096) [(SAlu ALU_ADD vRES (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22f Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22f).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - rewrite Fres, Fmaps. apply band_covered_app_cons. exact Hband.
    - intros e sz [[= <- <-]|[]]. exists a, n8w. rewrite Fmaps. split; [left; reflexivity|].
      unfold vRES. cbn [eval]. rewrite Ha. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hpl as (_ & _ & Pceil & _). change (mmap_nZ n8w) with 8192 in Pceil. pose proof (alloc_top_lt (m_vmmaps m)).
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange a); unfold two_pow_64 in *; lia).
      change (bv_unsigned n8w) with 8192. lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK HSP0). }
  apply triple_disj.
  -
    apply (run1 ok (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M (refuse E22f) RET0f RsSymJump rho tp);
      [exact run_22f_fail | apply OKFx' | apply STx | exact Xlr |].
    intros rho1 Hag1. rewrite Xr in Hag1.
    eapply triple_entailsA; [exact ent_RET0f | exact wid_RET0f | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RET0f [(NA, vRES)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0f). eapply VK_agree; [| exact HVK | exact Hag1]. plia. }
    apply (post_fin ok (KxA (mf_exp m a) (B + 4096)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a). split; [exact Hpl|]. split; [reflexivity|]. split; [|split; [exact (proj2 HVK1)|]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0f [(NA, vRES)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. symmetry. apply (proj1 Hag1). plia.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply triple_ex. intros g. apply triple_pure. intros Hplg.
    rewrite <- S22f_eq.
    apply (run1 ok (KxA (mgrant (mf_exp m a) g) (B + 4096 + 4096)) FUEL_M CUTS_M S22f RETPf RsSymJump _ tp);
      [exact run_22f | apply OKFx' | apply STx | exact Xls |].
    intros rho1 Hag1. rewrite Xs in Hag1.
    eapply triple_entailsA; [exact ent_RETPf | exact wid_RETPf | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RETPf [(NA, vRES); (NG, vGRPf)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPf). eapply VK_agree; [| | exact Hag1]; [plia|]. apply VK_set_rw; [plia|]. exact HVK. }
    apply (post_fin ok _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a), g. split; [exact Hpl|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split; [exact (proj2 HVK1)|]]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. rewrite <- (proj1 Hag1 (Pos.succ N18)) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). reflexivity.
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NG) with vGRPf by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPf. cbn [eval]. rewrite <- (proj1 Hag1 N22f) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Lemma etail_fail : ltac2:(tb__ "0|3|
S5S14S21Q40M0A1M1A1G1S5S90R4A1S9cS23G0Z0A2Vm;S6fR3A4S0G1S9R3S65S43A1A2R4A3S35R7S22G0R5A2M2S2fG2Z2000A2R4A4S8cS4S2bS4S6bS70Vm;R6A2S2fVB;Z1000A2A2S44R5R7A5S6cS4S24R8R7S77Vm;VB;A2A5A3F_;F_;F_;F_;Frho;Fa;Ftp;Frho0;").
Proof.
  intros rho0 tp a rho HSP0 Hpl Ha HVK. pose proof nexts_f as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls).
  pose proof E22f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  pose proof (mf_exp_facts a) as (Fres & Flim & Fmaps & Finit).
  eapply etriple_seq.
  { apply (enode_rw_any E22f (mf_exp m a) (B + 4096) [(SAlu ALU_ADD vRES (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22f Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22f).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - rewrite Fres, Fmaps. apply band_covered_app_cons. exact Hband.
    - intros e sz [[= <- <-]|[]]. exists a, n8w. rewrite Fmaps. split; [left; reflexivity|].
      unfold vRES. cbn [eval]. rewrite Ha. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hpl as (_ & _ & Pceil & _). change (mmap_nZ n8w) with 8192 in Pceil. pose proof (alloc_top_lt (m_vmmaps m)).
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange a); unfold two_pow_64 in *; lia).
      change (bv_unsigned n8w) with 8192. lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK HSP0). }
  apply etriple_disj.
  -
    apply (erun1 (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M (refuse E22f) RET0f RsSymJump rho tp);
      [exact run_22f_fail | apply STx | exact Xlr |].
    intros rho1 Hag1. rewrite Xr in Hag1.
    eapply etriple_entailsA; [exact ent_RET0f | exact wid_RET0f | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RET0f [(NA, vRES)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0f). eapply VK_agree; [| exact HVK | exact Hag1]. plia. }
    apply (epost_fin (KxA (mf_exp m a) (B + 4096)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a). split; [exact Hpl|]. split; [reflexivity|]. split; [|split; [exact (proj2 HVK1)|]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0f [(NA, vRES)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. symmetry. apply (proj1 Hag1). plia.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply etriple_ex. intros g. apply etriple_pure. intros Hplg.
    rewrite <- S22f_eq.
    apply (erun1 (KxA (mgrant (mf_exp m a) g) (B + 4096 + 4096)) FUEL_M CUTS_M S22f RETPf RsSymJump _ tp);
      [exact run_22f | apply STx | exact Xls |].
    intros rho1 Hag1. rewrite Xs in Hag1.
    eapply etriple_entailsA; [exact ent_RETPf | exact wid_RETPf | apply STx |].
    assert (HVK1 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho1 (post_sub RETPf [(NA, vRES); (NG, vGRPf)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPf). eapply VK_agree; [| | exact Hag1]; [plia|]. apply VK_set_rw; [plia|]. exact HVK. }
    apply (epost_fin _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK1)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK1)|].
    exists (O1_fail a), g. split; [exact Hpl|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split; [exact (proj2 HVK1)|]]].
    + cbn [out1_base]. unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NA) with vRES by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vRES. cbn [eval]. rewrite <- Ha. rewrite <- (proj1 Hag1 (Pos.succ N18)) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). reflexivity.
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPf [(NA, vRES); (NG, vGRPf)]) NG) with vGRPf by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPf. cbn [eval]. rewrite <- (proj1 Hag1 N22f) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + cbn [out1_model]. split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Definition grow_out (o : out1) : Prop := match o with O1_fail _ => False | _ => True end.

Lemma grow_facts : ltac2:(tb__ "0|9|
S7bS91R1A1S96S38S37Vm;A1M0A1M1A1S0S15S3eS1dS17S21Q40M2A1M3G3A2M4S3aG0A1M5G1A3S6eVm;A1S72A3S16A3S1S0S14G4A1S3aS37S7aVm;R4A2A1M6A1M7G5A3S1S0S13S3cG6A1S3cG0A1A3S1S0G3S3dG6A1S3dG0A1A3S1S2G3G3S2G3G3S1S8fG4S1bG3G3R2R1A4S38S37S7aVm;R6A2A1A1A3S1S30S22G2R2A2M8S2fVbrk0;Z1000A2A2S30S2fVbrk0;Z2000A2S2fG8S22G2R1A2A2A2A2A2Ls;A2Lb;A2S9bS1dG4G7S38G6A1A3S9aS99A3A2A2A2A2F_;F_;F_;Fo;").
Proof.
  intros o Ho Hwf Hfree3. pose proof (mg_vmmaps m Hlo Hhi) as MG. pose proof (n2w_val) as NV. pose proof n3w_val as NV3.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  pose proof (band_clear_of_free _ (brk0w m) n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  assert (BG : band_covered (vm_reserved (m_vmmaps m) ++ (brk0w m, n2w) :: vm_maps (m_vmmaps m)) SHADOW_BAND_LO SHADOW_BAND_HI)
    by (apply band_covered_app_cons; exact Hband).
  destruct o as [| | |a]; cbn [out1_model]; [| | |destruct Ho].
  -   rewrite MG. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact BG].
    exists (brk0w m), n2w. split; [left; reflexivity|]. rewrite NV. unfold brk0. lia.
  -   unfold mg_ok. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_ok_vm. cbn [vm_reserved vm_limit vm_maps vm_init_sp].
    rewrite MG. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact BG].
    exists (brk0w m), n2w. split; [left; reflexivity|]. rewrite NV. unfold brk0. lia.
  -   unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_dead_vm. cbn [vm_reserved vm_limit vm_maps vm_init_sp].
    rewrite MG. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0. fold brk0. rewrite Upg. cbn [maps_subtract].
    assert (Eiv : iv_subtract (brk0w m) n2w brk0 (brk0 + 4096) = [(Z_to_bv 64 (brk0 + 4096), Z_to_bv 64 4096)]).
    { unfold iv_subtract. unfold brk0. rewrite NV. rewrite Z.ltb_irrefl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
      rewrite Z.max_r by lia. f_equal. f_equal. f_equal. lia. }
    rewrite Eiv. cbn [app]. split.
    + exists (Z_to_bv 64 (brk0 + 4096)), (Z_to_bv 64 4096). split; [left; reflexivity|].
      pose proof Hlo. pose proof Hhi. unfold brk0 in *. rewrite !u64_of_lit by lia. lia.
    + apply band_covered_app_cons. apply band_covered_subtract; [exact Hwf | lia | | exact Hband].
      pose proof Hlo. pose proof Hhi. unfold brk0, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, SHADOW_BAND_LO, SHADOW_BAND_HI in *. right.
      destruct (Z.le_gt_cases (bv_unsigned (brk0w m) + 4096) 0x7fff7000) as [L|L]; [exact L|]. exfalso.
      destruct (Z.le_gt_cases 0x7fff7000 (bv_unsigned (brk0w m))).
      * apply (HBD (bv_unsigned (brk0w m))); lia.
      * apply (HBD 0x7fff7000); lia.
Qed.

Lemma facts_M_in_E22g : ltac2:(tb__ "0|0|
SaS8fSaR1S94A3S8fSaR2S11S25S45A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma objs_clear_E22g : ltac2:(tb__ "0|2|
S0S15S73S1aS17S7S13A2M0S1bS7S13SeS98S49ScZ1000M1A1A3G1A4S19G0A1A3S25S45A1A2S16A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S22g_eq : ltac2:(tb__ "0|1|
S0S26S4fS51S45SfS6S25S45A1A1M0A1S1aSbS9eG0Z1000A2S19SbA1A3S71G0A1S65G0A1A5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RET0g : ltac2:(tb__ "0|1|
S0S15S68S78S5aS1aS17S12S7A2M0S1bS12S7S79S49A4S19G0A1A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RETPg : ltac2:(tb__ "0|1|
S0S15S68S78S5cS1aS17S12S7A2M0S1bS12S7S79S49A4S1aG0S1bS12S7S7dS64A4S19G0A1A3A3A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nexts_g : ltac2:(tb__ "0|4|
S1S0S12S6S25S45A1A1S46A3S1S66S24S43A2S1S67S43S46A2S1S0S12S6S25S4fA1M0A1S65S46A1A3S1S0S12S6S25S48S45A1A1M1A1S46A3S1S0S15S8G1A1S18A3S1S0S15S8G0A1S18A3S1S0S12S6S25S50A1M2A1S65S65S43A1A1M3A3S1S0S15S8G2A1S18A3S66G3S46A2A2A2A2A2A2A2A2A2A2").
Proof.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [unfold NF, N18; lia|]. split; [unfold N18, N22g; lia|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. unfold N18, N22g; lia.
Qed.

Lemma tail_grow : ltac2:(tb__ "0|2|
S7bS5S14S21Q40A1M0A1S5S90R3A1S91R5A1S7eVm;R6A2S96S38S37Vm;A1A1A1S0G0S9R5S43A2S6eVm;A1A3S35R8Vbrk0;S2fVbrk0;Z2000M1A2R6A4S8bS4Vok;S2bS4S6bS7aVm;RaA2S2fVB;G1A2A2S50R7S7fVm;RaR8A3A5S6cS4S24R9R8S77Vm;VB;A2A5A4F_;F_;F_;F_;F_;F_;Frho;Ftp0;Frho0;Fo;").
Proof.
  intros o rho0 tp0 rho HSP0 Ho Hok Hwf HN18 HVK. pose proof nexts_g as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls & Xu & Xlu & Xun).
  pose proof E22g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  assert (Hfree3 : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (brk0w m) n3w = true)
    by (destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok)).
  destruct (grow_facts o Ho Hwf Hfree3) as (Fres & Flim & Finit & (b1 & s1 & Hb1 & Hb1l & Hb1h) & Fband).
  set (mx := out1_model m o) in *. set (tpx := out1_tp m o tp0) in *.
  apply (run1 ok (KxA mx (B + 8192)) FUEL_M CUTS_M U24c E22g RsCut rho tpx); [exact run_24 | apply OKFx' | apply STx | exact Xlu |].
  intros rho1 Hag1. rewrite Xu in Hag1.
  assert (HN18' : rw rho1 N18 = brk0w m) by (rewrite <- (proj1 Hag1 N18) by plia; exact HN18).
  assert (HVK1 : VK rho0 brk0 (brk0 + 8192) rho1) by (eapply VK_agree; [| exact HVK | exact Hag1]; plia).
  eapply triple_seq.
  { apply triple1_triple.
    apply (node_rw ok OKF OKP E22g mx (B + 8192) [(SAlu ALU_ADD vBRK (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22g Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22g).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - exact Fband.
    - intros e sz [[= <- <-]|[]]. exists b1, s1. split; [exact Hb1|].
      unfold vBRK. cbn [eval]. rewrite HN18'. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hlo. pose proof Hhi. unfold brk0 in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK1 HSP0). }
  apply triple_disj.
  -
    apply (run1 ok (KxA mx (B + 8192)) FUEL_M CUTS_M (refuse E22g) RET0g RsSymJump rho1 tpx);
      [exact run_22g_fail | apply OKFx' | apply STx | exact Xlr |].
    intros rho2 Hag2. rewrite Xr in Hag2.
    eapply triple_entailsA; [exact ent_RET0g | exact wid_RET0g | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RET0g [(NA, vBRK)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0g). eapply VK_agree; [| exact HVK1 | exact Hag2]. plia. }
    apply (post_fin ok (KxA mx (B + 8192)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o. split; [exact Hok|]. split; [reflexivity|]. split; [|split].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0g [(NA, vBRK)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by plia. rewrite HN18'. destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply triple_ex. intros g. apply triple_pure. intros Hplg.
    rewrite <- S22g_eq.
    apply (run1 ok (KxA (mgrant mx g) (B + 8192 + 4096)) FUEL_M CUTS_M S22g RETPg RsSymJump _ tpx);
      [exact run_22g | apply OKFx' | apply STx | exact Xls |].
    intros rho2 Hag2. rewrite Xs in Hag2.
    eapply triple_entailsA; [exact ent_RETPg | exact wid_RETPg | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPg). eapply VK_agree; [| | exact Hag2]; [plia|]. apply VK_set_rw; [plia|]. exact HVK1. }
    apply (post_fin ok _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o, g. split; [exact Hok|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split]].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). rewrite HN18'.
      destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NG) with vGRPg by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPg. cbn [eval]. rewrite <- (proj1 Hag2 N22g) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Lemma etail_grow : forall (o : out1) (rho0 : valuation) (tp0 : list word) (rho : valuation),
  SP0 rho0 -> grow_out o -> out1_ok m o -> ivs_wf (vm_maps (m_vmmaps m)) ->
  rw rho N18 = brk0w m -> VK rho0 brk0 (brk0 + 8192) rho ->
  etriple segsA (SPA segsA (KxA (out1_model m o) (B + 8192)) U24c rho (out1_tp m o tp0))
    (LQPA segsA NF rho0 tp0 (Posts_M m B)).
Proof.
  intros o rho0 tp0 rho HSP0 Ho Hok Hwf HN18 HVK. pose proof nexts_g as (Xn & Xf & Xlt & Xs & Xr & Xlr & Xls & Xu & Xlu & Xun).
  pose proof E22g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  assert (Hfree3 : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (brk0w m) n3w = true)
    by (destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok)).
  destruct (grow_facts o Ho Hwf Hfree3) as (Fres & Flim & Finit & (b1 & s1 & Hb1 & Hb1l & Hb1h) & Fband).
  set (mx := out1_model m o) in *. set (tpx := out1_tp m o tp0) in *.
  apply (erun1 (KxA mx (B + 8192)) FUEL_M CUTS_M U24c E22g RsCut rho tpx); [exact run_24 | apply STx | exact Xlu |].
  intros rho1 Hag1. rewrite Xu in Hag1.
  assert (HN18' : rw rho1 N18 = brk0w m) by (rewrite <- (proj1 Hag1 N18) by plia; exact HN18).
  assert (HVK1 : VK rho0 brk0 (brk0 + 8192) rho1) by (eapply VK_agree; [| exact HVK | exact Hag1]; plia).
  eapply etriple_seq.
  { apply (enode_rw_any E22g mx (B + 8192) [(SAlu ALU_ADD vBRK (SLit 4096), 4096)]
             eq_refl eq_refl facts_M_in_E22g Hecall R17 R10 R11 R12 R13 R14 R15 objs_clear_E22g).
    - rewrite Fres. exact Hres.
    - rewrite Flim. pose proof HB. lia.
    - unfold init_sp_ok. rewrite Finit. exact Htop.
    - exact Fband.
    - intros e sz [[= <- <-]|[]]. exists b1, s1. split; [exact Hb1|].
      unfold vBRK. cbn [eval]. rewrite HN18'. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096) by lia.
      pose proof Hlo. pose proof Hhi. unfold brk0 in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
    - unfold alloc_top. rewrite Finit. exact (VK_sp _ _ _ _ _ HVK1 HSP0). }
  apply etriple_disj.
  -
    apply (erun1 (KxA mx (B + 8192)) FUEL_M CUTS_M (refuse E22g) RET0g RsSymJump rho1 tpx);
      [exact run_22g_fail | apply STx | exact Xlr |].
    intros rho2 Hag2. rewrite Xr in Hag2.
    eapply etriple_entailsA; [exact ent_RET0g | exact wid_RET0g | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RET0g [(NA, vBRK)]))).
    { apply (VK_sub _ _ _ _ _ wid_RET0g). eapply VK_agree; [| exact HVK1 | exact Hag2]. plia. }
    apply (epost_fin (KxA mx (B + 8192)) P_null1 (JL_null1 m B)); [right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o. split; [exact Hok|]. split; [reflexivity|]. split; [|split].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RET0g [(NA, vBRK)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by plia. rewrite HN18'. destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply etriple_ex. intros g. apply etriple_pure. intros Hplg.
    rewrite <- S22g_eq.
    apply (erun1 (KxA (mgrant mx g) (B + 8192 + 4096)) FUEL_M CUTS_M S22g RETPg RsSymJump _ tpx);
      [exact run_22g | apply STx | exact Xls |].
    intros rho2 Hag2. rewrite Xs in Hag2.
    eapply etriple_entailsA; [exact ent_RETPg | exact wid_RETPg | apply STx |].
    assert (HVK2 : VK rho0 brk0 (brk0 + 8192) (rho_sub rho2 (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]))).
    { apply (VK_sub _ _ _ _ _ wid_RETPg). eapply VK_agree; [| | exact Hag2]; [plia|]. apply VK_set_rw; [plia|]. exact HVK1. }
    apply (epost_fin _ P_ok (JL_ok m B)); [right; right; left; reflexivity | | exact (proj1 HVK2)].
    intros tr md (Htr & Hem & Hpaid). split; [exact (proj1 HVK2)|].
    exists o, g. split; [exact Hok|]. split; [exact Hplg|]. split; [reflexivity|]. split; [|split; [|split]].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NA) with vBRK by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vBRK. cbn [eval]. rewrite <- (proj1 Hag2 N18) by (rewrite ?Xn; plia). rewrite rho_set_rw_other by (rewrite ?Xn; plia). rewrite HN18'.
      destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho].
    + unfold rho_sub. cbn [rw]. replace (wsub_get (post_sub RETPg [(NA, vBRK); (NG, vGRPg)]) NG) with vGRPg by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      unfold vGRPg. cbn [eval]. rewrite <- (proj1 Hag2 N22g) by (rewrite ?Xn; plia). rewrite Xn. apply rho_set_rw_at.
    + replace (out1_W m o) with (brk0, brk0 + 8192) by (destruct o; [reflexivity|reflexivity|reflexivity|destruct Ho]). exact (proj2 HVK2).
    + split; [exact Htr|]. split; [exact Hem|]. lia.
Qed.

Definition Z8 (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S21Q40M0A1S1S30S2fVbrk0;Z1000A2S22G0R1A2M1A2S31G1S2fVbrk0;Z2000A2A2A2S0S1cS21Q8M2A1M3A1S10Vrho;R2A2S1eG3S23G2Z0A2A2A3F_;Fa;").

Lemma nexts_20 : ltac2:(tb__ "0|5|
S1S0S12S6S25S60A1M0A1S65S43A1M1A3S1S0S12S6S25S5fA1M2A1G1A3S1S0S15S8G0A1S18A3S1S0S15S8G2A1S18A3S1S0S15S68S1aS17S12S7A2M3S1bS12S7G1S49A4S19G3A1M4A3S24A2S16A3S0S15S68S1aG3S1bS12S7G1ScS34S33Z2Z40A2Z1A2A1A4G4A3S24A2S16A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma from_L24 : ltac2:(tb__ "0|2|
S7bS5S14S21Q40A1M0A1S26S69S5S90R5A1S91R7A1S7eVm;R8A2S96S38S37Vm;A1A1A1S0S15S2aR7S62R6A3S16A3S0S15S68R7S24A2S16A3S0S15S68R8S65S43A1A2S16A3S0G0S9R8S43A2S6eVm;A1A3S35RdVbrk0;S2fVbrk0;Z2000M1A2R9A4S92RaA1S8bS4Vok;S2bS4S6bS7aVm;R10A2S2fVB;G1A2A2RdRbS7fVm;R10ReA3A5S6cS4S24RfReS77Vm;VB;A2A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fs;FL;Ftp0;Frho0;Fo;").
Proof.
  intros o rho0 tp0 L s rho HSP0 Ho Hok Hwf He Hs Hs' HN18 HVK HZ8.
  eapply triple_entailsA; [exact He | exact Hs | apply STx |].
  assert (HN18' : rw (rho_sub rho s) N18 = brk0w m) by (rewrite (rw_sub_other rho s N18 Hs'); exact HN18).
  assert (HVK' : VK rho0 brk0 (brk0 + 8192) (rho_sub rho s)) by (apply (VK_sub _ _ _ _ _ Hs); exact HVK).
  eapply triple_conseq; [| intros w Hw; exact Hw | apply (tail_grow o rho0 tp0 (rho_sub rho s) HSP0 Ho Hok Hwf HN18' HVK')].
  intros w Hw. apply (carve24 m Hlo Hhi Htop Hband _ (rho_sub rho s)); [exact HN18' | | exact (VK_sp _ _ _ _ _ HVK' HSP0) | | | exact Hw].
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj1 Hok).
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok).
  + intros a Ha. cbn. apply HZ8. exact Ha.
Qed.

Lemma efrom_L24 : forall (o : out1) (rho0 : valuation) (tp0 : list word) (L : axst) (s : wsub) (rho : valuation),
  SP0 rho0 -> grow_out o -> out1_ok m o -> ivs_wf (vm_maps (m_vmmaps m)) ->
  entailsA L U24 s = true -> wsub_id_below s NF = true -> wsub_id_below s (Pos.succ N18) = true ->
  rw rho N18 = brk0w m -> VK rho0 brk0 (brk0 + 8192) rho -> Z8 rho ->
  etriple segsA (SPA segsA (KxA (out1_model m o) (B + 8192)) L rho (out1_tp m o tp0))
    (LQPA segsA NF rho0 tp0 (Posts_M m B)).
Proof.
  intros o rho0 tp0 L s rho HSP0 Ho Hok Hwf He Hs Hs' HN18 HVK HZ8.
  eapply etriple_entailsA; [exact He | exact Hs | apply STx |].
  assert (HN18' : rw (rho_sub rho s) N18 = brk0w m) by (rewrite (rw_sub_other rho s N18 Hs'); exact HN18).
  assert (HVK' : VK rho0 brk0 (brk0 + 8192) (rho_sub rho s)) by (apply (VK_sub _ _ _ _ _ Hs); exact HVK).
  eapply etriple_conseq; [| intros w Hw; exact Hw | apply (etail_grow o rho0 tp0 (rho_sub rho s) HSP0 Ho Hok Hwf HN18' HVK')].
  intros w Hw. apply (carve24 m Hlo Hhi Htop Hband _ (rho_sub rho s)); [exact HN18' | | exact (VK_sp _ _ _ _ _ HVK' HSP0) | | | exact Hw].
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj1 Hok).
  + destruct o; cbn [out1_ok] in Hok; [| | |destruct Ho]; exact (proj2 Hok).
  + intros a Ha. cbn. apply HZ8. exact Ha.
Qed.

Lemma seg_grow : ltac2:(tb__ "0|6|
S5S14S21Q40A1M0A1S5S90R3A1S0G0S9R2S43A2S6eVm;A1M1A3S1S30S2fVbrk0;Z2000M2A2M3S3fS37Vm;A1M4A1A2S0S15S3eS1dS17G0G0A2S3aG4A1S38G4A1M5A3G1S72A3S16A3A2S96G5A1S35R7Vbrk0;G3R5A4S92R6A1S8bS4Vok;S2bS4S6bS76Vm;A1S2fVB;G2A2A2S55R7R8A5S6cS4S24R9R8S77Vm;VB;A2A5A4F_;F_;F_;F_;F_;F_;Frho;Ftp;Frho0;").
Proof.
  intros rho0 tp rho HSP0 HN18 Hok Hwf HVK HZ8. pose proof nexts_20 as (Xok & Xko & Lok & Lko & Wok & Wko).
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HVK20 : VK rho0 brk0 (brk0 + 8192) (rho20 m rho)).
  { unfold rho20. apply VK_set_rm; [exact HVK|]. intros x Hx. apply unmap_range_outside. rewrite Upg. unfold brk0 in Hx. lia. }
  assert (HZ20 : Z8 (rho20 m rho)).
  { unfold rho20, Z8. intros a Ha. unfold set_rm. cbn [rm]. rewrite unmap_range_outside by (rewrite Upg; unfold brk0 in Ha; lia). apply HZ8. exact Ha. }
  eapply triple_seq; [apply triple1_triple; apply (node20g ok OKF OKP m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho tp (B + 8192) HN18 (VK_sp _ _ _ _ _ HVK HSP0) (proj2 Hok))|].
  apply triple_disj; [|apply triple_disj; [|apply triple_pure; intros _]].
  -
    apply (run1 ok (KxA (mg m) (B + 8192)) FUEL_M (0xd59b4 :: CUTS_M) S20g_ko L24ko RsCut rho tp); [exact run_20g_ko | apply OKFx' | apply STx | exact Lko |].
    intros rho1 Hag1. rewrite Xko in Hag1.
    apply (from_L24 O1_kept rho0 tp L24ko _ rho1 HSP0 I Hok Hwf ent_24ko Wko Wko).
    + rewrite <- (proj1 Hag1 N18) by plia. exact HN18.
    + eapply VK_agree; [| exact HVK | exact Hag1]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ8. exact Ha.
  -
    apply (run1 ok (KxA (mg_ok m) (B + 8192)) FUEL_M (0xd59b4 :: CUTS_M) S20g_ok L24ok RsCut (rho20 m rho) tp); [exact run_20g_ok | apply OKFx' | apply STx | exact Lok |].
    intros rho1 Hag1. rewrite Xok in Hag1.
    apply (from_L24 O1_ok rho0 tp L24ok _ rho1 HSP0 I Hok Hwf ent_24ok Wok Wok).
    + rewrite <- (proj1 Hag1 N18) by plia. unfold rho20, set_rm. cbn [rw]. exact HN18.
    + eapply VK_agree; [| exact HVK20 | exact Hag1]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ20. exact Ha.
  -
    apply (run1 ok (KxA (mg_dead m) (B + 8192)) FUEL_M (0xd59b4 :: CUTS_M) S20g_ko L24ko RsCut (rho20 m rho) (tp20 m tp)); [exact run_20g_ko | apply OKFx' | apply STx | exact Lko |].
    intros rho1 Hag1. rewrite Xko in Hag1.
    apply (from_L24 O1_dead rho0 tp L24ko _ rho1 HSP0 I Hok Hwf ent_24ko Wko Wko).
    + rewrite <- (proj1 Hag1 N18) by plia. unfold rho20, set_rm. cbn [rw]. exact HN18.
    + eapply VK_agree; [| exact HVK20 | exact Hag1]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ20. exact Ha.
Qed.

Lemma eseg_grow : forall (rho0 : valuation) (tp : list word) (rho : valuation),
  SP0 rho0 -> rw rho N18 = brk0w m ->
  brk0 + 8192 <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (brk0w m) n3w = true ->
  ivs_wf (vm_maps (m_vmmaps m)) -> VK rho0 brk0 (brk0 + 8192) rho -> Z8 rho ->
  etriple segsA (SPA segsA (KxA (mg m) (B + 8192)) E20g rho tp) (LQPA segsA NF rho0 tp (Posts_M m B)).
Proof.
  intros rho0 tp rho HSP0 HN18 Hok Hwf HVK HZ8. pose proof nexts_20 as (Xok & Xko & Lok & Lko & Wok & Wko).
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HVK20 : VK rho0 brk0 (brk0 + 8192) (rho20 m rho)).
  { unfold rho20. apply VK_set_rm; [exact HVK|]. intros x Hx. apply unmap_range_outside. rewrite Upg. unfold brk0 in Hx. lia. }
  assert (HZ20 : Z8 (rho20 m rho)).
  { unfold rho20, Z8. intros a Ha. unfold set_rm. cbn [rm]. rewrite unmap_range_outside by (rewrite Upg; unfold brk0 in Ha; lia). apply HZ8. exact Ha. }
  eapply etriple_seq; [apply (enode20g_ok m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho tp (B + 8192) HN18 (VK_sp _ _ _ _ _ HVK HSP0) (proj2 Hok))|].
  apply (erun1 (KxA (mg_ok m) (B + 8192)) FUEL_M (0xd59b4 :: CUTS_M) S20g_ok L24ok RsCut (rho20 m rho) tp); [exact run_20g_ok | apply STx | exact Lok |].
  intros rho1 Hag1. rewrite Xok in Hag1.
  apply (efrom_L24 O1_ok rho0 tp L24ok _ rho1 HSP0 I Hok Hwf ent_24ok Wok Wok).
  + rewrite <- (proj1 Hag1 N18) by plia. unfold rho20, set_rm. cbn [rw]. exact HN18.
  + eapply VK_agree; [| exact HVK20 | exact Hag1]. plia.
  + intros a Ha. rewrite <- (proj2 (proj2 Hag1)). apply HZ20. exact Ha.
Qed.

Lemma nexts_main : ltac2:(tb__ "0|b|
S1S0S12S6S25S93A1M0A1S24A3S1S0S15S8G0A1S18A3S1S0S12S6S25S4bA1A1M1G1A3S1S0S12S6S25S4cA1M2A1S65S43A1M3A3S1S0S15S8G2A1S18A3S1S0S12S6S25S5dA1M4A1G3A3S1S0S15S8G4A1S18A3S1S0S12S6S25S4dA1M5A1G3A3S1S0S15S8G5A1S18A3S1S0S12S6S25S48S54A1A1M6A1G3A3S1S0S15S8G6A1S18A3S1S0S12S6S25S5eA1M7A1S65G3A1M8A3S1S0S15S8G7A1S18A3S1S0S12S6S25S48S56A1A1M9A1G8A3S1S0S15S8G9A1S18A3S1S0S12S6S25S61A1MaA1G8A3S0S15S8GaA1S18A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma wid_RET0a : ltac2:(tb__ "0|0|
S0S15S68S78S57S19S17S12S7A2A1A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_RET0b : ltac2:(tb__ "0|0|
S0S15S68S78S58S19S17S12S7A2A1A2S24A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma next_E18_ge : ltac2:(tb__ "0|0|
S1S66S24S6S25S4bA1A1A2S66S24S43A2A2").
Proof. split; [vm_compute; discriminate | unfold NF, N18; lia]. Qed.

Theorem musl_malloc40_main : ltac2:(tb__ "0|0|
S5S14S21Q40A1A1Sa2Vm;R1A2S96S38S37Vm;A1A1A1S90R4A1S8bS4Vok;S2bS4S6bVm;VB;A2S93R5R4A5S6cS4S24R5R4S77Vm;VB;A2A5A4F_;F_;F_;Ftp;Frho;").
Proof.
  intros rho0 tp Htp Hwf HSP0.
  pose proof nexts_main as (XnP & XlP & _ & Xn18 & Xl18 & Xn19g & Xl19g & Xn19f & Xl19f & Xn20r & Xl20r & Xn20 & Xl20 & Xn21r & Xl21r & Xn21 & Xl21).
  pose proof next_E18_ge as [XE18 XN18].

  apply (run1 ok (KxA m B) FUEL_M CUTS_M Pre_M E18 RsCut rho0 tp); [exact run_I | apply OKFx' | apply STx | exact XlP |].
  intros rho1 Hag1. rewrite XnP in Hag1.
  assert (HVK1 : VK rho0 0 0 rho1) by (eapply VK_agree; [apply Pos.le_refl | apply VK_refl | exact Hag1]).
  eapply (triple_entailsA segsA ok (KxA m B) NF E18 E18t []); [exact ent_18 | reflexivity | apply STx |].
  assert (HVK1' : VK rho0 0 0 (rho_sub rho1 [])) by (apply (VK_sub _ _ _ _ [] eq_refl); exact HVK1).
  set (rho1' := rho_sub rho1 []) in *.

  eapply triple_seq; [apply triple1_triple; apply (node18 ok OKF OKP m B Hal Hlo Hhi rho1' tp)|].
  assert (HVK2 : VK rho0 0 0 (rho_set_rw rho1' N18 (brk0w m))) by (apply VK_set_rw; [exact XN18 | exact HVK1']).
  apply (run1 ok (KxA m B) FUEL_M CUTS_M S18 E19 RsCut _ tp); [exact run_18 | apply OKFx' | apply STx | exact Xl18 |].
  intros rho2 Hag2. rewrite Xn18 in Hag2.
  assert (HN18 : rw rho2 N18 = brk0w m) by (rewrite <- (proj1 Hag2 N18) by plia; apply rho_set_rw_at).
  assert (HVK3 : VK rho0 0 0 rho2) by (eapply VK_agree; [| exact HVK2 | exact Hag2]; plia).

  eapply triple_seq; [apply triple1_triple; apply (node19 ok OKF OKP m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho2 tp HN18 (VK_sp _ _ _ _ _ HVK3 HSP0))|].
  apply triple_disj.
  -
    apply triple_ex. intros rho3. apply triple_pure. intros Hceil. apply triple_pure. intros Hfree. apply triple_pure. intros (R1 & R2 & R3 & R4).
    assert (HN18' : rw rho3 N18 = brk0w m) by (rewrite R1; exact HN18).
    assert (HVK4 : VK rho0 brk0 (brk0 + 8192) rho3).
    { destruct HVK3 as [Hav Hrm]. split.
      - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; symmetry; apply R1 | intros l; symmetry; apply R2].
      - intros x Hx. rewrite (R3 x) by (unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0; unfold brk0 in Hx; exact Hx). apply Hrm. lia. }
    apply (run1 ok (KxA (mg m) (B + 8192)) FUEL_M CUTS_M S19g E20g RsCut rho3 tp); [exact run_19g | apply OKFx' | apply STx | exact Xl19g |].
    intros rho4 Hag4. rewrite Xn19g in Hag4.
    apply (seg_grow rho0 tp rho4 HSP0).
    + rewrite <- (proj1 Hag4 N18) by plia. exact HN18'.
    + split; [unfold brk0; exact Hceil | exact Hfree].
    + exact Hwf.
    + eapply VK_agree; [| exact HVK4 | exact Hag4]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag4)). apply R4. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0. unfold brk0 in Ha. lia.
  -
    apply (run1 ok (KxA m B) FUEL_M CUTS_M S19f E20f RsCut rho2 tp); [exact run_19f | apply OKFx' | apply STx | exact Xl19f |].
    intros rho3 Hag3. rewrite Xn19f in Hag3.
    assert (HVK4 : VK rho0 0 0 rho3) by (eapply VK_agree; [| exact HVK3 | exact Hag3]; plia).
    eapply triple_seq; [apply triple1_triple; apply (node20f ok OKF OKP m B Hres HB Htop Hband rho3 tp (VK_sp _ _ _ _ _ HVK4 HSP0))|].
    apply triple_disj.
    +
      apply (run1 ok (KxA m B) FUEL_M CUTS_M (refuse E20f) RET0a RsSymJump rho3 tp); [exact run_20f_fail | apply OKFx' | apply STx | exact Xl20r |].
      intros rho4 Hag4. rewrite Xn20r in Hag4.
      eapply triple_entailsA; [exact ent_RET0a | exact wid_RET0a | apply STx |].
      assert (HVK5 : VK rho0 0 0 (rho_sub rho4 (post_sub RET0a []))).
      { apply (VK_sub _ _ _ _ _ wid_RET0a). eapply VK_agree; [| exact HVK4 | exact Hag4]. plia. }
      apply (post_fin ok (KxA m B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK5)].
      intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK5)|].
      exists O0_refused. split; [exact I|]. split; [exact (proj2 HVK5)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
    +
      apply triple_ex. intros a. apply triple_pure. intros Hpl.
      assert (HVK5 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho20f rho3 a)).
      { unfold rho20f. apply VK_set_rw; [plia|]. apply VK_set_rm; [eapply VK_widen; [| exact HVK4]; intros z Hz; lia|].
        intros x Hx. apply unmap_range_outside. change (bv_unsigned n8w) with 8192. exact Hx. }
      apply (run1 ok (KxA (mf_res m a) B) FUEL_M CUTS_M S20f E21f RsCut (rho20f rho3 a) tp); [exact run_20f | apply OKFx' | apply STx | exact Xl20 |].
      intros rho4 Hag4. rewrite Xn20 in Hag4.
      assert (Ha : rw rho4 (Pos.succ N18) = a) by (rewrite <- (proj1 Hag4 (Pos.succ N18)) by plia; unfold rho20f; apply rho_set_rw_at).
      assert (HVK6 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) rho4) by (eapply VK_agree; [| exact HVK5 | exact Hag4]; plia).
      eapply triple_seq; [apply triple1_triple; apply (node21f ok OKF OKP m B Hres HB Htop Hband Hlz Hlim rho4 tp a Ha (VK_sp _ _ _ _ _ HVK6 HSP0) Hpl Htp)|].
      apply triple_disj.
      *
        apply (run1 ok (KxA (mf_res m a) B) FUEL_M CUTS_M (refuse E21f) RET0b RsSymJump rho4 tp); [exact run_21f_fail | apply OKFx' | apply STx | exact Xl21r |].
        intros rho5 Hag5. rewrite Xn21r in Hag5.
        eapply triple_entailsA; [exact ent_RET0b | exact wid_RET0b | apply STx |].
        assert (HVK7 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho5 (post_sub RET0b []))).
        { apply (VK_sub _ _ _ _ _ wid_RET0b). eapply VK_agree; [| exact HVK6 | exact Hag5]. plia. }
        apply (post_fin ok (KxA (mf_res m a) B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK7)].
        intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK7)|].
        exists (O0_reserved a). split; [exact Hpl|]. split; [exact (proj2 HVK7)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
      *
        apply (run1 ok (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M S21f E22f RsCut rho4 tp); [exact run_21f | apply OKFx' | apply STx | exact Xl21 |].
        intros rho5 Hag5. rewrite Xn21 in Hag5.
        apply (tail_fail rho0 tp a rho5 HSP0 Hpl).
        -- rewrite <- (proj1 Hag5 (Pos.succ N18)) by plia. exact Ha.
        -- eapply VK_agree; [| exact HVK6 | exact Hag5]. plia.
Qed.

Theorem musl_malloc40_sum : ltac2:(tb__ "0|0|
S5S14S21Q40A1A1S8bS4Vok;S2bS4S7cVm;VB;A2S93R2R1A5S6cS4S24R2R1S77Vm;VB;A2A5A4Ftp;Frho;").
Proof.
  intros rho tp n Hg w HP. destruct w as [tr [ms md]].
  pose proof HP as [(Hsm & HMI & _) ((Htr & Hem & Hpaid) & HSP0)].
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _).
  apply (musl_malloc40_main rho tp); [| | exact HSP0 | exact Hg | exact (conj (proj1 HP) (proj1 (proj2 HP)))].
  - cbn [cfg_model snd] in HMI. intros p Hp. destruct (MI_tp_in_maps segsA _ _ HMI p Hp) as (Hal' & b & s0 & Hin & Hb). split; [exact Hal'|].
    exists b, s0. rewrite <- Evm. split; [exact Hin | exact Hb].
  - cbn [cfg_model snd] in HMI. rewrite <- Evm. exact (proj1 (MI_ivs_wf segsA _ _ HMI)).
Qed.

Lemma enode18 : ltac2:(tb__ "0|1|
S5S14S21Q40A1A1S8cS4S2bS4S6bVm;VB;A2M0S52R2R1A5S2bS4G0S4cS9fR2S43S6eVm;A1A3R1A5A3Ftp;Frho;").
Proof.
  intros rho tp. pose proof E18_at as (Hpc & Hecall & R17 & R10).
  apply etriple_ecall_detA; [apply STx | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _ & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E18t [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  exists ([], mkCfg (after_sys ms (vm_brk (m_vmmaps md))) md). split.
  - apply (wstep_brk_query_introA segsA ms md _ Hh H214 [] Hp G0).
  - split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
    unfold S18, cont. rewrite Evm. change (vm_brk (m_vmmaps m)) with (brk0w m).
    assert (HN : ss_next (ax_S E18t) = N18) by reflexivity. rewrite <- HN.
    eapply smatchA_after_ret_fresh; [exact Hsp | exact Hh | apply vm_same_refl | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    rewrite HN. unfold F18, vBRK. pose proof Hal as Hal'. pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 in Hal', Hlo', Hhi'.
    constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds eval]; rewrite rho_set_rw_at.
    + split; [lia|]. change (2 ^ 12) with 4096. exact Hal'.
    + rewrite (u64_of_lit 0x646000) by lia. lia.
    + rewrite (u64_of_lit 0x80646000) by lia. lia.
Qed.

Theorem musl_malloc40_main_ex : forall (rho : valuation) (tp : list word),
  tp_in_maps m tp -> ivs_wf (vm_maps (m_vmmaps m)) -> SP0 rho ->
  etriple segsA (SPA segsA (KxA m B) Pre_M rho tp) (LQPA segsA NF rho tp (Posts_M m B)).
Proof.
  intros rho0 tp Htp Hwf HSP0.
  pose proof nexts_main as (XnP & XlP & _ & Xn18 & Xl18 & Xn19g & Xl19g & Xn19f & Xl19f & Xn20r & Xl20r & Xn20 & Xl20 & Xn21r & Xl21r & Xn21 & Xl21).
  pose proof next_E18_ge as [XE18 XN18].
  apply (erun1 (KxA m B) FUEL_M CUTS_M Pre_M E18 RsCut rho0 tp); [exact run_I | apply STx | exact XlP |].
  intros rho1 Hag1. rewrite XnP in Hag1.
  assert (HVK1 : VK rho0 0 0 rho1) by (eapply VK_agree; [apply Pos.le_refl | apply VK_refl | exact Hag1]).
  eapply (etriple_entailsA segsA (KxA m B) NF E18 E18t []); [exact ent_18 | reflexivity | apply STx |].
  assert (HVK1' : VK rho0 0 0 (rho_sub rho1 [])) by (apply (VK_sub _ _ _ _ [] eq_refl); exact HVK1).
  set (rho1' := rho_sub rho1 []) in *.
  eapply etriple_seq; [apply (enode18 rho1' tp)|].
  assert (HVK2 : VK rho0 0 0 (rho_set_rw rho1' N18 (brk0w m))) by (apply VK_set_rw; [exact XN18 | exact HVK1']).
  apply (erun1 (KxA m B) FUEL_M CUTS_M S18 E19 RsCut _ tp); [exact run_18 | apply STx | exact Xl18 |].
  intros rho2 Hag2. rewrite Xn18 in Hag2.
  assert (HN18 : rw rho2 N18 = brk0w m) by (rewrite <- (proj1 Hag2 N18) by plia; apply rho_set_rw_at).
  assert (HVK3 : VK rho0 0 0 rho2) by (eapply VK_agree; [| exact HVK2 | exact Hag2]; plia).

  eapply etriple_seq; [apply (enode19_any m B Hres Hsb Hal Hlo Hhi HB Htop Hband rho2 tp HN18 (VK_sp _ _ _ _ _ HVK3 HSP0))|].
  apply etriple_disj.
  1:{
    apply etriple_ex. intros rho3. apply etriple_pure. intros Hceil. apply etriple_pure. intros Hfree. apply etriple_pure. intros (R1 & R2 & R3 & R4).
    assert (HN18' : rw rho3 N18 = brk0w m) by (rewrite R1; exact HN18).
    assert (HVK4 : VK rho0 brk0 (brk0 + 8192) rho3).
    { destruct HVK3 as [Hav Hrm]. split.
      - eapply agree_vals_trans; [exact Hav|]. split; [intros i Hi; symmetry; apply R1 | intros l; symmetry; apply R2].
      - intros x Hx. rewrite (R3 x) by (unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0; unfold brk0 in Hx; exact Hx). apply Hrm. lia. }
    apply (erun1 (KxA (mg m) (B + 8192)) FUEL_M CUTS_M S19g E20g RsCut rho3 tp); [exact run_19g | apply STx | exact Xl19g |].
    intros rho4 Hag4. rewrite Xn19g in Hag4.
    apply (eseg_grow rho0 tp rho4 HSP0).
    + rewrite <- (proj1 Hag4 N18) by plia. exact HN18'.
    + split; [unfold brk0; exact Hceil | exact Hfree].
    + exact Hwf.
    + eapply VK_agree; [| exact HVK4 | exact Hag4]. plia.
    + intros a Ha. rewrite <- (proj2 (proj2 Hag4)). apply R4. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0. unfold brk0 in Ha. lia. }
  apply (erun1 (KxA m B) FUEL_M CUTS_M S19f E20f RsCut rho2 tp); [exact run_19f | apply STx | exact Xl19f |].
  intros rho3 Hag3. rewrite Xn19f in Hag3.
  assert (HVK4 : VK rho0 0 0 rho3) by (eapply VK_agree; [| exact HVK3 | exact Hag3]; plia).

  eapply etriple_seq; [apply (enode20f_any okT OKF_triv OKP_triv m B Hres HB Htop Hband rho3 tp (VK_sp _ _ _ _ _ HVK4 HSP0))|].
  apply etriple_disj.
  -
    apply (erun1 (KxA m B) FUEL_M CUTS_M (refuse E20f) RET0a RsSymJump rho3 tp); [exact run_20f_fail | apply STx | exact Xl20r |].
    intros rho4 Hag4. rewrite Xn20r in Hag4.
    eapply etriple_entailsA; [exact ent_RET0a | exact wid_RET0a | apply STx |].
    assert (HVK5 : VK rho0 0 0 (rho_sub rho4 (post_sub RET0a []))).
    { apply (VK_sub _ _ _ _ _ wid_RET0a). eapply VK_agree; [| exact HVK4 | exact Hag4]. plia. }
    apply (epost_fin (KxA m B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK5)].
    intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK5)|].
    exists O0_refused. split; [exact I|]. split; [exact (proj2 HVK5)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
  -
    apply etriple_ex. intros a. apply etriple_pure. intros Hpl.
    assert (HVK5 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho20f rho3 a)).
    { unfold rho20f. apply VK_set_rw; [plia|]. apply VK_set_rm; [eapply VK_widen; [| exact HVK4]; intros z Hz; lia|].
      intros x Hx. apply unmap_range_outside. change (bv_unsigned n8w) with 8192. exact Hx. }
    apply (erun1 (KxA (mf_res m a) B) FUEL_M CUTS_M S20f E21f RsCut (rho20f rho3 a) tp); [exact run_20f | apply STx | exact Xl20 |].
    intros rho4 Hag4. rewrite Xn20 in Hag4.
    assert (Ha : rw rho4 (Pos.succ N18) = a) by (rewrite <- (proj1 Hag4 (Pos.succ N18)) by plia; unfold rho20f; apply rho_set_rw_at).
    assert (HVK6 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) rho4) by (eapply VK_agree; [| exact HVK5 | exact Hag4]; plia).

    eapply etriple_seq; [apply (enode21f_any okT OKF_triv OKP_triv m B Hres HB Htop Hband Hlz Hlim rho4 tp a Ha (VK_sp _ _ _ _ _ HVK6 HSP0) Hpl Htp)|].
    apply etriple_disj.
    +
      apply (erun1 (KxA (mf_res m a) B) FUEL_M CUTS_M (refuse E21f) RET0b RsSymJump rho4 tp); [exact run_21f_fail | apply STx | exact Xl21r |].
      intros rho5 Hag5. rewrite Xn21r in Hag5.
      eapply etriple_entailsA; [exact ent_RET0b | exact wid_RET0b | apply STx |].
      assert (HVK7 : VK rho0 (bv_unsigned a) (bv_unsigned a + 8192) (rho_sub rho5 (post_sub RET0b []))).
      { apply (VK_sub _ _ _ _ _ wid_RET0b). eapply VK_agree; [| exact HVK6 | exact Hag5]. plia. }
      apply (epost_fin (KxA (mf_res m a) B) P_null0 (JL_null0 m B)); [left; reflexivity | | exact (proj1 HVK7)].
      intros tr md (Htr & Hem & Hpaid). split; [reflexivity|]. split; [exact (proj1 HVK7)|].
      exists (O0_reserved a). split; [exact Hpl|]. split; [exact (proj2 HVK7)|]. split; [exact Htr|]. split; [exact Hem|]. lia.
    +
      apply (erun1 (KxA (mf_exp m a) (B + 4096)) FUEL_M CUTS_M S21f E22f RsCut rho4 tp); [exact run_21f | apply STx | exact Xl21 |].
      intros rho5 Hag5. rewrite Xn21 in Hag5.
      apply (etail_fail rho0 tp a rho5 HSP0 Hpl).
      * rewrite <- (proj1 Hag5 (Pos.succ N18)) by plia. exact Ha.
      * eapply VK_agree; [| exact HVK6 | exact Hag5]. plia.
Qed.

Theorem musl_malloc40_sum_ex : ltac2:(tb__ "0|0|
S5S14S21Q40A1A1S8cS4S2bS4S7cVm;VB;A2S93R2R1A5S6cS4S24R2R1S77Vm;VB;A2A5A3Ftp;Frho;").
Proof.
  intros rho tp w HP. destruct w as [tr [ms md]].
  pose proof HP as [(Hsm & HMI & _) ((Htr & Hem & Hpaid) & HSP0)].
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _).
  apply (musl_malloc40_main_ex rho tp); [| | exact HSP0 | exact (conj (proj1 HP) (proj1 (proj2 HP)))].
  - cbn [cfg_model snd] in HMI. intros p Hp. destruct (MI_tp_in_maps segsA _ _ HMI p Hp) as (Hal' & b & s0 & Hin & Hb). split; [exact Hal'|].
    exists b, s0. rewrite <- Evm. split; [exact Hin | exact Hb].
  - cbn [cfg_model snd] in HMI. rewrite <- Evm. exact (proj1 (MI_ivs_wf segsA _ _ HMI)).
Qed.
End Assembly.

Theorem musl_malloc40_sum_A : musl_malloc40_sum_stmt.
Proof. intros ok m B OKF OKP HM rho tp. exact (musl_malloc40_sum ok OKF OKP m B HM rho tp). Qed.

Theorem musl_malloc40_sum_ex_A : musl_malloc40_sum_ex_stmt.
Proof. intros m B HM rho tp. exact (musl_malloc40_sum_ex m B HM rho tp). Qed.
End MuslMalloc40.

