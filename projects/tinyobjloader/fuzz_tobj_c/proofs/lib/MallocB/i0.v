(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Placement.

(* [comment removed for export] *)
Module GlueMC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "opp"; "sub"; "to_nat"; "of_nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "cell"; "sv"; "rm"; "soff"; "eval"; "DUnknown"; "SLit"; "mkObj"; "ss_objs"; "sstate"; "valuation"; "c_width"; "c_off"; "mkSS"; "obj_holds"; "obj_range"; "ranges_disjoint"; "rom_ok"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "c_val"; "enc_bytes"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "nat"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC.WithSegs"; "gcells_in_view"; "gcells_inside"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "xwords_clear"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymFrame SymEntail SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition gcells_inside (rho : valuation) (lo hi : Z) (cs : list cell) : Prop := ltac2:(tb__ "0|2|
S3aSbSbS28S1Vlo;SeVrho;S17R1A1A2M0A2S28S1S0G0S16R1A1M1A2Vhi;A2S28S1Z1G1A2S1G1Z8A2A2A2A2Lc;Vcs;A3").

Definition gcells_in_view (rho : valuation) (rdv : word -> option byte) (b : Z) (cs : list cell) : Prop := ltac2:(tb__ "0|2|
S3aSbSbS39S48R1S6S16R2A1A1A2S29S34S2cQ8M0A1M1A1Vrdv;S2bQ40S0S0Vb;SeVrho;S17R3A1A2A2S7R2A1A2A2A1S33G1S3bG1R2S27S6S16R3A1A1SfVrho;S26R3A1A2A2S2bG0Z0A2A4A2A3F_;Fj;Lc;Vcs;A3").

Lemma obj_holds_frame_gen : ltac2:(tb__ "0|5|
S15S40S2cQ40M0A1S34S2cQ8A1M1A1M2F_;ScS8S8S31SbA1S1cVsegs;R6A2S2dG0SfR8R5A2A2S8S1S4S3Z2M3Z3eA2M4A1R5A2S1R6R5A2S2R6G4A2S1Z0S0R4R8A2A2S1S0R5R8A2S3G3Z40A2A2S3fReRaR9R8A4S8S28S1RcR1A2S2R1RbA2A2S28S29S30S2fVsegs;RfS2bG0S0R9R2A2A2A3S32A3S2aG1G1S29G2S2eVsegs;R10S2bG0S0RaR3A2A2A3S33G1R1A2A3Lx;A2A2F_;Foff;S3eR10S2eVsegs;ReA2R8RaA4S19Vsegs;R11S42R10RfA2S12ReS11RdA1S11RcA1RbS10A5A4F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;Fcs;Fhi;Flo;Fbase;Fm;Fms;Frho;").
Proof using .
  intros rho ms m base lo hi cs Hrom b Hlo Hlh Hhi Hb0 Hb1 Hins Hview Hcells.
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
  rewrite !soff_lit_small by lia.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. destruct (Hview off Hoff) as [W R]. exact (wview_of_views segs m _ W R). }
  split.
  { revert Hins Hcells. induction cs as [|c t IH]; intros Hins Hcells; [constructor|].
    apply Forall_cons_iff in Hins as [(Ho1 & Ho2 & Hk) Hins'].
    apply Forall_cons_iff in Hcells as [Hcv Hcells'].
    constructor; [|apply IH; assumption].
    unfold SymState.cell_holds.
    split; [lia|]. split; [lia|].
    apply rd_bytes_of_nth.
    - rewrite enc_bytes_length. reflexivity.
    - rewrite oaddr_unsigned by lia. fold b. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. fold b. rewrite (rd_with_mem segs) by exact Hrom.
      exact (Hcv j Hj). }
  split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. rewrite (rd_with_mem segs) by exact Hrom.
  destruct (Hview off Hoff) as [_ [x Hx]]. exists x. exact Hx.
Qed.

Lemma SPA_carve_gen : ltac2:(tb__ "0|4|
S3dS15S45S31S2cQ40M0A1A1S41ScS8S8S31SbA1S9S3cVsegs;RaR8R9R7R6A6S43R9A1S14S12R7S11R6A1S11R5A1R4S10A5SaS18S22R2A1S23R2A1S1fR2A1S1eR2A1S24R2A1S35SaS13R2A1S36SaR1S37SaA1A3A3S1dR2A1R4S20R2A1A9S14S29S30S25R1A1S32A3S47S21R4A1R6A2S2dG0SfRfRbA2A2S8S1S4S3Z2M1Z3eA2M2A1RbA2S1RcRbA2S2RcG2A2S1Z0S0R4ReA2A2S1S0R5ReA2S3G1Z40A2A2S3fR15R10RfReA4S3aSaSaS1bS1aR17R1A2S38S8S8S0R8R12A2S0R8R11A2A4A2Lo';S13RcA1A3S8S28S1R13R1A2S2R1R12A2A2S28S29S30S2fVsegs;SdR19A1S2bG0S0RaR2A2A2A3S32A3S2aS2cQ8A1M3G3S29S34G3A1S2eVsegs;SdR1aA1S2bG0S0RbR3A2A2A3S33G3R1A2A3Lx;A2A2F_;Foff;S3eR18S2eVsegs;SdR18A1A2R9R11A4S46R19R18S0RaR14A2S0RaR13A2A4S3cVsegs;R1bS44R19ReA2R1aR18R17A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';To;TS;F_;Fnx;Fcs;Fhi;Flo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w base lo hi cs nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S o S' Hwf' Hnx b Hs1 Hs2 Hs3 Hlo Hhi Hins Hdisj Hview Hcells Hxs.
  subst S. split; [|exact Hk].
  destruct w as [tr [ms md]].
  assert (Hrom : rom_ok segs (vms md tp ms)).
  { unfold virt in Hsm. cbn in Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). }
  assert (Hor : obj_range rho o = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi]. fold b. rewrite !soff_lit_small by lia. reflexivity. }
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_extend_objs segs rho (ax_S A) tr (vms md tp ms) (vmd md) [o] nx Hsm Hwf').
    + constructor; [|constructor]. apply obj_holds_frame_gen; auto.
    + constructor; [|constructor]. rewrite Hor. exact Hdisj.
    + cbn. split; [constructor | exact I].
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta. rewrite Hor. cbn [fst snd].
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

Lemma obj_holds_frame_gsym : ltac2:(tb__ "0|4|
S15S40S2cQ40M0A1S34S2cQ8A1M1A1M2F_;ScScScS31SbA1S1cVsegs;R6A2S2dG0SfR8R5A2A2S8SeR9R5A2S8SeRaR5A2S8S1R2R1A2S2S5R2R3A2S3Z2M3Z3fA2A2S1Z0S0R5R4A2A2S1S0R6R4A2S3G3Z40A2A2S3fRfR6R5R9A4S8S28S1R8R1A2S2R1R7A2A2S28S29S30S2fVsegs;R10S2bG0S0RaR2A2A2A3S32A3S2aG1G1S29G2S2eVsegs;R11S2bG0S0RbR3A2A2A3S33G1R1A2A3Lx;A2A2F_;Foff;S3eR11S2eVsegs;RfA2R9RbA4S19Vsegs;R12S42R11R10A2S12RfReRdRcS10A5A4F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;Fcs;Fehi;Felo;Fbase;Fm;Fms;Frho;").
Proof using .
  intros rho ms m base elo ehi cs Hrom b lo hi Hlh Hw Hb0 Hb1 Hins Hview Hcells.
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b. fold lo. fold hi.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. destruct (Hview off Hoff) as [W R]. exact (wview_of_views segs m _ W R). }
  split.
  { revert Hins Hcells. induction cs as [|c t IH]; intros Hins Hcells; [constructor|].
    apply Forall_cons_iff in Hins as [(Ho1 & Ho2 & Hk) Hins'].
    apply Forall_cons_iff in Hcells as [Hcv Hcells'].
    constructor; [|apply IH; assumption].
    unfold SymState.cell_holds.
    split; [lia|]. split; [lia|].
    apply rd_bytes_of_nth.
    - rewrite enc_bytes_length. reflexivity.
    - rewrite oaddr_unsigned by lia. fold b. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. fold b. rewrite (rd_with_mem segs) by exact Hrom.
      exact (Hcv j Hj). }
  split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. rewrite (rd_with_mem segs) by exact Hrom.
  destruct (Hview off Hoff) as [_ [x Hx]]. exists x. exact Hx.
Qed.

Lemma SPA_carve_gsym : ltac2:(tb__ "0|3|
S3dS15S45S31S2cQ40M0A1A1S41ScScScS31SbA1S9S3cVsegs;RaR8R9R7R6A6S43R9A1S14S12R7R6R5R4S10A5SaS18S22R2A1S23R2A1S1fR2A1S1eR2A1S24R2A1S35SaS13R2A1S36SaR1S37SaA1A3A3S1dR2A1R4S20R2A1A9S14S29S30S25R1A1S32A3S47S21R4A1R6A2S2dG0SfRfRbA2A2S8SeR10RbA2S8SeR11RbA2S8S1R2R1A2S2S5R2R3A2S3Z2M1Z3fA2A2S1Z0S0R5R4A2A2S1S0R6R4A2S3G1Z40A2A2S3fR16R6R5RfA4S3aSaSaS1bS1aR18R1A2S38S8S8S0R9R8A2S0R9R7A2A4A2Lo';S13RdA1A3S8S28S1R9R1A2S2R1R8A2A2S28S29S30S2fVsegs;SdR1aA1S2bG0S0RbR2A2A2A3S32A3S2aS2cQ8A1M2G2S29S34G2A1S2eVsegs;SdR1bA1S2bG0S0RcR3A2A2A3S33G2R1A2A3Lx;A2A2F_;Foff;S3eR19S2eVsegs;SdR19A1A2RaR12A4S46R1aR19S0RbRaA2S0RbR9A2A4S3cVsegs;R1cS44R1aRfA2R1bR19R18A6F_;F_;F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;F_;TS';To;TS;F_;Fnx;Fcs;Fehi;Felo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w base elo ehi cs nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S o S' Hwf' Hnx b lo hi Hlh Hw63 Hlo Hhi Hins Hdisj Hview Hcells Hxs.
  subst S. split; [|exact Hk].
  destruct w as [tr [ms md]].
  assert (Hrom : rom_ok segs (vms md tp ms)).
  { unfold virt in Hsm. cbn in Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). }
  assert (Hor : obj_range rho o = (b + lo, b + hi)) by reflexivity.
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_extend_objs segs rho (ax_S A) tr (vms md tp ms) (vmd md) [o] nx Hsm Hwf').
    + constructor; [|constructor]. apply obj_holds_frame_gsym; auto.
    + constructor; [|constructor]. rewrite Hor. exact Hdisj.
    + cbn. split; [constructor | exact I].
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta. rewrite Hor. cbn [fst snd].
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.
End WithSegs.
End GlueMC.

(* [comment removed for export] *)
Module IfaceTol.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "valuation"; "FcsrFrm0"; "mkSS"; "sprop"; "DUnknown"; "SLit"; "cell"; "mkObj"; "rw"; "rm"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "prod"; "list"; "app"; "nat"; "pair"; "None"; "false"; "option"; "Some"; "bool"; "true"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "cut_regs"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "free_depth"; "mkA"; "stack_win"; "JL_free"; "KcA"; "Kc_ok"; "V_FREE_A1"; "ae_free"; "pre_facts"; "J_free_pre"; "NPOSTM"; "UStopLe"; "V_TOP"; "ae_ret_free"; "pub_facts"; "ulink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.ContractsTol"; "tol_facts"; "J_free_tol_pre"; "L_free_tol"; "Pre_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "PRES"; "HB"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition PRES (segs : list Segment) (m : word -> option byte) (lo hi : Z) : Prop := ltac2:(tb__ "0|2|
S1dS23S29Vlo;R1A2S2bR1Vhi;A2A2S23S24S18S52Vsegs;Vm;S1bQ40M0R2A2A3S19A3S25S1aQ8A1M1G1S24S16G1A1S51Vsegs;Vm;S1bG0R3A2A3S17G1R1A2A3Lx;A2A2F_;Fa;").

Definition STK_SPAN : Z := 8388448.
Definition HBz (top : Z) : Z := page_round_up_Z (top + STK_SPAN).
Definition HB (rho : valuation) : Z := ltac2:(tb__ "0|0|
S43S1cQ40SbVrho;S39A2A2A1").

Lemma PRES_sub : ltac2:(tb__ "0|0|
S10S4cA1S1aQ40A1S16S1aQ8A1A1F_;S1dS1dS1dS1dS29R4R2A2S29R2R4A2S41R8R7R6R5A4S41R9R8R5R4A4F_;F_;F_;Fhi';Flo';Fhi;Flo;Fm;Fsegs;").
Proof. intros segs m lo hi lo' hi' H1 H2 H a Ha. apply H. lia. Qed.

Section ContractsTol.
Variable segs : list Segment.
Variable E : aentry.
Variable AInvA : ltac2:(tb__ "0|0|
S44S3S10S1aQ40A1A1S47OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Definition tol_facts : list sprop := chain_pre (Wcan 1).
Definition Pre_free_tol : axst := ltac2:(tb__ "0|1|
S2eS5S34VE;A1S21S20SeSfS12S0A2M0S13S12S0UbS2S33A1A4SdG0A1A3A2S1fS4S14S0A1SeS1S2fS11S1SeS1SaS2PcA1S8Z0A1S2PdA1SdS9A1S7A5SdS1A1A3S2cA3A3S11S6S3dS3bS2dA1A3S1eS15A9SdSfS0S0A2A1A2").
Definition Pre_free_tolI : axst := ltac2:(tb__ "0|1|
S2eS5S34VE;A1S21S20SeSfS12S0A2M0S13S12S0UbS2S33A1A4SdG0A1A3A2S1fS4S14S0A1SeS1S2fS11S1SeS1SaS2PcA1S8Z0A1S2PdA1SdS9A1S7A5SdS1A1A3S2cA3A3S11S6S3dS35S2dA1A3S1eS15A9SdSfS0S0A2A1A2").
Definition L_free_tol : axst := ltac2:(tb__ "0|0|
S2eS5S3aVE;A1S22S1eA1S1fS4S14S0A1SeS1S2fS2cA3S11S6S3dS35S2dA1A3S37S15A9SdSfS0S0A2A1A2").

Definition J_free_tol_pre (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S3S10S1aQ40M0A1A1S10S48A1S47S23S36VAInvA;SdS3cA1S38VA;VKc;R4R3R2R1A9S23S29S2aS46VA;A1S45VA;A1A2S53A2S41Vsegs;ScR4A1S1cG0SbR4PaA2A2S42R4A1A4A2A2Lmd;Ltr;Ltp;Lrho;").

Definition free_tol_contract : Prop := ltac2:(tb__ "0|1|
S4fOF_;S44S31S3S10S1aQ40A1A1S32R3A1S4bVsegs;R6S4aR4A1A3S50Vsegs;R7S4aR5A1A3S4eVsegs;R8S49Vsegs;S3eR7R6A2S40R5R4A5S28Vsegs;S1eR5R4SeSfS26S27A2M0S13S26S27S3fS30VAInvA;VCST;VXGL;R7R6A5A4SdG0A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition free_tol_contract_ex : Prop := ltac2:(tb__ "0|1|
S44S31S3S10S1aQ40A1A1S32R3A1S4dVsegs;S49Vsegs;S3eR5R4A2S40R3R2A5S28Vsegs;S1eR3R2SeSfS26S27A2M0S13S26S27S3fS30VAInvA;VCST;VXGL;R5R4A5A4SdG0A1A3A5A3F_;Ftp;Frho;FKc;FA;").
End ContractsTol.
End IfaceTol.

(* [comment removed for export] *)
Module CertStackFree.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "pair"; "prod"; "app"; "nat"; "None"; "false"; "true"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "sobj"; "SPUle"; "SVar"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "mkCell"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "F8"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "to_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "NW"; "cuts_sf"; "exits_sf"; "segsA"; "F_win"; "O_khigh"; "Post_sf"; "Pre_sf"; "gsv"; "shb"; "vG"; "win_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "IMG_HI"; "K_HIGH_MEM_END"; "@Corelib.Init.Logic"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.StackFree"; "F_sf"; "objs_sf"; "O_fshadow"; "f5_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "V_FL"; "mkA"; "A_globals"; "ae_ret_stack_free"; "ae_stack_free"; "flag_obj"; "flagbyte_obj"; "frame_obj"; "pre_facts"; "stack_malloc_depth"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition segsA : list Segment := AsanUbsan.M.loaded_segments.

Definition NW : positive := 200%positive.
Definition GW : positive := 160%positive.
Definition vG : positive := 150%positive.
Definition shb : sv := SLit SHADOW_OFF.

Definition gsv (e : sv) : sv := SAlu ALU_SRL e (SLit 3).

Definition khigh_cells : list (Z * nat * sv) := ltac2:(tb__ "0|4|
S0S4S4S16S6A2M0SdA2M1S3G0SdS3S16S6Zeeda0U8M2A4ScS2eA1A4S0G1S3G0SdS3S16S6Zeeda8G2A4ScZ0A1M3A4S0G1S3G0SdS3S16S6Zeedb0G2A4G3A4S1G1A1A3A3A3").
Definition O_khigh : sobj := carved (SLit 0) 0xeeda0 0xeedb8 khigh_cells.

Definition F_win (hi : bool) (e : sv) (sz : Z) : list sprop := ltac2:(tb__ "0|4|
S2SaSbA1Lhi;Vhi;S0SbSfScS2bA1Ve;A2S0SbSfVe;ScZ7fffff800000A1M0A2S0SbSfS11S1dVe;ScVsz;A1A3M1G0A2S1SbA1M2A3A3A3S0SbSfScS2dA1Ve;A2S0SbSfVe;ScS2cA1M3A2S0SbSfG1G3A2G2A3A3A3X2x2").
Definition win_hyp (hi : bool) (a len : Z) : Prop := ltac2:(tb__ "0|0|
S2OLhi;Vhi;S19S2bVa;A2S19S1aVa;Vlen;A2S2cA2X2x2").
Lemma win_hyp_cases : ltac2:(tb__ "0|0|
S16S16S31S19S1aR2R1A2S2cA2S19S2bR2A2A2S30S2S2S2aR1R4R3A3Lhi;A2F_;Flen;Fa;").
Proof. intros a len [H|H]; [exists false|exists true]; exact H. Qed.

Section StackFree.
Variable E : aentry.
Variable hi : bool.
Variable c : Z.
Let SZ : Z := fs_frame_size c.
Let NSH : Z := SZ / 8.

Definition O_fshadow (cs : list (Z * nat * sv)) : sobj := ltac2:(tb__ "0|0|
S46S11S1dS27S10PcA1A1S28A3Z0VNSH;Vcs;A4").

Definition F_sf : list sprop := ltac2:(tb__ "0|2|
S5SbS23Vhi;S10PcA1M0VSZ;A3S5SbS0SbSfScZ1000A1S10S3bA1M1A2S0SbSfS11S1dG1ScZ1A1A3ScZ7fffff800000A1A2S1SbA1A3A3S5SbS18S29G0A2S43S44A1A3A3A3").

Definition objs_sf (flagcells : list cell) (shcells : list (Z * nat * sv)) : list sobj := ltac2:(tb__ "0|3|
S5SeS0SeS45S0SeS42S10PcA1M0Vc;A2S0SeS40G0Vc;S10S3bA1M1A3S0SeS41G1Vflagcells;A2S1SeA1M2A3A3A3A3S5SeS3dS0SeS24S0SeS38Vshcells;A1G2A3A3A3A3").

Definition Pre_sf : axst := ltac2:(tb__ "0|0|
S3cS14S3fVE;Vc;A2S34S32S13S7SdA1S37S1S12A1S1S4S4S16S6A2SdA2A1A2S36S1fS8A9S1S4SdSdA2A1A2").

Definition F5W : Z := 0xf5f5f5f5f5f5f5f5.
Fixpoint f5_cells (k : nat) : list (Z * nat * sv) :=
  match k with O => [] | S k' => (8 * Z.of_nat k', 8%nat, SLit F5W) :: f5_cells k' end.
Definition Post_sf : axst := ltac2:(tb__ "0|1|
S3cS14S3eVE;Vc;A2S33S1eA1S32S13S7SdA1S37S0S12S15ScZ0A1M0Z1G0A3S1S12A1A3S39S1cS1bVNSH;Z8A2A1A1A2S36S1fS8A9S1S4SdSdA2A1A2").
End StackFree.

Definition cuts_sf (hi : bool) (c : Z) : list axst := ltac2:(tb__ "0|0|
S0S17S26S3aVhi;Vc;A3S1S17A1A3").
Definition exits_sf (hi : bool) (c : Z) : list axst := ltac2:(tb__ "0|0|
S0S17S25S3aVhi;Vc;A3S1S17A1A3").

Lemma cert_sf5 : ltac2:(tb__ "0|1|
S2S2fS2S35S22Uc8S1S16A1S1eS20R1Z5M0A2S21R1G0A2A6S9A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cert_sf6 : ltac2:(tb__ "0|1|
S2S2fS2S35S22U190S1S16A1S1eS20R1Z6M0A2S21R1G0A2A6S9A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertStackFree.

(* [comment removed for export] *)
Module Ledger.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "sub"; "of_nat"; "div"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "app"; "list"; "cons"; "snd"; "bool"; "fst"; "length"; "nat"; "Some"; "nil"; "option"; "pair"; "true"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "hwN"; "hwS"; "VCAP"; "GAPF"; "GN"; "apartW"; "live_hi"; "FBMAX"; "NBMAX"; "BETA1"; "QDEPK"; "maps_disjoint"; "ranges_apart"; "NLIM"; "Q1"; "SLIM"; "ledger"; "sepZ"; "GAPC"; "N0"; "QDEPF"; "QPIECES"; "S0"; "blocks_left"; "budget_boundD"; "gapN_ok"; "gapS_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_depot"; "aa_Km"; "aa_Kf"; "aa_V"; "aa_ptr_committed"; "dFB"; "dN"; "dNB"; "AA"; "budget_bound"; "dF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "gw_sizes"; "live_at"; "gap_weight"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "FBSZ"; "DEPC"; "NBSZ"; "dep_cost"; "dF_amort"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "acost"; "BETA_F"; "BETA_M"; "LIMIT"; "QMAX"; "QPRIM"; "U0"; "limit_ok_alloc"; "limit_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "kPtrArrayCommit"; "kUserMapSize"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "region_free"; "vm_maps"; "vm_reserved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Placement.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition BETA1 : Z := 1775.

Definition QPIECES : Z := ltac2:(tb__ "0|0|
S2Z1eS2Z2S0S57S5S57Z8A2A2A2A2").
Definition Q1 : Z := ltac2:(tb__ "0|0|
S0S0S0S0S31Z2404A2Z10000A2S2Z4S55A2A2S51A2").

Definition QDEPK : Z := 265.
Definition QDEPF : Z := 248.

Definition budget_boundD (A : AA) : Z := ltac2:(tb__ "0|0|
S0S0S0S0S0S52S4cS3aVA;A1A1A2S2S25S0S38VA;A1S39VA;A1A2A2A2S2aA2S3bVA;A1A2S48S37VA;A1A1A2").

Lemma budgetD_closes : ltac2:(tb__ "0|0|
S1S0S0S0S0S0S2aS26A2S30A2S46A2S56A2S2Z7S55A2A2S50A2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma BETA1_M : ltac2:(tb__ "0|0|
S1S0S0S25S26A2Z8A2S4eA2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma BETA1_F : ltac2:(tb__ "0|0|
S1S0S25S26A2S4dA2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Q1_nonneg : 0 <= Q1.
Proof. unfold Z.le. intro H. vm_compute in H. discriminate H. Qed.
Lemma BETA1_nonneg : 0 <= BETA1.
Proof. unfold BETA1. lia. Qed.

Lemma budgetD_le_budget : ltac2:(tb__ "0|4|
S3fS1S48S37R1A1M0A1S0S0S2Z10S3dG0A1A2S2Z8M1S41G0A1A2A2S46A2A2S49S37R2A1A1S1S3dS37R3A1A1S0S0S38R3A1S39R3A1A2Z1A2A2S18S1Z0M2S3bR4A1M3A2S1G3S0S2G1S38R4A1A2S56A2A2A2S1G2S38R5A1A2S1G2S39R6A1A2S1S34R7A1S40R7A1A2F_;F_;F_;F_;F_;F_;FA;").
Proof.
  intros A HC HF HN HP HKm HKf. unfold budget_boundD, budget_bound.
  pose proof (fblk_amort _ HF) as FA. destruct HF as (N1 & F0 & F1).
  pose proof budgetD_closes as CL. pose proof BETA1_M as BM. pose proof BETA1_F as BF.
  unfold QDEPK, QDEPF, PG in *.
  set (q1 := Q1) in *. set (qm := QMAX) in *. set (dc := DEPC) in *. set (pc := kPtrArrayCommit) in *.
  set (b1 := BETA1) in *. set (bm := BETA_M) in *. set (bf := BETA_F) in *. set (fb := fblk (dF (aa_depot A))) in *.
  clearbody q1 qm dc pc b1 bm bf fb. nia.
Qed.

Definition VCAP : Z := 4 * LIMIT / 7.
Definition NBMAX : Z := 4100.
Definition FBMAX : Z := 4100.
Definition GAPF : Z := 0x10007fff8000.
Definition GAPC : Z := 0x7fff7f800000.
Definition GN : Z := 64513.
Definition N0 : Z := 2 ^ 18.
Definition S0 : Z := 2 ^ 40.
Definition NLIM : Z := ltac2:(tb__ "0|0|
S0S0S0S0S2fS24A2S23A2S5S1eS20A2A2Z1A2").
Definition SLIM : Z := ltac2:(tb__ "0|0|
S0S0S0S32S2Z2S1eA2A2S2S47S24A2A2S2S45S23A2A2").

Definition MUK : Z := 2 ^ 20.

Lemma GAPF_eq : GAPF = Placement.SHADOW_BAND_HI. Proof. reflexivity. Qed.
Lemma GAPF_eqG : GAPF = Geometry.SHADOW_BAND_HI. Proof. reflexivity. Qed.
Lemma GAPC_eq : GAPC = alloc_ceiling_lo. Proof. reflexivity. Qed.
Lemma VCAP_acost : ltac2:(tb__ "0|0|
S6S1Z0R1A2S1S4cR2A1S4fA2S1R3S1eA2F_;F_;Fx;").
Proof.
  intros x Hx H. unfold acost, ALPHA_NUM, ALPHA_DEN, VCAP, LIMIT in *.
  pose proof (Z.div_mod (7 * x + 4 - 1) 4) as D1. pose proof (Z.mod_pos_bound (7 * x + 4 - 1) 4) as M1.
  pose proof (Z.div_mod (4 * 2 ^ 39) 7) as D2. pose proof (Z.mod_pos_bound (4 * 2 ^ 39) 7) as M2. lia.
Qed.
Lemma VCAP_limit_alloc : ltac2:(tb__ "0|2|
S6S6S6S6S1Z0M0S0R4R1A2A2S1G0R4A2M1G1S53R7R6R5R4A4S1S0R8R5A2S1eA2F_;F_;F_;F_;Fn;FKf;FKm;FV;").
Proof.
  intros V Km Kf n H0 HKm HKf H. unfold limit_ok_alloc, BETA_M, BETA_F in H.
  pose proof QMAX_nonneg. pose proof U0_nonneg. apply VCAP_acost; [exact H0 |]. set (q := QMAX) in *. set (u := U0) in *. clearbody q u. nia.
Qed.
Lemma VCAP_limit_free : ltac2:(tb__ "0|1|
S6S6S6S1Z0R3A2M0G0G0S54R6R5R4A3S1R7S1eA2F_;F_;F_;F_;FKf;FKm;FV;").
Proof.
  intros V Km Kf H0 HKm HKf H. unfold limit_ok_free, BETA_M, BETA_F in H.
  pose proof QMAX_nonneg. pose proof U0_nonneg. apply VCAP_acost; [exact H0 |]. set (q := QMAX) in *. set (u := U0) in *. clearbody q u. nia.
Qed.

Definition ledger (V : VmMaps) : list (word * word) := ltac2:(tb__ "0|1|
S8S7S15Q40A1M0G0A2S5aVV;A1S59VV;A1A3").

Definition live_hi (l : list (word * word)) : list (word * word) := List.filter (live_at GAPF) l.
Definition hwN (l : list (word * word)) : Z := Z.of_nat (length (live_hi l)).
Definition hwS (l : list (word * word)) : Z := gw_sizes (live_hi l).

Lemma gap_weight_hw : ltac2:(tb__ "0|1|
S6S9S7S15Q40A1M0G0A2A1S17S6S44R2S22R1A1A2S0S1dR1A1S2S1cR1A1S0R2ZfffA2A2A2A3Fl;FnZ;").
Proof. intros nZ l. unfold hwS, hwN. apply gap_weight_sizes. Qed.
Lemma live_hi_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17G2S22S8G1R2R1A3A1S8G1S22R2A1S22R1A1A3A3Fl2;Fl1;").
Proof. intros l1 l2. unfold live_hi. apply List.filter_app. Qed.
Lemma live_hi_cons : ltac2:(tb__ "0|4|
S7S15Q40A1M0G0A2M1S9G1A1M2S17G2S22SaG1R2R1A3A1S8G1ScG2L_;S43S1fR2A2SaG1R2S11G1A1M3A3G3Xcx2S22R1A1A3A3Fl;Fe;").
Proof. intros e l. unfold live_hi. cbn [List.filter]. destruct (live_at GAPF e); reflexivity. Qed.
Lemma gw_sizes_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17S6S42S8G1R2R1A3A1S0S42R2A1S42R1A1A2A3Fl2;Fl1;").
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn -[Z.add]; [lia | rewrite IH; lia]. Qed.
Lemma gw_sizes_nonneg : ltac2:(tb__ "0|1|
S9S7S15Q40A1M0G0A2A1S1Z0S42R1A1A2Fl;").
Proof. induction l as [|[b s] l IH]; cbn -[Z.add]; [lia|]. pose proof (bv_unsigned_in_range 64 s). lia. Qed.
Lemma hwN_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17S6S1cS8G1R2R1A3A1S0S1cR2A1S1cR1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold hwN. rewrite live_hi_app, length_app. lia. Qed.
Lemma hwS_app : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G2S17S6S1dS8G1R2R1A3A1S0S1dR2A1S1dR1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold hwS. rewrite live_hi_app. apply gw_sizes_app. Qed.
Lemma hwN_nonneg : ltac2:(tb__ "0|1|
S9S7S15Q40A1M0G0A2A1S1Z0S1cR1A1A2Fl;").
Proof. intros l. unfold hwN. lia. Qed.
Lemma hwS_nonneg : ltac2:(tb__ "0|1|
S9S7S15Q40A1M0G0A2A1S1Z0S1dR1A1A2Fl;").
Proof. intros l. unfold hwS. apply gw_sizes_nonneg. Qed.
Lemma hwN_cons : ltac2:(tb__ "0|2|
S7S15Q40A1M0G0A2M1S9G1A1S17S6S1cSaG1R2R1A3A1S0ScS6L_;S43S1fR2A2Z1Z0Xcx2S1cR1A1A2A3Fl;Fe;").
Proof. intros e l. unfold hwN. rewrite live_hi_cons. rewrite length_app. destruct (live_at GAPF e); cbn [length]; lia. Qed.
Lemma hwS_cons : ltac2:(tb__ "0|3|
S7S15Q40M0A1M1G1A2M2S9G2A1S17S6S1dSaG2R2R1A3A1S0ScS6L_;S43S1fR2A2S16G0SbG1G1R2A3A2Z0Xcx2S1dR1A1A2A3Fl;Fe;").
Proof. intros [b s] l. unfold hwS. rewrite live_hi_cons. rewrite gw_sizes_app. destruct (live_at GAPF (b, s)); cbn -[Z.add]; lia. Qed.

Lemma hwN_insert_le : ltac2:(tb__ "0|5|
S9S7S15Q40A1M0G0A2M1A1M2G1G2S18S1S1cS8G1R3R1A3A1M3S1cS8G1R3SaG1R2R1A3A3A1M4A2S1G4S0G3Z1A2A2A2Fl2;Fe;Fl1;").
Proof. intros l1 e l2. rewrite !hwN_app, hwN_cons. destruct (live_at GAPF e); lia. Qed.
Lemma hwS_insert_le : ltac2:(tb__ "0|6|
S9S7S15Q40M0A1M1G1A2M2A1M3G2G3S18S1S1dS8G2R3R1A3A1M4S1dS8G2R3SaG2R2R1A3A3A1M5A2S1G5S0G4S16G0SbG1G1R2A3A2A2A2A2Fl2;Fe;Fl1;").
Proof. intros l1 e l2. rewrite !hwS_app, hwS_cons. pose proof (bv_unsigned_in_range 64 (snd e)). destruct (live_at GAPF e); lia. Qed.

Lemma hwN_insert_low : ltac2:(tb__ "0|4|
S9S7S15Q40M0A1M1G1A2M2A1M3G2G3S1S0S16G0SdG1G1R2A3A2S16G0SbG1G1R2A3A2A2S1fA2S17S6S1cS8G2R4SaG2R3R2A3A3A1S1cS8G2R4R2A3A1A3F_;Fl2;Fe;Fl1;").
Proof.
  intros l1 [b s] l2 H. rewrite !hwN_app, hwN_cons. cbn [fst snd] in H.
  unfold live_at. cbn [fst snd]. destruct (GAPF <? bv_unsigned b + bv_unsigned s) eqn:E; [apply Z.ltb_lt in E; lia | lia].
Qed.
Lemma hwS_insert_low : ltac2:(tb__ "0|4|
S9S7S15Q40M0A1M1G1A2M2A1M3G2G3S1S0S16G0SdG1G1R2A3A2S16G0SbG1G1R2A3A2A2S1fA2S17S6S1dS8G2R4SaG2R3R2A3A3A1S1dS8G2R4R2A3A1A3F_;Fl2;Fe;Fl1;").
Proof.
  intros l1 [b s] l2 H. rewrite !hwS_app, hwS_cons. cbn [fst snd] in H.
  unfold live_at. cbn [fst snd]. destruct (GAPF <? bv_unsigned b + bv_unsigned s) eqn:E; [apply Z.ltb_lt in E; lia | lia].
Qed.

Definition blocks_left (A : AA) : Z := ltac2:(tb__ "0|1|
S0S3S24S4SeS6S3eS37VA;A1M0A1A2A1A2S3S23S4SeS6S3cG0A1A2A1A2A2").
Definition gapN_ok (A : AA) (V : VmMaps) : Prop := ltac2:(tb__ "0|0|
S1S0S0S2S20S1cS2cVV;A1A1A2S3S1eS3aVA;A1A2A2S2S20S33VA;A1A2A2S2S20S29A2A2").
Definition gapS_ok (A : AA) (V : VmMaps) : Prop := ltac2:(tb__ "0|1|
S1S0S0S0S1dS2cVV;A1A1S2Z2S3S1eS3aVA;A1A2A2A2S2S47S3S24S4SeS6S3eS37VA;A1M0A1A2A1A2A2A2S2S45S3S23S4SeS6S3cG0A1A2A1A2A2A2S2bA2").
Definition gap_ok (A : AA) (V : VmMaps) : Prop := ltac2:(tb__ "0|0|
S18S35VA;VV;A2S36VA;VV;A2A2").

Lemma GN_pays_chunk : ltac2:(tb__ "0|0|
S6S6S1S20R2A2S1R2S0R3Z3007A2A2S18S1S2S20Z1A2R4A2S1R3S2Z2R4A2A2A2F_;F_;Fms;Fn;").
Proof. intros n ms Hn Hms. unfold GN in *. lia. Qed.

Lemma gap_closes : ltac2:(tb__ "0|0|
S1S0S0S0S1fS45A2S2bA2S2S29S0S45ZfffA2A2A2S2eA2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition apartW (e1 e2 : word * word) : Prop := ltac2:(tb__ "0|4|
S19S1S0S16Q40M0SdS15G0A1M1G1Ve1;A3A2M2S16G0SbG1G1Ve1;A3A2A2S16G0SdG1G1Ve2;A3A2M3A2S1S0G3S16G0SbG1G1Ve2;A3A2A2G2A2A2").
Lemma apartW_sym : ltac2:(tb__ "0|2|
S7S15Q40A1M0G0A2M1G1S21R2R1A2S21R2R3A2F_;Fe2;Fe1;").
Proof. intros e1 e2 [H|H]; [right|left]; exact H. Qed.

Fixpoint ranges_apart (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | e :: r => Forall (apartW e) r /\ ranges_apart r
  end.
Definition maps_disjoint (l : list (word * word)) : Prop := ranges_apart l.

Lemma ranges_apart_app : ltac2:(tb__ "0|4|
S9S7S15Q40A1M0G0A2M1A1M2G2S1aS28S8G1R2R1A3A1S18S28R2A1S18S28R1A1G1G1S4aG1R2R4A3M3G3S21R4R3A2F_;F_;Fe2;Fe1;A2A2A2Fl2;Fl1;").
Proof.
  induction l1 as [|e l1 IH]; intros l2; cbn.
  - split; [intros H; split; [exact I|]; split; [exact H|]; intros e1 e2 [] | intros (_ & H & _); exact H].
  - rewrite Forall_app, IH. split.
    + intros ([F1 F2] & R1 & R2 & X). split; [split; [exact F1 | exact R1]|]. split; [exact R2|].
      intros e1 e2 [<-|H1] H2; [exact (proj1 (Forall_forall _ _) F2 e2 H2) | exact (X e1 e2 H1 H2)].
    + intros ([F1 R1] & R2 & X). split; [split; [exact F1|]|].
      * apply Forall_forall. intros e2 H2. apply X; [left; reflexivity | exact H2].
      * split; [exact R1|]. split; [exact R2|]. intros e1 e2 H1 H2. apply X; [right; exact H1 | exact H2].
Qed.

Lemma maps_disjoint_insert : ltac2:(tb__ "0|3|
S9S7S15Q40A1M0G0A2M1A1M2G1G2S27S8G1R3R1A3A1G1S4aG1R1S8G1R5R3A3A3S21R5R2A2F_;Fe';S27S8G1R5SaG1R4R3A3A3A1F_;F_;Fl2;Fe;Fl1;").
Proof.
  intros l1 e l2 H X. unfold maps_disjoint in *. apply ranges_apart_app in H as (R1 & R2 & Y).
  apply (proj2 (ranges_apart_app l1 (e :: l2))). split; [exact R1|]. split.
  - cbn. split; [|exact R2]. apply Forall_forall. intros e' H'. apply X. apply in_or_app. right. exact H'.
  - intros e1 e2 H1 [<-|H2]; [|exact (Y e1 e2 H1 H2)]. apply apartW_sym. apply X. apply in_or_app. left. exact H1.
Qed.
Lemma maps_disjoint_in : ltac2:(tb__ "0|4|
S9S7S15Q40A1M0G0A2M1A1SfSfG1G1S27R5A1S1bS17SfR5R4A3A1S17S12G1A1M2S4bG1R7R6A3S10G1R4A2M3A3S17G2S4bG1R8R6A3G3A3S21R6R5A2F_;F_;F_;F_;Fe2;Fe1;Fj;Fi;Fl;").
Proof.
  unfold maps_disjoint. induction l as [|e l IH]; intros i j e1 e2 H Hij H1 H2.
  - destruct i; discriminate H1.
  - cbn in H. destruct H as [F R]. destruct i as [|i], j as [|j]; cbn in H1, H2.
    + lia.
    + injection H1 as <-. apply nth_error_In in H2. exact (proj1 (Forall_forall _ _) F e2 H2).
    + injection H2 as <-. apply nth_error_In in H1. apply apartW_sym. exact (proj1 (Forall_forall _ _) F e1 H1).
    + apply (IH i j e1 e2 R ltac:(lia) H1 H2).
Qed.

Lemma apart_of_region_free : ltac2:(tb__ "0|2|
S9S7S15Q40A1M0G0A2M1A1G0G0S17ScS58R3R2R1A3S14A3G1S4aG1R1R5A3S21S13G0G0R5R4A4R2A2F_;Fe;F_;Fn;Fa;Fl;").
Proof.
  intros l a n H [b s] Hin. pose proof (region_free_In l a n b s H Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; unfold apartW; cbn [fst snd]; lia.
Qed.

Definition sepZ (r1 r2 : Z * Z) : Prop := ltac2:(tb__ "0|2|
S19S1S0SdS6S6Vr1;A3M0SbS6S6Vr1;A3A2SdS6S6Vr2;A3M1A2S1S0G1SbS6S6Vr2;A3A2G0A2A2").
Lemma sepZ_sym : ltac2:(tb__ "0|1|
S7S6S6A2M0G0S2dR2R1A2S2dR2R3A2F_;Fr2;Fr1;").
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.
End Ledger.

(* [comment removed for export] *)
Module SegD_cost.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "le"; "leb"; "div"; "min"; "modulo"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "sumZ"; "DEPC"; "dep_cost"; "depot_mem"; "depot_inv"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "dF"; "DG"; "dN"; "dFB"; "dFP"; "@Corelib.Init.Datatypes"; "bool"; "length"; "list"; "nat"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_wf.
Import ListNotations.
Open Scope Z_scope.

Lemma sumZ_firstn_S : ltac2:(tb__ "0|0|
S17S0A1S18S1eR1S16S0R2A2A2S1bS0S9SeS0S19R2A1R3A3A1S1S9SeS0R2R3A3A1SfS0R2R3Z0A4A2A3F_;Fn;Fl;").
Proof.
  induction l as [|x l IH]; intros [|n] Hn; cbn in Hn |- *; try lia.
  - unfold sumZ. cbn. destruct l; cbn; lia.
  - unfold sumZ in *. cbn. specialize (IH n ltac:(lia)). cbn in IH. rewrite IH. lia.
Qed.

Lemma sumZ_firstn_all : ltac2:(tb__ "0|0|
S17S0A1S1bS0S9SeS0S16S0R1A2R1A3A1S9R1A1A3Fl;").
Proof. intros l. rewrite firstn_all. reflexivity. Qed.

Lemma pages_prefix_bound : ltac2:(tb__ "0|6|
S11S1cS18ScR3R2A2S1dR2S16S0S13R4A1A2A2S5S10R5A1Z100000M0A2S0S3S2S1aS9SeS0R4S14R6A1A3A1A2S1S1S2S2Z8M1G0A2S6S8R4A1M2R1A2A2S15S0L_;M3S4G2R1A2Z0M4S1S1S2G1S7S10R6A1G0A2A2S1aA2Zf8M5A2X15x2A2G3S4G2S1R1Z1A2A2G4S1S1aG5A2X15x2A2A2Tq;F_;F_;Fn;Fm;FG;").
Proof.
  intros G m n HM Hn q. pose proof (dm_F _ _ HM) as (F0 & _ & F32 & _). pose proof (dm_fb_len _ _ HM) as [[L1 L2] HL].
  pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MB.
  assert (FB : fblk (dF G) <= q + 1).
  { unfold fblk, q. assert ((dF G + 1048576 - 1) / 1048576 < dF G / 1048576 + 1 + 1) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hq0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  induction n as [|n IH].
  - change (firstn 0 (dFP G)) with (@nil Z). change (Z.of_nat 0) with 0. unfold sumZ. cbn [fold_right]. rewrite Z.min_l by lia.
    replace (0 <=? q) with true by (symmetry; apply Z.leb_le; lia). replace (0 <=? q + 1) with true by (symmetry; apply Z.leb_le; lia). unfold PG. lia.
  - specialize (IH ltac:(lia)). rewrite sumZ_firstn_S by (rewrite HL; lia). rewrite Z.mul_add_distr_l.
    destruct (dm_fp _ _ HM n ltac:(lia)) as [[P0 P1] _]. pose proof (dm_fp_hi _ _ HM n ltac:(lia)) as PH.
    destruct (Z_lt_le_dec (Z.of_nat n) q) as [C1|C1].
    +
      rewrite (Z.min_l (Z.of_nat (S n))) by lia. rewrite Z.min_l in IH by lia.
      replace (Z.of_nat (S n) <=? q) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat (S n) <=? q + 1) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat n <=? q) with true in IH by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat n <=? q + 1) with true in IH by (symmetry; apply Z.leb_le; lia).
      unfold FBPAGES, PG in *. nia.
    + destruct (Z.eq_dec (Z.of_nat n) q) as [C2|C2].
      *
        rewrite (Z.min_r (Z.of_nat (S n))) by lia. rewrite Z.min_l in IH by lia.
        replace (Z.of_nat (S n) <=? q) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat (S n) <=? q + 1) with true by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat n <=? q) with true in IH by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat n <=? q + 1) with true in IH by (symmetry; apply Z.leb_le; lia).
        rewrite C2 in PH. unfold q in PH. unfold PG in *. nia.
      *
        assert (C3 : Z.of_nat n = q + 1) by lia.
        rewrite (Z.min_r (Z.of_nat (S n))) by lia. rewrite Z.min_r in IH by lia.
        replace (Z.of_nat (S n) <=? q) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat (S n) <=? q + 1) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat n <=? q) with false in IH by (symmetry; apply Z.leb_gt; lia).
        replace (Z.of_nat n <=? q + 1) with true in IH by (symmetry; apply Z.leb_le; lia).
        rewrite C3 in PH. unfold q in PH. unfold PG in *. nia.
Qed.

Theorem dep_cost_bound_mem : ltac2:(tb__ "0|0|
S11S1cScR2R1A2S3SbR3A1S1S1S2Z10S12R3A1A2S2Z8S10R3A1A2A2SaA2A2F_;Fm;FG;").
Proof.
  intros G m HM. pose proof (dm_F _ _ HM) as (F0 & _ & F32 & _). pose proof (dm_N _ _ HM) as [[N1 N2] _].
  pose proof (dm_fb_len _ _ HM) as [[L1 L2] HL]. pose proof (dm_map1_len _ _ HM) as [M1 M2].
  pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MB.
  pose proof (pages_prefix_bound G m (length (dFB G)) HM ltac:(lia)) as P. cbn zeta in P.
  rewrite <- HL, sumZ_firstn_all in P. rewrite HL in P.
  unfold dep_cost, dep_pages, DEPC.
  assert (NB : NBSZ * Z.of_nat (length (dNB G)) <= 16 * dN G + 16 + NBSZ).
  { unfold nblk in M2. destruct (Z.eqb_spec (dN G + 1) 0); [lia|].
    pose proof (Z.div_mod (dN G + 1) 65536 ltac:(lia)). pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)). unfold NBSZ. nia. }
  assert (FP : PG * sumZ (dFP G) <= 8 * dF G + 2 * PG + 496).
  { pose proof (Z.le_min_r (Z.of_nat (length (dFB G))) (dF G / 1048576)) as MR.
    destruct (Z.of_nat (length (dFB G)) <=? dF G / 1048576); destruct (Z.of_nat (length (dFB G)) <=? dF G / 1048576 + 1); unfold PG in *; nia. }
  unfold PG, NBSZ in *. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Theorem dep_cost_bound : ltac2:(tb__ "0|0|
S11S20S1fS17S21Q40A1A1SdVsegs;R4R3R2R1A5S3SbR5A1S1S1S2Z10S12R5A1A2S2Z8S10R5A1A2A2SaA2A2F_;Ftp;Fmd;Frho;FG;").
Proof. intros G rho md tp [HM _]. exact (dep_cost_bound_mem G _ HM). Qed.
End WithSegs.
End SegD_cost.

(* [comment removed for export] *)
Module CallocArith.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.Riscv.Sem"; "mul_div"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "M_MULHU"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "lt"; "div"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "eval"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "calloc_size"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Iface.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation word := (bv 64).
Local Notation U := bv_unsigned.

Lemma urange64 : ltac2:(tb__ "0|2|
S1Q40M0A1S4S8Z0S0G0R1A2M1A2SbG1SaZ2Z40A2A2A2Fx;").
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

Lemma mul_word_comm : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S3G1S2G0S6R2R1A4S2G0S6R1R2A4A3Fy;Fx;").
Proof. intros x y. apply bv_eq. rewrite !mul_val. f_equal. lia. Qed.

Lemma mulhu_val : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S3SdS0G0S2G0S7R2R1A4A2ScS9S0G0R2A2S0G0R1A2A2SaZ2Z40A2A2A3Fy;Fx;").
Proof.
  intros x y. unfold mul_div, bv_mulhuu. pose proof (urange64 x) as Hx. pose proof (urange64 y) as Hy.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (Z.of_N 64) with 64.
  rewrite Z.shiftr_div_pow2 by lia. apply Z.mod_small. split; [apply Z.div_pos; nia|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma mulhu_zero_iff : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S5S3SdS0G0S2G0S7R2R1A4A2Z0A3SbS9S0G0R2A2S0G0R1A2A2SaZ2Z40A2A2A2Fy;Fx;").
Proof.
  intros x y. rewrite mulhu_val. pose proof (urange64 x) as Hx. pose proof (urange64 y) as Hy. split.
  - intros H. apply Z.div_small_iff in H; [|lia]. destruct H as [H|H]; lia.
  - intros H. apply Z.div_small. nia.
Qed.

Lemma mul_exact : ltac2:(tb__ "0|3|
S1Q40M0A1M1G1SbS9S0G0R2A2M2S0G0R1A2A2SaZ2Z40A2A2S3SdS0G0S2G0S6R3R2A4A2S9S0G0R3A2G2A2A3F_;Fy;Fx;").
Proof. intros x y H. rewrite mul_val. pose proof (urange64 x). pose proof (urange64 y). apply Z.mod_small. nia. Qed.

Lemma mul_pos_factors : ltac2:(tb__ "0|3|
S1Q40M0A1M1G1S8Z1M2S0G0S2G0S6R2R1A4A2A2S4S8G2S0G0R3A2A2S8G2S0G0R2A2A2A2F_;Fy;Fx;").
Proof.
  intros x y H. rewrite mul_val in H. pose proof (urange64 x) as Hx. pose proof (urange64 y) as Hy.
  destruct (Z.eq_dec (U x) 0) as [E|E]; [rewrite E in H; cbn in H; lia|].
  destruct (Z.eq_dec (U y) 0) as [E'|E']; [rewrite E', Z.mul_0_r in H; cbn in H; lia|]. lia.
Qed.

Lemma calloc_size_val : ltac2:(tb__ "0|1|
S10S3S1Q40M0A1SfR1S11A2S2G0S6SeR1PcA2SeR1PdA2A4A3Frho;").
Proof. intros rho. reflexivity. Qed.
End CallocArith.

