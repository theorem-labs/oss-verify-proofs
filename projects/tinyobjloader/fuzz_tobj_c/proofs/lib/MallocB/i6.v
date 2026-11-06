(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4 i2.
From stdpp Require base list.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.

(* [comment removed for export] *)
Module GlueMU.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "rm"; "soff"; "ss_objs"; "sstate"; "DUnknown"; "cell"; "eval"; "mkObj"; "mkSS"; "obj_range"; "ranges_disjoint"; "smatch"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "valuation"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Init.Datatypes"; "bool"; "nil"; "pair"; "true"; "Some"; "app"; "cons"; "list"; "option"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "xwords_clear"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma smatch_carve_unk : ltac2:(tb__ "0|4|
S1dScS29S37A1M0S35S36S8S8S8S1S14Vsegs;R9R8S24G0S2fR7S30R6R5A2A4A4S11S19R9A1S1aR9A1S17R9A1S16R9A1S1bR9A1S27S7SbR9A1S28S7S10R5R4R3S23SeA1SdA5S23S7A1A3A3S15R9A1R2S18R9A1A9ScS1fS22S1cR1A1S25A3S2dQ40M1SfRcR7A2A2S0SaRdR7A2S0SaReR7A2S0S3R2R1A2S4S6R2R3A2S5Z2M2Z3fA2A2S3Z0S2R5R4A2A2S3S2R6R4A2S5G2Z40A2A2S2eS7S7S13S12R14R1A2S24S0S0S2R8R7A2S2R8R6A2A4A2Lo';SbR12A1A3S0S20S3S2R9R8A2R1A2S4R1S2R9R7A2A2A2S20S1fS22S34Vsegs;S9R16A1S2bG1R2A2A3S25A3S21S2cQ8A1M3G3S1fS2aG3A1S33Vsegs;S9R17A1S2bG1R3A2A3S26G3R1A2A3Lx;A2A2F_;Fa;S14Vsegs;R15RbS24G0S2fR13S30R12R11A2A4A4F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;TS';F_;Fnx;Fehi;Felo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md base elo ehi nx Hsm S' Hwf' b lo hi Hs1 Hs2 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base elo ehi [] DUnknown).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)) by reflexivity.
  assert (Hout : forall a, b + lo <= a < b + hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. apply Forall_forall. intros o Ho. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite u64_lit by lia. lia. }
  assert (MEM : forall a, b + lo <= a < b + hi -> ms_mem ms (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)).
  { intros a Ha. exact (Hfr _ (Hout a Ha)). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    subst newo. unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. fold lo. fold hi.
    split; [lia|]. split.
    { intros off Hoff _. destruct (Hbytes (b + off) ltac:(lia)) as [Hw Hb].
      unfold wview. rewrite (MEM (b + off)) by lia.
      pose proof (wview_of_views segs (rm rho) (Z_to_bv 64 (b + off)) Hw Hb) as X. unfold wview in X. exact X. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEM (b + off)) by lia.
    destruct (Hbytes (b + off) ltac:(lia)) as [_ [x Hb]]. unfold rd_of in Hb.
    destruct (rm rho (Z_to_bv 64 (b + off))) as [y|]; [exists y; reflexivity|].
    exists x. rewrite <- Hb. first [apply Hrom | symmetry; apply Hrom].
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. first [rewrite Hnr | subst newo; rewrite Hnr]. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_unk : ltac2:(tb__ "0|5|
S32S1dS3bS29S2cQ40M0A1A1S38S8S8S8S1S31Vsegs;R9R7R8R6R5A6S39R8A1ScS11S19R1A1S1aR1A1S17R1A1S16R1A1S1bR1A1S27S7SbR1A1S28S7S10R6R5R4S23SeA1SdA5S23S7A1A3A3S15R1A1R3S18R1A1A9ScS1fS22S1cR1A1S25A3S3dS1eR3A1R5A2S2dG0SfRdR9A2A2S0SaReR9A2S0SaRfR9A2S0S3R2R1A2S4S6R2R3A2S5Z2M1Z3fA2A2S3Z0S2R5R4A2A2S3S2R6R4A2S5G1Z40A2A2S2eS7S7S13S12R15R1A2S24S0S0S2R8R7A2S2R8R6A2A4A2Lo';SbRbA1A3S0S20S3S2R9R8A2M2R1A2S4R1S2R9R7A2M3A2A2S20S1fS22S34Vsegs;S9R17A1S2bG0R2A2A3S25A3S21S2cQ8A1M4G4S1fS2aG4A1S33Vsegs;S9R18A1S2bG0R3A2A3S26G4R1A2A3Lx;A2A2F_;Fa;S3cR16R15G2G3A4S31Vsegs;R18S3aR16RdA2R17R15R14A6F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;F_;TS';TS;F_;Fnx;Fehi;Felo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp [tr [ms md]] base elo ehi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hnx b lo hi Hs1 Hs2 Hlo Hhi Hdisj Hbytes Hxs.
  subst S' S. split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_unk rho (ax_S A) tr (vms md tp ms) (vmd md) base elo ehi nx Hsm Hwf' Hs1 Hs2 Hlo Hhi Hdisj Hbytes).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    change (obj_range rho (mkObj base elo ehi [] DUnknown)) with (b + lo, b + hi). cbn [fst snd].
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.
End WithSegs.
End GlueMU.

(* [comment removed for export] *)
Module SegD_glue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "rm"; "sstate"; "obj_range"; "ss_objs"; "SLit"; "eval"; "rw"; "sprop"; "smatch"; "SVar"; "holds"; "ss_facts"; "ss_regs"; "mkSS"; "rl"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_resv"; "sv_below"; "swf"; "cell"; "mkObj"; "ranges_disjoint"; "DUnknown"; "agree_below"; "DZero"; "enc_bytes"; "image_byte"; "ob_base"; "ob_hi"; "ob_lo"; "obj_holds"; "obj_wf"; "sprop_eqb"; "ss_next"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "bool"; "true"; "nil"; "fst"; "nat"; "option"; "app"; "cons"; "snd"; "None"; "Some"; "negb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "lt"; "of_nat"; "opp"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "existsb"; "NoDup"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_X"; "ax_S"; "ax_base"; "ax_setS"; "axwf"; "shadow_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue.SG"; "ro_win"; "skel"; "rho_sets"; "notin_b"; "notin_vars"; "inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "carved"; "cells_in_view"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "F_sp_high"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "obj_vars_all"; "@Stdlib.PArith.BinPos.Pos"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "win"; "win_bytes_in_frame"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SG.
Variable segs : list Segment.

Fixpoint rho_sets (rho : valuation) (bs : list (positive * word)) : valuation :=
  match bs with
  | [] => rho
  | (v, x) :: rest => rho_sets (mkVal (fun i => if Pos.eqb i v then x else rw rho i) (rl rho) (rm rho)) rest
  end.

Lemma rho_sets_rl_rm : ltac2:(tb__ "0|3|
S2eS2fS2dS43Q40A1M0A2A1S6S1S0S2dS2eS43Q8A1M1A1F_;S15S62R1R2A2M2A1S15R1A1A3S0G0S36G1A1F_;S7G2A1S7R1A1A3A2Frho;Fbs;").
Proof.
  induction bs as [|[v x] rest IH]; intros rho; cbn; [split; reflexivity|].
  destruct (IH (mkVal (fun i => if Pos.eqb i v then x else rw rho i) (rl rho) (rm rho))) as [A B]. cbn in A, B. rewrite A, B. split; reflexivity.
Qed.

Lemma rho_sets_other : ltac2:(tb__ "0|2|
S2eS2fS2dS43Q40A1M0A2M1A1S6S2dS2S49S2dR1S52G1S2dS34S2dG0A2R3A4A3A1S0G0SdS62R3R4A2R2A2SdR3R2A2A3F_;Fi;Frho;Fbs;").
Proof.
  induction bs as [|[v x] rest IH]; intros rho i Hn; cbn; [reflexivity|]. cbn in Hn.
  rewrite IH; [|tauto]. cbn. destruct (Pos.eqb_spec i v); [subst; tauto | reflexivity].
Qed.

Definition notin_b (bs : list (positive * word)) (v : positive) : bool := ltac2:(tb__ "0|2|
S3cS4aS2fS2dS43Q40A1M0A2M1G1S75S34S2dG0R1A3Vv;A2Lb;Vbs;A3A1").

Lemma notin_b_true : ltac2:(tb__ "0|2|
S2eS2fS2dS43Q40A1M0A2M1A1S2dS0S31S63R2R1A2S32A3S2S49S2dR2S52G1S2dS34S2dG0A2R3A4A3A1F_;Fv;Fbs;").
Proof.
  intros bs v H Hin. unfold notin_b in H. apply Bool.negb_true_iff in H.
  apply in_map_iff in Hin as ([v' x] & E & Hin). cbn in E. subst.
  assert (existsb (fun b : positive * word => (fst b =? v)%positive) bs = true); [|congruence].
  apply existsb_exists. exists (v, x). split; [exact Hin|]. cbn. apply Pos.eqb_refl.
Qed.

Lemma SPA_bindX : ltac2:(tb__ "0|3|
S4fS2dS59S6S2eS43Q40A1M0A1S70S2eS2fS2dG0A2M1A1S0S2eS2fS4S4A2M2A1S5aR5A1S33G2A1A3S50Vsegs;R7R8A3S2dS49S2dR1S52G1S2dS34S2dG0A2R4A4A3S74RaR2A2F_;Fv;S0S31S71S63R4A1S5bR8A1A2S32A3S0S31S72S63R5A1S5cR9A1A2S32A3S4eVsegs;RcRaR9R8R7A6S4eVsegs;RdRbS62RaR7A2R9R8A6F_;F_;F_;F_;F_;F_;Fbs;Fw;Ftp;Frho;FA;Fn;FJ;").
Proof using .
  intros J n A rho tp [tr [ms md]] bs HX Hst Hge Hvars Hbase [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  destruct (rho_sets_rl_rm bs rho) as [Hrl Hrm].
  assert (AG : agree_below n rho (rho_sets rho bs)).
  { split; [|split; [intros l; rewrite Hrl; reflexivity | intros a; rewrite Hrm; reflexivity]].
    intros i Hi. symmetry. apply rho_sets_other. intros Hin. specialize (Hge i Hin). lia. }
  split.
  - split; [|split; [exact HMI | split; [exact Hwf | split; [|exact Hhz]]]].
    + eapply (smatch_agree_vars segs (notin_b bs)); [| | | exact Hvars | exact Hsm].
      * intros v Hv. symmetry. apply rho_sets_other. apply notin_b_true. exact Hv.
      * intros l. rewrite Hrl. reflexivity.
      * rewrite Hrm. reflexivity.
    + unfold shadow_ok in *. rewrite HX. constructor.
  - cbn [w_tr w_cfg cfg_model] in *. eapply Hst; [exact AG | apply mat_equiv_refl | exact Hk].
Qed.

Lemma axwf_setS_nilX : ltac2:(tb__ "0|1|
S59S8S0S2eS2fS4S4A2M0A1S5aR2A1S33G0A1A3S0S31S1bS2bR2A1S5cR3A1A2S32A3S0S31S5eS5dR4R3A2A1S32A3F_;F_;FS';FA;").
Proof. intros A S' HX Hb. unfold axwf. cbn. rewrite HX. cbn. exact Hb. Qed.

Lemma shadow_ok_nilX : ltac2:(tb__ "0|1|
S6S59S8S0S2eS2fS4S4A2M0A1S5aR2A1S33G0A1A3S5fR4S5dR3R2A2A2F_;FS';FA;Frho;").
Proof. intros rho A S' HX. unfold shadow_ok. cbn. rewrite HX. constructor. Qed.

Lemma SPA_carve_winX : ltac2:(tb__ "0|6|
S4fS59S6S2eS43Q40M0A1A1S2eS55A1M1S54S56S4S2cS35S4S2dS0S2eS2fS4S4A2M2A1S5aRbA1S33G2A1A3S4eVsegs;RdRcRbRaS30G1S47R9S48R8R7A2A4A6S5bRdA1S8S14S19R1A1S13R1A1S17R1A1S16R1A1S1aR1A1S37S5SaR1A1S38S5S76R8R7R6R5A4S33S5A1A3A3S12R1A1R4S18R1A1A9S8S0S31S1cR1A1S32A3S0S31S1bR6S5cR10A1A2S32A3S44G0ScR10RbA2A2S2cS3eS42S3fZ2M3Z3fA2M4A1RbA2S40S3dRcS41RbA1A2G4A2S6eRcU8A2S3eZ0S3dR4ReA2A2S3eS3dS3dR5RfA2S41ReA1A2S3fG3Z40A2A2S51S5S5S1fS9R17R1A2S30S2cS2cS3dR7R11A2M5S3dG5S41R10A1A2A4A2Lo';SaRaA1A3S77R17R7R11R10ScR17RfA2A5S4eVsegs;R1aS5dR19RbA2R18R17S30G1S47R16S48R15R14A2A4A6F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';TS;F_;F_;Fnx;Fv;Fk;Foff;Fbase;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp tr ms md base off k v nx HX [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hb b Ho1 Ho2 Hk8 Hlo Hhi Hdisj Hbytes.
  split; [|exact Hk]. split; [|split; [exact HMI | split; [apply axwf_setS_nilX; assumption | split; [apply shadow_ok_nilX; exact HX | exact Hhz]]]].
  unfold virt in *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in *.
  exact (smatch_carve_win segs rho S _ base off k v nx Hsm Hwf' Ho1 Ho2 Hk8 Hlo Hhi Hdisj Hbytes).
Qed.

Lemma smatch_carve_unk : ltac2:(tb__ "0|5|
S6S8S2eS55A1M0S54S56S4S2cS2cS2dSfVsegs;R9R8S30G0S47R7S48R6R5A2A4A4S14S19R9A1S13R9A1S17R9A1S16R9A1S1aR9A1S37S5SaR9A1S38S5S1eR5SbR4A1SbR3A1S33S1dA1S20A5S33S5A1A3A3S12R9A1R2S18R9A1A9S8S0S31S1cR1A1S32A3S44Q40M1ScRcR7A2A2S2cS3eZ0M2R7A2S1S3eR8R7A2S40R7S3fZ2M3Z3fA2A2A2S3eG2S3dR3R9A2A2S3eS3dR4R9A2S3fG3Z40A2A2S51S5S5S1fS9R12R1A2S30S2cS2cS3dR6RcA2S3dR6RbA2A4A2Lo';SaR10A1A3S2cS1S3eS3dR7RdA2R1A2S40R1S3dR7RcA2A2A2S2S0S36S43Q8A1M4A1S7R14S45G1R2A2A2S3aG4A1A3A1F_;Fa;SfVsegs;R13R9S30G0S47R11S48R10RfA2A4A4F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md base lo hi nx Hsm S' Hwf' b Hs1 Hs2 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base (SLit lo) (SLit hi) [] DUnknown).
  assert (Hlo' : soff rho (SLit lo) = lo) by (rewrite soff_lit_small; lia).
  assert (Hhi' : soff rho (SLit hi) = hi) by (rewrite soff_lit_small; lia).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi]. rewrite Hlo', Hhi'. reflexivity. }
  assert (Hout : forall a, b + lo <= a < b + hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. apply Forall_forall. intros o Ho. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite u64_lit by lia. lia. }
  assert (MEM : forall a, b + lo <= a < b + hi -> exists byt, ms_mem ms (Z_to_bv 64 a) = Some byt).
  { intros a Ha. rewrite (Hfr _ (Hout a Ha)). destruct (rm rho (Z_to_bv 64 a)) eqn:E; [eexists; reflexivity|]. exfalso. exact (Hbytes a Ha E). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. rewrite Hlo', Hhi'.
    split; [lia|]. split.
    { intros off Hoff _. unfold wview. destruct (MEM (b + off)) as [byt Hb]; [lia|]. rewrite Hb. discriminate. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. destruct (MEM (b + off)) as [byt Hb]; [lia|]. rewrite Hb. eexists; reflexivity.
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. fold newo. rewrite Hnr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_unkX : ltac2:(tb__ "0|6|
S4fS59S6S2eS43Q40M0A1A1S2eS55A1M1S54S56S4S2cS2cS2dS0S2eS2fS4S4A2M2A1S5aRaA1S33G2A1A3S4eVsegs;RcRbRaR9S30G1S47R8S48R7R6A2A4A6S5bRcA1S8S14S19R1A1S13R1A1S17R1A1S16R1A1S1aR1A1S37S5SaR1A1S38S5S1eR7SbR6A1SbR5A1S33S1dA1S20A5S33S5A1A3A3S12R1A1R4S18R1A1A9S8S0S31S1cR1A1S32A3S0S31S1bR6S5cRfA1A2S32A3S44G0ScRfRaA2A2S2cS3eZ0M3RaA2S1S3eRbRaA2S40RaS3fZ2M4Z3fA2A2A2S3eG3S3dR3RcA2A2S3eS3dR4RcA2S3fG4Z40A2A2S51S5S5S1fS9R15R1A2S30S2cS2cS3dR6RfA2S3dR6ReA2A4A2Lo';SaR9A1A3S2cS1S3eS3dR7R10A2R1A2S40R1S3dR7RfA2A2A2S2S0S36S43Q8A1M5A1S7R17S45G0R2A2A2S3aG5A1A3A1F_;Fa;S4eVsegs;R18S5dR17RaA2R16R15S30G1S47R14S48R13R12A2A4A6F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';TS;F_;F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp tr ms md base lo hi nx HX [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hb b Hs1 Hs2 Hlo Hhi Hdisj Hbytes.
  split; [|exact Hk]. split; [|split; [exact HMI | split; [apply axwf_setS_nilX; assumption | split; [apply shadow_ok_nilX; exact HX | exact Hhz]]]].
  unfold virt in *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in *.

  exact (smatch_carve_unk rho S _ _ _ base lo hi nx Hsm Hwf' Hs1 Hs2 Hlo Hhi Hdisj Hbytes).
Qed.

Lemma SPA_release_winX : ltac2:(tb__ "0|7|
S4fS59S6S2eS43Q40M0A1A1S2eS55A1M1S54S56S2eS5A1M2S4S2cS35S4S2dS0S2eS2fS4S4A2M3A1S5aRcA1S33G3A1A3S4eVsegs;ReRdRcRbS30G1S47RaS48R9R8A2A4A6S5bReA1S8S0G2SaR1A1S37S5R9S38S5S76R8R7R6R5A4S33S5A1A3A3A3S14S19R2A1S13R2A1S17R2A1S16R2A1S1aR2A1RaS12R2A1R5S18R2A1A9S8S0S31S1cR1A1S32A3S0S31S1bR7S5cR12A1A2S32A3S44G0ScR12RcA2A2S2cS3eS42S3fZ2M4Z3fA2M5A1RcA2S40S3dRdS41RcA1A2G5A2S3eZ0S3dR3ReA2A2S3eS3dS3dR4RfA2S41ReA1A2S3fG4Z40A2A2S77R17R5R10RfScR17ReA2A5S35S6fR1R11A2S0S36S43Q8A1M6A1S24Vsegs;S45G0S3dS3dR8R13A2S41R2A1A2A2A2S3aG6A1A3F_;Fj;S4eVsegs;R1bS5dR1aRaA2R19R18S30G1S47R17S48R16R15A2A4A6F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';F_;TS;F_;F_;Fnx;Fv;Fk;Foff;Fbase;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp tr ms md objs base off k v nx HX [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S Ho S' Hwf' Hb b Ho1 Ho2 Hlo Hhi Hbytes Himg.
  split; [|exact Hk]. split; [|split; [exact HMI | split; [apply axwf_setS_nilX; assumption | split; [apply shadow_ok_nilX; exact HX | exact Hhz]]]].
  unfold virt in *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in *.
  exact (smatch_release_win segs rho S _ objs base off k v nx Hsm Ho Hwf' Ho1 Ho2 Himg Hbytes).
Qed.

Definition notin_vars (vs : list positive) (v : positive) : bool := negb (existsb (Pos.eqb v) vs).

Lemma notin_vars_true : ltac2:(tb__ "0|0|
S2eS2dA1S2dS0S31S64R2R1A2S32A3S2S49S2dR2R3A3A1F_;Fv;Fvs;").
Proof.
  intros vs v H Hin. unfold notin_vars in H. apply Bool.negb_true_iff in H.
  assert (existsb (Pos.eqb v) vs = true); [|congruence].
  apply existsb_exists. exists v. split; [exact Hin|]. apply Pos.eqb_refl.
Qed.

Lemma SPA_bindV : ltac2:(tb__ "0|5|
S4fS2dS59S6S2eS43Q40A1M0A1S70S2eS2fS2dG0A2M1A1S0S2eS2fS4S4A2M2A1S5aR5A1S33G2A1A3S50Vsegs;R7R8A3S2dS49S2dR1S52G1S2dS34S2dG0A2M3R4A4M4A3S74RaR2A2F_;Fv;S0S31S71S64G4A1S5bR8A1A2S32A3S0S31S72S64S52G1S2dG3R5A4A1S5cR9A1A2S32A3S4eVsegs;RcRaR9R8R7A6S4eVsegs;RdRbS62RaR7A2R9R8A6F_;F_;F_;F_;F_;F_;Fbs;Fw;Ftp;Frho;FA;Fn;FJ;").
Proof using .
  intros J n A rho tp [tr [ms md]] bs HX Hst Hge Hvars Hbase [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  destruct (rho_sets_rl_rm bs rho) as [Hrl Hrm].
  assert (AG : agree_below n rho (rho_sets rho bs)).
  { split; [|split; [intros l; rewrite Hrl; reflexivity | intros a; rewrite Hrm; reflexivity]].
    intros i Hi. symmetry. apply rho_sets_other. intros Hin. specialize (Hge i Hin). lia. }
  split.
  - split; [|split; [exact HMI | split; [exact Hwf | split; [|exact Hhz]]]].
    + eapply (smatch_agree_vars segs (notin_vars (map fst bs))); [| | | exact Hvars | exact Hsm].
      * intros v Hv. symmetry. apply rho_sets_other. apply notin_vars_true. exact Hv.
      * intros l. rewrite Hrl. reflexivity.
      * rewrite Hrm. reflexivity.
    + unfold shadow_ok in *. rewrite HX. constructor.
  - cbn [w_tr w_cfg cfg_model] in *. eapply Hst; [exact AG | apply mat_equiv_refl | exact Hk].
Qed.

Lemma rho_sets_agree : ltac2:(tb__ "0|2|
S2dS2eS2fS2dS43Q40A1M0A2M1A1S6S2dS49S2dR1S52G1S2dS34S2dG0A2R3A4A3S74R5R2A2F_;Fv;S21R4R2S62R2R3A2A3F_;Frho;Fbs;Fn;").
Proof.
  intros n bs rho Hge. destruct (rho_sets_rl_rm bs rho) as [Hrl Hrm].
  split; [|split; [intros l; rewrite Hrl; reflexivity | intros a; rewrite Hrm; reflexivity]].
  intros i Hi. symmetry. apply rho_sets_other. intros Hin. specialize (Hge i Hin). lia.
Qed.

Lemma rho_sets_get : ltac2:(tb__ "0|2|
S2eS2fS2dS43Q40A1M0A2M1A1S6S2dG0S4bS2dS52G1S2dS34S2dG0A2R4A4A2S49G1S30S2dG0R3R2A4R5A3S0G0SdS62R5R6A2R4A2R3A3F_;F_;Fx;Fv;Frho;Fbs;").
Proof.
  induction bs as [|[v' x'] rest IH]; intros rho v x Hnd Hin; [destruct Hin|].
  cbn in Hnd. inversion Hnd as [|a l Hnin Hnd']; subst. cbn. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite rho_sets_other; [cbn; rewrite Pos.eqb_refl; reflexivity | exact Hnin].
  - apply IH; assumption.
Qed.

Definition skel (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
S30S2fS4S4A2S4S30S4S4S25Vo;A1S27Vo;A1A4S26Vo;A1A4").
Lemma obj_range_skel : ltac2:(tb__ "0|0|
S6S5S5S0S2fS2fS4S4A2S4A2S61R2A1S61R1A1A3S0S2fS2cS2cA2S9R4R3A2S9R4R2A2A3F_;Fo';Fo;Frho;").
Proof. intros rho [b l h c d] [b' l' h' c' d'] E. cbn in E. injection E as -> -> ->. reflexivity. Qed.
Lemma Forall_ranges_skel : ltac2:(tb__ "0|2|
S6S2fS2cS2cA2OF_;S2eS5A1M0G0S0S2eS2fS2fS4S4A2S4A2M1A1S52S5G1S61R2A4S52S5G1S61R1A4A3S51S5S5R5S9R6R1A2A1Lo;R2A3S51S5S5R6S9R7R1A2A1Lo;R4A3F_;F_;Fl';Fl;FP;Frho;").
Proof.
  intros rho P l. induction l as [|o l IH]; intros [|o' l'] E H; cbn in E; try discriminate; [constructor|].
  assert (Es : skel o = skel o') by congruence. assert (El : map skel l = map skel l') by congruence.
  apply Forall_cons_iff in H as [Ha Hb]. constructor; [rewrite (obj_range_skel rho o o' Es); exact Ha | exact (IH l' El Hb)].
Qed.

Definition inclb (l1 l2 : list sprop) : bool := ltac2:(tb__ "0|0|
S4cSeSeS4aSeS2aR1A1Vl2;A3Lp;Vl1;A3").
Lemma inclb_incl : ltac2:(tb__ "0|1|
S2eSeA1M0G0S0S31S65R2R1A2S32A3S4dSeR3R2A3F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as X. apply existsb_exists in X as (q & Hq & E).
  apply sprop_eqb_sound in E. subst. exact Hq.
Qed.
Lemma holds_inclb : ltac2:(tb__ "0|1|
S6S2eSeA1M0G0S0S31S65R2R1A2S32A3S51SeS11R4A1R2A3S51SeS11R5A1R4A3F_;F_;Fl2;Fl1;Frho;").
Proof. intros rho l1 l2 H H2. apply Forall_forall. intros p Hp. exact (proj1 (Forall_forall _ _) H2 p (inclb_incl _ _ H p Hp)). Qed.

Lemma SPA_facts : ltac2:(tb__ "0|0|
S4fS59S6S2eS43Q40A1A1S70S4eVsegs;R5R4R3R2R1A6S51SeS11R4A1S12S5bR5A1A1A3F_;Fw;Ftp;Frho;FA;FJ;").
Proof. intros J A rho tp w [Hsm _]. eapply smatchA_facts. exact Hsm. Qed.

Lemma sw_lo_mm : ltac2:(tb__ "0|3|
S6S5S0S2fS2fS4S4A2M0S4A2S61R1A1S30G0S4S30S4S4S10PaM1A1S10S6cA1A4SbZ0A1A4A3S0S2cS34S2cS2cS9R3R2A2A3S3dS44Q40M2SdR3G1A2A2S46G2SdR3S6cA2A2A2A3F_;Fo;Frho;").
Proof using . intros rho [ob olo ohi ocs od] Hsk. cbn in Hsk. injection Hsk as -> -> ->. reflexivity. Qed.

Lemma sw_range_mm : ltac2:(tb__ "0|5|
S6S54S2eS5A1S5S51S5S28Vsegs;R4R3A3R2A3S49S5R2R3A3S0S2fS2fS4S4A2M0S4A2S61R3A1S30G0S4S30S4S4S10PaM1A1S10S6cA1A4SbZ0A1A4A3S11R7S6dA2S1S3eZ7fff7f800000S34S2cS2cS9R8R5A2M2A3M3A2S1S0S2cS39S2cS2cG2A3M4S44Q40SdR8G1A2A2A3S3eG3G4A2A2A2F_;F_;F_;F_;Fo;Fobjs;Fms;Frho;").
Proof using .
  intros rho ms objs o Hall Hin Hsk Hf.
  destruct o as [ob olo ohi ocs od]. cbn in Hsk. injection Hsk as -> -> ->.
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
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

Lemma sw_range_gen : ltac2:(tb__ "0|5|
S6S8S2fS2eS55A1S47A2S5SfVsegs;R4R3R2A4S49S5R2SaR4A1A3S0S2fS2fS4S4A2M0S4A2S61R3A1S30G0S4S30S4S4S10PaM1A1S10S6cA1A4SbZ0A1A4A3S11R7S6dA2S1S3eZ7fff7f800000S34S2cS2cS9R8R5A2M2A3M3A2S1S0S2cS39S2cS2cG2A3M4S44Q40SdR8G1A2A2A3S3eG3G4A2A2A2F_;F_;F_;F_;Fo;Fw;FS;Frho;").
Proof using .
  intros rho S w o Hsm Hin Hsk Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  exact (sw_range_mm rho _ _ o Hall Hin Hsk Hf).
Qed.

Lemma regs_vars_nth : ltac2:(tb__ "0|0|
S2dS31F_;S8S35S0S31S71R3R2A2S32A3S0S31S72R4S53S4R2S13R3A1SbZ0A1A4A2S32A3F_;Fi;FS;Ff;").
Proof.
  intros f S i H. unfold state_vars_all in H. repeat (apply andb_prop in H as [H ?X]).
  destruct (nth_in_or_default i (ss_regs S) (SLit 0)) as [Hin| ->]; [exact (proj1 (forallb_forall _ _) H _ Hin) | reflexivity].
Qed.

Definition ro_win (rho : valuation) (o : sobj) : Prop := ltac2:(tb__ "0|9|
S3S4S4S3S2cS2cS3S35S35S3S4S4S1S0S5Vo;S69R4R3S3dR3S41R2A1M0A2M1S38S2fS2fS2cS35A2M2S4A2M3S30G2S4S30S2cS35R3R2A4R1A4S33G3A1A3M4A4A3S1S3eS42S3fZ2M5Z3eA2M6A1R3A2S1S40G1G6A2S1S1S6eU1R2A2S6eR2U8A2A2S1S3eZ0S3dS44Q40ScVrho;R4A2A2M7R3A2M8A2S1S3eS3dG8G0A2S3fG5Z40A2A2S6aVrho;S68Vsegs;S7Vrho;A1A2G7G4A4A2A2A2A2A2A2Lv;A2Lk;A2Loff;A2Lbase;A2").

Lemma ro_win_agree : ltac2:(tb__ "0|0|
S2dS6S6S5S21R4R3R2A3S0S31S29R5R2A2S32A3S60R5R3A2S60R5R4A2F_;F_;F_;Fo;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' o Hag Hwf (base & off & k & v & -> & H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (obj_wf_parts n _ Hwf) as (Wb & _ & _ & Wc).
  assert (Eb : eval rho' base = eval rho base) by (symmetry; eapply eval_agree; eauto).
  assert (Wv : sv_below n v = true).
  { cbn [ob_cells carved lit_cells forallb] in Wc. apply andb_prop in Wc as [Wc _]. unfold cell_wf in Wc. cbn [c_off c_val c_width] in Wc.
    repeat (apply andb_prop in Wc as [Wc ?X]); first [exact X | exact X0 | exact Wc]. }
  assert (Ev : eval rho' v = eval rho v) by (symmetry; eapply eval_agree; eauto).
  exists base, off, k, v. rewrite Eb. repeat (split; [first [reflexivity | assumption]|]).
  destruct Hag as (_ & _ & Hrm). unfold cells_in_view in *. constructor; [|constructor].
  intros j Hj. rewrite Ev. replace (rm rho') with (rm rho) by (apply functional_extensionality; exact Hrm).
  pose proof (Forall_inv H6) as X. cbn beta iota in X. exact (X j Hj).
Qed.

Lemma ro_win_vars : ltac2:(tb__ "0|2|
S2dS31F_;S6S6S5S2dS0S31R5R1A1S32A3S0S43Q40A1M0SdR5R2A2SdR4R2A2A3F_;Fv;S2dS0S2eS43Q8A1M1A1S15R5R1A2S15R4R1A2A3Fl;G0S0S36G1A1S68Vsegs;S7R5A1R1A3S68Vsegs;S7R6A1R1A3A3Fa;S0S31S73R7R4A2S32A3S60R7R5A2S60R7R6A2F_;F_;F_;F_;F_;Fo;Frho';Frho;Ff;").
Proof using .
  intros f rho rho' o Hv Hl Hm Hvars (base & off & k & v & -> & H1 & H2 & H3 & H4 & H5 & H6).
  unfold obj_vars_all, carved in Hvars. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt lit_cells forallb c_off c_val dflt_vars_all] in Hvars.
  repeat (apply andb_prop in Hvars as [Hvars ?X]).
  apply andb_prop in X0 as [X0 _]. apply andb_prop in X0 as [_ Xv].
  assert (Eb : eval rho' base = eval rho base) by (symmetry; eapply eval_agree_vars; eauto).
  assert (Ev : eval rho' v = eval rho v) by (symmetry; eapply eval_agree_vars; eauto).
  exists base, off, k, v. rewrite Eb. repeat (split; [first [reflexivity | assumption]|]).
  unfold cells_in_view in *. constructor; [|constructor].
  intros j Hj. rewrite Ev, Hm.
  pose proof (Forall_inv H6) as Y. cbn beta iota in Y. exact (Y j Hj).
Qed.

Lemma view_eq_rd_of : ltac2:(tb__ "0|2|
S6S6S2cS0S36S43Q8A1A1M0S57Vsegs;S7R2A1R1A3S57Vsegs;S7R3A1M1R1A3A3Fz;S43Q40A1S0G0S68Vsegs;G1R1A3S68Vsegs;S7R4A1R1A3A3Fa;F_;Fr';Fr;").
Proof using .
  intros r r' HV a. pose proof (urange a) as R. pose proof (HV (bv_unsigned a)) as X. rewrite !view_in in X by lia.
  rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

Lemma dissolve_ro_view : ltac2:(tb__ "0|3|
S6S8S2eS55A1M0S54S56S2eS5A1M1G1SfVsegs;R7R6S30G0S47R5S48R4R3A2A4A4S0G1SaR7A1S37S5R3R2A3A3S51S5S60R9A1R3A3S66RaR4R7A3S6S1S2cS0S36S43Q8A1A1M2S57Vsegs;S7R2A1R1A3S57Vsegs;S7RcA1R1A3A3Fz;S43Q40A1S2S67RcR6R1A3A1S0G2S7R3R2A2S7RdR2A2A3F_;Fa;A2Trho';F_;F_;F_;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs R Hsm Ho HR rho'. split.
  - intros z. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:Ez; [|reflexivity].
    apply andb_prop in Ez as [Ez1 Ez2]. apply Z.leb_le in Ez1. apply Z.ltb_lt in Ez2.
    destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [Hin|Hout].
    + destruct Hin as (o & HoR & Hrng). pose proof (proj1 (Forall_forall _ _) HR o HoR) as (base & off & k & v & Eo & H1 & H2 & H3 & H4 & H5 & H6).
      subst o. unfold carved in Hrng. rewrite obj_range_mk in Hrng by lia. cbn [fst snd] in Hrng. rewrite u64_lit in Hrng by lia.
      set (b := bv_unsigned (eval rho base)) in *.
      destruct (absorb_carved_cells segs rho S tr ms md objs R base off (off + Z.of_nat k) [(off, k, v)] Hsm Ho HoR ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])) as [CV _].
      fold b in CV. fold rho' in CV.
      pose proof (Forall_inv CV (Z.to_nat (z - (b + off))) ltac:(lia)) as X. pose proof (Forall_inv H6 (Z.to_nat (z - (b + off))) ltac:(lia)) as Y.
      cbn beta iota in X, Y. replace (b + off + Z.of_nat (Z.to_nat (z - (b + off)))) with z in X, Y by lia.
      rewrite X, Y. unfold rho'. rewrite eval_absorb. reflexivity.
    + unfold rd_of. unfold rho'. rewrite (rm_absorb_out rho R ms _ Hout). reflexivity.
  - intros a Ha. unfold rho'. apply rm_absorb_out. exact Ha.
Qed.

Lemma absorb_view_ro : ltac2:(tb__ "0|3|
S6S8S2eS55A1M0S54S56S2eS5A1M1G1S5SfVsegs;R8R7S30G0S47R6S48R5R4A2A4A4S0G1SaR8A1S37S5R4R3A3A3S49S5R3R4A3S60RbR4A2S2cS1S3eS34S2cS2cS9RdR6A2M2A3R1A2S40R1S39S2cS2cG2A3A2A2S0S36S43Q8A1A1S57Vsegs;S7S66ReR8RbA3A1R2A3S57Vsegs;S7ReA1R2A3A3F_;Fz;F_;F_;F_;F_;Fo;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs R o Hsm Ho HoR (base & off & k & v & Eo & H1 & H2 & H3 & H4 & H5 & H6) z Hz.
  subst o. unfold carved in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz.
  set (b := bv_unsigned (eval rho base)) in *.
  destruct (absorb_carved_cells segs rho S tr ms md objs R base off (off + Z.of_nat k) [(off, k, v)] Hsm Ho HoR ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])) as [CV _].
  fold b in CV.
  pose proof (Forall_inv CV (Z.to_nat (z - (b + off))) ltac:(lia)) as X. pose proof (Forall_inv H6 (Z.to_nat (z - (b + off))) ltac:(lia)) as Y.
  cbn beta iota in X, Y. replace (b + off + Z.of_nat (Z.to_nat (z - (b + off)))) with z in X, Y by lia.
  rewrite !view_in by lia. rewrite X, Y. rewrite eval_absorb. reflexivity.
Qed.

Lemma absorb_view_cells : ltac2:(tb__ "0|9|
S6S8S2eS55A1M0S54S56S2eS5A1M1G1S4S2cS2cS2eS2fS2fS2cS35A2M2S4A2M3A1SfVsegs;RbRaS30G0S47R9S48R8R7A2A4A4S0G1SaRbA1S37S5R7R6A3A3S49S5S69R6R5R4R3A4R7A3S3eS42S3fZ2M4Z3fA2M5A1R6A2S3eR7R6A2S40R7G5A2S6bR9R8R7A3S44Q40ScR12RbA2A2S2cS3eZ0M6S3dR1RbA2A2S3eS3dR2RbA2S3fG4Z40A2A2S66R15RfR12A3S6S1S2cS35S4S35S49G3S30G2S4S30S2cS35R4R3A4R2A4R10A3S6fR2R4A2S0S36S43Q8M7A1M8A1S57Vsegs;S7R7A1S3dS3dRaR6A2S41R3A1A2A3S3bG8S53G8R3S23R5ScR1cR4A2A2S45G7G6A2A4A2A3F_;F_;Fj;Fv;Fk;Foff;S58S57Vsegs;S7R1A1A2S3dR4ReA2S3dR4RdA2A3A2Trho';F_;F_;Tb;F_;F_;F_;F_;F_;F_;F_;Fcs;Fhi;Flo;Fbase;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs R base lo hi cs Hsm Ho HoR H1 H2 H3 Hci b Hb1 Hb2 rho'.
  destruct (absorb_carved_cells segs rho S tr ms md objs R base lo hi cs Hsm Ho HoR H1 H2 H3 Hci) as [CV PR]. fold b in CV, PR. fold rho' in CV, PR.
  split.
  - intros off k v j Hin Hj. pose proof (proj1 (Forall_forall _ _) CV _ Hin) as X. cbn beta iota in X.
    pose proof (proj1 (Forall_forall _ _) Hci _ Hin) as B. cbn beta iota in B.
    rewrite view_in by lia. rewrite (X j Hj). unfold rho'. rewrite eval_absorb. reflexivity.
  - intros z Hz. destruct (PR (z - b) ltac:(lia)) as [x Hx]. replace (b + (z - b)) with z in Hx by lia. exists x. rewrite view_in by lia. exact Hx.
Qed.

Lemma ro_win_absorb : ltac2:(tb__ "0|3|
S6S2eS5A1S54S5S60R4R1A2S43Q40M0A1S1S3eS34S2cS2cS9R6R3A2M1A3S44G0R1A2M2A2S40G2S39S2cS2cG1A3A2A2S0S36S43Q8A1A1S7S66R7R6R5A3R2A2S7R7R2A2A3F_;Fa;S60S66R6R5R4A3R3A2F_;F_;Fo;Fms;FR;Frho;").
Proof using .
  intros rho R ms o (base & off & k & v & -> & H1 & H2 & H3 & H4 & H5 & H6) Hrm.
  unfold carved in Hrm. rewrite obj_range_mk in Hrm by lia. cbn [fst snd] in Hrm.
  exists base, off, k, v. rewrite !eval_absorb. repeat (split; [first [reflexivity | assumption]|]).
  unfold cells_in_view in *. constructor; [|constructor].
  intros j Hj. rewrite eval_absorb. pose proof (Forall_inv H6) as Y. cbn beta iota in Y. rewrite <- (Y j Hj).
  unfold rd_of. rewrite Hrm; [reflexivity|]. rewrite u64_lit by lia. lia.
Qed.

Lemma absorb_view_dzero : ltac2:(tb__ "0|7|
S6S8S2eS55A1M0S54S56S2eS5A1M1G1S4S2cS2cSfVsegs;RaR9S30G0S47R8S48R7R6A2A4A4S0G1SaRaA1S37S5R6R5A3A3S49S5S1eR5SbR4A1SbR3A1S33S1dA1S22A5R6A3S3eS42S3fZ2M2Z3fA2M3A1R5A2S3eR6R5A2S40R6G3A2S44Q40ScR10R9A2A2S2cS3eZ0M4S3dR1R9A2A2S3eS3dR2R9A2S3fG2Z40A2A2S2cS1S3eS3dR4RcA2R1A2S40R1S3dR4RbA2A2A2S0S36S43Q8M5A1M6A1S57Vsegs;S7S66R15RfR12A3A1R2A3S3bG6S45G5G4A2A2A3F_;Fz;F_;F_;Tb;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fbase;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs R base lo hi Hsm Ho HoR H1 H2 H3 b Hb1 Hb2 z Hz.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  pose proof (proj1 (Forall_forall _ _) HallR _ HoR) as Hoh.
  unfold obj_holds, obj_lo_of, obj_hi_of in Hoh. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Hoh. fold b in Hoh.
  rewrite !soff_lit_small in Hoh by lia.
  destruct Hoh as (Hbnd & Hwv & Hcl & Hdf & _).
  assert (RNG : in_ranges rho R (Z_to_bv 64 z)).
  { exists (mkObj base (SLit lo) (SLit hi) [] DZero). split; [exact HoR|]. rewrite obj_range_mk by lia. fold b. cbn [fst snd]. rewrite u64_lit by lia. lia. }
  rewrite view_in by lia. rewrite (rd_of_absorb_in segs rho R ms _ Hrom RNG).
  specialize (Hdf (z - b) ltac:(lia) ltac:(intros X; unfold covered in X; apply Exists_exists in X as (c & Hc' & _); destruct Hc')).
  cbn [dflt_holds] in Hdf. replace (b + (z - b)) with z in Hdf by lia. exact Hdf.
Qed.

End SG.
End SegD_glue.

(* [comment removed for export] *)
Module SegQpiece.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "false"; "Some"; "nil"; "option"; "pair"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "runA"; "@Corelib.Numbers.BinNums"; "positive"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "SVar"; "agree_below"; "rw"; "ss_lenient"; "sv"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "JQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece"; "chkN"; "chkNK"; "chk_leaves"; "chk_leavesK"; "idon"; "keeps"; "postsJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_sub"; "wsub"; "@Stdlib.PArith.BinPos.Pos"; "le"; "ltb"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Fixpoint chk_leaves (l : list leafA) (Ts : list axst) : bool :=
  match l, Ts with
  | [], [] => true
  | L :: l', T :: Ts' => entsI (la_state L) T && chk_leaves l' Ts'
  | _, _ => false
  end.
Definition chkN (l : list leafA) (Ts : list axst) : bool := ltac2:(tb__ "0|1|
S0SeA1M0S1Ll;Vl;S3SeG0S30Vl;VTs;A2Ll1;Ll0;X0x2").

Lemma chk_leaves_In : ltac2:(tb__ "0|0|
S0SeA1S0SdA1SeS9S1S30R3R2A2S2A3S16SeR2R4A3SbSdSdSaS16SdR1R5A3S9S1S2cS10R4A1R1A2S2A3A2LT;A2F_;F_;FL;FTs;Fl;").
Proof.
  induction l as [|L0 l IH]; intros [|T Ts] L H Hin; cbn in H; try discriminate H; [destruct Hin|].
  apply andb_prop in H as [HE HR]. destruct Hin as [<-|Hin].
  - exists T. split; [left; reflexivity | exact HE].
  - destruct (IH Ts L HR Hin) as (T' & HT' & HE'). exists T'. split; [right; exact HT' | exact HE'].
Qed.
Lemma chkN_ne : ltac2:(tb__ "0|1|
S0SeA1M0S0SdA1S9S1S2eR2R1A2S2A3ScS9G0R3S5SeA1A3A1F_;FTs;Fl;"). Proof. intros [|L l] Ts H; [discriminate H | discriminate]. Qed.
Lemma chkN_leaves : ltac2:(tb__ "0|0|
S0SeA1S0SdA1S9S1S2eR2R1A2S2A3S9S1S30R3R2A2S2A3F_;FTs;Fl;"). Proof. intros [|L l] Ts H; [discriminate H | exact H]. Qed.

Definition idon (s : wsub) (V : list positive) : bool := ltac2:(tb__ "0|0|
S17S15S15S1fS35Vs;R1A2S1aR1A1A2Lv;VV;A3").
Fixpoint chk_leavesK (l : list leafA) (Ts : list axst) (V : list positive) : bool :=
  match l, Ts with
  | [], [] => true
  | L :: l', T :: Ts' => entsI (la_state L) T && idon (infer_sub NPRE (ax_S (la_state L)) (ax_S T)) V && chk_leavesK l' Ts' V
  | _, _ => false
  end.
Definition chkNK (l : list leafA) (Ts : list axst) (V : list positive) : bool := ltac2:(tb__ "0|1|
S0SeA1M0S1Ll;Vl;S3SeG0S31Vl;VTs;VV;A3Ll1;Ll0;X0x2").

Lemma idon_get : ltac2:(tb__ "0|0|
S37S0S15A1S15S9S1S32R3R2A2S2A3S16S15R2R3A3S9S1eS35R5R3A2S1aR3A1A3F_;F_;Fv;FV;Fs;").
Proof. intros s V v H Hin. unfold idon in H. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) H v Hin). Qed.
Lemma chk_leavesK_In : ltac2:(tb__ "0|1|
S0SeA1S0SdA1S0S15A1SeS9S1S31R4R3R2A3S2A3S16SeR2R5A3SbSdSdSaS16SdR1R6A3SaS9S1S2cS10R4A1M0R1A2S2A3S9S1S32S2bS13SfG0A1SfR1A1A3R5A2S2A3A2A2LT;A2F_;F_;FL;FV;FTs;Fl;").
Proof.
  induction l as [|L0 l IH]; intros [|T Ts] V L H Hin; cbn in H; try discriminate H; [destruct Hin|].
  apply andb_prop in H as [H HR]. apply andb_prop in H as [HE HI]. destruct Hin as [<-|Hin].
  - exists T. split; [left; reflexivity | split; [exact HE | exact HI]].
  - destruct (IH Ts V L HR Hin) as (T' & HT' & HE' & HI'). exists T'. split; [right; exact HT' | split; [exact HE' | exact HI']].
Qed.
Lemma chkNK_ne : ltac2:(tb__ "0|1|
S0SeA1M0S0SdA1S0S15A1S9S1S2fR3R2R1A3S2A3ScS9G0R4S5SeA1A3A1F_;FV;FTs;Fl;"). Proof. intros [|L l] Ts V H; [discriminate H | discriminate]. Qed.
Lemma chkNK_leaves : ltac2:(tb__ "0|0|
S0SeA1S0SdA1S0S15A1S9S1S2fR3R2R1A3S2A3S9S1S31R4R3R2A3S2A3F_;FV;FTs;Fl;"). Proof. intros [|L l] Ts V H; [discriminate H | exact H]. Qed.

Definition postsJ (J : jpredA) (Ts : list axst) : list (axst * jpostA) := ltac2:(tb__ "0|0|
S3aSdS8SdS29A2SdS7SdS29R1S2dVJ;A1A4LT;VTs;A4").
Lemma In_postsJ : ltac2:(tb__ "0|0|
S21S0SdA1SdS16SdR1R2A3S16S8SdS29A2S7SdS29R2S2dR4A1A4S34R4R3A2A3F_;FT;FTs;FJ;").
Proof. intros J Ts T H. unfold postsJ. apply in_map_iff. exists T. split; [reflexivity | exact H]. Qed.

Section Piece.
Variables (fuel : nat) (cuts : list Z) (Pre : axst) (l : list leafA) (Ts : list axst).
Hypothesis RUNL : ltac2:(tb__ "0|0|
S9S0SeA1S14Vfuel;Vcuts;VPre;A3Vl;A3").
Hypothesis CHK : ltac2:(tb__ "0|0|
S9S1S2eVl;VTs;A2S2A3").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S9S1S1dSfVPre;A1A1S3A3").
Hypothesis HNX : ltac2:(tb__ "0|0|
S38S13S19SfVPre;A1A1A2").

Lemma piece_run_some : ltac2:(tb__ "0|1|
S9S6S0SeA1M0A1S11S12Vfuel;Vcuts;VPre;S2A5S4G0Vl;A2A3").
Proof using RUNL CHK. pose proof RUNL as R. unfold runA in R. destruct (sym_runA segsA fuel cuts Pre true) as [l'|]; [congruence|]. exfalso. apply (chkN_ne l Ts CHK). symmetry. exact R. Qed.

Theorem piece_sound : ltac2:(tb__ "0|0|
S21S25OF_;S18S0S24Q40A1A1S23S12R3R4A3S22S12S13R5A3S27S12R5S20S12R6VPre;R4R3A5S2aS12S13R4R3S34R6VTs;A2A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof using RUNL CHK HLEN HNX.
  intros J ok rho tp HOK HST. eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp piece_run_some HOK HLEN (stableA_mono segsA NPRE _ J HNX HST)).
  - apply triple_LQA_of_leaves. intros L0 rhoE Hin Hag.
    destruct (chk_leaves_In l Ts L0 (chkN_leaves l Ts CHK) Hin) as (T & HT & HE).
    exact (leaf_post J ok (la_state L0) T rho rhoE tp (postsJ J Ts) HE HST (In_postsJ J Ts T HT) (agree_below_le (ss_next (ax_S Pre)) NPRE rho rhoE HNX Hag)).
Qed.
Theorem piece_complete : ltac2:(tb__ "0|0|
S21S18S0S24Q40A1A1S22S12S13R3A3S26S12S20S12R4VPre;R3R2A5S2aS12S13R3R2S34R4VTs;A2A5A3F_;Ftp;Frho;FJ;").
Proof using RUNL CHK HLEN HNX.
  intros J rho tp HST. eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN (stableA_mono segsA NPRE _ J HNX HST) piece_run_some).
  - apply etriple_LQA_of_leaves. intros L0 rhoE Hin Hag.
    destruct (chk_leaves_In l Ts L0 (chkN_leaves l Ts CHK) Hin) as (T & HT & HE).
    exact (leaf_epost J (la_state L0) T rho rhoE tp (postsJ J Ts) HE HST (In_postsJ J Ts T HT) (agree_below_le (ss_next (ax_S Pre)) NPRE rho rhoE HNX Hag)).
Qed.
End Piece.

Definition keeps (V : list positive) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|0|
SaS1bS13Vrho;Vrho';A3S15S16S15R1VV;A3S9S24Q40A1S1cVrho';R2A2S1cVrho;R2A2A3F_;Fv;A2").

Section PieceK.
Variables (fuel : nat) (cuts : list Z) (Pre : axst) (l : list leafA) (Ts : list axst) (V : list positive).
Hypothesis RUNL : ltac2:(tb__ "0|0|
S9S0SeA1S14Vfuel;Vcuts;VPre;A3Vl;A3").
Hypothesis CHK : ltac2:(tb__ "0|0|
S9S1S2fVl;VTs;VV;A3S2A3").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S9S1S1dSfVPre;A1A1S3A3").
Hypothesis HNX : ltac2:(tb__ "0|0|
S38S13S19SfVPre;A1A1A2").
Hypothesis HV : ltac2:(tb__ "0|0|
S9S1S17S15S15S39R1S19SfVPre;A1A1A2Lv;VV;A3S2A3").

Lemma pieceK_run_some : ltac2:(tb__ "0|1|
S9S6S0SeA1M0A1S11S12Vfuel;Vcuts;VPre;S2A5S4G0Vl;A2A3").
Proof using RUNL CHK. pose proof RUNL as R. unfold runA in R. destruct (sym_runA segsA fuel cuts Pre true) as [l'|]; [congruence|]. exfalso. apply (chkNK_ne l Ts V CHK). symmetry. exact R. Qed.

Lemma leafK : ltac2:(tb__ "0|0|
S21SeSdS18S18S0S24Q40A1A1S25S9S1S2cS10R6A1R5A2S2A3S9S1S32S2bS13SfS10R7A1A1SfR6A1A3VV;A2S2A3S22S12S13R9A3S1bS19SfVPre;A1A1R7R6A3S20S12RbS10RaA1R7R6R5A6S36R8S2bS13SfS10RbA1A1SfRaA1A3A2S18SaS20S12RdRbR1R8R7A6S33VV;RaR1A3A2Trho';F_;F_;F_;F_;F_;Fw;Ftp;FrhoL;Frho;FT;FL;FJ;").
Proof using HNX HV.
  intros J L T rho rhoL tp w HE HI HST Hag HS rho'. destruct (ent_SPA J (la_state L) T rhoL tp w HE HST HS) as [HT Hag']. split; [exact HT|].
  split; [exact (agree_below_trans _ _ _ _ (agree_below_le _ _ _ _ HNX Hag) Hag')|].
  intros v Hv. unfold rho'. cbn [rho_sub rw]. rewrite (idon_get _ V v HI Hv). cbn [eval]. symmetry. apply (proj1 Hag).
  apply Pos.ltb_lt. exact (proj1 (forallb_forall _ _) HV v Hv).
Qed.

Theorem piece_soundK : ltac2:(tb__ "0|0|
S21S25OF_;S18S0S24Q40A1A1S28S23S12R4R5A3S22S12S13R6A3SdS18S16SdR2VTs;A3S33VV;R8R2A3S27S12RaS20S12RbR4R3R8A5R7A4F_;F_;Frho';FT;S27S12R7S20S12R8VPre;R6R5A5R4A4F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;").
Proof using RUNL CHK HLEN HNX HV.
  intros J ok rho tp Q HOK HST HC. eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp pieceK_run_some HOK HLEN (stableA_mono segsA NPRE _ J HNX HST)).
  - apply triple_LQA_of_leaves. intros L0 rhoL Hin Hag.
    destruct (chk_leavesK_In l Ts V L0 (chkNK_leaves l Ts V CHK) Hin) as (T & HT & HE & HI).
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (HC T (rho_sub rhoL (infer_sub NPRE (ax_S (la_state L0)) (ax_S T))) HT)].
    + intros w Hw. exact (proj1 (leafK J L0 T rho rhoL tp w HE HI HST Hag Hw)).
    +
      split; [|intros v Hv; cbn [rho_sub rw]; rewrite (idon_get _ V v HI Hv); cbn [eval]; symmetry; apply (proj1 Hag); apply Pos.ltb_lt; exact (proj1 (forallb_forall _ _) HV v Hv)].
      eapply agree_below_trans; [exact (agree_below_le _ _ _ _ HNX Hag)|]. apply rho_sub_agree.
      unfold entsI in HE. apply andb_prop in HE as [HE _]. apply andb_prop in HE as [HE _]. apply andb_prop in HE as [_ HIb]. exact HIb.
Qed.
Theorem piece_completeK : ltac2:(tb__ "0|0|
S21S18S0S24Q40A1A1S25OF_;S22S12S13R4A3SdS18S16SdR2VTs;A3S33VV;R7R2A3S26S12S20S12R9R4R3R7A5R6A3F_;F_;Frho';FT;S26S12S20S12R6VPre;R5R4A5R3A3F_;F_;FQ;Ftp;Frho;FJ;").
Proof using RUNL CHK HLEN HNX HV.
  intros J rho tp Q HST HC. eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN (stableA_mono segsA NPRE _ J HNX HST) pieceK_run_some).
  - apply etriple_LQA_of_leaves. intros L0 rhoL Hin Hag.
    destruct (chk_leavesK_In l Ts V L0 (chkNK_leaves l Ts V CHK) Hin) as (T & HT & HE & HI).
    eapply etriple_conseq; [| intros w Hw; exact Hw | apply (HC T (rho_sub rhoL (infer_sub NPRE (ax_S (la_state L0)) (ax_S T))) HT)].
    + intros w Hw. exact (proj1 (leafK J L0 T rho rhoL tp w HE HI HST Hag Hw)).
    + split; [|intros v Hv; cbn [rho_sub rw]; rewrite (idon_get _ V v HI Hv); cbn [eval]; symmetry; apply (proj1 Hag); apply Pos.ltb_lt; exact (proj1 (forallb_forall _ _) HV v Hv)].
      eapply agree_below_trans; [exact (agree_below_le _ _ _ _ HNX Hag)|]. apply rho_sub_agree.
      unfold entsI in HE. apply andb_prop in HE as [HE _]. apply andb_prop in HE as [HE _]. apply andb_prop in HE as [_ HIb]. exact HIb.
Qed.
End PieceK.
End SegQpiece.

(* [comment removed for export] *)
Module SegQC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1"; "JQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states"; "PostQC"; "PreQC"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states.
Import ListNotations.
Open Scope Z_scope.

Theorem seg_QC_sound : ltac2:(tb__ "0|1|
ScS15OF_;SaS6S12Q40A1A1SeS0R3R4A3SdS0S4R5A3S14S0R5SbS0R6S11R4R3A5S3S0S4R4R3S5S9S1S2A2M0S8S1S2S10SfR6A1A4S7G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof. intros J ok rho tp HOK HST. exact (straight_sound 600%nat [QCFULL; QCINIT] QCRET PreQC PostQC run_QC (proj1 preQC_nx) (proj2 preQC_nx) run_QC_eq chk_QC J ok rho tp HOK HST). Qed.
Theorem seg_QC_complete : ltac2:(tb__ "0|1|
ScSaS6S12Q40A1A1SdS0S4R3A3S13S0SbS0R4S11R3R2A5S3S0S4R3R2S5S9S1S2A2M0S8S1S2S10SfR4A1A4S7G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HST. exact (straight_complete 600%nat [QCFULL; QCINIT] QCRET PreQC PostQC run_QC (proj1 preQC_nx) (proj2 preQC_nx) run_QC_eq chk_QC J rho tp HST). Qed.
End SegQC.

(* [comment removed for export] *)
Module CertFreeNullInit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "nat"; "prod"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sobj"; "cell"; "mkCell"; "sprop"; "SAlu"; "FcsrFrm0"; "SPUle"; "mkSS"; "mkObj"; "DUnknown"; "DZero"; "SPAlign"; "SPBranch"; "SPNot"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit.FNI"; "Lcut"; "bytef"; "Lregs"; "stack_win_init"; "wordf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "mkA"; "AE_A"; "A_globals"; "unwind_objs"; "V_DEPTH"; "V_FREE_A1"; "ae_free"; "ae_ret_free"; "free_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "O_T3168"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit"; "O_inst"; "RT_rest"; "E_fni"; "IA_LO"; "L1"; "L2"; "L3"; "L4"; "P0_fni"; "fni_cutpcs"; "IA_HI"; "O_iaw"; "O_iaw_done"; "O_iaw_locked"; "fni_cuts"; "fni_vcuts"; "inst_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "O_T0"; "O_T40"; "O_cfa"; "O_ctx8"; "O_ctx98"; "O_mcs"; "O_pga"; "O_pgb"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition IA_LO : Z := 0xef2c0.
Definition IA_HI : Z := 0x1702f0.

Definition O_iaw (inited mtx : Z) : sobj := ltac2:(tb__ "0|5|
S39S9Z0A1M0Z17db48M1Z17db4cS0S4S4S1aS3A2M2S8A2M3S2G2S8S2S1aS3G1U1M4A4S9Vinited;A1A4S0G3S2G2S8S2S1aS3Z17db49G4A4S9Vmtx;A1A4S0G3S2G2S8S2S1aS3Z17db4aG4A4G0A4S0G3S2G2S8S2S1aS3Z17db4bG4A4G0A4S1G3A1A3A3A3A3A4").

Definition O_iaw_locked : sobj := ltac2:(tb__ "0|3|
S39S9Z0A1Z17db48M0Z17db4cS0S4S4S1aS3A2M1S8A2M2S2G1S8S2S1aS3G0U4A4S9Z100A1A4S1G2A1A3A4").

Definition O_inst (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S13S9Z0A1S9S40A1S9S47A1Vcs;S15A5").
Definition inst_cells : list cell := ltac2:(tb__ "0|1|
S0ScSdS9Z130088A1Z8M0S9Z130090A1A3S0ScSdS9Z130080A1G0S9Z1000A1A3S1ScA1A3A3").

Definition RT_rest : list sobj := ltac2:(tb__ "0|0|
S0SbS59S0SbS5aS0SbS5dS0SbS5eS0SbS5fS0SbS5bS0SbS5cS0SbS54S0SbS55S0SbS51S0SbS52S0SbS3cS0SbS53S0SbS57S0SbS58S0SbS56S1SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_iaw_done : sobj := ltac2:(tb__ "0|5|
S39S9Z0A1M0Z17db48M1Z17db4cS0S4S4S1aS3A2M2S8A2M3S2G2S8S2S1aS3Z17db49U1M4A4G0A4S0G3S2G2S8S2S1aS3G1G4A4S9Z1A1A4S0G3S2G2S8S2S1aS3Z17db4aU2A4G0A4S1G3A1A3A3A3A4").

Section FNI.
Variable W : list ulink.
Variable st : ustop.
Let FACTS : list sprop := ltac2:(tb__ "0|0|
S5SeS5SeS34VW;Vst;A2S32S31A1A3S3bA3").

Let OBJS (rt1 rt2 : list sobj) : list sobj := ltac2:(tb__ "0|0|
S5SbS5SbS0SbS33S5SbS2cVW;A1S2bA3A3Vrt1;A3Vrt2;A3").

Definition P0_fni : axst := ltac2:(tb__ "0|2|
S29S12S2fS2aA1S36S38S0S4S3S8A2M0S2S3S8U4S9S50A1A4S0G0S2S3S8UaS9Z0M1A1A4S0G0S2S3S8UbSaS2eA1A4S1G0A1A3A3A3A2S35S10S6S8A1VOBJS;S0SbS48G1G1A2S3eA3S0SbS3dS1ScA1A1S1SbA1A3A2VFACTS;S3aS7A9S1S4S8S8A2A1A2").

Definition Lregs (ra dst fin : Z) (s2 s3 : sv) : list sv := ltac2:(tb__ "0|0|
S0S8SaP14A1S0S8S9Vra;A1S0S8SfS21SaPaA1S9N880A1A3S0S8SaP17A1S0S8S9S50A1S0S8SaPa5A1S0S8SaPa6A1S0S8SaPa7A1S0S8S9Z17db48A1S0S8S9S40A1S0S8S9Vdst;A1S0S8S9Z0A1S0S8S9Vfin;A1S0S8SaPa0A1S0S8SaPaeA1S0S8SaPafA1S0S8SaPb0A1S0S8SaPb1A1S0S8Vs2;S0S8Vs3;S0S8SaP28A1S0S8SaP29A1S0S8SaP2aA1S0S8SaP2bA1S0S8SaP2cA1S0S8SaP2dA1S0S8SaP2eA1S0S8SaP2fA1S0S8SaPbcA1S0S8SaPbdA1S0S8SaPbeA1S0S8SaPbfA1S1S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition stack_win_init : sobj := ltac2:(tb__ "0|5|
S13SaPaA1M0SaS2dA1S9Z0A1M1S0ScSdS9N878A1Z8M2SaP27A1M3A3S0ScSdS9N870A1G2SaPbA1M4A3S0ScSdS9N868A1G2G1A3S0ScSdS9N860A1G2G0A3S0ScSdS9N858A1G2S9Z5e238A1A3S0ScSdS9N38A1G2SaP29A1A3S0ScSdS9N30A1G2SaP28A1A3S0ScSdS9N28A1G2G3A3S0ScSdS9N20A1G2SaP26A1A3S0ScSdS9N18A1G2SaP1dA1A3S0ScSdS9N10A1G2SaP1cA1A3S0ScSdS9N8A1G2G4A3S1ScA1A3A3A3A3A3A3A3A3A3A3A3A3S14A5").
Definition Lcut (pc ra dst fin : Z) (s2 s3 : sv) (lf : list sprop) : axst := ltac2:(tb__ "0|0|
S29S12Vpc;S25Vra;Vdst;Vfin;Vs2;Vs3;A5S35S10S6S8A1S5SbS5SbS0SbS26S5SbS2cVW;A1S2bA3A3S0SbS4aS3eA3A3S0SbS3dS1ScA1A1S1SbA1A3A3S5SeVlf;VFACTS;A3S3aS7A9S1S4S8S8A2A1A2").
Definition bytef (dst fin : Z) : list sprop := ltac2:(tb__ "0|2|
S0SeS11S9Vdst;A1SaPa0A1M0A2S0SeS11G0S9Vfin;A1M1A2S0SeS18S17S22G0G1A3A1S1SeA1A3A3A3").
Definition wordf (dst fin : Z) : list sprop := ltac2:(tb__ "0|2|
S0SeS11S9Vdst;A1SaPa0M0A1M1A2S0SeS19G1S9Vfin;A1A2S0SeS16G0Z4A2S1SeA1A3A3A3").
Definition L1 : axst := ltac2:(tb__ "0|2|
S23Z6feb4Z6a324Z1702c8M0Z1702f0M1SaPbA1SaP27A1S24G0G1A2A7").
Definition L2 : axst := ltac2:(tb__ "0|2|
S23Z6feb4Z6a33cZef2c8M0Z12f2c8M1SaPbA1S9Z40000A1S24G0G1A2A7").
Definition L3 : axst := ltac2:(tb__ "0|2|
S23Z6fee8Z6a354Z12f300M0Z130080M1SaPbA1S9Z40000A1S27G0G1A2A7").
Definition L4 : axst := ltac2:(tb__ "0|2|
S23Z6feb4Z6a36cZ130080M0Z1702c8M1S9Z41000A1S9Z40000A1S24G0G1A2A7").

Definition E_fni : axst := ltac2:(tb__ "0|1|
S29S12S30S2aA1S36S37S4eA1S0S4S3S8A2M0S2S3S8U4S9S50A1A4S1G0A1A3A2S35S10S6S8A1VOBJS;S0SbS49S3eA3S0SbS3dS4dA1S1SbA1A3A2VFACTS;S3aS7A9S1S4S8S8A2A1A2").
End FNI.

Definition fni_cuts (n : nat) (st : ustop) : list axst := ltac2:(tb__ "0|1|
S0S1fS45S28Vn;A1M0Vst;A2S0S1fS41G0Vst;A2S0S1fS42G0Vst;A2S0S1fS43G0Vst;A2S0S1fS44G0Vst;A2S1S1fA1A3A3A3A3A3").
Definition fni_cutpcs : list Z := [0x6feb4; 0x6fee8].
Definition fni_cert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|0|
S1dS4fUbb8S46S4eS4bVn;Vst;A2S0S1fS3fS28Vn;A1Vst;A2S1S1fA1A3A6").
Definition fni_vcuts (n : nat) (st : ustop) : list vnodeA := ltac2:(tb__ "0|2|
S0S1bS1cS45S28Vn;A1M0Vst;A2Z5S9Z0A1A3S0S1bS1cS41G0Vst;A2Z4SfS20S9Z1702f0A1SaPa0A1M1A3A3S0S1bS1cS42G0Vst;A2Z3SfS20S9Z12f2c8A1G1A3A3S0S1bS1cS43G0Vst;A2Z2SfS20S9Z130080A1G1A3A3S0S1bS1cS44G0Vst;A2Z1SfS20S9Z1702c8A1G1A3A3S1S1bA1A3A3A3A3A3").
Definition fni_ecert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|1|
S1eS4fUbb8S46S4eS4cVn;Vst;A2S0S1bS1cS3fS28Vn;A1Vst;A2Z0M0S9G0A1A3S1S1bA1A3A6").
Lemma fni_cert_0 : fni_cert 0 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fni_cert_1 : fni_cert 1 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fni_ecert_0 : fni_ecert 0 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fni_ecert_1 : fni_ecert 1 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertFreeNullInit.

(* [comment removed for export] *)
Module SegQsep.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "pow"; "mul"; "div"; "sub"; "leb"; "of_nat"; "eqb"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "qb_addr"; "aa_geom"; "ag_spacebeg"; "qb_items"; "AA"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "@Stdlib.Lists.List"; "In"; "Exists"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "mkACell"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "it_ab"; "it_cls"; "qitems"; "q_ids"; "it_id"; "qb_id"; "@Corelib.Init.Datatypes"; "prod"; "snd"; "app"; "bool"; "option"; "true"; "list"; "fst"; "andb"; "nil"; "cons"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "Size"; "is_primary"; "HIGH_SHADOW_END"; "kUserSpaceSize"; "rz"; "kSpaceSize"; "ClassID"; "kQuarantineBatchCount"; "kQuarantineBatchSize"; "needed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep"; "qlinks_to"; "ifoot"; "bfoot"; "hd_addr"; "last_addr"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "batch_mem"; "cls_of"; "item_mem"; "batch_pure"; "item_pure"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "live_ids"; "qlinks"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base list.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Inv SegQ_defs SegQ_wf2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Lemma kUserSpaceSize_val : ltac2:(tb__ "0|1|
SdS0S3aS8S5Z2M0Z20A2S5G0Z1dA2A2A3"). Proof. reflexivity. Qed.
Lemma rz_facts : ltac2:(tb__ "0|2|
S0ScScS1Z10M0S3bR1A1M1A2S1G1Z800A2A2SdS0S3G1G0A2Z0A3A2Fn;").
Proof.
  intros n. unfold rz, rz_log.
  destruct (n <=? 48); [|destruct (n <=? 96); [|destruct (n <=? 448); [|destruct (n <=? 3968); [|destruct (n <=? 16128); [|destruct (n <=? 32256); [|destruct (n <=? 64512)]]]]]];
  (split; [split|]); vm_compute; try reflexivity; intros HH; discriminate HH.
Qed.

Lemma item_geometry : ltac2:(tb__ "0|2|
S0S1Z1R1A2M0SdS2cS38R2A1S2eA3S3dS40R3A1A1S0ScScG0S1R1Z1eA2A2ScS1S2R4S3bR4A1A2S37R1A1M1A2ScSdS0S3G1Z10A2Z0A3S1R4Zfc00A2A2A2A2Tc;F_;F_;Fn;").
Proof.
  intros n Hn Hp c.
  assert (Hle : n <= 64512).
  { destruct (Z_lt_dec 64512 n) as [H|H]; [|lia]. rewrite (not_primary_large n ltac:(lia)) in Hp. discriminate Hp. }
  pose proof (slot_ok_all n ltac:(lia)) as S. unfold slot_ok, slot in S.
  apply andb_prop in S as [S S5]. apply andb_prop in S as [S S4]. apply andb_prop in S as [S S3]. apply andb_prop in S as [S1 S2].
  apply Z.leb_le in S2. apply Z.eqb_eq in S3. apply Z.leb_le in S4. apply Z.leb_le in S5. fold c in S2, S3, S4, S5.
  unfold needed, round_up in S2. split; [lia|]. split; [|split; [exact S3 | exact Hle]].
  pose proof (Z.div_mod (Z.max n kChunkHeader2Size + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n kChunkHeader2Size + 8 - 1) 8 ltac:(lia)).
  unfold kChunkHeader2Size in *. lia.
Qed.

Definition size_okb (c : Z) : bool := ltac2:(tb__ "0|2|
S31S31S9Z10M0S37Vc;A1M1A2S9G1Z10000A2A2SbS3G1G0A2Z0A2A2").
Lemma Size_facts : ltac2:(tb__ "0|2|
S0ScS1Z1R1A2S1R1Z1eA2A2ScScS1Z10M0S37R2A1M1A2S1G1Z10000A2A2SdS0S3G1G0A2Z0A3A2F_;Fc;").
Proof.
  intros c Hc. pose proof (forall_rangeZ_ok size_okb 1 30 c ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(lia)) as H.
  unfold size_okb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
Qed.

Lemma Sh_lt_HSE : ltac2:(tb__ "0|0|
S0ScS1Z0R1A2S4R1S5Z2Z2fA2A2A2S4S36R2A1S39A2F_;Fa;").
Proof. intros a Ha. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma shadow_zone_in_slot : ltac2:(tb__ "0|5|
S0S0S0S0SdS0S3R4Z8M0A2Z0M1A3M2G2SdS0S3R3G0A2G1A3S1G1R6A2M3G3S1S2R7R8A2R6A2ScS1S36RaA1S36S2RaR9A2A1M4A2S1S2G4S7S2R8Z7A2G0A2A2S36S2RaR7A2A1A2A2F_;F_;F_;F_;F_;F_;FS;Fn;Fr;Fab;").
Proof.
  intros ab r n S Hab Hr HS8 Hr0 Hn HS. split; [apply Sh_mono; lia|]. unfold Sh.
  pose proof (Z.div_mod ab 8 ltac:(lia)) as D1. pose proof (Z.div_mod r 8 ltac:(lia)) as D2. pose proof (Z.div_mod S 8 ltac:(lia)) as D3.
  rewrite Hab in D1. rewrite Hr in D2. rewrite HS8 in D3.
  set (qa := ab / 8) in *. set (qr := r / 8) in *. set (qs := S / 8) in *.
  replace (ab + r) with ((qa + qr) * 8) by lia. rewrite Z.div_mul by lia.
  replace (ab + S) with ((qa + qs) * 8) by lia. rewrite Z.div_mul by lia.
  pose proof (Z.div_le_mono (n + 7) ((qs - qr) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as M.
  replace ((qs - qr) * 8 + 7) with (7 + (qs - qr) * 8) in M by lia. rewrite Z.div_add in M by lia. cbn in M. lia.
Qed.

Lemma NoDup_map_In_inj : forall {X Y} (f : X -> Y) (l : list X) x y,
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros X Y f l. induction l as [|a l IH]; intros x y HN Hx Hy Hf; [destruct Hx|].
  cbn [map] in HN. apply NoDup_cons in HN as [Ha HN].
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y HN Hx Hy Hf)].
  - exfalso. apply Ha. apply list_elem_of_In. apply in_map_iff. exists y. split; [symmetry; exact Hf | exact Hy].
  - exfalso. apply Ha. apply list_elem_of_In. apply in_map_iff. exists x. split; [exact Hf | exact Hx].
Qed.
Lemma NoDup_app_disj : forall {X} (l k : list X) (x : X), NoDup (l ++ k) -> In x l -> In x k -> False.
Proof.
  intros X l k x HN Hl Hk. apply NoDup_app in HN as (_ & H & _). apply (H x); apply list_elem_of_In; assumption.
Qed.
Lemma NoDup_app_l : forall {X} (l k : list X), NoDup (l ++ k) -> NoDup l.
Proof. intros X l k HN. apply NoDup_app in HN as (H & _ & _). exact H. Qed.
Lemma NoDup_app_r : forall {X} (l k : list X), NoDup (l ++ k) -> NoDup k.
Proof. intros X l k HN. apply NoDup_app in HN as (_ & _ & H). exact H. Qed.

Section QSep.
Variable A : AA.
Let G : ageom := aa_geom A.
Let SB : Z := ag_spacebeg (aa_geom A).
Hypothesis HQP : q_pure A.
Hypothesis HIDS : ltac2:(tb__ "0|2|
S0ScS1Z1R1A2S1R1Z1eA2A2S4fS0S2bS0S1aS48VA;R2A2M0A1S2bS0S19G0A1S2bS0S4dS14VA;A1M1VA;R2A3S26G1S22VA;A1R2A3A3A3A3A2F_;Fc;").
Hypothesis HAU : ltac2:(tb__ "0|1|
S0ScS1Z1R1A2S1R1Z1eA2A2ScS1Z0S18S48VA;R2A2A1M0A2S1G0S3aA2A2F_;Fc;").
Hypothesis HG : geom_ok (aa_geom A).

Lemma SB_facts : ltac2:(tb__ "0|1|
ScSdS0S3S15S14VA;A1A1M0S5Z2Z10A2A2Z0A3ScS1S39G0A2S1S2S2G0S3cA2Z1000A2Z7fffff800000A2A2A2").
Proof.
  pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  pose proof (topG_range (aa_geom A)) as TG. rewrite kSpaceSize_val. unfold HIGH_SHADOW_END. split; [exact H1 | split; [exact H2 | lia]].
Qed.

Lemma batch_slot : ltac2:(tb__ "0|8|
S12S1bS12R1S22VA;A1A3S10S0S0ScSdS0S13R3A1M0S2S2S15S14VA;A1A1M1S6Z18S5Z2Z20A2M2A2A2S6Z10R1A2M3A2A3ScS1Z0M4R1A2ScSdS0S3R1Z200A2G4A3ScS1S2G3Z2000M5A2S3aA2ScS1S39G0A2ScS1S2G0G5A2S2G1S6Z19G2A2A2A2ScSdS0S3G0G5A2G4A3ScS1SaS34S29S0S0A2M6S16R3A1M7A2A1S3eA2S4cG6S4bVA;A1G7A3A2A2A2A2A2A2A2A2Ly;A2F_;Fb;").
Proof.
  intros b Hb. destruct HQP as [HBP _]. pose proof (proj1 (List.Forall_forall _ _) HBP b Hb) as (B1 & B2 & (y & E & Y0 & Yal & Y1) & B4).
  pose proof SB_facts as (S1 & S2 & S3). pose proof (HAU 24 ltac:(lia)) as AU. unfold kQuarantineBatchSize in Y1.
  unfold region_beg, kRegionSize in E. pose proof kUserSpaceSize_val as KU.
  exists y. split; [exact E|]. split; [exact Y0|]. split; [exact Yal|]. split; [lia|]. split; [exact B1|]. split; [lia|]. split; [|split; [exact B2 | exact B4]].
  rewrite E. pose proof (Z.div_mod (ag_spacebeg (aa_geom A)) (2 ^ 16) ltac:(lia)) as D. rewrite S1, Z.add_0_r in D.
  pose proof (Z.div_mod y 512 ltac:(lia)) as Dy. rewrite Yal, Z.add_0_r in Dy.
  rewrite D, Dy. replace (2 ^ 16 * (ag_spacebeg (aa_geom A) `div` 2 ^ 16) + 24 * 2 ^ 32 + 16 * (512 * (y `div` 512)))
    with ((8 * (ag_spacebeg (aa_geom A) `div` 2 ^ 16) + 24 * 2 ^ 19 + y `div` 512) * 8192) by lia. apply Z.mod_mul. lia.
Qed.

Lemma qitems_In : ltac2:(tb__ "0|2|
S29S0S0A2M0S1bG0R1S25S22VA;A1M1A1A3S10S12S12ScS1bS12R1G1A3S1bG0R3S16R1A1A3A2Lb;A2F_;Fit;").
Proof. intros it H. unfold qitems in H. apply in_flat_map in H. exact H. Qed.

Lemma item_slot : ltac2:(tb__ "0|a|
S29S0S0A2M0S1bG0R1S25S22VA;A1A1A3SdS2cS38S2aS0S0R2A3A1S2eA3S24R3A1S0S23R4A1S0S37R2A1S0S2S15S14VA;A1A1M1S6R3S5Z2Z20A2A2A2S0ScScS1Z1M2R4A2S1R4Z1eA2A2ScS1R1R3A2ScSdS0S3S8R3R1A2M3R2A2Z0M4A3ScS1S2G3R2A2S3aA2ScSdS0S3R3Z10M5A2G4A3ScScS1G5R2A2S1R2Z10000A2A2ScSdS0S3R2G5A2G4A3ScScS1G5S3bS2aS0S0R7A3M6A1M7A2S1G7Z800A2A2ScSdS0S3G7G5A2G4A3ScSdS0S30S0S0R7A3M8S2R3G7A2A3ScS1S2G8G6A2S2R3R2A2M9A2ScScS1G2G6A2S1G6Zfc00A2A2ScS1S39R3A2S1G9S2G1S3cA2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Trb;TS;Tab;Tc;F_;F_;Fit;").
Proof.
  intros it Hit Hp. cbv zeta. unfold it_cls, it_ab in *. destruct (qitems_In it Hit) as (b & Hb & Hin).
  destruct (batch_slot b Hb) as (y & _ & _ & _ & _ & _ & _ & _ & _ & HIP).
  pose proof (proj1 (List.Forall_forall _ _) HIP it Hin) as (I1 & I2 & I3 & _). specialize (I3 Hp). cbv zeta in I3. destruct I3 as (I3a & I3b & I3c).
  pose proof (item_geometry (snd it) I2 Hp) as (J1 & J2 & J3 & J4). pose proof (rz_facts (snd it)) as (R1 & R2). pose proof (Size_facts _ J1) as (Z1 & Z2).
  pose proof SB_facts as (S1 & S2 & S3). pose proof (HAU _ J1) as AU. pose proof kUserSpaceSize_val as KU. pose proof kSpaceSize_val as KS.
  unfold region_beg, kRegionSize in I3a, I3b, I3c.
  set (c := ClassID (needed (snd it))) in *. set (S := Size c) in *. set (sb := ag_spacebeg (aa_geom A)) in *.
  set (u := fst it) in *. set (n := snd it) in *.
  split; [exact J1|]. split; [exact I3a|]. split; [exact I3b|]. split; [lia|]. split.
  {
    pose proof (Z.div_mod (u - rz n - (sb + c * 2 ^ 32)) S ltac:(lia)) as D. rewrite I3b, Z.add_0_r in D.
    pose proof (Z.div_mod S 16 ltac:(lia)) as DS. rewrite Z2, Z.add_0_r in DS.
    pose proof (Z.div_mod sb (2 ^ 16) ltac:(lia)) as DB. rewrite S1, Z.add_0_r in DB.
    replace (u - rz n) with ((u - rz n - (sb + c * 2 ^ 32)) + (sb + c * 2 ^ 32)) by lia. rewrite D. rewrite DB at 2. rewrite DS at 1.
    replace (16 * (S `div` 16) * ((u - rz n - (sb + c * 2 ^ 32)) `div` S) + (2 ^ 16 * (sb `div` 2 ^ 16) + c * 2 ^ 32))
      with (((S `div` 16) * ((u - rz n - (sb + c * 2 ^ 32)) `div` S) + 2 ^ 12 * (sb `div` 2 ^ 16) + c * 2 ^ 28) * 16) by lia.
    apply Z.mod_mul. lia. }
  split; [exact Z1|]. split; [exact Z2|]. split; [exact R1|]. split; [exact R2|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; lia.
Qed.

Lemma batches_apart : ltac2:(tb__ "0|4|
S12S12S1bS12R2S22VA;A1A3M0G0SeSdS0S13R4A1M1S13R3A1A3A1SfS1S2S13R5A1M2Z2000M3A2G1A2S1S2G1G3A2G2A2A2F_;F_;F_;Fb2;Fb1;").
Proof.
  intros b1 b2 H1 H2 Hne.
  destruct (batch_slot b1 H1) as (y1 & E1 & _ & _ & _ & _ & _ & M1 & _). destruct (batch_slot b2 H2) as (y2 & E2 & _ & _ & _ & _ & _ & M2 & _).
  pose proof (Z.div_mod (qb_addr b1) 8192 ltac:(lia)) as D1. pose proof (Z.div_mod (qb_addr b2) 8192 ltac:(lia)) as D2.
  rewrite M1, Z.add_0_r in D1. rewrite M2, Z.add_0_r in D2.
  assert (qb_addr b1 `div` 8192 <> qb_addr b2 `div` 8192) by (intros E; apply Hne; lia). lia.
Qed.

Lemma qall_split_ne : ltac2:(tb__ "0|1|
S2fS12A1M0S12G0S12SdG0S22VA;A1S2bS12R4S33S12R3R2A3A3A3S1bS12R2S2bS12R5R3A3A3SeSdS0S13R3A1S13R5A1A3A1F_;F_;Fb';Fl2;Fb;Fl1;").
Proof.
  intros l1 b l2 b' E Hin Heq. destruct HQP as [_ HND]. rewrite E, map_app in HND. cbn [map] in HND.
  apply NoDup_app in HND as (N1 & N12 & N2). apply NoDup_cons in N2 as [Nb N2].
  apply in_app_or in Hin as [Hin|Hin].
  - apply (N12 (qb_addr b')); [apply list_elem_of_In; apply in_map; exact Hin | apply list_elem_of_In; left; symmetry; exact Heq].
  - apply Nb. apply list_elem_of_In. rewrite <- Heq. apply in_map. exact Hin.
Qed.

Lemma q_ids_item : ltac2:(tb__ "0|3|
S29S0S0A2M0S0S1bG0R2S25S22VA;A1M1A1A3SdS2cS38S2aS0S0R3A3A1S2eA3SdS0S24R4A1R3A3S1bS0S27S14VA;A1M2R5A2S26G2G1R4A3A3F_;F_;F_;Fc;Fit;").
Proof.
  intros it c Hit Hp Hc. unfold q_ids. apply in_or_app. left. apply in_map. apply filter_In. split; [exact Hit|].
  rewrite Hp, Hc, Z.eqb_refl. reflexivity.
Qed.
Lemma q_ids_batch : ltac2:(tb__ "0|2|
S12S1bS12R1S22VA;A1M0A3S1bS0S28S14VA;A1M1R2A2S26G1G0Z18A3A3F_;Fb;").
Proof. intros b Hb. unfold q_ids. apply in_or_app. right. rewrite Z.eqb_refl. apply in_map. exact Hb. Qed.

Lemma item_batch_apart : ltac2:(tb__ "0|4|
S29S0S0A2M0S12S1bG0R2S25S22VA;A1M1A1A3SdS2cS38S2aS0S0R3A3A1S2eA3S1bS12R3G1A3SfS1S2S23R5A1M2S37S24R5A1A1A2S13R4A1M3A2S1S2G3Z2000A2G2A2A2F_;F_;F_;Fb;Fit;").
Proof.
  intros it b Hit Hp Hb.
  pose proof (item_slot it Hit Hp) as IS. cbv zeta in IS. destruct IS as (C1 & R1 & M1 & U1 & _ & Z1 & _).
  destruct (batch_slot b Hb) as (y & E & Y0 & Yal & Y1 & _ & _ & M2 & _).
  pose proof kUserSpaceSize_val as KU.
  destruct (Z.eq_dec (it_cls it) 24) as [E24|N24].
  -
    rewrite E24 in *. change (Size 24) with 8192 in *.
    assert (Hne : it_id (aa_geom A) it <> qb_id (aa_geom A) b).
    { intros EQ. pose proof (HIDS 24 ltac:(lia)) as ND.
      apply NoDup_app_r in ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND.
      unfold q_ids in ND. rewrite Z.eqb_refl in ND.
      apply (NoDup_app_disj _ _ (it_id (aa_geom A) it) ND).
      + apply in_map. apply filter_In. split; [exact Hit|]. rewrite Hp, E24. reflexivity.
      + rewrite EQ. apply in_map. exact Hb. }
    unfold it_id, qb_id, ptr_to_compact, region_beg, kRegionSize, kCompactPtrScale in Hne. rewrite E24 in Hne.
    rewrite !Z.shiftr_div_pow2 in Hne by lia. change (2 ^ 4) with 16 in Hne.
    pose proof (Z.div_mod (it_ab it - (ag_spacebeg (aa_geom A) + 24 * 2 ^ 32)) 8192 ltac:(lia)) as D1. rewrite M1, Z.add_0_r in D1.
    rewrite E in Hne |- *.
    replace (ag_spacebeg (aa_geom A) + 24 * 2 ^ 32 + 16 * y - (ag_spacebeg (aa_geom A) + 24 * 2 ^ 32)) with (y * 16) in Hne by lia.
    rewrite Z.div_mul in Hne by lia.
    set (q := (it_ab it - (ag_spacebeg (aa_geom A) + 24 * 2 ^ 32)) `div` 8192) in *.
    replace (it_ab it - (ag_spacebeg (aa_geom A) + 24 * 2 ^ 32)) with (q * 512 * 16) in Hne by lia. rewrite Z.div_mul in Hne by lia.
    pose proof (Z.div_mod y 512 ltac:(lia)) as Dy. rewrite Yal, Z.add_0_r in Dy.
    assert (q <> y `div` 512) by (intros EQ; apply Hne; lia). lia.
  -
    assert (it_cls it <= 23 \/ 25 <= it_cls it) as [Hlt|Hgt] by lia; [left | right]; nia.
Qed.

Lemma items_apart : ltac2:(tb__ "0|5|
S29S0S0A2M0G0S1bG0R2S25S22VA;A1A1A3M1G1SdS2cS38S2aS0S0R4A3A1S2eA3M2G2SeSdG0R6R5A3A1SfS1S2S23R7A1M3S37S24R7A1A1A2S23R6A1M4A2S1S2G4S37S24R6A1A1A2G3A2A2F_;F_;F_;F_;F_;Fit2;Fit1;").
Proof.
  intros it1 it2 H1 H2 P1 P2 Hne.
  pose proof (item_slot it1 H1 P1) as IS1. cbv zeta in IS1. destruct IS1 as (C1 & R1 & M1 & U1 & _ & Z1 & ZM1 & _ & _ & E1 & _).
  pose proof (item_slot it2 H2 P2) as IS2. cbv zeta in IS2. destruct IS2 as (C2 & R2 & M2 & U2 & _ & Z2 & ZM2 & _ & _ & E2 & _).
  pose proof kUserSpaceSize_val as KU.
  destruct (Z.eq_dec (it_cls it1) (it_cls it2)) as [EC|NC].
  - rewrite <- EC in *. set (c := it_cls it1) in *. set (rb := ag_spacebeg (aa_geom A) + c * 2 ^ 32) in *. set (S := Size c) in *.
    assert (Hid : it_id (aa_geom A) it1 <> it_id (aa_geom A) it2).
    { intros EQ. apply Hne. pose proof (HIDS c C1) as ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND.
      unfold q_ids in ND. apply NoDup_app_l in ND.
      apply (NoDup_map_In_inj (it_id (aa_geom A)) _ it1 it2 ND); [apply filter_In | apply filter_In | exact EQ].
      + split; [exact H1|]. rewrite P1. fold c. rewrite Z.eqb_refl. reflexivity.
      + split; [exact H2|]. rewrite P2, <- EC, Z.eqb_refl. reflexivity. }
    unfold it_id, ptr_to_compact, region_beg, kRegionSize, kCompactPtrScale in Hid. rewrite <- EC in Hid. fold c rb in Hid.
    rewrite !Z.shiftr_div_pow2 in Hid by lia. change (2 ^ 4) with 16 in Hid.
    pose proof (Z.div_mod (it_ab it1 - rb) S ltac:(lia)) as D1. rewrite M1, Z.add_0_r in D1.
    pose proof (Z.div_mod (it_ab it2 - rb) S ltac:(lia)) as D2. rewrite M2, Z.add_0_r in D2.
    pose proof (Z.div_mod S 16 ltac:(lia)) as DS. rewrite ZM1, Z.add_0_r in DS.
    set (q1 := (it_ab it1 - rb) `div` S) in *. set (q2 := (it_ab it2 - rb) `div` S) in *. set (s16 := S `div` 16) in *.
    assert (q1 <> q2).
    { intros EQ. apply Hid. rewrite D1, D2, DS, EQ. reflexivity. }
    first [ clearbody q1 q2 s16; clear - D1 D2 H Z1; nia | nia ].
  - assert (it_cls it1 + 1 <= it_cls it2 \/ it_cls it2 + 1 <= it_cls it1) as [Hlt|Hgt] by lia; [left | right]; nia.
Qed.

Lemma item_zones : ltac2:(tb__ "0|7|
S29S0S0A2M0S1bG0R1S25S22VA;A1A1A3SdS2cS38S2aS0S0R2A3A1S2eA3S23R3A1S0S37S24R4A1A1S0S30S0S0R5A3S0S2aS0S0R6A3S0ScS1R4S8R2Z10M1A2A2ScS1S2R2R1A2S2R4R3A2M2A2ScS1S2R4G1A2S2S2R2Z0M3A2R3A2A2ScS1S36R4A1S36R2A1M4A2ScS1S2G4S7S2R1Z7A2Z8M5A2A2S36G2A1M6A2ScS4G6S39A2SdS0S3R2G5A2G3A3A2A2A2A2A2A2Tn;Tu;TS;Tab;F_;F_;Fit;").
Proof.
  intros it Hit Hp. cbv zeta. pose proof (item_slot it Hit Hp) as IS. cbv zeta in IS.
  destruct IS as (C1 & R1 & M1 & U1 & A16 & Z1 & Z2 & RZ & RZ16 & EU & UN & N1 & HS & TOP).
  pose proof kSpaceSize_val as KS. pose proof SB_facts as (_ & _ & S3).
  assert (U8 : fst it mod 8 = 0).
  { rewrite EU. rewrite Z.add_mod by lia. replace (it_ab it `mod` 8) with 0. 2:{ pose proof (Z.div_mod (it_ab it) 16 ltac:(lia)). rewrite A16 in H. symmetry. rewrite H. replace (16 * (it_ab it `div` 16) + 0) with ((2 * (it_ab it `div` 16)) * 8) by lia. apply Z.mod_mul. lia. }
    replace (rz (snd it) `mod` 8) with 0. 2:{ pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)). rewrite RZ16 in H. symmetry. rewrite H. replace (16 * (rz (snd it) `div` 16) + 0) with ((2 * (rz (snd it) `div` 16)) * 8) by lia. apply Z.mod_mul. lia. }
    reflexivity. }
  split; [lia|]. split; [lia|]. split; [lia|].
  destruct (shadow_zone_in_slot (it_ab it) (rz (snd it)) (snd it) (Size (it_cls it))) as [X1 X2].
  { pose proof (Z.div_mod (it_ab it) 16 ltac:(lia)) as D. rewrite A16 in D. rewrite D. replace (16 * (it_ab it `div` 16) + 0) with ((2 * (it_ab it `div` 16)) * 8) by lia. apply Z.mod_mul. lia. }
  { pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as D. rewrite RZ16 in D. rewrite D. replace (16 * (rz (snd it) `div` 16) + 0) with ((2 * (rz (snd it) `div` 16)) * 8) by lia. apply Z.mod_mul. lia. }
  { pose proof (Z.div_mod (Size (it_cls it)) 16 ltac:(lia)) as D. rewrite Z2 in D. rewrite D. replace (16 * (Size (it_cls it) `div` 16) + 0) with ((2 * (Size (it_cls it) `div` 16)) * 8) by lia. apply Z.mod_mul. lia. }
  { lia. } { lia. } { lia. }
  rewrite EU at 1 2. split; [exact X1|]. split; [exact X2|]. split; [|exact U8]. apply Sh_lt_HSE. unfold HIGH_SHADOW_END in HS. lia.
Qed.
End QSep.

Definition hd_addr (l : list qbatch) : Z := qb_addr (List.hd qb_dflt l).
Definition last_addr (l : list qbatch) : Z := qb_addr (List.last l qb_dflt).

Definition ifoot (it : Z * Z) (z : Z) : Prop := ltac2:(tb__ "0|2|
SfScS1S23Vit;A1Vz;A2S4Vz;S30S0S0Vit;A3M0A2A2ScS1S36G0A1M1Vz;A2S4Vz;S2G1S7S2S2aS0S0Vit;A3Z7A2Z8A2A2A2A2A2").
Definition bfoot (b : qbatch) (z : Z) : Prop := ltac2:(tb__ "0|2|
SfScS1S2S13Vb;A1M0Z8A2Vz;A2S4Vz;S2G0S3fA2A2A2S1cS29S0S0A2M1G1S42R1Vz;A2Lit;S16Vb;A1A3A2").

Lemma cell_ok_frame1 : ltac2:(tb__ "0|0|
S1eS1eS0S35S0S0ScS1R4R1A2S4R1S2R4SaR3A1A2A2A2SdS2dS46Q8A1A1R6R2A1R7R2A1A3F_;Fz;S1fR6S20R4R3R2A3A2S1fR6S20R5R4R3A3A2F_;F_;Fv;Fk;Fa;Fm';Fm;").
Proof. intros m m' a k v Hm Hc j Hj. cbn [c_addr c_w c_val] in *. rewrite Hm by lia. exact (Hc j Hj). Qed.
Lemma present_frame : ltac2:(tb__ "0|0|
S1eS1eS0S0S0ScS1R3R1A2S4R1R2A2A2SdS2dS46Q8A1A1R5R2A1R6R2A1A3F_;Fz;S21R5R3R2A3S21R5R4R3A3F_;F_;Fhi;Flo;Fm';Fm;").
Proof. intros m m' lo hi Hm Hp z Hz. rewrite Hm by lia. exact (Hp z Hz). Qed.

Lemma item_mem_frame : ltac2:(tb__ "0|0|
S1eS1eS29S0S0A2S1Z10S3bS2aS0S0R1A3A1A2S0S42R3R1A2SdS2dS46Q8A1A1R5R2A1R6R2A1A3F_;Fz;S49R5R3A2S49R5R4A2F_;F_;F_;Fit;Fm';Fm;").
Proof.
  intros m m' it Hrz Hm (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold ifoot, it_ab in Hm.
  assert (HL : forall z, fst it - rz (snd it) <= z < fst it -> m' z = m z) by (intros z Hz; apply Hm; left; lia).
  split; [rewrite HL by lia; exact H1|]. split; [eapply present_frame; [|exact H2]; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H3]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H4]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply present_frame; [|exact H5]; intros z Hz; apply HL; lia|].
  split.
  - unfold alloc_magic_ok in *. destruct H6 as [H6|[H6a H6b]]; [left; exact H6 | right].
    split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply HL; lia.
  - eapply present_frame; [|exact H7]. intros z Hz. apply Hm. right. exact Hz.
Qed.

Lemma batch_mem_frame : ltac2:(tb__ "0|0|
S17S1eS1eS12S4aR4R1A2S0S43R3R1A2SdS2dS46Q8A1A1R5R2A1R6R2A1A3F_;Fz;S47R5R3A2S47R5R4A2F_;F_;F_;Fb;Fm';Fm;FA;").
Proof.
  intros A m m' b (_ & HL & _ & HP) Hm (H1 & H2 & H3 & H4 & H5). unfold bfoot, kQuarantineBatchSize in Hm. unfold kQuarantineBatchCount in HL.
  assert (HB : forall z, qb_addr b + 8 <= z < qb_addr b + 8192 -> m' z = m z) by (intros z Hz; apply Hm; left; exact Hz).
  split; [eapply cell_ok_frame1; [|exact H1]; cbn; intros z Hz; apply HB; lia|].
  split; [eapply cell_ok_frame1; [|exact H2]; cbn; intros z Hz; apply HB; lia|].
  split; [exact H3|]. split; [eapply present_frame; [|exact H4]; intros z Hz; apply HB; unfold kQuarantineBatchSize in Hz; lia|].
  intros i it Hi. destruct (H5 i it Hi) as [C I]. pose proof (nth_error_In _ _ Hi) as Hin.
  assert (Hi' : (i < length (qb_items b))%nat) by (apply (proj1 (nth_error_Some (qb_items b) i)); rewrite Hi; discriminate).
  split.
  - eapply cell_ok_frame1; [|exact C]. cbn. intros z Hz. apply HB. lia.
  - eapply item_mem_frame; [apply (proj1 (rz_facts (snd it))) | | exact I]. intros z Hz. apply Hm. right. apply Exists_exists. exists it. split; [|exact Hz].
    apply list_elem_of_In. exact Hin.
Qed.

Fixpoint qlinks_to (m : bview) (l : list qbatch) (t : Z) : Prop :=
  match l with
  | [] => True
  | b :: r => cell_ok m (mkACell (qb_addr b) 8 (match r with [] => t | b' :: _ => qb_addr b' end)) /\ qlinks_to m r t
  end.
Lemma qlinks_to_0 : ltac2:(tb__ "0|0|
S1eS2fS12A1S11S4eR2R1A2S41R2R1Z0A3A2Fl;Fm;").
Proof. intros m l. induction l as [|b r IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma qlinks_to_app : ltac2:(tb__ "0|1|
S1eS2fS12A1M0G0S0SeSdG0R2S32S12A1A3A1S41R5R4S44R3A1A3S41R6R4R3A3S41R7S2bS12R6R5A3R4A3F_;F_;F_;Ft;Fl2;Fl1;Fm;").
Proof.
  intros m l1 l2 t Hne H1 H2. induction l1 as [|b r IH]; cbn in *; [exact H2|]. destruct H1 as [Hc Hr]. split; [|exact (IH Hr)].
  destruct r as [|b' r']; cbn; [|exact Hc]. destruct l2 as [|c l2']; [congruence|]. cbn. unfold hd_addr in Hc. cbn in Hc. exact Hc.
Qed.
Lemma qlinks_to_frame : ltac2:(tb__ "0|1|
S1eS1eS2fS12A1S0S12S0S1bS12R2R4A3ScS1S13R3A1M0R2A2S4R2S2G0Z8A2A2A2SdS2dS46Q8A1A1R7R3A1R8R3A1A3F_;F_;Fz;Fb;S41R5R3R2A3S41R5R4R3A3F_;F_;Ft;Fl;Fm';Fm;").
Proof.
  intros m m' l. induction l as [|b r IH]; intros t Hm H; cbn in *; [exact I|]. destruct H as [Hc Hr]. split.
  - eapply cell_ok_frame1; [|exact Hc]. cbn. intros z Hz. apply (Hm b); [left; reflexivity | lia].
  - apply IH; [|exact Hr]. intros b' z Hb' Hz. apply (Hm b'); [right; exact Hb' | exact Hz].
Qed.

Lemma qlinks_to_relast : ltac2:(tb__ "0|2|
S1eS1eS2fS12A1M0S0S0SeSdG0R3S32S12A1A3A1S12S0S1bS12R2S1dS12R6A2A3ScS1S13R3A1M1R2A2S4R2S2G1Z8A2A2A2SdS2dS46Q8A1A1R9R3A1RaR3A1A3F_;F_;Fz;Fb;S1fR6S20S45R5A1U8R3A3A2S41R8R6R5A3S41R8R7R5A3F_;F_;F_;F_;Ft';Ft;Fl;Fm';Fm;").
Proof.
  intros m m' l. induction l as [|b r IH]; intros t t' Hne Hm Hc H; [congruence|]. cbn in H |- *. destruct H as [Hb Hr].
  destruct r as [|b' r'].
  - split; [|exact I]. unfold last_addr in Hc. cbn in Hc. exact Hc.
  - split.
    + eapply cell_ok_frame1; [|exact Hb]. cbn. intros z Hz. apply (Hm b); [|lia]. cbn. left. reflexivity.
    + apply (IH t t'); [discriminate | | | exact Hr].
      * intros b0 z Hb0 Hz. apply (Hm b0); [|exact Hz]. cbn. destruct r' as [|b'' r'']; [destruct Hb0 | right; exact Hb0].
      * unfold last_addr in Hc |- *. cbn [last] in Hc. exact Hc.
Qed.
End SegQsep.

