(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool PArith FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From stdpp Require bitvector.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.

(* [comment removed for export] *)
Module SegD_glue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "rm"; "sstate"; "obj_range"; "ss_objs"; "SLit"; "eval"; "rw"; "sprop"; "smatch"; "SVar"; "holds"; "ss_facts"; "ss_regs"; "mkSS"; "rl"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_resv"; "sv_below"; "swf"; "cell"; "mkObj"; "ranges_disjoint"; "DUnknown"; "agree_below"; "DZero"; "enc_bytes"; "image_byte"; "ob_base"; "ob_hi"; "ob_lo"; "obj_holds"; "obj_wf"; "sprop_eqb"; "ss_next"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "bool"; "true"; "nil"; "fst"; "nat"; "option"; "app"; "cons"; "snd"; "None"; "Some"; "negb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "lt"; "of_nat"; "opp"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "existsb"; "NoDup"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_X"; "ax_S"; "ax_base"; "ax_setS"; "axwf"; "shadow_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue.SG"; "ro_win"; "skel"; "rho_sets"; "notin_b"; "notin_vars"; "inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "carved"; "cells_in_view"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "F_sp_high"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "obj_vars_all"; "@Stdlib.PArith.BinPos.Pos"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "win"; "win_bytes_in_frame"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA.
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
Module RebuildSM.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "pow"; "eqb"; "to_nat"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_fs_hint"; "aa_live"; "ag_fsb"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_frames"; "ageom"; "fs_alloc"; "aa_fs_busy"; "ag_ctx"; "ag_dtls"; "ag_thread"; "topG"; "@Corelib.Init.Datatypes"; "bool"; "list"; "pair"; "prod"; "app"; "cons"; "true"; "Some"; "length"; "false"; "fst"; "nat"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "enc_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "G0"; "RTC_A"; "cells_footb"; "in_rangesZ"; "rtc_cells_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_busy"; "busyb"; "fs_inv"; "geom_ok"; "live_sep"; "nthZ"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "fs_flags"; "fs_frame"; "fs_frame_size"; "fs_num_iter"; "HIGH_SHADOW_END"; "IMG_HI"; "SHADOW_OFF"; "fs_hint_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "client_addrA"; "client_shadowA"; "frame_flag"; "mem_keptA"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM.R"; "rt_zone"; "@Stdlib.Lists.List"; "In"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma busyb_of_split : ltac2:(tb__ "0|2|
SeS0S1fS21S0S0A2M0A1M1S0S0G1S2G1S35R6R5A2S22G0R4S23G0S20S0S0R3R2A4R1A3A3A3S2S1eS36R7R6R4A3S24A3F_;Fv;Ff;Fpos;Fu;Fc;FA;").
Proof.
  intros A c u pos f v E. unfold busyb. rewrite E, existsb_app. cbn [existsb fst]. rewrite Z.eqb_refl. cbn. apply orb_true_r.
Qed.

Lemma busyb_true_split : ltac2:(tb__ "0|2|
SeS0S0S2S1eS36R3R2R1A3S24A3S4S1fS21S0S0A2M0A1M1G1S4S0S0S4G1G1S1S2G1S35R7R6A2S22G0R3S23G0S20S0S0R5R2A4R1A3A3A3S5S4cS0R5S4dG0S0S28S0S0A2R3A4A3A1A2Lv;A2Lf;A2Lu;A2F_;Fpos;Fc;FA;").
Proof.
  intros A c pos H. unfold busyb in H. apply existsb_exists in H as ([p f] & Hin & E). cbn in E. apply Z.eqb_eq in E. subst p.
  revert Hin. generalize (fs_busy A c) as l. induction l as [|[p g] l IH]; intros Hin; [destruct Hin|].
  destruct (Z.eq_dec p pos) as [->|Hne].
  - exists [], g, l. split; [reflexivity | intros []].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; congruence|].
    destruct (IH Hin) as (u & f' & v & -> & Hn). exists ((p, g) :: u), f', v. split; [reflexivity|].
    cbn. intros [E|E]; [apply Hne; exact E | exact (Hn E)].
Qed.

Lemma fs_busy_alloc : ltac2:(tb__ "0|3|
SeS0S0S0S0S0S6Z0M0R5A2S6G0R2A2S3bScR7A1S26S1fS21S0S0A2M1A1M2S19R8A1A2A2S2G2S35S18R9R8R7R6R5A5R4A2S1eG2L_;SbR4R8A2S23G1S20S0S0R7R6A4S35R9R8A2A3S35R9R4A2X1ex2A3F_;F_;F_;Fc0;Fh;Ff;Fpos;Fc;FA;").
Proof.
  intros A c pos f h c0 Hc Hc0 Hlen. unfold fs_busy, nthZ, fs_alloc. cbn [aa_fs_busy].
  destruct (Z.eqb_spec c0 c).
  - subst c0. rewrite nth_list_upd_same by exact Hlen. reflexivity.
  - rewrite nth_list_upd_other; [reflexivity|]. intros E'. apply n. lia.
Qed.

Lemma fs_hint_alloc : ltac2:(tb__ "0|1|
SeS0S0S0S0S0S6Z0M0R5A2S6G0R2A2S3bScR7A1S26S0S10R8A1A2A2S2S0S3aS0S10S18R9R8R7R6R5A5A1R4G0A4S1eS0L_;SbR4R8A2R5S3aS0S10R9A1R4G0A4X1ex2A3F_;F_;F_;Fc0;Fh;Ff;Fpos;Fc;FA;").
Proof.
  intros A c pos f h c0 Hc Hc0 Hlen. unfold nthZ, fs_alloc. cbn [aa_fs_hint].
  destruct (Z.eqb_spec c0 c).
  - subst c0. rewrite nth_list_upd_same by exact Hlen. reflexivity.
  - rewrite nth_list_upd_other; [reflexivity|]. intros E'. apply n. lia.
Qed.

Section R.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma client_addr_cases : ltac2:(tb__ "0|5|
SeS0S2eS37R1R3A2S45VCST;R4R3A3S12SfR5A1A1S0S3S1S6S1dSfR6A1A1R5A2S7R5SaZ2Z2fA2A2A2S3S4S0S0S4S0S0S1S4cS21S0S0A2S20S0S0R2R1A4S11R8A1A3S1S6R2R7A2S7R7S8R2R1A2A2A2A2Ln;A2Lb;A2S3S4S0S0S4S0S0S1S1S6Z0M0R2A2S7R2ZbA2A2M1S1S1S6G0R1A2S7R1S40R2A1A2A2M2S1S2S1eS36R8R2R1A3S24A3M3S1S6S3eR3R2R1A3M4R7A2S7R7S8G4S3fR2A1A2A2A2A2A2A2Lp;A2Lc;A2S3S33VCST;R5A2S4S0S0S4S0S0S1G1S1G2S1G3S2S0R7S8S3dR3R2A2R1A2A3A2A2A2Lp;A2Lc;A2A2A2A2A2TF;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HF Hcl F.
  destruct Hcl as [[S|[L|[FR|C]]]|FL].
  - left. exact S.
  - right; left. exact L.
  - right; right; left. destruct FR as (f & s & Hin & Ha).
    destruct (aa_frames_fact _ A _ _ HF Hin) as (c & p & u & v & Hc & -> & Eb & _ & Hp & -> & _).
    exists c, p. split; [exact Hc|]. split; [exact Hp|]. split; [eapply busyb_of_split; exact Eb | exact Ha].
  - right; right; right; left. exact C.
  - right; right; right; right. destruct FL as ([f s] & Hin & ->).
    destruct (aa_frames_fact _ A _ _ HF Hin) as (c & p & u & v & Hc & Hs & Eb & _ & Hp & Hf & _). cbn [fst snd] in Hs, Hf.
    exists c, p. split; [exact Hc|]. split; [exact Hp|]. split; [eapply busyb_of_split; exact Eb |].
    unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite Hs, fs_class_of_size_ok by lia. fold F. rewrite Hf, fs_pos_frame by lia. reflexivity.
Qed.

Lemma client_addr_bounds : ltac2:(tb__ "0|0|
SeS0S2eS38SfR3A1A1S37R2R4A2S39R5A1S45VCST;R6R5A3S1S1S6Z0R6A2S7R6SaZ2Z2fA2A2A2S3S7R6Z7fff7000A2S6S8Z10007fff8000Z10A2R6A2A2A2F_;F_;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HG HF Hsep Hcl.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). rewrite FS_total_val in F2.
  pose proof (proj1 (geom_bands _ HG)) as WB. rewrite FS_total_val in WB.
  unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct (client_addr_cases A a m HF Hcl) as [S|[L|[FR|[C|FL]]]].
  - clear WB. lia.
  - clear WB. destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & _ & _ & _ & _ & S8).
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. lia.
  - clear WB. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
  - destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *.
    unfold IMG_HI in M. lia.
Qed.

Lemma client_shadow_bounds : ltac2:(tb__ "0|0|
SeS0S2eS38SfR3A1A1S37R2R4A2S39R5A1S46VCST;VXGL;R6R5A4S1S6S43R6A2S7R6S41A2A2F_;F_;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HG HF Hsep [(x & Hx & ->)|(x & Hx & ->)].
  - destruct (client_addr_bounds A x m HG HF Hsep Hx) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
  - destruct (HXGL x Hx). unfold Sh, SHADOW_OFF, HIGH_SHADOW_END, IMG_HI in *. lia.
Qed.

Definition rt_zone (G : ageom) (a : Z) : Prop := ltac2:(tb__ "0|5|
S3S1S1S6Z0Va;A2S7Va;S42A2A2S2S1eS32S34S31S30A2Va;A2S24A3A2S3S1S6S1cVG;A1M0Va;A2S7Va;S8G0Z1000M1A2A2A2S3S1S6S1aVG;A1M2Va;A2S7Va;S8G2G1A2A2A2S3S1S6S1bVG;A1M3Va;A2S7Va;S8G3G1A2A2A2S1S6S12VG;A1M4Va;A2S7Va;S8G4Z61A2A2A2A2A2A2A2").

Lemma client_not_rt : ltac2:(tb__ "0|0|
SeS0S2eS38SfR3A1A1S37R2R4A2S39R5A1S45VCST;R6R5A3S5S4bSfR7A1R6A2A1F_;F_;F_;F_;Fm;Fa;FA;").
Proof.

  intros A a m HG HF Hsep Hcl Hrt.
  pose proof (geom_nums _ HG) as (F1 & F2 & F0 & T1 & T2 & T0 & C1 & C2 & D1 & D2 & SP1 & SP2 & SP0 & TG).
  rewrite FS_total_val, kSpaceSize_val in *. unfold IMG_HI in F1.
  unfold rt_zone, IMG_HI in Hrt.
  destruct (client_addr_cases A a m HF Hcl) as [S|[L|[FR|[C|FL]]]].
  - lia.
  - destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & _). rewrite FS_total_val in S4.
    unfold IMG_HI in S2. lia.
  - destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M.
    pose proof (geom_seps _ HG) as (Q1 & Q2 & Q3 & _). rewrite FS_total_val in Q1, Q2, Q3. lia.
  - destruct (HCST _ C) as [X Y]. unfold IMG_LO, IMG_HI in X. destruct Hrt as [[_ R]|R]; [rewrite R in Y; discriminate|].
    pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & DI). unfold IMG_LO, IMG_HI in TI, CI, DI. lia.
  - destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *.
    pose proof (geom_seps _ HG) as (Q1 & Q2 & Q3 & _). rewrite FS_total_val in Q1, Q2, Q3. lia.
Qed.

Lemma sm_rebuild : ltac2:(tb__ "0|11|
S0SeS2cS2cS1fS4aQ40M0A1M1A1S4fS0G1S1S6Z0M2R8A2S7R8ZbA2A2VAInv;R8R7R5R4A4S1S6G2R4A2S7R4S40RaA1A2A2S2S1eS36RaRbR5A3S27A3SfRbA1S17S12R1A1S0S3eR1ReR8A3S0S8S3dR2RfA2R9A2S0S3fR10A1S0S44R4R11A2S0S2fVsegs;S2bRfA1A2S2eS2fVsegs;S2bR11A1A2S2eS2S2aS4aQ8M3A1M4A1M5R2R5A1S25G4S49G3Z1A2A2A3S0S1S6S3cR8A1M6R1A2S7R1S8G6S9R6Z8M7A2A2A2A2S2G5R5R2A1S25G4S49G3G2A2M8A2A3F_;Fz;S29S3bR1U8M9A2S2G5R6S8R7SdR2A1A2A1S25G4S4eG4R2S2dG9R11A2G8A4A2A3F_;Fj;S0S5S3S1S6R7R1A2S7R1S8R7G7A2A2A2S3S2S0R1R9A3S1S6S3cRaA1MaR1A2S7R1S8GaS9R8G7A2A2A2A2A2A2A1S2G5R7R2A1R6R2A1A3F_;Fz;S0S1S6G2R1A2S7R1SaZ2Z40A2A2A2S5S3S1S6R9R2A2S7R2S8R9G7A2A2A2S3S2S0R2RbA3S1S6S3cRcA1MbR2A2S7R2S8GbS9RaG7A2A2A2A2A2A2A1S5S4bRfR3A2A1S2G5S2bR19S49G0R4A2McA2S2bR1aGcA2A3F_;F_;F_;Fa;S4SeSeS4S1fS21S0S0A2MdA1MeGeS4GeGeS1VAInv;R3R19R18R17A4S1S2GeS11R3A1S11R1bA1A3S1S2GeS16R1bA1S22GdR2R1A3A3S1S2GeS16R3A1S22GdR2S23GdS20S0S0ReRcA4MfR1A3A3A3S1S2S0RdS47SfR1bA1M10GfA2A3S1S2S0S15R3A1S15R1bA1A3S1S2S0S14R3A1S14R1bA1A3S1S2S0S13R3A1S13R1bA1A3S1S2S17SfR3A1G10A3S48VCST;VXGL;R1bR3S2bR1aA1S2bR19A1A6A2A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2F_;F_;F_;F_;F_;TvE;Tv3;Thc;TS;Tfl;Tff;TF;TG;F_;F_;F_;F_;Fhw;Fpos;Fmd;Ftp;Frho3;FrhoE;FA;Fc;").
Proof.
  intros c A rhoE rho3 tp md pos hw Hc HA Hpos Hfree G F ff fl S hc v3 vE VF VS VH VO RMO.
  subst G.
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as NUM. cbn zeta in NUM. fold F ff S in NUM.
  destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10). fold fl in N6, N7.
  pose proof (topG_range (aa_geom A)) as TG. pose proof (proj1 (geom_bands _ HG)) as WB. fold F in WB.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in *. unfold IMG_HI in N8. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB.
  assert (SZ8 : 0 <= S / 8) by (apply Z.div_pos; lia).
  assert (ShF : Sh (F + 36864) <= Sh ff) by (apply Sh_mono; lia).
  assert (ShE : Sh ff + S / 8 <= Sh (F + 11571200)).
  { unfold Sh. replace (ff / 8 + SHADOW_OFF + S / 8) with ((ff + S) / 8 + SHADOW_OFF).
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    - replace ff with (ff / 8 * 8) at 1 by (pose proof (Z.div_mod ff 8); pose proof (Z.mod_divide ff 64); lia).
      rewrite Z.div_add_l by lia. lia. }
  assert (ShLo : 0x800b7600 <= Sh (F + 36864)) by (unfold Sh, SHADOW_OFF; lia).
  assert (ShHi : Sh (F + 11571200) < 17594333495296) by (unfold Sh, SHADOW_OFF; lia).
  assert (HCR : F <= hc /\ hc + 8 <= F + 88) by (unfold hc, fs_hint_cell; fold F; lia).

  assert (SHRT : forall a, 2147450880 <= a < 17594333495296 -> ~ rt_zone (aa_geom A) a).
  { intros a Ha. pose proof (geom_bands _ HG) as (BF & BT & BC & BD & _). fold F in BF.
    rewrite FS_total_val in BF. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BF, BT, BC, BD.
    unfold rt_zone, IMG_HI. fold F. intros [R|[R|[R|[R|R]]]]; [clear -Ha R; lia | clear -Ha R BT; lia | clear -Ha R BC; lia | clear -Ha R BD; lia | clear -Ha R BF; lia]. }
  destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh).
  fold F vE in Fhint, Fflags, Ffree, Fsh. rewrite FS_frames_off_val, FS_total_val in Fsh.
  assert (Hlenc : (Z.to_nat c < length (aa_fs_busy A))%nat) by (rewrite Flen; lia).
  assert (Hlenh : (Z.to_nat c < length (aa_fs_hint A))%nat) by (rewrite (proj1 Fhint); lia).

  set (h := bv_unsigned hw). pose proof (urange hw) as Hh. fold h in Hh.
  set (A' := fs_alloc A c pos ff h).
  assert (HB : nth_error (aa_fs_busy A) (Z.to_nat c) = Some (fs_busy A c)).
  { unfold fs_busy, nthZ. apply nth_error_nth'. exact Hlenc. }
  destruct (frames_of_insert (aa_fs_busy A) 0 (Z.to_nat c) (fs_busy A c) pos ff HB) as (l1 & l2 & E1 & E2).
  rewrite Z.add_0_l, Z2Nat.id in E2 by lia.
  assert (EBc : forall c0, 0 <= c0 -> fs_busy A' c0 = if c0 =? c then (pos, ff) :: fs_busy A c else fs_busy A c0).
  { intros c0 Hc0. apply fs_busy_alloc; lia. }
  assert (EBB : forall c0 p0, 0 <= c0 -> busyb A' c0 p0 = busyb A c0 p0 || ((c0 =? c) && (p0 =? pos))).
  { intros c0 p0 Hc0. unfold busyb. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
    - subst c0. cbn [existsb fst]. rewrite (Z.eqb_sym pos p0). destruct (p0 =? pos); cbn; [rewrite orb_true_r|rewrite orb_false_r]; reflexivity.
    - cbn [andb]. rewrite orb_false_r. reflexivity. }
  assert (Hnotin : ~ In pos (map fst (fs_busy A c))).
  { intros Hin. apply in_map_iff in Hin as ([p g] & E & Hin). cbn in E. subst p.
    unfold busyb in Hfree. assert (X : existsb (fun pf : Z * Z => fst pf =? pos) (fs_busy A c) = true); [|rewrite X in Hfree; discriminate].
    apply existsb_exists. exists (pos, g). split; [exact Hin | cbn; apply Z.eqb_refl]. }

  assert (HF' : fs_inv (restrictv (fs_footb (aa_geom A)) v3) A').
  { split; [|split; [|split; [|split; [|split]]]].
    - unfold A', fs_alloc. cbn [aa_fs_busy]. rewrite length_list_upd. exact Flen.
    - intros c0 Hc0. change (aa_geom A') with (aa_geom A). fold F. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
      + subst c0. destruct (Fcls c Hc) as [Hnd Hpf]. split.
        * cbn [map fst]. constructor; [exact Hnotin | exact Hnd].
        * intros pf [<-|Hin]; [cbn [fst snd]; split; [exact Hpos | reflexivity] | exact (Hpf pf Hin)].
      + exact (Fcls c0 Hc0).
    - change (aa_geom A') with (aa_geom A). fold F. destruct Fhint as [Hhl Fhint]. split.
      + unfold A', fs_alloc. cbn [aa_fs_hint]. rewrite length_list_upd. exact Hhl.
      + intros c0 Hc0. unfold A'. rewrite fs_hint_alloc by (unfold FS_NCLASSES in Hc0; lia). unfold FS_NCLASSES in Hc0.
        destruct (Z.eqb_spec c0 c).
        * subst c0. split; [exact Hh|]. intros k Hk. cbn [c_addr c_w c_val] in Hk |- *. fold hc.
          unfold restrictv. rewrite fs_footb_true1 by (fold F; lia). rewrite (VH k Hk). unfold h. rewrite Z_to_bv_bv_unsigned. reflexivity.
        * destruct (Fhint c0 Hc0) as [Hhr Hhc]. split; [exact Hhr|]. intros k Hk. specialize (Hhc k Hk).
          cbn [c_addr c_w c_val] in Hk, Hhc |- *. unfold fs_hint_cell in *.
          unfold restrictv in Hhc |- *. rewrite fs_footb_true1 in Hhc by (fold F; lia). rewrite fs_footb_true1 by (fold F; lia).
          rewrite VO by (unfold hc, fs_hint_cell; unfold Sh, SHADOW_OFF in *; lia). exact Hhc.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0. rewrite EBB by lia.
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      destruct (Z.eqb_spec c0 c); [destruct (Z.eqb_spec p0 pos)|].
      + subst c0 p0. rewrite Hfree. cbn [andb orb]. fold fl. exact VF.
      + cbn [andb]. rewrite orb_false_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite VO by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
      + cbn [andb]. rewrite orb_false_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite VO by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0 Hfree0 z Hz. rewrite EBB in Hfree0 by lia.
      apply orb_false_elim in Hfree0 as [Hfree0 Hne].
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      rewrite VO by (unfold Sh, SHADOW_OFF in *; lia).
      specialize (Ffree c0 p0 Hc0 Hp0 Hfree0 z Hz). unfold restrictv in Ffree.
      rewrite fs_footb_true2 in Ffree by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Ffree.
    - change (aa_geom A') with (aa_geom A). fold F. rewrite FS_frames_off_val, FS_total_val. intros z Hz.
      unfold restrictv. rewrite fs_footb_true3 by (fold F; rewrite FS_frames_off_val, FS_total_val; lia).
      destruct (Z_le_dec (Sh ff) z); [destruct (Z_lt_dec z (Sh ff + S / 8))|].
      1: exists (Z_to_bv 8 0); apply VS; lia.
      all: rewrite VO by (unfold Sh, SHADOW_OFF in *; lia); specialize (Fsh z Hz); unfold restrictv in Fsh;
           rewrite fs_footb_true3 in Fsh by (fold F; rewrite FS_frames_off_val, FS_total_val; lia); exact Fsh. }
  assert (HA' : AInv A' rho3 tp md).
  { apply (AInvA_fs_update segs A A' rhoE rho3 tp md HA).
    - unfold A', fs_alloc, same_but_fs. cbn. repeat split; reflexivity.
    - intros z Hz. fold v3 vE. apply VO. intros [X|[X|X]].
      + rewrite fs_footb_true1 in Hz by (fold F; lia). discriminate.
      + rewrite fs_footb_true2 in Hz by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). discriminate.
      + rewrite fs_footb_true3 in Hz by (fold F; rewrite FS_frames_off_val, FS_total_val; lia). discriminate.
    - exact HF'. }
  assert (Efl : fl = frame_flag (aa_geom A) (ff, S)).
  { unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. unfold S. rewrite fs_class_of_size_ok by lia. fold F. unfold ff. rewrite fs_pos_frame by lia. reflexivity. }
  exists A', l1, l2.
  split; [exact HA'|]. split; [reflexivity|]. split; [exact E1|]. split; [unfold aa_frames; unfold A', fs_alloc; cbn [aa_fs_busy]; exact E2|].
  split; [exact Efl|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].

  pose proof (conj Flen (conj Fcls (conj Fhint (conj Fflags (conj Ffree Fsh))))) as HF.
  destruct HRest as (Hsep & _).
  assert (Hsep' : live_sep A') by exact Hsep.
  assert (HG' : geom_ok (aa_geom A')) by exact HG.
  assert (NOCL : forall x, ff <= x < ff + S -> ~ client_addrA CST A x).
  { intros x Hx Hcl. destruct (client_addr_cases A x _ HF Hcl) as [X|[L|[FR|[C|FL]]]].
    - lia.
    - destruct L as (b & n & Hbn & Hx'). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2. lia.
    - destruct FR as (c' & p' & Hc'' & Hp' & Hb' & Hx'). fold F in Hx'.
      assert (Hne : c' <> c \/ p' <> pos) by (destruct (Z.eq_dec c' c) as [->|]; [right; intros ->; rewrite Hfree in Hb'; discriminate | left; assumption]).
      destruct (fs_frames_disjoint F c' p' c pos Hc'' Hp' Hc Hpos Hne) as [D|D]; fold ff in D; [lia|].
      pose proof (fs_frame_size_pos c' ltac:(lia)). lia.
    - destruct (HCST x C) as [X _]. unfold IMG_LO, IMG_HI in X. lia.
    - destruct FL as (c' & p' & Hc'' & Hp' & _ & ->). fold F in Hx.
      pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. lia. }
  assert (NOFL : ~ client_addrA CST A fl).
  { intros Hcl. destruct (client_addr_cases A fl _ HF Hcl) as [X|[L|[FR|[C|FL]]]].
    - lia.
    - destruct L as (b & n & Hbn & Hx'). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2. lia.
    - destruct FR as (c' & p' & Hc'' & Hp' & Hb' & Hx'). fold F in Hx'.
      pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. lia.
    - destruct (HCST fl C) as [X _]. unfold IMG_LO, IMG_HI in X. lia.
    - destruct FL as (c' & p' & Hc'' & Hp' & Hb' & E). fold F in E.
      destruct (fs_flags_inj F c' p' c pos Hc'' Hp' Hc Hpos ltac:(unfold fl in E; lia)) as [-> ->]. rewrite Hfree in Hb'. discriminate. }
  assert (CHG_nocl : forall a, (hc <= a < hc + 8 \/ a = fl \/ Sh ff <= a < Sh ff + S / 8) -> client_addrA CST A a -> False).
  { intros a Ha Hcl. destruct Ha as [Ha|[->|Ha]]; [| exact (NOFL Hcl) |].
    - apply (client_not_rt A a _ HG HF Hsep Hcl). right; right; right; right. fold F. lia.
    - destruct (client_addr_bounds A a _ HG HF Hsep Hcl) as [B1 B2]. clear WB. unfold Sh, SHADOW_OFF in *. lia. }
  assert (CHG_nosh : forall a, (hc <= a < hc + 8 \/ a = fl \/ Sh ff <= a < Sh ff + S / 8) -> client_shadowA CST XGL A a -> False).
  { intros a Ha Hcs. pose proof (client_shadow_bounds A a _ HG HF Hsep Hcs) as B. unfold HIGH_SHADOW_END, SHADOW_OFF in B.
    destruct Ha as [Ha|[->|Ha]]; [lia|lia|].
    destruct Hcs as [(x & Cx & Ex)|(x & Gx & Ex)].
    - assert (ff <= x < ff + S).
      { subst a. unfold Sh in Ha. destruct (client_addr_bounds A x _ HG HF Hsep Cx) as [Bx _].
        pose proof (Z.div_mod ff 8). pose proof (Z.div_mod x 8). pose proof (Z.mod_pos_bound x 8). pose proof (Z.mod_pos_bound ff 8).
        assert (ff mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans _ 64); [exists 8; reflexivity| apply Z.mod_divide; lia]).
        split; [first [ clear - Ha Bx H H0 H1 H2 H3; nia | nia ] |].
        destruct (Z_lt_dec x (ff + S)); [lia|].
        assert (Y : (ff + S) / 8 <= x / 8) by (apply Z.div_le_mono; lia).
        replace ff with (ff / 8 * 8) in Y at 1 by lia. rewrite Z.div_add_l in Y by lia. lia. }
      exact (NOCL x H Cx).
    - destruct (HXGL x Gx). unfold IMG_HI in *. subst a. unfold Sh, SHADOW_OFF in Ha. lia. }
  split.
  - intros a Ha Hcl.
    apply RMO; [exact Ha| |].
    + intros X. destruct Hcl as [[C1 _]|[C1 _]]; [exact (CHG_nocl a X C1) | exact (CHG_nosh a X C1)].
    + destruct Hcl as [[C1 _]|[C1 _]]; [exact (client_not_rt A a _ HG HF Hsep C1)|].
      pose proof (client_shadow_bounds A a _ HG HF Hsep C1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
      exact (SHRT a B).
  - intros x j Hx Hj Hdef.
    assert (Bx : 0 <= x < 2 ^ 47 /\ SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds A x _ HG HF Hsep C1) as [B _]. split; [exact B|]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
      - destruct (HXGL x GX). unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. lia. }
    destruct Bx as [Bx SB]. unfold SHADOW_OFF, HIGH_SHADOW_END in SB.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    set (a := Sh x / 8 * 8 + j) in *.
    assert (A8 : (Sh x / 8 * 8) mod 8 = 0) by (apply Z_mod_mult).
    destruct (Z_le_dec (Sh ff) a); [destruct (Z_lt_dec a (Sh ff + S / 8))|].
    +
      pose proof (VS a ltac:(lia)) as X. unfold v3 in X. rewrite view_in in X by lia.
      assert (BW : 0x646000 <= a < 2 ^ 64) by (clear -W1 SB Hj; lia).
      pose proof (rd_off_image (rm rho3) _ _ BW X) as M.
      unfold word_byte. fold a. rewrite M. discriminate.
    + unfold word_byte. fold a. rewrite RMO; [exact Hdef | lia | | ].
      * intros [X|[X|X]]; [lia| lia | lia].
      * apply SHRT. lia.
    + unfold word_byte. fold a. rewrite RMO; [exact Hdef | lia | | ].
      * intros [X|[X|X]]; [lia| lia | lia].
      * apply SHRT. lia.
Qed.
End R.
End RebuildSM.

(* [comment removed for export] *)
Module GlueMZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "opp"; "div"; "sub"; "mul"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "eval"; "ss_objs"; "sstate"; "valuation"; "DZero"; "cell"; "mkObj"; "rm"; "smatch"; "covered"; "mkSS"; "obj_range"; "ranges_disjoint"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "ss_next"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "nil"; "true"; "Some"; "app"; "option"; "cons"; "nat"; "fst"; "snd"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "lit_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma smatch_carve_zero_rd : ltac2:(tb__ "0|9|
S14S13S27S3cA1M0S3aS3bSfS0S0S1S19Vsegs;R9R8S28G0S37R7S38R6R5A2A4A4S1bS22R9A1S23R9A1S20R9A1S1fR9A1S24R9A1S2eSeS12R9A1S30SeS17R5S10R4A1S10R3A1S2bS16A1S15A5S2bSeA1A3A3S1eR9A1R2S21R9A1A9S13ScS2aS25R1A1S2cA3S35Q40M1S11RcR7A2A2S0S3S6S5Z2M2Z3fA2M3A1R7A2SbS3R8R7A2S4R7G3A2A2S4S8R8R9A2G3A2S3Z0M4S2R4RaA2A2S3S2R5RaA2S5G2Z40A2A2S39SeSeS1dS1cR13R1A2S28S0S0S2R7RdA2S2R7RcA2A4A2Lo';S12R11A1A3S0SbS3S2R8ReA2R1A2S4R1S2R8RdA2A2A2SbScS2aS43Vsegs;S18R15A1M5S34G1R2A2M6A3S2cA3ScS2fS36Q8M7A1M8A1S42Vsegs;G5G6A3S2dG8S34G7G4A2A2A3A2F_;Fa;S19Vsegs;R14RaS28G0S37R12S38R11R10A2A4A4F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md base lo hi nx Hsm S' Hwf' b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base (SLit lo) (SLit hi) [] DZero).
  assert (Hlo' : soff rho (SLit lo) = lo) by (rewrite soff_lit_small; lia).
  assert (Hhi' : soff rho (SLit hi) = hi) by (rewrite soff_lit_small; lia).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi]. rewrite Hlo', Hhi'. reflexivity. }
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
    unfold obj_holds, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. rewrite Hlo', Hhi'.
    split; [lia|]. split.
    { intros off Hoff _. destruct (Hbytes (b + off) ltac:(lia)) as [Hw Hb].
      unfold wview. rewrite (MEM (b + off)) by lia.
      pose proof (wview_of_views segs (rm rho) (Z_to_bv 64 (b + off)) Hw (ex_intro _ _ Hb)) as X. unfold wview in X. exact X. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEM (b + off)) by lia.
    destruct (Hbytes (b + off) ltac:(lia)) as [_ Hb]. unfold rd_of in Hb.
    destruct (rm rho (Z_to_bv 64 (b + off))) as [x|]; [exact Hb|]. rewrite <- Hb. first [apply Hrom | symmetry; apply Hrom].
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. fold newo. rewrite Hnr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_zero_rd : ltac2:(tb__ "0|e|
S46S14S41S27S36Q40M0A1A1S27S3cA1M1S3aS3bSfS0S0S1S45Vsegs;RbR9RaR8S28G1S37R7S38R6R5A2A4A6S1bS22S3dRaA1M2A1S23G2A1S20G2A1S1fG2A1S24G2A1S2eSeS12G2A1S30SeS17R5S10R4A1S10R3A1S2bS16A1S15A5S2bSeA1A3A3S1eG2A1R2S21G2A1A9S13ScS2aS25R1A1S2cA3S49S26S3dRcA1A1R4A2S35G0S11ReR8A2A2S0S3S6S5Z2M3Z3fA2M4A1R8A2SbS3R9R8A2S4R8G4A2A2S4S8R9RaA2G4A2S3Z0M5S2R4RbA2A2S3S2R5RbA2S5G3Z40A2A2S39SeSeS1dS1cR15R1A2S28S0S0S2R7ReA2S2R7RdA2A4A2Lo';S12S3dR13A1A1A3S0SbS3S2R8RfA2R1A2S4R1S2R8ReA2A2A2SbScS2aS43Vsegs;S18R17A1M6S34G0R2A2M7A3S2cA3ScS2fS36Q8M8A1M9A1S42Vsegs;G6G7A3S2dG9S34G8G5A2A2A3A2F_;Fa;S29SfSfA2MaS0S0S47GaR3S3eR18A1A3SbS3S35G0S11R1aS32SfSfR4A3A2A2MbR3A2S4R3S2GbS35G0S11R1aS33SfSfR4A3A2A2A2A2A2SbS3G5R3A2S4R3Z8McA2A2SdSbS3S2ReR15A2S2S9S7S2S35G0S11R1cS3fR1bA1A2A2S7R5GcA2A2GcA2GcA2R4A2MdA2S4GdS2ReR14A2A2A2A1F_;F_;F_;Fj;Fy;Frr;S45Vsegs;R18S40R16RcA2R17R15S28G1S37R14S38R13R12A2A4A6F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp tr ms md base lo hi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S' Hwf' Hnx b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes Hxs.
  split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_zero_rd rho (ax_S A) tr (vms md tp ms) (vmd md) base lo hi nx Hsm Hwf' Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. fold b.
    rewrite !soff_lit_small by lia.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

Lemma absorb_zero_dflt : ltac2:(tb__ "0|6|
S14S13S27S3cA1M0S3aS3bS27SeA1M1G1SfS0S0S27S16A1S19Vsegs;RbRaS28G0S37R9S38R8R7A2A4A4ScG1S12RbA1S2eSeR7R6A3A3S47SeS17R6S10R5A1S10R4A1R3S15A5R7A3S35Q40M2S11ReR7A2A2S0S3S6S5Z2Z3fA2M3A1R7A2S3R8R7A2S4R8G3A2S0SbS3RbR1A2S4R1RaA2A2SdS1aR14RaR2A3A1ScS2fS36Q8M4A1M5A1S42Vsegs;S18S48R15RfR12A3A1S34G2S2R7R3A2A2A3S2dG5S34G4Z0A2A2A3F_;F_;Foff;F_;F_;F_;Tb;F_;F_;F_;Fcs;Fhi;Flo;Fbase;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs R base lo hi cs Hsm Ho Hin b Hs1 Hs3 Hs2 off Hoff Hnc.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  pose proof (proj1 (Forall_forall _ _) HallR _ Hin) as Hoh.
  unfold obj_holds, obj_lo_of, obj_hi_of in Hoh. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Hoh. fold b in Hoh.
  rewrite !soff_lit_small in Hoh by lia.
  destruct Hoh as (Hbnd & Hwv & Hcl & Hdf & _).
  assert (RNG : in_ranges rho R (Z_to_bv 64 (b + off))).
  { exists (mkObj base (SLit lo) (SLit hi) cs DZero). split; [exact Hin|].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. fold b.
    rewrite !soff_lit_small by lia. cbn [fst snd]. rewrite u64_of_sum by lia. lia. }
  rewrite (rd_of_absorb_in segs rho R ms _ Hrom RNG).
  specialize (Hdf off Hoff Hnc). unfold dflt_holds in Hdf. exact Hdf.
Qed.

Lemma not_covered_lits : ltac2:(tb__ "0|3|
S14S27S29S29S0S31A2M0SfA2M1A1S0S39G1G1G1OLc;R1G0SfG0OLp;R2S0S31SbSbS3S6S5Z2Z3eA2M2A1R2A2S4R2G2A2A2SdSbS3R2R6A2S4R6S2R2SaR1A1A2A2A2A1A2Lk;Lo;X29x1Ls;Lp;X29x1Lc;R2A3SdS1aR4S44R3A1R2A3A1F_;Foff;Fcs;Frho;").
Proof.
  intros rho cs off HF Hcov. unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hic).
  induction cs as [|[[o k] v] t IH]; [destruct Hc|].
  cbn [lit_cells] in Hc. destruct Hc as [<-|Hc].
  - apply Forall_inv in HF. destruct HF as [Ho Hn]. unfold in_cell in Hic. cbn [c_off c_width] in Hic.
    rewrite soff_lit_small in Hic by lia. apply Hn. lia.
  - apply IH; [apply Forall_inv_tail in HF; exact HF | exact Hc].
Qed.
End WithSegs.
End GlueMZ.

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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA.
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
Module SegD_refl.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "list"; "prod"; "cons"; "option"; "nil"; "Some"; "fst"; "length"; "snd"; "app"; "nat"; "pair"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sv_eqb"; "cell"; "sprop"; "c_off"; "c_val"; "c_width"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "RsEcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl"; "leqb"; "cellb"; "sobjb"; "svp_eqb"; "andc"; "cut1"; "cut1e"; "cut2"; "is_ecall"; "sd_eqb"; "skel_eqb"; "tailb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "leaf"; "@Corelib.Numbers.BinNums"; "positive"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "odefault_eqb"; "@Stdlib.Bool.Bool"; "eqb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SegD_states.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma land_inv : ltac2:(tb__ "0|0|
S0S0SfS0S0S0L_;R2R1S1X0x2S2A3S10SfS0R3S2A3SfS0R2S2A3A2F_;Fb;Fa;").
Proof. intros [|] b; cbn; intros H; [split; [reflexivity|exact H] | discriminate]. Qed.

Definition andc (a b : bool) : bool := if a then b else false.
Lemma andc_inv : ltac2:(tb__ "0|0|
S0S0SfS0S29R2R1A2S2A3S10SfS0R3S2A3SfS0R2S2A3A2F_;Fb;Fa;").
Proof. intros [|] b; cbn; intros H; [split; [reflexivity|exact H] | discriminate]. Qed.

Definition cut1 (l : list leafA) : bool := ltac2:(tb__ "0|1|
S3S11A1M0S0Ll;Vl;S1S11G0S11S0Ll0;R2S12S22S22S0Lla_reason;R1S1G0S0Ll1;R3S2S11G0S1Ll3;Ll2;X3x2S1S1S1S1S1X22x7Lla_reason;Lla_state;X11x1Ll1;Ll0;X3x2").
Lemma cut1_sound : ltac2:(tb__ "0|1|
S3S11A1M0SfS0S2aR1A1S2A3SfG0R2S5S11S13S31U0R2A2S23A2S7S11A1A3A3F_;Fl;").
Proof.
  intros [|[S r] l]; [cbn; discriminate|]. destruct r; try (cbn; discriminate). destruct l; cbn; [reflexivity | discriminate].
Qed.

Definition cut2 (l : list leafA) : bool := ltac2:(tb__ "0|1|
S3S11A1M0S0Ll;Vl;S1S11G0S11S0Ll0;R2S12S22S22S0Lla_reason;R1S1G0S0Ll1;R3S1S11G0S11S0Ll2;R2S12S22S22S0Lla_reason0;R1S1G0S0Ll3;R3S2S11G0S1Ll5;Ll4;X3x2S1S1S1S1S1X22x7Lla_reason0;Lla_state0;X11x1Ll3;Ll2;X3x2S1S1S1S1S1X22x7Lla_reason;Lla_state;X11x1Ll1;Ll0;X3x2").
Lemma cut2_sound : ltac2:(tb__ "0|1|
S3S11A1M0SfS0S2cR1A1S2A3SfG0R2S5S11S13S31U0R2A2S23A2S5S11S13S31U1R2A2S23A2S7S11A1A3A3A3F_;Fl;").
Proof.
  intros [|[S r] l]; [cbn; discriminate|]. destruct r; try (cbn; discriminate). destruct l as [|[S' r'] l]; [cbn; discriminate|].
  destruct r'; try (cbn; discriminate). destruct l; cbn; [reflexivity | discriminate].
Qed.

Definition cut1e (l : list leafA) : bool := ltac2:(tb__ "0|1|
S3S11A1M0S0Ll;Vl;S1S11G0S11S0Ll0;R2S12S22S22S0Lla_reason;R1G0S0Ll1;R3S2S11G0S1Ll3;Ll2;X3x2S1S1S1S1S1S1X22x7Lla_reason;Lla_state;X11x1Ll1;Ll0;X3x2").
Lemma cut1e_sound : ltac2:(tb__ "0|1|
S3S11A1M0SfS0S2bR1A1S2A3SfG0R2S5S11S13S31U0R2A2S24A2S7S11A1A3A3F_;Fl;").
Proof.
  intros [|[S r] l]; [cbn; discriminate|]. destruct r; try (cbn; discriminate). destruct l; cbn; [reflexivity | discriminate].
Qed.

Definition is_ecall (o : option instr) : bool := match o with Some Ecall => true | _ => false end.
Lemma is_ecall_sound : ltac2:(tb__ "0|1|
S6S34A1M0SfS0S2dR1A1S2A3SfG0R2S8S34S35A2A3F_;Fo;").
Proof. intros [i|]; [|discriminate]. destruct i; cbn; intros; try discriminate. reflexivity. Qed.

Definition isnil {A : Type} (l : list A) : bool := match l with [] => true | _ => false end.
Lemma isnil_sound : forall {A : Type} (l : list A), isnil l = true -> l = [].
Proof. intros A [|x l]; cbn; [reflexivity | discriminate]. Qed.

Fixpoint leqb {A : Type} (f : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | [], [] => true
  | x :: l, y :: l' => f x y &&& leqb f l l'
  | _, _ => false
  end.
Lemma leqb_sound : forall {A : Type} (f : A -> A -> bool), (forall x y, f x y = true -> x = y) ->
  forall l l', leqb f l l' = true -> l = l'.
Proof.
  intros A f Hf l. induction l as [|x l IH]; intros [|y l']; cbn; intros H; try discriminate; [reflexivity|].
  apply land_inv in H as [H1 H2]. rewrite (Hf _ _ H1), (IH _ H2). reflexivity.
Qed.

Definition skel_eqb (a b : sv * sv * sv) : bool := ltac2:(tb__ "0|3|
S4S4S14S14A2M0S14A2M1S0La;Va;G0S14G0S0Lp;R2S14S14G1S0Lb;Vb;G0S14G0S0Lp0;R2S14S14S0S0L_;M2S16R6R2A2G2S16R5R1A2S16R7R3A2S1X0x2S1X0x2Lb2;Lb1;X4x1Lb3;Lp0;X4x1La2;La1;X4x1La3;Lp;X4x1").
Lemma skel_eqb_sound : ltac2:(tb__ "0|1|
S4S4S14S14A2S14A2M0G0SfS0S2fR2R1A2S2A3SfG0R3R2A3F_;Fb;Fa;").
Proof.
  intros [[a1 a2] a3] [[b1 b2] b3] H. cbn in H. apply land_inv in H as [H1 H]. apply land_inv in H as [H2 H3].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2), (sv_eqb_sound _ _ H3). reflexivity.
Qed.

Definition svp_eqb (a b : sv * sv) : bool := ltac2:(tb__ "0|0|
S0S0L_;S16S9S14S14Va;A3S9S14S14Vb;A3A2S16SbS14S14Va;A3SbS14S14Vb;A3A2S1X0x2").
Lemma svp_eqb_sound : ltac2:(tb__ "0|1|
S4S14S14A2M0G0SfS0S28R2R1A2S2A3SfG0R3R2A3F_;Fb;Fa;").
Proof.
  intros [a1 a2] [b1 b2] H. unfold svp_eqb in H. cbn [fst snd] in H. apply land_inv in H as [H1 H2].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2). reflexivity.
Qed.

Definition sd_eqb (o : option (list (sv * sv) * list sprop)) (l : list (sv * sv)) (F : list sprop) : bool := ltac2:(tb__ "0|4|
S6S4S3S4S14S14A2M0A1M1S3S18A1M2A2M3A1S0Lo;Vo;G3G3S0Lp;R1G1G2S0S0L_;S25G0S28R2Vl;A4S25S18S21R1VF;A4S1X0x2LF';Ll';X4x1Lp;S1X6x2").
Lemma sd_eqb_sound : ltac2:(tb__ "0|4|
S6S4S3S4S14S14A2A1M0S3S18A1M1A2M2A1M3G0G1SfS0S2eR3R2R1A3S2A3SfG3R4S8G2SeG0G1R3R2A4A2A3F_;FF;Fl;Fo;").
Proof.
  intros [[l' F']|] l F H; cbn [sd_eqb] in H; [|discriminate]. apply land_inv in H as [H1 H2].
  rewrite (leqb_sound _ svp_eqb_sound _ _ H1), (leqb_sound _ sprop_eqb_sound _ _ H2). reflexivity.
Qed.

Definition cellb (c c' : cell) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S16S19Vc;A1S19Vc';A1A2G0S3bS1bVc;A1S1bVc';A1A2S16S1aVc;A1S1aVc';A1A2S1X0x2S1X0x2").
Lemma cellb_sound : ltac2:(tb__ "0|0|
S17S17SfS0S26R2R1A2S2A3SfS17R3R2A3F_;Fc';Fc;").
Proof.
  intros [o w v] [o' w' v'] H. unfold cellb in H. cbn [c_off c_width c_val] in H.
  apply land_inv in H as [H1 H]. apply land_inv in H as [H2 H3].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H3), (proj1 (Z.eqb_eq _ _) H2). reflexivity.
Qed.

Definition sobjb (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S16S1cVo;A1S1cVo';A1A2G0S16S20Vo;A1S20Vo';A1A2G0S16S1fVo;A1S1fVo';A1A2G0S25S17S26S1dVo;A1S1dVo';A1A4S38S1eVo;A1S1eVo';A1A2S1X0x2S1X0x2S1X0x2S1X0x2").
Lemma sobjb_sound : ltac2:(tb__ "0|0|
S15S15SfS0S27R2R1A2S2A3SfS15R3R2A3F_;Fo';Fo;").
Proof.
  intros [b lo hi cs d] [b' lo' hi' cs' d'] H. unfold sobjb in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  apply land_inv in H as [H1 H]. apply land_inv in H as [H2 H]. apply land_inv in H as [H3 H]. apply land_inv in H as [H4 H5].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2), (sv_eqb_sound _ _ H3), (leqb_sound _ cellb_sound _ _ H4), (odefault_eqb_sound _ _ H5).
  reflexivity.
Qed.

Definition tailb (objs : list sobj) (k : nat) (L : list sobj) : bool := ltac2:(tb__ "0|0|
S25S15S27S37S15S33SaS15Vobjs;A2Vk;A2Vobjs;A3VL;A4").
Lemma tailb_sound : ltac2:(tb__ "0|1|
S3S15A1M0SdG0SfS0S30R3R2R1A3S2A3SfG0R4ScS15S36S15S33SaS15R4A2R3A2R4A3R2A3A3F_;FL;Fk;Fobjs;").
Proof.
  intros objs k L H. unfold tailb in H. rewrite <- (leqb_sound _ sobjb_sound _ _ H). symmetry. apply firstn_skipn.
Qed.

Lemma poseqb_sound : ltac2:(tb__ "0|0|
S32S32SfS0S3aR2R1A2S2A3SfS32R3R2A3F_;Fb;Fa;").
Proof. intros a b. apply Pos.eqb_eq. Qed.

Lemma eqb_false_sound : ltac2:(tb__ "0|0|
S0SfS0S39R1S1A2S2A3SfS0R2S1A3F_;Fb;").
Proof. intros [|]; cbn; [discriminate | reflexivity]. Qed.

Ltac splitC H :=
  lazymatch type of H with
  | andc _ _ = true => let C := fresh "C" in apply andc_inv in H as [C H]; splitC C; splitC H
  | _ => idtac
  end.

Ltac convC :=
  repeat match goal with
  | H : cut1 _ = true |- _ => apply cut1_sound in H
  | H : cut2 _ = true |- _ => apply cut2_sound in H
  | H : isnil _ = true |- _ => apply isnil_sound in H
  | H : leqb skel_eqb _ _ = true |- _ => apply (leqb_sound _ skel_eqb_sound) in H
  | H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H
  | H : sd_eqb _ _ _ = true |- _ => apply sd_eqb_sound in H
  | H : Pos.eqb _ _ = true |- _ => apply poseqb_sound in H
  | H : tailb _ _ _ = true |- _ => apply tailb_sound in H
  | H : Bool.eqb _ false = true |- _ => apply eqb_false_sound in H
  | H : cut1e _ = true |- _ => apply cut1e_sound in H
  | H : is_ecall _ = true |- _ => apply is_ecall_sound in H
  end.

Ltac dispC :=
  lazymatch goal with
  | |- runA ?f ?c _ = _ =>
      match goal with H : runA ?f' ?c' _ = _ |- _ => constr_eq f f'; constr_eq c c'; exact H end
  | |- entailsA ?a ?b _ = true =>
      match goal with H : entailsA ?a' ?b' _ = true |- _ => constr_eq a a'; constr_eq b b'; exact H end
  | |- ?g => match goal with H : ?t |- _ => constr_eq t g; exact H end
  end.
End SegD_refl.

(* [comment removed for export] *)
Module SecReveal.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "mul"; "lt"; "pow"; "modulo"; "ge"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "nat"; "bool"; "true"; "pair"; "option"; "false"; "None"; "Some"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "sobj"; "ss_objs"; "obj_range"; "ranges_disjoint"; "rl"; "rw"; "image_byte"; "outside_all"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_base"; "Model"; "page_mem"; "event"; "m_vm_lazy"; "page_in_ranges"; "m_vmmaps"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pageZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal"; "JT"; "revealed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "w_tr"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymFrame SymObj SymEntail Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition JT : jpredA := fun _ _ _ _ => True.

Lemma SPA_J_out : ltac2:(tb__ "0|0|
SfS3cA1S28S35S1aSfS24Q40A1A1S41S27R6R5R4R3R2R1A6S1S27R7S32R5R4R3R2A6R6R4R3S40R2A1S3aS3fR2A1A1A4A2F_;Fw;Ftp;Frho;FA;FJ;Fsegs;").
Proof. intros segs J A rho tp w [H1 H2]. split; [split; [exact H1 | exact I] | exact H2]. Qed.

Lemma SPA_J_in : ltac2:(tb__ "0|0|
SfS3cA1S28S35S1aSfS24Q40A1A1S41S27R6S32R4R3R2R1A6R6R4R3S40R2A1S3aS3fR2A1A1A4S27R8R7R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;FJ;Fsegs;").
Proof. intros segs J A rho tp w [H1 _] H2. split; [exact H1 | exact H2]. Qed.

Lemma JT_blind : ltac2:(tb__ "0|1|
S1aS1aSfS24Q40A1A1M0G0SfS2cA1S2aS32R6R4R2R1A4S32R6R4R3R2A4F_;Fmd;Ftr;Ft';Ft;Fr';Fr;").
Proof. intros. exact I. Qed.

Lemma pageZ_u : ltac2:(tb__ "0|1|
SdS10S5Z0R2A2S5S6S6R3S8Z1000M0S7R2A1A2A2G0A2SaZ2Z40A2A2S0SdS25Q40S31R4R3A2A2S6R4S8G0S7R3A1A2A2A3F_;F_;Fk;Fq;").
Proof. intros q k H0 H1. unfold pageZ. apply u64_lit. lia. Qed.

Lemma page_base_run : ltac2:(tb__ "0|7|
SdS10S24Q40M0A1M1S0SdSbR3Z1000M2A2Z0M3A3S5G3R4A2S5S6R5S8G2S7R4A1A2A2SaZ2Z40A2A2S1S5R6S25G0R4A2M4A2S9G4S6R6S8G2S7R5A1A2A2A2A2S2S10S10S1S37R1R7A2S1S0G1S29R6A1S31R8R1A2A3S1S5S6R8S8G2S7R1A1A2A2M5S25G0R6A2M6A2S9G6S6G5G2A2A2A2A2A2Lk;A2F_;F_;F_;F_;Fa;Fn;Fq;").
Proof.
  intros q n a Hal H0 Hhi Ha.
  set (kz := (bv_unsigned a - q) / 4096).
  assert (Hk : 0 <= kz < Z.of_nat n).
  { subst kz. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (Hr : q + 4096 * kz <= bv_unsigned a < q + 4096 * kz + 4096).
  { subst kz. pose proof (Z.div_mod (bv_unsigned a - q) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a - q) 4096 ltac:(lia)). lia. }
  exists (Z.to_nat kz). split; [lia|].
  assert (EK : Z.of_nat (Z.to_nat kz) = kz) by lia.
  split; [|rewrite EK; exact Hr].
  apply page_base_in_page.
  - rewrite pageZ_u by lia. rewrite EK. replace (q + 4096 * kz) with (q + kz * 4096) by lia.
    change page_size with 4096. rewrite Z_mod_plus_full. exact Hal.
  - unfold in_page. rewrite pageZ_u by lia. rewrite EK. change page_size with 4096. lia.
Qed.

Definition revealed (q : Z) (n : nat) (rho : valuation) (tp : list word) (rho' : valuation) (tp1 : list word) : Prop := ltac2:(tb__ "0|b|
S1SeS0S24Q40M0A1M1S21Vrho';R1A2S21Vrho;R1A2A3Fi;S1SeS0SfS24Q8M2A1M3A1S20Vrho';R1A2S20Vrho;R1A2A3Fl;S1G1S3bG1R1Vtp1;A3S1S2S10S10S1S37R1Vn;A2M4S0G1R3S31Vq;R1A2A3A2Lk;A2S3S3bG1R2Vtp;A3A1A2F_;Fp;S1S5S7S19G1Vtp1;A2A1S7Vn;A1M5A2S1S10G4S0S11S2bS31Vq;R2A2S18G1Vtp1;Vtp;A3A2S12A3F_;Fk;S1G1S1S5Vq;S25G0R1A2M6A2S9G6S6Vq;S8Z1000G5A2A2A2A2M7S0S11S2bS29R2A1Vtp;A2M8S15A3S0S14G3A1M9S1bVrho';R3A2MaS17G3S26G2Z0A2A2A3F_;F_;Fa;S1G1G7S0S11G8S12A3S0G9GaS1bVrho;R3A2A3F_;F_;Fa;G1S3G7A1S0G9S1bVrho';R2A2S1bVrho;R2A2A3F_;Fa;A2A2A2A2A2A2A2").

Lemma SPA_reveal_pages : ltac2:(tb__ "0|5|
S35SdS10S1aSfS24Q40A1M0A1M1SfS2cA1M2S3dS2aS27S34S32R8R5R4S13G2S38R3S39R2R1A2A4A6S0SdSbR8Z1000M3A2Z0A3S5Z646000R9A2S5S6RaS8G3S7R9A1A2A2SaZ2Z40A2A2S10S37R1RbA2S0S11S2eS31RdR2A2S2dR7A1A2S12A3F_;Fk;SdS1S5RdR1A2S9R1S6RdS8G3S7RcA1A2M4A2A2A2S0S11S44S30S2fR8A1A1R2A2S15A3F_;Fz;ScS43R7RaA2G4A2S3eS1cS1cS1fS1eRdR1A2S13SdSdRfS6RfS8G3S7ReA1A2A2A4A2Lo;S1dS36RfA1A1A3S2G1G1S2S1aS1aS1S27S34S32R12R1S18G0R2ReA3S13G2S38RdS39RcRbA2A4A6S33R11R10RfReR1R2A6A2Lrho';A2Ltp1;A2F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fn;Fq;FA;").
Proof.
  intros A q n. induction n as [|n IH]; intros rho tp tr ms md Hsp Hqal Hqlo Hqhi Hlz Hacc Hroom Hdisj.
  - exists [], rho. split; [exact Hsp|]. unfold revealed. cbn [app length Z.of_nat].
    split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros p []|]. split; [lia|].
    split; [intros k Hk; lia|]. split; [intros a Ha; lia|]. split; [intros a Ha; lia|]. intros; reflexivity.
  - rewrite Nat2Z.inj_succ in *.
    destruct (IH rho tp tr ms md Hsp Hqal Hqlo ltac:(lia) ltac:(intros k Hk; apply Hlz; lia)
                 ltac:(intros z Hz; apply Hacc; lia) ltac:(lia)) as (tp1 & rho1 & Hsp1 & HR).
    { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. lia. }
    destruct HR as (Hrw1 & Hrl1 & Htp1 & Hlen1 & Hvis1 & Hz1 & Hk1 & Ho1).
    set (p := pageZ q n).
    assert (Up : bv_unsigned p = q + 4096 * Z.of_nat n) by (unfold p; apply pageZ_u; lia).
    assert (Hobj : forall o, In o (ss_objs (ax_S A)) -> obj_range rho1 o = obj_range rho o).
    { intros o Ho. unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !(eval_ext_rwrl rho rho1) by assumption. reflexivity. }

    assert (PB : forall a : word, q + 4096 * Z.of_nat n <= bv_unsigned a < q + 4096 * Z.of_nat n + 4096 -> page_base a = p).
    { intros a Ha. apply page_base_in_page; [rewrite Up; replace (q + 4096 * Z.of_nat n) with (q + Z.of_nat n * 4096) by lia;
        change page_size with 4096; rewrite Z_mod_plus_full; exact Hqal |].
      unfold in_page. rewrite Up. change page_size with 4096. lia. }
    destruct (page_mem p (tp1 ++ tp)) eqn:Hpm.
    +
      assert (Hptp : page_mem p tp = true).
      { rewrite page_mem_app in Hpm. apply orb_prop in Hpm as [H|H]; [|exact H].
        exfalso. apply (proj1 (page_mem_In _ _)) in H. destruct (Htp1 p H) as ((k & Hk & E) & _).
        apply (f_equal bv_unsigned) in E. rewrite Up in E. rewrite pageZ_u in E by lia. lia. }
      exists tp1, rho1. split; [exact Hsp1|]. unfold revealed.
      split; [exact Hrw1|]. split; [exact Hrl1|].
      split; [intros p' Hp'; destruct (Htp1 p' Hp') as ((k & Hk & E) & Hn); split; [exists k; split; [lia | exact E] | exact Hn]|].
      split; [lia|].
      split.
      { intros k Hk. destruct (Nat.eq_dec k n) as [->|Hne]; [|apply Hvis1; lia]. fold p. exact Hpm. }
      split.
      { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge]; [apply Hz1; [lia | exact Hpa]|].
        exfalso. rewrite (PB a ltac:(lia)) in Hpa. rewrite Hptp in Hpa. discriminate. }
      split.
      { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge]; [apply Hk1; [lia | exact Hpa]|].
        apply Ho1. lia. }
      intros a Ha. apply Ho1. lia.
    +
      pose proof (proj1 (page_mem_false p (tp1 ++ tp)) Hpm) as Hnin.
      destruct (SPA_prepay_page_rm JT rho1 A p (tp1 ++ tp) tr ms md Hsp1) as (Hsp2 & Hz2 & Ho2).
      * rewrite Up. change page_size with 4096. replace (q + 4096 * Z.of_nat n) with (q + Z.of_nat n * 4096) by lia. rewrite Z_mod_plus_full. exact Hqal.
      * apply Hlz. lia.
      * exact Hnin.
      * intros j Hj. rewrite Up. apply Hacc. unfold page_size in Hj. lia.
      * unfold headroom in Hroom |- *. pose proof (paid_app_le md tp1 tp) as PL. unfold page_size in PL |- *. lia.
      * apply Forall_forall. intros o Ho. rewrite (Hobj o Ho). pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
        rewrite Up. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. unfold page_size. lia.
      * intros; exact I.
      * rewrite Up. lia.
      * cbv zeta in Hsp2, Hz2, Ho2.
        set (rho2 := rho_absorb rho1 [zero_page_obj p] (vms md (p :: tp1 ++ tp) ms)) in *.
        assert (Hptp : page_mem p tp = false).
        { rewrite page_mem_app in Hpm. apply orb_false_elim in Hpm as [_ H]. exact H. }
        exists (p :: tp1), rho2. split; [exact Hsp2|]. unfold revealed.
        split; [intros i; unfold rho2; rewrite rw_absorb; apply Hrw1|].
        split; [intros l; unfold rho2; rewrite rl_absorb; apply Hrl1|].
        split.
        { intros p' [<-|Hp'].
          - split; [exists n; split; [lia | reflexivity]|]. intros Hin. apply Hnin. apply in_app_iff. right. exact Hin.
          - destruct (Htp1 p' Hp') as ((k & Hk & E) & Hn). split; [exists k; split; [lia | exact E] | exact Hn]. }
        split; [cbn [length]; lia|].
        split.
        { intros k Hk. cbn [app]. unfold page_mem. cbn [existsb]. fold (page_mem (pageZ q k) (tp1 ++ tp)).
          destruct (Nat.eq_dec k n) as [->|Hne].
          - fold p. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
          - rewrite (Hvis1 k ltac:(lia)). apply orb_true_r. }
        split.
        { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge].
          - unfold rho2. rewrite Ho2; [apply Hz1; [lia | exact Hpa]|]. rewrite Up. unfold page_size. lia.
          - rewrite <- (Z_to_bv_bv_unsigned 64 a). unfold rho2. apply Hz2. rewrite Up. unfold page_size. lia. }
        split.
        { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge].
          - unfold rho2. rewrite Ho2; [apply Hk1; [lia | exact Hpa]|]. rewrite Up. unfold page_size. lia.
          - exfalso. rewrite (PB a ltac:(lia)) in Hpa. rewrite Hptp in Hpa. discriminate. }
        intros a Ha. unfold rho2. rewrite Ho2; [apply Ho1; lia|]. rewrite Up. unfold page_size. lia.
Qed.

Lemma revealed_paid : ltac2:(tb__ "0|2|
SdS10S1aSfS24Q40A1M0A1M1S1aG1S2aS33R7R6R5R4R3R2A6S5S42R2S18G0R3R5A3A2S6S42R2R5A2S8Z1000S7R7A1A2A2A2F_;Fmd;Ftp1;Frho';Ftp;Frho;Fn;Fq;").
Proof.
  intros q n rho tp rho' tp1 md (_ & _ & _ & Hlen & _). pose proof (paid_app_le md tp1 tp) as PL. unfold page_size in PL. nia.
Qed.

Lemma revealed_pages : ltac2:(tb__ "0|5|
SdS10S1aSfS24Q40M0A1M1A1M2S1aG2G1S33R7R6R5R4R3R2A6S3bG1R2R3A3S5Z0R9A2S5S6RaS8Z1000M3S7R9A1A2A2SaZ2Z40A2A2S1S5RbS25G0R5A2M4A2S1S5S6G4G3A2S6RbS8G3S7RaA1A2A2A2S1S0SdSbG4G3A2SbRbG3A2A3S3S3bG1R5R8A3A1A2A2A2F_;F_;F_;F_;Fp;Ftp1;Frho';Ftp;Frho;Fn;Fq;").
Proof.
  intros q n rho tp rho' tp1 p (_ & _ & Htp1 & _) Hp H0 Hhi. destruct (Htp1 p Hp) as ((k & Hk & ->) & Hn).
  rewrite pageZ_u by lia. split; [lia|]. split; [lia|]. split; [|exact Hn].
  replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma reveal_bytes : ltac2:(tb__ "0|7|
SfS3cA1SdS10S1aSfS24Q40M0A1M1A1M2S1aG2S33R6R5R4R3R2R1A6S5Z0R7A2S5S6R8S8Z1000M3S7R7A1A2A2SaZ2Z40A2A2G1S1S5RaS25G0R1A2M4A2S9G4S6RaS8G3S7R9A1A2A2A2A2S0S11S2bS29R2A1R8A2S12A3S3S0S14S24Q8A1M5A1M6S1bRaR3A2S16G5A1A3A1F_;F_;Fa;SdS1S5RbR1A2S9R1S6RbS8G3S7RaA1A2A2A2A2S1S0S11S46RdS1bR8A1S26G0R2A2A3S12A3S2G5G5S0G6S45ReS1bR9A1S26G0R3A2A3S17G5R1A2A3Lx;A2A2F_;Fz;F_;F_;F_;F_;Ftp1;Frho';Ftp;Frho;Fn;Fq;Fsegs;").
Proof.
  intros segs q n rho tp rho' tp1 (_ & _ & _ & _ & _ & Hz & Hk & _) H0 Hhi Hdef z Hzr.
  assert (Uz : bv_unsigned (Z_to_bv 64 z) = z) by (apply u64_lit; lia).
  assert (E : exists v, rm rho' (Z_to_bv 64 z) = Some v).
  { destruct (page_mem (page_base (Z_to_bv 64 z)) tp) eqn:Hp.
    - rewrite (Hk _ ltac:(rewrite Uz; exact Hzr) Hp).
      destruct (rm rho (Z_to_bv 64 z)) as [v|] eqn:E; [exists v; reflexivity|]. exfalso. exact (Hdef _ ltac:(rewrite Uz; exact Hzr) Hp E).
    - exists (Z_to_bv 8 0). exact (Hz _ ltac:(rewrite Uz; exact Hzr) Hp). }
  destruct E as [v Ev]. unfold wok_of, rd_of. rewrite Ev. split; [reflexivity | exists v; reflexivity].
Qed.

Lemma reveal_zero : ltac2:(tb__ "0|6|
SdS10S1aSfS24Q40M0A1M1A1M2S1aG2G1S33R7R6R5R4R3R2A6S1S5R8S25G0R2A2M3A2S9G3S6R8S8Z1000S7R7A1A2A2A2A2S0S11S2bS29R3A1R6A2S15A3S0S14S24Q8M4A1M5A1S1bR6R4A2S17G5S26G4Z0A2A2A3F_;F_;F_;Fa;Ftp1;Frho';Ftp;Frho;Fn;Fq;").
Proof. intros q n rho tp rho' tp1 a (_ & _ & _ & _ & _ & Hz & _) Ha Hp. exact (Hz a Ha Hp). Qed.

Lemma SPA_hidden_none : ltac2:(tb__ "0|3|
S28S35S1aSfS24Q40A1M0A1SfS2cA1M1S3dS2aG0S27S34R8R7R6R5S13G1S38R4S39R3R2A2A4A6S0S11S2eS29R2A1S2dR3A1A2S12A3S0S11S2bS29R3A1R7A2S15A3S23R9S1dS36RaA1A1R4A3S0S14S24Q8A1M2A1S1bRaR5A2S16G2A1A3F_;F_;F_;F_;Fa;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp tr ms md a [(Hsm & _) _] Hlz Hpm Hout.
  unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  rewrite <- (Hfr a Hout). rewrite vms_mem. unfold hid. rewrite Hlz, Hpm. reflexivity.
Qed.

Lemma revealed_ext : ltac2:(tb__ "0|8|
S28S35SdS10S1aSfS24Q40A1M0A1M1S1aG1SfS2cA1M2S3dS2aS27S34RbRaR7R6S13G2S38R3S39R2R1A2A4A6S33RaR9R8R7R6R5A6S0SdSbRbZ1000M3A2Z0A3S5Z646000RcA2S5S6RdS8G3S7RcA1A2A2SaZ2Z40A2A2S10S37R1ReA2S0S11S2eS31R10R2A2S2dR8A1A2S12A3F_;Fk;S3eS1cS1cS1fS1eReR1A2S13SdSdR10S6R10S8G3S7RfA1A2A2A4A2Lo;S1dS36R10A1A1A3G0S4S0S14S24Q8A1M4A1M5S1bRdR1A2S1bRfR1A2M6A3S1S0G5G6S16G4A1M7A3S0G5S22S34R1A2G7A3A2A2Fa;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp1;Frho';Ftp;Frho;Fn;Fq;FA;FJ;").
Proof.
  intros J A q n rho tp rho' tp1 tr ms md Hsp HR Hqal Hqlo Hqhi Hlz Hdisj a.
  destruct HR as (_ & _ & _ & _ & _ & Hz & Hk & Ho).
  destruct (Z_le_dec q (bv_unsigned a)); [destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n))|]; [|left; apply Ho; lia|left; apply Ho; lia].
  destruct (page_mem (page_base a) tp) eqn:Hpm; [left; apply Hk; [lia | exact Hpm]|].
  right. split.
  - destruct (page_base_run q n a Hqal ltac:(lia) Hqhi ltac:(lia)) as (k & Hk' & Ek & _).
    apply (SPA_hidden_none J A rho tp tr ms md a Hsp); [rewrite Ek; apply Hlz; exact Hk' | exact Hpm |].
    apply Forall_forall. intros o Ho'. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho') as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
  - apply image_byte_none_A. lia.
Qed.
End SecReveal.

