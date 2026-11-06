(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "True"; "False"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "cell"; "ob_dflt"; "eval"; "dflt_writable"; "holds"; "ob_base"; "ob_cells"; "obj_hi_of"; "obj_lo_of"; "odefault"; "smatch"; "sobj"; "sprop"; "ss_facts"; "swf"; "valuation"; "fld_ok"; "obj_wf"; "ss_next"; "sstate"; "sv"; "tfact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA"; "empty_dflt_ok"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition empty_dflt_ok (rho : valuation) (d : odefault) : Prop := ltac2:(tb__ "0|3|
S14OLd;Vd;S2S2S2SaS3Ll;M0G0S9S1fS4S8S9S9A2M1A1S4S20A1S1S28Z0M2R4A2S1S29G1S1bR4A1R2A3S0S9S2aQ40SdVrho;R3A2A2G2A3A2A2Ltmpl;Lflds;Lcnt;Lesz;X14x6").

Section G.
Variable segs : list Segment.

Lemma smatch_add_empty_gen : ltac2:(tb__ "0|2|
S1aS1eS16S8S4S30A1S2fA2S0S5S19S24R3R2A2A1S6A3S0S4SbA1S11R3A1S7SbA1A3S0S5SeScR4A1A1S6A3S29S17SfR7A1S18R6A1A3S1S0S9S12R8R6A2S13R8R6A2M0A3S1S1S25Z0S26S2aQ40SdR8S10R6A1A2A2G0A2M1A2S25G1S27Z2Z40A2A2A2S2eR8ScR6A1A2A2A2F_;S15Vsegs;R8R7R5A4S15Vsegs;R9S24R8R7A2R6A4F_;F_;F_;F_;F_;Fw;Fo;FSt;Frho;").
Proof using .
  intros rho St o [tr [ms md]] Hwf Hc Hdw Hemp Hsm.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *. destruct (Hemp Hfacts) as (Hhl & Hb & Hd).
  destruct Hmem as (Hall & Hpd & Hfr).
  unfold smatch, add_obj. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [exact Hwf|]. repeat (split; [assumption|]). split; [|exact Hfacts].
  split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds. cbn zeta. rewrite Hc. split; [lia|]. split; [intros off Hoff; lia|]. split; [constructor|].
    split; [intros off Hoff; lia|].
    destruct (ob_dflt o) as [| | |l|l|esz cnt flds tmpl]; cbn in Hd |- *; try exact I; try contradiction.
    destruct Hd as (He & Hf & Hz). rewrite Hz. split; [exact He|]. split; [exact Hf|]. split; [lia|]. intros k Hk. lia.
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app. cbn [map].
    revert Hpd. generalize (map (obj_range rho) (ss_objs St)) as l. intros l Hpd.
    induction l as [|r rest IH]; cbn in *; [split; [constructor | exact I]|].
    destruct Hpd as [Hf Hrest]. split; [|apply IH; exact Hrest].
    apply Forall_app. split; [exact Hf|]. constructor; [|constructor].
    unfold ranges_disjoint. right; left. unfold obj_range. cbn [fst snd]. lia.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. apply Forall_app in Hout as [A _]. exact A.
Qed.

Lemma SPA_add_empty_gen : ltac2:(tb__ "0|3|
S2dS1aS23S16S4S2bQ40M0A1A1S31S0S5S19S24S21R4A1R3A2A1S6A3S0S4SbA1S11R4A1S7SbA1A3S0S5SeScR5A1A1S6A3S0S5S1cS1dS21R7A1A1R6A2S6A3S29S17SfR9A1S18S21R8A1A1A3S1S0S9S12RaR8A2S13RaR8A2M1A3S1S1S25Z0S26S2aG0SdRaS10R8A1A2A2G1A2M2A2S25G2S27Z2Z40A2A2A2S2eRaScR8A1A2A2A2F_;S2cVsegs;RbR9RaR7R6A6S2cVsegs;RcS22RaS24S21RaA1R9A2A2RbR8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Fo;FA;Frho;FJ;").
Proof using .
  intros J rho A o tp [tr [ms md]] Hwf Hc Hdw Hwo Hemp [(Hsm & HMI & Haw & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_add_empty_gen rho (ax_S A) o _ Hwf Hc Hdw Hemp Hsm) as Hsm'.
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Haw |- *; cbn; exact Haw|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [add_obj set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|Ho2]; [exists o2; split; [exact Ho2 | exact Hx]|].
  exfalso. destruct Ho2 as [<-|[]].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hfacts.
  destruct (Hemp Hfacts) as [Hhl _]. unfold obj_range in Hx. cbn [fst snd] in Hx. lia.
Qed.
End G.
