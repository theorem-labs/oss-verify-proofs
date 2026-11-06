(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "true"; "cons"; "prod"; "app"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "cell"; "sv"; "valuation"; "DUnknown"; "SLit"; "eval"; "holds"; "ob_base"; "ob_cells"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "odefault"; "smatch"; "sprop"; "ss_facts"; "swf"; "obj_wf"; "ss_next"; "ss_objs"; "sstate"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "add"; "lt"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundL SymSoundM SymSoundR SymFrame SymObj SymEntail SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition add_obj (St : sstate) (o : sobj) : sstate := ltac2:(tb__ "0|0|
S33VSt;S8SaS1eVSt;A1S6SaVo;S4SaA1A3A3A2").

Section G.
Variable segs : list Segment.

Lemma smatch_add_empty : ltac2:(tb__ "0|2|
SdS1fSaS7S2S32A1S31A2S0S3S1bS2cR3R2A2A1S5A3S0S2SbA1S13R3A1S4SbA1A3S0S17S14R4A1SeA3S2dS19S11R7A1S1aR6A1A3S1S0S25S15R8R6A2S16R8R6A2M0A3S1S20Z0S22S30Q40S10R8S12R6A1A2A2G0A2M1A2S20G1S21Z2Z40A2A2A2A2F_;S18Vsegs;R8R7R5A4S18Vsegs;R9S2cR8R7A2R6A4F_;F_;F_;F_;F_;Fw;Fo;FSt;Frho;").
Proof using .
  intros rho St o [tr [ms md]] Hwf Hc Hd Hemp Hsm.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *. destruct (Hemp Hfacts) as [Hhl Hb].
  destruct Hmem as (Hall & Hpd & Hfr).
  unfold smatch, add_obj. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [exact Hwf|]. repeat (split; [assumption|]). split; [|exact Hfacts].
  split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds. cbn zeta. rewrite Hc, Hd. split; [lia|]. split; [intros off Hoff; lia|]. split; [constructor|].
    split; [intros off Hoff; lia|]. exact I.
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app. cbn [map].
    revert Hpd. generalize (map (obj_range rho) (ss_objs St)) as l. intros l Hpd.
    induction l as [|r rest IH]; cbn in *; [split; [constructor | exact I]|].
    destruct Hpd as [Hf Hrest]. split; [|apply IH; exact Hrest].
    apply Forall_app. split; [exact Hf|]. constructor; [|constructor].
    unfold ranges_disjoint. right; left. unfold obj_range. cbn [fst snd]. lia.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. apply Forall_app in Hout as [A _]. exact A.
Qed.

Lemma SPA_add_empty : ltac2:(tb__ "0|3|
S27SdS29SaS2S2fQ40M0A1A1S2eS0S3S1bS2cS28R4A1R3A2A1S5A3S0S2SbA1S13R4A1S4SbA1A3S0S17S14R5A1SeA3S0S3S1cS1dS28R7A1A1R6A2S5A3S2dS19S11R9A1S1aS28R8A1A1A3S1S0S25S15RaR8A2S16RaR8A2M1A3S1S20Z0S22S30G0S10RaS12R8A1A2A2G1A2M2A2S20G2S21Z2Z40A2A2A2A2F_;S26Vsegs;RbR9RaR7R6A6S26Vsegs;RcS2bRaS2cS28RaA1R9A2A2RbR8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Fo;FA;Frho;FJ;").
Proof using .
  intros J rho A o tp [tr [ms md]] Hwf Hc Hd Hwo Hemp [(Hsm & HMI & Haw & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_add_empty rho (ax_S A) o _ Hwf Hc Hd Hemp Hsm) as Hsm'.
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Haw |- *; cbn; exact Haw|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [add_obj set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|Ho2]; [exists o2; split; [exact Ho2 | exact Hx]|].
  exfalso. destruct Ho2 as [<-|[]].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hfacts.
  destruct (Hemp Hfacts) as [Hhl _]. unfold obj_range in Hx. cbn [fst snd] in Hx. lia.
Qed.

Lemma SPA_x_publish_empty : ltac2:(tb__ "0|1|
S27SdS29S25S2S2fQ40A1A1S2eS1S20Z0M0R3A2S23R3S21Z2Z40A2A2A2S0S25S24R4Z8A2G0A3S26Vsegs;R8R6R7R4R3A6S26Vsegs;R9S34R7S6S7ScScA2S9ScScSfR6A1SfG0A1A4S2aR7A1A3A2R8R5R4A6F_;F_;F_;Fw;Ftp;Fb;FA;Frho;FJ;").
Proof using .
  intros J rho A b tp w Hb H8 HS. apply SPA_x_publish; [reflexivity | | exact HS].
  unfold xr_ok. cbn [fst snd eval]. rewrite !lit_unsigned. rewrite (Z.mod_small b) by lia. rewrite (Z.mod_small 0) by lia.
  split; [exact H8|]. split; [lia|]. intros a Ha. lia.
Qed.
End G.
