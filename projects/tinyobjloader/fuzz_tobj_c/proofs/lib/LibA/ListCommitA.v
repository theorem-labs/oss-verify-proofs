(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_objs"; "ss_next"; "sstate"; "valuation"; "smatch"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "outside_all"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "false"; "negb"; "orb"; "nat"; "pair"; "Some"; "andb"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "obj_ext"; "ax_S"; "ax_setS"; "axst"; "ax_X"; "ax_base"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "sv_has_rl"; "rho_set_rl"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "smatchA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "virt"; "vmd"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA.LCA"; "exts_rl_free"; "X_rl_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_cfg"; "w_tr"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListCommit"; "commit_at"; "obj_upd"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymObj SymMaterialize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ListCommit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section LCA.
Variable segs : list Segment.

Definition exts_rl_free (l : positive) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S37S1S1S12S13S13S22Vl;S7R1A1A2S22Vl;S9R1A1A2A2S22Vl;S8R1A1A2A2A1Lo;Vobjs;A3").
Definition X_rl_free (l : positive) (A : axst) : bool := ltac2:(tb__ "0|1|
S17S12S22Vl;S20VA;A1A2A1S37SeS0S0A2M0G0S12S13S22Vl;S18S0S0R1A3A2S22Vl;S1aS0S0R1A3A2A2A1Lr;S1fVA;A1A3A2").

Lemma obj_range_set_rl : ltac2:(tb__ "0|0|
S5S25SdS24Q8A1A1S1ScSfS22R3S7R1A1A2S11A3ScSfS22R4S9R2A1A2S11A3ScSfS22R5S8R3A1A2S11A3ScSeS26S26A2SaS23R7R6R5A3R4A2SaR7R4A2A3F_;F_;F_;Fo;FL;Fl;Frho;").
Proof using .
  intros rho l L o Hb Hlo Hhi. unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite !eval_set_rl by assumption. reflexivity.
Qed.

Lemma outside_all_exts_rl : ltac2:(tb__ "0|2|
S5S25SdS24Q8A1A1SdS1A1M0G0S24Q40A1ScSdSeSeS0S0A2S0A2M1A1S21S1G1S1bR2A4S21S1G1S1bR3A4A3ScSfS32R6R4A2S10A3SbR8R5R3A3SbS23R9R8R7A3R5R4A3F_;F_;F_;Fx;Fobjs';Fobjs;FL;Fl;Frho;").
Proof using .
  intros rho l L objs. induction objs as [|o t IH]; intros [|o' t'] x Hm Hf H; cbn in Hm; try discriminate; [constructor|].
  assert (Ho : obj_ext o' = obj_ext o) by congruence. assert (Ht : map obj_ext t' = map obj_ext t) by congruence.
  cbn in Hf. apply andb_prop in Hf as [Hfo Hft].
  apply Bool.negb_true_iff in Hfo. apply Bool.orb_false_iff in Hfo as [Hfo Hhi]. apply Bool.orb_false_iff in Hfo as [Hb Hlo].
  inversion H; subst. constructor; [|apply IH; assumption].
  destruct o' as [b' lo' hi' c' d'], o as [b lo hi c d]. unfold obj_ext in Ho. cbn [ob_base ob_lo ob_hi] in Ho, Hb, Hlo, Hhi.
  assert (Eb : b' = b) by congruence. assert (Elo : lo' = lo) by congruence. assert (Ehi : hi' = hi) by congruence.
  subst b' lo' hi'.
  rewrite (obj_range_set_rl rho l L (mkObj b lo hi c' d')) by assumption.
  unfold obj_range, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi] in *. assumption.
Qed.

Lemma smatchA_relist : ltac2:(tb__ "0|1|
S5S25SdS24Q8A1A1SdS24Q40A1A1S1eS4SeSdS30A1S27A2S2aVsegs;R7R4R3R1A5S6Vsegs;S23R8R7R6A3R3S2dR5R2A2A4ScS25S3R4A1S3S1cR5A1A1A3ScSdSeSeS0S0A2S0A2M0A1S21S1G0S1bS2R5A1A4S21S1G0S1bS2S1cR6A1A1A4A3ScSfS32RaS2S1cR7A1A1A2S10A3ScSfS33RbR8A2S10A3S2aVsegs;S23RdRcRbA3RaS1dR9R8A2R7A5F_;F_;F_;F_;F_;F_;Fw;FS';FA;Ftp;FL;Fl;Frho;").
Proof using .
  intros rho l L tp A S' w (Hsm & HMI & Hwf & Hsh & Hhz) Hsm' Hnx Hexts Hfree HX.
  split; [exact Hsm'|]. split; [exact HMI|]. split.
  { unfold axwf in *. cbn [ax_S ax_X ax_base ax_setS]. rewrite Hnx. exact Hwf. }
  split; [|exact Hhz].
  unfold X_rl_free in HX. apply andb_prop in HX as [HXb HXr]. apply Bool.negb_true_iff in HXb.
  eapply (shadow_ok_transport rho (rho_set_rl rho l L) A (ax_setS A S')); [reflexivity | | | | exact Hsh].
  - cbn. apply eval_set_rl. exact HXb.
  - intros r Hr. pose proof (proj1 (forallb_forall _ _) HXr r Hr) as F. apply Bool.negb_true_iff in F.
    apply Bool.orb_false_iff in F as [F1 F2]. split; apply eval_set_rl; assumption.
  - intros x _ Ho _. split; [|reflexivity]. cbn [ax_S ax_setS]. eapply outside_all_exts_rl; eauto.
Qed.

Lemma SPA_relist : ltac2:(tb__ "0|1|
S2cS5S25SdS24Q8A1A1SdS24Q40A1A1S1eS4S34S2bVsegs;R8R3R7R4R1A6S6Vsegs;S23R8R7R6A3R3S2dR5R2A2A4ScS25S3R4A1S3S1cR5A1A1A3ScSdSeSeS0S0A2S0A2M0A1S21S1G0S1bS2R5A1A4S21S1G0S1bS2S1cR6A1A1A4A3ScSfS32RaS2S1cR7A1A1A2S10A3ScSfS33RbR8A2S10A3ReS23RdRcRbA3RaS36R7A1S29S35R7A1A1A4S2bVsegs;RfS1dRaR9A2S23ReRdRcA3RbR8A6F_;F_;F_;F_;F_;F_;F_;Fw;FS';FA;Ftp;FL;Fl;Frho;FJ;").
Proof using .
  intros J rho l L tp A S' w [Hsm _] Hsm' Hnx Hexts Hfree HX HJ. split; [|exact HJ].
  eapply smatchA_relist; eauto.
Qed.

Lemma smatchA_reobjs_same : ltac2:(tb__ "0|1|
S5SdS24Q40A1A1S1eS4SeSdS30A1S27A2S2aVsegs;R5R4R3R1A5S6Vsegs;R6R3S2dR5R2A2A4ScS25S3R4A1S3S1cR5A1A1A3ScSdSeSeS0S0A2S0A2M0A1S21S1G0S1bS2R5A1A4S21S1G0S1bS2S1cR6A1A1A4A3S2aVsegs;R9R8S1dR7R6A2R5A5F_;F_;F_;F_;Fw;FS';FA;Ftp;Frho;").
Proof using .
  intros rho tp A S' w (Hsm & HMI & Hwf & Hsh & Hhz) Hsm' Hnx Hexts.
  split; [exact Hsm'|]. split; [exact HMI|]. split.
  { unfold axwf in *. cbn [ax_S ax_X ax_base ax_setS]. rewrite Hnx. exact Hwf. }
  split; [|exact Hhz].
  apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_S ax_setS]. intros x _ Ho _.
  revert Ho. generalize (ss_objs (ax_S A)) (ss_objs S') Hexts. clear.
  induction l as [|o t IH]; intros [|o' t'] Hm H; cbn in Hm; try discriminate; [constructor|].
  assert (Ho : obj_ext o' = obj_ext o) by congruence. assert (Ht : map obj_ext t' = map obj_ext t) by congruence.
  inversion H; subst. constructor; [|apply IH; assumption].
  destruct o' as [b' lo' hi' c' d'], o as [b lo hi c d]. unfold obj_ext in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  assert (Eb : b' = b) by congruence. assert (Elo : lo' = lo) by congruence. assert (Ehi : hi' = hi) by congruence.
  subst b' lo' hi'. unfold obj_range, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi] in *. assumption.
Qed.

Lemma obj_upd_exts : ltac2:(tb__ "0|1|
S4S14S1S1ScS19S1A1S38S1S2R4A1R3A3S16S1R2A2A3ScSeSeS0S0A2S0A2M0S1bR2A1S1bR3A1A3ScSdG0A1S21S1G0S1bS2S3bR6R5R3A3A1A4S21S1G0S1bS2R6A1A4A3F_;F_;Fo';Fo;Fk;FS;").
Proof using .
  intros S k o o' Hn He. unfold obj_upd. cbn [ss_objs set_objs].
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  transitivity (map obj_ext (firstn k (ss_objs S) ++ o :: skipn (Datatypes.S k) (ss_objs S))); [|rewrite <- EQ; reflexivity].
  rewrite !map_app. cbn [map]. rewrite He. reflexivity.
Qed.
Lemma commit_at_exts : ltac2:(tb__ "0|1|
S4S14S25ScSdSeSeS0S0A2S0A2M0A1S21S1G0S1bS2S3aR3R2R1A3A1A4S21S1G0S1bS2R3A1A4A3Fl;Fk;FS;").
Proof using .
  intros S k l. unfold commit_at. destruct (nth_error (ss_objs S) k) as [o|] eqn:E; [|reflexivity].
  eapply obj_upd_exts; [exact E|reflexivity].
Qed.

Lemma virt_cfg : ltac2:(tb__ "0|1|
SdS24Q40A1A1SdS30A1M0S39S31ScS34S2dR4S15G0S27R3S28R2R1A2A4A2S15G0S27R3S28S2fR1R4R2A3S2eR1A1A2A4A3Fmd;Fms;Ftr;Ftp;").
Proof using . reflexivity. Qed.

End LCA.
