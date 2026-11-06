(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "cell"; "sstate"; "sobj"; "eval"; "sv"; "c_val"; "sv_below"; "valuation"; "cell_holds"; "cell_wf"; "covered"; "smatch"; "ss_next"; "holds"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop"; "ss_facts"; "ss_objs"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@Corelib.Init.Datatypes"; "option"; "prod"; "nat"; "Some"; "bool"; "list"; "pair"; "true"; "None"; "S"; "app"; "cons"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "skipn"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA"; "recellv_nth"; "recellv_at"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue CellTile.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint recellv_nth (cells : list cell) (j : nat) (v' : sv) : option (list cell * cell) :=
  match cells, j with
  | [], _ => None
  | c :: r, O => Some (mkCell (c_off c) (c_width c) v' :: r, c)
  | c :: r, S j' => match recellv_nth r j' v' with Some (r', c0) => Some (c :: r', c0) | None => None end
  end.

Definition recellv_at (S : sstate) (i j : nat) (v' : sv) : option (sstate * cell) := ltac2:(tb__ "0|6|
S1aS2A1S1aS1bS1S0A2M0A1M1Lx;S34S2S16VS;A1M2Vi;A3S2S1aS1bS1fS0A1M3S0A2M4A1G1Lx;S2eS10R1A1Vj;Vv';A3G4G4G1Lp;R1G3S0S1dG0S20S1S0S39VS;S24S2S27S2Vi;G2A3S25S2SeSfR4A1S13R4A1S12R4A1R2S11R4A1A5S28S2S23Vi;A1G2A3A3A3A2R1A4A2Lc;Lcells';X1bx1Lp;S22G0A1M5X1ax2Lo;G5X1ax2").

Lemma recellv_nth_spec : ltac2:(tb__ "0|2|
S1fS0A1M0S1cS4G0S0S17S1aS1bG0S0A2M1A1S2eR5R4R3A3S1dG1S20G0S0R2R1A4A2A3S7S4S29S29S35S17S30Q40A1S3R5R9A2S3R5S5R7A1A2A3S18S26S0S8R6R5R4R3R2A5RcA3S26S0S8R7R6R5R4R3A5RaA3F_;S29S19SaR7RaR1A3SaR7RdR1A3A2Foff;A2F_;Fms;Fhi;Flo;Fbase;Frho;F_;Fc0;Fcells';Fv';Fj;Fcells;").
Proof.
  induction cells as [|c r IH]; intros [|j] v' cells' c0 H rho base lo hi ms Hev; cbn [recellv_nth] in H; try discriminate.
  - injection H as <- <-. split.
    + intros HF. inversion HF; subst. constructor; [|assumption].
      unfold cell_holds in *. cbn [c_off c_width c_val]. rewrite Hev. assumption.
    + intros off. unfold covered. rewrite !Exists_cons. unfold in_cell. cbn [c_off c_width]. tauto.
  - destruct (recellv_nth r j v') as [[r' c1]|] eqn:E; [|discriminate]. injection H as <- <-. split.
    + intros HF. inversion HF; subst. constructor; [assumption|]. exact (proj1 (IH j v' r' c1 E rho base lo hi ms Hev) ltac:(assumption)).
    + intros off. unfold covered. rewrite !Exists_cons. pose proof (proj2 (IH j v' r' c1 E rho base lo hi ms Hev) off) as X. unfold covered in X. tauto.
Qed.

Lemma recellv_nth_wf : ltac2:(tb__ "0|2|
S2aS1fS0A1M0S1cS4G0S0S17S1aS1bG0S0A2M1A1S2eR5R4R3A3S1dG1S20G0S0R2R1A4A2A3S17S1eS6R7R4A2S21A3S17S1eS33S0S9R8A1R7A3S21A3S17S1eS33S0S9R9A1R5A3S21A3F_;F_;F_;Fc0;Fcells';Fv';Fj;Fcells;Fn;").
Proof.
  intros n cells. induction cells as [|c r IH]; intros [|j] v' cells' c0 H Hb Hw; cbn [recellv_nth] in H; try discriminate;
    cbn [forallb] in Hw; apply andb_prop in Hw as [H1 H2].
  - injection H as <- <-. cbn [forallb]. rewrite H2, andb_true_r.
    unfold cell_wf in *. cbn [c_off c_width c_val]. apply andb_prop in H1 as [H1 _]. rewrite H1, Hb. reflexivity.
  - destruct (recellv_nth r j v') as [[r' c1]|] eqn:E; [|discriminate]. injection H as <- <-. cbn [forallb]. rewrite H1. exact (IH j v' r' c1 E Hb H2).
Qed.

Section WithSegs.
Variable segs : list Segment.

Theorem smatch_recellv : ltac2:(tb__ "0|1|
S7S1S1cS1cS4S1S0S1bS1fS37A1S36A2S17S1aS1bS1S0A2M0A1S2fR7R6R5R4A4S1dG0S20S1S0R3R2A4A2A3S17S1eS6ScR8A1R5A2S21A3S17S30Q40A1S3RaR6A2S3RaS5R4A1A2A3SbVsegs;RbRaR4A4SbVsegs;RcR7R5A4F_;F_;F_;F_;Fw;Fc0;FS';Fv';Fj;Fi;FS;Frho;").
Proof using .
  intros rho S i j v' S' c0 [tr [ms md]] H Hb Hev Hsm. unfold recellv_at in H.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (recellv_nth (ob_cells o) j v') as [[cells' c1]|] eqn:Hc; [|discriminate]. injection H as <- ->.
  pose proof Hsm as (Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  set (o' := mkObj (ob_base o) (ob_lo o) (ob_hi o) cells' (ob_dflt o)).
  apply (smatch_set_objs_next segs rho S _ (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) (ss_next S) (ss_lenient S)).
  - destruct S; exact Hsm.
  - rewrite (split_at_nth' (ss_objs S) i o Hi) in Hmem. destruct Hmem as (Hall & Hpd & Hfr).
    assert (RNG : forall rho', map (obj_range rho') (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S))
                              = map (obj_range rho') (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S i) (ss_objs S))).
    { intros rho'. rewrite !map_app. reflexivity. }
    split; [|split].
    + rewrite !Forall_app in Hall |- *. destruct Hall as (A & B). split; [exact A|].
      apply Forall_cons_iff in B as [Ho Brest]. constructor; [|exact Brest].
      destruct Ho as (H1 & H2 & H3 & H4 & H5).
      destruct (recellv_nth_spec (ob_cells o) j v' cells' c0 Hc rho (ob_base o) (obj_lo_of rho o) (obj_hi_of rho o) ms Hev) as [HC HCOV].
      unfold obj_holds. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi] in *.
      split; [exact H1|]. split; [exact H2|]. split; [exact (HC H3)|]. split; [|exact H5].
      intros off Hoff Hncov. apply (H4 off Hoff). intros Hcov. apply Hncov. apply (proj2 (HCOV off)). exact Hcov.
    + apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite RNG. apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
    + unfold mem_frame, outside_all in *. intros a Ha. apply Hfr.
      rewrite Forall_app in Ha |- *. destruct Ha as [Ha1 Ha2]. split; [exact Ha1|]. inversion Ha2; subst. constructor; assumption.
  - unfold swf in *. cbn [ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    apply andb_prop in Hwf as [Hwf Hf]. apply andb_prop in Hwf as [Hwf Hobjs]. rewrite Hwf, Hf.
    rewrite (split_at_nth' (ss_objs S) i o Hi) in Hobjs. rewrite forallb_app in Hobjs |- *.
    apply andb_prop in Hobjs as [X1 X2]. cbn [forallb] in X2 |- *. apply andb_prop in X2 as [X2 X3].
    rewrite X1, X3. replace (obj_wf (ss_next S) o') with true; [reflexivity|]. symmetry.
    unfold obj_wf in *. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    apply andb_prop in X2 as [X2 Xd]. apply andb_prop in X2 as [X2 Xc]. rewrite X2, Xd, (recellv_nth_wf _ _ _ _ _ _ Hc Hb Xc). reflexivity.
Qed.

Lemma SPA_recellv : ltac2:(tb__ "0|2|
S32S7S2dS1cS1cS4S1S0S1fS30Q40A1M0A1S38S17S1aS1bS1S0A2M1A1S2fS2bR8A1R7R6R5A4S1dG1S20S1S0R4R3A4A2A3S17S1eS6ScS2bR9A1A1R6A2S21A3S26S14SdRbA1S15S2bRaA1A1A3S17G0S3RcR8A2S3RcS5R6A1A2A3F_;S31Vsegs;RdRbRcR5R4A6S31Vsegs;ReS2cRcR8A2RdR6R5A6F_;F_;F_;F_;Fw;Ftp;Fc0;FS';Fv';Fj;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i j v' S' c0 tp [tr [ms md]] H Hb Hev [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (Hev (smatch_facts segs _ _ _ Hsm)) as E.
  assert (Hnext : ss_next S' = ss_next (ax_S A) /\ map obj_ext (ss_objs S') = map obj_ext (ss_objs (ax_S A))
                  /\ forallb (obj_wf (ss_next (ax_S A))) (ss_objs (ax_S A)) = true).
  { unfold recellv_at in H. destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hi; [|discriminate].
    destruct (recellv_nth (ob_cells o) j v') as [[cells' c1]|] eqn:Hc; [|discriminate]. injection H as <- <-.
    cbn [set_objs ss_next ss_objs]. split; [reflexivity|]. split.
    - transitivity (map obj_ext (firstn i (ss_objs (ax_S A)) ++ o :: skipn (Datatypes.S i) (ss_objs (ax_S A)))).
      + rewrite !map_app. reflexivity.
      + f_equal. symmetry. exact (split_at_nth' (ss_objs (ax_S A)) i o Hi).
    - pose proof Hsm as (Hwf0 & _). unfold swf in Hwf0. apply andb_prop in Hwf0 as [Hwf0 _]. apply andb_prop in Hwf0 as [_ Hobjs]. exact Hobjs. }
  destruct Hnext as (Hn & Hext & Hobwf).
  split; [exact (smatch_recellv rho (ax_S A) i j v' S' c0 _ H Hb E Hsm)|]. split; [exact HMI|].
  split; [unfold axwf in Hwf |- *; cbn [ax_S ax_X ax_base ax_setS]; rewrite Hn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  intros o2 x Ho2 Hx.
  assert (G : forall (l' l : list sobj) (x : sobj), map obj_ext l' = map obj_ext l -> In x l' ->
              exists o, In o l /\ ob_base o = ob_base x /\ ob_lo o = ob_lo x /\ ob_hi o = ob_hi x).
  { clear. induction l' as [|a t IH]; intros [|b u] x Hm Hin; cbn [map] in Hm; try discriminate; [destruct Hin|].
    injection Hm as Hab Hlo Hhi Htu. destruct Hin as [<-|Hin].
    - exists b. split; [left; reflexivity | auto].
    - destruct (IH u x Htu Hin) as (o & Ho & He). exists o. split; [right; exact Ho | exact He]. }
  destruct (G _ _ o2 Hext Ho2) as (o & Ho & Eb & El & Eh). exists o. split; [exact Ho|].
  unfold obj_range, obj_lo_of, obj_hi_of in Hx |- *. rewrite Eb, El, Eh. exact Hx.
Qed.
End WithSegs.
