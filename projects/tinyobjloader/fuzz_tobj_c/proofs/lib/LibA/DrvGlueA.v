(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "DUnknown"; "cell"; "ob_cells"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "obj_range"; "odefault"; "ss_objs"; "obj_holds"; "valuation"; "mkObj"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "nil"; "option"; "prod"; "S"; "Some"; "app"; "bool"; "cons"; "nat"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "forget_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition set_obj_at (S : sstate) (i : nat) (o : sobj) : sstate := ltac2:(tb__ "0|1|
S2fVS;S19S0S2aS0Vi;S9VS;A1M0A3S1bS0Vo;S2bS0S17Vi;A1G0A3A3A3A2").

Definition forget_obj (o : sobj) : sobj := ltac2:(tb__ "0|0|
ScSdVo;A1SfVo;A1SeVo;A1S14S2A1S1A5").
Definition forget_at (S : sstate) (i : nat) : sstate := ltac2:(tb__ "0|0|
S15S0A1S10Lx;S25S0S9VS;A1Vi;A3S0S21VS;Vi;S22R1A1A3Lo;VS;X15x2").

Section G.
Variable segs : list Segment.

Lemma nth_error_split3 : forall {T} (l : list T) i x, nth_error l i = Some x -> l = firstn i l ++ x :: skipn (S i) l.
Proof.
  intros T l. induction l as [|y r IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - f_equal. apply IH. exact H.
Qed.

Lemma obj_holds_unknown_range : ltac2:(tb__ "0|2|
SbS2cS0S0S11S13S2A1M0S3R2A1S14S2A1M1A3S11S8S4R3A1S1A3S11G0S3R3A1G1A3S11S8S4R4A1S1A3S11S16S12S12A2S7R8R5A2S7R8R6A2A3S26S6R9R6A2S5R9R6A2A2S27S29S5RaR7A2S6RaR7A2A2S28Z2Z3fA2A2SaVsegs;RbRaR9A4SaVsegs;RcRbR9A4F_;F_;F_;F_;F_;F_;F_;F_;Fo';Fo;Fms;Frho;").
Proof.
  intros rho ms o o' Hc Hd Hc' Hd' Hr Hle Hsz (Hb & Hw & Hcells & Hdf & Hinv).
  unfold obj_range in Hr. injection Hr as E1 E2.
  unfold obj_holds. cbv zeta. rewrite Hc', Hd'. rewrite Hd in Hw. cbn [dflt_writable dflt_holds dflt_inv] in Hw |- *.
  split; [lia|]. split.
  - intros off Hoff _. replace (bv_unsigned (eval rho (ob_base o')) + off) with
      (bv_unsigned (eval rho (ob_base o)) + (off + obj_lo_of rho o - obj_lo_of rho o')) by lia.
    apply Hw; [lia | reflexivity].
  - split; [constructor|]. split; [| exact I].
    intros off Hoff _. rewrite Hc, Hd in Hdf. cbn [dflt_holds] in Hdf.
    replace (bv_unsigned (eval rho (ob_base o')) + off) with
      (bv_unsigned (eval rho (ob_base o)) + (off + obj_lo_of rho o - obj_lo_of rho o')) by lia.
    apply Hdf; [lia|]. intros HC. unfold covered in HC. apply Exists_exists in HC as (c & Hin & _). destruct Hin.
Qed.

Lemma SPA_reslice : ltac2:(tb__ "0|3|
S24SbS20S1cS0S0S13S30Q40A1A1S2dS11S15S0A1S25S0S9S1eR6A1A1R5A3S18S0R4A2A3S11S13S2A1M0S3R5A1S14S2A1M1A3S11S8S4R6A1S1A3S11G0S3R6A1G1A3S11S8S4R7A1S1A3S11S1aS2eS1eRbA1M2S21G2RaR8A3A2S1dA3S11S16S12S12A2S7RdR9A2S7RdRaA2A3S26S6ReRaA2S5ReRaA2A2S27S29S5RfRbA2S6RfRbA2A2S28Z2Z3fA2A2S23Vsegs;R11RfR10RbRaA6S23Vsegs;R12S1fR10S21S1eR10A1RfRdA3A2R11RcRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fo';Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o o' tp w Hn Hc Hd Hc' Hd' Hsame Hr Hle Hsz HS.
  pose proof HS as [(Hsm & HMI & Haw & Hsh & Hhz) Hk].
  pose proof (nth_error_split3 (ss_objs (ax_S A)) i o Hn) as EO.
  assert (Hin : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  apply (SPA_reobj segs J rho A (set_obj_at (ax_S A) i o') tp w).
  - exact Hsame.
  - reflexivity.
  - exact HS.
  - destruct w as [tr [ms md]]. unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg].
    unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
    pose proof (smatch_mm segs _ _ _ _ _ Hsm) as Hmm. cbn [ss_objs set_obj_at set_objs].
    rewrite EO in Hmm.
    change (firstn i (ss_objs (ax_S A)) ++ o' :: skipn (S i) (ss_objs (ax_S A)))
      with (firstn i (ss_objs (ax_S A)) ++ [o'] ++ skipn (S i) (ss_objs (ax_S A))).
    apply (mem_match_replace segs rho _ (firstn i (ss_objs (ax_S A))) o (skipn (S i) (ss_objs (ax_S A))) [o'] Hmm).
    + constructor; [|constructor]. destruct Hmm as (Hall & _ & _).
      apply (obj_holds_unknown_range rho _ o o' Hc Hd Hc' Hd' Hr Hle Hsz).
      exact (proj1 (Forall_forall _ _) Hall o ltac:(apply in_or_app; right; left; reflexivity)).
    + destruct Hmm as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
      rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hr. exact Hpd.
    + intros x. split.
      * intros Hx. exists o'. split; [left; reflexivity|]. rewrite Hr. exact Hx.
      * intros (o2 & [<-|[]] & Hx). rewrite Hr in Hx. exact Hx.
  - apply xshadow_outside_cover; [exact Hsh|]. cbn [ss_objs set_obj_at set_objs].
    intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
    + exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
    + exists o. split; [exact Hin|]. rewrite <- Hr. exact Hx.
    + exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.
End G.
