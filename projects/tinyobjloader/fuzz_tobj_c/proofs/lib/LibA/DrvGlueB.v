(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "valuation"; "obj_holds"; "obj_range"; "mkCell"; "ss_objs"; "cell"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "enc_bytes"; "DImage"; "mem_match"; "outside_all"; "rom_ok"; "c_off"; "c_width"; "mkObj"; "sstate"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Init.Datatypes"; "false"; "bool"; "list"; "option"; "andb"; "true"; "prod"; "Some"; "cons"; "app"; "nat"; "S"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@Stdlib.ZArith.BinInt.Z"; "le"; "leb"; "add"; "lt"; "opp"; "pow"; "to_nat"; "ltb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_eq_dec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "replace_obj_at"; "add_cell_front"; "cells_clear_lit"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "skipn"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "list_eq_dec"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "image_bytes"; "set_objs"; "snorm"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "xshadow_outside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "uncovered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB.G"; "img_cell_apply"; "img_cell_okb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundM SymSoundR SymFrame SymObj SymEntail SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition replace_obj_at (St : sstate) (i : nat) (o' : sobj) : sstate := ltac2:(tb__ "0|1|
S49VSt;S28S3S40S3Vi;SaVSt;A1M0A3S27S3Vo';S41S3S2aVi;A1G0A3A3A3A2").
Definition add_cell_front (o : sobj) (c : cell) : sobj := ltac2:(tb__ "0|0|
S19ScVo;A1S10Vo;A1SfVo;A1S27SbVc;SdVo;A1A3SeVo;A1A5").
Definition cells_clear_lit (cells : list cell) (off k : Z) : bool := ltac2:(tb__ "0|4|
S43SbSbS4S20Lx;S17R1A1S0S2bS30S31S4aR1A1M0S18R2A1A2Voff;A2S30S31Voff;Vk;A2G0A2A2Lco;S1S1fLi;S4cS4S4S1fLb;La;M1Lop;M2G2S4dG1Lop;M3G3S20S2S4S1fLa;Lw;Lsgn;S1S4S0S1fLk0;Li;Ll;X4x8Lc;Vcells;A3").

Section G.
Variable segs : list Segment.

Lemma mem_match_replace : ltac2:(tb__ "0|1|
S6S21S3A1M0S3S3G0S45S1cS25S0S0A2S8R6R3A2S8R6R4A2A3S7Vsegs;R7R2R5A4S7Vsegs;R8R3R5A4F_;S14Vsegs;R8S28S3R7S27S3R6R4A3A3R3A4S14Vsegs;R9S28S3R8S27S3R6R5A3A3R4A4F_;F_;F_;Fms;FB;Fo';Fo;FA;Frho;").
Proof.
  intros rho A o o' B ms RNG Himp (Hh & Hpd & Hfr). split; [|split].
  - apply Forall_app in Hh as [HA HxB]. inversion HxB; subst. apply Forall_app. split; [exact HA|]. constructor; [apply Himp; assumption | assumption].
  - rewrite (pairwise_disjoint_pdr) in Hpd |- *. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Lemma firstn_skipn_of_split : forall {T} (l1 l2 : list T) (a : T),
  firstn (length l1) (l1 ++ a :: l2) = l1 /\ skipn (S (length l1)) (l1 ++ a :: l2) = l2.
Proof.
  intros T l1 l2 a. split.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r.
  - rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma outside_all_ranges : ltac2:(tb__ "0|3|
S6S21S3A1M0G0S37Q40A1S1cS21S25S0S0A2M1A1S3fS3G1S8R4A1M2R2A4S3fS3G1G2R3A4A3S15R5R4R2A3S15R6R4R3A3F_;F_;Fa;Fobjs';Fobjs;Frho;").
Proof.
  intros rho objs objs' a Hm H. unfold outside_all in *. rewrite Forall_forall in H |- *. intros o' Ho'.
  assert (Hin : In (obj_range rho o') (map (obj_range rho) objs)) by (rewrite <- Hm; apply in_map; exact Ho').
  apply in_map_iff in Hin as (o & Ho & Hino). cbv zeta. rewrite <- Ho. exact (H o Hino).
Qed.

Lemma xshadow_outside_ranges : ltac2:(tb__ "0|3|
S6S2dS21S3A1M0G0S1cS21S25S0S0A2M1A1S3fS3G1S8R4A1M2R1A4S3fS3G1G2R2A4A3S4eR5R4R3A3S4eR6R5R3A3F_;F_;Fobjs';Fobjs;FA;Frho;").
Proof.
  intros rho A objs objs' Hm H. unfold xshadow_outside in *. rewrite Forall_forall in H |- *. intros r Hr a j Ha Hj.
  eapply outside_all_ranges; [exact Hm | exact (H r Hr a j Ha Hj)].
Qed.

Lemma nth_error_split' : forall {T} (l : list T) i x, nth_error l i = Some x ->
  exists l1 l2, l = l1 ++ x :: l2 /\ length l1 = i.
Proof.
  intros T l i x H. exists (firstn i l), (skipn (S i) l). split; [apply nth_error_split3; exact H | ].
  apply firstn_length_le. apply Nat.lt_le_incl. apply nth_error_Some. congruence.
Qed.

Lemma SPA_replace_obj : ltac2:(tb__ "0|1|
S3bS6S2dS29S3S3S21S37Q40A1A1S46S1cS22S3A1S42S3SaS2cR6A1A1R5A3S26S3R4A2A3S1cS25S0S0A2S8R8R4A2S8R8R5A2A3S45S16Vsegs;R1A2S7Vsegs;RbR2R8A4S7Vsegs;RcR3R8A4F_;F_;Fms;S1cS20S47S2cR9A1M0S3cG0R8R6A3A2S24A3S3aVsegs;RcRaRbR6R5A6S3aVsegs;RdS2eRbS3cS2cRbA1RaR8A3A2RcR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fo';Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o o' tp w Hn RNG Himp Hsame Hsp.
  destruct (nth_error_split' _ _ _ Hn) as (l1 & l2 & Hl & Hlen).
  assert (Eobjs : ss_objs (replace_obj_at (ax_S A) i o') = l1 ++ o' :: l2).
  { unfold replace_obj_at. cbn [ss_objs set_objs]. rewrite Hl, <- Hlen. destruct (firstn_skipn_of_split l1 l2 o) as [-> ->]. reflexivity. }
  apply (SPA_reobj segs J rho A (replace_obj_at (ax_S A) i o') tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segs _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segs _ _ _ _ _ S0) as MM. pose proof S0 as (_ & _ & _ & _ & Hrom & _). cbn [cfg_ms w_cfg snd] in Hrom.
    rewrite Eobjs. rewrite Hl in MM.
    apply (mem_match_replace rho l1 o o' l2); [exact RNG | apply Himp; exact Hrom | exact MM].
  - destruct Hsp as [Hsm _]. apply (xshadow_outside_ranges rho A (ss_objs (ax_S A))).
    + rewrite Eobjs, Hl, !map_app. cbn [map]. rewrite RNG. reflexivity.
    + apply shadow_ok_outside. exact (smatchA_shadow segs _ _ _ _ Hsm).
Qed.

Lemma cells_clear_lit_uncovered : ltac2:(tb__ "0|0|
S6S21SbA1S0S0S1cS20S3eR3R2R1A3S24A3S4fR5R4R3R2A4F_;Fk;Foff;Fcells;Frho;").
Proof.
  intros rho cells off k H j Hj Hcov. unfold SymState.covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hin).
  pose proof (proj1 (forallb_forall _ _) H c Hc) as X. cbv beta in X. unfold in_cell in Hin.
  destruct (c_off c) as [co| | | | | | |]; try discriminate. rewrite soff_lit in Hin.
  apply Bool.orb_true_iff in X as [X|X]; [apply Z.leb_le in X | apply Z.leb_le in X]; lia.
Qed.

Lemma obj_holds_add_img_cell : ltac2:(tb__ "0|5|
S6S45S3S0S0S0S0S0S16Vsegs;R7A2S7Vsegs;R9R8R7A4S1cS11SeR8A1S13A3S1cS4ScR9A1S5Z0M0A1A3S1cS4S10RaA1S5R9A1M1A3S1cS4SfRbA1G1A3S2fS33S34Z2Z3fA2M2A1RbA2S32RbG2A2S2fRdRbA2S2fS31RcRbA2RdA2S1dS32G0RcA2S2fRcZ8A2A2S1cS20S3eSdR11A1ReRdA3S24A3S1cS22S21S37Q8A1A1M3A1S48Vsegs;RfS35ReA1M4A3S26G3S12G4S38Q40RdA2A2A2A3S7Vsegs;R15R14S3dR13S9S5R10A1RfS5ReA1A3A2A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fhi;Flo;Fo;Fms;Frho;").
Proof.
  intros rho ms o lo hi off k v Hrom Ho Hz Hb Hlo Hhi Hlo63 Hhi63 H1 H2 Hk Hclr Himg.
  assert (Elo : obj_lo_of rho o = lo) by (unfold obj_lo_of; rewrite Hlo; apply soff_lit_small; lia).
  assert (Ehi : obj_hi_of rho o = hi) by (unfold obj_hi_of; rewrite Hhi; apply soff_lit_small; lia).
  unfold add_cell_front.
  apply (obj_holds_add_cells segs rho ms o [mkCell (SLit off) k (SLit v)] Ho).
  constructor; [|constructor]. unfold cell_holds. cbn [c_off c_width c_val]. rewrite soff_lit_small by lia. rewrite Elo, Ehi.
  split; [lia|]. split; [lia|].
  rewrite (obj_read_image segs rho ms o off k _ Hrom Ho Hz Hb ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)
             (cells_clear_lit_uncovered rho _ _ _ Hclr) Himg).
  reflexivity.
Qed.

Lemma SPA_add_img_cell : ltac2:(tb__ "0|8|
S3bS6S2dS29S3S0S0S0S0S0S21S37Q40M0A1A1S46S1cS22S3A1S42S3SaS2cRaA1A1R9A3S26S3R8A2A3S1cS11SeR9A1S13A3S1cS4ScRaA1S5Z0M1A1A3S1cS4S10RbA1S5RaA1M2A3S1cS4SfRcA1G2A3S2fS33S34Z2Z3fA2M3A1RcA2S32RcG3A2S2fReRcA2S2fS31RdRcA2ReA2S1dS32G1RdA2S2fRdZ8A2A2S1cS20S3eSdR12A1RfReA3S24A3S1cS22S21S37Q8A1A1M4A1S48Vsegs;R10S35RfA1M5A3S26G4S12G5S38G0ReA2A2A2A3S1cS20S47S2cR16A1M6S3cG6R15S3dR14S9S5R11A1M7R10S5RfA1A3A2A3A2S24A3S3aVsegs;R19R17R18RfReA6S3aVsegs;R1aS2eR18S3cS2cR18A1R17S3dR16S9S5R13A1R12G7A3A2A3A2R19R10RfA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fv;Fk;Foff;Fhi;Flo;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o lo hi off k v tp w Hn Hz Hb Hlo Hhi Hlo63 Hhi63 H1 H2 Hk Hclr Himg Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms Hrom Ho. eapply obj_holds_add_img_cell; eauto.
Qed.

Definition img_cell_okb (S : sstate) (i : nat) (off k v : Z) : bool := ltac2:(tb__ "0|11|
S22S3A1S20Lx;S42S3SaVS;A1Vi;A3S3S11S20Lx;SeR1A1S1fS1fS4S20Lx;M0ScR1A1S0S0S20Lz;R1G0S10R2A1S0G0SfR3A1S0S23S23S23S23S23S23S23S23S30S33S34Z2Z3fA2M1A1R2A2S36R1G1A2A2S30R2Voff;A2A2S30S31Voff;Vk;A2R1A2A2S36Z0Vk;A2A2S30Vk;Z8A2A2S3eSdR4A1Voff;Vk;A3A2S22S21S37Q8M2A1M3A1M4A1S20Lx;S48Vsegs;Voff;S35Vk;A1M5A3G4S4bS1cG4R1S12G5S38Q40Vv;A2A2M6A3M7S1eG7A1M8A2S20L_;S44G3S39G2A1R1G6A4G7S24L_;G8S1fL_;X4bx2Lbs;S1fX22x2A2S47VS;S3cVS;Vi;S3dR4S9S5Voff;A1Vk;S5Vv;A1A3A2A3A2A2Lhi;S1S1fLi0;M9S4cS4S4S1fLb;La;MaLop;MbGbS4dGaLop;McGcS20S2S4S1fLa;Lw;Lsgn;MdS1S4S0S1fLk0;Li0;Ll;MeX4x8Llo;G9GbGbGcGcGdGeX4x8S1S1fLp;MfGfX0x3Lz;G9GbGbGcGcGdGeX4x8S1S1fLl;M10G10S0S4S21S25S0S0A2A1S21S1bA1S1fLtmpl;Lflds;Lcnt;Lesz;X11x6Lo;S1fX22x2").
Definition img_cell_apply (S : sstate) (i : nat) (off k v : Z) : sstate := ltac2:(tb__ "0|0|
S22S3A1S1aLx;S42S3SaVS;A1Vi;A3S3S3cVS;Vi;S3dR1S9S5Voff;A1Vk;S5Vv;A1A3A2A3Lo;VS;X22x2").

Lemma SPA_img_cell : ltac2:(tb__ "0|0|
S3bS6S2dS29S0S0S0S21S37Q40A1A1S46S1cS20S51S2cR7A1R6R5R4R3A5S24A3S3aVsegs;RaR8R9R3R2A6S3aVsegs;RbS2eR9S50S2cR9A1R8R7R6R5A5A2RaR4R3A6F_;F_;Fw;Ftp;Fv;Fk;Foff;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i off k v tp w H HS. unfold img_cell_okb in H. unfold img_cell_apply.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (ob_dflt o) eqn:Hd; try discriminate.
  destruct (ob_base o) as [bz|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:Hb; try discriminate. destruct bz; try discriminate.
  destruct (ob_lo o) as [lo|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:Hlo; try discriminate.
  destruct (ob_hi o) as [hi|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:Hhi; try discriminate.
  apply andb_prop in H as [H Hsame]. apply andb_prop in H as [H Himg]. apply andb_prop in H as [H Hclr].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply Z.leb_le in H6.
  destruct (image_bytes segs off (Z.to_nat k)) as [bs|] eqn:Hib; [|discriminate].
  destruct (list_eq_dec _ bs _) as [->|]; [|discriminate].
  eapply (SPA_add_img_cell J rho A i o lo hi off k v tp w Hn Hd Hb Hlo Hhi); try assumption; try lia.
Qed.
End G.
