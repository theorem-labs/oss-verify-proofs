(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sstate"; "valuation"; "ob_dflt"; "ob_hi"; "ob_lo"; "obj_holds"; "SLit"; "cell"; "ob_base"; "odefault"; "mem_match"; "ob_cells"; "c_off"; "c_width"; "eval"; "mkCell"; "mkObj"; "rw"; "soff"; "ss_objs"; "swf"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "false"; "bool"; "option"; "andb"; "list"; "prod"; "cons"; "true"; "Some"; "orb"; "app"; "fst"; "pair"; "snd"; "None"; "S"; "nat"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "small_lit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAz.ZCell"; "add_zcells"; "add_zcell"; "lit_cells_clear"; "zcell_ok"; "zcells_at"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "subst_state"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjUnbase ObjXform ZeroObj TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section ZCell.
Variable segs : list Segment.

Definition lit_cells_clear (cells : list cell) (off w : Z) : bool := ltac2:(tb__ "0|3|
S44ScScS4S1eLx;S11R1A1S0S20S2fR1A1S26S38S39R1S12R2A1A2Voff;A2S38S39Voff;Vw;A2R1A2A2A2Lz;S1S1dLi;S3bS4S4S1dLb;La;M0Lop;M1G1S3cG0Lop;M2G2S1eS2S4S1dLa;Lw0;Lsgn;S1S4S0S1dLk;Li;Ll;X4x8Lc;Vcells;A3").
Definition zcell_ok (o : sobj) (ow : Z * Z) : bool := ltac2:(tb__ "0|a|
SeS1eLx;S7Vo;A1S1dS4S1eLx;M0S9Vo;A1S0G0S8Vo;A1S0S20S20S20S20S20S20S2fR2A1S2fR1A1A2S2fS28S0S0Vow;A3M1A1A2S38R2G1A2A2S38S39G1S2aS0S0Vow;A3M2A2R1A2A2S26S26S26S37G2Z1A2S37G2Z2A2A2S37G2Z4A2A2S37G2Z8A2A2A2S34S10Vo;A1G1G2A3A2Lhi;S1S1dLi;M3S3bS4S4S1dLb;La;M4Lop;M5G5S3cG4Lop;M6G6S1eS2S4S1dLa;Lw;Lsgn;M7S1S4S0S1dLk;Li;Ll;M8X4x8Llo;G3G5G5G6G6G7G8X4x8S1dS1S1dLl;M9G9S0S4S21S22S0S0A2A1S21S1aA1S1dLtmpl;Lflds;Lcnt;Lesz;Xex6").
Definition add_zcell (o : sobj) (ow : Z * Z) : sobj := ltac2:(tb__ "0|0|
S15SdVo;A1S9Vo;A1S8Vo;A1S23ScS14SbS28S0S0Vow;A3A1S2aS0S0Vow;A3SbZ0A1A3S10Vo;A1A3S7Vo;A1A5").
Fixpoint add_zcells (o : sobj) (l : list (Z * Z)) : option sobj :=
  match l with
  | [] => Some o
  | ow :: r => if zcell_ok o ow then add_zcells (add_zcell o ow) r else None
  end.
Definition zcells_at (S : sstate) (i : nat) (l : list (Z * Z)) : option sstate := ltac2:(tb__ "0|3|
S1fS3A1S1fS5A1Lx;M0S45S3S18VS;A1M1Vi;A3S3G0S32R1Vl;A2S3S25S5S42VS;S27S3S3fS3Vi;G1A3S23S3R1S40S3S2cVi;A1G1A3A3A3A2A2Lo';S2bS5A1M2X1fx2Lo;G2X1fx2").

Lemma small_lit_soff : ltac2:(tb__ "0|0|
S6S0S1bS1eS2fR1A1S24A3S1bS0S17R3SbR2A1A2R2A3F_;Fz;Frho;").
Proof using .
  intros rho z H. unfold small_lit in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  apply soff_lit_small. lia.
Qed.

Lemma add_zcell_holds : ltac2:(tb__ "0|0|
S6S3aS3S22S0S0A2S1bS1eS35R2R1A2S24A3SaVsegs;R5R4R3A4SaVsegs;R6R5S33R4R3A2A4F_;F_;Fow;Fo;Fms;Frho;").
Proof using .
  intros rho ms o [off w] Hok (Hb & Hw & Hc & Hd & Hi). unfold zcell_ok in Hok. cbn [fst snd] in Hok.
  destruct (ob_dflt o) eqn:ED; try discriminate.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:ELO; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:EHI; try discriminate.
  apply andb_prop in Hok as [Hok Hclr]. apply andb_prop in Hok as [Hok Hw8]. apply andb_prop in Hok as [Hok H2].
  apply andb_prop in Hok as [Hok H1]. apply andb_prop in Hok as [Hok Hso]. apply andb_prop in Hok as [Hslo Hshi].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  assert (Hw' : 0 < w <= 8).
  { repeat (apply orb_prop in Hw8; destruct Hw8 as [Hw8|Hw8]); apply Z.eqb_eq in Hw8; lia. }
  unfold obj_holds, obj_lo_of, obj_hi_of in *. rewrite ELO, EHI in *.
  rewrite (small_lit_soff rho lo Hslo) in *. rewrite (small_lit_soff rho hi Hshi) in *.
  cbn [ob_base ob_lo ob_hi ob_cells ob_dflt add_zcell fst snd]. rewrite ELO, EHI, ED.
  rewrite (small_lit_soff rho lo Hslo). rewrite (small_lit_soff rho hi Hshi).
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hi]].
  - constructor; [|exact Hc]. unfold cell_holds. cbn [c_off c_width c_val]. rewrite (small_lit_soff rho off Hso).
    split; [lia|]. split; [lia|].
    rewrite eval_lit0.
    apply rd_bytes_of_nth.
    + apply enc_bytes_length.
    + unfold oaddr. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Z.mod_small by lia. lia.
    + intros j Hj. rewrite enc_bytes_zero_nth.
      assert (Hnc : ~ covered rho (ob_cells o) (off + Z.of_nat j)).
      { intros HC. unfold covered in HC. apply Exists_exists in HC as (c & Hin & Hcc). unfold in_cell in Hcc.
        pose proof (proj1 (forallb_forall _ _) Hclr c Hin) as X. cbv beta in X.
        destruct (c_off c) as [z| | | | | | |]; try discriminate. apply andb_prop in X as [Xs X].
        rewrite (small_lit_soff rho z Xs) in Hcc. apply orb_prop in X. destruct X as [X|X]; apply Z.leb_le in X; lia. }
      pose proof (Hd (off + Z.of_nat j) ltac:(lia) Hnc) as D0. cbn [dflt_holds] in D0.
      unfold oaddr. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Z.mod_small by lia.
      replace (bv_unsigned (eval rho (ob_base o)) + off + Z.of_nat j) with (bv_unsigned (eval rho (ob_base o)) + (off + Z.of_nat j)) by lia.
      exact D0.
  - intros off' Hoff' Hncov. apply (Hd off' Hoff'). intros Hcov. apply Hncov. unfold covered in *. constructor 2. exact Hcov.
Qed.

Lemma add_zcells_holds : ltac2:(tb__ "0|0|
S6S3aS21S22S0S0A2A1S3S3S1bS1fS3A1S32R2R3A2S25S3R1A2A3SaVsegs;R6R5R3A4SaVsegs;R7R6R3A4F_;F_;Fo';Fo;Fl;Fms;Frho;").
Proof using .
  intros rho ms l. induction l as [|ow r IH]; intros o o' H Ho; cbn [add_zcells] in H.
  - injection H as <-. exact Ho.
  - destruct (zcell_ok o ow) eqn:E; [|discriminate]. eapply IH; [exact H|]. apply add_zcell_holds; [exact E | exact Ho].
Qed.
Lemma add_zcells_shape : ltac2:(tb__ "0|0|
S21S22S0S0A2A1S3S3S1bS1fS3A1S32R2R3A2S25S3R1A2A3S1cS1bS4SdR2A1SdR3A1A3S1cS1bS4S9R2A1S9R3A1A3S1cS1bS4S8R2A1S8R3A1A3S1bSeS7R2A1S7R3A1A3A2A2A2F_;Fo';Fo;Fl;").
Proof using .
  induction l as [|ow r IH]; intros o o' H; cbn [add_zcells] in H.
  - injection H as <-. auto.
  - destruct (zcell_ok o ow); [|discriminate]. destruct (IH _ _ H) as (A & B & C & D).
    unfold add_zcell in A, B, C, D. cbn in A, B, C, D. auto.
Qed.
Lemma mem_match_zcells : ltac2:(tb__ "0|1|
S6S3aS21S3A1M0S3S3G0S21S22S0S0A2A1S1bS1fS3A1S32R4R1A2S25S3R3A2A3SfVsegs;R8S27S3R6S23S3R5R3A3A3R7A4SfVsegs;R9S27S3R7S23S3R5R4A3A3R8A4F_;F_;Fl;FL2;Fo';Fo;FL1;Fms;Frho;").
Proof using .
  intros rho ms L1 o o' L2 l H (Hall & Hpd & Hfr).
  destruct (add_zcells_shape l o o' H) as (EB & EL & EH & ED).
  assert (RNG : forall rho', obj_range rho' o' = obj_range rho' o).
  { intros rho'. unfold obj_range, obj_lo_of, obj_hi_of. rewrite EB, EL, EH. reflexivity. }
  assert (RNGS : forall rho', map (obj_range rho') (L1 ++ o' :: L2) = map (obj_range rho') (L1 ++ o :: L2)).
  { intros rho'. rewrite !map_app. cbn [map]. rewrite RNG. reflexivity. }
  split; [|split].
  - rewrite !Forall_app in Hall |- *. destruct Hall as (A & B). split; [exact A|].
    inversion B; subst. constructor; [|assumption]. eapply add_zcells_holds; eauto.
  - apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite RNGS. apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr.
    rewrite Forall_app in Ha |- *. destruct Ha as [Ha1 Ha2]. split; [exact Ha1|]. inversion Ha2; subst. constructor; [|assumption].
    rewrite <- RNG. assumption.
Qed.
Lemma SPJ_zcells : ltac2:(tb__ "0|0|
S31S6S5S2dS21S22S0S0A2A1S5S3dS1bS1fS5A1S36R5R4R3A3S25S5R2A2A3S1bS1eS41R6R3A2S24A3S30Vsegs;R9R7R8R3A5S30Vsegs;RaR5R9R4A5F_;F_;F_;Fw;FS';Fl;Fi;FS;Frho;FJ;").
Proof using .
  intros J rho S i l S' [tr [ms md]] H Hsame Hw.
  eapply SPJ_reobj; [exact Hsame | exact Hw |].
  destruct Hw as [Hsm _]. cbn [w_cfg cfg_ms].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  unfold zcells_at in H. destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (add_zcells o l) as [o'|] eqn:Ha; [|discriminate]. injection H as <-. cbn [ss_objs set_objs].
  rewrite (split_at_nth (ss_objs S) i o Hi) in Hmem.
  eapply mem_match_zcells; [exact Ha | exact Hmem].
Qed.
End ZCell.

Section Pin.
Variable segs : list Segment.
Lemma SPJ_pin : ltac2:(tb__ "0|2|
S31S6S5S1S4S1S3dS1bS1eS19S3eS23S22S1S4A2M0S29S1S4R4R3A4S2eG0A1M1A3R5R2A3A1S24A3S1bS1eS43S1S24L_;R6A2S24A3S1bS46Q40A1S16R8R6A2S13R8R5A2A3S30Vsegs;RaR8R9R4A5S30Vsegs;RbS3eS23G0S29S1S4R8R7A4G1A3R9R6A3RaR5A5F_;F_;F_;F_;Fw;Fnx;Fe;Fv;FS;Frho;FJ;").
Proof using .
  intros J rho S v e nx w Hwf Hall Hv [Hsm HJ]. split; [|exact HJ].
  apply smatch_subst_intro; [exact Hwf|].
  apply (smatch_agree_vars segs (fun _ => true) rho (rho_sub rho [(v, e)]) S w); [ | reflexivity | reflexivity | exact Hall | exact Hsm].
  intros u _. unfold rho_sub. cbn [rw]. unfold wsub_get. cbn [find fst snd].
  destruct (Pos.eqb u v) eqn:E; cbn [eval].
  - apply Pos.eqb_eq in E. subst u. exact Hv.
  - reflexivity.
Qed.
End Pin.
