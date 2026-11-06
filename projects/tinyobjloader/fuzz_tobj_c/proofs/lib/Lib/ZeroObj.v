(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sstate"; "cell"; "SLit"; "obj_holds"; "odefault"; "smatch"; "valuation"; "DZero"; "c_off"; "c_val"; "c_width"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_objs"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "option"; "false"; "Some"; "list"; "None"; "andb"; "nat"; "prod"; "true"; "S"; "app"; "cons"; "nil"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "snorm"; "set_objs"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ZeroObj"; "zcover_from"; "zero_obj"; "zcell_covers"; "zero_obj_at"; "@Stdlib.ZArith.BinInt.Z"; "add"; "leb"; "le"; "lt"; "ltb"; "of_nat"; "sub"; "to_nat"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@Stdlib.Lists.List"; "In"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zcell_covers (c : cell) (off : Z) : bool := ltac2:(tb__ "0|a|
S1S18Lx;M0SaVc;A1S15G0SbVc;A1S15S15S18Lz0;R1S1eS1eS32S29R2A1M1Voff;A2S35Voff;S31G1ScVc;A1M2A2A2A2S32G2Z8A2A2S16S1aLp;M3G3X15x3Lz0;S16S1aLi;M4S2bS1S1S1aLb;La;M5Lop;M6G6S2cG5Lop;M7G7S18S17S1S1aLa;Lw;Lsgn;M8S16S1S15S1aLk;Li;Ll;M9X1x8Lz;G4G6G6G7G7G8G9X1x8").

Fixpoint zcover_from (cells : list cell) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => existsb (fun c => zcell_covers c off) cells && zcover_from cells (off + 1) n'
  end.

Lemma zcover_from_spec : ltac2:(tb__ "0|0|
S1cS3A1S1fS15S15S26S18S2dR4R2R3A3S21A3S27S33R3R2A2S34R2S31R3S36R4A1A2A2A2S28S3S3S27S3eS3R1R7A3S26S18S2fR1R4A2S21A3A2Lc;A2F_;F_;Fx;Foff;Fn;Fcells;").
Proof.
  intros cells n. induction n as [|n IH]; intros off x H Hx; [lia|].
  cbn [zcover_from] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x off) as [->|Hne].
  - apply existsb_exists in H1 as (c & Hin & Hc). exists c. auto.
  - apply (IH (off + 1)); [exact H2 | lia].
Qed.

Definition zero_obj (o : sobj) : option sobj := ltac2:(tb__ "0|b|
S1S19S0A1M0Lx;M1S12Vo;A1S15G1S11Vo;A1S15S6G0Lx;S10Vo;A1S18G0L_;S2dSfVo;A1S29R2A1M2S38S37S29R1A1G2A2A1A3S1bS0SdSeVo;A1S4R2A1S4R1A1S25S3A1S9A5A2S1dS0A1M3X18x2G3G3S16G3Ll;M4G4S15S1S1cS20S15S15A2A1S1cS14A1G3Ltmpl;Lflds;Lcnt;Lesz;X6x6Lhi;S16G3Li;M5S2bS1S1G3Lb;La;M6Lop;M7G7S2cG6Lop;M8G8S18S17S1G3La;Lw;Lsgn;M9S16S1S15G3Lk;Li;Ll;MaX1x8Llo;G5G7G7G8G8G9GaX1x8").

Definition zero_obj_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|3|
S19S0A1S19S2A1Lx;M0S3fS0S13VS;A1M1Vi;A3S0G0S2eR1A1S0S1bS2S2aVS;S23S0S39S0Vi;G1A3S24S0R1S3aS0S22Vi;A1G1A3A3A3A2A2Lo';S1dS2A1M2X19x2Lo;G2X19x2").

Section Z0.
Variable segs : list Segment.

Lemma zero_obj_holds : ltac2:(tb__ "0|0|
S8S3bS0S0S26S19S0A1S2eR2A1S1bS0R1A2A3S5Vsegs;R5R4R3A4S5Vsegs;R6R5R3A4F_;F_;Fo';Fo;Fms;Frho;").
Proof using .
  intros rho ms o o' Hz Ho. unfold zero_obj in Hz.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  destruct (ob_dflt o) eqn:Ed; try discriminate.
  destruct (zcover_from (ob_cells o) (snorm lo) (Z.to_nat (snorm hi - snorm lo))) eqn:Hc; [|discriminate].
  injection Hz as <-.
  pose proof Ho as (Hb & Hw & Hcells & Hd & Hdl). unfold obj_lo_of, obj_hi_of in *.
  rewrite Elo, Ehi in *. rewrite !soff_lit in *.
  unfold obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi].
  rewrite !soff_lit. split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff | rewrite Ed; reflexivity]|].
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds].
  destruct (zcover_from_spec _ _ _ off Hc ltac:(lia)) as (c & Hin & Hzc).
  unfold zcell_covers in Hzc.
  destruct (c_off c) as [z| | | | | | |] eqn:Eco; try discriminate.
  destruct (c_val c) as [v| | | | | | |] eqn:Ecv; try discriminate.
  destruct v; try discriminate.
  apply andb_prop in Hzc as [Hzc H8]. apply andb_prop in Hzc as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H8.
  pose proof (obj_read_cell segs rho ms o c off 1 Ho Hin H8) as R.
  unfold soff in R. rewrite Eco in R. cbn [eval] in R. rewrite signed_lit in R.
  specialize (R H1 ltac:(lia) ltac:(lia)). rewrite Ecv in R. cbn [eval] in R.
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 in R by reflexivity. rewrite Z.shiftr_0_l in R.
  unfold oaddr in R. change (Z.to_nat 1) with 1%nat in R.
  assert (E1 : enc_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0]).
  { rewrite <- (enc_bytes_1_byte (Z_to_bv 8 0)). reflexivity. }
  rewrite E1 in R. cbn [rd_bytes] in R.
  destruct (rd ms (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))) as [b|] eqn:Hrd; [|discriminate].
  injection R as ->. reflexivity.
Qed.

Lemma smatch_zero_obj : ltac2:(tb__ "0|0|
S8S2S1fS2S20S1cS3dA1S3cA2S26S19S2A1S30R4R3A2S1bS2R2A2A3S7Vsegs;R6R5R2A4S7Vsegs;R7R4R3A4F_;F_;Fw;FS';Fi;FS;Frho;").
Proof using .
  intros rho S i S' [tr [ms md]] Hz Hsm.
  unfold zero_obj_at in Hz.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (zero_obj o) as [o'|] eqn:Ho; [|discriminate]. injection Hz as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (SHAPE : ob_base o' = ob_base o /\ ob_lo o' = ob_lo o /\ ob_hi o' = ob_hi o /\ ob_cells o' = []).
  { unfold zero_obj in Ho. destruct (ob_lo o); try discriminate. destruct (ob_hi o); try discriminate.
    destruct (ob_dflt o); try discriminate.
    destruct (zcover_from (ob_cells o) (snorm z) (Z.to_nat (snorm z0 - snorm z))); [|discriminate].
    injection Ho as <-. cbn. auto. }
  destruct SHAPE as (Sb & Slo & Shi & Sc).
  assert (RG : obj_range rho o' = obj_range rho o).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Sb, Slo, Shi. reflexivity. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S))
      with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |].
    pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _].
    cbn [forallb]. unfold obj_wf in W |- *. rewrite Sb, Slo, Shi, Sc.
    apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. rewrite W.

    unfold zero_obj in Ho. destruct (ob_lo o); try discriminate. destruct (ob_hi o); try discriminate.
    destruct (ob_dflt o); try discriminate.
    destruct (zcover_from _ _ _); [|discriminate]. injection Ho as <-. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S))
    with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [|constructor]. eapply zero_obj_holds; [exact Ho|].
    destruct Hmem as (Hall & _ & _). apply Forall_app in Hall as [_ Hall]. inversion Hall; auto.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite RG. exact Hpd.
  - intros x. rewrite <- RG. split.
    + intros Hx. exists o'. split; [cbn; auto | exact Hx].
    + intros (o1 & [<-|[]] & Hx). exact Hx.
Qed.

End Z0.
