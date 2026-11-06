(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "obj_holds"; "obj_wf"; "ss_objs"; "mkObj"; "sv"; "cell"; "smatch"; "sstate"; "DList"; "rom_ok"; "rl"; "soff"; "SLit"; "ob_base"; "ob_hi"; "ob_lo"; "ss_next"; "dflt_writable"; "eval"; "mkCell"; "ob_dflt"; "obj_range"; "tfact"; "DArr"; "DUnknown"; "TFle"; "enc_bytes"; "holds"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "pair"; "nil"; "option"; "cons"; "Some"; "nat"; "prod"; "S"; "None"; "app"; "false"; "length"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListCommit.LC"; "obj_upd"; "bare"; "commit_at"; "listed"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "of_nat"; "opp"; "pow"; "to_nat"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymMaterialize"; "materialized_bytes"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf"; "lget"; "lput"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundL SymSoundM SymCall SymObj SymMaterialize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import RingBuf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma soff_lit_small' : ltac2:(tb__ "0|1|
S1S23S21S3fS44S45Z2Z3fA2M0A1R1A2S40R1G0A2A2S20S23SdR3SeR2A1A2R2A3F_;Fz;Frho;").
Proof. intros rho z Hz. rewrite soff_lit. apply snorm_id'. exact Hz. Qed.

Section LC.
Variable segs : list Segment.

Definition obj_upd (S : sstate) (k : nat) (o' : sobj) : sstate := ltac2:(tb__ "0|1|
S4fVS;S32S0S47S0Vk;S4VS;A1M0A3S2cS0Vo';S48S0S30Vk;A1G0A3A3A3A2").

Lemma smatch_obj_upd : ltac2:(tb__ "0|1|
S1S9S2eS0S0S28S3aA1M0S35S39S20S2bS0A1S38S0S4R7A1R6A3S2dS0R5A2A3S8Vsegs;R9R8S29G0S36R4S37R3R2A2A4A4S20S26S3S12R9A1R6A2S27A3S20S2fS23S23A2S17RbR7A2S17RbR8A2A3SbVsegs;R6A2S20S26S3S12RcA1RaA2S27A3S2Vsegs;ReR8RbA4S2Vsegs;RfR9RbA4F_;F_;F_;S8Vsegs;RdS3bRcRbR9A3S29G0S36R8S37R7R6A2A4A4F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Fo';Fo;Fk;FS;Frho;").
Proof using .
  intros rho S k o o' tr ms md Hnth Hsm Hwf' Hrange Himp.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hnth) as EQ.
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  pose proof (Himp Hrom Hwfo Hoh) as Hoh'.
  unfold smatch, obj_upd. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn k (ss_objs S) ++ o' :: skipn (Datatypes.S k) (ss_objs S))
      with (firstn k (ss_objs S) ++ [o'] ++ skipn (Datatypes.S k) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |]. cbn [forallb]. rewrite Hwf'. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn k (ss_objs S) ++ o' :: skipn (Datatypes.S k) (ss_objs S))
    with (firstn k (ss_objs S) ++ [o'] ++ skipn (Datatypes.S k) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists o'. split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o1 & [<-|[]] & Hx). rewrite Hrange in Hx. exact Hx.
Qed.

Definition bare (o : sobj) : sobj := ltac2:(tb__ "0|0|
S5SfVo;A1S11Vo;A1S10Vo;A1S2aS7A1S1aA5").

Lemma obj_holds_bare : ltac2:(tb__ "0|0|
S1S35S0S24SbVsegs;R3A2S20S26S3R2R3A2S27A3S20S26S13S16R4A1A1S27A3S2Vsegs;R7R6R5A4S2Vsegs;R8R7S3cR6A1A4F_;F_;F_;F_;Fn;Fo;Fms;Frho;").
Proof using .
  intros rho ms o n Hrom Hwf Hw Ho. pose proof Ho as (Hb & Hwr & Hc & Hd & Hinv).
  unfold obj_holds, bare, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [intros off Hoff _; apply Hwr; [exact Hoff|exact Hw]|].
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds].
  exact (obj_byte_readable segs rho ms o off n Hrom Hwf Ho Hoff).
Qed.

Lemma bare_wf : ltac2:(tb__ "0|0|
S24S0S20S26S3R2R1A2S27A3S20S26S3R3S3cR2A1A2S27A3F_;Fo;Fn;").
Proof using .
  intros n o H. unfold obj_wf, bare in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb dflt_wf].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. rewrite H. reflexivity.
Qed.

Definition listed (o : sobj) (l : positive) : sobj := ltac2:(tb__ "0|0|
S5SfVo;A1S11Vo;A1S10Vo;A1S2aS7A1SaVl;A1A5").
Definition commit_at (S : sstate) (k : nat) (l : positive) : sstate := ltac2:(tb__ "0|0|
S2bS0A1S9Lx;S38S0S4VS;A1Vk;A3S0S3bVS;Vk;S3eR1Vl;A2A3Lo;VS;X2bx2").

Lemma objs_obj_upd : ltac2:(tb__ "0|6|
S9S2eS0S0S20S2bS0A1M0S38S0S4R4A1R3A3S2dS0R2A2M1A3S21S20S28S0A1M2S47S0R4S4S3bR5R4R2A3A1M3A3S47S0R4S4R5A1M4A3A3S21S20G2S48S0S30R4A1M5G3A3S48S0G5G4A3A3S20G0S38S0G3R4A3G1A3A2A2F_;Fo';Fo;Fk;FS;").
Proof using .
  intros S k o o' H. unfold obj_upd. cbn [ss_objs set_objs].
  pose proof (nth_error_split3 _ _ _ H) as EQ.
  assert (Hk : length (firstn k (ss_objs S)) = k).
  { rewrite length_firstn. pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite H; discriminate)). lia. }
  split; [|split].
  - rewrite firstn_app, Hk, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. rewrite firstn_firstn. f_equal. lia.
  - rewrite skipn_app, Hk. replace (Datatypes.S k - k)%nat with 1%nat by lia. cbn [skipn].
    rewrite skipn_all2 by lia. reflexivity.
  - rewrite nth_error_app2 by lia. rewrite Hk, Nat.sub_diag. reflexivity.
Qed.

Theorem smatch_commit : ltac2:(tb__ "0|1|
S1S9S2eS0S24S28S3aA1M0S35S39S20S2bS0A1S38S0S4R7A1R6A3S2dS0R5A2A3S20S26S13S16R6A1A1S27A3S20S26S4bR6S3bR9R8S3cR7A1A3A2S33A3S8Vsegs;RbRaS29G0S36R6S37R5R4A2A4A4S8Vsegs;S4aRcR8S4cRcR6SfR9A1S11R9A1S10R9A1A5A3S3dRbRaR8A3S29G0S36R7S37R6R5A2A4A4F_;F_;F_;F_;Fmd;Fms;Ftr;Fl;Fo;Fk;FS;Frho;").
Proof using .
  intros rho S k o l tr ms md Hnth Hw Hno Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite (nth_error_split3 _ _ _ Hnth), forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (Hsm1 : smatch segs rho (obj_upd S k (bare o)) (tr, mkCfg ms md)).
  { eapply smatch_obj_upd; [exact Hnth | exact Hsm | apply bare_wf; exact Hwfo | reflexivity |].
    intros Hrom _ Ho. eapply obj_holds_bare; eauto. }
  destruct (objs_obj_upd S k o (bare o) Hnth) as (F1 & F2 & N1).
  assert (Hmat : materialize_at (obj_upd S k (bare o)) k l = Some (commit_at S k l)).
  { unfold commit_at. rewrite Hnth. unfold materialize_at. rewrite N1.
    cbv delta [bare] in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *. cbv beta iota. rewrite Hno.
    rewrite F1, F2. reflexivity. }
  exact (smatch_materialize segs rho (obj_upd S k (bare o)) k l (commit_at S k l) tr ms md
           (ob_base o) (ob_lo o) (ob_hi o) [] Hmat N1 Hsm1).
Qed.

Lemma commit_bytes1 : ltac2:(tb__ "0|8|
S1S35S6S6S6S6S24S24SbVsegs;R7A2S20S26S3R2S5R7SeZ0M0A1M1R6S2cS7S15R5Z4M2R4A3S2aS7A1M3A3SaR3A1A5A2S27A3S2Vsegs;RaR9S5R8G1R7S2cS7S15R6G2R5A3G3A3SaR4A1A5A4S21S20S28S4dQ8A1M4A1S4cRbRaR9G1R8A5S51ScRbR5A2M5S46SdRbR7A2M6A1S1cU4S14RbR6A2A2A3A3S21S3fG0G6A2S21S3fS41G6G2A2SdRbR8A2M7A2S20S23S43S34G4G5A2A1G7A3A2A2A2F_;F_;F_;Fn;Fl;Fev;Foff;Fhi;Fb;Fms;Frho;").
Proof using .
  intros rho ms b hi off ev l n Hrom Hwf Ho.
  pose proof Ho as (Hb & Hwr & Hc & Hd & Hinv).
  unfold obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  rewrite !soff_lit_small' in * by lia.
  apply Forall_cons_iff in Hc as [Hcell _]. destruct Hcell as (C1 & C2 & C3). cbn [c_off c_width c_val] in *.
  cbn [dflt_inv] in Hinv.
  assert (LEN : Z.of_nat (length (rl rho l)) = soff rho hi) by lia.
  split; [|lia].
  apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - pose proof (materialized_bytes_length rho ms b (SLit 0) hi) as L1. rewrite soff_lit_small' in L1 by lia.
    rewrite lput_length by (rewrite enc_bytes_length; lia). lia.
  - intros j Hj. pose proof (materialized_bytes_length rho ms b (SLit 0) hi) as L1. rewrite soff_lit_small' in L1 by lia.
    destruct (Z.lt_ge_cases (Z.of_nat j) (soff rho off)) as [Hlt|Hge];
      [|destruct (Z.lt_ge_cases (Z.of_nat j) (soff rho off + 4)) as [Hin|Hout]].
    +
      rewrite lput_nth_out by (rewrite ?enc_bytes_length; lia).
      assert (NC : ~ covered rho [mkCell off 4 ev] (Z.of_nat j)).
      { intros HC. apply Exists_cons in HC as [HC|HC]; [|inversion HC]. unfold in_cell in HC. cbn in HC. lia. }
      specialize (Hd (Z.of_nat j) ltac:(lia) NC). cbn [dflt_holds] in Hd.
      replace (Z.to_nat (Z.of_nat j - 0)) with j in Hd by lia.
      replace j with (Z.to_nat (Z.of_nat j - soff rho (SLit 0))) at 1 by (rewrite soff_lit_small' by lia; lia).
      apply materialized_bytes_nth; [rewrite !soff_lit_small' by lia; lia | exact Hd].
    +
      rewrite lput_nth_in by (rewrite ?enc_bytes_length; lia).
      pose proof (rd_bytes_nth ms _ _ _ (j - Z.to_nat (soff rho off)) C3 ltac:(lia)) as R.
      rewrite oaddr_unsigned in R by lia. specialize (R ltac:(lia)).
      replace (bv_unsigned (eval rho b) + soff rho off + Z.of_nat (j - Z.to_nat (soff rho off))) with (bv_unsigned (eval rho b) + Z.of_nat j) in R by lia.
      replace j with (Z.to_nat (Z.of_nat j - soff rho (SLit 0))) at 1 by (rewrite soff_lit_small' by lia; lia).
      apply materialized_bytes_nth; [rewrite !soff_lit_small' by lia; lia | exact R].
    +
      rewrite lput_nth_out by (rewrite ?enc_bytes_length; lia).
      assert (NC : ~ covered rho [mkCell off 4 ev] (Z.of_nat j)).
      { intros HC. apply Exists_cons in HC as [HC|HC]; [|inversion HC]. unfold in_cell in HC. cbn in HC. lia. }
      specialize (Hd (Z.of_nat j) ltac:(lia) NC). cbn [dflt_holds] in Hd.
      replace (Z.to_nat (Z.of_nat j - 0)) with j in Hd by lia.
      replace j with (Z.to_nat (Z.of_nat j - soff rho (SLit 0))) at 1 by (rewrite soff_lit_small' by lia; lia).
      apply materialized_bytes_nth; [rewrite !soff_lit_small' by lia; lia | exact Hd].
Qed.

Lemma obj_holds_list_arr : ltac2:(tb__ "0|5|
S1S35S6S6S24S6S23S24SbVsegs;R7A2S20S26S3R2S5R7SeZ0M0A1M1R6S2aS7A1M2SaR5A1A5A2S27A3S2Vsegs;RaR9S5R8G1R7G2SaR6A1A5A4S20S23SdRbR8A2S42Z4M3R5A2A3S20S23S4eQ40S14RcR7A2A2R6A3S23S21S3fG0R1A2S40R1R8A2A2S40S50ScRfRbA2R2A2R9A2F_;Fi;S2Vsegs;ReRdS5RcG1RbG2S19G3R9S2cS2fS23S23A2M4S29S23S23G0G3A4S2aG4A1A3S2cS18S1bS27U0S31S2fS26S25A2A1R9A4S2aS18A1A3A4A5A4F_;F_;F_;F_;F_;F_;Fk;Fn;Fvn;Fl;Fhi;Fb;Fms;Frho;").
Proof using .
  intros rho ms b hi l vn n k Hrom Hwf Ho Hhi Hvn Hall.
  pose proof Ho as (Hb & Hwr & Hc & Hd & Hinv).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  rewrite !soff_lit_small' in * by lia. cbn [dflt_inv] in Hinv.
  split; [exact Hb|]. split; [intros off Hoff _; apply Hwr; [exact Hoff|reflexivity]|].
  split; [constructor|]. split.
  - intros off Hoff NC. cbn [dflt_holds]. specialize (Hd off Hoff NC). cbn [dflt_holds] in Hd. rewrite Hd. eexists; reflexivity.
  - cbn [dflt_inv]. split; [lia|]. split.
    { constructor; [|constructor]. unfold fld_ok. cbn. lia. }
    rewrite Hvn. split; [lia|].
    intros i Hi. unfold elem_holds.
    exists [Z_to_bv 64 (lget (rl rho l) i)]. split; [reflexivity|]. split.
    + intros f fl Hf. destruct f as [|f]; [|destruct f; discriminate]. cbn in Hf. injection Hf as <-. cbn [fst snd fldv nth].
      pose proof (lget_range (rl rho l) i) as LR.
      rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (change (bv_modulus 64%N) with (2 ^ 64); lia).
      split; [|change (2 ^ (8 * 4)) with (2 ^ 32); lia].
      pose proof (obj_read_list segs rho ms (mkObj b (SLit 0) hi [] (DList l)) (4 * i) 4 l Ho eq_refl) as R.
      unfold obj_lo_of, obj_hi_of in R. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in R. rewrite !soff_lit_small' in R by lia.
      specialize (R ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros j _ HC; inversion HC)).
      unfold oaddr in R. replace (bv_unsigned (eval rho b) + 4 * i) with (bv_unsigned (eval rho b) + 0 + 4 * i + 0) in R by lia.
      rewrite R. f_equal. rewrite Z.sub_0_r. change (Z.to_nat 4) with 4%nat.
      unfold enc_bytes. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64%N) with (2 ^ 64); lia).
      apply sublist_lget; lia.
    + constructor; [|constructor]. cbn [tf_holds extv fldv nth zrel].
      rewrite Z_to_bv_unsigned, bv_wrap_small by (pose proof (lget_range (rl rho l) i); change (bv_modulus 64%N) with (2 ^ 64); lia).
      rewrite Hvn. apply Hall. lia.
Qed.

Lemma smatch_nth_obj : ltac2:(tb__ "0|1|
S1S9S2eS0S28S3aA1M0S35S39S8Vsegs;R7R6S29G0S36R3S37R2R1A2A4A4S20S2bS0A1S38S0S4R7A1R6A3S2dS0R5A2A3S21S2Vsegs;R9R4R6A4S21S20S26S3S12R8A1R6A2S27A3SbVsegs;R4A2A2A2F_;F_;Fmd;Fms;Ftr;Fo;Fk;FS;Frho;").
Proof using .
  intros rho S k o tr ms md Hsm Hnth.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hnth) as EQ.
  split; [|split; [|exact Hrom]].
  - destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto.
  - pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W.
Qed.

Lemma smatch_facts : ltac2:(tb__ "0|1|
S1S9S28S3aA1M0S35S39S8Vsegs;R5R4S29G0S36R3S37R2R1A2A4A4S49S1eS1dR6A1S1fR5A1A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md Hsm. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). Qed.

Lemma rho_set_rl2_other : ltac2:(tb__ "0|1|
S1S24S28S4dQ8A1A1M0S24G0S24S22S20S24R1R5A3A1S22S20S24R2R4A3A1S20G0ScS4aS4aR8R7R6A3R5R4A3R3A2ScR8R3A2A3F_;F_;Fl;Fb2;Fl2;Fb1;Fl1;Frho;").
Proof using . intros. rewrite !rho_set_rl_other by assumption. reflexivity. Qed.

End LC.
