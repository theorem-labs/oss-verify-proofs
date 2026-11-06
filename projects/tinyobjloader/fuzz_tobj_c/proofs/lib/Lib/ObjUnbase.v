(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sstate"; "cell"; "ob_base"; "ob_dflt"; "ss_facts"; "eval"; "ob_cells"; "obj_hi_of"; "obj_lo_of"; "smatch"; "sprop"; "ss_next"; "ss_objs"; "valuation"; "DUnknown"; "c_off"; "dflt_writable"; "holds"; "is_arr"; "mkObj"; "ob_hi"; "ob_lo"; "obj_wf"; "odefault"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "le"; "leb"; "pow"; "lt"; "ltb"; "@Corelib.Init.Datatypes"; "option"; "bool"; "Some"; "true"; "andb"; "list"; "prod"; "nat"; "None"; "S"; "app"; "cons"; "nil"; "false"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "shift_ok"; "shift_off"; "shift_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "unbase_obj"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "itv"; "mk_addk"; "set_objs"; "snorm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.U"; "reshape_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymEntail SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition unbase_obj (facts : list sprop) (o : sobj) (c0 : Z) : option sobj := ltac2:(tb__ "0|7|
S47Vc0;A1S1bS2aS1bS1bA2S24S0A1M0Lx;S44Vfacts;S3Vo;A1M1A2S1bS1bS25G0L_;S28S28S28S28S28S28S20R2R1A2S20Z0S1dR2R3A2A2A2S23S1dR1R3A2S21Z2Z40A2A2A2S33Vfacts;S16Vo;A1M2S1eR3A1M3A3A2S33Vfacts;S15Vo;A1M4G3A3A2S3cS2S2S33Vfacts;S10R1A1S1eR4A1A3Lcl;S7Vo;A1M5A3A2S32S13S4Vo;A1M6A1A1A2S26S0S14S45G1Vc0;A2S34G2G3A2S34G4G3A2S3fS2S2S35G3A1G5A4G6A5A2S2cS0A1X25x2Lh;Ll;X2ax1Tc;").

Definition unbase_obj_at (S : sstate) (i : nat) (c0 : Z) : option sstate := ltac2:(tb__ "0|3|
S24S0A1S24S1A1Lx;M0S3bS0SdVS;A1M1Vi;A3S0G0S3aS5VS;A1R1Vc0;A3S0S26S1S46VS;S2eS0S3eS0Vi;G1A3S2fS0R1S40S0S2dVi;A1G1A3A3A3A2A2Lo';S2cS1A1M2X24x2Lo;G2X24x2").

Lemma unbase_obj_shape : ltac2:(tb__ "0|5|
S29SbA1S0S1bS0S19S24S0A1S3aR4R3R2A3S26S0R1A2A3S47R3A1S1bS2aS1bS1bA2OLx;S44R6S3R5A1A2S1bS1bS1aS1fR2R1A2S1aS1fZ0S1dR2R3A2A2S1aS22S1dR1R3A2S21Z2Z40A2A2S1aS19S25S33R8S16R7A1M0S1eR3A1M1A3S27A3S1aS19S25S33R8S15R7A1M2G1A3S27A3S1aS19S25S3cS2S2S33R9S10R1A1S1eR4A1A3Lcl;S7R7A1M3A3S27A3S1aS19S25S13S4R7A1M4A1S31A3S19S0R5S14S45S3R7A1R6A2S34G0G1A2S34G2G1A2S3fS2S2S35G1A1G3A4G4A5A3A2A2A2A2A2A2A2Lh;Ll;X2ax1Tc;F_;Fo';Fc0;Fo;Ffacts;").
Proof.
  intros facts o c0 o' H. unfold unbase_obj in H. cbn zeta.
  destruct (itv facts (ob_base o)) as [l h].
  destruct (Z.leb_spec l h); [|discriminate].
  destruct (Z.leb_spec 0 (l + snorm c0)); [|discriminate].
  destruct (Z.ltb_spec (h + snorm c0) (2 ^ 64)); [|discriminate]. cbn [andb] in H.
  destruct (shift_ok facts (ob_lo o) (- snorm c0)); [|discriminate].
  destruct (shift_ok facts (ob_hi o) (- snorm c0)); [|discriminate].
  destruct (forallb (fun cl => shift_ok facts (c_off cl) (- snorm c0)) (ob_cells o)); [|discriminate].
  destruct (is_arr (ob_dflt o)); [discriminate|].
  cbn [andb negb] in H. injection H as <-. repeat split; auto.
Qed.

Section U.
Variable segs : list Segment.

Theorem smatch_unbase : ltac2:(tb__ "0|0|
SeS1S2bS1bS1S2aS29S42A1S41A2S19S24S1A1S39R5R4R3A3S26S1R2A2A3SaVsegs;R7R6R2A4SaVsegs;R8R4R3A4F_;F_;Fw;FS';Fc0;Fi;FS;Frho;").
Proof using .
  intros rho S i c0 S' [tr [ms md]] Hrb Hsm.
  unfold unbase_obj_at in Hrb.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (unbase_obj (ss_facts S) o c0) as [o'|] eqn:Ho; [|discriminate]. injection Hrb as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  pose proof (unbase_obj_shape _ _ _ _ Ho) as Hsh.
  cbn zeta in Hsh. destruct (itv (ss_facts S) (ob_base o)) as [l h] eqn:Hitv.
  destruct Hsh as (Hlh & Hl & Hh & Slo & Shi & Scells & NA & Eo').
  set (c := snorm c0) in *.
  assert (Hb : bv_unsigned (eval rho (ob_base o')) = bv_unsigned (eval rho (ob_base o)) + c).
  { rewrite Eo'. cbn [ob_base]. rewrite mk_addk_sound.
    replace (bv_unsigned (eval rho (ob_base o) + Z_to_bv 64 c0)%bv) with (bv_unsigned (eval rho (SAlu ALU_ADD (ob_base o) (SLit c0))))
      by reflexivity.
    apply (rebase_base_val rho (ss_facts S) (ob_base o) c0 Hfacts). rewrite Hitv. repeat split; assumption. }
  pose proof (shift_ok_sound rho _ _ _ Hfacts Slo) as Elo.
  pose proof (shift_ok_sound rho _ _ _ Hfacts Shi) as Ehi.
  assert (Ecells : forall cl, In cl (ob_cells o) -> soff rho (shift_off (c_off cl) (- c)) = soff rho (c_off cl) + - c).
  { intros cl Hcl. apply (shift_ok_sound rho (ss_facts S)); [exact Hfacts|].
    exact (proj1 (forallb_forall _ _) Scells cl Hcl). }
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb. rewrite Eo'. cbn [ob_base ob_lo ob_hi]. rewrite Elo, Ehi. f_equal; lia. }
  assert (Hwfo' : obj_wf (ss_next S) o' = true).
  { rewrite Eo'. unfold obj_wf in Hwfo |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    repeat (apply andb_prop in Hwfo; destruct Hwfo as [Hwfo ?]).
    rewrite (mk_addk_below _ _ _ Hwfo), (shift_off_below _ _ _ H2), (shift_off_below _ _ _ H1), H, Bool.andb_true_r. cbn [andb].
    apply forallb_forall. intros cl' Hin'. apply in_map_iff in Hin' as (cl & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) H0 cl Hin) as W. unfold cell_wf in W |- *. cbn [c_off c_width c_val shift_cell].
    repeat (apply andb_prop in W; destruct W as [W ?]).
    match goal with
    | Hw : (0 <? _) = true, Hw8 : (_ <=? 8) = true, Ho : sv_below _ (c_off cl) = true, Hv : sv_below _ (c_val cl) = true |- _ =>
        rewrite Hw, Hw8, Hv, (shift_off_below _ _ _ Ho); reflexivity
    end. }
  assert (Hoh' : obj_holds segs rho ms o').
  { apply (obj_holds_transfer segs rho rho ms o o' (ss_next S) Hrom Hwfo).
    - unfold obj_lo_of. rewrite Hb. rewrite Eo'. cbn [ob_base ob_lo]. rewrite Elo. lia.
    - unfold obj_hi_of. rewrite Hb. rewrite Eo'. cbn [ob_base ob_hi]. rewrite Ehi. lia.
    - reflexivity.
    - intros c2 Hin2. rewrite Eo' in Hin2. cbn [ob_cells] in Hin2. apply in_map_iff in Hin2 as (c1 & <- & Hin1).
      exists c1. split; [exact Hin1|]. rewrite Hb. unfold cell_abs, shift_cell. cbn [c_off c_width c_val].
      rewrite (Ecells c1 Hin1). f_equal. f_equal. lia.
    - right. left. split; [rewrite Eo'; reflexivity|]. split; [exact NA|]. intros c1 Hin1. exists (shift_cell (- c) c1).
      split; [rewrite Eo'; cbn [ob_cells]; apply in_map; exact Hin1|].
      rewrite Hb. unfold cell_abs, shift_cell. cbn [c_off c_width c_val].
      rewrite (Ecells c1 Hin1). f_equal. f_equal. lia.
    - exact Hoh. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |]. cbn. rewrite Hwfo'. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists o'. split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite Hrange in Hx. exact Hx.
Qed.

Lemma SPJ_unbase : ltac2:(tb__ "0|0|
S37SeS1S2bS1bS1S43S19S24S1A1S39R5R4R3A3S26S1R2A2A3S36Vsegs;R8R6R7R2A5S36Vsegs;R9R4R8R3A5F_;F_;Fw;FS';Fc0;Fi;FS;Frho;FJ;").
Proof using . intros J rho S i c0 S' w H [Hsm Hk]. split; [eapply smatch_unbase; eauto | exact Hk]. Qed.

Lemma unbase_facts : ltac2:(tb__ "0|0|
S1S2bS1bS1S19S24S1A1S39R4R3R2A3S26S1R1A2A3S1aS19S29SbA1S5R2A1S5R5A1A3S19S1cScR2A1ScR5A1A3A2F_;FS';Fc0;Fi;FS;").
Proof using .
  intros S i c0 S' H. unfold unbase_obj_at in H.
  destruct (nth_error (ss_objs S) i); [|discriminate]. destruct (unbase_obj _ _ _); [|discriminate].
  injection H as <-. split; reflexivity.
Qed.

Definition reshape_obj_at (S : sstate) (i : nat) (o' : sobj) : sstate := ltac2:(tb__ "0|1|
S46VS;S2eS0S3eS0Vi;SdVS;A1M0A3S2fS0Vo';S40S0S2dVi;A1G0A3A3A3A2").

Theorem smatch_reshape : ltac2:(tb__ "0|3|
SeS1S2bS0S0S2aS29S42A1S41A2S19S24S0A1S3bS0SdR5A1R4A3S26S0R3A2A3S19S29S2A1S7R3A1S30S2A1A3S19S18S4R4A1SfA3S19S25S11S4R6A1A1S27A3S19S25S17ScR9A1R6A2S27A3S3dSbS12RbA1S5RaA1A3S1aS19S1bS1dS38Q40M0S6RcS3R8A1A2A2M1S9RcR8A2A2S1dS38G0S6RcS3R9A1A2A2M2S9RcR9A2A2A3S19S1bS1dG1S8RcR8A2A2S1dG2S8RcR9A2A2A3A2F_;SaVsegs;RcRbR7A4SaVsegs;RdS48RcRbR9A3R8A4F_;F_;F_;F_;F_;F_;F_;Fw;Fo';Fo;Fi;FS;Frho;").
Proof using .
  intros rho S i o o' [tr [ms md]] Hn Hc' Hd' Hdw Hwfo' Hrng Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct (Hrng Hfacts) as [Elo Ehi].
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { unfold obj_range. rewrite Elo, Ehi. reflexivity. }
  assert (Hoh' : obj_holds segs rho ms o').
  { apply (obj_holds_transfer segs rho rho ms o o' (ss_next S) Hrom Hwfo).
    - symmetry. exact Elo.
    - symmetry. exact Ehi.
    - reflexivity.
    - intros c2 Hin2. rewrite Hc' in Hin2. destruct Hin2.
    - left. split; [exact Hd' | exact Hdw].
    - exact Hoh. }
  unfold smatch, reshape_obj_at. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |]. cbn. rewrite Hwfo'. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists o'. split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite Hrange in Hx. exact Hx.
Qed.

Lemma SPJ_reshape : ltac2:(tb__ "0|3|
S37SeS1S2bS0S0S43S19S24S0A1S3bS0SdR5A1R4A3S26S0R3A2A3S19S29S2A1S7R3A1S30S2A1A3S19S18S4R4A1SfA3S19S25S11S4R6A1A1S27A3S19S25S17ScR9A1R6A2S27A3S3dSbS12RbA1S5RaA1A3S1aS19S1bS1dS38Q40M0S6RcS3R8A1A2A2M1S9RcR8A2A2S1dS38G0S6RcS3R9A1A2A2M2S9RcR9A2A2A3S19S1bS1dG1S8RcR8A2A2S1dG2S8RcR9A2A2A3A2F_;S36Vsegs;RdRbRcR7A5S36Vsegs;ReS48RcRbR9A3RdR8A5F_;F_;F_;F_;F_;F_;F_;Fw;Fo';Fo;Fi;FS;Frho;FJ;").
Proof using . intros J rho S i o o' w H1 H2 H3 H4 H5 H6 [Hsm Hk]. split; [eapply smatch_reshape; eauto | exact Hk]. Qed.
End U.
