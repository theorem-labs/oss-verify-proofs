(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sstate"; "sv"; "valuation"; "obj_range"; "odefault"; "ss_next"; "ob_hi"; "ob_lo"; "obj_holds"; "cell"; "ob_dflt"; "smatch"; "ss_facts"; "ss_objs"; "SLit"; "mkObj"; "ob_base"; "ob_cells"; "obj_wf"; "sprop"; "tfact"; "DArr"; "obj_hi_of"; "obj_lo_of"; "sv_eqb"; "DUnknown"; "SMd"; "agree_below"; "holds"; "soff"; "sv_below"; "@Corelib.Init.Datatypes"; "option"; "prod"; "list"; "Some"; "bool"; "nat"; "true"; "false"; "fst"; "pair"; "snd"; "None"; "andb"; "S"; "app"; "cons"; "nil"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "obj_ext"; "exts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "skipn"; "Forall"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "sub"; "add"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA"; "arr_merge_obj"; "arr_cnt_bytes"; "arr_merge_at"; "arr_split_at"; "arr_split_obj"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "in_bounds"; "set_objs"; "sitv"; "uleq"; "same_atoms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArrMat"; "arr_mat_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile"; "tile_at"; "tiles_at"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue CellTile ArrMat.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition arr_split_obj (o : sobj) (mid : sv) : option (sobj * sobj) := ltac2:(tb__ "0|8|
S7S22S23S2S2A2M0A1M1Lx;SdVo;A1S2dG0A1M2G2G2S1G2Ll;M3G3S0S4S24S23S0S0A2A1S24S17A1S24ScA1M4G1Lx;S14Vo;A1S26G1L_;S1bSaVo;A1S11Z0A1M5A2S25G0S2bS2S2S12S13Vo;A1M6G5Vmid;S32ScA1M7S18R4R3R2R1A4A5S12G6Vmid;S9Vo;A1G7S1cA5A4A2G2X26x2ScG4G2Ll;Lc;X24x2Ltmpl;Lflds;Lcnt;Lesz;X7x6").

Definition arr_cnt_bytes (o : sobj) : sv := ltac2:(tb__ "0|2|
S7S4Lx;SdVo;A1S11Z0A1M0G0G0S1G0Ll;M1G1S0S4S24S23S0S0A2A1S24S17A1S1dS5cS11R4A1R3A3Ltmpl;Lflds;Lcnt;Lesz;X7x6").

Definition arr_split_at (S : sstate) (i : nat) (mid : sv) : option sstate := ltac2:(tb__ "0|6|
S22S2A1S22S3A1M0Lx;S4fS2S10VS;A1M1Vi;A3S2S26G0L_;S2eS2eS21S8VS;A1Vmid;A2S54SfVS;A1M2SaR1A1S9R1A1Vmid;Z0M3A5A2S57G2S4bR1A1G3Vmid;A4A2S22S23S2S2A2M4A1G0Lx;S4eR1Vmid;A2G4G4G0Lp;R1S2S2S25S3S55VS;S30S2S41S2Vi;G1A3S31S2R2S31S2R1S42S2S2fVi;A1G1A3A3A3A3A2A2Lo2;Lo1;X23x1Lp;S2dS3A1M5X22x2G5X26x2Lo;G5X22x2").

Definition arr_merge_obj (o1 o2 : sobj) : option sobj := ltac2:(tb__ "0|8|
S7S22S2A1M0Lx;SdVo1;A1S2dS2A1M1G1G1S1G1Ll;M2G2S0S4S24S23S0S0A2A1M3S24S17A1M4S26G0L_;S2eS2eS1bS13Vo1;A1M5S13Vo2;A1A2S22S0A1S26Lx;S58S9Vo1;A1SaVo2;A1A2S0S0S26Lz;R1S28S1S29Lp;M6G6X0x3Lz;S29X22x2A2S7S26Lx;SdVo2;A1S28S28S29S1S29Ll;M7G7S0S4G3G4S29Ltmpl0;Lflds0;Lcnt0;Lesz0;X7x6A2S25S2S12G5SaVo1;A1S9Vo2;A1S30ScS14Vo1;A1S14Vo2;A1A3S18R4R3R2R1A4A5A2G1X26x2Ltmpl;Lflds;Lcnt;Lesz;X7x6").

Definition arr_merge_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|8|
S22S2A1S22S3A1M0Lx;M1S4fS2S10VS;A1M2Vi;A3S2G1S4fS2G2S2fVi;A1M3A3S2S22S23S0S0A2M4A1G0Lx;M5S56SfVS;A1M6SaR2A1A2G4G4G0Lp;R1S0S0G5S56G6S9R4A1A2G4G4G0Lp0;R1S0S0S26G0L_;S49S47R1R5A2S46Z2Z3fA2A2G1S4aR8R7A2S2S25S3S55VS;S30S2S41S2Vi;G2A3S31S2R1S42S2S2fG3A1G2A3A3A3A2A2Lo;S2dS3A1M7X22x2G7X26x2Lh2;Lz0;X23x1Lp0;G7X22x2Lz;Ll1;X23x1Lp;G7X22x2Lo2;G7X22x2Lo1;G7X22x2").

Section WithSegs.
Variable segs : list Segment.

Lemma arr_split_holds : ltac2:(tb__ "0|7|
S5S51S2S4S2S2S24S16A1S43S16S1fR7A1R1A3S33S26S54R2SaR6A1S9R6A1R5Z0M0A5S28A3S33S26S57R3S4bR7A1G0R6A4S28A3S33S22S23S2S2A2M1A1S4eR8R7A2S25G1S2bS2S2R6R5A4A2A3SbVsegs;RbRaR9A4S34SbVsegs;RcRbR8A4S34SbVsegs;RcRbR7A4S34S33S23S0S0A2M2S6RcR8A2S2bS0S0S2aS0S0S6RcRaA2M3A3M4S48G4S20RcR9A2M5A2M6A4A3S34S33G2S6RcR7A2S2bS0S0G6S2cS0S0G3A3A4A3S34S34S44G0G5A2S44G5S19RcRaA2A2A2S33S0S1aRcRaA2G0A3A2A2A2A2A2F_;F_;F_;F_;F_;Ffacts;Fo2;Fo1;Fmid;Fo;Fms;Frho;").
Proof using .
  intros rho ms o mid o1 o2 facts HF Hib Hul Hsp Ho.
  unfold arr_split_obj in Hsp.
  destruct (ob_dflt o) as [| | | | |esz cnt flds tmpl] eqn:Hd; try discriminate.
  destruct (ob_cells o) eqn:Hc; try discriminate.
  destruct (sv_eqb (ob_lo o) (SLit 0)) eqn:Hlo; [|discriminate]. apply sv_eqb_sound in Hlo. injection Hsp as <- <-.
  pose proof (in_bounds_sound rho facts (ob_lo o) (ob_hi o) mid 0 HF ltac:(lia) Hib) as [M1 M2].
  rewrite Hlo in M1. rewrite soff_lit_small in M1 by lia.
  pose proof (uleq_sound rho facts _ 0 mid HF Hul) as UL. unfold arr_cnt_bytes in UL. rewrite Hd in UL.
  destruct Ho as (Hrng & Hwr & Hcells & Hdf & Hinv).
  unfold obj_lo_of, obj_hi_of in *. rewrite Hlo in *. rewrite soff_lit_small in Hrng, Hwr, Hdf, Hinv |- * by lia.
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  set (hi := soff rho (ob_hi o)) in *. set (m := soff rho mid) in *.
  rewrite Hd in Hinv. cbn [dflt_inv] in Hinv. destruct Hinv as (Hesz & Hflds & Hfit & Helems).

  assert (FIT : esz * bv_unsigned (eval rho cnt) <= m).
  { pose proof (urange (eval rho cnt)) as Rc.
    destruct (Z.eq_dec (bv_unsigned (eval rho cnt)) 0) as [E0|NE]; [rewrite E0; lia|].
    assert (P63 : esz * bv_unsigned (eval rho cnt) < 2 ^ 63) by lia.
    assert (Eesz : esz < 2 ^ 63) by nia.
    unfold U in UL. rewrite U_mul, U_lit in UL. unfold M64v in UL.
    rewrite (Z.mod_small esz) in UL by lia. rewrite Z.mod_small in UL by lia.
    assert (Em : m = bv_unsigned (eval rho mid)).
    { subst m. unfold soff. rewrite bv_signed_U. pose proof (urange (eval rho mid)) as Rm.
      destruct (Zsigned_spec (bv_unsigned (eval rho mid))) as [[_ X]|[X1 X]]; rewrite X; [reflexivity|].
      exfalso. unfold soff in M1, M2. rewrite bv_signed_U, X in M1. lia. }
    rewrite Em. lia. }
  assert (DF : forall off, 0 <= off < hi -> exists bb, rd ms (Z_to_bv 64 (b + off)) = Some bb).
  { intros off Hoff. specialize (Hdf off Hoff). rewrite Hc, Hd in Hdf. cbn [dflt_holds] in Hdf. apply Hdf. intros X. inversion X. }
  assert (WR : forall off, 0 <= off < hi -> wview segs (ms_mem ms) (Z_to_bv 64 (b + off)) <> None).
  { intros off Hoff. apply Hwr; [exact Hoff|]. rewrite Hd. reflexivity. }
  split; [|split; [|split; [|split]]].
  -
    unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite soff_lit_small by lia. fold b. fold m.
    split; [lia|]. split; [intros off Hoff _; apply WR; lia|]. split; [constructor|].
    split; [intros off Hoff _; cbn [dflt_holds]; apply DF; lia|].
    cbn [dflt_inv]. split; [exact Hesz|]. split; [exact Hflds|]. split; [lia|]. exact Helems.
  -
    unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b. fold m. fold hi.
    split; [lia|]. split; [intros off Hoff _; apply WR; lia|]. split; [constructor|].
    split; [intros off Hoff _; cbn [dflt_holds]; apply DF; lia|]. exact I.
  - unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Hlo. rewrite soff_lit_small by lia. fold b. cbn [fst snd]. f_equal; lia.
  - unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Hlo. rewrite soff_lit_small by lia. cbn [fst snd]. f_equal; lia.
  - lia.
Qed.

Theorem smatch_arr_split : ltac2:(tb__ "0|0|
S5S3S27S4S3S23S24S53A1S52A2S33S22S3A1S4dR5R4R3A3S25S3R2A2A3SeVsegs;R7R6R2A4SeVsegs;R8R4R3A4F_;F_;Fw;FS';Fmid;Fi;FS;Frho;").
Proof using .
  intros rho S i mid S' [tr [ms md]] Hsp Hsm.
  unfold arr_split_at in Hsp.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (sv_below (ss_next S) mid && in_bounds (ss_facts S) (ob_lo o) (ob_hi o) mid 0 && uleq (ss_facts S) (arr_cnt_bytes o) 0 mid)%bool eqn:Hck; [|discriminate].
  apply andb_prop in Hck as [Hck Hul]. apply andb_prop in Hck as [Hb Hib].
  destruct (arr_split_obj o mid) as [[o1 o2]|] eqn:Ho; [|discriminate]. injection Hsp as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  destruct (arr_split_holds rho ms o mid o1 o2 (ss_facts S) Hfacts Hib Hul Ho Hoh) as (H1 & H2 & R1 & R2 & Hm & Hlo0).
  assert (SH : exists esz cnt flds tmpl, ob_dflt o = DArr esz cnt flds tmpl /\ ob_cells o = []
            /\ o1 = mkObj (ob_base o) (SLit 0) mid [] (DArr esz cnt flds tmpl) /\ o2 = mkObj (ob_base o) mid (ob_hi o) [] DUnknown).
  { unfold arr_split_obj in Ho. destruct (ob_dflt o) as [| | | | |esz cnt flds tmpl]; try discriminate.
    destruct (ob_cells o); try discriminate. destruct (sv_eqb (ob_lo o) (SLit 0)); [|discriminate].
    injection Ho as <- <-. exists esz, cnt, flds, tmpl. auto. }
  destruct SH as (esz & cnt & flds & tmpl & Hd & Hc & E1 & E2).
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o1 :: o2 :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o1; o2] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |].
    subst o1 o2. unfold obj_wf in Hwfo |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb].
    repeat (apply andb_prop in Hwfo; destruct Hwfo as [Hwfo ?]). rewrite Hd in H. cbn [dflt_wf] in H |- *.
    rewrite Hwfo, H3, Hb, H. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o1 :: o2 :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o1; o2] ++ skipn (Datatypes.S i) (ss_objs S)).
  assert (LOHI : fst (obj_range rho o) <= snd (obj_range rho o)).
  { destruct Hoh as ((? & ? & ? & ?) & _). unfold obj_range. cbn [fst snd]. lia. }
  assert (FR : fst (obj_range rho o) = bv_unsigned (eval rho (ob_base o))).
  { unfold obj_range. cbn [fst]. rewrite Hlo0. lia. }
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact H1|]. constructor; [exact H2|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *.
    eapply pdr_replace2; [exact Hpd | | |]; rewrite ?R1, ?R2; unfold sub_range, ranges_disjoint; cbn [fst snd];
      unfold obj_range, obj_hi_of in Hm, LOHI |- *; cbn [fst snd] in *; lia.
  - intros x. split.
    + intros Hx. destruct (Z_lt_ge_dec x (fst (obj_range rho o) + soff rho mid)).
      * exists o1. split; [cbn; auto|]. rewrite R1. revert Hx l. clear. unfold in_range. cbn [fst snd]. intros; lia.
      * exists o2. split; [cbn; auto|]. rewrite R2. revert Hx g. clear. unfold in_range. cbn [fst snd]. intros; lia.
    + intros (o' & Hin' & Hx). destruct Hin' as [<-|[<-|[]]]; [rewrite R1 in Hx|rewrite R2 in Hx];
        revert Hx Hm LOHI FR; unfold in_range, obj_range, obj_hi_of; cbn [fst snd]; intros; lia.
Qed.

Lemma arr_merge_holds : ltac2:(tb__ "0|2|
S5S51S2S2S2S33S22S2A1S4aR3R2A2S25S2R1A2A3SbVsegs;R6R5R4A4SbVsegs;R7R6R4A4S45S47S19R8R5A2S1aR8R6A2A2S46Z2Z3fA2A2S34SbVsegs;R9R8R5A4S34S33S23S0S0A2S6R9R5A2S2bS0S0S2aS0S0S6R9R7A2M0A3S2cS0S0S6R9R6A2M1A3A4A3S33S0S2cS0S0G0A3S2aS0S0G1A3A3A2A2F_;F_;F_;F_;Fo;Fo2;Fo1;Fms;Frho;").
Proof using .
  intros rho ms o1 o2 o Hm H1 H2 Hw.
  unfold arr_merge_obj in Hm.
  destruct (ob_dflt o1) as [| | | | |esz cnt flds tmpl] eqn:Hd1; try discriminate.
  destruct (sv_eqb (ob_base o1) (ob_base o2)) eqn:Eb; [|discriminate].
  destruct (same_atoms (ob_hi o1) (ob_lo o2)) as [[|p|p]|] eqn:Ea; try discriminate. cbn [andb] in Hm.
  assert (D2 : ob_dflt o2 = DUnknown \/ ob_dflt o2 = DZero).
  { destruct (ob_dflt o2); try discriminate; auto. }
  assert (Eo : o = mkObj (ob_base o1) (ob_lo o1) (ob_hi o2) (ob_cells o1 ++ ob_cells o2) (DArr esz cnt flds tmpl)).
  { destruct (ob_dflt o2); try discriminate; injection Hm as <-; reflexivity. }
  clear Hm. subst o.
  apply sv_eqb_sound in Eb.
  pose proof (same_atoms_eq rho _ _ Ea) as Eq.
  assert (ADJ : obj_hi_of rho o1 = obj_lo_of rho o2).
  { unfold obj_hi_of, obj_lo_of, soff. rewrite Eq. reflexivity. }
  destruct H1 as (R1 & W1 & C1 & DF1 & I1). destruct H2 as (R2 & W2 & C2 & DF2 & I2).
  rewrite <- Eb in *.
  unfold obj_holds, obj_range. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi] in *. rewrite <- ?Eb.
  set (b := bv_unsigned (eval rho (ob_base o1))) in *.
  set (lo1 := soff rho (ob_lo o1)) in *. set (hi1 := soff rho (ob_hi o1)) in *.
  set (lo2 := soff rho (ob_lo o2)) in *. set (hi2 := soff rho (ob_hi o2)) in *.
  split; [|split; [cbn [fst snd]; reflexivity | cbn [fst snd]; lia]].
  split; [lia|].
  split. { intros off Hoff _.
           assert (D2w : dflt_writable (ob_dflt o2) = true) by (destruct D2 as [E|E]; rewrite E; reflexivity).
           destruct (Z_lt_ge_dec off hi1); [apply W1; [lia|rewrite Hd1; reflexivity] | apply W2; [lia|exact D2w]]. }
  split.
  { apply Forall_app. split.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) C1 c Hc) as (A & B & C). repeat split; try lia. exact C.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) C2 c Hc) as (A & B & C). repeat split; try lia. exact C. }
  split.
  { intros off Hoff Hnc.
    assert (NC1 : ~ covered rho (ob_cells o1) off).
    { intros H. apply Hnc. unfold covered in *. apply Exists_exists in H as (c & Hin & Hic). apply Exists_exists. exists c. split; [apply in_or_app; auto|exact Hic]. }
    assert (NC2 : ~ covered rho (ob_cells o2) off).
    { intros H. apply Hnc. unfold covered in *. apply Exists_exists in H as (c & Hin & Hic). apply Exists_exists. exists c. split; [apply in_or_app; auto|exact Hic]. }
    cbn [dflt_holds].
    destruct (Z_lt_ge_dec off hi1).
    - specialize (DF1 off ltac:(lia) NC1). rewrite Hd1 in DF1. exact DF1.
    - specialize (DF2 off ltac:(lia) NC2). destruct D2 as [E|E]; rewrite E in DF2; cbn [dflt_holds] in DF2; [exact DF2 | eexists; exact DF2]. }
  rewrite Hd1 in I1. cbn [dflt_inv] in I1 |- *. destruct I1 as (Hesz & Hflds & Hfit & Helems).
  split; [exact Hesz|]. split; [exact Hflds|]. split; [lia|]. exact Helems.
Qed.

Lemma obj_wf_arr_merge : ltac2:(tb__ "0|0|
S1S2S2S2S33S22S2A1S4aR3R2A2S25S2R1A2A3S33S26S15R5R4A2S28A3S33S26S15R6R4A2S28A3S33S26S15R7R4A2S28A3F_;F_;F_;Fo;Fo2;Fo1;Fn;").
Proof using .
  intros n o1 o2 o Hm W1 W2. unfold arr_merge_obj in Hm.
  destruct (ob_dflt o1) as [| | | | |esz cnt flds tmpl] eqn:Hd1; try discriminate.
  destruct (_ && _ && _)%bool; [|discriminate]. injection Hm as <-.
  unfold obj_wf in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  apply andb_prop in W1 as [W1 D1]. apply andb_prop in W1 as [W1 C1]. apply andb_prop in W1 as [W1 H1]. apply andb_prop in W1 as [B1 L1].
  apply andb_prop in W2 as [W2 D2]. apply andb_prop in W2 as [W2 C2]. apply andb_prop in W2 as [W2 H2]. apply andb_prop in W2 as [B2 L2].
  rewrite forallb_app, B1, L1, H2, C1, C2. cbn [andb]. rewrite Hd1 in D1. exact D1.
Qed.

Theorem smatch_arr_merge : ltac2:(tb__ "0|0|
S5S3S27S3S23S24S53A1S52A2S33S22S3A1S4cR4R3A2S25S3R2A2A3SeVsegs;R6R5R2A4SeVsegs;R7R4R3A4F_;F_;Fw;FS';Fi;FS;Frho;").
Proof using .
  intros rho S i S' [tr [ms md]] Hmg Hsm.
  unfold arr_merge_at in Hmg.
  destruct (nth_error (ss_objs S) i) as [o1|] eqn:Hn1; [|discriminate].
  destruct (nth_error (ss_objs S) (Datatypes.S i)) as [o2|] eqn:Hn2; [|discriminate].
  destruct (sitv (ss_facts S) (ob_lo o1)) as [[l1 h1]|] eqn:Hs1; [|discriminate].
  destruct (sitv (ss_facts S) (ob_hi o2)) as [[l2 h2]|] eqn:Hs2; [|discriminate].
  destruct (Z.ltb_spec (h2 - l1) (2 ^ 63)) as [Hlt|]; [|discriminate].
  destruct (arr_merge_obj o1 o2) as [o|] eqn:Ho; [|discriminate]. injection Hmg as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split4 _ _ _ _ Hn1 Hn2) as EQ.
  assert (Ho1 : obj_holds segs rho ms o1 /\ obj_holds segs rho ms o2).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall].
    inversion Hall as [|? ? A B]; subst. inversion B; subst. auto. }
  destruct Ho1 as [Ho1 Ho2].
  pose proof (sitv_sound rho (ss_facts S) (ob_lo o1) l1 h1 Hfacts Hs1) as (B1 & _).
  pose proof (sitv_sound rho (ss_facts S) (ob_hi o2) l2 h2 Hfacts Hs2) as (B2 & _).
  destruct (arr_merge_holds rho ms o1 o2 o Ho Ho1 Ho2 ltac:(unfold obj_lo_of, obj_hi_of; lia)) as (Hoh & Rng & Adj).
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S))
      with (firstn i (ss_objs S) ++ [o] ++ skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)).
    pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [Wa W]. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 Wb].
    assert (EQ' : ss_objs S = firstn i (ss_objs S) ++ o1 :: ([o2] ++ skipn (Datatypes.S (Datatypes.S i)) (ss_objs S))) by exact EQ.
    pose proof (swf_objs_replace S _ _ _ [] Hwf EQ' eq_refl) as Hwf1. cbn [app] in Hwf1.
    assert (EQ2 : ss_objs (set_objs S (firstn i (ss_objs S) ++ o2 :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)))
                  = firstn i (ss_objs S) ++ o2 :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)) by reflexivity.
    pose proof (swf_objs_replace _ _ _ _ [o] Hwf1 EQ2) as Hwf2. cbn [app forallb] in Hwf2.
    unfold set_objs in Hwf2. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf2.
    apply Hwf2. rewrite (obj_wf_arr_merge _ _ _ _ Ho W1 W2). reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  destruct Hmem as (Hall & Hpd & Hfr).
  split; [|split].
  - apply Forall_app in Hall as [A1 A2].
    inversion A2 as [|? ? _ A3]; subst. inversion A3 as [|? ? _ A4]; subst.
    apply Forall_app. split; [exact A1|]. constructor; [exact Hoh | exact A4].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *.
    eapply pdr_merge2; [exact Hpd|].
    intros a. rewrite Rng. unfold in_range. cbn [fst snd]. intros Ha.
    destruct (Z_lt_ge_dec a (snd (obj_range rho o1))); [left; lia | right; lia].
  - intros a Ha. apply Hfr.
    assert (COV : forall x, in_range (obj_range rho o) x <->
                   exists o', In o' [o1; o2] /\ in_range (obj_range rho o') x).
    { intros x. rewrite Rng. unfold in_range. cbn [fst snd]. split.
      + intros Hx. destruct (Z_lt_ge_dec x (snd (obj_range rho o1))).
        * exists o1. split; [cbn; auto | lia].
        * exists o2. split; [cbn; auto | lia].
      + intros (o' & Hin & Hx). cbn in Hin.
        assert (LE1 : fst (obj_range rho o1) <= snd (obj_range rho o1)).
        { destruct Ho1 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
        assert (LE2 : fst (obj_range rho o2) <= snd (obj_range rho o2)).
        { destruct Ho2 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
        destruct Hin as [<-|[<-|[]]]; lia. }
    apply (proj1 (outside_all_replace rho (firstn i (ss_objs S)) o
             (skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)) [o1; o2] a COV)). exact Ha.
Qed.

Lemma SPA_arr_split : ltac2:(tb__ "0|0|
S37S5S3bS27S4S3S24S3fQ40A1A1S3eS33S22S3A1S4dS39R6A1R5R4A3S25S3R3A2A3S36Vsegs;R9R7R8R3R2A6S36Vsegs;RaS3aR8R5A2R9R4R3A6F_;F_;Fw;Ftp;FS';Fmid;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i mid S' tp [tr [ms md]] Hsp [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_arr_split rho (ax_S A) i mid S' _ Hsp Hsm) as Hsm'.
  pose proof (smatch_facts segs _ _ _ Hsm) as HF0.
  unfold arr_split_at in Hsp.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (sv_below (ss_next (ax_S A)) mid && in_bounds (ss_facts (ax_S A)) (ob_lo o) (ob_hi o) mid 0 && uleq (ss_facts (ax_S A)) (arr_cnt_bytes o) 0 mid)%bool eqn:Hck; [|discriminate].
  apply andb_prop in Hck as [Hck Hul]. apply andb_prop in Hck as [Hb Hib].
  destruct (arr_split_obj o mid) as [[o1 o2]|] eqn:Ho; [|discriminate]. injection Hsp as <-.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  assert (Hoh : obj_holds segs rho (cfg_ms (snd (virt tp (tr, mkCfg ms md)))) o).
  { unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
    pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
    exact (proj1 (Forall_forall _ _) Hall o Hin_o). }
  destruct (arr_split_holds rho _ o mid o1 o2 (ss_facts (ax_S A)) HF0 Hib Hul Ho Hoh) as (_ & _ & R1 & R2 & Hm & Hlo0).
  assert (LOHI : fst (obj_range rho o) <= snd (obj_range rho o)).
  { destruct Hoh as ((? & ? & ? & ?) & _). unfold obj_range. cbn [fst snd]. lia. }
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [set_objs ss_objs]. intros o' x Ho' Hx. apply in_app_or in Ho' as [Ho'|[<-|[<-|Ho']]].
  - exists o'. split; [eapply In_firstn_In; exact Ho' | exact Hx].
  - exists o. split; [exact Hin_o|]. rewrite R1 in Hx. revert Hx Hm LOHI; unfold obj_range, obj_hi_of; cbn [fst snd]; intros; lia.
  - exists o. split; [exact Hin_o|]. rewrite R2 in Hx. revert Hx Hm LOHI Hlo0; unfold obj_range, obj_hi_of, obj_lo_of; cbn [fst snd]; intros; lia.
  - exists o'. split; [eapply In_skipn_In; exact Ho' | exact Hx].
Qed.

Lemma SPA_arr_merge : ltac2:(tb__ "0|0|
S37S5S3bS27S3S24S3fQ40A1A1S3eS33S22S3A1S4cS39R5A1R4A2S25S3R3A2A3S36Vsegs;R8R6R7R3R2A6S36Vsegs;R9S3aR7R5A2R8R4R3A6F_;F_;Fw;Ftp;FS';Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i S' tp [tr [ms md]] Hmg [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_arr_merge rho (ax_S A) i S' _ Hmg Hsm) as Hsm'.
  pose proof (smatch_facts segs _ _ _ Hsm) as HF0.
  unfold arr_merge_at in Hmg.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o1|] eqn:Hn1; [|discriminate].
  destruct (nth_error (ss_objs (ax_S A)) (Datatypes.S i)) as [o2|] eqn:Hn2; [|discriminate].
  destruct (sitv (ss_facts (ax_S A)) (ob_lo o1)) as [[l1 h1]|] eqn:Hs1; [|discriminate].
  destruct (sitv (ss_facts (ax_S A)) (ob_hi o2)) as [[l2 h2]|] eqn:Hs2; [|discriminate].
  destruct (Z.ltb_spec (h2 - l1) (2 ^ 63)) as [Hlt|]; [|discriminate].
  destruct (arr_merge_obj o1 o2) as [o|] eqn:Ho; [|discriminate]. injection Hmg as <-.
  assert (Hin1 : In o1 (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn1).
  assert (Hin2 : In o2 (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn2).
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall o1 Hin1) as Ho1.
  pose proof (proj1 (Forall_forall _ _) Hall o2 Hin2) as Ho2.
  pose proof (sitv_sound rho (ss_facts (ax_S A)) (ob_lo o1) l1 h1 HF0 Hs1) as (B1 & _).
  pose proof (sitv_sound rho (ss_facts (ax_S A)) (ob_hi o2) l2 h2 HF0 Hs2) as (B2 & _).
  destruct (arr_merge_holds rho _ o1 o2 o Ho Ho1 Ho2 ltac:(unfold obj_lo_of, obj_hi_of; lia)) as (Hoh & Rng & Adj).
  assert (LE1 : fst (obj_range rho o1) <= snd (obj_range rho o1)).
  { destruct Ho1 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
  assert (LE2 : fst (obj_range rho o2) <= snd (obj_range rho o2)).
  { destruct Ho2 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
  split; [unfold virt; cbn [fst snd cfg_ms cfg_model w_tr w_cfg]; exact Hsm'|]. split; [exact HMI|].
  split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [set_objs ss_objs]. intros o' x Ho' Hx. apply in_app_or in Ho' as [Ho'|[<-|Ho']].
  - exists o'. split; [eapply In_firstn_In; exact Ho' | exact Hx].
  - rewrite Rng in Hx. cbn [fst snd] in Hx.
    destruct (Z_lt_ge_dec x (snd (obj_range rho o1))).
    + exists o1. split; [exact Hin1 | lia].
    + exists o2. split; [exact Hin2 | lia].
  - exists o'. split; [eapply In_skipn_In; exact Ho' | exact Hx].
Qed.

Lemma tile_at_shape : ltac2:(tb__ "0|1|
S3S27S4S0S4S3S33S22S3A1S5aR6R5R4R3R2A5S25S3R1A2A3S34S33S1S8R2A1S8R7A1A3S34S33S24S16A1SfR2A1SfR7A1A3S33S24S23S23S4S4A2S4A2M0A1S40S2G0S3cS10R2A1A4S40S2G0S3cS10R7A1A4A3A2A2F_;FS';Fv;Fk;Foff;Fi;FS;").
Proof using .
  intros S i off k v S' H. unfold tile_at in H.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (tile_obj o off k v) as [o'|] eqn:Ho; [|discriminate].
  destruct (cell_wf (ss_next S) (mkCell off k v)); [|discriminate]. injection H as <-.
  cbn [set_objs ss_next ss_facts ss_objs]. split; [reflexivity|]. split; [reflexivity|].
  transitivity (map obj_ext (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S i) (ss_objs S))).
  - rewrite !map_app. cbn [map]. f_equal. f_equal.
    unfold tile_obj in Ho. destruct (_ && _ && _ && _)%bool; [|discriminate]. injection Ho as <-. reflexivity.
  - f_equal. symmetry. exact (split_at_nth' (ss_objs S) i o Hi).
Qed.

Lemma exts_cover : ltac2:(tb__ "0|4|
S5S24S2A1M0G0S33S24S23S23S4S4A2S4A2M1A1S40S2G1S3cR2A4S40S2G1S3cR1A4A3S2S0S50S2R2R5A3S34S44S2aS0S0S6R7R3A2M2A3R2A2S45R2S2cS0S0G2A3A2A2S35S2S2S34S50S2R1R7A3S34S44S2aS0S0S6R9R1A2M3A3R4A2S45R4S2cS0S0G3A3A2A2A2Lo;A2F_;F_;Fx;Fo';F_;Fl;Fl';Frho;").
Proof using .
  intros rho l'. induction l' as [|a t IH]; intros [|b u] Hm o' x Hin Hx; cbn [map] in Hm; try discriminate; [destruct Hin|].
  injection Hm as E1 E2 E3 Htu. destruct Hin as [<-|Hin].
  - exists b. split; [left; reflexivity|].
    unfold obj_range, obj_lo_of, obj_hi_of in Hx |- *. rewrite <- E1, <- E2, <- E3. exact Hx.
  - destruct (IH u Htu o' x Hin Hx) as (o & Ho & Hr). exists o. split; [right; exact Ho | exact Hr].
Qed.

Lemma SPA_tile : ltac2:(tb__ "0|0|
S37S5S3bS27S4S0S4S3S24S3fQ40A1A1S3eS33S22S3A1S5aS39R8A1R7R6R5R4A5S25S3R3A2A3S36Vsegs;RbR9RaR3R2A6S36Vsegs;RcS3aRaR5A2RbR4R3A6F_;F_;Fw;Ftp;FS';Fv;Fk;Foff;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i off k v S' tp [tr [ms md]] HT [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  destruct (tile_at_shape _ _ _ _ _ _ HT) as (Hn & _ & Hext).
  split; [exact (smatch_tile segs rho (ax_S A) i off k v S' _ HT Hsm)|]. split; [exact HMI|].
  split; [unfold axwf in Hwf |- *; cbn [ax_S ax_X ax_base ax_setS]; rewrite Hn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  intros o2 x Ho2 Hx. exact (exts_cover rho _ _ Hext o2 x Ho2 Hx).
Qed.

Lemma SPA_tiles : ltac2:(tb__ "0|0|
S37S5S24S23S23S23S27S4A2S0A2S4A2A1S3bS3S24S3fQ40A1A1S3eS33S22S3A1S5bS39R4A1R5A2S25S3R3A2A3S36Vsegs;R8R5R7R3R2A6S36Vsegs;R9S3aR6R5A2R8R4R3A6F_;F_;Fw;Ftp;FS';FA;Fts;Frho;FJ;").
Proof using .
  intros J rho ts. induction ts as [|[[[i off] k] v] rest IH]; intros A S' tp w HT Hw; cbn [tiles_at] in HT.
  - injection HT as <-. destruct A; exact Hw.
  - destruct (tile_at (ax_S A) i off k v) as [S1|] eqn:E; [|discriminate].
    pose proof (SPA_tile J rho A i off k v S1 tp w E Hw) as Hw1.
    pose proof (IH (ax_setS A S1) S' tp w) as IH'. cbn [ax_S ax_setS] in IH'.
    assert (EE : ax_setS (ax_setS A S1) S' = ax_setS A S') by (destruct A; reflexivity).
    rewrite <- EE. apply IH'; [|exact Hw1]. destruct A; exact HT.
Qed.

Lemma arr_mat_at_shape : ltac2:(tb__ "0|0|
S3S27S4S0S3S33S22S3A1S59R5R4R3R2A4S25S3R1A2A3S34S5dS8R6A1S8R2A1A2S33S24S23S23S4S4A2S4A2A1S3dR2A1S3dR6A1A3A2F_;FS';Fk;Foff;Fn;FS;").
Proof using .
  intros S n off k S' H. unfold arr_mat_at in H.
  destruct (nth_error (ss_objs S) n) as [o|] eqn:Hn; [|discriminate].
  destruct (ob_dflt o) as [| | | | |esz cnt flds tmpl] eqn:Hd; try discriminate.
  destruct (_ && _ && _)%bool; [|discriminate].
  destruct (load_arr S n o off k false (8 * Z.to_N k)%N esz cnt flds tmpl) as [v S1|] eqn:HL; [|discriminate].
  injection H as ->. split; [|exact (load_arr_exts S n o off k false _ esz cnt flds tmpl v S' Hn HL)].
  unfold load_arr in HL.
  destruct (lin_decomp _ _ _) as [[idx c]|].
  2: { unfold load_fresh, fresh in HL. destruct (dflt_writable (ob_dflt o)); apply lrok_inj in HL as [_ <-]; cbn; lia. }
  destruct (fld_index flds c k).
  2: { unfold load_fresh, fresh in HL. destruct (dflt_writable (ob_dflt o)); apply lrok_inj in HL as [_ <-]; cbn; lia. }
  destruct (uleq _ _ _ _).
  2: { unfold load_fresh, fresh in HL. destruct (dflt_writable (ob_dflt o)); apply lrok_inj in HL as [_ <-]; cbn; lia. }
  apply lrok_inj in HL as [_ <-]. cbn [ss_next]. lia.
Qed.

Lemma SPA_arr_mat : ltac2:(tb__ "0|0|
S37S5S3bS27S4S0S3S24S3fQ40A1A1S3eS33S22S3A1S59S39R7A1R6R5R4A4S25S3R3A2A3S38Vsegs;S8S39R8A1A1RaA3S36Vsegs;RbR9RaR4R3A6S35S5S5S34S1eS8S39RbA1A1RcR1A3S36Vsegs;RdS3aRbR7A2R1R6R5A6A2Lrho';A2F_;F_;F_;Fw;Ftp;FS';Fk;Foff;Fn;FA;Frho;FJ;").
Proof using .
  intros J rho A n off k S' tp [tr [ms md]] H HJ [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  destruct (smatch_arr_mat segs rho (ax_S A) n off k S' tr (vms md tp ms) (vmd md) H Hsm) as (rho' & Hag & Hle & Hsm').
  destruct (arr_mat_at_shape _ _ _ _ _ H) as [_ Hex].
  exists rho'. split; [exact Hag|]. split.
  - split; [unfold virt; cbn [fst snd cfg_ms cfg_model w_tr w_cfg]; exact Hsm'|]. split; [exact HMI|].
    split; [apply (axwf_stable A (ax_setS A S')); [exact Hwf | destruct A; exact Hle | destruct A; reflexivity | destruct A; reflexivity]|].
    split; [|exact Hhz].
    apply (shadow_ok_stable A (ax_setS A S') rho rho'); [exact Hag | exact Hwf | exact (smatch_swf segs _ _ _ Hsm) | destruct A; reflexivity | destruct A; reflexivity | destruct A; exact Hex | exact Hsh].
  - cbn [w_tr w_cfg cfg_model]. eapply HJ; [exact Hag | apply mat_equiv_refl | exact Hk].
Qed.

End WithSegs.
