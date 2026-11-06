(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "soff"; "valuation"; "eval"; "ob_dflt"; "smatch"; "cell"; "ob_base"; "ss_objs"; "sstate"; "ob_lo"; "sv"; "rl"; "ob_cells"; "obj_holds"; "ob_hi"; "obj_hi_of"; "obj_range"; "rd"; "dflt_writable"; "mkObj"; "obj_lo_of"; "obj_wf"; "odefault"; "swf"; "SLit"; "rom_ok"; "DList"; "DRom"; "is_arr"; "mkSS"; "ranges_disjoint"; "rd_bytes"; "rm"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "option"; "Some"; "list"; "bool"; "true"; "nat"; "prod"; "nil"; "S"; "app"; "cons"; "None"; "false"; "length"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "sub"; "pow"; "to_nat"; "opp"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "wview"; "ms_mem"; "@Stdlib.Lists.List"; "nth_error"; "Forall2"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL"; "dlist_of"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "BLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.DG"; "obj_rom_of"; "merge_lists"; "reframe_obj"; "obj_to_rom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymObj SymCall SymBytes SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslWL ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DG.
Variable segs : list Segment.

Lemma wview_ext : ltac2:(tb__ "0|3|
S46Q40A1M0S2fS46Q8A1A1M1F_;M2G2G0S2aG1R3R1A1R2R1A1A3S2aG1S4bVsegs;R4R2A3S4bVsegs;R3R2A3A3F_;Fa;Fm';Fm;").
Proof using . intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rd_of_mem : ltac2:(tb__ "0|0|
S4aS46Q40A1S1aVsegs;R2A2S2aS2fS46Q8A1A1S60Vsegs;S4cR3A1R2A3S12R3R2A2A3F_;Fa;Fms;").
Proof using . intros ms a Hrom. unfold rd_of, rd, ms_read_byte. rewrite (Hrom a). reflexivity. Qed.

Lemma bv_add_nat : ltac2:(tb__ "0|3|
S46Q40M0A1M1S34S40S3eS47G0R2A2S41R1A1A2S43Z2Z40A2A2S2aG1S49G0R3S48G0S41R2A1M2A2A3S48G0S3eS47G0R3A2G2A2A2A3F_;Fj;Fa;").
Proof using .
  intros a j H. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  pose proof (urange a). rewrite (Z.mod_small (Z.of_nat j)) by lia. reflexivity.
Qed.

Lemma rd_bytes_nth : ltac2:(tb__ "0|4|
S4aS34S46Q40M0A1S31S46Q8M1A1M2A1M3S34S2aS2fG3A1S20R5R3R4A3S30G3R2A2A3S61R2R5A2S3fS3eS47G0R5A2S41R6A1A2S43Z2Z40A2A2S2aS2fG2A1S12R8S48G0S3eS47G0R6A2S41R4A1A2A2A2S30G2S52G2R4R5S48G1Z0A2A4A2A3F_;F_;F_;Fj;Fbs;Fa;Fk;Fms;").
Proof using .
  intros ms k. induction k as [|k IH]; intros a bs j H Hj Hb; [lia|].
  cbn [rd_bytes] in H. destruct (rd ms a) as [b|] eqn:Eb; [|discriminate].
  destruct (rd_bytes ms (a + 1)%bv k) as [bs'|] eqn:Er; [|discriminate]. injection H as <-.
  destruct j as [|j].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Eb.
  - cbn [nth]. pose proof (urange a) as Ua.
    assert (E1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1).
    { rewrite bv_add_unsigned. unfold bv_wrap. rewrite two64. change (bv_unsigned (1%bv : bv 64)) with 1. apply Z.mod_small. lia. }
    specialize (IH (a + 1)%bv bs' j Er ltac:(lia) ltac:(rewrite E1; lia)).
    rewrite E1 in IH. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) in IH by lia. exact IH.
Qed.

Lemma obj_writable : ltac2:(tb__ "0|2|
S2S4aS0S2dSeVsegs;R4R3R2A4S2aS32S13S4R3A1A1S33A3S2bS3fS15R6R4A2R3A2S40R3S10R6R4A2A2A2S2cS2aS2fS46Q8A1M0A1S4bVsegs;S4cR6A1S48Q40M1S3eS47G1S3R7S7R5A1A2A2R4A2A2A3S3aG0A1A3A1F_;F_;F_;Foff;Fo;Fms;Frho;").
Proof using . intros rho ms o off (Hb & Hw & _) Hd Hoff. exact (Hw off Hoff Hd). Qed.

Lemma obj_bytes_list : ltac2:(tb__ "0|3|
S2S4aS0S2eS2dSeVsegs;R5R4R3A4S2aS2fS2eA1S51S4R4A1A1S30S2eR3A2A3S2aS31S6A1SdR5A1S36S6A1A3S2bS3fS15R8R6A2R4A2S40R4S10R8R6A2A2A2S2aS2fS46Q8M0A1M1A1S12R8S48Q40M2S3eS47G2S3R9S7R7A1A2A2R5A2A2A2S30G1S52G1S44S42R5S15R9R7A2A2A1ScR9R6A2S48G0Z0A2A4A2A3F_;F_;F_;F_;Foff;Fl;Fo;Fms;Frho;").
Proof using .
  intros rho ms o l off Ho Hd Hc Hoff.
  pose proof (listish_obj_rd_bytes segs rho ms o l 1 off Ho Hd Hc ltac:(lia) ltac:(lia)) as R.
  cbn [rd_bytes] in R. destruct (rd ms _) as [b|]; [|discriminate].
  destruct (skipn (Z.to_nat (off - obj_lo_of rho o)) (rl rho l)) as [|b' t] eqn:Es; cbn in R; [discriminate|].
  injection R as ->. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat _)), <- nth_skipn, Es. reflexivity.
Qed.

Lemma obj_list_length : ltac2:(tb__ "0|0|
S2S4aS0S2eSeVsegs;R4R3R2A4S2aS2fS2eA1S51S4R3A1A1S30S2eR2A2A3S2aS2dS41S3cS46Q8A1ScR6R3A2A2A1S42S10R6R4A2S15R6R4A2A2A3F_;F_;Fl;Fo;Fms;Frho;").
Proof using .
  intros rho ms o l (Hb & Hw & Hc & Hdf & Hinv) Hd.
  destruct (ob_dflt o); cbn [dlist_of] in Hd; try discriminate; injection Hd as ->; exact Hinv.
Qed.

Lemma obj_bytes_cells : ltac2:(tb__ "0|5|
S2S4aS0S2eS2dS34S31S57A1M0S2dSeVsegs;R8R7R6A4S2aS32S16R6R7A2S33A3S2aSbSaR8A1S19R6A1A3S3fS45S43Z2Z3eA2M1A1R7A2S3fS3eR8S41R7A1A2S10RcRaA2A2S40S10RdRbA2G1A2S2aS2fG0A1S59SdRcA1S19RaA1Z0M2R9A4S30G0R8A2A3S2bS3fRbR8A2S40R8S3eRbS41RaA1A2A2A2S2aS2fS46Q8A1M3A1S12RfS48Q40M4S3eS47G4S3R10S7ReA1A2A2R9A2A2A2S30G3S58R10S52S57S44S42R9RcA2A1RaS5aG2A1A4A2A2A3F_;F_;F_;F_;F_;F_;F_;F_;Foff;Fbl;Fk;Flo;Fn;Fo;Fms;Frho;").
Proof using .
  intros rho ms o n lo k bl off Ho Hwf Hlo Hlo1 Hk Hhi Hcb Hoff.
  pose proof Ho as (Hbnd & _).
  assert (Elo : obj_lo_of rho o = lo) by (unfold obj_lo_of; rewrite Hlo; apply soff_lit_small; lia).
  pose proof (cells_bytes_sound segs rho ms o n (SLit lo) 0 k bl Ho Hwf
                ltac:(rewrite soff_lit_small by lia; lia) Hcb) as R.
  rewrite soff_lit_small in R by lia. rewrite Z.add_0_r in R.
  pose proof (cells_bytes_length _ _ _ _ _ Hcb) as Hlen.
  pose proof (rd_bytes_nth ms k (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + lo)) _ (Z.to_nat (off - lo)) R ltac:(lia)) as X.
  rewrite u64_of_sum in X by lia.
  replace (bv_unsigned (eval rho (ob_base o)) + lo + Z.of_nat (Z.to_nat (off - lo)))
    with (bv_unsigned (eval rho (ob_base o)) + off) in X by lia.
  rewrite (X ltac:(lia)). f_equal.
  rewrite <- (map_nth (beval rho)). apply nth_indep. rewrite length_map. lia.
Qed.

Lemma released_rd : ltac2:(tb__ "0|2|
S46Q40A1M0S2fS46Q8A1A1M1F_;S4aG0OF_;G0G0R3R1A1S2aG1R6R2A1S4cR5R2A2A3F_;Fa;S1aVsegs;R4A2R4R3A1S2aG1S60Vsegs;R7R4A3S12R6R4A2A3F_;F_;F_;Fa;FP;Fms;Fm';").
Proof using . intros m' ms P a Hin Hrom Ha. unfold rd_of, rd, ms_read_byte. rewrite (Hin a Ha), (Hrom a). reflexivity. Qed.

Lemma released_wview : ltac2:(tb__ "0|2|
S46Q40A1M0S2fS46Q8A1A1M1F_;S4aG0OF_;G0G0R3R1A1S2aG1R6R2A1S4cR5R2A2A3F_;Fa;R3R2A1S2aG1S4bVsegs;R6R3A3S4bVsegs;S4cR5A1R3A3A3F_;F_;Fa;FP;Fms;Fm';").
Proof using . intros m' ms P a Hin Ha. apply wview_ext. exact (Hin a Ha). Qed.

Lemma smatch_carve_listobj : ltac2:(tb__ "0|7|
S2S9S35S31S50A1S4fA2SbSbSbS2dS2dS17S2eS2eS5Vsegs;RbRaR9A4S2aS2fS2eA1S51R4A1S30S2eR3A2A3S14RaR9R8S36S6A1R5A5S0S1eS26RdA1S27RdA1S24RdA1S23RdA1S28RdA1S38S0S8RdA1S39S0R1S36S0A1A3A3S22RdA1R4S25RdA1A9S9S2aS32S18R1A1S33A3S47Q40M0S3R10RdA2A2S2dS2aS2dS1R11RdA2RbA3S2aS2dS1R12RdA2RbA3S3fRdRcA2S40S42RdReA2S43Z2M1Z3fA2A2S3fZ0M2S3eR5RfA2A2S3fS3eR6RfA2S43G1Z40A2A2S2aS2dS41S3cS46Q8M3A1M4ScR17ReA2A2A1S42R10R11A2A3S55S0S0S1fS11R19R1A2S3dS2dS2dS3eR9R13A2S3eR9R12A2A4A2Lo';S8R17A1A3S2dS2bS3fR14R1A2S40R1R13A2A2S2aS32S13R13A1S33A3S2cS2aS2fG4A1M5S4bVsegs;S21R1cA1M6S48G0S3eRcR3A2A2A3S3aG4A1A3A1F_;F_;Foff;S2dS2bS3fR15R1A2S40R1R14A2A2S2aG5S60Vsegs;G6S48G0S3eRcR2A2A2A3S30G4S52G4S44S42R2R16A2A1ScR1cR13A2S48G3G2A2A4A2A3F_;Foff;S5Vsegs;R1bRdR19A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';To;F_;F_;Fnx;Fl;Fd;Fhi;Flo;Fehi;Felo;Fbase;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] base elo ehi lo hi d l nx Hsm Hd o S' Hwf b Elo Ehi Hlh Hhl Hb0 Hb1 Hlen Hdisj Hw Hrd.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).
  assert (OUT : forall off, lo <= off < hi -> outside_all rho (ss_objs S) (Z_to_bv 64 (b + off))).
  { intros off Hoff. eapply ranges_disjoint_outside; [exact Hdisj|]. rewrite u64_of_sum by lia. lia. }
  assert (Hmem : forall off, lo <= off < hi -> ms_mem ms (Z_to_bv 64 (b + off)) = rm rho (Z_to_bv 64 (b + off))).
  { intros off Hoff. apply Hfr. apply OUT. exact Hoff. }
  assert (Hrange : obj_range rho o = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi]. fold b. rewrite Elo, Ehi. reflexivity. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
    rewrite Elo, Ehi.
    split; [lia|]. split.
    { intros off Hoff Hdw. rewrite (wview_ext (ms_mem ms) (rm rho)) by (apply Hmem; exact Hoff). exact (Hw off Hoff Hdw). }
    split; [constructor|].
    split.
    { intros off Hoff _.
      assert (R : rd ms (Z_to_bv 64 (b + off)) = Some (nth (Z.to_nat (off - lo)) (rl rho l) (Z_to_bv 8 0))).
      { rewrite (rd_frame segs rho (ss_objs S) ms _ Hrom Hfr (OUT off Hoff)). exact (Hrd off Hoff). }
      destruct d; cbn [dlist_of] in Hd; try discriminate; injection Hd as ->; cbn [dflt_holds]; exact R. }
    destruct d; cbn [dlist_of] in Hd; try discriminate; injection Hd as ->; cbn [dflt_inv]; exact Hlen.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite Hrange. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

Definition obj_rom_of (o : sobj) : sobj := ltac2:(tb__ "0|0|
S17S0Lx;S4Vo;A1Vo;Vo;Vo;S2eS14S7Vo;A1SaVo;A1SfVo;A1SdVo;A1S1cR1A1A5Ll;S2eVo;Ll;S2dSbS31S35S2dS2dA2A1S31S29A1Vo;Ltmpl;Lflds;Lcnt;Lesz;X17x6").

Definition obj_to_rom (S : sstate) (i : nat) : sstate := ltac2:(tb__ "0|1|
S2fS0A1S9Lx;S4dS0S8VS;A1M0Vi;A3S0S5fVS;S38S0S53S0Vi;G0A3S39S0S5bR1A1S54S0S37Vi;A1G0A3A3A3A2Lo;VS;X2fx2").

Lemma obj_holds_rom_of : ltac2:(tb__ "0|0|
S2S4aS0SeVsegs;R3R2R1A4SeVsegs;R4R3S5bR2A1A4F_;Fo;Fms;Frho;").
Proof using .
  intros rho ms o Ho. unfold obj_rom_of. destruct (ob_dflt o) eqn:E; try exact Ho.
  pose proof Ho as (Hb & Hw & Hc & Hdf & Hinv).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *. rewrite E in *.
  split; [exact Hb|]. split; [intros off _ D; discriminate D|]. split; [exact Hc|]. split; [exact Hdf|exact Hinv].
Qed.

Lemma obj_range_rom_of : ltac2:(tb__ "0|0|
S2S0S2aS35S2dS2dA2S11R2S5bR1A1A2S11R2R1A2A3Fo;Frho;").
Proof using . intros rho o. unfold obj_rom_of. destruct (ob_dflt o); reflexivity. Qed.

Lemma obj_wf_rom_of : ltac2:(tb__ "0|0|
S2eS0S2aS32S16R2R1A2S33A3S2aS32S16R3S5bR2A1A2S33A3F_;Fo;Fn;").
Proof using .
  intros n o H. unfold obj_rom_of. destruct (ob_dflt o) eqn:E; try exact H.
  unfold obj_wf in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite E in H. cbn [dflt_wf] in *.
  exact H.
Qed.

Lemma Forall2_refl_ranges : ltac2:(tb__ "0|0|
S2S31S0A1S4eS0S0S0S0S2aS35S2dS2dA2S11R4R1A2S11R4R2A2A3Lo';Lo;R1R1A5FL;Frho;").
Proof using . intros rho L. induction L; constructor; [reflexivity | assumption]. Qed.

Theorem smatch_obj_to_rom : ltac2:(tb__ "0|0|
S2S9S35S31S50A1S4fA2S34S5Vsegs;R4R3R2A4S5Vsegs;R5S5eR4R2A2R3A4F_;Fi;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] i Hsm. unfold obj_to_rom.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|exact Hsm].
  pose proof Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 (ss_objs S) i o Hn) as Esplit.
  set (L1 := firstn i (ss_objs S)) in *. set (L2 := skipn (Datatypes.S i) (ss_objs S)) in *.
  assert (Hmm : mem_match segs rho (L1 ++ obj_rom_of o :: L2) ms).
  { rewrite Esplit in Hm. destruct Hm as (Hall & Hpd & Hfr). split; [|split].
    - apply Forall_app in Hall as [H1 H2]. inversion H2 as [|x l Ho H3]; subst.
      apply Forall_app. split; [exact H1|]. constructor; [apply obj_holds_rom_of; exact Ho | exact H3].
    - eapply pairwise_disjoint_Forall2; [|exact Hpd].
      apply Forall2_app; [apply Forall2_refl_ranges|]. constructor; [apply obj_range_rom_of | apply Forall2_refl_ranges].
    - intros a Ha. apply Hfr. eapply outside_all_Forall2; [|exact Ha].
      apply Forall2_app; [apply Forall2_refl_ranges|]. constructor; [apply obj_range_rom_of | apply Forall2_refl_ranges]. }
  unfold smatch, set_objs. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
  split.
  { unfold swf in *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
    rewrite Esplit in Hswf. rewrite forallb_app in Hswf |- *. cbn [forallb] in Hswf |- *.
    apply andb_prop in Hswf as [Hswf F8]. apply andb_prop in Hswf as [Hswf F7].
    apply andb_prop in F7 as [F7a F7]. apply andb_prop in F7 as [F7b F7c].
    rewrite Hswf, F8, F7a, F7c, (obj_wf_rom_of _ _ F7b). reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [exact Hmm|exact Hfa].
Qed.

Theorem smatch_obj_to_list_sym : ltac2:(tb__ "0|2|
S2S9S35S31S50A1S4fA2S34S2eS0S2dS2dS31S57A1M0S5Vsegs;R9R8R7A4S2aS2fS0A1S4dS0S8R9A1R7A3S30S0R5A2A3S2aS2dS1RbSaR6A1A2R5A3S2aS2dS1RcSfR7A1A2R5A3S3fS45S43Z2Z3eA2M1A1R7A2S2bS3fR8R7A2S40R7G1A2A2S2aS32S13S4RaA1A1S33A3S2aS32S1dS4RbA1A1S3bA3S2aS2fG0A1S59SdRcA1SaRcA1Z0S44S42RaRbA2A1A4S30G0R9A2A3S2aS32S63ReR11A2S3bA3S5Vsegs;S62R13RfS56S57S46Q8A1S58R13A1RbA4A3S64R12R10RfA3R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbl;Fhi;Flo;Fo;Fl;Fi;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] i l o lo hi bl Hsm Hn Hlo Hhi Hb0 Hb Hwr Harr Hcb Hrl.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof (swf_obj_nth S i o Hwf Hn) as Howf.

  assert (Hor : obj_has_rl l o = false).
  { pose proof Hrl as Hrl'. unfold state_has_rl in Hrl'.
    apply Bool.orb_false_iff in Hrl' as [Hrl' _]. apply Bool.orb_false_iff in Hrl' as [Hrl' Ro].
    exact (existsb_false_forall (obj_has_rl l) (ss_objs S) o Ro (nth_error_In _ _ Hn)). }
  pose proof Hor as Hor'. unfold obj_has_rl in Hor'.
  apply Bool.orb_false_iff in Hor' as [Hor' Rd]. apply Bool.orb_false_iff in Hor' as [Hor' Rc].
  apply Bool.orb_false_iff in Hor' as [Hor' Rhi]. apply Bool.orb_false_iff in Hor' as [Rb Rlo].
  assert (Eb : eval (rho_set_rl rho l (map (beval rho) bl)) (ob_base o) = eval rho (ob_base o)) by (apply eval_set_rl; exact Rb).
  assert (Elo : soff (rho_set_rl rho l (map (beval rho) bl)) (ob_lo o) = lo) by (unfold soff; rewrite (eval_set_rl rho l _ _ Rlo); exact Hlo).
  assert (Ehi : soff (rho_set_rl rho l (map (beval rho) bl)) (ob_hi o) = hi) by (unfold soff; rewrite (eval_set_rl rho l _ _ Rhi); exact Hhi).
  set (rho' := rho_set_rl rho l (map (beval rho) bl)) in *.
  assert (Hsm' : smatch segs rho' S (tr, mkCfg ms md)) by (apply smatch_set_rl; assumption).
  pose proof Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmm & _). cbn [fst snd cfg_ms cfg_model] in Hmm.
  destruct Hmm as (Hall & Hpd & Hfr).
  pose proof (Forall_nth_error _ _ _ _ Hall Hn) as Ho.
  unfold obj_to_list. rewrite Hn.
  pose proof (nth_error_split3 (ss_objs S) i o Hn) as Esplit.
  set (o' := mkObj (ob_base o) (ob_lo o) (ob_hi o) [] (DList l)).
  assert (Hrange : obj_range rho' o' = obj_range rho' o) by reflexivity.
  assert (Ho' : obj_holds segs rho' ms o').
  { pose proof Ho as (Hbnd & Hw & Hc & Hd & Hinv). unfold obj_holds. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi]. rewrite Elo, Ehi in *.
    split; [exact Hbnd|]. split; [intros off Hoff _; apply Hw; [exact Hoff | exact Hwr]|]. split; [constructor|]. split.
    - intros off Hoff _. cbn [dflt_holds]. subst rho'. cbn [rl rho_set_rl]. rewrite Pos.eqb_refl.
      destruct (smatch_mm segs rho S tr ms md Hsm) as (Hall0 & _ & _).
      pose proof (Forall_nth_error _ _ _ _ Hall0 Hn) as Ho0.
      pose proof Ho0 as (Hbnd0 & _). unfold obj_lo_of, obj_hi_of in Hbnd0. rewrite Hlo, Hhi in Hbnd0.
      pose proof (cells_bytes_sound segs rho ms o (ss_next S) (ob_lo o) 0 (Z.to_nat (hi - lo)) bl Ho0 Howf) as X.
      unfold obj_lo_of, obj_hi_of in X. rewrite Hlo, Hhi in X.
      specialize (X ltac:(lia) Hcb).
      rewrite Eb.
      pose proof (rd_bytes_nth ms (Z.to_nat (hi - lo)) (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + lo + 0)) _ (Z.to_nat (off - lo)) X ltac:(lia)) as Y.
      rewrite Z_to_bv_small in Y by (change (bv_modulus 64%N) with (2 ^ 64); lia).
      specialize (Y ltac:(lia)).
      replace (bv_unsigned (eval rho (ob_base o)) + lo + 0 + Z.of_nat (Z.to_nat (off - lo))) with (bv_unsigned (eval rho (ob_base o)) + off) in Y by lia.
      exact Y.
    - cbn [dflt_inv]. subst rho'. cbn [rl rho_set_rl]. rewrite Pos.eqb_refl, length_map, (cells_bytes_length _ _ _ _ _ Hcb). lia. }
  unfold set_objs.
  apply (smatch_set_objs_next segs rho' S (tr, mkCfg ms md) _ (ss_next S) (ss_lenient S) Hsm').
  - cbn [snd cfg_ms]. rewrite Esplit in Hall, Hpd, Hfr. split; [|split].
    + apply Forall_app in Hall as [A1 A2]. apply Forall_cons_iff in A2 as [_ A3]. apply Forall_app. split; [exact A1|]. constructor; assumption.
    + eapply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app in *. cbn [map] in *. rewrite Hrange. exact Hpd.
    + intros a Ha. apply Hfr. unfold outside_all in *. rewrite Forall_app in *. destruct Ha as [Ha1 Ha2]. apply Forall_cons_iff in Ha2 as [Ha2 Ha3].
      split; [exact Ha1|]. constructor; [rewrite <- Hrange; exact Ha2 | exact Ha3].
  - pose proof (smatch_swf segs _ _ _ Hsm') as W. unfold swf in W |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    repeat (apply andb_prop in W; destruct W as [W ?]). repeat (apply andb_true_intro; split); try assumption.
    match goal with Hx : forallb (obj_wf _) (ss_objs S) = true |- _ => rename Hx into Hobjs end.
    rewrite Esplit in Hobjs. rewrite forallb_app in Hobjs |- *. apply andb_prop in Hobjs as [F1 F2]. cbn [forallb] in F2 |- *. apply andb_prop in F2 as [F2 F3].
    rewrite F1, F3. cbn [andb]. rewrite Bool.andb_true_r.
    unfold obj_wf in Howf |- *. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    repeat (apply andb_prop in Howf; destruct Howf as [Howf ?]).
    repeat (apply andb_true_intro; split); try assumption; try reflexivity.
Qed.

Definition merge_lists (S : sstate) (i : nat) (l : positive) : sstate := ltac2:(tb__ "0|3|
S2fS0A1S9Lx;M0S4dS0S8VS;A1M1Vi;A3S0G0S4dS0G1S37Vi;A1M2A3S0S5fVS;S38S0S53S0Vi;G1A3S39S0S14S7R2A1SaR2A1SfR1A1S36S6A1S1bVl;A1A5S54S0S37G2A1G1A3A3A3A2Lo2;VS;X2fx2Lo1;VS;X2fx2").

Theorem smatch_merge_lists : ltac2:(tb__ "0|7|
S2S9S35S31S50A1S4fA2S34S2eS0S0S2eS2eS5Vsegs;R9R8R7A4S2aS2fS0A1M0S4dS0S8R9A1R7A3S30S0R5A2M1A3S2aG0S4dS0S8RaA1S37R8A1A3G1A3S2aS31S6A1SdR7A1S36S6A1A3M2G2S2aS2fS2eA1S51S4R9A1A1S30S2eR7A2A3M3G3S2aS32S13S4RbA1A1S33A3M4G4S2aS46Q40A1S3R12S7RdA1A2S3R12S7RcA1A2A3S2aS2dS1R13SfReA1M5A2S1R13SaRdA1A2A3S40S42S1R14G5A2S1R14SaRfA1A2A2S43Z2Z3fA2A2S2aS31S46Q8A1M6A1ScR15R11A2S38G6ScR15ReA2ScR15RdA2A3A3S2aS32S18S5cR15R13R12A3A1S33A3S5Vsegs;R17S5cR16R14R13A3R15A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fo2;Fo1;Fl;Fi;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] i l o1 o2 l1 l2 Hsm Hn1 Hn2 Hc1 Hc2 Hd1 Hd2 Hw1 Hw2 Eb Adj Hsz Hl Hwf.
  unfold merge_lists in *. rewrite Hn1, Hn2 in *.
  pose proof Hsm as (_ & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & Hmm & _). cbn [fst snd cfg_ms cfg_model] in Hmm, Hrom.
  destruct Hmm as (Hall & Hpd & Hfr).
  pose proof (nth_error_split4 _ _ _ _ Hn1 Hn2) as EQ.
  assert (Ho12 : obj_holds segs rho ms o1 /\ obj_holds segs rho ms o2).
  { rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall']. inversion Hall' as [|? ? A B]; subst. inversion B; subst. auto. }
  destruct Ho12 as [Ho1 Ho2].
  set (o := mkObj (ob_base o1) (ob_lo o1) (ob_hi o2) [] (DList l)).
  pose proof Ho1 as (Hb1 & Hwr1 & _ & Hdf1 & Hinv1). pose proof Ho2 as (Hb2 & Hwr2 & _ & Hdf2 & Hinv2).
  unfold obj_lo_of, obj_hi_of in *.
  assert (L1 : Z.of_nat (length (rl rho l1)) = soff rho (ob_hi o1) - soff rho (ob_lo o1)).
  { destruct (ob_dflt o1); cbn [dlist_of] in Hd1; try discriminate; injection Hd1 as ->; exact Hinv1. }
  assert (L2 : Z.of_nat (length (rl rho l2)) = soff rho (ob_hi o2) - soff rho (ob_lo o2)).
  { destruct (ob_dflt o2); cbn [dlist_of] in Hd2; try discriminate; injection Hd2 as ->; exact Hinv2. }
  assert (Rng : obj_range rho o = (fst (obj_range rho o1), snd (obj_range rho o2))).
  { unfold obj_range, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi]. rewrite Eb. reflexivity. }
  assert (Ho : obj_holds segs rho ms o).
  { unfold obj_holds, o, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    split; [rewrite Eb in *; lia|]. split.
    { intros off Hoff _. destruct (Z_lt_le_dec off (soff rho (ob_hi o1))).
      - apply Hwr1; [lia | exact Hw1].
      - rewrite Eb. apply Hwr2; [lia | exact Hw2]. }
    split; [constructor|]. split.
    { intros off Hoff _. cbn [dflt_holds]. rewrite Hl.
      destruct (Z_lt_le_dec off (soff rho (ob_hi o1))).
      - rewrite app_nth1 by lia.
        pose proof (Hdf1 off ltac:(lia) ltac:(rewrite Hc1; intros HC; inversion HC)) as D1.
        destruct (ob_dflt o1); cbn [dlist_of] in Hd1; try discriminate; injection Hd1 as ->; exact D1.
      - rewrite app_nth2 by lia. rewrite Eb.
        pose proof (Hdf2 off ltac:(lia) ltac:(rewrite Hc2; intros HC; inversion HC)) as D2.
        replace (Z.to_nat (off - soff rho (ob_lo o1)) - length (rl rho l1))%nat with (Z.to_nat (off - soff rho (ob_lo o2))) by lia.
        destruct (ob_dflt o2); cbn [dlist_of] in Hd2; try discriminate; injection Hd2 as ->; exact D2. }
    cbn [dflt_inv]. rewrite Hl, length_app. lia. }
  unfold set_objs.
  apply (smatch_set_objs_next segs rho S (tr, mkCfg ms md) _ (ss_next S) (ss_lenient S) Hsm); [|exact Hwf].
  cbn [snd cfg_ms]. rewrite EQ in Hall, Hpd, Hfr. split; [|split].
  - apply Forall_app in Hall as [A1 A2]. inversion A2 as [|? ? _ A3]; subst. inversion A3 as [|? ? _ A4]; subst.
    apply Forall_app. split; [exact A1|]. constructor; [exact Ho | exact A4].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *.
    eapply pdr_merge2; [exact Hpd|].
    intros a. rewrite Rng. unfold in_range, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. intros Ha.
    rewrite <- Eb in *. destruct (Z_lt_ge_dec a (bv_unsigned (eval rho (ob_base o1)) + soff rho (ob_hi o1))); [left; lia | right; lia].
  - intros a Ha. apply Hfr.
    assert (COV : forall x, in_range (obj_range rho o) x <-> exists o', In o' [o1; o2] /\ in_range (obj_range rho o') x).
    { intros x. rewrite Rng. unfold in_range, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. rewrite <- Eb. split.
      + intros Hx. destruct (Z_lt_ge_dec x (bv_unsigned (eval rho (ob_base o1)) + soff rho (ob_hi o1))).
        * exists o1. split; [cbn; auto | lia].
        * exists o2. split; [cbn; auto | rewrite <- Eb; lia].
      + intros (o' & Hin & Hx). cbn in Hin. destruct Hin as [<-|[<-|[]]]; [lia|]. rewrite <- Eb in Hx. lia. }
    apply (proj1 (outside_all_replace rho (firstn i (ss_objs S)) o
             (skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)) [o1; o2] a COV)). exact Ha.
Qed.

Definition reframe_obj (S : sstate) (i : nat) (b lo hi : sv) : sstate := ltac2:(tb__ "0|1|
S2fS0A1S9Lx;S4dS0S8VS;A1M0Vi;A3S0S5fVS;S38S0S53S0Vi;G0A3S39S0S14Vb;Vlo;Vhi;S36S6A1S4R1A1A5S54S0S37Vi;A1G0A3A3A3A2Lo;VS;X2fx2").

Theorem smatch_reframe_listobj : ltac2:(tb__ "0|1|
S2S9S35S31S50A1S4fA2S34S0S2eSbSbSbS5Vsegs;R9R8R7A4S2aS2fS0A1S4dS0S8R9A1R7A3S30S0R6A2A3S2aS31S6A1SdR7A1S36S6A1A3S2aS2fS2eA1S51S4R8A1A1S30S2eR7A2A3S2aS2dS3eS47Q40M0S3RdR7A2A2S1RdR6A2A2S3eS47G0S3RdS7R9A1A2A2S1RdSaR9A1A2A2A3S2aS2dS3eS47G0S3ReR8A2A2S1ReR6A2A2S3eS47G0S3ReS7RaA1A2A2S1ReSfRaA1A2A2A3S2aS32S18S5dReRcR9R8R7A5A1S33A3S5Vsegs;R10S5dRfRdRaR9R8A5ReA4F_;F_;F_;F_;F_;F_;F_;Fhi';Flo';Fb';Fl;Fo;Fi;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] i o l b' lo' hi' Hsm Hn Hc Hd Elo Ehi Hwf.
  unfold reframe_obj in *. rewrite Hn in *.
  pose proof Hsm as (_ & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & Hmm & _). cbn [fst snd cfg_ms cfg_model] in Hmm, Hrom.
  destruct Hmm as (Hall & Hpd & Hfr).
  pose proof (nth_error_split3 (ss_objs S) i o Hn) as Esplit.
  pose proof (Forall_nth_error _ _ _ _ Hall Hn) as Ho.
  set (o' := mkObj b' lo' hi' [] (ob_dflt o)).
  pose proof Ho as (Hb & Hw & _ & Hdf & Hinv). unfold obj_lo_of, obj_hi_of in *.
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { unfold obj_range, obj_lo_of, obj_hi_of, o'. cbn [ob_base ob_lo ob_hi]. rewrite Elo, Ehi. reflexivity. }
  assert (Ho' : obj_holds segs rho ms o').
  { unfold obj_holds, o', obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    split; [pose proof (urange (eval rho b')); lia|]. split.
    { intros off Hoff Hdw. replace (bv_unsigned (eval rho b') + off) with (bv_unsigned (eval rho (ob_base o)) + (off - soff rho lo' + soff rho (ob_lo o))) by lia.
      apply Hw; [lia | exact Hdw]. }
    split; [constructor|]. split.
    { intros off Hoff _. replace (bv_unsigned (eval rho b') + off) with (bv_unsigned (eval rho (ob_base o)) + (off - soff rho lo' + soff rho (ob_lo o))) by lia.
      pose proof (Hdf (off - soff rho lo' + soff rho (ob_lo o)) ltac:(lia) ltac:(rewrite Hc; intros HC; inversion HC)) as D.
      destruct (ob_dflt o); cbn [dlist_of] in Hd; try discriminate; cbn [dflt_holds] in D |- *;
        replace (off - soff rho lo' + soff rho (ob_lo o) - soff rho (ob_lo o)) with (off - soff rho lo') in D by lia; exact D. }
    destruct (ob_dflt o); cbn [dlist_of] in Hd; try discriminate; cbn [dflt_inv] in Hinv |- *; lia. }
  unfold set_objs.
  apply (smatch_set_objs_next segs rho S (tr, mkCfg ms md) _ (ss_next S) (ss_lenient S) Hsm); [|exact Hwf].
  cbn [snd cfg_ms]. rewrite Esplit in Hall, Hpd, Hfr. split; [|split].
  - apply Forall_app in Hall as [A1 A2]. apply Forall_cons_iff in A2 as [_ A3]. apply Forall_app. split; [exact A1|]. constructor; assumption.
  - eapply pairwise_disjoint_Forall2; [|exact Hpd].
    apply Forall2_app; [apply Forall2_refl_ranges|]. constructor; [exact Hrange | apply Forall2_refl_ranges].
  - intros a Ha. apply Hfr. eapply outside_all_Forall2; [|exact Ha].
    apply Forall2_app; [apply Forall2_refl_ranges|]. constructor; [exact Hrange | apply Forall2_refl_ranges].
Qed.

End DG.
