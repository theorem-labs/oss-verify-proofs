(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rm"; "smatch"; "sstate"; "sv"; "ss_objs"; "valuation"; "mkSS"; "obj_range"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "SLit"; "eval"; "rom_ok"; "DUnknown"; "enc_bytes"; "image_byte"; "mem_frame"; "mkObj"; "obj_holds"; "outside_all"; "ranges_disjoint"; "rd"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "option"; "bool"; "list"; "nat"; "true"; "Some"; "app"; "cons"; "nil"; "None"; "false"; "fst"; "pair"; "snd"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.WithSegs"; "rd_of"; "in_rng"; "wok_of"; "carved"; "cells_in_view"; "cells_inside"; "lit_cells"; "wseg_addr"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_ms"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_writable"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "find_segment"; "machine_state"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundM SymFrame SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition wseg_addr (a : word) : bool := ltac2:(tb__ "0|0|
S24S4cA1S25Lx;S4fVsegs;S34Q40Va;A2Z1A3S4cS4dR1A1Lseg;S2eX24x2").
Definition rd_of (m : word -> option byte) (a : word) : option byte := ltac2:(tb__ "0|2|
S24S32Q8A1M0A1M1G1Lx;Vm;Va;A1G0S29G0R1A2Lb;S16Vsegs;Va;A2X24x2").
Definition wok_of (m : word -> option byte) (a : word) : bool := ltac2:(tb__ "0|1|
S24S32Q8A1M0A1S25Lx;Vm;Va;A1G0S28Lb;S43Va;A1X24x2").

Fixpoint lit_cells (cs : list (Z * nat * sv)) : list cell :=
  match cs with
  | [] => []
  | (off, k, v) :: t => mkCell (SLit off) (Z.of_nat k) v :: lit_cells t
  end.

Definition cells_in_view (rho : valuation) (rdv : word -> option byte) (b : Z) (cs : list (Z * nat * sv)) : Prop := ltac2:(tb__ "0|4|
S44S23S23S21S27A2M0S4A2M1G1G1OLc;R1G0S4G0OLp;R2S21S27S27S4bR1R2A2S1dS24S32Q8M2A1M3A1Vrdv;S33Q40S35S35Vb;R4A2S38R2A1A2A2A1S29G3S45G3R2S15R3S12Vrho;R5A2A2S33G2Z0A2A4A2A3F_;Fj;Lk;Loff;X23x1Lv;Lp;X23x1Lc;Vcs;A3").

Definition cells_inside (lo hi : Z) (cs : list (Z * nat * sv)) : Prop := ltac2:(tb__ "0|2|
S44S23S23S21S27A2M0S4A2M1G1G1OLc;R1G0S4G0OLp;R2S21S27S1eS36Vlo;R2A2S1eS36S35R2S38R1A1A2Vhi;A2S1eS4aU1R1A2S4aR1U8A2A2A2A2Lk;Loff;X23x1Lv;Lp;X23x1Lc;Vcs;A3").

Definition carved (base : sv) (lo hi : Z) (cs : list (Z * nat * sv)) : sobj := ltac2:(tb__ "0|0|
S18Vbase;S11Vlo;A1S11Vhi;A1S42Vcs;A1S14A5").

Lemma wview_of_views : ltac2:(tb__ "0|3|
S32Q40A1M0S24S32Q8A1M1A1M2F_;G0S1dS25S3eR2R1A2S28A3S1fG1G1S1dG2S3cR4R3A2S29G1R1A2A3Lb;A2S20S1dG2S51Vsegs;R4R3A3S2dG1A1A3A1F_;F_;Fa;Fm;").
Proof using .
  intros m a Hw [b Hb]. unfold wview, wok_of, rd_of in *.
  destruct (m a) as [x|]; [discriminate|].
  unfold wseg_addr in Hw. unfold image_byte, memory_read in Hb.
  replace (Z.of_N 1) with 1 in Hb by reflexivity.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|discriminate].
  rewrite Hw. destruct (seg_readable seg); [|discriminate].
  replace (N.to_nat 1) with 1%nat in Hb by reflexivity. cbn [segment_read_bytes] in Hb.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))); [discriminate|].
  discriminate.
Qed.

Lemma rd_frame : ltac2:(tb__ "0|0|
S6S26S0A1S50S32Q40A1S13Vsegs;R2A2S17R5R4R3A3S1aR6R5R3A3S1dS24S32Q8A1A1S1cR5R4A2S3cS1R7A1R4A2A3F_;F_;F_;Fa;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms a Hrom Hfr Hout. unfold rd, ms_read_byte, rd_of. rewrite (Hfr a Hout), (Hrom a). reflexivity.
Qed.

Lemma smatch_carve_obj : ltac2:(tb__ "0|4|
S6S3S23S26S48A1S47A2S4S21S21S26S23S23S21S27A2S4A2A1S22S2Vsegs;R8R7R6A4S7SdR8A1SeR8A1SbR8A1SaR8A1SfR8A1S2aS0S5R8A1S2bS0S3fR6R5R4R3A4S2cS0A1A3A3S9R8A1R2ScR8A1A9S3S1dS25S10R1A1S28A3S34Q40M0S12RbR8A2A2S21S36S3aS39Z2M1Z3fA2M2A1R8A2S36R9R8A2S37R9G2A2S37S3bRaRbA2G2A2S36Z0S35R5RcA2A2S36S35R6RcA2S39G1Z40A2A2S41ReRdRcA3S44S0S0S1bS8R14R1A2S30S21S21S35R9R10A2S35R9RfA2A4A2Lo';S5R12A1A3S21S1eS36R11R1A2S37R1R10A2A2S1eS1dS25S3eS1R16A1S33G0S35RbR2A2A2A2S28A3S1fS32Q8A1M3G3S1dS24G3A1S3cS1R17A1S33G0S35RcR3A2A2A2S29G3R1A2A3Lx;A2A2F_;Foff;S40R15S3cS1R15A1A1RaRfA4S2Vsegs;R16RdR14A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fcs;Fhi;Flo;Fbase;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] base lo hi cs nx Hsm S' Hwf b Hlo Hlh Hhi Hhl Hb0 Hb1 Hins Hdisj Hview Hcells.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).
  assert (OUT : forall off, lo <= off < hi -> outside_all rho (ss_objs S) (Z_to_bv 64 (b + off))).
  { intros off Hoff. eapply ranges_disjoint_outside; [exact Hdisj|]. rewrite u64_of_sum by lia. lia. }
  assert (RD : forall off, lo <= off < hi -> rd ms (Z_to_bv 64 (b + off)) = rd_of (rm rho) (Z_to_bv 64 (b + off))).
  { intros off Hoff. apply (rd_frame rho (ss_objs S)); auto. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs].
  assert (RNG : obj_range rho (carved base lo hi cs) = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi]. fold b.
    rewrite !soff_lit_small by lia. reflexivity. }
  split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
    rewrite !soff_lit_small by lia.
    split; [lia|]. split.
    { intros off Hoff _. unfold wview. rewrite (Hfr _ (OUT off Hoff)).
      destruct (Hview off Hoff) as [W R]. exact (wview_of_views (rm rho) _ W R). }
    split.
    {
      clear RNG Hwf Hdisj. subst S'. revert Hins Hcells. induction cs as [|[[o k] v] t IH]; intros Hins Hcells; [constructor|].
      apply Forall_cons_iff in Hins as [Hokv Hins']. destruct Hokv as (Ho1 & Ho2 & Hk).
      apply Forall_cons_iff in Hcells as [Hcv Hcells'].
      constructor; [|apply IH; assumption].
      unfold cell_holds. cbn [c_off c_width c_val]. rewrite !soff_lit_small by lia. rewrite Nat2Z.id.
      split; [lia|]. split; [lia|].
      apply rd_bytes_of_nth.
      - apply enc_bytes_length.
      - rewrite oaddr_unsigned by lia. fold b. lia.
      - intros j Hj. rewrite oaddr_unsigned by lia. fold b.
        replace (b + o + Z.of_nat j) with (b + (o + Z.of_nat j)) by lia.
        rewrite (RD (o + Z.of_nat j)) by lia.
        replace (b + (o + Z.of_nat j)) with (b + o + Z.of_nat j) by lia. exact (Hcv j Hj). }
    split; [|exact I].
    intros off Hoff _. cbn [dflt_holds]. rewrite (RD off Hoff). destruct (Hview off Hoff) as [_ [x Hx]]. exists x. exact Hx.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite RNG. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

Definition in_rng (r : Z * Z) (a : Z) : Prop := ltac2:(tb__ "0|0|
S1eS36S2fS21S21Vr;A3Va;A2S37Va;S31S21S21Vr;A3A2A2").

Lemma smatch_drop_last : ltac2:(tb__ "0|2|
S6S3S23S26S48A1S47A2S26S0A1M0S0S22S2Vsegs;R6R5R4A4S1dG0S5R6A1S2aS0R4S2bS0R3S2cS0A1A3A3A3S7SdR7A1SeR7A1SbR7A1SaR7A1SfR7A1R5S9R7A1R3ScR7A1A9S3S1dS25S10R1A1S28A3S32Q40M1A1S3dS8RbR7A2S34G1R1A2A2S1dS24S32Q8A1A1S4eS46S49RaA1A1R2A2S1RcR2A2A3F_;Fa;S2Vsegs;RbR3R9A4F_;F_;TS';F_;F_;Fnx;Fo;Fobjs;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] objs o nx Hsm Hobjs S' Hwf Hagree.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model w_cfg] in *.
  rewrite Hobjs in Hm. destruct Hm as (Hall & Hpd & Hfr).
  apply Forall_app in Hall as [Hall _].
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [exact Hall|]. split; [eapply pairwise_disjoint_app_l; exact Hpd|].
  intros a Ha.
  destruct (Z_lt_dec (bv_unsigned a) (fst (obj_range rho o))) as [Hlt|Hge];
    [|destruct (Z_lt_dec (bv_unsigned a) (snd (obj_range rho o))) as [Hlt2|Hge2]].
  - apply Hfr. apply outside_all_app. split; [exact Ha|]. constructor; [|constructor]. cbn zeta. lia.
  - apply Hagree. unfold in_rng. lia.
  - apply Hfr. apply outside_all_app. split; [exact Ha|]. constructor; [|constructor]. cbn zeta. lia.
Qed.

Lemma smatch_release_obj : ltac2:(tb__ "0|8|
S6S3S23S26S48A1S47A2S26S0A1M0S0S22S2Vsegs;R6R5R4A4S1dG0S5R6A1S2aS0R4S2bS0R3S2cS0A1A3A3A3S7SdR7A1SeR7A1SbR7A1SaR7A1SfR7A1R5S9R7A1R3ScR7A1A9S3S1dS25S10R1A1S28A3S1fS32Q40M1A1M2S24S32Q8A1A1M3F_;M4G4S1eS2Vsegs;S52RbR1A2R3R9A4S1eG2S20S3dS8RcR8A2S34G1R1A2A2M5A1S1dG3R3R2A1M6S1RdR2A2A3F_;Fa;S1eG2G5S1dG3G6S4eS46S49RbA1A1R2A2A3F_;Fa;S1eS19Vsegs;RbS46S49R9A1A1M7R7A4S13Vsegs;G7A2A2A2A2A2Lm';A2F_;TS';F_;F_;Fnx;Fo;Fobjs;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] objs o nx Hsm Hobjs S' Hwf.
  set (m' := fun a => if in_ranges_dec rho [o] a then ms_mem ms a else rm rho a).
  exists m'.
  pose proof Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model w_cfg] in *.
  pose proof Hm as (Hall & Hpd & Hfr). rewrite Hobjs in Hall. apply Forall_app in Hall as [_ Ho].
  inversion Ho as [|x l Hoh _]; subst. clear Ho.
  assert (IN1 : forall a, in_ranges rho [o] a <-> in_rng (obj_range rho o) (bv_unsigned a)).
  { intros a. unfold in_ranges, in_rng. split.
    - intros (o' & [<-|[]] & H). exact H.
    - intros H. exists o. split; [left; reflexivity | exact H]. }
  assert (M'in : forall a, in_rng (obj_range rho o) (bv_unsigned a) -> m' a = ms_mem ms a).
  { intros a Ha. subst m'. cbn beta. destruct (in_ranges_dec rho [o] a) as [|Hn]; [reflexivity|]. exfalso. apply Hn. apply IN1. exact Ha. }
  assert (M'out : forall a, ~ in_rng (obj_range rho o) (bv_unsigned a) -> m' a = rm rho a).
  { intros a Ha. subst m'. cbn beta. destruct (in_ranges_dec rho [o] a) as [Hi|]; [|reflexivity]. exfalso. apply Ha. apply IN1. exact Hi. }
  split; [|split; [exact M'out | split; [exact M'in | split; [exact Hoh | exact Hrom]]]].
  assert (Hsm1 : smatch segs (set_rm rho m') S (tr, {| cfg_ms := ms; cfg_model := md |})).
  { unfold set_rm. apply smatch_set_rm; [|exact Hsm]. intros a Ha. apply M'out.
    rewrite Hobjs in Ha. apply outside_all_app in Ha as [_ Ha]. inversion Ha as [|x l Hx _]; subst.
    unfold in_rng. exact Hx. }
  apply (smatch_drop_last (set_rm rho m') S _ objs o nx Hsm1 Hobjs Hwf).
  cbn [cfg_ms w_cfg snd]. intros a Ha. rewrite obj_range_set_rm in Ha. cbn [set_rm rm]. symmetry. apply M'in. exact Ha.
Qed.

End WithSegs.
