(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "soff"; "sstate"; "mkObj"; "valuation"; "cell"; "eval"; "odefault"; "rd"; "DList"; "DUnknown"; "obj_holds"; "smatch"; "ss_objs"; "rl"; "tfact"; "@Corelib.Init.Datatypes"; "option"; "list"; "nat"; "Some"; "bool"; "length"; "pair"; "None"; "S"; "app"; "cons"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "of_nat"; "to_nat"; "le"; "lt"; "max"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymMaterialize.WithSegs"; "read_range"; "materialized_bytes"; "materialize_at"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "map"; "seq"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "nth_error"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymCall SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition read_range (ms : machine_state) (a0 : Z) (n : nat) : list byte := ltac2:(tb__ "0|2|
S31S13S23Q8M0A1M1S13S11G1A1G1Lx;S9Vms;S22Q40S25Va0;S27R1A1A2A2A2G1R1Lx;S22G0Z0A2X11x2Li;S32U0Vn;A2A4").

Lemma read_range_length : ltac2:(tb__ "0|0|
S21S1fS13S1dS13S16S23Q8A1S2cR3R2R1A3A2R1A3Fn;Fa0;Fms;").
Proof using . intros. unfold read_range. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_map_lt : forall {A B} (f : A -> B) (l : list A) (d : A) (d' : B) i,
  (i < length l)%nat -> nth i (map f l) d' = f (nth i l d).
Proof using .
  intros A B f l. induction l as [|x t IH]; intros d d' i Hi; cbn in Hi; [lia|].
  destruct i; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma read_range_nth : ltac2:(tb__ "0|3|
S21S1fS13S13S37R1R2A2S1dS23Q8M0A1M1S2fG1R2S2cR5R4R3A3S22G0Z0A2M2A4S11G1A1G1Lx;S9R5S22Q40S25R4S27R2A1A2A2A2G1R1Lx;G2X11x2A3F_;Fi;Fn;Fa0;Fms;").
Proof using .
  intros ms a0 n i Hi. unfold read_range.
  rewrite (nth_map_lt _ _ 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma obj_holds_materialize : ltac2:(tb__ "0|1|
S5S21S0S0S0S12S6A1S20ScVsegs;R7R6S4R5R4R3R2SbA5A4S1dS12S23Q8A1A1SfR8R2A2S2cR7S25S24Q40S7R8R6A2A2S2R8R5A2M0A2S28S26S2R8R4A2G0A2A1A3A3ScVsegs;R9R8S4R7R6R5R4SaR3A1A5A4F_;F_;Fl;Fcells;Fehi;Felo;Fbase;Fms;Frho;").
Proof using .
  intros rho ms base elo ehi cells l Ho Hl.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho |- *.
  cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Ho |- *.
  destruct Ho as (Hb & Hw & Hc & Hd & _).
  split; [exact Hb|]. split; [exact Hw|]. split; [exact Hc|]. split.
  - intros off Hoff Hnc. cbn [dflt_holds]. specialize (Hd off Hoff Hnc). cbn [dflt_holds] in Hd.
    destruct Hd as [b0 Hb0]. rewrite Hb0. f_equal. rewrite Hl.
    rewrite read_range_nth by lia.
    replace (bv_unsigned (eval rho base) + soff rho elo + Z.of_nat (Z.to_nat (off - soff rho elo)))
      with (bv_unsigned (eval rho base) + off) by lia.
    rewrite Hb0. reflexivity.
  - cbn [dflt_inv]. rewrite Hl, read_range_length. lia.
Qed.

Definition materialize_at (S : sstate) (k : nat) (l : positive) : option sstate := ltac2:(tb__ "0|4|
S11S1A1S11S3A1M0Lx;S36S1SeVS;A1M1Vk;A3S1S1G0Ls;R1S0S0S0S12S6A1S8S8G0Lob_dflt;R1S15G0L_;S3bVl;VS;A2S18S3A1M2S14S3S3cVS;S1aS1S30S1Vk;G1A3S1bS1S4R5R4R3R2SaVl;A1A5S33S1S19Vk;A1G1A3A3A3A2A2X15x2G2G2S20G2Ll0;M3G3S1fS0S12S1cS1fS1fA2A1S12S10A1G2Ltmpl;Lflds;Lcnt;Lesz;X8x6Lob_dflt;Lcells;Lehi;Lelo;Lbase;X1x1Ls;G2X11x2").

Definition materialized_bytes (rho : valuation) (ms : machine_state) (base elo ehi : sv) : list byte := ltac2:(tb__ "0|1|
S2cVms;S25S24Q40S7Vrho;Vbase;A2A2S2Vrho;Velo;A2M0A2S28S26S2Vrho;Vehi;A2G0A2A1A3").

Theorem smatch_materialize : ltac2:(tb__ "0|1|
S5S3S13S20S3S12S39A1M0S21S38S0S0S0S12S6A1S1dS11S3A1S2eRbRaR9A3S14S3R8A2A3S1dS11S1A1S36S1SeRcA1RbA3S14S1S4R5R4R3R2SbA5A2A3SdVsegs;ReRdS17G0S34R9S35R8R7A2A4A4SdVsegs;S3aRfRcS2dRfR9R7R6R5A5A3RbS17G0S34RaS35R9R8A2A4A4F_;F_;F_;Fcells;Fehi;Felo;Fbase;Fmd;Fms;Ftr;FS';Fl;Fk;FS;Frho;").
Proof using .
  intros rho S k l S' tr ms md base elo ehi cells Hm Hnth Hsm.
  unfold materialize_at in Hm. rewrite Hnth in Hm.
  destruct (state_has_rl l S) eqn:Hno; [discriminate|]. injection Hm as <-.
  set (L := materialized_bytes rho ms base elo ehi). set (rho' := rho_set_rl rho l L).
  pose proof (smatch_set_rl segs rho l L S (tr, mkCfg ms md) Hno Hsm) as Hsm'.
  change (smatch segs rho' S (tr, mkCfg ms md)) in Hsm'.
  pose proof (smatch_swf segs _ _ _ Hsm') as Hwf.
  destruct Hsm' as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hnth) as EQ.

  pose proof Hno as Hno0. unfold state_has_rl in Hno.
  apply Bool.orb_false_iff in Hno as [Hno _]. apply Bool.orb_false_iff in Hno as [_ Hob].
  pose proof (existsb_false_forall _ _ _ Hob (nth_error_In _ _ Hnth)) as Hok.
  destruct (obj_has_rl_split l _ Hok) as (Hb0 & Hlo0 & Hhi0 & _ & _).
  cbn [ob_base ob_lo ob_hi] in Hb0, Hlo0, Hhi0.
  assert (Hoh : obj_holds segs rho' ms (mkObj base elo ehi cells DUnknown)).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall].
    inversion Hall; auto. }
  assert (Hoh' : obj_holds segs rho' ms (mkObj base elo ehi cells (DList l))).
  { apply obj_holds_materialize; [exact Hoh|].
    subst rho'. rewrite rho_set_rl_at. subst L. unfold materialized_bytes.
    rewrite (eval_set_rl rho l _ base Hb0), (soff_set_rl rho l _ elo Hlo0), (soff_set_rl rho l _ ehi Hhi0).
    reflexivity. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn k (ss_objs S) ++ mkObj base elo ehi cells (DList l) :: skipn (Datatypes.S k) (ss_objs S))
      with (firstn k (ss_objs S) ++ [mkObj base elo ehi cells (DList l)] ++ skipn (Datatypes.S k) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |].
    pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _].
    cbn [forallb]. unfold obj_wf in W |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_wf] in W |- *.
    rewrite W. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn k (ss_objs S) ++ mkObj base elo ehi cells (DList l) :: skipn (Datatypes.S k) (ss_objs S))
    with (firstn k (ss_objs S) ++ [mkObj base elo ehi cells (DList l)] ++ skipn (Datatypes.S k) (ss_objs S)).
  apply mem_match_replace with (o := mkObj base elo ehi cells DUnknown).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. exact Hpd.
  - intros x. split.
    + intros Hx. exists (mkObj base elo ehi cells (DList l)). split; [cbn; auto|]. exact Hx.
    + intros (o' & [<-|[]] & Hx). exact Hx.
Qed.

Lemma materialized_bytes_length : ltac2:(tb__ "0|0|
S5S21S0S0S0S1dS1fS27S16S23Q8A1S2dR5R4R3R2R1A5A2A1S2bZ0S26S2R5R1A2S2R5R2A2A2A2A3Fehi;Felo;Fbase;Fms;Frho;").
Proof using .
  intros. unfold materialized_bytes. rewrite read_range_length. lia.
Qed.

Lemma materialized_bytes_nth : ltac2:(tb__ "0|3|
S5S21S0S0S0S1fS23Q8M0A1M1S1eS29S2R7R4A2R2A2S2aR2S2R7R3A2A2A2S1dS11G1A1S9R7S22Q40M2S25S24G2S7R8R6A2A2R3A2A2A2S14G1R2A2A3S1dG1S2fG1S28S26R4S2R9R6A2A2A1S2dR9R8R7R6R5A5S22G0Z0A2A4R3A3F_;F_;Fb;Foff;Fehi;Felo;Fbase;Fms;Frho;").
Proof using .
  intros rho ms base elo ehi off b Hoff Hrd. unfold materialized_bytes.
  rewrite read_range_nth by lia.
  replace (bv_unsigned (eval rho base) + soff rho elo + Z.of_nat (Z.to_nat (off - soff rho elo)))
    with (bv_unsigned (eval rho base) + off) by lia.
  rewrite Hrd. reflexivity.
Qed.

End WithSegs.
