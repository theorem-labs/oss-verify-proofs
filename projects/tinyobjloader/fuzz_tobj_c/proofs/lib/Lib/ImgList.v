(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sstate"; "ss_objs"; "cell"; "ob_base"; "ob_hi"; "ob_lo"; "odefault"; "smatch"; "ss_facts"; "ss_next"; "ss_pc"; "ss_regs"; "sv"; "valuation"; "DList"; "eval"; "image_byte"; "mkObj"; "ob_cells"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "sprop"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "option"; "nat"; "list"; "Some"; "bool"; "false"; "app"; "S"; "cons"; "nil"; "prod"; "None"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.Lists.List"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "sv_has_rl"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ImgList.I"; "img_bytes"; "img_bytes_from"; "img_to_list_at"; "img_byte_d"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "sub"; "to_nat"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "map"; "nth"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I.
Variable segs : list Segment.

Definition img_byte_d (a : Z) : byte := ltac2:(tb__ "0|2|
S1bS2bQ8M0A1M1A1G1Lx;S11Vsegs;S2cQ40Va;A2A2G1R1Lb;S2cG0Z0A2X1bx2").

Definition img_bytes_from (a0 : Z) (count : nat) : list byte := ltac2:(tb__ "0|0|
S3bS1cS2bQ8A1S1cS34S35Va0;S36R1A1A2A1Lj;S3dU0Vcount;A2A4").

Definition img_bytes (rho : valuation) (o : sobj) : list byte := ltac2:(tb__ "0|1|
S32S35S2dQ40S10Vrho;S4Vo;A1A2A2S16Vrho;Vo;A2M0A2S38S37S15Vrho;Vo;A2G0A2A1A2").

Definition img_to_list_at (S : sstate) (i : nat) (l : positive) : option sstate := ltac2:(tb__ "0|5|
S1bS0A1S1bS1A1M0Lx;S2aS0S2VS;A1M1Vi;A3S0S1dS3A1M2G0Lx;S13R1A1S7G0Lx;S14R1A1S26S1A1M3G3S1fG0L_;S30Vl;VS;A2G3S1eS1S45VS;S21S0S39S0Vi;G1A3S21S0S23S0S12S4R1A1S6R1A1S5R1A1S24S3A1SfVl;A1A5S24S0A1A3S3aS0S22Vi;A1G1A3A3A3A2A2X1fx2S29G3Ll0;M4G4S28SdS1dS25S28S28A2A1S1dS18A1G3Ltmpl;Lflds;Lcnt;Lesz;X7x6S3G2G3Ll0;Lc;X1dx2Lo;G3X1bx2").

Lemma img_bytes_from_length : ltac2:(tb__ "0|0|
S28S1cS19S1cS27S2bQ8A1S32R2R1A2A2R1A3Fn;Fa0;").
Proof using . intros. unfold img_bytes_from. rewrite length_map, length_seq. reflexivity. Qed.

Lemma img_bytes_from_nth : ltac2:(tb__ "0|2|
S28S1cS1cS42R1R2A2S19S2bQ8M0A1M1S3cG1R2S32R4R3A2S2cG0Z0A2A4S34S35R4S36R2A1A2A1A3F_;Fj;Fn;Fa0;").
Proof using .
  intros a0 n j Hj. unfold img_bytes_from.
  assert (G : forall s, (j < n)%nat -> nth j (map (fun k => img_byte_d (a0 + Z.of_nat k)) (seq s n)) (Z_to_bv 8 0) = img_byte_d (a0 + Z.of_nat (s + j))).
  { revert j Hj. induction n as [|n IH]; intros j Hj s Hj'; [lia|].
    cbn [seq map]. destruct j as [|j].
    - cbn [nth]. rewrite Nat.add_0_r. reflexivity.
    - cbn [nth]. rewrite (IH j ltac:(lia) (S s) ltac:(lia)). f_equal. f_equal. lia. }
  rewrite (G 0%nat Hj). reflexivity.
Qed.

Lemma split_at_nth3 {A} : ltac2:(tb__ "0|1|
S1dVA;A1M0S1cVA;S19S1bVA;A1S2aVA;R3R2A3S1eVA;R1A2A3S19G0R4S21VA;S39VA;R3R4A3S23VA;R2S3aVA;S22R3A1R4A3A3A3A3F_;Fx;Fi;Fl;").
Proof using .
  intros l i. revert l. induction i as [|i IH]; intros [|y l] x H; cbn in *; try discriminate.
  - injection H as <-. reflexivity.
  - f_equal. exact (IH l x H).
Qed.

Lemma state_has_rl_obj : ltac2:(tb__ "0|0|
S29S1S1cS0S19S1fS30R4R3A2S20A3S19S1bS0A1S2aS0S2R4A1R3A3S1eS0R2A2A3S1aS19S1fS2fR6S4R3A1A2S20A3S1aS19S1fS2fR6S6R3A1A2S20A3S19S1fS2fR6S5R3A1A2S20A3A2A2F_;F_;Fo;Fi;FS;Fl;").
Proof using .
  intros l S i o H Hi. unfold state_has_rl in H.
  repeat (apply Bool.orb_false_iff in H as [H ?]).
  assert (Ho : obj_has_rl l o = false).
  { apply nth_error_In in Hi. destruct (obj_has_rl l o) eqn:E; [|reflexivity].
    exfalso. assert (X : existsb (obj_has_rl l) (ss_objs S) = true) by (apply existsb_exists; exists o; auto). congruence. }
  unfold obj_has_rl in Ho. repeat (apply Bool.orb_false_iff in Ho as [Ho ?]). auto.
Qed.

Theorem smatch_img_to_list : ltac2:(tb__ "0|0|
SeS1S1cS29S1S0S25S1dS3eA1S43A2S19S1bS1A1S33R6R5R4A3S1eS1R3A2A3S19S1bS0A1S2aS0S2R7A1R6A3S1eS0R3A2A3S8Vsegs;R9R8R3A4S8Vsegs;S2eRaR7S31RaR5A2A3R6R4A4F_;F_;F_;Fw;Fo;FS';Fl;Fi;FS;Frho;").
Proof using .
  intros rho S i l S' o [tr [ms md]] H Hi Hsm. unfold img_to_list_at in H. rewrite Hi in H.
  destruct (ob_cells o) eqn:Hc; [|discriminate]. destruct (ob_dflt o) eqn:Hd; try discriminate.
  destruct (state_has_rl l S) eqn:Hrl; [discriminate|]. injection H as <-.
  destruct (state_has_rl_obj l S i o Hrl Hi) as (NB & NL & NH).
  set (o' := mkObj (ob_base o) (ob_lo o) (ob_hi o) [] (DList l)).
  set (bl := img_bytes rho o). set (rho' := rho_set_rl rho l bl).
  pose proof (smatch_set_rl segs rho l bl S _ Hrl Hsm) as Hsm'.
  pose proof Hsm' as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (split_at_nth3 (ss_objs S) i o Hi) as EQ.
  assert (Hoh : obj_holds segs rho' ms o) by (eapply mem_match_nth; [exact Hmem | exact Hi]).
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (RNG : obj_range rho' o' = obj_range rho' o) by reflexivity.
  assert (Ebase : eval rho' (ob_base o) = eval rho (ob_base o)) by (subst rho'; apply eval_set_rl; exact NB).
  assert (Elo : soff rho' (ob_lo o) = soff rho (ob_lo o)) by (subst rho'; apply soff_set_rl; exact NL).
  assert (Ehi : soff rho' (ob_hi o) = soff rho (ob_hi o)) by (subst rho'; apply soff_set_rl; exact NH).
  assert (Hoh' : obj_holds segs rho' ms o').
  { destruct Hoh as (H1 & H2 & H3 & H4 & H5). rewrite Hc in *. rewrite Hd in *.
    unfold obj_holds. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi] in *.
    split; [exact H1|]. split; [exact H2|]. split; [constructor|]. split.
    - intros off Hoff Hnc. specialize (H4 off Hoff ltac:(intros C; inversion C)). cbn [dflt_holds] in H4 |- *.
      destruct H4 as [Hnone [b Hb]].
      rewrite (rd_rom segs ms _ Hrom Hnone). rewrite Hb.
      rewrite ?Elo, ?Ebase. rewrite ?Elo, ?Ehi in Hoff. rewrite ?Ebase in Hb.
      subst rho'. rewrite rho_set_rl_at. subst bl. unfold img_bytes, obj_lo_of, obj_hi_of.
      rewrite img_bytes_from_nth by lia.
      unfold img_byte_d.
      replace (bv_unsigned (eval rho (ob_base o)) + soff rho (ob_lo o) + Z.of_nat (Z.to_nat (off - soff rho (ob_lo o))))
        with (bv_unsigned (eval rho (ob_base o)) + off) by lia.
      rewrite Hb. reflexivity.
    - cbn [dflt_inv]. rewrite Elo, Ehi. rewrite Elo, Ehi in H1. subst rho'. rewrite rho_set_rl_at. subst bl. unfold img_bytes, obj_lo_of, obj_hi_of.
      rewrite img_bytes_from_length. lia. }
  unfold set_objs.
  apply (smatch_set_objs_next segs rho' S _ (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)) (ss_next S) (ss_lenient S)).
  - destruct S; exact Hsm'.
  - rewrite EQ in Hmem.
    apply mem_match_replace with (o := o).
    + exact Hmem.
    + constructor; [exact Hoh'|]. constructor.
    + destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
      rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite RNG. exact Hpd.
    + intros x. split.
      * intros Hx. exists o'. split; [cbn; auto|]. rewrite RNG. exact Hx.
      * intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite RNG in Hx. exact Hx.
  - pose proof (swf_objs_replace S (firstn i (ss_objs S)) o (skipn (Datatypes.S i) (ss_objs S)) [o'] Hwf EQ) as W.
    unfold set_objs in W. apply W. cbn [forallb]. rewrite andb_true_r.
    unfold obj_wf in *. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb dflt_wf].
    apply andb_prop in Hwfo as [X _]. apply andb_prop in X as [X _]. rewrite X. reflexivity.
Qed.

Lemma img_to_list_facts : ltac2:(tb__ "0|0|
S1S1cS29S1S19S1bS1A1S33R4R3R2A3S1eS1R1A2A3S1aS19S29SaR2A1SaR5A1A3S1aS19S1dS17A1S9R2A1S9R5A1A3S1aS19S1dSdA1ScR2A1ScR5A1A3S19S28SbR2A1SbR5A1A3A2A2A2F_;FS';Fl;Fi;FS;").
Proof using .
  intros S i l S' H. unfold img_to_list_at in H.
  destruct (nth_error (ss_objs S) i) as [o|]; [|discriminate]. destruct (ob_cells o); [|discriminate].
  destruct (ob_dflt o); try discriminate. destruct (state_has_rl l S); [discriminate|]. injection H as <-. repeat split; reflexivity.
Qed.

Lemma SPJ_img_to_list : ltac2:(tb__ "0|0|
S41SeS1S1cS29S1S0S44S19S1bS1A1S33R6R5R4A3S1eS1R3A2A3S19S1bS0A1S2aS0S2R7A1R6A3S1eS0R3A2A3S1dS3eA1S3fRcRbR2R1A3RdS2eRcR9S31RcR7A2A3R3R2A3F_;Fmd;Ftr;S40Vsegs;RbR9RaR4A5S40Vsegs;RcR7S2eRbR8S31RbR6A2A3R5A5F_;F_;F_;F_;Fw;Fo;FS';Fl;Fi;FS;Frho;FJ;").
Proof using .
  intros J rho S i l S' o w H Hi HJ [Hsm HK]. split; [eapply smatch_img_to_list; eauto | apply HJ; exact HK].
Qed.
End I.
