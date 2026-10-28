(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ZeroObj.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zk_zero (c : cell) : bool :=
  match c_val c with SLit 0 => true | _ => false end.

Definition kcell_covers (c : cell) (off : Z) : bool :=
  match c_off c with
  | SLit z => Z.leb (snorm z) off && Z.ltb off (snorm z + c_width c)
  | _ => false
  end.

Fixpoint zkcover_from (cells keep : list cell) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      (existsb (fun c => zcell_covers c off) cells || existsb (fun c => kcell_covers c off) keep)
      && zkcover_from cells keep (off + 1) n'
  end.

Definition zk_keep (cells : list cell) : list cell := List.filter (fun c => negb (zk_zero c)) cells.

Definition zero_keep (o : sobj) : option sobj :=
  match ob_lo o, ob_hi o, ob_dflt o with
  | SLit lo, SLit hi, DUnknown =>
      if zkcover_from (ob_cells o) (zk_keep (ob_cells o)) (snorm lo) (Z.to_nat (snorm hi - snorm lo))
      then Some (mkObj (ob_base o) (SLit lo) (SLit hi) (zk_keep (ob_cells o)) DZero)
      else None
  | _, _, _ => None
  end.

Definition zero_keep_at (S : sstate) (i : nat) : option sstate :=
  match nth_error (ss_objs S) i with
  | Some o =>
      match zero_keep o with
      | Some o' => Some (set_objs S (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)))
      | None => None
      end
  | None => None
  end.

Lemma zkcover_from_spec : forall cells keep n off x,
  zkcover_from cells keep off n = true -> off <= x < off + Z.of_nat n ->
  (exists c, In c cells /\ zcell_covers c x = true) \/ (exists c, In c keep /\ kcell_covers c x = true).
Proof.
  intros cells keep n. induction n as [|n IH]; intros off x H Hx; [lia|].
  cbn [zkcover_from] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x off) as [->|Hne].
  - apply orb_prop in H1 as [H1|H1]; apply existsb_exists in H1 as (c & Hin & Hc); [left|right]; exists c; auto.
  - apply (IH (off + 1)); [exact H2 | lia].
Qed.

Lemma forallb_filter_keep : forall (A : Type) (f g : A -> bool) l,
  forallb f l = true -> forallb f (List.filter g l) = true.
Proof.
  intros A f g l H. apply forallb_forall. intros x Hx. apply filter_In in Hx as [Hx _].
  exact (proj1 (forallb_forall _ _) H x Hx).
Qed.

Section ZK.
Variable segs : list Segment.

Lemma zero_keep_holds : forall rho ms o o',
  zero_keep o = Some o' -> obj_holds segs rho ms o -> obj_holds segs rho ms o'.
Proof.
  intros rho ms o o' Hz Ho. unfold zero_keep in Hz.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  destruct (ob_dflt o) eqn:Ed; try discriminate.
  destruct (zkcover_from (ob_cells o) (zk_keep (ob_cells o)) (snorm lo) (Z.to_nat (snorm hi - snorm lo))) eqn:Hc;
    [|discriminate].
  injection Hz as <-.
  pose proof Ho as (Hb & Hw & Hcells & Hd & Hdl). unfold obj_lo_of, obj_hi_of in *.
  rewrite Elo, Ehi in *. rewrite !soff_lit in *.
  unfold obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi].
  rewrite !soff_lit. split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff | rewrite Ed; reflexivity]|].
  split.
  { apply Forall_forall. intros c Hin. apply filter_In in Hin as [Hin _].
    exact (proj1 (Forall_forall _ _) Hcells c Hin). }
  split; [|exact I].
  intros off Hoff Hnc. cbn [dflt_holds].
  destruct (zkcover_from_spec _ _ _ _ off Hc ltac:(lia)) as [(c & Hin & Hzc)|(c & Hin & Hkc)].
  - unfold zcell_covers in Hzc.
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
  - exfalso. apply Hnc. apply Exists_exists. exists c. split; [exact Hin|].
    unfold kcell_covers in Hkc. unfold in_cell.
    destruct (c_off c) as [z| | | | | | |] eqn:Eco; try discriminate.
    rewrite soff_lit. apply andb_prop in Hkc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma smatch_zero_keep : forall rho S i S' w,
  zero_keep_at S i = Some S' -> smatch segs rho S w -> smatch segs rho S' w.
Proof.
  intros rho S i S' [tr [ms md]] Hz Hsm.
  unfold zero_keep_at in Hz.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (zero_keep o) as [o'|] eqn:Ho; [|discriminate]. injection Hz as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (SHAPE : ob_base o' = ob_base o /\ ob_lo o' = ob_lo o /\ ob_hi o' = ob_hi o
                  /\ ob_cells o' = zk_keep (ob_cells o) /\ ob_dflt o' = DZero).
  { unfold zero_keep in Ho. destruct (ob_lo o); try discriminate. destruct (ob_hi o); try discriminate.
    destruct (ob_dflt o); try discriminate.
    destruct (zkcover_from _ _ _ _); [|discriminate].
    injection Ho as <-. cbn. auto. }
  destruct SHAPE as (Sb & Slo & Shi & Sc & Sd).
  assert (RG : obj_range rho o' = obj_range rho o).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Sb, Slo, Shi. reflexivity. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S))
      with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |].
    pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _].
    cbn [forallb]. unfold obj_wf in W |- *. rewrite Sb, Slo, Shi, Sc, Sd.
    apply andb_prop in W as [W _]. apply andb_prop in W as [W Wc]. rewrite W.
    unfold zk_keep. rewrite (forallb_filter_keep _ _ _ _ Wc). reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S))
    with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [|constructor]. eapply zero_keep_holds; [exact Ho|].
    destruct Hmem as (Hall & _ & _). apply Forall_app in Hall as [_ Hall]. inversion Hall; auto.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite RG. exact Hpd.
  - intros x. rewrite <- RG. split.
    + intros Hx. exists o'. split; [cbn; auto | exact Hx].
    + intros (o1 & [<-|[]] & Hx). exact Hx.
Qed.

Lemma SPJ_zero_keep : forall J rho S i S' w,
  zero_keep_at S i = Some S' -> SPJ segs J S rho w -> SPJ segs J S' rho w.
Proof.
  intros J rho S i S' w Hz [Hs HJ]. split; [|exact HJ]. exact (smatch_zero_keep rho S i S' w Hz Hs).
Qed.

End ZK.
