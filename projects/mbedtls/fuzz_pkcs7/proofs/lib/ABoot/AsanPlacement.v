(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanCeil PlacementSearch.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanPlacement () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.iv_overlap"; "Corelib.Init.Datatypes.true"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "live_at"; "Stdlib.ZArith.BinInt.Z.add"; "gap_weight"; "Stdlib.Lists.List.filter"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "OSSVerify.KrLib.ABoot.AsanCeil.bottomup_floor"; "OSSVerify.KrLib.ABoot.AsanCeil.alloc_ceiling"; "stdpp.bitvector.definitions.Z_to_bv"; "Gap.scan_inv"; "Corelib.Init.Logic.or"; "Gap.gap_at"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "gw_sizes"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "OSSVerify.KrLib.ABoot.AsanCeil.hint_placement_ok_b"; "ledger_split"; "Corelib.Init.Datatypes.cons"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "OSSVerify.KrLib.ABoot.AsanCeil.placement_ok_b"; "Stdlib.ZArith.BinInt.Z.min"; "kHighMemBeg"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fg_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. exact Hz.
Qed.

Lemma fg_alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

Lemma fg_u64_range : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.

(* [comment removed for export] *)
Lemma page_multiple_eq : forall z, z mod page_size = 0 -> z = z / 4096 * 4096.
Proof.
  intros z Hz. unfold page_size in Hz.
  pose proof (Z.div_mod z 4096 ltac:(lia)). lia.
Qed.

Lemma fg_region_free_false : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Plo,(2.&40.)Pn,(2.&40.)P,(3.$4.(5.R3.R2.R1.)$6.)(7.(2.&40.)Lb,(2.&40.)(7.(2.&40.)Ls,(2.&40.)(8.(9.(1.(2.&40.)(2.&40.))(:.(2.&40.)(2.&40.)R2.R1.)R6.)(3.$4.(;.R5.R4.R2.R1.)$<.))))")
(* [comment removed for export] *).
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - destruct (IH lo n H) as (b' & s' & Hin & Hov).
    exists b', s'. split; [now right|exact Hov].
Qed.

(* [comment removed for export] *)
Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Lemma gap_weight_app : forall nZ l1 l2,
  gap_weight nZ (l1 ++ l2) = gap_weight nZ l1 + gap_weight nZ l2.
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn; [reflexivity|rewrite IH; lia]. Qed.

Lemma gap_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.

(* [comment removed for export] *)
Definition live_at (c : Z) (p : word * word) : bool :=
  c <? bv_unsigned (fst p) + bv_unsigned (snd p).

Lemma gap_weight_filter_le : forall nZ f l, 0 <= nZ ->
  gap_weight nZ (List.filter f l) <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
  destruct (f (b, s)); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma live_weight_step : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "PnZ,$=.Pl,(0.(1.(2.&40.)(2.&40.)))Pc,$=.Pc',$=.Pb,(2.&40.)Ps,(2.&40.)P,(>.=R6.)P,(>.R5.R4.)P,(9.(1.(2.&40.)(2.&40.))(:.(2.&40.)(2.&40.)R4.R3.)R7.)P,(3.$4.(?.R7.(:.(2.&40.)(2.&40.)R5.R4.))$<.)P,(3.$4.(?.R7.(:.(2.&40.)(2.&40.)R6.R5.))$6.)(8.(>.(10.(11.R;.(12.(1.(2.&40.)(2.&40.))(?.R8.)R:.))(10.(10.(13.&40.R6.)R;.)+???.))(11.R;.(12.(1.(2.&40.)(2.&40.))(?.R9.)R:.)))(14.(15.(1.(2.&40.)(2.&40.))(12.(1.(2.&40.)(2.&40.))(?.R8.)R:.))(15.(1.(2.&40.)(2.&40.))(12.(1.(2.&40.)(2.&40.))(?.R9.)R:.))))")
(* [comment removed for export] *).
Proof.
  intros nZ l c c' b s HnZ Hcc'.
  induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
  assert (Hmono : forall p, live_at c' p = true -> live_at c p = true).
  { intros [x y] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
  assert (Hle : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
                /\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
  { clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
    pose proof (bv_unsigned_in_range 64 y).
    destruct (live_at c' (x, y)) eqn:E'.
    - rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
    - destruct (live_at c (x, y)); cbn; destruct IHl; split; try lia. }
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
    destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
  - destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
    pose proof (bv_unsigned_in_range 64 s0).
    destruct (live_at c' (b0, s0)) eqn:E'.
    + rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
    + destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Gap.
  Variable L : list (word * word).
  Variable nZ : Z.
  Hypothesis HnZ : 0 <= nZ.

  (* [comment removed for export] *)
  Definition scan_inv (c : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "(8.(3.$=.(16.O1.$17.)=)(8.(>.$18.O1.)(>.(10.(10.O1.VnZ,)(11.VnZ,(12.(1.(2.&40.)(2.&40.))(?.O1.)VL,)))$19.)))")
(* [comment removed for export] *).

  Definition gap_at (c : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "(8.(3.$=.(16.O1.$17.)=)(8.(>.$18.O1.)(8.(>.(10.O1.VnZ,)$19.)(3.$4.(5.VL,(1:.&40.O1.)(1:.&40.VnZ,))$<.))))")
(* [comment removed for export] *).

  #[using="HnZ"] Lemma scan_ok_or_step : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Pc,$=.P,(1;.R1.)(1<.(1=.R2.)(7.$=.Lc',$=.(8.(1;.R1.)(14.(15.(1.(2.&40.)(2.&40.))(12.(1.(2.&40.)(2.&40.))(?.R1.)VL,))(15.(1.(2.&40.)(2.&40.))(12.(1.(2.&40.)(2.&40.))(?.R3.)VL,))))))")
(* [comment removed for export] *).
  Proof.
    intros c (Hal & Hfl & Hw).
    pose proof fg_alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (page_round_up_Z_ge (B + S)) as Hge.
      assert (Hle : c' <= B + S + 4095).
      { unfold c', page_round_up_Z, page_size.
        pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
      assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply page_round_up_Z_aligned|].
      split; lia.
  Qed.

  #[using="HnZ"] Lemma scan : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_inv c ->
    exists g, gap_at g.
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
      exists c. exact Hok.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
      + exists c. exact Hok.
      + apply (IH c'); [lia|exact Hinv'].
  Qed.

  (* [comment removed for export] *)
  #[using="HnZ"] Theorem free_gap_of_slack : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "P,(>.(10.(10.$18.VnZ,)(11.VnZ,VL,))$19.)(7.$=.Lg,$=.(8.(3.$=.(16.R1.$17.)=)(8.(>.$18.R1.)(8.(>.(10.R1.VnZ,)$19.)(3.$4.(5.VL,(1:.&40.R1.)(1:.&40.VnZ,))$<.)))))")
(* [comment removed for export] *).
  Proof.
    intros Hslack.
    assert (Hinv : scan_inv bottomup_floor).
    { split; [rewrite bottomup_floor_val; reflexivity|]. split; [lia|].
      pose proof (gap_weight_filter_le nZ (live_at bottomup_floor) L HnZ). lia. }
    exact (scan _ bottomup_floor (le_n _) Hinv).
  Qed.
End Gap.

(* [comment removed for export] *)
Lemma gap_weight_bound : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "PnZ,$=.PN,$=.Pl,(0.(1.(2.&40.)(2.&40.)))P,(>.=R3.)P,(1>.(1.(2.&40.)(2.&40.))Lp,(1.(2.&40.)(2.&40.))(>.(13.&40.(1?.(2.&40.)(2.&40.)R1.))R4.)R2.)(>.(11.R5.R3.)(20.(21.(15.(1.(2.&40.)(2.&40.))R3.))(10.(10.R4.R5.)+???.)))")
(* [comment removed for export] *).
Proof.
  intros nZ N l HnZ H. induction H as [|[b s] l Hs _ IH]; cbn -[Z.of_nat]; [lia|].
  cbn in Hs. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Fixpoint gw_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.

Lemma gap_weight_sizes : forall nZ l,
  gap_weight nZ l = gw_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.

Theorem free_gap_of_totals : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Ph,$22.PnZ,$=.Ptot,$=.P,(>.=R2.)P,(>.(23.(24.(1.(2.&40.)(2.&40.))(25.R4.)(26.R4.)))R2.)P,(>.(10.(10.(10.$18.R4.)R3.)(20.(21.(15.(1.(2.&40.)(2.&40.))(24.(1.(2.&40.)(2.&40.))(25.R5.)(26.R5.))))(10.R4.+???.)))$19.)(7.$=.Lg,$=.(8.(3.$=.(16.R1.$17.)=)(8.(>.$18.R1.)(8.(>.(10.R1.R6.)$19.)(8.(3.$4.(5.(24.(1.(2.&40.)(2.&40.))(25.R7.)(26.R7.))(1:.&40.R1.)(1:.&40.R6.))$<.)(3.$4.(27.(1:.&40.=)R7.R1.R6.)$<.))))))")
(* [comment removed for export] *).
Proof.
  intros h nZ tot HnZ Htot Hband.
  destruct (free_gap_of_slack (vm_reserved h ++ vm_maps h) nZ HnZ) as (g & Hal & Hfl & Hc & Hfree).
  { rewrite gap_weight_sizes. lia. }
  exists g. split; [exact Hal|]. split; [exact Hfl|]. split; [exact Hc|]. split; [exact Hfree|].
  apply hint_placement_ok_b_of_floor. exact Hfl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition ledger_split (l : list (word * word)) (K Y : Z) : Prop :=
  forall b s, In (b, s) l -> bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b.

Lemma ledger_split_nil : forall K Y, ledger_split [] K Y.
Proof. intros K Y b s []. Qed.

Lemma ledger_split_mono : forall l K Y Y',
  ledger_split l K Y -> Y' <= Y -> ledger_split l K Y'.
Proof. intros l K Y Y' H HY b s Hin. destruct (H b s Hin); [left|right]; lia. Qed.

Lemma ledger_split_cons : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Pl,(0.(1.(2.&40.)(2.&40.)))PK,$=.PY,$=.Pb,(2.&40.)Ps,(2.&40.)P,(28.R5.R4.R3.)P,(1<.(>.(10.(13.&40.R3.)(13.&40.R2.))R5.)(>.R4.(13.&40.R3.)))(28.(29.(1.(2.&40.)(2.&40.))(:.(2.&40.)(2.&40.)R4.R3.)R7.)R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros l K Y b s H Hbs b' s' [Heq|Hin]; [injection Heq as <- <-; exact Hbs|].
  exact (H b' s' Hin).
Qed.

Lemma ledger_split_app : forall l1 l2 K Y,
  ledger_split l1 K Y -> ledger_split l2 K Y -> ledger_split (l1 ++ l2) K Y.
Proof.
  intros l1 l2 K Y H1 H2 b s Hin. apply in_app_iff in Hin as [Hin|Hin]; eauto.
Qed.

Lemma ledger_split_app_inv : forall l1 l2 K Y,
  ledger_split (l1 ++ l2) K Y -> ledger_split l1 K Y /\ ledger_split l2 K Y.
Proof.
  intros l1 l2 K Y H. split; intros b s Hin; apply H; apply in_app_iff; auto.
Qed.

(* [comment removed for export] *)
Lemma ledger_split_incl : forall l l' K Y,
  ledger_split l K Y -> incl l' l -> ledger_split l' K Y.
Proof. intros l l' K Y H Hincl b s Hin. apply H. apply Hincl. exact Hin. Qed.

Lemma ledger_split_filter : forall f l K Y,
  ledger_split l K Y -> ledger_split (List.filter f l) K Y.
Proof.
  intros f l K Y H. apply (ledger_split_incl l); [exact H|].
  intros x Hx. apply filter_In in Hx. tauto.
Qed.

(* [comment removed for export] *)
Lemma ledger_split_window_free : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Pl,(0.(1.(2.&40.)(2.&40.)))PK,$=.PY,$=.PnZ,$=.P,(>.=R3.)P,(2:.=R2.)P,(>.(10.R5.(20.+2.R3.))R4.)P,(2:.R5.(2;.+2.+40.))P,(28.R8.R7.R6.)(3.$4.(5.R9.(1:.&40.(2<.R7.R6.))(1:.&40.R6.))$<.)")
(* [comment removed for export] *).
Proof.
  intros l K Y nZ HK HnZ HY HY64 Hsplit.
  apply region_free_intro. intros b s Hin.
  unfold iv_overlap. rewrite !fg_u64_lit by lia.
  pose proof (bv_unsigned_in_range 64 s).
  destruct (Hsplit b s Hin) as [Hlow|Hhigh].
  - apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Theorem null_hint_grant_above : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Ph,$22.Pa,(2.&40.)PnZ,$=.PK,$=.PY,$=.P,(2:.=R3.)P,(3.$=.(16.R4.$17.)=)P,(3.$=.(16.(13.&40.R6.)$17.)=)P,(3.$=.(16.R4.$17.)=)P,(>.R5.(13.&40.(2=.R9.)))P,(>.=R7.)P,(>.(10.R8.(20.+2.R9.))R7.)P,(28.(24.(1.(2.&40.)(2.&40.))(25.R<.)(26.R<.))R9.R8.)P,(3.$4.(2>.R=.(13.&40.R<.)R;.)$<.)(1<.(>.$18.(13.&40.R=.))(2:.(2<.R:.(20.+2.R<.))(13.&40.R=.)))")
(* [comment removed for export] *).
Proof.
  intros h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl.
  pose proof (fg_u64_range a) as Ha.
  pose proof (fg_u64_range (vm_mmap_base h)) as HB.
  assert (HY64 : Y < 2 ^ 64) by (clear - HB HYB; lia).
  assert (HgAl : (Y - nZ) mod page_size = 0).
  { rewrite Zminus_mod, HYal, HnAl. reflexivity. }
  pose proof (ledger_split_window_free _ K Y nZ HK HnZ HY HY64 Hsplit) as Hfree.
  apply (placement_ok_b_iff h (bv_unsigned a) nZ (proj1 Ha) HnZ HaAl HnAl) in Hpl.
  clear HnAl HaAl HYal.
  destruct Hpl as [Hfl|Hnhf]; [left; exact Hfl|right].
  destruct (Z.lt_ge_cases (Y - 2 * nZ) (bv_unsigned a)) as [Hlt|Hge]; [exact Hlt|exfalso].
  assert (H1 : bv_unsigned a + nZ <= Y - nZ) by (clear - Hge; lia).
  assert (H2 : Y - nZ + nZ <= bv_unsigned (vm_mmap_base h)) by (clear - HYB; lia).
  pose proof (Hnhf (Y - nZ) HgAl H1 H2) as Hno.
  rewrite Hfree in Hno. discriminate.
Qed.

(* [comment removed for export] *)
Theorem null_hint_grant_step : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Ph,$22.Pa,(2.&40.)Pn,(2.&40.)PnZ,$=.PK,$=.PY,$=.P,(2:.=R3.)P,(3.$=.(16.R4.$17.)=)P,(3.$=.(16.(13.&40.R7.)$17.)=)P,(3.$=.(16.R4.$17.)=)P,(>.R5.(13.&40.(2=.R:.)))P,(>.=R7.)P,(2:.R8.$18.)P,(>.(10.R9.(20.+2.R:.))R8.)P,(28.(24.(1.(2.&40.)(2.&40.))(25.R>.)(26.R>.))R:.R9.)P,(3.$4.(2>.R?.(13.&40.R>.)R<.)$<.)ZY',$=.(2?.R;.(13.&40.R?.))(8.(2:.R=.(13.&40.R10.))(8.(1<.(>.$18.R1.)(>.(10.(2<.R<.(20.+2.R>.))$17.)R1.))(8.(>.R1.R<.)(8.(3.$=.(16.R1.$17.)=)(8.(>.R1.(13.&40.(2=.R11.)))(28.(24.(1.(2.&40.)(2.&40.))(25.R11.)(29.(1.(2.&40.)(2.&40.))(:.(2.&40.)(2.&40.)R10.R?.)(26.R11.)))R=.R1.))))))")
(* [comment removed for export] *).
Proof.
  intros h a n nZ K Y HnZ HnAl HaAl HYal HYB HK HKfl HY Hsplit Hpl Y'.
  pose proof (null_hint_grant_above h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl) as Habove.
  pose proof bottomup_floor_val as Hfv.
  (* [comment removed for export] *)
  pose proof (page_multiple_eq _ HaAl) as E1.
  pose proof (page_multiple_eq _ HYal) as E2.
  pose proof (page_multiple_eq _ HnAl) as E3.
  clear HnAl HaAl HYal Hpl. unfold page_size.
  set (qa := bv_unsigned a / 4096) in *. set (qy := Y / 4096) in *. set (qn := nZ / 4096) in *.
  clearbody qa qy qn.
  assert (Hqn : 1 <= qn) by lia.
  assert (Hpage : bottomup_floor <= bv_unsigned a \/ Y - 2 * nZ + 4096 <= bv_unsigned a).
  { destruct Habove as [Hfl|Hlt]; [left; exact Hfl|right]. lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - destruct Habove; lia.
  - subst Y'.
    destruct (Z.le_gt_cases Y (bv_unsigned a));
      [rewrite Z.min_l by lia; right; lia | rewrite Z.min_r by lia; destruct Hpage; [left|right]; lia].
  - lia.
  - subst Y'. destruct (Z.le_gt_cases Y (bv_unsigned a)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia];
      [rewrite E2 | rewrite E1]; apply Z_mod_mult.
  - lia.
  - apply ledger_split_app_inv in Hsplit as [Hr Hm].
    apply ledger_split_app; [eapply ledger_split_mono; [exact Hr|lia]|].
    apply ledger_split_cons; [eapply ledger_split_mono; [exact Hm|lia]|].
    right. lia.
Qed.

(* [comment removed for export] *)
Definition kHighMemBeg : Z := 0x10007fff8000.

Lemma kHighMemBeg_below_mmap_base_min :
  kHighMemBeg + 0x544d555f000 = mmap_base_min /\ mmap_base_min < bottomup_floor.
Proof. unfold kHighMemBeg, mmap_base_min. rewrite bottomup_floor_val. split; reflexivity. Qed.

(* [comment removed for export] *)
Corollary kHighMemBeg_le : ltac2:(CDefT.buildp (gd_tbl_AsanPlacement ()) "Ph,$22.Pa,(2.&40.)PnZ,$=.PY,$=.P,(2:.=R2.)P,(3.$=.(16.R3.$17.)=)P,(3.$=.(16.(13.&40.R5.)$17.)=)P,(3.$=.(16.R4.$17.)=)P,(>.R5.(13.&40.(2=.R8.)))P,(>.(10.$30.(20.+2.R7.))R6.)P,(28.(24.(1.(2.&40.)(2.&40.))(25.R:.)(26.R:.))$30.R7.)P,(3.$4.(2>.R;.(13.&40.R:.)R9.)$<.)(2:.$30.(13.&40.R;.))")
(* [comment removed for export] *).
Proof.
  intros h a nZ Y HnZ HnAl HaAl HYal HYB HY Hsplit Hpl.
  assert (HK : 0 <= kHighMemBeg) by (unfold kHighMemBeg; clear; lia).
  destruct (null_hint_grant_above h a nZ kHighMemBeg Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl)
    as [Hfl|Hlt]; clear HnAl HaAl HYal Hpl; [|lia].
  rewrite bottomup_floor_val in Hfl. unfold kHighMemBeg. lia.
Qed.
