(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (imports of the model's Mmap and Placement; free_gap_of_totals, ledger_split_window_free, null_hint_grant_above, null_hint_grant_step and kHighMemBeg_le written out in plain text from their encoded (CDefT) form and restated for Linux's placement rule, linux_place under the mmap_top ceiling; new lemmas ledger_split_window_free_w and mmap_top_of_ceiling; explanatory comments added). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanCeil PlacementSearch.  (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* ========================================================================= *)
(* Small facts                                                                *)
(* ========================================================================= *)

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

Theorem free_gap_of_totals : forall (h : VmMaps) (thp : bool) nZ tot,
  0 < nZ -> nZ mod page_size = 0 ->
  alloc_ceiling <= alloc_top h ->
  gw_sizes (vm_reserved h ++ vm_maps h) <= tot ->
  bottomup_floor + nZ + tot + Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (nZ + 4095) <= alloc_ceiling ->
  exists g, linux_place h thp (Z_to_bv 64 0) nZ g.
Proof.
  intros h thp nZ tot HnZ HnAl Htop Htot Hband.
  destruct (free_gap_of_slack (vm_reserved h ++ vm_maps h) nZ ltac:(lia))
    as (g & Hal & Hfl & Hc & Hfree).
  { rewrite gap_weight_sizes. lia. }
  apply (linux_place_exists h thp (Z_to_bv 64 0) nZ HnZ HnAl).
  exists g. right. unfold gap_fits.
  pose proof bottomup_floor_val as Hfv.
  repeat split; [exact Hal | unfold task_unmapped_base; lia | lia | exact Hfree].
Qed.

(* ========================================================================= *)
(* NULL-hint placement: where a kernel-placed grant can land                  *)
(* ========================================================================= *)

(** What the [choose] guard of a NULL-hint grant says ([Mmap.placement_ok]):
    the base is at or above [bottomup_floor], or no page-aligned free window
    of the same size lies between the grant's end and [vm_mmap_base].  The
    ASan proof needs a LOWER BOUND on such a base (every application address
    must be >= kHighMemBeg = 0x10007fff8000, the end of the high shadow).
    The invariant that yields it: the ledger is SPLIT — every interval
    either ends at or below a low mark [K] or starts at or above a high
    mark [Y] <= vm_mmap_base — with at least two windows of slack
    ([K + 2 nZ <= Y]).  Then [Y - nZ, Y) is a free aligned window, so a
    top-down placement must END above [Y - nZ], i.e. start above
    [Y - 2 nZ]; a bottom-up one is above the floor anyway.  Adding the
    grant keeps the ledger split with the high mark lowered to
    [min Y a] — so the mark drops by less than twice the total size of the
    NULL-hint grants made, starting from [min bottomup_floor vm_mmap_base]
    >= [State.mmap_base_min] = 0x154555557000, which leaves 0x544d555f000 (~5.3 TiB) of
    descent before kHighMemBeg. *)

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
Lemma ledger_split_window_free_w : forall l K Y w,
  0 <= K -> 0 < w -> K + w <= Y -> Y < 2 ^ 64 ->
  ledger_split l K Y ->
  region_free l (Z_to_bv 64 (Y - w)) (Z_to_bv 64 w) = true.
Proof.
  intros l K Y w HK Hw HY HY64 Hsplit.
  apply region_free_intro. intros b s Hin.
  unfold iv_overlap. rewrite !fg_u64_lit by lia.
  pose proof (bv_unsigned_in_range 64 s).
  destruct (Hsplit b s Hin) as [Hlow|Hhigh].
  - apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Lemma ledger_split_window_free : forall l K Y nZ,
  0 <= K -> 0 < nZ -> K + 2 * nZ <= Y -> Y < 2 ^ 64 ->
  ledger_split l K Y ->
  region_free l (Z_to_bv 64 (Y - nZ)) (Z_to_bv 64 nZ) = true.
Proof.
  intros l K Y nZ HK HnZ HY HY64 Hsplit.
  apply (ledger_split_window_free_w l K Y nZ); [lia|lia|lia|lia|exact Hsplit].
Qed.

(** THE PLACEMENT BOUND.  A NULL-hint grant [a] of rounded length [nZ]
    into a split ledger lands above [Y - 2 nZ].

    WHY, UNDER THE NEW RULE.  The split leaves [[K, Y)] free, and
    [Y <= mmap_top h], so a window of [w] bytes ending at [Y] is a fit
    inside Linux's top-down search range [[page_size, mmap_top h)] for
    every [w <= Y - K].  Two things follow at once: the bottom-up
    fallback cannot run (it needs the top-down window to hold NO fit),
    and the top-down answer, being the HIGHEST fit, is at or above
    [Y - w].  With [w = nZ] for the plain search and
    [w = nZ + pmd_size] for the padded one a THP kernel runs first
    (there [nZ] is a multiple of [pmd_size], so [nZ + pmd_size <= 2 nZ],
    and [thp_align] only moves the answer UP), the bound is
    [Y - 2 nZ < a] in every branch.

    THE CEILING IS [mmap_top h], NOT [vm_mmap_base h].  LPS searches
    below [Z.min (vm_mmap_base h) (page_round_down_Z (alloc_top h))];
    [mmap_top_of_ceiling] below turns the two bounds a caller holds
    into this one. *)
Theorem null_hint_grant_above : forall h (a : word) nZ K Y,
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 ->
  Y mod page_size = 0 -> Y <= mmap_top h ->
  page_size <= K -> K + 2 * nZ <= Y ->
  ledger_split (vm_reserved h ++ vm_maps h) K Y ->
  placement_ok_b h (bv_unsigned a) nZ = true ->
  bottomup_floor <= bv_unsigned a \/ Y - 2 * nZ < bv_unsigned a.
Proof.
  intros h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl.
  right.
  pose proof (fg_u64_range a) as Ha.
  pose proof pmd_size_pos as Hpmd.
  pose proof (mmap_top_lt_two_pow_64 h) as Htop64.
  assert (HY64 : Y < 2 ^ 64) by (clear - Htop64 HYB; unfold two_pow_64 in *; lia).
  (* every window of width [w <= Y - K] ending at [Y] is a top-down fit *)
  assert (FIT : forall w, 0 < w -> w mod page_size = 0 -> K + w <= Y ->
           gap_fits (vm_reserved h ++ vm_maps h) page_size (mmap_top h) w (Y - w)).
  { intros w Hw Hwal Hroom. unfold gap_fits.
    repeat split.
    - rewrite Zminus_mod, HYal, Hwal. reflexivity.
    - unfold page_size in HK |- *. lia.
    - lia.
    - exact (ledger_split_window_free_w _ K Y w ltac:(unfold page_size in HK; lia)
               Hw ltac:(lia) HY64 Hsplit). }
  (* the top-down search's answer is at or above [Y - w] *)
  assert (TD : forall w b, 0 < w -> w mod page_size = 0 -> K + w <= Y ->
           topdown_search h w b -> (Y - w <= b)%Z).
  { intros w b Hw Hwal Hroom Hts. unfold topdown_search in Hts. cbv zeta in Hts.
    destruct Hts as [[_ Hmax]|[Hno _]].
    - exact (Hmax _ (FIT w Hw Hwal Hroom)).
    - exfalso. exact (Hno (Y - w) (FIT w Hw Hwal Hroom)). }
  apply (placement_ok_b_iff h (bv_unsigned a) nZ HnZ HnAl) in Hpl.
  destruct Hpl as (thp & Hpl).
  unfold linux_place in Hpl. cbv zeta in Hpl.
  assert (Hg : hint_address (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity).
  rewrite Hg, Z.eqb_refl in Hpl. cbv iota in Hpl.
  destruct (thp && (nZ mod pmd_size =? 0)%Z)%bool eqn:Hthp.
  - assert (Hmul : (nZ mod pmd_size = 0)%Z)
      by (apply andb_true_iff in Hthp as [_ E]; now apply Z.eqb_eq).
    assert (Hge : (pmd_size <= nZ)%Z).
    { pose proof (Z.div_mod nZ pmd_size ltac:(lia)) as D.
      assert (0 < nZ / pmd_size)%Z by nia. nia. }
    assert (HpadAl : ((nZ + pmd_size) mod page_size = 0)%Z).
    { rewrite Zplus_mod, HnAl, (mod_pmd_mod_page pmd_size (Z_mod_same_full pmd_size)).
      reflexivity. }
    destruct Hpl as [(ret & Hret & ->)|[_ Hts]].
    + pose proof (thp_align_bounds ret) as [Hb1 _].
      pose proof (TD (nZ + pmd_size) ret ltac:(lia) HpadAl ltac:(lia) Hret). lia.
    + pose proof (TD nZ _ HnZ HnAl ltac:(lia) Hts). lia.
  - pose proof (TD nZ _ HnZ HnAl ltac:(lia) Hpl). lia.
Qed.

(** The two bounds a caller holds, turned into [Y <= mmap_top h]:
    [mmap_top] is the lower of the recorded base and the page-rounded
    allocation top, and [init_sp_ok] puts the latter at or above the
    constant [alloc_ceiling], which is itself page-aligned. *)
Lemma mmap_top_of_ceiling : forall h Y,
  init_sp_ok h -> Y <= bv_unsigned (vm_mmap_base h) -> Y <= alloc_ceiling ->
  Y <= mmap_top h.
Proof.
  intros h Y Hisp HB Hce.
  pose proof (alloc_ceiling_le_alloc_top h Hisp) as Hat.
  unfold mmap_top. apply Z.min_glb; [exact HB|].
  apply (Z.le_trans Y alloc_ceiling _); [exact Hce|].
  apply page_round_down_Z_greatest; [lia|].
  unfold alloc_ceiling, page_size. reflexivity.
Qed.

(** Packaged for a grant step: the grant is above [K] (strictly: by at
    least a page, being aligned above [Y - 2nZ] >= K), and the extended
    ledger is split at the lowered high mark [Z.min Y (bv_unsigned a)]
    (page-aligned, at or below [mmap_top h], and >= Y - 2 nZ + page or
    >= the floor).  The ceiling the mark is measured against is
    [mmap_top h], the top of Linux's top-down window; use
    [mmap_top_of_ceiling] to produce it. *)
Theorem null_hint_grant_step : forall h (a n : word) nZ K Y,
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 ->
  Y mod page_size = 0 -> Y <= mmap_top h ->
  page_size <= K -> K < bottomup_floor -> K + 2 * nZ <= Y ->
  ledger_split (vm_reserved h ++ vm_maps h) K Y ->
  placement_ok_b h (bv_unsigned a) nZ = true ->
  let Y' := Z.min Y (bv_unsigned a) in
  K < bv_unsigned a
  /\ (bottomup_floor <= Y' \/ Y - 2 * nZ + page_size <= Y') /\ Y' <= Y
  /\ Y' mod page_size = 0 /\ Y' <= mmap_top h
  /\ ledger_split (vm_reserved h ++ (a, n) :: vm_maps h) K Y'.
Proof.
  intros h a n nZ K Y HnZ HnAl HaAl HYal HYB HK HKfl HY Hsplit Hpl Y'.
  pose proof (null_hint_grant_above h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl) as Habove.
  pose proof bottomup_floor_val as Hfv.
  (* page arithmetic: name the quotients so everything is linear *)
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

(** The numbers for the ASan layout: kHighMemBeg and the descent room. *)
Definition kHighMemBeg : Z := 0x10007fff8000.

Lemma kHighMemBeg_below_mmap_base_min :
  kHighMemBeg + 0x544d555f000 = mmap_base_min /\ mmap_base_min < bottomup_floor.
Proof. unfold kHighMemBeg, mmap_base_min. rewrite bottomup_floor_val. split; reflexivity. Qed.

(* [comment removed for export] *)
Corollary kHighMemBeg_le : forall h (a : word) nZ Y,
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 ->
  Y mod page_size = 0 -> Y <= mmap_top h ->
  kHighMemBeg + 2 * nZ <= Y ->
  ledger_split (vm_reserved h ++ vm_maps h) kHighMemBeg Y ->
  placement_ok_b h (bv_unsigned a) nZ = true ->
  kHighMemBeg < bv_unsigned a.
Proof.
  intros h a nZ Y HnZ HnAl HaAl HYal HYB HY Hsplit Hpl.
  assert (HK : page_size <= kHighMemBeg) by (unfold kHighMemBeg, page_size; clear; lia).
  destruct (null_hint_grant_above h a nZ kHighMemBeg Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl)
    as [Hfl|Hlt]; clear HnAl HaAl HYal Hpl; [|lia].
  rewrite bottomup_floor_val in Hfl. unfold kHighMemBeg. lia.
Qed.
