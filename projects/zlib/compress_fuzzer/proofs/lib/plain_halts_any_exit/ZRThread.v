(** * ZRThread — the tree-state invariant and its cash-out at a flush.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).  ThreadSeam
    discharge, part 2: [ZRTreeInv] (blcount support, BL freqs zero,
    all three length arrays nonnegative) implies [ZR_DynEntry] at the
    same state, modulo one residual (the [TK_D] maxcode lower bound,
    [ZR_MaxcD]).  Part 3 threads [ZRTreeInv] along the walk. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  BuildTree BuildChain BtBlSide BtItem6b CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwEv SwStep ZREmitBody ZRTreeFacts ZRTreeState.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac tprj :=
  cbn [ts_trees ts_blcount ts_maxcode ts_heap ts_heapmax ts_optlen
       ts_statlen ts_symbuf ts_symnext ts_heaplen ts_depth
       set_statlen set_optlen set_blcount set_heapmax set_heaplen
       set_depth set_heap set_max set_maxcode set_trees
       set_matches set_symnext set_bw ts_bw
       fst snd].

Local Ltac dsimp :=
  cbn [d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype
       setZ_in setZ_done setZ_out setZ_availout setZ_totalin setZ_totalout
       setZ_adler setZ_datatype
       fst snd].

(** RESOLVED (2026-08-20): the R39 repair train. [bt_loop] writes
    internal-node frequencies at [BL_CODES <=] slots that nothing ever
    clears, so only the in-range form is true at reachable states; the
    keystone premises are weakened to match (g1's ScanR [_r] family +
    [build_bl_tree_mbi3_r]), and this predicate now spells the canon
    [0 <= i < 19] literal.  The historical all-indices spelling is
    recoverable from git; nothing consumes it. *)
Definition ZR_BlfAll (ts : TSt) : Prop :=
  forall i, 0 <= i < 19 -> t_freq (ts_trees ts TK_BL) i = 0.

(** The one residual: the distance tree's maxcode after the two builds.
    (zlib's [bt_force2] guarantees it; own derivation pending.) *)
Definition ZR_MaxcD (ts : TSt) : Prop :=
  1 <= ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D.

(* ==========================================================================
   2.  The invariant implies the dynamic arm's entry facts.
   ========================================================================== *)

Theorem treeinv_dynentry : forall ts,
  ZRTreeInv ts ->
  ZR_BlfAll ts ->
  ZR_MaxcD ts ->
  ZR_DynEntry ts.
Proof.
  intros ts (Hblc & Hblf0 & HdlL & HdlD & HdlBL) Hblf Hmaxc.
  unfold ZR_DynEntry.
  (* the L build *)
  assert (D4 : forall b, b < 0 \/ 15 < b ->
      ts_blcount (build_tree TK_L ts) b = 0).
  { apply build_tree_blc_support; [| |vm_compute; reflexivity..|exact Hblc].
    - vm_compute. split; intro K; discriminate K.
    - vm_compute. split; intro K; discriminate K. }
  assert (D5 : DlNn (ts_trees (build_tree TK_L ts) TK_L))
    by (apply build_tree_dl; exact HdlL).
  (* the D build *)
  assert (D6 : forall b, b < 0 \/ 15 < b ->
      ts_blcount (build_tree TK_D (build_tree TK_L ts)) b = 0).
  { apply build_tree_blc_support; [| |vm_compute; reflexivity..|exact D4].
    - vm_compute. split; intro K; discriminate K.
    - vm_compute. split; intro K; discriminate K. }
  assert (HdlD' : DlNn (ts_trees (build_tree TK_L ts) TK_D)).
  { intro i.
    rewrite build_tree_tree_other by (vm_compute; intro K; discriminate K).
    exact (HdlD i). }
  assert (D7 : DlNn (ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_D))
    by (apply build_tree_dl; exact HdlD').
  (* the BL build inside [build_bl_tree] *)
  assert (HblBL' : DlNn (ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_BL)).
  { intro i.
    rewrite build_tree_tree_other by (vm_compute; intro K; discriminate K).
    rewrite build_tree_tree_other by (vm_compute; intro K; discriminate K).
    exact (HdlBL i). }
  assert (D6' := D6).
  set (s1D := build_tree TK_D (build_tree TK_L ts)) in *.
  assert (D9 : forall b, b < 0 \/ 15 < b ->
      ts_blcount (snd (build_bl_tree s1D)) b = 0).
  { unfold build_bl_tree. cbv zeta. tprj.
    intros b Hb.
    match goal with
    | |- ts_blcount (build_tree TK_BL ?X) b = 0 =>
        revert b Hb;
        apply (build_tree_blc_support TK_BL X)
    end.
    - vm_compute. split; intro K; discriminate K.
    - vm_compute. split; intro K; discriminate K.
    - vm_compute. reflexivity.
    - intros b Hb.
      unfold set_tree, set_trees. cbn [ts_blcount].
      apply D6. exact Hb. }
  assert (D10 : forall i, 0 <= t_len
      (ts_trees (snd (build_bl_tree s1D)) TK_BL) i).
  { unfold build_bl_tree. cbv zeta. tprj.
    match goal with
    | |- forall i, 0 <= t_len (ts_trees (build_tree TK_BL ?X) TK_BL) i =>
        apply (build_tree_dl TK_BL X)
    end.
    intro i.
    rewrite set_tree_same.
    unfold scan_tree. cbn [snd].
    rewrite scan_go_len.
    rewrite set_tree_same.
    rewrite scan_go_len.
    exact (HblBL' i). }
  repeat (split; [assumption|]).
  assumption.
Qed.

Print Assumptions treeinv_dynentry.

(** The maxcode residual holds UNCONDITIONALLY: [bt_force2] always
    leaves at least two heap entries, and the census then puts the
    distance tree's maxcode at 1 or higher. *)
Theorem maxcd_all : forall ts, ZR_MaxcD ts.
Proof.
  intro ts. unfold ZR_MaxcD.
  apply build_tree_maxc_ge1.
  vm_compute. split; intro K; discriminate K.
Qed.

Print Assumptions maxcd_all.

(** Per-event: the threaded invariant plus the (repair-pending) BlfAll
    residual give the whole dyn-entry bundle — pack-independent. *)
Lemma dynentries_from_invariants : forall evs,
  Forall (fun ev => ZRTreeInv (d_ts (fe_s ev))) evs ->
  Forall (fun ev => ZR_BlfAll (d_ts (fe_s ev))) evs ->
  Forall (fun ev => ZR_DynEntry (d_ts (fe_s ev))) evs.
Proof.
  induction evs as [|ev evs IH]; intros HTI HBl; [constructor|].
  inversion HTI as [|? ? HTh HTt]; subst.
  inversion HBl as [|? ? HBh HBt]; subst.
  constructor.
  - apply treeinv_dynentry; [exact HTh | exact HBh | apply maxcd_all].
  - apply IH; [exact HTt | exact HBt].
Qed.
