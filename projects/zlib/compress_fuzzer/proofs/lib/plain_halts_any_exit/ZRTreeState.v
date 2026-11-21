(** * ZRTreeState — the walk-threaded tree-state invariant.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).  ThreadSeam,
    part 2a.  [ZRTreeInv] (blcount support, in-range BL freqs zero, all
    three length arrays nonnegative) is preserved by every non-flush op
    the slow-path walk performs, and RE-ESTABLISHED by the block flush
    ([treeinv_flush]) — [init_block] re-zeroes the in-range BL
    frequencies, the builds keep support and nonnegativity
    (ZRTreeFacts).  Upstream of SwEv so the walk lemmas can thread it. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  BuildTree BuildChain BtBlSide BtItem6b CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRTreeFacts.
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
       set_matches set_symnext set_symbuf set_bw ts_bw
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

(* ==========================================================================
   1.  The walk-threaded tree-state invariant.
   ========================================================================== *)

Definition ZRTreeInv (ts : TSt) : Prop :=
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0)
  /\ (forall i, 0 <= i < BL_CODES -> t_freq (ts_trees ts TK_BL) i = 0)
  /\ DlNn (ts_trees ts TK_L)
  /\ DlNn (ts_trees ts TK_D)
  /\ DlNn (ts_trees ts TK_BL).

(* ==========================================================================
   3.  The invariant is re-established by every block flush.
   ========================================================================== *)

(** The four state-facts the flush's tail needs, bundled. *)
Local Definition TFour (ts : TSt) : Prop :=
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0)
  /\ DlNn (ts_trees ts TK_L)
  /\ DlNn (ts_trees ts TK_D)
  /\ DlNn (ts_trees ts TK_BL).

Lemma tfour_setbw : forall b ts, TFour ts -> TFour (set_bw b ts).
Proof.
  intros b ts (A & C & D & E).
  unfold TFour in *. tprj. tauto.
Qed.

Local Lemma zrts_pj_trees : forall b s, ts_trees (set_bw b s) = ts_trees s.
Proof. reflexivity. Qed.
Local Lemma zrts_pj_blcount : forall b s, ts_blcount (set_bw b s) = ts_blcount s.
Proof. reflexivity. Qed.

Lemma treeinv_init_block : forall s4 last,
  TFour s4 ->
  ZRTreeInv (if Z.eqb last 0 then init_block s4
             else set_bw (bw_windup (ts_bw (init_block s4)))
                         (init_block s4)).
Proof.
  intros s4 last (A4 & C4 & D4 & E4).
  assert (HIB : ZRTreeInv (init_block s4)).
  { unfold init_block. cbv zeta.
    split; [|split; [|split; [|split]]].
    - (* blcount *)
      intros b Hb. tprj.
      rewrite !bc_settree. apply A4. exact Hb.
    - (* BL freqs, in range *)
      intros i Hi. tprj.
      rewrite set_tree_same.
      apply tree_zero_freq_zero.
      change (Z.of_nat (Z.to_nat BL_CODES)) with BL_CODES.
      lia.
    - (* L lens *)
      intro i. tprj.
      rewrite set_tree_other by (unfold TK_L, TK_BL; lia).
      rewrite set_tree_other by (unfold TK_L, TK_D; lia).
      rewrite set_tree_same.
      unfold t_len at 1. rewrite dl_setfreq. rewrite tree_zero_freq_len.
      exact (C4 i).
    - (* D lens *)
      intro i. tprj.
      rewrite set_tree_other by (unfold TK_D, TK_BL; lia).
      rewrite set_tree_same.
      rewrite tree_zero_freq_len.
      exact (D4 i).
    - (* BL lens *)
      intro i. tprj.
      rewrite set_tree_same.
      rewrite tree_zero_freq_len.
      exact (E4 i). }
  destruct (Z.eqb last 0); [exact HIB|].
  unfold ZRTreeInv.
  rewrite zrts_pj_blcount, !zrts_pj_trees.
  exact HIB.
Qed.

(** The four facts at [build_bl_tree]'s output state. *)
Lemma tfour_bbl : forall ts0,
  ZRTreeInv ts0 ->
  TFour (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0)))).
Proof.
  intros ts0 (Hblc & Hblf & HdlL & HdlD & HdlBL).
  set (s1 := build_tree TK_D (build_tree TK_L ts0)).
  (* the L/D-build support and lens *)
  assert (SL : forall b, b < 0 \/ 15 < b ->
      ts_blcount (build_tree TK_L ts0) b = 0).
  { apply build_tree_blc_support; [| |vm_compute; reflexivity|exact Hblc].
    - vm_compute. split; intro K; discriminate K.
    - vm_compute. split; intro K; discriminate K. }
  assert (SD : forall b, b < 0 \/ 15 < b -> ts_blcount s1 b = 0).
  { apply build_tree_blc_support; [| |vm_compute; reflexivity|exact SL].
    - vm_compute. split; intro K; discriminate K.
    - vm_compute. split; intro K; discriminate K. }
  assert (LL : DlNn (ts_trees s1 TK_L)).
  { intro i. unfold s1.
    rewrite build_tree_tree_other by (unfold TK_L, TK_D; lia).
    exact (build_tree_dl TK_L ts0 HdlL i). }
  assert (LD : DlNn (ts_trees s1 TK_D)).
  { apply build_tree_dl. intro i.
    rewrite build_tree_tree_other by (unfold TK_D, TK_L; lia).
    exact (HdlD i). }
  assert (LBL : DlNn (ts_trees s1 TK_BL)).
  { intro i. unfold s1.
    rewrite build_tree_tree_other by (unfold TK_BL, TK_D; lia).
    rewrite build_tree_tree_other by (unfold TK_BL, TK_L; lia).
    exact (HdlBL i). }
  unfold build_bl_tree. cbv zeta. cbn [snd].
  split; [|split; [|split]].
  - (* blcount *)
    intros b Hb. tprj.
    revert b Hb.
    match goal with
    | |- forall b, _ -> ts_blcount (build_tree TK_BL ?X) b = 0 =>
        apply (build_tree_blc_support TK_BL X)
    end.
    + vm_compute. split; intro K; discriminate K.
    + vm_compute. split; intro K; discriminate K.
    + vm_compute. reflexivity.
    + intros b Hb.
      unfold set_tree, set_trees. cbn [ts_blcount].
      apply SD. exact Hb.
  - (* L lens: the BL build leaves the (guarded) L tree alone *)
    intro i. tprj.
    rewrite build_tree_tree_other by (unfold TK_L, TK_BL; lia).
    rewrite set_tree_other by (unfold TK_L, TK_BL; lia).
    rewrite set_tree_other by (unfold TK_L, TK_D; lia).
    rewrite set_tree_other by (unfold TK_L, TK_BL; lia).
    rewrite set_tree_same.
    unfold scan_tree. cbn [fst].
    unfold t_len at 1, t_setlen. cbn [tr_dl].
    destruct (Z.eq_dec i (ts_maxcode s1 TK_L + 1)) as [-> | Hne].
    + rewrite zset_same. change (u16 65535) with 65535. lia.
    + rewrite zset_other by exact Hne. exact (LL i).
  - (* D lens *)
    intro i. tprj.
    rewrite build_tree_tree_other by (unfold TK_D, TK_BL; lia).
    rewrite set_tree_other by (unfold TK_D, TK_BL; lia).
    rewrite set_tree_same.
    tprj.
    rewrite set_tree_other by (unfold TK_D, TK_BL; lia).
    rewrite set_tree_other by (unfold TK_D, TK_L; lia).
    unfold scan_tree. cbn [fst].
    unfold t_len at 1, t_setlen. cbn [tr_dl].
    match goal with
    | |- 0 <= zset _ ?G _ i => destruct (Z.eq_dec i G) as [-> | Hne]
    end.
    + rewrite zset_same. change (u16 65535) with 65535. lia.
    + rewrite zset_other by exact Hne. exact (LD i).
  - (* BL lens *)
    intro i. tprj. revert i.
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
    exact (LBL i).
Qed.

Theorem treeinv_tfb : forall buf sl last lvl strat dt ts0,
  0 < lvl ->
  ZRTreeInv ts0 ->
  ZRTreeInv (snd (tr_flush_block buf sl last lvl strat dt ts0)).
Proof.
  intros buf sl last lvl strat dt ts0 Hlvl HI.
  pose proof (tfour_bbl ts0 HI) as HS2.
  unfold tr_flush_block.
  rewrite (proj2 (Z.ltb_lt 0 lvl) Hlvl).
  cbv zeta iota.
  change (Z.eqb last 0) with (Z.eqb last 0).
  cbn [snd].
  destruct buf as [dat|]; cbv iota.
  - match goal with
    | |- context [if ?c then Some _ else None] => destruct c
    end; cbv iota.
    + apply treeinv_init_block.
      unfold tr_stored_block. cbv zeta.
      apply tfour_setbw. exact HS2.
    + match goal with
      | |- context [if ?c
                    then set_bw (compress_block _ _ static_ltree static_dtree _) _
                    else _] =>
          destruct c
      end; apply treeinv_init_block; apply tfour_setbw; exact HS2.
  - match goal with
    | |- context [if ?c
                  then set_bw (compress_block _ _ static_ltree static_dtree _) _
                  else _] =>
        destruct c
    end; apply treeinv_init_block; apply tfour_setbw; exact HS2.
Qed.

Lemma treeinv_flush_pending : forall x,
  ZRTreeInv (d_ts x) -> ZRTreeInv (d_ts (flush_pending x)).
Proof.
  intros x (A & B & C & D & E).
  unfold flush_pending. cbv zeta.
  destruct (Z.eqb _ 0); dsimp; unfold tr_flush_bits;
    unfold ZRTreeInv; tprj; tauto.
Qed.

Theorem treeinv_flush : forall l s,
  0 < dg_level (d_cfg s) ->
  ZRTreeInv (d_ts s) ->
  ZRTreeInv (d_ts (flush_block_only l s)).
Proof.
  intros l s Hlvl HI.
  unfold flush_block_only. cbv zeta.
  apply treeinv_flush_pending. dsimp.
  apply treeinv_tfb; [exact Hlvl | exact HI].
Qed.

Print Assumptions treeinv_flush.

(** The invariant is insensitive to the byte writer and to L/D frequency
    tallies — the two non-flush ways the walk touches [d_ts]. *)
Lemma treeinv_setbw : forall b ts, ZRTreeInv ts -> ZRTreeInv (set_bw b ts).
Proof.
  intros b ts (A & B & C & D & E). unfold ZRTreeInv. tprj. tauto.
Qed.

Lemma treeinv_tally_frame : forall ts ts',
  ts_blcount ts' = ts_blcount ts ->
  (forall i, t_freq (ts_trees ts' TK_BL) i = t_freq (ts_trees ts TK_BL) i) ->
  (forall i, t_len (ts_trees ts' TK_L) i = t_len (ts_trees ts TK_L) i) ->
  (forall i, t_len (ts_trees ts' TK_D) i = t_len (ts_trees ts TK_D) i) ->
  (forall i, t_len (ts_trees ts' TK_BL) i = t_len (ts_trees ts TK_BL) i) ->
  ZRTreeInv ts -> ZRTreeInv ts'.
Proof.
  intros ts ts' Hb Hf HL HD HBL (A & B & C & D & E).
  split; [|split; [|split; [|split]]].
  - intros x Hx. rewrite Hb. apply A. exact Hx.
  - intros i Hi. rewrite Hf. apply B. exact Hi.
  - intro i. rewrite HL. apply C.
  - intro i. rewrite HD. apply D.
  - intro i. rewrite HBL. apply E.
Qed.

(** The invariant at the reset writer state ([tr_init ts_new]) — the
    entry point every run starts from. *)
Lemma treeinv_init : ZRTreeInv (tr_init ts_new).
Proof.
  unfold tr_init.
  split; [|split; [|split; [|split]]].
  - intros b _. reflexivity.
  - intros i Hi.
    unfold init_block. cbv zeta. tprj.
    rewrite set_tree_same.
    apply tree_zero_freq_zero.
    change (Z.of_nat (Z.to_nat BL_CODES)) with BL_CODES. lia.
  - intro i. exact (Z.le_refl 0).
  - intro i. exact (Z.le_refl 0).
  - intro i. exact (Z.le_refl 0).
Qed.

Print Assumptions treeinv_init.

(* ==========================================================================
   4.  Frames for the walk's non-flush [d_ts] mutations.
   ========================================================================== *)

Lemma treeinv_tally_lit : forall c se ts,
  ZRTreeInv ts -> ZRTreeInv (snd (tr_tally_lit c se ts)).
Proof.
  intros c se ts HI.
  unfold tr_tally_lit. cbv zeta. cbn [snd].
  refine (treeinv_tally_frame ts _ _ _ _ _ _ HI).
  - tprj. rewrite bc_settree. tprj. reflexivity.
  - intro i. rewrite set_tree_other by (unfold TK_BL, TK_L; lia).
    tprj. reflexivity.
  - intro i. rewrite set_tree_same. rewrite dl_setfreq.
    tprj. reflexivity.
  - intro i. rewrite set_tree_other by (unfold TK_D, TK_L; lia).
    tprj. reflexivity.
  - intro i. rewrite set_tree_other by (unfold TK_BL, TK_L; lia).
    tprj. reflexivity.
Qed.

Lemma treeinv_tally_dist : forall d l se ts,
  ZRTreeInv ts -> ZRTreeInv (snd (tr_tally_dist d l se ts)).
Proof.
  intros d l se ts HI.
  unfold tr_tally_dist. cbv zeta. cbn [snd].
  refine (treeinv_tally_frame ts _ _ _ _ _ _ HI).
  - tprj. rewrite !bc_settree. tprj. reflexivity.
  - intro i.
    rewrite set_tree_other by (unfold TK_BL, TK_D; lia).
    rewrite set_tree_other by (unfold TK_BL, TK_L; lia).
    tprj. reflexivity.
  - intro i.
    rewrite set_tree_other by (unfold TK_L, TK_D; lia).
    rewrite set_tree_same. rewrite dl_setfreq.
    tprj. reflexivity.
  - intro i.
    rewrite set_tree_same. rewrite dl_setfreq.
    reflexivity.
  - intro i.
    rewrite set_tree_other by (unfold TK_BL, TK_D; lia).
    rewrite set_tree_other by (unfold TK_BL, TK_L; lia).
    tprj. reflexivity.
Qed.

Lemma flush_block_only_cfg : forall l s,
  d_cfg (flush_block_only l s) = d_cfg s.
Proof.
  intros l s.
  unfold flush_block_only, flush_pending. cbv zeta.
  destruct (Z.eqb _ 0); dsimp; reflexivity.
Qed.

(* ==========================================================================
   5.  The converged per-event snapshot record (EvSnapOk) and the side
       invariants that thread it: fleet-canon spelling agreed with
       g6-bound (consumer) and crc-capstone (design), 2026-08-20.
   ========================================================================== *)

(** g6's (m): a tallied minimum match is never TOO_FAR away — ds_body's
    strategy-0 filter (Deflate.v:646). *)
Definition FarOkTok (t : Tok) : Prop :=
  match t with
  | TMatch len dist => len = 3 -> dist <= TOO_FAR
  | TLit _ => True
  end.

(** The pending-match residue of the filter: between the trip that finds
    a minimum match and the trip that tallies it, [strstart] advances by
    exactly one, hence the [+ 1]. *)
Definition FarPend (l : LSt) : Prop :=
  ls_matchlen l = MIN_MATCH ->
  ls_strstart l - ls_matchstart l <= TOO_FAR + 1.

(** g6's (n): a negative block start (post-slide) means the block already
    spans more than the maximum match distance. *)
Definition SldInv (g : DeflGeom) (l : LSt) : Prop :=
  ls_blockstart l < 0 ->
  dg_max_dist g < ls_strstart l - ls_blockstart l.

(** The walk-threaded side bundle: the tree-state invariant plus the
    token/pending/slide/counter threads. *)
Definition ZRSideInv (g : DeflGeom) (toks : list Tok) (s : DSt) : Prop :=
  ZRTreeInv (d_ts s)
  /\ ts_optlen (d_ts s) = 0
  /\ ts_statlen (d_ts s) = 0
  /\ Forall FarOkTok toks
  /\ FarPend (d_ls s)
  /\ SldInv g (d_ls s).

(* --- counter frames: the tallies and the writer don't touch them ------- *)

Lemma statzero_tally_lit : forall c se ts,
  ts_optlen ts = 0 /\ ts_statlen ts = 0 ->
  ts_optlen (snd (tr_tally_lit c se ts)) = 0
  /\ ts_statlen (snd (tr_tally_lit c se ts)) = 0.
Proof.
  intros c se ts (Ho & Hs).
  unfold tr_tally_lit. cbv zeta. cbn [snd]. tprj.
  split; assumption.
Qed.

Lemma statzero_tally_dist : forall d l se ts,
  ts_optlen ts = 0 /\ ts_statlen ts = 0 ->
  ts_optlen (snd (tr_tally_dist d l se ts)) = 0
  /\ ts_statlen (snd (tr_tally_dist d l se ts)) = 0.
Proof.
  intros d l se ts (Ho & Hs).
  unfold tr_tally_dist. cbv zeta. cbn [snd]. tprj.
  split; assumption.
Qed.

Lemma statzero_setbw : forall b ts,
  ts_optlen ts = 0 /\ ts_statlen ts = 0 ->
  ts_optlen (set_bw b ts) = 0 /\ ts_statlen (set_bw b ts) = 0.
Proof. intros b ts (Ho & Hs). tprj. split; assumption. Qed.

(** The flush restores the counters to zero unconditionally
    ([init_block] is the last counter write). *)
Lemma statzero_tfb : forall buf sl last lvl strat dt ts0,
  ts_optlen (snd (tr_flush_block buf sl last lvl strat dt ts0)) = 0
  /\ ts_statlen (snd (tr_flush_block buf sl last lvl strat dt ts0)) = 0.
Proof.
  intros buf sl last lvl strat dt ts0.
  unfold tr_flush_block.
  destruct (Z.ltb 0 lvl); cbv zeta; destruct (Z.eqb last 0);
    split; vm_compute; reflexivity.
Qed.

Lemma statzero_flush : forall l s,
  ts_optlen (d_ts (flush_block_only l s)) = 0
  /\ ts_statlen (d_ts (flush_block_only l s)) = 0.
Proof.
  intros l s.
  unfold flush_block_only. cbv zeta.
  match goal with
  | |- context [flush_pending ?X] => set (s2 := X)
  end.
  assert (H2 : ts_optlen (d_ts s2) = 0 /\ ts_statlen (d_ts s2) = 0)
    by (unfold s2; dsimp; apply statzero_tfb).
  unfold flush_pending. cbv zeta.
  match goal with
  | |- context [if ?c then _ else _] => destruct c
  end; dsimp; unfold tr_flush_bits; tprj; exact H2.
Qed.

(** The initial counters are zero. *)
Lemma statzero_init :
  ts_optlen (tr_init ts_new) = 0 /\ ts_statlen (tr_init ts_new) = 0.
Proof. split; reflexivity. Qed.

Print Assumptions statzero_flush.

(** The flush's ls is exactly the blockstart reset (the pending drain
    never touches [d_ls]). *)
Lemma flush_block_only_ls : forall l s,
  d_ls (flush_block_only l s)
  = setL_blockstart (ls_strstart (d_ls s)) (d_ls s).
Proof.
  intros l s.
  unfold flush_block_only, flush_pending. cbv zeta.
  destruct (Z.eqb _ 0); dsimp; reflexivity.
Qed.

(** The tally's full-buffer flag pins the post-tally symbol count at the
    block boundary. *)
Lemma tally_lit_full : forall c se ts,
  fst (tr_tally_lit c se ts) = true ->
  ts_symnext (snd (tr_tally_lit c se ts)) = se.
Proof.
  intros c se ts H.
  unfold tr_tally_lit in *. cbv zeta in *. cbn [fst snd] in *.
  apply Z.eqb_eq in H. tprj. exact H.
Qed.

Lemma tally_dist_full : forall d l se ts,
  fst (tr_tally_dist d l se ts) = true ->
  ts_symnext (snd (tr_tally_dist d l se ts)) = se.
Proof.
  intros d l se ts H.
  unfold tr_tally_dist in *. cbv zeta in *. cbn [fst snd] in *.
  apply Z.eqb_eq in H. tprj. exact H.
Qed.

(** The aligned-drain writer step keeps the counters at zero. *)
Lemma statzero_flush_pending : forall s,
  ts_optlen (d_ts s) = 0 /\ ts_statlen (d_ts s) = 0 ->
  ts_optlen (d_ts (flush_pending s)) = 0
  /\ ts_statlen (d_ts (flush_pending s)) = 0.
Proof.
  intros s H2.
  unfold flush_pending. cbv zeta.
  match goal with
  | |- context [if ?c then _ else _] => destruct c
  end; dsimp; unfold tr_flush_bits; tprj; exact H2.
Qed.
