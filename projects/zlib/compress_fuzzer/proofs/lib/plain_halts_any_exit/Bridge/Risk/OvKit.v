(** * Bridge.Risk.OvKit — the sym_buf overlay, functional half: proofs (group R).

    S5 keeps its symbols inside [pending_buf] (from [lit_bufsize] on) and
    writes the block's bits into the same array from 0.  S5's own proof
    carries, through [compress_block]'s loop, the invariant [CBI]
    ([RefDeflSafeE4]): the bits written so far lie below the next unread
    symbol, and everything at or above [pending] is still the block-entry
    array.  [CBI_step] shows each step's send_bits calls are the ones
    computed from the block-entry ("pristine") symbols.  This file chains
    those steps: [compress_block] equals [sbs_run] over the pristine calls
    ([ov_compress_block]), and at a flush ([fb_entry]) both the dynamic
    branch (by S5's [overlay_core_proof]) and the static branch (31 bits per
    3-byte symbol at most) meet the invariant ([ov_emit_dyn],
    [ov_emit_stat]).  [Risk.RiskIface] re-exports these. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees TreesTab DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel CompressModel TreeModel FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay RefDeflSafeFB RefDeflSafeE1 RefDeflSafeE3 RefDeflSafeE4 RefDeflSafeE5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ OverlayCoreL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** The send_bits calls for symbols [j, j+1, ..., j+n-1] of [s0], read from
    [s0]'s symbol bytes ([sym_calls] reads [pending_buf] at
    [lit_bufsize + 3j .. lit_bufsize + 3j + 2]). *)
Fixpoint cb_calls_from (s0 : deflate_state) (lfc ldl dfc ddl : arr) (j : Z) (n : nat) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => sym_calls s0 lfc ldl dfc ddl (3 * j) ++ cb_calls_from s0 lfc ldl dfc ddl (j + 1) n'
  end.

Definition cb_calls (s0 : deflate_state) (lfc ldl dfc ddl : arr) (N : Z) : list (Z * Z) :=
  cb_calls_from s0 lfc ldl dfc ddl 0 (Z.to_nat N).

(** The whole block body: every symbol, then END_BLOCK. *)
Definition cb_all (s0 : deflate_state) (lfc ldl dfc ddl : arr) (N : Z) : list (Z * Z) :=
  cb_calls s0 lfc ldl dfc ddl N ++ [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)].

Section CB.
Variables (s0 : deflate_state) (lfc ldl dfc ddl : arr) (N W0 : Z).
Hypothesis HN : 0 <= N.
Hypothesis HPBL : arr_len (ds_pending_buf s0) = ds_lit_bufsize s0 * 4.
Hypothesis Hroom : ds_lit_bufsize s0 + 3 * N + 3 <= arr_len (ds_pending_buf s0).
Hypothesis Hsyms : forall j, 0 <= j < N -> sym_okb s0 j.
Hypothesis HlenL : forall j, 0 <= j < N -> 0 <= arr_get ldl (sym_lcode s0 j) <= 15.
Hypothesis HlenD : forall j, 0 <= j < N -> sym_isdist s0 j = true -> 0 <= arr_get ddl (sym_dcode s0 j) <= 15.
Hypothesis PREFIX : forall k, 0 <= k < N -> W0 + zsum (dcost ldl ddl s0) 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s0 + 3 * k).
Hypothesis TOTAL : W0 + zsum (dcost ldl ddl s0) 0 (Z.to_nat N) <= 8 * arr_len (ds_pending_buf s0).

Lemma cb_loop_calls : forall f k y sx, sx = 3 * k -> CBI s0 ldl ddl N W0 k y -> k < N -> (Z.to_nat (N - k) <= f)%nat ->
  compress_block_loop f y lfc ldl dfc ddl sx = sbs_run y (cb_calls_from s0 lfc ldl dfc ddl k (Z.to_nat (N - k))).
Proof.
  induction f as [|f IH]; intros k y sx -> I Hk Hf; [lia|].
  rewrite cb_loop_S. cbv zeta.
  pose proof (CBI_step s0 lfc ldl dfc ddl N W0 HPBL Hroom Hsyms HlenL HlenD PREFIX TOTAL k y I Hk) as C.
  cbv zeta in C. destruct C as (Ecs & I1 & _).
  replace (Z.to_nat (N - k)) with (S (Z.to_nat (N - (k + 1)))) by lia. cbn [cb_calls_from].
  rewrite sbs_run_app, <- Ecs.
  set (y1 := sbs_run y (sym_calls y lfc ldl dfc ddl (3 * k))) in *. clearbody y1.
  rewrite (ci_sn _ _ _ _ _ _ _ I1).
  destruct (Z.ltb_spec (3 * k + 1 + 1 + 1) (3 * N)) as [Lt|Ge].
  - apply IH; [lia | exact I1 | lia | lia].
  - replace (Z.to_nat (N - (k + 1))) with 0%nat by lia. reflexivity.
Qed.

Lemma ov_compress_block_sec : forall y, CBI s0 ldl ddl N W0 0 y ->
  compress_block y lfc ldl dfc ddl = sbs_run y (cb_all s0 lfc ldl dfc ddl N).
Proof.
  intros y I. unfold compress_block, cb_all, cb_calls. rewrite (ci_sn _ _ _ _ _ _ _ I).
  rewrite sbs_run_app.
  destruct (Z.eqb_spec (3 * N) 0) as [Z0|NZ]; cbn [negb].
  - replace (Z.to_nat N) with 0%nat by lia. reflexivity.
  - rewrite (cb_loop_calls (Z.to_nat (3 * N)) 0 y 0 eq_refl I ltac:(lia) ltac:(lia)).
    replace (N - 0) with N by lia. reflexivity.
Qed.
End CB.

(** [compress_block] on the overlaid array emits the pristine symbols. *)
Lemma ov_compress_block : forall s0 lfc ldl dfc ddl N W0,
  0 <= N ->
  arr_len (ds_pending_buf s0) = ds_lit_bufsize s0 * 4 ->
  ds_lit_bufsize s0 + 3 * N + 3 <= arr_len (ds_pending_buf s0) ->
  (forall j, 0 <= j < N -> sym_okb s0 j) ->
  (forall j, 0 <= j < N -> 0 <= arr_get ldl (sym_lcode s0 j) <= 15) ->
  (forall j, 0 <= j < N -> sym_isdist s0 j = true -> 0 <= arr_get ddl (sym_dcode s0 j) <= 15) ->
  (forall k, 0 <= k < N -> W0 + zsum (dcost ldl ddl s0) 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s0 + 3 * k)) ->
  W0 + zsum (dcost ldl ddl s0) 0 (Z.to_nat N) <= 8 * arr_len (ds_pending_buf s0) ->
  forall y, CBI s0 ldl ddl N W0 0 y ->
  compress_block y lfc ldl dfc ddl = sbs_run y (cb_all s0 lfc ldl dfc ddl N).
Proof. intros. eapply ov_compress_block_sec; eassumption. Qed.

(** At a flush, dynamic branch. *)
Lemma ov_emit_dyn : forall s last,
  fb_entry s last ->
  tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 1 ->
  let X6 := ov_X6 s in
  let y := hX13 X6 last (ov_mb s) in
  compress_block y (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6)
  = sbs_run y (cb_all s (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6) (nsym s)).
Proof.
  intros s last FE HB X6 y. subst X6 y.
  pose proof (OP s last FE) as OPs. pose proof (tree_phase s OPs) as TP.
  pose proof (X6n s last FE) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _).
  pose proof (FEn s last FE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
  pose proof (branch1_lt _ _ _ (tp_opt _ TP) (tp_stat_range _ TP) HB) as LT.
  destruct (stat_val s last FE) as [SV SB]. pose proof (dyn_total s last FE) as DT.
  destruct (HDRs s last FE) as [[NB13 W13 BV13 BB13 PL13 PE13 PB13 PR13] _].
  pose proof (N_range s OPs) as RN.
  set (W0 := ds_bi_valid s + ov_hdr s).
  set (cost := dcost (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) s).
  assert (HE : 0 <= arr_get (ds_dyn_ltree_dl (ov_X6 s)) END_BLOCK <= 15).
  { pose proof (used_E s last FE) as X. rewrite Len_eq, tree_dl_TL in X. lia. }
  assert (TOTAL : W0 + zsum cost 0 (Z.to_nat (nsym s)) <= 8 * arr_len (ds_pending_buf s)).
  { rewrite F2. subst W0 cost. lia. }
  assert (PREFIX : forall k, 0 <= k < nsym s -> W0 + zsum cost 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s + 3 * k)).
  { intros k Hk. pose proof (overlay_core_proof s OPs HB k Hk) as X. unfold ov_wpos, ov_rpos, ov_LD, ov_DD in X. subst W0 cost. lia. }
  assert (HlenL : forall j, 0 <= j < nsym s -> 0 <= arr_get (ds_dyn_ltree_dl (ov_X6 s)) (sym_lcode s j) <= 15).
  { intros j Hj. pose proof (used_L s last FE j Hj) as X. rewrite Len_eq, tree_dl_TL in X. lia. }
  assert (HlenD : forall j, 0 <= j < nsym s -> sym_isdist s j = true -> 0 <= arr_get (ds_dyn_dtree_dl (ov_X6 s)) (sym_dcode s j) <= 15).
  { intros j Hj Hd. pose proof (used_D s last FE j Hj Hd) as X. rewrite Len_eq, tree_dl_TD in X. lia. }
  assert (Hroom : ds_lit_bufsize s + 3 * nsym s + 3 <= arr_len (ds_pending_buf s)) by (rewrite F2; lia).
  pose proof (nb_view_facts _ _ NB13) as (V1 & V2 & _).
  assert (CB0 : CBI s (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) (nsym s) W0 0 (hX13 (ov_X6 s) last (ov_mb s))).
  { constructor.
    - lia.
    - rewrite V1. exact P5.
    - rewrite PL13. symmetry. exact F2.
    - rewrite V2. exact P6.
    - rewrite W13. change (zsum _ 0 (Z.to_nat 0)) with 0. subst W0. lia.
    - exact BV13.
    - exact PB13.
    - exact PE13.
    - intros i Hi. rewrite (PR13 i Hi). rewrite P1. reflexivity. }
  exact (ov_compress_block s _ _ _ _ (nsym s) W0 (proj1 RN) F2 Hroom (op_syms _ OPs) HlenL HlenD PREFIX TOTAL _ CB0).
Qed.

(** At a flush, static branch (no branch hypothesis needed). *)
Lemma ov_emit_stat : forall s last,
  fb_entry s last ->
  let y := send_bits (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3 in
  compress_block y static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
  = sbs_run y (cb_all s static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl (nsym s)).
Proof.
  intros s last FE y. subst y.
  pose proof (OP s last FE) as OPs.
  pose proof (X6n s last FE) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _).
  pose proof (FEn s last FE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  pose proof (N_range s OPs) as RN.
  set (y0 := send_bits (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3).
  set (W0 := ds_bi_valid s + 3).
  set (cost := dcost static_ltree_dl static_dtree_dl s).
  assert (Esum : forall n, zsum cost 0 n = zsum (scost s) 0 n) by (intros; apply zsum_ext; intros; reflexivity).
  assert (TOTAL : W0 + zsum cost 0 (Z.to_nat (nsym s)) <= 8 * arr_len (ds_pending_buf s)).
  { rewrite F2, Esum. pose proof (zsum_bound (scost s) 0 (Z.to_nat (nsym s)) 31 ltac:(lia)
      ltac:(intros; apply (scost_bound s OPs); lia)). subst W0. lia. }
  assert (PREFIX : forall k, 0 <= k < nsym s -> W0 + zsum cost 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s + 3 * k)).
  { intros k Hk. rewrite Esum. pose proof (zsum_bound (scost s) 0 (Z.to_nat k) 31 ltac:(lia) ltac:(intros; apply (scost_bound s OPs); lia)).
    subst W0. lia. }
  assert (HlenL : forall j, 0 <= j < nsym s -> 0 <= arr_get static_ltree_dl (sym_lcode s j) <= 15).
  { intros j Hj. pose proof (static_ltree_dl_bound (sym_lcode s j)). lia. }
  assert (HlenD : forall j, 0 <= j < nsym s -> sym_isdist s j = true -> 0 <= arr_get static_dtree_dl (sym_dcode s j) <= 15).
  { intros j Hj _. pose proof (static_dtree_dl_bound (sym_dcode s j)). lia. }
  assert (Hroom : ds_lit_bufsize s + 3 * nsym s + 3 <= arr_len (ds_pending_buf s)) by (rewrite F2; lia).
  assert (Hbv6 : 0 <= ds_bi_valid (ov_X6 s) <= 16) by (rewrite P4; lia).
  pose proof (nb_view_facts _ _ (send_bits_nb_view (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3)) as (V1 & V2 & _).
  fold y0 in V1, V2.
  assert (CB0 : CBI s static_ltree_dl static_dtree_dl (nsym s) W0 0 y0).
  { constructor.
    - lia.
    - rewrite V1. exact P5.
    - subst y0. rewrite sb_pbl, P1. reflexivity.
    - rewrite V2. exact P6.
    - subst y0 W0. rewrite send_bits_W. change (zsum _ 0 (Z.to_nat 0)) with 0. unfold ov_W. rewrite P2, P4. lia.
    - subst y0. apply send_bits_biv; [exact Hbv6 | lia].
    - subst y0. apply send_bits_PBB. unfold PBB. rewrite P1. exact F12.
    - subst y0. pose proof (send_bits_pending_mono (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3). rewrite P2 in *. lia.
    - intros i Hi. subst y0. rewrite send_bits_frame by lia. rewrite P1. reflexivity. }
  exact (ov_compress_block s _ _ _ _ (nsym s) W0 (proj1 RN) F2 Hroom (op_syms _ OPs) HlenL HlenD PREFIX TOTAL _ CB0).
Qed.

(** The pristine calls depend only on the symbol bytes [[3j, 3(j+n))]. *)
Lemma cb_calls_from_ext : forall a b lfc ldl dfc ddl n j,
  (forall i, 3 * j <= i < 3 * (j + Z.of_nat n) -> sym_buf_get b i = sym_buf_get a i) ->
  cb_calls_from b lfc ldl dfc ddl j n = cb_calls_from a lfc ldl dfc ddl j n.
Proof.
  induction n as [|n IH]; intros j H; [reflexivity|]. cbn [cb_calls_from].
  rewrite Nat2Z.inj_succ in H.
  rewrite (sym_calls_ext a b).
  - rewrite IH; [reflexivity|]. intros i Hi. apply H. lia.
  - unfold sym_dist, sym_d0, sym_d1. rewrite !H by lia. reflexivity.
  - unfold sym_lc. rewrite H by lia. reflexivity.
Qed.

Lemma cb_calls_ext : forall a b lfc ldl dfc ddl N,
  (forall i, 0 <= i < 3 * N -> sym_buf_get b i = sym_buf_get a i) ->
  cb_calls b lfc ldl dfc ddl N = cb_calls a lfc ldl dfc ddl N.
Proof.
  intros a b lfc ldl dfc ddl N H. unfold cb_calls. apply cb_calls_from_ext.
  intros i Hi. apply H. lia.
Qed.
