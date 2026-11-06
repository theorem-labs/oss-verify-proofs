(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOps3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fupdZ {A} (f : Z -> A) (x : Z) (v : A) : Z -> A := fun y => if Z.eqb y x then v else f y.
Lemma fupdZ_same : forall A (f : Z -> A) x v, fupdZ f x v x = v.
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). rewrite Z.eqb_refl. reflexivity. Qed.
Lemma fupdZ_other : forall A (f : Z -> A) x v y, y <> x -> fupdZ f x v y = f y.
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec y x); [contradiction|reflexivity]. Qed.

Definition set_reg (st : ast) (c : Z) (r : region) : ast :=
  AST (fupdZ (a_reg st) c r) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st).
Definition set_cache (st : ast) (c : Z) (ks : list Z) : ast :=
  AST (a_reg st) (a_cinit st) (fupdZ (a_cache st) c ks) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st).
Definition set_cinit (st : ast) : ast :=
  AST (a_reg st) true (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st).
Definition set_tq (st : ast) (q : list batch) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) q (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st).
Definition set_gq (st : ast) (q : list batch) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) q (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st).
Definition set_sec (st : ast) (l : list schunk) (nres : Z) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) l nres (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st).

Definition set_hint (st : ast) (k v : Z) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (fupdZ (a_hint st) k v) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st).
Definition set_ialloc (st : ast) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) true (a_aa st) (a_kact st) (a_shsec st).
(* [comment removed for export] *)
Definition add_meter (st : ast) (cost : Z) (newaa : list (Z * Z)) (shs : Z) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st ++ newaa) (a_kact st + cost) (a_shsec st + shs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition op_cache_pop (st : ast) (c : Z) : ast := set_cache st c (removelast (a_cache st c)).
(* [comment removed for export] *)
Definition op_refill (st : ast) (c m : Z) : ast :=
  let r := a_reg st c in let n := Z.of_nat (length (r_free r)) in
  let keep := firstn (Z.to_nat (n - m)) (r_free r) in let taken := skipn (Z.to_nat (n - m)) (r_free r) in
  set_cache (set_reg st c (REG (r_mapped_user r) (r_alloc_user r) (r_mapped_fa r) keep (r_uhole r) (r_fhole r))) c taken.
(* [comment removed for export] *)
Definition carve_list (spacebeg c j0 newn : Z) : list Z :=
  map (fun i => compact_of spacebeg c (chunk_addr spacebeg c (j0 + (newn - 1 - Z.of_nat i)))) (seq 0 (Z.to_nat newn)).

(* [comment removed for export] *)
Definition op_sec_alloc (st : ast) (map n : Z) (grow : bool) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st ++ [SCH map n]) (if grow then a_nres st + 2 ^ 14 else a_nres st)
      (a_dep st) (a_hint st) (a_ialloc st) (a_aa st ++ sec_naa map n) (a_kact st) (a_shsec st).
(* [comment removed for export] *)
Definition blk_opt (o : option Z) : list Z := match o with Some p => [p] | None => [] end.
Definition store_aa (newstore : option Z) : list (Z * Z) := map (fun q => (q, q + 2 ^ 23)) (blk_opt newstore).
Definition op_depot_insert (st : ast) (b h s2 sid fr' : Z) (std' : Z -> Z) (newnode : option Z) (newstore : option Z) : ast :=
  let d := a_dep st in let id := dp_nids d + 1 in
  let d' := DEP id (fupdZ (dp_tab d) b id) (fupdZ (dp_hash d) id h) (fupdZ (dp_link d) id s2) (fupdZ (dp_store d) id sid)
                (dp_nodeblocks d ++ blk_opt newnode) (dp_storeblocks d ++ blk_opt newstore) fr' std' in
  (* [comment removed for export] *)
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) d' (a_hint st) (a_ialloc st)
      (a_aa st ++ store_aa newstore) (a_kact st) (a_shsec st).
(* [comment removed for export] *)
Definition op_meter := add_meter.
(* [comment removed for export] *)
Definition op_cache_init := set_cinit.

(* [comment removed for export] *)
Definition op_quar_append (st : ast) (m n : Z) : ast :=
  match rev (a_tq st) with
  | [] => st
  | b :: r => set_tq st (rev r ++ [BATCH (ba_addr b) (ba_items b ++ [(m, n)])])
  end.
(* [comment removed for export] *)
Definition op_quar_newbatch (st : ast) (ba m n : Z) : ast := set_tq st (a_tq st ++ [BATCH ba [(m, n)]]).
(* [comment removed for export] *)
Definition op_drain (st : ast) : ast := set_gq (set_tq st []) (a_gq st ++ a_tq st).

(* [comment removed for export] *)
Definition swap_remove {A} (l : list A) (i : nat) : list A :=
  match rev l with
  | [] => l
  | last :: r' => let l' := rev r' in if Nat.ltb i (length l') then firstn i l' ++ [last] ++ skipn (S i) l' else l'
  end.
(* [comment removed for export] *)
Fixpoint remove1_iv (iv : Z * Z) (A : list (Z * Z)) : list (Z * Z) :=
  match A with
  | [] => []
  | x :: r => if (Z.eqb (fst x) (fst iv) && Z.eqb (snd x) (snd iv))%bool then r else x :: remove1_iv iv r
  end.
Definition release_aa (A : list (Z * Z)) (mp n : Z) : list (Z * Z) := remove1_iv (sec_hull_lo mp, sec_hull_hi mp n) A ++ sec_edges mp n.
(* [comment removed for export] *)
Definition op_sec_release (st : ast) (mp n : Z) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st)
      (release_aa (a_aa st) mp n) (a_kact st) (a_shsec st).
(* [comment removed for export] *)
Definition sec_entry (st : ast) (i : nat) : schunk := nth i (a_sec st) (SCH 0 0).
Definition op_sec_free (st : ast) (i : nat) : ast :=
  let s := sec_entry st i in
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (swap_remove (a_sec st) i) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st)
      (release_aa (a_aa st) (sc_map s) (sc_n s)) (a_kact st) (a_shsec st + 2 * PG).
(* [comment removed for export] *)
Definition op_cache_push (st : ast) (c k : Z) : ast := set_cache st c (a_cache st c ++ [k]).

(* [comment removed for export] *)
Definition op_fake_alloc (st : ast) (k newhint : Z) : ast := set_hint st k newhint.
Definition op_fake_release (st : ast) : ast := st.
(* [comment removed for export] *)
Definition op_ialloc_init := set_ialloc.

(* [comment removed for export] *)
Definition op_uhole (st : ast) (c : Z) : ast :=
  let r := a_reg st c in set_reg st c (REG (r_mapped_user r) (r_alloc_user r) (r_mapped_fa r) (r_free r) true (r_fhole r)).
Definition op_fhole (st : ast) (c : Z) : ast :=
  let r := a_reg st c in set_reg st c (REG (r_mapped_user r) (r_alloc_user r) (r_mapped_fa r) (r_free r) (r_uhole r) true).
(* [comment removed for export] *)
Definition op_usermap (st : ast) (c : Z) : ast :=
  let r := a_reg st c in set_reg st c (REG (r_mapped_user r + KUSERMAP) (r_alloc_user r) (r_mapped_fa r) (r_free r) false (r_fhole r)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac proj_cbn := cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in *.

Section WFops.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition mu_room (st : ast) : Prop := sum_mu st + KUSERMAP <= KUSERMAP * (a_kact st / EVT).
  Definition sec_room (st : ast) : Prop := a_shsec st + 2 * PG * (Z.of_nat (length (a_sec st)) + 1) <= 2 * PG * (a_kact st / EVT).

  (* [comment removed for export] *)
  Definition OPS_WF_cache_pop : Prop := forall st Lc FF c ks k n,
    WF bt st Lc FF -> 1 <= c <= 30 -> a_cache st c = ks ++ [k] ->
    1 <= n <= NMAX -> is_primary n = true -> class_of (needed n) = c ->
    Z.of_nat (length Lc) + 1 <= LMAX -> PHI Lc + (n + MBLK) <= GBUDGET ->      (* [comment removed for export] *)
    let p := chunk_of_compact SBEG c k + rz n in
    WF bt (op_cache_pop st c) ((p, n) :: Lc) FF.

  (* [comment removed for export] *)
  Lemma WF_cache_init : forall st Lc FF, WF bt st Lc FF -> WF bt (op_cache_init st) Lc FF.
  Proof.
    intros st Lc FF W.
    destruct W as (WR & WC & WQ & WS & WL & WK & WD & WM & WMP & G).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, op_cache_init, set_cinit in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
    split; [exact WR|]. split.
    { intros c Hc. destruct (WC c Hc) as (C1 & C2 & C3). split; [exact C1|]. split; [intros H; discriminate H | exact C3]. }
    split; [exact WQ|]. split; [exact WS|]. split; [exact WL|]. split; [exact WK|]. split; [exact WD|]. split; [exact WM|]. split; [exact WMP|]. exact G.
  Qed.

  (* [comment removed for export] *)
  Definition OPS_WF_refill : Prop := forall st Lc FF c m,
    WF bt st Lc FF -> 1 <= c <= 30 -> a_cache st c = [] -> a_cinit st = true -> m = cache_hint c ->
    m <= Z.of_nat (length (r_free (a_reg st c))) ->
    WF bt (op_refill st c m) Lc FF.


  (* [comment removed for export] *)
  Definition OPS_WF_sec_alloc : Prop := forall st Lc FF map n grow,
    WF bt st Lc FF -> 64513 <= n <= NMAX -> map mod PG = 0 -> dyn_ok (bt_ia bt) map (map + sec_map_size n) ->
    (forall lo hi, In (lo, hi) (all_ranges bt st) -> map + sec_map_size n <= lo \/ hi <= map) ->
    (grow = true <-> Z.of_nat (length (a_sec st)) = a_nres st) -> (grow = true -> a_nres st + 2 ^ 14 <= 2 ^ 20) ->   (* [comment removed for export] *)
    Z.of_nat (length Lc) + 1 <= LMAX -> PHI Lc + (n + MBLK) <= GBUDGET ->      (* [comment removed for export] *)
    (forall b n0, In (b, n0) (bt_maps0 bt) -> map + sec_map_size n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned n0 <= map) ->   (* [comment removed for export] *)
    sec_room st ->                                                             (* [comment removed for export] *)
    WF bt (op_sec_alloc st map n grow) ((map + sec_user_off n, n) :: Lc) FF.

  (* [comment removed for export] *)
  Definition depot_room (st : ast) : Prop :=
    dp_nids (a_dep st) + 1 <= dp_nids (bt_dep0 bt) + a_kact st / EVT
    /\ dp_frames (a_dep st) + FRW <= dp_frames (bt_dep0 bt) + FRW * (a_kact st / EVT) + FRW * Z.of_nat (length (dp_storeblocks (a_dep st))).
  Definition OPS_WF_depot_insert : Prop := forall st Lc FF b h s2 sid fr' std' newnode newstore,
    WF bt st Lc FF -> 0 <= b < 2 ^ 20 -> 0 <= h < 2 ^ 64 -> 0 <= sid < 2 ^ 32 -> (forall i, 0 <= std' i < 2 ^ 32) ->
    s2 = dp_tab (a_dep st) b ->
    depot_room st ->                                                          (* [comment removed for export] *)
    dp_nids (a_dep st) + 1 < 2 ^ 31 - 1 ->                                    (* [comment removed for export] *)
    (newnode = None <-> (dp_nids (a_dep st) + 1) / 2 ^ 16 = Z.of_nat (length (dp_nodeblocks (a_dep st)))) ->
    dp_frames (a_dep st) <= fr' <= dp_frames (a_dep st) + FRW + FRW * Z.of_nat (length (blk_opt newstore)) ->
    Z.of_nat (length (dp_storeblocks (a_dep st) ++ blk_opt newstore)) = Z.min (Z.max 0 ((fr' - 1) / 2 ^ 20)) (2 ^ 12 - 1) ->
    Z.of_nat (length (dp_storeblocks (a_dep st) ++ blk_opt newstore)) + 1 <= 2 ^ 12 ->
    (forall p, newnode = Some p -> dyn_ok (bt_ia bt) p (p + 2 ^ 20) /\ p mod PG = 0 /\
        forall lo hi, In (lo, hi) (all_ranges bt st) -> p + 2 ^ 20 <= lo \/ hi <= p) ->
    (forall p, newstore = Some p -> dyn_ok (bt_ia bt) p (p + 2 ^ 23) /\ p mod PG = 0 /\
        forall lo hi, In (lo, hi) (all_ranges bt st) -> p + 2 ^ 23 <= lo \/ hi <= p) ->
    (forall p q, newnode = Some p -> newstore = Some q -> p + 2 ^ 20 <= q \/ q + 2 ^ 23 <= p) ->
    (* [comment removed for export] *)
    (forall p b0 n0, newnode = Some p -> In (b0, n0) (bt_maps0 bt) -> p + 2 ^ 20 <= bv_unsigned b0 \/ bv_unsigned b0 + bv_unsigned n0 <= p) ->
    (forall p b0 n0, newstore = Some p -> In (b0, n0) (bt_maps0 bt) -> p + 2 ^ 23 <= bv_unsigned b0 \/ bv_unsigned b0 + bv_unsigned n0 <= p) ->
    WF bt (op_depot_insert st b h s2 sid fr' std' newnode newstore) Lc FF.

  (* [comment removed for export] *)
  Lemma WFq_meter : forall st Lc FF cost naa shs qt qg, WFq bt st Lc FF qt qg -> 0 <= cost -> shs = 0 ->
    WFq bt (op_meter st cost naa shs) Lc FF qt qg.
  Proof.
    intros st Lc FF cost naa shs qt qg W.
    destruct W as (WR & WC & WQ & WS & WL & WK & WD & WME & WMP & G). intros Hc Hs. subst shs.
    (lazymatch goal with |- ?G => let G' := eval unfold WFq, op_meter, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
    assert (MONO : a_kact st / EVT <= (a_kact st + cost) / EVT) by (apply Z.div_le_mono; (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia).
    split; [exact WR|]. split; [exact WC|]. split; [exact WQ|]. split; [exact WS|]. split; [exact WL|]. split; [exact WK|].
    split. { destruct WD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & Drest). (lazymatch goal with |- ?G => let G' := eval unfold wf_depot in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep a_kact] in G in change_no_check G' end).
             split; [exact D1|]. split; [lia|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|].
             split; [exact D7|]. split; [exact D8|]. split; [unfold FRW in *; lia | exact Drest]. }
    split.
    { destruct WME as (M1 & M2 & M3 & M4 & M5). (lazymatch goal with |- ?G => let G' := eval unfold wf_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_shsec a_sec a_reg] in G in change_no_check G' end).
      change (sum_mu (AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st)
                          (a_aa st ++ naa) (a_kact st + cost) (a_shsec st + 0))) with (sum_mu st).
      unfold PG, KUSERMAP in *. split; [lia|]. split; [lia|]. split; [nia|]. split; [nia|]. exact M5. }
    split; [exact WMP|]. exact G.
  Qed.
  Lemma WF_meter : forall st Lc FF cost naa shs, WF bt st Lc FF -> 0 <= cost -> shs = 0 ->
    WF bt (op_meter st cost naa shs) Lc FF.
  Proof. intros st Lc FF cost naa shs. apply WFq_meter. Qed.

  (* [comment removed for export] *)
  Lemma depot_room_meter : forall st Lc FF cost naa shs, WF bt st Lc FF -> EVT <= cost -> depot_room (op_meter st cost naa shs).
  Proof.
    intros st Lc FF cost naa shs W Hc. destruct W as (_ & _ & _ & _ & _ & _ & WD & WME & _).
    destruct WD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & Drest).
    (lazymatch goal with |- ?G => let G' := eval unfold depot_room, op_meter, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep a_kact] in G in change_no_check G' end).
    assert (MONO : a_kact st / EVT + 1 <= (a_kact st + cost) / EVT).
    { replace (a_kact st / EVT + 1) with ((a_kact st + 1 * EVT) / EVT) by (apply Z.div_add; (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia).
      apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | lia]. }
    unfold FRW in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma rooms_meter : forall st Lc FF cost naa qt qg, WFq bt st Lc FF qt qg -> EVT <= cost ->
    mu_room (op_meter st cost naa 0) /\ sec_room (op_meter st cost naa 0) /\ depot_room (op_meter st cost naa 0).
  Proof.
    intros st Lc FF cost naa qt qg W Hc. destruct W as (_ & _ & _ & _ & _ & _ & WD & WME & _).
    destruct WD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & Drest). destruct WME as (M1 & M2 & M3 & M4 & M5).
    (lazymatch goal with |- ?G => let G' := eval unfold mu_room, sec_room, depot_room, op_meter, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep a_kact a_shsec a_sec a_reg] in G in change_no_check G' end).
    change (sum_mu (AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st)
                        (a_aa st ++ naa) (a_kact st + cost) (a_shsec st + 0))) with (sum_mu st).
    assert (MONO : a_kact st / EVT + 1 <= (a_kact st + cost) / EVT).
    { replace (a_kact st / EVT + 1) with ((a_kact st + 1 * EVT) / EVT) by (apply Z.div_add; (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia).
      apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | lia]. }
    unfold FRW, PG, KUSERMAP in *. split; [nia|]. split; [nia|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kcap_evt_bound : 9 * (KCAP / EVT) + 2 ^ 20 + 9 * 2 ^ 12 + 9 <= 2 ^ 32.
  Proof. vm_compute. intros H. discriminate H. Qed.
  Lemma depot_nids_room : forall st Lc FF, WF bt st Lc FF -> depot_room st -> a_kact st <= KCAP -> dp_nids (bt_dep0 bt) <= 2 ^ 20 ->
    dp_nids (a_dep st) + 1 < 2 ^ 31 - 1.
  Proof.
    intros st Lc FF W [R1 R2] HK H0.
    assert (Q : a_kact st / EVT <= KCAP / EVT) by (apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | exact HK]).
    pose proof kcap_evt_bound as E. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma depot_frames_room : forall st Lc FF, WF bt st Lc FF -> depot_room st -> a_kact st <= KCAP -> dp_frames (bt_dep0 bt) <= 2 ^ 20 ->
    dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Proof.
    intros st Lc FF W [R1 R2] HK H0. destruct W as (_ & _ & _ & _ & _ & _ & WD & _).
    destruct WD as (_ & _ & _ & _ & _ & _ & _ & D8 & _).
    assert (Q : a_kact st / EVT <= KCAP / EVT) by (apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | exact HK]).
    pose proof kcap_evt_bound as E. clear - R2 D8 Q H0 E. unfold FRW in *. lia.
  Qed.



    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma WF_fake_alloc : forall st Lc FF k pos newhint,
    WF bt st Lc FF -> 0 <= k <= KMAXCLASS -> 0 <= pos < FCAP k -> 0 <= newhint ->
    ~ In (fake_frame_addr (bt_fs bt) k pos, k) FF ->
    WF bt (op_fake_alloc st k newhint) Lc ((fake_frame_addr (bt_fs bt) k pos, k) :: FF).
  Proof.
    intros st Lc FF k pos newhint W Hk Hpos Hh NI.
    destruct W as (WR & WC & WQ & WS & WL & (K1 & K2 & K3) & WD & WME & WMP & G).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, op_fake_alloc, set_hint in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
    split; [exact WR|]. split; [exact WC|]. split; [exact WQ|]. split; [exact WS|]. split; [exact WL|].
    split.
    { split.
      - intros f k' [E | Hin]; [|exact (K1 f k' Hin)]. injection E as <- <-.
        assert (EP : fpos bt (fake_frame_addr (bt_fs bt) k pos) k = pos).
        { (lazymatch goal with |- ?G => let G' := eval unfold fpos, fake_frame_addr in G in change_no_check G' end).
          replace (bt_fs bt + 0x9000 + k * 2 ^ 20 + FS k * pos - (bt_fs bt + 0x9000 + k * 2 ^ 20)) with (pos * FS k) by lia.
          apply Z.div_mul. (lazymatch goal with |- ?G => let G' := eval unfold FS in G in change_no_check G' end). assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). lia. }
        rewrite EP. repeat split; try lia.
      - split; [constructor; [exact NI | exact K2]|]. intros k'. proj_cbn. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb k' k); [lia | exact (K3 k')]. }
    split; [exact WD|]. split; [exact WME|]. split; [exact WMP|]. exact G.
  Qed.

  (* [comment removed for export] *)
  Lemma WF_fake_release : forall st Lc FF F1 F2 f k,
    WF bt st Lc FF -> FF = F1 ++ (f, k) :: F2 -> WF bt (op_fake_release st) Lc (F1 ++ F2).
  Proof.
    intros st Lc FF F1 F2 f k W E.
    destruct W as (WR & WC & WQ & WS & WL & (K1 & K2 & K3) & WD & WME & WMP & G).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, op_fake_release in G in change_no_check G' end). split; [exact WR|]. split; [exact WC|]. split; [exact WQ|]. split; [exact WS|]. split; [exact WL|].
    split.
    { split.
      - intros f' k' Hin. apply K1. rewrite E. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [X|X]; [left; exact X | right; right; exact X].
      - split; [|exact K3]. rewrite E in K2. exact (NoDup_remove_1 _ _ _ K2). }
    split; [exact WD|]. split; [exact WME|]. split; [exact WMP|]. exact G.
  Qed.

  (* [comment removed for export] *)
  Lemma WF_ialloc_init : forall st Lc FF, WF bt st Lc FF -> WF bt (op_ialloc_init st) Lc FF.
  Proof.
    intros st Lc FF W. destruct W as (WR & WC & WQ & WS & WL & WK & WD & WME & WMP & G).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, op_ialloc_init, set_ialloc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). repeat (split; [assumption|]). exact G.
  Qed.
End WFops.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RepOps.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Definition agrees_off (FOOT : Z -> Prop) (M M' : mem) : Prop :=
    forall a : word, M' a <> M a -> FOOT (bv_unsigned a) /\ M' a <> None.

  (* [comment removed for export] *)
  Definition foot_cache_hit (c p n : Z) (a : Z) : Prop :=
    (T + T_PC + PC_SZ * c <= a < T + T_PC + PC_SZ * c + 4)            (* [comment removed for export] *)
    \/ (T + 2768 <= a < T + 2800 + 368)                                 (* [comment removed for export] *)
    \/ (p - rz n <= a < p + n)                                           (* [comment removed for export] *)
    \/ (sh_lo p <= a < sh_hi p n)                                        (* [comment removed for export] *)
    \/ CEIL <= a.                                                        (* [comment removed for export] *)
  Definition OPS_REP_cache_hit : Prop := forall st Lc FF M M' mdl mdl' c ks k n,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 -> a_cache st c = ks ++ [k] ->
    1 <= n <= NMAX -> is_primary n = true -> class_of (needed n) = c ->
    let ab := chunk_of_compact SBEG c k in let p := ab + rz n in
    agrees_off (foot_cache_hit c p n) M M' ->
    cellZ SG M' (T + T_PC + PC_SZ * c) 4 (Z.of_nat (length ks)) ->
    rep_hdr bt M' p n 2 ->
    (forall i, 0 <= i < n / 8 -> M' (Z_to_bv 64 (sh_lo p + i)) = Some (Z_to_bv 8 0)) ->
    (n mod 8 <> 0 -> M' (Z_to_bv 64 (sh_lo p + n / 8)) = Some (Z_to_bv 8 (n mod 8))) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_cache_pop st c) ((p, n) :: Lc) FF M' mdl'.

  (* [comment removed for export] *)
  Definition foot_fake_alloc (k f : Z) (a : Z) : Prop :=
    (bt_fs bt + 8 * k <= a < bt_fs bt + 8 * k + 8) \/ (bt_fs bt + 0x1000 <= a < bt_fs bt + 0x9000)
    \/ (f <= a < f + FS k) \/ (sh_lo f <= a < sh_hi f (FS k)) \/ CEIL <= a.
  Definition OPS_REP_fake_alloc : Prop := forall st Lc FF M M' mdl mdl' k pos newhint,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 0 <= k <= KMAXCLASS -> 0 <= pos < FCAP k -> 0 <= newhint < 2 ^ 64 ->
    let f := fake_frame_addr (bt_fs bt) k pos in
    ~ In (f, k) FF ->
    agrees_off (foot_fake_alloc k f) M M' ->
    cellZ SG M' (bt_fs bt + 8 * k) 8 newhint ->
    byteZ SG M' (fake_flag_addr (bt_fs bt) k pos) 1 ->
    (forall k' pos', 0 <= k' <= 10 -> 0 <= pos' < FCAP k' -> (k', pos') <> (k, pos) ->
        M' (Z_to_bv 64 (fake_flag_addr (bt_fs bt) k' pos')) = M (Z_to_bv 64 (fake_flag_addr (bt_fs bt) k' pos'))) ->
    cellZ SG M' (f + FS k - 8) 8 (fake_flag_addr (bt_fs bt) k pos) ->
    (forall i, sh_lo f <= i < sh_hi f (FS k) -> M' (Z_to_bv 64 i) <> None) ->       (* [comment removed for export] *)
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_fake_alloc st k newhint) Lc ((f, k) :: FF) M' mdl'.

  (* [comment removed for export] *)
  Definition OPS_REP_fake_release : Prop := forall st Lc FF F1 F2 M M' mdl f k,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> FF = F1 ++ (f, k) :: F2 ->
    agrees_off (fun a => a = fake_flag_addr (bt_fs bt) k (fpos bt f k)) M M' ->
    byteZ SG M' (fake_flag_addr (bt_fs bt) k (fpos bt f k)) 0 ->
    Rep bt (op_fake_release st) Lc (F1 ++ F2) M' mdl.

  (* [comment removed for export] *)
  Definition foot_quar_append (p n ba : Z) (cnt : Z) (a : Z) : Prop :=
    a = p - 16 \/ (p <= a < p + 8) \/ (sh_lo p <= a < sh_hi p n)
    \/ (ba + 8 <= a < ba + 24) \/ (ba + 24 + 8 * cnt <= a < ba + 32 + 8 * cnt)
    \/ (T + T_QC + 24 <= a < T + T_QC + 32) \/ (T + 2800 <= a < T + 3168) \/ CEIL <= a.
  Definition OPS_REP_quar_append : Prop := forall st Lc FF L1 L2 M M' mdl mdl' p n tq' b,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> Lc = L1 ++ (p, n) :: L2 -> a_tq st = tq' ++ [b] ->
    Z.of_nat (length (ba_items b)) < BATCHCAP ->                        (* [comment removed for export] *)
    let cnt := Z.of_nat (length (ba_items b)) in
    agrees_off (foot_quar_append p n (ba_addr b) cnt) M M' ->
    byteZ SG M' (p - 16) 3 ->
    (forall g, user_granule p n g -> byteZ SG M' (SB + g) 0xfd) ->
    cellZ SG M' (ba_addr b + 8) 8 (ba_bytes b + n) -> cellZ SG M' (ba_addr b + 16) 8 (cnt + 1) ->
    cellZ SG M' (ba_addr b + 24 + 8 * cnt) 8 (p - 16) ->
    cellZ SG M' (T + T_QC + 24) 8 (q_bytes (a_tq st) + n) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_quar_append st (p - 16) n) (L1 ++ L2) FF M' mdl'.



  (* [comment removed for export] *)
  Definition OPS_REP_meter : Prop := forall st Lc FF M mdl mdl' cost naa shs,
    Rep bt st Lc FF M mdl ->
    m_vmmaps mdl' = m_vmmaps mdl -> (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                   /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    A_wf (a_aa st ++ naa) -> MInv (a_aa st ++ naa) mdl' ->
    eager_used mdl' <= eager_used mdl -> A_bytes naa <= shs ->
    Rep bt (op_meter st cost naa shs) Lc FF M mdl'.
End RepOps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Reads.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).



  Lemma read_consts : forall st Lc FF M mdl, Rep bt st Lc FF M mdl -> cells_hold SG M (bt_consts bt).
  Proof. intros st Lc FF M mdl R. destruct R as (X & _). exact X. Qed.

  Lemma read_thread : forall st Lc FF M mdl, Rep bt st Lc FF M mdl ->
    cellZ SG M (bt_thread bt) 8 (bt_tctx bt) /\ cellZ SG M (bt_thread bt + 8) 8 (bt_stack_top bt)
    /\ cellZ SG M (bt_thread bt + 16) 8 (bt_stack_bottom bt) /\ byteZ SG M (bt_thread bt + 40) 0
    /\ cellZ SG M (bt_thread bt + 72) 8 (bt_fs bt) /\ byteZ SG M (bt_thread bt + T_UNW) 0
    /\ cellZ SG M (bt_tctx bt + 152) 8 (bt_thread bt) /\ cellZ SG M (bt_tctx bt + 8) 4 0.
  Proof.
    intros st Lc FF M mdl R. destruct R as (_ & _ & RT & _). destruct RT as (A & B & C & D & E & F & _ & _ & _ & G & H & _).
    repeat split; assumption.
  Qed.


  (* [comment removed for export] *)
  Lemma read_tls : forall st Lc FF M mdl, Rep bt st Lc FF M mdl ->
    cellZ SG M (bt_thread bt + 48) 8 (bt_tp bt + 0x738) /\ cellZ SG M (bt_thread bt + 56) 8 (bt_tp bt + 0x814)
    /\ cellZ SG M (bt_tls_fs bt + 8) 8 (bt_dtls bt) /\ cellZ SG M (bt_dtls bt + 24) 8 (bt_tp bt).
  Proof.
    intros st Lc FF M mdl R. destruct R as (_ & _ & RT & _ & _ & _ & _ & _ & _ & RF & _).
    destruct RT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T48 & T56). destruct RF as (_ & _ & _ & _ & _ & _ & _ & D1 & D2).
    exact (conj T48 (conj T56 (conj D1 D2))).
  Qed.

End Reads.
End AsAinvOps3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsPf3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b AsAinvOps3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma A_bytes_app : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. induction l1 as [|iv r IH]; intros l2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [reflexivity | rewrite IH; lia]. Qed.

Lemma page_allowedb_app_l : forall l1 l2 p, page_allowedb l1 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros l1 l2 p H. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.

Lemma range_allowed_app : forall AA AA' lo hi, range_allowed AA lo hi -> range_allowed (AA ++ AA') lo hi.
Proof. intros AA AA' lo hi H a Ha. apply page_allowedb_app_l. exact (H a Ha). Qed.

(* [comment removed for export] *)
Lemma page_allowedb_app_r : forall l1 l2 p, page_allowedb l2 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros l1 l2 p H. unfold page_allowedb in *. rewrite existsb_app, H. apply Bool.orb_true_r. Qed.
Lemma range_allowed_hull : forall AA mp n,
  0 <= sh_lo mp -> sh_hi mp (sec_map_size n) < 2 ^ 64 ->
  range_allowed (AA ++ sec_naa mp n) (sh_lo mp) (sh_hi mp (sec_map_size n)).
Proof.
  intros AA mp n H0 H64 a Ha. apply page_allowedb_app_r. (lazymatch goal with |- ?G => let G' := eval unfold page_allowedb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sec_naa existsb fst snd] in G in change_no_check G' end). rewrite Bool.orb_false_r.
  (lazymatch goal with |- ?G => let G' := eval unfold sec_hull_lo, sec_hull_hi, pgdn, pgup, PG in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold page_base, page_base_of, page_size in G in change_no_check G' end).
  rewrite (u64_lit a) by lia.
  assert (R : 0 <= a / 4096 * 4096 < 2 ^ 64) by (Z.div_mod_to_equations; lia). rewrite u64_lit by exact R.
  apply andb_true_intro; split; apply Z.leb_le; Z.div_mod_to_equations; nia.
Qed.
Lemma A_wf_sec_naa : forall AA mp n, A_wf AA -> 0 <= sec_map_size n -> A_wf (AA ++ sec_naa mp n).
Proof.
  intros AA mp n H Hn. unfold A_wf in *. apply Forall_app. split; [exact H|]. constructor; [| constructor]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
  (lazymatch goal with |- ?G => let G' := eval unfold sec_hull_lo, sec_hull_hi in G in change_no_check G' end). split; [| split; [apply pgdn_mod | apply pgup_mod]].
  pose proof (pgdn_le (sh_lo mp)). pose proof (pgup_ge (sh_hi mp (sec_map_size n))).
  assert (sh_lo mp <= sh_hi mp (sec_map_size n)) by ((lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end); apply Z.add_le_mono_l; apply Z.div_le_mono; lia). lia.
Qed.

Lemma agrees_DEFK : forall FOOT M M', agrees_off FOOT M M' -> DEFK M M'.
Proof. intros FOOT M M' H a Ha. exact (proj2 (H a Ha)). Qed.

Lemma agrees_at' : forall (FOOT : Z -> Prop) M M', agrees_off FOOT M M' ->
  forall i, ~ FOOT i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
  intros FOOT M M' H. apply (agree_at (fun i => ~ FOOT i) M M'). intros a Ha NF. exact (NF (proj1 (H a Ha))).
Qed.


Section Pf.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  (* [comment removed for export] *)
  Ltac Ztac := Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Rep_sbm : forall st Lc FF M mdl mdl',
    Rep bt st Lc FF M mdl -> MInv (a_aa st) mdl' -> same_but_materialized mdl mdl' -> Rep bt st Lc FF M mdl'.
  Proof.
    intros st Lc FF M mdl mdl' R MI S.
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    pose proof (same_but_materialized_frame mdl mdl' S) as F.
    destruct F as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). repeat (split; [assumption|]) || idtac.
    split; [exact (rep_ledger_sbm bt st mdl mdl' S R13)|].
    split; [| exact R15].
    (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). rewrite E3. repeat (split; [assumption|]). exact B8.
  Qed.


  Theorem OPS_REP_meter_pf : OPS_REP_meter bt.
  Proof.
    intros st Lc FF M mdl mdl' cost naa shs R EM EL FL AW MI EAG SHS.
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). repeat (split; [assumption|]) || idtac.
    split.
    { (* [comment removed for export] *) destruct R13 as (L1 & L2 & L3 & L4 & L5). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_sec a_dep a_reg a_nres op_meter add_meter] in G in change_no_check G' end).
      rewrite EM. split; [exact L1|]. split; [exact L2|]. split; [| split; [exact FL | exact L5]].
      intros a. rewrite (EL a). exact (L3 a). }
    split; [| exact R15].
    destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa a_kact a_shsec a_reg a_sec a_dep a_nres op_meter add_meter] in G in change_no_check G' end).
    split; [exact AW|]. split; [exact MI|].
    split; [intros lo hi H; apply range_allowed_app; exact (B3 lo hi H)|].
    split; [intros p n H; apply range_allowed_app; exact (B4 p n H)|].
    split; [intros c Hc; destruct (B5 c Hc) as [X Y]; split; apply range_allowed_app; assumption|].
    split; [intros s Hs; apply range_allowed_app; exact (B6 s Hs)|].
    split; [intros b Hb; apply range_allowed_app; exact (B7 b Hb)|].
    rewrite A_bytes_app. change (prim_charge (op_meter st cost naa shs)) with (prim_charge st).
    change (sec_charge (op_meter st cost naa shs)) with (sec_charge st). change (depot_charge (op_meter st cost naa shs)) with (depot_charge st).
    destruct B8 as [B8 B9]. split; [lia|].
    (* [comment removed for export] *)
    intros s0 Hs0. apply in_app_iff. left. exact (B9 s0 Hs0).
  Qed.


  (* [comment removed for export] *)
End Pf.
End AsAinvOpsPf3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvHole3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b AsAinvOps3 AsAinvOpsPf3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition regdata_eq (r r' : region) : Prop :=
  r_mapped_user r' = r_mapped_user r /\ r_alloc_user r' = r_alloc_user r /\ r_mapped_fa r' = r_mapped_fa r /\ r_free r' = r_free r.
(* [comment removed for export] *)
Definition st_regdata (st st' : ast) : Prop :=
  (forall c, regdata_eq (a_reg st c) (a_reg st' c))
  /\ (forall c, ~ (1 <= c <= 30) -> a_reg st' c = a_reg st c)
  /\ a_cinit st' = a_cinit st /\ a_cache st' = a_cache st /\ a_tq st' = a_tq st /\ a_gq st' = a_gq st
  /\ a_sec st' = a_sec st /\ a_nres st' = a_nres st /\ a_dep st' = a_dep st /\ a_hint st' = a_hint st
  /\ a_ialloc st' = a_ialloc st /\ a_aa st' = a_aa st /\ a_kact st' = a_kact st /\ a_shsec st' = a_shsec st.

Lemma st_regdata_uhole : forall st c, 1 <= c <= 30 -> st_regdata st (op_uhole st c).
Proof.
  intros st c Hc. (lazymatch goal with |- ?G => let G' := eval unfold st_regdata, op_uhole, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
  split. { intros c'. (lazymatch goal with |- ?G => let G' := eval unfold regdata_eq, fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity. }
  split. { intros c' NC. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; [exfalso; exact (NC Hc) | reflexivity]. }
  repeat split; reflexivity.
Qed.
Lemma st_regdata_fhole : forall st c, 1 <= c <= 30 -> st_regdata st (op_fhole st c).
Proof.
  intros st c Hc. (lazymatch goal with |- ?G => let G' := eval unfold st_regdata, op_fhole, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
  split. { intros c'. (lazymatch goal with |- ?G => let G' := eval unfold regdata_eq, fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity. }
  split. { intros c' NC. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; [exfalso; exact (NC Hc) | reflexivity]. }
  repeat split; reflexivity.
Qed.

Lemma uhole_flags : forall st c c',
  r_uhole (a_reg (op_uhole st c) c') = (if Z.eqb c' c then true else r_uhole (a_reg st c'))
  /\ r_fhole (a_reg (op_uhole st c) c') = r_fhole (a_reg st c').
Proof. intros st c c'. (lazymatch goal with |- ?G => let G' := eval unfold op_uhole, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); split; reflexivity. Qed.
Lemma fhole_flags : forall st c c',
  r_fhole (a_reg (op_fhole st c) c') = (if Z.eqb c' c then true else r_fhole (a_reg st c'))
  /\ r_uhole (a_reg (op_fhole st c) c') = r_uhole (a_reg st c').
Proof. intros st c c'. (lazymatch goal with |- ?G => let G' := eval unfold op_fhole, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); split; reflexivity. Qed.
Lemma usermap_fields : forall st c c',
  r_mapped_user (a_reg (op_usermap st c) c') = (if Z.eqb c' c then r_mapped_user (a_reg st c') + KUSERMAP else r_mapped_user (a_reg st c'))
  /\ r_alloc_user (a_reg (op_usermap st c) c') = r_alloc_user (a_reg st c')
  /\ r_mapped_fa (a_reg (op_usermap st c) c') = r_mapped_fa (a_reg st c')
  /\ r_free (a_reg (op_usermap st c) c') = r_free (a_reg st c')
  /\ r_uhole (a_reg (op_usermap st c) c') = (if Z.eqb c' c then false else r_uhole (a_reg st c'))
  /\ r_fhole (a_reg (op_usermap st c) c') = r_fhole (a_reg st c').
Proof.
  intros st c c'. (lazymatch goal with |- ?G => let G' := eval unfold op_usermap, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RegData.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Variables st st' : ast.
  Hypothesis EQ : st_regdata st st'.
  (* [comment removed for export] *)
  Hypothesis FHX : forall c, 1 <= c <= 30 -> r_fhole (a_reg st' c) = true ->
    r_fhole (a_reg st c) = true \/ r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29.

  Lemma carved_regdata : forall c a, carved bt st' c a <-> carved bt st c a.
  Proof. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold carved in G in change_no_check G' end). destruct (proj1 EQ c) as (_ & RAU & _). rewrite RAU. tauto. Qed.

  Lemma quar_regdata : quar st' = quar st.
  Proof. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & ETQ & EGQ & _). rewrite ETQ, EGQ. reflexivity. Qed.

  Lemma registered_regdata : forall p n, registered st' p n <-> registered st p n.
  Proof. intros p n. (lazymatch goal with |- ?G => let G' := eval unfold registered in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & _ & _ & ES & _). rewrite ES. tauto. Qed.

  Lemma in_quar_c_regdata : forall c a, in_quar_c st' c a <-> in_quar_c st c a.
  Proof. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). rewrite quar_regdata. tauto. Qed.
  Lemma in_cache_c_regdata : forall c a, in_cache_c bt st' c a <-> in_cache_c bt st c a.
  Proof. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c in G in change_no_check G' end). destruct EQ as (_ & _ & _ & EC & _). rewrite EC. tauto. Qed.
  Lemma in_fa_c_regdata : forall c a, in_fa_c bt st' c a <-> in_fa_c bt st c a.
  Proof. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_fa_c in G in change_no_check G' end). destruct (proj1 EQ c) as (_ & _ & _ & RFR). rewrite RFR. tauto. Qed.
  Lemma in_batch_regdata : forall a, in_batch st' a <-> in_batch st a.
  Proof. intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_batch in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & ETQ & EGQ & _). rewrite ETQ, EGQ. tauto. Qed.

  Lemma partition_regdata : forall Lc c, partition_c bt st Lc c -> partition_c bt st' Lc c.
  Proof.
    intros Lc c P. unfold partition_c in *.
    destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    destruct EQ as (RD & _ & _ & EC & _). destruct (RD c) as (_ & _ & _ & RFR).
    pose proof carved_regdata as CV. pose proof in_quar_c_regdata as IQ. pose proof in_cache_c_regdata as ICC. pose proof in_fa_c_regdata as IFA. pose proof in_batch_regdata as IB.
    split; [intros a; rewrite (CV c a), (IQ c a), (ICC c a), (IFA c a), (IB a); exact (P1 a)|].
    split; [intros a; rewrite (IQ c a); exact (P2 a)|].
    split; [intros a; rewrite (ICC c a); exact (P3 a)|].
    split; [intros a; rewrite (IFA c a); exact (P4 a)|].
    split; [intros a; rewrite (IQ c a), (ICC c a); exact (P5 a)|].
    split; [intros a; rewrite (IQ c a), (IFA c a); exact (P6 a)|].
    split; [intros a; rewrite (ICC c a), (IFA c a); exact (P7 a)|].
    split; [intros a Hb Hc; rewrite (IQ c a), (ICC c a), (IFA c a); apply P8; [apply IB; exact Hb | exact Hc]|].
    rewrite EC, RFR. exact (conj P9 P10).
  Qed.

  Lemma wf_batch_regdata : forall b, wf_batch bt st b -> wf_batch bt st' b.
  Proof.
    intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply carved_regdata; exact B2|].
    intros m n Hin. destruct (B3 m n Hin) as (N1 & [[HP CV] | [HP RG]]); (split; [exact N1|]).
    - left. split; [exact HP | apply carved_regdata; exact CV].
    - right. split; [exact HP | apply registered_regdata; exact RG].
  Qed.
  Lemma wf_batch_regdata0 : forall b, wf_batch0 bt st b -> wf_batch0 bt st' b.
  Proof.
    intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply carved_regdata; exact B2|].
    intros m n Hin. destruct (B3 m n Hin) as (N1 & [[HP CV] | [HP RG]]); (split; [exact N1|]).
    - left. split; [exact HP | apply carved_regdata; exact CV].
    - right. split; [exact HP | apply registered_regdata; exact RG].
  Qed.

  Lemma dyn_ranges_regdata : dyn_ranges st' = dyn_ranges st.
  Proof. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & _ & _ & ES & _ & ED & _). rewrite ES, ED. reflexivity. Qed.

  Theorem WF_regdata : forall Lc FF {qt qg : Z}, WFq bt st Lc FF qt qg -> WFq bt st' Lc FF qt qg.
  Proof.
    intros Lc FF qt qg W.
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & (K1 & K2 & K3) & WD & WM & WMP & G).
    pose proof EQ as (RD & RO & ECI & EC & ETQ & EGQ & ES & ENR & ED & EH & EIA & EAA & EK & ESH).
    pose proof quar_regdata as QR. pose proof dyn_ranges_regdata as DR.
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split. { split.
             - intros c Hc. destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK). destruct (RD c) as (RMU & RAU & RFA & RFR).
               (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). rewrite RMU, RAU, RFA, RFR. repeat (split; [assumption|]). split.
               + intros k Hk. destruct (Y9 k Hk) as [Kr CV]. split; [exact Kr | apply carved_regdata; exact CV].
               + split; [apply partition_regdata; exact PART|].
                 intros HF'. destruct (FHX c Hc HF') as [HF | LE]; [exact (FHK HF) | exact LE].
             - intros c NC. destruct (WR2 c NC) as [E1 E2]. rewrite (RO c NC), EC. exact (conj E1 E2). }
    split. { intros c Hc. destruct (WC c Hc) as (C1 & C2 & C3). rewrite EC, ECI. split; [exact C1|]. split; [destruct (RD c) as (_ & RAU' & _); rewrite RAU'; exact C2|].
             intros k Hk. destruct (C3 k Hk) as [Kr CV]. split; [exact Kr | apply carved_regdata; exact CV]. }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). rewrite ETQ, EGQ, QR.
             split; [rewrite Forall_forall in Q1 |- *; intros b Hb; apply wf_batch_regdata; exact (Q1 b Hb)|].
             split; [rewrite Forall_forall in Q2 |- *; intros b Hb; apply wf_batch_regdata0; exact (Q2 b Hb)|].
             exact (conj Q3 (conj Q4 (conj Q5 Q6))). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). rewrite ES, ENR, QR. repeat (split; [assumption|]).
             split; [intros p n Hin HP; apply registered_regdata; exact (S7 p n Hin HP)|].
             intros m n Hin HP. apply registered_regdata. exact (S8 m n Hin HP). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| exact (conj LV2 LV3)]. intros p n Hin. destruct (LV1 p n Hin) as (A1 & A2 & A3 & CVL).
             split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros HP. apply carved_regdata. exact (CVL HP). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_fake in G in change_no_check G' end). rewrite EH. exact (conj K1 (conj K2 K3)). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_depot in G in change_no_check G' end). rewrite ED, EK. exact WD. }
    split. { (* [comment removed for export] *)
             apply (wf_meter_transfer st st' EK ESH ltac:(rewrite ES; reflexivity)); [| exact WM].
             intros c Hc. destruct (RD c) as (RMU & _ & RFA & _). exact (conj RMU RFA). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_maps, all_ranges in G in change_no_check G' end). rewrite DR. exact WMP. }
    exact G.
  Qed.
End RegData.

Section Holes.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Corollary WF_uhole : forall st Lc FF c {qt qg : Z}, 1 <= c <= 30 -> WFq bt st Lc FF qt qg -> WFq bt (op_uhole st c) Lc FF qt qg.
  Proof.
    intros st Lc FF c qt qg Hc W. apply (WF_regdata bt st (op_uhole st c) (st_regdata_uhole st c Hc)); [| exact W].
    intros c0 Hc0 HF. left. destruct (uhole_flags st c c0) as [_ EF]. rewrite EF in HF. exact HF.
  Qed.
  (* [comment removed for export] *)
  Corollary WF_fhole : forall st Lc FF c {qt qg : Z}, 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    WFq bt st Lc FF qt qg -> WFq bt (op_fhole st c) Lc FF qt qg.
  Proof.
    intros st Lc FF c qt qg Hc FR W. apply (WF_regdata bt st (op_fhole st c) (st_regdata_fhole st c Hc)); [| exact W].
    intros c0 Hc0 HF. destruct (fhole_flags st c c0) as [EF _]. rewrite EF in HF.
    destruct (Z.eqb_spec c0 c) as [-> | NE]; [right; exact FR | left; exact HF].
  Qed.




  (* [comment removed for export] *)
  Lemma holes_le_keep : forall h st st',
    (forall c, r_uhole (a_reg st' c) = r_uhole (a_reg st c) /\ r_fhole (a_reg st' c) = r_fhole (a_reg st c)) ->
    holes_le h st -> holes_le h st'.
  Proof. intros h st st' K HL c Hf. destruct (K c) as [EU EF]. rewrite EU, EF in Hf. exact (HL c Hf). Qed.
  (* [comment removed for export] *)
  Lemma holes_le_same_reg : forall h st st', a_reg st' = a_reg st -> holes_le h st -> holes_le h st'.
  Proof. intros h st st' E HL. apply (holes_le_keep h st st'); [| exact HL]. intros c. rewrite E. split; reflexivity. Qed.



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  (* [comment removed for export] *)
  Definition pop_mu (r : region) (c : Z) : Z :=
    if Z.ltb (r_mapped_user r) (r_alloc_user r + cache_hint c * csize c) then r_mapped_user r + KUSERMAP else r_mapped_user r.
  Definition pop_newn (r : region) (c : Z) : Z := (pop_mu r c - r_alloc_user r) / csize c.
  Definition holes_ls (n : Z) (st : ast) : Prop :=
    forall c, (r_uhole (a_reg st c) = true \/ r_fhole (a_reg st c) = true) ->
      (n <= 64512 /\ c = class_of (needed n))
      /\ a_cache st c = []
      /\ Z.of_nat (length (r_free (a_reg st c))) < cache_hint c
      /\ (r_uhole (a_reg st c) = true -> r_mapped_user (a_reg st c) < r_alloc_user (a_reg st c) + cache_hint c * csize c)
      /\ (r_fhole (a_reg st c) = true -> r_mapped_fa (a_reg st c) < 4 * (Z.of_nat (length (r_free (a_reg st c))) + pop_newn (a_reg st c) c)).
  Definition holes_lsopt (h : option Z) : ast -> Prop :=
    match h with None => holes_le None | Some n => holes_ls n end.
  Definition AAINV_HS (h : option Z) := AAINVP (holes_lsopt h) bt.

  Lemma holes_ls_le : forall n st, holes_ls n st -> holes_le (Some n) st.
  Proof. intros n st HS c Hf. destruct (HS c Hf) as ((Hn & Hc) & _). exists n. split; [reflexivity | split; [exact Hn | exact Hc]]. Qed.
  Lemma holes_lsopt_le : forall h st, holes_lsopt h st -> holes_le h st.
  Proof. intros [n|] st; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [apply holes_ls_le | intros H; exact H]. Qed.




  (* [comment removed for export] *)
  Lemma holes_ls_of_opt : forall h n st, holes_lsopt h st -> (h = None \/ h = Some n) -> holes_ls n st.
  Proof.
    intros h n st HP [-> | ->]; cbn in HP; [| exact HP].
    intros c Hf. destruct (HP c Hf) as (n0 & E & _). discriminate E.
  Qed.


  (* [comment removed for export] *)
  Lemma holes_ls_same_regcache : forall n st st', a_reg st' = a_reg st -> a_cache st' = a_cache st -> holes_ls n st -> holes_ls n st'.
  Proof. intros n st st' ER EC HS c. rewrite ER, EC. exact (HS c). Qed.

  Lemma uhole_data : forall st c c', regdata_eq (a_reg st c') (a_reg (op_uhole st c) c').
  Proof. intros st c c'. (lazymatch goal with |- ?G => let G' := eval unfold op_uhole, set_reg, regdata_eq in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity. Qed.
  Lemma fhole_data : forall st c c', regdata_eq (a_reg st c') (a_reg (op_fhole st c) c').
  Proof. intros st c c'. (lazymatch goal with |- ?G => let G' := eval unfold op_fhole, set_reg, regdata_eq in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hint_size_le : forall c, 1 <= c <= 30 -> cache_hint c * csize c <= 65536.
  Proof.
    intros c Hc. pose proof (csize_pos c Hc) as ((S1 & S2) & _). (lazymatch goal with |- ?G => let G' := eval unfold cache_hint in G in change_no_check G' end).
    set (q := 1024 / csize c). assert (Q1 : q * csize c <= 1024) by (subst q; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (Q0 : 0 <= q) by (subst q; apply Z.div_pos; lia).
    destruct (Z.le_gt_cases 1 q) as [G|L].
    - assert (HM : Z.max 1 (Z.min 8 q) <= q) by lia. nia.
    - assert (HM : Z.max 1 (Z.min 8 q) = 1) by lia. rewrite HM. lia.
  Qed.





  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Notation u := bv_unsigned.

  (* [comment removed for export] *)
  Definition uslot (st : ast) (c : Z) (a : Z) : Prop :=
    region_beg SBEG c + r_mapped_user (a_reg st c) <= a < region_beg SBEG c + r_mapped_user (a_reg st c) + KUSERMAP.
  Definition fslot (st : ast) (c : Z) (a : Z) : Prop :=
    fa_beg SBEG c + r_mapped_fa (a_reg st c) <= a < fa_beg SBEG c + r_mapped_fa (a_reg st c) + KFAMAP.

  (* [comment removed for export] *)
  Definition ledger_destroyed (mdl mdl' : Model) (lo len : Z) : Prop :=
    let h := m_vmmaps mdl in let h' := m_vmmaps mdl' in
    vm_maps h' = maps_subtract (vm_maps h) lo (lo + len)
    /\ vm_noaccess h' = maps_subtract (vm_noaccess h) lo (lo + len)
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + len))
    /\ Forall (fun iv : word * word => u (fst iv) mod PG = 0 /\ u (snd iv) mod PG = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL
                                   /\ (u (fst iv) + u (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= u (fst iv))) (m_vm_lazy mdl')
    /\ vm_reserved h' = vm_reserved h /\ vm_brk h' = vm_brk h /\ vm_start_brk h' = vm_start_brk h /\ vm_mmap_base h' = vm_mmap_base h
    /\ vm_init_sp h' = vm_init_sp h /\ vm_limit h' = vm_limit h.

  (* [comment removed for export] *)
  Definition OPS_REP_uhole : Prop := forall st Lc FF M M' mdl mdl' c,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 -> r_uhole (a_reg st c) = false ->
    r_mapped_user (a_reg st c) + KUSERMAP <= KREGION_EXHAUST ->
    (forall a : word, M' a <> M a -> uslot st c (u a) /\ M' a = None) ->
    ledger_destroyed mdl mdl' (region_beg SBEG c + r_mapped_user (a_reg st c)) KUSERMAP ->
    MInv (a_aa st) mdl' -> eager_used mdl' <= eager_used mdl ->
    Rep bt (op_uhole st c) Lc FF M' mdl'.
  (* [comment removed for export] *)
  Definition OPS_REP_fhole : Prop := forall st Lc FF M M' mdl mdl' c,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = false ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    (forall a : word, M' a <> M a -> fslot st c (u a) /\ M' a = None) ->
    ledger_destroyed mdl mdl' (fa_beg SBEG c + r_mapped_fa (a_reg st c)) KFAMAP ->
    MInv (a_aa st) mdl' -> eager_used mdl' <= eager_used mdl ->
    Rep bt (op_fhole st c) Lc FF M' mdl'.

  (* [comment removed for export] *)
  Definition OPS_WF_usermap : Prop := forall st Lc FF c,
    WF bt st Lc FF -> 1 <= c <= 30 -> r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST ->
    r_mapped_user (a_reg st c) - r_alloc_user (a_reg st c) < csize c ->      (* [comment removed for export] *)
    mu_room st ->                                                             (* [comment removed for export] *)
    WF bt (op_usermap st c) Lc FF.
  (* [comment removed for export] *)
  Definition foot_usermap (st : ast) (c : Z) (a : Z) : Prop :=
    (reginfo bt c + 48 <= a < reginfo bt c + 56) \/ (reginfo bt c + 72 <= a < reginfo bt c + 128)
    \/ (sh_lo (region_beg SBEG c + r_mapped_user (a_reg st c)) <= a < sh_lo (region_beg SBEG c + r_mapped_user (a_reg st c)) + KUSERMAP / 8)
    \/ uslot st c a
    \/ (bt_thread bt + 2768 <= a < bt_thread bt + T_UNW) \/ CEIL <= a.
  Definition OPS_REP_usermap : Prop := forall st Lc FF M M' mdl mdl' c,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 ->
    r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST ->
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    agrees_off (foot_usermap st c) M M' ->
    cellZ SG M' (reginfo bt c + 48) 8 (r_mapped_user (a_reg st c) + KUSERMAP) ->
    writableZ SG M' (reginfo bt c) (reginfo bt c + 128) ->
    writableZ SG M' lo (lo + KUSERMAP) ->
    fillZ SG M' (sh_lo lo) (sh_lo lo + KUSERMAP / 8) FA ->
    (* [comment removed for export] *)
    (r_uhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl)) ->
    (r_uhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KUSERMAP) :: vm_maps (m_vmmaps mdl))) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KUSERMAP)) ->
    (* [comment removed for export] *)
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KUSERMAP)) ->
    Forall (fun iv : word * word => u (fst iv) mod PG = 0 /\ u (snd iv) mod PG = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL
                                   /\ (u (fst iv) + u (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= u (fst iv))) (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) -> vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    MInv (a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)]) mdl' -> eager_used mdl' <= eager_used mdl + KUSERMAP ->
    Rep bt (add_meter (op_usermap st c) 0 [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] 0) Lc FF M' mdl'.
End Holes.
End AsAinvHole3.
Module AsAinvFacts3c.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 AsAinvHole3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BigAl.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Lemma big_live_aligned_WF : forall st Lc FF b m, WF bt st Lc FF -> In (b, m) Lc -> 64512 < m -> b mod 4096 = 2048.
  Proof.
    intros st Lc FF b m W Hin Hm.
    assert (HP : is_primary m = false).
    { (lazymatch goal with |- ?G => let G' := eval unfold is_primary, needed in G in change_no_check G' end). pose proof (rounded_ge m) as (R1 & _). rewrite (rz_big m Hm). apply Z.leb_gt. lia. }
    destruct (live_sec bt st Lc FF W b m Hin HP) as (sc & Hs & Eu & En).
    pose proof W as (_ & _ & _ & (_ & _ & _ & S4 & _) & _). destruct (S4 sc Hs) as (_ & AL).
    unfold sc_user, sec_user_off in Eu. rewrite En, (rz_big m Hm) in Eu. unfold PG in *. rewrite <- Eu.
    Z.div_mod_to_equations. lia.
  Qed.

  Theorem BIGAL_P : forall (P : ast -> Prop) L FF B C K M mdl b m,
    AAINVP P bt L FF B C K M mdl -> In (b, m) L -> 64512 < m -> b mod 4096 = 2048.
  Proof. intros P L FF B C K M mdl b m (st & W & _) Hin Hm. exact (big_live_aligned_WF st L FF b m W Hin Hm). Qed.

  Theorem BIGAL : forall h L FF B C K M mdl b m,
    AAINV_HS bt h L FF B C K M mdl -> In (b, m) L -> 64512 < m -> b mod 4096 = 2048.
  Proof. intros h. exact (BIGAL_P _). Qed.

End BigAl.
End AsAinvFacts3c.
Module AsAinvLedger.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Frag.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable st : ast.
  #[local] Notation u := bv_unsigned.
  #[local] Notation SBEG := (bt_spacebeg bt).
  #[local] Notation R6 := (bt_resv6 bt).
  #[local] Notation E6 := (bt_resv6 bt + bt_resv6_len bt).

  (* [comment removed for export] *)
  Lemma slot_edges_apart : forall s e,
    (s - SBEG) mod KUSERMAP = 0 -> (e - SBEG) mod KUSERMAP = 0 -> s < e -> s + KUSERMAP <= e.
  Proof.
    intros s e Hs He Hlt. unfold KUSERMAP in *.
    pose proof (Z.div_mod (s - SBEG) (2 ^ 18) ltac:(lia)) as Ds.
    pose proof (Z.div_mod (e - SBEG) (2 ^ 18) ltac:(lia)) as De.
    rewrite Hs in Ds. rewrite He in De.
    assert ((s - SBEG) / 2 ^ 18 < (e - SBEG) / 2 ^ 18) by nia.
    nia.
  Qed.

  (* [comment removed for export] *)
  Lemma slot_in_one_fragment : forall (F6 : list (word * word)) (s : Z),
    Forall (frag_ok bt) F6 ->
    (forall a, in_resv6 bt a -> (in_ivz F6 a <-> ~ holes bt st a)) ->
    (s - SBEG) mod KUSERMAP = 0 -> R6 <= s -> s + KUSERMAP <= E6 ->
    s + KUSERMAP <= SBEG + KSPACE ->                                  (* [comment removed for export] *)
    (forall a, s <= a < s + KUSERMAP -> ~ holes bt st a) ->
    exists iv, In iv F6 /\ u (fst iv) <= s /\ s + KUSERMAP <= u (fst iv) + u (snd iv).
  Proof.
    intros F6 s HF HB Hs Hlo Hhi HRI Hnh.
    assert (K0 : 0 < KUSERMAP) by ((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia).
    assert (Hin : in_ivz F6 s).
    { apply (proj2 (HB s ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_resv6 in G in change_no_check G' end); lia))). apply Hnh. lia. }
    destruct Hin as (b & n & Hbn & Hrng). exists (b, n). split; [exact Hbn|]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
    split; [lia|].
    rewrite Forall_forall in HF. pose proof (HF (b, n) Hbn) as (F1 & F2 & F3 & F4 & F5). cbn [fst snd] in *.
    destruct (Z_le_gt_dec (s + KUSERMAP) (u b + u n)) as [LE|GT]; [exact LE|]. exfalso.
    destruct F5 as [E | [M | M]]; [lia | | unfold PG in M; lia].
    pose proof (slot_edges_apart s (u b + u n) Hs M ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma map_contains_of_frag : forall (F6 rest maps : list (word * word)) (s : Z),
    Permutation maps (F6 ++ rest) ->
    Forall (frag_ok bt) F6 ->
    (forall a, in_resv6 bt a -> (in_ivz F6 a <-> ~ holes bt st a)) ->
    (s - SBEG) mod KUSERMAP = 0 -> R6 <= s -> s + KUSERMAP <= E6 -> s + KUSERMAP <= SBEG + KSPACE ->
    (forall a, s <= a < s + KUSERMAP -> ~ holes bt st a) ->
    0 <= s -> s + KUSERMAP < 2 ^ 64 ->
    map_contains maps (Z_to_bv 64 s) (Z_to_bv 64 KUSERMAP) = true.
  Proof.
    intros F6 rest maps s HP HF HB Hs Hlo Hhi HRI Hnh S0 S64.
    destruct (slot_in_one_fragment F6 s HF HB Hs Hlo Hhi HRI Hnh) as ([b n] & Hbn & H1 & H2). cbn [fst snd] in H1, H2.
    (lazymatch goal with |- ?G => let G' := eval unfold map_contains in G in change_no_check G' end). apply existsb_exists. exists (b, n). split.
    - apply (Permutation_in _ (Permutation_sym HP)). apply in_app_iff. left. exact Hbn.
    - (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). assert (K0 : 0 < KUSERMAP) by ((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia).
      rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_modulus in G in change_no_check G' end). change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite (Z.mod_small s) by lia. rewrite (Z.mod_small KUSERMAP) by (unfold KUSERMAP in *; lia).
      apply andb_true_intro. split; apply Z.leb_le; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma frag_ok_whole : forall (b n : word),
    u b = R6 -> u n = bt_resv6_len bt -> 0 < bt_resv6_len bt -> frag_ok bt (b, n).
  Proof.
    intros b n Hb Hn Hpos. (lazymatch goal with |- ?G => let G' := eval unfold frag_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Hb, Hn. repeat split; try lia; left; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma user_slot_aligned : forall c m,
    m mod KUSERMAP = 0 -> (region_beg SBEG c + m - SBEG) mod KUSERMAP = 0.
  Proof.
    intros c m Hm. unfold region_beg, KREGION, KUSERMAP in *.
    replace (SBEG + c * 2 ^ 32 + m - SBEG) with (m + (c * 2 ^ 14) * 2 ^ 18) by lia.
    rewrite Z.mod_add by lia. exact Hm.
  Qed.

  Lemma fa_slot_aligned : forall c m,
    m mod KFAMAP = 0 -> (fa_beg SBEG c + m - SBEG) mod KUSERMAP = 0.
  Proof.
    intros c m Hm. unfold fa_beg, region_beg, KREGION, KFAOFF, KUSERMAP, KFAMAP in *.
    replace (SBEG + c * 2 ^ 32 + 3758096384 + m - SBEG) with (m + (c * 2 ^ 14 + 14336) * 2 ^ 18) by lia.
    rewrite Z.mod_add by lia. exact Hm.
  Qed.
End Frag.
End AsAinvLedger.
Module AsKSys4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 AsAinvOps3 AsAinvOpsPf3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Sh.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Notation u := bv_unsigned.





  (* [comment removed for export] *)
  Lemma maps0_in_vm_maps : forall st mdl iv, rep_ledger bt st mdl -> In iv (bt_maps0 bt) -> In iv (vm_maps (m_vmmaps mdl)).
  Proof.
    intros st mdl iv (L1 & _) Hin. destruct L1 as (F6 & PM & _).
    apply (Permutation_in iv (Permutation_sym PM)). apply in_app_iff. right. apply in_app_iff. left. exact Hin.
  Qed.
End Sh.
End AsKSys4.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 AsAinvLedger AsAinvHole3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BackingAlgebra.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section Entry.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation FSB := (bt_fs bt).
  #[local] Abbreviation D0 := (bt_dep0 bt).
  #[local] Abbreviation R6 := (bt_resv6 bt).
  #[local] Abbreviation L6 := (bt_resv6_len bt).

  (* [comment removed for export] *)
  Definition st0 : ast :=
    AST (fun _ => region0) false (fun _ => []) [] [] [] 0 (bt_dep0 bt) (fun _ => 0) false (bt_aa0 bt) 0 0.

  (* [comment removed for export] *)
  Definition boot_ok : Prop :=
    bt_spacebeg bt mod 2 ^ 16 = 0
    /\ wf_maps bt st0                                    (* [comment removed for export] *)
    /\ FSB mod PG = 0
    (* [comment removed for export] *)
    /\ dp_nids D0 = 1 /\ (forall i, 0 <= dp_tab D0 i <= 1) /\ dp_link D0 1 = 0 /\ 0 <= dp_hash D0 1 < 2 ^ 64 /\ 0 <= dp_store D0 1 < 2 ^ 32
    /\ dp_nodeblocks D0 = [] /\ dp_storeblocks D0 = [] /\ 1 <= dp_frames D0 <= 2 ^ 20 /\ (forall i, 0 <= dp_stored D0 i < 2 ^ 32)
    /\ (forall i, i <> 0 -> dp_stored D0 i = 0)
    (* [comment removed for export] *)
    /\ A_wf (bt_aa0 bt)
    /\ (forall lo hi, In (lo, hi) (SHC (bt_ia bt) FSB) -> range_allowed (bt_aa0 bt) lo hi)
    /\ range_allowed (bt_aa0 bt) (bt_store0 bt) (bt_store0 bt + 2 ^ 23)
    (* [comment removed for export] *)
    /\ 0 <= ia_instance (bt_ia bt) /\ ia_instance (bt_ia bt) + 4096 <= AS_LO
    /\ 0 <= ia_ialloc_inst (bt_ia bt) /\ ia_ialloc_inst (bt_ia bt) + IASZ <= AS_LO
    /\ 0 <= ia_stackstore (bt_ia bt) /\ ia_stackstore (bt_ia bt) + 2 ^ 17 <= AS_LO
    /\ 0 <= ia_depot_tab (bt_ia bt) /\ ia_depot_tab (bt_ia bt) + 2 ^ 23 <= AS_LO
    /\ 0 <= ia_ialloc_flag (bt_ia bt) /\ ia_ialloc_flag (bt_ia bt) + 8 <= AS_LO
    /\ 0 <= bt_tls_fs bt /\ bt_tls_fs bt + 16 <= AS_LO
    /\ 0 < L6
    /\ bt_ok bt.                                        (* [comment removed for export] *)

  #[local] Abbreviation I := (IB bt).
  #[local] Abbreviation RI := (bt_spacebeg bt + KSPACE).

  (* [comment removed for export] *)
  Definition main_facts (M : mem) (mdl : Model) : Prop :=
    let h := m_vmmaps mdl in
    cells_hold SG M (bt_consts bt)
    (* [comment removed for export] *)
    /\ cellZ SG M (I + 112) 8 0 /\ cellZ SG M (I + 120) 8 0 /\ byteZ SG M (I + 680) 0 /\ byteZ SG M (I + 880) 0 /\ byteZ SG M (I + 881) 0
    /\ byteZ SG M (I + 984) 0 /\ fillZ SG M (I + 888) (I + 920) 0
    (* [comment removed for export] *)
    /\ cellZ SG M T 8 (bt_tctx bt) /\ cellZ SG M (T + 8) 8 (bt_stack_top bt) /\ cellZ SG M (T + 16) 8 (bt_stack_bottom bt)
    /\ byteZ SG M (T + 40) 0 /\ cellZ SG M (T + 72) 8 FSB /\ fillZ SG M (T + 80) (T + 3169) 0 /\ writableZ SG M T (T + PG)
    /\ cellZ SG M (bt_tctx bt + 152) 8 T /\ cellZ SG M (bt_tctx bt + 8) 4 0
    (* [comment removed for export] *)
    /\ fillZ SG M RI (RI + PG) 0 /\ writableZ SG M RI (RI + PG)
    (* [comment removed for export] *)
    /\ (forall i, 0 <= i < 2 ^ 20 -> cellZ SG M (DEPOT_TAB bt + 4 * i) 4 (dp_tab D0 i))
    /\ cellZ SG M (DEPOT_NIDS bt) 4 1 /\ byteZ SG M (DEPOT_NIDS bt + 8) 0
    /\ cellZ SG M (DEPOT_MAP1 bt) 8 (bt_nodes0 bt) /\ (forall i, 1 <= i < 2 ^ 15 -> cellZ SG M (DEPOT_MAP1 bt + 8 * i) 8 0)
    /\ cellZ SG M (bt_nodes0 bt + 16) 8 (dp_hash D0 1) /\ cellZ SG M (bt_nodes0 bt + 24) 4 (dp_link D0 1) /\ cellZ SG M (bt_nodes0 bt + 28) 4 (dp_store D0 1)
    /\ writableZ SG M (bt_nodes0 bt) (bt_nodes0 bt + 2 ^ 20)
    /\ cellZ SG M (SSOBJ bt) 8 (dp_frames D0) /\ cellZ SG M (SSOBJ bt + 16) 8 (bt_store0 bt) /\ cellZ SG M (SSOBJ bt + 24) 4 (dp_stored D0 0)
    /\ byteZ SG M (SSOBJ bt + 28) 0
    /\ (forall i, 1 <= i < 2 ^ 12 -> cellZ SG M (SSOBJ bt + 16 + 16 * i) 8 0 /\ cellZ SG M (SSOBJ bt + 24 + 16 * i) 4 0 /\ byteZ SG M (SSOBJ bt + 28 + 16 * i) 0)
    /\ writableZ SG M (bt_store0 bt) (bt_store0 bt + 2 ^ 23)
    (* [comment removed for export] *)
    /\ fillZ SG M FSB (FSB + 0x58) 0 /\ cellZ SG M (FSB + 0x58) 8 FSLOG /\ fillZ SG M (FSB + 0x60) (FSB + FAKE_SIZE) 0 /\ writableZ SG M FSB (FSB + FAKE_SIZE)
    /\ cellZ SG M (bt_tls_fs bt) 8 FSB
    (* [comment removed for export] *)
    /\ byteZ SG M (IA_FLAG bt) 0 /\ byteZ SG M (IA_FLAG bt + 1) 0 /\ fillZ SG M (IA_INST bt + 8) (IA_INST bt + 8 + 0x40000) 0
    (* [comment removed for export] *)
    /\ (exists w6 n6 : word, u w6 = R6 /\ u n6 = L6 /\ Permutation (vm_maps h) ((w6, n6) :: bt_maps0 bt))
    /\ (forall a, in_ivz (vm_noaccess h) a <-> in_ivz (bt_noacc0 bt) a)
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl) a <-> pg_in_ivz (bt_lazy0 bt) a)
    /\ Forall (fun iv : word * word => u (fst iv) mod PG = 0 /\ u (snd iv) mod PG = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL
                                      /\ (u (fst iv) + u (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= u (fst iv))) (m_vm_lazy mdl)
    /\ vm_reserved h = bt_reserved bt /\ vm_brk h = bt_brk bt /\ vm_start_brk h = bt_start_brk bt
    /\ vm_mmap_base h = bt_mmap_base bt /\ vm_init_sp h = bt_init_sp bt /\ page_floor (alloc_top h) = CEIL /\ StoreOk.RunLim.LMIN <= vm_limit h   (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ Forall (fun e : word * word => 0 < u (snd e)) (vm_noaccess h)
    (* [comment removed for export] *)
    /\ MInv (bt_aa0 bt) mdl /\ eager_used mdl + A_bytes (bt_aa0 bt) <= KBASE
    (* [comment removed for export] *)
    /\ cellZ SG M (ia_rtc_sb (bt_ia bt)) 8 SB /\ cellZ SG M (ia_rtc_uar (bt_ia bt)) 4 1
    (* [comment removed for export] *)
    /\ (forall z, shmaps z -> M (Z_to_bv 64 z) <> None)
    (* [comment removed for export] *)
    /\ BackingAlgebra.model_ivs_wf mdl
    (* [comment removed for export] *)
    /\ cellZ SG M (T + 48) 8 (bt_tp bt + 0x738) /\ cellZ SG M (T + 56) 8 (bt_tp bt + 0x814)
    /\ cellZ SG M (bt_tls_fs bt + 8) 8 (bt_dtls bt) /\ cellZ SG M (bt_dtls bt + 24) 8 (bt_tp bt).
End Entry.

Section EntryProof.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Hypothesis BOK : boot_ok bt.
  #[local] Abbreviation ST0 := (st0 bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Lemma quar0 : quar ST0 = []. Proof. reflexivity. Qed.

  Lemma carved0 : forall c a, 1 <= c <= 30 -> ~ carved bt ST0 c a.
  Proof.
    intros c a Hc (j & Hj & Hle & _). cbn in Hle. pose proof (csize_pos c Hc) as ((S1 & S2) & _). nia.
  Qed.

  Lemma partition0 : forall c, 1 <= c <= 30 -> partition_c bt ST0 [] c.
  Proof.
    intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold partition_c in G in change_no_check G' end).
    assert (NL : forall a, ~ in_live_c [] c a) by (intros a (p & n & Hin & _); exact Hin).
    assert (NQ : forall a, ~ in_quar_c ST0 c a) by (intros a (m & n & Hin & _); rewrite quar0 in Hin; exact Hin).
    assert (NC : forall a, ~ in_cache_c bt ST0 c a) by (intros a (k & Hin & _); exact Hin).
    assert (NF : forall a, ~ in_fa_c bt ST0 c a) by (intros a (k & Hin & _); exact Hin).
    assert (NB : forall a, ~ in_batch ST0 a) by (intros a (b & Hin & _); exact Hin).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - intros a. split.
      + intros H. exfalso. exact (carved0 c a Hc H).
      + intros [H|[H|[H|[H|[_ H]]]]]; exfalso; [exact (NL a H)|exact (NQ a H)|exact (NC a H)|exact (NF a H)|exact (NB a H)].
    - intros a [H _]; exact (NL a H).
    - intros a [H _]; exact (NL a H).
    - intros a [H _]; exact (NL a H).
    - intros a [H _]; exact (NQ a H).
    - intros a [H _]; exact (NQ a H).
    - intros a [H _]; exact (NC a H).
    - intros a H; exfalso; exact (NB a H).
    - constructor.
    - constructor.
  Qed.

  Lemma WF0 : WF bt ST0 [] [].
  Proof.
    pose proof BOK as (B1 & BM & BFS & Dn & Dt & Dl & Dh & Ds & Dnb & Dsb & Dfr & Dst & Dst0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BTOK).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, WFq in G in change_no_check G' end). split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact BM | split; [split; [exact B1 | split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold LMAX in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold GBUDGET in G in change_no_check G' end); lia]] | split; [exact BTOK | (* [comment removed for export] *) split; [rewrite Dn; lia | exact Dfr]]]]]]]]]]]].
    - (* [comment removed for export] *) split.
      + intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg st0 r_alloc_user r_mapped_user r_mapped_fa r_free r_fhole region0 length Z.of_nat] in G in change_no_check G' end).
        pose proof (csize_pos c Hc) as ((S1 & S2) & _).
        split; [(lazymatch goal with |- ?G => let G' := eval unfold AMAX in G in change_no_check G' end); lia|]. split; [reflexivity|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KREGION_EXHAUST in G in change_no_check G' end); lia|].
        split; [apply Z.mod_0_l; lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
        split; [intros k Hk; destruct Hk|]. split; [exact (partition0 c Hc)|]. intros H; discriminate H.
      + intros c Hc. split; reflexivity.
    - (* [comment removed for export] *) intros c Hc. (lazymatch goal with |- ?G => let G' := eval cbn [a_cache a_cinit st0 length Z.of_nat] in G in change_no_check G' end). split; [(lazymatch goal with |- ?G => let G' := eval unfold cache_max, cache_hint in G in change_no_check G' end); lia|].
      split; [intros _; split; reflexivity|]. intros k Hk; destruct Hk.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq st0 q_bytes fold_right app map] in G in change_no_check G' end). rewrite quar0. (lazymatch goal with |- ?G => let G' := eval cbn [map] in G in change_no_check G' end).
      repeat split; try lia; constructor.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_sec a_nres st0 length Z.of_nat map] in G in change_no_check G' end). rewrite quar0.
      split; [lia|]. split; [reflexivity|]. split; [lia|].
      split; [intros s0 Hs; destruct Hs|]. split; [constructor|]. split; [intros s0 Hs; destruct Hs|].
      split; [intros p n Hin; destruct Hin|]. intros m n Hin; destruct Hin.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [intros p n Hin; destruct Hin|]. split; [constructor|]. intros p n p' n' Hin; destruct Hin.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_fake in G in change_no_check G' end). split; [intros f k Hin; destruct Hin|]. split; [constructor|]. intros k. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_depot in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep a_kact st0] in G in change_no_check G' end). rewrite Dnb, Dsb, Dn. (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat] in G in change_no_check G' end).
      split; [lia|]. split; [rewrite Z.div_0_l by ((lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia); lia|]. split; [lia|].
      split; [intros i Hi; pose proof (Dt i); lia|].
      split; [intros id Hid; assert (id = 1) by lia; subst id; rewrite Dl; lia|].
      split; [reflexivity|]. split; [lia|]. split; [lia|].
      split; [rewrite Z.div_0_l by ((lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia); (lazymatch goal with |- ?G => let G' := eval unfold FRW in G in change_no_check G' end); lia|].
      split. { assert (E : (dp_frames (bt_dep0 bt) - 1) / 2 ^ 20 = 0) by (apply Z.div_small; lia). rewrite E. reflexivity. }
      split; [intros i; pose proof (Dst i); lia|]. intros b Hb; destruct Hb.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_meter, sum_mu in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_shsec a_sec a_reg st0 r_mapped_user r_mapped_fa region0 sum_classes length Z.of_nat] in G in change_no_check G' end).
      rewrite Z.div_0_l by ((lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia). repeat split; try lia. intros c Hc. rewrite Zdiv_0_l. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). lia.
  Qed.

  Section WithState.
    Variables (M : mem) (mdl : Model).
    Hypothesis EF : main_facts bt M mdl.

    Lemma Rep0 : Rep bt ST0 [] [] M mdl.
    Proof.
      pose proof BOK as (B1 & BM & BFS & Dn & Dt & Dl & Dh & Ds & Dnb & Dsb & Dfr & Dst & Dst0 & AW & ASHC & AST0
                         & GI1 & GI2 & GA1 & GA2 & GSS1 & GSS2 & GD1 & GD2 & GF1 & GF2 & GTL1 & GTL2 & L6P & BTOK).
      pose proof EF as (Ec & Ei1 & Ei2 & Ei3 & Ei4 & Ei5 & Ei6 & Ei7 & Et1 & Et2 & Et3 & Et4 & Et5 & Et6 & Et7 & Et8 & Et9
                        & Er1 & Er2 & Ed1 & Ed2 & Ed3 & Ed4 & Ed5 & Ed6 & Ed7 & Ed8 & Ed9 & Ed10 & Ed11 & Ed12 & Ed13 & Ed14 & Ed15
                        & Ef1 & Efs & Ef2 & Ef3 & Ef4 & Ea1 & Ea2 & Ea3 & El1 & El2 & El3 & El4 & El5 & El6 & El7 & El8 & El9 & El10 & El11 & El12 & Eb1 & Eb2 & Ert1 & Ert2 & Eshd & _ & Ex1 & Ex2 & Ex3 & Ex4).
      (* [comment removed for export] *)
      pose proof BM as (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _).
      destruct (RNG _ _ (all_ranges_fixed bt ST0 _ INT)) as ((XT1 & _ & XT3 & _ & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt ST0 _ INC)) as ((XC1 & _ & XC3 & _ & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt ST0 _ INFS)) as ((XF1 & _ & XF3 & _ & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt ST0 _ INN)) as ((XN1 & _ & XN3 & _ & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt ST0 _ INS)) as ((XS1 & _ & XS3 & _ & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt ST0 _ IN6)) as ((X61 & _ & X63 & _ & _) & _).
      pose proof ceil_rng as CR.
      unfold IB, DEPOT_NIDS, DEPOT_MAP1, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST in *. unfold AS_HEAPLO, AS_LO, FAKE_SIZE, PG, KSPACE, IASZ in *.
      (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
      split; [exact Ec|].
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_instance, IB in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_nres a_sec a_gq st0 length Z.of_nat] in G in change_no_check G' end).
        repeat (split; [assumption|]).
        split. { (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat rev q_bytes fold_right] in G in change_no_check G' end).
                 repeat split; apply (fill_cellZ_zero _ _ _ _ Ei7); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia. }
        split. { intros i s0 Hs. destruct i; discriminate Hs. }
        intros i Hi. lia. }
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_cinit a_cache st0] in G in change_no_check G' end).
        split; [exact Et1|]. split; [exact Et2|]. split; [exact Et3|]. split; [exact Et4|]. split; [exact Et5|].
        split. { (lazymatch goal with |- ?G => let G' := eval unfold byteZ in G in change_no_check G' end). apply (fill_cellN_zero _ _ _ _ Et6 1); (lazymatch goal with |- ?G => let G' := eval unfold T_UNW in G in change_no_check G' end); lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold rep_list, T_QC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat rev q_bytes fold_right] in G in change_no_check G' end).
                 repeat split; apply (fill_cellZ_zero _ _ _ _ Et6); lia. }
        split. { intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold rep_pclass, T_PC, PC_SZ in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat] in G in change_no_check G' end).
                 split; [|split; [|split; [|intros i k Hk; destruct i; discriminate Hk]]];
                 apply (fill_cellZ_zero _ _ _ _ Et6); lia. }
        split; [exact Et7|]. split; [exact Et8|]. split; [exact Et9|]. split; [exact Ex1 | exact Ex2]. }
      split. { (* [comment removed for export] *) intros c Hc. split.
        - (lazymatch goal with |- ?G => let G' := eval unfold rep_reginfo, reginfo in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_alloc_user r_mapped_user region0 a_reg st0 length Z.of_nat] in G in change_no_check G' end).
          unfold KSPACE, PG in *.
          repeat match goal with |- _ /\ _ => split end;
            try (apply (fill_cellZ_zero _ _ _ _ Er1); lia);
            try ((lazymatch goal with |- ?G => let G' := eval unfold byteZ in G in change_no_check G' end); apply (fill_cellN_zero _ _ _ _ Er1 1); lia).
          intros i Hi. apply Er2. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold rep_freearray in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_mapped_user region0 a_reg st0] in G in change_no_check G' end).
          split; [intros i k Hk; destruct i; discriminate Hk|]. split; intros i Hi; lia. }
      split. { intros i b Hb. destruct i; discriminate Hb. }
      split. { intros i b Hb. destruct i; discriminate Hb. }
      split. { intros i s0 Hs. destruct i; discriminate Hs. }
      split. { split; [intros p n Hin; destruct Hin|]. intros m n Hin. rewrite quar0 in Hin. destruct Hin. }
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_depot in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep st0] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold node_addr in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold node_blocks, store_blocks in G in change_no_check G' end). rewrite Dnb, Dsb, Dn.
        (lazymatch goal with |- ?G => let G' := eval unfold DEPOT_NIDS, DEPOT_MAP1, DEPOT_TAB, SSOBJ in G in change_no_check G' end).
        split; [exact Ed1|]. split; [exact Ed2|]. split; [exact Ed3|].
        split. { intros i Hi. destruct (Z.eq_dec i 0) as [->|NE].
                 - change (Z.to_nat 0) with 0%nat. (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end). rewrite Z.mul_0_r, Z.add_0_r. exact Ed4.
                 - replace (nth (Z.to_nat i) [bt_nodes0 bt] 0) with 0.
                   + apply Ed5. lia.
                   + destruct (Z.to_nat i) as [|[|k]] eqn:E; [lia|reflexivity|reflexivity]. }
        split. { intros id Hid. assert (id = 1) by lia. subst id.
                 change (1 / 2 ^ 16) with 0. change (1 mod 2 ^ 16) with 1. change (Z.to_nat 0) with 0%nat. (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end).
                 replace (bt_nodes0 bt + 16 * 1 + 8) with (bt_nodes0 bt + 24) by lia.
                 replace (bt_nodes0 bt + 16 * 1 + 12) with (bt_nodes0 bt + 28) by lia.
                 replace (bt_nodes0 bt + 16 * 1) with (bt_nodes0 bt + 16) by lia.
                 split; [exact Ed6|]. split; [exact Ed7|]. exact Ed8. }
        split. { intros b [<-|[]]. exact Ed9. }
        split; [exact Ed10|].
        split. { intros i Hi. destruct (Z.eq_dec i 0) as [->|NE].
                 - change (Z.to_nat 0) with 0%nat. (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end). rewrite Z.mul_0_r, !Z.add_0_r. split; [exact Ed11|]. split; [exact Ed12|]. exact Ed13.
                 - replace (nth (Z.to_nat i) [bt_store0 bt] 0) with 0
                     by (destruct (Z.to_nat i) as [|[|k]] eqn:E; [lia|reflexivity|reflexivity]).
                   rewrite (Dst0 i NE). exact (Ed14 i ltac:(lia)). }
        intros b [<-|[]]. exact Ed15. }
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_fake in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_hint st0] in G in change_no_check G' end).
        split. { intros k Hk. apply (fill_cellZ_zero _ _ _ _ Ef1); lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold byteZ in G in change_no_check G' end). apply (fill_cellN_zero _ _ _ _ Ef2 1); lia. }
        split. { intros k pos Hk Hpos. (lazymatch goal with |- ?G => let G' := eval cbn [existsb] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold byteZ in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fake_flag_addr, fake_flags_off in G in change_no_check G' end). unfold FCAP in Hpos.
                 assert (0 < 2 ^ (14 - k) <= 2 ^ 14) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
                 apply (fill_cellN_zero _ _ _ _ Ef2 1); lia. }
        split. { intros f k Hin. destruct Hin. }
        split; [exact Ef3 |]. split; [exact Ef4 |]. split; [exact Efs|]. split; [exact Ex3 | exact Ex4]. }
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_ialloc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_ialloc st0] in G in change_no_check G' end). split; [exact Ea1|]. split; [exact Ea2|]. split; [exact Ea3|].
        intros H; discriminate H. }
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_sec st0 r_mapped_user r_mapped_fa region0] in G in change_no_check G' end). rewrite quar0.
        split. { intros c g Hc Hg. exfalso. rewrite Z.add_0_r in Hg. lia. }
        split. { intros c g Hc Hg. exfalso. rewrite Z.add_0_r in Hg. lia. }
        split. { intros s g Hs. destruct Hs. }
        split. { intros s g Hs. destruct Hs. }
        split. { intros c g Hc Hg. exfalso. rewrite Z.add_0_r in Hg. lia. }
        intros s g Hs. destruct Hs. }
      assert (NCOM : forall a, ~ committed bt ST0 a).
      { intros a [(c & Hc & [R | R])|R]; cbn [a_reg st0 r_mapped_user r_mapped_fa region0 a_nres] in R; lia. }
      assert (NHOL : forall a, ~ holes bt ST0 a).
      { intros a (c & Hc & [[R _]|[R _]]); cbn [a_reg st0 r_uhole r_fhole region0] in R; discriminate R. }
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_sec a_dep st0] in G in change_no_check G' end). rewrite Dnb, Dsb. (lazymatch goal with |- ?G => let G' := eval cbn [map app] in G in change_no_check G' end). rewrite app_nil_r.
        destruct El1 as (w6 & n6 & Ew & En & PM).
        split. { exists [(w6, n6)]. split; [exact PM|].
                 split. { apply Forall_cons; [| apply Forall_nil]. apply (frag_ok_whole bt); [exact Ew | exact En | exact L6P]. }
                 split. { intros l1 x l2 y E Hy. destruct l1 as [|z l1']; [| destruct l1'; discriminate E]. cbn in E. injection E as <- <-. destruct Hy. }
                 intros a Ha. split; [intros _; exact (NHOL a)|]. intros _. exists w6, n6. split; [left; reflexivity|]. unfold in_resv6 in Ha. rewrite Ew, En. exact Ha. }
        split. { intros a. rewrite El2. split; [intros H; split; [exact H | split; [exact (NCOM a) | exact (NHOL a)]] | intros [H _]; exact H]. }
        split. { intros a. rewrite El3. split; [intros H; left; split; [exact H | split; [exact (NCOM a) | exact (NHOL a)]] |].
                 intros [[H _] | (b & Hb & _)]; [exact H | destruct Hb]. }
        split; [exact El4|]. split; [exact El5|]. split; [exact El6|]. split; [exact El7|]. split; [exact El8|].
        split; [exact El9|]. split; [exact El10|]. split; [exact El11|]. exact El12. }
      split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa a_kact a_reg a_sec a_dep a_nres a_shsec st0 r_mapped_user r_mapped_fa region0] in G in change_no_check G' end). rewrite Dsb.
        split; [exact AW|]. split; [exact Eb1|]. split; [exact ASHC|].
        split; [intros p n Hin; destruct Hin|].
        split. { intros c Hc. rewrite Z.div_0_l by lia. rewrite !Z.add_0_r. split; intros a Ha; lia. }
        split; [intros s0 Hs; destruct Hs|].
        split. { intros b [<-|[]]. exact AST0. }
        (lazymatch goal with |- ?G => let G' := eval unfold prim_charge, sec_charge, depot_charge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_sec a_dep a_shsec a_nres st0 r_mapped_user r_mapped_fa region0 sum_classes fold_right Z.of_nat length] in G in change_no_check G' end).
        rewrite Dnb, Dsb. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
        (* [comment removed for export] *)
        intros s0 Hs; destruct Hs. }
      split; [intros p n Hin; destruct Hin|]. split; [intros f k Hin; destruct Hin|]. split; [exact Ert1|]. split; [exact Ert2|]. split; [exact Eshd | intros NE; exfalso; apply NE; reflexivity].
    Qed.

    Lemma MWF0 : BackingAlgebra.model_ivs_wf mdl.
    Proof. pose proof EF as EF'. do 59 (apply proj2 in EF'). exact (proj1 EF'). Qed.

    Theorem AAINVP_main : forall P : ast -> Prop, P ST0 -> AAINVP P bt [] [] 0 0 0 M mdl.
    Proof.
      intros P HP. exists ST0. split; [exact WF0|]. split; [exact Rep0|]. split; [| exact MWF0]. split; [| exact HP]. (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [PHI a_kact st0 length Z.of_nat fold_right] in G in change_no_check G' end). lia.
    Qed.


  End WithState.
End EntryProof.
