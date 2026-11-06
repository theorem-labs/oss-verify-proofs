(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfin (r : dres) : Z * dst * dstrm :=
  match r with
  | DGo _ L' d' s' => (BZ_OK, d_set_sv d' L', s')
  | DRet rv L' d' s' => (rv, d_set_sv d' L', s')
  | DRetNoSave rv _ d' s' => (rv, d', s')
  end.

(* [comment removed for export] *)
Definition dgo (F : nat) (r : dres) : dres :=
  match r with
  | DGo lbl L d s => drun F lbl L d s
  | _ => r
  end.

Lemma dgo_DGo : forall F lbl L d s, dgo F (DGo lbl L d s) = drun F lbl L d s. Proof. reflexivity. Qed.
Lemma dgo_DRet : forall F rv L d s, dgo F (DRet rv L d s) = DRet rv L d s. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma dfin_DRet : forall rv L d s, dfin (DRet rv L d s) = (rv, d_set_sv d L, s). Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma dgo_if : forall F (b : bool) r1 r2, dgo F (if b then r1 else r2) = if b then dgo F r1 else dgo F r2.
Proof. intros F [] r1 r2; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fuel_ok (F : nat) (d : dst) (s : dstrm) : Prop :=
  9 * Z.of_nat (length (s_in s)) + d_bsLive d < Z.of_nat F.



Lemma fuel_ok_pos : forall F d s, 0 <= d_bsLive d -> fuel_ok F d s -> exists f, F = S f.
Proof.
  intros F d s Hb H. unfold fuel_ok in H. destruct F as [|f]; [| exists f; reflexivity].
  exfalso. cbn [Z.of_nat] in H. lia.
Qed.

(* [comment removed for export] *)
Lemma fuel_ok_bits : forall f d d' s s', fuel_ok (S f) d s ->
  length (s_in s') = length (s_in s) -> d_bsLive d' <= d_bsLive d - 1 -> fuel_ok f d' s'.
Proof. intros f d d' s s' H E B. unfold fuel_ok in *. rewrite E. rewrite Nat2Z.inj_succ in H. lia. Qed.

(* [comment removed for export] *)
Lemma fuel_ok_pull : forall f d d' s s', fuel_ok (S f) d s ->
  S (length (s_in s')) = length (s_in s) -> d_bsLive d' <= d_bsLive d + 8 -> fuel_ok f d' s'.
Proof. intros f d d' s s' H E B. unfold fuel_ok in *. rewrite <- E in H. rewrite !Nat2Z.inj_succ in H. lia. Qed.

(* [comment removed for export] *)
Lemma fuel_ok_eq : forall F d d' s s', fuel_ok F d s ->
  length (s_in s') = length (s_in s) -> d_bsLive d' = d_bsLive d -> fuel_ok F d' s'.
Proof. intros F d d' s s' H E B. unfold fuel_ok in *. rewrite E, B. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gbval (bb bl n : Z) : Z := Z.land (Z.shiftr bb (bl - n)) (Z.shiftl 1 n - 1).

Lemma drun_S : forall f lbl L d s, drun (S f) lbl L d s =
  (let d0 := d_set_state d lbl in
   let n := gb_bits lbl L in
   if n <=? d_bsLive d0 then
     let v := Z.land (Z.shiftr (d_bsBuff d0) (d_bsLive d0 - n)) (Z.shiftl 1 n - 1) in
     let d1 := d_set_bsLive d0 (d_bsLive d0 - n) in
     match gb_after lbl v L d1 s with
     | DGo lbl' L' d' s' => drun f lbl' L' d' s'
     | r => r
     end
   else
     match s_in s with
     | [] => DRet BZ_OK L d0 s
     | b :: rest =>
         let d1 := d_set_bsLive (d_set_bsBuff d0 (u32 (Z.lor (Z.shiftl (d_bsBuff d0) 8) b))) (d_bsLive d0 + 8) in
         drun f lbl L d1 (s_set_tin (s_set_in s rest) (s_tin s + 1))
     end).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma drun_bits : forall f lbl L d s n, n = gb_bits lbl L -> n <= d_bsLive d ->
  drun (S f) lbl L d s =
  dgo f (gb_after lbl (gbval (d_bsBuff d) (d_bsLive d) n) L (d_set_bsLive (d_set_state d lbl) (d_bsLive d - n)) s).
Proof.
  intros f lbl L d s n En Hn. rewrite drun_S. cbv zeta. rewrite <- En.
  replace (d_bsLive (d_set_state d lbl)) with (d_bsLive d) by (destruct d; reflexivity).
  replace (d_bsBuff (d_set_state d lbl)) with (d_bsBuff d) by (destruct d; reflexivity).
  replace (n <=? d_bsLive d) with true by (symmetry; apply Z.leb_le; lia).
  unfold dgo, gbval. destruct (gb_after lbl _ L _ s); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma drun_pull : forall f lbl L d s n b rest, n = gb_bits lbl L -> d_bsLive d < n -> s_in s = b :: rest ->
  drun (S f) lbl L d s =
  drun f lbl L (d_set_bsLive (d_set_bsBuff (d_set_state d lbl) (u32 (Z.lor (Z.shiftl (d_bsBuff d) 8) b))) (d_bsLive d + 8))
       (s_set_tin (s_set_in s rest) (s_tin s + 1)).
Proof.
  intros f lbl L d s n b rest En Hn Hs. rewrite drun_S. cbv zeta. rewrite <- En.
  replace (d_bsLive (d_set_state d lbl)) with (d_bsLive d) by (destruct d; reflexivity).
  replace (d_bsBuff (d_set_state d lbl)) with (d_bsBuff d) by (destruct d; reflexivity).
  replace (n <=? d_bsLive d) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hs. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma drun_eof : forall f lbl L d s n, n = gb_bits lbl L -> d_bsLive d < n -> s_in s = [] ->
  drun (S f) lbl L d s = DRet BZ_OK L (d_set_state d lbl) s.
Proof.
  intros f lbl L d s n En Hn Hs. rewrite drun_S. cbv zeta. rewrite <- En.
  replace (d_bsLive (d_set_state d lbl)) with (d_bsLive d) by (destruct d; reflexivity).
  replace (n <=? d_bsLive d) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hs. reflexivity.
Qed.

(* [comment removed for export] *)
Definition gbst (d : dst) (lbl bb bl : Z) : dst := d_set_bsLive (d_set_bsBuff (d_set_state d lbl) bb) bl.

(* [comment removed for export] *)
Lemma gbst_take : forall d lbl bb bl x, d_set_bsLive (d_set_state (gbst d lbl bb bl) lbl) x = d_set_bsLive (gbst d lbl bb bl) x.
Proof. intros []; reflexivity. Qed.
Lemma gbst_state : forall d lbl bb bl, d_set_state (gbst d lbl bb bl) lbl = gbst d lbl bb bl.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Lemma drun_gbst : forall f lbl L d s, drun (S f) lbl L d s = drun (S f) lbl L (gbst d lbl (d_bsBuff d) (d_bsLive d)) s.
Proof.
  intros f lbl L d s. rewrite !drun_S. cbv zeta. rewrite gbst_state.
  replace (d_set_state d lbl) with (gbst d lbl (d_bsBuff d) (d_bsLive d)) by (destruct d; reflexivity). reflexivity.
Qed.

Lemma drun_bits' : forall f lbl L d s bb bl n, n = gb_bits lbl L -> n <= bl ->
  drun (S f) lbl L (gbst d lbl bb bl) s =
  dgo f (gb_after lbl (gbval bb bl n) L (d_set_bsLive (gbst d lbl bb bl) (bl - n)) s).
Proof.
  intros f lbl L d s bb bl n En Hn. rewrite (drun_bits f lbl L _ s n En) by (destruct d; cbn; lia).
  rewrite gbst_take. destruct d; reflexivity.
Qed.

Lemma drun_pull' : forall f lbl L d s bb bl n b rest, n = gb_bits lbl L -> bl < n -> s_in s = b :: rest ->
  drun (S f) lbl L (gbst d lbl bb bl) s =
  drun f lbl L (gbst d lbl (u32 (Z.lor (Z.shiftl bb 8) b)) (bl + 8)) (s_set_tin (s_set_in s rest) (s_tin s + 1)).
Proof.
  intros f lbl L d s bb bl n b rest En Hn Hs. rewrite (drun_pull f lbl L _ s n b rest En) by first [destruct d; cbn; lia | exact Hs].
  destruct d; reflexivity.
Qed.

Lemma drun_eof' : forall f lbl L d s bb bl n, n = gb_bits lbl L -> bl < n -> s_in s = [] ->
  drun (S f) lbl L (gbst d lbl bb bl) s = DRet BZ_OK L (gbst d lbl bb bl) s.
Proof.
  intros f lbl L d s bb bl n En Hn Hs. rewrite (drun_eof f lbl L _ s n En) by first [destruct d; cbn; lia | exact Hs].
  rewrite gbst_state. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma drun_pull_D : forall f lbl L d bb bl n b rest sout sav tin tout, n = gb_bits lbl L -> bl < n ->
  drun (S f) lbl L (gbst d lbl bb bl) (DSTRM (b :: rest) sout sav tin tout) =
  drun f lbl L (gbst d lbl (u32 (Z.lor (Z.shiftl bb 8) b)) (bl + 8)) (DSTRM rest sout sav (tin + 1) tout).
Proof. intros. rewrite (drun_pull' f lbl L d _ bb bl n b rest) by first [assumption | reflexivity]. reflexivity. Qed.
(* [comment removed for export] *)
Lemma fuel_ok_pull_D : forall f d lbl bb bl bb' b rest sout sav tin tin' tout,
  fuel_ok (S f) (gbst d lbl bb bl) (DSTRM (b :: rest) sout sav tin tout) ->
  fuel_ok f (gbst d lbl bb' (bl + 8)) (DSTRM rest sout sav tin' tout).
Proof. intros. eapply fuel_ok_pull; [eassumption| reflexivity | destruct d; cbn; lia]. Qed.

(* [comment removed for export] *)
Lemma fuel_ok_gbst : forall F d lbl s, fuel_ok F d s -> fuel_ok F (gbst d lbl (d_bsBuff d) (d_bsLive d)) s.
Proof. intros F d lbl s H. unfold fuel_ok in *. destruct d; cbn in *. exact H. Qed.
(* [comment removed for export] *)
Lemma fuel_ok_gbst_bits : forall f d lbl bb bl n s, fuel_ok (S f) (gbst d lbl bb bl) s -> 1 <= n ->
  fuel_ok f (d_set_bsLive (gbst d lbl bb bl) (bl - n)) s.
Proof. intros. eapply fuel_ok_bits; [eassumption| reflexivity | destruct d; cbn; lia]. Qed.
Lemma fuel_ok_gbst_S : forall F d lbl bb bl s, fuel_ok F (gbst d lbl bb bl) s -> 0 <= bl -> exists f, F = S f.
Proof. intros F d lbl bb bl s H Hb. eapply fuel_ok_pos; [|exact H]. destruct d; cbn; lia. Qed.

(* [comment removed for export] *)
Lemma decompress_eq : forall d s,
  decompress d s =
  let d0 := if d_state d =? BZ_X_MAGIC_1 then d_set_sv d dsv_zero else d in
  dfin (drun (9 * length (s_in s) + 64) (d_state d0) (d_sv d0) d0 s).
Proof. intros d s. unfold decompress, dfin. cbv zeta. destruct (drun _ _ _ _ s); reflexivity. Qed.

Lemma decompress_eq14 : forall d s, d_state d <> BZ_X_MAGIC_1 ->
  decompress d s = dfin (drun (9 * length (s_in s) + 64) (d_state d) (d_sv d) d s).
Proof.
  intros d s H. rewrite decompress_eq. replace (d_state d =? BZ_X_MAGIC_1) with false by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gb_after_10 : forall v L d s, gb_after 10 v L d s =
    if v =? 66 then DGo 11 L d s else DRet BZ_DATA_ERROR_MAGIC L d s.
Proof. reflexivity. Qed.
Lemma gb_after_11 : forall v L d s, gb_after 11 v L d s =
    if v =? 90 then DGo 12 L d s else DRet BZ_DATA_ERROR_MAGIC L d s.
Proof. reflexivity. Qed.
Lemma gb_after_12 : forall v L d s, gb_after 12 v L d s =
    if v =? 104 then DGo 13 L d s else DRet BZ_DATA_ERROR_MAGIC L d s.
Proof. reflexivity. Qed.
Lemma gb_after_13 : forall v L d s, gb_after 13 v L d s =
    let d1 := d_set_bs100k d v in
    if (v <? 49) || (57 <? v) then DRet BZ_DATA_ERROR_MAGIC L d1 s
    else let d2 := d_set_bs100k d1 (v - 48) in
    let d3 := if smallb d2 then d_set_ll_al d2 true else d_set_tt_al d2 true in
    DGo 14 L d3 s.
Proof. reflexivity. Qed.
Lemma gb_after_14 : forall v L d s, gb_after 14 v L d s =
    if v =? 23 then DGo 42 L d s else if v =? 49 then DGo 15 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_15 : forall v L d s, gb_after 15 v L d s =
    if v =? 65 then DGo 16 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_16 : forall v L d s, gb_after 16 v L d s =
    if v =? 89 then DGo 17 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_17 : forall v L d s, gb_after 17 v L d s =
    if v =? 38 then DGo 18 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_18 : forall v L d s, gb_after 18 v L d s =
    if v =? 83 then DGo 19 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_19 : forall v L d s, gb_after 19 v L d s =
    if v =? 89 then DGo 20 L (d_set_sbcrc (d_set_blockNo d (d_blockNo d + 1)) 0) s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_20 : forall v L d s, gb_after 20 v L d s =
    DGo 21 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_21 : forall v L d s, gb_after 21 v L d s =
    DGo 22 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_22 : forall v L d s, gb_after 22 v L d s =
    DGo 23 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_23 : forall v L d s, gb_after 23 v L d s =
    DGo 24 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_24 : forall v L d s, gb_after 24 v L d s =
    DGo 25 L (d_set_origPtr (d_set_rand d v) 0) s.
Proof. reflexivity. Qed.
Lemma gb_after_25 : forall v L d s, gb_after 25 v L d s =
    DGo 26 L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s.
Proof. reflexivity. Qed.
Lemma gb_after_26 : forall v L d s, gb_after 26 v L d s =
    DGo 27 L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s.
Proof. reflexivity. Qed.
Lemma gb_after_27 : forall v L d s, gb_after 27 v L d s =
    let d1 := d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v) in
    if d_origPtr d1 <? 0 then DRet BZ_DATA_ERROR L d1 s
    else if 10 + 100000 * d_bs100k d1 <? d_origPtr d1 then DRet BZ_DATA_ERROR L d1 s
    else DGo 28 (sv_set_i L 0) d1 s.
Proof. reflexivity. Qed.
Lemma gb_after_28 : forall v L d s, gb_after 28 v L d s =
    let d1 := d_set_inUse16 d (zset (d_inUse16 d) (sv_i L) (if v =? 1 then 1 else 0)) in
    let i1 := sv_i L + 1 in
    if i1 <? 16 then DGo 28 (sv_set_i L i1) d1 s
    else let d2 := d_set_inUse d1 (clear256 256 0 (d_inUse d1)) in
    map2_outer 17 0 (sv_set_i L 256) d2 s.
Proof. reflexivity. Qed.
Lemma gb_after_29 : forall v L d s, gb_after 29 v L d s =
    let d1 := if v =? 1 then d_set_inUse d (zset (d_inUse d) (sv_i L * 16 + sv_j L) 1) else d in
    let j1 := sv_j L + 1 in
    if j1 <? 16 then DGo 29 (sv_set_j L j1) d1 s
    else map2_outer 17 (sv_i L + 1) (sv_set_j L j1) d1 s.
Proof. reflexivity. Qed.
Lemma gb_after_30 : forall v L d s, gb_after 30 v L d s =
    if (v <? 2) || (BZ_N_GROUPS <? v) then DRet BZ_DATA_ERROR (sv_set_nGroups L v) d s
    else DGo 31 (sv_set_nGroups L v) d s.
Proof. reflexivity. Qed.
Lemma gb_after_31 : forall v L d s, gb_after 31 v L d s =
    if v <? 1 then DRet BZ_DATA_ERROR (sv_set_nSelectors L v) d s
    else DGo 32 (sv_set_j (sv_set_i (sv_set_nSelectors L v) 0) 0) d s.
Proof. reflexivity. Qed.
Lemma gb_after_32 : forall v L d s, gb_after 32 v L d s =
    if v =? 0 then
    let i := sv_i L in let j := sv_j L in
    let d1 := if i <? BZ_MAX_SELECTORS then d_set_selMtf d (zset (d_selMtf d) i j) else d in
    let i1 := i + 1 in
    if i1 <? sv_nSelectors L then DGo 32 (sv_set_j (sv_set_i L i1) 0) d1 s
    else
    
    let nSel := if BZ_MAX_SELECTORS <? sv_nSelectors L then BZ_MAX_SELECTORS else sv_nSelectors L in
    let pos0 := pos_init (Z.to_nat (sv_nGroups L)) 0 znew in
    let '(_, sel1) := sel_undo (Z.to_nat nSel) 0 pos0 (d_selMtf d1) (d_sel d1) in
    DGo 33 (sv_set_t (sv_set_i (sv_set_nSelectors L nSel) nSel) 0) (d_set_sel d1 sel1) s
    else
    let j1 := sv_j L + 1 in
    if sv_nGroups L <=? j1 then DRet BZ_DATA_ERROR (sv_set_j L j1) d s
    else DGo 32 (sv_set_j L j1) d s.
Proof. reflexivity. Qed.
Lemma gb_after_33 : forall v L d s, gb_after 33 v L d s =
    coding_check (sv_set_i (sv_set_curr L v) 0) d s.
Proof. reflexivity. Qed.
Lemma gb_after_34 : forall v L d s, gb_after 34 v L d s =
    if v =? 0 then
    let t := sv_t L in let i := sv_i L in
    let d1 := d_set_len d (zset (d_len d) (258 * t + i) (sv_curr L)) in
    let i1 := i + 1 in
    if i1 <? sv_alphaSize L then coding_check (sv_set_i L i1) d1 s
    else let t1 := t + 1 in
    if t1 <? sv_nGroups L then DGo 33 (sv_set_t (sv_set_i L i1) t1) d1 s
    else after_tables (sv_set_t (sv_set_i L i1) t1) d1 s
    else DGo 35 L d s.
Proof. reflexivity. Qed.
Lemma gb_after_35 : forall v L d s, gb_after 35 v L d s =
    coding_check (sv_set_curr L (if v =? 0 then sv_curr L + 1 else sv_curr L - 1)) d s.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gb_after_42 : forall v L d s, gb_after 42 v L d s =
    if v =? 114 then DGo 43 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_43 : forall v L d s, gb_after 43 v L d s =
    if v =? 69 then DGo 44 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_44 : forall v L d s, gb_after 44 v L d s =
    if v =? 56 then DGo 45 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_45 : forall v L d s, gb_after 45 v L d s =
    if v =? 80 then DGo 46 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_46 : forall v L d s, gb_after 46 v L d s =
    if v =? 144 then DGo 47 L (d_set_sccrc d 0) s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_47 : forall v L d s, gb_after 47 v L d s =
    DGo 48 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_48 : forall v L d s, gb_after 48 v L d s =
    DGo 49 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_49 : forall v L d s, gb_after 49 v L d s =
    DGo 50 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_50 : forall v L d s, gb_after 50 v L d s =
    DRet BZ_STREAM_END L (d_set_state (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) BZ_X_IDLE) s.
Proof. reflexivity. Qed.
