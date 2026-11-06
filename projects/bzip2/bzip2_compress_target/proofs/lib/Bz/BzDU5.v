(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK.
Import ListNotations.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
Module BzDRv.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition rv_ok (r : dres) : Prop :=
  match r with DGo _ _ _ _ => True | DRet rv _ _ _ => -5 <= rv <= 4 | DRetNoSave rv _ _ _ => -5 <= rv <= 4 end.
Lemma rv_DRet : forall rv L d s, -5 <= rv <= 4 -> rv_ok (DRet rv L d s). Proof. intros; exact H. Qed.
Lemma rv_DRetNoSave : forall rv L d s, -5 <= rv <= 4 -> rv_ok (DRetNoSave rv L d s). Proof. intros; exact H. Qed.
Lemma rv_DGo : forall lbl L d s, rv_ok (DGo lbl L d s). Proof. intros; exact I. Qed.

Ltac rvc := unfold BZ_OK, BZ_DATA_ERROR, BZ_DATA_ERROR_MAGIC, BZ_STREAM_END, BZ_MEM_ERROR; lia.
(* [comment removed for export] *)
Ltac rvt leaf :=
  lazymatch goal with
  | |- rv_ok (DGo _ _ _ _) => apply rv_DGo
  | |- rv_ok (DRet _ _ _ _) => apply rv_DRet; rvc
  | |- rv_ok (DRetNoSave _ _ _ _) => apply rv_DRetNoSave; rvc
  | |- rv_ok (if ?c then _ else _) => destruct c; rvt leaf
  | |- rv_ok (match ?e with _ => _ end) => destruct e; rvt leaf
  | |- _ => leaf
  end.

Lemma rv_block_end : forall L d s, rv_ok (block_end L d s).
Proof. intros. unfold block_end. cbv zeta. rvt fail. Qed.

Lemma rv_mtf_val_start : forall lbl L d s, rv_ok (mtf_val_start lbl L d s).
Proof. intros. unfold mtf_val_start. cbv zeta. rvt fail. Qed.

Lemma rv_run_body : forall L d s, rv_ok (run_body L d s).
Proof. intros. unfold run_body. cbv zeta. rvt ltac:(apply rv_mtf_val_start). Qed.

Lemma rv_sym_dispatch : forall L d s, rv_ok (sym_dispatch L d s).
Proof.
  intros. unfold sym_dispatch. cbv zeta.
  rvt ltac:(first [apply rv_block_end | apply rv_run_body | apply rv_mtf_val_start]).
Qed.

Lemma rv_run_exit : forall L d s, rv_ok (run_exit L d s).
Proof. intros. unfold run_exit. cbv zeta. rvt ltac:(apply rv_sym_dispatch). Qed.

Lemma rv_mtf_val_loop : forall w L d s, rv_ok (mtf_val_loop w L d s).
Proof.
  intros. unfold mtf_val_loop. cbv zeta.
  rvt ltac:(first [apply rv_run_body | apply rv_run_exit | apply rv_sym_dispatch]).
Qed.

Lemma rv_coding_check : forall L d s, rv_ok (coding_check L d s).
Proof. intros. unfold coding_check. rvt fail. Qed.

Lemma rv_after_tables : forall L d s, rv_ok (after_tables L d s).
Proof. intros. unfold after_tables. cbv zeta. apply rv_mtf_val_start. Qed.

Lemma rv_map2_outer : forall n i L d s, rv_ok (map2_outer n i L d s).
Proof.
  induction n as [|n IH]; intros i L d s; cbn [map2_outer]; cbv zeta; rvt ltac:(apply IH).
Qed.

Lemma rv_gb_after : forall lbl v L d s, rv_ok (gb_after lbl v L d s).
Proof.
  intros. unfold gb_after. cbv zeta.
  rvt ltac:(first [ apply rv_map2_outer | apply rv_coding_check | apply rv_after_tables | apply rv_mtf_val_loop ]).
Qed.

Lemma rv_drun : forall f lbl L d s, rv_ok (drun f lbl L d s).
Proof.
  induction f as [|f IH]; intros lbl L d s.
  - cbn [drun]. apply rv_DRet. rvc.
  - cbn [drun]. cbv zeta.
    destruct (gb_bits lbl L <=? d_bsLive (d_set_state d lbl)).
    + pose proof (rv_gb_after lbl (Z.land (Z.shiftr (d_bsBuff (d_set_state d lbl)) (d_bsLive (d_set_state d lbl) - gb_bits lbl L))
                    (Z.shiftl 1 (gb_bits lbl L) - 1)) L (d_set_bsLive (d_set_state d lbl) (d_bsLive (d_set_state d lbl) - gb_bits lbl L)) s) as G.
      destruct (gb_after _ _ _ _ _); [apply IH | exact G | exact G].
    + destruct (s_in s); [apply rv_DRet; rvc | apply IH].
Qed.

(* [comment removed for export] *)
Theorem decompress_rv : forall d s, let '(rv, _, _) := decompress d s in -5 <= rv <= 4.
Proof.
  intros d s. unfold decompress. cbv zeta.
  match goal with |- context [drun ?f ?l ?L ?dd ?ss] => pose proof (rv_drun f l L dd ss) as R; destruct (drun f l L dd ss) end;
    cbn in R; [unfold BZ_OK; lia | exact R | exact R].
Qed.
End BzDRv.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition belown (a : zarr) (n ng : Z) : Prop := forall k, 0 <= k < n -> 0 <= zget a k < ng.

Lemma belown_0 : forall a ng, belown a 0 ng.
Proof. intros a ng k Hk. lia. Qed.
(* [comment removed for export] *)
Lemma belown_set : forall a n ng v, belown a n ng -> 0 <= v < ng -> belown (zset a n v) (n + 1) ng.
Proof.
  intros a n ng v H Hv k Hk. rewrite zget_zset. destruct (Z.eqb_spec k n); [lia|]. apply H. lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nsel_clamp (ns : Z) : Z := if BZ_MAX_SELECTORS <? ns then BZ_MAX_SELECTORS else ns.
Lemma nsel_clamp_eq : forall ns, nsel_clamp ns = Z.min ns 18002.
Proof. intros ns. unfold nsel_clamp, BZ_MAX_SELECTORS. destruct (Z.ltb_spec 18002 ns); lia. Qed.

(* [comment removed for export] *)
Definition L_cod (L : dsv) (nsc : Z) : dsv := sv_set_t (sv_set_i (sv_set_nSelectors L nsc) nsc) 0.

(* [comment removed for export] *)
Definition K_LP2 (F : nat) (L : dsv) (d : dst) (s : dstrm) (nsc i : Z) (pos : zarr) : dres :=
  let '(_, sel1) := sel_undo (Z.to_nat (nsc - i)) i pos (d_selMtf d) (d_sel d) in
  drun F 33 (L_cod L nsc) (d_set_sel d sel1) s.
(* [comment removed for export] *)
Definition K_X78 (F : nat) (L : dsv) (d : dst) (s : dstrm) (nsc i : Z) (pos : zarr) (tmp : Z) : dres :=
  K_LP2 F L (d_set_sel d (zset (d_sel d) i tmp)) s nsc (i + 1) (zset pos 0 tmp).
(* [comment removed for export] *)
Definition K_LP3 (F : nat) (L : dsv) (d : dst) (s : dstrm) (nsc i : Z) (pos : zarr) (tmp w : Z) : dres :=
  K_X78 F L d s nsc i (pos_shift (Z.to_nat w) w pos) tmp.
(* [comment removed for export] *)
Definition K_LP1 (F : nat) (L : dsv) (d : dst) (s : dstrm) (nsc v : Z) (pos : zarr) : dres :=
  K_LP2 F L d s nsc 0 (pos_init (Z.to_nat (sv_nGroups L - v)) v pos).
(* [comment removed for export] *)
Definition K_HUND (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres :=
  K_LP1 F L d s (nsel_clamp (sv_nSelectors L)) 0 znew.
(* [comment removed for export] *)
Definition K_HCOD (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres :=
  if sv_t L <? sv_nGroups L then drun F 33 L d s else dgo F (after_tables L d s).
(* [comment removed for export] *)
Definition K_L5O (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres :=
  if sv_i L <? sv_nSelectors L then drun F 32 (sv_set_j L 0) d s else K_HUND F L d s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Lsplit L :=
  destruct L as [L_i L_j L_t L_alphaSize L_nGroups L_nSelectors L_EOB L_groupNo L_groupPos L_nextSym L_nblockMAX
                 L_nblock L_es L_N L_curr L_zt L_zn L_zvec L_zj L_gSel L_gMinlen L_gPtr];
  cbv beta iota delta [sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock
       sv_es sv_N sv_curr sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr
       sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos
       sv_set_nextSym sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj
       sv_set_gSel sv_set_gMinlen sv_set_gPtr] in *.

(* [comment removed for export] *)
Ltac bz_consts := cbv delta [BZ_N_GROUPS BZ_MAX_SELECTORS BZ_MAX_ALPHA_SIZE BZ_G_SIZE BZ_RUNA BZ_RUNB MTFA_SIZE MTFL_SIZE
                             BZ_X_IDLE BZ_X_OUTPUT BZ_X_MAGIC_1 BZ_X_BLKHDR_1 BZ_X_MTF_1 BZ_X_MTF_3 BZ_X_MTF_5
                             BZ_OK BZ_STREAM_END BZ_DATA_ERROR BZ_DATA_ERROR_MAGIC BZ_MEM_ERROR].
Ltac blia :=
  bz_consts;
  rewrite ?Bool.orb_true_iff, ?Bool.orb_false_iff, ?Bool.andb_true_iff, ?Bool.andb_false_iff,
          ?Bool.negb_true_iff, ?Bool.negb_false_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq; lia.

Lemma dgo_if_true : forall F (c : bool) r1 r2, c = true -> dgo F (if c then r1 else r2) = dgo F r1.
Proof. intros F c r1 r2 ->. reflexivity. Qed.
Lemma dgo_if_false : forall F (c : bool) r1 r2, c = false -> dgo F (if c then r1 else r2) = dgo F r2.
Proof. intros F c r1 r2 ->. reflexivity. Qed.
Lemma if_trueP : forall {T} (c : bool) (r1 r2 : T), c = true -> (if c then r1 else r2) = r1.
Proof. intros T c r1 r2 ->. reflexivity. Qed.
Lemma if_falseP : forall {T} (c : bool) (r1 r2 : T), c = false -> (if c then r1 else r2) = r2.
Proof. intros T c r1 r2 ->. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_set_sel_sel : forall d a b, d_set_sel (d_set_sel d a) b = d_set_sel d b.
Proof. intros []; reflexivity. Qed.
Lemma d_set_sel_id : forall d, d_set_sel d (d_sel d) = d.
Proof. intros []; reflexivity. Qed.
Lemma d_sel_set_sel : forall d a, d_sel (d_set_sel d a) = a.
Proof. intros []; reflexivity. Qed.
Lemma d_selMtf_set_sel : forall d a, d_selMtf (d_set_sel d a) = d_selMtf d.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma edge_31 : forall F v L d s, 1 <= v ->
  dgo F (gb_after 31 v L d s) = K_L5O F (sv_set_i (sv_set_nSelectors L v) 0) d s.
Proof.
  intros F v L d s Hv. rewrite gb_after_31. unfold K_L5O.
  replace (v <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  Lsplit L. replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma edge_31_ret : forall v L d s, v < 1 ->
  gb_after 31 v L d s = DRet BZ_DATA_ERROR (sv_set_nSelectors L v) d s.
Proof. intros v L d s Hv. rewrite gb_after_31. replace (v <? 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma K_L5O_lt : forall F L d s, sv_i L < sv_nSelectors L -> K_L5O F L d s = drun F 32 (sv_set_j L 0) d s.
Proof. intros. unfold K_L5O. replace (sv_i L <? sv_nSelectors L) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma K_L5O_ge : forall F L d s, sv_nSelectors L <= sv_i L -> K_L5O F L d s = K_HUND F L d s.
Proof. intros. unfold K_L5O. replace (sv_i L <? sv_nSelectors L) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma edge_32_0 : forall F L d s,
  dgo F (gb_after 32 0 L d s) =
  K_L5O F (sv_set_i L (sv_i L + 1))
    (if sv_i L <? BZ_MAX_SELECTORS then d_set_selMtf d (zset (d_selMtf d) (sv_i L) (sv_j L)) else d) s.
Proof.
  intros F L d s. rewrite gb_after_32. change (0 =? 0) with true. cbv iota. cbv zeta.
  unfold K_L5O, K_HUND, K_LP1, K_LP2, nsel_clamp, L_cod. rewrite !Z.sub_0_r.
  Lsplit L. rewrite dgo_if, dgo_DGo.
  destruct (L_i + 1 <? L_nSelectors); [reflexivity|].
  destruct (sel_undo _ 0 _ _ _) as [p sel1]. reflexivity.
Qed.
Lemma edge_32_0' : forall F v L d s, v = 0 ->
  dgo F (gb_after 32 v L d s) =
  K_L5O F (sv_set_i L (sv_i L + 1))
    (if sv_i L <? BZ_MAX_SELECTORS then d_set_selMtf d (zset (d_selMtf d) (sv_i L) (sv_j L)) else d) s.
Proof. intros F v L d s ->. apply edge_32_0. Qed.
(* [comment removed for export] *)
Lemma edge_32_1 : forall v L d s, v <> 0 ->
  gb_after 32 v L d s =
  if sv_nGroups L <=? sv_j L + 1 then DRet BZ_DATA_ERROR (sv_set_j L (sv_j L + 1)) d s
  else DGo 32 (sv_set_j L (sv_j L + 1)) d s.
Proof. intros v L d s Hv. rewrite gb_after_32. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hv). reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_HUND_LP1 : forall F L d s, K_HUND F L d s = K_LP1 F L d s (nsel_clamp (sv_nSelectors L)) 0 znew.
Proof. reflexivity. Qed.

Lemma K_LP1_step : forall F L d s nsc v pos, 0 <= v < sv_nGroups L ->
  K_LP1 F L d s nsc v pos = K_LP1 F L d s nsc (v + 1) (zset pos v v).
Proof.
  intros F L d s nsc v pos Hv. unfold K_LP1.
  replace (Z.to_nat (sv_nGroups L - v)) with (S (Z.to_nat (sv_nGroups L - (v + 1)))) by lia. reflexivity.
Qed.
Lemma K_LP1_exit : forall F L d s nsc v pos, v = sv_nGroups L ->
  K_LP1 F L d s nsc v pos = K_LP2 F L d s nsc 0 pos.
Proof. intros F L d s nsc v pos ->. unfold K_LP1. rewrite Z.sub_diag. reflexivity. Qed.

Lemma pos_shift_fuel : forall n m v pos, (Z.to_nat v <= n)%nat -> (Z.to_nat v <= m)%nat ->
  pos_shift n v pos = pos_shift m v pos.
Proof.
  intros n. induction n as [|n IH]; intros m v pos Hn Hm.
  - destruct m as [|m]; [reflexivity|]. cbn. destruct (Z.ltb_spec 0 v); [exfalso; lia| reflexivity].
  - destruct m as [|m]; cbn.
    + destruct (Z.ltb_spec 0 v); [exfalso; lia| reflexivity].
    + destruct (Z.ltb_spec 0 v); [|reflexivity]. apply IH; lia.
Qed.

Lemma K_LP2_step : forall F L d s nsc i pos, 0 <= i < nsc ->
  let v := zget (d_selMtf d) i in 0 <= v <= 8 ->
  K_LP2 F L d s nsc i pos =
  (if 0 <? v then K_LP3 F L d s nsc i pos (zget pos v) v else K_X78 F L d s nsc i pos (zget pos v)).
Proof.
  intros F L d s nsc i pos Hi v Hv. unfold K_LP3, K_X78, K_LP2.
  replace (Z.to_nat (nsc - i)) with (S (Z.to_nat (nsc - (i + 1)))) by lia. cbn [sel_undo].
  fold v. rewrite d_selMtf_set_sel, d_sel_set_sel.
  rewrite (pos_shift_fuel 8 (Z.to_nat v) v pos) by lia.
  destruct (Z.ltb_spec 0 v).
  - destruct (sel_undo _ _ _ _ _) as [p sel1]. rewrite d_set_sel_sel. reflexivity.
  - replace (Z.to_nat v) with 0%nat by lia. cbn [pos_shift]. destruct (sel_undo _ _ _ _ _) as [p sel1]. rewrite d_set_sel_sel. reflexivity.
Qed.
Lemma K_LP2_exit : forall F L d s nsc i pos, i = nsc ->
  K_LP2 F L d s nsc i pos = drun F 33 (L_cod L nsc) d s.
Proof. intros F L d s nsc i pos ->. unfold K_LP2. rewrite Z.sub_diag. cbn [sel_undo Z.to_nat]. rewrite d_set_sel_id. reflexivity. Qed.

Lemma K_LP2_exit_HCOD : forall F L d s nsc i pos, i = nsc -> 1 <= sv_nGroups L ->
  K_LP2 F L d s nsc i pos = K_HCOD F (L_cod L nsc) d s.
Proof.
  intros F L d s nsc i pos Hi Hg. rewrite K_LP2_exit by exact Hi. unfold K_HCOD.
  replace (sv_t (L_cod L nsc) <? sv_nGroups (L_cod L nsc)) with true; [reflexivity|].
  symmetry. apply Z.ltb_lt. unfold L_cod. Lsplit L. lia.
Qed.

Lemma K_LP3_step : forall F L d s nsc i pos tmp w, 1 <= w ->
  K_LP3 F L d s nsc i pos tmp w = 
  (if 0 <? w - 1 then K_LP3 F L d s nsc i (zset pos w (zget pos (w - 1))) tmp (w - 1)
   else K_X78 F L d s nsc i (zset pos w (zget pos (w - 1))) tmp).
Proof.
  intros F L d s nsc i pos tmp w Hw. unfold K_LP3.
  replace (Z.to_nat w) with (S (Z.to_nat (w - 1))) by lia. cbn [pos_shift].
  replace (0 <? w) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (Z.ltb_spec 0 (w - 1)); [reflexivity|].
  replace (Z.to_nat (w - 1)) with 0%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hdr_ok (d : dst) : Prop :=
  0 <= d_rand d <= 1 /\ 0 <= d_sbcrc d < 2^32 /\ 0 <= d_origPtr d <= 900010.
Definition alpha_ok (L : dsv) (d : dst) : Prop :=
  (sv_alphaSize L = d_nInUse d + 2 /\ 1 <= d_nInUse d <= 256 /\
   0 <= d_rand d <= 1 /\ 0 <= d_sbcrc d < 2^32 /\ 0 <= d_origPtr d <= 900010 /\
   d_state d <> 2 (* [comment removed for export] *)) /\
  0 <= sv_nblock L <= 900000.
Lemma alpha_ok_hdr : forall L d, alpha_ok L d -> hdr_ok d.
Proof. intros L d [(_ & _ & C & D & E & _) _]. exact (conj C (conj D E)). Qed.
Lemma alpha_ok_state : forall L d, alpha_ok L d -> d_state d <> BZ_X_OUTPUT.
Proof. intros L d [(_ & _ & _ & _ & _ & S) _]. exact S. Qed.

Definition dinv_HSEL (L : dsv) (d : dst) : Prop := alpha_ok L d.

Definition dinv_L5O (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ 2 <= sv_nGroups L <= 6 /\ 1 <= sv_nSelectors L < 32768 /\ 0 <= sv_i L <= sv_nSelectors L /\
  belown (d_selMtf d) (Z.min (sv_i L) 18002) (sv_nGroups L).

Definition dinv_L5I (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ 2 <= sv_nGroups L <= 6 /\ 1 <= sv_nSelectors L < 32768 /\ 0 <= sv_i L < sv_nSelectors L /\
  0 <= sv_j L < sv_nGroups L /\
  belown (d_selMtf d) (Z.min (sv_i L) 18002) (sv_nGroups L).

Definition dinv_HUND (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ 2 <= sv_nGroups L <= 6 /\ 1 <= sv_nSelectors L < 32768 /\
  belown (d_selMtf d) (Z.min (sv_nSelectors L) 18002) (sv_nGroups L).

(* [comment removed for export] *)
Definition dinv_HCOD (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ 2 <= sv_nGroups L <= 6 /\ 1 <= sv_nSelectors L <= 18002 /\
  belown (d_sel d) (sv_nSelectors L) (sv_nGroups L) /\
  0 <= sv_t L <= sv_nGroups L /\
  (forall t i, 0 <= t < sv_t L -> 0 <= i < sv_alphaSize L -> 1 <= zget (d_len d) (258 * t + i) <= 20).

(* [comment removed for export] *)
(* [comment removed for export] *)
