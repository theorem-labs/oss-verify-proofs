(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCStream BzDBlock BzR5a.
Import ListNotations.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDState. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
Module BzR5cLB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition setLB (d : dst) (B V : Z) : dst := d_set_bsLive (d_set_bsBuff d B) V.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lbg_state : forall d B V, d_state (setLB d B V) = d_state d. Proof. intros; reflexivity. Qed.
Lemma lbg_out_ch : forall d B V, d_out_ch (setLB d B V) = d_out_ch d. Proof. intros; reflexivity. Qed.
Lemma lbg_out_len : forall d B V, d_out_len (setLB d B V) = d_out_len d. Proof. intros; reflexivity. Qed.
Lemma lbg_rand : forall d B V, d_rand (setLB d B V) = d_rand d. Proof. intros; reflexivity. Qed.
Lemma lbg_rNToGo : forall d B V, d_rNToGo (setLB d B V) = d_rNToGo d. Proof. intros; reflexivity. Qed.
Lemma lbg_rTPos : forall d B V, d_rTPos (setLB d B V) = d_rTPos d. Proof. intros; reflexivity. Qed.
Lemma lbg_bs100k : forall d B V, d_bs100k (setLB d B V) = d_bs100k d. Proof. intros; reflexivity. Qed.
Lemma lbg_small : forall d B V, d_small (setLB d B V) = d_small d. Proof. intros; reflexivity. Qed.
Lemma lbg_blockNo : forall d B V, d_blockNo (setLB d B V) = d_blockNo d. Proof. intros; reflexivity. Qed.
Lemma lbg_verb : forall d B V, d_verb (setLB d B V) = d_verb d. Proof. intros; reflexivity. Qed.
Lemma lbg_origPtr : forall d B V, d_origPtr (setLB d B V) = d_origPtr d. Proof. intros; reflexivity. Qed.
Lemma lbg_tPos : forall d B V, d_tPos (setLB d B V) = d_tPos d. Proof. intros; reflexivity. Qed.
Lemma lbg_k0 : forall d B V, d_k0 (setLB d B V) = d_k0 d. Proof. intros; reflexivity. Qed.
Lemma lbg_unzftab : forall d B V, d_unzftab (setLB d B V) = d_unzftab d. Proof. intros; reflexivity. Qed.
Lemma lbg_nused : forall d B V, d_nused (setLB d B V) = d_nused d. Proof. intros; reflexivity. Qed.
Lemma lbg_cftab : forall d B V, d_cftab (setLB d B V) = d_cftab d. Proof. intros; reflexivity. Qed.
Lemma lbg_cftabCopy : forall d B V, d_cftabCopy (setLB d B V) = d_cftabCopy d. Proof. intros; reflexivity. Qed.
Lemma lbg_tt : forall d B V, d_tt (setLB d B V) = d_tt d. Proof. intros; reflexivity. Qed.
Lemma lbg_ll16 : forall d B V, d_ll16 (setLB d B V) = d_ll16 d. Proof. intros; reflexivity. Qed.
Lemma lbg_ll4 : forall d B V, d_ll4 (setLB d B V) = d_ll4 d. Proof. intros; reflexivity. Qed.
Lemma lbg_tt_al : forall d B V, d_tt_al (setLB d B V) = d_tt_al d. Proof. intros; reflexivity. Qed.
Lemma lbg_ll_al : forall d B V, d_ll_al (setLB d B V) = d_ll_al d. Proof. intros; reflexivity. Qed.
Lemma lbg_sbcrc : forall d B V, d_sbcrc (setLB d B V) = d_sbcrc d. Proof. intros; reflexivity. Qed.
Lemma lbg_sccrc : forall d B V, d_sccrc (setLB d B V) = d_sccrc d. Proof. intros; reflexivity. Qed.
Lemma lbg_cbcrc : forall d B V, d_cbcrc (setLB d B V) = d_cbcrc d. Proof. intros; reflexivity. Qed.
Lemma lbg_cccrc : forall d B V, d_cccrc (setLB d B V) = d_cccrc d. Proof. intros; reflexivity. Qed.
Lemma lbg_nInUse : forall d B V, d_nInUse (setLB d B V) = d_nInUse d. Proof. intros; reflexivity. Qed.
Lemma lbg_inUse : forall d B V, d_inUse (setLB d B V) = d_inUse d. Proof. intros; reflexivity. Qed.
Lemma lbg_inUse16 : forall d B V, d_inUse16 (setLB d B V) = d_inUse16 d. Proof. intros; reflexivity. Qed.
Lemma lbg_s2u : forall d B V, d_s2u (setLB d B V) = d_s2u d. Proof. intros; reflexivity. Qed.
Lemma lbg_mtfa : forall d B V, d_mtfa (setLB d B V) = d_mtfa d. Proof. intros; reflexivity. Qed.
Lemma lbg_mtfbase : forall d B V, d_mtfbase (setLB d B V) = d_mtfbase d. Proof. intros; reflexivity. Qed.
Lemma lbg_sel : forall d B V, d_sel (setLB d B V) = d_sel d. Proof. intros; reflexivity. Qed.
Lemma lbg_selMtf : forall d B V, d_selMtf (setLB d B V) = d_selMtf d. Proof. intros; reflexivity. Qed.
Lemma lbg_len : forall d B V, d_len (setLB d B V) = d_len d. Proof. intros; reflexivity. Qed.
Lemma lbg_limit : forall d B V, d_limit (setLB d B V) = d_limit d. Proof. intros; reflexivity. Qed.
Lemma lbg_base : forall d B V, d_base (setLB d B V) = d_base d. Proof. intros; reflexivity. Qed.
Lemma lbg_perm : forall d B V, d_perm (setLB d B V) = d_perm d. Proof. intros; reflexivity. Qed.
Lemma lbg_minLens : forall d B V, d_minLens (setLB d B V) = d_minLens d. Proof. intros; reflexivity. Qed.
Lemma lbg_sv : forall d B V, d_sv (setLB d B V) = d_sv d. Proof. intros; reflexivity. Qed.
Lemma lbg_bsBuff : forall d B V, d_bsBuff (setLB d B V) = B. Proof. intros; reflexivity. Qed.
Lemma lbg_bsLive : forall d B V, d_bsLive (setLB d B V) = V. Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Lemma lbs_state : forall d B V v, d_set_state (setLB d B V) v = setLB (d_set_state d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_out_ch : forall d B V v, d_set_out_ch (setLB d B V) v = setLB (d_set_out_ch d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_out_len : forall d B V v, d_set_out_len (setLB d B V) v = setLB (d_set_out_len d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_rand : forall d B V v, d_set_rand (setLB d B V) v = setLB (d_set_rand d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_rNToGo : forall d B V v, d_set_rNToGo (setLB d B V) v = setLB (d_set_rNToGo d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_rTPos : forall d B V v, d_set_rTPos (setLB d B V) v = setLB (d_set_rTPos d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_bs100k : forall d B V v, d_set_bs100k (setLB d B V) v = setLB (d_set_bs100k d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_small : forall d B V v, d_set_small (setLB d B V) v = setLB (d_set_small d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_blockNo : forall d B V v, d_set_blockNo (setLB d B V) v = setLB (d_set_blockNo d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_verb : forall d B V v, d_set_verb (setLB d B V) v = setLB (d_set_verb d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_origPtr : forall d B V v, d_set_origPtr (setLB d B V) v = setLB (d_set_origPtr d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_tPos : forall d B V v, d_set_tPos (setLB d B V) v = setLB (d_set_tPos d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_k0 : forall d B V v, d_set_k0 (setLB d B V) v = setLB (d_set_k0 d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_unzftab : forall d B V v, d_set_unzftab (setLB d B V) v = setLB (d_set_unzftab d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_nused : forall d B V v, d_set_nused (setLB d B V) v = setLB (d_set_nused d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_cftab : forall d B V v, d_set_cftab (setLB d B V) v = setLB (d_set_cftab d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_cftabCopy : forall d B V v, d_set_cftabCopy (setLB d B V) v = setLB (d_set_cftabCopy d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_tt : forall d B V v, d_set_tt (setLB d B V) v = setLB (d_set_tt d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_ll16 : forall d B V v, d_set_ll16 (setLB d B V) v = setLB (d_set_ll16 d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_ll4 : forall d B V v, d_set_ll4 (setLB d B V) v = setLB (d_set_ll4 d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_tt_al : forall d B V v, d_set_tt_al (setLB d B V) v = setLB (d_set_tt_al d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_ll_al : forall d B V v, d_set_ll_al (setLB d B V) v = setLB (d_set_ll_al d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_sbcrc : forall d B V v, d_set_sbcrc (setLB d B V) v = setLB (d_set_sbcrc d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_sccrc : forall d B V v, d_set_sccrc (setLB d B V) v = setLB (d_set_sccrc d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_cbcrc : forall d B V v, d_set_cbcrc (setLB d B V) v = setLB (d_set_cbcrc d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_cccrc : forall d B V v, d_set_cccrc (setLB d B V) v = setLB (d_set_cccrc d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_nInUse : forall d B V v, d_set_nInUse (setLB d B V) v = setLB (d_set_nInUse d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_inUse : forall d B V v, d_set_inUse (setLB d B V) v = setLB (d_set_inUse d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_inUse16 : forall d B V v, d_set_inUse16 (setLB d B V) v = setLB (d_set_inUse16 d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_s2u : forall d B V v, d_set_s2u (setLB d B V) v = setLB (d_set_s2u d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_mtfa : forall d B V v, d_set_mtfa (setLB d B V) v = setLB (d_set_mtfa d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_mtfbase : forall d B V v, d_set_mtfbase (setLB d B V) v = setLB (d_set_mtfbase d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_sel : forall d B V v, d_set_sel (setLB d B V) v = setLB (d_set_sel d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_selMtf : forall d B V v, d_set_selMtf (setLB d B V) v = setLB (d_set_selMtf d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_len : forall d B V v, d_set_len (setLB d B V) v = setLB (d_set_len d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_limit : forall d B V v, d_set_limit (setLB d B V) v = setLB (d_set_limit d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_base : forall d B V v, d_set_base (setLB d B V) v = setLB (d_set_base d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_perm : forall d B V v, d_set_perm (setLB d B V) v = setLB (d_set_perm d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_minLens : forall d B V v, d_set_minLens (setLB d B V) v = setLB (d_set_minLens d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_sv : forall d B V v, d_set_sv (setLB d B V) v = setLB (d_set_sv d v) B V. Proof. intros; destruct d; reflexivity. Qed.
Lemma lbs_setLB : forall d B V B' V', setLB (setLB d B V) B' V' = setLB d B' V'. Proof. intros; destruct d; reflexivity. Qed.

Lemma setLB_eq : forall d B V, setLB d B V = d_set_bsLive (d_set_bsBuff d B) V. Proof. reflexivity. Qed.
Opaque setLB.
Create Rewrite HintDb lb.
#[export] Hint Rewrite lbg_state lbg_out_ch lbg_out_len lbg_rand lbg_rNToGo lbg_rTPos lbg_bs100k lbg_small lbg_blockNo lbg_verb lbg_origPtr lbg_tPos lbg_k0 lbg_unzftab lbg_nused lbg_cftab lbg_cftabCopy lbg_tt lbg_ll16 lbg_ll4 lbg_tt_al lbg_ll_al lbg_sbcrc lbg_sccrc lbg_cbcrc lbg_cccrc lbg_nInUse lbg_inUse lbg_inUse16 lbg_s2u lbg_mtfa lbg_mtfbase lbg_sel lbg_selMtf lbg_len lbg_limit lbg_base lbg_perm lbg_minLens lbg_sv lbs_state lbs_out_ch lbs_out_len lbs_rand lbs_rNToGo lbs_rTPos lbs_bs100k lbs_small lbs_blockNo lbs_verb lbs_origPtr lbs_tPos lbs_k0 lbs_unzftab lbs_nused lbs_cftab lbs_cftabCopy lbs_tt lbs_ll16 lbs_ll4 lbs_tt_al lbs_ll_al lbs_sbcrc lbs_sccrc lbs_cbcrc lbs_cccrc lbs_nInUse lbs_inUse lbs_inUse16 lbs_s2u lbs_mtfa lbs_mtfbase lbs_sel lbs_selMtf lbs_len lbs_limit lbs_base lbs_perm lbs_minLens lbs_sv lbs_setLB : lb.

Lemma lb_if : forall (c : bool) x y B V, (if c then setLB x B V else setLB y B V) = setLB (if c then x else y) B V.
Proof. intros [|]; reflexivity. Qed.
Lemma lb_smallb : forall d B V, smallb (setLB d B V) = smallb d.
Proof. intros; reflexivity. Qed.
Lemma lb_rand_mask : forall d B V, rand_mask (setLB d B V) = rand_mask d.
Proof. intros; reflexivity. Qed.
Lemma lb_rand_upd : forall d B V, rand_upd (setLB d B V) = setLB (rand_upd d) B V.
Proof.
  intros d B V. unfold rand_upd. rewrite lbg_rNToGo, lbg_rTPos.
  destruct (d_rNToGo d =? 0); autorewrite with lb; reflexivity.
Qed.
Lemma lb_get_ll4 : forall d B V i, get_ll4 (setLB d B V) i = get_ll4 d i.
Proof. intros; reflexivity. Qed.
Lemma lb_get_ll : forall d B V i, get_ll (setLB d B V) i = get_ll d i.
Proof. intros; reflexivity. Qed.
Lemma lb_set_ll4 : forall d B V i n, set_ll4 (setLB d B V) i n = setLB (set_ll4 d i n) B V.
Proof. intros; destruct d; reflexivity. Qed.
Lemma lb_set_ll : forall d B V i n, set_ll (setLB d B V) i n = setLB (set_ll d i n) B V.
Proof. intros. unfold set_ll. rewrite lbg_ll16, lbs_ll16. apply lb_set_ll4. Qed.
#[export] Hint Rewrite lb_if lb_smallb lb_rand_mask lb_rand_upd lb_get_ll4 lb_get_ll lb_set_ll4 lb_set_ll : lb.

Lemma lb_makeMaps_d : forall d B V, makeMaps_d (setLB d B V) = setLB (makeMaps_d d) B V.
Proof.
  intros d B V. unfold makeMaps_d. rewrite lbg_inUse, lbg_s2u. destruct (mkmaps 256 0 (d_inUse d) (d_s2u d) 0).
  rewrite lbs_s2u, lbs_nInUse. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma make_tables_S : forall n t a d, make_tables (S n) t a d =
  (let off := 258 * t in
   let '(minLen, maxLen) := minmax_len (Z.to_nat a) 0 (d_len d) off 32 0 in
   let '(li, ba, pe) := hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) off minLen maxLen a in
   let d1 := d_set_minLens (d_set_perm (d_set_base (d_set_limit d li) ba) pe) (zset (d_minLens d) t minLen) in
   make_tables n (t + 1) a d1).
Proof. reflexivity. Qed.
Lemma lb_make_tables : forall n t a d B V, make_tables n t a (setLB d B V) = setLB (make_tables n t a d) B V.
Proof.
  induction n as [|n IH]; intros t a d B V; [reflexivity|]. rewrite !make_tables_S. cbv zeta.
  rewrite !lbg_len, !lbg_limit, !lbg_base, !lbg_perm, !lbg_minLens.
  destruct (minmax_len _ _ _ _ _ _) as [mn mx]. destruct (hbCreateDecodeTables _ _ _ _ _ _ _ _) as [[li ba] pe].
  rewrite lbs_limit, lbs_base, lbs_perm, lbs_minLens. apply IH.
Qed.
Lemma lb_mtf_init : forall d B V, mtf_init (setLB d B V) = setLB (mtf_init d) B V.
Proof.
  intros d B V. unfold mtf_init. rewrite lbg_mtfa, lbg_mtfbase. destruct (mtfinit_i _ _ _ _ _) as [a b].
  rewrite lbs_mtfa, lbs_mtfbase. reflexivity.
Qed.
Lemma lb_mtf_decode : forall d B V nn,
  mtf_decode (setLB d B V) nn = (let '(uc, d') := mtf_decode d nn in (uc, setLB d' B V)).
Proof.
  intros d B V nn. unfold mtf_decode. rewrite lbg_mtfa, lbg_mtfbase.
  destruct (nn <? 16).
  - destruct (mtf_sh4 _ _ _ _) as [a1 nn1]. rewrite lbs_mtfa. reflexivity.
  - destruct (mtf_pull _ _ _ _) as [a2 mb2]. destruct (zget mb2 0 - 1 =? 0).
    + destruct (mtfrb_i _ _ _ _ _) as [a4 mb4]. rewrite lbs_mtfa, lbs_mtfbase. reflexivity.
    + rewrite lbs_mtfa, lbs_mtfbase. reflexivity.
Qed.
Lemma tvec_small_S : forall n i d, tvec_small (S n) i d =
  (let uc := Z.land (zget (d_ll16 d) i) 255 in let k := zget (d_cftabCopy d) uc in let d1 := set_ll d i k in
   tvec_small n (i + 1) (d_set_cftabCopy d1 (zset (d_cftabCopy d1) uc (k + 1)))).
Proof. reflexivity. Qed.
Lemma lb_tvec_small : forall n i d B V, tvec_small n i (setLB d B V) = setLB (tvec_small n i d) B V.
Proof.
  induction n as [|n IH]; intros i d B V; [reflexivity|]. rewrite !tvec_small_S. cbv zeta.
  rewrite lbg_ll16, lbg_cftabCopy, lb_set_ll, lbg_cftabCopy, lbs_cftabCopy. apply IH.
Qed.
Lemma prev_loop_S : forall n i j d, prev_loop (S n) i j d =
  (let tmp := get_ll d j in let d1 := set_ll d j i in if j =? d_origPtr d then (j, tmp, d1) else prev_loop n j tmp d1).
Proof. reflexivity. Qed.
Lemma lb_prev_loop : forall n i j d B V,
  prev_loop n i j (setLB d B V) = (let '(i', j', d') := prev_loop n i j d in (i', j', setLB d' B V)).
Proof.
  induction n as [|n IH]; intros i j d B V; [reflexivity|]. rewrite !prev_loop_S. cbv zeta.
  rewrite lb_get_ll, lb_set_ll, lbg_origPtr. destruct (j =? d_origPtr d); [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma run_write_S : forall n small uc nblock es nbMAX d, run_write (S n) small uc nblock es nbMAX d =
  (if 0 <? es then
     if nbMAX <=? nblock then (nblock, es, d, true)
     else let d1 := if small then d_set_ll16 d (zset (d_ll16 d) nblock uc) else d_set_tt d (zset (d_tt d) nblock uc) in
          run_write n small uc (nblock + 1) (es - 1) nbMAX d1
   else (nblock, es, d, false)).
Proof. reflexivity. Qed.
Lemma lb_run_write : forall n sm uc nb es mx d B V,
  run_write n sm uc nb es mx (setLB d B V) = (let '(a, b, d', f) := run_write n sm uc nb es mx d in (a, b, setLB d' B V, f)).
Proof.
  induction n as [|n IH]; intros sm uc nb es mx d B V; [reflexivity|]. rewrite !run_write_S. cbv zeta.
  destruct (0 <? es); [|reflexivity]. destruct (mx <=? nb); [reflexivity|].
  destruct sm; rewrite ?lbg_ll16, ?lbs_ll16, ?lbg_tt, ?lbs_tt; apply IH.
Qed.
#[export] Hint Rewrite lb_makeMaps_d lb_make_tables lb_mtf_init lb_mtf_decode lb_tvec_small lb_prev_loop lb_run_write : lb.

(* [comment removed for export] *)
Ltac dnorm d :=
  destruct d as [x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42];
  cbv beta iota zeta delta [d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k d_set_small
       d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab d_set_cftabCopy d_set_tt d_set_ll16
       d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u
       d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit d_set_base d_set_perm d_set_minLens d_set_sv
       d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0
       d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16
       d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv].

(* [comment removed for export] *)
Definition dres_map2 (F : dst -> dst) (s2 : dstrm) (r : dres) : dres :=
  match r with
  | DGo l L d s => DGo l L (F d) s2
  | DRet rv L d s => DRet rv L (F d) s2
  | DRetNoSave rv L d s => DRetNoSave rv L (F d) s2
  end.
Definition FLB (B V : Z) : dst -> dst := fun x => setLB x B V.

(* [comment removed for export] *)
Ltac lbfin :=
  repeat first
    [ reflexivity
    | progress (autorewrite with lb)
    | match goal with |- context [if ?c then _ else _] => destruct c end
    | match goal with |- context [match ?p with pair _ _ => _ end] => destruct p end ].

Lemma lb_mtf_val_start : forall s lbl1 L d s2 B V,
  mtf_val_start lbl1 L (setLB d B V) s2 = dres_map2 (FLB B V) s2 (mtf_val_start lbl1 L d s).
Proof. intros. unfold mtf_val_start, FLB. lbfin. Qed.
Lemma lb_coding_check : forall s L d s2 B V,
  coding_check L (setLB d B V) s2 = dres_map2 (FLB B V) s2 (coding_check L d s).
Proof. intros. unfold coding_check, FLB. lbfin. Qed.
Lemma map2_outer_S : forall n i L d s, map2_outer (S n) i L d s =
  (if 16 <=? i then
     let d1 := makeMaps_d d in let L1 := sv_set_i L i in
     if d_nInUse d1 =? 0 then DRet BZ_DATA_ERROR L1 d1 s else DGo 30 (sv_set_alphaSize L1 (d_nInUse d1 + 2)) d1 s
   else if negb (zget (d_inUse16 d) i =? 0) then DGo 29 (sv_set_j (sv_set_i L i) 0) d s
   else map2_outer n (i + 1) L d s).
Proof. reflexivity. Qed.
Lemma lb_map2_outer : forall s n i L d s2 B V,
  map2_outer n i L (setLB d B V) s2 = dres_map2 (FLB B V) s2 (map2_outer n i L d s).
Proof.
  intros s n. induction n as [|n IH]; intros i L d s2 B V; [reflexivity|]. rewrite !map2_outer_S.
  unfold FLB in *. destruct (16 <=? i).
  - rewrite lb_makeMaps_d, lbg_nInUse. destruct (d_nInUse (makeMaps_d d) =? 0); reflexivity.
  - rewrite lbg_inUse16. destruct (negb (zget (d_inUse16 d) i =? 0)); [reflexivity| apply IH].
Qed.
Lemma lb_after_tables : forall s L d s2 B V,
  after_tables L (setLB d B V) s2 = dres_map2 (FLB B V) s2 (after_tables L d s).
Proof. intros. unfold after_tables. autorewrite with lb. apply lb_mtf_val_start. Qed.

Ltac lbfin2 s :=
  repeat first
    [ reflexivity
    | progress (autorewrite with lb)
    | rewrite (lb_mtf_val_start s)
    | rewrite (lb_coding_check s)
    | rewrite (lb_map2_outer s)
    | rewrite (lb_after_tables s)
    | match goal with |- context [if ?c then _ else _] => destruct c end
    | match goal with |- context [match ?p with pair _ _ => _ end] => destruct p end ].

Definition mtf_lbl (lbl : Z) : bool := (36 <=? lbl) && (lbl <=? 41).

(* [comment removed for export] *)
Lemma gb_after_LB : forall lbl v L d s s2 B V, mtf_lbl lbl = false ->
  gb_after lbl v L (setLB d B V) s2 = dres_map2 (FLB B V) s2 (gb_after lbl v L d s).
Proof.
  intros lbl v L d s s2 B V Hl. unfold gb_after, FLB. remember BZ_MAX_SELECTORS as MX eqn:HMX. clear HMX.
  remember (Z.to_nat (lbl - 10)) as m eqn:Hm.
  assert (CS : (m <= 25)%nat \/ (32 <= m)%nat).
  { unfold mtf_lbl in Hl. destruct (Z.leb_spec 36 lbl), (Z.leb_spec lbl 41); cbn in Hl; try discriminate; lia. }
  clear Hm Hl.
  do 26 (destruct m as [|m]; cbv beta iota; [lbfin2 s; fail|]).
  do 6 (destruct m as [|m]; [exfalso; lia|]).
  do 9 (destruct m as [|m]; cbv beta iota; [lbfin2 s; fail|]).
  cbv beta iota. lbfin2 s.
Qed.
End BzR5cLB.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint wbits (ws : list (Z * Z)) : bits :=
  match ws with [] => bnil | (n, v) :: ws' => bapp (Bits n v) (wbits ws') end.
Definition wlegal (ws : list (Z * Z)) : Prop := Forall (fun nv => 1 <= fst nv <= 24 /\ 0 <= snd nv < 2 ^ fst nv) ws.

Lemma wbits_ok : forall ws, wlegal ws -> bits_ok (wbits ws).
Proof.
  induction ws as [|[n v] ws IH]; intros W.
  - unfold bits_ok, bnil; cbn. lia.
  - apply Forall_cons_iff in W as [[W1 W2] W3]. cbn [wbits]. apply bapp_ok; [| apply IH; exact W3].
    unfold bits_ok; cbn [b_len b_val fst snd] in *. lia.
Qed.
Lemma wbits_len : forall ws, wlegal ws -> 0 <= b_len (wbits ws).
Proof. intros ws W. exact (proj1 (wbits_ok ws W)). Qed.
Lemma wlegal_app : forall ws1 ws2, wlegal (ws1 ++ ws2) <-> wlegal ws1 /\ wlegal ws2.
Proof. intros. unfold wlegal. apply Forall_app. Qed.
Lemma wlegal_cons : forall n v ws, wlegal ((n, v) :: ws) <-> (1 <= n <= 24 /\ 0 <= v < 2 ^ n) /\ wlegal ws.
Proof. intros. unfold wlegal. rewrite Forall_cons_iff. cbn [fst snd]. tauto. Qed.
Lemma wlegal_nil : wlegal [].
Proof. constructor. Qed.
Lemma wbits_app : forall ws1 ws2, wlegal ws1 -> wlegal ws2 -> wbits (ws1 ++ ws2) = bapp (wbits ws1) (wbits ws2).
Proof.
  induction ws1 as [|[n v] ws1 IH]; intros ws2 W1 W2; cbn [wbits app].
  - symmetry. apply bapp_bnil_l.
  - apply Forall_cons_iff in W1 as [[A1 A2] W1]. cbn [fst snd] in *. rewrite IH by assumption.
    symmetry. apply bapp_assoc; apply wbits_len; assumption.
Qed.
Lemma wbits_cons : forall n v ws, wbits ((n, v) :: ws) = bapp (Bits n v) (wbits ws).
Proof. reflexivity. Qed.
Lemma bapp_bnil_r : forall x, bapp x bnil = x.
Proof. intros [l v]; unfold bapp, bnil; cbn [b_len b_val]. change (2 ^ 0) with 1. f_equal; lia. Qed.
Lemma wlegal_repeat : forall n v k, 1 <= n <= 24 -> 0 <= v < 2 ^ n -> wlegal (repeat (n, v) k).
Proof. intros n v k Hn Hv. unfold wlegal. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. cbn. lia. Qed.

(* [comment removed for export] *)
Fixpoint wlen (ws : list (Z * Z)) : Z := match ws with [] => 0 | (n, _) :: ws' => n + wlen ws' end.
Lemma wbits_blen : forall ws, b_len (wbits ws) = wlen ws.
Proof. induction ws as [|[n v] ws IH]; cbn [wbits wlen]; [reflexivity|]. unfold bapp; cbn [b_len]. rewrite <- IH. reflexivity. Qed.
Lemma wlen_app : forall ws1 ws2, wlen (ws1 ++ ws2) = wlen ws1 + wlen ws2.
Proof. induction ws1 as [|[n v] ws1 IH]; intros; cbn [wlen app]; [lia|]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
Lemma wbits_split2 : forall n m v, 0 <= n -> 0 <= m -> 0 <= v < 2 ^ (n + m) ->
  wbits [(n + m, v)] = wbits [(n, v / 2 ^ m); (m, v mod 2 ^ m)].
Proof.
  intros n m v Hn Hm Hv. cbn [wbits]. rewrite !bapp_bnil_r. unfold bapp; cbn [b_len b_val]. f_equal.
  pose proof (Z.div_mod v (2 ^ m) ltac:(apply Z.pow_nonzero; lia)). lia.
Qed.
Lemma wbits_24_bytes : forall v, 0 <= v < 2 ^ 24 ->
  wbits [(24, v)] = wbits [(8, v / 65536); (8, (v / 256) mod 256); (8, v mod 256)].
Proof.
  intros v Hv. change 24 with (16 + 8) at 1.
  rewrite (wbits_split2 16 8 v) by (try lia; exact Hv). change (2 ^ 8) with 256.
  assert (E : wbits [(16, v / 256)] = wbits [(8, v / 65536); (8, (v / 256) mod 256)]).
  { change 16 with (8 + 8). rewrite (wbits_split2 8 8 (v / 256)); try lia.
    - change (2 ^ 8) with 256. rewrite Z.div_div by lia. reflexivity.
    - change (2 ^ (8 + 8)) with 65536. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia|]]. change (2 ^ 24) with 16777216 in Hv. lia. }
  change [(8, v / 65536); (8, (v / 256) mod 256); (8, v mod 256)] with ([(8, v / 65536); (8, (v / 256) mod 256)] ++ [(8, v mod 256)]).
  rewrite wbits_app.
  - rewrite <- E. cbn [wbits]. rewrite !bapp_bnil_r. reflexivity.
  - apply wlegal_cons. split; [| apply wlegal_cons; split; [| apply wlegal_nil]].
    + split; [lia|]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia|]]. change (2 ^ 24) with 16777216 in Hv. change (2 ^ 8) with 256. lia.
    + split; [lia|]. change (2 ^ 8) with 256. apply Z.mod_pos_bound. lia.
  - apply wlegal_cons. split; [| apply wlegal_nil]. split; [lia|]. change (2 ^ 8) with 256. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Definition ws_u32 (u : Z) : list (Z * Z) :=
  [(8, Z.land (Z.shiftr u 24) 255); (8, Z.land (Z.shiftr u 16) 255); (8, Z.land (Z.shiftr u 8) 255); (8, Z.land u 255)].
Lemma land255 : forall x, 0 <= Z.land x 255 < 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change 256 with (2 ^ 8). apply Z.mod_pos_bound. lia. Qed.
Lemma ws_u32_legal : forall u, wlegal (ws_u32 u).
Proof.
  intros u. unfold ws_u32. change (2 ^ 8) with 256.
  repeat (apply wlegal_cons; split; [split; [lia| change (2 ^ 8) with 256; apply land255]|]). apply wlegal_nil.
Qed.


Lemma u32_push : forall x v, 0 <= x -> 0 <= v < 256 -> u32 (Z.lor (Z.shiftl x 8) v) = (x * 256 + v) mod 4294967296.
Proof.
  intros x v Hx Hv. unfold u32. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (lor_disjoint (x * 256) v 8); [reflexivity| lia| lia| change (2 ^ 8) with 256; apply Z.mod_mul; lia| change (2 ^ 8) with 256; lia].
Qed.
Lemma lor8 : forall x v, 0 <= x -> 0 <= v < 256 -> Z.lor (Z.shiftl x 8) v = x * 256 + v.
Proof.
  intros x v Hx Hv. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  apply (lor_disjoint (x * 256) v 8); [lia| lia| change (2 ^ 8) with 256; apply Z.mod_mul; lia| change (2 ^ 8) with 256; lia].
Qed.
(* [comment removed for export] *)
Lemma u32_bytes : forall u, 0 <= u < 4294967296 ->
  Z.land (Z.shiftr u 24) 255 = u / 16777216 /\ Z.land (Z.shiftr u 16) 255 = (u / 65536) mod 256 /\
  Z.land (Z.shiftr u 8) 255 = (u / 256) mod 256 /\ Z.land u 255 = u mod 256.
Proof.
  intros u Hu. change 255 with (Z.ones 8). rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256. change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536.
  repeat split; try reflexivity. apply Z.mod_small. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma u32_reassemble : forall u, 0 <= u < 4294967296 ->
  ((u / 16777216 * 256 + (u / 65536) mod 256) * 256 + (u / 256) mod 256) * 256 + u mod 256 = u.
Proof.
  intros u Hu.
  pose proof (Z.div_mod u 256 ltac:(lia)). pose proof (Z.div_mod (u / 256) 256 ltac:(lia)). pose proof (Z.div_mod (u / 65536) 256 ltac:(lia)).
  rewrite (Z.div_div u 256 256) in * by lia. change (256 * 256) with 65536 in *.
  rewrite (Z.div_div u 65536 256) in * by lia. change (65536 * 256) with 16777216 in *. lia.
Qed.
Lemma u24_reassemble : forall u, 0 <= u < 16777216 -> (u / 65536 * 256 + (u / 256) mod 256) * 256 + u mod 256 = u.
Proof.
  intros u Hu.
  pose proof (Z.div_mod u 256 ltac:(lia)). pose proof (Z.div_mod (u / 256) 256 ltac:(lia)).
  rewrite (Z.div_div u 256 256) in * by lia. change (256 * 256) with 65536 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma crc_assemble : forall c, 0 <= c < 4294967296 ->
  u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl 0 8) (c / 16777216))) 8) ((c / 65536) mod 256))) 8)
     ((c / 256) mod 256))) 8) (c mod 256)) = c.
Proof.
  intros c Hc.
  assert (R1 : 0 <= c / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.mod_pos_bound (c / 65536) 256 ltac:(lia)) as R2. pose proof (Z.mod_pos_bound (c / 256) 256 ltac:(lia)) as R3.
  pose proof (Z.mod_pos_bound c 256 ltac:(lia)) as R4.
  pose proof (u32_reassemble c Hc) as RA.
  rewrite (u32_push 0) by lia. rewrite (Z.mod_small (0 * 256 + _)) by lia.
  rewrite (u32_push (0 * 256 + c / 16777216)) by lia. rewrite (Z.mod_small (_ * 256 + _)) by lia.
  rewrite (u32_push ((0 * 256 + c / 16777216) * 256 + (c / 65536) mod 256)) by lia. rewrite (Z.mod_small (_ * 256 + _)) by lia.
  rewrite (u32_push (((0 * 256 + c / 16777216) * 256 + (c / 65536) mod 256) * 256 + (c / 256) mod 256)) by lia.
  rewrite (Z.mod_small (_ * 256 + _)) by lia. lia.
Qed.
Lemma op_assemble : forall op, 0 <= op < 16777216 ->
  Z.lor (Z.shiftl (Z.lor (Z.shiftl (Z.lor (Z.shiftl 0 8) (op / 65536)) 8) ((op / 256) mod 256)) 8) (op mod 256) = op.
Proof.
  intros op Hop.
  assert (R1 : 0 <= op / 65536 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.mod_pos_bound (op / 256) 256 ltac:(lia)) as R3. pose proof (Z.mod_pos_bound op 256 ltac:(lia)) as R4.
  pose proof (u24_reassemble op Hop).
  rewrite (lor8 0) by lia. rewrite (lor8 (0 * 256 + op / 65536)) by lia. rewrite (lor8 ((0 * 256 + op / 65536) * 256 + (op / 256) mod 256)) by lia. lia.
Qed.
