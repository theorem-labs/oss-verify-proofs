(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutCB.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

#[local] Transparent gp_maps gp_nInUse gp_unseq gp_EOB gp_fin gp_st gp_s0 gp_mtf0 gp_yy0.
Section ACeilS1. Context {BZP : BzParams}.

(* [comment removed for export] *)
Lemma gm_loop_set_arr2 : forall e a', gm_facts e -> agree_below (e_nblock e) (e_arr2 e) a' ->
  forall i, Z.of_nat i <= e_nblock e ->
  gm_loop i a' (gp_unseq e) (e_nblock e) 0 (gp_s0 e) = gp_st e i.
Proof.
  intros e a' GF AG. induction i as [|i IH]; intros Hi.
  - reflexivity.
  - rewrite gm_loop_snoc, gp_st_S, IH by lia. rewrite Z.add_0_l.
    pose proof (gp_st_GI e GF i ltac:(lia)) as G. set (s := gp_st e i) in *. clearbody s.
    cps_destruct G as (W0 & P0 & WP & _ & _ & _ & _ & SAME & _).
    pose proof GF as GF'. cps_destruct GF' as (_ & _ & NB & _ & _ & _ & M1).
    assert (PTR : rd32 (gm_arr1 s) (Z.of_nat i) = rd32 (e_arr1 e) (Z.of_nat i)).
    { unfold rd32. rewrite !SAME by lia. reflexivity. }
    pose proof (M1 (Z.of_nat i) ltac:(lia)) as PR.
    unfold gm_iter. rewrite !PTR.
    set (j0 := rd32 (e_arr1 e) (Z.of_nat i) - 1).
    set (j := if j0 <? 0 then j0 + e_nblock e else j0).
    assert (Hj : 0 <= j < e_nblock e) by (subst j j0; destruct (Z.ltb_spec (rd32 (e_arr1 e) (Z.of_nat i) - 1) 0); lia).
    unfold rd8. rewrite (AG j Hj). reflexivity.
Qed.

Theorem generateMTFValues_set_arr2 : forall e a', gm_facts e -> agree_below (e_nblock e) (e_arr2 e) a' ->
  generateMTFValues (est_set_arr2 e a') znew =
  (est_set_arr2 (fst (generateMTFValues e znew)) a', snd (generateMTFValues e znew)).
Proof.
  intros e a' GF AG.
  rewrite (generateMTFValues_eq e).
  assert (L : generateMTFValues (est_set_arr2 e a') znew =
    (let '(arr1, mtfFreq, wr) := gp_fin e (gm_loop (Z.to_nat (e_nblock e)) a' (gp_unseq e) (e_nblock e) 0 (gp_s0 e)) in
     (EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 a' (e_ftab e) (e_origPtr e)
          (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (gp_nInUse e) (e_inUse e) (gp_unseq e)
          (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) wr mtfFreq (e_selector e) (e_selectorMtf e)
          (e_len e) (e_code e) (e_rfreq e) (e_len_pack e),
      gm_yy (gm_loop (Z.to_nat (e_nblock e)) a' (gp_unseq e) (e_nblock e) 0 (gp_s0 e))))).
  { unfold generateMTFValues, gp_fin, gp_s0, gp_mtf0, gp_yy0, gp_EOB, gp_nInUse, gp_unseq, gp_maps.
    cbn [e_inUse e_unseqToSeq e_mtfFreq e_nblock e_arr2 e_arr1 e_mode e_state e_avail_in_expect e_ftab e_origPtr e_state_in_ch e_state_in_len
         e_state_out_pos e_bw e_blockCRC e_combinedCRC e_blockNo e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_set_arr2].
    destruct (mk_maps 256 (e_inUse e) (e_unseqToSeq e) 0 0) as [unseq nInUse]. cbn [fst snd].
    set (s := gm_loop _ _ _ _ _ _). clearbody s. destruct (if 0 <? gm_zPend s then _ else _) as [[arr1 mf] wr]. cbv beta iota zeta. reflexivity. }
  rewrite L. clear L. rewrite (gm_loop_set_arr2 e a' GF AG) by (cps_pose GF as (_ & _ & NB & _); lia).
  destruct (gp_fin e (gp_st e (Z.to_nat (e_nblock e)))) as [[arr1 mf] wr]. cbv beta iota zeta. cbn [fst snd].
  (* [comment removed for export] *)
  unfold est_set_arr2.
  cbn [e_inUse e_unseqToSeq e_mtfFreq e_nblock e_arr2 e_arr1 e_mode e_state e_avail_in_expect e_ftab e_origPtr e_state_in_ch e_state_in_len
       e_state_out_pos e_bw e_blockCRC e_combinedCRC e_blockNo e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack e_nInUse e_nMTF].
  reflexivity.
Qed.

Corollary generateMTFValues_set_arr2_fst : forall e a', gm_facts e -> agree_below (e_nblock e) (e_arr2 e) a' ->
  fst (generateMTFValues (est_set_arr2 e a') znew) = est_set_arr2 (fst (generateMTFValues e znew)) a'.
Proof. intros e a' GF AG. rewrite (generateMTFValues_set_arr2 e a' GF AG). cbn [fst]. reflexivity. Qed.

Theorem cb_glue_gm_ok : cb_glue_gm.
Proof. exact generateMTFValues_set_arr2_fst. Qed.

End ACeilS1.
