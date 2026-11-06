(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition BZ_OK : Z := 0.
Definition BZ_STREAM_END : Z := 4.
Definition BZ_SEQUENCE_ERROR : Z := -1.
(* [comment removed for export] *)
Definition BZ_MEM_ERROR : Z := -3.
Definition BZ_DATA_ERROR : Z := -4.
Definition BZ_DATA_ERROR_MAGIC : Z := -5.
Definition BZ_UNEXPECTED_EOF : Z := -7.
Definition BZ_OUTBUFF_FULL : Z := -8.
(* [comment removed for export] *)
Definition BZ_X_IDLE : Z := 1.
Definition BZ_X_OUTPUT : Z := 2.
Definition BZ_X_MAGIC_1 : Z := 10.
Definition BZ_X_BLKHDR_1 : Z := 14.
(* [comment removed for export] *)
Definition BZ_RUNA : Z := 0.
Definition BZ_RUNB : Z := 1.
Definition BZ_N_GROUPS : Z := 6.
Definition BZ_G_SIZE : Z := 50.
Definition BZ_MAX_ALPHA_SIZE : Z := 258.
Definition BZ_MAX_SELECTORS : Z := 18002.
Definition MTFA_SIZE : Z := 4096.
Definition MTFL_SIZE : Z := 16.

(* [comment removed for export] *)
Record dsv := DSV {
  sv_i : Z;
  sv_j : Z;
  sv_t : Z;
  sv_alphaSize : Z;
  sv_nGroups : Z;
  sv_nSelectors : Z;
  sv_EOB : Z;
  sv_groupNo : Z;
  sv_groupPos : Z;
  sv_nextSym : Z;
  sv_nblockMAX : Z;
  sv_nblock : Z;
  sv_es : Z;
  sv_N : Z;
  sv_curr : Z;
  sv_zt : Z;
  sv_zn : Z;
  sv_zvec : Z;
  sv_zj : Z;
  sv_gSel : Z;
  sv_gMinlen : Z;
  sv_gPtr : bool
}.
Definition sv_set_i (r : dsv) (v : Z) : dsv :=
  DSV v (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_j (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) v (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_t (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) v (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_alphaSize (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) v (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_nGroups (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) v (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_nSelectors (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) v (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_EOB (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) v (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_groupNo (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) v (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_groupPos (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) v (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_nextSym (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) v (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_nblockMAX (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) v (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_nblock (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) v (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_es (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) v (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_N (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) v (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_curr (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) v (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_zt (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) v (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_zn (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) v (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_zvec (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) v (sv_zj r) (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_zj (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) v (sv_gSel r) (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_gSel (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) v (sv_gMinlen r) (sv_gPtr r).
Definition sv_set_gMinlen (r : dsv) (v : Z) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) v (sv_gPtr r).
Definition sv_set_gPtr (r : dsv) (v : bool) : dsv :=
  DSV (sv_i r) (sv_j r) (sv_t r) (sv_alphaSize r) (sv_nGroups r) (sv_nSelectors r) (sv_EOB r) (sv_groupNo r) (sv_groupPos r) (sv_nextSym r) (sv_nblockMAX r) (sv_nblock r) (sv_es r) (sv_N r) (sv_curr r) (sv_zt r) (sv_zn r) (sv_zvec r) (sv_zj r) (sv_gSel r) (sv_gMinlen r) v.

(* [comment removed for export] *)
Definition dsv_zero : dsv := DSV 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 false.

(* [comment removed for export] *)
Record dst := DST {
  d_state : Z;
  d_out_ch : Z;
  d_out_len : Z;
  d_rand : Z;
  d_rNToGo : Z;
  d_rTPos : Z;
  d_bsBuff : Z;
  d_bsLive : Z;
  d_bs100k : Z;
  d_small : Z;
  d_blockNo : Z;
  d_verb : Z;
  d_origPtr : Z;
  d_tPos : Z;
  d_k0 : Z;
  d_unzftab : zarr;
  d_nused : Z;
  d_cftab : zarr;
  d_cftabCopy : zarr;
  d_tt : zarr;
  d_ll16 : zarr;
  d_ll4 : zarr;
  d_tt_al : bool;
  d_ll_al : bool;
  d_sbcrc : Z;
  d_sccrc : Z;
  d_cbcrc : Z;
  d_cccrc : Z;
  d_nInUse : Z;
  d_inUse : zarr;
  d_inUse16 : zarr;
  d_s2u : zarr;
  d_mtfa : zarr;
  d_mtfbase : zarr;
  d_sel : zarr;
  d_selMtf : zarr;
  d_len : zarr;
  d_limit : zarr;
  d_base : zarr;
  d_perm : zarr;
  d_minLens : zarr;
  d_sv : dsv
}.
Definition d_set_state (r : dst) (v : Z) : dst :=
  DST v (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_out_ch (r : dst) (v : Z) : dst :=
  DST (d_state r) v (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_out_len (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) v (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_rand (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) v (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_rNToGo (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) v (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_rTPos (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) v (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_bsBuff (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) v (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_bsLive (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) v (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_bs100k (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) v (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_small (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) v (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_blockNo (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) v (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_verb (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) v (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_origPtr (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) v (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_tPos (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) v (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_k0 (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) v (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_unzftab (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) v (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_nused (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) v (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_cftab (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) v (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_cftabCopy (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) v (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_tt (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) v (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_ll16 (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) v (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_ll4 (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) v (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_tt_al (r : dst) (v : bool) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) v (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_ll_al (r : dst) (v : bool) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) v (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_sbcrc (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) v (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_sccrc (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) v (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_cbcrc (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) v (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_cccrc (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) v (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_nInUse (r : dst) (v : Z) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) v (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_inUse (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) v (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_inUse16 (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) v (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_s2u (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) v (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_mtfa (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) v (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_mtfbase (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) v (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_sel (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) v (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_selMtf (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) v (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_len (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) v (d_limit r) (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_limit (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) v (d_base r) (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_base (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) v (d_perm r) (d_minLens r) (d_sv r).
Definition d_set_perm (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) v (d_minLens r) (d_sv r).
Definition d_set_minLens (r : dst) (v : zarr) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) v (d_sv r).
Definition d_set_sv (r : dst) (v : dsv) : dst :=
  DST (d_state r) (d_out_ch r) (d_out_len r) (d_rand r) (d_rNToGo r) (d_rTPos r) (d_bsBuff r) (d_bsLive r) (d_bs100k r) (d_small r) (d_blockNo r) (d_verb r) (d_origPtr r) (d_tPos r) (d_k0 r) (d_unzftab r) (d_nused r) (d_cftab r) (d_cftabCopy r) (d_tt r) (d_ll16 r) (d_ll4 r) (d_tt_al r) (d_ll_al r) (d_sbcrc r) (d_sccrc r) (d_cbcrc r) (d_cccrc r) (d_nInUse r) (d_inUse r) (d_inUse16 r) (d_s2u r) (d_mtfa r) (d_mtfbase r) (d_sel r) (d_selMtf r) (d_len r) (d_limit r) (d_base r) (d_perm r) (d_minLens r) v.

(* [comment removed for export] *)
Record dstrm := DSTRM {
  s_in : list Z;
  s_out : list Z;
  s_avail_out : Z;
  s_tin : Z;
  s_tout : Z
}.
Definition s_set_in (r : dstrm) (v : list Z) : dstrm :=
  DSTRM v (s_out r) (s_avail_out r) (s_tin r) (s_tout r).
Definition s_set_out (r : dstrm) (v : list Z) : dstrm :=
  DSTRM (s_in r) v (s_avail_out r) (s_tin r) (s_tout r).
Definition s_set_avail_out (r : dstrm) (v : Z) : dstrm :=
  DSTRM (s_in r) (s_out r) v (s_tin r) (s_tout r).
Definition s_set_tin (r : dstrm) (v : Z) : dstrm :=
  DSTRM (s_in r) (s_out r) (s_avail_out r) v (s_tout r).
Definition s_set_tout (r : dstrm) (v : Z) : dstrm :=
  DSTRM (s_in r) (s_out r) (s_avail_out r) (s_tin r) v.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition s_output (s : dstrm) : list Z := rev (s_out s).

(* [comment removed for export] *)
Definition dst_init (junk : dst) (verbosity small : Z) : dst :=
  d_set_verb (d_set_blockNo (d_set_ll_al (d_set_tt_al (d_set_small
   (d_set_cccrc (d_set_bsBuff (d_set_bsLive (d_set_state junk BZ_X_MAGIC_1) 0) 0) 0) small) false) false) 0) verbosity.
Definition dstrm_init (input : list Z) (avail_out : Z) : dstrm := DSTRM input [] avail_out 0 0.
