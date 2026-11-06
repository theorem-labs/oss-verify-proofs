(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState ApErr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SZ_ASN1_STRING : Z := 24.     (* [comment removed for export] *)
Definition SZ_STACK : Z := 56.           (* [comment removed for export] *)
Definition SZ_SCT : Z := 104.            (* [comment removed for export] *)
Definition SZ_BIO : Z := 128.            (* [comment removed for export] *)
Definition CT_V1_HASHLEN : Z := 32.      (* [comment removed for export] *)
Definition SZ_GEN_DATA : Z := 20.        (* [comment removed for export] *)
Definition SZ_GENSTR : Z := 19.          (* [comment removed for export] *)
Definition SK_MIN_NODES : Z := 4.
Definition MAX_SCT_SIZE : Z := 65535.
Definition MAX_SCT_LIST_SIZE : Z := 65535.
Definition V_ASN1_OCTET_STRING : Z := 4.
Definition V_ASN1_GENERALIZEDTIME : Z := 24.

(* [comment removed for export] *)
Definition NID_undef : Z := 0.
Definition NID_sha256WithRSAEncryption : Z := 668.
Definition NID_ecdsa_with_SHA256 : Z := 794.
Definition sig_nid (version hash_alg sig_alg : Z) : Z :=
  if (version =? 0) && (hash_alg =? 4) then
    (if sig_alg =? 3 then NID_ecdsa_with_SHA256 else if sig_alg =? 1 then NID_sha256WithRSAEncryption else NID_undef)
  else NID_undef.
(* [comment removed for export] *)
Definition nid_ln_len (nid : Z) : Z := if nid =? NID_ecdsa_with_SHA256 then 17 else if nid =? NID_sha256WithRSAEncryption then 23 else 0.

(* [comment removed for export] *)
Definition ERR_LIB_CT : Z := 50.
Definition ERR_R_NESTED_ASN1_ERROR : Z := 524554.
(* [comment removed for export] *)
Definition RS_td_small        : rsite := mkRS 23 20 212  (ERR_PACK ERR_LIB_ASN1 224).     (* [comment removed for export] *)
Definition RS_prim_nested     : rsite := mkRS 23 22 779  (ERR_PACK ERR_LIB_ASN1 ERR_R_NESTED_ASN1_ERROR).
Definition RS_coll_unexp_eoc  : rsite := mkRS 23 13 1107 (ERR_PACK ERR_LIB_ASN1 159).
Definition RS_coll_nested     : rsite := mkRS 23 13 1116 (ERR_PACK ERR_LIB_ASN1 ERR_R_NESTED_ASN1_ERROR).
Definition RS_coll_nest_str   : rsite := mkRS 23 13 1123 (ERR_PACK ERR_LIB_ASN1 197).
Definition RS_coll_miss_eoc   : rsite := mkRS 23 13 1133 (ERR_PACK ERR_LIB_ASN1 137).
Definition RS_tlen_bad_hdr    : rsite := mkRS 23 16 1226 (ERR_PACK ERR_LIB_ASN1 102).
Definition RS_tlen_wrong_tag  : rsite := mkRS 23 16 1236 (ERR_PACK ERR_LIB_ASN1 168).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RS_list_len        : rsite := mkRS 19 13 262 (ERR_PACK ERR_LIB_CT 105).
Definition RS_list_mismatch   : rsite := mkRS 19 13 268 (ERR_PACK ERR_LIB_CT 105).
Definition RS_list_lt2        : rsite := mkRS 19 13 289 (ERR_PACK ERR_LIB_CT 105).
Definition RS_list_sctlen     : rsite := mkRS 19 13 296 (ERR_PACK ERR_LIB_CT 105).
Definition RS_sct_len         : rsite := mkRS 19 8 76   (ERR_PACK ERR_LIB_CT 104).     (* [comment removed for export] *)
Definition RS_sct_43          : rsite := mkRS 19 8 99   (ERR_PACK ERR_LIB_CT 104).
Definition RS_sct_ext         : rsite := mkRS 19 8 114  (ERR_PACK ERR_LIB_CT 104).
Definition RS_sct_sig         : rsite := mkRS 19 8 128  (ERR_PACK ERR_LIB_CT 104).
Definition RS_sig_version     : rsite := mkRS 19 18 31  (ERR_PACK ERR_LIB_CT 103).     (* [comment removed for export] *)
Definition RS_sig_len4        : rsite := mkRS 19 18 42  (ERR_PACK ERR_LIB_CT 107).
Definition RS_sig_nid         : rsite := mkRS 19 18 51  (ERR_PACK ERR_LIB_CT 107).
Definition RS_sig_overrun     : rsite := mkRS 19 18 58  (ERR_PACK ERR_LIB_CT 107).
Definition RS_i2o_notset      : rsite := mkRS 19 8 204  (ERR_PACK ERR_LIB_CT 106).
Definition RS_i2o_list        : rsite := mkRS 19 13 328 (ERR_PACK ERR_LIB_CT 105).
Definition RS_i2o_siginc      : rsite := mkRS 19 18 159 (ERR_PACK ERR_LIB_CT 107).     (* [comment removed for export] *)
