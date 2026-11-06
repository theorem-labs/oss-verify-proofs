(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TBL_bom : Z := 0xad760.
Definition tbl_bom : list mentry :=
  [ ME 0x23b60 [Z_to_bv 8 235; Z_to_bv 8 187; Z_to_bv 8 191] 0xa8e20 0x22e00;
    ME 0 [] 0xa8e40 0x22e40 ].
Lemma tbl_bom_wf : mtab_wf tbl_bom.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_bom_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_bom.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition TBL_attr_include : Z := 0xad8a0.
Definition tbl_attr_include : list mentry :=
  [ ME 0x23ce0 [Z_to_bv 8 115; Z_to_bv 8 114; Z_to_bv 8 99; Z_to_bv 8 61] 0xa8fc0 0x23620;
    ME 0x23d00 [Z_to_bv 8 111; Z_to_bv 8 110; Z_to_bv 8 101; Z_to_bv 8 114; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 61] 0xa8fc0 0x23620;
    ME 0 [] 0xa8fe0 0x235a0 ].
Lemma tbl_attr_include_wf : mtab_wf tbl_attr_include.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_attr_include_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_attr_include.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition TBL_esi : Z := 0xad840.
Definition tbl_esi : list mentry :=
  [ ME 0x23c80 [Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 99; Z_to_bv 8 108; Z_to_bv 8 117; Z_to_bv 8 100; Z_to_bv 8 101] 0xa8f40 0x23180;
    ME 0x23ca0 [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 109; Z_to_bv 8 111; Z_to_bv 8 118; Z_to_bv 8 101] 0xa8f60 0x232a0;
    ME 0x23cc0 [Z_to_bv 8 99; Z_to_bv 8 111; Z_to_bv 8 109; Z_to_bv 8 109; Z_to_bv 8 101; Z_to_bv 8 110; Z_to_bv 8 116] 0xa8f80 0x232c0;
    ME 0 [] 0xa8fa0 0x233a0 ].
Lemma tbl_esi_wf : mtab_wf tbl_esi.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_esi_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_esi.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition TBL_starttag : Z := 0xad7a0.
Definition tbl_starttag : list mentry :=
  [ ME 0x23b80 [Z_to_bv 8 33; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 101; Z_to_bv 8 115; Z_to_bv 8 105] 0xa8e60 0x23080;
    ME 0x23ba0 [Z_to_bv 8 33; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 62] 0xa8e80 0x22e60;
    ME 0x23bc0 [Z_to_bv 8 33; Z_to_bv 8 45; Z_to_bv 8 45] 0xa8ea0 0x23020;
    ME 0x23be0 [Z_to_bv 8 47; Z_to_bv 8 101; Z_to_bv 8 115; Z_to_bv 8 105; Z_to_bv 8 58] 0xa8ec0 0x23140;
    ME 0x23c00 [Z_to_bv 8 101; Z_to_bv 8 115; Z_to_bv 8 105; Z_to_bv 8 58] 0xa8ee0 0x23160;
    ME 0x23c20 [Z_to_bv 8 33; Z_to_bv 8 91; Z_to_bv 8 67; Z_to_bv 8 68; Z_to_bv 8 65; Z_to_bv 8 84; Z_to_bv 8 65; Z_to_bv 8 91] 0xa8f00 0x23100;
    ME 0 [] 0xa8f20 0x22fe0 ].
Lemma tbl_starttag_wf : mtab_wf tbl_starttag.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_starttag_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_starttag.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition ST_Start : Z := 0x22e00.  (* [comment removed for export] *)
Definition ST_BOM : Z := 0x22e40.  (* [comment removed for export] *)
Definition ST_NxtTag : Z := 0x22e60.  (* [comment removed for export] *)
Definition ST_NotMyTag : Z := 0x22fe0.  (* [comment removed for export] *)
Definition ST_Comment : Z := 0x23020.  (* [comment removed for export] *)
Definition ST_CommentESI : Z := 0x23080.  (* [comment removed for export] *)
Definition ST_CDATA : Z := 0x23100.  (* [comment removed for export] *)
Definition ST_end_ESITag : Z := 0x23140.  (* [comment removed for export] *)
Definition ST_ESITag : Z := 0x23160.  (* [comment removed for export] *)
Definition ST_ESI_Include : Z := 0x23180.  (* [comment removed for export] *)
Definition ST_ESI_Remove : Z := 0x232a0.  (* [comment removed for export] *)
Definition ST_ESI_Comment : Z := 0x232c0.  (* [comment removed for export] *)
Definition ST_ESI_Bogon : Z := 0x233a0.  (* [comment removed for export] *)
Definition ST_SkipAttribute : Z := 0x235a0.  (* [comment removed for export] *)
Definition ST_AttrGetValue : Z := 0x23620.  (* [comment removed for export] *)
