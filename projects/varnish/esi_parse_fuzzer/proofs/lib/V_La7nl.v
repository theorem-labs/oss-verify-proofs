(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TBL_bom : Z := 0x31820.
Definition tbl_bom : list mentry :=
  [ ME 0x11091 [Z_to_bv 8 235; Z_to_bv 8 187; Z_to_bv 8 191] 0x30618 0x10af1;
    ME 0 [] 0x30620 0x116b4 ].
Lemma tbl_bom_wf : mtab_wf tbl_bom.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_bom_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_bom.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition TBL_attr_include : Z := 0x31840.
Definition tbl_attr_include : list mentry :=
  [ ME 0x11841 [Z_to_bv 8 115; Z_to_bv 8 114; Z_to_bv 8 99; Z_to_bv 8 61] 0x30680 0x10c2f;
    ME 0x102d6 [Z_to_bv 8 111; Z_to_bv 8 110; Z_to_bv 8 101; Z_to_bv 8 114; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 61] 0x30680 0x10c2f;
    ME 0 [] 0x30688 0x116d1 ].
Lemma tbl_attr_include_wf : mtab_wf tbl_attr_include.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_attr_include_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_attr_include.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition TBL_esi : Z := 0x31870.
Definition tbl_esi : list mentry :=
  [ ME 0x11de9 [Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 99; Z_to_bv 8 108; Z_to_bv 8 117; Z_to_bv 8 100; Z_to_bv 8 101] 0x30660 0x116c3;
    ME 0x11b8d [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 109; Z_to_bv 8 111; Z_to_bv 8 118; Z_to_bv 8 101] 0x30668 0x10b4b;
    ME 0x110b0 [Z_to_bv 8 99; Z_to_bv 8 111; Z_to_bv 8 109; Z_to_bv 8 109; Z_to_bv 8 101; Z_to_bv 8 110; Z_to_bv 8 116] 0x30670 0x10c21;
    ME 0 [] 0x30678 0x1148d ].
Lemma tbl_esi_wf : mtab_wf tbl_esi.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_esi_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_esi.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition TBL_starttag : Z := 0x318b0.
Definition tbl_starttag : list mentry :=
  [ ME 0x10d61 [Z_to_bv 8 33; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 101; Z_to_bv 8 115; Z_to_bv 8 105] 0x30628 0x11344;
    ME 0x10b8d [Z_to_bv 8 33; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 62] 0x30630 0x11aa8;
    ME 0x10494 [Z_to_bv 8 33; Z_to_bv 8 45; Z_to_bv 8 45] 0x30638 0x12174;
    ME 0x1205d [Z_to_bv 8 47; Z_to_bv 8 101; Z_to_bv 8 115; Z_to_bv 8 105; Z_to_bv 8 58] 0x30640 0x102cc;
    ME 0x111d1 [Z_to_bv 8 101; Z_to_bv 8 115; Z_to_bv 8 105; Z_to_bv 8 58] 0x30648 0x11c67;
    ME 0x11095 [Z_to_bv 8 33; Z_to_bv 8 91; Z_to_bv 8 67; Z_to_bv 8 68; Z_to_bv 8 65; Z_to_bv 8 84; Z_to_bv 8 65; Z_to_bv 8 91] 0x30650 0x1059a;
    ME 0 [] 0x30658 0x10d46 ].
Lemma tbl_starttag_wf : mtab_wf tbl_starttag.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try (cbv; intuition discriminate). Qed.
Lemma tbl_starttag_strings : forall m, mem_inv rsegs m -> mtab_strings rsegs m tbl_starttag.
Proof. intros m MI. apply mtab_strings_intro; [exact MI | vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition ST_end_ESITag : Z := 0x102cc.  (* [comment removed for export] *)
Definition ST_CDATA : Z := 0x1059a.  (* [comment removed for export] *)
Definition ST_Start : Z := 0x10af1.  (* [comment removed for export] *)
Definition ST_ESI_Remove : Z := 0x10b4b.  (* [comment removed for export] *)
Definition ST_ESI_Comment : Z := 0x10c21.  (* [comment removed for export] *)
Definition ST_AttrGetValue : Z := 0x10c2f.  (* [comment removed for export] *)
Definition ST_NotMyTag : Z := 0x10d46.  (* [comment removed for export] *)
Definition ST_CommentESI : Z := 0x11344.  (* [comment removed for export] *)
Definition ST_ESI_Bogon : Z := 0x1148d.  (* [comment removed for export] *)
Definition ST_BOM : Z := 0x116b4.  (* [comment removed for export] *)
Definition ST_ESI_Include : Z := 0x116c3.  (* [comment removed for export] *)
Definition ST_SkipAttribute : Z := 0x116d1.  (* [comment removed for export] *)
Definition ST_NxtTag : Z := 0x11aa8.  (* [comment removed for export] *)
Definition ST_ESITag : Z := 0x11c67.  (* [comment removed for export] *)
Definition ST_Comment : Z := 0x12174.  (* [comment removed for export] *)
