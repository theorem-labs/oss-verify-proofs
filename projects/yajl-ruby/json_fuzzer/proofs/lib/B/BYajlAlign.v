(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BA_aycb_null (P : acc -> Prop) (sp : word) : Prop :=
  True.
Definition BA_aycb_boolean (P : acc -> Prop) (sp : word) : Prop :=
  True.
Definition BA_aycb_string (P : acc -> Prop) (sp : word) : Prop :=
  True.
Definition BA_aycb_number (P : acc -> Prop) (l lo : Z) (sp : word) : Prop :=
  True.
Definition BA_aycb_start_map (P : acc -> Prop) (CX lo : Z) (cx : yctx) (sp : word) : Prop :=
  0 < CX /\ CX mod 4 = 0.
Definition BA_aycb_map_key (P : acc -> Prop) (CX lo : Z) (cx : yctx) (sp : word) : Prop :=
  0 < CX /\ CX mod 4 = 0.
Definition BA_aycb_end_map (P : acc -> Prop) (CX lo : Z) (cx : yctx) (sp : word) : Prop :=
  0 < CX /\ CX mod 4 = 0.
Definition BA_aycb_start_array (P : acc -> Prop) (CX lo : Z) (cx : yctx) (sp : word) : Prop :=
  0 < CX /\ CX mod 4 = 0.
Definition BA_aycb_end_array (P : acc -> Prop) (CX lo : Z) (cx : yctx) (sp : word) : Prop :=
  0 < CX /\ CX mod 4 = 0.
Definition BA_aybuf_err (P : acc -> Prop) (B st lo : Z) (OA On : Z) (sp : word) : Prop :=
  0 < B /\ B mod 8 = 0.
Definition BA_aybuf_len (P : acc -> Prop) (B D AF lo : Z) (b : ybuf) (sp : word) : Prop :=
  0 < B /\ B mod 8 = 0.
Definition BA_aybuf_data (P : acc -> Prop) (B D AF lo : Z) (b : ybuf) (sp : word) : Prop :=
  0 < B /\ B mod 8 = 0.
Definition BA_aybuf_clear (P : acc -> Prop) (B D AF lo : Z) (b : ybuf) (sp : word) : Prop :=
  0 < B /\ B mod 8 = 0.
Definition BA_aybs_set (P : acc -> Prop) (h : yhandle) (mh : mhand) (s s' : ystate) (rest : list ystate) (lo : Z) (sp : word) : Prop :=
  0 < mh_addr mh /\ mh_addr mh mod 8 = 0 /\ 0 < mh_stack mh.
Definition BA_ayhexToDigit (P : acc -> Prop) (VP S v lo : Z) (h0 h1 h2 h3 : Z) (v' : Z) (OA On : Z) (sp : word) : Prop :=
  VP mod 4 = 0 /\ 0 < S /\ S + 4 < 2^64.
Definition BA_ayset_default (P : acc -> Prop) (YAF lo : Z) (junk : list byte) (sp : word) : Prop :=
  0 < YAF /\ YAF mod 8 = 0.
Definition BA_aylex_realloc (P : acc -> Prop) (L AF lo : Z) (lx : ylexer) (mbl : mbuf) (sp : word) : Prop :=
  0 < L /\ L mod 8 = 0 /\ 0 < mb_addr mbl /\ mb_addr mbl mod 8 = 0.
Definition BA_ayreset_parser (P : acc -> Prop) (h : yhandle) (mh : mhand) (lo : Z) (sp : word) : Prop :=
  0 < mh_addr mh /\ mh_addr mh mod 8 = 0 /\ 0 < mh_lexer mh /\ mh_lexer mh mod 8 = 0 /\ 0 < mb_addr (mh_lexbuf mh) /\ mb_addr (mh_lexbuf mh) mod 8 = 0.
Definition BA_aybuf_alloc (LF : list fblock) (REST : list ablock) (AF lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  0 < AF /\ AF mod 8 = 0.
Definition BA_aybuf_free (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  0 < mb_addr mb /\ mb_addr mb mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0.
Definition BA_aybuf_append (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  0 < mb_addr mb /\ mb_addr mb mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0 /\ 0 < S.
Definition BA_aylex_alloc (LF : list fblock) (REST : list ablock) (AF aC v8 lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  0 < AF /\ AF mod 8 = 0.
Definition BA_aylex_free (LF : list fblock) (REST : list ablock) (L AF : Z) (mbl : mbuf) (lx : ylexer) (lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  0 < L /\ L mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0 /\ 0 < mb_addr mbl /\ mb_addr mbl mod 8 = 0.
Definition BA_aylex_lex (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (T : Z) (txt : list Z) (off OBP OLP OT OTn : Z) (obw olw : word) (lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  OBP mod 8 = 0 /\ OLP mod 4 = 0.
Definition BA_aystring_decode (LF : list fblock) (REST : list ablock) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n OT OTn lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  0 < mb_addr mbd /\ mb_addr mbd mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0 /\ bv_unsigned sp mod 16 = 0.
Definition BA_aydo_parse (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  bv_unsigned sp mod 16 = 0 /\ mh_ctx mh mod 4 = 0.
Definition BA_ayparse (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  bv_unsigned sp mod 16 = 0 /\ mh_ctx mh mod 4 = 0.
Definition BA_ayalloc (LF : list fblock) (REST : list ablock) (CFGP CX lo L : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  bv_unsigned sp mod 16 = 0 /\ CFGP mod 4 = 0.
Definition BA_ayfree (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  0 < mh_addr mh /\ mh_addr mh mod 8 = 0 /\ 0 < mh_lexer mh /\ mh_lexer mh mod 8 = 0 /\ 0 < mb_addr (mh_lexbuf mh) /\ mb_addr (mh_lexbuf mh) mod 8 = 0 /\ 0 < mb_addr (mh_decbuf mh) /\ mb_addr (mh_decbuf mh) mod 8 = 0.
Definition BA_ayfuzz (LF : list fblock) (REST : list ablock) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z) (K : TSet) (sp : word) : Prop :=
  bv_unsigned sp mod 16 = 0.
