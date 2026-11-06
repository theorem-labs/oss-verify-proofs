(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition UA_ycb_null  (sp : word) : Prop := True.
Definition UA_ycb_boolean  (sp : word) : Prop := True.
Definition UA_ycb_string  (sp : word) : Prop := True.
Definition UA_ycb_number (l : Z) (sp : word) : Prop := True.
Definition UA_ycb_start_map (CX : Z) (cx : yctx) (sp : word) : Prop := 0 < CX /\ CX mod 4 = 0.
Definition UA_ycb_map_key (CX : Z) (cx : yctx) (sp : word) : Prop := 0 < CX /\ CX mod 4 = 0.
Definition UA_ycb_end_map (CX : Z) (cx : yctx) (sp : word) : Prop := 0 < CX /\ CX mod 4 = 0.
Definition UA_ycb_start_array (CX : Z) (cx : yctx) (sp : word) : Prop := 0 < CX /\ CX mod 4 = 0.
Definition UA_ycb_end_array (CX : Z) (cx : yctx) (sp : word) : Prop := 0 < CX /\ CX mod 4 = 0.
Definition UA_ybuf_err (B st lo : Z) (rest : list cell) (sp : word) : Prop := 0 < B /\ B mod 8 = 0.
Definition UA_ybuf_len (B D AF lo : Z) (b : ybuf) (sp : word) : Prop := 0 < B /\ B mod 8 = 0.
Definition UA_ybuf_data (B D AF lo : Z) (b : ybuf) (sp : word) : Prop := 0 < B /\ B mod 8 = 0.
Definition UA_ybuf_clear (B D AF lo : Z) (b : ybuf) (sp : word) : Prop := 0 < B /\ B mod 8 = 0.
Definition UA_ybs_set (h : yhandle) (mh : mhand) (s s' : ystate) (rest : list ystate) (lo : Z) (sp : word) : Prop := 0 < mh_addr mh /\ mh_addr mh mod 8 = 0 /\ 0 < mh_stack mh.
Definition UA_yhexToDigit (VP S v lo : Z) (h0 h1 h2 h3 : Z) (v' : Z) (sp : word) : Prop := VP mod 4 = 0 /\ 0 < S /\ S + 4 < 2^64.
Definition UA_yset_default (YAF : Z) (junk : list byte) (sp : word) : Prop := 0 < YAF /\ YAF mod 8 = 0.
Definition UA_ylex_realloc (L AF lo : Z) (lx : ylexer) (mbl : mbuf) (sp : word) : Prop := 0 < L /\ L mod 8 = 0 /\ 0 < mb_addr mbl /\ mb_addr mbl mod 8 = 0.
Definition UA_yreset_parser (h : yhandle) (mh : mhand) (lo : Z) (sp : word) : Prop := 0 < mh_addr mh /\ mh_addr mh mod 8 = 0 /\ 0 < mh_lexer mh /\ mh_lexer mh mod 8 = 0 /\ 0 < mb_addr (mh_lexbuf mh) /\ mb_addr (mh_lexbuf mh) mod 8 = 0.
Definition UA_ybuf_alloc (REST : list block) (AF lo B : Z) (errv : word) (sp : word) : Prop := 0 < AF /\ AF mod 8 = 0.
Definition UA_ybuf_free (REST : list block) (mb : mbuf) (b : ybuf) (AF lo B : Z) (errv : word) (sp : word) : Prop := 0 < mb_addr mb /\ mb_addr mb mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0.
Definition UA_ybuf_append (REST : list block) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo B : Z) (errv : word) (sp : word) : Prop := 0 < mb_addr mb /\ mb_addr mb mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0 /\ 0 < S.
Definition UA_ylex_alloc (REST : list block) (AF aC v8 lo B : Z) (errv : word) (sp : word) : Prop := 0 < AF /\ AF mod 8 = 0.
Definition UA_ylex_free (REST : list block) (lid : bptr) (L AF : Z) (mbl : mbuf) (lx : ylexer) (lo B : Z) (errv : word) (sp : word) : Prop := 0 < L /\ L mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0 /\ 0 < mb_addr mbl /\ mb_addr mbl mod 8 = 0.
Definition UA_ylex_lex (REST : list block) (h : yhandle) (mh : mhand) (T : Z) (txt : list Z) (off OBP OLP : Z) (obw olw : word) (lo B : Z) (errv : word) (sp : word) : Prop := OBP mod 8 = 0 /\ OLP mod 4 = 0.
Definition UA_ystring_decode (REST : list block) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n lo B : Z) (errv : word) (sp : word) : Prop := 0 < mb_addr mbd /\ mb_addr mbd mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0 /\ bv_unsigned sp mod 16 = 0.
Definition UA_ydo_parse (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (lo B : Z) (errv : word) (sp : word) : Prop := bv_unsigned sp mod 16 = 0 /\ mh_ctx mh mod 4 = 0.
Definition UA_yparse (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (lo B : Z) (errv : word) (sp : word) : Prop := bv_unsigned sp mod 16 = 0 /\ mh_ctx mh mod 4 = 0.
Definition UA_yalloc (REST : list block) (CFGP CX lo B : Z) (errv : word) (sp : word) : Prop := bv_unsigned sp mod 16 = 0 /\ CFGP mod 4 = 0.
Definition UA_yfree (REST : list block) (h : yhandle) (mh : mhand) (lo B : Z) (errv : word) (sp : word) : Prop := 0 < mh_addr mh /\ mh_addr mh mod 8 = 0 /\ 0 < mh_lexer mh /\ mh_lexer mh mod 8 = 0 /\ 0 < mb_addr (mh_lexbuf mh) /\ mb_addr (mh_lexbuf mh) mod 8 = 0 /\ 0 < mb_addr (mh_decbuf mh) /\ mb_addr (mh_decbuf mh) mod 8 = 0.
Definition UA_yfuzz (REST : list block) (T : Z) (txt : list Z) (lo B : Z) (errv : word) (sp : word) : Prop := bv_unsigned sp mod 16 = 0.
End RC__1.
