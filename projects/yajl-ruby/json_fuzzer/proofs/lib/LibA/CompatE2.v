(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel ImplRzA NodesA_mm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition srzA_evt segs := rzA_evt_cfg segs acfg.
Definition srzA_evt_disjoint segs := rzA_evt_disjoint_cfg segs acfg.
#[warnings="-notation-for-abbreviation"] Notation srzA_seg := rzA_seg_cfg (only parsing).
#[warnings="-notation-for-abbreviation"] Notation implA_trzA_srealizes := implA_trzA_realizes_cfg (only parsing).
#[warnings="-notation-for-abbreviation"] Notation srzA_enode := rzA_enode_cfg (only parsing).
