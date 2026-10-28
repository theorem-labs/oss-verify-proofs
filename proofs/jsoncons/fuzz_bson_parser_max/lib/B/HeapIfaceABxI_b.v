(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HAJI.
Import HAJ.
(* [comment removed for export] *)
Definition lib_ext_ok (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (scfg : SpuriousCfg) (HI : asan_iface)
           (E : ext_consts) : Prop :=
  exists HIR, HI = strict_of HIR /\ asan_iface_okR L ar C scfg HIR /\ aicpt_ok L ar IL scfg HIR /\ asan_ext_ok L ar scfg HIR E.

End HAJI.
