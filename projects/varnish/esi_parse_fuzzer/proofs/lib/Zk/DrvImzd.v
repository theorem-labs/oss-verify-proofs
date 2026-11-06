(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0 DriverKit InstDefs.

Module Allo10x.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 InstDefs Instjhg InstFree Instffk Instjk7 Inst5lz Inst6mb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope Z_scope.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

#[global] Instance AllocP0 : AllocSpec LayoutP0 := {|
  AS := ias;
  a_live := p0_live;
  ainv := p0_ainv;
  owned := p0_owned;
  a_livebytes := p0_livebytes;   (* [comment removed for export] *)
  a_nlive := p0_nlive;
  as_static_owned := p0_static_owned;
  as_static_where := p0_static_where;
  as_shared_where := p0_shared_where;
  as_shared_not_static := p0_shared_not_static;
  as_errno_where := p0_errno_where;
  as_errno_not_static := p0_errno_not_static;
  as_layout_order := p0_layout_order;
  as_ro_addr_iff := p0_ro_addr_iff;
  as_seg_rom_outside := p0_seg_rom_outside;
  as_find_segment_outside := p0_find_segment_outside;
  as_owned_where := p0_owned_where;
  as_live_ok := p0_live_ok;
  as_live_disjoint := p0_live_disjoint;
  as_lazy_nil := p0_lazy_nil;
  as_budget_nonneg := p0_budget_nonneg;
  as_live_budget := p0_live_budget;
  as_frame := p0_frame;
  as_malloc_cps := p0_malloc_cps;
  as_free_cps := p0_free_cps;
  as_calloc_cps := p0_calloc_cps;
  as_realloc_cps := p0_realloc_cps_top;
  as_realloc_null_cps := fun ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m md A T AI E H =>
      realloc_null_p0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m md T
        (proj2 (p0_lazy_nil A m md AI)) (proj1 (p0_lazy_nil A m md AI)) E H
|}.

End CEIL.
End Allo10x.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require InstInit Instmc8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.DriverKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.InstDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.DrvImzd.Allo10x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.InstInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instmc8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

#[global] Instance DriverP0 : @DriverKit _ LayoutP0 InitP0 AllocP0 := {|
  dk_init_frame := p0_dk_init_frame;
  dk_malloc_first_nf := p0_dk_malloc_first_nf
|}.

End CEIL.
