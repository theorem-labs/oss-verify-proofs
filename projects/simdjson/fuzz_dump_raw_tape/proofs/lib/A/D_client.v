(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_libiface HandoffKit RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Record client_A : Type := mkClientA {
  cl_LIB : mem -> Prop;
  cl_loc : fp_local LIB_FP cl_LIB;
  cl_hs_ok : acs -> bool;
  cl_hs : forall (A : atable) (nx0 : nat) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs),
      (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None) ->
      APS.hull_ok A -> (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
      forall (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
      APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model ->
      forall A' : list (Z * Z), (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
      cl_hs_ok ch = true -> cl_LIB (mH FULL model A');
  cl_fuzz : rt_contracts2 RTA -> fuzz_one_cps RTA cl_LIB
}.
