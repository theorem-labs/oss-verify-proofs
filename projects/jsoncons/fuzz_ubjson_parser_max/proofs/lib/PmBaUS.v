(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU PmParSpecs PmParSpecsU PmBaUStmts PmBaU10.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBAU.
Import PMU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Theorem begin_array_ok : PMPSU.peek_spec L HI -> PMPSU.ignore_spec L HI -> PMPSU.src_read_spec L HI -> PMU.get_length_spec L HI ->
PMU.make_ec_spec L HI -> PMU.opnew_spec L HI -> PMU.opdel_spec L HI -> PMU.begin_array_spec L HI.
Proof.
intros PEEK IGN SRD GL MKE OPN OPD.
unfold PMU.begin_array_spec, PMSP.begin_array_spec, PMSP.run_spec, PMSP.run_spec_r.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
assert (PRE : PMBAUS.pre L HI R M model K LBX cr sp r fb cat s str sm e).
{ unfold PMBAUS.pre. repeat (split; [assumption|]). exact CRED. }
unfold PMSP.cfg. cbn [pa_begin_array AD PmLayoutU.ADDR_U].
exact (PMBAU10.entry L HI LY HIok R M model K LBX cr sp r fb cat s str sm e PRE KONT PEEK IGN SRD GL MKE OPN OPD fx).
Qed.
End WithHeap.
End PMBAU.
