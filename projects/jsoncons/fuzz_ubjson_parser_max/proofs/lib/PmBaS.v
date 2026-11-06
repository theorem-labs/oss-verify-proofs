(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS PmParSpecs PmParSpecsS PmBaStmts PmBa10.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBA.
Import PMS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Theorem begin_array_ok : PMPSS.peek_spec L HI -> PMPSS.ignore_spec L HI -> PMPSS.src_read_spec L HI -> PMS.get_length_spec L HI ->
PMS.make_ec_spec L HI -> PMS.opnew_spec L HI -> PMS.opdel_spec L HI -> PMS.begin_array_spec L HI.
Proof.
intros PEEK IGN SRD GL MKE OPN OPD.
unfold PMS.begin_array_spec, PMSP.begin_array_spec, PMSP.run_spec, PMSP.run_spec_r.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
assert (PRE : PMBAS.pre L HI R M model K LBX cr sp r fb cat s str sm e).
{ unfold PMBAS.pre. repeat (split; [assumption|]). exact CRED. }
unfold PMSP.cfg. cbn [pa_begin_array AD PmLayoutS.ADDR_S].
exact (PMBA10.entry L HI LY HIok R M model K LBX cr sp r fb cat s str sm e PRE KONT PEEK IGN SRD GL MKE OPN OPD fx).
Qed.
End WithHeap.
End PMBA.
