(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmSpecs PmSpecsS PmParSpecs PmParSpecsS PmSRdValD PmSRdValQ PmSRdValR PmSRdValS PmSRdValA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSRV.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Theorem read_value_ok : PMPSS.src_read_spec L HI -> PMS.get_length_spec L HI -> PMS.read_span_spec L HI -> PMS.validate_spec L -> PMS.is_base10_spec L ->
PMS.begin_array_spec L HI -> PMS.begin_object_spec L HI -> PMS.make_ec_spec L HI -> PMS.read_value_spec L HI.
Proof.
intros SR GL RS VAL B10 BA BO MKE. unfold PMS.read_value_spec, PMSP.read_value_spec, PMSP.run_spec, PMSP.run_spec_r.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS.
destruct ARGS as (A10 & A11 & A13 & t & Ht & A12).
destruct (PMSRVD.rv_split t Ht) as [G|[G|[G|G]]].
- pose proof (PMSRVQ.rv_partQ L HI LY HIok MKE) as P. unfold PMSP.run_spec, PMSP.run_spec_r in P.
apply (P fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK). exact (conj A10 (conj A11 (conj A13 (ex_intro _ t (conj Ht (conj G A12)))))).
- pose proof (PMSRVR.rv_partR L HI LY HIok SR VAL MKE) as P. unfold PMSP.run_spec, PMSP.run_spec_r in P.
apply (P fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK). exact (conj A10 (conj A11 (conj A13 (ex_intro _ t (conj Ht (conj G A12)))))).
- pose proof (PMSRVS.rv_partS L HI LY HIok GL RS VAL B10 MKE) as P. unfold PMSP.run_spec, PMSP.run_spec_r in P.
apply (P fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK). exact (conj A10 (conj A11 (conj A13 (ex_intro _ t (conj Ht (conj G A12)))))).
- pose proof (PMSRVA.rv_partA L HI LY HIok BA BO MKE) as P. unfold PMSP.run_spec, PMSP.run_spec_r in P.
apply (P fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK). exact (conj A10 (conj A11 (conj A13 (ex_intro _ t (conj Ht (conj G A12)))))).
Qed.
End WithHeap.
End PMSRV.
