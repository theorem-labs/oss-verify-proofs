(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core
PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsX PmSpecsU PmTopU PmUHarness PmUReaderRead PmUVecDtor.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMUT.
Section Top.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Record top_deps : Prop := TDEPS {
td_str_ctor : PMU.str_ctor_spec L HI;
td_iss_ctor : PMU.iss_ctor_spec L HI;
td_reader_ctor : PMU.reader_ctor_spec L HI;
td_syscat : PMU.syscat_spec L HI;
td_reset : PMU.reset_spec L HI;
td_parse : PMU.parse_spec L HI;
td_opdel : PMU.opdel_spec L HI;
td_src_dtor : PMU.src_dtor_spec L HI;
td_locale_dtor : PMU.locale_dtor_spec L;
td_ios_dtor : PMU.ios_dtor_spec L HI
}.
Theorem top_iface_ok : top_deps -> lib_iface_ok (PMTU.TopLay L) SCFG HI PMTU.TopLS.
Proof.
intros [STR ISS RDR SYS RST PARSE OPD SDT LDT IDT].
apply (PMUHT.harness_iface_ok L HI LY HIok). constructor; try assumption.
- exact (PMURR.reader_read_ok L HI LY HIok RST PARSE).
- exact (PMUVD.vec_dtor_ok L HI LY HIok OPD).
Qed.
End Top.
End PMUT.
