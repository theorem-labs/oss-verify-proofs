(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5DefsAB0 HeapIfaceAJx
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb PmSpecsBX PmSpecsAmc PmBLibOk
PmBStr PmBIss PmBSys PmBOpnew PmBOpdel PmBLoc PmBReaderRead.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBCL.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Close.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Hypothesis RDC : PMB.reader_ctor_spec L ar HI.
Hypothesis RST : PMB.reset_spec L ar HI.
Hypothesis PARSE : PMB.parse_spec L ar HI.
Hypothesis VDT : PMB.vec_dtor_spec L ar HI.
Hypothesis SRCD : PMB.src_dtor_spec L ar HI.
Hypothesis IOD : PMB.ios_dtor_spec L ar HI.
Theorem deps_closed : PMBLO.harness_depsB L ar HI.
Proof.
pose proof (PMBOPN.opnew_ok L ar C HI LY HIok) as OPN.
pose proof (PMBOPD.opdel_ok L ar C HI LY HIok) as OPD.
pose proof (PMBLOC.locale_ctor_ok L ar C IL HI LY HIok ICok ILY MCC) as LCC.
pose proof (PMBLOC.locale_dtor_ok L ar C HI LY HIok) as LCD.
split; [exact (PMBSTR.str_ctor_ok L ar C HI LY HIok OPN)|].
split; [exact (PMBISS.iss_ctor_ok L ar C IL HI LY HIok ICok ILY LCC OPN)|].
split; [exact RDC|].
split; [exact (PMBSY.syscat_ok L ar C HI LY HIok)|].
split; [exact (PMBRR.reader_read_ok L ar C HI LY HIok RST PARSE)|].
split; [exact VDT|].
split; [exact OPD|].
split; [exact SRCD|].
split; [exact LCD| exact IOD].
Qed.
End Close.
End SCFG_1.
End PMBCL.
