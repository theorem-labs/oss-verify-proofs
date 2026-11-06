(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5DefsA HeapIfaceAJx
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAa PmALibOk
PmAStr PmAIss PmARd PmASys PmAReset PmAVecDtor PmASrcDtor PmAIosDtor PmAOpnew PmAOpdel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMACL.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Close.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Hypothesis LCC : PMA.locale_ctor_spec L ar HI.
Hypothesis LCD : PMA.locale_dtor_spec L ar HI.
Hypothesis PMI : PMA.push_mi_spec L ar HI.
Hypothesis PMIU : PMA.push_miu_spec L ar HI.
Hypothesis ASH : PMA.ann_shrink_spec L ar HI.
Hypothesis ADL : PMA.ann_delete_spec L ar HI.
Hypothesis PARSE : PMA.parse_spec L ar HI.
Theorem deps_closed : PMALO.harness_depsA L ar HI.
Proof.
pose proof (PMAOPN.opnew_ok L ar C HI LY HIok) as OPN.
pose proof (PMAOPD.opdel_ok L ar C HI LY HIok) as OPD.
pose proof (PMAID.ios_dtor_ok L ar C HI LY HIok EXT LCD) as IOD.
split; [exact (PMASTR.str_ctor_ok L ar C HI LY HIok OPN)|].
split; [exact (PMAISS.iss_ctor_ok L ar C IL HI LY HIok ICok ILY LCC OPN)|].
split; [exact (PMARD.reader_ctor_ok L ar C IL HI LY HIok ICok ILY LCC OPN PMI)|].
split; [exact (PMASY.syscat_ok L ar C HI LY HIok)|].
split; [exact (PMARS.reset_ok L ar C HI LY HIok ASH PMIU)|].
split; [exact PARSE|].
split; [exact (PMAVD.vec_dtor_ok L ar C HI LY HIok ASH ADL OPD)|].
split; [exact OPD|].
split; [exact (PMASD.src_dtor_ok L ar C HI LY HIok OPD LCD IOD)|].
split; [exact LCD| exact IOD].
Qed.
End Close.
End SCFG_1.
End PMACL.
