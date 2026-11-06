(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceAJ L5Defs L5Core L5DefsA HeapIfaceAJx HeapIfaceAJxI
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAa PmTopAL PmAHarnessStmts PmAHarness PmAStaticsTop PmAImgGap Ja0MainPhaseA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMALO.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Definition harness_depsA (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
PMA.str_ctor_spec L ar HI /\ PMA.iss_ctor_spec L ar HI /\ PMA.reader_ctor_spec L ar HI /\ PMA.syscat_spec L ar HI /\ PMA.reset_spec L ar HI
/\ PMA.parse_spec L ar HI /\ PMA.vec_dtor_spec L ar HI /\ PMA.opdel_spec L ar HI /\ PMA.src_dtor_spec L ar HI /\ PMA.locale_dtor_spec L ar HI
/\ PMA.ios_dtor_spec L ar HI.
Section LibOk.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis PKG : forall ar HIR, HAJ.asan_iface_okR L ar C SCFG HIR -> aicpt_ok L ar IL SCFG HIR -> HAJ.asan_ext_ok L ar SCFG HIR PMA.EXT ->
PMAGAP.rt_img_gap HIR -> harness_depsA L ar HIR.
Theorem lib_ok : lib_ok_stmt SCFG L C IL PMA.EXT (PMHAS.Lay L) (fun _ => PMSTA.TopLSA RSEGS PMA.AD PMA.AAD).
Proof.
unfold lib_ok_stmt, lib_ext_okG. intros ar HI _ _ (HIR & EHI & HIRok & ICok & EXT & GAP). subst HI.
split; [reflexivity|].
destruct (PKG ar HIR HIRok ICok EXT GAP) as (STR & ISS & RDC & SYS & RST & PARSE & VDT & OPD & SRCD & LCD & IOD).
constructor.
- exact (PMHA.harness_call_okA L ar C HIR IL LY HIRok ICok ILY STR ISS RDC SYS RST PARSE VDT OPD SRCD LCD IOD).
- exact (PMSTT.statics_initA L ar C LY).
- exact (PMSTT.statics_frameA L ar).
Qed.
End LibOk.
End SCFG_1.
End PMALO.
