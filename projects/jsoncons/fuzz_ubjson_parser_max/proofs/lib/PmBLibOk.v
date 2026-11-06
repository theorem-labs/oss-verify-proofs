(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceAJ L5Defs L5Core L5DefsAB0 HeapIfaceAJx
HeapIfaceAJxI PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmSpecsBX PmTopAL PmBHarnessStmts PmBHarness PmBStaticsTop PmBImgGap Jb0MainPhaseA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBLO.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Definition harness_depsB (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
PMB.str_ctor_spec L ar HI /\ PMB.iss_ctor_spec L ar HI /\ PMB.reader_ctor_spec L ar HI /\ PMB.syscat_spec L ar HI /\ PMBX.reader_read_spec L ar HI
/\ PMB.vec_dtor_spec L ar HI /\ PMB.opdel_spec L ar HI /\ PMB.src_dtor_spec L ar HI /\ PMB.locale_dtor_spec L ar HI
/\ PMB.ios_dtor_spec L ar HI.
Section LibOk.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMB.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis PKG : forall ar HIR, HAJ.asan_iface_okR L ar C SCFG HIR -> aicpt_ok L ar IL SCFG HIR -> HAJ.asan_ext_ok L ar SCFG HIR PMB.EXT ->
PMBGAP.rt_img_gap HIR -> harness_depsB L ar HIR.
Theorem lib_ok : lib_ok_stmt SCFG L C IL PMB.EXT (PMHAS.Lay L) (fun _ => PMSTA.TopLSA RSEGS PMB.AD PMB.AAD).
Proof.
unfold lib_ok_stmt, lib_ext_okG. intros ar HI _ _ (HIR & EHI & HIRok & ICok & EXT & GAP). subst HI.
split; [reflexivity|].
destruct (PKG ar HIR HIRok ICok EXT GAP) as (STR & ISS & RDC & SYS & RRD & VDT & OPD & SRCD & LCD & IOD).
constructor.
- exact (PMHA.harness_call_okA L ar C HIR IL LY HIRok ICok ILY STR ISS RDC SYS RRD VDT OPD SRCD LCD IOD).
- exact (PMSTTB.statics_initA L ar C LY PMHAS.STK PMHAS.FRAMES PMHAS.LEAK PMHAS.CREDIT).
- exact (PMSTTB.statics_frameA L ar PMHAS.STK PMHAS.FRAMES PMHAS.LEAK PMHAS.CREDIT).
Qed.
End LibOk.
End SCFG_1.
End PMBLO.
