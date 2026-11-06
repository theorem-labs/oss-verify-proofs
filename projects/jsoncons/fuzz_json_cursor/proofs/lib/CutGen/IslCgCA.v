(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ICG.
Section S.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Definition locale_ctor_first_specA_cg (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.ISLAND_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.ls_ok L IC PML.LS0 M /\ PMSA.acobj ar FF sp o 8 /\ o mod 8 = 0 /\ L5.defined M o 8 /\ PMSA.stksh ar M sp PMSA.ISLAND_SCR)
      (fun R M R' M' LB' cr' LBk W => PMSA.u64 L M' o (PMLA.CLASSIC_IMP IC) /\ PMSA.u8 L M' (PMLA.GLOC_GUARD IC) 1 /\ PMSA.u64 L M' (PMLA.GLOC_PTR IC) (PMLA.CLASSIC_IMP IC) /\
                        PMLA.errcat_guard (hl_segs L) IC M' 0 /\ PMLA.convcat_guard (hl_segs L) IC M' 0 /\ PMLA.atexit_ok (hl_segs L) IC M' PML.LS0 /\ PMLA.img_ro IC M' /\
                        PMSA.u8 L M' (PMLA.SYSCAT_GUARD IC) 0 /\ PMSA.u8 L M' (PMLA.SYSCAT_GUARD IC + 1) 0 /\
                        LB' = LB /\ cr' = cr /\ LBk = LB /\ W = (o, 8) :: PMSA.foot_ranges IC).
Lemma cg_weaken : forall pc, locale_ctor_first_specA_cg pc -> PMSA.locale_ctor_first_specA L ar HI IC pc.
Proof.
  intros pc H LB FF LK cr A o sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE CONT.
  apply (H LB FF LK cr A o sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE).
  intros fx' R' M' model' LB' cr' LBk W LK' A' Hfp' (P1 & P2 & P3 & P4 & _ & P5). apply (CONT fx' R' M' model' LB' cr' LBk W LK' A' Hfp').
  exact (conj P1 (conj P2 (conj P3 (conj P4 P5)))).
Qed.
End S.
End ICG.
