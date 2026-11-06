(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmCurDefs PmLibSpecsA PmCurSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HNKC.
Abbreviation mem := (word -> option byte).
Section Stmt.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Definition HARN_SCR : Z := 16384.
Definition EMPTY_C : Z := 0x68f020.
Definition len_class (lng : bool) (txt : list Z) : Prop := if lng then (23 <= length txt)%nat else (length txt <= 22)%nat.
Definition harness_pre (LB : list (Z * Z)) (cr : credit) (sp ptr : Z) (txt : list Z) (g : PML.ls_state) (R : bvmap 5 word) (M : mem) : Prop :=
  let n := Z.of_nat (length txt) in
  PMSA.a0 R ptr /\ PMSA.a1 R n /\ n < 2 ^ 26 /\ sp mod 16 = 0 /\ PMSA.stksh ar M sp HARN_SCR /\
  ((txt = [] /\ ptr = EMPTY_C) \/ (0 < n /\ In (ptr, n) LB)) /\ L5.bytes_at (hl_segs L) M ptr txt /\ L5.defined M ptr n /\ (0 < n -> shadow_blk M ptr n) /\
  PMLA.ls_ok (hl_segs L) IC g M /\
  fst (PMCSA.pm_creditA_c L n) <= fst cr /\ snd (PMCSA.pm_creditA_c L n) <= snd cr.
Definition harness_post (LB : list (Z * Z)) (cr : credit) (txt : list Z)
           (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  let n := Z.of_nat (length txt) in
  exists g' : PML.ls_state,
    PMSA.a0 R' 0 /\ PMLA.ls_ok (hl_segs L) IC g' M' /\ g' <> PML.LS0 /\ LB' = LB /\ LBk = LB /\
    fst cr - fst (PMCSA.pm_creditA_c L n) <= fst cr' /\ snd cr - snd (PMCSA.pm_creditA_c L n) <= snd cr' /\
    W = PMSA.foot_ranges IC ++ [(hl_tp L - 164, 4)].
Definition harness_chainA (pc aln : Z) (lng : bool) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r ptr : Z) (txt : list Z) (g : PML.ls_state),
    sp mod 32 = aln -> len_class lng txt ->
    PMSA.cps_asan L ar HI pc r sp HARN_SCR LB FF LK cr A PMCSA.LIB_FRAMES_C (harness_pre LB cr sp ptr txt g) (harness_post LB cr txt).
End Stmt.
End HNKC.
