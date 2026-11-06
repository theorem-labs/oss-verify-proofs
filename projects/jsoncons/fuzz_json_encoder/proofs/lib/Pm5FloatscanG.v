(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5L5DefsA PmHeapIfaceA PmLibSpecsA
  DecIface DecJson DecIfaceA StrtodIface FloatLazyA Pm5FloatscanOk Pm5FsInfOk.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A CutBridgeA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FSGA.
Definition ENTRY : Z := 1381192.
Definition gtext (txt : list Z) : Prop := PDJ.num_final txt \/ FSIA.infnan txt.
Section S.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FL : PDCA.float_layoutA L FSIA.AD.
Definition fs_pre_g (sp F s CAN : Z) (txt : list Z) (LB : list (Z * Z)) (FF : list fframe) (R : bvmap 5 word) (M : PDCA.mem) : Prop :=
  PDCA.fs_preA L ar FSIA.AD sp F s CAN txt LB FF R M \/ FSIA.fs_pre_nf L ar sp F s CAN txt LB FF R M.
Definition floatscan_g_contractA (pc : Z) : Prop :=
  forall r sp F s CAN txt, PDCA.cps_pureLB L ar HI PMSA.fp_ok pc r sp PSI.WIN 0 [(F + 8, 8); (PDC.a_TP FSIA.AD - 164, 4)] (fs_pre_g sp F s CAN txt) (PDCA.fs_postA L F s txt).
Theorem floatscan_g_okA : floatscan_g_contractA ENTRY.
Proof.
  intros r sp F s CAN txt LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hpre Hcont.
  destruct Hpre as [Hp|Hp].
  - exact (FSOA.floatscan_okA L ar C HI HIok LAY FL r sp F s CAN txt LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hp Hcont).
  - exact (FSIA.floatscan_nf_okA L ar C HI HIok LAY FL r sp F s CAN txt LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hp Hcont).
Qed.
End S.
End FSGA.
