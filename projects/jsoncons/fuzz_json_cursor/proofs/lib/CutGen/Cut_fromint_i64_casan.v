(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_fromint_i64_casan_T Cut_fromint_i64_casan_R0p0 Cut_fromint_i64_casan_R0p1 Cut_fromint_i64_casan_R0p2 Cut_fromint_i64_casan_R0p3 Cut_fromint_i64_casan_R0p4 Cut_fromint_i64_casan_R0p5 Cut_fromint_i64_casan_R0p6 Cut_fromint_i64_casan_R0p7 Cut_fromint_i64_casan_R0p8 Cut_fromint_i64_casan_R0p9 Cut_fromint_i64_casan_R0p10 Cut_fromint_i64_casan_R0p11 Cut_fromint_i64_casan_R0p12 Cut_fromint_i64_casan_R0p13 Cut_fromint_i64_casan_R0p14 Cut_fromint_i64_casan_R1p0 Cut_fromint_i64_casan_R1p1 Cut_fromint_i64_casan_R1p2 Cut_fromint_i64_casan_R1p3 Cut_fromint_i64_casan_R1p4 Cut_fromint_i64_casan_R1p5 Cut_fromint_i64_casan_R1p6 Cut_fromint_i64_casan_R1p7 Cut_fromint_i64_casan_R1p8 Cut_fromint_i64_casan_R1p9.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Export Cut_fromint_i64_casan_D.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_fromint_i64_casan_C0 Cut_fromint_i64_casan_C1 Cut_fromint_i64_casan_C2 Cut_fromint_i64_casan_C3 Cut_fromint_i64_casan_C4 Cut_fromint_i64_casan_C5 Cut_fromint_i64_casan_C6 Cut_fromint_i64_casan_C7 Cut_fromint_i64_casan_C8 Cut_fromint_i64_casan_C9 Cut_fromint_i64_casan_C10 Cut_fromint_i64_casan_C11 Cut_fromint_i64_casan_C12 Cut_fromint_i64_casan_C13 Cut_fromint_i64_casan_C14 Cut_fromint_i64_casan_C15 Cut_fromint_i64_casan_C16 Cut_fromint_i64_casan_C17 Cut_fromint_i64_casan_C18 Cut_fromint_i64_casan_C19 Cut_fromint_i64_casan_C20 Cut_fromint_i64_casan_C21 Cut_fromint_i64_casan_C22 Cut_fromint_i64_casan_C23 Cut_fromint_i64_casan_C24.
Lemma tags_ok : CC.tags_chk CPS TAGS NF = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound RSEGS c.
Proof.
  intros i c H.
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert0)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert1)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert2)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert3)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert4)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert5)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert6)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert7)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert8)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert9)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert10)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert11)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert12)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert13)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert14)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert15)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert16)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert17)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert18)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert19)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert20)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert21)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert22)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert23)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert24)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert25)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert26)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert27)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert28)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert29)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert30)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert31)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert32)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert33)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert34)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert35)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert36)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert37)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert38)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert39)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert40)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert41)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert42)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert43)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert44)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert45)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert46)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert47)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert48)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert49)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert50)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert51)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert52)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert53)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert54)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert55)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert56)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert57)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert58)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert59)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert60)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert61)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert62)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert63)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert64)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert65)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert66)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert67)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert68)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert69)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert70)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert71)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert72)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert73)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert74)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert75)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert76)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert77)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert78)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert79)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert80)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert81)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert82)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert83)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert84)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert85)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert86)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert87)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert88)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert89)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert90)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert91)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert92)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert93)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert94)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert95)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert96)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert97)|].
  destruct i as [|i]; [injection H as <-; exact (as0_cut_plan_sound _ _ _ _ _ _ cert98)|].
  destruct i; discriminate H.
Qed.
Lemma NF_le : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof.
  assert (X : CC.cps_all CPS (fun _ c => Nat.leb NF (CC.cp_nx c)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply Nat.leb_le. exact (CC.cps_all_sound _ _ X i c H).
Qed.
