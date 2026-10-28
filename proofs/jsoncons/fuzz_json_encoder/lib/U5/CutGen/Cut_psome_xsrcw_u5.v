(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX SmallKnX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_psome_xsrcw_T_u5 Cut_psome_xsrcw_R0_u5 Cut_psome_xsrcw_R1p0_u5 Cut_psome_xsrcw_R1p1_u5 Cut_psome_xsrcw_R1p2_u5 Cut_psome_xsrcw_R1p3_u5 Cut_psome_xsrcw_R1p4_u5 Cut_psome_xsrcw_R2_u5 Cut_psome_xsrcw_R3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Export Cut_psome_xsrcw_D_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_psome_xsrcw_C0_u5 Cut_psome_xsrcw_C1_u5 Cut_psome_xsrcw_C2_u5 Cut_psome_xsrcw_C3_u5 Cut_psome_xsrcw_C4_u5 Cut_psome_xsrcw_C5_u5.
Lemma tags_ok : CC.tags_chk CPS TAGS NF = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound RSEGS c.
Proof.
  intros i c H.
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert0)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert1)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert2)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert3)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert4)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert5)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert6)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert7)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert8)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert9)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert10)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert11)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert12)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert13)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert14)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert15)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert16)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert17)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert18)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert19)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert20)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert21)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert22)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert23)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert24)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert25)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert26)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert27)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert28)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert29)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert30)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert31)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert32)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert33)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert34)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert35)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert36)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert37)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert38)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert39)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert40)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert41)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert42)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert43)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert44)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert45)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert46)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert47)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert48)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert49)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert50)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert51)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert52)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert53)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert54)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert55)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert56)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert57)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert58)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert59)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert60)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert61)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert62)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert63)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert64)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert65)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert66)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert67)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert68)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert69)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert70)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert71)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert72)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert73)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert74)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert75)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert76)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert77)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert78)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert79)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert80)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert81)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert82)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert83)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert84)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert85)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert86)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert87)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert88)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert89)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert90)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert91)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert92)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert93)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert94)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert95)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert96)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert97)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert98)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert99)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert100)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert101)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert102)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert103)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert104)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert105)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert106)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert107)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert108)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert109)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert110)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert111)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert112)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert113)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert114)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert115)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert116)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert117)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert118)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert119)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert120)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert121)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert122)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert123)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert124)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert125)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert126)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert127)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert128)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert129)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert130)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert131)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert132)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert133)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert134)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert135)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert136)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert137)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert138)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert139)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert140)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert141)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert142)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert143)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert144)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert145)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert146)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert147)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert148)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert149)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert150)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert151)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert152)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert153)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert154)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert155)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert156)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert157)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert158)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert159)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert160)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert161)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert162)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert163)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert164)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert165)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert166)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert167)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert168)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert169)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert170)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert171)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert172)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert173)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert174)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert175)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert176)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert177)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert178)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert179)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert180)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert181)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert182)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert183)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert184)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert185)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert186)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert187)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert188)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert189)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert190)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert191)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert192)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert193)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert194)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert195)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert196)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert197)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert198)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert199)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert200)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert201)|].
  destruct i; discriminate H.
Qed.
Lemma NF_le : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof.
  assert (X : CC.cps_all CPS (fun _ c => Nat.leb NF (CC.cp_nx c)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply Nat.leb_le. exact (CC.cps_all_sound _ _ X i c H).
Qed.
