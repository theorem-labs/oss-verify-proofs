(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_alloc_lib () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Stdlib.Lists.List.In"; "uw_obj"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"].


Lemma hstkhi_le64 : forall segs R (HIA : artA segs R) h,
  arl_stklo R <= 2^64 -> hstkhi segs R HIA h <= 2^64.
Proof.
  intros segs R HIA h HS. destruct (Z_le_gt_dec (hstkhi segs R HIA h) (2^64)) as [H|H]; [exact H|]. exfalso.
  pose proof (hcs_stack segs R HIA h (2^64) ltac:(lia)) as C.
  destruct (hcs_ok segs R HIA h) as (C1 & _). destruct (C1 _ C) as (R0 & _). lia.
Qed.

Lemma fr_charge_nonneg : forall segs m LO TOP v F d, uwc segs m LO TOP v F d -> 0 <= fr_charge d.
Proof. intros. unfold fr_charge. pose proof (uwc_nonneg _ _ _ _ _ _ _ H). lia. Qed.

Lemma uwc_callW : ltac2:(CDefT.buildp (gd_tbl_A_alloc_lib ()) "Psegs,(0.$1.)PW,(0.$2.)Pm,P,(3.&40.)(4.(3.&8.))Pm1,P,(3.&40.)(4.(3.&8.))PLO,$5.PTOP,$5.Pv,$5.PSP,$5.PSP',$5.Pd,$5.P,(6.R:.R8.R6.R5.R4.R3.R1.)P,(7.R:.R9.R8.)P,Pa,$5.P,(8.(9.R6.R1.)(:.R1.R8.))(;.R=.R2.)P,(9.R5.R6.)P,(9.=R7.)P,(9.R:.(<.+2.+40.))(6.R10.R=.R<.R;.R:.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs W m m1 LO TOP v SP SP' d UW MU OW HS H0 HT.
  eapply uwc_floor; [| exact HS]. eapply uwc_munch; eauto.
Qed.

(* [comment removed for export] *)
Lemma uwc_call : ltac2:(CDefT.buildp (gd_tbl_A_alloc_lib ()) "Psegs,(0.$1.)PW,(0.$2.)Pm,P,(3.&40.)(4.(3.&8.))Pm1,P,(3.&40.)(4.(3.&8.))PLO,$5.PTOP,$5.Pv,$5.PSP,$5.PSP',$5.Pd,$5.P,(6.R:.R8.R6.R5.R4.R3.R1.)P,(7.R:.R9.R8.)P,(=.(>.$5.$5.)Liv,(>.$5.$5.)(9.(?.$5.$5.R1.)R6.)R;.)P,(9.R5.R6.)P,(9.=R7.)P,(9.R:.(<.+2.+40.))(6.R10.R=.R<.R;.R:.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs W m m1 LO TOP v SP SP' d UW MU HW HS H0 HT.
  eapply uwc_callW; eauto. intros a Ha. clear - HW Ha.
  induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *.
  split; [lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma presW_sub_blocks : ltac2:(CDefT.buildp (gd_tbl_A_alloc_lib ()) "Psegs,(0.$1.)PR,$10.PHIA,(11.R2.R1.)Ph,(12.R3.R2.R1.)PLB,(0.$13.)PLBk,(0.$13.)PLF,(0.$13.)PSP,$5.PSSP,$5.PW,(0.$2.)Pm0,P,(3.&40.)(4.(3.&8.))Pm,P,(3.&40.)(4.(3.&8.))P,(14.R<.R;.R:.R9.R8.R6.R5.R4.R3.R2.R1.)P,Pb,$13.P,(15.$13.R1.R9.)(15.$13.R2.R;.)(14.R>.R=.R<.R;.R9.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros segs R HIA h LB LBk LF SP SSP W m0 m dd_H; ddestruct dd_H as (P & C1 & C2 & C3); intros HS).
  assert (HIB : forall x, in_block LBk x -> in_block LB x) by ((intros x dd_H; ddestruct dd_H as (b & Hb & Hr)); exists b; split; [apply HS, Hb| exact Hr]).
  split; [| split; [| split]].
  - eapply presA_weaken; [exact P| exact HS| intros b Hb; exact Hb| lia| lia| lia| intros x Hx; exact Hx].
  - intros c Hc. apply C1. destruct Hc as [A|[A|[A|A]]]; [left; exact A| right; left; apply HIB, A| right; right; left; exact A| right; right; right; exact A].
  - intros B j HB. apply C2. apply in_app_iff in HB. apply in_app_iff. destruct HB as [HB|HB]; [left; apply HS, HB| right; exact HB].
  - intros B j HB. apply C3. apply in_app_iff in HB. apply in_app_iff. destruct HB as [HB|HB]; [left; apply HS, HB| right; exact HB].
Qed.

Lemma wlow_sub_blocks : forall R LB LBk LF, wlow R LB LF -> (forall b, In b LBk -> In b LB) -> wlow R LBk LF.
Proof.
  intros R LB LBk LF [BL DL] HS. split; [| exact DL]. intros B j HB. apply BL.
  apply in_app_iff in HB. apply in_app_iff. destruct HB as [HB|HB]; [left; apply HS, HB| right; exact HB].
Qed.

(* [comment removed for export] *)
Definition uw_obj (R : art_layout) (A n d : Z) : Prop := (A + n <= arl_stklo R /\ 0 <= d) \/ 28 <= d.

Lemma uw_obj_uwc : ltac2:(CDefT.buildp (gd_tbl_A_alloc_lib ()) "Psegs,(0.$1.)PR,$10.Pm,P,(3.&40.)(4.(3.&8.))PTOP,$5.PA,$5.Pn,$5.Pd,$5.Pv,$5.PF,$5.P,(16.R8.R5.R4.R3.)P,(8.(9.R6.R3.)(:.R3.(17.R6.R5.)))(6.R;.R9.(18.R:.)R8.R4.R3.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs R m TOP A n d v F [[H Hd]|H] Hv.
  - apply uwc_data; [exact Hd| lia].
  - apply uwc_cap. exact H.
Qed.

Lemma uw_obj_nonneg : forall R A n d, uw_obj R A n d -> 0 <= d.
Proof. intros R A n d [[_ H]|H]; lia. Qed.

Lemma uw_obj_sub : forall R A n d A' n', uw_obj R A n d -> A <= A' -> A' + n' <= A + n -> uw_obj R A' n' d.
Proof. intros R A n d A' n' [[H Hd]|H] H1 H2; [left; split; [lia| exact Hd]| right; exact H]. Qed.

(* [comment removed for export] *)
Lemma uw_obj_block : ltac2:(CDefT.buildp (gd_tbl_A_alloc_lib ()) "Psegs,(0.$1.)PR,$10.PHIA,(11.R2.R1.)Ph,(12.R3.R2.R1.)PLB,(0.$13.)PLF,(0.$13.)Pm,P,(3.&40.)(4.(3.&8.))PB,$5.Pj,$5.PA,$5.Pn,$5.Pd,$5.P,(19.R<.R;.R:.R9.R8.R7.R6.)P,(15.(>.$5.$5.)(1:.$5.$5.R6.R5.)(1;.$13.R9.R8.))P,(9.R7.R5.)P,(9.(17.R6.R5.)(17.R8.R7.))P,(9.=R5.)(16.R10.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m B j A n d HH HIn H1 H2 Hd. left. split; [| exact Hd].
  destruct (hm_apart segs R HIA h LB LF m HH) as [HF _]. rewrite Forall_forall in HF.
  ddestruct (HF (B, j) HIn) as (_ & _ & HC & _). cbn in HC. pose proof (art_lo segs R HIA). lia.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma presA_drop_below : ltac2:(CDefT.buildp (gd_tbl_A_alloc_lib ()) "Psegs,(0.$1.)PR,$10.PHIA,(11.R2.R1.)Ph,(12.R3.R2.R1.)PLB,(0.$13.)PLF,(0.$13.)PW,(0.(>.$5.$5.))Pa,$5.Pb,$5.Pmm,P,(3.&40.)(4.(3.&8.))Pm1,P,(3.&40.)(4.(3.&8.))Pm2,P,(3.&40.)(4.(3.&8.))PSP,$5.P,(19.R=.R<.R;.R:.R9.R8.R4.)P,(1<.R>.R=.R:.R9.R2.(18.R=.)(1=.R>.R=.R<.R;.)(1>.(>.$5.$5.)(1:.$5.$5.R7.R6.)R8.)R4.R3.)P,(9.R7.R3.)P,(9.(18.R?.)R9.)(1<.R11.R10.R=.R<.R5.(18.R10.)(1=.R11.R10.R?.R>.)R;.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF W a b mm m1 m2 SP HH [P S] Hb Ha. split; [| exact S].
  pose proof (art_lo segs R HIA) as ALO. pose proof (art_data_lo segs R HIA) as DHI.
  destruct (hm_apart segs R HIA h LB LF mm HH) as [HBR _]. rewrite Forall_forall in HBR.
  intros x Hx Hc Ho. apply P; [exact Hx| exact Hc|]. cbn [outside]. split; [| exact Ho].
  intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(bk & Hbk & Hr)]].
  - clear - Hs Hin Hb. lia.
  - clear - Hd1 Hin Ha ALO DHI. cbn in *. lia.
  - apply in_app_iff in Hbk. destruct Hbk as [Hbk|Hbk].
    + ddestruct (HBR bk ltac:(apply in_app_iff; left; exact Hbk)) as (_ & _ & HC & _). clear - HC Hr Hin Ha ALO. lia.
    + ddestruct (in_fdata_hull LF bk x Hbk Hr) as (fb & Hfb & Hr2).
      ddestruct (HBR fb ltac:(apply in_app_iff; right; exact Hfb)) as (_ & _ & HC & _). clear - HC Hr2 Hin Ha ALO. lia.
Qed.

(* [comment removed for export] *)
Lemma presA_drop_fresh : ltac2:(CDefT.buildp (gd_tbl_A_alloc_lib ()) "Psegs,(0.$1.)PR,$10.PHIA,(11.R2.R1.)Ph,(12.R3.R2.R1.)PLB,(0.$13.)PLF,(0.$13.)PW,(0.(>.$5.$5.))PN,$5.Pk,$5.Pm1,P,(3.&40.)(4.(3.&8.))Pm2,P,(3.&40.)(4.(3.&8.))PSP,$5.P,(1<.R<.R;.R8.R7.R1.(18.R;.)(1=.R<.R;.R:.R9.)(1>.(>.$5.$5.)(1:.$5.$5.R5.(17.R5.R4.))R6.)R3.R2.)P,(1?.R<.R9.R8.R6.R5.)P,(9.(18.R=.)R3.)(1<.R?.R>.R;.R:.R4.(18.R>.)(1=.R?.R>.R=.R<.)R9.R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros segs R HIA h LB LF W N k m1 m2 SP [P S] dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros HS). split; [| exact S].
  pose proof (art_lo segs R HIA) as ALO.
  intros a Ha Hc Ho. apply P; [exact Ha| exact Hc|]. cbn [outside]. split; [| exact Ho].
  intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]].
  - clear - Hs Hin F1 ALO HS. lia.
  - clear - Hd1 Hd2 Hin F2. cbn in *. lia.
  - destruct b as [B j]. cbn in Hr. pose proof (F3 B j Hb). clear - Hr Hin H. lia.
Qed.
