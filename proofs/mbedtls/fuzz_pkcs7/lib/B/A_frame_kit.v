(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX Asn1Aux HeapIface Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_frame_kit () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Corelib.Init.Datatypes.app"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.sinv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Spec.CrtFacts.blocks_below"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "stdpp.bitvector.definitions.bv_unsigned"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blocks_apart_app2 : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PL1,(0.$1.)PL2,(0.$1.)Pb1,$1.Pb2,$1.P,(2.(3.$1.R4.R3.))P,(4.$1.R3.R5.)P,(4.$1.R3.R5.)(5.(6.(7.(8.$9.$9.R5.)(:.$9.$9.R5.))(8.$9.$9.R4.))(6.(7.(8.$9.$9.R4.)(:.$9.$9.R4.))(8.$9.$9.R5.)))")
(* [comment removed for export] *).
Proof.
  induction L1 as [|[x y] L1 IH]; cbn; intros L2 b1 b2 H H1 H2; [destruct H1|].
  destruct H as [Hx H]. destruct H1 as [<-|H1].
  - cbn. destruct b2 as [B k]. cbn. apply Hx. apply in_app_iff. right. exact H2.
  - eapply IH; eauto.
Qed.

Lemma fdata_sub2 : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PLF',(0.$1.)Pb,$1.P,(4.$1.R1.(;.R2.))(<.$1.Lfb,$1.(=.(4.$1.R1.R4.)(=.(6.(8.$9.$9.R1.)(8.$9.$9.R3.))(6.(7.(8.$9.$9.R3.)(:.$9.$9.R3.))(7.(8.$9.$9.R1.)(:.$9.$9.R1.))))))")
(* [comment removed for export] *).
Proof.
  induction LF' as [|[FB n] r IH]; intros b Hb; [destruct Hb|].
  cbn [fdata] in Hb. destruct Hb as [E|[E|Hb]].
  - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. split; [lia|]. pose proof (Z.le_min_r 24 n). lia.
  - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. lia.
  - ddestruct (IH b Hb) as (fb & H1 & H2). exists fb. split; [right; exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_unblob : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "Psegs,(0.$>.)Pm,P,(?.&40.)(10.(?.&8.))Pm',P,(?.&40.)(10.(?.&8.))PA,$9.Pcs,(0.$11.)Pn,$12.P,(13.R6.R5.R3.R2.)P,(14.$12.(15.R3.)R2.)P,(13.R8.R6.R5.(16.$11.(17.R3.(18.R4.))(19.$11.)))(13.R9.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' A cs n H <- HB. destruct H as [[Hwf _] _].
  eapply rw_cells_reshape; [exact HB| exact Hwf| cbn; rewrite app_nil_r; reflexivity].
Qed.

Lemma client_range_of_w : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PL,$1:.PLBF,(0.$1.)Plo,$9.PTOP,$9.PA,$9.Pn,$9.P,(1;.R6.R5.R4.R3.R2.R1.)(1<.R7.R6.R5.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros L LBF lo TOP A n CW x Hx. destruct (CW x Hx) as [X|[X|X]]; [left; lia| right; left; exact X| right; right; exact X].
Qed.

(* [comment removed for export] *)
Lemma client_range_lower : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PL,$1:.PLBF,(0.$1.)Plo,$9.PSP,$9.PA,$9.Pn,$9.P,(1<.R6.R5.R4.R2.R1.)P,(6.(7.R3.R2.)R5.)(1<.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros L LBF lo SP A n CR HLO. eapply client_range_sep; [exact CR| intros b Hb; exact Hb| left; exact HLO]. Qed.

(* [comment removed for export] *)
Lemma si_outside1 : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PL,$1:.PSI,(1=.R1.)PX,$9.Pn,$9.Pa,$9.P,(5.(6.(7.R3.R2.)(1>.R5.))(6.(1?.R5.)R3.))P,(20.(21.(22.R6.R5.)R2.))(21.(16.(23.$9.$9.)(24.$9.$9.R5.(7.R5.R4.))(19.(23.$9.$9.)))R3.)")
(* [comment removed for export] *).
Proof. intros L SI X n a HX Ha. ddestruct (si_data SI a Ha) as (Da & _ & _). cbn. split; [lia| exact I]. Qed.
Lemma si_outside2 : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PL,$1:.PSI,(1=.R1.)PX,$9.Pn,$9.PY,$9.Pk,$9.Pa,$9.P,(5.(6.(7.R5.R4.)(1>.R7.))(6.(1?.R7.)R5.))P,(5.(6.(7.R4.R3.)(1>.R8.))(6.(1?.R8.)R4.))P,(20.(21.(22.R9.R8.)R3.))(21.(16.(23.$9.$9.)(24.$9.$9.R8.(7.R8.R7.))(16.(23.$9.$9.)(24.$9.$9.R6.(7.R6.R5.))(19.(23.$9.$9.))))R4.)")
(* [comment removed for export] *).
Proof. intros L SI X n Y k a HX HY Ha. ddestruct (si_data SI a Ha) as (Da & _ & _). cbn. split; [lia| split; [lia| exact I]]. Qed.

Section WithR.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).

  (* [comment removed for export] *)
  #[using="Type"] Lemma presW_hmono : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "Ph,(25.$26.VR,VHIA,)Ph',(25.$26.VR,VHIA,)PLB,(0.$1.)PLF,(0.$1.)PSP,$9.PSSP,$9.PW,(0.$27.)Pm0,P,(?.&40.)(10.(?.&8.))Pm,P,(?.&40.)(10.(?.&8.))P,(28.$26.VR,VHIA,R9.R7.R6.R5.R4.R3.R2.R1.)P,Px,$9.P,(29.$26.VR,VHIA,R;.R1.)(29.$26.VR,VHIA,R;.R2.)P,(14.$9.(2:.$26.VR,VHIA,R:.)(2:.$26.VR,VHIA,R;.))(28.$26.VR,VHIA,R;.R:.R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    (intros h h' LB LF SP SSP W m0 m dd_H; ddestruct dd_H as (P & C1 & C2 & C3); intros HS ET). unfold presW. rewrite ET.
    split; [exact P|]. split; [intros c Hc; apply HS, C1, Hc|].
    split; [intros B j Hb; eapply crange_mono; [exact HS| apply (C2 B j Hb)]| exact C3].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma presW_init_at : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "Ph',(25.$26.VR,VHIA,)PLBh,(0.$1.)PLFh,(0.$1.)PLB',(0.$1.)PLF,(0.$1.)Pm,P,(?.&40.)(10.(?.&8.))PSP,$9.PSSP,$9.PW,(0.$27.)Ph,(25.$26.VR,VHIA,)P,(2;.$26.VR,VHIA,R:.R9.R8.R5.)P,Pb,$1.P,(4.$1.R1.R9.)(4.$1.R2.R<.)P,Pfb,$1.P,(4.$1.R1.R9.)(4.$1.R2.R<.)P,Px,$9.P,(29.$26.VR,VHIA,R5.R1.)(29.$26.VR,VHIA,R?.R2.)P,(14.$9.(2:.$26.VR,VHIA,R>.)(2:.$26.VR,VHIA,R5.))P,(6.(2<.VR,)R8.)(28.$26.VR,VHIA,R10.R=.R<.R:.R9.R8.R;.R;.)")
(* [comment removed for export] *).
  Proof.
    intros h' LBh LFh LB' LF m SP SSP W h HH HB HF HS ET HSSP.
    split; [apply presA_refl|]. split; [| split].
    - intros c Hc. destruct Hc as [X|[X|[X|X]]].
      + apply HS. apply (hcs_stack asegs R HIA h). rewrite ET in X. lia.
      + ddestruct X as ([B j] & Hb & Hr). cbn in Hr. eapply (hcs_block asegs R HIA h' _ _ m B j HH (HB _ Hb)). exact Hr.
      + ddestruct X as ([B j] & Hb & Hr). cbn in Hr. eapply (hcs_fake asegs R HIA h' _ _ m B j HH (HF _ Hb)). exact Hr.
      + apply hcs_static. exact X.
    - intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + eapply hcs_block; [exact HH| exact (HB _ Hb)].
      + destruct (fdata_sub2 LF _ Hb) as ([FB' n'] & HFB & H1 & H2). cbn [fst snd] in H1, H2.
        eapply crange_sub; [eapply hcs_fake; [exact HH| exact (HF _ HFB)]| exact H1| exact H2].
    - pose proof (hm_blocks_low asegs R HIA h' _ _ _ HH) as BL. intros B j Hb. apply BL.
      apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (HB _ Hb)| right; exact (HF _ Hb)].
  Qed.

  #[using="Type"] Lemma blocks_below_hm : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "Ph,(25.$26.VR,VHIA,)PLBh,(0.$1.)PLFh,(0.$1.)Pm,P,(?.&40.)(10.(?.&8.))PLB',(0.$1.)P,(2;.$26.VR,VHIA,R5.R4.R3.R2.)P,Pb,$1.P,(4.$1.R1.R3.)(4.$1.R2.R7.)(2=.R3.(2>.(2?.VR,)))")
(* [comment removed for export] *).
  Proof.
    intros h LBh LFh m LB' HH HB b Hb. destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
    destruct (BR b ltac:(apply in_app_iff; left; exact (HB _ Hb))) as (B0 & _ & Bce & _). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma obj_apart_new : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "Phq,(25.$26.VR,VHIA,)PLBc,(0.$1.)PLB,(0.$1.)PLF,(0.$1.)PLF',(0.$1.)Pmq,P,(?.&40.)(10.(?.&8.))Plo,$9.PTOPq,$9.PA,$9.Pn,$9.PB,$9.Pk,$9.P,(=.(6.(30.(2?.VR,))(1>.(2?.VR,)))(6.(1?.(2?.VR,))(31.(2?.VR,))))P,(2;.$26.VR,VHIA,R=.(3.$1.R<.R;.)R9.R8.)P,Pfb,$1.P,(4.$1.R1.R<.)(4.$1.R2.R<.)P,(1;.(2?.VR,)(3.$1.R=.(;.R<.))R9.R8.R7.R6.)P,(6.(2>.(2?.VR,))R:.)P,(32.=R8.)P,(4.(23.$9.$9.)(24.$9.$9.R8.R7.)R11.)P,(32.=R8.)(5.(6.(7.R:.R9.)R<.)(6.(7.R<.R;.)R:.))")
(* [comment removed for export] *).
  Proof.
    intros hq LBc LB LF LF' mq lo TOPq A n B k DIMG HH HLF CW CE Hn HB Hk.
    destruct (hm_apart asegs R HIA hq _ _ _ HH) as [BR BA]. rewrite Forall_forall in BR.
    ddestruct (BR (B, k) ltac:(apply in_app_iff; left; apply in_app_iff; left; exact HB)) as (B0 & _ & Bce & Bimg). cbn [fst snd] in B0, Bce, Bimg.
    eapply (client_wrange_apart L (LB ++ fdata LF) lo TOPq A n B k CW); [exact Hn| exact Hk| exact CE| exact Bce| clear - Bimg DIMG; lia|].
    intros B' j' Hb'. rewrite <- app_assoc in BA. apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
    - exact (blocks_apart_app2 LBc (LB ++ LF') (B, k) (B', j') BA HB ltac:(apply in_app_iff; left; exact Hb')).
    - destruct (fdata_sub2 LF _ Hb') as ([FB n'] & HF & H1 & H2). cbn [fst snd] in H1, H2.
      pose proof (blocks_apart_app2 LBc (LB ++ LF') (B, k) (FB, n') BA HB ltac:(apply in_app_iff; right; apply HLF; exact HF)) as AP'. cbn [fst snd] in AP'.
      clear - AP' H1 H2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fresh_apart_grow : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "Ph3,(25.$26.VR,VHIA,)PLBc,(0.$1.)PLB,(0.$1.)PLF,(0.$1.)Pm3,P,(?.&40.)(10.(?.&8.))PFB,$9.Pn,$9.P,(33.VR,R5.R4.R2.R1.)P,(2;.$26.VR,VHIA,R8.(3.$1.R7.R6.)(16.(23.$9.$9.)(24.$9.$9.R3.R2.)R5.)R4.)(33.VR,(3.$1.R8.R7.)R6.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros h3 LBc LB LF m3 FB n dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros HH). split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
    intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; right; exact Hb].
    apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; left; exact Hb].
    destruct (hm_apart asegs R HIA h3 _ _ _ HH) as [_ BA]. rewrite <- app_assoc in BA.
    pose proof (blocks_apart_app2 LBc (LB ++ (FB, n) :: LF) (B, j) (FB, n) BA Hb ltac:(apply in_app_iff; right; left; reflexivity)) as X. cbn [fst snd] in X. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma frame_factsA : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PCS,P,$9.SpPh1,(25.$26.VR,VHIA,)PLB,(0.$1.)PLF,(0.(23.$9.$9.))Pm1,P,(?.&40.)(10.(?.&8.))PFB,$9.Pn,$9.Plo,$9.P,(2;.$26.VR,VHIA,R7.R6.(16.(23.$9.$9.)(24.$9.$9.R3.R2.)R5.)R4.)P,(14.P,$9.Sp(29.$26.VR,VHIA,R8.)R9.)P,(33.VR,R8.R7.R5.R4.)P,(14.$9.(34.R6.+40.)=)P,(6.+28.R6.)P,(14.$9.(34.R7.+8.)=)P,(6.(2<.VR,)R7.)(=.(35.R?.R:.R9.)(=.(4.(23.$9.$9.)(24.$9.$9.R:.R9.)(16.(23.$9.$9.)(24.$9.$9.R:.R9.)R<.))(=.(4.(23.$9.$9.)(24.$9.$9.R:.+18.)(3.$1.R=.(;.(16.(23.$9.$9.)(24.$9.$9.R:.R9.)R<.))))(=.(4.(23.$9.$9.)(24.$9.$9.(7.R:.+20.)(36.R9.+28.))(3.$1.R=.(;.(16.(23.$9.$9.)(24.$9.$9.R:.R9.)R<.))))(=.PB,$9.Pj,$9.P,(4.(23.$9.$9.)(24.$9.$9.R2.R1.)R>.)(5.(6.(7.R=.R<.)R3.)(6.(7.R3.R2.)R=.))(=.(=.(32.=R:.)(=.(6.(7.R:.R9.)(2>.(2?.VR,)))(=.(5.(6.(7.R:.R9.)(1>.(2?.VR,)))(6.(1?.(2?.VR,))R:.))PB,$9.Pj,$9.P,(4.(23.$9.$9.)(24.$9.$9.R2.R1.)(3.$1.R?.(;.R>.)))(5.(6.(7.R=.R<.)R3.)(6.(7.R3.R2.)R=.)))))(=.(14.$9.(34.R:.+8.)=)(=.(6.(7.R:.R9.)R8.)(=.(=.(6.(1?.(2?.VR,))(7.(37.R:.+3.)(38.(39.VR,))))(6.(7.(7.(37.R:.+3.)(38.(39.VR,)))(3:.R9.+8.))(2>.(2?.VR,))))(5.(6.(7.(7.(37.R:.+3.)(38.(39.VR,)))(3:.R9.+8.))R:.)(6.(7.R:.R9.)(7.(37.R:.+3.)(38.(39.VR,))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros CS h1 LB LF m1 FB n lo HH1 Ehcs FRSH F64 N40 N8 LOS.
    dpose FRSH as (F0 & F1 & F2 & F3).
    assert (INF : In (FB, n) ((FB, n) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA h1 LB _ m1 FB n HH1 INF) as CFB. rewrite Ehcs in CFB.
    pose proof (art_lo asegs R HIA) as ALO.
    assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
    pose proof (hcs_ok asegs R HIA h1) as CSOK. rewrite Ehcs in CSOK.
    split; [exact CFB|]. split; [exact INF|].
    split; [apply in_app_iff; right; left; rewrite Z.min_l by lia; reflexivity|].
    split; [apply in_app_iff; right; right; left; reflexivity|].
    split; [exact (hm_fresh_frame_apart asegs R HIA h1 LB LF m1 FB n HH1)|].
    split; [exact (conj F0 (conj F1 (conj F2 F3)))|].
    split; [clear - F64; Z.div_mod_to_equations; lia|].
    split; [clear - F1 ALO LOS; lia|].
    split.
    - pose proof (hcs_shadow_band asegs R HIA h1 FB) as SBlo. rewrite Ehcs in SBlo. specialize (SBlo (CFB FB ltac:(clear - N40; lia))).
      pose proof (hcs_shadow_band asegs R HIA h1 (FB + 8 * (n / 8 - 1))) as SBhi. rewrite Ehcs in SBhi.
      specialize (SBhi (CFB (FB + 8 * (n / 8 - 1)) ltac:(clear - N40 N8; Z.div_mod_to_equations; lia))).
      rewrite shadow_of_plus in SBhi. unfold shadow_of in SBlo, SBhi. rewrite <- SHFB in SBlo, SBhi. clear - SBlo SBhi. lia.
    - pose proof (apart_shadow_client AL CS FB n FB (shadow_of AL FB) (n / 8) CSOK CFB) as APS.
      unfold shadow_of in APS. rewrite <- SHFB in APS.
      replace (8 * (n / 8)) with n in APS by (clear - N8 N40; Z.div_mod_to_equations; lia).
      destruct (APS CFB eq_refl ltac:(clear - N40; lia) ltac:(clear - N40 N8; Z.div_mod_to_equations; lia)); [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HIA"] Lemma frame_apart_obj : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PLB,(0.$1.)PLF,(0.$1.)Plo,$9.PTOP,$9.PA,$9.Pk,$9.PFB,$9.Pn,$9.P,(33.VR,R8.R7.R2.R1.)P,(1;.(2?.VR,)(3.$1.R9.(;.R8.))R7.R6.R5.R4.)P,(32.=R5.)P,(32.=R4.)P,(6.(2<.VR,)R:.)(5.(6.(7.R7.R6.)R9.)(6.(7.R9.R8.)R7.))")
(* [comment removed for export] *).
  Proof.
    intros LB LF lo TOP A k FB n FRSH CW Hk Hn LOS. pose proof (art_lo asegs R HIA) as ALO.
    eapply (fresh_apart_client R LB LF lo A k FB n FRSH); [| exact Hk| exact Hn| clear - ALO LOS; lia].
    eapply (client_range_inside L); [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia].
  Qed.
  #[using="HIA"] Lemma frame_apart_obj0 : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "PLB,(0.$1.)PLF,(0.$1.)Plo,$9.PA,$9.Pk,$9.PFB,$9.Pn,$9.P,(33.VR,R7.R6.R2.R1.)P,(1<.(2?.VR,)(3.$1.R8.(;.R7.))R6.R5.R4.)P,(6.=R5.)P,(32.=R4.)P,(6.(2<.VR,)R9.)(5.(14.$9.R8.=)(5.(6.(7.R7.R6.)R9.)(6.(7.R9.R8.)R7.)))")
(* [comment removed for export] *).
  Proof.
    intros LB LF lo A k FB n FRSH CR Hk Hn LOS. pose proof (art_lo asegs R HIA) as ALO.
    eapply (fresh_apart_client0 R LB LF lo A k FB n FRSH CR Hk Hn). clear - ALO LOS; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_frame_save : ltac2:(CDefT.buildp (gd_tbl_A_frame_kit ()) "Pm,P,(?.&40.)(10.(?.&8.))PTOP,$9.Ps0,(?.&40.)Pspv,$9.Psp1,$9.Pd,$9.P,(3;.$26.R6.(36.R3.+10.)(16.$11.(3<.R4.)(19.$11.)))P,(3=.$26.R7.(2<.VR,)R6.(3>.&40.R5.)R4.R2.)P,(6.(7.R4.+10.)R5.)P,(14.$9.(34.R6.+8.)=)P,(6.=R5.)(3=.$26.R;.(2<.VR,)R:.R8.R7.(7.R6.+1.))")
(* [comment removed for export] *).
  Proof.
    intros m TOP s0 spv sp1 d RO UW H1 H2 Hd.
    pose proof (bv_unsigned_in_range 64 s0) as XR. unfold bv_modulus in XR. cbn [Z.pow Z.of_N Pos.pow] in XR.
    rewrite <- (Z_to_bv_bv_unsigned s0) in RO.
    eapply uwc_frame; [exact H1| exact H2| exact XR| exact Hd| exact RO| exact UW].
  Qed.
End WithR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kland K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by (clear; lia));
  try rewrite Z.mod_small in K by lia.

(* [comment removed for export] *)
Ltac stk_merge_into H1 H2 :=
  lazymatch type of H1 with stk ?segs ?m ?a ?b =>
  lazymatch type of H2 with stk _ _ ?b' ?c =>
    (tryif constr_eq b b' then idtac else replace b' with b in H2 by lia);
    let K := fresh "STK" in
    pose proof (stk_merge segs m a b c H1 H2 ltac:(pose proof (proj1 H1); pose proof (proj1 H2); pose proof (proj1 (proj2 H1)); pose proof (proj1 (proj2 H2)); lia)) as K;
    clear H1 H2; rename K into H1
  end end.

(* [comment removed for export] *)
Ltac chunk_to_stk H :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let z := eval cbv in (Z.of_nat (cells_size cs)) in
    let K := fresh "STK" in
    pose proof (stk_of_rw_cells segs m A cs H) as K; clear H;
    change (Z.of_nat (cells_size cs)) with z in K; rename K into H
  end.

(* [comment removed for export] *)
Ltac ex_state :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end.
