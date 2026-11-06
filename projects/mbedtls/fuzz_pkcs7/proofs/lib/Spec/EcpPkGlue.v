(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux MpiCoreAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves EcpLoad EcpFacts.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_EcpPkGlue () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.EcpCurves.curve_addrs"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Spec.RepEcp.g_P"; "OSSVerify.KrLib.Spec.EcpCurves.grp_sw"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.EcpLoad.curve_statics"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Spec.EcpCurves.is_sw"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Spec.RepEcp.ecp_grp"; "OSSVerify.KrLib.Spec.RepEcp.g_h"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.RepEcp.pt_X"; "OSSVerify.KrLib.Spec.RepEcp.g_G"; "OSSVerify.KrLib.Spec.RepEcp.pt_Y"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.RepEcp.g_A"; "OSSVerify.KrLib.Spec.RepEcp.g_B"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "Corelib.Init.Logic.or"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.RepEcp.grp_mpds"; "OSSVerify.KrLib.Spec.EcpCurves.grp_mx"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Spec.RepEcp.grp_init"; "Corelib.Init.Datatypes.nat"; "Groups.wr_img_b"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Mem.wr_at"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.AStep.const_at"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Statics.img_bytes_b"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"].


(* [comment removed for export] *)
Lemma cP_val_pos : forall id, 1 <= id <= 13 -> 1 <= limbs_val (cP id).
Proof.
  intros id Hid.
  assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]; vm_compute; discriminate.
Qed.

Section Groups.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cP_short : forall id, Z.of_nat (length (cP id)) <= 17.
  Proof.
    intros id. unfold cP.
    destruct id as [|p|p]; [cbn; lia| | cbn; lia].
    do 5 (destruct p as [p|p|]; [| | cbn; lia]); cbn; lia.
  Qed.
  #[using="Type"] Lemma grp_sw_Pn : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pid,$0.Pca,$1.PONE,$0.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)(3.(4.(5.(6.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))+1387.)")
(* [comment removed for export] *).
  Proof. intros. unfold grp_sw. cbn -[cP Z.le Z.of_nat]. pose proof (cP_short id). lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma grp_sw_checks : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pca,$1.PONE,$0.Pid,$0.Pm,P,(2.&40.)(7.(2.&8.))PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)P,(8.Vsegs,R>.R=.R<.R;.)P,(9.$:.(;.R=.)$<.)P,(=.(3.+1.R>.)(3.R>.+=.))Zg,$>.(6.R?.R11.R10.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(=.(9.$0.(?.R1.)+1.)(=.(10.(9.$0.(11.(12.(13.R1.)))=))(=.(10.(9.$0.(11.(14.(13.R1.)))=))(=.(9.$0.(15.(5.R1.))+1.)(=.(9.$0.(15.(16.R1.))+1.)(=.(9.$0.(15.(17.R1.))+1.)(=.(3.+1.(18.(5.R1.)))(=.(19.(9.$0.(15.(5.R1.))+1.)(9.$0.(15.(5.R1.))-1.))(1:.$1;.Ld,$1;.(10.(9.$1<.(1=.R1.)$1>.))(1?.R1.))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. intros (SP & SA & SW & SN & SO) HSW Hid. cbv zeta. destruct (SW HSW) as (SB & SX & SY).
    pose proof SX as (_ & _ & _ & X0 & _). pose proof SY as (_ & _ & _ & Y0 & _).
    unfold grp_sw. cbn -[cP cA cB cGX cGY cN has_A core_bitlen limbs_val Z.le Z.lt Z.mul].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [destruct (has_A id); reflexivity|]. split; [reflexivity|].
    split; [unfold mpd_val; cbn -[cP limbs_val Z.le Z.mul]; pose proof (cP_val_pos id Hid); lia|]. split; [left; reflexivity|].
    unfold grp_mpds, pt_mpds. cbn -[cP cA cB cGX cGY cN has_A].
    constructor; [cbn; discriminate|]. constructor; [destruct (has_A id); cbn; discriminate|]. repeat (constructor; [cbn; discriminate|]). constructor.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma grp_mx_checks : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pca,$1.Pid,$0.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PPA,$0.PPX,$0.PPZ,$0.PwA,(2.&40.)PwX,(2.&40.)PwZ,(2.&40.)P,(19.(9.$0.R11.+9.)(9.$0.R11.+=.))Zg,$>.(20.R12.R13.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(=.(9.$0.(?.R1.)+2.)(=.(9.$0.(11.(14.(13.R1.)))=)(=.(9.$0.(15.(5.R1.))+1.)(=.(9.$0.(15.(16.R1.))+1.)(=.(9.$0.(15.(17.R1.))+1.)(=.(3.+1.(18.(5.R1.)))(=.(19.(9.$0.(15.(5.R1.))+1.)(9.$0.(15.(5.R1.))-1.))Pd,$1;.P,(21.$1;.R1.(1?.R2.))P,(9.$1<.(1=.R2.)$1>.)(19.(=.(9.$0.(11.R3.)R;.)(9.$0.(4.R3.)+1.))(19.(=.(9.$0.(11.R3.)R:.)(9.$0.(4.R3.)+1.))(=.(9.$0.(11.R3.)R9.)(9.$0.(4.R3.)+1.)))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until wZ. intros Hid. cbv zeta. unfold grp_mx, grp_mxi, heap1. cbn -[cP cN core_bitlen limbs_val mx_nbits Z.le Z.lt Z.mul].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold mpd_val; cbn -[cP limbs_val Z.le Z.mul]; pose proof (cP_val_pos id ltac:(lia)); lia|]. split; [left; reflexivity|].
    intros d Hd O. unfold grp_mpds, pt_mpds in Hd. cbn -[cP cN] in Hd.
      destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O |- *; try discriminate; auto.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma grp_sw_check_pubkey_kind : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pca,$1.PONE,$0.Pid,$0.Pm,P,(2.&40.)(7.(2.&8.))PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)P,(8.Vsegs,R>.R=.R<.R;.)P,(9.$:.(;.R=.)$<.)P,(=.(3.+1.R>.)(3.R>.+=.))Zg,$>.(6.R?.R11.R10.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(19.(=.(9.$0.(?.R1.)+1.)(=.(10.(9.$0.(11.(12.(13.R1.)))=))(10.(9.$0.(11.(14.(13.R1.)))=))))(=.(9.$0.(?.R1.)+2.)(9.$0.(11.(14.(13.R1.)))=)))")
(* [comment removed for export] *).
  Proof. intros. destruct (grp_sw_checks ca ONE id m A idpad pP pA pB pX pY pZ pN hpad H H0 H1) as (A1 & A2 & A3 & _). left. auto. Qed.

  #[using="Type"] Lemma grp_mx_check_pubkey_kind : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pca,$1.Pid,$0.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PPA,$0.PPX,$0.PPZ,$0.PwA,(2.&40.)PwX,(2.&40.)PwZ,(2.&40.)P,(19.(9.$0.R11.+9.)(9.$0.R11.+=.))Zg,$>.(20.R12.R13.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(19.(=.(9.$0.(?.R1.)+1.)(=.(10.(9.$0.(11.(12.(13.R1.)))=))(10.(9.$0.(11.(14.(13.R1.)))=))))(=.(9.$0.(?.R1.)+2.)(9.$0.(11.(14.(13.R1.)))=)))")
(* [comment removed for export] *).
  Proof. intros. destruct (grp_mx_checks ca id A idpad pP pA pB pX pY pZ pN hpad PA PX PZ wA wX wZ H) as (A1 & A2 & _). right. auto. Qed.

  #[using="Type"] Lemma grp_sw_point_read_facts : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pca,$1.PONE,$0.Pid,$0.Pm,P,(2.&40.)(7.(2.&8.))PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)P,(8.Vsegs,R>.R=.R<.R;.)P,(9.$:.(;.R=.)$<.)P,(=.(3.+1.R>.)(3.R>.+=.))Zg,$>.(6.R?.R11.R10.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(10.(9.$0.(11.(12.(13.R1.)))=))P,(10.(9.$0.(11.(14.(13.R2.)))=))(=.(9.$0.(?.R3.)+1.)(=.(9.$0.(15.(5.R3.))+1.)(=.(9.$0.(15.(16.R3.))+1.)(=.(9.$0.(15.(17.R3.))+1.)(=.(3.+1.(18.(5.R3.)))(3.(4.(5.R3.))+1387.))))))")
(* [comment removed for export] *).
  Proof. intros. destruct (grp_sw_checks ca ONE id m A idpad pP pA pB pX pY pZ pN hpad H H0 H1) as (A1 & _ & _ & A4 & A5 & A6 & A7 & _). pose proof (grp_sw_Pn id ca ONE A idpad pP pA pB pX pY pZ pN hpad). auto 7. Qed.

  #[using="Type"] Lemma grp_mx_point_read_facts : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pca,$1.Pid,$0.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PPA,$0.PPX,$0.PPZ,$0.PwA,(2.&40.)PwX,(2.&40.)PwZ,(2.&40.)P,(19.(9.$0.R11.+9.)(9.$0.R11.+=.))Zg,$>.(20.R12.R13.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(10.(9.$0.(11.(12.(13.R1.)))=))P,(10.(9.$0.(11.(14.(13.R2.)))=))(=.(9.$0.(?.R3.)+1.)(=.(9.$0.(15.(5.R3.))+1.)(=.(9.$0.(15.(16.R3.))+1.)(=.(9.$0.(15.(17.R3.))+1.)(=.(3.+1.(18.(5.R3.)))(3.(4.(5.R3.))+1387.))))))")
(* [comment removed for export] *).
  Proof. intros until wZ. intros Hid. cbv zeta. intros _ HY. exfalso. apply HY. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma grp_init_GX : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)(9.$0.(11.(12.(13.(22.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.))))=)")
(* [comment removed for export] *).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wr_img_b (A : Z) (n : nat) : bool :=
    forallb (fun i => match wview segs (fun _ => None) (wa (A + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 n).

  #[using="Type"] Lemma wr_at_img : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "Pm,P,(2.&40.)(7.(2.&8.))PA,$0.Pn,$23.P,(9.$:.(24.R2.R1.)$<.)P,(3.=R3.)P,(3.(25.R4.(26.R3.))(27.+2.+40.))(28.Vsegs,R6.R5.(26.R4.))")
(* [comment removed for export] *).
  Proof.
    intros m A n WB HA HB. split; [lia|]. split; [lia|]. intros i Hi.
    unfold wr_img_b in WB. rewrite forallb_forall in WB.
    specialize (WB (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in WB by lia.
    unfold wview in *. destruct (m (wa (A + i))); [discriminate|]. cbn in WB. intros E. rewrite E in WB. discriminate WB.
  Qed.

  #[using="Type"] Lemma rw_cells_img : ltac2:(CDefT.buildp (gd_tbl_EcpPkGlue ()) "PL,$29.Pm,P,(2.&40.)(7.(2.&8.))PA,$0.Pbs,(2:.(2.&8.))P,(2;.Vsegs,R4.R3.)P,(2<.R5.R3.(26.(2=.(2.&8.)R2.)))P,(9.$:.(2>.Vsegs,R4.R3.)$<.)P,(9.$:.(24.R5.(2=.(2.&8.)R4.))$<.)P,(3.(25.R6.(26.(2=.(2.&8.)R5.)))(27.+2.+40.))(2?.Vsegs,R8.R7.(30.$31.(32.(2=.(2.&8.)R6.)R6.)(33.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros L m A bs SOK CA IB WB HB. pose proof (statics_ok_cells segs L m A bs SOK CA IB) as RO.
    split; [exact RO|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. apply wr_at_img; [exact WB| destruct CA as (C1 & _); destruct SOK as (S0 & _); lia| exact HB].
  Qed.
End Groups.
