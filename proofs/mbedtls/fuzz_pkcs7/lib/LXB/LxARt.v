(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Cells Step CellsX Frame PropExec Asn1Aux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow AEvtA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxDenot LxTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxARt () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hm_writable"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_opq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "WithR.HMQ"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lawcli"; "WithR.LAWt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.min"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lawobj"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.cshd"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "WithR.pres_wr"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.shadow_free"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "WithR.drop_empty"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"].


Section WithR.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Local Notation L := (arl_L R).
  Local Notation AL := (arl_AL R).
  Variable HIA : artA asegs R.

  (* [comment removed for export] *)
  Lemma lx_opq_HM : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PCS,P,$0.SpPh,(1.$2.VR,VHIA,)PLB,(3.$4.)PLF,(3.$4.)POK,(3.(5.$0.$0.))PSH,(3.(5.$0.$0.))Pm,P,(6.&40.)(7.(6.&8.))P,(8.$2.VR,VHIA,R6.R5.R4.R1.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(?.VR,R9.R8.(10.$2.VR,VHIA,R:.)R2.)R4.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pc,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(11.(:.(;.(12.VR,)R2.)(=.R2.(10.$2.VR,VHIA,R;.)))(13.R9.R2.))R4.)(14.$2.(15.VR,)R:.Lm,P,(6.&40.)(7.(6.&8.))(8.$2.VR,VHIA,R:.R9.R8.R1.)R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros CS h LB LF OK SH m HH HOK HSH.
    apply (lx_opq_intro asegs AL CS (fun m => HM asegs R HIA h LB LF m) (hm_writable R LB LF (htop asegs R HIA h))).
    - exact HH.
    - intros W m1 m2 H1 MU WM HW. exact (hm_munch asegs R HIA h LB LF W m1 m2 H1 MU WM HW).
    - intros lo hi a HIn Ha. rewrite Forall_forall in HOK. exact (HOK (lo, hi) HIn a Ha).
    - intros lo hi c HIn Hc HCS. rewrite Forall_forall in HSH. right. exists c. split; [exact (HSH (lo, hi) HIn c Hc) | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition HMQ (h : HST asegs R HIA) (LB LF : list blk) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "(16.(1.$2.VR,VHIA,)Lh',(1.$2.VR,VHIA,)(:.(8.$2.VR,VHIA,R1.O3.O2.O1.)(:.(17.P,$0.Sp(18.$2.VR,VHIA,R1.)(18.$2.VR,VHIA,O4.))(:.(17.$0.(10.$2.VR,VHIA,R1.)(10.$2.VR,VHIA,O4.))(:.(17.$0.(19.$2.VR,VHIA,R1.)(19.$2.VR,VHIA,O4.))(:.Pmo,$1:.(1;.(1<.$2.VR,VHIA,R2.R1.)(1<.$2.VR,VHIA,O4.R1.))(:.(17.$0.(1=.$2.VR,VHIA,R1.)(1=.$2.VR,VHIA,O4.))(:.(17.$0.(1>.$2.VR,VHIA,R1.)(1>.$2.VR,VHIA,O4.))(17.$0.(1?.$2.VR,VHIA,R1.)(1?.$2.VR,VHIA,O4.))))))))))")
(* [comment removed for export] *).
  Lemma hmq_intro : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Ph,(1.$2.VR,VHIA,)Ph1,(1.$2.VR,VHIA,)PLB,(3.$4.)PLF,(3.$4.)Pm,P,(6.&40.)(7.(6.&8.))P,(8.$2.VR,VHIA,R4.R3.R2.R1.)P,(17.P,$0.Sp(18.$2.VR,VHIA,R5.)(18.$2.VR,VHIA,R6.))P,(17.$0.(10.$2.VR,VHIA,R6.)(10.$2.VR,VHIA,R7.))P,(17.$0.(19.$2.VR,VHIA,R7.)(19.$2.VR,VHIA,R8.))P,Pmo,$1:.(1;.(1<.$2.VR,VHIA,R9.R1.)(1<.$2.VR,VHIA,R:.R1.))P,(17.$0.(1=.$2.VR,VHIA,R9.)(1=.$2.VR,VHIA,R:.))P,(17.$0.(1>.$2.VR,VHIA,R:.)(1>.$2.VR,VHIA,R;.))P,(17.$0.(1?.$2.VR,VHIA,R;.)(1?.$2.VR,VHIA,R<.))(20.R=.R;.R:.R9.)")
(* [comment removed for export] *).
  Proof. intros. exists h1. repeat split; auto; apply H3. Qed.
  Lemma hmq_of_hm : forall h LB LF m, HM asegs R HIA h LB LF m -> HMQ h LB LF m.
  Proof. intros. exists h. repeat split; auto; tauto. Qed.
  (* [comment removed for export] *)
  Lemma hmq_repin : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Ph,(1.$2.VR,VHIA,)Ph1,(1.$2.VR,VHIA,)PLB,(3.$4.)PLF,(3.$4.)Pm,P,(6.&40.)(7.(6.&8.))P,(20.R4.R3.R2.R1.)P,(17.P,$0.Sp(18.$2.VR,VHIA,R5.)(18.$2.VR,VHIA,R6.))P,(17.$0.(10.$2.VR,VHIA,R6.)(10.$2.VR,VHIA,R7.))P,(17.$0.(19.$2.VR,VHIA,R7.)(19.$2.VR,VHIA,R8.))P,Pmo,$1:.(1;.(1<.$2.VR,VHIA,R9.R1.)(1<.$2.VR,VHIA,R:.R1.))P,(17.$0.(1=.$2.VR,VHIA,R9.)(1=.$2.VR,VHIA,R:.))P,(17.$0.(1>.$2.VR,VHIA,R:.)(1>.$2.VR,VHIA,R;.))P,(17.$0.(1?.$2.VR,VHIA,R;.)(1?.$2.VR,VHIA,R<.))(20.R=.R;.R:.R9.)")
(* [comment removed for export] *).
  Proof.
    intros h h1 LB LF m (h' & HH & E1 & E2 & E3 & E4 & E5 & E6 & E7) P1 P2 P3 P4 P5 P6 P7.
    exists h'. split; [exact HH|]. rewrite E1, E2, E3, E5, E6, E7. repeat split; auto.
    - intros X. apply P4. apply E4. exact X.
    - intros X. apply E4. apply P4. exact X.
  Qed.
  Lemma lx_opq_HMQ : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PCS,P,$0.SpPh,(1.$2.VR,VHIA,)PLB,(3.$4.)PLF,(3.$4.)POK,(3.(5.$0.$0.))PSH,(3.(5.$0.$0.))Pm,P,(6.&40.)(7.(6.&8.))P,(20.R6.R5.R4.R1.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(?.VR,R9.R8.(10.$2.VR,VHIA,R:.)R2.)R4.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pc,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(11.(:.(;.(12.VR,)R2.)(=.R2.(10.$2.VR,VHIA,R;.)))(13.R9.R2.))R4.)(14.$2.(15.VR,)R:.Lm,P,(6.&40.)(7.(6.&8.))(20.R:.R9.R8.R1.)R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros CS h LB LF OK SH m HQ HOK HSH.
    apply (lx_opq_intro asegs AL CS (fun m => HMQ h LB LF m) (hm_writable R LB LF (htop asegs R HIA h))).
    - exact HQ.
    - intros W m1 m2 (h' & H1 & E1 & E2 & E) MU WM HW. exists h'. split; [| exact (conj E1 (conj E2 E))].
      apply (hm_munch asegs R HIA h' LB LF W m1 m2 H1 MU WM). rewrite E2. exact HW.
    - intros lo hi a HIn Ha. rewrite Forall_forall in HOK. exact (HOK (lo, hi) HIn a Ha).
    - intros lo hi c HIn Hc HCS. rewrite Forall_forall in HSH. right. exists c. split; [exact (HSH (lo, hi) HIn c Hc) | reflexivity].
  Qed.


  (* [comment removed for export] *)
  Definition LAWt (LB LF : list blk) (SP TOP : Z) : list (Z * Z) -> mem -> mem -> Prop := ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "LX,(3.(5.$0.$0.))Lm,P,(6.&40.)(7.(6.&8.))Lm',P,(6.&40.)(7.(6.&8.))(21.$2.VR,O4.O3.O2.O2.O1.R3.R2.R1.)")
(* [comment removed for export] *).

  Lemma lawcli_LAWt : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLB,(3.$4.)PLF,(3.$4.)PSP,$0.PTOP,$0.Pa,$0.Pn,$0.P,(22.(23.VR,)(24.$4.R6.(25.R5.))R4.R2.R1.)(26.$2.(27.R7.R6.R5.R4.)R3.R2.)")
(* [comment removed for export] *).
  Proof.
    intros LB LF SP TOP a n CR X m1 m2 x [HP _] Hx HR HO. apply HP; [exact HR | apply CR; exact Hx | exact HO].
  Qed.
  (* [comment removed for export] *)
  Lemma client_range_resp : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLBs,(3.$4.)Plo,$0.Psp,$0.Pspv,$0.Pa,$0.Pn,$0.P,(22.(23.VR,)R6.R5.R2.R1.)P,(11.(;.(28.R3.R2.)R6.)(;.R5.R3.))P,(;.R5.R6.)(22.(23.VR,)R9.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros LBs lo sp spv a n CR DS LE x Hx. destruct (CR x Hx) as [X|[X|X]]; [| right; left; exact X | right; right; exact X].
    destruct DS as [D|D]; [exfalso; lia | left; lia].
  Qed.
  Lemma client_range_resp0 : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLBs,(3.$4.)Plo,$0.Psp,$0.Pspv,$0.Pa,$0.Pn,$0.P,(22.(23.VR,)R6.R5.R2.R1.)P,(11.(17.$0.R2.=)(11.(;.(28.R3.R2.)R6.)(;.R5.R3.)))P,(;.R5.R6.)(22.(23.VR,)R9.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros LBs lo sp spv a n CR [D|DS] LE; [intros x Hx; exfalso; lia | eapply client_range_resp; eauto].
  Qed.
  Lemma client_range_above : forall LBs spv a n, spv <= a -> client_range L LBs spv a n.
  Proof. intros LBs spv a n H x Hx. left. lia. Qed.
  Lemma lxr_client_range_blk : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLB,(3.$4.)PLF,(3.(5.$0.$0.))Pspv,$0.PFB,$0.Pn,$0.Pa,$0.Pk,$0.P,(29.(5.$0.$0.)(2:.$0.$0.R4.R3.)R6.)P,(11.(:.(;.R5.R3.)(;.(28.R3.R2.)(28.R5.(2;.+18.R4.))))(:.(;.(28.R5.+20.)R3.)(;.(28.R3.R2.)(28.(28.R5.+20.)(2<.R4.+28.)))))(22.(23.VR,)(24.$4.R9.(25.R8.))R7.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB LF spv FB n a k HIn H x Hx. right; right.
    destruct H as [[H1 H2]|[H1 H2]].
    - exists (FB, Z.min 24 n). split; [apply in_app_iff; right; apply In_fdata_hdr; exact HIn | cbn; lia].
    - exists (FB + 32, n - 40). split; [apply in_app_iff; right; apply In_fdata_dat; exact HIn | cbn; lia].
  Qed.
  Lemma lawobj_LAWt : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PCS,P,$0.SpPLB,(3.$4.)PLF,(3.$4.)PSP,$0.PTOP,$0.Pa,$0.Pn,$0.P,(2=.(15.VR,)R7.)P,(22.(23.VR,)(24.$4.R7.(25.R6.))R5.R3.R2.)P,Px,$0.P,A1.R:.R1.(=.R2.R7.)(2>.$2.(15.VR,)R:.(27.R9.R8.R7.R6.)R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros CS LB LF SP TOP a n OK CR HT X m1 m2 b k HL H1 H2 OB.
    eapply (presA_aobj asegs R CS LB LF SP SP TOP X m1 m2 b k OK HL OB); [| lia | exact HT].
    intros x Hx. apply CR. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma lawcli_LAWt_shadow : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLB,(3.$4.)PLF,(3.$4.)PSP,$0.PTOP,$0.PB,$0.Pn,$0.P,Pc,$0.P,(:.(;.R3.R1.)(=.R1.(28.R3.(2?.+8.R2.))))(30.VR,R8.R7.R6.R5.R2.)P,(17.$0.(31.R3.+8.)=)P,Pc,$0.P,(:.(;.R5.R1.)(=.R1.(28.R5.(2?.+8.R4.))))(:.(;.=(32.(15.VR,)R2.))(=.(32.(15.VR,)R2.)(33.+2.+40.)))(26.$2.(27.R9.R8.R7.R6.)(32.(15.VR,)R5.)R4.)")
(* [comment removed for export] *).
  Proof.
    intros LB LF SP TOP B n HC HB8 HS X m1 m2 x [_ HP] Hx _ _.
    (* [comment removed for export] *)
    set (c := B + 8 * (x - shadow_of AL B)).
    assert (Hc : B <= c < B + 8 * n) by (subst c; lia).
    assert (E : x = shadow_of AL c) by (subst c; unfold shadow_of in *; Z.div_mod_to_equations; lia).
    rewrite E. apply HP; [exact (HC c Hc) | apply HS; exact Hc].
  Qed.

  (* [comment removed for export] *)
  Lemma client_range_lift : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLBF,(3.$4.)PLBF',(3.$4.)Plo,$0.Psp,$0.Pspv,$0.Pa,$0.Pn,$0.P,(22.(23.VR,)R7.R5.R2.R1.)P,Pb,$4.P,(29.$4.R1.R9.)(29.$4.R2.R9.)P,(11.(17.$0.R3.=)(11.(;.(28.R4.R3.)R7.)(;.R6.R4.)))P,(;.R6.R7.)(22.(23.VR,)R:.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros LBF LBF' lo sp spv a n CR SUB DS LE x Hx.
    destruct (CR x Hx) as [X|[X|(b & Hb & Hr)]].
    - destruct DS as [D|[D|D]]; [exfalso; lia | exfalso; lia | left; lia].
    - right; left; exact X.
    - right; right. exists b. split; [apply SUB, Hb | exact Hr].
  Qed.
  Lemma client_range_lift2 : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLBF,(3.$4.)PLBF',(3.$4.)Plo,$0.Psp,$0.Pspv,$0.Pa,$0.Pn,$0.P,(22.(23.VR,)R7.R5.R2.R1.)P,Pb,$4.P,(29.$4.R1.R9.)(29.$4.R2.R9.)P,(11.(;.(28.R4.R3.)R7.)(;.R6.R4.))P,(;.R6.R7.)(22.(23.VR,)R:.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof. intros. eapply client_range_lift; eauto. Qed.
  Lemma lawcli_LAWt_shadow3 : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PLB,(3.$4.)PLF,(3.$4.)PSP,$0.PTOP,$0.PB,$0.Pn,$0.P,Pc,$0.P,(:.(;.R3.R1.)(=.R1.(28.R3.(2?.+8.R2.))))(30.VR,R8.R7.R6.R5.R2.)P,(17.$0.(31.R3.+8.)=)P,Pc,$0.P,(:.(;.R5.R1.)(=.R1.(28.R5.(2?.+8.R4.))))(:.(;.=(32.(15.VR,)R2.))(=.(32.(15.VR,)R2.)(33.+2.+40.)))(26.$2.(27.R9.R8.R7.R6.)(28.(34.R5.+3.)(35.(15.VR,)))R4.)")
(* [comment removed for export] *).
  Proof.
    intros. replace (Z.shiftr B 3 + al_sb AL) with (shadow_of AL B) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
    apply lawcli_LAWt_shadow; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition pres_wr (CS : Z -> Prop) (LB LF : list blk) (SP SSP TOP : Z) (W : list ivl) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "(:.(36.(:.(37.(23.VR,)(24.$4.O7.(25.O6.))O5.O1.)(38.O2.O1.)))Pc,$0.P,(30.VR,O7.O6.O4.O3.R1.)P,A1.O8.R2.(36.(17.$0.O1.(32.(15.VR,)R3.))))")
(* [comment removed for export] *).

  Lemma in_W_not_outside : forall (W : list ivl) lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ outside W a.
  Proof.
    induction W as [|[l h] W IH]; cbn; intros lo hi a HIn Ha; [exact (fun _ => HIn)|].
    intros [N O]. destruct HIn as [E|HIn]; [injection E; intros; subst; lia | exact (IH lo hi a HIn Ha O)].
  Qed.

  Lemma presW_law : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Ph,(1.$2.VR,VHIA,)PLB,(3.$4.)PLF,(3.$4.)PSP,$0.PSSP,$0.PW,(3.$39.)Pm0,P,(6.&40.)(7.(6.&8.))PW',(3.$39.)Pm1,P,(6.&40.)(7.(6.&8.))Pm2,P,(6.&40.)(7.(6.&8.))P,(3:.$2.VR,VHIA,R:.R9.R8.R7.R6.R5.R4.R2.)P,(3;.R4.R3.R2.)P,(3<.$2.R4.R3.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(3=.(18.$2.VR,VHIA,R10.)R?.R>.R=.R<.(19.$2.VR,VHIA,R10.)R;.R2.)R6.)(3:.$2.VR,VHIA,R>.R=.R<.R;.R:.R9.R8.R5.)")
(* [comment removed for export] *).
  Proof.
    intros h LB LF SP SSP W m0 W' m1 m2 (P & C1 & C2 & C3) MU WM HW.
    split; [| split; [exact C1| split; [exact C2| exact C3]]].
    eapply presA_trans; [exact P|].
    assert (KEEP : forall a, 0 <= a < 2^64 ->
              ~ (forall x, In x W' -> forall a', fst x <= a' < snd x -> a <> a') \/ m2 (wa a) = m1 (wa a)).
    { intros a Ha. destruct (outside_dec W' a) as [Y|N].
      - right. apply MU. rewrite wa_unsigned by exact Ha. exact Y.
      - left. intros K. destruct (not_outside_in W' a N) as (lo & hi & HIn & Hr). exact (K (lo, hi) HIn a Hr eq_refl). }
    rewrite Forall_forall in HW.
    split.
    - intros a Ha Hc Ho. split; [| apply WM].
      destruct (KEEP a Ha) as [K|E]; [| exact E]. exfalso. apply K. intros x HIn a' Ha' ->.
      destruct x as [lo hi]. exact (proj1 (HW (lo, hi) HIn a' Ha') (conj Hc Ho)).
    - intros c Hc Hr. split; [| apply WM].
      destruct (KEEP (shadow_of AL c) Hr) as [K|E]; [| exact E]. exfalso. apply K. intros x HIn a' Ha' E.
      destruct x as [lo hi]. exact (proj2 (HW (lo, hi) HIn a' Ha') c Hc (C1 c Hc) (eq_sym E)).
  Qed.

  Lemma same_shadow_granule : forall c c', shadow_of AL c = shadow_of AL c' -> c - c mod 8 <= c' < c - c mod 8 + 8.
  Proof.
    intros c c' E. unfold shadow_of in E.
    pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.div_mod c' 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c' 8 ltac:(lia)). lia.
  Qed.

  Lemma granule_inside : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Plo,$0.Phi,$0.Pc,$0.P,(17.$0.(31.R3.+8.)=)P,(17.$0.(31.R3.+8.)=)P,(:.(;.R5.R3.)(=.R3.R4.))(:.(;.R6.(2<.R4.(31.R4.+8.)))(;.(28.(2<.R4.(31.R4.+8.))+8.)R5.))")
(* [comment removed for export] *).
  Proof.
    intros lo hi c A0 A1 Hc.
    pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)).
    pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)).
    assert (lo / 8 <= c / 8) by (apply Z.div_le_mono; lia).
    assert (c / 8 < hi / 8) by (apply Z.div_lt_upper_bound; lia).
    lia.
  Qed.


  (* [comment removed for export] *)
  Lemma lx_opq_presW : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Ph,(1.$2.VR,VHIA,)PLB,(3.$4.)PLF,(3.$4.)PSP,$0.PSSP,$0.PW,(3.$39.)Pm0,P,(6.&40.)(7.(6.&8.))POK,(3.(5.$0.$0.))PSH,(3.(5.$0.$0.))Pm,P,(6.&40.)(7.(6.&8.))P,(3:.$2.VR,VHIA,R:.R9.R8.R7.R6.R5.R4.R1.)P,(;.(3>.(23.VR,))R8.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)(:.(3?.VR,R<.R;.R:.R8.(<.$0.$0.R1.)(2<.(>.$0.$0.R1.)(<.$0.$0.R1.)))(40.(18.$2.VR,VHIA,R=.)(<.$0.$0.R1.)(2<.(>.$0.$0.R1.)(<.$0.$0.R1.))))R5.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)(:.(17.$0.(31.(<.$0.$0.R1.)+8.)=)(:.(17.$0.(31.(>.$0.$0.R1.)+8.)=)(:.(40.(18.$2.VR,VHIA,R>.)(<.$0.$0.R1.)(2<.(>.$0.$0.R1.)(<.$0.$0.R1.)))(41.VR,R=.R<.R:.(19.$2.VR,VHIA,R>.)(<.$0.$0.R1.)(2<.(>.$0.$0.R1.)(<.$0.$0.R1.))))))R5.)(14.$2.(15.VR,)(18.$2.VR,VHIA,R>.)Lm,P,(6.&40.)(7.(6.&8.))(3:.$2.VR,VHIA,R?.R>.R=.R<.R;.R:.R9.R1.)R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros h LB LF SP SSP W m0 OK SH m HP HSP HOK HSH.
    pose proof (hcs_ok asegs R HIA h) as OKcs. destruct OKcs as (OK1 & _ & _ & _).
    pose proof HP as HP'. destruct HP' as (_ & C1 & C2 & C3).
    apply (lx_opq_intro asegs AL (hcs asegs R HIA h) _ (pres_wr (hcs asegs R HIA h) LB LF SP SSP (hstkhi asegs R HIA h) W)).
    - exact HP.
    - intros W' m1 m2 H1 MU WM HW. exact (presW_law h LB LF SP SSP W m0 W' m1 m2 H1 MU WM HW).
    - intros lo hi a HIn Ha. rewrite Forall_forall in HOK. destruct (HOK (lo, hi) HIn) as [WC CR]; cbn [fst snd] in WC, CR.
      split.
      + intros [Hc Ho]. exact (WC a ltac:(lia) Hc Ho).
      + intros c Hc HCS E. pose proof (CR a ltac:(lia)) as HA. destruct (OK1 c HCS) as (_ & _ & _ & NCS). apply NCS. subst a. exact HA.
    - intros lo hi c HIn Hc HCS. rewrite Forall_forall in HSH. destruct (HSH (lo, hi) HIn) as (A0 & A1 & CR & SF); cbn [fst snd] in A0, A1, CR, SF.
      destruct (OK1 c HCS) as (Rc & S0 & S1 & NCS).
      pose proof (hcs_shadow_band asegs R HIA h c HCS) as HB.
      split.
      + intros [Hca _]. destruct Hca as [Hs | [[Hd _] | Hb]].
        * lia.
        * lia.
        * destruct Hb as ([B j] & HBin & Hr). cbn [fst snd] in Hr. apply NCS. exact (C2 B j HBin (shadow_of AL c) Hr).
      + intros c' Hc' HCS' E.
        pose proof (same_shadow_granule c c' E) as G. pose proof (granule_inside lo hi c A0 A1 Hc) as [G1 G2].
        exact (SF c' Hc' ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma disjoint1_of_pointwise : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PW,(3.$39.)Px,$0.P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(36.(17.$0.R2.R4.))R2.)(42.R3.R2.+1.)")
(* [comment removed for export] *).
  Proof.
    induction W as [|[lo hi] W IH]; cbn; intros x HW; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [Hy HW']. cbn [fst snd] in Hy. split; [| exact (IH x HW')].
    destruct (Z_lt_le_dec x lo); [lia|]. destruct (Z_lt_le_dec x hi); [| lia]. exfalso. exact (Hy x ltac:(lia) eq_refl).
  Qed.

  Lemma lx_opq_sshad : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PCS,P,$0.SpPlo,$0.Phi,$0.POK,(3.(5.$0.$0.))PSH,(3.(5.$0.$0.))Pm,P,(6.&40.)(7.(6.&8.))P,(43.$2.(15.VR,)R1.R5.R4.)P,(2=.(15.VR,)R7.)P,(40.R8.R7.(2<.R6.R7.))P,(9.(5.$0.$0.)Liv,(5.$0.$0.)(40.R:.(<.$0.$0.R1.)(2<.(>.$0.$0.R1.)(<.$0.$0.R1.)))R6.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)(11.(;.(>.$0.$0.R1.)R:.)(;.R9.(<.$0.$0.R1.)))R6.)(14.$2.(15.VR,)R;.Lm,P,(6.&40.)(7.(6.&8.))(43.$2.(15.VR,)R1.R;.R:.)R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros CS lo hi OK SH m SS OKcs CR HOK HSH. destruct OKcs as (OK1 & _ & _ & _).
    apply (lx_opq_intro asegs AL CS _ (fun a => forall g, lo <= g -> g + 8 <= hi -> g mod 8 = 0 -> a <> shadow_of AL g)).
    - exact SS.
    - intros W' m1 m2 (S0 & S1 & H1) MU WM HW. split; [exact S0|]. split; [exact S1|].
      intros g G1 G2 G3. eapply rw_cells_transport; [exact (H1 g G1 G2 G3) | exact MU | exact WM |].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. apply disjoint1_of_pointwise.
      eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hiv a Ha. exact (Hiv a Ha g G1 G2 G3).
    - intros lo' hi' a HIn Ha g G1 G2 G3 E. rewrite Forall_forall in HOK. pose proof (HOK (lo', hi') HIn a ltac:(cbn; lia)) as HA.
      destruct (OK1 g (CR g ltac:(lia))) as (_ & _ & _ & NCS). apply NCS. rewrite <- E. exact HA.
    - intros lo' hi' c HIn Hc HCS g G1 G2 G3 E. rewrite Forall_forall in HSH. pose proof (HSH (lo', hi') HIn) as D; cbn [fst snd] in D.
      pose proof (same_shadow_granule g c (eq_sym E)) as G. rewrite G3 in G. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lx_opq_aobj : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PCS,P,$0.SpPA,$0.Pn,$0.POK,(3.(5.$0.$0.))PSH,(3.(5.$0.$0.))Pm,P,(6.&40.)(7.(6.&8.))P,(44.$2.(15.VR,)R6.R1.R5.R4.)P,(2=.(15.VR,)R7.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)(40.R9.(<.$0.$0.R1.)(2<.(>.$0.$0.R1.)(<.$0.$0.R1.)))R5.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)(:.(17.$0.(31.(<.$0.$0.R1.)+8.)=)(:.(17.$0.(31.(>.$0.$0.R1.)+8.)=)(11.(17.$0.R8.=)(11.(;.(>.$0.$0.R1.)R9.)(;.(28.R9.R8.)(<.$0.$0.R1.))))))R5.)(14.$2.(15.VR,)R:.Lm,P,(6.&40.)(7.(6.&8.))(44.$2.(15.VR,)R;.R1.R:.R9.)R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros CS A n OK SH m OB OKcs HOK HSH. pose proof OKcs as OKcs'. destruct OKcs' as (OK1 & _ & _ & _).
    destruct OB as [CR SO].
    apply (lx_opq_intro asegs AL CS _ (fun a => forall a', A <= a' < A + n -> a <> shadow_of AL a')).
    - split; assumption.
    - intros W' m1 m2 [CR1 SO1] MU WM HW. split; [exact CR1|].
      intros a' Ha'. destruct (SO1 a' Ha') as (k & Bk & Vk). exists k. split; [| exact Vk].
      eapply bytes_at_transport0; [exact Bk | exact MU |]. right. cbn [length Z.of_nat Pos.of_succ_nat].
      apply disjoint1_of_pointwise. eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hiv a Ha. exact (Hiv a Ha a' Ha').
    - intros lo hi a HIn Ha a' Ha' E. rewrite Forall_forall in HOK. pose proof (HOK (lo, hi) HIn a ltac:(cbn; lia)) as HA.
      destruct (OK1 a' (CR a' Ha')) as (_ & _ & _ & NCS). apply NCS. rewrite <- E. exact HA.
    - intros lo hi c HIn Hc HCS a' Ha' E. rewrite Forall_forall in HSH. destruct (HSH (lo, hi) HIn) as (A0 & A1 & D); cbn [fst snd] in A0, A1, D.
      pose proof (same_shadow_granule c a' E) as G. pose proof (granule_inside lo hi c A0 A1 Hc) as [G1 G2]. lia.
  Qed.

  (* [comment removed for export] *)
  Fixpoint drop_empty (W : list ivl) : list ivl :=
    match W with
    | nil => nil
    | (lo, hi) :: W' => if Z.ltb lo hi then (lo, hi) :: drop_empty W' else drop_empty W'
    end.
  Lemma outside_drop_empty : forall (W : list ivl) x, outside (drop_empty W) x -> outside W x.
  Proof.
    induction W as [|[lo hi] W IH]; cbn; intros x Hx; [exact I|].
    destruct (Z.ltb_spec lo hi); cbn in Hx; [destruct Hx as [H1 H2]; split; [exact H1 | exact (IH x H2)] | split; [lia | exact (IH x Hx)]].
  Qed.
  Lemma munch_drop_empty : forall (W : list ivl) m1 m2, munch W m1 m2 -> munch (drop_empty W) m1 m2.
  Proof. intros W m1 m2 MU x Hx. apply MU. apply outside_drop_empty. exact Hx. Qed.

  Lemma disjoint_from_pw : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PW,(3.$39.)PA,$0.Pn,$0.P,(=.=R1.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(36.(:.(;.R6.R2.)(=.R2.(28.R6.R5.))))R4.)(42.(45.R5.)R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros W A n Hn HW. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [fst snd] in H1.
    destruct (Z.ltb_spec lo hi); cbn; [| exact (IH HW)].
    split; [| exact (IH HW)].
    destruct (Z_lt_le_dec lo (A + n)); [| lia]. destruct (Z_lt_le_dec A hi); [| lia]. exfalso.
    exact (H1 (Z.max lo A) ltac:(lia) ltac:(lia)).
  Qed.

  Lemma rw_cells_transport_pw : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PW,(3.$39.)Pm1,P,(6.&40.)(7.(6.&8.))Pm2,P,(6.&40.)(7.(6.&8.))PA,$0.Pcs,(3.$46.)P,(47.$2.R4.R2.R1.)P,(3;.R6.R5.R4.)P,(3<.$2.R6.R5.)P,(=.=(48.(49.R4.)))P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(36.(:.(;.R9.R2.)(=.R2.(28.R9.(48.(49.R8.))))))R9.)(47.$2.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros W m1 m2 A cs H MU WM Hn HW.
    eapply rw_cells_transport; [exact H | exact (munch_drop_empty W m1 m2 MU) | exact WM |].
    apply disjoint_from_pw; assumption.
  Qed.

  Lemma lx_opq_shchunk : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PCS,P,$0.SpPX,$0.Pcs,(3.$46.)POK,(3.(5.$0.$0.))Pm,P,(6.&40.)(7.(6.&8.))P,(47.$2.R1.(28.(34.R4.+3.)(35.(15.VR,)))R3.)P,(2=.(15.VR,)R6.)P,(17.$0.(31.R6.+8.)=)P,(=.=(48.(49.R6.)))P,(40.R9.R8.(2?.+8.(48.(49.R7.))))P,(9.(5.$0.$0.)Liv,(5.$0.$0.)(40.R;.(<.$0.$0.R1.)(2<.(>.$0.$0.R1.)(<.$0.$0.R1.)))R7.)(14.$2.(15.VR,)R;.Lm,P,(6.&40.)(7.(6.&8.))(47.$2.R1.(28.(34.R;.+3.)(35.(15.VR,)))R:.)R8.(4:.$39.)R7.)")
(* [comment removed for export] *).
  Proof.
    intros CS X cs OK m H OKcs AX Hn CR HOK. destruct OKcs as (OK1 & _ & _ & _).
    apply (lx_opq_intro asegs AL CS _ (fun a => forall c, X <= c < X + 8 * Z.of_nat (cells_size cs) -> a <> shadow_of AL c)).
    - exact H.
    - intros W' m1 m2 H1 MU WM HW. eapply rw_cells_transport_pw; [exact H1 | exact MU | exact WM | exact Hn |].
      eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hiv a Ha [G1 G2].
      apply (Hiv a Ha (X + 8 * (a - (Z.shiftr X 3 + al_sb AL)))); [lia|].
      unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      rewrite Z.shiftr_div_pow2 in G1, G2 by lia. change (2 ^ 3) with 8 in G1, G2.
      rewrite Z.mul_comm, Z.div_add by lia. lia.
    - intros lo hi a HIn Ha c Hc E. rewrite Forall_forall in HOK. pose proof (HOK (lo, hi) HIn a ltac:(cbn; lia)) as HA.
      destruct (OK1 c (CR c Hc)) as (_ & _ & _ & NCS). apply NCS. rewrite <- E. exact HA.
    - intros lo hi c HIn. destruct HIn.
  Qed.



End WithR.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma outside_of_pw : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "PW,(3.$39.)PA,$0.Pn,$0.Px,$0.P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(11.(=.R2.R6.)(;.(28.R6.R5.)R2.))R4.)P,(:.(;.R4.R2.)(=.R2.(28.R4.R3.)))(38.R6.R3.)")
(* [comment removed for export] *).
Proof.
  intros W A n x HW Hx. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
  apply Forall_cons_iff in HW. destruct HW as [H1 H2]. split; [| apply IH; exact H2].
  intros Hin. cbn in H1. specialize (H1 x Hin). lia.
Qed.
Lemma bytes_at_transport_pw : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Psegs,(3.$4;.)PW,(3.$39.)Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))PA,$0.Pbs,(3.(6.&8.))P,(4<.R6.R4.R2.R1.)P,(3;.R6.R5.R4.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(11.(=.R2.R7.)(;.(28.R7.(48.(4=.(6.&8.)R6.)))R2.))R7.)(4<.R9.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs W m m' A bs (Ha & Hl & H) Hm HW. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm; [apply H; exact Hi|].
  rewrite wa_unsigned by lia. eapply outside_of_pw; [exact HW | lia].
Qed.

(* [comment removed for export] *)
Lemma lx_opq_bytes : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Psegs,(3.$4;.)PAL,$4>.PCS,P,$0.SpPA,$0.Pbs,(3.(6.&8.))POK,(3.$39.)Pm,P,(6.&40.)(7.(6.&8.))P,(4<.R7.R1.R4.R3.)P,(9.(5.$0.$0.)Liv,(5.$0.$0.)Pa,$0.P,(:.(;.(<.$0.$0.R2.)R1.)(=.R1.(>.$0.$0.R2.)))(11.(=.R2.R8.)(;.(28.R8.(48.(4=.(6.&8.)R7.)))R2.))R3.)(14.R9.R8.R7.Lm,P,(6.&40.)(7.(6.&8.))(4<.R:.R1.R7.R6.)R4.(4:.$39.)R3.)")
(* [comment removed for export] *).
Proof.
  intros segs AL CS A bs OK m HB HOK.
  apply (lx_opq_intro segs AL CS (fun m => bytes_at segs m A bs) (fun a => a < A \/ A + Z.of_nat (length bs) <= a) OK [] m HB).
  - intros W m1 m2 H1 MU _ HW. eapply bytes_at_transport_pw; eauto.
  - intros lo hi a HIn Ha. rewrite Forall_forall in HOK. exact (HOK (lo, hi) HIn a Ha).
  - intros lo hi c HIn. destruct HIn.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxr_cur_mem := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end.

(* [comment removed for export] *)
Ltac lxr_cw_list L acc :=
  match goal with
  | H : client_wrange L _ _ _ ?A ?n |- _ =>
      lazymatch acc with
      | context [(A, A + n)] => fail
      | _ => lxr_cw_list L ((A, A + n) :: acc)
      end
  | _ => acc
  end.
(* [comment removed for export] *)
Ltac lxr_sf_list R acc :=
  match goal with
  | H : shadow_free R _ _ _ _ ?A ?n |- _ =>
      lazymatch acc with
      | context [(A, A + n)] => fail
      | _ => lxr_sf_list R ((A, A + n) :: acc)
      end
  | _ => acc
  end.

Ltac lxr_cr_list CS acc :=
  match goal with
  | H : crange CS ?A ?n |- _ =>
      lazymatch acc with context [(A, A + n)] => fail | _ => lxr_cr_list CS ((A, A + n) :: acc) end
  | H : aobj _ _ CS _ ?A ?n |- _ =>
      lazymatch acc with context [(A, A + n)] => fail | _ => lxr_cr_list CS ((A, A + n) :: acc) end
  | _ => acc
  end.
(* [comment removed for export] *)
Ltac lxr_in_block :=
  (* [comment removed for export] *)
  let c := fresh "c" in let Hc := fresh "Hc" in
  intros c Hc;
  try match goal with E : htop ?sg ?R ?HIA _ = htop ?sg ?R ?HIA _ |- _ => rewrite E end;
  first [ match goal with W : forall x, _ -> _ \/ in_block _ x |- _ => exact (W c Hc) end
                     | match goal with W : forall x, _ -> _ \/ in_block _ x |- _ => apply W; lia end
                     | right; eexists; split; [ left; reflexivity | cbn [fst snd]; lia ]
                     | right; eexists; split; [ right; left; reflexivity | cbn [fst snd]; lia ]
                     | left; lia ].
Tactic Notation "lxr_forall" tactic3(tac) := repeat (apply Forall_cons; [ cbn [fst snd]; tac | ]); apply Forall_nil.
(* [comment removed for export] *)
Ltac lx_lia1 :=
  first [ clear_disj; lia
        | match goal with
          | H : _ \/ _ |- _ => solve [ generalize H; clear_disj; let HH := fresh in intros HH; decompose [or and] HH; subst; lia ]
          end ].
Ltac lxr_lia := clear_mods; lx_prune; lx_lia1.

(* [comment removed for export] *)
Definition lxr_okw (P : Prop) : Prop := P.
Ltac lxr_filter cands P tac k :=
  lazymatch cands with
  | nil => k constr:(@nil ivl)
  | cons (?lo, ?hi) ?rest =>
      let T := P lo hi in
      (* [comment removed for export] *)
      tryif (first [ lazymatch goal with W : lxr_okw T |- _ => idtac end
                   | let H := fresh "OKW" in assert (H : lxr_okw T) by (unfold lxr_okw; tac) ])
      then lxr_filter rest P tac ltac:(fun l => k constr:(cons (lo, hi) l))
      else lxr_filter rest P tac k
  | cons ?x ?rest => lxr_filter rest P tac k
  end.
Ltac lxr_by_okw := cbn [fst snd]; match goal with W : lxr_okw ?T |- _ => exact W end.
Ltac lxr_clear_okw := idtac.   (* [comment removed for export] *)
Ltac lxr_forall_okw := lxr_forall (idtac; first [ lxr_by_okw | assumption ]).

(* [comment removed for export] *)
Ltac lxr_in_list acc :=
  match goal with
  | H : In (?A, ?n) (_ ++ fdata _) |- _ =>
      lazymatch acc with
      | context [(A, A + n)] => fail
      | _ => lxr_in_list ((A, A + n) :: acc)
      end
  | _ => acc
  end.
(* [comment removed for export] *)
Ltac lxr_crfb_list acc :=
  match goal with
  | H : crange _ ?A ?n, I : In (?A, ?n) _ |- _ =>
      lazymatch acc with
      | context [(A, A + n)] => fail
      | _ => lxr_crfb_list ((A, A + n) :: acc)
      end
  | _ => acc
  end.

(* [comment removed for export] *)
Ltac lxr_goal_cs := lazymatch goal with |- evtA _ _ ?CS _ _ => CS | |- aevtA _ ?K _ _ => lazymatch goal with _ : kinv_laws _ ?CS K |- _ => CS end end.
Ltac lxr_goal_al := lazymatch goal with |- evtA _ ?AL _ _ _ => AL | |- aevtA _ ?K _ _ => lazymatch goal with _ : kinv_laws ?AI _ K, _ : ainv_laws ?AL ?AI |- _ => AL end end.
Ltac lxr_goal_segs := lazymatch goal with |- evtA ?sg _ _ _ _ => sg | |- aevtA ?sg _ _ _ => sg end.

(* [comment removed for export] *)
Ltac lxr_pose_HM :=
  let mx := lxr_cur_mem in
  lazymatch goal with
  | HH : HM ?segs ?R ?HIA ?h ?LB ?LF mx |- _ =>
      let AL := lxr_goal_al in let CS := lxr_goal_cs in
      let L := constr:(arl_L R) in
      let TOP := constr:(htop segs R HIA h) in
      let cands := lxr_cw_list L constr:([(arl_stklo R, htop segs R HIA h)] : list ivl) in
      let cands := lxr_in_list cands in
      let shc := lxr_sf_list R constr:(@nil ivl) in
      let shc := lxr_crfb_list shc in
      (* [comment removed for export] *)
      lxr_filter cands ltac:(fun lo hi => constr:(forall a, lo <= a < hi -> hm_writable R LB LF TOP a))
        ltac:(first [ apply w_writable_of_client_wrange; solve_client_wrange
                    | try match goal with E : htop ?sg ?R' ?HIA' _ = htop ?sg ?R' ?HIA' _ |- _ => rewrite E end;
                      first [ apply w_writable_of_client_wrange; solve_client_wrange
                            | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left; left; lxr_lia
                            | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left; right; right;
                              match goal with I : In (?A0, ?n0) _ |- _ => exists (A0, n0); split; [ exact I | cbn [fst snd]; lxr_lia ] end ] ])
        ltac:(fun ok =>
          lxr_filter shc ltac:(fun lo hi => constr:(forall c, lo <= c < hi -> arl_stklo R <= c < TOP \/ in_block LF c))
            ltac:(idtac; lxr_in_block)
            ltac:(fun sh =>
              let H := fresh "OQH" in
              assert (H : lx_opq segs AL CS (fun m => HM segs R HIA h LB LF m) ok sh mx);
              [ apply (lx_opq_HM R HIA CS h LB LF ok sh mx HH); [ lxr_forall_okw | lxr_forall_okw ] | ]));
      lxr_clear_okw
  end.

(* [comment removed for export] *)
Ltac lxr_pose_presW :=
  let mx := lxr_cur_mem in
  repeat match goal with
  | HP : presW ?segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m0 mx |- _ =>
      let AL := lxr_goal_al in let CS := lxr_goal_cs in
      lazymatch goal with
      | _ : lx_opq _ _ _ (fun m => presW segs R HIA h LB LF SP SSP W m0 m) _ _ mx |- _ => fail
      | |- _ => idtac
      end;
      let L := constr:(arl_L R) in
      let CSh := constr:(hcs segs R HIA h) in
      let SHI := constr:(hstkhi segs R HIA h) in
      let cands := lxr_cw_list L constr:([(arl_stklo R, SP)] : list ivl) in
      let cands := lxr_in_list cands in
      let shc := lxr_sf_list R constr:(@nil ivl) in
      let shc := lxr_crfb_list shc in
      lxr_filter cands ltac:(fun lo hi => constr:(wcover R LB LF SP W lo (hi - lo) /\ crange CSh lo (hi - lo)))
        ltac:(split; [ solve_wcover | solve_crange ])
        ltac:(fun ok =>
          lxr_filter shc ltac:(fun lo hi => constr:(lo mod 8 = 0 /\ hi mod 8 = 0 /\ crange CSh lo (hi - lo) /\ shadow_free R LB LF SSP SHI lo (hi - lo)))
            ltac:(split; [ lxr_lia | split; [ lxr_lia | split; [ solve_crange
                    | first [ assumption | eapply shadow_free_sub; [ eassumption | lxr_lia | lxr_lia ]
                            | eapply shadow_free_of_fresh'; [ eassumption | eassumption | eassumption | lxr_lia | lxr_lia | lxr_lia ]
                            (* [comment removed for export] *)
                            | eapply shadow_free_fresh; [ eassumption | destruct HP as (_ & _ & _ & K); exact K | lxr_lia | lxr_lia | lxr_lia
                                                        | first [ assumption | eapply hm_fresh_frame_apart; eassumption ] ] ] ] ] ])
            ltac:(fun sh =>
              let H := fresh "OQP" in
              assert (H : lx_opq segs AL CS (fun m => presW segs R HIA h LB LF SP SSP W m0 m) ok sh mx);
              [ apply (lx_opq_presW R HIA h LB LF SP SSP W m0 ok sh mx HP); [ lxr_lia | lxr_forall_okw | lxr_forall_okw ] | ]));
      lxr_clear_okw
  end.

(* [comment removed for export] *)
Ltac lxr_pose_sshad1 SS :=
  let mx := lxr_cur_mem in
  lazymatch type of SS with
  | sshad ?segs ?AL mx ?lo ?hi =>
    lazymatch goal with
    | OK : cs_ok AL ?CS, R : art_layout |- _ =>
      let cands := lxr_cr_list CS constr:(@nil ivl) in
      let shc := lxr_sf_list R constr:(@nil ivl) in
      let shc := lxr_crfb_list shc in
      lxr_filter cands ltac:(fun a b => constr:(crange CS a (b - a))) ltac:(idtac; solve_crange)
        ltac:(fun ok =>
          lxr_filter shc ltac:(fun a b => constr:(b <= lo \/ hi <= a)) ltac:(idtac; lxr_lia)
            ltac:(fun sh =>
              let H := fresh "OQS" in
              assert (H : lx_opq segs AL CS (fun m => sshad segs AL m lo hi) ok sh mx);
              [ apply (lx_opq_sshad R CS lo hi ok sh mx SS OK); [ solve_crange | lxr_forall_okw | lxr_forall_okw ] | ]));
      lxr_clear_okw
    end
  end.
Ltac lxr_pose_sshad :=
  let mx := lxr_cur_mem in
  repeat match goal with
  | SS : sshad ?segs ?AL mx ?lo ?hi |- _ =>
      lazymatch goal with
      | _ : lx_opq _ _ _ (fun m => sshad _ _ m lo hi) _ _ mx |- _ => fail
      | _ => lxr_pose_sshad1 SS
      end
  end.

(* [comment removed for export] *)
Ltac lxr_pose_sh :=
  let mx := lxr_cur_mem in
  repeat match goal with
  | FS : rw_cells ?segs mx (Z.shiftr ?X 3 + al_sb ?AL) ?cs, OK : cs_ok ?AL ?CS |- _ =>
      let ok := lxr_cr_list CS constr:(@nil ivl) in
      let H := fresh "OQSH" in
      assert (H : lx_opq segs AL CS (fun m => rw_cells segs m (Z.shiftr X 3 + al_sb AL) cs) ok [] mx);
      [ apply (lx_opq_shchunk _ CS X cs ok mx FS OK);
        [ clear_disj; lia
        | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia
        | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul Pos.mul]; solve_crange
        | lxr_forall (idtac; solve_crange) ]
      | clear FS ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lx_lbeq {A : Type} (x y : A) : Prop := x = y.
(* [comment removed for export] *)
Ltac lxr_abs1 t := let x := fresh "lxBL" in let E := fresh "lxEBL" in set (x := t) in *; pose proof (eq_refl x : lx_lbeq x t) as E.
Ltac lxr_abs_lists :=
  let mx := lxr_cur_mem in
  repeat match goal with
  | H : HM _ _ _ _ ?LB _ mx |- _ => lazymatch LB with context [_ ++ _] => lxr_abs1 LB end
  | H : HM _ _ _ _ _ ?LF mx |- _ => lazymatch LF with context [_ ++ _] => lxr_abs1 LF end
  | H : HMQ _ _ _ ?LB _ mx |- _ => lazymatch LB with context [_ ++ _] => lxr_abs1 LB end
  | H : HMQ _ _ _ _ ?LF mx |- _ => lazymatch LF with context [_ ++ _] => lxr_abs1 LF end
  | H : presW _ _ _ _ ?LB _ _ _ _ _ mx |- _ => lazymatch LB with context [_ ++ _] => lxr_abs1 LB end
  | H : presW _ _ _ _ _ ?LF _ _ _ _ mx |- _ => lazymatch LF with context [_ ++ _] => lxr_abs1 LF end
  | H : presW _ _ _ _ _ _ _ _ ?W _ mx |- _ => lazymatch W with context [_ ++ _] => lxr_abs1 W end
  end.
Ltac lxr_unabs_lists := repeat match goal with E : lx_lbeq ?x _ |- _ => clear E; cbv delta [x] in *; try clear x end.
(* [comment removed for export] *)
Ltac lxr_pose := lx_pins_hook; lxr_abs_lists; try lxr_pose_HM; try lxr_pose_presW; try lxr_pose_sshad.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_opqa :=
  lazymatch goal with
  | |- ?P ?mx => match goal with H : lx_opq _ _ _ ?Q _ _ mx |- _ => exact (lx_opq_holds _ _ _ _ _ _ _ H) end
  end.
Ltac lx_eassumption := first [ eassumption | lx_opqa ].

(* [comment removed for export] *)
Ltac lx_mkR :=
  lazymatch goal with
  | |- context [MS ?R _ _ _ _ _ _] =>
    lazymatch R with
    | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
         (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
         (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) =>
      change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    end
  end.

(* [comment removed for export] *)
Ltac lxr_replace H0 T H := clear H0; assert (H0 : T) by exact (lx_opq_holds _ _ _ _ _ _ _ H); clear H.
Ltac lxr_unpack :=
  let mx := lxr_cur_mem in
  repeat match goal with
  | H : lx_opq _ _ _ ?P _ _ ?my |- _ =>
      lazymatch my with
      | mx => let T := eval cbv beta in (P mx) in
              first [ lazymatch T with
                      (* [comment removed for export] *)
                      | HMQ ?R ?HIA ?h ?LB ?LF _ =>
                          let N := fresh "HQ" in assert (N : T) by exact (lx_opq_holds _ _ _ _ _ _ _ H); clear H;
                          let hq := fresh "hq" in let HHq := fresh "HHq" in
                          destruct N as (hq & HHq & ?EQcs & ?EQtop & ?EQstk & ?EQhk & ?EQfl & ?EQvol & ?EQfr)
                      | HM ?sg ?R ?HIA ?h ?LB ?LF _ => match goal with H0 : HM sg R HIA h LB LF _ |- _ => lxr_replace H0 T H end
                      | presW ?sg ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m0 _ => match goal with H0 : presW sg R HIA h LB LF SP SSP W m0 _ |- _ => lxr_replace H0 T H end
                      | sshad ?sg ?al _ ?lo ?hi => match goal with H0 : sshad sg al _ lo hi |- _ => lxr_replace H0 T H end
                      | aobj ?sg ?al ?cs _ ?A ?n => match goal with H0 : aobj sg al cs _ A n |- _ => lxr_replace H0 T H end
                      | rw_cells ?sg _ ?a ?cs => match goal with H0 : rw_cells sg _ a _ |- _ => lxr_replace H0 T H end
                      end
                    | let N := fresh "OQF" in assert (N : T) by exact (lx_opq_holds _ _ _ _ _ _ _ H); clear H ]
      | _ => clear H
      end
  end;
  (* [comment removed for export] *)
  try (lazymatch goal with |- evtA _ _ _ _ _ =>
         match goal with PR : presW _ _ _ _ _ _ _ _ _ _ mx, MU : munch _ ?ma mx, WM : wmono _ ?ma' mx |- _ => clear MU WM end end);
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with
  | X0 : LAWt _ _ _ _ _ _ _ _ |- _ =>
      repeat match goal with
      | X : LAWt _ _ _ _ _ _ _ _ |- _ => clear X
      | MU : munch _ _ ?mc, X : wmono _ _ ?mc |- _ => lazymatch mc with mx => fail | _ => try clear MU; try clear X end
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac lxr_pose_HMQ :=
  let mx := lxr_cur_mem in
  lazymatch goal with
  | HH : HM ?segs ?R ?HIA ?h1 ?LB ?LF mx |- _ =>
      let AL := lxr_goal_al in let CS := lxr_goal_cs in
      let HQ := fresh "HQ0" in
      first [ match goal with ET : htop segs R HIA h1 = htop segs R HIA ?h |- _ =>
                assert (HQ : HMQ R HIA h LB LF mx) by (eapply (hmq_intro R HIA h h1); eassumption) end
            | pose proof (hmq_of_hm R HIA h1 LB LF mx HH) as HQ ];
      lazymatch type of HQ with HMQ _ _ ?h _ _ _ =>
      let L := constr:(arl_L R) in
      let TOP := constr:(htop segs R HIA h) in
      let cands := lxr_cw_list L constr:([(arl_stklo R, htop segs R HIA h)] : list ivl) in
      let cands := lxr_in_list cands in
      let shc := lxr_sf_list R constr:(@nil ivl) in
      let shc := lxr_crfb_list shc in
      lxr_filter cands ltac:(fun lo hi => constr:(forall a, lo <= a < hi -> hm_writable R LB LF TOP a))
        ltac:(first [ apply w_writable_of_client_wrange; solve_client_wrange
                    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left; left; lxr_lia
                    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left; right; right;
                      match goal with I : In (?A0, ?n0) _ |- _ => exists (A0, n0); split; [ exact I | cbn [fst snd]; lxr_lia ] end ])
        ltac:(fun ok =>
          lxr_filter shc ltac:(fun lo hi => constr:(forall c, lo <= c < hi -> arl_stklo R <= c < TOP \/ in_block LF c))
            ltac:(idtac; lxr_in_block)
            ltac:(fun sh =>
              let H := fresh "OQH" in
              assert (H : lx_opq segs AL CS (fun m => HMQ R HIA h LB LF m) ok sh mx);
              [ apply (lx_opq_HMQ R HIA CS h LB LF ok sh mx HQ); [ lxr_forall_okw | lxr_forall_okw ] | ]));
      lxr_clear_okw; clear HQ
      end
  end.

(* [comment removed for export] *)
Definition lxr_tried (P : Prop) : Prop := True.   (* [comment removed for export] *)
Ltac lxr_law_tags_at LAW mx0 :=
  lazymatch LAW with LAWt ?R ?LB ?LF' ?spv ?TOP =>
  let mx := mx0 in
  let segs := lxr_goal_segs in let AL := lxr_goal_al in let CS := lxr_goal_cs in
  let SUB := match goal with
             | S : forall b, In b (?LB0 ++ fdata ?LF0) -> In b (LB ++ fdata LF') |- _ => S
             | _ => constr:(fun (b : blk) (H : In b (LB ++ fdata LF')) => H)
             end in
  (* [comment removed for export] *)
  repeat match goal with
  | CR : client_range _ (?LB0 ++ fdata ?LF0) ?lo ?a ?n |- _ =>
      lazymatch goal with
      | _ : lawcli _ LAW a n |- _ => fail
      | _ : lxr_tried (lawcli _ LAW a n) |- _ => fail
      | |- _ =>
          first [ assert (lawcli segs LAW a n)
                    by (apply lawcli_LAWt;
                        first [ eapply (client_range_lift2 R _ _ lo _ spv a n CR SUB); [ first [ eassumption | lxr_lia ] | lxr_lia ]
                              | eapply (client_range_lift R _ _ lo _ spv a n CR SUB); [ first [ eassumption | lxr_lia ] | lxr_lia ] ])
                | pose proof (I : lxr_tried (lawcli segs LAW a n)) ]   (* [comment removed for export] *)
      end
  end;
  repeat match goal with H : lxr_tried (lawcli _ _ _ _) |- _ => clear H end;
  (* [comment removed for export] *)
  repeat match goal with
  | OB : aobj _ _ _ mx ?a ?n, T : lawcli _ LAW ?a ?n |- _ =>
      lazymatch goal with
      | _ : lawobj _ _ _ LAW a n |- _ => fail
      | _ : lxr_tried (lawobj _ _ _ LAW a n) |- _ => fail
      | |- _ => first [ assert (lawobj segs AL CS LAW a n)
                          by (apply lawobj_LAWt; [ assumption | | solve_cs_top ];
                              match goal with CR : client_range _ _ ?lo a n |- _ =>
                                first [ eapply (client_range_lift2 R _ _ lo _ spv a n CR SUB); [ first [ eassumption | lxr_lia ] | lxr_lia ]
                                      | eapply (client_range_lift R _ _ lo _ spv a n CR SUB); [ first [ eassumption | lxr_lia ] | lxr_lia ] ] end)
                      | pose proof (I : lxr_tried (lawobj segs AL CS LAW a n)) ]
      end
  end;
  repeat match goal with H : lxr_tried (lawobj _ _ _ _ _ _) |- _ => clear H end;
  (* [comment removed for export] *)
  repeat match goal with
  | H : rw_cells _ mx ?a ?cs |- _ =>
      lazymatch a with
      | Z.shiftr _ 3 + al_sb _ => fail
      | _ =>
        let n := eval cbv in (Z.of_nat (cells_size cs)) in
        lazymatch goal with
        | _ : lawcli _ LAW a n |- _ => fail
        | _ : lxr_tried (lawcli _ LAW a n) |- _ => fail
        | |- _ =>
          first [ assert (lawcli segs LAW a n) by (apply lawcli_LAWt; apply client_range_above; lxr_lia)
                | assert (lawcli segs LAW a n)
                    by (apply lawcli_LAWt; eapply lxr_client_range_blk; [ left; reflexivity | cbn [Z.min Z.sub Z.add Z.leb Z.compare]; lxr_lia ])
                | pose proof (I : lxr_tried (lawcli segs LAW a n)) ]
        end
      end
  | H : stk _ mx ?a ?b |- _ =>
      lazymatch goal with
      | _ : lawcli _ LAW a (b - a) |- _ => fail
      | _ : lxr_tried (lawcli _ LAW a (b - a)) |- _ => fail
      | |- _ => first [ assert (lawcli segs LAW a (b - a)) by (apply lawcli_LAWt; apply client_range_above; lxr_lia)
                      | pose proof (I : lxr_tried (lawcli segs LAW a (b - a))) ]
      end
  end;
  repeat match goal with H : lxr_tried (lawcli _ _ _ _) |- _ => clear H end;
  (* [comment removed for export] *)
  repeat match goal with
  | H : rw_cells _ mx (Z.shiftr ?B 3 + al_sb ?al) ?cs |- _ =>
      let n := eval cbv in (Z.of_nat (cells_size cs)) in
      lazymatch goal with
      | _ : lawcli _ LAW (Z.shiftr B 3 + al_sb al) n |- _ => fail
      | _ : lxr_tried (lawcli _ LAW (Z.shiftr B 3 + al_sb al) n) |- _ => fail
      | |- _ =>
          first [ assert (lawcli segs LAW (Z.shiftr B 3 + al_sb al) n)
                    by (apply lawcli_LAWt_shadow3;
                        [ let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc;
                          match goal with FWS : forall x, B <= x < B + _ -> _ \/ in_block LF' x |- _ =>
                            let X := fresh "X" in
                            destruct (FWS c ltac:(lxr_lia)) as [X|X]; [ left; lxr_lia | right; right; left; exact X ] end
                        | first [ assumption | lxr_lia ]
                        | let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc;
                          match goal with OK : cs_ok al ?CS', CR : crange ?CS' B _ |- _ =>
                            let Y := fresh "Y" in
                            destruct (proj1 OK c ltac:(apply CR; lxr_lia)) as (? & Y & ? & ?); lxr_lia end ])
                | pose proof (I : lxr_tried (lawcli segs LAW (Z.shiftr B 3 + al_sb al) n)) ]
      end
  end;
  repeat match goal with H : lxr_tried (lawcli _ _ _ _) |- _ => clear H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxr_law_tags LAW := let mx := lxr_cur_mem in lxr_law_tags_at LAW mx.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxr_link_residual HP :=
  lazymatch type of HP with presA ?segs ?R ?LB ?LF ?SP ?SSP ?TOP ?W ?m ?m' =>
    repeat match goal with
    | H : sshad segs ?AL m ?lo ?hi |- _ =>
        first [ apply (presA_sshad segs R LB LF SP SSP TOP W m m' lo hi HP) in H; [ | qlia | qlia ]
              | idtac "note: dropping sshad across call (link):" H; clear H ]
    | H : abase segs _ m |- _ => clear H
    | H : auar segs _ _ m |- _ => clear H
    | H : wr_at segs m _ _ |- _ => clear H
    | H : mem_inv segs m |- _ => clear H
    end
  end.
Ltac lxr_link_tags LAW mx0 :=
  lxr_law_tags_at LAW mx0;
  lazymatch LAW with LAWt ?R ?LB ?LF' ?spv ?TOP =>
  let segs := lxr_goal_segs in let AL := lxr_goal_al in let CS := lxr_goal_cs in
  repeat match goal with
  | H : rw_cells _ mx0 ?a ?cs |- _ =>
      lazymatch a with
      | Z.shiftr ?B 3 + al_sb ?al =>
          let n := eval cbv in (Z.of_nat (cells_size cs)) in
          lazymatch goal with
          | _ : lawcli _ LAW a n |- _ => fail
          | _ : lxr_tried (lawcli _ LAW a n) |- _ => fail
          | |- _ =>
              first [ assert (lawcli segs LAW a n)
                        by (apply lawcli_LAWt_shadow3;
                            [ simpl_sizes; solve_cshd_range
                            | first [ assumption | lxr_lia ]
                            | let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc;
                              match goal with OK : cs_ok al ?CS', CR : crange ?CS' B _ |- _ =>
                                let Y := fresh "Y" in destruct (proj1 OK c ltac:(apply CR; lxr_lia)) as (? & Y & ? & ?); lxr_lia end ])
                    | pose proof (I : lxr_tried (lawcli segs LAW a n)) ]
          end
      | _ =>
          let n := eval cbv in (Z.of_nat (cells_size cs)) in
          lazymatch goal with
          | _ : lawcli _ LAW a n |- _ => fail
          | _ : lxr_tried (lawcli _ LAW a n) |- _ => fail
          | |- _ => first [ assert (lawcli segs LAW a n) by (apply lawcli_LAWt; simpl_sizes; solve_client_range)
                          | pose proof (I : lxr_tried (lawcli segs LAW a n)) ]
          end
      end
  | H : ro_cells _ mx0 ?a ?cs |- _ =>
      let n := eval cbv in (Z.of_nat (cells_size cs)) in
      lazymatch goal with
      | _ : lawcli _ LAW a n |- _ => fail
      | _ : lxr_tried (lawcli _ LAW a n) |- _ => fail
      | |- _ => first [ assert (lawcli segs LAW a n) by (apply lawcli_LAWt; simpl_sizes; solve_client_range)
                      | pose proof (I : lxr_tried (lawcli segs LAW a n)) ]
      end
  | H : bytes_at _ mx0 ?a ?bs |- _ =>
      lazymatch goal with
      | _ : lawcli _ LAW a (Z.of_nat (length bs)) |- _ => fail
      | _ : lxr_tried (lawcli _ LAW a (Z.of_nat (length bs))) |- _ => fail
      | |- _ => first [ assert (lawcli segs LAW a (Z.of_nat (length bs))) by (apply lawcli_LAWt; simpl_sizes; solve_client_range)
                      | pose proof (I : lxr_tried (lawcli segs LAW a (Z.of_nat (length bs)))) ]
      end
  end;
  repeat match goal with H : lxr_tried (lawcli _ _ _ _) |- _ => clear H end;
  (* [comment removed for export] *)
  repeat match goal with
  | OB : aobj _ _ _ mx0 ?a ?n |- _ =>
      lazymatch goal with
      | _ : lawobj _ _ _ LAW a n |- _ => fail
      | _ : lxr_tried (lawobj _ _ _ LAW a n) |- _ => fail
      | |- _ => first [ assert (lawobj segs AL CS LAW a n) by (apply lawobj_LAWt; [ assumption | simpl_sizes; solve_client_range | solve_cs_top ])
                      | pose proof (I : lxr_tried (lawobj segs AL CS LAW a n)) ];
                (* [comment removed for export] *)
                lazymatch goal with
                | _ : lawcli _ LAW a n |- _ => idtac
                | |- _ => try (assert (lawcli segs LAW a n) by (apply lawcli_LAWt; simpl_sizes; solve_client_range))
                end
      end
  end;
  repeat match goal with H : lxr_tried (lawobj _ _ _ _ _ _) |- _ => clear H end
  end.

Ltac lx_rw_sub :=
  lazymatch goal with
  | |- rw_cells ?sg ?m ?A ?cs =>
      let n := eval cbv in (Z.of_nat (cells_size cs)) in
      match goal with
      | H : rw_cells sg m ?A0 ?cs0 |- _ =>
          let d := addr_diff A A0 in
          let k1 := lx_cells_upto cs0 d in
          let rest := eval cbv beta iota delta [skipn] in (skipn k1 cs0) in
          let k2 := lx_cells_upto rest n in
          let pre := eval cbv beta iota delta [firstn] in (firstn k1 cs0) in
          let mid := eval cbv beta iota delta [firstn] in (firstn k2 rest) in
          let post := eval cbv beta iota delta [skipn] in (skipn k2 rest) in
          let H2 := fresh "Hsub" in
          pose proof H as H2;
          change (rw_cells sg m A0 (pre ++ (mid ++ post))) in H2;
          apply (proj1 (rw_cells_app sg m A0 pre (mid ++ post))) in H2;
          let H3 := fresh "Hsub" in
          destruct H2 as [_ H3];
          apply (proj1 (rw_cells_app sg m _ mid post)) in H3;
          destruct H3 as [H3 _];
          first [ exact H3
                | lazymatch type of H3 with rw_cells _ _ ?A1 _ => replace A1 with A in H3 by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia); exact H3 end ]
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lx_b8_mod : forall z, Z_to_bv 8 z = Z_to_bv 8 (z mod 256).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Ltac lx_b8_norm :=
  repeat match goal with
  | H : context [Z_to_bv 8 (Zneg ?p)] |- _ =>
      let k := eval vm_compute in (Z.modulo (Zneg p) 256) in
      rewrite (lx_b8_mod (Zneg p)) in H; change ((Zneg p) mod 256) with k in H
  | |- context [Z_to_bv 8 (Zneg ?p)] =>
      let k := eval vm_compute in (Z.modulo (Zneg p) 256) in
      rewrite (lx_b8_mod (Zneg p)); change ((Zneg p) mod 256) with k
  end.
(* [comment removed for export] *)
Ltac lx_shbase_norm :=
  repeat match goal with
  | H : rw_cells ?sg ?m (al_sb ?AL + ?X) ?cs |- _ => rewrite (Z.add_comm (al_sb AL) X) in H
  | |- context [Z_to_bv 64 (al_sb ?AL + ?X)] => rewrite (Z.add_comm (al_sb AL) X)
  end.
(* [comment removed for export] *)
Ltac lxr_abase :=
  let mx := lxr_cur_mem in
  lazymatch goal with
  | _ : abase _ _ mx |- _ => idtac
  | HH : HM ?segs ?R ?HIA ?h ?LB ?LF mx |- _ => pose proof (hm_abase segs R HIA h LB LF mx HH)
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Lemma lx_lit_signed : forall z k, k = z - 2 ^ 64 -> Z_to_bv 64 z = Z_to_bv 64 k.
Proof.
  intros z k ->. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). replace (z - 2 ^ 64) with (z + (-1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Ltac lx_signed_lits :=
  repeat match goal with
  | |- context [MS ?R _ _ _ _ _ _] =>
      match R with context [Z_to_bv 64 (Zpos ?p)] =>
        lazymatch eval vm_compute in (Z.leb (2 ^ 63) (Zpos p)) with true => idtac end;
        let k := eval vm_compute in (Zpos p - 2 ^ 64)%Z in
        rewrite (lx_lit_signed (Zpos p) k eq_refl)
      end
  end.

(* [comment removed for export] *)
Ltac lxr_leaf := lxr_unpack; lxr_unabs_lists; lx_b8_norm; lx_shbase_norm; lxr_abase; try lx_signed_lits.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_rw_join_grow H n :=
  (* [comment removed for export] *)
  lazymatch type of H with
  | rw_cells ?sg ?m ?A ?cs0 =>
      let z := eval cbv in (Z.of_nat (cells_size cs0)) in
      lazymatch eval vm_compute in (Z.ltb z n) with
      | false => idtac
      | true =>
          match goal with
          | H2 : rw_cells sg m ?B ?cs1 |- _ =>
              let d := addr_diff B A in constr_eq d z;
              let J := fresh "Hjoin" in
              pose proof (proj2 (rw_cells_app sg m A cs0 cs1)
                            (conj H ltac:(replace (A + Z.of_nat (cells_size cs0)) with B
                                              by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear; lia);
                                            exact H2))) as J;
              cbn [app] in J; clear H; lx_rw_join_grow J n
          end
      end
  end.
Ltac lx_rw_join :=
  lazymatch goal with
  | |- rw_cells ?sg ?m ?A ?cs =>
      let n := eval cbv in (Z.of_nat (cells_size cs)) in
      match goal with
      | H : rw_cells sg m ?A0 ?cs0 |- _ =>
          let d := addr_diff A0 A in constr_eq d 0%Z;
          let z := eval cbv in (Z.of_nat (cells_size cs0)) in
          lazymatch eval vm_compute in (Z.ltb z n) with true => idtac end;
          let H1 := fresh "Hjoin" in pose proof H as H1; lx_rw_join_grow H1 n;
          match goal with J : rw_cells sg m _ _ |- _ => exact J end
      end
  end.

(* [comment removed for export] *)
Lemma lx_rw_to_blob : ltac2:(CDefT.buildp (gd_tbl_LxARt ()) "Psegs,(3.$4;.)Pm,P,(6.&40.)(7.(6.&8.))PA,$0.Pcs,(3.$46.)Pn,$4?.P,(17.$4?.(49.R2.)R1.)P,(47.R6.R5.R4.R3.)(47.R7.R6.R5.(50.$46.(51.R3.(52.R4.))(4:.$46.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A cs n E H. pose proof H as [[WF _] _].
  eapply rw_cells_reshape; [exact H | | cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity].
  cbn [cells_wf cell_wf]. split; [|exact I]. rewrite cells_bytes_length by exact WF. exact E.
Qed.
Ltac lx_rw_blob :=
  lazymatch goal with
  | |- rw_cells ?sg ?m ?A [CB ?n ?tb] =>
      is_evar tb;
      let z := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rw_cells sg m ?A0 ?cs0 |- _ =>
          let d := addr_diff A0 A in constr_eq d 0%Z;
          let H1 := fresh "Hjoin" in pose proof H as H1; lx_rw_join_grow H1 z;
          match goal with J : rw_cells sg m ?B ?cs |- _ =>
            let d2 := addr_diff B A in constr_eq d2 0%Z;
            apply (lx_rw_to_blob sg m _ cs n eq_refl) in J; cbn [cells_bytes cbytes app] in J; rewrite ?app_nil_r in J; exact J
          end
      end
  end.

(* [comment removed for export] *)
#[export] Ltac lx_app_hook ::= first [ lx_rw_sub | lx_rw_join | lx_rw_blob | lx_opqa ].

(* [comment removed for export] *)
Ltac lx_align32 N :=
  match goal with
  | Hm : ?v mod _ = 0 |- context [MS (mkR _ (Z_to_bv 64 ?v') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
      constr_eq v v'; is_var v;
      (* [comment removed for export] *)
      try (lazymatch type of Hm with v mod (2 ^ Z.of_N ?k) = 0 => let c := eval vm_compute in (2 ^ Z.of_N k)%Z in change (v mod c = 0) in Hm end);
      rename v into N
  end.


(* [comment removed for export] *)
Lemma lx_cond_eqT : forall a b, (zlow 64 a =? zlow 64 b) = true -> a mod 2^64 = b mod 2^64.
Proof. intros a b H. apply Z.eqb_eq in H. unfold zlow in H. exact H. Qed.
Lemma lx_cond_eqF : forall a b, (zlow 64 a =? zlow 64 b) = false -> a mod 2^64 <> b mod 2^64.
Proof. intros a b H. apply Z.eqb_neq in H. unfold zlow in H. exact H. Qed.
Lemma lx_cond_ltT : forall a b, (zlow 64 a <? zlow 64 b) = true -> a mod 2^64 < b mod 2^64.
Proof. intros a b H. apply Z.ltb_lt in H. unfold zlow in H. exact H. Qed.
Lemma lx_cond_ltF : forall a b, (zlow 64 a <? zlow 64 b) = false -> b mod 2^64 <= a mod 2^64.
Proof. intros a b H. apply Z.ltb_ge in H. unfold zlow in H. lia. Qed.
Ltac lx_cond K :=
  match goal with
  | H : (zlow 64 ?a =? zlow 64 ?b) = true |- _ => pose proof (lx_cond_eqT a b H) as K; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in K; rewrite ?Zmod_0_l in K
  | H : (zlow 64 ?a =? zlow 64 ?b) = false |- _ => pose proof (lx_cond_eqF a b H) as K; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in K; rewrite ?Zmod_0_l in K
  | H : (zlow 64 ?a <? zlow 64 ?b) = true |- _ => pose proof (lx_cond_ltT a b H) as K; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in K
  | H : (zlow 64 ?a <? zlow 64 ?b) = false |- _ => pose proof (lx_cond_ltF a b H) as K; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in K
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac lxr_stk_join :=
  let mx := lxr_cur_mem in
  repeat match goal with
  | A : stk ?sg mx ?lo ?mid, B : stk ?sg mx ?mid' ?hi |- _ =>
      first [ constr_eq mid mid' | replace mid' with mid in B by (clear; lia) ];
      let J := fresh "STJ" in
      pose proof (stk_merge sg mx lo mid hi A B ltac:(lx_prune; clear_disj; lia)) as J; clear A B
  | A : stk ?sg mx ?lo ?mid, C : rw_cells ?sg mx ?mid' ?cs |- _ =>
      first [ constr_eq mid mid' | replace mid' with mid in C by (clear; lia) ];
      let z := eval cbv in (Z.of_nat (cells_size cs)) in
      release_frame C A (mid + z)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxr_find_eq v B :=
  lazymatch B with
  | v = ?e /\ _ => e
  | v = ?e => e
  | _ /\ ?B' => lxr_find_eq v B'
  end.
(* [comment removed for export] *)
Ltac lxr_path_var v eR eF t :=
  first [ lazymatch goal with _ : v <= eR \/ eF <= v |- _ => idtac end | assert (v <= eR \/ eF <= v) by t | idtac ];
  first [ lazymatch goal with _ : v <= eF \/ eR <= v |- _ => idtac end | assert (v <= eF \/ eR <= v) by t | idtac ];
  first [ assert (eR <= v) by t | assert (eF <= v) by t | idtac ];
  first [ assert (v <= eF) by t | assert (v <= eR) by t | idtac ].
(* [comment removed for export] *)
Ltac lxr_path_le v w t :=
  first [ constr_eq v w
        | lazymatch type of w with Z => idtac end;
          first [ lazymatch goal with _ : v <= w |- _ => idtac end | assert (v <= w) by t | idtac ];
          first [ lazymatch goal with _ : w <= v |- _ => idtac end | assert (w <= v) by t | idtac ]
        | idtac ].
Ltac lxr_path_pairs A0 B v t :=
  lazymatch A0 with
  | ?w = _ /\ ?A' => first [ is_var w; let chk := lxr_find_eq w B in lxr_path_le v w t | idtac ]; lxr_path_pairs A' B v t
  | ?w = _ => first [ is_var w; let chk := lxr_find_eq w B in lxr_path_le v w t | idtac ]
  | _ /\ ?A' => lxr_path_pairs A' B v t
  | _ => idtac
  end.
Ltac lxr_path_eqs A0 A B t :=
  lazymatch A with
  | ?v = ?eR /\ ?A' => first [ is_var v; let eF := lxr_find_eq v B in lxr_path_var v eR eF t; lxr_path_pairs A0 B v t | idtac ]; lxr_path_eqs A0 A' B t
  | ?v = ?eR => first [ is_var v; let eF := lxr_find_eq v B in lxr_path_var v eR eF t; lxr_path_pairs A0 B v t | idtac ]
  | _ /\ ?A' => lxr_path_eqs A0 A' B t
  | _ => idtac
  end.
Ltac lxr_path :=
  (* [comment removed for export] *)
  repeat match goal with
  | H : ?c <= ?d \/ ?a = ?b |- _ =>
      lazymatch goal with
      | _ : a <= b \/ c <= d |- _ => fail
      | _ => assert (a <= b \/ c <= d) by (clear - H; lia)
      end
  end;
  (* [comment removed for export] *)
  match goal with
  | H : (?s2v = 0 /\ ?A) \/ (?s2v = ?FB /\ ?B) |- _ =>
      (* [comment removed for export] *)
      let t := (let D := fresh "D" in destruct H as [D|D]; decompose [and] D; subst; clear_mods; lx_prune;
                first [ clear_disj; lia
                      | match goal with S : _ <= arl_stklo _ \/ _ |- _ =>
                          solve [ generalize S; clear_disj; let SS := fresh in intros SS; destruct SS; lia ] end ]) in
      lxr_path_eqs (s2v = 0 /\ A) (s2v = 0 /\ A) (s2v = FB /\ B) t
  | |- _ => idtac
  end.
