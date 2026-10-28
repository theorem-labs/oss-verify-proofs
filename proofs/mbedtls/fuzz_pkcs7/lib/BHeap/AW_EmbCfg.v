(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_Populate.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_EmbCfg () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_EMB"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.EM"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.sub_fp"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "ARUN_1.emb_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "ARUN_1.Kfx"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.emb_cells"; "ARUN_1.emb_step"; "ARUN_1.emb_fresh"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.b12_statics"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.B12_NEEDX"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.Site.b12_postS"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_FMT_OOM1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_ASAN_NAME"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_PRINTF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.nil"].


Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition emb_wf (P d cap sz : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "(0.P,(1.$2.O3.=)(0.(1.$2.O4.=)(0.(1.$2.O2.=)(1.$2.O1.=)))P,(3.(1.$2.O3.=))(0.(1.$2.O4.(4.$5.+20.))(0.(1.$2.O2.$6.)(0.(7.=O1.)(7.O1.(8.+3>.$9.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition emb_step (P d cap sz P' d' cap' sz' : Z) (xa : option Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "(0.(1.$2.O5.(4.$5.+20.))(0.(1.$2.O3.$6.)(0.(0.(:.O6.O2.)(7.O2.(4.O6.$9.)))(;.(0.(1.$2.O8.=)(<.$2.La,$2.(0.(1.(=.$2.)O1.(>.$2.R1.))(0.(1.$2.O4.R1.)(3.(1.$2.R1.=))))))(0.(3.(1.$2.O8.=))(0.(1.(=.$2.)O1.(?.$2.))(1.$2.O4.O8.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition emb_geo (EB T CTX SB : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "P,(3.(1.$2.O4.=))(0.(7.+65?000.O4.)(0.(7.(4.O4.$6.)(10.VhAR,))(0.(;.(7.(4.O4.$6.)+7???7000.)(7.+10007???8000.O4.))(0.(;.(7.(4.O4.$6.)O1.)(7.(4.(4.O1.(11.+2.+25.))+1000.)O4.))(0.(;.(7.(4.O4.$6.)O3.)(7.(4.O3.+1000.)O4.))(;.(7.(4.O4.$6.)O2.)(7.(4.O2.+10000.)O4.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition emb_fresh (CS : Z -> Prop) (xa : option Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "Pa,$2.P,(1.(=.$2.)O1.(>.$2.R1.))(0.(7.+65?000.R2.)(0.(7.(4.R2.$6.)(10.VhAR,))(0.(;.(7.(4.R2.$6.)+7???7000.)(7.+10007???8000.R2.))(0.(1.$2.(12.R2.+1000.)=)Py,$2.P,A1.O2.R1.(3.(0.(7.R4.R2.)(:.R2.(4.R4.$6.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition Kfx (K00 : Model -> Prop) (Kx : Z -> Model -> Prop) (xa : option Z) : Model -> Prop :=
  match xa with None => K00 | Some a => Kx a end.
Definition CSfx (CS00 : Z -> Prop) (CSx : Z -> Z -> Prop) (xa : option Z) : Z -> Prop :=
  match xa with None => CS00 | Some a => CSx a end.

Section FX.
  Variable AL : asan_layout.
  Variables (CS00 : Z -> Prop) (K00 : Model -> Prop) (CSx : Z -> Z -> Prop) (Kx : Z -> Model -> Prop).
  Hypothesis CSOK00 : cs_ok AL CS00.
  Hypothesis KL00 : kinv AL CS00 K00.
  Hypothesis CSOKx : forall a, cs_ok AL (CSx a).
  Hypothesis KxL : forall a, kinv AL (CSx a) (Kx a).
  Hypothesis CSx_inc : forall a y, CS00 y -> CSx a y.

  #[using="CSOK00 CSOKx"] Lemma CSOKfx : forall xa, cs_ok AL (CSfx CS00 CSx xa).
  Proof. intros [a|]; [apply CSOKx| exact CSOK00]. Qed.
  #[using="KL00 KxL"] Lemma KLfx : forall xa, kinv AL (CSfx CS00 CSx xa) (Kfx K00 Kx xa).
  Proof. intros [a|]; [apply KxL| exact KL00]. Qed.
  #[using="CSx_inc"] Lemma CSfx_inc : forall xa y, CS00 y -> CSfx CS00 CSx xa y.
  Proof. intros [a|] y H; [apply CSx_inc; exact H| exact H]. Qed.
  #[using="CSx_inc"] Lemma crange_fx : forall xa A n, crange CS00 A n -> crange (CSfx CS00 CSx xa) A n.
  Proof. intros xa A n H x Hx. apply CSfx_inc. exact (H x Hx). Qed.
End FX.

(* [comment removed for export] *)
#[using="Type"] Lemma sub_fp_app_tail : forall (W W' E : list (Z * Z)), sub_fp W W' -> sub_fp (W ++ E) (W' ++ E).
Proof.
  intros W W' E H x Hx. revert Hx. 
  assert (G : forall (A B : list (Z * Z)), outside (A ++ B) x <-> outside A x /\ outside B x).
  { induction A as [|[lo hi] A IH]; intros B; cbn [app outside]; [tauto|]. rewrite IH. tauto. }
  rewrite !G. intros [H1 H2]. split; [exact (H x H1)| exact H2].
Qed.
#[using="Type"] Lemma sub_fp_app_l : forall (W W' E : list (Z * Z)), sub_fp W W' -> sub_fp W (W' ++ E).
Proof.
  intros W W' E H x Hx.
  assert (G : forall (A B : list (Z * Z)), outside (A ++ B) x -> outside A x).
  { induction A as [|[lo hi] A IH]; intros B; cbn [app outside]; [tauto|]. intros [H1 H2]. split; [exact H1| exact (IH B H2)]. }
  exact (H x (G W' E Hx)).
Qed.
#[using="Type"] Lemma munch_tail2 : ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "PW0,(13.(14.$2.$2.))PW1,(13.(14.$2.$2.))PW2,(13.(14.$2.$2.))PW3,(13.(14.$2.$2.))PE,(13.(14.$2.$2.))Pm0,P,(15.&40.)(=.(15.&8.))Pm1,P,(15.&40.)(=.(15.&8.))Pm2,P,(15.&40.)(=.(15.&8.))Pm3,P,(15.&40.)(=.(15.&8.))P,(16.R9.R4.R3.)P,(16.(17.(14.$2.$2.)R9.R6.)R4.R3.)P,(16.R9.R4.R3.)P,(18.R<.R9.)P,(18.R<.R:.)P,(18.R<.R;.)(16.(17.(14.$2.$2.)R<.R;.)R:.R7.)")
(* [comment removed for export] *).
Proof.
  intros W0 W1 W2 W3 E m0 m1 m2 m3 M0 M1 M2 S0 S1 S2.
  eapply munch_trans; [eapply munch_weaken; [apply sub_fp_app_l; exact S0| exact M0]|].
  eapply munch_trans; [eapply munch_weaken; [apply sub_fp_app_tail; exact S1| exact M1]|].
  eapply munch_weaken; [apply sub_fp_app_l; exact S2| exact M2].
Qed.

(* [comment removed for export] *)
Definition emb_fp (d' : Z) : list (Z * Z) := [(A_EMB, A_EMB + 56); (d', d' + kEmbBytes)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition B12_NEEDX : Z := 1408.

Section Site.
  Variable AL : asan_layout.
  Variables (CS00 : Z -> Prop) (K00 : Model -> Prop) (CSx : Z -> Z -> Prop) (Kx : Z -> Model -> Prop).
  Variables (EP EB ECAP ESZ : Z).

  (* [comment removed for export] *)
  Definition b12_postS (SP0 : Z) (gp tp x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (c lo0 : Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "Lcf,$19.(<.$1:.Lms',$1:.(<.$1;.Lmo',$1;.(<.(=.$2.)Lxa,(=.$2.)(<.$2.LP',$2.(<.$2.Ld',$2.(<.$2.Lcap',$2.(<.$2.Lsz',$2.(<.(15.&40.)Lt0',(15.&40.)(<.(15.&40.)Lt1',(15.&40.)(<.(15.&40.)Lt2',(15.&40.)(<.(15.&40.)La0',(15.&40.)(<.(15.&40.)La1',(15.&40.)(<.(15.&40.)La2',(15.&40.)(<.(15.&40.)La3',(15.&40.)(<.(15.&40.)La4',(15.&40.)(<.(15.&40.)La5',(15.&40.)(<.(15.&40.)La6',(15.&40.)(<.(15.&40.)La7',(15.&40.)(<.(15.&40.)Lt3',(15.&40.)(<.(15.&40.)Lt4',(15.&40.)(<.(15.&40.)Lt5',(15.&40.)(<.(15.&40.)Lt6',(15.&40.)(<.P,(15.&40.)(=.(15.&8.))Lmm,P,(15.&40.)(=.(15.&8.))(0.(1.$19.R18.(1<.R17.R16.))(0.(1.$1:.R17.(1=.(1>.(1?.&40.+4<><0.)(1?.&40.O13.)O12.O11.R10.R?.R>.(1?.&40.O3.)O10.R=.R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(1?.&40.+4<><0.)O4.(?.(15.&40.))R1.(20.$21.)))(0.(16.(22.(14.$2.$2.)(23.$2.$2.O2.O13.)(24.R13.))O1.R1.)(0.(25.$21.O1.R1.)(0.(26.$21.R1.)(0.(27.$21.R1.O2.O13.)(0.(28.VK00,VKx,R15.R16.)(0.(29.R1.R16.)(0.(2:.R14.R13.R12.R11.R1.)(0.(2;.VEP,VEB,VECAP,VESZ,R14.R13.R12.R11.R15.)(2<.VCS00,R15.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition b12_siteS : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "PQ,P,$19.SpPgp,(15.&40.)Ptp,(15.&40.)Px5,(15.&40.)Px6,(15.&40.)Px7,(15.&40.)Px9,(15.&40.)Px12,(15.&40.)Px13,(15.&40.)Px14,(15.&40.)Px15,(15.&40.)Px16,(15.&40.)Px17,(15.&40.)Px18,(15.&40.)Px19,(15.&40.)Px20,(15.&40.)Px21,(15.&40.)Px22,(15.&40.)Px23,(15.&40.)Px24,(15.&40.)Px25,(15.&40.)Px26,(15.&40.)Px27,(15.&40.)Px28,(15.&40.)Px29,(15.&40.)Px30,(15.&40.)Px31,(15.&40.)PSP0,$2.Plo0,$2.Pc,$2.PF,(2=.&5.(15.&40.))Pfc,(15.&20.)Pm,P,(15.&40.)(=.(15.&8.))Pmo,$1;.P,(0.(7.+1.R5.)(7.R5.+1?.))P,(2>.VEP,VEB,VECAP,VESZ,R3.)P,(27.$21.R4.R8.R9.)P,(7.(10.VhAR,)R9.)P,(7.R:.(2?.R;.$30.))P,(7.R<.(11.+2.+3?.))P,(1.$2.(12.R=.+10.)=)P,(31.VCS00,R=.(2?.R>.R=.))P,(26.$21.R:.)P,A1.VK00,R:.P,(29.R<.R;.)P,Pc',$19.P,(32.R13.R2=.R2<.R28.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R10.R?.R11.R12.R>.R1.)(33.$21.R2?.R2.)(33.$21.R2>.(1<.(1=.(1>.(1?.&40.+4<>4<.)(1?.&40.R13.)R2=.R2<.R2;.R2:.R29.(1?.&40.R11.)R28.(1?.&40.$34.)(1?.&40.$35.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R10.(1?.&40.$36.)R?.(?.(15.&40.))R>.(20.$21.))R=.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition exh_xpost (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Wl : list (Z * Z)) (XP : mem -> Prop) (R lo : Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_EmbCfg ()) "Lcf,$19.(<.$1:.Lms',$1:.(<.$1;.Lmo',$1;.(<.(=.$2.)Lxa,(=.$2.)(<.$2.LP',$2.(<.$2.Ld',$2.(<.$2.Lcap',$2.(<.$2.Lsz',$2.(<.(15.&40.)Lt0,(15.&40.)(<.(15.&40.)Lt1,(15.&40.)(<.(15.&40.)Lt2,(15.&40.)(<.(15.&40.)La1,(15.&40.)(<.(15.&40.)La2,(15.&40.)(<.(15.&40.)La3,(15.&40.)(<.(15.&40.)La4,(15.&40.)(<.(15.&40.)La5,(15.&40.)(<.(15.&40.)La6,(15.&40.)(<.(15.&40.)La7,(15.&40.)(<.(15.&40.)Lt3,(15.&40.)(<.(15.&40.)Lt4,(15.&40.)(<.(15.&40.)Lt5,(15.&40.)(<.(15.&40.)Lt6,(15.&40.)(<.P,(15.&40.)(=.(15.&8.))Lmm,P,(15.&40.)(=.(15.&8.))(0.(1.$19.R17.(1<.R16.R15.))(0.(1.$1:.R16.(1=.(1>.O17.(1?.&40.O16.)O15.O14.R?.R>.R=.O13.O12.(1?.&40.=)R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(37.O17.)O6.(?.(15.&40.))R1.(20.$21.)))(0.(16.(17.(14.$2.$2.)O5.(24.R12.))O1.R1.)(0.(25.$21.O1.R1.)(0.(26.$21.R1.)(0.(27.$21.R1.O2.O16.)(0.(28.VK00,VKx,R14.R15.)(0.(29.R1.R15.)(0.(38.$21.R1.(4.O3.+44.)(22.$39.(3:.(1?.&8.+1.))(3;.$39.)))(0.(2:.R13.R12.R11.R10.R1.)(0.(2;.VEP,VEB,VECAP,VESZ,R13.R12.R11.R10.R14.)(0.(2<.VCS00,R14.)A1.O4.R1.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
End Site.

End ARUN_1.
