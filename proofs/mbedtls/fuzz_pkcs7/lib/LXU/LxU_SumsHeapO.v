(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA AEvt HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_x509_get_name_A U_x509_get_name.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxRun LxDenot LxSoundRun LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Export LxU_SumsHeap.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_LxP_SumsHeapO () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.snd"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.cwP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_heapkit"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.hpP"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.lawP"; "Kit.lawPX"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_hcli"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_fprop"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.objP"; "Kit.cwoP"; "Kit.croP"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.map"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.True"; "Corelib.Lists.ListDef.nth"; "Corelib.Numbers.BinNums.positive"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMXH"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.U_X509_GET_NAME"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XB"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FProp"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "havoc16"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.heapcall"; "HC_getnameP"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUM"; "Stdlib.ZArith.BinInt.Z.of_N"; "havoc4"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XRep"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "Valid.wchunks"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Valid.wz"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.hres"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_validHR"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "cwoP"; "croP"; "lawPX"; "RnameP"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundRun.tgt_aevtM"; "SUM_getnameP"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_hress"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.SUM_calloc1P"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.HC_calloc1P"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_blks"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.SUM_freeP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.HC_freeP"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.summary"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.su_gbind"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_valid"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okMR"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_no_layout"].


(* [comment removed for export] *)
Section Kit.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.

  (* [comment removed for export] *)
  Definition lawPX : list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop := fun LB sp X m m' => heap_presx usegs L LB sp X m m'.
  Lemma lawPX_ok : hlaw_ok usegs lawPX.
  Proof.
    intros LB sp X m1 m2 x H HR HO Hc. apply H; [exact HR| | exact HO]. destruct Hc as [Hs|Hb]; [left; exact Hs| right; right; exact Hb].
  Qed.
  (* [comment removed for export] *)
  Lemma heapkit_introX : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "Ph,(0.$1.VL,VHI,)PLB,(2.$3.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$6.POK,(2.$7.)P,(8.$1.VL,VHI,R5.R4.R3.R2.)P,(9.(:.$;.$;.)Liv,(:.$;.$;.)Px,$;.P,(<.(=.(>.$;.$;.R2.)R1.)(?.R1.(10.$;.$;.R2.)))PLB',(2.$3.)P,Pb,$3.P,(11.$3.R1.R:.)(11.$3.R2.R3.)(12.VL,(13.$1.VL,VHI,R;.)R2.R4.)R2.)(14.$1.(15.VL,VHI,(13.$1.VL,VHI,R7.)R4.)(12.VL,(13.$1.VL,VHI,R7.))(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(17.VL,)(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp$18.(19.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)))R6.R6.R3.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo OK HH HOK. destruct (heapkit_intro L HI h LB m mo OK HH HOK) as [A [B [C [D _]]]].
    split; [exact A| split; [exact B| split; [exact C| split; [exact D|]]]].
    constructor; [apply lawP_ok| constructor; [apply lawPX_ok| constructor]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41625301678.1800000:S1b1k1x2Hx". (* [comment removed for export] *)
  Lemma hcliX_block : forall LB smax b k, In (b, k) LB -> lx_hcli usegs LB lawPX smax b k.
  Proof.
    intros LB smax b k Hin LB' sp X m1 m2 x HX _ H Hx HR HO. apply H; [exact HR| | exact HO]. right; right. exists (b, k). split; [apply HX; exact Hin| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5892541444.1900000BS1L1a1n2H12H21x2Hx". (* [comment removed for export] *)
  Lemma hcliX_static : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.(:.$;.$;.))Psmax,$;.Pa,$;.Pn,$;.P,(=.(1:.VL,)R2.)P,(=.(1;.R3.R2.)(1<.VL,))P,Px,$;.P,(<.(=.R5.R1.)(?.R1.(1;.R5.R4.)))(1=.(1>.VL,R2.))(1?.$1.R7.$18.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof. intros LB smax a n H1 H2 H3 LB' sp X m1 m2 x _ _ H Hx HR HO. apply H; [exact HR| | exact HO]. right; left. split; [lia| apply H3; exact Hx]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L34961879063.2200000LS2lo4smax1b1k1D2sp1x2Hs2Hx1S". (* [comment removed for export] *)
  Lemma hcliX_crange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.Psmax,$;.Pb,$;.Pk,$;.P,(20.VL,R5.R4.R2.R1.)P,(21.(=.(1;.R3.R2.)R5.)(=.R4.R3.))(1?.$1.R7.$18.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB lo smax b k CR D LB' sp X m1 m2 x HX Hs H Hx HR HO. apply H; [exact HR| | exact HO].
    destruct (CR x Hx) as [S|[S|(bb & Hbb & Hr)]]; [left; lia| right; left; exact S| right; right].
    exists bb. split; [apply HX; exact Hbb| exact Hr].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21855022796.1300000<S2lo3TOP1x1S". (* [comment removed for export] *)
  Lemma hcliX_cwrange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.PTOP,$;.Psmax,$;.Pb,$;.Pk,$;.P,(22.VL,R6.R5.R4.R2.R1.)P,(21.(=.(1;.R3.R2.)R6.)(=.R4.R3.))(1?.$1.R8.$18.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB lo TOP smax b k CR D. apply (hcliX_crange LB lo); [|exact D]. intros x Hx.
    destruct (CR x Hx) as [S|[S|S]]; [left; lia| right; left; exact S| right; right; exact S].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cwoP (LB0 : list (Z * Z)) (lo TOP : Z) (vs : list Z) : Prop :=
    match vs with [b; k] => client_wrange L LB0 lo TOP b k | _ => True end.
  Definition croP (LB0 : list (Z * Z)) (lo : Z) (vs : list Z) : Prop :=
    match vs with [b; k] => client_range L LB0 lo b k | _ => True end.
  (* [comment removed for export] *)
  Lemma obj3_crange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.PTOP,$;.Plo',$;.Pb,$;.Pk,$;.P,(20.VL,R6.R3.R2.R1.)P,(=.(23.VL,)R4.)P,(=.=R3.)(24.(16.Pvs,(2.$;.)Sp(25.VL,R9.)(16.Pvs,(2.$;.)Sp(26.R9.R8.R7.)(16.Pvs,(2.$;.)Sp(27.R9.R8.)(19.Pvs,(2.$;.)Sp))))#0.(16.$;.R5.(16.$;.R4.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros. eapply obj_crange; eassumption. Qed.
  Lemma obj3_cwrange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.PTOP,$;.Plo',$;.PTOP',$;.Pb,$;.Pk,$;.P,(22.VL,R7.R4.R3.R2.R1.)P,(=.(23.VL,)R5.)P,(=.=R3.)(24.(16.Pvs,(2.$;.)Sp(25.VL,R:.)(16.Pvs,(2.$;.)Sp(26.R:.R9.R8.)(16.Pvs,(2.$;.)Sp(27.R:.R9.)(19.Pvs,(2.$;.)Sp))))#0.(16.$;.R5.(16.$;.R4.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros. eapply obj_cwrange; eassumption. Qed.
  Lemma obj3_block : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.(:.$;.$;.))Plo,$;.PTOP,$;.Pb,$;.Pk,$;.P,(11.(:.$;.$;.)(28.$;.$;.R2.R1.)R5.)P,(=.=R2.)(24.(16.Pvs,(2.$;.)Sp(25.VL,R7.)(16.Pvs,(2.$;.)Sp(26.R7.R6.R5.)(16.Pvs,(2.$;.)Sp(27.R7.R6.)(19.Pvs,(2.$;.)Sp))))#0.(16.$;.R4.(16.$;.R3.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros. eapply obj_block; eassumption. Qed.
  Lemma cwo_cwrange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.PTOP,$;.Pb,$;.Pk,$;.P,(22.VL,R5.R4.R3.R2.R1.)(24.(16.Pvs,(2.$;.)Sp(25.VL,R6.)(16.Pvs,(2.$;.)Sp(26.R6.R5.R4.)(16.Pvs,(2.$;.)Sp(27.R6.R5.)(19.Pvs,(2.$;.)Sp))))#1.(16.$;.R3.(16.$;.R2.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros LB lo TOP b k H. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5468055284.1400000DS1a1n1b1k2H12H21x2Hx". (* [comment removed for export] *)
  Lemma cwo_sub : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.PTOP,$;.Pa,$;.Pn,$;.Pb,$;.Pk,$;.P,(22.VL,R7.R6.R5.R4.R3.)P,(=.R5.R3.)P,(=.(1;.R4.R3.)(1;.R6.R5.))(24.(16.Pvs,(2.$;.)Sp(25.VL,R:.)(16.Pvs,(2.$;.)Sp(26.R:.R9.R8.)(16.Pvs,(2.$;.)Sp(27.R:.R9.)(19.Pvs,(2.$;.)Sp))))#1.(16.$;.R5.(16.$;.R4.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros LB lo TOP a n b k H H1 H2 x Hx. apply H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L64928013280.1100000GS2lo3TOP1b1k2H12H21x2Hx". (* [comment removed for export] *)
  Lemma cwo_stack : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.(:.$;.$;.))Plo,$;.PTOP,$;.Pb,$;.Pk,$;.P,(=.R4.R2.)P,(=.(1;.R3.R2.)R4.)(24.(16.Pvs,(2.$;.)Sp(25.VL,R7.)(16.Pvs,(2.$;.)Sp(26.R7.R6.R5.)(16.Pvs,(2.$;.)Sp(27.R7.R6.)(19.Pvs,(2.$;.)Sp))))#1.(16.$;.R4.(16.$;.R3.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros LB lo TOP b k H1 H2 x Hx. left. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41625298503.1000000:S1b1k1x2Hx". (* [comment removed for export] *)
  Lemma cwo_block : forall LB lo TOP b k, In (b, k) LB -> lx_fprop [objP L LB; cwoP LB lo TOP; croP LB lo] 1 [b; k].
  Proof. intros LB lo TOP b k Hin x Hx. right; right. exists (b, k). split; [exact Hin| cbn; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma cro_crange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.PTOP,$;.Pb,$;.Pk,$;.P,(20.VL,R5.R4.R2.R1.)(24.(16.Pvs,(2.$;.)Sp(25.VL,R6.)(16.Pvs,(2.$;.)Sp(26.R6.R5.R4.)(16.Pvs,(2.$;.)Sp(27.R6.R5.)(19.Pvs,(2.$;.)Sp))))#2.(16.$;.R3.(16.$;.R2.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros LB lo TOP b k H. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21855022796.1200000=S2lo4TOP'1x1S". (* [comment removed for export] *)
  Lemma cro_cwrange : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)Plo,$;.PTOP,$;.PTOP',$;.Pb,$;.Pk,$;.P,(22.VL,R6.R5.R3.R2.R1.)(24.(16.Pvs,(2.$;.)Sp(25.VL,R7.)(16.Pvs,(2.$;.)Sp(26.R7.R6.R5.)(16.Pvs,(2.$;.)Sp(27.R7.R6.)(19.Pvs,(2.$;.)Sp))))#2.(16.$;.R3.(16.$;.R2.(19.$;.))))")
(* [comment removed for export] *).
  Proof. intros LB lo TOP TOP' b k H x Hx. destruct (H x Hx) as [S|[S|S]]; [left; lia| right; left; exact S| right; right; exact S]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21857564705.1000000@S2lo1b1k2H11x2Hx". (* [comment removed for export] *)
  Lemma cro_stack : forall LB lo TOP b k, lo <= b -> lx_fprop [objP L LB; cwoP LB lo TOP; croP LB lo] 2 [b; k].
  Proof. intros LB lo TOP b k H1 x Hx. left. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma client_wrange_ext : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)PLB',(2.$3.)Plo,$;.PTOP,$;.Pb,$;.Pk,$;.P,(22.VL,R6.R4.R3.R2.R1.)P,Px,$3.P,(11.$3.R1.R8.)(11.$3.R2.R8.)(22.VL,R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB LB' lo TOP b k H EXT x Hx. destruct (H x Hx) as [S|[S|(bb & Hbb & Hr)]]; [left; exact S| right; left; exact S| right; right].
    exists bb. split; [apply EXT; exact Hbb| exact Hr].
  Qed.
  Lemma client_range_ext : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PLB,(2.$3.)PLB',(2.$3.)Plo,$;.Pb,$;.Pk,$;.P,(20.VL,R5.R3.R2.R1.)P,Px,$3.P,(11.$3.R1.R7.)(11.$3.R2.R7.)(20.VL,R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB LB' lo b k H EXT x Hx. destruct (H x Hx) as [S|[S|(bb & Hbb & Hr)]]; [left; exact S| right; left; exact S| right; right].
    exists bb. split; [apply EXT; exact Hbb| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Definition RnameP : hres := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "Lblo,(2.(:.$;.$;.))Lbln,(2.(:.$;.$;.))Lvs,(2.$;.)Lm,P,(4.&40.)(5.(4.&8.))(29.(2.$;.)Lnodes,(2.$;.)(<.(2:.(2.(:.$;.$;.))R4.(2;.(:.$;.$;.)(2<.$;.(:.$;.$;.)La,$;.(28.$;.$;.R1.+40.)(2=.$;.R1.))R5.))(<.(2>.$;.R1.)(<.Px,$;.P,(11.$;.R1.R2.)PB,$;.Pk,$;.P,(11.(:.$;.$;.)(28.$;.$;.R2.R1.)R9.)(21.(=.(1;.R5.+40.)R3.)(=.(1;.R3.R2.)R5.))(<.(9.$;.Lx,$;.(2?.VL,R1.+40.)R1.)(<.(30.$1.L,(2.$31.)$32.R2.R4.(33.$;.#0.R3.=)R1.)P,(1=.(2:.$;.(33.$;.#1.R3.=)=))(2:.(2.$;.)R2.(19.$;.))))))))")
(* [comment removed for export] *).

  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L13768844289.29L59308579027.34L59314938599.30L59315317366.3000000;00P00m01DS1x2cs1y2HyS1x2cs1y2Hy1b1k2Hr2H0S1L4DIM14DIM21x2cs1y2Hy3HAI1DS1L3TOP1x2cs1y2Hy3HAC1S". (* [comment removed for export] *)
  Lemma RnameP_ok : forall TOP, hres_ok usegs (cwP L TOP) RnameP.
  Proof.
    intros TOP blo bln vs m1 m2 (nodes & -> & HND & HAP & HBR & HCH & HR0). intros.
    lazymatch goal with H : (forall x : Z, _ -> in_block _ x -> _ -> _) |- _ => rename H into AG end. exists nodes.
    split; [reflexivity|]. split; [exact HND|]. split; [exact HAP|]. split; [exact HBR|]. split; [| exact HR0].
    pose proof (@alloc_ceiling_lo L) as ACL0.
    eapply chain_mem; [exact HCH| | ].
    - intros x Hx. exact (chain_nodes_in _ _ _ _ _ _ _ _ HCH x Hx).
    - intros x cs Hx HC HSZ. eapply rw_cells_agree; [exact HC|]. rewrite HSZ. change NAME_SIZE with 64. intros y Hy HRy.
      rewrite List.Forall_forall in HBR. destruct (HBR x Hx) as (HA0 & _ & _ & HAC & HAI).
      apply AG; [exact HRy| |].
      + exists (x, 64). split; [apply in_or_app; left; apply in_map_iff; exists x; split; [reflexivity| apply in_rev in Hx; exact Hx]| cbn; lia].
      + intros [S|[(D & _)|(bk & Hbk & Hr)]]; [lia| lia|]. destruct bk as [b k]. cbn in Hr. pose proof (HAP x Hx b k Hbk). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Kit.
(* [comment removed for export] *)
Notation GS7 L lo TOP := [TOP; @hl_stack L; @alloc_ceiling L; @hl_tp L; @hl_img_lo L; @hl_img_hi L; lo].
Notation PROPS3 L LB0 lo TOP := [objP L LB0; cwoP L LB0 lo TOP; croP L LB0 lo].
Notation LH2 L := [lawP L; lawPX L].
Notation HRS1 L := [RnameP L].

(* [comment removed for export] *)
Definition havoc16 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "(16.(:.$;.$34.)(28.$;.$34.+:.^10.)(16.(:.$;.$34.)(28.$;.$34.+5.^11.)(16.(:.$;.$34.)(28.$;.$34.+6.^12.)(16.(:.$;.$34.)(28.$;.$34.+7.^13.)(16.(:.$;.$34.)(28.$;.$34.+;.^14.)(16.(:.$;.$34.)(28.$;.$34.+<.^15.)(16.(:.$;.$34.)(28.$;.$34.+=.^16.)(16.(:.$;.$34.)(28.$;.$34.+>.^17.)(16.(:.$;.$34.)(28.$;.$34.+?.^18.)(16.(:.$;.$34.)(28.$;.$34.+10.^19.)(16.(:.$;.$34.)(28.$;.$34.+11.^1:.)(16.(:.$;.$34.)(28.$;.$34.+1<.^1;.)(16.(:.$;.$34.)(28.$;.$34.+1=.^1<.)(16.(:.$;.$34.)(28.$;.$34.+1>.^1=.)(16.(:.$;.$34.)(28.$;.$34.+1?.^1>.)(19.(:.$;.$34.)))))))))))))))))")
(* [comment removed for export] *).
Definition HC_getnameP : heapcall := HCR 1%nat 4%positive [] None BEOpq None [(0%nat, [q 38; q 16])].
Definition SUM_getnameP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "(35.$36.$37.#?.#18.#4.(16.(:.$;.$34.)(28.$;.$34.+:.^1.)(16.(:.$;.$34.)(28.$;.$34.+;.^2.)(16.(:.$;.$34.)(28.$;.$34.+<.^3.)(16.(:.$;.$34.)(28.$;.$34.+2.^4.)(16.(:.$;.$34.)(28.$;.$34.+4.^5.)(19.(:.$;.$34.)))))))(16.(:.$34.$38.)(28.$34.$38.^6.#0.)(16.(:.$34.$38.)(28.$34.$38.^7.#1.)(16.(:.$34.$38.)(28.$34.$38.^8.#2.)(16.(:.$34.$38.)(28.$34.$38.^9.#3.)(16.(:.$34.$38.)(28.$34.$38.^:.#4.)(16.(:.$34.$38.)(28.$34.$38.^;.#5.)(16.(:.$34.$38.)(28.$34.$38.^=.#6.)(19.(:.$34.$38.)))))))))(39.$34.)(16.$3:.(3;.(3<.^1.)(16.$3=.(3>.&8.(3<.^<.))(19.$3=.)))(16.$3:.(3;.(3<.^3.)(16.$3=.(3?.&30.^2.)(16.$3=.(3>.&8.(40.=))(16.$3=.(3?.&1.^3.)(16.$3=.(3?.&7.^4.)(19.$3=.))))))(19.$3:.)))(41.(:.$34.$34.)(28.$34.$34.^=.^4.))(16.(:.(:.$34.$34.)$34.)(28.(:.$34.$34.)$34.(28.$34.$34.^>.^?.)^1.)(19.(:.(:.$34.$34.)$34.)))(19.$3:.)(16.$42.(43.(3<.^5.)(3<.^9.))(16.$42.(44.(3<.^>.)(3<.^<.))(16.$42.(44.(3<.^<.)(3<.^2.))(16.$42.(44.(3<.^2.)(45.(3<.^>.)(3<.^?.)))(16.$42.(46.(45.(3<.^>.)(3<.^?.))(40.(47.+2.+3?.)))(16.$42.(48.(3<.^1.)(40.+8.)(3<.^3.)(40.+40.))(16.$42.(48.(3<.^1.)(40.+8.)(3<.^>.)(3<.^?.))(16.$42.(48.(3<.^3.)(40.+40.)(3<.^>.)(3<.^?.))(16.$42.(49.(4:.^1.)&3.)(16.$42.(49.(4:.^3.)&3.)(16.$42.(46.(40.=)(3<.^1.))(16.$42.(46.(40.=)(3<.^3.))(16.$42.(46.(40.=)(3<.^>.))(16.$42.(44.(3<.^=.)(45.(45.(3<.^4.)(4;.-1.(40.+:0.)))(4;.-1.(3<.^7.))))(16.$42.(44.(3<.^8.)(3<.^=.))(16.$42.(44.(3<.^4.)(3<.^6.))(16.$42.(49.(4:.^4.)&4.)(16.$42.(46.(3<.^4.)(40.(47.+2.+40.)))(16.$42.(4<.(45.(3<.^1.)(40.+8.))(3<.^=.)(3<.^4.)(3<.^1.))(16.$42.(4<.(45.(3<.^3.)(40.+40.))(3<.^=.)(3<.^4.)(3<.^3.))(16.$42.(4<.(45.(3<.^>.)(3<.^?.))(3<.^=.)(3<.^4.)(3<.^>.))(16.$42.(4=.#1.(16.$4>.(3<.^1.)(16.$4>.(40.+8.)(19.$4>.))))(16.$42.(4=.#1.(16.$4>.(3<.^3.)(16.$4>.(40.+40.)(19.$4>.))))(16.$42.(4=.#2.(16.$4>.(3<.^>.)(16.$4>.(3<.^?.)(19.$4>.))))(19.$42.)))))))))))))))))))))))))(16.(:.$4>.$4>.)(28.$4>.$4>.(3<.^1.)(45.(3<.^1.)(40.+8.)))(16.(:.$4>.$4>.)(28.$4>.$4>.(3<.^3.)(45.(3<.^3.)(40.+40.)))(19.(:.$4>.$4>.))))$4?.(16.$3:.(50.(3<.^=.)(3<.^4.))(16.$3:.(3;.(3<.^1.)(16.$3=.(3>.&8.(3<.^1?.))(19.$3=.)))(16.$3:.(3;.(3<.^3.)(16.$3=.(3>.&8.(3<.^20.))(16.$3=.(3>.&8.(3<.^21.))(16.$3=.(3>.&8.(3<.^22.))(16.$3=.(3>.&8.(3<.^23.))(16.$3=.(3>.&8.(3<.^24.))(16.$3=.(3>.&8.(3<.^25.))(16.$3=.(3>.&8.(3<.^26.))(16.$3=.(3>.&8.(3<.^27.))(19.$3=.))))))))))(19.$3:.))))(16.$42.(46.(40.-3000.)(3<.^10.))(16.$42.(44.(3<.^10.)(40.=))(16.$42.(44.(3<.^<.)(3<.^1?.))(16.$42.(44.(3<.^1?.)(3<.^2.))(19.$42.)))))(19.$38.)(39.$38.)(41.$51.$52.))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Definition havoc4 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "(16.(:.$;.$34.)(28.$;.$34.+5.^4.)(16.(:.$;.$34.)(28.$;.$34.+6.^5.)(16.(:.$;.$34.)(28.$;.$34.+7.^6.)(16.(:.$;.$34.)(28.$;.$34.+;.^7.)(16.(:.$;.$34.)(28.$;.$34.+<.^8.)(16.(:.$;.$34.)(28.$;.$34.+=.^9.)(16.(:.$;.$34.)(28.$;.$34.+>.^:.)(16.(:.$;.$34.)(28.$;.$34.+?.^;.)(16.(:.$;.$34.)(28.$;.$34.+10.^<.)(16.(:.$;.$34.)(28.$;.$34.+11.^=.)(16.(:.$;.$34.)(28.$;.$34.+1<.^>.)(16.(:.$;.$34.)(28.$;.$34.+1=.^?.)(16.(:.$;.$34.)(28.$;.$34.+1>.^10.)(16.(:.$;.$34.)(28.$;.$34.+1?.^11.)(19.(:.$;.$34.))))))))))))))))")
(* [comment removed for export] *).
Definition SUM_memset0P (w : N) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "(53.+46>44.$37.#3.#>.#1.(16.(:.$;.$34.)(28.$;.$34.+:.^1.)(16.(:.$;.$34.)(28.$;.$34.+;.^2.)(16.(:.$;.$34.)(28.$;.$34.+<.^3.)(19.(:.$;.$34.)))))(39.$34.)(16.$3:.(3;.(3<.^1.)(16.$3=.(3?.O1.^1.)(19.$3=.)))(19.$3:.))(39.(:.$34.$34.))(19.(:.(:.$34.$34.)$34.))(19.$3:.)(16.$42.(43.(3<.^2.)(40.=))(16.$42.(43.(3<.^3.)(40.(54.O1.)))(19.$42.)))(16.(:.$4>.$4>.)(28.$4>.$4>.(3<.^1.)(45.(3<.^1.)(40.(54.O1.))))(19.(:.$4>.$4>.)))$55.(16.$3:.(3;.(3<.^1.)(16.$3=.(56.O1.(40.=))(19.$3=.)))(19.$3:.))(19.$42.))")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L11778184105.70L11780626960.52L15032677542.53L15124051453.53L24931956363.49L43322819350.50L44544695689.50L53760326130.49L65510932776.69L65510932776.7000000B00T00c01201A01S01e02702U02VS1w2Hw1A2bs3LBS2ABS1w2Hw1A2bs3LBS2ABS1w1A2bs3LBS2ABS1w1A2bs3LBS2ABS1w1A2bs3LBS2ABS1w2Hw1A2bs3LBS2ABS1w2Hw1A2bs3LBS2ABS1w2Hw1A2bs3LBS2ABS2Hw1A1N2bs1m2P23LBS2AB3HNu2m'F". (* [comment removed for export] *)
Lemma sum_memset0P_valid : forall (w : N) AL, 0 < Z.of_N w < 2^32 -> summary_valid usegs AL (SUM_memset0P w).
Proof.
  intros w AL Hw. unfold SUM_memset0P, havoc4, q. lx_sum_unfold.
  intros A V N bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 _ HA P1 P2.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS). subst x10 x11 x12. rewrite P1, P2.
  assert (LBS : length bs = N.to_nat w) by (destruct HA as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
  pose proof (bytes_at_bound _ _ _ _ (proj2 (proj1 HA))) as AB. cbn [cells_bytes cbytes] in AB. rewrite app_nil_r, LBS in AB.
  assert (HAu : bv_unsigned (Z_to_bv 64 A) = A) by (apply lx_uw64; unfold two64; lia).
  assert (HNu : bv_unsigned (Z_to_bv 64 (Z.of_N w)) = Z.of_N w) by (apply lx_uw64; unfold two64; lia).
  pose proof U_memset_spec as SP. unfold memset_stmt in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 _ _ _ x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m bs); [| exact MI].
    rewrite HAu, HNu. replace (Z.to_nat (Z.of_N w)) with (N.to_nat w) by lia. exact HA. }
  clear SP. intros ms' POST. unfold memset_post in POST. rewrite HAu, HNu, lx_uw64 in POST by (unfold two64; lia).
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & HA').
  change (0 mod 256) with 0 in HA'. replace (Z.to_nat (Z.of_N w)) with (N.to_nat w) in HA' by lia.
  apply evt_done.
  lx_sum_post.
  (* [comment removed for export] *)
  destruct w as [|p]; [cbn in Hw; lia|]. cbn. exact MU.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section Valid.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = 0x3f960.
  Hypothesis HFREE : hl_free L = 0x3fa98.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.

  (* [comment removed for export] *)
  Lemma le8_word_of : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "Pbs,(2.(4.&8.))P,(2:.$38.(57.(4.&8.)R1.)#8.)(2:.(2.(4.&8.))(58.(59.&40.(5:.&40.(5;.R2.))))R2.)")
(* [comment removed for export] *).
  Proof. intros bs H. rewrite Z_to_bv_bv_unsigned. apply le8_le_bytes_to_word. exact H. Qed.

  (* [comment removed for export] *)
  Definition wz (bs : list byte) : Z := bv_unsigned (le_bytes_to_word bs).   (* [comment removed for export] *)
  Fixpoint wchunks (k : nat) (bs : list byte) : list cell :=
    match k with
    | O => []
    | S k' => C8 (Z_to_bv 64 (wz (firstn 8 bs))) :: wchunks k' (skipn 8 bs)
    end.
  Lemma wchunks_wf : forall k bs, cells_wf (wchunks k bs).
  Proof. induction k as [|k IH]; intros bs; cbn; [exact I| split; [exact I| apply IH]]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L36433146347.12L5145511510.12 L63913244806.1100000900B00KS1k2bs2HlS1k2bs2HlS1b2bs2Hl". (* [comment removed for export] *)
  Lemma wchunks_bytes : forall k bs, length bs = (8 * k)%nat -> cells_bytes (wchunks k bs) = bs.
  Proof.
    induction k as [|k IH]; intros bs Hl; cbn [wchunks cells_bytes cbytes].
    - destruct bs; [reflexivity| cbn in Hl; lia].
    - unfold wz at 1. rewrite le8_word_of by (rewrite firstn_length; lia). rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35707271340.11000003S1k". (* [comment removed for export] *)
  Lemma wchunks_size : forall k bs, cells_size (wchunks k bs) = (8 * k)%nat.
  Proof. induction k as [|k IH]; intros bs; cbn [wchunks cells_size csize]; [reflexivity| rewrite IH; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition w8 (bs : list byte) (i : nat) : Z := bv_unsigned (le_bytes_to_word (firstn 8 (skipn (8 * i) bs))).
  Lemma name_blob_words : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "Pm,P,(4.&40.)(5.(4.&8.))PA,$;.Pj48,(2.(4.&8.))Pnx,$;.Pmg,(4.&8.)Ppad7,(2.(4.&8.))P,(5<.$1.R6.R5.(5=.R4.R3.R2.R1.))(5<.$1.R7.R6.(2;.$31.(5>.#6.R5.)(16.$31.(5?.(59.&40.R4.))(16.$31.(5?.(59.&40.(60.(16.(4.&8.)R3.R2.))))(19.$31.)))))")
(* [comment removed for export] *).
  Proof.
    intros m A j48 nx mg pad7 H. pose proof H as H0. destruct H as [[WF _] _]. cbn in WF. destruct WF as (L48 & _ & _ & L7 & _).
    eapply rw_cells_reshape; [exact H0| |].
    - rewrite cells_wf_app. split; [apply wchunks_wf| cbn; repeat split; exact I].
    - rewrite cells_bytes_app, (wchunks_bytes 6 j48) by (rewrite L48; reflexivity). unfold name_blob. cbn [cells_bytes cbytes app].
      change (wz (mg :: pad7)) with (bv_unsigned (le_bytes_to_word (mg :: pad7))). rewrite le8_word_of by (cbn; rewrite L7; reflexivity). rewrite <- ?app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma words_name_blob : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "Pm,P,(4.&40.)(5.(4.&8.))PA,$;.Pz0,$;.Pz1,$;.Pz2,$;.Pz3,$;.Pz4,$;.Pz5,$;.Pnx,$;.Pz7,$;.P,(5<.$1.R:.R9.(16.$31.(5?.(59.&40.R8.))(16.$31.(5?.(59.&40.R7.))(16.$31.(5?.(59.&40.R6.))(16.$31.(5?.(59.&40.R5.))(16.$31.(5?.(59.&40.R4.))(16.$31.(5?.(59.&40.R3.))(16.$31.(5?.(59.&40.R2.))(16.$31.(5?.(59.&40.R1.))(19.$31.))))))))))(29.(2.(4.&8.))Lj48,(2.(4.&8.))(29.(4.&8.)Lmg,(4.&8.)(29.(2.(4.&8.))Lpad7,(2.(4.&8.))(5<.$1.R>.R=.(5=.R3.R6.R2.R1.)))))")
(* [comment removed for export] *).
  Proof.
    intros m A z0 z1 z2 z3 z4 z5 nx z7 H.
    exists (le8 (Z_to_bv 64 z0) ++ le8 (Z_to_bv 64 z1) ++ le8 (Z_to_bv 64 z2) ++ le8 (Z_to_bv 64 z3) ++ le8 (Z_to_bv 64 z4) ++ le8 (Z_to_bv 64 z5)),
           (nth 0 (le8 (Z_to_bv 64 z7)) (Z_to_bv 8 0)), (skipn 1 (le8 (Z_to_bv 64 z7))).
    eapply rw_cells_reshape; [exact H| cbn; repeat split; reflexivity| cbn; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L1283667607.104 L20634578730.141L21309606977.141L22367853296.141L23767186630.100L25310541591.141L25344790145.104L25638420483.104L27803033683.104L30035450845.100L30473894389.141L44307034803.104L5626815944.141 L58972775030.104L59027797549.104L61494456947.141L66422103386.141L68314206323.10400000100^00_01L02D02E02F04505U06306X08G08H09V09W0:<0:=0;OFS2PP3END3CUR2SP1P2bs2mg3AL13AL23SPA2L32p'3Hp'FS2PP3END3CUR2SP1P2bs2mg3AL13AL23SPA2L32p'3Hp'S1L3HLS2lo2PP3CUR2SP2bs3AL13AL23NZ13NZ23ACL3SLO3SPA4ACL0FFS1L3HLS2lo2PP3END3CUR2SP1P3BUF4BLEN2bs2mg3HBL2B12B22B32D12D22D33AL13AL23NZ13NZ23ACL3SLO3SPA3DS33DS23DS14ACL02L3S1L3HLS2lo2PP3CUR2SP3BUF4BLEN2bs2mg3HBL2D12D22D33AL13AL23NZ13NZ23ACL3SLO3SPA3DS33DS23DS14ACL02L3S2PP3CUR2SP2bs3AL13AL23SPA3SPBS2PP3CUR2SP2bs2mg3AL13AL23SPA2L31r2HrS1L3HLS2lo2PP3END3CUR2SP1P3BUF4BLEN2bs2mg3HBL2B12B22B32D12D22D33AL13AL23NZ13NZ23ACL3SLO3SPA3DS33DS23DS14ACL02L3FS1L3HLS2lo2PP3CUR2SP3BUF4BLEN2bs2mg3HBL2B43AL13AL23NZ13NZ23ACL3SLO3SPA4ACL02L3FS2PP3CUR2SP2bs2mg3AL13AL23SPA2L31r2HrFS1L3HLS2lo2PP3END3CUR2SP3BUF4BLEN2bs2mg3HBL2B33AL13AL23NZ13NZ23ACL3SLO3SPA4ACL02L3". (* [comment removed for export] *)
  Lemma sum_getnameP_valid : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PQ,P,$61.SpPLB0,(2.(:.$;.$;.))Plo,$;.PTOP,$;.PMO0,$6.PAL,$62.POPS,(2.P,P,(4.&40.)(5.(4.&8.))Sp)PLAWS,(2.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PCS,P,$;.SpPGX,(2.$;.)PPX,(2.Pvs,(2.$;.)Sp)PLX,(2.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PHX,(2.$63.)(64.$1.R8.(2;.$;.(16.$;.R:.(16.$;.(65.VL,)(16.$;.(23.VL,)(16.$;.(66.VL,)(16.$;.(67.VL,)(16.$;.(68.VL,)(16.$;.R;.(19.$;.))))))))R4.)R7.R6.(2;.Pvs,(2.$;.)Sp(16.Pvs,(2.$;.)Sp(25.VL,R<.)(16.Pvs,(2.$;.)Sp(69.VL,R<.R;.R:.)(16.Pvs,(2.$;.)Sp(6:.VL,R<.R;.)(19.Pvs,(2.$;.)Sp))))R3.)R<.(15.VL,VHI,R:.R9.)(12.VL,R:.)(2;.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(17.VL,)(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(6;.VL,)(19.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)))R2.)(2;.$63.(16.$63.(6<.VL,)(19.$63.))R1.)(6=.$1.R=.)$6>.$52.R5.)")
(* [comment removed for export] *).
  Proof.
    intros Q LB0 lo TOP MO0 AL OPS LAWS CS GX PX LX HX. cbn [app]. split; [reflexivity|]. unfold SUM_getnameP, HC_getnameP, havoc16, q. lx_sum_unfold.
    intros PP END CUR SP TPV TOP' HLS' ACE HLTP IMGLO IMGHI P LO BUF BLEN.
    intros bs b2 b3 b4.
    intros F fc m mo LB.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros _ _ MI G0 G1 G2 G3 G4 G5 G6 R10 R11 R12 R2 R4 ST HPP HCUR [HBUF HBL] TP B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 SLO ACL HTOP SPA SPB DS1 DS2 DS3
      CW1 CW2 CR3 EXT (h & HH & HT & MF) _ K1 _.
    unfold tgt_aevtM. intros MK. subst x10 x11 x12 x2 x4. subst TOP' HLS' ACE HLTP IMGLO IMGHI LO TPV.
    cbn [cwoP croP] in CW1, CW2, CR3.
    pose proof (@alloc_ceiling_lo L) as ACL0.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64; lia).
    (* [comment removed for export] *)
    assert (L3 : length b3 = 1%nat) by (destruct HCUR as [[WF _] _]; cbn in WF; tauto).
    destruct b3 as [|mg [|]]; [discriminate| | discriminate].
    assert (HCUR' : rw_cells usegs m CUR (name_blob b2 0 mg b4)).
    { eapply rw_cells_reshape; [exact HCUR| | reflexivity]. destruct HCUR as [[WF _] _]. cbn in WF |- *. tauto. }
    pose proof (U_x509_get_name_spec L HI HCALLOC HFREE HLS) as SPN. unfold x509_get_name_stmt in SPN.
    eapply aevtM_cut.
    { eapply SPN with (lo := lo) (bs := bs) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (h := h) (LB := LB);
        rewrite ?HSP, ?HT, <- ?HBL; try reflexivity; try eassumption; try lia.
      all: rewrite ?HBL; first [ eapply client_wrange_ext; [eassumption| exact EXT] | eapply client_range_ext; [exact CR3| exact EXT] ]. }
    clear SPN. intros ms' mo2 PO. unfold x509_get_name_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & h' & r & p' & j48 & mg' & pad7 & nodes & E & PO).
    injection E; intros <- ->. rewrite ?HSP in PO.
    destruct PO as (MI' & ST' & MF' & HT' & -> & Hr & HPP' & Hp' & HCUR6 & HCH & HND & HAP & HH' & HPX & Hr0).
    apply name_blob_words in HCUR6. cbn [wchunks app] in HCUR6.
    lx_aevtM_zregs.
    (* [comment removed for export] *)
    eapply (K1 r _ _ _ _ _ _ _ _ _ _ _ _ _ _ p' _ _ _ _ _ _ (hd 0 nodes) _ _ _ (map (fun a => (a, 64)) (rev nodes) ++ LB));
      try eassumption; try reflexivity; try exact I; try lia; try exact (heap_mok _ _ HI _ _ _ _ HH').
    - (* [comment removed for export] *)
      split; [| split; [apply RnameP_ok; [exact DIM1| exact DIM2]| split; [apply cwP_blk| split; [constructor| split; [exact EXT| intros b Hb; apply in_or_app; right; exact Hb]]]]].
      exists nodes. cbn [nth]. split; [reflexivity|]. split; [exact HND|]. split; [exact HAP|]. split; [| split; [exact HCH| exact Hr0]].
      destruct (heap_blocks _ _ HI _ _ _ _ HH') as [HBR _]. rewrite Forall_app in HBR. destruct HBR as [HBR _].
      apply List.Forall_forall. intros x Hx. rewrite List.Forall_forall in HBR. apply (HBR (x, 64)). apply in_map_iff. exists x. split; [reflexivity| apply in_rev in Hx; exact Hx].
    - (* [comment removed for export] *)
      exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
    - (* [comment removed for export] *) intros b Hb. apply in_or_app. right. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L1552573036.124 L23767186630.91 L26229258606.92 L30035450845.91 L34628747056.92 L36145463366.124L4281492471.124 L52154758886.124L5466787776.92  L5564767749.124 L5996035145.92  L66432770007.124L6644464632.92  L6646561273.126 L6753818142.92  L7293058555.124 00000<00a01@01I01_01`01a02B02H02^03003103703?03B03CS1n2Hn1A3HA0S1L1n2SP2LO4HLS'3ACE2G22P32P42P74ACL0S1L2HI1n3TOP2SP4TOP'2G02P61h2HTS1n2SP2P8S1L1n2SP2LO4HLS'2G12P4FFS1L1n5IMGLO5IMGHI2G42G51A3HA03HAIS1n2HnS1L1n3ACE2G21A3HA03HACS1L1n2LO3ACE2G22P3FS1n2HnS1n2Hn1AS1nF". (* [comment removed for export] *)
  Lemma sum_calloc1P_validX : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "Pn,$6?.PQ,P,$61.SpPLB0,(2.(:.$;.$;.))Plo,$;.PTOP,$;.PMO0,$6.PAL,$62.POPS,(2.P,P,(4.&40.)(5.(4.&8.))Sp)PLAWS,(2.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PCS,P,$;.SpPGX,(2.$;.)PPX,(2.Pvs,(2.$;.)Sp)PLX,(2.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PHRS,$70.P,(<.(?.=(54.R>.))(?.(54.R>.)(47.+2.+20.)))(64.$1.R9.(2;.$;.(16.$;.R;.(16.$;.(65.VL,)(16.$;.(23.VL,)(16.$;.(66.VL,)(16.$;.(67.VL,)(16.$;.(68.VL,)(16.$;.R<.(19.$;.))))))))R5.)R8.R7.(16.Pvs,(2.$;.)Sp(25.VL,R=.)R4.)R=.(15.VL,VHI,R;.R:.)(12.VL,R;.)(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(17.VL,)R3.)R2.(6=.$1.R>.)(71.R?.)(72.R?.)R6.)")
(* [comment removed for export] *).
  Proof.
    intros n Q LB0 lo TOP MO0 AL OPS LAWS CS GX PX LX HRS Hn. cbn [app]. split; [reflexivity|]. unfold SUM_calloc1P, HC_calloc1P, havoc13, q. lx_sum_unfold.
    intros cnt sz SP LO TPV TOP' HLS' ACE HLTP IMGLO IMGHI F fc m mo LB.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros _ _ MI G0 G1 G2 G3 G4 G5 R10 R11 R2 R4 ST P1 P2 P5 P3 P4 P6 P7 P8 EXT (h & HH & HT & MF) _ K1 K2.
    unfold tgt_aevtM. intros MK. subst x10 x11 x2 x4. rewrite P1. rewrite P5, G3 in K1, K2 |- *. rewrite P2 in K2 |- *.
    pose proof (@alloc_ceiling_lo L) as ACL0.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64; lia).
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut.
    { eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := Z.of_N n) (lo := LO); rewrite ?HSP; try reflexivity; try eassumption; try lia. }
    intros ms' mo2 PO. unfold call_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & E & PO).
    injection E; intros <- ->. rewrite ?HSP in PO. destruct PO as (MI' & ST' & MF' & HPR & h' & HT' & CASES).
    destruct CASES as [[-> HH']| (A & -> & HBR & HH' & HNEW)]; lx_aevtM_zregs.
    - (* [comment removed for export] *)
      eapply (K1 0); try eassumption; try reflexivity; try exact I; try exact (heap_mok _ _ HI _ _ _ _ HH').
      exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
    - (* [comment removed for export] *)
      destruct HBR as (HA0 & HA16 & _ & HAC & HAI). rewrite Z.mul_1_l in HAC, HAI, HH', HNEW.
      destruct (heap_blocks _ _ HI _ _ _ _ HH') as [_ [HAP _]].
      assert (HOBJ : forall b k, objP L LB0 [b; k] -> k = 0 \/ A + Z.of_N n <= b \/ b + k <= A).
      { intros b k HO. eapply (obj_apart L HI); [exact HH'| exact EXT| exact DIM1| exact DIM2| exact HO| lia]. }
      eapply (K2 A); try eassumption; try lia; try exact (heap_mok _ _ HI _ _ _ _ HH'); try (split; [exact HAP| exact HOBJ]).
      all: try (replace (N.to_nat n) with (Z.to_nat (Z.of_N n)) by lia; exact HNEW).
      all: try (change (2 ^ Z.of_N 4) with 16; exact HA16).
      exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L23767186630.88L26229258606.89L30035450845.88L34628747056.89L5996035145.89 00000S01001701K01[S1L2SP2LO4HLS'3ACE2G22P22P32P54ACL0S1L2HI3TOP2SP4TOP'2G02P41h2HTS2SP2P6S1L2SP2LO4HLS'2G12P3S1L2LO3ACE2G22P2". (* [comment removed for export] *)
  Lemma sum_freeP_validX : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PQ,P,$61.SpPLB0,$73.Plo,$;.PTOP,$;.PMO0,$6.PAL,$62.POPS,(2.P,P,(4.&40.)(5.(4.&8.))Sp)PLAWS,(2.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PCS,P,$;.SpPGX,(2.$;.)PPROPS,(2.P,(2.$;.)Sp)PLX,(2.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PHRS,$70.(64.$1.R8.(2;.$;.(16.$;.R:.(16.$;.(65.VL,)(16.$;.(23.VL,)(16.$;.(66.VL,)(16.$;.(67.VL,)(16.$;.(68.VL,)(16.$;.R;.(19.$;.))))))))R4.)R7.R6.R3.R<.(15.VL,VHI,R:.R9.)(12.VL,R:.)(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(17.VL,)R2.)R1.(6=.$1.R=.)$74.$75.R5.)")
(* [comment removed for export] *).
  Proof.
    intros Q LB0 lo TOP MO0 AL OPS LAWS CS GX PROPS LX HRS. cbn [app]. split; [reflexivity|]. unfold SUM_freeP, HC_freeP, havoc11, q. lx_sum_unfold.
    intros A SP LO TPV TOP' HLS' ACE HLTP IMGLO IMGHI F fc m mo LB.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros _ _ MI G0 G1 G2 G3 G4 G5 R10 R2 R4 ST P1 P2 P3 P4 P5 P6 EXT (h & HH & HT & MF) (n & HIN) K1 _.
    unfold tgt_aevtM. intros MK. subst x10 x2 x4. rewrite P1, G3 in K1 |- *.
    pose proof (@alloc_ceiling_lo L) as ACL0.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64; lia).
    replace (Z_to_bv 64 0x3fa98) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
    eapply aevtM_cut.
    { eapply (heap_free usegs L HI) with (lo := LO); rewrite ?HSP; try reflexivity; try eassumption; try lia. }
    intros ms' mo2 PO. unfold call_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & E & PO).
    injection E; intros <- ->. rewrite ?HSP in PO. destruct PO as (MI' & ST' & MF' & HPR & h' & HT' & HH').
    lx_aevtM_zregs.
    eapply (K1 (bv_unsigned a0')); try eassumption; try reflexivity; try exact I; try exact (heap_mok _ _ HI _ _ _ _ HH').
    exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sum_plain_MR : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "PAL,$62.PGS,(2.$;.)POPS,(2.P,P,(4.&40.)(5.(4.&8.))Sp)PLAWS,(2.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PPROPS,(2.P,(2.$;.)Sp)PLB0,(2.(:.$;.$;.))PHP,P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,$6.SpPCW,P,(2.(:.$;.$;.))P,$;.SpPLH,(2.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)PHRS,$70.PTGT,P,$6.P,$76.SpPCS,P,$;.SpPsu,$77.P,(2:.(2.(:.$34.$38.))(78.R1.)(19.(:.$34.$38.)))P,(79.$1.R>.R2.)(7:.$1.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su E V. apply summary_okG_MR. apply apply_summary_soundG.
    apply (summary_validG_ext usegs AL [] GS su); [rewrite E; reflexivity| exact V].
  Qed.
  Lemma sums_plain_MR : forall AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS l,
    forallb (fun su => match su_gbind su with [] => true | _ => false end) l = true ->
    Forall (summary_valid usegs AL) l -> Forall (summary_okMR usegs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS) l.
  Proof.
    intros AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS l Hg V. induction V as [|su l Vs Vl IH]; [constructor|].
    cbn [forallb] in Hg. apply andb_prop in Hg as [H1 H2]. constructor; [| apply IH; exact H2].
    apply sum_plain_MR; [| exact Vs]. destruct (su_gbind su); [reflexivity| discriminate].
  Qed.

  (* [comment removed for export] *)
  Lemma SUMS_nameP_ok : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsHeapO ()) "Pn,$6?.PQ,P,$61.SpPLB0,(2.(:.$;.$;.))Plo,$;.PTOP,$;.PMO0,$6.P,(<.(?.=(54.R6.))(?.(54.R6.)(47.+2.+20.)))(9.$77.(7:.$1.$7;.(16.$;.R3.(16.$;.(65.VL,)(16.$;.(23.VL,)(16.$;.(66.VL,)(16.$;.(67.VL,)(16.$;.(68.VL,)(16.$;.R4.(19.$;.))))))))(19.P,P,(4.&40.)(5.(4.&8.))Sp)(19.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)(16.Pvs,(2.$;.)Sp(25.VL,R5.)(16.Pvs,(2.$;.)Sp(69.VL,R5.R4.R3.)(16.Pvs,(2.$;.)Sp(6:.VL,R5.R4.)(19.Pvs,(2.$;.)Sp))))R5.(15.VL,VHI,R3.R2.)(12.VL,R3.)(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(17.VL,)(16.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp(6;.VL,)(19.P,(2.(:.$;.$;.))P,$;.P,(2.(:.$;.$;.))P,P,(4.&40.)(5.(4.&8.))P,P,(4.&40.)(5.(4.&8.))Sp)))(16.$63.(6<.VL,)(19.$63.))(6=.$1.R6.)L,$;.$32.)(16.$77.(71.R7.)(16.$77.$74.(16.$77.$6>.(19.$77.)))))")
(* [comment removed for export] *).
  Proof.
    intros. constructor; [|constructor; [|constructor; [|constructor]]].
    - eapply apply_summary_soundMR. apply (sum_calloc1P_validX n Q LB0 lo TOP MO0 _ _ _ _ [] _ _ _). assumption.
    - eapply apply_summary_soundMR. apply (sum_freeP_validX Q LB0 lo TOP MO0 _ _ _ _ [] _ _ _).
    - eapply apply_summary_soundMR. apply (sum_getnameP_valid Q LB0 lo TOP MO0 _ _ _ _ [] [] [] []).
  Qed.
End Valid.
