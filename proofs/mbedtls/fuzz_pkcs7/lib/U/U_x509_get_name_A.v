(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA X509Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_x509_get_name_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "Stdlib.Lists.List.hd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "x509_get_name_post"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove_all"; "Stdlib.Lists.List.last"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Walk.nLBof"; "Walk.nfresh"; "Walk.curF"; "Walk.headrep"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_lseg"; "Stdlib.Lists.List.removelast"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Walk.frame_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Walk.W"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"].


Definition U_X509_GET_NAME : Z := 0x27d34.
Definition U_CALLOC : Z := 0x3f960.
Notation X509_GET_NAME_STACK := 160 (only parsing).
(* [comment removed for export] *)
Notation K1W := (Z_to_bv 64 18446744073709542426) (only parsing).
Notation K2W := (Z_to_bv 64 18446744073709542432) (only parsing).

Definition x509_get_name_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (PP CUR P END lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1>.O1=.O1<.)Lh',(5.O1>.O1=.O1<.)(1.$6.Lr,$6.(1.$6.Lp',$6.(1.(7.(2.&8.))Lj48,(7.(2.&8.))(1.(2.&8.)Lmg,(2.&8.)(1.(7.(2.&8.))Lpad7,(7.(2.&8.))(1.(7.$6.)Lnodes,(7.$6.)(8.(9.$0.R19.(:.(;.(<.O1;.O1:.O19.O18.R18.R17.R16.O17.O16.R15.R14.R13.R12.R11.R10.R?.R>.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R=.R<.R;.R:.)O;.(=.O1;.)O:.(>.(2.&40.))R9.(?.O1>.))R8.))(8.(10.O1>.R9.)(8.(11.O1>.R9.O3.(12.&40.O1:.))(8.(13.O1.R8.)(8.(9.$6.(14.O1>.O1=.O1<.R7.)(14.O1>.O1=.O1<.O9.))(8.(9.(2.&40.)R15.(15.&40.R6.))(8.(8.(16.-3000.R6.)(17.R6.=))(8.(18.O1>.R9.O7.(19.$1:.(1;.(15.&40.R5.))(1<.$1:.)))(8.(8.(17.O5.R5.)(17.R5.O4.))(8.(18.O1>.R9.O6.(1=.R4.(1>.$6.=R1.)R3.R2.))(8.(1?.O1>.L,(7.$1:.)$20.R9.(21.(22.$6.$6.)(23.$6.(22.$6.$6.)La,$6.(24.$6.$6.R1.+40.)(25.$6.R1.))O8.)(1>.$6.=R1.)R1.)(8.(26.$6.R1.)(8.Px,$6.P,(27.$6.R1.R2.)PB,$6.Pk,$6.P,(27.(22.$6.$6.)(24.$6.$6.R2.R1.)O8.)(28.(17.(29.R5.+40.)R3.)(17.(29.R3.R2.)R5.))(8.(2:.O1>.O1=.O1<.R7.(21.(22.$6.$6.)(23.$6.(22.$6.$6.)La,$6.(24.$6.$6.R1.+40.)(25.$6.R1.))O8.)R9.R8.)(8.(2;.O1>.O1=.O8.(12.&40.O1:.)(19.(22.$6.$6.)(24.$6.$6.O7.(29.O7.+8.))(19.(22.$6.$6.)(24.$6.$6.O6.(29.O6.+40.))(1<.(22.$6.$6.))))O2.R9.)P,(2<.(9.$6.R6.=))(9.(7.$6.)R2.(1<.$6.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_name_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O4.O3.O2.)PLB,(7.$2>.)PPP,$6.PCUR,$6.PP,$6.PEND,$6.PBUF,$6.Plo,$6.Pbs,(7.(2.&8.))Pj48,(7.(2.&8.))Pmg,(2.&8.)Ppad7,(7.(2.&8.))P,(2:.O4.O3.O2.R<.R;.R>.R=.)P,(18.O4.R?.R;.(19.$1:.(1;.(15.&40.R9.))(1<.$1:.)))P,(18.O4.R10.R;.(1=.R5.=R4.R3.))P,(2?.O4.R11.R9.R7.)P,(17.R:.R<.)P,(17.R=.R<.)P,(17.R=.(29.R<.(30.(31.(2.&8.)R:.))))P,(16.(29.R=.(30.(31.(2.&8.)R;.)))(32.+2.+3?.))P,(28.(17.(29.R12.+8.)R11.)(17.(29.R11.+40.)R12.))P,(28.(17.(29.R13.+8.)R?.)(17.(29.R?.(30.(31.(2.&8.)R=.)))R13.))P,(28.(17.(29.R13.+40.)R10.)(17.(29.R10.(30.(31.(2.&8.)R>.)))R13.))P,(9.$6.(33.R15.+8.)=)P,(9.$6.(33.R15.+8.)=)P,(16.=R17.)P,(16.=R17.)P,(16.=R15.)P,(11.O4.R1>.R15.(12.&40.R3>.))P,(17.R16.(34.(34.(12.&40.R3?.)+:0.)(35.O3.)))P,(17.(36.O3.)R17.)P,(17.(12.&40.R41.)(14.O4.O3.O2.R1?.))P,(9.$6.(33.(12.&40.R42.)+10.)=)P,(17.(37.O3.)(36.O3.))P,(17.(38.O3.)(39.O3.))P,(17.(37.O3.)(3:.O3.))P,(28.(17.(29.R22.+8.)R1=.)(17.(12.&40.R46.)R22.))P,(28.(17.(29.R22.+40.)R1>.)(17.(12.&40.R47.)R22.))P,(28.(17.(29.R20.(30.(31.(2.&8.)R1>.)))R1?.)(17.(12.&40.R48.)R20.))P,(3;.O3.R26.R20.(14.O4.O3.O2.R27.)R25.+8.)P,(3;.O3.R27.R21.(14.O4.O3.O2.R28.)R25.+40.)P,(3<.O3.R28.R22.R23.(30.(31.(2.&8.)R21.)))P,(9.(2.&40.)R4:.(15.&40.(3=.O3.)))P,(10.O4.R2=.)P,(9.(2.&40.)R46.(15.&40.R2:.))P,(9.(2.&40.)R46.(15.&40.R28.))P,(9.(2.&40.)R46.(15.&40.R2;.))(3>.O4.R30.(3?.O4.O3.O2.R52.R51.R50.R4?.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R33.R32.R2?.R2>.R2=.R2<.R2;.R2:.R28.R31.R30.)(;.(<.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(15.&40.O1.)R32.(>.(2.&40.))R31.(?.O4.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma lb_remove_notfirst : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pa,$6.PLB1,(7.(22.$6.$6.))PLB2,(7.(22.$6.$6.))P,Pk,$6.(2<.(27.(22.$6.$6.)(24.$6.$6.R4.R1.)R3.))(9.(7.$2>.)(40.R4.(21.(22.$6.$6.)R3.R2.))(21.(22.$6.$6.)R3.(40.R4.R2.)))")
(* [comment removed for export] *).
Proof.
  intros a LB1 LB2. induction LB1 as [|[b k] r IH]; cbn; intros H; [reflexivity|].
  destruct (Z.eqb_spec b a) as [->|NE]; [exfalso; apply (H k); left; reflexivity|].
  cbn. rewrite IH; [reflexivity|]. intros k' Hk'. apply (H k'). right. exact Hk'.
Qed.

Lemma lb_remove_all_new : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)PLB,(7.$2>.)P,(26.$6.R2.)(9.(7.$2>.)(41.R3.(21.(22.$6.$6.)(23.$6.(22.$6.$6.)La,$6.(24.$6.$6.R1.+40.)(25.$6.R3.))R2.))R2.)")
(* [comment removed for export] *).
Proof.
  induction nodes as [|a r IH]; intros LB HND; cbn [lb_remove_all rev map app]; [reflexivity|].
  inversion HND as [|a' r' Hna Hr]; subst.
  rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
  rewrite lb_remove_notfirst.
  - cbn [lb_remove fst]. rewrite Z.eqb_refl. apply IH. exact Hr.
  - intros k Hk. apply in_map_iff in Hk. ddestruct Hk as (x & E & Hx). injection E as -> _. apply Hna. apply in_rev. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma removelast_last_app : forall (l : list Z) d, l <> [] -> removelast l ++ [last l d] = l.
Proof. intros l d H. symmetry. apply app_removelast_last. exact H. Qed.

Lemma hd_app_ne : forall (l l' : list Z) d, l <> [] -> hd d (l ++ l') = hd d l.
Proof. intros [|a l] l' d H; [congruence| reflexivity]. Qed.

Lemma in_removelast : forall (l : list Z) x, In x (removelast l) -> In x l.
Proof.
  intros l x H. destruct l as [|a r]; [exact H|].
  rewrite <- (removelast_last_app (a :: r) 0) by congruence. apply in_or_app. left. exact H.
Qed.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP CUR P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 64 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 64 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 64 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 64 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top usegs L HI h) CUR 64.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 64)].
  Notation POST := (x509_get_name_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -144)).

  Definition nLBof (nodes : list Z) : list blk := map (fun a => (a, 64)) (rev nodes) ++ LB.

  Definition nfresh (nodes : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Px,$6.P,(27.$6.R1.O1.)(8.(17.(29.R2.+40.)(36.VL,))(8.(28.(17.(29.R2.+40.)(38.VL,))(17.(3:.VL,)R2.))PB,$6.Pk,$6.P,(27.(22.$6.$6.)(24.$6.$6.R2.R1.)VLB,)(28.(17.(29.R5.+40.)R3.)(17.(29.R3.R2.)R5.))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition W (cur : Z) : list ivl := [(PP, PP + 8); (cur, cur + 64); (bv_unsigned sp - 144, bv_unsigned sp)].

  (* [comment removed for export] *)
  Definition curF (nodes : list Z) (cur : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "(8.(9.$6.(33.O1.+8.)=)(8.(16.=O1.)(8.(17.(29.O1.+40.)(32.+2.+40.))(8.(28.(17.(29.VPP,+8.)O1.)(17.(29.O1.+40.)VPP,))(8.(28.(17.(29.O1.+40.)VBUF,)(17.(29.VBUF,(30.(31.(2.&8.)Vbs,)))O1.))(8.(28.(17.(29.O1.+40.)Vlo,)(17.(12.&40.Vsp,)O1.))(28.(8.(9.(7.$6.)O2.(1<.$6.))(9.$6.O1.VCUR,))(8.(2<.(9.(7.$6.)O2.(1<.$6.)))(8.(9.$6.O1.(42.$6.O2.=))(8.(9.$6.(33.O1.+10.)=)(28.(17.(29.O1.+40.)VCUR,)(17.(29.VCUR,+40.)O1.))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition headrep (mm : mem) (nodes : list Z) : Prop :=
    nodes = [] \/ exists j48 mg p7, rw_cells usegs mm CUR (name_blob j48 (hd 0 nodes) mg p7).

  Definition frame_hi : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition ninv (c1 c2 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI) (nodes : list Z) (cur : Z)
             (slen alen : word) (j8 : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "(8.(2:.$43.VL,VHI,O6.(44.O5.)O8.O7.)(8.(9.$6.(14.$43.VL,VHI,O6.)(14.$43.VL,VHI,Vh,))(8.(26.$6.O5.)(8.(45.O5.)(8.(46.O5.O4.)(8.(47.O8.O5.)(8.(48.$43.O8.(44.O5.)(49.$6.O5.)(42.$6.O5.=))(8.(18.$43.O8.(29.(12.&40.Vsp,)-90.)(19.$1:.(1;.(15.&40.+????????????=<1>.))(19.$1:.(1;.O:.)(19.$1:.(1;.O9.)(1<.$1:.)))))(8.(18.$43.O8.(29.(12.&40.Vsp,)-78.)(19.$1:.(1;.O3.)(1<.$1:.)))(8.(18.$43.O8.(29.(12.&40.Vsp,)-70.)(19.$1:.(1;.O2.)(1<.$1:.)))(8.(18.$43.O8.(29.(12.&40.Vsp,)-68.)$4;.)(8.(11.$43.O8.Vlo,(29.(12.&40.Vsp,)-90.))(8.(10.$43.O8.)(8.(2?.$43.O8.VBUF,Vbs,)(8.(2;.$43.VL,VLB,(12.&40.Vsp,)(19.(22.$6.$6.)(24.$6.$6.VPP,(29.VPP,+8.))(19.(22.$6.$6.)(24.$6.$6.VCUR,(29.VCUR,+40.))(1<.(22.$6.$6.))))Vm,O8.)(13.Vmo,O7.))))))))))))))))")
(* [comment removed for export] *).

  #[using="HBR0"] Lemma in_block_below : forall a, in_block LB a -> a < alloc_ceiling.
  Proof.
    clear -HBR0. (intros a dd_H; ddestruct dd_H as (b & Hb & Hr)). rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Hc & _). lia.
  Qed.

  #[using="Type"] Lemma nLBof_snoc : forall nodes N, nLBof (nodes ++ [N]) = (N, 64) :: nLBof nodes.
  Proof. intros. unfold nLBof. rewrite rev_app_distr. reflexivity. Qed.

  #[using="Type"] Lemma nLBof_sub : forall nodes b, In b LB -> In b (nLBof nodes).
  Proof. intros. unfold nLBof. apply in_or_app. right. assumption. Qed.

  #[using="Type"] Lemma nLBof_in : forall nodes x, In x nodes -> In (x, 64) (nLBof nodes).
  Proof. intros. unfold nLBof. apply in_or_app. left. apply in_map_iff. exists x. split; [reflexivity|]. rewrite <- in_rev. exact H. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma presx_munch : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "PWx,(7.$4<.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(4=.R3.R2.R1.)P,(4>.$43.R3.R2.)P,Pa,$6.P,(8.(17.=R1.)(16.R1.(32.+2.+40.)))P,(28.(17.(12.&40.Vsp,)R2.)(28.(8.(17.(39.VL,)R2.)(16.R2.(37.VL,)))(4?.VLB,R2.)))P,(50.(19.(22.$6.$6.)(24.$6.$6.VPP,(29.VPP,+8.))(19.(22.$6.$6.)(24.$6.$6.VCUR,(29.VCUR,+40.))(1<.(22.$6.$6.))))R3.)(50.R9.R4.)(2;.$43.VL,VLB,(12.&40.Vsp,)(19.(22.$6.$6.)(24.$6.$6.VPP,(29.VPP,+8.))(19.(22.$6.$6.)(24.$6.$6.VCUR,(29.VCUR,+40.))(1<.(22.$6.$6.))))R5.R4.)")
(* [comment removed for export] *).
  Proof.
    clear. intros Wx mm m1 MU WM HW. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. apply HW; [exact Ha| | exact Ho].
    destruct Hc as [Hs|[[Hd1 Hd2]|Hb]]; [left; exact Hs| right; left; lia| right; right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  #[using="DIM1 DIM2"] Lemma cur_cases : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.P,(45.R2.)P,(46.R3.R2.)(28.(9.$6.R3.VCUR,)(8.(27.$6.R3.R4.)(8.(17.(29.R3.+40.)(36.VL,))(8.(28.(17.(29.R3.+40.)(39.VL,))(17.(37.VL,)R3.))PB,$6.Pk,$6.P,(27.(22.$6.$6.)(24.$6.$6.R2.R1.)VLB,)(28.(17.(29.R6.+40.)R3.)(17.(29.R3.R2.)R6.))))))")
(* [comment removed for export] *).
  Proof.
    clear -DIM1 DIM2. (intros nodes cur HFR dd_H; ddestruct dd_H as (_ & _ & _ & _ & _ & _ & [[_ ->]|(Hne & -> & _ & _)])); [left; reflexivity| right].
    assert (HIN : In (last nodes 0) nodes).
    { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
    destruct (HFR _ HIN) as (A1 & A2 & A3). split; [exact HIN|]. split; [exact A1|]. split; [lia| exact A3].
  Qed.

  #[using="SLO HLS ACL DHI DIM1 DIM2 HBR0"] Lemma presx_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(45.R4.)P,(46.R5.R4.)P,(4=.(51.R5.)R4.R3.)P,(4>.$43.R5.R4.)P,(2;.$43.VL,VLB,(12.&40.Vsp,)(19.(22.$6.$6.)(24.$6.$6.VPP,(29.VPP,+8.))(19.(22.$6.$6.)(24.$6.$6.VCUR,(29.VCUR,+40.))(1<.(22.$6.$6.))))Vm,R6.)(2;.$43.VL,VLB,(12.&40.Vsp,)(19.(22.$6.$6.)(24.$6.$6.VPP,(29.VPP,+8.))(19.(22.$6.$6.)(24.$6.$6.VCUR,(29.VCUR,+40.))(1<.(22.$6.$6.))))Vm,R6.)")
(* [comment removed for export] *).
  Proof.
    clear -DIM1 DIM2 HBR0 ACL SLO HLS DHI. intros nodes cur mm m1 HFR HCF MU WM HPX.
    eapply heap_presx_trans; [exact HPX|]. eapply presx_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. cbn [outside W] in Ho |- *.
    destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & HC & HD & HAP)].
    - destruct Hc as [Hs|[Hd|Hb]]; [lia| lia| pose proof (in_block_below a Hb); lia].
    - destruct Hc as [Hs|[Hd|Hb]]; [lia| lia|].
      ddestruct Hb as (b & Hb & Hr). destruct b as [B j]. cbn in Hr. pose proof (HAP B j Hb).
      pose proof (in_block_below a ltac:(exists (B, j); split; [exact Hb| cbn; lia])). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SLO HLS ACL HTOP DIM1 DIM2 CWPP CWCUR"] Lemma heap_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$43.VL,VHI,)PLBx,(7.$2>.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))Pmoc,$4.P,(45.R7.)P,(46.R8.R7.)P,(2:.$43.VL,VHI,R7.R6.R5.R3.)P,(9.$6.(14.$43.VL,VHI,R8.)(14.$43.VL,VHI,Vh,))P,Pb,$2>.P,(27.$2>.R1.(44.R<.))(27.$2>.R2.R:.)P,(4=.(51.R;.)R8.R7.)P,(4>.$43.R9.R8.)(2:.$43.VL,VHI,R<.R;.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    clear -ACL CWPP CWCUR SLO HLS HTOP DIM1 DIM2. intros nodes cur hc LBx mm m1 moc HFR HCF HH HT HS MU WM.
    eapply HEAP_munch; [exact HH| exact ACL| exact MU| exact WM|].
    intros a Ha Hin. cbn [outside W] in Hin. rewrite HT.
    assert (HS' : forall b, In b LB -> In b LBx) by (intros b Hb; apply HS; apply nLBof_sub; exact Hb).
    destruct (outside_dec [(PP, PP + 8)] a) as [O1|O1]; cbn [outside] in O1.
    2:{ exact (client_wrange_mono L _ _ _ _ _ _ CWPP HS' a ltac:(lia)). }
    destruct (outside_dec [(bv_unsigned sp - 144, bv_unsigned sp)] a) as [O3|O3]; cbn [outside] in O3.
    2:{ left. lia. }
    assert (HA : cur <= a < cur + 64) by lia.
    destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & _)].
    - exact (client_wrange_mono L _ _ _ _ _ _ CWCUR HS' a HA).
    - right. right. exists (cur, 64). split; [apply HS; apply nLBof_in; exact HIN| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="h ACL DIM1 DIM2 CWPP"] Lemma others_apart : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$43.VL,VHI,)PLBx,(7.$2>.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Py,$6.P,(2:.$43.VL,VHI,R5.R4.R3.R2.)P,Pb,$2>.P,(27.$2>.R1.(44.R9.))(27.$2>.R2.R7.)P,(26.$6.R9.)P,(45.R:.)P,(46.R;.R:.)P,(27.$6.R6.(49.$6.R<.))(8.(28.(17.(29.R7.+40.)VPP,)(17.(29.VPP,+8.)R7.))(8.(28.(17.(29.R7.+40.)R<.)(17.(29.R<.+40.)R7.))(17.(29.R7.+40.)(36.VL,))))")
(* [comment removed for export] *).
  Proof.
    clear -ACL CWPP CWCUR DIM1 DIM2. intros nodes cur hc LBx mm moc y HH HS HND HFR HCF Hy.
    pose proof (in_removelast _ _ Hy) as HyN.
    ddestruct (HFR y HyN) as (HC & HD & HAP).
    assert (HD' : y + 64 <= hl_data_lo L \/ hl_data_hi L <= y) by lia.
    split; [| split; [| exact HC]].
    - eapply client_wrange_apart; [exact CWPP| lia| lia| exact ACL| exact HC| exact HD'| exact HAP].
    - ddestruct HCF as (_ & _ & _ & _ & _ & _ & [[-> ->]|(Hne & -> & _ & _)]); [destruct Hy|].
      destruct (heap_blocks _ _ HI _ _ _ _ HH) as [_ HAPc].
      assert (NE : y <> last nodes 0).
      { intros E. rewrite <- (removelast_last_app nodes 0) in HND by exact Hne.
        apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
      eapply blocks_apart_in2; [exact HAPc| apply HS; apply nLBof_in; exact HyN| apply HS; apply nLBof_in| exact NE].
      rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity.
  Qed.

  #[using="h SLO HLS ACL DIM1 DIM2 CWPP"] Lemma lseg_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$43.VL,VHI,)PLBx,(7.$2>.)PLBn,(7.$2>.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Pfin,$6.P,(2:.$43.VL,VHI,R7.R6.R4.R2.)P,Pb,$2>.P,(27.$2>.R1.(44.R;.))(27.$2>.R2.R9.)P,(26.$6.R;.)P,(45.R<.)P,(46.R=.R<.)P,(48.$43.R9.R:.(49.$6.R>.)R6.)P,(4=.(51.R>.)R:.R9.)P,(4>.$43.R;.R:.)(48.$43.R;.R=.(49.$6.R11.)R9.)")
(* [comment removed for export] *).
  Proof.
    clear -ACL CWPP CWCUR DIM1 DIM2 SLO HLS. intros nodes cur hc LBx LBn mm m1 moc fin HH HS HND HFR HCF HL MU WM.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
    ddestruct (others_apart nodes cur hc LBx mm moc y HH HS HND HFR HCF Hy) as (A1 & A2 & A3).
    cbn [disjoint_from W]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="L D1 SLO HLS DS2"] Lemma headrep_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(46.R4.R3.)P,(47.R3.R5.)P,(4=.(51.R5.)R4.R3.)P,(4>.$43.R5.R4.)(47.R5.R8.)")
(* [comment removed for export] *).
  Proof.
    clear -D1 DS2 SLO HLS. intros nodes cur mm m1 HCF [->|(j48 & mg & p7 & HR)] MU WM; [left; reflexivity|].
    ddestruct HCF as (_ & _ & _ & _ & _ & _ & [[-> _]|(Hne & _ & _ & AP)]); [left; reflexivity| right].
    dexists j48, mg, p7. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="D1 SLO HLS ACL HTOP DHI DIM1 DIM2 DS2 CWPP CWCUR HBR0"] Lemma sync_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$43.VL,VHI,)PLBx,(7.$2>.)PLBn,(7.$2>.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Pfin,$6.P,(2:.$43.VL,VHI,R7.R6.R4.R2.)P,(9.$6.(14.$43.VL,VHI,R8.)(14.$43.VL,VHI,Vh,))P,Pb,$2>.P,(27.$2>.R1.(44.R<.))(27.$2>.R2.R:.)P,(26.$6.R<.)P,(45.R=.)P,(46.R>.R=.)P,(47.R:.R?.)P,(48.$43.R;.R<.(49.$6.R10.)R8.)P,(2;.$43.VL,VLB,(12.&40.Vsp,)(19.(22.$6.$6.)(24.$6.$6.VPP,(29.VPP,+8.))(19.(22.$6.$6.)(24.$6.$6.VCUR,(29.VCUR,+40.))(1<.(22.$6.$6.))))Vm,R<.)P,(4=.(51.R11.)R=.R<.)P,(4>.$43.R>.R=.)(8.(2:.$43.VL,VHI,R12.R11.R>.R=.)(8.(47.R>.R14.)(8.(48.$43.R>.R10.(49.$6.R14.)R<.)(2;.$43.VL,VLB,(12.&40.Vsp,)(19.(22.$6.$6.)(24.$6.$6.VPP,(29.VPP,+8.))(19.(22.$6.$6.)(24.$6.$6.VCUR,(29.VCUR,+40.))(1<.(22.$6.$6.))))Vm,R>.))))")
(* [comment removed for export] *).
  Proof.
    intros nodes cur hc LBx LBn mm m1 moc fin HH HT HS HND HFR HCF HHD HL HPX MU WM.
    split; [eapply heap_W; eassumption|]. split; [eapply headrep_W; eassumption|].
    split; [eapply lseg_W; eassumption| eapply presx_W; eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma close_nodes : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))PJ,(7.(2.&8.))PMG,(2.&8.)PP7,(7.(2.&8.))P,(46.R6.R5.)P,(47.R5.R7.)P,(48.$43.R6.(44.R8.)(49.$6.R8.)(42.$6.R8.=))P,(18.$43.R7.R8.(1=.R6.=R5.R4.))(8.(1.(7.(2.&8.))Lj48,(7.(2.&8.))(1.(2.&8.)Lmg,(2.&8.)(1.(7.(2.&8.))Lp7,(7.(2.&8.))(18.$43.R;.VCUR,(1=.R3.(1>.$6.=R=.)R2.R1.)))))(48.$43.R8.(44.R:.)R:.=))")
(* [comment removed for export] *).
  Proof.
    clear. intros nodes cur mm J MG P7 HCF HHD HL HR.
    ddestruct HCF as (AL & POS & _ & _ & _ & _ & [[-> ->]|(Hne & -> & A16 & _)]).
    - split; [dexists J, MG, P7; exact HR| exact I].
    - destruct HHD as [E|HHD]; [exfalso; exact (Hne E)|]. split; [exact HHD|].
      rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply name_lseg_app. split; [exact HL|].
      cbn [name_lseg hd]. split; [apply nLBof_in|].
      { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
      split; [exact A16|]. split; [exact POS|]. split; [| exact I]. dexists J, MG, P7. exact HR.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma close_fin : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))PJ,(7.(2.&8.))PMG,(2.&8.)PP7,(7.(2.&8.))Pfin,$6.PLBx,(7.$2>.)P,(46.R8.R7.)P,(48.$43.R7.(44.R9.)(49.$6.R9.)(42.$6.R9.=))P,(18.$43.R8.R9.(1=.R7.R4.R6.R5.))P,Pb,$2>.P,(27.$2>.R1.(44.R<.))(27.$2>.R2.R6.)(48.$43.R:.R5.R<.R6.)")
(* [comment removed for export] *).
  Proof.
    clear. intros nodes cur mm J MG P7 fin LBx HCF HL HR HS.
    destruct nodes as [|n0 rest0]; [exact I|]. assert (Hne : n0 :: rest0 <> []) by discriminate. revert Hne HCF HL HS. generalize (n0 :: rest0). clear n0 rest0. intros nodes Hne HCF HL HS.
    ddestruct HCF as (AL & POS & _ & _ & _ & _ & [[E _]|(_ & -> & A16 & _)]); [exfalso; exact (Hne E)|].
    eapply name_lseg_mem; [| intros x Hx; apply HS; apply nLBof_in; exact Hx| intros x cs _ HRx _; exact HRx].
    rewrite <- (removelast_last_app nodes 0) at 1 by exact Hne. apply name_lseg_app. split; [exact HL|].
    cbn [name_lseg hd]. split; [apply nLBof_in|].
    { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
    split; [exact A16|]. split; [exact POS|]. split; [| exact I]. dexists J, MG, P7. exact HR.
  Qed.

  #[using="Type"] Lemma headrep_snoc : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))PJ,(7.(2.&8.))PMG,(2.&8.)PP7,(7.(2.&8.))PN,$6.P,(46.R7.R6.)P,(47.R6.R8.)P,(18.$43.R7.R8.(1=.R6.R3.R5.R4.))(47.R8.(21.$6.R:.(19.$6.R4.(1<.$6.))))")
(* [comment removed for export] *).
  Proof.
    clear. intros nodes cur mm J MG P7 N HCF HHD HR. right.
    ddestruct HCF as (_ & _ & _ & _ & _ & _ & [[-> ->]|(Hne & _ & _ & _)]).
    - dexists J, MG, P7. exact HR.
    - destruct HHD as [E|(j48 & mg & p7 & HH)]; [exfalso; exact (Hne E)|]. dexists j48, mg, p7. rewrite hd_app_ne by exact Hne. exact HH.
  Qed.

  (* [comment removed for export] *)
  #[using="HI h lo DS2 CWCUR"] Lemma headrep_pres : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)PLBx,(7.$2>.)Pmm,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))P,(52.$43.VL,R3.(29.(12.&40.Vsp,)-90.)R2.R1.)P,Pb,$2>.P,(27.$2>.R1.VLB,)(27.$2>.R2.R6.)P,(47.R4.R6.)(47.R4.R7.)")
(* [comment removed for export] *).
  Proof.
    clear -CWCUR DS2. intros nodes LBx mm m2 HP HS [->|(j48 & mg & p7 & HR)]; [left; reflexivity| right].
    dexists j48, mg, p7. eapply heap_pres_rw_cells; [exact HP| exact HR|].
    eapply client_range_wsep; [exact CWCUR| exact HS| cbn; lia].
  Qed.

  #[using="Type"] Lemma lseg_pres : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "PLBx,(7.$2>.)Pl,(7.$6.)Pfin,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))PSP,$6.P,(52.$43.VL,R6.R1.R3.R2.)P,(48.$43.R4.R7.R6.R5.)(48.$43.R4.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    clear. intros LBx l fin mm m2 SP HP HL.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply heap_pres_rw_cells; [exact HP| exact HR|]. rewrite Hsz.
    eapply client_range_block; [eapply name_lseg_in; [exact HL| exact Hy] | lia | cbn; lia].
  Qed.

  #[using="DIM1 DIM2 CWCUR"] Lemma cur_wrange : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.PLBx,(7.$2>.)P,(45.R3.)P,(46.R4.R3.)P,Pb,$2>.P,(27.$2>.R1.(44.R6.))(27.$2>.R2.R5.)(3;.VL,R4.Vlo,(14.$43.VL,VHI,Vh,)R5.+40.)")
(* [comment removed for export] *).
  Proof.
    clear -CWCUR DIM1 DIM2. intros nodes cur LBx HFR HCF HS.
    destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & _)].
    - eapply client_wrange_inside; [exact CWCUR| intros b Hb; apply HS; apply nLBof_sub; exact Hb| lia| lia].
    - eapply client_wrange_block; [apply HS; apply nLBof_in; exact HIN| lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="h SLO HLS ACL DIM1 DIM2 CWPP CWCUR CRBUF SPB"] Lemma snoc_facts : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_A ()) "Pnodes,(7.$6.)Pcur,$6.PN,$6.Phc2,(5.$43.VL,VHI,)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.P,(2:.$43.VL,VHI,R3.(19.(22.$6.$6.)(24.$6.$6.R4.+40.)(44.R6.))R2.R1.)P,(26.$6.R7.)P,(45.R8.)P,(46.R9.R8.)P,(53.VL,R8.+40.)P,(16.=(30.(31.(2.&8.)Vbs,)))(8.(26.$6.(21.$6.R<.(19.$6.R:.(1<.$6.))))(8.(45.(21.$6.R<.(19.$6.R:.(1<.$6.))))(8.(46.(21.$6.R<.(19.$6.R:.(1<.$6.)))R:.)(8.(28.(17.(29.R:.+40.)R;.)(17.(29.R;.+40.)R:.))(8.(28.(17.(29.R:.+40.)VPP,)(17.(29.VPP,+8.)R:.))(28.(17.(29.R:.+40.)VBUF,)(17.(29.VBUF,(30.(31.(2.&8.)Vbs,)))R:.)))))))")
(* [comment removed for export] *).
  Proof.
    clear -ACL CWPP CWCUR CRBUF DIM1 DIM2 SLO HLS SPB. (intros nodes cur N hc2 mm moc HH HND HFR HCF dd_H; ddestruct dd_H as (HN0 & HN16 & _ & HNC & HNI); intros LBS).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [_ HAP]. cbn [blocks_apart] in HAP. destruct HAP as [HAPN HAPc].
    assert (HND' : N + 64 <= hl_data_lo L \/ hl_data_hi L <= N) by lia.
    assert (HAPN0 : forall B j, In (B, j) LB -> N + 64 <= B \/ B + j <= N) by (intros B j HBj; apply HAPN; apply nLBof_sub; exact HBj).
    assert (APC : N + 64 <= CUR \/ CUR + 64 <= N)
      by (eapply client_wrange_apart; [exact CWCUR | lia | lia | exact ACL | exact HNC | exact HND' | exact HAPN0]).
    assert (APP : N + 64 <= PP \/ PP + 8 <= N)
      by (eapply client_wrange_apart; [exact CWPP | lia | lia | exact ACL | exact HNC | exact HND' | exact HAPN0]).
    assert (APB : N + 64 <= BUF \/ BUF + Z.of_nat (length bs) <= N)
      by (eapply client_range_apart; [exact CRBUF | lia | lia | exact ACL | exact HNC | exact HND' | exact HAPN0]).
    assert (APcur : N + 64 <= cur \/ cur + 64 <= N).
    { destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & _)]; [exact APC|]. apply HAPN. apply nLBof_in. exact HIN. }
    split; [| split; [| split; [| split; [exact APcur| split; [exact APP| exact APB]]]]].
    - apply List.NoDup_app; [exact HND| constructor; [intros HIn; destruct HIn| constructor] |].
      intros y Hy [E|[]]. pose proof (HAPN y 64 (nLBof_in nodes y Hy)). lia.
    - intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|[]]]; [exact (HFR y Hy)|].
      split; [exact HNC|]. split; [exact HNI| exact HAPN0].
    - unfold curF. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      right. split; [apply app_cons_not_nil || (destruct nodes; discriminate)|]. split; [symmetry; apply last_last|]. split; [exact HN16| lia].
  Qed.
End Walk.

Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ seq_cells buf_cells mpi_cells name_blob frame_hi];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].
