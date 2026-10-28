(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_oid U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_get_name.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_x509_parse_san_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.prod"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.rev"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "x509_parse_san_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.div"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"].


Definition U_X509_PARSE_SAN : Z := 0x289b8.
Notation X509_PARSE_SAN_STACK := 256 (only parsing).

Definition x509_parse_san_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (SAN lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1;.O1:.O19.)Lh',(5.O1;.O1:.O19.)(1.$6.Lr,$6.(1.$6.Lt,$6.(1.$6.Ldn,$6.(1.(7.$8.)Lrest,(7.$8.)(1.(7.$6.)Lnodes,(7.$6.)(9.(:.$0.R18.(;.(<.(=.O18.O17.O16.O15.R17.R16.R15.O14.O13.R14.R13.R12.R11.R10.R?.R>.R=.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R<.R;.R:.R9.)O8.(>.O18.)O7.(?.(2.&40.))R8.(10.O1;.))R7.))(9.(11.O1;.R8.)(9.(12.O1;.R8.O3.(13.&40.O17.))(9.(14.O1.R7.)(9.(:.$6.(15.O1;.O1:.O19.R6.)(15.O1;.O1:.O19.O6.))(9.(:.(2.&40.)R14.(16.&40.R5.))(9.(9.(17.-3000.R5.)(18.R5.=))(9.(19.O1;.R8.O4.(1:.$8.(1;.(16.&40.R4.))R2.))(9.(:.$6.(1<.(1=.R2.))+4<.)(9.(9.(18.=R4.)(18.R4.+7.))(9.P,(:.$6.R4.+4.)(1.(7.(2.&8.))Lp4,(7.(2.&8.))(1.(7.(2.&8.))Lj48,(7.(2.&8.))(1.(2.&8.)Lmg,(2.&8.)(1.(7.(2.&8.))Lpad7,(7.(2.&8.))(1.(7.(2.&8.))Lj8,(7.(2.&8.))(:.(7.$8.)R8.(1:.$8.(1>.#4.R5.)(1?.$8.(20.R4.R9.R3.R2.)(1:.$8.(1>.#8.R1.)(21.$8.))))))))))(9.P,(:.$6.R4.+4.)(22.O1;.L,(7.$8.)$23.R9.(1?.(24.$6.$6.)(25.$6.(24.$6.$6.)La,$6.(26.$6.$6.R1.+40.)(27.$6.R2.))O5.)R4.R2.)(9.P,(28.(:.$6.R4.+4.))(:.(7.$6.)R2.(21.$6.))(9.P,(28.(:.$6.R5.=))(:.(7.$6.)R2.(21.$6.))(9.(29.$6.R1.)(9.Px,$6.P,(2:.$6.R1.R2.)PB,$6.Pk,$6.P,(2:.(24.$6.$6.)(26.$6.$6.R2.R1.)O5.)(2;.(18.(2<.R5.+40.)R3.)(18.(2<.R3.R2.)R5.))(9.(2=.O1;.O1:.O19.R6.(1?.(24.$6.$6.)(25.$6.(24.$6.$6.)La,$6.(26.$6.$6.R1.+40.)(27.$6.R1.))O5.)R8.R7.)(2>.O1;.O1:.O5.(13.&40.O17.)(1:.(24.$6.$6.)(26.$6.$6.O4.(2<.O4.+50.))(21.(24.$6.$6.)))O2.R8.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_parse_san_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O4.O3.O2.)PLB,(7.$30.)PSB,$6.PSAN,$6.PBUF,$6.Psp0,$6.Pslen,$6.Plo,$6.Pbs,(7.(2.&8.))Ptgw,(2.&40.)Ppdw,(2.&40.)P,(2=.O4.O3.O2.R;.R:.R=.R<.)P,(19.O4.R>.R:.(31.R3.R2.R6.R7.))P,(19.O4.R?.R:.(1:.$8.(1>.#50.(32.(2.&8.)(16.&8.=)#50.))(21.$8.)))P,(33.O4.R10.R:.R6.)P,(18.R;.R:.)P,(18.=R:.)P,(18.(2<.R<.R;.)(2<.R=.(1<.(34.(2.&8.)R9.))))P,(17.(2<.R>.(1<.(34.(2.&8.)R:.)))(35.+2.+3?.))P,(2;.(18.(2<.R10.+50.)R11.)(18.(2<.R11.+18.)R10.))P,(2;.(18.(2<.R11.+50.)R10.)(18.(2<.R10.(1<.(34.(2.&8.)R<.)))R11.))P,(:.$6.(36.R13.+8.)=)P,(:.$6.(36.R13.+8.)=)P,(17.=R15.)P,(17.=R15.)P,(17.=R15.)P,(12.O4.R1<.R13.(13.&40.R3<.))P,(18.R14.(37.(37.(13.&40.R3=.)+100.)(38.O3.)))P,(18.(39.O3.)R15.)P,(18.(13.&40.R3?.)(15.O4.O3.O2.R1=.))P,(:.$6.(36.(13.&40.R40.)+10.)=)P,(18.(3:.O3.)(39.O3.))P,(18.(3;.O3.)(3<.O3.))P,(18.(3:.O3.)(3=.O3.))P,(2;.(18.(2<.R20.+18.)R1;.)(18.(13.&40.R44.)R20.))P,(2;.(18.(2<.R20.+50.)R1<.)(18.(13.&40.R45.)R20.))P,(2;.(18.(2<.R20.(1<.(34.(2.&8.)R1<.)))R1=.)(18.(13.&40.R46.)R20.))P,(3>.O3.R24.R1>.R23.+18.)P,(3?.O3.R25.R1?.(15.O4.O3.O2.R26.)R23.+50.)P,(3>.O3.R26.R20.R23.(1<.(34.(2.&8.)R1?.)))P,(:.(2.&40.)R48.(16.&40.(40.O3.)))P,(11.O4.R2;.)P,(:.(2.&40.)R44.(16.&40.R28.))P,(:.(2.&40.)R44.(16.&40.R28.))(41.O4.R2=.(42.O4.O3.O2.R4?.R4>.R4=.R4<.R48.R47.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R30.R2?.R2<.R2;.R29.R25.R2>.R2=.)(<.(=.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)R30.(16.&40.O1.)R2?.(?.(2.&40.))R2>.(10.O4.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma rw_cells_split_C8 : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Psegs,(7.$43.)Pm,P,(2.&40.)(3.(2.&8.))PA,$6.Ppre,(7.$8.)Pv,(2.&40.)Ppost,(7.$8.)P,(19.R6.R5.R4.(1?.$8.R3.(1:.$8.(44.R2.)R1.)))(19.R7.R6.R5.(1?.$8.R4.(1:.$8.(1;.R3.)(1:.$8.(1;.(16.&40.(45.(13.&40.R3.)(35.+2.+20.))))R2.))))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre v post H. eapply rw_cells_reshape; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]].
    apply cells_wf_app. split; [exact H1|]. cbn. auto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le8_split4. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac spine_firstn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
  | Datatypes.S ?k' => lazymatch cs with
             | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
             | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
             end
  end.
Ltac spine_skipn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => cs
  | Datatypes.S ?k' => lazymatch cs with
             | _ :: ?cs' => spine_skipn k' cs'
             | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
             end
  end.
Ltac split_c8 H k :=
  lazymatch type of H with rw_cells ?sg ?mx ?A ?cs =>
    let pre := spine_firstn k cs in
    let post := spine_skipn k cs in
    lazymatch post with C8 ?v :: ?tl =>
      change (rw_cells sg mx A cs) with (rw_cells sg mx A (pre ++ C8 v :: tl)) in H;
      apply (rw_cells_split_C8 sg mx A pre v tl) in H; cbn [app] in H
    end
  end.

(* [comment removed for export] *)
Lemma rw_cells_join_C4C4 : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Psegs,(7.$43.)Pm,P,(2.&40.)(3.(2.&8.))PA,$6.Ppre,(7.$8.)Pv,(2.&40.)Pw,(2.&40.)Ppost,(7.$8.)P,(19.R7.R6.R5.(1?.$8.R4.(1:.$8.(1;.R3.)(1:.$8.(1;.R2.)R1.))))(19.R8.R7.R6.(1?.$8.R5.(1:.$8.(44.(46.(1?.(2.&8.)(47.R4.)(47.R3.))))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre v w post H. eapply rw_cells_reshape; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. ddestruct Hwf as [H1 [_ [_ H3]]].
    apply cells_wf_app. split; [exact H1|]. cbn. auto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes].
    rewrite le8_le_bytes_to_word by (rewrite app_length, !length_le4; reflexivity). rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_slice : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Psegs,(7.$43.)Pm,P,(2.&40.)(3.(2.&8.))PA,$6.Pbs,(7.(2.&8.))Pa,$6.Pn,$6.P,(33.R6.R5.R4.R3.)P,(18.R5.R3.)P,(18.=R3.)P,(18.(2<.R5.R4.)(2<.R7.(1<.(34.(2.&8.)R6.))))(33.R:.R9.R6.(48.(2.&8.)(49.R5.)(4:.(2.&8.)(49.(37.R6.R8.))R7.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A bs a n H Ha Hn Hb.
  rewrite <- (firstn_skipn (Z.to_nat (a - A)) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  replace (A + Z.of_nat (Z.to_nat (a - A))) with a in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat (a - A)) bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma bytes_at_slice_length : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Pbs,(7.(2.&8.))PA,$6.Pa,$6.Pn,$6.P,(18.R3.R2.)P,(18.=R2.)P,(18.(2<.R4.R3.)(2<.R5.(1<.(34.(2.&8.)R6.))))(:.$6.(1<.(34.(2.&8.)(48.(2.&8.)(49.R4.)(4:.(2.&8.)(49.(37.R5.R6.))R7.))))R4.)")
(* [comment removed for export] *).
Proof. intros. rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. Qed.

(* [comment removed for export] *)
Definition san_ctx (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (CALLOC FREE : Z)
    (sp tp : word) (h : HST segs L HI) (LB : list blk) (SB SAN BUF sp0 slen lo : Z) (bs : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "(9.(:.$6.(4;.O?.)O=.)(9.(:.$6.(4<.O?.)O<.)(9.(18.=(38.O?.))(9.(:.(2.&40.)O:.(16.&40.(40.O?.)))(9.(18.O5.O4.)(9.(18.=O3.)(9.(18.(2<.O4.O3.)(2<.O5.(1<.(34.(2.&8.)O1.))))(9.(17.(2<.O5.(1<.(34.(2.&8.)O1.)))(35.+2.+3?.))(9.(2;.(18.(2<.O6.+50.)O7.)(18.(2<.O7.+18.)O6.))(9.(2;.(18.(2<.O6.+50.)O5.)(18.(2<.O5.(1<.(34.(2.&8.)O1.)))O6.))(9.(:.$6.(36.O7.+8.)=)(9.(:.$6.(36.O6.+8.)=)(9.(17.=O7.)(9.(17.=O6.)(9.(17.=O5.)(9.(18.O2.(37.(37.(13.&40.O;.)+100.)(38.O?.)))(9.(18.(39.O?.)O2.)(9.(17.+1000.(39.O?.))(9.(18.(13.&40.O;.)(15.O10.O?.O>.O9.))(9.(:.$6.(36.(13.&40.O;.)+10.)=)(9.(18.(3:.O?.)(39.O?.))(9.(18.(3;.O?.)(3<.O?.))(9.(18.(3:.O?.)(3=.O?.))(9.(2;.(18.(2<.O7.+18.)O2.)(18.(13.&40.O;.)O7.))(9.(2;.(18.(2<.O6.+50.)O2.)(18.(13.&40.O;.)O6.))(9.(2;.(18.(2<.O5.(1<.(34.(2.&8.)O1.)))O2.)(18.(13.&40.O;.)O5.))(9.(3>.O?.O8.O2.O7.+18.)(9.(3?.O?.O8.O2.(15.O10.O?.O>.O9.)O6.+50.)(9.(3>.O?.O8.O2.O5.(1<.(34.(2.&8.)O1.)))(9.(9.(18.=(13.&40.O;.))(17.(13.&40.O;.)(35.+2.+40.)))(9.(9.(18.=O6.)(18.(2<.O6.+50.)(35.+2.+40.)))(9.(9.(18.=O7.)(18.(2<.O7.+18.)(35.+2.+40.)))(4=.(24.$6.$6.)Lb,(24.$6.$6.)(4>.O?.(4?.$6.$6.R1.)(50.$6.$6.R1.))O8.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Ltac open_sctx HC :=
  pose proof HC as HCc;
  destruct HCc as (HCALLOC & HFREE & HLS & TP & B1 & B2 & B3 & B4 & D1 & D2 & ALB & ALS & NZSB & NZS & NZB & SLO & ACL & ACP & HTOP & SPA
                   & DHI & DIM1 & DIM2 & DSB & DSS & DSBUF & CRSB & CWS & CRBUF & SPR & SANB & SBB & HBR0).

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (SB SAN BUF sp0 slen lo : Z) (bs : list byte).
  Notation CTX := (san_ctx usegs L HI U_CALLOC U_FREE sp tp h LB SB SAN BUF sp0 slen lo bs).
  Hypothesis HC : CTX.

  Notation X := [(SAN, SAN + 80)].
  Notation W := [(SAN, SAN + 80); (bv_unsigned sp - 80, bv_unsigned sp)].
  Notation POST := (x509_parse_san_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB SAN lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
  #[using="HI sp tp h SB SAN BUF sp0 slen lo bs HC"] Lemma in_block_below' : forall a, in_block LB a -> a < alloc_ceiling.
  Proof. open_sctx HC. clear -HBR0. (intros a dd_H; ddestruct dd_H as (b & Hb & Hr)). rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Hc & _). lia. Qed.

  (* [comment removed for export] *)
  #[using="tp SB BUF sp0 slen lo bs HC"] Lemma heap_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(2=.$51.VL,VHI,Vh,VLB,R2.Vmo,)P,(52.(1:.(24.$6.$6.)(26.$6.$6.VSAN,(2<.VSAN,+50.))(1:.(24.$6.$6.)(26.$6.$6.(37.(13.&40.Vsp,)+50.)(13.&40.Vsp,))(21.(24.$6.$6.))))R3.R2.)P,(53.$51.R4.R3.)(2=.$51.VL,VHI,Vh,VLB,R4.Vmo,)")
(* [comment removed for export] *).
  Proof.
    open_sctx HC. clear -ACL CWS SLO HLS HTOP. intros mm m1 HH MU WM.
    apply (Asn1AuxA.HEAP_munch usegs L HI h LB mm m1 mo lo _ HH ACL MU WM).
    intros a Ha Hin. cbn [outside] in Hin.
    destruct (outside_dec [(SAN, SAN + 80)] a) as [O1|O1]; cbn [outside] in O1. 2:{ exact (CWS a ltac:(clear -O1; lia)). }
    left. clear -Hin O1 SLO HLS HTOP Ha. lia.
  Qed.

  #[using="HI tp h SB BUF sp0 slen lo bs HC"] Lemma presx_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_A ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(2>.$51.VL,VLB,(13.&40.Vsp,)(1:.(24.$6.$6.)(26.$6.$6.VSAN,(2<.VSAN,+50.))(21.(24.$6.$6.)))Vm,R2.)P,(52.(1:.(24.$6.$6.)(26.$6.$6.VSAN,(2<.VSAN,+50.))(1:.(24.$6.$6.)(26.$6.$6.(37.(13.&40.Vsp,)+50.)(13.&40.Vsp,))(21.(24.$6.$6.))))R3.R2.)P,(53.$51.R4.R3.)(2>.$51.VL,VLB,(13.&40.Vsp,)(1:.(24.$6.$6.)(26.$6.$6.VSAN,(2<.VSAN,+50.))(21.(24.$6.$6.)))Vm,R4.)")
(* [comment removed for export] *).
  Proof.
    pose proof in_block_below' as IBB. open_sctx HC. clear -ACL SLO HLS DHI IBB. intros mm m1 HPX MU WM.
    eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. cbn [outside] in Ho |- *.
    destruct Hc as [Hs|[[Hd1 Hd2]|Hb]]; [clear -Ho Hs SLO HLS; lia| clear -Ho Hd1 Hd2 DHI ACL SLO HLS; lia|].
    pose proof (IBB a Hb) as HY. clear -Ho HY ACL SLO HLS. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SB BUF sp0 slen bs HC"] Lemma epi_walk : forall (r t : Z) (rest : list cell) (pw lw : word)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -80) [C8 pw; C8 lw; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mm lo (bv_unsigned sp + -80) -> mem_inv usegs mm -> munch W m mm -> wmono usegs m mm ->
    HEAP usegs L HI h LB m mo -> -12288 < r <= 0 ->
    rw_cells usegs mm SAN (C4 (Z_to_bv 64 t) :: rest) -> Z.of_nat (cells_size rest) = 76 -> t <> 4 -> 0 <= t <= 7 ->
    aevtM usegs mo POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 166976) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros r t rest pw lw x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 mm
      FR ST MI MU WM HH Hr HSAN HSZ Ht Ht7.
    open_sctx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (heap_W m _ HH MU WM) as HH9.
    pose proof (presx_W m _ (heap_presx_refl usegs L LB (bv_unsigned sp) X m) MU WM) as HPX9.
    release_frame FR ST (bv_unsigned sp).
    apply aevtM_done. unfold x509_parse_san_post. deexists 15. dexists mm, mo, h, r, t, 0, rest, [].
    split; [reflexivity|]. cbn [map rev app].
    repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
    - apply mo_frame_refl.
    - clear -Hr; lia. - clear -Hr; lia.
    - clear -Ht7; lia. - clear -Ht7; lia.
    - intros E. exfalso. exact (Ht E).
    - constructor.
    - intros x [].
  Qed.
End Walk.
