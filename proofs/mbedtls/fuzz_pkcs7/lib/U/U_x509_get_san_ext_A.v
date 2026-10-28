(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_len U_asn1_sequence_free U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_parse_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_x509_get_san_ext_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.hd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "x509_get_san_ext_post"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove_all"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.last"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Walk.nLBof"; "Walk.nfresh"; "Walk.curF"; "Walk.headrep"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "Stdlib.Lists.List.removelast"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Walk.frame_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Walk.W"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"].


Definition U_X509_GET_SAN_EXT : Z := 0x28790.
Notation X509_GET_SAN_EXT_STACK := 480 (only parsing).

Definition x509_get_san_ext_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1?.O1>.O1=.)Lh',(5.O1?.O1>.O1=.)(1.$6.Lr,$6.(1.$6.Lp',$6.(1.(2.&40.)Lct,(2.&40.)(1.(2.&40.)Lcpad,(2.&40.)(1.$6.Lcl,$6.(1.$6.Lcp,$6.(1.$6.Lcn,$6.(1.(7.$6.)Lnodes,(7.$6.)(8.(9.$0.R1;.(:.(;.(<.O1<.O1;.O1:.O19.R1:.R19.R18.O18.O17.R17.R16.R15.R14.R13.R12.R11.R10.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R?.R>.R=.R<.)O<.(=.O1<.)O;.(>.(2.&40.))R;.(?.O1?.))R:.))(8.(10.O1?.R;.)(8.(11.O1?.R;.O3.(12.&40.O1;.))(8.(13.O1.R:.)(8.(9.$6.(14.O1?.O1>.O1=.R9.)(14.O1?.O1>.O1=.O:.))(8.(9.(2.&40.)R17.(15.&40.R8.))(8.(8.(16.-3000.R8.)(17.R8.=))(8.(18.O1?.R;.O8.(19.$1:.(1;.(15.&40.R7.))(1<.$1:.)))(8.(8.(17.O6.R7.)(17.R7.O5.))(8.(18.O1?.R;.O7.(1=.R6.R5.R4.R3.R2.))(8.(1>.(8.(9.$6.R3.=)(8.(9.$6.R4.=)(9.(7.$6.)R1.(1<.$6.))))(8.(17.O4.R3.)(8.(17.=R4.)(17.(1?.R3.R4.)O5.))))(8.(9.$6.R2.(20.$6.=R1.))(8.(21.O1?.L,(7.$1:.)$22.R;.(23.(24.$6.$6.)(25.$6.(24.$6.$6.)La,$6.(26.$6.$6.R1.+20.)(27.$6.R1.))O9.)R2.R1.)(8.(28.$6.R1.)(8.Px,$6.P,(29.$6.R1.R2.)PB,$6.Pk,$6.P,(29.(24.$6.$6.)(26.$6.$6.R2.R1.)O9.)(1>.(17.(1?.R5.+20.)R3.)(17.(1?.R3.R2.)R5.))(8.(2:.O1?.O1>.O1=.R9.(23.(24.$6.$6.)(25.$6.(24.$6.$6.)La,$6.(26.$6.$6.R1.+20.)(27.$6.R1.))O9.)R;.R:.)(2;.O1?.O1>.O9.(12.&40.O1;.)(19.(24.$6.$6.)(26.$6.$6.O8.(1?.O8.+8.))(19.(24.$6.$6.)(26.$6.$6.O7.(1?.O7.+20.))(1<.(24.$6.$6.))))O2.R;.)))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_san_ext_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O4.O3.O2.)PLB,(7.$2=.)PPP,$6.PCUR,$6.PP,$6.PEND,$6.PBUF,$6.Plo,$6.Pbs,(7.(2.&8.))Pct,(2.&40.)Pcpad,(2.&40.)P,(2:.O4.O3.O2.R;.R:.R=.R<.)P,(18.O4.R>.R:.(19.$1:.(1;.(15.&40.R8.))(1<.$1:.)))P,(18.O4.R?.R:.(1=.R4.R3.===))P,(2>.O4.R10.R8.R6.)P,(17.R9.R;.)P,(17.R<.R;.)P,(17.R<.(1?.R;.(2?.(30.(2.&8.)R9.))))P,(16.(1?.R<.(2?.(30.(2.&8.)R:.)))(31.+2.+3?.))P,(1>.(17.(1?.R11.+8.)R10.)(17.(1?.R10.+20.)R11.))P,(1>.(17.(1?.R12.+8.)R>.)(17.(1?.R>.(2?.(30.(2.&8.)R<.)))R12.))P,(1>.(17.(1?.R12.+20.)R?.)(17.(1?.R?.(2?.(30.(2.&8.)R=.)))R12.))P,(9.$6.(32.R14.+8.)=)P,(9.$6.(32.R14.+8.)=)P,(16.=R16.)P,(16.=R16.)P,(16.=R14.)P,(11.O4.R1=.R14.(12.&40.R3=.))P,(17.R15.(33.(33.(12.&40.R3>.)+1>0.)(34.O3.)))P,(17.(35.O3.)R16.)P,(17.(12.&40.R40.)(14.O4.O3.O2.R1>.))P,(9.$6.(32.(12.&40.R41.)+10.)=)P,(17.(36.O3.)(35.O3.))P,(17.(37.O3.)(38.O3.))P,(17.(36.O3.)(39.O3.))P,(1>.(17.(1?.R21.+8.)R1<.)(17.(12.&40.R45.)R21.))P,(1>.(17.(1?.R21.+20.)R1=.)(17.(12.&40.R46.)R21.))P,(1>.(17.(1?.R1?.(2?.(30.(2.&8.)R1=.)))R1>.)(17.(12.&40.R47.)R1?.))P,(3:.O3.R25.R1?.(14.O4.O3.O2.R26.)R24.+8.)P,(3:.O3.R26.R20.(14.O4.O3.O2.R27.)R24.+20.)P,(3;.O3.R27.R21.R22.(2?.(30.(2.&8.)R20.)))P,(9.(2.&40.)R49.(15.&40.(3<.O3.)))P,(10.O4.R2<.)P,(9.(2.&40.)R45.(15.&40.R29.))P,(9.(2.&40.)R45.(15.&40.R27.))P,(9.(2.&40.)R45.(15.&40.R2:.))(3=.O4.R2?.(3>.O4.O3.O2.R51.R50.R4?.R4>.R4:.R49.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R32.R31.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R30.R2?.)(;.(<.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R32.(15.&40.O1.)R31.(>.(2.&40.))R30.(?.O4.)))")
(* [comment removed for export] *).

Lemma lb_remove_all_new32 : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)PLB,(7.$2=.)P,(28.$6.R2.)(9.(7.$2=.)(3?.R3.(23.(24.$6.$6.)(25.$6.(24.$6.$6.)La,$6.(26.$6.$6.R1.+20.)(27.$6.R3.))R2.))R2.)")
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
Lemma le4_le_bytes_to_word' : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  pose proof (PropExec.bytes_le_to_Z_bound bs) as HB. rewrite Hl in HB. pose proof (bytes_le_to_Z_nonneg bs) as H0.
  rewrite Z.mod_small by (cbn in HB; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_CB4_C4' : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Psegs,(7.$40.)Pm,P,(2.&40.)(3.(2.&8.))PA,$6.Ppre,(7.$1:.)Pbs,(7.(2.&8.))Ppost,(7.$1:.)P,(18.R6.R5.R4.(23.$1:.R3.(19.$1:.(41.#4.R2.)R1.)))(18.R7.R6.R5.(23.$1:.R4.(19.$1:.(42.(43.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le4_le_bytes_to_word' by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Ltac cb4_to_c4 H pre :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A _ => apply (rw_cells_CB4_C4' sg mx A pre) in H; cbn [app] in H
  end.

(* [comment removed for export] *)
Definition ext_ctx (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (CALLOC FREE : Z)
    (sp tp : word) (h : HST segs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (bs : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "(8.(9.$6.(44.O?.)O=.)(8.(9.$6.(45.O?.)O<.)(8.(17.=(34.O?.))(8.(9.(2.&40.)O:.(15.&40.(3<.O?.)))(8.(17.O3.O5.)(8.(17.O4.(1?.O3.(2?.(30.(2.&8.)O1.))))(8.(16.(1?.O3.(2?.(30.(2.&8.)O1.)))(31.+2.+3?.))(8.(1>.(17.(1?.O7.+8.)O6.)(17.(1?.O6.+20.)O7.))(8.(1>.(17.(1?.O7.+8.)O3.)(17.(1?.O3.(2?.(30.(2.&8.)O1.)))O7.))(8.(1>.(17.(1?.O6.+20.)O3.)(17.(1?.O3.(2?.(30.(2.&8.)O1.)))O6.))(8.(8.(17.=O7.)(17.(1?.O7.+8.)(31.+2.+40.)))(8.(8.(17.=O6.)(17.(1?.O6.+20.)(31.+2.+40.)))(8.(9.$6.(32.O7.+8.)=)(8.(9.$6.(32.O6.+8.)=)(8.(16.=O7.)(8.(16.=O6.)(8.(16.=O3.)(8.(17.O2.(33.(33.(12.&40.O;.)+1>0.)(34.O?.)))(8.(17.(35.O?.)O2.)(8.(16.+1000.(35.O?.))(8.(17.(12.&40.O;.)(14.O10.O?.O>.O9.))(8.(9.$6.(32.(12.&40.O;.)+10.)=)(8.(17.(36.O?.)(35.O?.))(8.(17.(37.O?.)(38.O?.))(8.(17.(36.O?.)(39.O?.))(8.(1>.(17.(1?.O7.+8.)O2.)(17.(12.&40.O;.)O7.))(8.(1>.(17.(1?.O6.+20.)O2.)(17.(12.&40.O;.)O6.))(8.(1>.(17.(1?.O3.(2?.(30.(2.&8.)O1.)))O2.)(17.(12.&40.O;.)O3.))(8.(3:.O?.O8.O2.(14.O10.O?.O>.O9.)O7.+8.)(8.(3:.O?.O8.O2.(14.O10.O?.O>.O9.)O6.+20.)(8.(3;.O?.O8.O2.O3.(2?.(30.(2.&8.)O1.)))(8.(8.(17.=(12.&40.O;.))(16.(12.&40.O;.)(31.+2.+40.)))(46.(24.$6.$6.)Lb,(24.$6.$6.)(47.O?.(48.$6.$6.R1.)(49.$6.$6.R1.))O8.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Ltac open_ectx HC :=
  pose proof HC as HCc;
  destruct HCc as (HCALLOC & HFREE & HLS & TP & B1 & B3 & B4 & D1 & D2 & D3 & PPB & CURB & AL1 & AL2 & NZ1 & NZ2 & NZ3
                   & SLO & ACL & ACP & HTOP & SPA & DHI & DIM1 & DIM2 & DS1 & DS2 & DS3 & CWPP & CWCUR & CRBUF & SPR & HBR0).

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (bs : list byte).
  Notation CTX := (ext_ctx usegs L HI U_CALLOC U_FREE sp tp h LB PP CUR P END BUF lo bs).
  Hypothesis HC : CTX.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (x509_get_san_ext_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -224)).

  Definition nLBof (nodes : list Z) : list blk := map (fun a => (a, 32)) (rev nodes) ++ LB.

  Definition nfresh (nodes : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Px,$6.P,(29.$6.R1.O1.)(8.(17.(1?.R2.+20.)(35.VL,))(8.(1>.(17.(1?.R2.+20.)(37.VL,))(17.(39.VL,)R2.))PB,$6.Pk,$6.P,(29.(24.$6.$6.)(26.$6.$6.R2.R1.)VLB,)(1>.(17.(1?.R5.+20.)R3.)(17.(1?.R3.R2.)R5.))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition W (cur : Z) : list ivl := [(PP, PP + 8); (cur, cur + 32); (bv_unsigned sp - 224, bv_unsigned sp)].

  (* [comment removed for export] *)
  Definition curF (nodes : list Z) (cur : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "(8.(9.$6.(32.O1.+8.)=)(8.(16.=O1.)(8.(17.(1?.O1.+20.)(31.+2.+40.))(8.(1>.(17.(1?.VPP,+8.)O1.)(17.(1?.O1.+20.)VPP,))(8.(1>.(17.(1?.O1.+20.)VBUF,)(17.(1?.VBUF,(2?.(30.(2.&8.)Vbs,)))O1.))(8.(1>.(17.(1?.O1.+20.)Vlo,)(17.(12.&40.Vsp,)O1.))(1>.(8.(9.(7.$6.)O2.(1<.$6.))(9.$6.O1.VCUR,))(8.(4:.(9.(7.$6.)O2.(1<.$6.)))(8.(9.$6.O1.(4;.$6.O2.=))(8.(9.$6.(32.O1.+10.)=)(1>.(17.(1?.O1.+20.)VCUR,)(17.(1?.VCUR,+20.)O1.))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition headrep (mm : mem) (nodes : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "(1>.(9.(7.$6.)O1.(1<.$6.))(1.(2.&40.)Lt,(2.&40.)(1.(2.&40.)Lpd,(2.&40.)(1.$6.Ll,$6.(1.$6.Lp,$6.(8.(18.$4<.O2.VCUR,(1=.R4.R3.R2.R1.(20.$6.=O1.)))(8.(17.VBUF,R1.)(8.(17.=R2.)(17.(1?.R1.R2.)VEND,)))))))))")
(* [comment removed for export] *).

  Definition frame_hi : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition ninv (mm : mem) (moc : Model) (hc : HST usegs L HI) (nodes : list Z) (cur : Z)
             (j0 : list byte) (fb fs : list cell) (tl : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "(8.(2:.$4<.VL,VHI,O7.(4=.O6.)O9.O8.)(8.(9.$6.(14.$4<.VL,VHI,O7.)(14.$4<.VL,VHI,Vh,))(8.(28.$6.O6.)(8.(4>.O6.)(8.(4?.O6.O5.)(8.(50.O9.O6.)(8.(51.$4<.O9.(4=.O6.)VBUF,VEND,(52.$6.O6.)(4;.$6.O6.=))(8.(18.$4<.O9.(1?.(12.&40.Vsp,)->0.)(19.$1:.(41.#8.O4.)(1<.$1:.)))(8.(18.$4<.O9.(1?.(12.&40.Vsp,)-=8.)O3.)(8.(9.$53.(54.O3.)#18.)(8.(18.$4<.O9.(1?.(12.&40.Vsp,)-<0.)O2.)(8.(9.$53.(54.O2.)#50.)(8.(18.$4<.O9.(1?.(12.&40.Vsp,)-70.)(19.$1:.(1;.O1.)(1<.$1:.)))(8.(18.$4<.O9.(1?.(12.&40.Vsp,)-68.)$55.)(8.(11.$4<.O9.Vlo,(1?.(12.&40.Vsp,)->0.))(8.(10.$4<.O9.)(8.(2>.$4<.O9.VBUF,Vbs,)(8.(2;.$4<.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,O9.)(13.Vmo,O8.)))))))))))))))))))")
(* [comment removed for export] *).

  #[using="HI sp tp h PP CUR P END BUF lo bs HC"] Lemma in_block_below : forall a, in_block LB a -> a < alloc_ceiling.
  Proof.
    open_ectx HC. clear -HBR0. (intros a dd_H; ddestruct dd_H as (b & Hb & Hr)). rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Hc & _). lia.
  Qed.

  #[using="Type"] Lemma nLBof_snoc : forall nodes N, nLBof (nodes ++ [N]) = (N, 32) :: nLBof nodes.
  Proof. intros. unfold nLBof. rewrite rev_app_distr. reflexivity. Qed.

  #[using="Type"] Lemma nLBof_sub : forall nodes b, In b LB -> In b (nLBof nodes).
  Proof. intros. unfold nLBof. apply in_or_app. right. assumption. Qed.

  #[using="Type"] Lemma nLBof_in : forall nodes x, In x nodes -> In (x, 32) (nLBof nodes).
  Proof. intros. unfold nLBof. apply in_or_app. left. apply in_map_iff. exists x. split; [reflexivity|]. rewrite <- in_rev. exact H. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma presx_munch : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "PWx,(7.$56.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(57.R3.R2.R1.)P,(58.$4<.R3.R2.)P,Pa,$6.P,(8.(17.=R1.)(16.R1.(31.+2.+40.)))P,(1>.(17.(12.&40.Vsp,)R2.)(1>.(8.(17.(38.VL,)R2.)(16.R2.(36.VL,)))(59.VLB,R2.)))P,(5:.(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))R3.)(5:.R9.R4.)(2;.$4<.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))R5.R4.)")
(* [comment removed for export] *).
  Proof.
    clear. intros Wx mm m1 MU WM HW. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. apply HW; [exact Ha| | exact Ho].
    destruct Hc as [Hs|[[Hd1 Hd2]|Hb]]; [left; exact Hs| right; left; lia| right; right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  #[using="HI tp h P END HC"] Lemma cur_cases : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.P,(4>.R2.)P,(4?.R3.R2.)(1>.(9.$6.R3.VCUR,)(8.(29.$6.R3.R4.)(8.(17.(1?.R3.+20.)(35.VL,))(8.(1>.(17.(1?.R3.+20.)(38.VL,))(17.(36.VL,)R3.))PB,$6.Pk,$6.P,(29.(24.$6.$6.)(26.$6.$6.R2.R1.)VLB,)(1>.(17.(1?.R6.+20.)R3.)(17.(1?.R3.R2.)R6.))))))")
(* [comment removed for export] *).
  Proof.
    open_ectx HC. clear -DIM1 DIM2. (intros nodes cur HFR dd_H; ddestruct dd_H as (_ & _ & _ & _ & _ & _ & [[_ ->]|(Hne & -> & _ & _)])); [left; reflexivity| right].
    assert (HIN : In (last nodes 0) nodes).
    { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
    destruct (HFR _ HIN) as (A1 & A2 & A3). split; [exact HIN|]. split; [exact A1|]. split; [lia| exact A3].
  Qed.

  #[using="HI tp h P END HC"] Lemma presx_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(4>.R4.)P,(4?.R5.R4.)P,(57.(5;.R5.)R4.R3.)P,(58.$4<.R5.R4.)P,(2;.$4<.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,R6.)(2;.$4<.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,R6.)")
(* [comment removed for export] *).
  Proof.
    pose proof in_block_below as IBB. pose proof cur_cases as CC. open_ectx HC. clear -DIM1 DIM2 ACL SLO HLS DHI IBB CC.
    intros nodes cur mm m1 HFR HCF MU WM HPX.
    eapply heap_presx_trans; [exact HPX|]. eapply presx_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. cbn [outside W] in Ho |- *.
    destruct (CC nodes cur HFR HCF) as [->|(HIN & HCc & HD & HAP)].
    - destruct Hc as [Hs|[Hd|Hb]]; [lia| lia| pose proof (IBB a Hb); lia].
    - destruct Hc as [Hs|[Hd|Hb]]; [lia| lia|].
      ddestruct Hb as (b & Hb & Hr). destruct b as [B j]. cbn in Hr. pose proof (HAP B j Hb).
      pose proof (IBB a ltac:(exists (B, j); split; [exact Hb| cbn; lia])). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tp P END HC"] Lemma heap_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$4<.VL,VHI,)PLBx,(7.$2=.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))Pmoc,$4.P,(4>.R7.)P,(4?.R8.R7.)P,(2:.$4<.VL,VHI,R7.R6.R5.R3.)P,(9.$6.(14.$4<.VL,VHI,R8.)(14.$4<.VL,VHI,Vh,))P,Pb,$2=.P,(29.$2=.R1.(4=.R<.))(29.$2=.R2.R:.)P,(57.(5;.R;.)R8.R7.)P,(58.$4<.R9.R8.)(2:.$4<.VL,VHI,R<.R;.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    pose proof cur_cases as CC. open_ectx HC. clear -ACL CWPP CWCUR SLO HLS HTOP DIM1 DIM2 CC.
    intros nodes cur hc LBx mm m1 moc HFR HCF HH HT HS MU WM.
    eapply HEAP_munch; [exact HH| exact ACL| exact MU| exact WM|].
    intros a Ha Hin. cbn [outside W] in Hin. rewrite HT.
    assert (HS' : forall b, In b LB -> In b LBx) by (intros b Hb; apply HS; apply nLBof_sub; exact Hb).
    destruct (outside_dec [(PP, PP + 8)] a) as [O1|O1]; cbn [outside] in O1.
    2:{ exact (client_wrange_mono L _ _ _ _ _ _ CWPP HS' a ltac:(lia)). }
    destruct (outside_dec [(bv_unsigned sp - 224, bv_unsigned sp)] a) as [O3|O3]; cbn [outside] in O3.
    2:{ left. lia. }
    assert (HA : cur <= a < cur + 32) by lia.
    destruct (CC nodes cur HFR HCF) as [->|(HIN & _)].
    - exact (client_wrange_mono L _ _ _ _ _ _ CWCUR HS' a HA).
    - right. right. exists (cur, 32). split; [apply HS; apply nLBof_in; exact HIN| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="tp h P END HC"] Lemma others_apart : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$4<.VL,VHI,)PLBx,(7.$2=.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Py,$6.P,(2:.$4<.VL,VHI,R5.R4.R3.R2.)P,Pb,$2=.P,(29.$2=.R1.(4=.R9.))(29.$2=.R2.R7.)P,(28.$6.R9.)P,(4>.R:.)P,(4?.R;.R:.)P,(29.$6.R6.(52.$6.R<.))(8.(1>.(17.(1?.R7.+20.)VPP,)(17.(1?.VPP,+8.)R7.))(8.(1>.(17.(1?.R7.+20.)R<.)(17.(1?.R<.+20.)R7.))(17.(1?.R7.+20.)(35.VL,))))")
(* [comment removed for export] *).
  Proof.
    open_ectx HC. clear -ACL CWPP CWCUR DIM1 DIM2. intros nodes cur hc LBx mm moc y HH HS HND HFR HCF Hy.
    pose proof (in_removelast _ _ Hy) as HyN.
    ddestruct (HFR y HyN) as (HCc & HD & HAP).
    assert (HD' : y + 32 <= hl_data_lo L \/ hl_data_hi L <= y) by lia.
    split; [| split; [| exact HCc]].
    - eapply client_wrange_apart; [exact CWPP| lia| lia| exact ACL| exact HCc| exact HD'| exact HAP].
    - ddestruct HCF as (_ & _ & _ & _ & _ & _ & [[-> ->]|(Hne & -> & _ & _)]); [destruct Hy|].
      destruct (heap_blocks _ _ HI _ _ _ _ HH) as [_ HAPc].
      assert (NE : y <> last nodes 0).
      { intros E. rewrite <- (removelast_last_app nodes 0) in HND by exact Hne.
        apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
      eapply blocks_apart_in2; [exact HAPc| apply HS; apply nLBof_in; exact HyN| apply HS; apply nLBof_in| exact NE].
      rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity.
  Qed.

  #[using="tp h P HC"] Lemma lseg_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$4<.VL,VHI,)PLBx,(7.$2=.)PLBn,(7.$2=.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Pfin,$6.P,(2:.$4<.VL,VHI,R7.R6.R4.R2.)P,Pb,$2=.P,(29.$2=.R1.(4=.R;.))(29.$2=.R2.R9.)P,(28.$6.R;.)P,(4>.R<.)P,(4?.R=.R<.)P,(51.$4<.R9.R:.VBUF,VEND,(52.$6.R>.)R6.)P,(57.(5;.R>.)R:.R9.)P,(58.$4<.R;.R:.)(51.$4<.R;.R=.VBUF,VEND,(52.$6.R11.)R9.)")
(* [comment removed for export] *).
  Proof.
    pose proof others_apart as OA. open_ectx HC. clear -ACL CWPP CWCUR DIM1 DIM2 SLO HLS OA.
    intros nodes cur hc LBx LBn mm m1 moc fin HH HS HND HFR HCF HL MU WM.
    eapply seq_lseg_mem; [exact HL| intros y Hy; eapply seq_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
    ddestruct (OA nodes cur hc LBx mm moc y HH HS HND HFR HCF Hy) as (A1 & A2 & A3).
    cbn [disjoint_from W]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="L HI tp h LB P HC"] Lemma headrep_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(4?.R4.R3.)P,(50.R3.R5.)P,(57.(5;.R5.)R4.R3.)P,(58.$4<.R5.R4.)(50.R5.R8.)")
(* [comment removed for export] *).
  Proof.
    open_ectx HC. clear -D1 DS2 SLO HLS. intros nodes cur mm m1 HCF [->|(t & pd & l & p & HR & HB)] MU WM; [left; reflexivity|].
    ddestruct HCF as (_ & _ & _ & _ & _ & _ & [[-> _]|(Hne & _ & _ & AP)]); [left; reflexivity| right].
    dexists t, pd, l, p. split; [| exact HB]. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tp P HC"] Lemma sync_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Phc,(5.$4<.VL,VHI,)PLBx,(7.$2=.)PLBn,(7.$2=.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Pfin,$6.P,(2:.$4<.VL,VHI,R7.R6.R4.R2.)P,(9.$6.(14.$4<.VL,VHI,R8.)(14.$4<.VL,VHI,Vh,))P,Pb,$2=.P,(29.$2=.R1.(4=.R<.))(29.$2=.R2.R:.)P,(28.$6.R<.)P,(4>.R=.)P,(4?.R>.R=.)P,(50.R:.R?.)P,(51.$4<.R;.R<.VBUF,VEND,(52.$6.R10.)R8.)P,(2;.$4<.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,R<.)P,(57.(5;.R11.)R=.R<.)P,(58.$4<.R>.R=.)(8.(2:.$4<.VL,VHI,R12.R11.R>.R=.)(8.(50.R>.R14.)(8.(51.$4<.R>.R10.VBUF,VEND,(52.$6.R14.)R<.)(2;.$4<.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,R>.))))")
(* [comment removed for export] *).
  Proof.
    intros nodes cur hc LBx LBn mm m1 moc fin HH HT HS HND HFR HCF HHD HL HPX MU WM.
    split; [eapply heap_W; eassumption|]. split; [eapply headrep_W; eassumption|].
    split; [eapply lseg_W; eassumption| eapply presx_W; eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma close_nodes : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.P,(4?.R7.R6.)P,(50.R6.R8.)P,(51.$4<.R7.(4=.R9.)VBUF,VEND,(52.$6.R9.)(4;.$6.R9.=))P,(18.$4<.R8.R9.(1=.R7.R6.R5.R4.=))P,(1>.(8.(9.$6.R5.=)(8.(9.$6.R6.=)(9.(7.$6.)R;.(1<.$6.))))(8.(17.VBUF,R5.)(8.(17.=R6.)(17.(1?.R5.R6.)VEND,))))(8.(1.(2.&40.)Lt,(2.&40.)(1.(2.&40.)Lpd,(2.&40.)(1.$6.Ll,$6.(1.$6.Lp,$6.(8.(18.$4<.R>.VCUR,(1=.R4.R3.R2.R1.(20.$6.=R10.)))(1>.(8.(9.$6.R1.=)(8.(9.$6.R2.=)(9.(7.$6.)R10.(1<.$6.))))(8.(17.VBUF,R1.)(8.(17.=R2.)(17.(1?.R1.R2.)VEND,)))))))))(51.$4<.R:.(4=.R<.)VBUF,VEND,R<.=))")
(* [comment removed for export] *).
  Proof.
    clear. intros nodes cur mm ct cpad cl cp HCF HHD HL HR HB.
    ddestruct HCF as (AL & POS & _ & _ & _ & _ & [[-> ->]|(Hne & -> & A16 & _)]).
    - split; [dexists ct, cpad, cl, cp; split; [exact HR| exact HB]| exact I].
    - destruct HHD as [E|(t & pd & l & p & HH & HB')]; [exfalso; exact (Hne E)|]. split; [dexists t, pd, l, p; split; [exact HH| right; exact HB']|].
      destruct HB as [(_ & _ & E)|HB]; [exfalso; exact (Hne E)|].
      rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply seq_lseg_app. split; [exact HL|].
      cbn [seq_lseg hd]. split; [apply nLBof_in|].
      { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
      split; [exact A16|]. split; [exact POS|]. split; [| exact I]. dexists ct, cpad, cl, cp. split; [exact HR| exact HB].
  Qed.

  #[using="Type"] Lemma headrep_snoc : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.PN,$6.P,(4?.R8.R7.)P,(50.R7.R9.)P,(18.$4<.R8.R9.(1=.R7.R6.R5.R4.R3.))P,(17.VBUF,R5.)P,(17.=R7.)P,(17.(1?.R7.R8.)VEND,)(50.R<.(23.$6.R>.(19.$6.R7.(1<.$6.))))")
(* [comment removed for export] *).
  Proof.
    clear. intros nodes cur mm ct cpad cl cp N HCF HHD HR HB1 HB2 HB3. right.
    ddestruct HCF as (_ & _ & _ & _ & _ & _ & [[-> ->]|(Hne & _ & _ & _)]).
    - dexists ct, cpad, cl, cp. split; [exact HR| lia].
    - destruct HHD as [E|(t & pd & l & p & HH & HB)]; [exfalso; exact (Hne E)|]. dexists t, pd, l, p. rewrite hd_app_ne by exact Hne. split; [exact HH| exact HB].
  Qed.

  (* [comment removed for export] *)
  #[using="HI tp h PP P lo bs HC"] Lemma headrep_pres : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)PLBx,(7.$2=.)Pmm,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))P,(5<.$4<.VL,R3.(1?.(12.&40.Vsp,)->0.)R2.R1.)P,Pb,$2=.P,(29.$2=.R1.VLB,)(29.$2=.R2.R6.)P,(50.R4.R6.)(50.R4.R7.)")
(* [comment removed for export] *).
  Proof.
    open_ectx HC. clear -CWCUR DS2. intros nodes LBx mm m2 HP HS [->|(t & pd & l & p & HR & HB)]; [left; reflexivity| right].
    dexists t, pd, l, p. split; [| exact HB]. eapply heap_pres_rw_cells; [exact HP| exact HR|].
    eapply client_range_wsep; [exact CWCUR| exact HS| cbn; lia].
  Qed.

  #[using="Type"] Lemma lseg_pres : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "PLBx,(7.$2=.)Pl,(7.$6.)Pfin,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))PSP,$6.P,(5<.$4<.VL,R6.R1.R3.R2.)P,(51.$4<.R4.R7.VBUF,VEND,R6.R5.)(51.$4<.R4.R8.VBUF,VEND,R7.R6.)")
(* [comment removed for export] *).
  Proof.
    clear. intros LBx l fin mm m2 SP HP HL.
    eapply seq_lseg_mem; [exact HL| intros y Hy; eapply seq_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply heap_pres_rw_cells; [exact HP| exact HR|]. rewrite Hsz.
    eapply client_range_block; [eapply seq_lseg_in; [exact HL| exact Hy] | lia | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lseg_presx : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "PLBx,(7.$2=.)PLBn,(7.$2=.)PXc,(7.$56.)Pl,(7.$6.)Pfin,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))PSP,$6.P,(2;.$4<.VL,R8.R1.R6.R3.R2.)P,(51.$4<.R4.R8.VBUF,VEND,R6.R5.)P,Py,$6.P,(29.$6.R1.R8.)(8.(29.(24.$6.$6.)(26.$6.$6.R2.+20.)R<.)(5=.R:.R2.+20.))(51.$4<.R5.R:.VBUF,VEND,R8.R7.)")
(* [comment removed for export] *).
  Proof.
    clear. intros LBx LBn Xc l fin mm m2 SP HP HL HY.
    eapply seq_lseg_mem; [exact HL| intros y Hy; eapply seq_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. destruct (HY y Hy) as [HIn HD]. eapply heap_presx_rw_cells; [exact HP| exact HR| |]; rewrite Hsz.
    - eapply client_range_block; [exact HIn | lia | cbn; lia].
    - exact HD.
  Qed.

  (* [comment removed for export] *)
  #[using="HI tp h PP P lo bs HC"] Lemma headrep_presx : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)PLBx,(7.$2=.)PXc,(7.$56.)Pmm,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))P,(2;.$4<.VL,R4.(1?.(12.&40.Vsp,)->0.)R3.R2.R1.)P,Pb,$2=.P,(29.$2=.R1.VLB,)(29.$2=.R2.R7.)P,(5=.R5.VCUR,+20.)P,(50.R5.R8.)(50.R5.R9.)")
(* [comment removed for export] *).
  Proof.
    open_ectx HC. clear -CWCUR DS2. intros nodes LBx Xc mm m2 HP HS HD [->|(t & pd & l & p & HR & HB)]; [left; reflexivity| right].
    dexists t, pd, l, p. split; [| exact HB]. eapply heap_presx_rw_cells; [exact HP| exact HR| | exact HD].
    eapply client_range_wsep; [exact CWCUR| exact HS| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="HI tp h P END BUF lo bs HC"] Lemma presx_call : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "PLBx,(7.$2=.)Pmm,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))Pa1,$6.Pb1,$6.P,(2;.$4<.VL,R5.(1?.(12.&40.Vsp,)->0.)(19.(24.$6.$6.)(26.$6.$6.R2.R1.)(1<.(24.$6.$6.)))R4.R3.)P,Pb,$2=.P,(29.$2=.R1.VLB,)(29.$2=.R2.R8.)P,(17.(1?.(12.&40.Vsp,)->0.)R4.)P,(17.R4.(12.&40.Vsp,))(2;.$4<.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))R8.R7.)")
(* [comment removed for export] *).
  Proof.
    pose proof in_block_below as IBB. open_ectx HC. clear -ACL SLO HLS DHI IBB.
    intros LBx mm m2 a1 b1 HP HS Ha1 Hb a Ha Hc Ho. apply HP; [exact Ha| |].
    - destruct Hc as [Hs|[Hd|(b & Hb' & Hr)]]; [left; clear -Hs; lia| right; left; exact Hd| right; right].
      exists b. split; [apply HS; exact Hb'| exact Hr].
    - cbn [outside]. split; [| exact I]. destruct Hc as [Hs|[[Hd1 Hd2]|Hb']]; [clear -Hs Hb; lia| clear -Hd1 Hd2 DHI ACL SLO HLS Ha1; lia|].
      pose proof (IBB a Hb') as HY. clear -HY ACL SLO HLS Ha1. lia.
  Qed.

  #[using="tp P END HC"] Lemma cur_wrange : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.PLBx,(7.$2=.)P,(4>.R3.)P,(4?.R4.R3.)P,Pb,$2=.P,(29.$2=.R1.(4=.R6.))(29.$2=.R2.R5.)(3:.VL,R4.Vlo,(14.$4<.VL,VHI,Vh,)R5.+20.)")
(* [comment removed for export] *).
  Proof.
    pose proof cur_cases as CC. open_ectx HC. clear -CWCUR DIM1 DIM2 CC. intros nodes cur LBx HFR HCF HS.
    destruct (CC nodes cur HFR HCF) as [->|(HIN & _)].
    - eapply client_wrange_inside; [exact CWCUR| intros b Hb; apply HS; apply nLBof_sub; exact Hb| lia| lia].
    - eapply client_wrange_block; [apply HS; apply nLBof_in; exact HIN| lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="tp h P END HC"] Lemma snoc_facts : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_A ()) "Pnodes,(7.$6.)Pcur,$6.PN,$6.Phc2,(5.$4<.VL,VHI,)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.P,(2:.$4<.VL,VHI,R3.(19.(24.$6.$6.)(26.$6.$6.R4.+20.)(4=.R6.))R2.R1.)P,(28.$6.R7.)P,(4>.R8.)P,(4?.R9.R8.)P,(47.VL,R8.+20.)P,(16.=(2?.(30.(2.&8.)Vbs,)))(8.(28.$6.(23.$6.R<.(19.$6.R:.(1<.$6.))))(8.(4>.(23.$6.R<.(19.$6.R:.(1<.$6.))))(8.(4?.(23.$6.R<.(19.$6.R:.(1<.$6.)))R:.)(8.(1>.(17.(1?.R:.+20.)R;.)(17.(1?.R;.+20.)R:.))(8.(1>.(17.(1?.R:.+20.)VPP,)(17.(1?.VPP,+8.)R:.))(1>.(17.(1?.R:.+20.)VBUF,)(17.(1?.VBUF,(2?.(30.(2.&8.)Vbs,)))R:.)))))))")
(* [comment removed for export] *).
  Proof.
    pose proof cur_cases as CC. open_ectx HC. clear -ACL CWPP CWCUR CRBUF DIM1 DIM2 SLO HLS SPR CC.
    (intros nodes cur N hc2 mm moc HH HND HFR HCF dd_H; ddestruct dd_H as (HN0 & HN16 & _ & HNC & HNI); intros LBS).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [_ HAP]. cbn [blocks_apart] in HAP. destruct HAP as [HAPN HAPc].
    assert (HND' : N + 32 <= hl_data_lo L \/ hl_data_hi L <= N) by lia.
    assert (HAPN0 : forall B j, In (B, j) LB -> N + 32 <= B \/ B + j <= N) by (intros B j HBj; apply HAPN; apply nLBof_sub; exact HBj).
    assert (APC : N + 32 <= CUR \/ CUR + 32 <= N)
      by (eapply client_wrange_apart; [exact CWCUR | lia | lia | exact ACL | exact HNC | exact HND' | exact HAPN0]).
    assert (APP : N + 32 <= PP \/ PP + 8 <= N)
      by (eapply client_wrange_apart; [exact CWPP | lia | lia | exact ACL | exact HNC | exact HND' | exact HAPN0]).
    assert (APB : N + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= N)
      by (eapply client_range_apart; [exact CRBUF | lia | lia | exact ACL | exact HNC | exact HND' | exact HAPN0]).
    assert (APcur : N + 32 <= cur \/ cur + 32 <= N).
    { destruct (CC nodes cur HFR HCF) as [->|(HIN & _)]; [exact APC|]. apply HAPN. apply nLBof_in. exact HIN. }
    split; [| split; [| split; [| split; [exact APcur| split; [exact APP| exact APB]]]]].
    - apply List.NoDup_app; [exact HND| constructor; [intros HIn; destruct HIn| constructor] |].
      intros y Hy [E|[]]. pose proof (HAPN y 32 (nLBof_in nodes y Hy)). lia.
    - intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|[]]]; [exact (HFR y Hy)|].
      split; [exact HNC|]. split; [exact HNI| exact HAPN0].
    - unfold curF. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      right. split; [apply app_cons_not_nil || (destruct nodes; discriminate)|]. split; [symmetry; apply last_last|]. split; [exact HN16| lia].
  Qed.
End Walk.
