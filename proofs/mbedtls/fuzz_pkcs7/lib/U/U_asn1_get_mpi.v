(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX HeapIface Arr Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_mpi_addsub U_mpi_read_binary.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_asn1_get_mpi () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_read_binary.mpi_read_binary_stmt"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "asn1_get_mpi_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nat"; "asn1_get_mpi_stmt"; "U_ASN1_GET_MPI"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_read_binary.U_MPI_READ_BINARY"].


Definition U_ASN1_GET_MPI : Z := 0x1e850.

Notation ASN1_GET_MPI_STACK := 112 (only parsing).

Definition asn1_get_mpi_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (PP P END : Z) (dX : mpd) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1>.O1=.O1<.)Lh',(5.O1>.O1=.O1<.)(1.(6.$7.)LLB',(6.$7.)(1.$8.LdX',$8.(1.$9.Lr,$9.(1.$9.Lp',$9.(:.(;.$0.R16.(<.(=.(>.O1;.O1:.O19.O18.R15.R14.R13.O17.O16.(?.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R;.R:.R9.R8.)O;.(10.O1;.)O:.(11.(2.&40.))R7.(12.O1>.))R6.))(:.(13.O1>.R7.)(:.(14.O1>.R7.O3.(15.&40.O1:.))(:.(16.O1.R6.)(:.(;.$9.(17.O1>.O1=.O1<.R5.)(17.O1>.O1=.O1<.O9.))(:.(18.O1>.O1=.O1<.R5.R4.R7.R6.)(:.(19.O1>.R7.R4.R3.)(:.(1:.O8.O4.R4.R3.)(:.(1;.O1>.O1=.O8.(15.&40.O1:.)(1<.(1=.$9.$9.)(1>.$9.$9.O7.(1?.O7.+8.))(20.O4.))O2.R7.)(:.(21.O1>.O1=.R7.)(:.(22.O1>.R7.O7.(1<.$23.(24.(?.&40.R1.))(25.$23.)))(:.(:.(26.O6.R1.)(26.R1.O5.))(:.(:.(27.-7?.R2.)(26.R2.=))(:.P,(;.$9.R2.=)(:.(26.(1?.O6.+2.)R2.)(;.$9.(28.R4.)+1.))Pb,$7.P,(29.$7.R1.(2:.R4.))(2;.(29.$7.R2.(2:.O4.))(2<.(29.$7.R2.O8.))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_mpi_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY RB MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "P,(2=.O6.O5.O4.O2.O1.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O6.O5.O4.)PLB,(6.$7.)PPP,$9.PP,$9.PEND,$9.PBUF,$9.Pbs,(6.(2.&8.))PdX,$8.Plo,$9.P,(18.O6.O5.O4.R9.R8.R;.R:.)P,(22.O6.R<.R8.(1<.$23.(24.(?.&40.R7.))(25.$23.)))P,(2?.O6.R=.R6.R5.)P,(26.R7.R9.)P,(26.R:.R9.)P,(26.R:.(1?.R9.(30.(31.(2.&8.)R8.))))P,(27.(1?.R:.(30.(31.(2.&8.)R9.)))(32.+2.+3?.))P,(19.O6.R12.R?.R9.)P,(2<.(;.$33.(34.R:.)$35.))P,(36.O5.R11.(15.&40.R34.)(17.O6.O5.O4.R12.)R;.)P,(2;.(26.(1?.R11.+8.)R>.)(26.(1?.R>.(30.(31.(2.&8.)R=.)))R11.))P,(2;.(26.(1?.R12.+8.)(37.R=.))(26.(1?.(37.R=.)+10.)R12.))P,P,(;.$33.(34.R>.)$38.)(2;.(26.(1?.R14.+8.)(39.R?.))(26.(1?.(39.R?.)(3:.+4.(3;.R?.)))R14.))P,(2;.(26.(1?.R11.(30.(31.(2.&8.)R10.)))(37.R?.))(26.(1?.(37.R?.)+10.)R11.))P,P,(;.$33.(34.R10.)$38.)(2;.(26.(1?.R13.(30.(31.(2.&8.)R12.)))(39.R11.))(26.(1?.(39.R11.)(3:.+4.(3;.R11.)))R13.))P,(;.$9.(3<.R16.+8.)=)P,(27.=R17.)P,(27.=R15.)P,(14.O6.R1=.R13.(15.&40.R3=.))P,(26.R14.(3=.(3=.(15.&40.R3>.)+70.)(3>.O5.)))P,(26.(3?.O5.)R15.)P,(26.(15.&40.R40.)(17.O6.O5.O4.R1>.))P,(;.$9.(3<.(15.&40.R41.)+10.)=)P,(26.(40.O5.)(3?.O5.))P,(26.(41.O5.)(42.O5.))P,(26.(40.O5.)(43.O5.))P,(2;.(26.(1?.R21.+8.)R1;.)(26.(15.&40.R45.)R21.))P,(2;.(26.(1?.R1?.(30.(31.(2.&8.)R1>.)))R1<.)(26.(15.&40.R46.)R1?.))P,(2;.(26.(1?.R23.+8.)(42.O5.))(26.(40.O5.)R23.))P,(44.O5.R25.R1>.(17.O6.O5.O4.R26.)R24.+8.)P,(45.O5.R26.R1?.R22.(30.(31.(2.&8.)R21.)))P,(;.(2.&40.)R48.(?.&40.(46.O5.)))P,(13.O6.R2;.)P,(21.O6.O5.R2<.)P,(47.O5.O1.+8.)P,(;.(2.&40.)R46.(?.&40.R2:.))P,(;.(2.&40.)R46.(?.&40.R29.))P,(;.(2.&40.)R46.(?.&40.(37.R27.)))(48.O6.R30.(49.O6.O5.O4.R52.R51.R50.R4?.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R33.R32.R2?.R2>.R2=.R2<.R2;.R28.R27.R31.R30.)(=.(>.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(?.&40.O3.)R32.(11.(2.&40.))R31.(12.O6.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L11656893434.10L62891525837.1000000@00KS1A2bs1a1n2Hn2HbS1A2bs1a2Ha". (* [comment removed for export] *)
Lemma bytes_at_sub : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "Psegs,(6.$4:.)Pm,P,(2.&40.)(3.(2.&8.))PA,$9.Pbs,(6.(2.&8.))Pa,$9.Pn,$9.P,(2?.R6.R5.R4.R3.)P,(26.R5.R3.)P,(26.=R3.)P,(26.(1?.R5.R4.)(1?.R7.(30.(31.(2.&8.)R6.))))(2?.R:.R9.R6.(4;.(2.&8.)(4<.R5.)(4=.(2.&8.)(4<.(3=.R6.R8.))R7.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A bs a n H Ha Hn Hb.
  rewrite <- (firstn_skipn (Z.to_nat (a - A)) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  replace (A + Z.of_nat (Z.to_nat (a - A))) with a in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat (a - A)) bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39025037992.7L51857236553.700000?00HS2bs1A1a1n1H2H1S2bs1n2H0". (* [comment removed for export] *)
Lemma bytes_at_sub_length : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "Pbs,(6.(2.&8.))PA,$9.Pa,$9.Pn,$9.P,(26.R3.R2.)P,(26.=R2.)P,(26.(1?.R4.R3.)(1?.R5.(30.(31.(2.&8.)R6.))))(;.$9.(30.(31.(2.&8.)(4;.(2.&8.)(4<.R4.)(4=.(2.&8.)(4<.(3=.R5.R6.))R7.))))R4.)")
(* [comment removed for export] *).
Proof. intros. rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma mpd_at_munch : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "Psegs,(6.$4:.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)Pd,$8.PW,(6.$4>.)P,(19.R6.R5.R3.R2.)P,(2<.(;.$33.(34.R3.)$35.))P,(4?.R3.R7.R6.)P,(50.R9.R8.R7.)P,(51.R5.(37.R6.)+10.)P,P,(;.$33.(34.R7.)$38.)(51.R7.(39.R8.)(3:.+4.(3;.R8.)))(19.R<.R:.R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB d W [HA HS] HNS MU WM HD1 HD2. split; [| exact HS].
  ddestruct HA as (HR & HAL & HPOS & HL & HN & HO).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_transport; [exact HR| exact MU| exact WM| exact HD1].
  - destruct (md_own d); [exact HO| | exfalso; exact (HNS eq_refl)].
    ddestruct HO as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    eapply u32arr_transport; [exact H4| exact MU| exact WM|]. rewrite HL. apply HD2. reflexivity.
Qed.

Lemma mpd_out_refl : forall LB d, md_own d <> LStatic -> mpd_out LB d LB d.
Proof.
  intros LB d H. unfold mpd_out. repeat split; auto.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L16562103865.1300000DS2SP3SP'3top2HS1a2Hs". (* [comment removed for export] *)
Lemma mpd_writable_sp_mono : forall L LB SP SP' top d,
  mpd_writable L LB SP top d -> SP' <= SP -> mpd_writable L LB SP' top d.
Proof.
  (intros L LB SP SP' top d dd_H; ddestruct dd_H as (H1 & H2 & H3); intros HS). split; [| split; [exact H2| exact H3]].
  intros a Ha. destruct (H1 a Ha) as [Hs|[Hd|Hb]]; [left; lia| right; left; exact Hd| right; right; exact Hb].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59314873579.1800000BS2dX1A1n1a2Ha2Hr1H". (* [comment removed for export] *)
Lemma client_wrange_mpd_out : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "PL,$52.PLB,(6.$7.)PLB',(6.$7.)Plo,$9.PTOP,$9.PdX,$8.PdX',$8.PA,$9.Pn,$9.P,(44.R9.R8.R6.R5.R2.R1.)P,(1:.R9.R5.R8.R4.)P,P,(;.$33.(34.R6.)$38.)(2;.(26.(1?.R5.R4.)(39.R7.))(26.(1?.(39.R7.)(3:.+4.(3;.R7.)))R5.))(44.R<.R:.R9.R8.R5.R4.)")
(* [comment removed for export] *).
Proof.
  (intros L LB LB' lo TOP dX dX' A n CW dd_H; ddestruct dd_H as (_ & _ & _ & HK & _); intros HD a Ha).
  destruct (CW a Ha) as [Hs|[Hd|(b & Hb & Hr)]]; [left; exact Hs| right; left; exact Hd| right; right].
  exists b. split; [| exact Hr]. apply HK; [exact Hb|].
  unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail).
  intros [<-|[]]. cbn in Hr. destruct (HD eq_refl); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18797602918.1300000;S1C1j1B1k1H". (* [comment removed for export] *)
Lemma blocks_apart_neq : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "PLB,(6.$7.)Pb1,$7.Pb2,$7.P,(53.R3.)P,(29.$7.R3.R4.)P,(29.$7.R3.R5.)P,(2<.(;.$7.R5.R4.))P,(27.=(54.$9.$9.R6.))P,(27.=(54.$9.$9.R6.))(2;.(26.(1?.(55.$9.$9.R8.)(54.$9.$9.R8.))(55.$9.$9.R7.))(26.(1?.(55.$9.$9.R7.)(54.$9.$9.R7.))(55.$9.$9.R8.)))")
(* [comment removed for export] *).
Proof.
  induction LB as [|[C j] r IH]; cbn; intros b1 b2 HA H1 H2 HNE P1 P2; [destruct H1|].
  destruct HA as [HC Hr].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - exfalso. apply HNE. congruence.
  - subst b1. destruct b2 as [B k]. cbn in *. exact (HC B k H2).
  - subst b2. destruct b1 as [B k]. cbn in *. destruct (HC B k H1); lia.
  - apply IH; assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L16350316721.36L25728158397.36L37924432859.36L43360042234.37L47143634736.37L49186560843.45L51794627208.45L59308585607.40L59308587542.40L59314873579.43L59315284336.46L59347697501.36L68394101197.3500000<00H00T00^00i01601F01i02L02e03>03I03SS3dX'1A1n2H2S3dX'1A1n2H2S3dX'1A1n2HnS3dX'1A2H1S3dX'1A3HN1S3dX'1A3HN11aS3dX'1A1a1B1k2HrS1L3dX'1A3HN14DIM14DIM23HI21a2HY2HdS1L2lo3TOP3dX'1A3HN13ACL2HC1a2HY2HsS2dX3dX'1A1n2Hn1a2HX2Hr1HS3dX'1A1a1B1k2Hr1Q3HN12HYS2dX3dX'2E2S3dX'1A2H1". (* [comment removed for export] *)
Lemma client_apart_new_limbs : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "Psegs,(6.$4:.)PL,$52.PHI,(56.R2.R1.)Ph',(5.R3.R2.R1.)PLB,(6.$7.)PLB',(6.$7.)Pm',P,(2.&40.)(3.(2.&8.))Pm'',P,(2.&40.)(3.(2.&8.))Pmo',$4.Plo,$9.PTOP,$9.PdX,$8.PdX',$8.PA,$9.Pn,$9.P,(18.R?.R>.R=.R<.R:.R8.R7.)P,(19.R10.R:.R;.R4.)P,(1:.R=.R6.R<.R5.)P,Pb,$7.P,(29.$7.R1.(2:.R7.))(2;.(29.$7.R2.(2:.R9.))(2<.(29.$7.R2.R10.)))P,(44.R12.R?.R:.R9.R6.R5.)P,(27.=R6.)P,(26.(3?.R14.)R<.)P,(26.(41.R15.)(42.R15.))P,(26.(40.R16.)(43.R16.))P,P,(;.$33.(34.R=.)$38.)(2;.(26.(1?.R<.R;.)(39.R>.))(26.(1?.(39.R>.)(3:.+4.(3;.R>.)))R<.))P,(;.$33.(34.R=.)$38.)(2;.(26.(1?.R=.R<.)(39.R>.))(26.(1?.(39.R>.)(3:.+4.(3;.R>.)))R=.))")
(* [comment removed for export] *).
Proof.
  intros segs L HI h' LB LB' m' m'' mo' lo TOP dX dX' A n HH [HA _] HOUT HF CW Hn ACL DIM1 DIM2 HD HO.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. rewrite Forall_forall in HBR.
  ddestruct HA as (_ & _ & _ & HL & HN & HOWN). rewrite HO in HOWN. ddestruct HOWN as (HN1 & HIN & _ & _).
  pose proof (HBR _ HIN) as (_ & _ & _ & HC & HI2). cbn [fst snd] in HC, HI2.
  destruct (HF (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite HO; left; reflexivity)) as [HOLD|HNEW].
  - (* [comment removed for export] *) unfold mpd_blk in HOLD. destruct (md_own dX) eqn:EO; try (destruct HOLD; fail).
    destruct HOLD as [E|[]]. injection E as E1 E2. rewrite <- E1.
    replace (4 * md_n dX') with (4 * md_n dX) by lia. apply HD. reflexivity.
  - destruct (Z_lt_le_dec A (md_p dX' + 4 * md_n dX')) as [H1|H1]; [| right; lia].
    destruct (Z_lt_le_dec (md_p dX') (A + n)) as [H2|H2]; [| left; lia].
    exfalso. set (a := Z.max A (md_p dX')).
    assert (HX : A <= a < A + n) by (subst a; split; [apply Z.le_max_l| apply Z.max_lub_lt; lia]).
    assert (HY : md_p dX' <= a < md_p dX' + 4 * md_n dX') by (subst a; split; [apply Z.le_max_r| apply Z.max_lub_lt; lia]).
    destruct (CW a HX) as [Hs|[[Hd _]|(b & Hb & Hr)]]; [lia| lia|].
    ddestruct HOUT as (_ & _ & _ & HK & _).
    assert (HbLB' : In b LB').
    { apply HK; [exact Hb|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail).
      intros [<-|[]]. cbn in Hr. destruct (HD eq_refl); lia. }
    assert (NE : b <> (md_p dX', 4 * md_n dX')) by (intros ->; exact (HNEW Hb)).
    destruct b as [B k]. cbn in Hr.
    destruct (blocks_apart_neq _ _ _ HAP HbLB' HIN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L16576048038.14L37273016624.15L38630852471.16L53410322327.15L59308577866.16L6661866317.19 L6668188668.15 00000700C00T00[01401B01MS1A1k1KS2SP3top1a1CS1L1A1k2lo3CLO2H'S1A1k1KS1L2SP1A1k2lo3CLO2LK1H2H'S1L1a1B1n1C2B4S1L3DHI1a1C". (* [comment removed for export] *)
Lemma client_wrange_where' L LB SP top A k lo : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "P,(44.O7.O6.O5.O4.O3.O2.)P,(27.=O2.)P,(57.(1=.$9.$9.)Lb,(1=.$9.$9.)(58.O7.(55.$9.$9.R1.)(54.$9.$9.R1.))O6.)P,(26.(40.O7.)(3?.O7.))P,(26.(3?.O7.)O1.)P,(26.(1?.O1.O2.)O5.)(2;.(26.(1?.O3.O2.)O1.)(26.O5.O3.))")
(* [comment removed for export] *).
Proof.
  intros CW K BR DHI CLO LK.
  assert (LOW : forall a, client_waddr L LB SP top a -> SP <= a \/ a < alloc_ceiling).
  { intros a [C|[C|([B n] & Hb & C)]]; [left; lia| right; lia|]. right. pose proof (proj1 (Forall_forall _ _) BR _ Hb) as (_ & _ & _ & B4 & _). cbn in C, B4. lia. }
  destruct (LOW _ (CW A ltac:(lia))) as [H|H]; [right; exact H|].
  destruct (LOW _ (CW (A + k - 1) ltac:(lia))) as [H'|H']; [exfalso; lia| left; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L37275288388.1600000@S2SP3SP'2HS1a2Hs". (* [comment removed for export] *)
Lemma heap_presx_weaken : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "Psegs,(6.$4:.)PL,$52.PLB,(6.$7.)PSP,$9.PSP',$9.PX,(6.$4>.)PX',(6.$4>.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))P,(1;.R9.R8.R7.R6.R4.R2.R1.)P,(26.R7.R6.)P,Pa,$9.P,(59.R6.R1.)(59.R8.R2.)(1;.R<.R;.R:.R8.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs L LB SP SP' X X' m m' H HS HX a Ha Hc Ho. apply H; [exact Ha| | apply HX; exact Ho].
  destruct Hc as [Hs|[Hd|Hb]]; [left; lia| right; left; exact Hd| right; right; exact Hb].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Ltac al8_close k := exfalso; rewrite ?unsigned_lit in k by lia; change 7 with (Z.ones 3) in k; rewrite Z.land_ones in k by lia; change (2 ^ 3) with 8 in k; lia.
Ltac b2z_close k :=
  exfalso;
  repeat match type of k with context [Z.ltb ?a ?b] =>
    first [ let H := fresh in assert (H : a < b) by lia; apply Z.ltb_lt in H; rewrite H in k; clear H
          | let H := fresh in assert (H : b <= a) by lia; apply Z.ltb_ge in H; rewrite H in k; clear H ] end;
  cbn in k; first [discriminate k | lia].

Ltac joinr H1 H2 :=
  lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn; lia);
    let Hj := fresh "J" in
    pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
    cbn [app] in H1
  end end.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable MSF : Z.
  Hypothesis HRB : mpi_read_binary_stmt usegs L HI U_MPI_READ_BINARY MSF.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP P END BUF lo : Z) (bs : list byte) (dX : mpd).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis HX : mpd_at usegs m LB dX.
  Hypothesis HNS : md_own dX <> LStatic.
  Hypothesis HWR : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis DX1 : PP + 8 <= md_addr dX \/ md_addr dX + 16 <= PP.
  Hypothesis DX2 : md_own dX = LHeap -> PP + 8 <= md_p dX \/ md_p dX + 4 * md_n dX <= PP.
  Hypothesis DX3 : BUF + Z.of_nat (length bs) <= md_addr dX \/ md_addr dX + 16 <= BUF.
  Hypothesis DX4 : md_own dX = LHeap -> BUF + Z.of_nat (length bs) <= md_p dX \/ md_p dX + 4 * md_n dX <= BUF.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 112 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis OD1 : PP + 8 <= hl_data_lo L \/ hl_data_hi L <= PP.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis CA : const_at L MSF 8.
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.
  (* [comment removed for export] *)
  Hypothesis DSX : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX.
  Hypothesis XLB : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= alloc_ceiling /\ 0 < md_p dX.

  Notation W := [(PP, PP + 8); (bv_unsigned sp - 32, bv_unsigned sp)].
  Notation POST := (asn1_get_mpi_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP P END dX lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -32)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L52101695852.19L52103791482.2200000Q011S2sp1a2Hs1L2lo3SLO3HLS3ACL3DHI2HdS1L2sp2lo3SLO3HLS3ACL1a1b2Hr3Hce". (* [comment removed for export] *)
  #[using="lo SLO HLS ACL DHI HBR0"] Lemma presx_W : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "Pmm,P,(2.&40.)(3.(2.&8.))P,(4?.(1<.(1=.$9.$9.)(1>.$9.$9.VPP,(1?.VPP,+8.))(1<.(1=.$9.$9.)(1>.$9.$9.(3=.(15.&40.Vsp,)+20.)(15.&40.Vsp,))(25.(1=.$9.$9.))))Vm,R1.)P,(50.$5:.Vm,R2.)(1;.$5:.VL,VLB,(15.&40.Vsp,)(1<.(1=.$9.$9.)(1>.$9.$9.VPP,(1?.VPP,+8.))(20.VdX,))Vm,R3.)")
(* [comment removed for export] *).
  Proof.
    clear - ACL HBR0 DHI SLO HLS. intros mm MU WM. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. cbn [outside] in Ho |- *. destruct Ho as [Ho _]. split; [exact Ho|]. split; [| exact I].
    destruct Hc as [Hs|[[Hd _]|(b & Hb & Hr)]]; [lia| lia|].
    rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Hce & _). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L38348216800.19L38348297982.2000000O012S1L2sp2PP2lo2dX3DX13SLO3HLS3DSXS1L2sp2PP2lo2dX3DX23SLO3HLS3ACL3XLB". (* [comment removed for export] *)
  #[using="L lo HX HNS DX1 DX2 SLO HLS ACL DSX XLB"] Lemma mpd_at_W : forall mm, munch W m mm -> wmono usegs m mm -> mpd_at usegs mm LB dX.
  Proof.
    clear - HX HNS DX1 DX2 DSX XLB ACL SLO HLS. intros mm MU WM.
    eapply mpd_at_munch; [exact HX| exact HNS| exact MU| exact WM| |]; cbn [disjoint_from].
    - lia.
    - intros HO. specialize (DX2 HO). specialize (XLB HO). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L13952552502.97L15139255722.97L20944616522.97L21887662552.92L26086495700.97L29604563019.97L33510041944.92L3672538608.97 L39532515111.97L39939731869.98L41564619544.97L45172553166.97L61492657120.97L631627681.97  L64027611664.97L66083662040.9200000?01V01k02502602702A02R02S03e03o04D04S04T04U04_S2sp2PP2bs1r2HrS1L2sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SLO3HLS3ACL3ACP3DS13DS33DSX1p1r2Hp2HrS2sp2PP1P3END2bs1p2HpS2sp2PP2bsFFS2sp2PP2bsS1L2HI2sp1h2PP2bsFS1L2sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SLO3HLS3ACL3ACP3DS13DS33DSX1p2HpS2sp2PP2bsS2sp2PP1P3END2bs1p2HpS2sp2PP2bs1r2HrFFS2sp2PP2bs". (* [comment removed for export] *)
  #[using="BUF bs B1 B3 HX HNS D2 DX1 DX2 DX3 PPB SLO HLS ACL ACP DHI DS1 DS3 HBR0 DSX XLB"] Lemma fail_walk : forall (p r : Z) (j : list byte) (x13 x14 x15 x16 x17 : word) (mm : mem), HEAP usegs L HI h LB mm mo -> rw_cells usegs mm PP [C8 (Z_to_bv 64 p)] -> P <= p <= END -> -127 < r < 0 -> rw_cells usegs mm (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra] -> stk usegs mm lo (bv_unsigned sp + -32) -> mem_inv usegs mm -> statics_ok usegs L mm -> munch W m mm -> wmono usegs m mm -> forall (x9 x11 x12 x1 x5 x6 x7 x28 x29 x30 x31 : word), aevtM usegs mo POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 PP) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x1e8f4) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros p r j x13 x14 x15 x16 x17 mm HH HPP Hp Hr FR ST MI SOK MU WM x9 x11 x12 x1 x5 x6 x7 x28 x29 x30 x31.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    apply aevtM_done. unfold asn1_get_mpi_post. deexists 14.
    dexists mm, mo, h, LB, dX, r, p.
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - apply mo_frame_refl.
    - apply mpd_at_W; assumption.
    - apply mpd_out_refl. exact HNS.
    - apply presx_W; assumption.
    - intros b Hb. left. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00n0@D28496781288.135D30471956959.135D37216054521.133D37226362885.135D44492853884.135D4453582353.135 D47139703723.133D61556549392.135D61571118060.133D63898547005.135L13952736592.2  L1427382265.135 L21887662552.126L30478252847.128L33510041944.126L39941750528.133L41202929119.125L41562522430.132L41940799491.135L41940799575.100L53271535775.125L5360928661.3   L58823222561.4  L59382276234.134L61492275334.2  L61565418556.88 L63368329103.135L63892251085.128L64180445855.89 L66083662040.126L9817085104.88  R11326150134.96 R11338682488.97 R11423978205.103R13134887424.135R13950634009.135R19205489441.103R23880466740.103R24111427218.96 R2689854971.135 R2691935871.136 R37370775634.103R38443780093.103R38758372169.103R42814994432.96 R45293011284.103R45822971042.134R52700097983.135R5592750443.135 R574998272.135  R57764720491.97 R57777220325.96 R61027708549.135R61300841723.103R61490183631.135R62031154087.96 R62035430953.97 R6667934847.135 R7190686615.123 R7190735638.103 R8200475188.104 R8200884917.103 00000P00Q00f01J01K01k02<02`03503603<03J03X04T04b06D06R06`06n07<07J07U07`07n08409409B09g0:R0:`0;`0<V0=O0>W0>X0>Y0>Z0?a0@70@a0AK0BI0Bc0Ca0Ck0DV0Dk0Ed0Fh0G=0GT0Gd0H90HP0HQ0IH0J?0K20K]0LH0MN0N]S2sp2PP2bs2p13ibs2HB5Ha_st5Hl_stFS2sp2PP2bs3PPB3ibs2HBS2sp2PP2bs3PPB2p13ibs2HB5Ha_st5Hl_stFS2sp2PP2bs2p13ibs2HB5Ha_st5Hl_stS2sp2PP2bs3ibs2HBS2sp2PP2bs3PPB2p13ibs2HB5Ha_st5Hl_stS2sp2PP2bs3PPB3ibs2HBFS1r2HrS2sp2PP2bs3ibsS2sp2PP2bs3ibsS1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP2p13ibs2HB5Ha_st5Hl_st2HDS2sp2PP2bs3ibsS1L2sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SLO3HLS3ACL3ACP3DS13DS33DSX2p12Lw2Hp3ibs2KC4LENIS2sp2PP2bs3ibsS2sp2PP2bs3ibsS2sp2PP2bs3ibsS2sp2PP2bs3ibsS2sp2PP2bs3ibsS2PP3dX22APS2dX1a1k2H3S2sp2PP2bs3ibsS1r2HrS1L2sp2PP1P3END3BUF2lo2bs2B12B32B43PPB3NZ33SLO3HLS3ACL3ACP2p12HpS2sp2PP2bs3ibsS1L2sp2PP2bs2p13ibs2HB5Ha_st5Hl_st2HDS2sp2PP1P3END3BUF2bs2B12B32B43PPB3NZ32p12HpS2sp2PP2bs3ibsS1L2sp2PP1P3END3BUF2lo2bs2B12B32B43PPB3NZ33SLO3HLS3ACL3ACP2p12HpS1L2sp2PP1P3END3BUF2lo2bs2B13PPB3SLO3HLS3ACL3ACP2p12HpS1L2sp2PP1P3END3BUF2lo2bs2B13PPB3SLO3HLS3ACL3ACP2p12Lw2HpS1L2sp2PP1P3END3BUF2lo2bs2B12B33PPB3SLO3HLS3ACL3ACP2p12Lw2Hp2KC3ibs1a2HaFFFS1L2sp2PP1P3END3BUF2lo2bs2B12B33PPB3SLO3HLS3ACL3ACP3DS32p12Lw2Hp2KC3ibsS2sp2PP1P3END2bs2p12HpS1L2sp2PP2lo2bs2dX3PPB3SLO3HLS3ACL3ACP3ibsS1L2sp2PP2lo2bs2dX3PPB3SLO3HLS3ACL3ACP3ibsS1L2sp2PP3END3BUF2lo2bs2B32B43PPB3SLO3HLS3ACL3ACP2p12Lw2KC3ibsS1L2HI2sp1h2PP2bs4HTOP3ibsS1L2sp2PP1P3END3BUF2lo2bs2B13PPB3NZ33SLO3HLS3ACL3ACP2p12Hp3ibsS2sp2PP2bsS1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP3SPA3ibsS2sp2PP2bs2dX3DX13ibsS1L2sp2PP3END2lo2bs3PPB3SLO3HLS3ACL3ACP2p12Lw3ibs2KC4LENIS1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP3SPA2p12Lw2Hp3ibs3dX21r3Hr0S2sp2PP2lo2bs3DS13ibsS2sp2PP3BUF2bs2p12Lw2LRS2sp2PP2bs2Lw2LRS2sp2PP2bs2dX3DX13ibsS1L2sp2PP2lo2bs3SLO3ibsFS1L2sp2PP3END3BUF2lo2bs2B33PPB3SLO3HLS3ACL3ACP2p12Lw2KCS1L2sp2PP3END3BUF2lo2bs2B33PPB3SLO3HLS3ACL3ACP2p12Lw2KCS1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP2p12Hp3ibsS1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP3SPB3ibsS1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP3SPB3ibsS1L2sp2PP1P3END3BUF2lo2bs2dX2B12B33PPB3SLO3HLS3ACL3ACP2p12Lw2Hp2KC3ibsS1L2sp2PP1P3END3BUF2lo2bs2dX2B12B33DX33PPB3SLO3HLS3ACL3ACP2p12Lw2Hp2KC3ibs4LENI". (* [comment removed for export] *)
  #[using="MSF HRB B1 B3 B4 HX HNS HWR D2 DX1 DX2 DX3 DX4 PPB NZ1 NZ3 SLO HLS ACL ACP HTOP SPA DHI DIM1 DIM2 DS1 DS3 OD1 CWPP CRBUF TP CA SPB HBR0 DSX XLB"] Lemma j1_walk : forall (p1 : Z) (Lw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mm : mem), P + 2 <= p1 <= END -> p1 + bv_unsigned Lw <= END -> HEAP usegs L HI h LB mm mo -> rw_cells usegs mm PP [C8 (Z_to_bv 64 p1)] -> rw_cells usegs mm (bv_unsigned sp + -32) [C8 Lw; C8 s1; C8 s0; C8 ra] -> stk usegs mm lo (bv_unsigned sp + -32) -> mem_inv usegs mm -> statics_ok usegs L mm -> bytes_at usegs mm BUF bs -> munch W m mm -> wmono usegs m mm -> aevtM usegs mo POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 PP) (Z_to_bv 64 (md_addr dX)) x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x1e8b0) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros p1 Lw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm Hp KC HH HPP FR ST MI SOK HBUF MU WM.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    zstep. zstep. zstep. zstep.
    set (ibs := firstn (Z.to_nat (bv_unsigned Lw)) (skipn (Z.to_nat (p1 - BUF)) bs)).
    assert (LENI : Z.of_nat (length ibs) = bv_unsigned Lw) by (subst ibs; apply bytes_at_sub_length; plia).
    assert (HIB : bytes_at usegs mm p1 ibs) by (subst ibs; eapply bytes_at_sub; [exact HBUF| plia| plia| plia]).
    pose proof (mpd_at_W mm MU WM) as HXm.
    assert (HWR' : mpd_writable L LB (bv_unsigned sp + -32) (heap_top usegs L HI h) dX) by (eapply mpd_writable_sp_mono; [exact HWR| lia]).
    assert (CRI : client_range L LB lo p1 (bv_unsigned Lw)) by (intros a Ha; apply CRBUF; plia).
    replace Lw with (Z_to_bv 64 (Z.of_nat (length ibs))) by (rewrite LENI; apply Z_to_bv_bv_unsigned).
    clearbody ibs.
    pose proof HRB as SP. unfold mpi_read_binary_stmt, U_MPI_READ_BINARY in SP.
    eapply aevtM_cut; [ eapply SP with (dX := dX) (B := p1) (ibs := ibs) (lo := lo) (LB := LB) (h := h);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by plia; rewrite ?LENI; try eassumption; try reflexivity; try plia | ].
    { generalize DX3; plia. }
    { intros HO. generalize (DX4 HO); plia. }
    clear SP.
    intros ms' mo' PO. unfold mpi_read_binary_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by plia. rewrite ?LENI in PO.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & HX2 & HOUT & HPX2 & SOK2 & Hr & Hr0 & HFRESH).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HH2 with HEAP _ _ _ ?hh ?LBB _ _ => rename hh into h2; rename LBB into LB2 end.
    match type of HX2 with mpd_at _ _ _ ?d => rename d into dX2 end.
    match type of Hr with ?rr = 0 \/ _ => rename rr into r end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. clear MK.
    (* [comment removed for export] *)
    assert (IVS : forall a k, (a + k <= md_addr dX \/ md_addr dX + 16 <= a) ->
                   (md_own dX = LHeap -> a + k <= md_p dX \/ md_p dX + 4 * md_n dX <= a) -> disjoint_from (mpd_ivs dX) a k).
    { intros a k H2 H3. unfold mpd_ivs. destruct (md_own dX) eqn:EO; cbn [disjoint_from].
      - split; [exact H2| exact I].
      - split; [exact H2|]. split; [| exact I]. specialize (H3 eq_refl). clear -H3. lia.
      - exfalso. exact (HNS eq_refl). }
    apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2) in FR;
      [| apply client_range_stack; simpl_sizes; lia | simpl_sizes; apply IVS; [generalize DSX; plia| intros HO; generalize (XLB HO); plia] ].
    apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2) in HPP;
      [| simpl_sizes; eapply client_range_wsep; [exact CWPP| intros b Hb; exact Hb| generalize DS1; plia]
       | simpl_sizes; apply IVS; [generalize DX1; plia| exact DX2] ].
    clear ST MI SOK HBUF HIB HXm HH.
    assert (CW2 : client_wrange L LB2 lo (heap_top usegs L HI h2) PP 8).
    { rewrite HT2. eapply client_wrange_mpd_out; [exact CWPP| exact HOUT| exact DX2]. }
    assert (HTOP2 : bv_unsigned sp <= heap_top usegs L HI h2) by (rewrite HT2; exact HTOP).
    pose proof (munch_refl [(PP, PP + 8)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    zstep. zstep. zstep.
    try replace (bv_unsigned Lw + p1) with (p1 + Z.of_nat (length ibs)) in * by lia.
    zstep; if_cases KW; zify_cond KW; [exfalso; plia|].
    zstep. zstep. zstep. zstep; if_cases KN; zify_cond KN; [b2z_close KN|].
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    release_frame FR ST2 (bv_unsigned sp).
    pose proof HOUT as HOUT'. ddestruct HOUT' as (HA2 & HNS2 & _).
    assert (HX9 : mpd_at usegs m9 LB2 dX2).
    { eapply mpd_at_munch; [exact HX2| exact HNS2| exact MU2| exact WM2| |]; cbn [disjoint_from].
      - rewrite HA2. generalize DX1; plia.
      - intros HO. split; [| exact I].
        pose proof (client_apart_new_limbs usegs L HI _ _ _ _ _ _ _ _ _ _ _ _ HH2 HX2 HOUT HFRESH CWPP ltac:(lia) ACL DIM1 DIM2 DX2 HO) as AP.
        clear -AP. lia. }
    apply aevtM_done. unfold asn1_get_mpi_post. deexists 14.
    dexists m9, mo2, h2, LB2, dX2, r, (p1 + Z.of_nat (length ibs)).
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try plia; try (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear -Hr; lia).
    - (* [comment removed for export] *)
      eapply heap_presx_trans; [exact (presx_W mm MU WM)|].
      eapply heap_presx_trans.
      + eapply heap_presx_weaken; [exact HPX2| lia| intros a Ha; exact (proj2 Ha)].
      + eapply heap_presx_of_munch; [exact MU2| exact WM2|]. intros a _ _ [Ho _]. cbn [outside]. split; [exact Ho| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "01n0@D10463954377.96 D10463954377.97 D12223852868.96 D12223852868.97 D20139305660.102D20139305660.107D20139305660.112D27668705378.96 D27668705378.97 D28496781288.102D28496781288.107D28496781288.112D30471956959.102D30471956959.107D30471956959.112D32669241193.100D32669241193.105D32669241193.110D32669241193.94 D32669241193.95 D35754698159.96 D35754698159.97 D35765334355.94 D35765334355.95 D37216054521.100D37216054521.105D37216054521.110D37226362885.102D37226362885.107D37226362885.112D44492853884.102D44492853884.107D44492853884.112D4453582353.102 D4453582353.107 D4453582353.112 D44622288685.96 D44622288685.97 D49698585326.96 D49698585326.97 D49705053714.94 D49705053714.95 D55610685700.96 D55610685700.97 D61556549392.102D61556549392.107D61556549392.112D61571118060.100D61571118060.105D61571118060.110D63898547005.102D63898547005.107D63898547005.112L10097566489.90 L11668900560.87 L12223852868.90 L12223852868.91 L12550711524.97 L12550742471.96 L12552788672.94 L16070426553.105L16070426553.106L16108054177.102L16110144372.93 L16605321107.88 L1803595871.89  L20139305660.101L20139305660.106L20139305660.96 L21515407737.102L21765854580.88 L21887662552.87 L21991360968.89 L21993419083.91 L24148001045.94 L2591683900.109 L27775132660.88 L28350014407.109L30471956959.101L30471956959.106L30471956959.96 L30803094856.98 L33510041944.88 L34290115814.93 L35203203157.102L35347804779.97 L39644505002.109L39675226408.109L41202929119.103L41202929119.88 L41202929119.93 L41202929119.98 L43059266230.91 L50091501498.92 L508980326.100  L53271535775.103L53271535775.93 L53271535775.98 L55610685700.90 L55610685700.91 L63152446533.102L63898547005.101L63898547005.106L63898547005.96 L65515010990.86 L66083662040.88 L785069053.86   L9716869748.87  L9817098198.92  L9817183408.87  R14003500297.109R24782612882.104R30965436485.109R37917973656.109R42808704008.95 R42812894818.109R42814981047.100R43781856510.104R43781856510.109R47832358507.105R49921671781.100R49921682489.105R49923780528.109R52751350366.95 R52753442471.99 R60929927345.99 00000X01C01D01E01F01G01H02902m03H03c04A04B04C04D04Q04^04n05;05H05d06C06P06]06n07?07S08208Q09309409509609Q09l0:J0;C0<?0<_0=B0=S0=d0=e0=f0>E0>d0?F0?W0?h0@<0@=0@>0@?0@T0A@0B40Bk0C>0CQ0Cd0D40DD0D]0E30E_0FA0Fc0GH0Gj0H=0HG0HQ0Hd0I70IY0If0J00JC0K60Kl0L_0L`0Lj0M40M50M?0MO0M^0Mk0N50N?0NI0Nh0OT0Od0P10P;0PE0Q=0R80RH0Rh0SK0Sk0T50T?0T^0Th0UT0V@0VA0VT0Vf0W=0WG0WT0W^0Wl0X=0XJ0X]0Y30YI0Y\0Yo0Z9S1L2HI2ra2sp1h2PP2bs4HTOP2HB5Ha_st5Hl_stS1L2HI2sp2s01h2PP2bs4HTOP2HB5Ha_st5Hl_st2s1FFFFFS1L3HLS2ra2sp2PP2bs2lo3NZ13SLO3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02PP2bs2lo3NZ13SLO3SPB2HB5Ha_st5Hl_st2s1S2sp2PP1P2bs2HB5Ha_st5Hl_stS2sp2PP1P2bs2HB5Ha_st5Hl_stS2sp2PP1P2bs2nn2HB5Ha_st5Hl_stFFFS2sp2PP2bs2HBS2sp2PP2bs2HBS2sp2PP2bs2nn2HBS2sp2PP2bs2HBS2sp2PP2bs2HBS2ra2sp2PP2bs2HB5Ha_st5Hl_stS2sp2s02PP2bs2HB5Ha_st5Hl_st2s1S2sp2PP2bs2HBS2sp2PP2bs2HBS2sp2PP2bs3NZ12HBS2sp2PP2bs3NZ12HBS2sp2PP2bs3NZ12nn2HBS2sp2PP1P2bs3NZ12HB5Ha_st5Hl_stS2sp2PP1P2bs3NZ12HB5Ha_st5Hl_stS2sp2PP1P2bs3NZ12nn2HB5Ha_st5Hl_stFFFS2sp2PP1P2bs2HB5Ha_st5Hl_stS2sp2PP1P2bs2HB5Ha_st5Hl_stS2sp2PP1P2bs2nn2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP2bs2lo3NZ13SLO3ACL3DHI3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02PP2bs2lo3NZ13SLO3ACL3DHI3SPB2HB5Ha_st5Hl_st2s1S2ra2sp2PP2bs3SPB2HB5Ha_st5Hl_stS2sp2s02PP2bs3SPB2HB5Ha_st5Hl_st2s1S2sp2PP2bs3SPB2HBS2sp2PP2bs3SPB2HBFFS2sp2PP1P2bs3PPB2HB5Ha_st5Hl_stS2sp2PP1P2bs3PPB2HB5Ha_st5Hl_stS2sp2PP1P2bs3PPB2nn2HB5Ha_st5Hl_stS2sp2PP2bs3PPB2HBS2sp2PP2bs3PPB2HBS2sp2PP2bs3PPB2nn2HBFFFS1L2sp2PP2bs2dX2H02HCS2sp2PP1P3END3BUF2bs2B12B22B32B43NZ13NZ33SPBS1L3HLS2ra2sp2PP2bs2lo3NZ13SLO2HD3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02PP2bs2lo3NZ13SLO2HD3SPB2HB5Ha_st5Hl_st2s1S2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bsS2sp2PP1P3BUF2bsS2sp2PP1P3END2bs2K02K12nnS2sp2PP1P3END2bs2K02K1S2sp2PP1P3END3BUF2bs2B12B22B32B43NZ13NZ33SPBS2sp2PP1P3END3BUF2bs2B33NZ13SPB2K0S2sp2PP1P3BUF2bs2HD2HB5Ha_st5Hl_stS2sp2PP1P3BUF2bs2HD2nn2HB5Ha_st5Hl_stS2sp2PP1P3BUF2bs2HD2HB5Ha_st5Hl_stS2sp2PP2bs2nn2NR2HNS2sp2PP2bsS2sp2PP2bsS2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bs2B1S2sp2PP1P3END3BUF2bs2B33NZ13SPB2K3S2sp2PP2bs2nnS2sp2PP2bsS2sp2PP2bs2nn2NR2HNS1L3HLS2sp2PP1P2bs2lo3NZ13SLO2HD3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2PP1P2bs2lo3NZ13SLO2HD3SPB2nn2HB5Ha_st5Hl_stS1L3HLS2sp2PP1P2bs2lo3NZ13SLO2HD3SPB2HB5Ha_st5Hl_stFS2sp2PP2bsS2sp2PP2bsFS2sp2PP2bsS2sp2PP2bs2nn2HNS2sp2PP1P2bs2nnS2sp2PP2bs2nnS2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS1L3HLS2sp2PP2bs2lo3NZ13SLO3SPBS2sp2PP1P3END3BUF2bs2B12B32B43NZ13NZ33SPB2K0S2sp2PP1P3BUF2bsS2sp2PP2bs2nnS2sp2PP2bsS2sp2PP2bsS1L3HLS2ra2sp2PP3BUF2bs2lo3NZ13SLO2HD3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02PP3BUF2bs2lo3NZ13SLO2HD3SPB2HB5Ha_st5Hl_st2s1S2sp2PP2bs2nn2NRS1L2sp2PP1P2bs2HD2HB5Ha_st5Hl_stS1L2sp2PP1P2bs2HD2nn2HB5Ha_st5Hl_stS1L2sp2PP1P2bs2HD2HB5Ha_st5Hl_stS2sp2PP2bsS2sp2PP2bsS1L3HLS2sp2PP2bs2lo3NZ13SLO3SPBS2sp2PP2bsS2sp2PP1P3END3BUF2bs2B12B32B43NZ13NZ33SPB2K0S2sp2PP1P3END3BUF2bs2B12B22B32B43NZ13NZ33SPBFS2sp2PP1P3END2bs2K3S2sp2PP1P2bs2nn2HNS2sp2PP1P3END2bs2nn3KgeS2sp2PP2bsS2sp2PP2bs2nnS2sp2PP2bsS2sp2PP2bs3SPBS2sp2PP2bs3SPB2nnS2sp2PP2bs2b1S2sp2PP1P3END2bs2K0S2sp2PP1P3END2bs2K02b1S2sp2PP1P3END2bs2K02nnS2sp2PP1P3END2bs2B2S2sp2PP1P3END2bs2B2S2sp2PP2bs". (* [comment removed for export] *)
Lemma U_asn1_get_mpi_spec : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_mpi ()) "PL,$52.PHI,(56.$5:.R1.)PMSF,$9.P,(26.=(3>.R3.))(5=.$5:.R4.R3.$5>.$5?.R2.)")
(* [comment removed for export] *).
Proof.
  intros L HI MSF HLS HRB. unfold U_ASN1_GET_MPI.
  intros until lo. intros HH HPP HBUF B1 B2 B3 B4 HX HNS HWR D2 DX1 DX2 DX3 DX4 AL1 NZ1 NZ3 ST SLO ACL HTOP SPA DHI DIM1 DIM2 DS1 DS3 OD1
    CWPP CRBUF TP MI SOK CA -> -> ->.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
  assert (DSX : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX).
  { eapply (client_wrange_where' L LB (bv_unsigned sp) _ _ 16 lo); [exact (proj1 HWR)| lia| exact HBR0| exact DHI| exact ACL| lia]. }
  assert (XLB : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= alloc_ceiling /\ 0 < md_p dX).
  { intros HO. destruct HX as [(_ & _ & _ & _ & _ & HOWN) _]. rewrite HO in HOWN. ddestruct HOWN as (_ & HIN & _).
    rewrite Forall_forall in HBR0. destruct (HBR0 _ HIN) as (H0 & _ & _ & HC & _). cbn in H0, HC. lia. }
  pose proof CWPP as CWp.
  pose proof (munch_refl [(PP, PP + 8); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep.
  zstep; if_cases KN0; zify_cond KN0; [exfalso; rewrite ?unsigned_lit in KN0 by plia; plia|].
  zstep. zstep. zstep; if_cases KA0; zify_cond KA0; [al8_close KA0|].
  zstep. zstep. zstep; if_cases K; zify_cond K.
  { (* [comment removed for export] *)
    zstep. zstep. eapply fail_walk; try eassumption; try plia. }
  zstep; if_cases KP0; zify_cond KP0; [exfalso; rewrite ?unsigned_lit in KP0 by plia; plia|].
  get_byte bs (P - BUF) b0 NB0. read_at HBUF NB0 (P - BUF) RD0.
  zstep. clear RD0. zstep. zstep; if_cases Kt; zify_cond Kt.
  { (* [comment removed for export] *) zstep. eapply fail_walk; try eassumption; try plia. }
  zstep. zstep. zstep; if_cases KE0; zify_cond KE0; [exfalso; rewrite ?unsigned_lit in KE0 by plia; plia|].
  zstep. zstep. zstep. zstep. zstep.
  apply (rw_cells_CB8_C8 usegs _ _ []) in FR. cbn [app] in FR.
  lazymatch type of FR with rw_cells _ _ _ (?c :: ?rest) => destruct (proj1 (rw_cells_app usegs m1 (bv_unsigned sp + -32) [c] rest) FR) as [FRL FRR] end.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRR.
  replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FRR by lia.
  pose proof U_asn1_get_len_spec as SPL. unfold asn1_get_len_stmt, U_ASN1_GET_LEN in SPL.
  eapply aevtM_cut_evt; [exact MK| eapply SPL with (PP := PP) (LENP := bv_unsigned sp + -32) (P := P + 1) (END := END) (BUF := BUF) (bs := bs); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by plia; try eassumption; try reflexivity; try plia |].
  clear SPL. intros ms' PO. unfold asn1_get_len_post in PO.
  destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & rl & p2 & Ll & -> & MU2 & WM2 & MI2 & EA0 & HRL & HPP2 & HLEN2 & HP2 & HOK).
  subst ya0.
  replace (ret_pc (Z_to_bv 64 0x1e8ac)) with (Z_to_bv 64 0x1e8ac) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  assert (HH2 : HEAP usegs L HI h LB m2 mo).
  { eapply (HEAP_munch usegs L HI h LB m1 m2 mo lo); [exact HH| exact ACL| exact MU2| exact WM2|].
    intros a Ha NO. cbn [outside] in NO. destruct (Z.leb_spec PP a) as [Ha1|Ha1]; [destruct (Z.ltb_spec a (PP + 8)) as [Ha2|Ha2]; [exact (CWPP a ltac:(lia))|] |]; unfold client_waddr; left; lia. }
  assert (SOK2 : statics_ok usegs L m2).
  { eapply statics_ok_munch; [exact SOK| exact MU2|]. intros a Ha Hn. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (bytes_at_transport usegs _ m1 m2 _ _ HBUF MU2 ltac:(cbn; repeat split; try exact I; lia)) as HBUF2.
  pose proof (rw_cells_transport usegs _ m1 m2 _ _ FRR MU2 WM2 ltac:(cbn; repeat split; try exact I; lia)) as FRR2.
  pose proof (stk_transport_disjoint usegs _ m1 m2 _ _ ST MU2 WM2 ltac:(cbn; repeat split; try exact I; lia)) as ST2.
  assert (MUt : munch [(PP, PP + 8); (bv_unsigned sp - 32, bv_unsigned sp)] m m2) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; intros a Ha; cbn in Ha |- *; lia]).
  assert (WMt : wmono usegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear HH SOK HBUF FRR ST MU WM FRL MI.
  zstep; if_cases KR; zify_cond KR.
  - destruct (Z.eq_dec rl 0) as [E|E]; [subst rl; exfalso; vm_compute in KR; first [exact (KR eq_refl) | discriminate KR | lia] |].
    apply lxp_cell_to_CB in HLEN2. cbn [csize] in HLEN2. joinr HLEN2 FRR2.
    eapply fail_walk; try eassumption; try plia.
  - destruct (Z.eq_dec rl 0) as [E|E]; [| exfalso; clear -KR HRL E; lia].
    subst rl. destruct (HOK eq_refl) as [HOK1 HOK2].
    joinr HLEN2 FRR2.
    eapply j1_walk; try eassumption; try plia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
