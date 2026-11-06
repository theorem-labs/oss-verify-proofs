(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo
     A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_seq_cb A_x509_seq_stmts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_asn1_trav () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.LibA.ARt.presA"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.havol"; "TRAV_PHI"; "OSSVerify.KrLib.LibA.ARt.hfr"; "TRAV_FFR"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.hd"; "OSSVerify.KrLib.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.CrtParseStmts.SSEQ"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Spec.Rep.SEQ_SIZE"; "OSSVerify.KrLib.LibA.ARt.HM"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "TRAV_STK"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.A.A_asn1_seq_cb.A_ASN1_SEQ_CB"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "Stmt.asn1_trav_postA"; "Stmt.seqrep"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.removelast"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "Walk.Call.nLB"; "OSSVerify.KrLib.A.AImg.asegs"; "Walk.Call.nodeF"; "seqrep"; "Walk.Call.curP"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.presW"; "Walk.Call.tinv"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.A.A_asn1_seq_cb.ASN1_SEQ_CB_PHI"; "OSSVerify.KrLib.LibA.ARt.fr_charge"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "asn1_trav_postA"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Stdlib.Lists.List.last"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Walk.Call.LoopOblig"; "Corelib.Init.Peano.le"; "A_ASN1_TRAV"].


Definition A_ASN1_TRAV : Z := 0x099d0c.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TRAV_PHI (n : Z) : Z := (n / 2) * ASN1_SEQ_CB_PHI.
Definition TRAV_FFR (n : Z) : Z := (n / 2) * fr_charge 0.
Definition TRAV_STK (R : art_layout) : Z := 112 + 64 + arl_need_malloc R.

Section Stmt.
  Variable segs : list Segment.
  Variable R : art_layout.
  Variable HIA : artA segs R.
  Let AL := arl_AL R.

  Definition asn1_trav_postA
      (h : HST segs R HIA) (LB LF : list blk)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (PP CTX CUR P END BUF n lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.Vsegs,VR,VHIA,)Lh',(5.Vsegs,VR,VHIA,)(1.$6.Lr,$6.(1.$6.Lp',$6.(1.(2.&40.)Lct,(2.&40.)(1.(2.&40.)Lcpad,(2.&40.)(1.$6.Lcl,$6.(1.$6.Lcp,$6.(1.$6.Lcn,$6.(1.(7.$6.)Lnodes,(7.$6.)(8.(9.$0.R1;.(:.(;.(<.O1<.O1;.O1:.O19.R1:.R19.R18.O18.O17.R17.R16.R15.R14.R13.R12.R11.R10.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R?.R>.R=.R<.)O<.(=.O1<.)O;.(>.(2.&40.))R;.(?.Vsegs,))R:.))(8.(9.(2.&40.)R17.(10.&40.R8.))(8.(8.(11.-3000.R8.)(12.R8.=))(8.(13.Vsegs,R;.)(8.(14.Vsegs,R;.O3.(15.&40.O1;.))(8.(16.O1.R:.)(8.(17.Vsegs,VR,O1>.O1=.(15.&40.O1;.)(18.VR,)(19.Vsegs,VR,VHIA,O1?.)(1:.(1;.$6.$6.)(1<.$6.$6.O:.(1=.O:.+8.))(1:.(1;.$6.$6.)(1<.$6.$6.O8.(1=.O8.+20.))(1:.(1;.$6.$6.)(1<.$6.$6.(1=.O9.+8.)(1=.O9.+10.))(1>.(1;.$6.$6.)))))O2.R;.)(8.(9.$6.(1?.Vsegs,VR,VHIA,R9.)(1?.Vsegs,VR,VHIA,O1?.))(8.(9.$6.(19.Vsegs,VR,VHIA,R9.)(19.Vsegs,VR,VHIA,O1?.))(8.(9.$6.(20.Vsegs,VR,VHIA,R9.)(20.Vsegs,VR,VHIA,O1?.))(8.(21.Vsegs,VR,VHIA,R9.R:.)(8.Px,$6.P,(22.Vsegs,VR,VHIA,O1?.R1.)(22.Vsegs,VR,VHIA,R;.R2.)(8.(12.(23.Vsegs,VR,VHIA,R9.)(1=.(23.Vsegs,VR,VHIA,O1?.)(24.O4.)))(8.(12.(25.Vsegs,VR,VHIA,R9.)(1=.(25.Vsegs,VR,VHIA,O1?.)(26.O4.)))(8.(12.(27.(28.$6.R1.))(29.O4.+2.))(8.(2:.Vsegs,R;.O:.(1:.$2;.(2<.(10.&40.R7.))(1>.$2;.)))(8.(8.(12.O7.R7.)(12.R7.O6.))(8.(2:.Vsegs,R;.O8.(2=.R6.R5.R4.R3.R2.))(8.(2>.(8.(9.$6.R3.=)(8.(9.$6.R4.=)(9.(7.$6.)R1.(1>.$6.))))(8.(12.O5.R3.)(8.(12.=R4.)(12.(1=.R3.R4.)O6.))))(8.(9.$6.R2.(2?.$6.=R1.))(8.(30.Vsegs,L,(7.$2;.)$31.R;.(32.$33.(34.(35.$6.R1.))O1>.)R2.R1.)(8.(36.$6.R1.)(8.Px,$6.P,(37.$6.R1.R2.)PB,$6.Pk,$6.P,(37.(1;.$6.$6.)(1<.$6.$6.R2.R1.)O1>.)(2>.(12.(1=.R5.$38.)R3.)(12.(1=.R3.R2.)R5.))(8.(39.Vsegs,VR,VHIA,R9.(32.$33.(34.(35.$6.R1.))O1>.)O1=.R;.)P,(9.$6.R8.=)(9.$6.R8.O6.)))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition asn1_trav_stmtA (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Ph,(5.Vsegs,VR,VHIA,)PLB,(7.$33.)PLF,(7.$33.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPP,$6.PCTX,$6.PCUR,$6.PP,$6.PEND,$6.PBUF,$6.Plo,$6.Pbs,(7.(2.&8.))Pct,(2.&40.)Pcpad,(2.&40.)P,(39.Vsegs,VR,VHIA,R30.R2?.R2>.R<.)P,(21.Vsegs,VR,VHIA,R31.R<.)P,(2:.Vsegs,R>.R<.(1:.$2;.(2<.(10.&40.R9.))(1>.$2;.)))P,(9.$6.(3;.R=.+8.)=)P,(11.=R>.)P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R35.)R11.R?.+8.)P,(3=.(3>.VR,)(32.$33.R35.(3?.R34.))R:.(1?.Vsegs,VR,VHIA,R36.)R10.+8.)P,(12.(1=.R11.+8.)R;.)P,(40.Vsegs,R14.R=.R;.)P,(37.(1;.$6.$6.)(1<.$6.$6.R>.(27.(28.(2.&8.)R<.)))R38.)P,(12.R?.R11.)P,(12.R12.R11.)P,(12.R12.(1=.R11.(27.(28.(2.&8.)R?.))))P,(11.(1=.R12.(27.(28.(2.&8.)R10.)))(41.+2.+2?.))P,(11.=R13.)P,(2>.(12.(1=.R19.+8.)R14.)(12.(1=.R14.(27.(28.(2.&8.)R12.)))R19.))P,(2:.Vsegs,R1<.R18.(2=.R12.R11.===))P,(9.$6.(3;.R19.+8.)=)P,(11.=R1:.)P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R43.)R1?.R1;.+20.)P,(3=.(3>.VR,)(32.$33.R43.(3?.R42.))R18.(1?.Vsegs,VR,VHIA,R44.)R1<.+20.)P,(12.(1=.R1=.+20.)R19.)P,(2>.(12.(1=.R1>.+20.)R1;.)(12.(1=.R1;.(27.(28.(2.&8.)R19.)))R1>.))P,(2>.(12.(1=.R21.+8.)R1?.)(12.(1=.R1?.+20.)R21.))P,(2:.Vsegs,R24.(1=.R21.+8.)(1:.$2;.(2<.(10.&40.R20.))(1>.$2;.)))P,(9.$6.(3;.(1=.R22.+8.)+8.)=)P,(12.=R23.)P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R4;.)R27.(1=.R24.+8.)+8.)P,(3=.(3>.VR,)(32.$33.R4;.(3?.R4:.))R20.(1?.Vsegs,VR,VHIA,R4<.)(1=.R25.+8.)+8.)P,(12.(1=.R26.+10.)(18.VR,))P,(2>.(12.(1=.R27.+10.)R23.)(12.(1=.R23.(27.(28.(2.&8.)R21.)))(1=.R27.+8.)))P,(2>.(12.(1=.R29.+8.)(1=.R28.+8.))(12.(1=.R28.+10.)R29.))P,(2>.(12.(1=.R29.+10.)R28.)(12.(1=.R28.+20.)(1=.R29.+8.)))P,(14.Vsegs,R2=.R25.(15.&40.R4=.))P,(12.(18.VR,)R26.)P,(12.R27.(42.(15.&40.R4?.)(43.VR,)))P,(12.(15.&40.R50.)(1?.Vsegs,VR,VHIA,R54.))P,(9.$6.(3;.(15.&40.R51.)+10.)=)P,(13.Vsegs,R32.)P,(9.(2.&40.)R51.(10.&40.(44.VR,)))P,(12.(1=.(23.Vsegs,VR,VHIA,R58.)(24.(42.R2>.R2?.)))$45.)P,(12.(1=.(25.Vsegs,VR,VHIA,R59.)(26.(42.R2?.R30.)))$46.)P,(9.(2.&40.)R4>.(10.&40.R34.))P,(9.(2.&40.)R4>.(10.&40.R31.))P,(9.(2.&40.)R4>.(10.&40.+??.))P,(9.(2.&40.)R4=.(10.&40.=))P,(9.(2.&40.)R4=.(10.&40.=))P,(9.(2.&40.)R4=.(10.&40.$47.))P,(9.(2.&40.)R4=.(10.&40.R39.))(48.Vsegs,(49.R61.R60.R5?.R5>.R5=.R5<.R5;.R57.R56.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R3?.R3>.R3;.R3:.R39.R38.R37.R36.(42.R37.R38.)R35.R3=.R3<.)(:.(;.(<.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.)R3?.(10.&40.O1.)R3>.(>.(2.&40.))R3=.(?.Vsegs,))R3<.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition seqrep (m : mem) (Lh : list blk) (BUF END CUR : Z) (nodes : list Z) (cur : Z) : Prop :=
    match nodes with
    | [] => cur = CUR
    | _ :: _ => cur = last nodes 0 /\ In (cur, 32) Lh /\ cur mod 16 = 0 /\ 0 < cur
                /\ (exists (t pd : word) (l p : Z), rw_cells segs m CUR (seq_cells t pd l p (hd 0 nodes)) /\ BUF <= p /\ 0 <= l /\ p + l <= END)
                /\ seq_lseg segs m Lh BUF END (removelast nodes) cur
    end.

  #[using="Type"] Lemma seqrep_mem : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLh,(7.$33.)PLh',(7.$33.)PBUF,$6.PEND,$6.PCUR,$6.Pnodes,(7.$6.)Pcur,$6.P,(4:.R9.R7.R5.R4.R3.R2.R1.)P,Pb,$33.P,(37.$33.R1.R9.)(37.$33.R2.R9.)P,PA,$6.Pcs,(7.$2;.)P,(2>.(8.(9.$6.R2.R7.)(4;.(9.(7.$6.)R6.(1>.$6.))))(37.$6.R2.(4<.$6.R6.)))P,(2:.Vsegs,R>.R3.R2.)P,(9.$4=.(4>.R3.)#20.)(2:.Vsegs,R?.R5.R4.)(4:.R;.R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros m m' Lh Lh' BUF END CUR nodes cur H HL HK. destruct nodes as [|a r]; [exact H|].
    ddestruct H as (E & HI & H16 & H0 & (t & pd & l & p & HC & G1 & G2 & G3) & HS).
    split; [exact E|]. split; [apply HL; exact HI|]. split; [exact H16|]. split; [exact H0|]. split.
    - dexists t, pd, l, p. split; [apply HK; [left; split; [reflexivity| discriminate]| exact HC| reflexivity]| repeat split; assumption].
    - eapply seq_lseg_mem; [exact HS| intros x Hx; apply HL; eapply seq_lseg_in; [exact HS| exact Hx]|].
      intros x cs Hx HR Hsz. apply HK; [right; exact Hx| exact HR| exact Hsz].
  Qed.

  #[using="Type"] Lemma rl_last_app : forall (l : list Z) d, l <> [] -> removelast l ++ [last l d] = l.
  Proof. intros l d H. symmetry. apply app_removelast_last. exact H. Qed.
  #[using="Type"] Lemma last_in : forall (nodes : list Z), nodes <> [] -> In (last nodes 0) nodes.
  Proof. intros nodes Hne. rewrite <- (rl_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. Qed.
  #[using="Type"] Lemma in_rl : forall (l : list Z) x, In x (removelast l) -> In x l.
  Proof. intros l x H. destruct l as [|a r]; [exact H|]. rewrite <- (rl_last_app (a :: r) 0) by congruence. apply in_or_app. left. exact H. Qed.
  #[using="Type"] Lemma hd_app_ne : forall (l : list Z) x d, l <> [] -> hd d (l ++ [x]) = hd d l.
  Proof. intros [|a r] x d H; [exfalso; exact (H eq_refl)| reflexivity]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma seqrep_snoc : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pm,P,(2.&40.)(3.(2.&8.))PLh,(7.$33.)PBUF,$6.PEND,$6.PCUR,$6.Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.PN,$6.P,(4:.R<.R;.R:.R9.R8.R7.R6.)P,(2:.Vsegs,R=.R7.(2=.R6.R5.R4.R3.R2.))P,(12.R<.R4.)P,(12.=R6.)P,(12.(1=.R6.R7.)R=.)P,(37.(1;.$6.$6.)(1<.$6.$6.R6.+20.)R10.)P,(9.$6.(3;.R7.+10.)=)P,(11.=R8.)(4:.R14.R13.R12.R11.R10.(32.$6.R?.(1:.$6.R9.(1>.$6.)))R9.)")
(* [comment removed for export] *).
  Proof.
    intros m Lh BUF END CUR nodes cur ct cpad cl cp N H HR G1 G2 G3 HN N16 N0.
    destruct nodes as [|a r].
    - cbn in H. subst cur. cbn [app seqrep last hd removelast seq_lseg].
      split; [reflexivity|]. split; [exact HN|]. split; [exact N16|]. split; [exact N0|]. split; [| exact I].
      dexists ct, cpad, cl, cp. split; [exact HR| repeat split; assumption].
    - ddestruct H as (E & HI & H16 & H0 & (t & pd & l & p & HC & K1 & K2 & K3) & HS).
      assert (Hne : a :: r <> []) by discriminate.
      change (seqrep m Lh BUF END CUR ((a :: r) ++ [N]) N) with
        (N = last ((a :: r) ++ [N]) 0 /\ In (N, 32) Lh /\ N mod 16 = 0 /\ 0 < N
         /\ (exists (t pd : word) (l p : Z), rw_cells segs m CUR (seq_cells t pd l p (hd 0 ((a :: r) ++ [N]))) /\ BUF <= p /\ 0 <= l /\ p + l <= END)
         /\ seq_lseg segs m Lh BUF END (removelast ((a :: r) ++ [N])) N).
      rewrite last_last, removelast_last, (hd_app_ne (a :: r) N 0 Hne).
      split; [reflexivity|]. split; [exact HN|]. split; [exact N16|]. split; [exact N0|]. split.
      + dexists t, pd, l, p. split; [exact HC| repeat split; assumption].
      + rewrite <- (rl_last_app (a :: r) 0) by exact Hne. apply seq_lseg_app. rewrite <- E. split; [exact HS|].
        cbn [seq_lseg hd]. split; [exact HI|]. split; [exact H16|]. split; [exact H0|]. split; [| exact I].
        dexists ct, cpad, cl, cp. split; [exact HR| repeat split; assumption].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma seqrep_close : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pm,P,(2.&40.)(3.(2.&8.))PLh,(7.$33.)PBUF,$6.PEND,$6.PCUR,$6.Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.P,(4:.R;.R:.R9.R8.R7.R6.R5.)P,(2:.Vsegs,R<.R6.(2=.R5.R4.R3.R2.=))P,(2>.(8.(9.$6.R3.=)(8.(9.$6.R4.=)(9.(7.$6.)R8.(1>.$6.))))(8.(12.R;.R3.)(8.(12.=R4.)(12.(1=.R3.R4.)R:.))))(1.(2.&40.)Lt,(2.&40.)(1.(2.&40.)Lpd,(2.&40.)(1.$6.Ll,$6.(1.$6.Lp,$6.(8.(2:.Vsegs,R12.R>.(2=.R4.R3.R2.R1.(2?.$6.=R=.)))(8.(2>.(8.(9.$6.R1.=)(8.(9.$6.R2.=)(9.(7.$6.)R=.(1>.$6.))))(8.(12.R10.R1.)(8.(12.=R2.)(12.(1=.R1.R2.)R?.))))(30.Vsegs,L,(7.$2;.)$31.R12.R11.(2?.$6.=R=.)R=.)))))))")
(* [comment removed for export] *).
  Proof.
    intros m Lh BUF END CUR nodes cur ct cpad cl cp H HR HB. destruct nodes as [|a r].
    - cbn in H. subst cur. dexists ct, cpad, cl, cp. split; [exact HR|]. split; [exact HB| reflexivity].
    - ddestruct H as (E & HI & H16 & H0 & (t & pd & l & p & HC & K1 & K2 & K3) & HS).
      assert (Hne : a :: r <> []) by discriminate.
      destruct HB as [(_ & _ & X)|HB]; [discriminate X|].
      dexists t, pd, l, p. split; [exact HC|]. split; [right; repeat split; assumption|].
      apply (seq_lseg_chain segs m Lh BUF END). rewrite <- (rl_last_app (a :: r) 0) by exact Hne. apply seq_lseg_app. rewrite <- E.
      split; [exact HS|]. cbn [seq_lseg hd]. split; [exact HI|]. split; [exact H16|]. split; [exact H0|]. split; [| exact I].
      dexists ct, cpad, cl, cp. split; [exact HR| exact HB].
  Qed.
End Stmt.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.
  Hypothesis CBSPEC : asn1_seq_cb_stmtA asegs R HIA A_ASN1_SEQ_CB.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CTX CUR P END BUF lo : Z) (bs : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis ALX : (CTX + 8) mod 8 = 0.
  Hypothesis CTX0 : 0 <= CTX.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (CTX + 8) 8.
  Hypothesis CTXLO : CTX + 16 <= arl_stklo R.
  Hypothesis DXB : CTX + 16 <= BUF \/ BUF + n <= CTX + 8.
  Hypothesis DXP : PP + 8 <= CTX + 8 \/ CTX + 16 <= PP.
  Hypothesis DXC : CTX + 16 <= CUR \/ CUR + 32 <= CTX + 8.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - TRAV_STK R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Local Notation X := [(PP, PP + 8); (CUR, CUR + 32); (CTX + 8, CTX + 16)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation SPT := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Local Notation POST := (asn1_trav_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CTX CUR P END BUF (END - P) lo m mo0).
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Definition nLB (nodes : list Z) : list blk := SSEQ (rev nodes) ++ LB.
  #[using="Type"] Lemma nLB_sub : forall nodes b, In b LB -> In b (nLB nodes).
  Proof. intros nodes b Hb. apply in_or_app. right. exact Hb. Qed.
  #[using="Type"] Lemma nLB_in : forall nodes x, In x nodes -> In (x, 32) (nLB nodes).
  Proof. intros nodes x Hx. apply in_or_app. left. unfold SSEQ. apply (in_map (fun a => (a, SEQ_SIZE))). apply -> in_rev. exact Hx. Qed.
  #[using="Type"] Lemma nLB_snoc : forall nodes N, nLB (nodes ++ [N]) = (N, 32) :: nLB nodes.
  Proof. intros nodes N. unfold nLB, SSEQ. rewrite rev_app_distr. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition nodeF (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "(8.(11.=O1.)(8.(9.$6.(3;.O1.+10.)=)(8.(12.(1=.O1.+20.)Vlo,)(8.(2>.(12.(1=.VPP,+8.)O1.)(12.(1=.O1.+20.)VPP,))(8.(2>.(12.(1=.VCTX,+10.)O1.)(12.(1=.O1.+20.)(1=.VCTX,+8.)))(8.(2>.(12.(1=.VCUR,+20.)O1.)(12.(1=.O1.+20.)VCUR,))(8.PB,$6.Pk,$6.P,(37.(1;.$6.$6.)(1<.$6.$6.R2.R1.)VLB,)(2>.(12.(1=.O1.$38.)R3.)(12.(1=.R3.R2.)O1.))(4?.VR,VLB,VLF,O1.+20.))))))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L15756354262.4L20299287777.3L38692635477.0L39332637397.0L42258334380.3L52443941380.3L57807720085.500000>00G00H00I00R00Z00hS1R2lo3LOS3ALOS3CTX1x1KSSS3CUR1x1KS2PP1x1KS1R2lo1x2F12CE". (* [comment removed for export] *)
  #[using="HIA h CWP CWC CWX LOS"] Lemma nodeF_of_fresh : forall x, x mod 16 = 0 -> fresh_apart R LB LF x 32 -> nodeF x.
  Proof.
    intros x H16 FR. dpose FR as (F0 & F1 & F2 & F3). pose proof (art_lo asegs R HIA) as ALO.
    assert (CE : alloc_ceiling <= lo) by (clear - ALO LOS; lia).
    unfold nodeF. spine; try assumption.
    - clear - F1 CE. lia.
    - destruct (fresh_apart_client R LB LF lo PP 8 x 32 FR (client_range_of_w L _ _ _ _ _ CWP) ltac:(clear; lia) ltac:(clear; lia) CE) as [K|K]; clear - K; lia.
    - destruct (fresh_apart_client R LB LF lo (CTX + 8) 8 x 32 FR (client_range_of_w L _ _ _ _ _ CWX) ltac:(clear; lia) ltac:(clear; lia) CE) as [K|K]; clear - K; lia.
    - destruct (fresh_apart_client R LB LF lo CUR 32 x 32 FR (client_range_of_w L _ _ _ _ _ CWC) ltac:(clear; lia) ltac:(clear; lia) CE) as [K|K]; clear - K; lia.
    - intros B k Hb. unfold SEQ_SIZE. apply F3. apply in_or_app. left. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition curP (nodes : list Z) (cur : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "(8.(11.=O1.)(8.(9.$6.(3;.O1.+8.)=)(8.(12.(1=.O1.+20.)Vlo,)(8.(2>.(12.(1=.VPP,+8.)O1.)(12.(1=.O1.+20.)VPP,))(8.(2>.(12.(1=.VCTX,+10.)O1.)(12.(1=.O1.+20.)(1=.VCTX,+8.)))(8.(2>.(12.(1=.O1.+20.)VBUF,)(12.(1=.VBUF,(27.(28.(2.&8.)Vbs,)))O1.))(8.(3=.(3>.VR,)(32.$33.(50.O2.)(3?.VLF,))Vlo,(1?.$51.VR,VHIA,Vh,)O1.+20.)(2>.(9.$6.O1.VCUR,)(37.$6.O1.O2.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L38383890888.1 L44052539574.1 L64638104799.4 L66151427842.1600000500:00J00eS3curS3curS3BUF2bs3cur3NLBS3cur2r03N161q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="BIN ALC CUR0 CWC CURLO DCB D1 DXC"] Lemma curP_of : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pm',P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.P,Px,$6.P,(37.$6.R1.R3.)(52.R2.)P,(53.$51.R4.(50.R3.)VBUF,VEND,VCUR,R3.R2.)(54.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m' nodes cur HF HS. destruct nodes as [|a r].
    - cbn in HS. subst cur. unfold curP. spine; first [assumption | left; reflexivity].
    - ddestruct HS as (E & HI & H16 & H0 & _).
      assert (Hne : a :: r <> []) by discriminate.
      pose proof (last_in (a :: r) Hne) as HIN. rewrite <- E in HIN.
      ddestruct (HF cur HIN) as (N0 & N16 & NLO & NPP & NCTX & NCUR & NLB & _).
      unfold curP. spine; try assumption.
      + clear - N16. Z.div_mod_to_equations. lia.
      + specialize (NLB _ _ BIN). unfold SEQ_SIZE in NLB. clear - NLB. lia.
      + eapply client_wrange_block; [apply in_or_app; left; exact HI| clear; lia| clear; lia].
      + right. exact HIN.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition tinv (mm : mem) (hc : HST asegs R HIA) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "(8.(39.$51.VR,VHIA,O8.(50.O7.)VLF,O9.)(8.Px,$6.P,(22.$51.VR,VHIA,Vh,R1.)(22.$51.VR,VHIA,O8.R2.)(8.(9.$6.(1?.$51.VR,VHIA,O8.)(1?.$51.VR,VHIA,Vh,))(8.(9.$6.(19.$51.VR,VHIA,O8.)(19.$51.VR,VHIA,Vh,))(8.(9.$6.(20.$51.VR,VHIA,O8.)(20.$51.VR,VHIA,Vh,))(8.(36.$6.O7.)(8.Px,$6.P,(37.$6.R1.O7.)(52.R2.)(8.(53.$51.O9.(50.O7.)VBUF,VEND,VCUR,O7.O6.)(8.(2:.$51.O9.O6.(2=.O5.O4.O3.O2.=))(8.(2>.(8.(9.$6.O2.=)(8.(9.$6.O3.=)(9.(7.$6.)O7.(1>.$6.))))(8.(12.VBUF,O2.)(8.(12.=O3.)(12.(1=.O2.O3.)VEND,))))(8.(2:.$51.O9.(1=.VCTX,+8.)(1:.$2;.(2<.(10.&40.O6.))(1>.$2;.)))(8.(2:.$51.O9.(1=.(15.&40.Vsp,)-70.)(1:.$2;.(55.#8.O1.)(1:.$2;.(2<.Vs11,)(1:.$2;.(2<.Vs10,)(1:.$2;.(2<.Vs9,)(1:.$2;.(2<.Vs8,)(1:.$2;.(2<.Vs7,)(1:.$2;.(2<.Vs6,)(1:.$2;.(2<.Vs5,)(1:.$2;.(2<.Vs4,)(1:.$2;.(2<.Vs3,)(1:.$2;.(2<.Vs2,)(1:.$2;.(2<.Vs1,)(1:.$2;.(2<.Vs0,)(1:.$2;.(2<.Vra,)(1>.$2;.))))))))))))))))(8.(14.$51.O9.Vlo,(1=.(15.&40.Vsp,)-70.))(8.(13.$51.O9.)(8.(40.$51.O9.VBUF,Vbs,)(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.VPP,+8.)(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.VBUF,(27.(28.(2.&8.)Vbs,)))(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.(1=.VCTX,+8.)+8.)(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.VCUR,+20.)(57.$51.VR,VHIA,O8.VLB,VLF,(15.&40.Vsp,)(18.VR,)(1:.(1;.$6.$6.)(1<.$6.$6.VPP,(1=.VPP,+8.))(1:.(1;.$6.$6.)(1<.$6.$6.VCUR,(1=.VCUR,+20.))(1:.(1;.$6.$6.)(1<.$6.$6.(1=.VCTX,+8.)(1=.VCTX,+10.))(1>.(1;.$6.$6.)))))Vm,O9.))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac rt_facts hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold TRAV_STK in SLO;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo0) as KINV.

  (* [comment removed for export] *)
  Ltac open_inv INV hc :=
    destruct INV as (HHc & HCSc & HTc & HSc & HFc & HND & HNF & HSR & HCURC & HCB & HCTX & FRM & STK & MI & HBUF & OPP & OBUF & OCTX & OCUR & PRES);
    pose proof (curP_of _ _ _ HNF HSR) as (C0 & C8 & CLO & CPPa & CCTX & CBUFa & CWcur & CIN);
    rt_facts hc;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOPc; rewrite HTc, HSc in HTOPc;
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo))
      by (eapply crange_mono; [exact HCSc| eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SLO NEED0 TOP HTOPc; lia]]);
    assert (WCP : wcover R LB LF (bv_unsigned sp) X PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    lazymatch type of HSR with seqrep _ _ (nLB ?nds) _ _ _ _ _ =>
      assert (CWPn : client_wrange L (nLB nds ++ fdata LF) lo (htop asegs R HIA hc) PP 8)
        by (rewrite HTc; eapply client_wrange_mono; [exact CWP| intros b' Hb'; apply in_app_iff in Hb'; apply in_app_iff; destruct Hb' as [Hb'|Hb']; [left; apply nLB_sub; exact Hb'| right; exact Hb']]) end;
    unfold seq_cells in HCURC.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@L11093748225.153L13098889560.144L18868739288.144L2138888664.144 L21541644120.144L24626469156.9  L24628566308.9  L27111942217.1  L28359040934.6  L29834048600.144L3043381336.144 L35609665496.144L35655538583.9  L38282648152.144L45674082520.144L48479123582.154L52361663192.144L54106875608.144L55013023064.144L60098763854.3  L62417105880.144Q15647600541.154Q18361649565.154Q18382898686.154Q21892278270.154Q24385319550.154Q27597577117.154Q27911476350.154Q29501203869.154Q30402535678.154Q31258893597.154Q32659612829.154Q33914012414.154Q36438515070.154Q3834572414.154 Q39935311742.154Q41139760797.154Q44652956445.154Q4546183325.154 Q51223295517.154Q52105414429.154Q54481540862.154Q59244229149.154Q59830472733.154Q60498756478.154Q66534732286.154Q9839090942.154 00000R01401V02802Z03703S03W03n04P05205T05m06O07108:08\09>09`09j0:L0:b0;80;]0<B0<g0==0=b0>80>]0?30?I0?n0@S0A80A]0B30BI0B_0C50CK0D00DF0D\0EA0Ef0FKS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R3HIA1h1P3END2hc1e2HE5BUDFaS1R3HIA1h1P3END2hc1e2HE4BUDaS2PPS1P3END5nodes1e2HE4HLENS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R3HIA1h2sp2lo3TOP5HTOPcS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R5NEED02sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03SLO5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R2lo3LOSS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodes". (* [comment removed for export] *)
  #[using="IMG NEED0 PP0 CWP BIN B2 ALC CUR0 CWC CURLO DCB D1 CTX0 DXC LOS SLO TOP"] Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pe,$6.Pr,$6.Pp',$6.Px1,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(58.R26.R27.R25.R24.R23.R22.R21.R20.R1?.)P,(2:.$51.R27.VPP,(1:.$2;.(2<.(10.&40.R1=.))(1>.$2;.)))P,(8.(12.VP,R1>.)(12.R1>.VEND,))P,(8.(11.-3000.R20.)(12.R20.=))P,P,(9.$6.R21.=)(9.$6.R21.VEND,)P,(8.(12.=R23.)(12.R23.(29.(42.VEND,VP,)+2.)))P,(12.(23.$51.VR,VHIA,R2=.)(1=.(23.$51.VR,VHIA,Vh,)(59.R24.$5:.)))P,(12.(25.$51.VR,VHIA,R2>.)(1=.(25.$51.VR,VHIA,Vh,)(59.R25.(5;.=))))P,(12.(27.(28.$6.R2=.))R26.)(5<.$51.(5=.$51.VR,VHIA,R30.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R24.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,(10.&40.R26.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(10.&40.+9:04<.)Vfc,(>.(2.&40.))R2?.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HPP Hp' RR HEND HE BUDa BUDFa HLEN.
    open_inv INV hc.
    do 16 zstep.
    release_frame FRM STK (bv_unsigned sp).
    idtac "EXIT-DONE".
    lazymatch goal with H : rw_cells _ ?mxc cur _ |- _ => change (rw_cells asegs mxc cur (seq_cells ct cpad cl cp 0)) in H end.
    destruct (seqrep_close asegs _ _ _ _ _ _ _ _ _ _ _ HSR HCURC HCB) as (t & pd & l & p & HHEAD & HCB' & HCH).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold asn1_trav_postA.
    deexists 15. dexists mm, mo9, hc, r, p', t, pd, l, p, (hd 0 nodes), nodes.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI|]. split; [exact STK|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES) as HPF; rewrite HSc in HPF; exact HPF|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
    split; [unfold TRAV_PHI; unfold ASN1_SEQ_CB_PHI, AVOL_CALL in *; clear - BUDa HE; lia|].
    split; [unfold TRAV_FFR; unfold fr_charge in *; clear - BUDFa HE; lia|].
    split; [clear - HLEN HE; lia|].
    split; [exact HPP|]. split; [exact Hp'|]. split; [exact HHEAD|]. split; [exact HCB'|]. split; [reflexivity|].
    split; [exact HCH|]. split; [exact HND|].
    split; [intros x Hx; ddestruct (HNF x Hx) as (_ & _ & _ & _ & _ & _ & NLBx & _); exact NLBx|].
    split; [exact HHc|]. exact HEND.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L32049390996.3L55806865597.300000;00ES2PP3CUR2D1S2PP1A3NPP". (* [comment removed for export] *)
  #[using="D1"] Lemma seqrep_pp : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pmm',P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.P,(53.$51.R4.(50.R2.)VBUF,VEND,VCUR,R2.R1.)P,Px,$6.P,(37.$6.R1.R4.)(52.R2.)P,(5?.(1:.(1;.$6.$6.)(1<.$6.$6.VPP,(1=.VPP,+8.))(1>.(1;.$6.$6.)))R6.R5.)P,(60.$51.R7.R6.)(53.$51.R7.(50.R6.)VBUF,VEND,VCUR,R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros mm mm' nodes cur HS HF MU WM. eapply seqrep_mem; [exact HS| intros b Hb; exact Hb|].
    intros A cs HA HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz. cbn [disjoint_from]. split; [| exact I].
    destruct HA as [[-> _]|HA]; [clear - D1; lia|].
    destruct (HF A (in_rl _ _ HA)) as (_ & _ & _ & NPP & _). clear - NPP. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma others_apart : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmq,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Py,$6.P,(39.$51.VR,VHIA,R4.(50.R2.)VLF,R3.)P,(36.$6.R3.)P,(4;.(9.(7.$6.)R4.(1>.$6.)))P,(37.$6.R4.(4<.$6.R5.))(2>.(12.(1=.R5.+20.)(61.$6.R6.=))(12.(1=.(61.$6.R6.=)+20.)R5.))")
(* [comment removed for export] *).
  Proof.
    intros hc mq nodes y HH HND Hne Hy.
    pose proof (in_rl _ _ Hy) as HyN.
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [_ HAP].
    assert (NE : y <> last nodes 0).
    { intros E. rewrite <- (rl_last_app nodes 0) in HND by exact Hne.
      apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
    eapply (blocks_apart_in2 _ y 32 (last nodes 0) 32); [exact HAP| apply in_or_app; left; apply nLB_in; exact HyN| apply in_or_app; left; apply nLB_in; apply last_in; exact Hne| exact NE].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0@L10837002389.2  L11865810590.5  L12638084075.5  L12654381620.1  L13062538913.0  L17860490787.7  L19002552252.25 L22706556809.5  L23327695577.7  L23615739305.3  L26061550921.25 L2676165540.3   L27111942217.1  L27356735122.8  L33306264495.25 L35655538583.9  L3582028444.1   L36471176264.6  L37323683604.9  L37714553091.1  L38383890888.1  L39280637297.0  L41448345567.11 L42268239257.8  L43876917036.5  L44052539574.1  L4449834141.10  L4462386950.5   L48065260594.2  L48476763649.5  L51828132648.8  L52840045532.7  L55628717916.1  L56454306668.25 L57628700040.4  L57628700040.5  L59314923118.2  L60044334350.3  L60098763854.3  L6133078798.8   L61564981147.11 L62018535662.1  L62658486538.3  L63103657906.165L64700576064.13 L66151427842.16 L6746078414.6   L7036479304.1   00000800L00b00g00h01<01S01d02002:02V02c02g03C03\04504904P05305605;05<05_06=06R06W07:07M07T07g08M08h08k09^09l0:=0:B0:O0:Y0;30;T0;W0;d0<O0=50=O0=i0=mS3BUF2bsS1R3CTX2lo5CTXLO3LOSS3CTX3CUR3DXC3cur4NCURS3BUFSS1R3CTX2lo5CTXLO3LOSS2bs4tagb4lenw4Htag3lenS2PP3CTX3CUR1x2HxS2lo3cur3CLOS1R3HIA2hcS1R3HIA1h2sp2bs3TOP4lenw3lenS5nodes1e3HLNS2PPS1R3HIA1h2hc1e5BUDFa2h'4HFR'S1R2sp2lo2bs3SLO4lenw3lenS1R3HIA1h2sp2lo3TOP5HTOPcS2spS1R5NEED02sp2lo3LOS3SLOS1R5NEED02sp2lo3LOS3SLO3ALO3ACV3SPRS1AS3curSS1R3HIA1h1P3END2hc1e3HE15BUDFa4BUDFS3END3BUF2B55nodes2cl2cp1K3CP0S2PP3CTX3DXP3cur4CPPaS3curS1R3CTX2lo5CTXLO3LOS3cur3CLO1A1k2HAS3CTX3cur1A2OA4NCTXS1e3HLNS1R5NEED02sp2lo3SLOS3END3BUF5start4lenw4HST03len3HSE4HLENS1R5NEED02sp2lo3LOS3SLO3ALOS1AS3END3BUF2bs2B33B472B55start4lenw4HST03len3HSE4HLENS3CTX3cur1x2HxS2PP3CTX3CUR1x2HxS1N1KS5nodes1e3HLNS1R2lo3LOSS1R3HIA1h2hc1e4BUDa2h'3HV'S1R3HIA1h1P3END2hc1e3HE14BUDa3BUDS1RS1R3CTX5CTXLOS2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lenw3lenS3END3BUF2bs2B33B472B55nodes2cl2cp3HCBS2sp2r03SPA1q1r1H2H02q02H4S3CTX3BUF2bs3DXB3cur5CBUFaS2sp". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC CWP PPLO BIN B3 B47 B5 ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV"] Lemma cb_step : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pp,$6.Ptagb,$6.Pstart,$6.Pe,$6.Plenw,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)PS0,(2.&40.)PS1,(2.&40.)PS2,(2.&40.)PS3,(2.&40.)PS4,(2.&40.)PS5,(2.&40.)PS6,(2.&40.)PS7,(2.&40.)PS8,(2.&40.)PS9,(2.&40.)PS10,(2.&40.)PS11,(2.&40.)P,(58.R24.R25.R23.R22.R21.R20.R1?.R1>.R1=.)P,(2:.$51.R25.VPP,(1:.$2;.(2<.(10.&40.R1=.))(1>.$2;.)))P,(8.(12.=R1=.)(11.R1=.+100.))P,(12.VBUF,R1=.)P,(12.(1=.R1>.(15.&40.R1<.))VEND,)P,(12.=R1>.)P,(12.(1=.R1?.+1.)(29.(42.VEND,VP,)+2.))P,(12.(23.$51.VR,VHIA,R2<.)(1=.(23.$51.VR,VHIA,Vh,)(59.R20.$5:.)))P,(12.(25.$51.VR,VHIA,R2=.)(1=.(25.$51.VR,VHIA,Vh,)(59.R21.(5;.=))))P,(12.(27.(28.$6.R2<.))R22.)P,(12.(1=.(23.$51.VR,VHIA,Vh,)(24.(42.VEND,VP,)))$45.)P,(12.(1=.(25.$51.VR,VHIA,Vh,)(26.(42.VEND,VP,)))$46.)P,Phc',(5.$51.VR,VHIA,)Pmm',P,(2.&40.)(3.(2.&8.))Pnodes',(7.$6.)Pcur',$6.Pct',(2.&40.)Pcpad',(2.&40.)Pcl',$6.Pcp',$6.Pr,$6.Py5,(2.&40.)Py6,(2.&40.)Py7,(2.&40.)Py11,(2.&40.)Py12,(2.&40.)Py13,(2.&40.)Py14,(2.&40.)Py15,(2.&40.)Py16,(2.&40.)Py17,(2.&40.)Py28,(2.&40.)Py29,(2.&40.)Py30,(2.&40.)Py31,(2.&40.)P,(2>.(9.$6.R?.=)(9.$6.R?.-6:.))P,(58.R17.R18.R16.R15.R14.R13.R12.R11.R41.)P,(2:.$51.R18.VPP,(1:.$2;.(2<.(10.&40.R41.))(1>.$2;.)))P,(12.(23.$51.VR,VHIA,R1:.)(1=.(23.$51.VR,VHIA,Vh,)(59.(1=.R3?.+1.)$5:.)))P,(12.(25.$51.VR,VHIA,R1;.)(1=.(25.$51.VR,VHIA,Vh,)(59.(1=.R40.+1.)(5;.=))))P,(12.(27.(28.$6.R1:.))(1=.R41.+1.))(5<.$51.(5=.$51.VR,VHIA,R1=.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.(10.&40.+99?60.)(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,R14.R13.R12.R35.R34.(10.&40.R15.)R11.R10.R?.R>.R=.R<.R;.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R:.R9.R8.R7.)VF,(10.&40.+99?60.)Vfc,(>.(2.&40.))R1<.(?.$51.)))(5<.$51.(5=.$51.VR,VHIA,R32.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R24.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,R23.R22.R21.R19.R18.(10.&40.VCTX,)(10.&40.R28.)(10.&40.R27.)R25.R20.R1?.(10.&40.$47.)R1>.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R1=.R1<.R1;.R1:.)VF,(10.&40.+99?5<.)Vfc,(>.(2.&40.))R31.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    intros until S11. intros INV HPP Htag HST0 HSE HE0 HE1 BUDa BUDFa HLN BUD BUDF KONT.
    pose proof (bv_unsigned_in_range 64 lenw) as HLEN. unfold bv_modulus in HLEN. cbn [Z.pow Z.of_N Pos.pow] in HLEN. set (len := bv_unsigned lenw) in *.
    pose proof INV as INV0.
    open_inv INV hc.
    assert (SPTR : 0 <= bv_unsigned sp + -112 < 2^64) by (clear - SPR SLO LOS ALO ACV NEED0; lia).
    assert (CPR : 0 <= cp < 2^64) by (clear - HCB B1 B2 B3 B47 B5; lia).
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (nLB nodes ++ fdata LF)).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply nLB_sub; exact Hb| right; exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (nLB nodes ++ fdata LF) (bv_unsigned sp + -112) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    assert (OCN : aobj asegs AL (hcs asegs R HIA hc) mm cur 32).
    { destruct CIN as [->|CIN]; [exact OCUR|]. exact (hm_aobj_block asegs R HIA hc _ _ mm cur 32 HHc (nLB_in _ _ CIN)). }
    unfold A_ASN1_SEQ_CB.
    (* [comment removed for export] *)
    zstep.
    idtac "CB-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      pose proof CBSPEC as SPC. unfold asn1_seq_cb_stmtA, A_ASN1_SEQ_CB in SPC.
      eapply SPC with (h := hc) (LB := nLB nodes) (LF := LF) (CTX := CTX) (CURN := cur) (TAG := tagb) (START := start) (LEN := len) (lo := lo)
                      (ct := ct) (cpad := cpad) (cl := cl) (cp := cp) (cn := 0) (d := 0);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by exact SPTR; rewrite ?HTc, ?HSc;
        first [ exact HHc | exact HK1 | exact HCTX | exact HCURC | exact ALX | exact C8 | exact CTX0 | exact C0 | exact CCTX | exact CPR | exact STK | exact LOS | exact MI | exact TPV
              | exact OCTX | exact OCN | exact CWcur | exact HLEN | reflexivity | (symmetry; apply Z_to_bv_bv_unsigned)
              | lazymatch goal with
                | |- client_wrange _ _ _ _ (CTX + 8) 8 => eapply client_wrange_mono; [exact CWX| exact SUBq]
                | |- uwc _ _ _ _ _ _ _ => apply uwc_data; [clear; lia| clear - CTXLO; lia]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold TRAV_PHI in BUD; unfold ASN1_SEQ_CB_PHI, AVOL_CALL in *; clear - BUD BUDa HE0 HE1; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold TRAV_FFR in BUDF; unfold fr_charge in *; clear - BUDF BUDFa HE0 HE1; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- _ \/ _ => left; clear - CTXLO LOS CLO; lia
                | |- _ => clear - Htag HST0 HLEN HSE B1 B2 B3 B47 B5 SLO NEED0 TOP; lia
                end
              | match goal with |- ?g => idtac "CB-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    idtac "CB-POST".
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m' & mo' & h' & r
                    & E4 & MI' & ST' & MF' & WM' & HPc & HT' & HS' & HF' & HK' & HCS' & HV' & HFR' & CASES).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0x99f60)) with (Z_to_bv 64 0x99f60 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST', HPc by exact SPTR.
    assert (HCSh' : forall x, CS x -> hcs asegs R HIA h' x) by (intros x Hx; apply HCS'; apply HCSc; exact Hx).
    assert (TOPCS : forall x, hcs asegs R HIA hc x -> x < hstkhi asegs R HIA hc) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (DJS : forall A k, lo <= A -> disjoint_from [(CTX + 8, CTX + 16); (cur, cur + 32)] A k).
    { intros A k HA. cbn [disjoint_from]. clear - HA CTXLO LOS CLO. lia. }
    (* [comment removed for export] *)
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mm m' _ _ HPc) in FRM;
      [| apply client_range_stack; clear; lia| apply DJS; clear - SLO NEED0; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mm m' _ _ HPc) in HPP;
      [| cbn [cells_size csize Nat.add]; apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]
       | cbn [disjoint_from cells_size csize Nat.add]; clear - DXP CPPa; lia].
    assert (HBUF' : bytes_at asegs m' BUF bs).
    { eapply (presA_bytes_at asegs R); [exact HPc| exact HBUF| eapply client_range_block; [apply in_app_iff; left; apply nLB_sub; exact BIN| clear; lia| clear; lia]|].
      cbn [disjoint_from]. clear - DXB CBUFa. lia. }
    assert (OPP' : aobj asegs AL (hcs asegs R HIA h') m' PP 8).
    { eapply aobj_cs_mono; [exact HCS'|]. eapply (presA_aobj asegs R); [exact CSOK| exact HPc| exact OPP| apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear - LOS SLO NEED0; lia| exact TOPCS]. }
    assert (OCTX' : aobj asegs AL (hcs asegs R HIA h') m' (CTX + 8) 8).
    { eapply aobj_cs_mono; [exact HCS'|]. eapply (presA_aobj asegs R); [exact CSOK| exact HPc| exact OCTX| apply CRo; [clear - CTXLO LOS; lia| exact (client_range_of_w L _ _ _ _ _ CWX)]| clear - LOS SLO NEED0; lia| exact TOPCS]. }
    assert (OCUR' : aobj asegs AL (hcs asegs R HIA h') m' CUR 32).
    { eapply aobj_cs_mono; [exact HCS'|]. eapply (presA_aobj asegs R); [exact CSOK| exact HPc| exact OCUR| apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| clear - LOS SLO NEED0; lia| exact TOPCS]. }
    assert (SR' : seqrep asegs m' (nLB nodes) BUF END CUR nodes cur).
    { eapply seqrep_mem; [exact HSR| intros b Hb; exact Hb|].
      intros A cs HA HR Hsz.
      assert (CURE : nodes <> [] -> cur = last nodes 0 /\ In cur nodes).
      { intros Hne. destruct nodes as [|a0 r0]; [exfalso; exact (Hne eq_refl)|]. destruct HSR as (E & _). split; [exact E| rewrite E; apply last_in; exact Hne]. }
      eapply (presA_rw_cells asegs R); [exact HPc| exact HR| |]; rewrite Hsz.
      - destruct HA as [[-> _]|HA]; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]|].
        eapply client_range_block; [apply in_app_iff; left; apply nLB_in; exact (in_rl _ _ HA)| clear; lia| clear; lia].
      - cbn [disjoint_from]. destruct HA as [[-> Hne]|HA].
        + destruct (CURE Hne) as [_ CINn]. ddestruct (HNF cur CINn) as (_ & _ & _ & _ & _ & NCUR & _). clear - DXC NCUR. lia.
        + assert (Hne : nodes <> []) by (intros E; rewrite E in HA; exact HA).
          destruct (CURE Hne) as [CE _]. pose proof (others_apart hc mm nodes A HHc HND Hne HA) as OA. rewrite <- CE in OA.
          destruct (HNF A (in_rl _ _ HA)) as (_ & _ & _ & _ & NCTX & _). clear - OA NCTX. lia. }
    (* [comment removed for export] *)
    assert (HPx : presA asegs R LB LF (bv_unsigned sp + -112) (arl_stklo R) (hstkhi asegs R HIA hc) X mm m').
    { destruct CIN as [CE|CINn].
      - subst cur. eapply presA_weaken; [exact HPc| intros b Hb; apply nLB_sub; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia.
      - ddestruct (HNF cur CINn) as (_ & _ & _ & _ & _ & _ & _ & NFR).
        assert (HP1 : presA asegs R LB LF (bv_unsigned sp + -112) (arl_stklo R) (hstkhi asegs R HIA hc) [(cur, cur + 32); (CTX + 8, CTX + 16)] mm m').
        { eapply presA_weaken; [exact HPc| intros b Hb; apply nLB_sub; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
          intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
        assert (HP2 : presA asegs R LB LF (bv_unsigned sp + -112) (arl_stklo R) (hstkhi asegs R HIA hc) [(CTX + 8, CTX + 16)] mm m').
        { eapply (presA_drop_fresh_gen R LB LF _ _ _ [(CTX + 8, CTX + 16)] cur 32 cur (cur + 32)); [exact HP1| exact NFR| clear; lia| clear; lia| clear - ALO LOS SLO NEED0; lia]. }
        eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
    assert (PRES' : presW asegs R HIA h' LB LF (bv_unsigned sp) (arl_stklo R) X m m').
    { eapply (presW_hmono R HIA hc h'); [| exact HCS'| exact HS'].
      eapply (presW_call asegs R HIA hc LB LF _ _ X m mm m' LB LF); [exact PRES| exact HPx| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    idtac "CB-TRANSPORTED".
    pose proof (eq_trans HT' HTc) as HTh'. pose proof (eq_trans HS' HSc) as HSh'. pose proof (eq_trans HF' HFc) as HFh'.
    assert (BUD1 : havol asegs R HIA h' <= havol asegs R HIA h + (e + 1) * ASN1_SEQ_CB_PHI) by (clear - HV' BUDa; lia).
    assert (BUDF1 : hfr asegs R HIA h' <= hfr asegs R HIA h + (e + 1) * fr_charge 0) by (clear - HFR' BUDFa; lia).
    destruct CASES as [(-> & CP0 & HH' & HCTX' & (pad' & HCUR')) | [(N & -> & CPN & N16 & NFR & _ & HH' & HCTX' & HCUR' & HN') | (-> & CPN & HH' & HCTX' & HCUR')]].
    - (* [comment removed for export] *)
      idtac "CB-FILL".
      assert (NE : nodes = []) by (clear - HCB CP0 B5; destruct HCB as [(_ & _ & E)|K]; [exact E| lia]).
      subst nodes. cbn in SR'. subst cur.
      eapply KONT with (hc' := h') (mm' := m') (nodes' := @nil Z) (cur' := CUR) (ct' := Z_to_bv 64 tagb) (cpad' := pad') (cl' := len) (cp' := start) (r := 0);
        [left; reflexivity| | exact HPP| exact BUD1| exact BUDF1| clear - HLN; cbn [length] in *; lia| exact (conj HK' (mo_frame_trans _ _ _ MF1 MF'))].
      unfold tinv. spine; first [ eassumption | reflexivity | exact HCSh' | exact I
        | lazymatch goal with
          | |- _ \/ _ => right; clear - HST0 HLEN HSE; lia
          | |- aobj _ _ _ _ BUF _ => exact (hm_aobj_block asegs R HIA h' _ _ m' BUF n HH' (nLB_sub _ _ BIN))
          end
        | match goal with |- ?g => idtac "FILL-LEFT:" g end ].
    - (* [comment removed for export] *)
      idtac "CB-APPEND".
      assert (HCB2 : BUF <= cp /\ 0 <= cl /\ cp + cl <= END) by (clear - HCB CPN; destruct HCB as [(E & _)|K]; [exfalso; exact (CPN E)| exact K]).
      dpose NFR as (NF0 & NF1 & NF2 & NF3).
      assert (NFR0 : fresh_apart R LB LF N 32).
      { split; [exact NF0|]. split; [exact NF1|]. split; [exact NF2|]. intros B j Hb. apply NF3. apply SUBq. exact Hb. }
      assert (NNI : ~ In N nodes).
      { intros HI. destruct (NF3 N 32 ltac:(apply in_or_app; left; apply nLB_in; exact HI)) as [K|K]; clear - K; lia. }
      eapply KONT with (hc' := h') (mm' := m') (nodes' := nodes ++ [N]) (cur' := N) (ct' := Z_to_bv 64 tagb) (cpad' := Z_to_bv 64 0) (cl' := len) (cp' := start) (r := 0);
        [left; reflexivity| | exact HPP| exact BUD1| exact BUDF1| rewrite length_app; cbn [length]; clear - HLN; lia| exact (conj HK' (mo_frame_trans _ _ _ MF1 MF'))].
      unfold tinv. rewrite nLB_snoc. spine; first [ eassumption | reflexivity | exact HCSh' | exact HN'
        | lazymatch goal with
          | |- _ \/ _ => right; clear - HST0 HLEN HSE; lia
          | |- aobj _ _ _ _ BUF _ => exact (hm_aobj_block asegs R HIA h' _ _ m' BUF n HH' (or_intror (nLB_sub _ _ BIN)))
          | |- List.NoDup _ => apply NoDup_app; [exact HND| repeat constructor; intros []| intros x Hx [<-|[]]; exact (NNI Hx)]
          | |- forall x, In x (nodes ++ [N]) -> nodeF x => intros x Hx; apply in_app_iff in Hx; destruct Hx as [Hx|[<-|[]]]; [exact (HNF x Hx)| exact (nodeF_of_fresh N N16 NFR0)]
          | |- seqrep _ _ _ _ _ _ _ _ =>
              eapply seqrep_snoc with (cur := cur) (ct := ct) (cpad := cpad) (cl := cl) (cp := cp);
                [ eapply seqrep_mem; [exact SR'| intros b Hb; right; exact Hb| intros A cs _ HR _; exact HR]
                | exact HCUR' | exact (proj1 HCB2) | exact (proj1 (proj2 HCB2)) | exact (proj2 (proj2 HCB2)) | left; reflexivity | exact N16 | exact NF0 ]
          end
        | match goal with |- ?g => idtac "APPEND-LEFT:" g end ].
    - (* [comment removed for export] *)
      idtac "CB-FAIL".
      eapply KONT with (hc' := h') (mm' := m') (nodes' := nodes) (cur' := cur) (ct' := ct) (cpad' := cpad) (cl' := cl) (cp' := cp) (r := -106);
        [right; reflexivity| | exact HPP| exact BUD1| exact BUDF1| clear - HLN; lia| exact (conj HK' (mo_frame_trans _ _ _ MF1 MF'))].
      unfold tinv. spine; first [ eassumption | reflexivity | exact HCSh'
        | lazymatch goal with
          | |- aobj _ _ _ _ BUF _ => exact (hm_aobj_block asegs R HIA h' _ _ m' BUF n HH' (nLB_sub _ _ BIN))
          end
        | match goal with |- ?g => idtac "FAIL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis BUD : havol asegs R HIA h + TRAV_PHI (END - P) <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + TRAV_FFR (END - P) <= FR_MAX.

  Ltac open_inv_mu INV hc :=
    open_inv INV hc;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(PP, PP + 8)] mx) as MU; pose proof (wmono_refl asegs mx) as WM;
      lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HHx) as AB end end.
  (* [comment removed for export] *)
  Ltac fold_inv INVn hc nodes cur ct cpad cl cp j0 :=
    lazymatch goal with MU : munch _ ?m0 ?mx, WM : wmono _ ?m0 ?mx, SRx : seqrep _ ?m0 _ _ _ _ _ _, NFx : (forall x, In x _ -> nodeF x) |- _ =>
      let HSR2 := fresh "HSR2" in
      pose proof (seqrep_pp _ _ _ _ SRx NFx MU WM) as HSR2;
      assert (INVn : tinv mx hc nodes cur ct cpad cl cp j0) by (unfold tinv; spine; first [eassumption | match goal with |- ?g => idtac "FOLD-LEFT:" g end])
    end.

  (* [comment removed for export] *)
  Definition LoopOblig (p : Z) (tgw s3w : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pe,$6.Px1,(2.&40.)Px5,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(58.R19.R1:.R18.R17.R16.R15.R14.R13.R12.)P,(2:.$51.R1:.VPP,(1:.$2;.(2<.(10.&40.O3.))(1>.$2;.)))P,(12.=R13.)P,(12.(59.+2.R14.)(42.O3.VP,))P,(12.(23.$51.VR,VHIA,R1>.)(1=.(23.$51.VR,VHIA,Vh,)(59.R15.$5:.)))P,(12.(25.$51.VR,VHIA,R1?.)(1=.(25.$51.VR,VHIA,Vh,)(59.R16.(5;.=))))P,(12.(27.(28.$6.R1>.))R17.)(5<.$51.(5=.$51.VR,VHIA,R21.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R17.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,R16.(10.&40.O3.)R15.R14.(10.&40.(62.(56.VR,)))(10.&40.VPP,)(10.&40.VEND,)(10.&40.+??.)O2.(10.&40.=)(10.&40.=)(10.&40.$47.)(10.&40.VCTX,)(10.&40.(1=.(63.VPP,+3.)(62.(56.VR,))))O1.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(10.&40.+99>9<.)Vfc,(>.(2.&40.))R20.(?.$51.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@D28498761192.161D4451634193.161 D60109196847.161K3337916572.161 K44164039966.161K56840826649.161L1685717371.0   L24007014857.5  L27111942217.1  L29010574176.145L29457085556.9  L30664565398.16 L31958765794.13 L32887553589.11 L3323761050.2   L34035016763.2  L35655538583.9  L37237756232.12 L39172636981.0  L41202929119.146L43517519711.12 L43520010079.13 L44168742175.3  L45529054250.149L53271535775.146L54880129650.12 L56826150901.2  L56937456180.12 L58485672988.16 L60098763854.3  L8978340120.13  L9315331005.13  L9817099214.149 P34030614239.161Q10649498890.158Q10649605192.157Q13735186293.157Q17701933584.158Q28496781288.160Q28498761192.161Q34390149656.158Q37216054521.158Q39600066516.158Q4451634193.161 Q4453582353.160 Q45355845111.157Q47135511895.161Q54050196007.158Q61556549392.159Q61847600945.15800000n01l03303i04^05S05T05k05o06006O06e06l07S07T07U07n08;08<08`09109B09C0:n0;R0;Y0;Z0<?0<Y0<c0=K0>30?^0@e0A80AK0A^0B10B^0CK0CL0Cf0Cg0DT0EA0ET0FA0FB0F^0GVS2sp2PP3CTX3CUR1P3END2bs5nodes3cur5start1r4lenw2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs5nodes3cur5start1r4lenw2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS5nodes3cur5start1r4lenw2HB5Ha_st5Hl_stS2PP1P3END2bs5nodes3cur5start4lenw4CPPa2HB5Ha_st5Hl_stS2PP1P3END3BUF2bs3DPB5nodes5start4lenw2HB5Ha_st5Hl_stS2PP3CTX1P3END2bs3DXP5nodes5start4lenw2HB5Ha_st5Hl_stSS2p05start4lenw4HST02LRS2PPFS1P2p05start1e4lenw4HST03HE22LRS3END2bs5start4lenw2KlS1P3ENDS1P3END2p05start1e4lenw4HST03HSE3HE22LRFFS1R3HIA1h2sp2lo3TOP5HTOPcS1P3END5startSS2sp2PP3CTX3CUR1P3END2bs5nodes3cur1rS1P3END1e3HE03HEES1P3END1e3HE03HEEFS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur2p05start1r4lenw3HP04HST03HSE2LR2C03SPRS2sp2PP3CTX3CUR1P3END2bs5nodes3cur1rS1P3ENDFS1P3END2p05start4lenw3HP04HST03HSE2LRS3END2bs5start4lenw3HSE2KlS1R2lo3LOSS1P3END2p05start4lenw3HP04HST03HSE2LR2PES1P3END2p05start4lenw3HP04HST03HSE2LR2PES2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur2p05start1r4lenw3HP04HST03HSE2LR2C03SPRS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodes5start4lenw2HB5Ha_st5Hl_stS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodes5start4lenw2HB5Ha_st5Hl_stS2PP1P3END2bs5nodes5start4lenw2HB5Ha_st5Hl_stFS2PP1P3END2bs3PP05nodes2HBFS2PP1P3END2bs5nodes5start4lenw2HB5Ha_st5Hl_stS2PP1P3END2bs5nodes5start4lenw2HB5Ha_st5Hl_stS2PP1P3END2bs5nodesS2PP1P3END2bs5nodes5start4lenw2HB5Ha_st5Hl_stFS2PP1P3END2bs5nodes2HB5Ha_stS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur1r3SPR". (* [comment removed for export] *)
  #[using="IMG NEED0 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 CTX0 CTXLO DXP DXC LOS SLO TOP"] Lemma aftercb_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pp0,$6.Pstart,$6.Pe,$6.Pr,$6.Plenw,(2.&40.)Ptgw,(2.&40.)Ps3w,(2.&40.)Py5,(2.&40.)Py6,(2.&40.)Py7,(2.&40.)Py11,(2.&40.)Py12,(2.&40.)Py13,(2.&40.)Py14,(2.&40.)Py15,(2.&40.)Py16,(2.&40.)Py17,(2.&40.)Py28,(2.&40.)Py29,(2.&40.)Py30,(2.&40.)Py31,(2.&40.)P,(58.R1=.R1>.R1<.R1;.R1:.R19.R18.R17.R16.)P,(2:.$51.R1>.VPP,(1:.$2;.(2<.(10.&40.R15.))(1>.$2;.)))P,(2>.(9.$6.R14.=)(9.$6.R14.-6:.))P,(12.VP,R18.)P,(12.(1=.R19.+2.)R18.)P,(12.(1=.R19.(15.&40.R16.))VEND,)P,(12.=R19.)P,(12.(59.+2.R1:.)(42.(1=.R1<.+2.)VP,))P,(12.(23.$51.VR,VHIA,R26.)(1=.(23.$51.VR,VHIA,Vh,)(59.R1;.$5:.)))P,(12.(25.$51.VR,VHIA,R27.)(1=.(25.$51.VR,VHIA,Vh,)(59.R1<.(5;.=))))P,(12.(27.(28.$6.R26.))R1=.)P,Pp',$6.P,(12.(1=.R21.+2.)R1.)P,(11.R2.VEND,)(64.R3.R1>.R1=.)(5<.$51.(5=.$51.VR,VHIA,R2:.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.(10.&40.+99?60.)(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,R1:.R19.R18.R1=.(10.&40.(62.(56.VR,)))(10.&40.R1>.)R17.R16.R15.R14.R13.R12.R11.(10.&40.(1=.(63.VPP,+3.)(62.(56.VR,))))R1;.(10.&40.VEND,)(10.&40.+??.)(10.&40.=)R1<.(10.&40.=)(10.&40.VPP,)(10.&40.VCTX,)(10.&40.$47.)R10.R?.R>.R=.)VF,(10.&40.+99?60.)Vfc,(>.(2.&40.))R29.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    intros until y31. intros INV HPP Hr HP0 HST0 HSE HE0 HE2 BUDa BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 lenw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof INV as INV0.
    open_inv_mu INV hc.
    assert (HEE : e <= (END - P) / 2) by (apply Z.div_le_lower_bound; [clear; lia| clear - HE0 HE2 HST0 HSE LR; lia]).
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "CB-ERR".
      assert (r = -106) as -> by (clear - Kr Hr; destruct Hr as [->| ->]; [exfalso; apply Kr; reflexivity| reflexivity]).
      eapply exit_walk with (e := e) (p' := start); first [ exact INV0 | exact HPP | eassumption | clear - HP0 HST0 HSE LR HE0 HEE; lia | match goal with |- ?g => idtac "AFT-EXIT-LEFT:" g end ]. }
    idtac "CB-OK".
    (* [comment removed for export] *)
    do 5 zstep.
    fold_inv INV2 hc nodes cur ct cpad cl cp j0.
    (* [comment removed for export] *)
    zstep. if_cases Kl; zify_cond Kl.
    - idtac "LOOP-AGAIN".
      assert (PL : start + bv_unsigned lenw < END) by (clear - Kl HSE LR B1 B3 B5 B47 HP0 HST0; try kland Kl; rewrite ?Z.mod_small in Kl by lia; lia).
      eapply (KLOOP (start + bv_unsigned lenw) ltac:(clear - HST0 LR; lia) PL) with (e := e);
        first [ exact INV2 | eassumption | clear - HE0 HE2 HST0 LR; lia | match goal with |- ?g => idtac "AFT-LOOP-LEFT:" g end ].
    - idtac "LOOP-END".
      (* [comment removed for export] *)
      zstep.
      assert (PE : start + bv_unsigned lenw = END) by (clear - Kl HSE LR B1 B3 B5 B47 HP0 HST0; try kland Kl; rewrite ?Z.mod_small in Kl by lia; lia).
      eapply exit_walk with (e := e) (r := 0) (p' := start + bv_unsigned lenw);
        first [ exact INV2 | eassumption | clear - HP0 HST0 HSE LR HE0 HEE PE; lia | match goal with |- ?g => idtac "AFT-END-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00X0@L12068562588.12 L16967450418.10 L19613121687.50 L27111942217.1  L27798497327.17 L30297398587.147L32889713813.9  L34384969785.12 L35655538583.9  L37237756232.10 L39172636981.0  L41202929119.147L41202929119.148L43517519711.10 L48785228659.12 L51964804511.16 L53519145549.148L56439626597.146L56937456180.10 L57402439861.147L60098763854.3  L9815055909.146 Q10649498890.158Q10649498890.159Q10651748285.158Q10651750077.157Q13733107072.157Q13733108864.158Q17701933584.158Q17701933584.159Q34390149656.158Q34390149656.159Q39600066516.158Q39600066516.159Q45353768450.158Q45353770754.157Q54050196007.158Q54050196007.159Q61847600945.158Q61847600945.15900000<00C00D00H00d02F02f02m03F03S03T04604X04i05N05b06D07f08D08m0970:Y0:l0;?0;R0;e0<80<K0<^0=10=20=30=40=50=H0=[0=\0=]0>S0?IS1P2p01e3HE2S1P3ENDFS2PPS1P3BUF2B12p05start3HP04HST0S2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur2p05start3HP04HST04HSE02C03SPRS1P3END2p05start1e4HST04HSE03HE2S1e3HE0S1R3HIA1h2sp2lo3TOP5HTOPcS1P3END5startSS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1P3END1e3HE03HEES1P3END2p05start1e2Lw4HST03HE22LR3HSES3END2bs5start2Lw2KcS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur2p05start3HP04HST04HSE02C03SPRS1P3END2p05start3HP04HST04HSE0S2sp2PP3CTX3CUR1P3END2bs5nodes3cur2tb3HtbS1R2lo3LOSS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur2p05start3HP04HST04HSE02C03SPRS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesFFFFS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesFFS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPR". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma join2_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pp0,$6.Pstart,$6.Ptb,$6.Pe,$6.PLw,(2.&40.)Ptgw,(2.&40.)Ps3w,(2.&40.)Px1,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(58.R1>.R1?.R1=.R1<.R1;.R1:.R19.R18.R17.)P,(2:.$51.R1?.VPP,(1:.$2;.(2<.(10.&40.R16.))(1>.$2;.)))P,(12.VP,R18.)P,(12.(1=.R19.+2.)R18.)P,(12.R19.VEND,)P,(8.(12.=R19.)(11.R19.+100.))P,(12.=R19.)P,(12.(59.+2.R1:.)(42.R1=.VP,))P,(12.(23.$51.VR,VHIA,R27.)(1=.(23.$51.VR,VHIA,Vh,)(59.R1;.$5:.)))P,(12.(25.$51.VR,VHIA,R28.)(1=.(25.$51.VR,VHIA,Vh,)(59.R1<.(5;.=))))P,(12.(27.(28.$6.R27.))R1=.)P,Pp',$6.P,(12.(1=.R22.+2.)R1.)P,(11.R2.VEND,)(64.R3.R1?.R1>.)(5<.$51.(5=.$51.VR,VHIA,R2;.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R1;.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,(10.&40.R20.)R1:.R19.R1>.(10.&40.(62.(56.VR,)))(10.&40.VPP,)(10.&40.VEND,)(10.&40.+??.)R1=.(10.&40.=)(10.&40.=)(10.&40.$47.)(10.&40.VCTX,)(10.&40.(1=.(63.VPP,+3.)(62.(56.VR,))))R1<.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)VF,(10.&40.+99?04.)Vfc,(>.(2.&40.))R2:.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HPP HP0 HST0 HSE0 Htb HE0 HE2 BUDa BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof INV as INV0.
    open_inv_mu INV hc.
    assert (HEE : e <= (END - P) / 2) by (apply Z.div_le_lower_bound; [clear; lia| clear - HE0 HE2 HST0 HSE0; lia]).
    (* [comment removed for export] *)
    do 4 zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kc; zify_cond Kc.
    { idtac "J2-OOD".
      do 2 zstep.
      eapply exit_walk with (e := e) (r := -96) (p' := start); first [ exact INV0 | exact HPP | eassumption | clear - HP0 HST0 HSE0 HE0 HEE; lia | match goal with |- ?g => idtac "J2-EXIT-LEFT:" g end ]. }
    assert (HSE : start + bv_unsigned Lw <= END) by (clear - Kc HSE0 LR B1 B3 B5 B47 HP0 HST0; try kland Kc; rewrite ?Z.mod_small in Kc by lia; lia).
    clear Kc.
    idtac "J2-OK".
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Km; zify_cond Km.
    { exfalso. rewrite Z.land_0_r in Km. first [ apply Km; reflexivity | clear - Km; cbn in Km; lia ]. }
    clear Km.
    (* [comment removed for export] *)
    do 14 zstep.
    idtac "J2-CBARGS".
    fold_inv INV2 hc nodes cur ct cpad cl cp j0.
    assert (HE1 : e + 1 <= (END - P) / 2) by (apply Z.div_le_lower_bound; [clear; lia| clear - HP0 HST0 HSE LR HE0 HE2; lia]).
    eapply cb_step with (e := e) (p := start) (tagb := tb) (start := start) (lenw := Lw);
      first [ exact INV2 | exact BUD | exact BUDF | eassumption | clear - HP0 HST0 HSE0 HSE LR HE0 HE2 B1 Htb; lia | idtac ].
    intros hc' mm' nodes' cur' ct' cpad' cl' cp' r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Hr INV' HPP' BUD' BUDF' HLN'.
    eapply aftercb_walk with (e := e + 1) (p0 := p0) (start := start);
      first [ exact INV' | exact HPP' | exact Hr | exact KLOOP | eassumption | clear - HP0 HST0 HSE LR HE0 HE2; lia | match goal with |- ?g => idtac "J2-AFT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0150@D28498761192.162D4451634193.162 D60109196847.162K3337916572.162 K44164039966.162K56840826649.162L1685717371.0   L24577716658.12 L25810914902.160L27111942217.1  L3323761050.2   L34035016763.2  L35655538583.9  L41202929119.148L43938004642.148L44168742175.3  L46064784831.108L52067441322.151L53271535775.148L54273833131.12 L54866785944.1  L55345685748.143L55345854604.146L56303674338.11 L56826150901.2  L56951873990.1  L57892315391.145L60098763854.3  L62338813384.3  L62908422684.147L62909071722.145L66665204274.12 L66667342307.11 L68648578258.2  L8463380018.145 P34030614239.162Q10649498890.157Q10649685048.158Q10650081102.156Q12757461271.157Q13734317171.156Q15930096381.157Q17525089906.159Q17525187323.157Q17701933584.157Q20741671226.159Q20880934901.157Q20881294204.159Q28496781288.161Q28498761192.162Q29850408660.157Q34390149656.157Q36349221533.154Q37216054521.159Q39600066516.157Q40016855704.157Q40016971031.154Q40017217041.159Q43608216472.154Q4451634193.162 Q4453582353.161 Q45355769223.158Q47135511895.162Q54050196007.157Q61556549392.160Q61847600945.157Q62944057836.157Q62944222565.159Q68390477037.15700000j01d02g03[04N05A05B05U06D06H06I06J06c07N07O07P0:I0;40;_0<20<50=S0?10?A0?B0?E0@L0@V0@_0B30CG0Ca0D80D>0Di0Ek0FG0Fc0G?0G_0H;0HT0HU0HV0I20IR0IS0IT0J?0Jj0KC0KD0Kd0LG0LH0M50Mb0NO0Nh0OS0P>0PZ0QE0QF0Qk0Rg0Rh0Ri0SYS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCE2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCE2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR3END2lo2bs3LOS1j5nodes3cur1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes3cur1c2Hj3HCE4CPPa2HB5Ha_st5Hl_stS2PP3END3BUF2bs3DPB1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3CTX3END2bs3DXP1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stSS3END1j1c2Hj3HCE2J1S2sp2PP3CTX3CUR3END3BUF2bs1j5nodes3cur1c2Hj3HCES2PPFFS1R3HIA1h2sp2lo3TOP5HTOPcS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCEFFS1R3HIA1h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m3mo02PP3CTX3CUR1P3END3BUF2lo2bs2hc2mm5nodes1c2tb2Lw3tgw3s3w2x13x203x213x223x233x243x253x263x273x293x303x312Hj3HCES2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCES2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCES3END1j1c2Hj3HCE2J1S1cS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B33B472B54CUR04CTX01j5nodes3cur2p01c2Hj3HP03HC03HCE2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B33B472B54CUR04CTX01j5nodes3cur2p01c2Hj3HP03HC03HCE2C03SPRS3END1j1c2Hj3HCEFS1jS2sp2PP3CTX3CUR3END3BUF2bs3PP02B34CUR04CTX01j5nodes3cur1c2Hj3HCE2C03SPRS1R2lo3LOSS1j2Hj2KLS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B14CUR04CTX01j5nodes3cur2p01c2Hj3HP03HC03HCE2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B14CUR04CTX01j5nodes3cur2p01c2Hj3HP03HC03HCE2C03SPRS3END1j2p01c2Hj3HC03HCE2J1S3END1j2p01c2Hj3HC03HCES1j2HjS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCES1R5NEED02sp2PP3END2lo2bs4PPLO3SLO1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCES3END3BUF2bs2B31j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCES3END2bs1j5nodes1c2Hj3HCEFFS2PP3END2bs1j5nodes1c2Hj3HCES3END3BUF2bs2B31j5nodes1c2Hj3HCEFFS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS3END2bs1j5nodes1c2Hj3HCEFS3END3BUF2bs2B31j5nodes1c2Hj3HCES2PP3END2bs3PP01j5nodes1c2Hj3HCE2HBFS1P3END3BUF2bs2B11j5nodes2p01c2Hj3HP03HC03HCES1P3END3BUF2bs2B11j5nodes2p01c2Hj3HP03HC03HCES1P3END3BUF2bs2B11j5nodes2p01c2Hj3HP03HC03HCES3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stFS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_stS2sp2PP3CTX3CUR3END2bs3ALP3PP04CTX01j5nodes3cur1c2Hj3HCE3SPRFFS1P3END3BUF2bs2B12B51j5nodes2p01c2Hj3HP03HC03HCE". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma lenloop2_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pj,$4=.Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pp0,$6.Pc,$6.Ptb,$6.Pe,$6.PLw,(2.&40.)Ptgw,(2.&40.)Ps3w,(2.&40.)Px1,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(8.(65.#1.R1=.)(65.R1=.#4.))P,(12.VP,R14.)P,(12.(1=.R15.+2.)R14.)P,(12.(1=.R15.(27.R20.))VEND,)P,(8.(12.=R15.)(11.R15.+100.))P,(58.R20.R21.R1?.R1>.R1=.R1<.R1;.R1:.R19.)P,(2:.$51.R21.VPP,(1:.$2;.(2<.(10.&40.R18.))(1>.$2;.)))P,(12.=R17.)P,(12.(59.+2.R18.)(42.R1;.VP,))P,(12.(23.$51.VR,VHIA,R25.)(1=.(23.$51.VR,VHIA,Vh,)(59.R19.$5:.)))P,(12.(25.$51.VR,VHIA,R26.)(1=.(25.$51.VR,VHIA,Vh,)(59.R1:.(5;.=))))P,(12.(27.(28.$6.R25.))R1;.)P,Pp',$6.P,(12.(1=.R20.+2.)R1.)P,(11.R2.VEND,)(64.R3.R1=.R1<.)(5<.$51.(5=.$51.VR,VHIA,R29.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R19.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,(10.&40.R1>.)(10.&40.(1=.R1?.+1.))(10.&40.R1?.)R1<.(10.&40.(62.(56.VR,)))(10.&40.VPP,)(10.&40.VEND,)(10.&40.+??.)R1;.(10.&40.=)(10.&40.=)(10.&40.$47.)(10.&40.VCTX,)(10.&40.(1=.(63.VPP,+3.)(62.(56.VR,))))R1:.R18.R17.R16.R15.R14.R13.R12.R11.(10.&40.(27.R2:.))R10.R?.R>.)VF,(10.&40.+99?=0.)Vfc,(>.(2.&40.))R28.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    induction j as [|j IH]; intros until x31; intros Hj HP0 HC0 HCE Htb INV HPP HE0 HE2 BUDa BUDFa HLN KLOOP; [lia|].
    open_inv_mu INV hc.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF c.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    get_byte bs (c - BUF) b NB. read_at HBUF NB (c - BUF) RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    do 5 zstep.
    rewrite (swrap32_id (Z.of_nat (S j) + -1)) by (clear - Hj; lia).
    fold_inv INV2 hc nodes cur ct cpad cl cp j0.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - idtac "LL2-ITER".
      replace (Z_to_bv 64 (Z.of_nat (S j) + -1)) with (Z_to_bv 64 (Z.of_nat j)) by (f_equal; clear; lia).
      replace (Z_to_bv 64 (c + 2)) with (Z_to_bv 64 (c + 1 + 1)) by (f_equal; clear; lia).
      assert (J1 : (1 <= j)%nat) by (clear - KL Hj; try kland KL; rewrite ?Z.mod_small in KL by lia; lia).
      eapply (IH hc _ nodes cur ct cpad cl cp j0 p0 (c + 1) tb e);
        first [ exact INV2 | exact KLOOP | eassumption | clear - Hj J1 HP0 HC0 HCE Htb; lia | match goal with |- ?g => idtac "LL2-IH-LEFT:" g end ].
    - idtac "LL2-DONE".
      (* [comment removed for export] *)
      zstep.
      eapply join2_walk with (p0 := p0) (start := c + 1) (tb := tb) (e := e);
        first [ exact INV2 | exact KLOOP | eassumption | clear - Hj HP0 HC0 HCE Htb; lia | match goal with |- ?g => idtac "LL2-J2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02^0@D28498761192.156D28498761192.172D28498761192.176D4451634193.156 D4451634193.172 D4451634193.176 D60109196847.156D60109196847.172D60109196847.176K3337916572.156 K3337916572.172 K3337916572.176 K44164039966.156K44164039966.172K44164039966.176K56840826649.156K56840826649.172K56840826649.176L16108054177.161L16110144372.150L1685717371.0   L16967450418.7  L2006341092.154 L2006341095.160 L2006470375.156 L22271692658.7  L22649229297.154L27081481460.2  L27111942217.1  L27592979920.7  L30803094856.158L31163740229.141L31165787832.145L32889713813.7  L33042191776.10 L3323761050.2   L34035016763.2  L34064182271.146L34531113896.146L34541613483.148L35345707766.150L35347804779.157L35655538583.9  L39061430287.1  L39172636981.0  L41202929119.142L41202929119.158L41202929119.162L42563570082.12 L42987192166.161L43517519711.7  L44168742175.3  L45172557417.10 L45172570324.12 L53271535775.142L53271535775.158L53271535775.162L53520062717.152L53520219188.155L53520219188.161L53522454876.149L53792479276.6  L5548916134.12  L5632928883.3   L56620768531.10 L56620770222.12 L56826150901.2  L60098763854.3  L63152446533.161L676697817.169  L676697817.173  L68713103657.7  L689969970.7    L9720153999.14  L9815156144.149 P34030614239.156P34030614239.172P34030614239.176Q10596658666.172Q10596658667.168Q10598656341.166Q10598656341.172Q10649498890.153Q10649498890.169Q10649498890.173Q10649520692.172Q10651703251.168Q10651750077.152Q13733088494.168Q13733107072.152Q13734809865.172Q15930096381.156Q15930096381.166Q15930096381.172Q17701933584.153Q17701933584.169Q17701933584.173Q20122090275.166Q20122090275.172Q20123762588.172Q20123762589.168Q25103717808.153Q25582878921.156Q25584979540.153Q25585075316.160Q26298105566.172Q26298105567.168Q28496781288.155Q28496781288.171Q28496781288.175Q28498761192.156Q28498761192.172Q28498761192.176Q30803724357.169Q30805965286.163Q3154241099.166 Q3154241099.172 Q34390149656.153Q34390149656.169Q34390149656.173Q36482499258.156Q36484171271.160Q37216054521.153Q37216054521.169Q37216054521.173Q39502765953.160Q39504763708.156Q39600066516.153Q39600066516.169Q39600066516.173Q4113544236.156 Q43608501033.163Q43610462858.153Q43610462858.169Q4451634193.156 Q4451634193.172 Q4451634193.176 Q4453582353.155 Q4453582353.171 Q4453582353.175 Q44956607449.166Q44956607449.172Q45353748076.168Q45353770754.152Q45355998091.172Q47135511895.156Q47135511895.172Q47135511895.176Q48193398520.160Q48195330629.156Q53622987766.156Q54050196007.153Q54050196007.169Q54050196007.173Q54487414257.160Q5517035412.168 Q5517035413.172 Q5518770986.166 Q5518770986.172 Q57399308128.163Q57399431262.166Q57399431262.172Q57401365728.168Q57401365729.172Q57401532099.169Q57988484915.166Q57988484915.172Q58126184374.156Q61556549392.154Q61556549392.170Q61556549392.174Q61847600945.153Q61847600945.169Q61847600945.17300000c01V02I03<03o04b05^06Z07V08C09009]0:I0;50;a0<M0=90=e0>O0?_0?`0?g0@m0B30C90C@0DF0DM0DQ0D]0D^0En0G>0GP0GZ0G[0G\0Hb0Ih0Jn0KP0L20LK0LN0LO0M10MS0N50NE0Nm0O>0O?0OK0OW0P90P[0Q=0RP0Sc0U60VF0VP0VW0Va0Vd0Vg0Vh0W20WZ0XB0Xj0Y30Y:0YK0Z[0[Y0\W0]U0]V0]W0]X0]Y0]l0^?0^R0^e0_80_K0_^0`10`D0`T0`d0a40aG0aZ0am0an0ao0b00b10bP0bo0cN0cm0dL0dk0eO0f30fW0g;0g_0hC0hb0iA0ic0jE0jF0jG0jH0jI0jJ0jd0k>0kX0kY0kZ0k[0k\0k]0l?0lO0l_0lo0mS0n70n[0o?0oc10G10f11E11X11k12>12b13F13j13k13l14>14?14@14A14`14a14b14c14d15C15b16A16`17?17^18018B18a19=19Y1:51:k1;a1<WS2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS1p5nodes3cur2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS1p5nodes3cur2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS1p5nodes3cur2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes3cur4CPPa2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes3cur4CPPa2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes3cur4CPPa2HB5Ha_st5Hl_stS2PP1P3END3BUF2bs3DPB1p5nodes2HB5Ha_st5Hl_stS2PP1P3END3BUF2bs3DPB1p5nodes2HB5Ha_st5Hl_stS2PP1P3END3BUF2bs3DPB1p5nodes2HB5Ha_st5Hl_stS2PP3CTX1P3END2bs3DXP1p5nodes2HB5Ha_st5Hl_stS2PP3CTX1P3END2bs3DXP1p5nodes2HB5Ha_st5Hl_stS2PP3CTX1P3END2bs3DXP1p5nodes2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs1p2Hp5nodes3cur2K1S2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPRSS1P3ENDS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B24CUR04CTX01p2Hp5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B24CUR04CTX01p2Hp5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B24CUR04CTX01p2Hp5nodes3cur2C03SPRS1P3ENDS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B22B34CUR04CTX01p5nodes3cur2C03SPR2P1S2nn2HNS2PPS1P3END1p2HpFS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPRS1P3END1p2Hp1e3HE2S3END1p2P1FFS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B22B34CUR04CTX01p2Hp5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B24CUR04CTX01p2Hp5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B24CUR04CTX01p2Hp5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R3HIA1h2sp2lo3TOP5HTOPcS1pSS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS3END1p2nn2HN2PNS2sp2PP3CTX3CUR1P3END3BUF2bs1p5nodes3curS1P3END1e3HE03HEEFS1P3END1p2HpS1P3END1p2HpS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPR2P1S2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPR2P1S2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPR2P1S2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPRS2b12nn2KnS2nn2HNS3END1p2K0S1pS1pFS1R2lo3LOSS2sp2PP3CTX3CUR1P3END2bs5nodes3cur2nn2NRS2sp2PP3CTX3CUR1P3END3BUF2bs1p5nodes3curS2sp2PP3CTX3CUR1P3END3BUF2bs1p5nodes3curS1P3END1pS1P3ENDS3END2bs1p2nn3KgeS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX01p2Hp5nodes3cur2C03SPRS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO1p5nodes2HB5Ha_st5Hl_stS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO1p5nodes2HB5Ha_st5Hl_stS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO1p5nodes2HB5Ha_st5Hl_stFFFFS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS1P3END2bs5nodesS1P3END2bs5nodesS1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesFFFFS1P3END3BUF2bs2B22B31p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B22B31p5nodes2P1S1P3END3BUF2bs2B22B31p5nodes2P1S2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS1P3END3BUF2bs2B22B31p5nodes2P1S1P3END3BUF2bs2B22B31p5nodes2P1S1P3END3BUF2bs2B12B22B51p2Hp5nodesS1P3END3BUF2bs2B12B22B51p2Hp5nodesFFFFFS2PP1P3END2bs3PP05nodes2HBS2PP1P3END2bs3PP05nodes2HBS2PP1P3END2bs3PP05nodes2HBFFFFFS1P3END3BUF2bs2B12B22B51p2Hp5nodesS1P3END2bs5nodesS1P3END2bs5nodesS1P3END2bs5nodesS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS1P3END3BUF2bs2B22B31p5nodes2P1S1P3END3BUF2bs2B22B31p5nodes2P1S2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stS2PP1P3END2bs1p5nodes2HB5Ha_st5Hl_stFFS1P3END2bs1p5nodesFFFS1P3END3BUF2bs2B22B31p2Hp5nodesFFFFS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END3BUF2bs2B12B21p2Hp5nodesS1P3END2bs1p5nodesS1P3END2bs1p5nodesS1P3END3BUF2bs2B22B31p2Hp5nodesS2PP1P3END2bs5nodes2HB5Ha_stS2PP1P3END2bs5nodes2HB5Ha_stS2PP1P3END2bs5nodes2HB5Ha_stS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPR". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma body_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pp,$6.Ptgw,(2.&40.)Ps3w,(2.&40.)P,(8.(12.VP,R3.)(11.R3.VEND,))P,(9.$6.(15.&40.R2.)(42.(41.+2.+40.)+4.))P,Pp',$6.P,(12.(1=.R6.+2.)R1.)P,(11.R2.VEND,)(64.R3.R7.R6.)(64.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros p tgw s3w Hp Hs3 KLOOP. unfold LoopOblig. intros until x31. intros INV HPP HE0 HE2 BUDa BUDFa HLN.
    pose proof INV as INV0.
    open_inv_mu INV hc.
    assert (HEE : e <= (END - P) / 2) by (apply Z.div_le_lower_bound; [clear; lia| clear - HE0 HE2 Hp; lia]).
    (* [comment removed for export] *)
    do 6 zstep.
    shadow_chk1 OBUF p.
    fold_inv INV1 hc nodes cur ct cpad cl cp j0.
    (* [comment removed for export] *)
    get_byte bs (p - BUF) b0 NB0. read_at HBUF NB0 (p - BUF) RD0.
    zstep. clear RD0. zstep.
    pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. cbn in B0R.
    zstep. if_cases Kt; zify_cond Kt.
    { idtac "B-TAG".
      zstep.
      eapply exit_walk with (e := e) (r := -98) (p' := p + 1); first [ exact INV1 | eassumption | clear - Hp HE0 HEE; lia | match goal with |- ?g => idtac "B-TAG-LEFT:" g end ]. }
    clear Kt.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K2; zify_cond K2.
    { idtac "B-OOD1".
      do 2 zstep.
      eapply exit_walk with (e := e) (r := -96) (p' := p + 1); first [ exact INV1 | eassumption | clear - Hp HE0 HEE; lia | match goal with |- ?g => idtac "B-OOD1-LEFT:" g end ]. }
    assert (P1 : p + 1 < END) by (match goal with H : 0 < END - (p + 1) |- _ => clear - H; lia end).
    idtac "B-LENBYTE".
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF (p + 1).
    (* [comment removed for export] *)
    get_byte bs (p + 1 - BUF) b1 NB1. read_at HBUF NB1 (p + 1 - BUF) RD1.
    zstep. clear RD1.
    zstep. if_cases Ksg; zify_cond Ksg.
    - idtac "B-LONG".
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      { idtac "B-INVLEN".
        do 2 zstep.
        eapply exit_walk with (e := e) (r := -100) (p' := p + 1); first [ exact INV1 | eassumption | clear - Hp HE0 HEE; lia | match goal with |- ?g => idtac "B-INVLEN-LEFT:" g end ]. }
      idtac "B-LONG2".
      pose proof (P_asn1_get_tag.land_127_range (bv_unsigned (sxb b1))) as NR.
      set (nn := Z.land (Z.land (bv_unsigned (sxb b1)) 255) 127) in *.
      assert (HN : 1 <= nn <= 4) by (clear - NR Kn Hs3; apply P_asn1_get_tag.longform_n; [exact NR|]; rewrite Hs3 in Kn; lia).
      clearbody nn. clear Kn.
      (* [comment removed for export] *)
      zstep. if_cases Kge; zify_cond Kge.
      { idtac "B-OOD2".
        do 2 zstep.
        eapply exit_walk with (e := e) (r := -96) (p' := p + 1); first [ exact INV1 | eassumption | clear - Hp HE0 HEE; lia | match goal with |- ?g => idtac "B-OOD2-LEFT:" g end ]. }
      assert (PN : p + 2 + nn <= END) by (clear - Kge HN P1 Hp B1 B3 B5 B47; try kland Kge; rewrite ?Z.mod_small in Kge by lia; lia).
      clear Kge.
      (* [comment removed for export] *)
      do 6 zstep.
      fold_inv INV2 hc nodes cur ct cpad cl cp j0.
      replace (Z_to_bv 64 nn) with (Z_to_bv 64 (Z.of_nat (Z.to_nat nn))) by (f_equal; clear - HN; lia).
      replace (Z_to_bv 64 (p + 3)) with (Z_to_bv 64 (p + 2 + 1)) by (f_equal; clear; lia).
      idtac "B-LOOP2".
      eapply lenloop2_walk with (j := Z.to_nat nn) (p0 := p) (c := p + 2) (tb := bv_unsigned b0) (e := e);
        first [ exact INV2 | exact KLOOP | eassumption | clear - HN PN Hp B0R HE0 HE2; lia | match goal with |- ?g => idtac "B-LL2-LEFT:" g end ].
    - idtac "B-SHORT".
      (* [comment removed for export] *)
      do 4 zstep.
      shadow_chk1 OBUF (p + 1).
      (* [comment removed for export] *)
      read_at HBUF NB1 (p + 1 - BUF) RD2. zstep. clear RD2.
      fold_inv INV2 hc nodes cur ct cpad cl cp j0.
      eapply join2_walk with (p0 := p) (start := p + 2) (tb := bv_unsigned b0) (e := e);
        first [ exact INV2 | exact KLOOP | eassumption | clear - P1 Hp B0R HE0 HE2; lia | match goal with |- ?g => idtac "B-J2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26726586762.6L34758806549.7L4591830978.7300000B00W01?S3END1k1p2Hk2p'2H1S1P3END1p2Hp2p'2H12H2S2sp2PP3CTX3CUR1P3END2bs1p3tgw3s3w2Hk2Hp". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma tloop : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pk,$4=.Pp,$6.Ptgw,(2.&40.)Ps3w,(2.&40.)P,(12.(42.VEND,R3.)(27.R4.))P,(8.(12.VP,R4.)(11.R4.VEND,))P,(9.$6.(15.&40.R3.)(42.(41.+2.+40.)+4.))(64.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros p tgw s3w Hk Hp Hs3; [lia|].
    apply body_walk; [exact Hp| exact Hs3|]. intros p' H1 H2. apply IH; [clear - Hk H1; lia| clear - Hp H1 H2; lia| exact Hs3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@L10945067458.13 L13302564338.5  L15045244990.5  L16967447858.5  L1815538771.5   L24339882801.6  L24341866801.5  L25850739944.12 L26141518430.5  L27111942217.1  L31958782178.6  L35655538583.9  L39172636981.0  L3925149779.5   L39280637297.0  L41202929119.140L41202929119.141L41202929119.142L49334200720.5  L49336181648.6  L49336182299.5  L56775168221.142L56775329836.139L60098763854.3  L63039848099.141L65108480066.5  L67434879103.140L9817097297.142 L9817099845.141 L9817267360.139 Q10649498890.151Q10649498890.152Q10649498890.153Q10649607901.152Q10649608159.151Q10649766968.150Q13735089925.150Q13735183586.151Q13735183840.152Q17701933584.151Q17701933584.152Q17701933584.153Q34390149656.151Q34390149656.152Q34390149656.153Q39600066516.151Q39600066516.152Q39600066516.153Q45355752839.150Q45355847264.151Q45355847522.152Q54050196007.151Q54050196007.152Q54050196007.153Q61847600945.151Q61847600945.152Q61847600945.15300000A00B00C00D00E00S00Z00g01101501601O01P01Y01Z02<02^03@03Q03b04205L06a06k08E08V09k0;E0<c0>80>K0>^0?10?D0?W0?j0@=0@P0@c0A60AI0A\0A]0A^0A_0A`0Aa0Ab0B50BH0B[0B\0B]0B^0CT0DJ0E@S3END2bs1q3HQE2KqSSSFS3END1q3HQE2QES3END1qS3END2bs1q2KqS3END1q2QLS2PPSS1R3HIA1h2sp2lo3TOP5HTOPcSS1P1q3HQ0SS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1P3END1q3HQ03HQES1P3END1q3HQ03HQES1P3END1q3HQ02QLS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur1q2Lw3HQ02LR2C03SPR2KeS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur1q3HQ03HQE2C03SPRS1R2lo3LOSS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur1q2Lw3HQ02LR2C03SPR2KcS1P3END1q3HQ03HQES2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur1q3HQ03HQE2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur1q2Lw3HQ02LR2C03SPR2KeS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur1q3HQ03HQE2C03SPR2Lw2LR2KcS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX05nodes3cur1q3HQ03HQE2C03SPRS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesFFFFFFS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesFFFS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX05nodes3cur3SPR". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma join1_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pq,$6.PLw,(2.&40.)Ptgw,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px8,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(58.R1<.R1=.R1;.R1:.R19.R18.R17.R16.R15.)P,(2:.$51.R1=.VPP,(1:.$2;.(2<.(10.&40.R15.))(1>.$2;.)))P,(12.(1=.VP,+2.)R16.)P,(12.R17.VEND,)P,(12.(23.$51.VR,VHIA,R21.)(1=.(23.$51.VR,VHIA,Vh,)(59.=$5:.)))P,(12.(25.$51.VR,VHIA,R22.)(1=.(25.$51.VR,VHIA,Vh,)(59.=(5;.=))))P,(12.(27.(28.$6.R21.))=)(5<.$51.(5=.$51.VR,VHIA,R24.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R18.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,R17.R16.R1:.R15.(10.&40.(62.(56.VR,)))(10.&40.VPP,)(10.&40.VEND,)(10.&40.+??.)R19.(10.&40.=)(10.&40.=)(10.&40.$47.)(10.&40.VCTX,)(10.&40.(1=.(63.VPP,+3.)(62.(56.VR,))))R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(10.&40.+99==4.)Vfc,(>.(2.&40.))R23.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HPP HQ0 HQE BUDa BUDFa HLN.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof INV as INV0.
    assert (HE00 : 0 <= 0 <= (END - P) / 2) by (split; [clear; lia| apply Z.div_pos; [clear - HQ0 HQE; lia| clear; lia]]).
    open_inv_mu INV hc.
    (* [comment removed for export] *)
    do 4 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    { idtac "J1-OOD".
      do 2 zstep.
      eapply exit_walk with (e := 0) (r := -96) (p' := q); first [ exact INV0 | exact HPP | eassumption | clear - HQ0 HQE; lia | match goal with |- ?g => idtac "J1-OOD-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 4 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    2:{ idtac "J1-MISMATCH".
        do 2 zstep.
        eapply exit_walk with (e := 0) (r := -102) (p' := q); first [ exact INV0 | exact HPP | eassumption | clear - HQ0 HQE; lia | match goal with |- ?g => idtac "J1-MM-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Kq; zify_cond Kq.
    { idtac "J1-EMPTY".
      do 2 zstep.
      assert (QE : q = END) by (clear - Kq HQ0 HQE B1 B2 B3 B5 B47; try kland Kq; rewrite ?Z.mod_small in Kq by lia; lia).
      eapply exit_walk with (e := 0) (r := 0) (p' := q); first [ exact INV0 | exact HPP | eassumption | clear - HQ0 HQE QE; lia | match goal with |- ?g => idtac "J1-EMPTY-LEFT:" g end ]. }
    assert (QL : q < END) by (clear - Kq HQ0 HQE B1 B3 B5 B47; try kland Kq; rewrite ?Z.mod_small in Kq by lia; lia).
    (* [comment removed for export] *)
    zstep.
    idtac "J1-LOOP".
    eapply (tloop (Z.to_nat (END - q)) q) with (e := 0);
      first [ exact INV0 | exact HPP | eassumption | clear - QL HQ0; lia | (vm_compute; reflexivity) | match goal with |- ?g => idtac "J1-LOOP-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0150@D28498761192.155D4451634193.155 D60109196847.155K3337916572.155 K44164039966.155K56840826649.155L1685717371.0   L24577716658.8  L25810914902.153L27111942217.1  L3323761050.2   L34035016763.2  L35655538583.9  L41202929119.141L43938004642.141L44168742175.3  L52067441322.144L52982375861.101L53271535775.141L54273833131.8  L54866785944.1  L55345685748.136L55345854604.139L56303680263.7  L56826150901.2  L56951873990.1  L57892315391.138L60098763854.3  L61397434406.7  L61399513874.8  L62338813384.3  L62908422684.140L62909071722.138L68648578258.2  L8463380018.138 P34030614239.155Q10649498890.150Q10649685048.151Q10650081102.149Q12757461271.150Q13734317171.149Q15930096381.150Q17525089906.152Q17525187323.150Q17701933584.150Q20741671226.152Q20880934901.150Q20881294204.152Q28496781288.154Q28498761192.155Q29850408660.150Q34390149656.150Q36349221533.147Q37216054521.152Q39600066516.150Q40016855704.150Q40016971031.147Q40017217041.152Q43608216472.147Q4451634193.155 Q4453582353.154 Q45355769223.151Q47135511895.155Q54050196007.150Q61556549392.153Q61847600945.150Q62944057836.150Q62944222565.152Q68390477037.15000000j01d02g03[04N05A05B05U06D06H06I06J06c07N07O07P08;0;40;_0<20<50=L0>c0?30?40?70@>0@H0@^0A70A@0BM0CZ0C`0DK0EM0Ei0FE0Fa0GA0G]0H60H70H80HT0I40I50I60Ia0JL0Je0Jf0KF0Ki0Kj0LP0M60M\0N50N`0OK0Og0PR0PS0Q80R40R50R60R_S2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCE2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCE2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR3END2lo2bs3LOS1j5nodes3cur1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes3cur1c2Hj3HCE4CPPa2HB5Ha_st5Hl_stS2PP3END3BUF2bs3DPB1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3CTX3END2bs3DXP1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stSS3END1j1c2Hj3HCE2J1S2sp2PP3CTX3CUR3END3BUF2bs1j5nodes3cur1c2Hj3HCES2PPFFS1R3HIA1h2sp2lo3TOP5HTOPcS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCEFFS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCES1R3HIA1h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m3mo02PP3CTX3CUR1P3END3BUF2lo2bs2hc2mm5nodes1c2Lw3tgw2x12x83x193x203x213x223x233x243x253x263x273x293x303x312Hj3HCES2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCES3END1j1c2Hj3HCE2J1S1cS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B33B472B54CUR04CTX01j5nodes3cur1c2Hj3HC03HCE2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B33B472B54CUR04CTX01j5nodes3cur1c2Hj3HC03HCE2C03SPRS3END1j1c2Hj3HCEFS1jS2sp2PP3CTX3CUR3END3BUF2bs3PP02B34CUR04CTX01j5nodes3cur1c2Hj3HCE2C03SPRS1R2lo3LOSS1P3END1j1c2Hj3HC03HCES1P3END1j1c2Hj3HC03HCE2J1S1j2Hj2KLS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B14CUR04CTX01j5nodes3cur1c2Hj3HC03HCE2C03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B14CUR04CTX01j5nodes3cur1c2Hj3HC03HCE2C03SPRS1j2HjS2sp2PP3CTX3CUR3END2bs1j5nodes3cur1c2Hj3HCES1R5NEED02sp2PP3END2lo2bs4PPLO3SLO1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCES3END3BUF2bs2B31j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCES3END2bs1j5nodes1c2Hj3HCEFFS2PP3END2bs1j5nodes1c2Hj3HCES3END3BUF2bs2B31j5nodes1c2Hj3HCEFFS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS3END2bs1j5nodes1c2Hj3HCEFS3END3BUF2bs2B31j5nodes1c2Hj3HCES2PP3END2bs3PP01j5nodes1c2Hj3HCE2HBFS1P3END3BUF2bs2B11j5nodes1c2Hj3HC03HCES1P3END3BUF2bs2B11j5nodes1c2Hj3HC03HCES1P3END3BUF2bs2B11j5nodes1c2Hj3HC03HCES3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stS2PP3END2bs1j5nodes1c2Hj3HCES2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_st5Hl_stFS2PP3END2bs1j5nodes1c2Hj3HCE2HB5Ha_stS2sp2PP3CTX3CUR3END2bs3ALP3PP04CTX01j5nodes3cur1c2Hj3HCE3SPRFFS1P3END3BUF2bs2B12B51j5nodes1c2Hj3HC03HCE". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma lenloop1_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pj,$4=.Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pc,$6.PLw,(2.&40.)Ptgw,(2.&40.)Px1,(2.&40.)Px8,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(8.(65.#1.R1;.)(65.R1;.#4.))P,(12.(1=.VP,+2.)R12.)P,(12.(1=.R13.(27.R1=.))VEND,)P,(58.R1<.R1=.R1;.R1:.R19.R18.R17.R16.R15.)P,(2:.$51.R1=.VPP,(1:.$2;.(2<.(10.&40.R15.))(1>.$2;.)))P,(12.(23.$51.VR,VHIA,R1?.)(1=.(23.$51.VR,VHIA,Vh,)(59.=$5:.)))P,(12.(25.$51.VR,VHIA,R20.)(1=.(25.$51.VR,VHIA,Vh,)(59.=(5;.=))))P,(12.(27.(28.$6.R1?.))=)(5<.$51.(5=.$51.VR,VHIA,R22.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R16.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,(10.&40.(1=.R19.+1.))(10.&40.R19.)R18.R15.(10.&40.(62.(56.VR,)))(10.&40.VPP,)(10.&40.VEND,)(10.&40.+??.)R17.(10.&40.=)(10.&40.=)(10.&40.$47.)(10.&40.VCTX,)(10.&40.(1=.(63.VPP,+3.)(62.(56.VR,))))R14.R13.R12.R11.R10.R?.R>.R=.R<.(10.&40.(27.R23.))R;.R:.R9.)VF,(10.&40.+99>3<.)Vfc,(>.(2.&40.))R21.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    induction j as [|j IH]; intros until x31; intros Hj HC0 HCE INV HPP BUDa BUDFa HLN; [lia|].
    open_inv_mu INV hc.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF c.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    get_byte bs (c - BUF) b NB. read_at HBUF NB (c - BUF) RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    do 5 zstep.
    rewrite (swrap32_id (Z.of_nat (S j) + -1)) by (clear - Hj; lia).
    fold_inv INV2 hc nodes cur ct cpad cl cp j0.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - idtac "LL1-ITER".
      replace (Z_to_bv 64 (Z.of_nat (S j) + -1)) with (Z_to_bv 64 (Z.of_nat j)) by (f_equal; clear; lia).
      replace (Z_to_bv 64 (c + 2)) with (Z_to_bv 64 (c + 1 + 1)) by (f_equal; clear; lia).
      assert (J1 : (1 <= j)%nat) by (clear - KL Hj; try kland KL; rewrite ?Z.mod_small in KL by lia; lia).
      eapply (IH hc _ nodes cur ct cpad cl cp j0 (c + 1));
        first [ exact INV2 | eassumption | clear - Hj J1 HC0 HCE; lia | match goal with |- ?g => idtac "LL1-IH-LEFT:" g end ].
    - idtac "LL1-DONE".
      (* [comment removed for export] *)
      zstep.
      eapply join1_walk with (q := c + 1);
        first [ exact INV2 | eassumption | clear - Hj HC0 HCE; lia | match goal with |- ?g => idtac "LL1-J1-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04N0@D28498761192.135D28498761192.146D28498761192.150D35881667587.111D35881667587.112D4451634193.135 D4451634193.146 D4451634193.150 D51794440367.111D51794440367.112D60109196847.135D60109196847.146D60109196847.150K15067692764.135K15067692764.146K15067692764.150K44164039966.135K44164039966.146K44164039966.150K56840826649.135K56840826649.146K56840826649.150L11668849344.103L11668954808.115L11670715342.112L12222146976.2  L12550742471.134L12551142084.132L12551142087.138L13098889560.103L13107166054.3  L14795424372.103L15082368954.2  L16070426553.143L16070426553.147L16108054177.139L16110150436.128L16603218173.110L1685717371.0   L16967042233.4  L16969368967.3  L1804587928.114 L18868739288.103L20806881524.103L2138888664.103 L21541644120.103L21991189007.114L21993419083.116L22269507015.3  L24150417681.132L25113361410.4  L26828156276.103L27081481460.2  L27111942217.1  L2759026548.103 L29834048600.103L3043381336.103 L30803094856.136L32855866356.103L34035016763.2  L35347804779.135L35609665496.103L35653441506.9  L37917982831.12 L38282648152.103L38866126964.103L39172636981.0  L39280637297.0  L39934434991.1  L40834179097.106L41202929119.104L41202929119.125L41202929119.136L41202929119.140L41679287937.3  L43057481256.105L43339676709.2  L4345510978.5   L43491718995.0  L44168742175.3  L44179762835.3  L44891662068.103L45674082520.103L46365646862.3  L46859059904.103L47401587060.103L47938282092.3  L47940377838.5  L49924178779.4  L50088985666.130L50091047489.124L50091499700.133L50091499700.139L508980326.124  L50903118708.102L52361663192.102L52753581537.3  L53271535775.125L53271535775.136L53271535775.140L53410279412.103L54106875608.103L54434390506.2  L55013023064.103L5548916134.5   L56380991837.7  L56826150901.2  L59438513268.103L59474218047.3  L60098763854.3  L60330452198.107L62018535662.1  L62417105880.103L63152446533.139L65110679799.3  L65451395828.103L66099488952.3  L690364601.4    L8769959412.103 L9816906285.124 L9817267360.103 P12226132804.111P12226132804.112P34030614239.135P34030614239.146P34030614239.150P43350158537.111P43350158537.112P44164039966.111P44164039966.112P54432297100.111P54432297100.112Q10649498890.110Q10649498890.132Q10649498890.143Q10649498890.147Q10649520692.146Q10649537205.131Q10649766968.109Q10651703251.142Q10732447889.123Q13074342371.143Q13074443200.142Q13074443201.146Q13074468991.137Q13076443006.140Q13076443006.146Q13733088494.142Q13734809865.146Q13734859144.131Q13735089925.109Q14633614404.111Q15063504633.140Q15063504633.146Q15597187341.111Q15643324129.107Q15930096381.121Q15930096381.140Q15930096381.146Q17701933584.110Q17701933584.132Q17701933584.143Q17701933584.147Q18365925601.108Q18378753154.108Q18694146040.111Q1954359180.121 Q20091533181.111Q20568046174.111Q21027042243.140Q21027042243.146Q21028779900.146Q21028779901.142Q21798041355.111Q21879645826.108Q2217915340.118 Q22318986966.111Q22318986966.112Q22712450012.111Q22712450012.112Q23733024212.123Q23733047272.118Q23735546217.121Q24389563138.108Q25157988860.111Q25513505925.110Q25513505925.111Q25662358575.111Q26611046992.111Q27584944865.108Q27907200258.108Q28496781288.134Q28496781288.145Q28496781288.149Q28498761192.135Q28498761192.146Q28498761192.150Q29505479905.108Q30415036802.108Q30485177150.146Q30485177151.142Q31228709292.111Q31271525473.108Q31394594844.111Q31407197753.137Q31407341477.143Q32655500769.108Q32871135979.140Q32871135979.146Q33185036414.111Q33918256002.108Q34390149656.110Q34390149656.132Q34390149656.143Q34390149656.147Q35014437530.111Q36425882626.108Q37216054521.132Q37216054521.143Q37216054521.147Q37343932385.123Q37345667932.121Q38069160682.111Q3830427394.108 Q39600066516.110Q39600066516.132Q39600066516.143Q39600066516.147Q39939554818.108Q41152393185.108Q43610462858.143Q43610598038.118Q43610598166.137Q44482882979.111Q44482882979.112Q4451634193.135 Q4451634193.146 Q4451634193.150 Q4453582353.134 Q4453582353.145 Q4453582353.149 Q44648843873.108Q4533518817.108 Q45353748076.142Q45355752839.109Q45355916042.131Q45355998091.146Q47135511895.135Q47135511895.146Q47135511895.150Q49698585326.109Q49698585326.110Q50387908578.111Q51235796833.108Q52101170785.108Q5257172243.140 Q5257172243.146 Q53711815251.108Q53711815251.109Q53969758199.111Q54050196007.110Q54050196007.132Q54050196007.143Q54050196007.147Q54485784450.108Q57351519894.121Q59256763233.108Q59843137889.108Q60511257090.108Q61556549392.133Q61556549392.144Q61556549392.148Q61847600945.110Q61847600945.132Q61847600945.143Q61847600945.147Q62641111670.121Q6416456232.111 Q65925244770.110Q65925244770.111Q66522067074.108Q6736239515.111 Q6736239515.112 Q9487243258.111 Q9487243258.112 Q9843367298.107 00000W01>01e02U03h04O05605]06f08R09B0:20:b0;E0;h0<K0<o0=S0>70>[0??0?c0@a0Ac0Be0Bf0CE0Cd0DC0DU0D^0E00E10EM0Ei0FI0Fi0Gg0Gh0Gi0Gj0Hb0I40IF0IX0Ij0JI0Jh0Ji0Ka0Kh0L:0LA0LE0LW0Li0M;0M<0MN0MO0Mg0N90NQ0Nb0O40OF0OG0OH0OK0O_0P10PI0Pa0Q90Q@0R30R40RD0RE0RF0RQ0Rc0S50S@0T80TJ0TM0TP0T[0U]0V_0Wa0Xc0Y?0YQ0Yc0Ym0ZE0Z]0[50[G0[Y0[Z0[l0\30\L0\M0\_0\j0]40]F0]I0][0^90^C0^U0^^0^_0_10`30a10aa0c40cj0d`0eV0fL0ge0hW0il0j^0l30l:0lG0lT0la0ln0m;0mB0mO0mg0n80nI0nZ0nk0o<0oM0oZ0og10410;10<10T10l10m11711A11K11U11\11i12612C12M12c12n13E13F13G13H13I13J13K13L13b14:14;14<14U15Q15b16316D16Z16e17A18@18A18B18L18b19>19Z1:61:R1:n1;J1;T1;j1<B1<Z1<f1=01=41=L1=d1=n1>E1>\1>]1?31?41?51?61?71?C1?Y1?m1@A1@U1@V1@W1@X1@n1@o1A01A11A21AH1AR1A\1Af1B01B`1D31DO1Dk1EG1Ec1F?1F[1Fe1Fo1G<1GC1GP1G]1H91HU1I11IE1IY1IZ1Id1In1J81JB1JL1JV1Jb1Jc1Jd1Je1Jf1K<1KT1K^1Kh1L>1LT1Lj1M@1Mc1NO1O;1Og1P11P<1Pd1Qo1RE1S51TH1TI1TJ1T`S2sp2PP3CTX3CUR1P3END2bs2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2PP3CTX3CUR2bs3TOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s02PP3CTX3CUR2bs3TOP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp2PP3CTX3CUR1P3END2bs2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END2bs2HB5Ha_st5Hl_stS1R5NEED02ra2sp2PP3CTX3CUR2lo2bs3PP04CUR04CTX03LOS3SLO3SPR2HB5Ha_st5Hl_stS1R5NEED02sp2s02PP3CTX3CUR2lo2bs3PP04CUR04CTX03LOS3SLO3SPR2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS2HB5Ha_st5Hl_stS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS2HB5Ha_st5Hl_stS2PP3CUR1P3END2bs2D12HB5Ha_st5Hl_stS2PP3CUR1P3END2bs2D12HB5Ha_st5Hl_stS2PP3CUR1P3END2bs2D12HB5Ha_st5Hl_stS2PP1P3END3BUF2bs3DPB2HB5Ha_st5Hl_stS2PP1P3END3BUF2bs3DPB2HB5Ha_st5Hl_stS2PP1P3END3BUF2bs3DPB2HB5Ha_st5Hl_stS2PP3CTX1P3END2bs3DXP2HB5Ha_st5Hl_stS2PP3CTX1P3END2bs3DXP2HB5Ha_st5Hl_stS2PP3CTX1P3END2bs3DXP2HB5Ha_st5Hl_stS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPRS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPR3P0LS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPR3P0LFS2sp2PP3CTX3CUR1P3END3BUF2bs2B1S2sp2PP3CTX3CUR1P3END3BUF2bs2B1S2sp2PP3CTX3CUR1P3END3BUF2bs2B1S2sp2PP3CTX3CUR2bsS1R3HIA1hS2sp2PP3CTX3CUR2bsFS2sp2PP3CTX3CUR1P3END3BUF2bsS2sp2PP3CTX3CUR1P3END3BUF2bsS2sp2PP3CTX3CUR1P3END2bs3Ka03Ka1S2sp2PP3CTX3CUR1P3END2bs3Ka03Ka1S2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPRSSSS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B22B34CUR04CTX03SPR3P0LS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR1P3END3BUF2bs2B1S2sp2PP3CTX3CUR1P3END3BUF2bs2B1SS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B22B34CUR04CTX03SPR3P1LS1P3ENDS2sp2PP3CTX3CUR2bsS2nn2HNS2PPS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsFS2sp2PP3CTX3CUR2bsFS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR2bsS1R3HIA1h2sp2lo3TOP4HTOPS1P3END2bs2nn3KgeS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsSSS1PS1R2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS1P3ENDS1R5NEED02sp2PP3CTX3CUR2lo2bs3PP04CUR04CTX03SLO3SPRFS1P3END2nn2HN2PNSFS1P3END3Kb0S2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsS1P3END3Ka0S1R5NEED02sp2PP3CTX3CUR2lo2bs3PP04PPLO4CUR04CTX03SLO3SPRS2sp2PP3CTX3CUR2bsS1PS1PS1P3END3P0LS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPR3P1LS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPR3P0LS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPR3P1LS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPR3P1LS2sp2PP3CTX3CUR1P3END3BUF2bsS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsS1P3END2B2S2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR2bsFS2sp2PP3CTX3CUR2bsS2nn2HNS1R3BUF2lo2bs3LOS3ALO3BCEFS2sp2PP3CTX3CUR2bsS1P3END3P1LS1R2lo3LOSS2sp2PP3CTX3CUR2bsS1RS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR1P3END2bs2nn2NRS1P3END2B2S2sp2PP3CTX3CUR2bsS1R3HIA1hSS2sp2PP3CTX3CUR2bsS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPR3P0LS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33B472B54CUR04CTX03SPRS1R5NEED02ra2sp2PP2lo2bs4PPLO3SLO2HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs4PPLO3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO2HB5Ha_st5Hl_stS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO2HB5Ha_st5Hl_stS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO2HB5Ha_st5Hl_stS1R5NEED02ra2sp3CTX2lo2bs5CTXLO3LOS3SLO2HB5Ha_st5Hl_stS1R5NEED02sp2s03CTX2lo2bs5CTXLO3LOS3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02ra2sp3BUF2lo2bs3SLO5BUFLO2HB5Ha_st5Hl_stS1R5NEED02sp2s03BUF2lo2bs3SLO5BUFLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02ra2sp3CUR2lo2bs5CURLO3SLO2HB5Ha_st5Hl_stS1R5NEED02sp2s03CUR2lo2bs5CURLO3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2PP2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP2bsS2PP1P3END2bsS1P3END3BUF2bs2B22B33P0LS1P3END3BUF2bs2B1S1P3END3BUF2bs2B1S1P3END3BUF2bs2B1S1P3END3BUF2bs2B1S1P3END3BUF2bs2B1S1P3END3BUF2bs2B1S2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP2bsFS1P3END3BUF2bs2B22B33P1LS1P3END3BUF2bs2B22B33P1LFS2sp2lo2bsS1P3END2bsS1P3END2bsS1P3END2bsS2PP2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2sp2lo2bsS1R5NEED02sp2lo2bs3SLOS1R2bs4IMG'S1P3END3BUF2bs2B12B22B5FFFFFFFS1R5NEED02sp2lo2bs3SLOS1P3END3BUF2bs2B22B33P0LFFS2ra2sp2bs2HB5Ha_st5Hl_stS2sp2s02bs2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1P3END3BUF2bs2B1S1P3END3BUF2bs2B1S1P3END3BUF2bs2B1S1R5NEED02sp2lo2bs3SLOS1R2bs4IMG'S2ra2sp2lo2bs2HB5Ha_st5Hl_stS2sp2s02lo2bs2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FFS2sp2lo2bsS1R5NEED02sp2lo2bs3SLOS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2sp2lo2bsS1R5NEED02sp2lo2bs3SLOS1P3END3BUF2bs2B22B33P1LS1P3END3BUF2bs2B22B33P1LS1R2bs5ALWF'S2sp2lo2bsS2bsS1P3END3BUF2bs2B22B33P1LS1P3END3BUF2bs2B22B33P1LS2sp2lo2bsS1P3END3BUF2bs2B12B22B5S1P3END3BUF2bs2B12B22B5FS1R5NEED02sp2lo2bs3SLOFFFFS1R2bs5ALWF'S1R5NEED02sp2lo2bs3SLOS2PP1P3END2bs3PP02HBS2PP1P3END2bs3PP02HBS2PP1P3END2bs3PP02HBFFFS1R5NEED02sp2lo2bs3SLOFFFFS1R5NEED02sp2lo2bs3SLOS2sp2lo2bsS1P3END2bsS1P3END2bsS1P3END2bsS1R5NEED02ra2sp2PP2lo2bs4PPLO3SLO2HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs4PPLO3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2sp2lo2bsS2sp2lo2bsS2PP1P3END2bsS2PP2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2PP1P3END2bs2HB5Ha_st5Hl_stS2sp2bs3SPR2HB5Ha_stS2sp2bs3SPR2HB5Ha_stFS2sp2lo2bsS2sp2lo2bsS1P3END2bsS1P3END2bsS2sp2bs2HBS2sp2bs2HBS1R2bs5ALWF'FFFFS1R5NEED02sp2lo2bs3SLOS1P3END3BUF2bs2B22B33P0LS2sp2lo2bsS2sp2lo2bsS1R5NEED02sp2lo2bs3SLOS2PP1P3END2bs2HB5Ha_stS2PP1P3END2bs2HB5Ha_stS2PP1P3END2bs2HB5Ha_stS2sp2PP3CTX3CUR2bs3ALP3PP04CTX03SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX03SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX03SPRS2sp2PP3CTX3CUR1P3END2bs3ALP3PP02B24CTX03SPRS1P3END2bsS1R2bs4IMG'S1R5NEED02ra2sp2lo2bs3SLO2HB5Ha_st5Hl_stS1R5NEED02sp2s02lo2bs3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02sp2lo2bs3SLOS1R5NEED02ra2sp2lo2bs3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R5NEED02sp2s02lo2bs3LOS3SLO3ALO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FFS1R5NEED02sp2lo2bs3SLO". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma trav_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Pct,(2.&40.)Pcpad,(2.&40.)Ptgw,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(39.$51.VR,VHIA,Vh,VLB,VLF,Vm,)P,(21.$51.VR,VHIA,Vh,Vmo0,)P,(2:.$51.Vm,VPP,(1:.$2;.(2<.(10.&40.VP,))(1>.$2;.)))P,(2:.$51.Vm,VCUR,(2=.R=.R<.===))P,(2:.$51.Vm,(1=.VCTX,+8.)(1:.$2;.(2<.(10.&40.VCUR,))(1>.$2;.)))P,(40.$51.Vm,VBUF,Vbs,)P,(14.$51.Vm,Vlo,(15.&40.Vsp,))P,(13.$51.Vm,)P,(3<.$51.(56.VR,)(22.$51.VR,VHIA,Vh,)Vm,VPP,+8.)P,(3<.$51.(56.VR,)(22.$51.VR,VHIA,Vh,)Vm,VCUR,+20.)P,(3<.$51.(56.VR,)(22.$51.VR,VHIA,Vh,)Vm,(1=.VCTX,+8.)+8.)(48.$51.(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(:.(;.(<.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(10.&40.VPP,)(10.&40.VEND,)(10.&40.+??.)R13.(10.&40.=)(10.&40.=)(10.&40.$47.)(10.&40.VCTX,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(10.&40.$66.)Vfc,(>.(2.&40.))Vm,(?.$51.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HK0 HPP HCUR HCTX HBUF ST MI OPP OCUR OCTX. unfold A_ASN1_TRAV.
    rt_facts h.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SLO NEED0 TOP HTOP; lia]).
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) X HH ltac:(clear; lia)) as PRES.
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCP : wcover R LB LF (bv_unsigned sp) X PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
    unfold seq_cells in HCUR.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    zstep. carve_frame 112%nat ST.
    do 13 zstep.
    idtac "T-SAVED".
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB end end.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB.
    rewrite (proj1 IMG') in GOT.
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    do 6 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -112) (CB 8 ?jj :: _) |- _ => set (j0 := jj) in *; clearbody j0 end.
    assert (INV : tinv m1 h [] CUR ct cpad 0 0 j0).
    { unfold tinv. spine; first [ eassumption | reflexivity | exact I
        | lazymatch goal with
          | |- List.NoDup [] => constructor
          | |- forall x, CS x -> _ => intros x Hx; exact Hx
          | |- forall x, In x [] -> _ => intros x []
          | |- _ \/ _ => left; repeat split; reflexivity
          end
        | match goal with |- ?g => idtac "T-INV-LEFT:" g end ]. }
    assert (HE00 : 0 <= 0 <= (END - P) / 2) by (split; [clear; lia| apply Z.div_pos; [clear - B2; lia| clear; lia]]).
    assert (B0 : havol asegs R HIA h <= havol asegs R HIA h + 0 * ASN1_SEQ_CB_PHI) by (clear; lia).
    assert (BF0 : hfr asegs R HIA h <= hfr asegs R HIA h + 0 * fr_charge 0) by (clear; lia).
    assert (LN0 : Z.of_nat (length (@nil Z)) <= 0) by (cbn; clear; lia).
    zstep. if_cases Ka; zify_cond Ka.
    { idtac "T-OOD0".
      do 2 zstep.
      eapply exit_walk with (e := 0) (r := -96) (p' := P); first [ exact INV | eassumption | clear - B2; lia | match goal with |- ?g => idtac "T-OOD0-LEFT:" g end ]. }
    assert (P0L : P < END) by (match goal with H : 0 < END - P |- _ => clear - H; lia end).
    idtac "T-TAG".
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF P.
    (* [comment removed for export] *)
    get_byte bs (P - BUF) b0 NB0. read_at HBUF NB0 (P - BUF) RD0.
    zstep. clear RD0. zstep.
    zstep. if_cases Kt; zify_cond Kt.
    { idtac "T-BADTAG".
      zstep.
      eapply exit_walk with (e := 0) (r := -98) (p' := P); first [ exact INV | eassumption | clear - B2; lia | match goal with |- ?g => idtac "T-TAG-LEFT:" g end ]. }
    clear Kt.
    idtac "T-LEN".
    (* [comment removed for export] *)
    pose proof (munch_refl [(PP, PP + 8)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    ddestruct INV as (_ & HCSc & HTc & HSc & HFc & HND & HNF & HSR & _ & HCB & _).
    do 5 zstep.
    fold_inv INV1 h (@nil Z) CUR ct cpad 0 0 j0.
    zstep. if_cases Kb; zify_cond Kb.
    { idtac "T-OOD1".
      do 2 zstep.
      eapply exit_walk with (e := 0) (r := -96) (p' := P + 1); first [ exact INV1 | eassumption | clear - B2 P0L; lia | match goal with |- ?g => idtac "T-OOD1-LEFT:" g end ]. }
    assert (P1L : P + 1 < END) by (match goal with H : 0 < END - (P + 1) |- _ => clear - H; lia end).
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF (P + 1).
    (* [comment removed for export] *)
    get_byte bs (P + 1 - BUF) b1 NB1. read_at HBUF NB1 (P + 1 - BUF) RD1.
    zstep. clear RD1.
    zstep. if_cases Ksg; zify_cond Ksg.
    - idtac "T-LONG".
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      2:{ idtac "T-INVLEN".
          do 2 zstep.
          eapply exit_walk with (e := 0) (r := -100) (p' := P + 1); first [ exact INV1 | eassumption | clear - B2 P0L; lia | match goal with |- ?g => idtac "T-INVLEN-LEFT:" g end ]. }
      idtac "T-LONG2".
      pose proof (P_asn1_get_tag.land_127_range (bv_unsigned (sxb b1))) as NR.
      set (nn := Z.land (Z.land (bv_unsigned (sxb b1)) 255) 127) in *.
      assert (HN : 1 <= nn <= 4) by (clear - NR Kn; apply P_asn1_get_tag.longform_n; [exact NR| exact Kn]).
      clearbody nn. clear Kn.
      (* [comment removed for export] *)
      zstep. if_cases Kge; zify_cond Kge.
      { idtac "T-OOD2".
        do 2 zstep.
        eapply exit_walk with (e := 0) (r := -96) (p' := P + 1); first [ exact INV1 | eassumption | clear - B2 P0L; lia | match goal with |- ?g => idtac "T-OOD2-LEFT:" g end ]. }
      assert (PN : P + 2 + nn <= END) by (clear - Kge HN P1L B1 B3 B5 B47; try kland Kge; rewrite ?Z.mod_small in Kge by lia; lia).
      clear Kge.
      (* [comment removed for export] *)
      do 6 zstep.
      fold_inv INV2 h (@nil Z) CUR ct cpad 0 0 j0.
      replace (Z_to_bv 64 nn) with (Z_to_bv 64 (Z.of_nat (Z.to_nat nn))) by (f_equal; clear - HN; lia).
      replace (Z_to_bv 64 (P + 3)) with (Z_to_bv 64 (P + 2 + 1)) by (f_equal; clear; lia).
      idtac "T-LOOP1".
      eapply lenloop1_walk with (j := Z.to_nat nn) (c := P + 2);
        first [ exact INV2 | eassumption | clear - HN PN; lia | match goal with |- ?g => idtac "T-LL1-LEFT:" g end ].
    - idtac "T-SHORT".
      (* [comment removed for export] *)
      do 4 zstep.
      shadow_chk1 OBUF (P + 1).
      (* [comment removed for export] *)
      read_at HBUF NB1 (P + 1 - BUF) RD2. zstep. clear RD2.
      fold_inv INV2 h (@nil Z) CUR ct cpad 0 0 j0.
      eapply join1_walk with (q := P + 2);
        first [ exact INV2 | eassumption | clear - P1L; lia | match goal with |- ?g => idtac "T-J1-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  #[using="IMG NEED0 CBSPEC"] Theorem A_asn1_trav_spec : asn1_trav_stmtA asegs R HIA A_ASN1_TRAV.
  Proof.
    unfold asn1_trav_stmtA. intros until cpad. intros; subst.
    eapply trav_walk with (bs := bs) (ct := ct) (cpad := cpad); first [eassumption | reflexivity].
  Qed.
End Walk.

(* [comment removed for export] *)
