(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts
     A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_seq_cb A_x509_seq_stmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import LxConv_getlen LxConv_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_asn1_trav () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "TRAV_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "TRAV_FFR"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.hd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.SSEQ"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.SEQ_SIZE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "TRAV_STK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_seq_cb.A_ASN1_SEQ_CB"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "Stmt.asn1_trav_postA"; "Stmt.seqrep"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.removelast"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Walk.Call.nLB"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Walk.Call.nodeF"; "seqrep"; "Walk.Call.curP"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Walk.Call.tinv"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_seq_cb.ASN1_SEQ_CB_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "asn1_trav_postA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.Lists.List.last"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Walk.Call.LoopOblig"; "Corelib.Init.Peano.le"; "A_ASN1_TRAV"].


Definition A_ASN1_TRAV : Z := 0x09a1d8.       (* [comment removed for export] *)

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
  Definition asn1_trav_stmtA (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Ph,(5.Vsegs,VR,VHIA,)PLB,(7.$33.)PLF,(7.$33.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPP,$6.PCTX,$6.PCUR,$6.PP,$6.PEND,$6.PBUF,$6.Plo,$6.Pbs,(7.(2.&8.))Pct,(2.&40.)Pcpad,(2.&40.)P,(39.Vsegs,VR,VHIA,R30.R2?.R2>.R<.)P,(21.Vsegs,VR,VHIA,R31.R<.)P,(2:.Vsegs,R>.R<.(1:.$2;.(2<.(10.&40.R9.))(1>.$2;.)))P,(9.$6.(3;.R=.+8.)=)P,(11.=R>.)P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R35.)R11.R?.+8.)P,(3=.(3>.VR,)(32.$33.R35.(3?.R34.))R:.(1?.Vsegs,VR,VHIA,R36.)R10.+8.)P,(12.(1=.R11.+8.)R;.)P,(40.Vsegs,R14.R=.R;.)P,(37.(1;.$6.$6.)(1<.$6.$6.R>.(27.(28.(2.&8.)R<.)))R38.)P,(12.R?.R11.)P,(12.R12.R11.)P,(12.R12.(1=.R11.(27.(28.(2.&8.)R?.))))P,(11.(1=.R12.(27.(28.(2.&8.)R10.)))(41.+2.+2?.))P,(11.=R13.)P,(2>.(12.(1=.R19.+8.)R14.)(12.(1=.R14.(27.(28.(2.&8.)R12.)))R19.))P,(2:.Vsegs,R1<.R18.(2=.R12.R11.===))P,(9.$6.(3;.R19.+8.)=)P,(11.=R1:.)P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R43.)R1?.R1;.+20.)P,(3=.(3>.VR,)(32.$33.R43.(3?.R42.))R18.(1?.Vsegs,VR,VHIA,R44.)R1<.+20.)P,(12.(1=.R1=.+20.)R19.)P,(2>.(12.(1=.R1>.+20.)R1;.)(12.(1=.R1;.(27.(28.(2.&8.)R19.)))R1>.))P,(2>.(12.(1=.R21.+8.)R1?.)(12.(1=.R1?.+20.)R21.))P,(2:.Vsegs,R24.(1=.R21.+8.)(1:.$2;.(2<.(10.&40.R20.))(1>.$2;.)))P,(9.$6.(3;.(1=.R22.+8.)+8.)=)P,(12.=R23.)P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R4;.)R27.(1=.R24.+8.)+8.)P,(3=.(3>.VR,)(32.$33.R4;.(3?.R4:.))R20.(1?.Vsegs,VR,VHIA,R4<.)(1=.R25.+8.)+8.)P,(12.(1=.R26.+10.)(18.VR,))P,(2>.(12.(1=.R27.+10.)R23.)(12.(1=.R23.(27.(28.(2.&8.)R21.)))(1=.R27.+8.)))P,(2>.(12.(1=.R29.+8.)(1=.R28.+8.))(12.(1=.R28.+10.)R29.))P,(2>.(12.(1=.R29.+10.)R28.)(12.(1=.R28.+20.)(1=.R29.+8.)))P,(14.Vsegs,R2=.R25.(15.&40.R4=.))P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R52.)R2>.(42.(15.&40.R4>.)+70.)+8.)P,(12.(18.VR,)R27.)P,(12.R28.(42.(15.&40.R50.)(43.VR,)))P,(12.(15.&40.R51.)(1?.Vsegs,VR,VHIA,R55.))P,(9.$6.(3;.(15.&40.R52.)+10.)=)P,(13.Vsegs,R33.)P,(9.(2.&40.)R52.(10.&40.(44.VR,)))P,(12.(1=.(23.Vsegs,VR,VHIA,R59.)(24.(42.R2?.R30.)))$45.)P,(12.(1=.(25.Vsegs,VR,VHIA,R5:.)(26.(42.R30.R31.)))$46.)P,(9.(2.&40.)R4?.(10.&40.R35.))P,(9.(2.&40.)R4?.(10.&40.R32.))P,(9.(2.&40.)R4?.(10.&40.+??.))P,(9.(2.&40.)R4>.(10.&40.=))P,(9.(2.&40.)R4>.(10.&40.=))P,(9.(2.&40.)R4>.(10.&40.$47.))P,(9.(2.&40.)R4>.(10.&40.R3:.))(48.Vsegs,(49.R62.R61.R60.R5?.R5>.R5=.R5<.R58.R57.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R40.R3?.R3<.R3;.R3:.R39.R38.R37.(42.R38.R39.)R36.R3>.R3=.)(:.(;.(<.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.)R40.(10.&40.O1.)R3?.(>.(2.&40.))R3>.(?.Vsegs,))R3=.))")
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
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.

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
  Definition tinv (mm : mem) (hc : HST asegs R HIA) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "(8.(39.$51.VR,VHIA,O8.(50.O7.)VLF,O9.)(8.Px,$6.P,(22.$51.VR,VHIA,Vh,R1.)(22.$51.VR,VHIA,O8.R2.)(8.(9.$6.(1?.$51.VR,VHIA,O8.)(1?.$51.VR,VHIA,Vh,))(8.(9.$6.(19.$51.VR,VHIA,O8.)(19.$51.VR,VHIA,Vh,))(8.(9.$6.(20.$51.VR,VHIA,O8.)(20.$51.VR,VHIA,Vh,))(8.(36.$6.O7.)(8.Px,$6.P,(37.$6.R1.O7.)(52.R2.)(8.(53.$51.O9.(50.O7.)VBUF,VEND,VCUR,O7.O6.)(8.(2:.$51.O9.O6.(2=.O5.O4.O3.O2.=))(8.(2>.(8.(9.$6.O2.=)(8.(9.$6.O3.=)(9.(7.$6.)O7.(1>.$6.))))(8.(12.VBUF,O2.)(8.(12.=O3.)(12.(1=.O2.O3.)VEND,))))(8.(2:.$51.O9.(1=.VCTX,+8.)(1:.$2;.(2<.(10.&40.O6.))(1>.$2;.)))(8.(2:.$51.O9.(1=.(15.&40.Vsp,)-70.)(1:.$2;.(2<.O1.)(1:.$2;.(2<.Vs11,)(1:.$2;.(2<.Vs10,)(1:.$2;.(2<.Vs9,)(1:.$2;.(2<.Vs8,)(1:.$2;.(2<.Vs7,)(1:.$2;.(2<.Vs6,)(1:.$2;.(2<.Vs5,)(1:.$2;.(2<.Vs4,)(1:.$2;.(2<.Vs3,)(1:.$2;.(2<.Vs2,)(1:.$2;.(2<.Vs1,)(1:.$2;.(2<.Vs0,)(1:.$2;.(2<.Vra,)(1>.$2;.))))))))))))))))(8.(14.$51.O9.Vlo,(1=.(15.&40.Vsp,)-70.))(8.(13.$51.O9.)(8.(40.$51.O9.VBUF,Vbs,)(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.VPP,+8.)(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.VBUF,(27.(28.(2.&8.)Vbs,)))(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.(1=.VCTX,+8.)+8.)(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.VCUR,+20.)(8.(3<.$51.(56.VR,)(22.$51.VR,VHIA,O8.)O9.(1=.(15.&40.Vsp,)-70.)+8.)(57.$51.VR,VHIA,O8.VLB,VLF,(15.&40.Vsp,)(18.VR,)(1:.(1;.$6.$6.)(1<.$6.$6.VPP,(1=.VPP,+8.))(1:.(1;.$6.$6.)(1<.$6.$6.VCUR,(1=.VCUR,+20.))(1:.(1;.$6.$6.)(1<.$6.$6.(1=.VCTX,+8.)(1=.VCTX,+10.))(1>.(1;.$6.$6.)))))Vm,O9.)))))))))))))))))))))")
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
    destruct INV as (HHc & HCSc & HTc & HSc & HFc & HND & HNF & HSR & HCURC & HCB & HCTX & FRM & STK & MI & HBUF & OPP & OBUF & OCTX & OCUR & OSLOT & PRES);
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0190@L11093748225.154L13098889560.145L18868739288.145L2138888664.145 L21541644120.145L24626469156.9  L24628566308.9  L27111942217.1  L28359040934.6  L29834048600.145L3043381336.145 L35609665496.145L35655538583.9  L38282648152.145L45674082520.145L48479123582.155L52361663192.145L54106875608.145L55013023064.145L60098763854.3  L62417105880.145Q10446337025.155Q1089777154.155 Q1248400641.155 Q14451378945.155Q15636006274.155Q15647600541.155Q18361649565.155Q18382898686.155Q21653107202.155Q21892278270.155Q24385319550.155Q26098498177.155Q27597577117.155Q27655643266.155Q27911476350.155Q29501203869.155Q30294576897.155Q30402535678.155Q31258893597.155Q32659612829.155Q32741662593.155Q33674845442.155Q33914012414.155Q34295432705.155Q36438515070.155Q36744615553.155Q3834572414.155 Q39935311742.155Q41139760797.155Q44652956445.155Q4546183325.155 Q45732231170.155Q45925774721.155Q48223171714.155Q51223295517.155Q51749328514.155Q52105414429.155Q54242484482.155Q54481540862.155Q56592851329.155Q57751864066.155Q59244229149.155Q59321760001.155Q59830472733.155Q60276367234.155Q60498756478.155Q63324712961.155Q63771062658.155Q66295680002.155Q66534732286.155Q7719533697.155 Q9839090942.155 00000R01401V02802Z03703S03W03n04P05205T05m06O07108:08\09>09`09j0:L0:M0:`0:a0:b0;50;K0;a0<F0<Y0=>0=c0=d0>:0>M0?20?H0?I0?n0@D0@Z0@[0@n0AS0AT0B90B:0B_0CD0CZ0D00DF0DY0DZ0Dm0EC0EV0El0F?0Fd0Fe0G80GN0GO0Ge0H80H]0H^0I10ID0Ii0Ij0JOS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R3HIA1h1P3END2hc1e2HE5BUDFaS1R3HIA1h1P3END2hc1e2HE4BUDaS2PPS1P3END5nodes1e2HE4HLENS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R3HIA1h2sp2lo3TOP5HTOPcS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R5NEED02sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03SLO5nodes3cur2C03SPRS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R2lo3LOSS2sp2PP3CTX3CUR1P3END2bs5nodes3curFS2sp1P3END2bs5nodesFFS2sp1P3END2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesFS2sp1P3END2lo2bs5nodesS2sp1P3END2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesFS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesFS2sp1P3END2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesFS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesFS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2bs5nodesFS2sp1P3END2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesFS2sp1P3END2bs5nodesS2sp1P3END2lo2bs5nodesFS2sp1P3END2lo2bs5nodesS2sp1P3END2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesFS2sp1P3END2bs5nodesS2sp1P3END2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesFS1R5NEED02sp1P3END2lo2bs2B23SLO5nodes". (* [comment removed for export] *)
  #[using="IMG NEED0 PP0 CWP BIN B2 ALC CUR0 CWC CURLO DCB D1 CTX0 DXC LOS SLO TOP"] Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_trav ()) "Phc,(5.$51.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pnodes,(7.$6.)Pcur,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(2.&40.)Pe,$6.Pr,$6.Pp',$6.Px1,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px5,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(58.R26.R27.R25.R24.R23.R22.R21.R20.R1?.)P,(2:.$51.R27.VPP,(1:.$2;.(2<.(10.&40.R1=.))(1>.$2;.)))P,(8.(12.VP,R1>.)(12.R1>.VEND,))P,(8.(11.-3000.R20.)(12.R20.=))P,P,(9.$6.R21.=)(9.$6.R21.VEND,)P,(8.(12.=R23.)(12.R23.(29.(42.VEND,VP,)+2.)))P,(12.(23.$51.VR,VHIA,R2=.)(1=.(23.$51.VR,VHIA,Vh,)(59.R24.$5:.)))P,(12.(25.$51.VR,VHIA,R2>.)(1=.(25.$51.VR,VHIA,Vh,)(59.R25.(5;.=))))P,(12.(27.(28.$6.R2=.))R26.)(5<.$51.(5=.$51.VR,VHIA,R30.Vmo0,)(5>.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCTX,VCUR,VP,VEND,VBUF,(42.VEND,VP,)Vlo,Vm,Vmo0,)(;.(<.R24.(10.&40.(1=.(15.&40.Vsp,)-70.))Vgp,Vtp,R1>.R23.R22.R21.R20.R1?.(10.&40.R26.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(10.&40.+9:3<4.)Vfc,(>.(2.&40.))R2?.(?.$51.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HPP Hp' RR HEND HE BUDa BUDFa HLEN.
    open_inv INV hc.
    do 16 zstep.
    release_frame FRM STK (bv_unsigned sp).
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0@L10837002389.2  L11865810590.5  L12638084075.5  L12654381620.1  L17860490787.7  L19002552252.25 L22706556809.5  L23327695577.7  L23615739305.3  L26061550921.25 L2676165540.3   L27111942217.1  L27356735122.8  L33306264495.25 L35655538583.9  L3582028444.1   L36471176264.6  L37323683604.9  L37714553091.1  L38383890888.1  L39280637297.0  L41448345567.11 L42268239257.8  L43876917036.5  L44052539574.1  L4449834141.10  L4462386950.5   L46883672865.0  L48065260594.2  L48476763649.5  L51643361202.165L51828132648.8  L52840045532.7  L55628717916.1  L56454306668.25 L57628700040.4  L57628700040.5  L59314923118.2  L60044334350.3  L60098763854.3  L6133078798.8   L61564981147.11 L62018535662.1  L62658486538.3  L64700576064.13 L66151427842.16 L6746078414.6   L7036479304.1   00000800L00b00g01;01P01a01m02702Q02^02b03>03U03n04204I04l04o05405505X06606K06P07307F07G07N07a08J08n09I09L0:=0:K0:\0:a0:n0;80;R0<30<60<C0<i0=C0=]0=aS3BUF2bsS1R3CTX2lo5CTXLO3LOSS3CTX3CUR3DXC3cur4NCURS3BUFS1R3CTX2lo5CTXLO3LOSS2bs2j04tagb4Htag3lenS2PP3CTX3CUR1x2HxS2lo3cur3CLOS1R3HIA2hcS1R3HIA1h2sp2bs3TOP2j03lenS5nodes1e3HLNS2PPS1R3HIA1h2hc1e5BUDFa2h'4HFR'S1R2sp2lo2bs3SLO2j03lenS1R3HIA1h2sp2lo3TOP5HTOPcS2spS1R5NEED02sp2lo3LOS3SLOS1R5NEED02sp2lo3LOS3SLO3ALO3ACV3SPRS1AS3curSS1R3HIA1h1P3END2hc1e3HE15BUDFa4BUDFS3END3BUF2B55nodes2cl2cp1K3CP0S2PP3CTX3DXP3cur4CPPaS3curS1R3CTX2lo5CTXLO3LOS3cur3CLO1A1k2HAS3CTX3cur1A2OA4NCTXSS1e3HLNS1R5NEED02sp2lo3SLOS2sp2PP3CTX3CUR1P3END2bs5nodes3cur2j03lenS3END3BUF2j05start4HST03len3HSE4HLENS1R5NEED02sp2lo3LOS3SLO3ALOS1AS3END3BUF2bs2B33B472B52j05start4HST03len3HSE4HLENS3CTX3cur1x2HxS2PP3CTX3CUR1x2HxS1N1KS5nodes1e3HLNS1R2lo3LOSS1R3HIA1h2hc1e4BUDa2h'3HV'S1R3HIA1h1P3END2hc1e3HE14BUDa3BUDS1RS1R3CTX5CTXLOS3END3BUF2bs2B33B472B55nodes2cl2cp3HCBS2sp2r03SPA1q1r1H2H02q02H4S3CTX3BUF2bs3DXB3cur5CBUFaS2sp". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC CWP PPLO BIN B3 B47 B5 ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV"] Lemma cb_step :
    forall (hc : HST asegs R HIA) (mm : mem) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : word)
           (p tagb start e : Z)
           (x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 S0 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word),
      tinv mm hc nodes cur ct cpad cl cp j0 ->
      rw_cells asegs mm PP [C8 (Z_to_bv 64 p)] ->
      0 <= tagb < 256 -> BUF <= start -> start + bv_unsigned j0 <= END ->
      0 <= e -> e + 1 <= (END - P) / 2 ->
      havol asegs R HIA hc <= havol asegs R HIA h + e * ASN1_SEQ_CB_PHI ->
      hfr asegs R HIA hc <= hfr asegs R HIA h + e * fr_charge 0 ->
      Z.of_nat (length nodes) <= e ->
      havol asegs R HIA h + TRAV_PHI (END - P) <= AVOL_MAX ->
      hfr asegs R HIA h + TRAV_FFR (END - P) <= FR_MAX ->
      (forall (hc' : HST asegs R HIA) (mm' : mem) (nodes' : list Z) (cur' : Z) (ct' cpad' : word) (cl' cp' r : Z)
              (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
         r = 0 \/ r = -106 ->
         tinv mm' hc' nodes' cur' ct' cpad' cl' cp' j0 ->
         rw_cells asegs mm' PP [C8 (Z_to_bv 64 p)] ->
         havol asegs R HIA hc' <= havol asegs R HIA h + (e + 1) * ASN1_SEQ_CB_PHI ->
         hfr asegs R HIA hc' <= hfr asegs R HIA h + (e + 1) * fr_charge 0 ->
         Z.of_nat (length nodes') <= e + 1 ->
         aevtA asegs (KF asegs R HIA hc' mo0) POST
           (MS (mkR (Z_to_bv 64 0x9a374) SPT gp tp y5 y6 y7 S0 (Z_to_bv 64 A_ASN1_SEQ_CB) (Z_to_bv 64 r)
                    y11 y12 y13 y14 y15 y16 y17 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 y28 y29 y30 y31)
               F (Z_to_bv 64 0x9a374) fc None mm' (seg_rom asegs))) ->
      aevtA asegs (KF asegs R HIA hc mo0) POST
        (MS (mkR x1 SPT gp tp x5 x6 x7 S0 (Z_to_bv 64 A_ASN1_SEQ_CB) (Z_to_bv 64 CTX) (Z_to_bv 64 tagb) (Z_to_bv 64 start)
                 j0 x14 x15 x16 x17 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9a370) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until S11. intros INV HPP Htag HST0 HSE HE0 HE1 BUDa BUDFa HLN BUD BUDF KONT.
    pose proof (bv_unsigned_in_range 64 j0) as HLEN. unfold bv_modulus in HLEN. cbn [Z.pow Z.of_N Pos.pow] in HLEN. set (len := bv_unsigned j0) in *.
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
                end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m' & mo' & h' & r
                    & E4 & MI' & ST' & MF' & WM' & HPc & HT' & HS' & HF' & HK' & HCS' & HV' & HFR' & CASES).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0x9a374)) with (Z_to_bv 64 0x9a374 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
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
    assert (OSLOT' : aobj asegs AL (hcs asegs R HIA h') m' (bv_unsigned sp + -112) 8).
    { eapply aobj_cs_mono; [exact HCS'|]. eapply (presA_aobj asegs R); [exact CSOK| exact HPc| exact OSLOT| apply client_range_stack; clear; lia| clear - LOS SLO NEED0; lia| exact TOPCS]. }
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
    pose proof (eq_trans HT' HTc) as HTh'. pose proof (eq_trans HS' HSc) as HSh'. pose proof (eq_trans HF' HFc) as HFh'.
    assert (BUD1 : havol asegs R HIA h' <= havol asegs R HIA h + (e + 1) * ASN1_SEQ_CB_PHI) by (clear - HV' BUDa; lia).
    assert (BUDF1 : hfr asegs R HIA h' <= hfr asegs R HIA h + (e + 1) * fr_charge 0) by (clear - HFR' BUDFa; lia).
    destruct CASES as [(-> & CP0 & HH' & HCTX' & (pad' & HCUR')) | [(N & -> & CPN & N16 & NFR & _ & HH' & HCTX' & HCUR' & HN') | (-> & CPN & HH' & HCTX' & HCUR')]].
    - (* [comment removed for export] *)
      assert (NE : nodes = []) by (clear - HCB CP0 B5; destruct HCB as [(_ & _ & E)|K]; [exact E| lia]).
      subst nodes. cbn in SR'. subst cur.
      eapply KONT with (hc' := h') (mm' := m') (nodes' := @nil Z) (cur' := CUR) (ct' := Z_to_bv 64 tagb) (cpad' := pad') (cl' := len) (cp' := start) (r := 0);
        [left; reflexivity| | exact HPP| exact BUD1| exact BUDF1| clear - HLN; cbn [length] in *; lia| exact (conj HK' (mo_frame_trans _ _ _ MF1 MF'))].
      unfold tinv. spine; first [ eassumption | reflexivity | exact HCSh' | exact I
        | lazymatch goal with
          | |- _ \/ _ => right; clear - HST0 HLEN HSE; lia
          | |- aobj _ _ _ _ BUF _ => exact (hm_aobj_block asegs R HIA h' _ _ m' BUF n HH' (nLB_sub _ _ BIN))
          end ].
    - (* [comment removed for export] *)
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
          end ].
    - (* [comment removed for export] *)
      eapply KONT with (hc' := h') (mm' := m') (nodes' := nodes) (cur' := cur) (ct' := ct) (cpad' := cpad) (cl' := cl) (cp' := cp) (r := -106);
        [right; reflexivity| | exact HPP| exact BUD1| exact BUDF1| clear - HLN; lia| exact (conj HK' (mo_frame_trans _ _ _ MF1 MF'))].
      unfold tinv. spine; first [ eassumption | reflexivity | exact HCSh'
        | lazymatch goal with
          | |- aobj _ _ _ _ BUF _ => exact (hm_aobj_block asegs R HIA h' _ _ m' BUF n HH' (nLB_sub _ _ BIN))
          end ].
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
  Definition LoopOblig (p : Z) (tgw : word) : Prop :=
    forall (hc : HST asegs R HIA) (mm : mem) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : word) (e : Z)
           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
      tinv mm hc nodes cur ct cpad cl cp j0 ->
      rw_cells asegs mm PP [C8 (Z_to_bv 64 p)] ->
      0 <= e -> 2 * e <= p - P ->
      havol asegs R HIA hc <= havol asegs R HIA h + e * ASN1_SEQ_CB_PHI ->
      hfr asegs R HIA hc <= hfr asegs R HIA h + e * fr_charge 0 ->
      Z.of_nat (length nodes) <= e ->
      aevtA asegs (KF asegs R HIA hc mo0) POST
        (MS (mkR x1 SPT gp tp x5 x6 x7 (Z_to_bv 64 PP) (Z_to_bv 64 A_ASN1_SEQ_CB) (Z_to_bv 64 p)
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) (Z_to_bv 64 0) tgw (Z_to_bv 64 255) (Z_to_bv 64 END) x23
                 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr PP 3)) (Z_to_bv 64 CTX) (Z_to_bv 64 2)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9a308) fc None mm (seg_rom asegs))
(* [comment removed for export] *).

  #[using="D1 CURLO"] Lemma seqrep_pp2 : forall (mm mm' : mem) (nodes : list Z) (cur hi : Z),
      seqrep asegs mm (nLB nodes) BUF END CUR nodes cur -> (forall x, In x nodes -> nodeF x) ->
      munch [(PP, PP + 8); (lo, hi)] mm mm' -> wmono asegs mm mm' -> seqrep asegs mm' (nLB nodes) BUF END CUR nodes cur.
  Proof.
    intros mm mm' nodes cur hi HS HF MU WM. eapply seqrep_mem; [exact HS| intros b Hb; exact Hb|].
    intros A cs HA HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz. cbn [disjoint_from].
    destruct HA as [[-> _]|HA].
    - split; [clear - D1; lia| split; [clear - CURLO; lia| exact I]].
    - destruct (HF A (in_rl _ _ HA)) as (_ & _ & NLO & NPP & _). split; [clear - NPP; lia| split; [clear - NLO; lia| exact I]].
  Qed.

  Ltac hide_heap :=
    pose proof (art_alwf asegs R HIA) as ALWF;
    repeat match goal with
    | H : HM _ _ _ _ _ _ _ |- _ => lx_hide1 H
    | H : presW _ _ _ _ _ _ _ _ _ _ _ |- _ => lx_hide1 H
    | H : tinv _ _ _ _ _ _ _ _ _ |- _ => lx_hide1 H
    | H : rw_cells _ _ CUR _ |- _ => lx_hide1 H
    | H : rw_cells _ _ (CTX + 8) _ |- _ => lx_hide1 H
    | H : aobj _ _ _ _ CUR _ |- _ => lx_hide1 H
    | H : aobj _ _ _ _ (CTX + 8) _ |- _ => lx_hide1 H
    end.

  Ltac leaf_prep :=
    lx_unhide;
    try (match goal with LX : ?x = ?y |- _ => is_var x; is_var y; let T := type of x in unify T mem; subst x end);
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with
      | MU9 : munch ?W ?m0 mx, WM9 : wmono _ ?m0 mx |- _ =>
          lazymatch m0 with
          | mx => idtac
          | _ =>
            let MU2 := fresh "MU2" in
            assert (MU2 : munch [(PP, PP + 8); (lo, bv_unsigned sp)] m0 mx)
              by (eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; intros ? ?; lia);
            repeat match goal with H : munch _ _ m0 |- _ => clear H end;
            transport_after_callA asegs m0 mx MU2;
            transport_after_call asegs m0 mx MU2 WM9;
            try (match goal with SR : seqrep _ m0 _ _ _ _ _ _, NF : (forall x, In x _ -> nodeF x) |- _ =>
                   pose proof (seqrep_pp2 m0 mx _ _ _ SR NF MU2 WM9) as HSR2 end)
          end
      end;
      try lx_rejoin
    end.

  Ltac mk_tinv INVn hc nodes cur ct cpad cl cp jj :=
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      assert (INVn : tinv mx hc nodes cur ct cpad cl cp jj)
        by (unfold tinv; spine; first
              [ eassumption | reflexivity | exact I
              | lazymatch goal with
                | |- List.NoDup [] => constructor
                | |- forall x, In x [] -> _ => intros ? []
                | |- forall x, _ -> _ => intros ? Hx; exact Hx
                | |- _ \/ _ => left; repeat split; reflexivity
                end ])
    end.

  Ltac leaf_arith :=
    first [ eassumption | (split; eassumption)
          | (rewrite uw64' by (first [lx_arith | lia]); leaf_arith)
          | lazymatch goal with |- _ <= _ / 2 => apply Z.div_le_lower_bound; [clear; lia| leaf_arith] end
          | (rewrite Z2Nat.id by (first [lx_arith | lia]); leaf_arith)
          | lx_arith | lia ].

  Ltac reA :=
    lazymatch goal with
    | k : ?K ?mo |- aevtS ?sg ?Q (mkCfg ?ms ?mo) => revert k; revert mo; change (aevtA sg K Q ms)
    | _ => idtac
    end.

  Ltac lclose INVx HPx := first [ exact INVx | exact HPx | lx_regs_eq | leaf_arith ].

  Ltac exit_leaf hc nodes cur ct cpad cl cp e :=
    lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?rv) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mx _] =>
    lazymatch goal with HPx : rw_cells _ mx PP [C8 (Z_to_bv 64 ?pv)] |- _ =>
    lazymatch goal with FRx : rw_cells _ mx (bv_unsigned sp + -112) (C8 ?jj :: _) |- _ =>
      let INVx := fresh "INVx" in
      mk_tinv INVx hc nodes cur ct cpad cl cp jj;
      reA;
      lx_via_eq (eapply (exit_walk hc mx nodes cur ct cpad cl cp jj e rv pv));
      lclose INVx HPx
    end end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01B0@C17014924541.169C40864224109.171D10651797128.172D46805804653.172D56485271081.172D60098748265.172K31000086261.172K31000086261.174K58794436880.169K67304026837.169L12435490074.170L17585600796.2  L1767414736.2   L19225025704.2  L19644534226.2  L1996626901.1   L22704466500.173L22782772884.2  L24576932131.1  L26284580866.2  L27111942217.1  L2836159258.2   L28784832391.2  L29062839687.3  L29444421150.133L29729353963.4  L29735681138.4  L30997223346.3  L31003745067.3  L31946070045.133L32887553589.11 L35655538583.9  L39172636981.0  L43219406168.2  L44740776243.134L46833003080.2  L48648023719.1  L49453778011.2  L50676528412.3  L52448574109.2  L54894795405.130L56518885357.2  L56931183307.130L58794207418.2  L58911198308.131L60098763854.3  L61097676998.2  L62068091525.170L64179129035.1  L65084533637.3  L65157903559.2  L67304579733.2  L8990544359.133 O11949499318.169O12501939656.170O17014924541.169O24731047031.169O37553640761.172O37553640761.174O43846829591.172O43846829591.174O49997634727.169O50823326746.170O54109279441.169O7793049834.169 P19641962096.170P28783279300.170P29065473732.169P29734055221.172P29734055221.174P50678081119.169P61096117125.169P65084898245.169Q10651797128.172Q15756291957.172Q17012703463.172Q28689695590.172Q45059259747.172Q46805804653.172Q50846742593.172Q62390855917.172Q66279241507.17200000100500W01902I03403O04604Q04m06c06d06e06f06g06h07S07T07U07V07Z07[07\07]09109209309409509W0:<0:U0:V0:W0;I0;J0;K0;L0;M0;N0<00<10=G0=H0>20><0>=0>k0>l0>m0>n0>o0@E0@F0@G0@H0@I0@J0@K0@L0@M0@N0@O0@P0@Q0A>0A?0Ah0Ai0Aj0BH0BI0Bg0C:0CZ0Cm0DR0DS0Df0E<0EW0EXFS2PPS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03TOP2hc5nodes3cur3HTc2C03SPRS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS5nodes3curS2PP1P3END3BUF2bs3DPB5nodesS2PP1P3END3BUF1l2B33B473DPB5nodes5LXlenS2PP3CTX1P3END2bs3DXP5nodesS2PP1P3END2bs5nodes3cur4CPPaS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33DPB4CUR03DCB2D14CTX03DXB3DXP3DXC5nodes3cur2j02p05start3HP04HST02LR2C03SPR2H9FFFFFS2sp2PP3CTX3CUR1P3END2lo2bs5nodes3cur1x3H13FFFS2PPFFFS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX05nodes3cur2j02p05start1e4HST03HE22LR2C03SPRFFFFS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1P3END2j02p05start1e4HST03HSE3HE22LRS1R3HIA1h2sp2lo3TOP5HTOPcSFS2sp2PP3CTX3CUR1P3END2bs5nodes3cur2j05start3HSE2H9FFFFFS2sp2PP3CTX3CUR1P3END2bs5nodes3curFS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX05nodes3cur2j02p05start3HP04HST03HSE2LR2C03SPRFS2sp2PP3CTX3CUR1P3END2bs5nodes3cur5start1HS1R2lo3LOSFS2sp2PP3CTX3CUR1P3END2bs5nodes3cur2j05start2H9FFFFS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX05nodes3cur2j02p05start3HP04HST03HSE2LR2C03SPRFFFFFFFFFFFFS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesFS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOS5nodesFFS2sp2PP1P3END2lo2bs4PPLO5nodesFS2sp1P3END2lo2bs5nodes3cur3CLOS2PP1P3END2bs5nodesS1R1P3END2lo2bs2B23LOS5nodes3ALOS2PP1P3END2bs5nodesS1R5NEED02sp1P3END2lo2bs2B23SLO5nodesFS2PP1P3END2bs5nodesS2sp1P3END2lo2bs5nodesS2PP1P3END2lo2bs4PPLO5nodesF". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma aftercb_walk :
    forall (hc : HST asegs R HIA) (mm : mem) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : word)
           (p0 start e r : Z) (tgw y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word),
      tinv mm hc nodes cur ct cpad cl cp j0 ->
      rw_cells asegs mm PP [C8 (Z_to_bv 64 start)] ->
      r = 0 \/ r = -106 ->
      P <= p0 -> p0 + 2 <= start -> start + bv_unsigned j0 <= END ->
      0 <= e -> 2 * e <= p0 + 2 - P ->
      havol asegs R HIA hc <= havol asegs R HIA h + e * ASN1_SEQ_CB_PHI ->
      hfr asegs R HIA hc <= hfr asegs R HIA h + e * fr_charge 0 ->
      Z.of_nat (length nodes) <= e ->
      (forall p', p0 + 2 <= p' -> p' < END -> LoopOblig p' tgw) ->
      aevtA asegs (KF asegs R HIA hc mo0) POST
        (MS (mkR (Z_to_bv 64 0x9a374) SPT gp tp y5 y6 y7 (Z_to_bv 64 PP) (Z_to_bv 64 A_ASN1_SEQ_CB) (Z_to_bv 64 r)
                 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) (Z_to_bv 64 0) tgw (Z_to_bv 64 255) (Z_to_bv 64 END) y23
                 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (al_sb AL + Z.shiftr PP 3)) (Z_to_bv 64 CTX) (Z_to_bv 64 2)
                 y28 y29 y30 y31)
            F (Z_to_bv 64 0x9a374) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until y31. intros INV HPP Hr HP0 HST0 HSE HE0 HE2 BUDa BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 j0) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof INV as INV0.
    open_inv_mu INV hc.
    assert (HEE : e <= (END - P) / 2) by (apply Z.div_le_lower_bound; [clear; lia| clear - HE0 HE2 HST0 HSE LR; lia]).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    unfold LoopOblig in KLOOP.
    hide_heap.
    (* [comment removed for export] *)
    destruct Hr as [-> | ->].
    all: lx_run_tac (PLAN [0x9a308; 0x9a3c4] [] 120%N).
    all: lx_tree.
    all: leaf_prep.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x9a3c4) _ _ _ _] => exit_leaf hc nodes cur ct cpad cl cp e
         | |- context [MS _ _ (Z_to_bv 64 0x9a308) _ _ ?mx _] =>
             lazymatch goal with
             | HPx : rw_cells _ mx PP [C8 (Z_to_bv 64 ?pv)], FRx : rw_cells _ mx (bv_unsigned sp + -112) (C8 ?jj :: _) |- _ =>
                 let INVx := fresh "INVx" in
                 mk_tinv INVx hc nodes cur ct cpad cl cp jj;
                 reA;
                 lx_via_eq (eapply (KLOOP pv _ _ hc mx nodes cur ct cpad cl cp jj e));
                 lclose INVx HPx
             end
         end.
    Unshelve.
    all: try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03D0@C17014924541.182C17014924541.210C17014924541.212C17014924541.215C40864224109.183C40864224109.211C40864224109.213C40864224109.216D10651797128.185D10651797128.213D10651797128.215D10651797128.218D46805804653.185D46805804653.213D46805804653.215D46805804653.218D56485271081.185D56485271081.213D56485271081.215D56485271081.218D60098748265.185D60098748265.213D60098748265.215D60098748265.218K31000086261.185K31000086261.213K31000086261.215K31000086261.218K58794436880.182K58794436880.210K58794436880.212K58794436880.215K67304026837.182K67304026837.210K67304026837.212K67304026837.215L10895256630.200L16756239124.2  L17585600796.2  L17627977677.172L1767414736.2   L19225025704.2  L19597388323.174L19644534226.2  L19656180023.170L21578397731.1  L22273804173.142L22704466626.186L22782772884.2  L2348403288.2   L25757637051.171L26284580866.2  L26547817935.172L27111942217.1  L27586673967.142L2836159258.2   L28590442968.2  L28784832391.2  L29062839687.3  L29657318826.156L29735681138.4  L30507144274.2  L30997223346.3  L31186747242.172L31186747242.200L31457063545.143L31952344941.174L32889713813.7  L34326279175.1  L34389167798.200L35655538583.9  L36510325972.215L36516598692.172L36516598692.200L39172636981.0  L39646648071.2  L43219406168.2  L44395247765.174L45165886418.200L46253804627.200L46833003080.2  L47025078861.170L48648023719.1  L48781037052.172L49453778011.2  L50676528412.3  L52448574109.2  L56380991837.7  L56518885357.2  L56995717126.155L57626594114.216L57626594115.214L57626594116.219L57782531189.215L58794207418.2  L60098763854.3  L61097676998.2  L64179129035.1  L65084533637.3  L65157903559.2  L66153253411.1  L67304579733.2  L68257292700.2  L9050821394.175 O11949499318.182O11949499318.210O11949499318.212O11949499318.215O12501939656.184O12501939656.212O12501939656.214O12501939656.217O1489058376.185 O1489058376.213 O1489058376.215 O1489058376.218 O17014924541.182O17014924541.210O17014924541.212O17014924541.215O18978647962.185O18978647962.213O18978647962.215O18978647962.218O24731047031.182O24731047031.210O24731047031.212O24731047031.215O37553640761.185O37553640761.213O37553640761.215O37553640761.218O43846829591.185O43846829591.213O43846829591.215O43846829591.218O49997634727.182O49997634727.210O49997634727.212O49997634727.215O50823326746.184O50823326746.212O50823326746.214O50823326746.217O54109279441.182O54109279441.210O54109279441.212O54109279441.215O7793049834.182 O7793049834.210 O7793049834.212 O7793049834.215 P19641962096.184P19641962096.212P19641962096.214P19641962096.217P29065473732.182P29065473732.210P29065473732.212P29065473732.215P29734055221.185P29734055221.213P29734055221.215P29734055221.218P30508931056.185P30508931056.213P30508931056.215P30508931056.218P50678081119.182P50678081119.210P50678081119.212P50678081119.215P65084898245.182P65084898245.210P65084898245.212P65084898245.215Q10651797128.185Q10651797128.213Q10651797128.215Q10651797128.218Q15756291957.185Q15756291957.213Q15756291957.215Q15756291957.218Q17012703463.185Q17012703463.213Q17012703463.215Q17012703463.218Q28689695590.185Q28689695590.213Q28689695590.215Q28689695590.218Q45059259747.185Q45059259747.213Q45059259747.215Q45059259747.218Q46805804653.185Q46805804653.213Q46805804653.215Q46805804653.218Q50846742593.185Q50846742593.213Q50846742593.215Q50846742593.218Q62390855917.185Q62390855917.213Q62390855917.215Q62390855917.218Q66279241507.185Q66279241507.213Q66279241507.215Q66279241507.21800000100200300400800<00@00D00f01H01j02L02n03P04204T05d07408D09T0:?0:j0;U0<@0<[0=60=Q0=l0>G0>b0?=0?X0@60@T0A20AP0BD0BE0BF0CU0CV0CW0Dl0Dm0F90F:0F\0GI0GJ0GK0HY0HZ0II0IM0J40J50J60J70J80KM0KN0KO0KP0L?0M50M[0N=0NO0NS0OB0O[0PK0Q;0R20R30R40R50SI0T70Th0Ti0UX0UY0W50W60W70W80WQ0WR0X[0[I0^30`a0bW0bX0bb0bc0bd0be0bf0bj0bk0bl0c`0ca0cb0cc0cd0d30dB0dQ0d`0do0e>0eM0e\0ek0f:0fI0fX0fY0fZ0f[0f\0f]0f^0f_0f`0fa0fb0fc0fd0fe0ff0fg0fh0fi0fj0fk0fl0fm0fn0fo0g00g10g20g30g40g50g60g70g80ge0hR0i?0il0jU0k>0kg0lP0m00mP0n00nP0o=0oj10W11D11b12@12^13<13Z14814V15415G15Z15m16@16`17@17`18@18S18f19919L19g1:B1:]1;81;91;:1;;1;<1;O1;b1<51<H1<^1=41=J1=`1>;1>V1?11?L1?M1?N1?O1?PFFFFS2PPS2PPS2PPS2PPS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03TOP2hc5nodes3cur3HTc2C03SPRS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03TOP2hc5nodes3cur3HTc2C03SPRS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03TOP2hc5nodes3cur3HTc2C03SPRS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03TOP2hc5nodes3cur3HTc2C03SPRS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS5nodes3curS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS5nodes3curS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS5nodes3curS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOS5nodes3curS2PP1P3END3BUF2bs3DPB5nodesS2PP1P3END3BUF2bs3DPB5nodesS2PP1P3END3BUF2bs3DPB5nodesS2PP1P3END3BUF2bs3DPB5nodesS2PP3CTX1P3END2bs3DXP5nodesS2PP3CTX1P3END2bs3DXP5nodesS2PP3CTX1P3END2bs3DXP5nodesS2PP3CTX1P3END2bs3DXP5nodesS2PP1P3END2bs1p5nodes3cur4CPPaS2PP1P3END2bs1p5nodes3cur4CPPaS2PP1P3END2bs1p5nodes3cur4CPPaS2PP1P3END2bs1p5nodes3cur4CPPaS2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur4lxv33H156nodes'FFS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B24CUR04CTX01p2Hp5nodes3cur2C03SPR4lxv33H15FFS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX01p2Hp5nodes3cur2C03SPR4lxv34lxv43H153H163H17FS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX01p2Hp5nodes3cur2C03SPR4lxv33H153H16FS2sp2PP3CTX3CUR1P3END2bs5nodes3curS2sp2PP3CTX3CUR1P3END2lo2bs1p5nodes3cur1x3H21FFS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX05nodes3cur2C03SPR4lxv24lxv33H103H151HFS2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv13H223H23S2PPS2sp2PP3CTX3CUR1P3END2bs1p2Hp5nodes3curFFFFS1R5NEED02sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03LOS3SLO5nodes3cur2C03ALO3ACV3SPRFFFS2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv43H123H13S2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv43H123H136nodes'S2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur1HS2sp2PP3CTX3CUR1P3END2bs5nodes3curS1P3END1p2Hp1e3HE2S2spS2sp2PP3CTX3CUR1P3END2bs5nodes3cur1e3HE06nodes'S1R3HIA1h2sp2lo3TOP5HTOPcS2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv34lxv43H10S2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv34lxv43H14S2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv34lxv43H146nodes'SFFS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX01p5nodes3cur1e3HE22C03SPR4lxv34lxv43H153H17S2sp2PP3CTX3CUR1P3END2bs1p2Hp5nodes3cur6nodes'S2sp2PP3CTX3CUR1P3END2bs1p5nodes3cur1e3HE26nodes'FS2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv23H103H18FS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX01p5nodes3cur1e3HE22C03SPR4lxv34lxv43H133H143H153H16FFFS1R3BUF2lo2bs3LOS3ALO3BCEFS1R5NEED02sp2PP3CTX3CUR1P3END2lo2bs3PP02B24CUR04CTX03SLO5nodes3cur2C03SPRS1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO1p2Hp5nodes3cur2C03CLO4CCTX5CBUFa3SPR5BUFLO4lxv34lxv43H133H143H153H161x3H32S1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO1p2Hp5nodes3cur2C03CLO4CCTX5CBUFa3SPR5BUFLO4lxv34lxv43H123H153H161x3H31S1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO1p2Hp5nodes3cur2C03CLO4CCTX5CBUFa3SPR5BUFLO4lxv34lxv43H103H153H171x3H343H18S2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33DPB4CUR03DCB2D14CTX03DXB3DXP3DXC1p2Hp5nodes3cur2C03SPR4lxv34lxv43H103H153H17FS1R2lo3LOSFFFFS2spFFS2sp2PP3CTX3CUR1P3END2bs5nodes3cur4lxv34lxv43H103H16FFFFS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqS2sp2lo2bs4SLOqFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOS5nodesS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOS5nodesS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOS5nodesS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOS5nodesS2sp1P3END3BUF2lo2bs5nodes5BUFLOS2sp1P3END3BUF2lo2bs5nodes5BUFLOS2sp1P3END3BUF2lo2bs5nodes5BUFLOS2sp1P3END3BUF2lo2bs5nodes5BUFLOS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLO5nodesS2sp2PP1P3END2lo2bs4PPLO5nodesS2sp2PP1P3END2lo2bs4PPLO5nodesS2sp2PP1P3END2lo2bs4PPLO5nodesS2sp2PP1P3END2lo2bs4PPLO5nodesS2sp1P3END2lo2bs5nodes3cur3CLOS2sp1P3END2lo2bs5nodes3cur3CLOS2sp1P3END2lo2bs5nodes3cur3CLOS2sp1P3END2lo2bs5nodes3cur3CLOS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS1R1P3END2lo2bs2B23LOS5nodes3ALOS1R1P3END2lo2bs2B23LOS5nodes3ALOS1R1P3END2lo2bs2B23LOS5nodes3ALOS1R1P3END2lo2bs2B23LOS5nodes3ALOS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2sp1P3END2lo2bs5nodes4SLOqS2sp1P3END2lo2bs5nodes4SLOqS2sp1P3END2lo2bs5nodes4SLOqS2sp1P3END2lo2bs5nodes4SLOqFFFFS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2PP1P3END2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2sp1P3END2lo2bs5nodesS2PP1P3END2lo2bs4PPLO5nodesS2PP1P3END2lo2bs4PPLO5nodesS2PP1P3END2lo2bs4PPLO5nodesS2PP1P3END2lo2bs4PPLO5nodesFFFF". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma body_walk :
    forall (p : Z) (tgw : word), P <= p < END ->
      (forall p', p + 2 <= p' -> p' < END -> LoopOblig p' tgw) -> LoopOblig p tgw
(* [comment removed for export] *).
  Proof.
    intros p tgw Hp KLOOP. unfold LoopOblig. intros until x31. intros INV HPP HE0 HE2 BUDa BUDFa HLN.
    pose proof INV as INV0.
    open_inv_mu INV hc.
    assert (HEE : e <= (END - P) / 2) by (apply Z.div_le_lower_bound; [clear; lia| clear - HE0 HE2 Hp; lia]).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA hc (nLB nodes) LF mm LB HHc (nLB_sub nodes) _ BIN) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
    pose proof (sums_getlen_ok AL IMG) as LXSUMS.
    rewrite <- (Z_to_bv_bv_unsigned j0) in FRM.
    destruct (proj1 (rw_cells_app asegs mm (bv_unsigned sp + -112) [Cells.C8 (Z_to_bv 64 (bv_unsigned j0))] SAVEL) FRM) as [FRS FRV].
    change (Z.of_nat (cells_size [Cells.C8 (Z_to_bv 64 (bv_unsigned j0))])) with 8 in FRV.
    replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in FRV by (clear; lia).
    clear FRM.
    assert (SLOq : lo <= bv_unsigned sp + -128) by (unfold TRAV_STK in SLO; lia).
    assert (SPq : 0 <= bv_unsigned sp + -128) by lia.
    hide_heap.
    (* [comment removed for export] *)
    lx_run_tac (PLANS [0x9a370; 0x9a3c4; 0x9a308] [(0x9a328, DJoin)] 200%N [SUM_getlenA]).
    lx_tree.
    all: leaf_prep.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x9a3c4) _ _ _ _] => exit_leaf hc nodes cur ct cpad cl cp e
         | |- context [MS _ _ (Z_to_bv 64 0x9a308) _ _ ?mx _] =>
             lazymatch goal with
             | HPx : rw_cells _ mx PP [C8 (Z_to_bv 64 ?pv)], FRx : rw_cells _ mx (bv_unsigned sp + -112) (C8 ?jj :: _) |- _ =>
                 let INVx := fresh "INVx" in
                 mk_tinv INVx hc nodes cur ct cpad cl cp jj;
                 reA;
                 lx_via_eq (eapply (KLOOP pv _ _ hc mx nodes cur ct cpad cl cp jj e));
                 lclose INVx HPx
             end
         | |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?tg) (Z_to_bv 64 ?st) ?jj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9a370) _ _ ?mx _] =>
             lazymatch goal with HPx : rw_cells _ mx PP [C8 (Z_to_bv 64 ?pv)] |- _ =>
               let INVx := fresh "INVx" in
               mk_tinv INVx hc nodes cur ct cpad cl cp jj;
               reA;
               lx_via_eq (eapply (cb_step hc mx nodes cur ct cpad cl cp jj pv tg st e));
               first [ exact INVx | exact HPx | exact BUD | exact BUDF | lx_regs_eq
                     | lazymatch goal with
                       | |- forall (_ : HST _ _ _), _ =>
                           intros hc' mm' nodes' cur' ct' cpad' cl' cp' r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HR INV' HPP' BV1 BF1 HL1;
                           lx_via_eq (eapply (aftercb_walk hc' mm' nodes' cur' ct' cpad' cl' cp' jj p st (e + 1) r));
                           first [ exact INV' | exact HPP' | exact HR | exact BV1 | exact BF1 | exact HL1 | exact KLOOP | lx_regs_eq | leaf_arith ]
                       end
                     | leaf_arith ]
             end
         end.
    Unshelve.
    all: try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L26472204151.71L26726586762.6 L34758806549.7 00000T00f01;S2sp2PP3CTX3CUR1P3END2bs1p3tgw2Hk2HpS3END1k1p2Hk2p'2H1S1P3END1p2Hp2p'2H12H2". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma tloop :
    forall (k : nat) (p : Z) (tgw : word), END - p <= Z.of_nat k -> P <= p < END -> LoopOblig p tgw
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros p tgw Hk Hp; [lia|].
    apply body_walk; [exact Hp|]. intros p' H1 H2. apply IH; [clear - Hk H1; lia| clear - Hp H1 H2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03V0@C17014924541.129C17014924541.138C17014924541.167C17014924541.169C17014924541.171C40864224109.130C40864224109.139C40864224109.168C40864224109.170C40864224109.172D10651797128.131D10651797128.140D10651797128.169D10651797128.171D10651797128.173D46805804653.131D46805804653.140D46805804653.169D46805804653.171D46805804653.173D60098748265.131D60098748265.140D60098748265.169D60098748265.171D60098748265.173D64317825486.131D64317825486.140D64317825486.169D64317825486.171D64317825486.173K31000086261.131K31000086261.140K31000086261.169K31000086261.171K31000086261.173K32051337109.130K32051337109.139K32051337109.168K32051337109.170K32051337109.172K58794436880.130K58794436880.139K58794436880.168K58794436880.170K58794436880.172L13107166054.3  L13287900941.133L16973756365.97 L17585600796.2  L1767414736.2   L18637876888.2  L19225025704.2  L19644534226.2  L19656180023.132L19656180023.133L19656180023.134L19656180023.170L22273804173.104L23084353748.2  L24916562796.170L2493589960.2   L25757637051.133L25757637051.134L25757637051.135L26284580866.2  L28784832391.2  L29062839687.3  L29735681138.4  L30997223346.3  L31797844461.2  L31946070045.134L32051500981.2  L35653441506.9  L36119671557.134L39172636981.0  L39280637297.0  L43051290284.109L43491718995.0  L46481978224.105L46481978224.98 L47025078861.132L49453778011.2  L50676528412.3  L52757608363.104L52757608363.97 L55191838493.2  L56380991837.7  L57626593346.132L57626593353.141L57626593480.170L57626593483.172L57626594112.174L58794207418.2  L60098763854.3  L60330452198.111L60689750810.2  L61097676998.2  L62018535662.1  L64179129035.1  L65110679799.3  L65157903559.2  L66099488952.3  L66153253411.1  L68257292700.2  L8983083206.3   O11949499318.130O11949499318.139O11949499318.168O11949499318.170O11949499318.172O12501939656.131O12501939656.140O12501939656.169O12501939656.171O12501939656.173O17014924541.129O17014924541.138O17014924541.167O17014924541.169O17014924541.171O33548756817.130O33548756817.139O33548756817.168O33548756817.170O33548756817.172O37553640761.131O37553640761.140O37553640761.169O37553640761.171O37553640761.173O3855256695.130 O3855256695.139 O3855256695.168 O3855256695.170 O3855256695.172 O43846829591.131O43846829591.140O43846829591.169O43846829591.171O43846829591.173O49997634727.129O49997634727.138O49997634727.167O49997634727.169O49997634727.171O50823326746.131O50823326746.140O50823326746.169O50823326746.171O50823326746.173O7793049834.130 O7793049834.139 O7793049834.168 O7793049834.170 O7793049834.172 P19641962096.131P19641962096.140P19641962096.169P19641962096.171P19641962096.173P28783279300.131P28783279300.140P28783279300.169P28783279300.171P28783279300.173P29065473732.130P29065473732.139P29065473732.168P29065473732.170P29065473732.172P29734055221.131P29734055221.140P29734055221.169P29734055221.171P29734055221.173P50678081119.129P50678081119.138P50678081119.167P50678081119.169P50678081119.171P61096117125.129P61096117125.138P61096117125.167P61096117125.169P61096117125.171P8980441989.130 P8980441989.139 P8980441989.168 P8980441989.170 P8980441989.172 Q10651797128.131Q10651797128.140Q10651797128.169Q10651797128.171Q10651797128.173Q15756291957.131Q15756291957.140Q15756291957.169Q15756291957.171Q15756291957.173Q17012703463.131Q17012703463.140Q17012703463.169Q17012703463.171Q17012703463.173Q28689695590.131Q28689695590.140Q28689695590.169Q28689695590.171Q28689695590.173Q46805804653.131Q46805804653.140Q46805804653.169Q46805804653.171Q46805804653.173Q50846742593.131Q50846742593.140Q50846742593.169Q50846742593.171Q50846742593.173Q63266948804.131Q63266948804.140Q63266948804.169Q63266948804.171Q63266948804.173Q66279241507.131Q66279241507.140Q66279241507.169Q66279241507.171Q66279241507.17300000100200300400500900=00A00E00I00a01901Q01i02A02Y03103I03a04904Z05;05\06=06^07E07l08S09:09a0:60:K0:`0;50;J0;^0<20<F0<Z0<n0=C0=X0=m0>B0>W0>`0?80?P0?Q0?R0?S0?T0?U0@:0@_0AD0Ah0B@0BA0C[0C\0D\0E;0E_0E`0Ea0Eb0Ec0Ed0Ee0F=0F>0FV0G70G80G90Gl0Gm0HG0Ha0IE0IF0IG0Ib0J=0J>0JW0LJ0NA0On0Q[0SH0SI0SS0Se0Sf0Sg0Sj0Sk0T50T60T?0TC0TD0TE0TF0TG0TH0TI0TJ0TK0TL0TM0TN0TO0TP0TQ0TR0TS0TT0TU0TV0TW0TX0TY0TZ0T[0T\0T]0T^0T_0T`0Ta0Tb0Tc0Td0Te0Tf0Tg0Th0Ti0Tj0Tk0Tl0Tm0Tn0To0U00U10U20U30U40U50U60U70U^0VE0Vl0WS0X:0X;0X<0X=0X>0X?0Xb0YE0Yh0ZK0Zn0[H0[b0\<0\V0]00]H0]`0^80^P0^h0^i0^j0^k0^l0^m0_G0_a0`;0`U0`o0a<0aI0aV0ac0b00bJ0bd0c>0cX0d20d?0dL0dY0df0e30eR0f10fP0fo0gN0g[0gh0h50hB0hO0h_0ho0i?0iO0i_0j40jI0j^0k30kH0kI0kJ0kK0kL0kMFFFFFS2PPS2PPS2PPS2PPS2PPS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOSS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOSS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOSS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOSS1R2sp2PP3CTX3CUR1P3END2lo2bs3LOSS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3TOPS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3TOPS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3TOPS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3TOPS1R3HIA1h2sp2PP3CTX3CUR1P3END2lo2bs3TOPS2PP1P3END3BUF2bs3DPBS2PP1P3END3BUF2bs3DPBS2PP1P3END3BUF2bs3DPBS2PP1P3END3BUF2bs3DPBS2PP1P3END3BUF2bs3DPBS2PP3CUR1P3END2bs2D1S2PP3CUR1P3END2bs2D1S2PP3CUR1P3END2bs2D1S2PP3CUR1P3END2bs2D1S2PP3CUR1P3END2bs2D1S2PP3CTX1P3END2bs3DXPS2PP3CTX1P3END2bs3DXPS2PP3CTX1P3END2bs3DXPS2PP3CTX1P3END2bs3DXPS2PP3CTX1P3END2bs3DXPS1R3HIA1hS2sp2PP3CTX3CUR1P3END2bsS2sp2PP3CTX3CUR1P3END2bsFFFFFS2sp2PP3CTX3CUR1P3END2bs4lxv33H143H15S2sp2PP3CTX3CUR1P3END2bs4lxv33H143H15S2sp2PP3CTX3CUR1P3END2bs4lxv33H153H16S2sp2PP3CTX3CUR1P3END2bs4lxv32H93H15S2sp2PP3CTX3CUR1P3END2bsFS2sp2PP3CTX3CUR1P3END3BUF2bs3PP02B12B22B33DPB4CUR03DCB2D14CTX03DXB3DXP3DXC3SPR4lxv32H93H15FS2sp2PP3CTX3CUR1P3END2bs3PP02B24CUR04CTX03SPR4lxv24lxv32H93H141HS2sp2PP3CTX3CUR1P3END2bs4lxv31HS2sp2PP3CTX3CUR1P3END2bs4lxv32H93H16FFFFFFS2sp2PP3CTX3CUR1P3END2bsFS1R3HIA1h2sp2lo3TOP4HTOPS2sp2PP3CTX3CUR1P3END2bs4lxv33H15SSS1R5NEED02sp2PP3CTX3CUR2lo2bs3PP04CUR04CTX03SLO3SPRSS2sp2PP3CTX3CUR1P3END2bs1HS2sp2PP3CTX3CUR1P3END2bs1HS2sp2PP3CTX3CUR1P3END2bs4lxv22H93H17FFS2sp2PP3CTX3CUR1P3END2bs2B2S2sp2PP3CTX3CUR1P3END2bs2B2FS1R3BUF2lo2bs3LOS3ALO3BCES1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO3SPR5BUFLO1x3H12S1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO3SPR5BUFLO3H111x3H17S1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B24CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO3SPR5BUFLO1x3H28S1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B24CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO3SPR5BUFLO1x3H29S1R5NEED02sp2PP3CTX3CUR1P3END3BUF2lo2bs3PP04PPLO2B24CUR05CURLO3DCB4CTX05CTXLO3DXB3DXC3LOS3SLO3SPR5BUFLO1x3H30FS1R2lo3LOSS2sp2PP3CTX3CUR2bsFFS1RFS1P3END2B2FS1R3HIA1hS2spFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLOS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLOS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLOS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLOS1R5NEED02sp2PP1P3END2lo2bs4PPLO2B23SLOFFFFFS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOSS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOSS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOSS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOSS1R2sp3CTX1P3END2lo2bs2B25CTXLO3LOSS2sp1P3END3BUF2lo2bs5BUFLOS2sp1P3END3BUF2lo2bs5BUFLOS2sp1P3END3BUF2lo2bs5BUFLOS2sp1P3END3BUF2lo2bs5BUFLOS2sp1P3END3BUF2lo2bs5BUFLOS2sp2PP1P3END2lo2bs4PPLOS2sp2PP1P3END2lo2bs4PPLOS2sp2PP1P3END2lo2bs4PPLOS2sp2PP1P3END2lo2bs4PPLOS2sp2PP1P3END2lo2bs4PPLOFFFFFS2sp3CUR1P3END2lo2bs5CURLOS2sp3CUR1P3END2lo2bs5CURLOS2sp3CUR1P3END2lo2bs5CURLOS2sp3CUR1P3END2lo2bs5CURLOS2sp3CUR1P3END2lo2bs5CURLOS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS1R1P3END2lo2bs2B23LOS3ALOS1R1P3END2lo2bs2B23LOS3ALOS1R1P3END2lo2bs2B23LOS3ALOS1R1P3END2lo2bs2B23LOS3ALOS1R1P3END2lo2bs2B23LOS3ALOS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS1R5NEED02sp1P3END2lo2bs2B23SLOS1R5NEED02sp1P3END2lo2bs2B23SLOS1R5NEED02sp1P3END2lo2bs2B23SLOS1R5NEED02sp1P3END2lo2bs2B23SLOS1R5NEED02sp1P3END2lo2bs2B23SLOS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2PP1P3END2bsS2sp1P3END2lo2bsS2sp1P3END2lo2bsS2sp1P3END2lo2bsS2sp1P3END2lo2bsS2sp1P3END2lo2bsS2PP3CTX3CUR1P3END2bsS2PP3CTX3CUR1P3END2bsS2PP3CTX3CUR1P3END2bsS2PP3CTX3CUR1P3END2bsS2PP3CTX3CUR1P3END2bsFFFFF". (* [comment removed for export] *)
  #[using="IMG NEED0 CBSPEC ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 ALX CTX0 CWX CTXLO DXB DXP DXC LOS SLO TOP SPA TPV BUD BUDF"] Lemma trav_walk :
    forall (ct cpad tgw t0 t1 t2 t3 t4 t5 t6 : word),
      HM asegs R HIA h LB LF m -> HK asegs R HIA h mo0 ->
      rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m CUR (seq_cells ct cpad 0 0 0) ->
      rw_cells asegs m (CTX + 8) [C8 (Z_to_bv 64 CUR)] -> bytes_at asegs m BUF bs ->
      stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      aobj asegs AL CS m PP 8 -> aobj asegs AL CS m CUR 32 -> aobj asegs AL CS m (CTX + 8) 8 ->
      aobj asegs AL CS m (bv_unsigned sp - 112) 8 ->
      aevtS asegs POST
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 255) tgw (Z_to_bv 64 0)
                        (Z_to_bv 64 0) (Z_to_bv 64 A_ASN1_SEQ_CB) (Z_to_bv 64 CTX) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 A_ASN1_TRAV) fc None m (seg_rom asegs)) mo0)
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HK0 HPP HCUR HCTX HBUF ST MI OPP OCUR OCTX OSLOT. unfold A_ASN1_TRAV.
    rt_facts h.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SLO NEED0 TOP HTOP; lia]).
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) X HH ltac:(clear; lia)) as PRES.
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
    unfold seq_cells in HCUR.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(PP, PP + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (sums_getlen_ok AL IMG) as LXSUMS.
    carve_frame 112%nat ST.
    apply (rw_cells_split_CB asegs m (bv_unsigned sp + -112) [] 112 junk [] [8; 104]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    cb8_to_c8 FR (@nil cell).
    lazymatch type of FR with rw_cells _ _ _ (C8 ?w :: _) => rewrite <- (Z_to_bv_bv_unsigned w) in FR end.
    assert (HE00 : 0 <= 0 <= (END - P) / 2) by (split; [clear; lia| apply Z.div_pos; [clear - B2; lia| clear; lia]]).
    assert (B0 : havol asegs R HIA h <= havol asegs R HIA h + 0 * ASN1_SEQ_CB_PHI) by (clear; lia).
    assert (BF0 : hfr asegs R HIA h <= hfr asegs R HIA h + 0 * fr_charge 0) by (clear; lia).
    assert (LN0 : Z.of_nat (length (@nil Z)) <= 0) by (cbn; clear; lia).
    hide_heap.
    (* [comment removed for export] *)
    lx_run_tac (PLANS [0x9a308; 0x9a3c4] [(0x9a270, DJoin)] 400%N [SUM_getlenA]).
    lx_tree.
    all: leaf_prep.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x9a3c4) _ _ _ _] => exit_leaf h (@nil Z) CUR ct cpad 0 0 0
         | |- context [MS _ _ (Z_to_bv 64 0x9a308) _ _ ?mx _] =>
             lazymatch goal with
             | HPx : rw_cells _ mx PP [C8 (Z_to_bv 64 ?pv)], FRx : rw_cells _ mx (bv_unsigned sp + -112) (C8 ?jj :: _) |- _ =>
                 let INVx := fresh "INVx" in
                 mk_tinv INVx h (@nil Z) CUR ct cpad 0 0 jj;
                 reA;
                 lx_via_eq (eapply (tloop (Z.to_nat (END - pv)) pv tgw _ _ h mx (@nil Z) CUR ct cpad 0 0 jj 0));
                 lclose INVx HPx
             end
         end.
    Unshelve.
    all: try lia.
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
