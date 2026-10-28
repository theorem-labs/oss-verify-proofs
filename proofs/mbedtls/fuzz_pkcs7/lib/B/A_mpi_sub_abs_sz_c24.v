(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_add_abs_W P_mpi_add_abs_C P_mpi_sub_abs_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_journey
     A_mpi_core_sub A_mpi_core_sub_int A_amemset A_amemcpy A_mpi_add_abs_W A_mpi_read_binary_stmt A_mpi_stmtA_sz A_mpi_sub_abs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_journey_c24 A_mpi_copy_c24 A_mpi_sub_abs_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_sub_abs_sz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_mpi_sub_abs_sz_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_opnd.opnd_atA"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs.sub_abs_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs.sub_abs_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_c24.C24_SUB_ABS_c"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.sub_abs_Rsz"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "WS.SA_FRAME_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.sub_abs_nz"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_NEGATIVE_VALUE"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "WS.SA_POST_A"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_sub.MPI_CORE_SUB_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_sub.A_MPI_CORE_SUB"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lseg"; "WS.rideS"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XDA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.FBA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"; "WS.KJ_stmt"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JBA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.BJA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_ABS"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs.A_WRAP_CALLOC_SA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs.A_ASAN_MEMCPY_SA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs.A_ASAN_MEMSET_SA"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "mpi_sub_abs_stmtA_oz_c"; "mpi_sub_abs_stmtA_z_c"].


Definition mpi_sub_abs_stmtA_oz_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(<.O4.O3.R2<.R:.R2=.(=.&40.R2:.)R7.)P,(<.O4.O3.R2=.R;.R2>.(=.&40.R2;.)R7.)P,(>.R:.R9.)P,(>.R;.R9.)P,(>.R;.R:.)P,(?.(10.$11.(12.R=.)$13.))P,(14.R>.R=.R;.(=.&40.R30.))P,(14.R?.R=.R<.(=.&40.R31.))P,(15.(16.O3.)(17.$2.R35.(18.R34.))R=.(19.R?.)+10.)P,P,(10.$11.(12.R10.)$1:.)(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(1;.R11.)(1<.+4.(1=.R11.)))P,(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(19.R10.)+10.)P,P,(10.$11.(12.R11.)$1:.)(15.(16.O3.)(17.$2.R39.(18.R38.))R11.(1;.R12.)(1<.+4.(1=.R12.)))P,(1>.O3.R39.R38.(=.&40.R36.)(1?.O4.O3.O2.R3:.)R14.)P,P,(?.(10.$11.(12.R15.)$20.))(21.(22.(23.(1;.R16.)(1<.+4.(1=.R16.)))R13.)(22.(=.&40.R38.)(1;.R16.)))P,(24.O4.R18.R13.(=.&40.R38.))P,(22.(25.O3.)R14.)P,(22.R15.(26.(26.(=.&40.R3:.)+>0.)(27.O3.)))P,(22.(=.&40.R3;.)(1?.O4.O3.O2.R3?.))P,(10.$8.(28.(=.&40.R3<.)+10.)=)P,(10.(3.&40.)R3;.(29.&40.(2:.O3.)))P,(2;.O4.R1>.)P,(10.$8.(28.(=.&40.R40.)+2.)=)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R44.)R20.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R45.)R21.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R46.)R22.R1>.)P,P,(10.$11.(12.R20.)$13.)P,Pi,$8.P,(2?.(22.=R1.)(30.R1.(1<.+4.(1=.R22.))))(10.$31.(32.O4.(33.(23.(1;.R23.)R2.)))$34.)(10.$31.(35.(1;.R22.)(1<.+4.(1=.R22.)))$34.)P,P,(10.$11.(12.R20.)$13.)P,Pi,$8.P,(2?.(22.=R1.)(30.R1.(1<.+4.(1=.R22.))))(10.$31.(32.O4.(33.(23.(1;.R23.)R2.)))$34.)(10.$31.(35.(1;.R22.)(1<.+4.(1=.R22.)))$34.)P,P,(10.$11.(12.R22.)$13.)(22.(23.(23.(1;.R23.)(1<.+4.(1=.R23.)))+8.)(36.+2.+2?.))P,(22.(23.(37.O4.O3.O2.R4:.)(38.R24.R23.R22.))$39.)P,(3:.O4.R27.(25.O3.)(3;.O4.O3.O2.R4;.)(=.&40.R41.)(=.&40.R47.)R21.)P,(3<.O3.(19.R26.)+10.R22.)P,(3<.O3.(19.R26.)+10.R23.)P,(3<.O3.(19.R26.)+10.R24.)P,(22.(23.(3=.O4.O3.O2.R4?.)(3>.R25.))$3?.)P,(22.(23.(40.R4?.)$41.)$42.)P,(10.(3.&40.)R45.(29.&40.(19.R2;.)))P,(10.(3.&40.)R45.(29.&40.(19.R2;.)))P,(10.(3.&40.)R45.(29.&40.(19.R2;.)))(43.O4.(44.O4.O3.O2.R51.R50.R4?.R4>.R4:.R49.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R32.R31.R54.R53.R52.R2>.(45.R53.R2>.R2=.R2<.)(38.R2>.R2=.R2<.)(3>.R2:.)R2;.R30.R2?.)(46.(47.(48.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R32.(29.&40.O1.)R31.(49.(3.&40.))R30.(4:.O4.))R2?.))")
(* [comment removed for export] *).

Definition mpi_sub_abs_stmtA_z_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(;.O4.R:.R2=.R7.)P,(;.O4.R;.R2>.R7.)P,(>.R:.R9.)P,(>.R;.R9.)P,(>.R;.R:.)P,(?.(10.$11.(12.R=.)$13.))P,(14.R>.R=.R;.(=.&40.R30.))P,(14.R?.R=.R<.(=.&40.R31.))P,(15.(16.O3.)(17.$2.R35.(18.R34.))R=.(19.R?.)+10.)P,P,(10.$11.(12.R10.)$1:.)(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(1;.R11.)(1<.+4.(1=.R11.)))P,(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(19.R10.)+10.)P,P,(10.$11.(12.R11.)$1:.)(15.(16.O3.)(17.$2.R39.(18.R38.))R11.(1;.R12.)(1<.+4.(1=.R12.)))P,(1>.O3.R39.R38.(=.&40.R36.)(1?.O4.O3.O2.R3:.)R14.)P,P,(?.(10.$11.(12.R15.)$20.))(21.(22.(23.(1;.R16.)(1<.+4.(1=.R16.)))R13.)(22.(=.&40.R38.)(1;.R16.)))P,(24.O4.R18.R13.(=.&40.R38.))P,(22.(25.O3.)R14.)P,(22.R15.(26.(26.(=.&40.R3:.)+>0.)(27.O3.)))P,(22.(=.&40.R3;.)(1?.O4.O3.O2.R3?.))P,(10.$8.(28.(=.&40.R3<.)+10.)=)P,(10.(3.&40.)R3;.(29.&40.(2:.O3.)))P,(2;.O4.R1>.)P,(10.$8.(28.(=.&40.R40.)+2.)=)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R44.)R20.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R45.)R21.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R46.)R22.R1>.)P,P,(10.$11.(12.R20.)$13.)P,Pi,$8.P,(2?.(22.=R1.)(30.R1.(1<.+4.(1=.R22.))))(10.$31.(32.O4.(33.(23.(1;.R23.)R2.)))$34.)(10.$31.(35.(1;.R22.)(1<.+4.(1=.R22.)))$34.)P,P,(10.$11.(12.R20.)$13.)P,Pi,$8.P,(2?.(22.=R1.)(30.R1.(1<.+4.(1=.R22.))))(10.$31.(32.O4.(33.(23.(1;.R23.)R2.)))$34.)(10.$31.(35.(1;.R22.)(1<.+4.(1=.R22.)))$34.)P,P,(10.$11.(12.R22.)$13.)(22.(23.(23.(1;.R23.)(1<.+4.(1=.R23.)))+8.)(36.+2.+2?.))P,(22.(23.(37.O4.O3.O2.R4:.)(38.R24.R23.R22.))$39.)P,(3:.O4.R27.(25.O3.)(3;.O4.O3.O2.R4;.)(=.&40.R41.)(=.&40.R47.)R21.)P,(3<.O3.(19.R26.)+10.R22.)P,(3<.O3.(19.R26.)+10.R23.)P,(3<.O3.(19.R26.)+10.R24.)P,(22.(23.(3=.O4.O3.O2.R4?.)(3>.R25.))$3?.)P,(22.(23.(40.R4?.)$41.)$42.)P,(10.(3.&40.)R45.(29.&40.(19.R2;.)))P,(10.(3.&40.)R45.(29.&40.(19.R2;.)))P,(10.(3.&40.)R45.(29.&40.(19.R2;.)))(43.O4.(44.O4.O3.O2.R51.R50.R4?.R4>.R4:.R49.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R32.R31.R54.R53.R52.R2>.(45.R53.R2>.R2=.R2<.)(38.R2>.R2=.R2<.)(3>.R2:.)R2;.R30.R2?.)(46.(47.(48.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R32.(29.&40.O1.)R31.(49.(3.&40.))R30.(4:.O4.))R2?.))")
(* [comment removed for export] *).

Section WS.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_SA.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_SA.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_SA.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Hypothesis C24H : cnt24 LB + C24_SUB_ABS_c <= C24MAX.     (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition SA_FRAME_A := aa_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BUD : havol asegs R HIA h + sub_abs_PHI dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + sub_abs_FR d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 224 - arl_need_rt R.

  Local Notation NZB := (sub_abs_nz nX (md_n dA) (md_n dB)).
  Definition SA_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "(44.$4;.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(45.VLB,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(38.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(3>.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A []).
  Local Notation XJ1 An cnt := (XJA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A [(An, 4 * cnt)]).
  Local Notation XD0 := (XDA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A).
  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Local Notation SH10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Local Notation SHA E := (Z_to_bv 64 (Z.shiftr E 3 + al_sb AL)).
  Local Ltac chk_ltb K :=
    repeat match type of K with
    | context [?a <? ?b] => revert K; case (Z.ltb_spec a b); intros ? K
    | context [?a =? ?b] => revert K; case (Z.eqb_spec a b); intros ? K
    end; cbn [Z.b2z] in K; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in K.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41422916509.51000004S2ra".
  #[using="ra"] Lemma land3_mod : forall a, Z.land a 3 = a mod 4.
  Proof. intros a. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L29781691149.51000004S2ra".
  #[using="ra"] Lemma land7_mod : forall a, Z.land a 7 = a mod 8.
  Proof. intros a. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
  #[using="ra"] Lemma lor_land3 : forall a b, a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
  Proof. intros a b Ha Hb. rewrite Z.land_lor_distr_l, !land3_mod, Ha, Hb. reflexivity. Qed.
  Local Notation SPL mc := (rw_cells asegs mc (bv_unsigned sp + -112) [C8 (Z_to_bv 64 (md_addr dB))]).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L21575160055.70L30226092596.70L48328664223.7000000M01001YS2ra3lo'2a02a12c02c12c22E12HLS2ra3lo'2a02a12a22c02c12c22E12E22HLS2ra3lo'2a02a12a22hi2c02c12c22E12E22E32HL".
  #[using="ra"] Lemma stk_up3 : forall mm lo' a0 a1 a2 hi (c0 c1 c2 : list cell),
    stk asegs mm lo' a0 -> rw_cells asegs mm a0 c0 -> rw_cells asegs mm a1 c1 -> rw_cells asegs mm a2 c2 ->
    a1 = a0 + Z.of_nat (cells_size c0) -> a2 = a1 + Z.of_nat (cells_size c1) -> hi = a2 + Z.of_nat (cells_size c2) -> lo' <= a0 ->
    stk asegs mm lo' hi.
  Proof.
    intros mm lo' a0 a1 a2 hi c0 c1 c2 ST S0 S1 S2 E1 E2 E3 HL.
    pose proof (stk_of_rw_cells _ _ _ _ S0) as T0. pose proof (stk_of_rw_cells _ _ _ _ S1) as T1. pose proof (stk_of_rw_cells _ _ _ _ S2) as T2.
    rewrite <- E1 in T0. rewrite <- E2 in T1. rewrite <- E3 in T2.
    eapply stk_merge; [eapply stk_merge; [eapply stk_merge; [exact ST| exact T0| lia]| exact T1| lia]| exact T2| lia].
  Qed.
  Local Ltac stk_up ST :=
    eapply stk_up3 with (a1 := bv_unsigned sp + -120) (a2 := bv_unsigned sp + -112);
    [exact ST| eassumption| eassumption| eassumption| cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| ].
  Local Ltac stk_top ST S hi :=
    lazymatch type of S with rw_cells _ _ ?a ?cs =>
      replace hi with (a + Z.of_nat (cells_size cs)) by (cbn [cells_size csize Nat.add]; clear; lia);
      eapply stk_merge; [exact ST| apply stk_of_rw_cells; exact S| cbn [cells_size csize Nat.add] ] end.
  Local Ltac xa_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@L22163852504.143L22972055896.143L25741856728.143L29428324939.5  L31421052760.143L33232266840.143L34987518552.143L40379729343.142L42842486707.143L48958709976.143L52536714200.143L54486063391.143L57408231128.143L60968405464.143L6141606276.1   L64900869464.143L68463140952.143Q15899910614.143Q20510050466.143Q21926974294.143Q24435349718.143Q29963071266.143Q30445619798.143Q33963780182.143Q36223636898.143Q38324966690.143Q3859172566.143 Q39849717666.143Q39974853590.143Q43352947362.143Q4524655138.143 Q45996133718.143Q48510014166.143Q49411331106.143Q53371831074.143Q54531556438.143Q546509986.143  Q55602980898.143Q60541843414.143Q66569427286.143Q6961619874.143 Q7051364770.143 Q9887022678.143 00000700>00E00W00^00e00l01301:01A01H01c01j02102502<02C02[03703O03g04C04[05305O05k06C06_07707S07o08G08_09;09W09o0:K0:g0;?0;W0<30<O0<gS2ra2spS2ra2spS2ra2spS1R2lo3LOS3ALO3ACPS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1R2ra2sp2lo4SLO25NEEDR3SPRS2ra2spS2ra2spS2spS2ra2spS2ra2spS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOS". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma sa_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "Pv,$8.Pf,$8.Phc,(0.$4;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4=.$4;.VR,VHIA,Vh,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4>.(4?.$2.)R22.R21.R20.R1?.R1>.R1=.)P,(22.(1=.R1>.)(50.VnX,(1=.VdA,)(1=.VdB,)))P,(21.(2?.(10.$8.R1>.=)(2?.(10.$8.(51.R1?.)(26.(52.VdA,)(52.VdB,)))(10.$8.(53.R1?.)+1.)))(21.(10.$8.R1>.$54.)(2?.(10.$8.R1>.$55.)(30.(52.VdA,)(52.VdB,)))))P,(22.R25.(38.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(22.R25.(3>.Vd,))(56.$4;.(57.$4;.VR,VHIA,R25.Vmo,)$58.(47.(48.R20.(29.&40.(23.(=.&40.Vsp,)-80.))Vgp,Vtp,R1?.R1>.R1=.R1<.R1;.(29.&40.R21.)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)VF,(29.&40.+9>87<.)Vfc,(49.(3.&40.))R23.(4:.$4;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J NGX HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold SA_FRAME_A, aa_frame in FR1. replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 13 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold SA_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [| cbn [md_n]; exact NGX]. split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@D24976250634.169D50797141399.169D52014138856.169K3345721225.169 L21501700990.2  L29074096193.161L29074168500.164L3352129893.15  L35663928186.7  L60098763854.3  Q22285631880.166Q22285648010.163Q22286196081.165Q24974040330.168Q39212284437.166Q42081808994.166Q4926406185.166 Q52016320488.168Q54253886744.165Q56761401107.166Q6027349519.169 Q60511567613.166Q62965564504.167Q63231501142.163Q9538787269.163 00000O01I01h02^02e03<03S03T03i04304=04G04Q04j05405D05N05g06106>06W06_07607@07HS2ra2sp1X3xs02xs2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22xs5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO21p2xs5NEEDR3FSZ3DSX2HB5Ha_st5Hl_stS2dA2dBS2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16FS1R3HIA1h2sp2lo3TOP1HS1R2lo3LOSS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xs2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xs2X02HBS1X3xs02xsS1X3xs02xs2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xs2X0S1X3xs02xs2HB5Ha_st5Hl_stS3xs02xsS1X3xs02xs3X162HB5Ha_stS1X3xs02xsS3xs02xs". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma sa_SIGN : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    limbs_val (md_limbs dXc) = mpd_abs dA - mpd_abs dB ->
    v <= sub_abs_PHI dX dA dB ->
    f <= sub_abs_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 SB xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e85c) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg n p xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as CWX. cbn [md_addr] in CWX. rewrite <- HT1 in CWX.
    pose proof (munch_refl [(X, X + 16)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : HM asegs R HIA hc LBc LF m2 |- _ => rename H into HH2 end.
    match goal with H : aobj asegs AL (hcs asegs R HIA hc) m2 X 16 |- _ => rename H into OX2 end.
    match goal with H : rw_cells asegs m2 X _ |- _ => rename H into CX2 end.
    pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ 1 J0 MU WM MI2 CX2 ltac:(left; reflexivity) HH2 OX2) as J2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J2.
    eapply sa_ret; [exact J2| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| left; split; [reflexivity| split; [unfold mpd_val; cbn [md_sg md_limbs]; rewrite HVV; clear; lia| reflexivity]]| exact BV| exact BF].
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "SIGN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02M0@C11264273767.195C11264273767.196C237391055.197  D23374924298.199D26345934764.199D26351829262.196D32872594577.196D32879014451.199D39497720659.199D43803414146.196D53935720026.196D62012212072.199K11728656926.193K11728656926.194K19167344963.193K19167344963.194K25382859142.198K39785057286.198K46334408099.195K46334408099.196K46438937728.198K5410285399.197 K65977774223.198L10255219601.7  L11741563003.2  L1286294210.5   L146940511.10   L14858295739.5  L15721821085.5  L19173860537.5  L19949327823.6  L20925015897.9  L20935828777.10 L2188786020.3   L23100341967.171L23672846821.3  L2424955998.3   L25238078280.6  L25371356284.17 L26349732406.4  L26502719108.5  L27313416501.17 L27315443595.13 L27315444501.8  L27315886994.8  L2803465242.13  L2805482148.16  L2975768925.2   L29763661393.2  L29765106966.174L30168684972.14 L30661508504.1  L31411798818.8  L3370416396.3   L33922697967.1  L34125036709.12 L34848507734.5  L34848753617.6  L34848754511.9  L35663928186.7  L37382714296.6  L38235734261.1  L39794528764.4  L40065549985.0  L40613469158.2  L41072328611.171L41126667518.5  L41590708471.3  L42633816569.1  L43178104794.9  L43343125556.5  L43878034250.5  L44631303542.4  L45672603263.14 L45674556632.8  L45674766529.10 L46160487540.175L46323034201.4  L46428582412.2  L47439038290.12 L47440770549.7  L47441212786.8  L47441213932.21 L47441213932.9  L48157064005.171L49658103718.14 L49660279064.10 L53234647444.6  L53283758644.1  L53517043217.171L5416286893.4   L54976812668.3  L56386468090.3  L58609956177.2  L59310730064.5  L59310730065.8  L59751516949.1  L60098763854.3  L60283674290.11 L60973657551.4  L61145405211.199L6141606276.1   L61929067222.174L65506141272.7  L65971907957.4  L66151427842.19 L66151427842.20 L68065932444.8  L68151462958.5  L7406239801.8   L9244221278.6   O11264273767.195O11264273767.196O237391055.197  O35105909750.198O36632239767.193O36632239767.194O44976997556.198O48199580980.198O50423766113.198O54539614568.193O54539614568.194P11728656926.193P11728656926.194P46334408099.195P46334408099.196P46438937728.198P5410285399.197 Q12370813529.176Q17201186252.175Q23374924298.202Q26207421841.179Q26207721832.180Q26209866839.177Q26345934764.202Q31654082872.179Q32879014451.202Q35717815871.201Q37618859566.175Q38669227488.200Q38669227488.201Q39212284437.180Q39497720659.202Q43925228937.180Q45252829750.202Q49149041523.200Q49149041523.201Q49645664135.202Q5470531635.175 Q5485174314.176 Q59703481013.176Q60511567613.180Q60697995187.180Q6143569392.176 Q66030093059.180Q8882927371.177 Q9540557816.177 00000100200300400N01401V01n01o02o03n04F04G04H04n05T06B07007107207307407j08?08@08P09409D09T09U09i09j0:N0:Z0;00;80;@0;R0;S0;_0<30<40<50<60<70<80<90<@0<G0<c0<g0<k0=70=?0=C0=g0>30>40>50>J0>^0>b0>c0>d0>i0?]0?^0?g0?l0?m0@=0@D0@S0@T0@U0@V0A30A40A50A60A70A80AQ0AR0BB0BC0BD0BM0BQ0Bg0Bh0C00C80C?0CO0Cg0Ck0D50DY0Df0Dg0Dk0EX0F20F30FQ0FR0Fa0G10G70GK0GL0GM0GN0GO0GP0GQ0GR0GS0GT0GU0GV0GW0GX0GY0GZ0G[0G\0H90HE0HF0HR0H^0Hj0I<0IH0IX0IY0Ie0If0Ig0J30J40J@0JA0JB0JC0JD0JP0J\0J]0Jg0K60KB0L00L<0LFFFFFS2ra2sp1X3xs03pXc2xs1n3KU1S2ra2sp1X3xs01N3pXc2xs1n3KU14xs6h4LEN6S2ra2sp1X3xs01N3pXc2xs1n4xs6h4LEN6S2ra2sp1X3xs01N3pXc2xs1nFS1R2ra2sp1X3xs02lo4SLO21N3pXc2xs1n5NEEDR3LOS2X03SPR2P04xs6h4LEN6S1R3HIA1h2ra2sp1X3xs02hc1N3pXc2xs1n3TOP2X03SPR3HT12P04xs6h4LEN6S1R2ra2sp1X3xs03pXc2xs1nFFS1R2sp3xs02lo1N3pXc2xs1n2HN3LOS3ALO2PCS1R2sp3xs02lo1N3pXc2xs1n2HN3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n5NEEDR3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n5NEEDR3LOS3ALO2PCFFFFS2sp1X3xs02lo1N3pXc2xs1n2HN3x142N13XPc2x23x153x164POSTS2dA2dB1N2xs1n3HVV2c'FS1N2xs1n2HN4LEN1S1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScS1N2xs1n2HN4LEN1S1N2xs1n2HN4LEN1FS1R2sp2lo4SLO25NEEDRFS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScS2c'3HC03HC1S2ra2sp1X3xs03pXc2xs1nS1N1n2HNS1N1n2HNS1X1N3pXc1n2HN3XPcFS1N3pXc1n2HNS1R2sp2lo4SLO25NEEDRFFFFFFS1N3pXcS1N3NR1S2ra2sp1X3xs01N3pXc2xs1n3NR1S2spS2spS1N2xs1n3LHIS1N1n2HNS2spS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScS2sp3SPA3SPRFFS1R3HIA1h2sp2lo3TOP1HS1R2sp2lo4SLO25NEEDRS2loFSS1N1nS2ra2sp1X3xs01N3pXc2xs1n2HN2X03SPR2N12P03P473LHI3KU1FS2dA2dB1NS3pXcFS1N2xs1n2HN4LEN1S2sp2loS2c'3HC03HC12KCFFFS2ra2sp1X3xs03pXc2xs1n2X03X16FFFFFS2sp1N3pXc2xs1n2HN3SPR2P0FS2ra2sp1X3xs01N3pXc2xs1n2HN2X03SPR2P03P473LHI2N1FFS1N3pXc1nS2spS2ra2sp1X3xs03pXc2xs1nFS1N1n2HNS1N1n2HNS1N3NR1S1N3pXc1n2HN3KU1S1N3pXc1n2HN1H2H03KU22P0S2spS1R2lo3LOSS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR1a2NOS2dA2dB1N3BNDFS2spS2ra2sp1X3xs01N3pXc2xs1n2HN2X03SPR2P03P473LHIS1R2sp1X2lo4SLO25NEEDR3DSXFS3pXc1n2r04XPAL1q1r1H2H02q02H4FS1N2xs1n2HN3NR1S1N2xs1n2HN4LEN1S2xs1nS1N2xs1n2c'4xs6h3LV6FFFFFFFFFFFFFFFFFS2ra2sp1X3xs03pXc2xs1n2X03XALS1X3xs02xs1nFS1X3xs02xs1nS1X3xs02xs1nS1X3xs02xs1nS3xs03pXc2xs1n3KU1S1X3xs02xs1nS3xs01N3pXc2xs1nFS1X3xs02xs1nFFS1X3xs02xs1nFS1X3xs02xs1nFFFFS1X3xs02xs1nS1X3xs02xs1nFS3xs02xs1nS1X3xs02xs1n2X0S1X3xs02xs1nS1R2sp3xs02lo4SLO22xs1n5NEEDR3LOS4SP643ALO3ACPS1X3xs02xs1nS3xs02xs1n". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma sa_SUBINT : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (n : Z)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs9 xs11 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    md_own dXc = LHeap ->
    1 <= n <= md_n dXc ->
    limbs_val (md_limbs dXc) = mpd_abs dA - mpd_abs dB + 2 ^ (32 * n) ->
    v <= sub_abs_PHI dX dA dB ->
    f <= sub_abs_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (X + 10)) SHX xs5 xs6
              SB (Z_to_bv 64 (4 * n)) xs9 SH10 xs11 xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e810) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX EO HN HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc. unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 24 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 24) with (bv_unsigned sp + -128) in STc, SLOT by (clear; lia).
    (* [comment removed for export] *)
    pose proof XARR as PU. rewrite <- (firstn_skipn (Z.to_nat n) xs) in PU. apply u32arr_app in PU. destruct PU as [PUlo PUhi].
    rewrite firstn_length_le in PUhi by (clear - HN LEN1; lia). replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) in PUhi by (clear - HN; lia).
    assert (LHI : Z.of_nat (length (skipn (Z.to_nat n) xs)) = N - n) by (rewrite length_skipn; clear - HN LEN1; lia).
    pose proof (munch_refl [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -128 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -128)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj PUlo I) as PUlo'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. zstep.
    zstep. if_cases KU1; zify_cond KU1; [exfalso; clear - KU1 HN; lia|].
    zstep. zstep. zstep. zstep. if_cases KU2; zify_cond KU2; [exfalso; clear - KU2 HN P0; chk_ltb KU2; lia|].
    (* [comment removed for export] *)
    shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep. replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep. zstep. zstep.
    pose proof (A_mpi_core_sub_int_spec AL IMG) as SPC. unfold mpi_core_sub_int_stmtA, A_MPI_CORE_SUB_INT in SPC.
    acallxA_sp (bv_unsigned sp + -128)
      (eapply SPC with (X := pXc + 4 * n) (A := pXc + 4 * n) (n := N - n) (c := 1) (lo := lo) (xs := skipn (Z.to_nat n) xs) (ys := skipn (Z.to_nat n) xs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia;
       try eassumption; try reflexivity;
       first [ apply u32arr_ro; exact PUhi
             | left; split; reflexivity
             | clear - HN LEN1 LHI N1 NR1; lia
             | clear - XPAL HN; Z.div_mod_to_equations; lia
             | eapply aobj_sub; [exact OP| clear - HN; lia| clear - HN NR1 N1; lia]
             | unfold MPI_CORE_SUB_INT_STACK_A; clear - SLO2 NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
             | unfold MPI_CORE_SUB_INT_STACK_A; rewrite LHI; clear - XLSc SLO2 NEEDR HN; lia
             | clear - HN LEN1 LHI N1 NR1 P0 XPAL SLO2 NEEDR LOS SPA SPR LOSP XLSc; lia
             | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "CSI-PRE-LEFT:" g end ] ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CSI-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned sp + -128) |- _ => rename H into ST6 end.
    match goal with H : u32arr asegs m6 (pXc + 4 * n) ?l, H2 : length ?l = length _ |- _ => rename H into XHI6; rename H2 into LEN6; rename l into xs6h end.
    match goal with H : lval xs6h (N - n) - ?cc * _ = _, H2 : 0 <= ?cc, H3 : ?cc <= 1 \/ ?cc = 1 |- _ => rename H into LV6; rename H2 into HC0; rename H3 into HC1; rename cc into c' end.
    (* [comment removed for export] *)
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -128 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -128)] mc m6) in HH6;
      [| exact MU| exact WM| unfold MPI_CORE_SUB_INT_STACK_A; solve_w_writable].
    match goal with H : rw_cells asegs m6 (bv_unsigned sp + -128) _ |- _ => rename H into SL6 end.
    assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
    { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp + -104) with (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 24 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SL6. }
    destruct PUlo' as [PUlo _].
    pose proof (u32arr_transport asegs _ mc m6 _ _ PUlo MU WM) as PUlo6. rewrite firstn_length_le in PUlo6 by (clear - HN LEN1; lia).
    specialize (PUlo6 ltac:(cbn [disjoint_from]; unfold MPI_CORE_SUB_INT_STACK_A; clear - HN XLSc SLO2 NEEDR P0 NR1; lia)).
    assert (XARR6 : u32arr asegs m6 pXc (firstn (Z.to_nat n) xs ++ xs6h)).
    { apply u32arr_app. split; [exact PUlo6|]. rewrite firstn_length_le by (clear - HN LEN1; lia). replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) by (clear - HN; lia). exact XHI6. }
    assert (HW6 : forall a, ~ outside [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -128 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -128)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
    { intros a NO. cbn [outside] in NO. unfold MPI_CORE_SUB_INT_STACK_A in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN SLO2 NEEDR; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    assert (DJF : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -128 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -128)] (bv_unsigned sp - 104) 104).
    { cbn; unfold MPI_CORE_SUB_INT_STACK_A. split; [clear - XLSc SLO2 NEEDR HN; lia| split; [clear; lia| exact I]]. }
    assert (DJX : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -128 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -128)] X 16).
    { cbn; unfold MPI_CORE_SUB_INT_STACK_A. split; [clear - XPc HN; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]. }
    assert (LEN6' : length (firstn (Z.to_nat n) xs ++ xs6h) = length xs).
    { rewrite length_app, LEN6, length_skipn, firstn_length_le by (clear - HN LEN1; lia). clear - HN LEN1; lia. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6 DJF DJX XARR6 LEN6') as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    (* [comment removed for export] *)
    assert (L6Z : Z.of_nat (length xs6h) = N - n) by (rewrite LEN6; exact LHI).
    assert (VNEW : limbs_val (firstn (Z.to_nat n) xs ++ xs6h) = mpd_abs dA - mpd_abs dB + c' * 2 ^ (32 * N)).
    { rewrite limbs_val_app, firstn_length_le by (clear - HN LEN1; lia). replace (Z.of_nat (Z.to_nat n)) with n by (clear - HN; lia).
      change (limbs_val (firstn (Z.to_nat n) xs)) with (lval xs n).
      rewrite (limbs_val_lval xs6h), L6Z.
      pose proof (limbs_val_split xs n ltac:(clear - HN; lia) ltac:(clear - HN LEN1; lia)) as SPL.
      rewrite (limbs_val_lval (skipn (Z.to_nat n) xs)), LHI in SPL.
      replace (2 ^ (32 * N)) with (2 ^ (32 * n) * 2 ^ (32 * (N - n))) by (rewrite <- Z.pow_add_r by (clear - HN; lia); f_equal; clear; lia).
      assert (EQ6 : lval xs6h (N - n) = lval (skipn (Z.to_nat n) xs) (N - n) - 1 + c' * 2 ^ (32 * (N - n))) by (clear - LV6; lia).
      rewrite EQ6. rewrite SPL in HVV. clear - HVV. lia. }
    subst x2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KC; zify_cond KC; swap 1 2.
    - (* [comment removed for export] *)
      eapply sa_SIGN; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| cbn [md_limbs]; rewrite VNEW; rewrite ?Z.mod_small in KC by (clear - HC0 HC1; lia); rewrite KC; clear; lia| exact BV| exact BF].
    - (* [comment removed for export] *)
      eapply sa_ret; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| right; right; split; [reflexivity|]| exact BV| exact BF].
      pose proof (limbs_val_bound (firstn (Z.to_nat n) xs ++ xs6h)) as BND.
      rewrite length_app, LEN6, firstn_length_le, length_skipn in BND by (clear - HN LEN1; lia).
      rewrite ?Z.mod_small in KC by (clear - HC0 HC1; lia).
      assert (C1 : c' = 1) by (clear - KC HC0 HC1; lia).
      rewrite VNEW, C1 in BND. replace (Z.of_nat (Z.to_nat n + (length xs - Z.to_nat n))) with N in BND by (clear - HN LEN1; lia).
      clear - BND. lia.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "SUBINT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00e0@L10013191668.103L13679629912.103L16024124020.103L20817808472.103L22051162356.103L24695658136.101L29502821080.103L3991920500.103 L42606771444.102L44235170136.103L45988853080.102L45988853080.103L46254298584.103L48636430708.103L50393421374.99 L53392477144.103L54646761460.103L55688143946.102L60674471028.103L62842592998.101L65656017752.103L66683159284.103L8090362072.103 Q11801279589.105Q11801279589.106Q12625347329.102Q13130782593.102Q13746912257.102Q17056504010.101Q17056504010.102Q21228174890.104Q21228174890.105Q27566990629.104Q27566990629.105Q29105366474.102Q35116208202.102Q360992257.102  Q37024021121.102Q37145055361.101Q37145055361.102Q37624048842.102Q41143783114.102Q43651603274.102Q45162273921.102Q47152758090.102Q49146820865.102Q49698585326.103Q49698585326.104Q5300226131.102 Q5300226131.103 Q53180328906.102Q53306986881.102Q59193198154.10200000<00H00T00`00l01801D01P01\01h02402@02L02X02k03703C03V03b03n04:04F04R04j05V05_05h06106=06I06h07[08708g09309?09H09Q09Z09c09o0:;0:G0:P0:\0:e0;80;K0;S0;[0;g0<00<<S2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xsp3lo'2LOS2ra3xra3xspS2ra3xra3xspS2ra3xra3xsp3lo'2LOS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS3xra3xsp2HB5Ha_st5Hl_stS3xsp2y02HB5Ha_st5Hl_st2y12y22y32y42y52y62y7S3xsp3lo'S3xsp3lo'S3xsp3lo'S3xsp3lo'2LOS3xsp3lo'2LOS3xra3xsp3lo'2LO2HB5Ha_st5Hl_stS3xsp2y03lo'2LO2HB5Ha_st5Hl_st2y12y22y32y42y52y62y7S3xra3xsp3lo'2HB5Ha_st5Hl_stS3xsp2y03lo'2HB5Ha_st5Hl_st2y12y22y32y42y52y62y7S3xsp3lo'2LOS3xsp3lo'2LOS3xsp3lo'S3xsp3lo'S3xsp3lo'S3xsp3lo'S3xsp3lo'2LOS3xsp3lo'2LOS3xsp3lo'2LOS3xsp3lo'S3xsp3lo'2LOS3xsp3lo'S3xsp4SPR'2HB5Ha_stS3xsp4SPR'2HB5Ha_stS3xsp2HBS3xsp2HBS3xsp3lo'2LOS3xsp3lo'S3xsp3lo'2LO". (* [comment removed for export] *)
  #[using="HIA IMG ra"] Lemma core_sub_n0A : forall (CS : Z -> Prop) (xra xsp xgp xtp t0 t1 t2 y0 y1 a0 a1 a2 a3 a4 a5 a6 a7 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3 t4 t5 t6 : word)
      (FF : bvmap 5 word) (ffc : bv 32) (mm : mem) (lo' : Z),
    cs_ok AL CS -> mem_inv asegs mm -> stk asegs mm lo' (bv_unsigned xsp) -> lo' <= bv_unsigned xsp - 80 ->
    bv_unsigned xsp mod 16 = 0 -> crange CS lo' (bv_unsigned xsp - lo') -> bv_unsigned xra mod 2 = 0 -> a3 = Z_to_bv 64 0 ->
    evtA asegs AL CS
      (fun ms' : machine_state => exists (a4' : word) (m' : mem),
         ms' = MS (mkR xra xsp xgp xtp t0 t1 t2 y0 y1 (Z_to_bv 64 0) a1 a2 a3 a4' a5 a6 a7 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3 t4 t5 t6) FF
                 (ret_pc xra) ffc None m' (seg_rom asegs)
         /\ munch [(bv_unsigned xsp - 80, bv_unsigned xsp)] mm m' /\ wmono asegs mm m' /\ mem_inv asegs m' /\ stk asegs m' lo' (bv_unsigned xsp))
      (MS (mkR xra xsp xgp xtp t0 t1 t2 y0 y1 a0 a1 a2 a3 a4 a5 a6 a7 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3 t4 t5 t6) FF
          (Z_to_bv 64 A_MPI_CORE_SUB) ffc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until lo'; intros CSOK' MI ST LO SPA16 SCS' RAE' ->. unfold A_MPI_CORE_SUB.
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (cs_ok_sb _ _ CSOK') as SB64'.
    pose proof (bv_unsigned_in_range 64 xsp) as SPR'. unfold bv_modulus in SPR'. cbn [Z.pow Z.of_N Pos.pow] in SPR'.
    pose proof (proj1 ST) as LO0'.
    pose proof (munch_refl [(bv_unsigned xsp - 80, bv_unsigned xsp)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    do 12 zstep.
    (* [comment removed for export] *)
    do 12 zstep.
    release_frame FR ST (bv_unsigned xsp).
    finish.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "N0-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03J0@C24112444547.219D23374924298.225D24502936410.196D24502936410.219D24504905208.202D30202740417.219D30213615715.225D39497720659.225D42633159082.219D42643779336.225D59342652290.196D59342652290.219D59357728032.202D62012212072.225K10771443815.224K10771443815.226K11420089551.219K11728656926.217K11728656926.218K12094054176.202K19350120286.202K28284592895.217K28284592895.218K32498756882.222K36247032466.222K46438937728.222K48868404123.223K48868404123.225K55616087766.202K59873658948.199K59873658948.200K61717199003.222L10781994143.4  L10786545777.4  L11410546997.3  L11741563003.2  L12083187511.3  L12083502369.8  L12096050726.8  L1282143298.11  L1286294210.5   L14249421094.3  L16811220711.14 L16811253217.16 L18141400273.11 L19188710447.4  L19360473554.2  L19949327823.6  L20530645700.2  L22550422114.3  L23100341967.192L23643762344.6  L2424955998.3   L2428946895.12  L2428979913.10  L25858625233.2  L26502719108.5  L26589659220.5  L27313318451.16 L27313416501.14 L27315444501.8  L27315886994.8  L28274540293.4  L2975768925.2   L29971684470.4  L30168684972.14 L30661508504.1  L32509800680.3  L33922697967.1  L34846635767.12 L34848507734.5  L34848753617.6  L35144635169.0  L35663928186.7  L36252569448.16 L37410676568.7  L38213925978.12 L38214025052.10 L38235734261.1  L39039617557.1  L39449875093.8  L39451644133.8  L41128898453.2  L41590179991.3  L42633816569.1  L43629307734.4  L43878034250.5  L45905491903.5  L45918108856.6  L46428582412.2  L47797436189.12 L47844466047.11 L47844499065.13 L47846944728.7  L48857545612.4  L48862050147.4  L49658103718.11 L49658135712.13 L49929943149.15 L49930042219.16 L51284464315.192L51314995137.6  L52356417956.2  L53283758644.1  L55345850227.215L55600789184.3  L55601603799.8  L55614222288.10 L55614222288.8  L5802193334.7   L5803901713.12  L5803933719.13  L58177949655.192L58286053747.12 L58286086773.13 L58287746004.7  L59865231950.1  L59868486177.2  L60098763854.3  L60283674290.11 L60447858056.11 L60611602004.3  L61136745943.3  L6141606276.1   L61651670997.2  L61707527521.3  L62729654052.16 L62729686050.15 L64123984374.14 L66151427842.16 L66151427842.17 L8733446998.1   L9829757877.1   L9832141279.10  O11179910172.202O12406415574.202O14042253711.223O14042253711.225O186895464.202  O22331808284.220O23731696274.199O23731696274.200O24112444547.219O27573497883.217O27573497883.218O35105909750.222O38605364411.201O41080831185.224O41080831185.226O43419437345.222O44282969958.222O48091478445.221O53669666824.202O54539614568.217O54539614568.218O9464130022.222 P10771443815.224P10771443815.226P11420089551.219P11728656926.217P11728656926.218P14260335836.220P20526252370.202P46438937728.222P48868404123.223P48868404123.225P52351369907.201P59873658948.199P59873658948.200P61147129901.221Q10044758524.197Q11826285690.230Q12370813529.198Q17207432298.197Q18347242623.229Q1946824128.197 Q21750490675.197Q21750569356.198Q23374924298.230Q30213615715.230Q33478850983.198Q36646300200.198Q37625261960.197Q39016945843.228Q39016945843.229Q39497720659.230Q40106689634.227Q40106689634.228Q40106689634.229Q42643779336.230Q45252829750.230Q45903101625.202Q47588311916.226Q47588311916.227Q47588311916.228Q47588311916.229Q49058237960.198Q49433500843.198Q49645664135.230Q53113263298.197Q5485126037.197 Q5485174314.198 Q5516068337.202 Q57633846657.202Q59564950637.230Q60807234163.198Q61264001456.198Q61264037391.197Q6143569392.198 Q66027932809.196Q66030093059.208Q66375044744.198Q67329072568.197Q8222473558.198 Q9827600259.226 Q9827600259.227 Q9827600259.228 Q9827600259.229 00000100201>02\03h05;06E06F07907c0900:O0;\0<H0<I0<J0<K0<L0<M0=70=\0>M0?>0@:0A60A70A80A90Ac0Ad0Ae0Bf0Bg0Bh0Bi0Bj0Bk0Bl0CK0Cc0D30D40D50D60DZ0De0Df0E:0E;0EE0Ek0F=0FE0FF0FG0FH0F\0Fl0Fm0Fn0Fo0G00G10G80GC0GG0GK0GL0GP0GQ0G]0G^0G_0H40H50HO0HP0HQ0HU0HY0I80I90I:0IC0IH0IT0I[0Io0JC0JD0JE0JF0JG0JH0JI0JJ0JK0JL0JM0JN0K40KH0KI0KM0LF0LG0LH0LI0Lh0Li0Lj0Lk0MQ0MR0MS0MT0MX0MY0Mc0NG0N^0Ng0Nh0Nl0Nm0Nn0No0O00O40OP0OQ0OU0OY0P=0P>0P?0P@0PA0PB0PC0PD0PE0PF0PG0PH0PI0PJ0PK0PL0PM0PN0PO0PP0PQ0PR0PS0PT0PU0PV0PW0PX0PY0PZ0P[0P\0P]0P^0P_0P`0Pa0Q60Q70Qd0R80R90RN0Rc0S80S90SW0SX0Sm0TA0TB0TC0TD0TE0TF0TG0T]0T^0U90U:0U;0U<0U=0U>0V50V60VK0V_0W30W>0WL0WM0WN0Wc0X80XL0Y80Yn0ZC0ZX0[L0[M0[N0[O0[PFFS1R3HIA1h2ra2sp1X3xs02dA2dB2hc2xs2pa2pb3ysA3zsB2A02B03TOP2X03SPR3HT13YAB3ZBBS1R3HIA1h2ra2sp1X3xs02dA2dB2hc3pXc2xs1n2pa2pb3ysA3zsB2A02B03TOP2X03SPR3HT13YAB3ZBB2P03xs64LEN6S1R3HIA1h2ra2sp1X3xs02dA2dB2hc2xs2pa2pb3ysA3zsB2A02B03TOP2X03SPR3HT13YAB3ZBBS2ra2sp1X3xs02dA2dB1N3pXc2xs1n2pa2pb3ysA3zsB2HN2A02B02X03SPR3YAB3ZBB2N12P03xs64LEN6S2ra2sp1X3xs02dA2dB1N3pXc2xs1n2pa2pb3ysA3zsB2HN2A02B02X03SPR3YAB3ZBB2N12P0FS2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsB3xs64LEN6S2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsBS1R2ra2sp1X3xs02dA2dB2lo4SLO22xs2pa2pb3ysA3zsB2A02B05NEEDR3LOS2X03SPR3YAB3ZBBS1R2ra2sp1X3xs02dA2dB2lo4SLO23pXc2xs1n2pa2pb3ysA3zsB2A02B05NEEDR3LOS2X03SPR3YAB3ZBB2P03xs64LEN6S1R2ra2sp1X3xs02dA2dB2lo4SLO22xs2pa2pb3ysA3zsB2A02B05NEEDR3LOS2X03SPR3YAB3ZBBS1R2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsBFFFFFS1R2sp3xs02lo4SLO23pXc2xs2pa3ysA3YAS5NEEDRS1R2sp1X3xs02lo4SLO23pXc2xs5NEEDR3DSXS1R2sp3xs02lo1N3pXc2xs1n3ysA3zsB2HN3LOS3ALO2N12PCS1R2sp3xs02lo1N3pXc2xs1n3ysA3zsB2HN3LOS3ALO2N12PCS1R2sp3xs02lo4SLO21N3pXc2xs1n3ysA3zsB2HN5NEEDR3LOS3ALO2N12PCS1R2sp3xs02lo4SLO21N3pXc2xs1n3ysA3zsB2HN5NEEDR3LOS3ALO2N12PCFFFS1R2sp3xs02lo4SLO23pXc2xs2pb3zsB3ZBS5NEEDRFFS2sp1X3xs02lo1N3pXc2xs1n3ysA3zsB2HN3x142NZ2N13XPc2x23x153x164POSTFFFFFFS1R2sp2lo4SLO22pa3ysA3YAS5NEEDRS1N2xs1n3ysA3zsB2HN4LEN1S1N2xs1n2HN4LEN1FFFS2dA2dB2xs1n3ysA3zsB2VA2VB1c3xs63LV6S1N1n2HN2NZFS1R2sp2lo4SLO25NEEDRFS1c3HC62KCS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsBS1X1N3pXc1n2HN3XPcS1N1n2HNFFFS1R2sp2lo4SLO25NEEDRS2dA2dB2xs2VB2VAFFFFFS1N3pXcS1N1n2HN2NZS2spS2spFS2spFS2sp3SPA3SPRFSS1R3HIA1h2sp2lo3TOP1HFS1R2sp1X2lo4SLO25NEEDR3DSXFFS2loS2spS1R2sp2lo4SLO21N3pXc5NEEDR4XLScFFS2dA2dB1nS3pXcS1N3pXc1n2HNS2sp2loS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRFFFFFFFFFFFS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsBS1R2sp2lo4SLO25NEEDRFS2spS2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsB1c3xs63HC64LEN6FFFS1R2sp2lo4SLO22pb3zsB3ZBS5NEEDRFFFS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsBFFFS2spFS1R2lo3LOSS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR1a2NOS1N2xs1n3ysA3zsB2HN3NR1S2dA2dB1nFS2spFFFFS2spS3pXc2r04XPAL1q1r1H2H02q02H4FS2spS2spS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS3xs02dA2xs1n3ysA3zsBFS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsB2X03XALS1X3xs02xs1n3ysA3zsBFS3xs02dB2xs1n3ysA3zsBS3xs02dB2xs1n3ysA3zsBS3xs02dB2xs1n3ysA3zsBFS3xs01N3pXc2xs1n3ysA3zsB2HN2N1FS3xs02dB2xs1n3ysA3zsBS1X3xs02xs1n3ysA3zsBFFFFFFS3xs03pXc2xs1n3ysA3zsBFS1R2sp3xs02lo4SLO22xs5NEEDRFFFFFS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsB2A02B03BAL2X03SPRFS3xs02dB2xs1n3ysA3zsBS1X3xs02xs1n3ysA3zsBS1X3xs02xs1n3ysA3zsBS2sp3xs02xsS2sp3xs02lo2xsFFS3xs02dA2xs1n3ysA3zsBS3xs02dA2xs1n3ysA3zsBS1X3xs02xs1n3ysA3zsBS1R2sp3xs02lo4SLO22xs5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22xs1n3ysA3zsB5NEEDR3LOS4SP643ALO3ACPS3xs02dA2xs1n3ysA3zsBS3xs02dA2xs1n3ysA3zsBS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsB2A03AAL2X03SPRFFFF". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma sa_CSUB : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (n pa sa na : Z) (pda : word) (pb sb nb : Z) (pdb : word)
      (ysA zsB : list word) (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs4 xs11 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    0 <= n <= md_n dXc ->
    (1 <= n -> md_own dXc = LHeap) ->
    rw_cells asegs mc (md_addr dA) (mpi_cells pa (Z_to_bv 64 sa) na pda) ->
    aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dA) 16 ->
    0 < md_addr dA -> md_addr dA + 16 <= 2 ^ 64 -> md_addr dA mod 8 = 0 ->
    bytes_at asegs mc pa (u32s ysA) ->
    n <= Z.of_nat (length ysA) ->
    pa = md_p dXc /\ ysA = md_limbs dXc \/ pa + 4 * Z.of_nat (length ysA) <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= pa ->
    pa mod 4 = 0 ->
    (1 <= n -> 0 < pa) ->
    pa + 4 * Z.of_nat (length ysA) <= lo \/ bv_unsigned sp <= pa ->
    (1 <= n -> aobj asegs AL (hcs asegs R HIA hc) mc pa (4 * n)) ->
    rw_cells asegs mc (md_addr dB) (mpi_cells pb (Z_to_bv 64 sb) nb pdb) ->
    aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dB) 16 ->
    0 < md_addr dB -> md_addr dB + 16 <= 2 ^ 64 -> md_addr dB mod 8 = 0 ->
    bytes_at asegs mc pb (u32s zsB) ->
    n <= Z.of_nat (length zsB) ->
    pb = md_p dXc /\ zsB = md_limbs dXc \/ pb + 4 * Z.of_nat (length zsB) <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= pb ->
    pb mod 4 = 0 ->
    (1 <= n -> 0 < pb) ->
    pb + 4 * Z.of_nat (length zsB) <= lo \/ bv_unsigned sp <= pb ->
    (1 <= n -> aobj asegs AL (hcs asegs R HIA hc) mc pb (4 * n)) ->
    lval ysA n + 2 ^ (32 * n) * limbs_val (skipn (Z.to_nat n) (md_limbs dXc)) = mpd_abs dA ->
    lval zsB n = mpd_abs dB ->
    v <= sub_abs_PHI dX dA dB ->
    f <= sub_abs_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              (Z_to_bv 64 (X + 10)) xs4 (Z_to_bv 64 (Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 (Z.shiftr X 3)) SB (Z_to_bv 64 (4 * n)) (SHA (md_addr dB)) SH10 xs11
              xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e7d8) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX HN EOn CEA OEA A0 A16 AAL YA LYA DJA PAL PA0 YAS OAL CEB OEB B0 B16 BAL ZB LZB DJB PBL PB0 ZBS OBL VA VB BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1, CEA, CEB.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 24 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 24) with (bv_unsigned sp + -128) in STc, SLOT by (clear; lia).
    pose proof (u32ro_bound _ _ _ _ YA) as YAB. pose proof (u32ro_bound _ _ _ _ ZB) as ZBB.
    pose proof (munch_refl [(pXc, pXc + 4 * n); (bv_unsigned sp + -128 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -128)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec n 0) as [EN0|NZ].
    - (* [comment removed for export] *)
      subst n. clear MU WM. pose proof (munch_refl [(bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
      zstep.
      acallxA_sp (bv_unsigned sp + -128)
        (eapply core_sub_n0A with (lo' := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia; try eassumption; try reflexivity;
         first [ clear - SLO2 NEEDR LOS; lia
               | clear - SPA SPR LOSP; lia
               | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
               | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "N0CALL-PRE-LEFT:" g end ] ]).
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-N0CALL-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo (bv_unsigned sp + -128) |- _ => rename H into ST6 end.
      match goal with H : rw_cells asegs m6 (bv_unsigned sp + -128) _ |- _ => rename H into SL6 end.
      pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
      apply (hm_munch asegs R HIA hc LBc LF [(bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)] mc m6) in HH6;
        [| exact MU| exact WM| solve_w_writable].
      assert (ST6' : stk asegs m6 lo (bv_unsigned sp - 104)).
      { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp - 104) with (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 24 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SL6. }
      pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m6 J0 MU WM MI6 ST6' HH6
                    ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      (* [comment removed for export] *)
      zstep.
      eapply sa_SIGN; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| cbn [md_limbs]| exact BV| exact BF].
      rewrite lval_0 in VA, VB. change (skipn (Z.to_nat 0) xs) with xs in VA. rewrite Z.mul_0_r, Z.pow_0_r in VA. clear - VA VB. lia.
    - (* [comment removed for export] *)
      pose proof (EOn ltac:(clear - NZ HN; lia)) as EO. subst own.
      ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
      pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
      assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
        by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
      pose proof (A_mpi_core_sub_spec AL IMG) as SPC. unfold mpi_core_sub_stmtA, A_MPI_CORE_SUB in SPC.
      zstep.
      acallxA_sp (bv_unsigned sp + -128)
        (eapply SPC with (X := pXc) (A := pa) (B := pb) (n := n) (lo := lo) (xs := xs) (ys := ysA) (zs := zsB);
         rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia;
         try eassumption; try reflexivity;
         first [ rewrite LEN1; exact DJA
               | rewrite LEN1; exact DJB
               | clear - HN LEN1 N1 NR1 LYA LZB; lia
               | clear - XPAL; Z.div_mod_to_equations; lia
               | apply PA0; clear - NZ HN; lia
               | apply PB0; clear - NZ HN; lia
               | eapply aobj_sub; [exact OP| clear; lia| clear - HN; lia]
               | apply OAL; clear - NZ HN; lia
               | apply OBL; clear - NZ HN; lia
               | unfold MPI_CORE_SUB_STACK_A; clear - SLO2 NEEDR LOS; lia
               | clear - SPA SPR LOSP; lia
               | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
               | unfold MPI_CORE_SUB_STACK_A; rewrite LEN1; clear - XLSc SLO2 NEEDR; lia
               | unfold MPI_CORE_SUB_STACK_A; clear - YAS SLO2 NEEDR; lia
               | unfold MPI_CORE_SUB_STACK_A; clear - ZBS SLO2 NEEDR; lia
               | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "CSUBCALL-PRE-LEFT:" g end ] ]).
      clear SPC.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CSUBCALL-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo (bv_unsigned sp + -128) |- _ => rename H into ST6 end.
      match goal with H : rw_cells asegs m6 (bv_unsigned sp + -128) _ |- _ => rename H into SL6 end.
      match goal with H : u32arr asegs m6 pXc ?l, H2 : length ?l = length xs |- _ => rename H into XARR6; rename H2 into LEN6; rename l into xs6 end.
      match goal with H : lval xs6 n - ?cc * _ = _, H2 : 0 <= ?cc <= 1, H3 : skipn _ xs6 = _ |- _ => rename H into LV6; rename H2 into HC6; rename H3 into SK6; rename cc into c end.
      pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
      apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * n); (bv_unsigned sp + -128 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -128)] mc m6) in HH6;
        [| exact MU| exact WM| unfold MPI_CORE_SUB_STACK_A; solve_w_writable].
      assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
      { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp + -104) with (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 24 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SL6. }
      assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * n); (bv_unsigned sp + -128 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -128)] a ->
                    (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
      { intros a NO. cbn [outside] in NO. unfold MPI_CORE_SUB_STACK_A in NO.
        assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN SLO2 NEEDR; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc, pXc + 4 * n); (bv_unsigned sp + -128 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -128)] (bv_unsigned sp - 104) 104).
      { cbn; unfold MPI_CORE_SUB_STACK_A. split; [clear - XLSc SLO2 NEEDR HN; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc, pXc + 4 * n); (bv_unsigned sp + -128 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -128)] X 16).
      { cbn; unfold MPI_CORE_SUB_STACK_A. split; [clear - XPc HN; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6 DJF DJX XARR6 LEN6) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      assert (VNEW : limbs_val xs6 = mpd_abs dA - mpd_abs dB + c * 2 ^ (32 * n)).
      { rewrite (limbs_val_split xs6 n ltac:(clear - HN; lia) ltac:(rewrite LEN6; clear - HN LEN1; lia)). rewrite SK6.
        clear - LV6 VA VB. lia. }
      subst x2.
      (* [comment removed for export] *)
      zstep. if_cases KC; zify_cond KC; rewrite ?Z.mod_small in KC by (clear - HC6; lia).
      + eapply sa_SIGN; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| cbn [md_limbs]; rewrite VNEW, KC; clear; lia| exact BV| exact BF].
      + assert (C1 : c = 1) by (clear - KC HC6; lia). rewrite C1.
        eapply sa_SUBINT; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| reflexivity| cbn [md_n]; clear - HN NZ; lia| cbn [md_limbs]; rewrite VNEW, C1; clear; lia| exact BV| exact BF].
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "CSUB-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L26547048773.56L53778998493.56L64577079243.5600000>00M00\S2ra2xs2na3HnaS2ra2xs2na1n2HnS2ra2xs2na1n2Hn". (* [comment removed for export] *)
  #[using="ra"] Lemma zext_low : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "Pxs,(1.(3.&40.))Pna,$8.Pn,$8.Pk,$74.P,(2?.(22.=R2.)(22.R2.R3.))P,(22.R4.(6?.(70.(3.&40.)R5.)))(10.$8.(71.(17.(3.&40.)(75.(3.&40.)(73.R5.)R6.)(76.(3.&40.)(29.&40.=)R3.))R4.)(71.R6.R4.))")
(* [comment removed for export] *).
  Proof.
    intros xs na n k Hn Hna. apply lval_ext. rewrite firstn_app, firstn_firstn, firstn_length_le by lia.
    replace (Z.to_nat n - Z.to_nat na)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L26547048773.56L43727839089.56L64577079243.5600000>00M00\S2ra2xs2na3HnaS2ra2xs2na1n2HnS2ra2xs2na1n2Hn". (* [comment removed for export] *)
  #[using="ra"] Lemma zext_high : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "Pxs,(1.(3.&40.))Pna,$8.Pn,$8.Pk,$74.P,(2?.(22.=R2.)(22.R2.R3.))P,(22.R4.(6?.(70.(3.&40.)R5.)))(10.$8.(59.(72.(3.&40.)(73.R4.)(17.(3.&40.)(75.(3.&40.)(73.R5.)R6.)(76.(3.&40.)(29.&40.=)R3.))))(77.R6.R4.R5.))")
(* [comment removed for export] *).
  Proof.
    intros xs na n k Hn Hna. rewrite skipn_app, firstn_length_le by lia. replace (Z.to_nat n - Z.to_nat na)%nat with 0%nat by lia. rewrite skipn_O.
    rewrite limbs_val_app, limbs_val_repeat0, Z.mul_0_r, Z.add_0_r.
    unfold lseg, lval. rewrite skipn_firstn_comm. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rideS (dE : mpd) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop :=
    md_addr dE = X \/ (JBE dE /\ BJE dE hc LBc mc dXc).

  #[using="JC"] Lemma rideS_transport : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PdE,$7.PEX,(1.$2.)Pv,$8.Pf,$8.Phc,(0.$4;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pm2,P,(3.&40.)(5.(3.&8.))Ph2,(0.$4;.VR,VHIA,)PLB2,(1.$2.)P,(4=.$4;.VR,VHIA,Vh,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4>.R:.R9.R8.R7.R6.R5.R4.)P,(78.R<.R8.R7.R6.R5.)P,(79.$4;.VR,(17.$2.R<.R8.)VLF,(26.(=.&40.Vsp,)+68.)(25.VR,)(3;.$4;.VR,VHIA,R9.)(4?.$7:.)R7.R5.)P,(2;.$4;.R6.)P,Px,$8.P,(2>.$4;.VR,VHIA,R<.R1.)(2>.$4;.VR,VHIA,R8.R2.)P,(9.$4;.VR,VHIA,R7.R6.VLF,R8.)P,Pb,$2.P,(7;.$2.R1.R=.)(7;.$2.R2.R9.)(78.R12.R9.R=.R:.R;.)")
(* [comment removed for export] *).
  Proof.
    intros dE EX v f hc LBc mc dXc m2 h2 LB2 J [E|[DBJ B]] HP MI2 HCS2 HH2 INC; [left; exact E| right; split; [exact DBJ|]].
    eapply (bja_transport _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ J B HP MI2 HCS2 HH2 INC).
  Qed.

  #[using="JC"] Lemma rideS_finish : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PdE,$7.Pv,$8.Pf,$8.Phd,(0.$4;.VR,VHIA,)PLBd,(1.$2.)PAn,$8.Pcnt,$8.Pys,(1.(3.&40.))Pme,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pm5,P,(3.&40.)(5.(3.&8.))P,(7<.$4;.VR,VHIA,Vh,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4>.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(78.R<.R9.R8.R4.R3.)P,(64.(65.(66.$8.$8.)(67.$8.$8.VX,(23.VX,+10.))(4?.(66.$8.$8.)))R5.R3.)P,(68.$4;.R6.R4.)(78.R?.R<.(65.(66.$8.$8.)(67.$8.$8.R:.(1<.+4.R9.))R;.)R5.(4<.VX,(53.R6.)R9.R:.R8.(7=.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))$1:.))")
(* [comment removed for export] *).
  Proof.
    intros dE v f hd LBd An cnt ys me dXc m5 D [E|[DBJ B]] MU WM; [left; exact E| right; split; [exact DBJ|]].
    eapply (bja_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ D B MU WM).
  Qed.

  #[using="JC"] Lemma rideS_zfree : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$4;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.PAn,$8.Pcnt,$8.Pys,(1.(3.&40.))Pm4,P,(3.&40.)(5.(3.&8.))Ph4,(0.$4;.VR,VHIA,)P,(4=.$4;.VR,VHIA,Vh,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4>.(65.(66.$8.$8.)(67.$8.$8.R5.(1<.+4.R4.))(4?.(66.$8.$8.)))R;.R:.R9.R8.R7.R6.)P,(7>.$4;.VR,VLB,VLF,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vlo,R9.R6.R5.R4.R8.R7.)P,(78.R>.R;.R:.R9.R8.)P,(10.$11.(12.R9.)$1:.)P,(79.$4;.VR,(7?.(1;.R:.)(65.(66.$8.$8.)(67.$8.$8.R9.(1<.+4.R8.))R<.))VLF,(26.(=.&40.Vsp,)+68.)(25.VR,)(3;.$4;.VR,VHIA,R=.)(65.(66.$8.$8.)(67.$8.$8.(1;.R:.)(23.(1;.R:.)(1<.+4.(1=.R:.))))(4?.(66.$8.$8.)))R;.R6.)P,(2;.$4;.R7.)P,Px,$8.P,(2>.$4;.VR,VHIA,R10.R1.)(2>.$4;.VR,VHIA,R9.R2.)P,(9.$4;.VR,VHIA,R8.(7?.(1;.R=.)(65.(66.$8.$8.)(67.$8.$8.R<.(1<.+4.R;.))R?.))VLF,R9.)(78.R14.R9.(7?.(1;.R>.)R10.)R:.R>.)")
(* [comment removed for export] *).
  Proof.
    intros dE v f hc LBc mc dXc An cnt ys m4 h4 J FBx [E|[DBJ B]] EO HP MI4 HCS4 HH4; [left; exact E| right; split; [exact DBJ|]].
    eapply (bja_zfree _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ m4 h4 J FBx B EO HP MI4 HCS4 HH4).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L19957680682.4L56053389009.6L57154143136.6L7845029754.4 00000>00Q00e012S2sp2lo2dE3EL5S2dE2An3cnt1k2Hk2ELS2dE2An3cnt1k2Hk3ESAS2sp2lo2dE2ES". (* [comment removed for export] *)
  #[using="JC"] Lemma rideS_fresh_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$4;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.PAn,$8.Pcnt,$8.Pys,(1.(3.&40.))Pk,$8.Pm3,P,(3.&40.)(5.(3.&8.))P,(4=.$4;.VR,VHIA,Vh,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4>.(65.(66.$8.$8.)(67.$8.$8.R5.(1<.+4.R4.))(4?.(66.$8.$8.)))R;.R:.R9.R8.R7.R6.)P,(7>.$4;.VR,VLB,VLF,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vlo,R9.R6.R5.R4.R8.R7.)P,(78.R>.R;.R:.R9.R8.)P,(2?.(22.=R5.)(22.R5.(1<.+4.R7.)))P,(64.(65.(66.$8.$8.)(67.$8.$8.R9.(23.R9.R6.))(65.(66.$8.$8.)(67.$8.$8.Vlo,(23.(=.&40.Vsp,)-68.))(4?.(66.$8.$8.))))R;.R5.)P,(68.$4;.R<.R6.)P,(80.(2>.$4;.VR,VHIA,R?.)(65.(66.$8.$8.)(67.$8.$8.R;.(23.R;.R8.))(65.(66.$8.$8.)(67.$8.$8.Vlo,(23.(=.&40.Vsp,)-68.))(4?.(66.$8.$8.)))))(78.R13.R10.R?.R8.R=.)")
(* [comment removed for export] *).
  Proof.
    intros dE v f hc LBc mc dXc An cnt ys k m3 J FBx [E|[DBJ B]] Hk MU WM WC; [left; exact E| right; split; [exact DBJ|]].
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC dE DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof (bja_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ J FBx B) as [ESA ELA].
    eapply bja_munch; try eassumption.
    - cbn. split; [clear - ESA Hk; lia|]. split; [clear - ES; lia| exact I].
    - intros BN. cbn. split; [pose proof (ELA BN) as EL; clear - EL Hk; lia|].
      split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L11129613429.12L13419968508.8 L45080137934.5 L64145259332.8 00000R01001B01_S1R3HIA1h2sp3wlo3whi3Hhi3TOP5HTOP0S2sp2lo2dE3wlo3whi3Hlo3Hhi3EL5S1R2lo3wlo3Hlo3LOSS2sp2lo2dE3wlo3whi3Hlo3Hhi2ES".
  #[using="JC"] Lemma rideS_stk_munch : forall (dE : mpd) (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (wlo whi : Z) (m3 : mem),
    XJ0 v f hc LBc mc dXc -> rideS dE hc LBc mc dXc -> lo <= wlo -> whi <= bv_unsigned sp - 104 ->
    munch [(wlo, whi)] mc m3 -> wmono asegs mc m3 -> rideS dE hc LBc m3 dXc.
  Proof.
    intros dE v f hc LBc mc dXc wlo whi m3 J0 [E|[DBJ B]] Hlo Hhi MU WM; [left; exact E| right; split; [exact DBJ|]].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HS1.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP0.
    assert (B3 : BJE dE hc LBc m3 dXc).
    { eapply bja_munch; try eassumption.
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS0| clear - LOS Hlo; lia| rewrite HS1; clear - HTOP0 TOP LOSP Hhi Hlo; lia]| apply Forall_nil].
      - cbn. split; [clear - ES Hlo Hhi; lia| exact I].
      - intros BN. cbn. split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5 Hlo Hhi; lia| exact I]. }
    destruct B3 as [A1 A2 A3 A4 A5]. constructor; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L62463072682.3000009S2xs1n2Hn". (* [comment removed for export] *)
  #[using="Type"] Lemma lval_app_l : forall (xs zs : list word) n, 0 <= n <= Z.of_nat (length xs) -> lval (xs ++ zs) n = lval xs n.
  Proof. intros xs zs n Hn. unfold lval. rewrite firstn_app. replace (Z.to_nat n - length xs)%nat with 0%nat by (clear - Hn; lia). cbn [firstn]. rewrite app_nil_r. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition KJ_stmt (n NA : Z) : Prop := forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    SPL mc ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    0 <= n <= NA ->
    NA <= md_n dXc ->
    (1 <= NA -> md_own dXc = LHeap) ->
    (md_addr dA = X -> md_n dXc = NA /\ limbs_val (md_limbs dXc) = mpd_abs dA) ->
    (md_addr dA <> X -> md_n dA = NA) ->
    (md_addr dB = X -> lval (md_limbs dXc) n = mpd_abs dB) ->
    (md_addr dB <> X -> lval (md_limbs dB) n = mpd_abs dB /\ n <= md_n dB) ->
    v <= sub_abs_PHI dX dA dB ->
    f <= sub_abs_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              (Z_to_bv 64 (X + 10)) (Z_to_bv 64 (md_addr dA + 10)) xs5 (Z_to_bv 64 (Z.shiftr X 3)) SB (Z_to_bv 64 (4 * n)) (SHA (md_addr dB)) SH10
              (SHA (md_addr dA + 10)) xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e6f0) fc None mc (seg_rom asegs))
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06>0@C17025492443.265C17025492443.266C17025492443.267C53526081063.268C53526081063.269C53526081063.270D10380291872.290D10380291872.297D10847206599.295D14178172153.203D14190867032.294D15901575446.251D20201464024.294D20214132345.203D2158531065.203 D22000850582.172D22466435734.271D22638901081.289D22638901081.291D22638901081.296D22643014136.200D22643014136.203D23186196919.271D24976250634.225D24976250634.300D50797141399.225D50797141399.226D50797141399.300D50818716548.172D52014138856.225D52014138856.226D52014138856.300D57950589477.251D59228252318.300D60109446735.271D62155808737.226D62155808737.300D7340709316.271 D8160936825.202 D8165051864.294 D8734838546.295 D939044794.271  K12565428082.251K1329197271.268 K1329197271.269 K1329197271.270 K16174975305.251K2612272047.267 K2612272047.271 K3345721225.226 K3345721225.300 K3345721225.301 K38856059124.301K42587433812.172K42587433812.251K46911551239.225K46911551239.226K46911551239.300K46911551239.301K57790897799.225K57790897799.226K57790897799.300K57790897799.301K61538741255.225K61538741255.226K61538741255.300K61538741255.301K7412424035.271 K8616265952.267 K8616265952.271 K9644101664.265 K9644101664.266 K9644101664.267 L10307112399.6  L10379880580.5  L10847386467.5  L10981993624.1  L11277620759.203L12483832067.1  L12553287539.3  L12755534717.10 L12755534717.9  L1342025005.3   L14533354851.3  L14748712526.18 L14751320984.1  L14760987928.8  L15330064952.4  L16187148616.3  L16473205958.6  L16473494895.4  L16962092547.167L17585880332.14 L17871063442.5  L20515953304.1  L20562933465.11 L20679771697.6  L20679869488.10 L20803911415.2  L2166243551.4   L21800167073.0  L22479292268.1  L23100341967.214L23100341967.219L23100341967.253L23100341967.286L23199152784.5  L23332241046.14 L23615739305.3  L23999514035.214L23999514035.285L24313534829.3  L24313585860.4  L24313813357.7  L25044269509.2  L25046775673.252L25047280258.241L25640185240.1  L2607826517.4   L26950159893.14 L27332801253.1  L27481632834.8  L27481632834.9  L27954469902.3  L28231168598.1  L28655862141.3  L28927958424.1  L29397724604.3  L29576766064.3  L29770261488.3  L30743879498.8  L30744140956.30 L30747872606.3  L30748437532.18 L32513960931.3  L3352129893.15  L34412813842.32 L34424803280.3  L34846938932.1  L34859173495.30 L34859173495.32 L34936451766.1  L3519181112.12  L35352914354.18 L35353471283.4  L35365525810.32 L35365788388.10 L35655538624.7  L35655538630.7  L35663928186.7  L36655483780.5  L3667582691.3   L37079340467.167L37079340467.214L37079340467.222L37079340467.289L37667531699.239L37667531699.253L37667531699.285L38235734261.1  L38868673902.3  L38868673902.5  L39172636981.0  L39436426759.7  L39475339062.297L40132738746.30 L40294887048.3  L40437308144.3  L40449602357.4  L41389564045.11 L42455678978.5  L42594106808.2  L43625157983.1  L43631939593.32 L43878034250.5  L45674614936.1  L46160487540.219L46160487540.242L46160487540.287L46380960401.4  L46389908878.16 L46754254770.237L46756382136.214L46917722603.2  L46948640662.32 L47335295182.10 L47845385650.3  L47847399772.4  L48154966246.214L48157095910.237L49578233423.219L49578233423.286L49579218529.32 L49807695752.8  L5098421631.4   L5261871668.3   L54742141067.1  L547707976.3    L55610740483.239L55713073806.238L5572256557.16  L5630863510.2   L56412235289.5  L56577124758.2  L57008433794.5  L57784780907.2  L57869133146.30 L59308633593.3  L59308664813.4  L59308762472.4  L59308972243.3  L59321342699.2  L60098763854.3  L6141606276.1   L61527849707.2  L61562785068.30 L61611120794.225L61611120794.299L62018535662.1  L64600040930.4  L64811930313.11 L64934269637.2  L65603665675.1  L65925215236.5  L66151427842.16 L66661851587.4  L67431076118.2  L67601363691.1  L67833596567.4  L68505269079.5  L7400112281.3   L7419031306.30  L7555946507.1   L7735739976.14  L8243585534.4   L8378265800.15  L8612731009.4   L8616396945.8   L8733446998.1   L9631842885.2   L9951453048.12  N12524314323.266N20716133971.266O13435130648.269O17025492443.265O17025492443.266O17025492443.267O22987107037.267O22987107037.271O32329373691.271O37539299629.265O37539299629.266O37539299629.267O45218884275.267O45218884275.271O47864099224.269O53526081063.268O53526081063.269O53526081063.270O5986429080.271 O65801484870.270P1329197271.268 P1329197271.269 P1329197271.270 P27967082900.251P29564469130.269P29774741002.271P38856059124.226P38856059124.301P40437264079.265P40437264079.266P40437264079.267P40441743114.269P46402209908.270P7412424035.271 P9644101664.265 P9644101664.266 P9644101664.267 Q11801279589.172Q12370813529.218Q12370813529.223Q12370813529.262Q12370813529.297Q14534274354.294Q17205055869.296Q17205141463.222Q17207432298.217Q17207432298.261Q22466435734.271Q23186196919.271Q24974040330.225Q24974040330.300Q25513505925.171Q25513505925.250Q26207421841.222Q26207421841.250Q26207721832.223Q26207721832.251Q26207721832.298Q26207967338.220Q26207967338.261Q26207967338.295Q26209519061.297Q26222581589.248Q26992454707.251Q31651985788.297Q31653536963.261Q31654082872.222Q31654082872.250Q32513565618.294Q34060184889.250Q35074966634.169Q3667187378.294 Q37623358517.222Q37623376543.296Q37625261960.217Q37625261960.261Q38248387216.271Q39212284437.223Q39212284437.251Q39212284437.298Q42081808994.223Q42081808994.298Q42451157671.225Q42451157671.299Q42453173279.168Q42453173279.217Q43879899724.271Q43925228937.223Q43925228937.251Q43925228937.298Q48474732447.217Q48474732447.295Q49698585326.170Q49698585326.249Q50854331388.217Q50854331388.295Q52016320488.225Q52016320488.299Q52016320488.300Q53365265348.225Q53365265348.299Q53367281020.168Q53367281020.217Q5483308162.296 Q5483358760.222 Q5485126037.217 Q5485126037.261 Q5485174314.218 Q5485174314.223 Q5485174314.262 Q5485174314.297 Q5573176188.295 Q56993377951.247Q56993377951.261Q56993377951.295Q58585641145.171Q58874076138.248Q6027349519.225 Q6027349519.226 Q6027349519.299 Q6027349519.300 Q60511567613.223Q60511567613.251Q60511567613.298Q60697995187.223Q60697995187.251Q60697995187.298Q6143569392.218 Q6143569392.223 Q6143569392.262 Q6143569392.297 Q62157788641.225Q62157788641.299Q62965564504.224Q62965564504.298Q62965564504.299Q63333451516.247Q63333451516.261Q63333451516.295Q66028012439.190Q66028012439.286Q66030093059.251Q66030192691.268Q66030192693.172Q7317014269.201 Q7317014269.202 Q7329679452.292 Q7329679452.293 Q7329679452.294 Q7891539809.223 Q7891539809.297 Q8880503606.220 Q8880503606.295 Q8886727689.248 Q9536755962.248 Q9538787269.220 Q9538787269.295 00000100200300400500600700800900I00l02H02k03;03K04E04m04n04o05005105206006U07G08K09L0:`0;Y0<>0<`0=R0>W0>X0?I0?k0@]0@^0@n0AQ0B40Bm0DA0DB0DC0DD0EX0FV0GT0Ha0J<0KC0KD0L?0MJ0ND0O>0PD0QG0RA0S;0TA0UD0V>0W80X>0YA0YB0Z:0[20[30[40[50[I0[J0[K0[O0[_0[c0[d0[e0[f0[g0[h0\;0\<0\=0\J0\K0\^0\_0\o0]00]A0]E0]M0]V0]_0]`0^00^10^50^H0^[0_50_X0_g0_k0`50`H0`k0a80a90a:0aC0ae0bQ0bU0bV0bW0b[0b\0b]0b^0bb0bc0bg0c30c40c50c60cL0cM0cc0cd0ce0d30d40d50dA0dM0dQ0dZ0dl0dm0e?0e@0e[0f60fK0f_0f`0g00gC0gV0h90ha0i;0i^0ib0ic0id0ie0j;0j^0k50k80k90k:0k;0kO0kP0kQ0kg0kn0l20lL0m;0me0mf0mg0ni10910:10]10^10_10o11011m12@12c13G13H13_13i13m14714_15G15H15O15^15e16916:16M16X16g16h17317417>17B17C17f18]19a19d19o1:E1:N1:R1:f1;I1;Y1;`1;e1<41<D1<E1<l1=01=41=C1=J1=K1=_1=c1=d1=e1>J1>o1?01?11?21?31?41?51?61?71?81?91?:1?;1?<1?=1?>1??1?@1?A1?B1?C1?D1@U1AX1B[1B\1B]1CY1DU1EQ1FT1GW1GX1GY1GZ1G[1H71HQ1Hk1IL1J61Jl1KB1KL1KV1Kc1L?1Lc1M?1Md1NC1O51O?1OZ1Od1P?1PU1P_1Pl1QB1QX1R31SG1S]1Sj1T41TO1UE1VE1VS1WI1WS1Wi1X31X@1X\1Xf1YA1YW1Yg1ZC1Z^1[E1[`1\;1\Z1\d1]?1]U1^01^W1_01_Z1_h1`B1`a1aI1an1b<1bV1bd1c21cH1cR1c\1ci1d31d=1dJ1d`1eV1fE1fc1gJ1h61hU1i11iM1j21jZ1jb1k;1kO1k\1l:1lS1l]1lg1m41mJ1mf1nN1ne1oH1ok20J20[21521a22Y23Y24Q25=25>25?25@25A25B25R25n26826N26i27B27J27^FFFFFFFFFS2ra2sp1X3xs02xsS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS1R2ra2sp1X3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS2X03SPR2An3An02N12P04SLEN4DLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS2ra2sp1X3xs02xsS2ra2sp1X3xs02xsS1R2ra2sp1X3xs02lo4SLO22xs5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS2ra2sp1X3xs02NA3nXc3pXc2xs2An4SLEN4DLENFFFFFS2ra2sp1X3xs02NA3nXc3pXc2xs2X03SPR2An3An02N12P04Fcnt4SLEN4DLENS2ra2sp1X3xs02NA2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22NA2xs5NEEDR3LOS2X03SPR2An3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22xs2An5NEEDR3LOS2X03SPR3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS2X03SPR2An3An02P04ZLEN2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X3xs02hc2xs3TOP2X03SPR3HT12HB5Ha_st5Hl_stS2ra2sp1X3xs02NA2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1R3HIA2ra2sp1X3xs02NA3nXc3pXc2xs2h22An4TOP24SLEN4DLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo2NA3nXc3pXc2xs3LOS2An4SLEN4DLENS2ra2sp1X3xs02xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stFS2ra2sp1X3xs02xsS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS1R3HIA2ra2sp1X3xs02lo2NA3nXc3pXc2xs2h22An4TOP24SLEN4DLENS1R2sp1X3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS3ALO4LEN12N12PC4SLEN4DLEN2HB5Ha_st5Hl_stFFFS1R2sp1X3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS3ALO4LEN12N12PC4SLEN4DLEN2HB5Ha_st5Hl_stS1X3xs02dA2NA3nXc3pXc2xs3VA13ANX4LEN12An2N14Fcnt4SLEN4DLEN3SEPS1X3xs02dA2NA3nXc3pXc2xs3VA13ANX4LEN12An2N14Fcnt4SLEN4DLEN3SEPS1R2sp1X3xs02dA2lo4SLO22NA2xs5NEEDR3FSZ3ANX3DSX2HB5Ha_st5Hl_st3nXc3CNT3VA12AnS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs3VA15NEEDR3FSZ3ANX3DSX4LEN12An2N14Fcnt4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3FSZ3ANX3DSX4ZLEN2HB5Ha_st5Hl_stFS1R2sp1X3xs02dA2lo4SLO23pXc2xs5NEEDR3ANX3DSX2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3ANX3DSX2N14SLEN4DLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA2xs5NEEDR3ANX3DSX2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22xs5NEEDR3ANX3DSX2An2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3ANX3DSX2An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3ANX3DSX4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA2xs5NEEDR3ANX3DSX2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22xs5NEEDR3ANX3DSX2An2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3ANX3DSX2An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3ANX3DSX4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA2xs5NEEDR3ANX3DSX2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22xs5NEEDR3ANX3DSX2An2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3ANX3DSX2An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02dA2lo4SLO22NA3nXc2xs5NEEDR3ANX3DSX4ZLEN2HB5Ha_st5Hl_stFS1R2sp3xs02lo2NA3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo2NA3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENFFFS1R2sp2lo4SLO25NEEDRFFS2spS2ra2sp1X3xs02xsS2NAFFFFFS2sp2NA3nXc3CNT3SPRFFS1n2NA2HN3VBnFS2NA3nXc3CNT2An3A47FS2ra2sp1X3xs02xsFS1n2NA3nXc2HN3VBnS2spS1d1f2BFS2NA1v2BVS2NA1v2BVFS3nXc2xs4LEN12N1SS2AnS2ra2sp1X3xs02xs2AnS2ra2sp1X3xs02xs2AnS2ra2sp1X3xs02NA3pXc2xs2AnS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS2NA3nXc3CNT2AnS2spS1R3HIA2hcS2ra2sp1X3xs02xs2AnS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS3nXc3pXc3P47FFS3nXc3NR1S2ra2sp1X3xs02NA3nXc3pXc2xs3NR12AnS2ra2sp1X3xs02NA3nXc3pXc2xs3NR12An4SLEN4DLENS2spFFS2NAFFFS2spFS2spS2NA3nXc3CNTFFFS1R2sp2lo4SLO23NRM3SPRFS1R2sp2lo4SLO23NRA3SPRFFS1R2sp2lo4SLO2FFS2sp3SPA3SPRS2sp3SPA3SPRS2spS2NA1v2BVS1R3HIA2sp2h24TOP2FS1R3HIA2sp2h24TOP2FS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HS1R2sp2lo4SLO25NEEDRFS2ra2sp1X3xs02xsS2ra2sp1X3xs02xs2AnS2ra2sp1X3xs02xs2AnS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS2ra2sp1X3xs02NA3nXc3pXc2xs2An4SLEN4DLENS2ra2sp1X3xs02NA3pXc2xs2AnS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS2loFFSS1R3nXc3pXc2N12P02PC1HS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS2sp2NA3nXc3CNT3SPR3NR1S1XFFFS1R2sp2lo4SLO25NEEDRFFS2sp2NA3nXc3CNT3SPR2N1S2sp2loS2spS2ra2sp1X3xs02xs2X03X162AnS2ra2sp1X3xs02NA3nXc3pXc2xs2X03X162An4SLEN4DLENS2ra2sp1X3xs02NA3nXc3pXc2xs2X03X162An4ZLENFFS2ra2sp1X3xs02NA3nXc3pXc2xs2X03SPR2An3An02N12P04Fcnt4SLEN4DLEN3A47S1R2ra2sp1X2nX3xs02lo4SLO22NA3nXc2xs3CNT5NEEDR3LOS2X03LEN3ALO3SPR2An3An03AnC3NM1FS1R3HIA1h2sp2NA3BUD1v2BV3SPR2h23HV1FFS2LB4C24H3LBc2CIFS2ra2sp1X3xs02NA3nXc3pXc2xs2X03SPR2An3An02N12P03P474SLEN4DLENS2ra2sp1X3xs02xs2AnS2ra2sp1X3xs02NA3nXc3pXc2xs2An4ZLENS1R3HIA1h2sp1d4BUDF1f2BF3SPR2h24HFR1FS2NA3nXc3CNT2N12xs4LEN1S1X2X03X16S2spS1R3HIA2h2S2ra2sp1X3xs02NA3nXc3pXc2xs2An4SLEN4DLENS2ra2sp1X3xs02NA3nXc3pXc2xs2An4SLEN4DLENFS2sp2loS2NA3nXc3CNT2AnS2sp2loS1R2sp2lo4SLO25NEEDRFS2sp2NA3nXc3CNT3SPRS2An3An02KZS2NA3dXc3CNT2ENFS3pXc2KP2P0FS1R2lo3LOSS2spFS1R3HIA1h2sp2NA3BUD1v2hc2BV3SPR3HV1S2ra2sp1X2nX3xs02dA2NA3nXc2xs2An3CNT3ENA2X03SPR3An03NM1S2ra2sp1X2nX3xs02dA2NA3nXc3pXc2xs2An3ENA2X03SPR4LEN13An02P04ZLEN3ZN1S1RS1d2D01f2BFS2lo2NA3nXc3CNT2An3FloS3nXc3NR1S2spS1R2sp2lo4SLO25NEEDRS3pXc2r04XPAL1q1r1H2H02q02H42An3A16S3nXc3pXc2An3SEPS2sp2loS3nXcS2NA3nXc3CNT2N1S1R3HIA1h2sp3TOPFS1R3HIA1h2sp1d2D04BUDF1f2hc2BF3SPR4HFR1S2spS2spS2NA3nXc3CNT2N1S2sp2loFS2sp2lo3nXc3pXc4XLScS2spFFS2sp3xs02lo2NA3nXc2xs4SLEN4DLEN3x291CS2sp3xs02lo2NA3nXc2xs4SLEN4DLEN3x291CFFFFFFFFFFFFFFFFFFFFFS1R2sp1X3xs02lo4SLO22NA3nXc2xs5NEEDR2An2N14Fcnt3Flo4SLEN4DLEN2HB5Ha_st5Hl_st4FlenS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENFFS1R2sp3xs02lo2NA3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo2NA3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo2NA3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENFFFFS2sp1X3xs02xs2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2X03XAL2AnS2ra2sp1X3xs02xs2X03XAL2AnS2ra2sp1X3xs02NA3pXc2xs2X03XAL2AnS2ra2sp1X3xs02NA3nXc3pXc2xs2X03XAL2An4ZLENS1R2sp3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENS1X3xs02NA3nXc2xs4ZLENS1X3xs02xsS1X3xs02xsS1X3xs02NA2xsS3xs02NA3nXc2xs2An4SLEN4DLENS3xs02NA3nXc2xs2An2N14Fcnt4SLEN4DLENS1X3xs02NA2xs2HB5Ha_st5Hl_stS1X3xs02NA3nXc2xs4ZLEN2HB5Ha_st5Hl_stS2sp1X3xs02lo2xs2HB5Ha_st5Hl_stS1R2sp1X3xs02lo2NA3nXc2xs4SLEN4DLEN2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02NA3nXc2xs4SLEN4DLENS1X3xs02xsS1X3xs02NA3nXc2xs4SLEN4DLENS1X3xs02NA3nXc2xs4ZLENS1X3xs02xsS1X3xs02NA2xsS1X3xs02NA3nXc2xs4ZLENS1X3xs02NA3nXc2xs4ZLENS1X3xs02NA3nXc2xs4SLEN4DLENS1R2sp1X3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLEN2HB5Ha_st5Hl_stS1X3xs02NA3nXc2xs4ZLENS1X3xs02NA2xsS1X3xs02xsS1X3xs02NA3nXc2xs4SLEN4DLENS1R2sp3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENS1R2sp1X3xs02lo4SLO22NA3nXc2xs5NEEDR2N14SLEN4DLEN2HB5Ha_st5Hl_stS2sp3xs02xs2HBS1R2sp3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENS1X3xs02xsS1X3xs02NA3nXc2xs4ZLENS1X3xs02xsS1X3xs02NA2xsS3xs02lo2NA3nXc2xs4SLEN4DLENS1X3xs02xsS1X3xs02NA3nXc2xs4SLEN4DLENS1X3xs02NA3nXc2xs4ZLENS1X3xs02xs2X02HBS1X3xs02NA3nXc2xs2X04ZLEN2HBS1R2sp3xs02lo4SLO22xs5NEEDRS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR4ZLENS1R2sp3xs02lo4SLO22xs5NEEDRS1R2sp3xs02lo4SLO22xs5NEEDRS2sp3xs02lo2NA3nXc2xs4SLEN4DLENS1X3xs02xsS1X3xs02NA3nXc2xs4SLEN4DLENS1X3xs02NA3nXc2xs4ZLENS1R2sp3xs02lo4SLO22xs5NEEDRS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR4ZLENS2sp3xs02xs4SP642HB5Ha_stS2sp3xs02NA3nXc2xs4SP644SLEN4DLEN2HB5Ha_stS2sp3xs02lo2xsS2sp3xs02lo2NA3nXc2xs4ZLENS1X3xs02NA2xs2HB5Ha_st5Hl_st2AnS1X3xs02NA3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02NA3nXc2xs4ZLEN2HB5Ha_st5Hl_stS2sp3xs02lo2xsS2sp3xs02lo2NA3nXc2xs4ZLENS2sp3xs02lo2xsS2sp3xs02lo2xsS1X3xs02NA3nXc2xs4ZLENS1X3xs02xsS1X3xs02xsS1X3xs02NA2xsS1X3xs02xsS1X3xs02xsS1X3xs02NA2xsS1X3xs02NA3nXc2xs4ZLENS1R2sp3xs02lo4SLO22NA3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR2N14SLEN4DLENS1R2sp3xs02lo4SLO22NA2xs5NEEDRS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR4ZLENS1R2sp1X3xs02lo4SLO22xs5NEEDR2HB5Ha_st5Hl_stS2sp3xs02NA3nXc2xs4SLEN4DLEN2HBS1X3xs02NA2xs2HB5Ha_st5Hl_stS1X3xs02xs2An2HB5Ha_st5Hl_stS1X3xs02NA3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs02NA3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS3xs02xsS3xs02NA3nXc2xs4SLEN4DLENS3xs02NA3nXc2xs4ZLENS1X3xs02xs2X0S1X3xs02NA3nXc2xs2X04SLEN4DLENS1X3xs02NA3nXc2xs2X04ZLENS1X3xs02xsS1X3xs02xsS1X3xs02NA2xsS1X3xs02NA3nXc2xs4ZLENS1X3xs02xs2An2HB5Ha_st5Hl_stS1X3xs02NA3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs3X162HB5Ha_stS1X3xs02NA3nXc2xs3X164ZLEN2HB5Ha_stS1X3xs02NA3nXc2xs3X164ZLEN2HB5Ha_stS2sp3xs02lo2NA3nXc2xs4SLEN4DLENS2sp3xs02lo2NA2xsS2sp3xs02lo2NA3nXc2xs4ZLENS1R2sp3xs02lo4SLO22xs5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo4SLO22NA3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs5NEEDR3LOS4SP643ALO3ACPFFFFFS1X3xs02xs2X02HBS1X3xs02NA3nXc2xs2X04ZLEN2HBS1X3xs02xsS1X3xs02NA3nXc2xs4ZLENS1X3xs02NA3nXc2xs4SLEN4DLENS3xs02NA3nXc2xs4SLEN4DLENS3xs02xsS3xs02NA3nXc2xs4ZLEN". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC C24H JC TPV UWX D0 BUD BUDF SLO2"] Lemma sa_GROW : forall (n NA v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    KJ_stmt n NA ->
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    SPL mc ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    0 <= n <= NA ->
    md_n dXc < NA <= 10000 ->
    (md_addr dA = X -> md_n dXc = NA /\ limbs_val (md_limbs dXc) = mpd_abs dA) ->
    (md_addr dA <> X -> md_n dA = NA) ->
    (md_addr dB = X -> lval (md_limbs dXc) n = mpd_abs dB /\ n <= md_n dXc) ->
    (md_addr dB <> X -> lval (md_limbs dB) n = mpd_abs dB /\ n <= md_n dB) ->
    v <= 0 ->
    f <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              (Z_to_bv 64 (X + 10)) (Z_to_bv 64 (md_addr dA + 10)) (Z_to_bv 64 NA) (Z_to_bv 64 (Z.shiftr X 3)) SB (Z_to_bv 64 (4 * n)) (SHA (md_addr dB)) SH10
              (SHA (md_addr dA + 10)) xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e650) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros K1 J NGX SPL0 RA RB HN CNT VA1 VA2 VB1 VB2 BV BF. jc_open. unfold KJ_stmt in K1.
    assert (ANX : md_addr dA <> X) by (intros EAX; destruct (VA1 EAX) as [EN _]; clear - EN CNT; lia).
    pose proof (VA2 ANX) as ENA.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_split asegs mc lo (bv_unsigned sp + -112) (bv_unsigned sp + -104) ST1 ltac:(clear - SLO2 NEEDR LOSP; lia)) as [STa _].
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -112) 8 STa ltac:(clear - SLO2 NEEDR; lia)) as [STb [jk1 SLOT1]].
    replace (bv_unsigned sp + -112 - Z.of_nat 8) with (bv_unsigned sp + -120) in STb, SLOT1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -120) 8 STb ltac:(clear - SLO2 NEEDR; lia)) as [STc [jk0 SLOT0]].
    replace (bv_unsigned sp + -120 - Z.of_nat 8) with (bv_unsigned sp + -128) in STc, SLOT0 by (clear; lia).
    clear STa STb.
    pose proof (munch_refl [(bv_unsigned sp + -120, bv_unsigned sp + -112)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : mem_inv asegs m1 |- _ => rename H into MIs end.
    match goal with H : HM asegs R HIA hc LBc LF m1 |- _ => rename H into HHs end.
    match goal with H : stk asegs m1 lo (bv_unsigned sp + -128) |- _ => rename H into STs end.
    assert (STs' : stk asegs m1 lo (bv_unsigned sp - 104)) by (stk_up STs; clear - SLO2 NEEDR; lia).
    pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m1 J MU WM MIs STs' HHs ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as Js.
    pose proof (rideS_stk_munch dA _ _ _ _ _ _ (bv_unsigned sp + -120) (bv_unsigned sp + -112) m1 J RA ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia) MU WM) as RAs.
    pose proof (rideS_stk_munch dB _ _ _ _ _ _ (bv_unsigned sp + -120) (bv_unsigned sp + -112) m1 J RB ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia) MU WM) as RBs.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in Js, RAs, RBs.
    clear J RA RB STs'. rename Js into J. rename RAs into RA. rename RBs into RB.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := NA) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia; try eassumption; try reflexivity.
      all: try ((intros _; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ])).   (* [comment removed for export] *)
      all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: unfold sub_abs_PHI, sub_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *; rewrite ?ENA in *;
           clear - CNT NR1 NR LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -128)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp + -104)) by (stk_up ST2; clear - SLO2 NEEDR; lia).
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA hc) [] m1 m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep. zstep. zstep.
      eapply sa_ret with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact J2| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| right; left; reflexivity| |].
      + unfold sub_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. rewrite ?ENA in *. clear - BV CNT NR1. lia.
      + unfold sub_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace (NA * 4) with (4 * NA) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An NA J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT; lia)) as [J2 F2].
      pose proof (rideS_transport dA _ _ _ _ _ _ _ _ _ _ J RA HP2' MI2 HCS2 HH2 ltac:(intros b Hb; right; exact Hb)) as RA2.
      pose proof (rideS_transport dB _ _ _ _ _ _ _ _ _ _ J RB HP2' MI2 HCS2 HH2 ltac:(intros b Hb; right; exact Hb)) as RB2.
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J RA RB. try clear MI1; try clear ST1; try clear STc; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1; try clear CX1; try clear OWN0; try clear OWN1;
      xa_open J2.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        assert (EO : own = LNull).
        { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso.
          ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _ & _ & _ & P0 & PC & _).
          rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia). clear - KP P0; lia. }
        subst own. ddestruct (OWN0 eq_refl) as (EP & EN & EL). clear OWN1 KP.
        pose proof (xga_null _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
        pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D2) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5. rewrite <- HT1 in CW5.
        clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        (* [comment removed for export] *)
        shadow_chk OX1 (X + 10) 2.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D2 MU WM MI1 CX2 HH1 OX1) as J5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        pose proof (rideS_finish dA _ _ _ _ _ _ _ _ _ _ D2 RA2 MU WM) as RA5.
        pose proof (rideS_finish dB _ _ _ _ _ _ _ _ _ _ D2 RB2 MU WM) as RB5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA5, RB5.
        zstep.
        eapply K1; [exact J5| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| eassumption| exact RA5| exact RB5| exact HN| cbn [md_n]; clear; lia| intros _; reflexivity| intros EAX; exfalso; exact (ANX EAX)| exact VA2| | exact VB2| |].
        * intros EBX. cbn [md_limbs]. destruct (VB1 EBX) as [VBl VBn]. rewrite EN in VBn. assert (n = 0) by (clear - VBn HN; lia). subst n.
          rewrite <- VBl. unfold lval. reflexivity.
        * unfold sub_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. rewrite ?ENA in *. clear - BV CNT HV2. lia.
        * unfold sub_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
      + (* [comment removed for export] *)
        assert (EO : own = LHeap).
        { destruct own; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. apply KP. rewrite (proj1 (OWN0 eq_refl)). reflexivity. }
        subst own. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1 KP.
        pose proof (XLS1 ltac:(discriminate)) as XLSc. pose proof (XP1 eq_refl) as XPc.
        pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
        destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl)
          as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
        rewrite firstn_length in DST, DLEN. rewrite repeat_length in DST, DLEN.
        replace (Init.Nat.min (Z.to_nat nXc) (Z.to_nat NA)) with (Z.to_nat nXc) in DST, DLEN by (clear - CNT N1; lia).
        (* [comment removed for export] *)
        zstep. zstep. zstep. if_cases KAL; zify_cond KAL; [exfalso; apply KAL; apply lor_land3; [clear - XPAL; Z.div_mod_to_equations; lia| first [clear - A16; Z.div_mod_to_equations; lia| clear - Fal; Z.div_mod_to_equations; lia]]|].
        clear MU WM. pose proof (munch_refl [(An, An + 4 * nXc); (lo, bv_unsigned sp + -104)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        zstep.
        shadow_chk OX1 (X + 10) 2.
        zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_SA) as SPC. unfold A_ASAN_MEMCPY_SA in SPC.
        apply (u8arr_of_rw_cells asegs) in DST.
        (* [comment removed for export] *)
        acallxA_sp (bv_unsigned sp + -128)
          (eapply SPC with (h := h2) (LB := (An, 4 * NA) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * nXc) (lo := lo)
                            (ss := u32s xs);
           rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia;
           try eassumption; try reflexivity;
           first [ left; rewrite AMC; reflexivity
                 | rewrite u32s_length, firstn_length, repeat_length; clear - N1 CNT; lia
                 | rewrite u32s_length; clear - LEN1 N1; lia
                 | eapply aobj_sub; [exact OA| clear; lia| clear - CNT N1; lia]
                 | right; clear - SEP; lia
                 | left; clear - Flo CNT N1 SLO2 NEEDR; lia
                 | clear - XLSc SLO2 NEEDR; lia
                 | right; clear - A47 CNT N1; lia
                 | right; clear - P47; lia
                 | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
                 | eapply client_wrange_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - CNT N1; lia]
                 | f_equal; clear; lia
                 | clear - NR1 N1 CNT LOS SLO SLO2 NEEDR NRA TOP2 SPA SPR; lia
                 | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ] ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
        assert (ST3' : stk asegs m3 lo (bv_unsigned sp + -104)) by (stk_up ST3; clear - SLO2 NEEDR; lia).
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        replace (4 * length xs)%nat with (Z.to_nat (4 * nXc)) in HPA by (clear - LEN1 N1; lia).
        destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
        assert (WC3 : w_client (hcs asegs R HIA h2) [(An, An + 4 * nXc); (lo, bv_unsigned sp + -104)]).
        { unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OA| clear; lia| clear - CNT N1; lia]|].
          apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]| apply Forall_nil]. }
        pose proof (rideS_fresh_munch dA _ _ _ _ _ _ _ _ _ (4 * nXc) m3 J2 F2 RA2 ltac:(clear - CNT N1; lia) MU WM WC3) as RA3.
        pose proof (rideS_fresh_munch dB _ _ _ _ _ _ _ _ _ (4 * nXc) m3 J2 F2 RB2 ltac:(clear - CNT N1; lia) MU WM WC3) as RB3.
        clear J2 F2 RA2 RB2 OA OP' SBY SLEN DLEN INA INP.
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
        try clear CX2. pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
        (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep. zstep. zstep. zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
        destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
        pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
        eapply aevtA_call.
        { intros mo3 [HK3 MF3].
          eapply SPZ with (h := h2) (LB := (An, 4 * NA) :: LBc) (LF := LF) (buf := pXc) (len := 4 * nXc) (lo := lo) (d := d) (junk := u32s xs);
            rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia; try eassumption; try reflexivity.
          all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
          all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
          all: try (f_equal; clear; lia).
          all: unfold sub_abs_PHI, sub_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *; rewrite ?ENA in *;
               clear - CNT NR1 NR N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
          all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end ]. }
        clear SPZ.
        (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
        destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -128)) in PO by qlia.
        ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
        match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
        presA_transport HP4.
        assert (ST4' : stk asegs m4 lo (bv_unsigned sp + -104)) by (stk_up ST4; clear - SLO2 NEEDR; lia).
        assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * NA) :: LBc)) LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA h2)
                         [(pXc, pXc + 4 * nXc)] m3 m4).
        { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
        pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
        pose proof (rideS_zfree dA _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 RA3 eq_refl HP4' MI4 HCS4 HH4) as RA4.
        pose proof (rideS_zfree dB _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 RB3 eq_refl HP4' MI4 HCS4 HH4) as RB4.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4, RA4, RB4.
        assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
        apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
        clear CSOK SB64 SCS0 SCS HTOP2.
        pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
        assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 RA3 RB3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2.
        pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM. unfold mpi_cells in DCX.
        pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
        assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
        pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
        rewrite <- HT4h in CW5.
        pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        (* [comment removed for export] *)
        zstep. zstep.
        shadow_chk DOX (X + 10) 2.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
        pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        pose proof (rideS_finish dA _ _ _ _ _ _ _ _ _ _ D4 RA4 MU WM) as RA5.
        pose proof (rideS_finish dB _ _ _ _ _ _ _ _ _ _ D4 RB4 MU WM) as RB5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA5, RB5.
        zstep.
        eapply K1; [exact J5| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| eassumption| exact RA5| exact RB5| exact HN| cbn [md_n]; clear; lia| intros _; reflexivity| intros EAX; exfalso; exact (ANX EAX)| exact VA2| | exact VB2| |].
        * intros EBX. cbn [md_limbs]. destruct (VB1 EBX) as [VBl VBn]. rewrite skipn_repeat. rewrite lval_app_l by (rewrite LEN1; clear - VBn HN; lia). exact VBl.
        * unfold sub_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. rewrite ?ENA in *. clear - BV CNT HV2 HV4. lia.
        * unfold sub_abs_FR, calls_FR, fr_charge in *. clear - BF D0 HFR2 HFR4. lia.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "SAGROW-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L12528478301.2 L30274085261.3 L32027975233.0 L33655257162.3 L38569812941.1 L39280637297.0 L46832644263.3 L54742304139.2 L57140746179.2 L57140746204.3 L59031206751.1 L59308579152.3 L59310766035.4 L60016188669.2 L60456143867.3 L62357985085.2 L66151427842.1600000800B00C00N00S00T00^00f00m01401801F01U01]01i02202NS3dXc2P0S2dE1n3HnESS3dXc1n3HnXS3dXcSS1X2dE3SXBS2lo3LO0S1n3HnES1n3HnXS2dES1n3HnX2H13HnES2dE1l4LENE3En0S2dE3EP0S2dE3dXc3SL2S3dXc3PX0S3dXc2r04XPAL1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="JC"] Lemma rideS_view : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$4;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pn,$8.P,(4=.$4;.VR,VHIA,Vh,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4>.(4?.$2.)R7.R6.R5.R4.R3.R2.)P,(78.R9.R6.R5.R4.R3.)P,(22.=R3.)P,P,(10.$8.(19.R;.)VX,)(22.R5.(1=.R6.))P,P,(?.(10.$8.(19.R<.)VX,))(22.R6.(1=.R=.))(62.$8.Lpe,$8.(62.$8.Lse,$8.(62.$8.Lne,$8.(62.(3.&40.)Lpde,(3.&40.)(62.(1.(3.&40.))Lys,(1.(3.&40.))(2?.(6:.$4;.R=.(19.R12.)(6;.R5.(29.&40.R4.)R3.R2.))(2?.(6<.$4;.(2=.VR,)(2>.$4;.VR,VHIA,R?.)R=.(19.R12.)+10.)(2?.(30.=(19.R12.))(2?.(22.(23.(19.R12.)+10.)(36.+2.+40.))(2?.(10.$8.(28.(19.R12.)+8.)=)(2?.(6=.$4;.R=.R5.(6>.R1.))(2?.(22.R;.(6?.(70.(3.&40.)R1.)))(2?.(21.(2?.(10.$8.R5.(1;.R<.))(10.(1.(3.&40.))R1.(5:.R<.)))(21.(22.(23.R5.(1<.+4.(6?.(70.(3.&40.)R1.))))(1;.R<.))(22.(23.(1;.R<.)(1<.+4.(1=.R<.)))R5.)))(2?.(10.$8.(28.R5.+4.)=)(2?.P,(22.+1.R;.)(30.=R6.)(2?.(21.(22.(23.R5.(1<.+4.(6?.(70.(3.&40.)R1.))))Vlo,)(22.(=.&40.Vsp,)R5.))(2?.P,(22.+1.R;.)(6<.$4;.(2=.VR,)(2>.$4;.VR,VHIA,R10.)R>.R6.(1<.+4.R<.))(2?.P,(10.$8.(19.R12.)VX,)(10.(1.(3.&40.))R2.(5:.R=.))(2?.P,(?.(10.$8.(19.R12.)VX,))(10.(1.(3.&40.))R2.(5:.R13.))(2?.P,(10.$8.(19.R12.)VX,)(10.$8.R4.(1=.R=.))P,(?.(10.$8.(19.R12.)VX,))(10.$8.R4.(1=.R13.))))))))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros dE v f hc LBc mc dXc n J0 RE Hn HnX HnE.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof (xa_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as ADc. pose proof (xa_pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as PDc.
    destruct RE as [EAX|[DBJ B]].
    - (* [comment removed for export] *)
      dexists (md_p dXc), (md_sg dXc), (md_n dXc), (md_pad dX), (md_limbs dXc). rewrite EAX.
      split; [exact CX1|]. split; [exact (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0)|].
      split; [exact X0|]. split; [exact X16|]. split; [exact XAL|].
      pose proof (xa_XLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as XLSc.
      specialize (HnX EAX).
      destruct (md_own dXc) eqn:EOW.
      + ddestruct (OWN0 eq_refl) as (EP & En0 & EL). rewrite EP, EL. rewrite En0 in HnX.
        split; [cbn; apply bytes_at_nil; clear; lia|]. split; [cbn [length]; clear - HnX Hn; lia|].
        split; [left; split; reflexivity|]. split; [reflexivity|]. split; [intros H1; exfalso; clear - H1 HnX; lia|].
        split; [left; cbn [length]; clear - LO0; lia|]. split; [intros H1; exfalso; clear - H1 HnX; lia|].
        split; [intros _; reflexivity|]. split; [intros C; exfalso; exact (C eq_refl)|]. split; [intros _; reflexivity| intros C; exfalso; exact (C eq_refl)].
      + ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
        split; [apply u32arr_ro; exact XARR|]. split; [rewrite LEN1; exact HnX|].
        split; [left; split; reflexivity|]. split; [clear - XPAL; Z.div_mod_to_equations; lia|]. split; [intros _; exact P0|].
        split; [rewrite LEN1; exact (XLSc ltac:(discriminate))|].
        split; [intros H1; eapply aobj_sub; [exact OP| clear; lia| clear - HnX; lia]|].
        split; [intros _; reflexivity|]. split; [intros C; exfalso; exact (C eq_refl)|]. split; [intros _; reflexivity| intros C; exfalso; exact (C eq_refl)].
      + exfalso. destruct (OWN1 ltac:(discriminate)) as (C & _). discriminate C.
    - (* [comment removed for export] *)
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
      pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B)) as [(CE & _) _].
      assert (ENX : md_addr dE <> X) by (destruct DBJ as [_ _ _ _ SXB _]; cbn [md_addr] in SXB; clear - SXB; lia).
      specialize (HnE ENX).
      assert (PX0 : 0 <= md_p dXc /\ (md_own dXc <> LHeap -> md_p dXc = 0 /\ md_n dXc = 0)).
      { destruct (md_own dXc) eqn:EOW.
        - ddestruct (OWN0 eq_refl) as (EP & En0 & _). rewrite EP. split; [clear; lia| intros _; split; [reflexivity| exact En0]].
        - ddestruct (OWN1 ltac:(discriminate)) as (_ & _ & _ & _ & _ & P0 & _). split; [clear - P0; lia| intros C; exfalso; exact (C eq_refl)].
        - exfalso. destruct (OWN1 ltac:(discriminate)) as (C & _). discriminate C. }
      destruct PX0 as [PX0 PXN].
      dexists (md_p dE), (md_sg dE), (md_n dE), (md_pad dE), (md_limbs dE).
      split; [exact CE|]. split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)|]. split; [exact E0|]. split; [exact E16|]. split; [exact EAL|].
      pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B) as SEPL. pose proof (bj_aobjL _ _ _ _ _ _ _ _ _ _ B) as OEL.
      destruct (md_own dE) eqn:EOE.
      + destruct (OWNE0 eq_refl) as (EP & En0).
        assert (EL : md_limbs dE = []) by (destruct (md_limbs dE); [reflexivity| exfalso; cbn [length] in LENE; clear - LENE En0; lia]).
        rewrite EP, EL. rewrite En0 in HnE.
        split; [cbn; apply bytes_at_nil; clear; lia|]. split; [cbn [length]; clear - HnE; lia|].
        split; [right; left; cbn [length]; clear - PX0; lia|]. split; [reflexivity|]. split; [intros H1; exfalso; clear - H1 HnE; lia|].
        split; [left; cbn [length]; clear - LO0; lia|]. split; [intros H1; exfalso; clear - H1 HnE; lia|].
        split; [intros C; exfalso; exact (ENX C)|]. split; [intros _; reflexivity|]. split; [intros C; exfalso; exact (ENX C)| intros _; reflexivity].
      + ddestruct (OWNE1 ltac:(discriminate)) as (N1e & EP0 & EPAL & EBY & ESK & _).
        split; [exact EBY|]. split; [rewrite LENE; exact HnE|].
        split; [right; rewrite LENE; destruct (md_own dXc) eqn:EOW;
                [ destruct (PXN ltac:(discriminate)) as [EPX ENXn]; right; rewrite EPX, ENXn; clear - EP0; lia
                | pose proof (SEPL eq_refl ltac:(discriminate)) as SL2; clear - SL2; lia
                | destruct (PXN ltac:(discriminate)) as [EPX ENXn]; right; rewrite EPX, ENXn; clear - EP0; lia ]|].
        split; [exact EPAL|]. split; [intros _; exact EP0|]. split; [rewrite LENE; exact ESK|].
        split; [intros H1; eapply aobj_sub; [exact (OEL ltac:(discriminate))| clear; lia| clear - HnE; lia]|].
        split; [intros C; exfalso; exact (ENX C)|]. split; [intros _; reflexivity|]. split; [intros C; exfalso; exact (ENX C)| intros _; reflexivity].
      + ddestruct (OWNE1 ltac:(discriminate)) as (N1e & EP0 & EPAL & EBY & ESK & _).
        split; [exact EBY|]. split; [rewrite LENE; exact HnE|].
        split; [right; rewrite LENE; destruct (md_own dXc) eqn:EOW;
                [ destruct (PXN ltac:(discriminate)) as [EPX ENXn]; right; rewrite EPX, ENXn; clear - EP0; lia
                | pose proof (SEPL eq_refl ltac:(discriminate)) as SL2; clear - SL2; lia
                | destruct (PXN ltac:(discriminate)) as [EPX ENXn]; right; rewrite EPX, ENXn; clear - EP0; lia ]|].
        split; [exact EPAL|]. split; [intros _; exact EP0|]. split; [rewrite LENE; exact ESK|].
        split; [intros H1; eapply aobj_sub; [exact (OEL ltac:(discriminate))| clear; lia| clear - HnE; lia]|].
        split; [intros C; exfalso; exact (ENX C)|]. split; [intros _; reflexivity|]. split; [intros C; exfalso; exact (ENX C)| intros _; reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L11101649562.5L22120834513.3L2424955998.3 00000A00K00US2dA3dXc1n2V13SPLS3dXc1n2HNS3dXc1n2HN". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma sa_CSUBr : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (n : Z)
      (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs4 xs11 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    0 <= n <= md_n dXc ->
    (1 <= n -> md_own dXc = LHeap) ->
    (md_addr dA = X -> limbs_val (md_limbs dXc) = mpd_abs dA) ->
    (md_addr dA <> X -> n <= md_n dA /\ lval (md_limbs dA) n + 2 ^ (32 * n) * limbs_val (skipn (Z.to_nat n) (md_limbs dXc)) = mpd_abs dA) ->
    (md_addr dB = X -> lval (md_limbs dXc) n = mpd_abs dB) ->
    (md_addr dB <> X -> n <= md_n dB /\ lval (md_limbs dB) n = mpd_abs dB) ->
    v <= sub_abs_PHI dX dA dB ->
    f <= sub_abs_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              (Z_to_bv 64 (X + 10)) xs4 (Z_to_bv 64 (Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 (Z.shiftr X 3)) SB (Z_to_bv 64 (4 * n)) (SHA (md_addr dB)) SH10 xs11
              xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e7d8) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX RA RB HN EOn VA1 VA2 VB1 VB2 BV BF.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (_ & LEN1 & _).
    destruct (rideS_view dA _ _ _ _ _ _ n J0 RA (proj1 HN) ltac:(intros _; exact (proj2 HN)) ltac:(intros C; exact (proj1 (VA2 C))))
      as (pa & sa & na & pda & ysA & CEA & OEA & A0 & A16 & AAL & YA & LYA & DJA & PAL & PA0 & YAS & OAL & YAX & YAR & _ & _).
    destruct (rideS_view dB _ _ _ _ _ _ n J0 RB (proj1 HN) ltac:(intros _; exact (proj2 HN)) ltac:(intros C; exact (proj1 (VB2 C))))
      as (pb & sb & nb & pdb & zsB & CEB & OEB & B0 & B16 & BAL & ZB & LZB & DJB & PBL & PB0 & ZBS & OBL & ZBX & ZBR & _ & _).
    eapply (sa_CSUB v f hc LBc mc dXc n pa sa na pda pb sb nb pdb ysA zsB); try eassumption.
    - destruct (Z.eq_dec (md_addr dA) X) as [E|NE].
      + rewrite (YAX E). pose proof (VA1 E) as V1.
        pose proof (limbs_val_split (md_limbs dXc) n ltac:(clear - HN; lia) ltac:(rewrite LEN1; clear - HN; lia)) as SPL.
        clear - V1 SPL. lia.
      + rewrite (YAR NE). exact (proj2 (VA2 NE)).
    - destruct (Z.eq_dec (md_addr dB) X) as [E|NE]; [rewrite (ZBX E); exact (VB1 E)| rewrite (ZBR NE); exact (proj2 (VB2 NE))].
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "CSUBR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L23648481964.8L24071605674.4L33358731881.5L35655538626.8L50392148218.4L50758139803.8L53591371865.3L60098763854.300000E00S00_01801E01Z01d01nS2dE3dXc1a1b2Ha2Hb2S2S2sp2lo2dE3EL5S3dXc1a1b2HbS1R3HIA1h2sp2lo3TOP5HTOP0S2sp2lo2dE2ESS2dE3dXc1a1b2Ha2Hb2S1S3dXc1a2HaS1R2lo3LOS". (* [comment removed for export] *)
  #[using="JC"] Lemma rideS_xl_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$4;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pa,$8.Pb,$8.Pxs',(1.(3.&40.))Pm3,P,(3.&40.)(5.(3.&8.))P,(4=.$4;.VR,VHIA,Vh,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4>.(4?.$2.)R:.R9.R8.R7.R6.R5.)P,(78.R<.R9.R8.R7.R6.)P,(10.$11.(12.R7.)$1:.)P,(22.(1;.R8.)R7.)P,(22.R8.R7.)P,(22.R8.(23.(1;.R:.)(1<.+4.(1=.R:.))))P,(64.(65.(66.$8.$8.)(67.$8.$8.R:.R9.)(65.(66.$8.$8.)(67.$8.$8.Vlo,(23.(=.&40.Vsp,)-80.))(4?.(66.$8.$8.))))R<.R7.)P,(68.$4;.R=.R8.)(78.R13.R10.R?.R9.(4<.(19.R=.)(53.R=.)(1=.R=.)(1;.R=.)R:.(7=.R=.)(12.R=.)))")
(* [comment removed for export] *).
  Proof.
    intros dE v f hc LBc mc dXc a b xs' m3 J0 [E|[DBJ B]] EO Ha Hab Hb MU WM; [left; exact E| right; split; [exact DBJ|]].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HS1.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP0.
    assert (B3 : BJE dE hc LBc m3 dXc).
    { eapply bja_munch; try eassumption.
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OP| clear - Ha; lia| clear - Hab Hb; lia]|].
        apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; clear - HTOP0 TOP LOSP; lia]| apply Forall_nil].
      - cbn. split; [pose proof (bj_sepS _ _ _ _ _ _ _ _ _ _ B EO) as S1; clear - S1 Ha Hab Hb; lia|]. split; [clear - ES; lia| exact I].
      - intros BN. cbn. split; [pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B EO BN) as S2; clear - S2 Ha Hab Hb; lia|].
        split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5; lia| exact I]. }
    destruct B3 as [A1 A2 A3 A4 A5]. constructor; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02T0@C11264273767.215C11264273767.216C17025492443.212C17025492443.213C17025492443.214C237391055.217  D32879014451.217D39122030177.217D56475227919.217D60109446735.217K19167344963.212K19167344963.213K19167344963.214K25382859142.217K36226586886.217K39785057286.217K46334408099.215K46334408099.216K65977774223.217K8474424312.217 K9644101664.212 K9644101664.213 K9644101664.214 L10307112399.6  L12530932062.2  L146940511.12   L14769340704.4  L14858295739.5  L16192802388.7  L19171242580.5  L1981962437.8   L21812184103.189L21820691587.174L21824805693.6  L21824887228.191L23002796746.5  L23004893895.3  L23100341967.190L23999514035.216L25238078280.8  L25369787025.17 L2610977716.1   L272527732.191  L27791514431.4  L28709956679.19 L28722243361.5  L2975768925.2   L29763579088.191L29763661393.2  L29767770607.174L30743879498.19 L30747872606.3  L34125036709.14 L35663928186.7  L35978283095.4  L36230550033.4  L37231249068.3  L38129129185.3  L38235734261.1  L39109575675.4  L39172636981.0  L39280637297.0  L39407799300.8  L39788758801.4  L40145318023.3  L407990430.7    L41126667518.5  L42633816569.1  L43878034250.5  L45703525153.0  L45711213078.15 L46160487540.172L46329855668.4  L47401054516.1  L47725787526.2  L48157064005.190L49245743301.2  L49655171755.3  L50170224419.190L51476717110.4  L52531031119.6  L53234661796.3  L53236858660.6  L53517043217.190L5414710336.4   L55187859527.2  L5630863510.2   L56577124758.2  L56598719221.7  L58609956177.2  L58641002120.174L59308660947.6  L59308661072.4  L59310730064.7  L59310730065.10 L59952597784.1  L60098763854.3  L60283674290.10 L6141606276.1   L61714773053.6  L62959842117.3  L64045840071.2  L64049675681.19 L65925215236.5  L65973484440.4  L67970915500.7  L68505269079.5  L6880799821.3   L8265267294.0   L8486281629.3   L9631842885.2   O11264273767.215O11264273767.216O17025492443.212O17025492443.213O17025492443.214O237391055.217  O36019832244.217O36632239767.212O36632239767.213O36632239767.214O44976997556.217O48199580980.217O50423766113.217O57399310481.217P46334408099.215P46334408099.216P9644101664.212 P9644101664.213 P9644101664.214 Q12370813529.195Q17201186252.194Q18133098905.175Q18135196125.173Q18136087844.176Q26207721832.174Q26207721832.175Q26207967338.171Q31653717441.175Q32879014451.217Q34225026208.173Q34419558587.175Q37618859566.194Q38248387216.217Q39122030177.217Q39212284437.174Q39212284437.176Q43879899724.217Q43925228937.174Q48476778790.220Q50852185413.220Q5470531635.194 Q5485174314.195 Q58692335428.176Q59703481013.195Q60511567613.174Q60511567613.176Q60697995187.174Q6143569392.195 Q64768105610.176Q66030093065.197Q8880503606.171 Q9538243134.173 Q9538787269.171 00000100200300400500600T01402302X03>03d04J05;05l06]06^06_07I07b07c07d07e08908B08i09509E09\09]0:20:f0;U0;h0<]0<l0=40=P0>40>I0>J0>N0?E0?P0?n0?o0@60@X0@_0A80AN0AO0B10BF0BR0BS0B[0B\0B`0Bm0Bn0Bo0C00C10C:0CH0CI0CN0CU0CV0C]0D70D80D<0DC0E;0EA0EI0FE0FR0Ff0G00G:0GV0GW0G_0Gf0Gm0H?0HF0H`0I00I;0IL0Ie0Ii0J30JM0JQ0Jd0Jm0Jn0KD0KX0KY0Kf0L60L?0L@0LA0LB0LC0LD0LE0LF0LG0L\0L]0L^0L_0L`0La0Lb0Lc0Ld0Le0Lf0Lg0Lh0Li0ML0M[0Mf0N10N<0NF0NP0NZ0Nd0O70OB0OM0O\0Ol0PA0PK0PV0Pi0Q30Q[0R60RE0RT0Rb0Rc0Rk0S30S@0SO0SZ0TK0TU0T]0TeFFFFFFS2ra2sp1X3xs02dA1N3pXc2xs1n2NAS2ra2sp1X3xs02dA3pXc2xs1n2NA3KU1S1R3HIA1h2ra2sp1X3xs02dA2lo2hc3pXc2xs1n2NA3TOP2X03SPR2A03HT12P0S1R2ra2sp1X3xs02dA2lo3pXc2xs1n2NA3LOSS1R2sp3xs02lo1N3pXc2xs1n2NA3LOS3ALO2PCS1R2sp3xs02lo1N3pXc2xs1n2NA3LOS3ALO2PCS1R2sp3xs02lo1N3pXc2xs1n2NA3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n2NA5NEEDR3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n2NA5NEEDR3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n2NA5NEEDR3LOS3ALO2PCFFS1X3xs02dA1N3pXc2xs1n2NA3VA11K3XPc3ANX3KU1S2sp1X3xs02lo2xs1n2NA3DSXFFFS1R2sp2lo4SLO25NEEDRS3dXc3NR1S1R2sp2lo4SLO21N3pXc1n2NA2HN5NEEDR4XLScS1N2NA3HNA1KS1N2xs1n2HN4LEN1S1N2xs1n2NA2HN3HNA4LEN1FS1N2xs1n2NA2HN4LEN11KS2ra2sp1X3xs02dA1N3pXc2xs1n2NA2HN2X03SPR2A01K2P03P47S2ra2sp1X3xs02dA1N2xs1n2NA2HN3HNA2X03SPR3NR12A0S1N1n2NA2HN3HNA3NR1S2ra2sp1X3xs02dA1N3pXc2xs1n2NA2X03SPR2A01K2P03P473KU1S1N1n2NA2HN3HNAS1N1n2HNS2ra2sp1X3xs02dA3pXc2xs1n2NAS2ra2sp1X3xs02dA1N3pXc2xs1n2NA5LEN6'S1X1N3pXc1n2NA2HN3XPcFS2spS2ra2sp1X3xs02dA1N3pXc2xs1n2NA3HNA2X03SPR2A02P03P473KU1S1N1n2HN2H1S2sp2lo1N3pXc1n2NA2HN3SPR4XLScFS1N3pXcS2ra2sp1X3xs02dA1N3pXc2xs1n2NA3NR1S1N3NR1S2ra2sp1X3xs02dA1N2xs3NR1S1R2sp2lo4SLO23NRA3SPRFS2sp2lo1N3pXc1n2NA2HN3HNA3NR14XLScS1R3HIA1h2sp2lo3TOP1HS1N3pXc2NA1KFS1N1n2HNFS2loS3pXc1n2NA2HNSSFFS1n2NA2HNS1N3pXc2NA3P47FS3pXcS2sp2loSS2sp2loS2ra2sp1X3xs02dA2xs2X03X16FS2spS2sp2loS2ra2sp1X3xs02dA1N3pXc2xs1n2NA2X03SPR2A02N12P03P471K3KU1S1N2NAS1N2NA1KS2ra2sp1X3xs02dA1N3pXc2xs1n2NA2HN2X03SPR2A01K2P03P473ENa3KU1S2sp1X2lo3DSXS1R2sp2lo4SLO25NEEDRS1N3pXc2NAS1N3pXc2NAS2ra2sp1X3xs02dA3pXc2xs1n2NAFS3pXc2NAS2sp2loS2sp2loS1N2xs2NA3HNA4LEN1S1N3NR1S2ra2sp1X3xs02dA2xs2A03A16S1N1n2NA2HN1K2E0S1N2NA1K2E1S3pXc1n2NA2HN3KU1S3pXc1n2NA2HN1H2H03KU22P0S2spS1R2lo3LOSS2sp2lo1N3pXc1n2NA2HN1a2NOS2spS1N1n2NA2HN3HNA3NR1S1n2NA2HNFS2sp1N1n2NA2HN3SPR3NR1S1R2sp2lo4SLO25NEEDRFS1N2xs2NA3LHIS1R3HIA1h2sp3TOPS1n2NA2HNSFFFFFFFS1N3pXc2xs1n2NA1K3LHIFFFFFFFFFFFFFS2ra2sp1X3xs02dA3pXc2xs1n2NA2X03XALS1X3xs02xs1n2NAS3xs02dA2xsS3xs02dA2xsS3xs02dA2xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS3xs01N3pXc2xs1n2NAS3xs02dA2xsS3xs02dA2xsS1X3xs02xs1n2NAS3xs02lo2xs1n2NAS3xs03pXc2xs1n2NA3KU1S1X3xs02xsS3xs02dA2xsS2sp3xs02lo2xs1n2NAS1X3xs02xsS1R2sp3xs02lo4SLO21N2xs1n2NA5NEEDR5LEN6'S2sp3xs02lo1N2xs1n2NA5LEN6'S1X3xs02xs1n2NAS1X3xs02xs1n2NAS3xs02dA2xs2A0FS3xs02xsS3xs02xsS1X3xs02xs2X0S1X3xs02xs1n2NAS3xs02dA2xsS1R2sp3xs02lo4SLO22xs1n2NA5NEEDR3LOS4SP643ALO3ACPS1X3xs02xsS3xs02xsS3xs02xs". (* [comment removed for export] *)
  #[using="IMG AMS JC SLO2"] Lemma sa_MEMSET : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (n NA : Z)
      (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    SPL mc ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    0 <= n <= NA ->
    NA <= md_n dXc ->
    (1 <= NA -> md_own dXc = LHeap) ->
    (md_addr dA = X -> md_n dXc = NA /\ limbs_val (md_limbs dXc) = mpd_abs dA) ->
    (md_addr dA <> X -> md_n dA = NA /\ lval (md_limbs dA) n + 2 ^ (32 * n) * lseg (md_limbs dXc) n NA = mpd_abs dA) ->
    (md_addr dB = X -> lval (md_limbs dXc) n = mpd_abs dB) ->
    (md_addr dB <> X -> n <= md_n dB /\ lval (md_limbs dB) n = mpd_abs dB) ->
    v <= sub_abs_PHI dX dA dB ->
    f <= sub_abs_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              (Z_to_bv 64 (X + 10)) (Z_to_bv 64 (md_addr dA + 10)) (Z_to_bv 64 (Z.shiftr (md_addr dA) 3)) (Z_to_bv 64 (Z.shiftr X 3)) SB (Z_to_bv 64 (4 * n))
              (SHA (md_addr dB)) SH10 (SHA (md_addr dA + 10)) xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e77c) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX SPL0 RA RB HN HNA EOn VA1 VA2 VB1 VB2 BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct (rideS_view dA _ _ _ _ _ _ 0 J0 RA ltac:(clear; lia) ltac:(intros _; clear - NR1; lia) ltac:(intros C; rewrite (proj1 (VA2 C)); clear - HN; lia))
      as (pa & sa & na & pda & ysA & CEA & OEA & A0 & A16 & AAL & _ & _ & _ & _ & _ & _ & _ & _ & _ & NAX & NAR).
    assert (ENA : na = NA) by (destruct (Z.eq_dec (md_addr dA) X) as [E|NE]; [rewrite (NAX E); exact (proj1 (VA1 E))| rewrite (NAR NE); exact (proj1 (VA2 NE))]).
    subst na. clear NAX NAR.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1, CEA.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    shadow_chk OEA (md_addr dA + 10) 2.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 NA)) with (Z_to_bv 64 NA) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1 HN HNA; lia); rewrite Z.mod_small by (clear - NR1 HN HNA; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (clear - NR1 HN HNA; lia).
    - (* [comment removed for export] *)
      assert (EN : N = NA) by (clear - K HNA; lia). subst NA.
      eapply sa_CSUBr; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact RA| exact RB| cbn [md_n]; clear - HN; lia| cbn [md_own]; intros H1; apply EOn; clear - H1 HN; lia
                       | intros E; exact (proj2 (VA1 E))| | exact VB1| exact VB2| exact BV| exact BF].
      intros NE. destruct (VA2 NE) as [ENa VA]. split; [rewrite ENa; clear - HN; lia|]. cbn [md_limbs].
      rewrite <- VA. f_equal. f_equal. unfold lseg. rewrite (limbs_val_lval (skipn (Z.to_nat n) xs)), length_skipn. f_equal. clear - HN LEN1. lia.
    - (* [comment removed for export] *)
      assert (EO : own = LHeap) by (destruct own; [exfalso; ddestruct (OWN0 eq_refl) as (_ & E0 & _); clear - E0 K HN; lia| reflexivity| exfalso; exact (NS1 eq_refl)]).
      subst own. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
      pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
      assert (ANX : md_addr dA <> X) by (intros E; destruct (VA1 E) as [E1 _]; clear - E1 K; lia).
      destruct (VA2 ANX) as [ENa VA].
      assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
        by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
      destruct (stk_split asegs mc lo (bv_unsigned sp + -112) (bv_unsigned sp + -104) ST1 ltac:(clear - SLO2 NEEDR LOSP; lia)) as [STa _].
      destruct (stk_carve asegs mc lo (bv_unsigned sp + -112) 16 STa ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
      replace (bv_unsigned sp + -112 - Z.of_nat 16) with (bv_unsigned sp + -128) in STc, SLOT by (clear; lia).
      (* [comment removed for export] *)
      pose proof XARR as PU. rewrite <- (firstn_skipn (Z.to_nat NA) xs) in PU. apply u32arr_app in PU. destruct PU as [PUlo PUhi].
      rewrite firstn_length_le in PUhi by (clear - HN HNA LEN1; lia). replace (4 * Z.of_nat (Z.to_nat NA)) with (4 * NA) in PUhi by (clear - HN; lia).
      assert (LHI : Z.of_nat (length (skipn (Z.to_nat NA) xs)) = N - NA) by (rewrite length_skipn; clear - HN HNA LEN1; lia).
      pose proof (conj PUlo I) as PUlo'. clear CEA OEA.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      zstep. zstep. if_cases KU1; zify_cond KU1; [exfalso; clear - KU1 HN HNA; lia|].
      zstep. zstep. zstep. zstep. if_cases KU2; zify_cond KU2; [exfalso; clear - KU2 HN HNA P0; chk_ltb KU2; lia|].
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      zstep. zstep.
      clear MU WM. pose proof (munch_refl [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -128)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
      pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_SA) as SPM. unfold A_ASAN_MEMSET_SA in SPM.
      acallxA_sp (bv_unsigned sp + -128)
        (eapply SPM with (h := hc) (LB := LBc) (LF := LF) (DST := pXc + 4 * NA) (v := 0) (n := 4 * (N - NA)) (lo := lo) (ds := u32s (skipn (Z.to_nat NA) xs));
         rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia;
         try eassumption; try reflexivity;
         first [ left; rewrite AMS; reflexivity
               | apply MpiWalkAux.u8arr_of_u32arr; exact PUhi
               | rewrite u32s_length; clear - LHI HN HNA; lia
               | eapply aobj_sub; [exact OP| clear - HN; lia| clear - HN HNA; lia]
               | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
               | eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear - HN; lia| clear - HN HNA; lia]
               | rewrite HT1; clear - TOP; lia
               | f_equal; clear; lia
               | right; clear - P47 HN HNA; lia
               | clear - XLSc SLO2 NEEDR HN HNA NR1 NRA LOS SPA SPR LOSP K; lia
               | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ] ]).
      clear SPM.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo (bv_unsigned sp + -128) |- _ => rename H into ST6 end.
      match goal with H : u8arr asegs m6 (pXc + 4 * NA) _ |- _ => rename H into HPZ end.
      match goal with H : HM asegs R HIA hc LBc LF m6 |- _ => rename H into HH6 end.
      match goal with H : rw_cells asegs m6 (bv_unsigned sp + -128) _ |- _ => rename H into SL6 end.
      match goal with H : rw_cells asegs m6 (bv_unsigned sp + -112) _ |- _ => rename H into SPL6 end.
      assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
      { eapply stk_merge with (mid := bv_unsigned sp + -112); [| | clear - SLO2 NEEDR LOSP; lia].
        - eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
          replace (bv_unsigned sp + -112) with (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 16 junk])) by (cbn; clear; lia).
          apply stk_of_rw_cells. exact SL6.
        - replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [C8 (Z_to_bv 64 (md_addr dB))])) by (cbn; clear; lia).
          apply stk_of_rw_cells. exact SPL6. }
      destruct PUlo' as [PUlo _].
      pose proof (u32arr_transport asegs _ mc m6 _ _ PUlo MU WM) as PUlo6. rewrite firstn_length_le in PUlo6 by (clear - HN HNA LEN1; lia).
      specialize (PUlo6 ltac:(cbn [disjoint_from]; clear - HN HNA XLSc SLO2 NEEDR P0 NR1; lia)).
      replace (Z.to_nat (4 * (N - NA))) with (4 * Z.to_nat (N - NA))%nat in HPZ by (clear - K; lia).
      apply (rw_cells_of_u8arr asegs) in HPZ.
      assert (XARR6 : u32arr asegs m6 pXc (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA)))).
      { apply u32arr_app. split; [exact PUlo6|]. rewrite firstn_length_le by (clear - HN HNA LEN1; lia). replace (4 * Z.of_nat (Z.to_nat NA)) with (4 * NA) by (clear - HN; lia).
        eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]. }
      assert (HW6 : forall a, ~ outside [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -128)] a ->
                    (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
      { intros a NO. cbn [outside] in NO.
        assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN HNA; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -128)] (bv_unsigned sp - 104) 104).
      { cbn. split; [clear - XLSc SLO2 NEEDR HN HNA; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -128)] X 16).
      { cbn. split; [clear - XPc HN HNA; lia| split; [clear - DSX; lia| exact I]]. }
      assert (LEN6' : length (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA))) = length xs).
      { rewrite length_app, repeat_length, firstn_length_le by (clear - HN HNA LEN1; lia). clear - HN HNA LEN1 K; lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6 DJF DJX XARR6 LEN6') as J6.
      pose proof (rideS_xl_munch dA _ _ _ _ _ _ (pXc + 4 * NA) (pXc + 4 * NA + 4 * (N - NA)) (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA))) m6 J0 RA eq_refl
                    ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear; lia) MU WM) as RA6.
      pose proof (rideS_xl_munch dB _ _ _ _ _ _ (pXc + 4 * NA) (pXc + 4 * NA + 4 * (N - NA)) (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA))) m6 J0 RB eq_refl
                    ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear; lia) MU WM) as RB6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6, RA6, RB6.
      zstep.
      eapply sa_CSUBr; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact RA6| exact RB6| cbn [md_n]; clear - HN HNA; lia| intros _; reflexivity
                       | intros E; exfalso; exact (ANX E)| | | exact VB2| exact BV| exact BF].
      + intros _. split; [rewrite ENa; clear - HN; lia|]. cbn [md_limbs]. rewrite (zext_high xs NA n _ HN ltac:(rewrite LEN1; exact HNA)). exact VA.
      + intros E. cbn [md_limbs]. rewrite (zext_low xs NA n _ HN ltac:(rewrite LEN1; exact HNA)). exact (VB1 E).
    all: match goal with |- ?g => idtac "MEMSET-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis A47 : md_own dA <> LNull -> md_p dA + 4 * md_n dA + 8 <= 2^47.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0350@C11264273767.238C11264273767.239C17025492443.235C17025492443.236C17025492443.237C237391055.240  D49149041523.242K10420231391.243K14404318560.241K14404318560.243K19167344963.235K19167344963.236K19167344963.237K23923546397.241K25382859142.241K28709825590.241K36226586886.241K39785057286.241K46334408099.238K46334408099.239K47640792208.241K65977774223.241K8474424312.241 K9644101664.235 K9644101664.236 K9644101664.237 L10307112399.6  L10420362414.22 L10430644263.5  L10433304520.5  L12530932062.2  L13194033576.4  L14399007128.5  L14402745233.4  L146940511.12   L15732191779.8  L17363933084.3  L17899959536.3  L19169968050.5  L21185175647.13 L21820691587.186L21824705721.215L21824805693.6  L22648980509.4  L23100341967.211L23458795923.213L23461305150.175L23461383506.174L23644720577.215L23911418744.3  L23999514035.240L25075940858.17 L25238078280.8  L25367656311.17 L2610977716.1   L26349732406.4  L26711796672.7  L28709956679.22 L28719786695.5  L28722019415.6  L30116386634.3  L30743879498.22 L30747872606.3  L31344024617.5  L31660590328.4  L3370416396.3   L34125036709.14 L35663928186.7  L36233404407.4  L38126476039.3  L38129129185.3  L38235734261.1  L38419819008.4  L39172636981.0  L39280637297.0  L39790824183.4  L40145318023.3  L41072603811.211L41072603812.214L41126667518.5  L41435825861.1  L414529038.13   L43082406170.1  L43343125556.7  L43878034250.5  L44359877029.4  L44608837741.2  L45711213078.15 L46329554370.4  L47401054516.1  L47638170209.4  L47725787526.2  L48022265433.14 L48157275717.211L51284464315.213L51476717110.4  L52531031119.6  L5260001178.175 L53236858660.5  L53236858660.6  L53516864273.211L53516864279.213L53611082567.22 L53615638561.2  L5413828406.4   L55376803619.3  L55713320373.215L5630863510.2   L56339604272.4  L56577124758.2  L57129482334.4  L58641002120.175L59308873939.7  L59311007312.5  L59311007313.8  L59311007318.5  L59311007319.8  L59952597784.1  L60098763854.3  L60283674290.10 L6141606276.1   L61714773053.6  L61927706159.186L61931654677.215L65925215236.5  L65976202878.4  L66151427842.17 L66590572961.0  L67229871644.4  L67699444668.5  L68505269079.5  L7458806278.5   L8478935369.14  L8486281629.3   L8927572646.214 L8927572647.213 L9631842885.2   O10808784559.241O11264273767.238O11264273767.239O15317411454.243O16243737850.241O16578584084.241O17025492443.235O17025492443.236O17025492443.237O237391055.240  O36019832244.241O36632239767.235O36632239767.236O36632239767.237O44976997556.241O48199580980.241O50423766113.241O57399310481.241O8875751214.241 O8875751214.243 P14404318560.241P28709825590.241P46334408099.238P46334408099.239P9644101664.235 P9644101664.236 P9644101664.237 Q10042611905.220Q12370813529.219Q17201186764.218Q18135743526.174Q18136070065.177Q18136087844.177Q26345934764.242Q32879014451.242Q34224482651.174Q34422627987.177Q37618859054.218Q38248387216.242Q39095944126.221Q39212284437.177Q40278613695.219Q43879899724.242Q48476778790.247Q50852185413.247Q5470532147.218 Q5485174314.219 Q58692335428.177Q59703481013.219Q60511567613.177Q60807234163.221Q61264001456.221Q61266183986.220Q6143569392.219 Q64768105610.177Q66030093059.222Q66375044744.221Q67327024261.220Q8222473558.221 Q9538787269.174 00000100200300400500600701001102802l03`04T05C06B06C07B08A08B08C09H0:>0:_0:`0:a0:b0;60;T0;U0;V0;_0;k0;l0;m0<X0=10=90=A0=B0=a0>T0?U0?h0@10@R0A\0B60BP0CR0CS0DF0Dn0EG0EH0EL0EY0F00FR0FS0FT0F]0G30G40G@0GL0GU0H70HL0HM0HN0HO0HS0H^0H_0H`0Ha0Hj0JA0KP0KQ0KT0L40L80LO0LV0Lb0Lh0Lo0M00M40M50M<0M=0NF0Ng0O40OH0Ob0P20PB0Pc0QD0Q^0Q_0Ql0R50RV0R]0Rh0Ro0S:0ST0Si0T:0TS0Tc0U<0U@0UJ0Uh0Ul0V?0Vl0X10XE0XF0Xl0Xm0Xn0Xo0Y?0Y@0YA0YB0ZH0[R0[S0[T0[U0[V0[W0[X0[Y0[Z0[[0[\0\30\40\50\60\70\80\90\:0\;0\<0\=0\>0\?0\@0\A0\B0\C0\D0\Y0]C0]Z0]e0^00^;0^X0_90_D0_O0_f0`>0`?0`J0`K0`f0ab0bO0bf0c=0cK0cL0cT0cU0cj0d?0dV0da0e\0f10fF0g:0gBFFFFFFFS2sp1X3xs02dA2lo1n2NA2xs2KX3ENa1K3EP03ESK4LMID1l4SLEN3TK3FS1X3xs02dA1n2NA1N3pXc2xs3HNA3VA14LEN12KX3ENa1K3EP04SEPL4LMID1l4SLEN3TK3S1R2sp3xs02dA2lo1n2NA1N3pXc2xs3HNA3LOS3ALO1K2PC4LMIDS1R2sp3xs02dA2lo1n2NA1N3pXc2xs3HNA3LOS3ALO1K2PC4LMIDS1R2sp3xs02dA2lo1n2NA1N3pXc2xs3HNA3LOS3ALO1K2PC4LMIDS2sp1X3xs02dA2lo1n2NA2xs2KX4LENE1K3EP03ESK4LMIDS1R2sp3xs02dA2lo4SLO21n2NA1N3pXc2xs3HNA5NEEDR3LOS3ALO1K2PC4LMIDFS1R2sp3xs02dA2lo4SLO21n2NA1N3pXc2xs3HNA5NEEDR3LOS3ALO1K2PC4LMIDS1R2sp3xs02dA2lo4SLO21n2NA1N3pXc2xs3HNA5NEEDR3LOS3ALO1K2PC4LMIDFFS1X3xs02dA1n2NA1N3pXc2xs3HNA3VA14LEN12KX4LENE3ENa1K3EP04SEPL4LMID3TK3S1X3xs02dA1n2NA1N3pXc2xs3HNA3VA12KX1K3EP03XPc4LMID3TK3S2sp1X3xs02dA2lo1n2NA2xs3DSX4LMIDFFFS1R2sp2lo4SLO25NEEDRS2sp2dA2lo1n2NA2HN3SPR3ENa3ESKFFS3dXc3NR1S2dA1n2NA2HNFFS1R2sp2lo4SLO21n2NA1N3pXc2HN3HNA5NEEDR4XLScS1n2NA1N2xs2HN3HNA4LEN11KS1n2NA1KS1n2NA1KFS2dA1n2NA1N3pXc2HN3HNA3ENa4SEPLS2ra2sp1X3xs02dA2NA1N2xs3HNA2X03SPR3NR12A04LENE3ENaS2ra2sp1X3xs02dA1n2NA3pXc2xs2X03SPR2A03ENa1K3EP02P04A47'4LMID3TK3S1n2NA1N2HN3HNA3NR1S2dA1n2NAS2ra2sp1X3xs02dA1n2NA3pXc2xs4LMIDS2ra2sp1X3xs02dA1n2NA3pXc2xs2X03SPR2A03ENa1K3EP02P04A47'4LMID4SLEN3TK13TK3S2ra2sp1X3xs02dA2xs2A03A16S2ra2sp1X3xs02dA2xs2A03A16S2ra2sp1X3xs02dA1n2NA3pXc2xs2HN2X03SPR2A03ENa3EP02P04A47'4LMID3TK3FS2ra2sp1X3xs02dA1n2NA3pXc2xs4LMID4Amid2HI3LAM5LEN6'S2sp2lo1n2NA1N3pXc2xs2HN3HNA4LEN11K4XLScS1X1n2NA1N3pXc2HN3HNA3XPcFS2spS1n2NA3pXc2HNS1n2NA1N2xs2HN3HNA4LEN1S2sp2lo1n2NA1N3pXc2HN3HNA3SPR4XLScFFS1n2NA2HNS1R2sp2lo4SLO23NRA3SPRFS1n2NA3pXc1KS1n2NA3pXc1KS1n2NA2HNS2sp2lo1n2NA1N3pXc2HN3HNA3NR14XLScS1R3HIA1h2sp2lo3TOP1HFFFS2loS1n2NA2HN1KSSFS1n2NA2HNS2ra2sp1X3xs02dA1n2NA1N3pXc2xs2HN2X03SPR2A03ENa1K3EP02N12P03P474A47'4LMID4SLEN4LENE3TK1S2ra2sp1X3xs02dA1n2NA1N3pXc2xs2X03SPR2A03ENa1K3EP02N12P03P474A47'4LMID4SLEN3TK3FS1nS1n2NA1N3pXc3HNA3P472dA3ENa4A47'S2NAS1n2NA1N2xs2HN3HNA4LEN1S2sp2loS2dA1n2NA2HNS1n2NAS2sp2loFS2spFS2sp2loFS2ra2sp1X3xs02dA1n2NA1N3pXc2xs3HNA2X03SPR2A03ENa1K3N1e3EP02P03P474LMID2N1S2ra2sp1X3xs02dA1n2NA3pXc2xs4LMIDS2sp1X2lo3DSXS1R2sp2lo4SLO25NEEDRS2ra2sp1X3xs02dA2xs2X03X16S1n2NA1N3pXc3HNAS1n2NA1N3pXc3HNAS2ra2sp1X3xs02dA1n2NA3pXc2xs4LMIDS2ra2sp1X3xs02dA1n2NA3pXc2xs4LMIDS2sp1n2NA1N2HN3HNA3SPR3NR1FS1n2NA3pXc2xsS1n2NA2HNS2ra2sp1X3xs02dA1n2NA3pXc2xs4LMIDS2sp2loS1n2NA2HN1KS2sp2loS1n2NA2HN1KS2ra2sp1X3xs02dA2xs2A03A16S2dA1n2NA2HN3ENa1K2Z0S1n2NA3pXc2HN3TK1S1n2NA3pXc2HN1H2H03TK22P0S2dA1n2NA2HN3TK3S2dA1n2NA2HN1H2H03TK43EP0S2spS1R2lo3LOSS2sp2lo1n2NA1N3pXc2HN3HNA1a2NOS2spS1n2NA1N2HN3HNA3NR1S2ra2sp1X3xs02dA1n2NA2xs2HN2X03SPR2A03NRE3ENaS2ra2sp1X3xs02dA1n2NA3pXc2xs2HN2X03SPR2A03ENa1K3EP02P04A47'4LMID4SLENS1R2sp2lo4SLO25NEEDRFS1n3pXc2r04XPAL1q1r1H2H02q02H42dA4EPALSFFS1R3HIA1h2sp3TOPFFFS2ra2sp1X3xs02dA1n2NA3pXc2xs2X03SPR2A03ENa1K3EP02P04A47'4LMID4SLEN3TK3S2ra2sp1X3xs02dA1n2NA3pXc2xs2X03SPR2A03ENa1K3EP02P04A47'4LMID4SLEN3TK13TK3FFFFFFFFFFS2dA1n2NA3pXc2xs1K4LMIDFFFFFFFFFFFFFFFFFS3xs02dA1n2NA2xs4LMIDS2ra2sp1X3xs02dA1n2NA3pXc2xs2X03XAL1K4LMIDS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2xsS3xs02dA2xsS3xs02dA2xsS3xs02dA1n2NA3pXc2xs4LMID3TK1S3xs02dA1n2NA1N3pXc2xs3HNA1K4LMIDS3xs02dA2xsS3xs02dA2xsS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2lo1n2NA2xs4LMIDFS3xs02dA2xsFS2sp3xs02dA2lo1n2NA2xs4LMIDS1R2sp3xs02dA2lo4SLO21n2NA2xs5NEEDR1K4LMID4Amid2HI3LAM5LEN6'S2sp3xs02dA2lo1n2NA2xs4LMID4Amid2HI3LAM5LEN6'S1X3xs02dA1n2NA2xs4LMIDS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2xs2A0FS3xs02xsFS3xs02dA1n2NA2xs4LMIDS3xs02dA1n2NA2xs4LMIDS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2xsS1R2sp3xs02dA2lo4SLO21n2NA2xs5NEEDR3LOS4SP643ALO3ACP1K4LMIDS3xs02dA1n2NA2xs4LMIDS3xs02dA1n2NA2xs4LMIDS2ra2sp1X3xs02dA1n2NA3pXc2xs2X03SPR2A03AAL1K2P04LMIDS3xs02xs". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 A47"] Lemma sa_TAIL : forall n NA, KJ_stmt n NA.
  Proof.
    unfold KJ_stmt. intros n NA. intros until xt6; intros J0 NGX SPL0 RA RB HN HNA EOn VA1 VA2 VB1 VB2o BV BF.
    assert (VB2 : md_addr dB <> X -> n <= md_n dB /\ lval (md_limbs dB) n = mpd_abs dB) by (intros C; destruct (VB2o C); split; assumption).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct (rideS_view dA _ _ _ _ _ _ 0 J0 RA ltac:(clear; lia) ltac:(intros _; clear - NR1; lia) ltac:(intros C; rewrite (VA2 C); clear - HN; lia))
      as (pa & sa & na & pda & ysA & CEA & OEA & A0 & A16 & AAL & _ & _ & _ & _ & _ & _ & _ & _ & _ & NAX & NAR).
    assert (ENA : na = NA) by (destruct (Z.eq_dec (md_addr dA) X) as [E|NE]; [rewrite (NAX E); exact (proj1 (VA1 E))| rewrite (NAR NE); exact (VA2 NE)]).
    subst na. clear NAX NAR.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1, CEA.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    shadow_chk OEA (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear - A0 A16 X0 X16; lia).
    - (* [comment removed for export] *)
      eapply sa_MEMSET; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact SPL0| exact RA| exact RB| exact HN| exact HNA| exact EOn| exact VA1| | exact VB1| exact VB2| exact BV| exact BF].
      intros NE. exfalso. exact (NE KX).
    - (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 NA)) with (Z_to_bv 64 NA) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1 HN HNA; lia); rewrite Z.mod_small by (clear - NR1 HN HNA; lia); reflexivity).
      destruct RA as [E|[DBJA BA]]; [exfalso; exact (KX E)|].
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJA _ _ _ _ BA) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
      pose proof (VA2 KX) as ENa.
      assert (VAL : limbs_val (md_limbs dA) = mpd_abs dA) by (unfold mpd_abs; reflexivity).
      (* [comment removed for export] *)
      zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (clear - NR1 HN HNA; lia).
      + (* [comment removed for export] *)
        assert (EnN : n = NA) by (clear - K HN; lia). subst n.
        eapply sa_MEMSET; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact SPL0| right; split; [exact DBJA| exact BA]| exact RB| exact HN| exact HNA| exact EOn| exact VA1| | exact VB1| exact VB2| exact BV| exact BF].
        intros _. split; [exact ENa|]. unfold lseg. replace (NA - NA) with 0 by (clear; lia). unfold lval at 2. cbn [Z.to_nat firstn limbs_val].
        rewrite Z.mul_0_r, Z.add_0_r. rewrite <- VAL. rewrite (limbs_val_lval (md_limbs dA)), LENE, ENa. reflexivity.
      + (* [comment removed for export] *)
        assert (EN : md_own dA <> LNull) by (intros C; destruct (OWNE0 C) as [_ Z0]; clear - Z0 ENa K HN; lia).
        ddestruct (OWNE1 EN) as (N1e & EP0 & EPAL & EBY & ESK & _).
        assert (EO : own = LHeap) by (apply EOn; clear - K HN; lia). subst own.
        ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
        pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
        pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ BA eq_refl EN) as SEPL. pose proof (bj_aobjL _ _ _ _ _ _ _ _ _ _ BA EN) as OAL.
        cbn [md_own md_p md_n] in SEPL. pose proof (A47 EN) as A47'.
        replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
        destruct (stk_split asegs mc lo (bv_unsigned sp + -112) (bv_unsigned sp + -104) ST1 ltac:(clear - SLO2 NEEDR LOSP; lia)) as [STa _].
        destruct (stk_carve asegs mc lo (bv_unsigned sp + -112) 16 STa ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
        replace (bv_unsigned sp + -112 - Z.of_nat 16) with (bv_unsigned sp + -128) in STc, SLOT by (clear; lia).
        (* [comment removed for export] *)
        pose proof XARR as PU. rewrite <- (firstn_skipn (Z.to_nat n) xs) in PU. apply u32arr_app in PU. destruct PU as [PUlo PUr].
        rewrite firstn_length_le in PUr by (clear - HN HNA LEN1; lia). replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) in PUr by (clear - HN; lia).
        rewrite <- (firstn_skipn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) xs)) in PUr. apply u32arr_app in PUr. destruct PUr as [PUmid PUhi].
        assert (LMID : length (firstn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) xs)) = Z.to_nat (NA - n)) by (apply firstn_length_le; rewrite length_skipn; clear - HN HNA LEN1; lia).
        rewrite LMID in PUhi. replace (pXc + 4 * n + 4 * Z.of_nat (Z.to_nat (NA - n))) with (pXc + 4 * NA) in PUhi by (clear - HN K; lia).
        (* [comment removed for export] *)
        pose proof EBY as EBr. rewrite <- (firstn_skipn (Z.to_nat n) (md_limbs dA)) in EBr. rewrite u32s_app in EBr. apply bytes_at_app in EBr. destruct EBr as [_ EBr].
        rewrite u32s_length, firstn_length_le in EBr by (rewrite <- (Nat2Z.id (length (md_limbs dA))), LENE, ENa; clear - HN; lia).
        replace (md_p dA + Z.of_nat (4 * Z.to_nat n)) with (md_p dA + 4 * n) in EBr by (clear - HN; lia).
        rewrite <- (firstn_skipn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) (md_limbs dA))) in EBr. rewrite u32s_app in EBr. apply bytes_at_app in EBr. destruct EBr as [SBY _].
        assert (SLEN : Z.of_nat (length (u32s (firstn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) (md_limbs dA))))) = 4 * (NA - n)).
        { rewrite u32s_length, firstn_length_le by (rewrite length_skipn, <- (Nat2Z.id (length (md_limbs dA))), LENE, ENa; clear - HN K; lia). clear - K; lia. }
        pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ BA)) as [(CE & _) _]. clear CEA. unfold mpi_cells in CE.
        pose proof (conj PUlo I) as PUlo'. pose proof (conj PUhi I) as PUhi'.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases TK1; zify_cond TK1; [exfalso; clear - TK1 HN; lia|].
        zstep. zstep. zstep. zstep. if_cases TK2; zify_cond TK2; [exfalso; clear - TK2 HN P0; chk_ltb TK2; lia|].
        zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases TK3; zify_cond TK3; [exfalso; clear - TK3 HN; lia|].
        zstep. zstep. zstep. zstep. if_cases TK4; zify_cond TK4; [exfalso; clear - TK4 HN EP0; chk_ltb TK4; lia|].
        zstep. zstep. zstep. zstep. zstep. if_cases TK5; zify_cond TK5; [exfalso; apply TK5; apply lor_land3; [clear - XPAL; Z.div_mod_to_equations; lia| clear - EPAL; Z.div_mod_to_equations; lia]|].
        (* [comment removed for export] *)
        zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
        clear CE OEA.
        clear MU WM. pose proof (munch_refl [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -128)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_SA) as SPC. unfold A_ASAN_MEMCPY_SA in SPC.
        acallxA_sp (bv_unsigned sp + -128)
          (eapply SPC with (h := hc) (LB := LBc) (LF := LF) (DST := pXc + 4 * n) (SRC := md_p dA + 4 * n) (n := 4 * (NA - n)) (lo := lo)
                            (ds := u32s (firstn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) xs))) (ss := u32s (firstn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) (md_limbs dA))));
           rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by qlia;
           try eassumption; try reflexivity;
           first [ left; rewrite AMC; reflexivity
                 | apply MpiWalkAux.u8arr_of_u32arr; exact PUmid
                 | rewrite u32s_length, LMID; clear - K; lia
                 | eapply aobj_sub; [exact OP| clear - HN; lia| clear - HN HNA; lia]
                 | eapply aobj_sub; [exact OAL| clear - HN; lia| rewrite ENa; clear - HN; lia]
                 | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
                 | eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear - HN; lia| clear - HN HNA; lia]
                 | rewrite HT1; clear - TOP; lia
                 | f_equal; clear; lia
                 | right; clear - P47 A47' SEPL HN HNA K ENa NR1; lia
                 | clear - XLSc ESK SLO2 NEEDR HN HNA NR1 NRA LOS SPA SPR LOSP K ENa; lia
                 | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "TCOPY-PRE-LEFT:" g end ] ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-TCOPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
        match goal with H : stk asegs m6 lo (bv_unsigned sp + -128) |- _ => rename H into ST6 end.
        match goal with H : u8arr asegs m6 (pXc + 4 * n) _ |- _ => rename H into HPA end.
        match goal with H : HM asegs R HIA hc LBc LF m6 |- _ => rename H into HH6 end.
        match goal with H : rw_cells asegs m6 (bv_unsigned sp + -128) _ |- _ => rename H into SL6 end.
        match goal with H : rw_cells asegs m6 (bv_unsigned sp + -112) _ |- _ => rename H into SPL6 end.
        assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
        { eapply stk_merge with (mid := bv_unsigned sp + -112); [| | clear - SLO2 NEEDR LOSP; lia].
          - eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
            replace (bv_unsigned sp + -112) with (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 16 junk])) by (cbn; clear; lia).
            apply stk_of_rw_cells. exact SL6.
          - replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [C8 (Z_to_bv 64 (md_addr dB))])) by (cbn; clear; lia).
            apply stk_of_rw_cells. exact SPL6. }
        destruct PUlo' as [PUlo _]. destruct PUhi' as [PUhi _].
        pose proof (u32arr_transport asegs _ mc m6 _ _ PUlo MU WM) as PUlo6. rewrite firstn_length_le in PUlo6 by (clear - HN HNA LEN1; lia).
        specialize (PUlo6 ltac:(cbn [disjoint_from]; clear - HN HNA XLSc SLO2 NEEDR P0 NR1; lia)).
        pose proof (u32arr_transport asegs _ mc m6 _ _ PUhi MU WM) as PUhi6. rewrite !length_skipn in PUhi6.
        specialize (PUhi6 ltac:(cbn [disjoint_from]; clear - HN HNA K LEN1 XLSc SLO2 NEEDR P0 NR1; lia)).
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        set (Amid := firstn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) (md_limbs dA))) in *.
        set (HI := skipn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) xs)) in *.
        assert (LAM : length Amid = Z.to_nat (NA - n)) by (subst Amid; apply firstn_length_le; rewrite length_skipn, <- (Nat2Z.id (length (md_limbs dA))), LENE, ENa; clear - HN K; lia).
        assert (XARR6 : u32arr asegs m6 pXc (firstn (Z.to_nat n) xs ++ (Amid ++ HI))).
        { apply u32arr_app. split; [exact PUlo6|]. rewrite firstn_length_le by (clear - HN HNA LEN1; lia). replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) by (clear - HN; lia).
          apply u32arr_app. split; [eapply (u32arr_of_cells asegs); [exact HPA| reflexivity]|].
          rewrite LAM. replace (pXc + 4 * n + 4 * Z.of_nat (Z.to_nat (NA - n))) with (pXc + 4 * NA) by (clear - HN K; lia). exact PUhi6. }
        assert (HW6 : forall a, ~ outside [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -128)] a ->
                      (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
        { intros a NO. cbn [outside] in NO.
          assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN HNA; lia).
          destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
        assert (DJF : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -128)] (bv_unsigned sp - 104) 104).
        { cbn. split; [clear - XLSc SLO2 NEEDR HN HNA; lia| split; [clear; lia| exact I]]. }
        assert (DJX : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -128)] X 16).
        { cbn. split; [clear - XPc HN HNA; lia| split; [clear - DSX; lia| exact I]]. }
        assert (LEN6' : length (firstn (Z.to_nat n) xs ++ (Amid ++ HI)) = length xs).
        { rewrite !length_app, LAM, firstn_length_le by (clear - HN HNA LEN1; lia). subst HI. rewrite !length_skipn. clear - HN HNA LEN1 K; lia. }
        pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6 DJF DJX XARR6 LEN6') as J6.
        pose proof (rideS_xl_munch dA _ _ _ _ _ _ (pXc + 4 * n) (pXc + 4 * n + 4 * (NA - n)) (firstn (Z.to_nat n) xs ++ (Amid ++ HI)) m6 J0 (or_intror (conj DBJA BA)) eq_refl
                      ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear - HNA; lia) MU WM) as RA6.
        pose proof (rideS_xl_munch dB _ _ _ _ _ _ (pXc + 4 * n) (pXc + 4 * n + 4 * (NA - n)) (firstn (Z.to_nat n) xs ++ (Amid ++ HI)) m6 J0 RB eq_refl
                      ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear - HNA; lia) MU WM) as RB6.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6, RA6, RB6.
        zstep.
        eapply sa_MEMSET; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact SPL6| exact RA6| exact RB6| exact HN| cbn [md_n]; exact HNA| intros _; reflexivity
                          | intros E; exfalso; exact (KX E)| | | exact VB2| exact BV| exact BF].
        * intros _. split; [exact ENa|]. cbn [md_limbs].
          assert (LS : lseg (firstn (Z.to_nat n) xs ++ (Amid ++ HI)) n NA = lseg (md_limbs dA) n NA).
          { unfold lseg. rewrite skipn_app, firstn_length_le by (clear - HN HNA LEN1; lia). rewrite Nat.sub_diag, skipn_O.
            rewrite skipn_all2 by (rewrite firstn_length_le by (clear - HN HNA LEN1; lia); clear; lia). cbn [app].
            rewrite lval_app_l by (rewrite LAM; clear - K; lia). unfold lval. subst Amid. rewrite firstn_firstn, Nat.min_id. reflexivity. }
          rewrite LS, <- (lval_split (md_limbs dA) n NA HN). rewrite <- VAL, (limbs_val_lval (md_limbs dA)), LENE, ENa. reflexivity.
        * intros E. cbn [md_limbs]. rewrite lval_app_l by (rewrite firstn_length_le by (clear - HN HNA LEN1; lia); clear - HN; lia).
          rewrite <- (VB1 E). unfold lval. rewrite firstn_firstn, Nat.min_id. reflexivity.
    all: match goal with |- ?g => idtac "TAIL-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@D50818716548.178D61461898774.178K42587433812.178L14740288161.5  L15477852824.1  L16636399386.4  L21826988606.165L21826988989.178L23999514035.173L24982576641.167L26168871548.12 L26502719108.5  L29763661393.2  L29765672657.178L33177208579.173L3465864266.3   L35663928186.7  L42594106808.2  L46160487540.170L46160492685.167L48481432450.5  L52259572182.1  L5259998348.166 L5260339702.169 L53982396750.1  L58609956177.2  L59308630368.3  L59308632045.3  L59308660947.5  L60098763854.3  L6141606276.1   L67080090232.4  L7735739976.14  Q11801279589.178Q25513505925.177Q26207421841.171Q26207721832.172Q26207772262.169Q29323018297.177Q31654082872.171Q39212284437.172Q43925228937.172Q48474732447.174Q49698585326.176Q50854331388.174Q5829129450.175 Q60511567613.172Q60697995187.172Q8880831802.169 Q9538458057.169 00000l01i02f03:03>03J03n04R04b05205\06006706M06]06f07;07<07S07j08>08B08Y09009409;09E09N09]09g09k0:60::0:W0;70;A0;K0;U0<B0<L0<V0<`0=;0=T0=b0>00>80>E0>O0>WS1R3HIA1h2ra2sp1X3xs02dB2hc2xs3TOP2X03SPR3HT12HB5Ha_st5Hl_stS1R2ra2sp1X3xs02dB2lo4SLO22xs5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R2sp1X3xs02dB2lo4SLO23pXc2xs5NEEDR2X03DSX2KN2HB5Ha_st5Hl_stS1R2sp2lo4SLO25NEEDRS2spS1N2NA2K02K1S2ra2sp1X3xs02xs1n2NA2HN4NA162X03SPRS2ra2sp1X3xs02xs1n2NA2HN4NA162X03SPRS2ra2sp1X3xs02xsS2ra2sp1X3xs02xsS1X2sX2nX2pX3xs04padX4ownX2dA2dB1v2BV4PHI0S1R2sp2lo4SLO25NEEDRS1N3NR1S2ra2sp1X3xs01N2xs3NR1S2ra2sp1X3xs02xsS1N2NA2K1S1R3HIA1h2sp2lo3TOP1HFS2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S1R2sp2lo4SLO25NEEDRS2spS2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S2spS1N3NR1S1X3XAL2KAS1X2X02KNS1N2NA2K12H12E0S1R2lo3LOSS2spS1d2D01f2BFS2spS2sp3xs02dB2xs2HB5Ha_st5Hl_stS2sp3xs02dB2lo2xs2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xsS1X3xs02xsS1R2sp3xs02dB2lo4SLO22xs5NEEDR2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xsS1X3xs02xsS1R2sp3xs02lo4SLO22xs5NEEDRS2sp3xs02xs4SP642HB5Ha_stS2sp3xs02lo2xsS2sp3xs02xs2HBS3xs02xsS1X3xs02xs2X0S1X3xs02xsS3xs02xs". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC AMS C24H JC TPV UWX D0 BUD BUDF SLO2 A47"] Lemma sa_J1 : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (n NA : Z)
      (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs10 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    0 <= n <= NA ->
    NA < 2 ^ 16 ->
    (md_addr dA = X -> md_n dXc = NA /\ limbs_val (md_limbs dXc) = mpd_abs dA) ->
    (md_addr dA <> X -> md_n dA = NA) ->
    (md_addr dB = X -> lval (md_limbs dXc) n = mpd_abs dB /\ n <= md_n dXc) ->
    (md_addr dB <> X -> lval (md_limbs dB) n = mpd_abs dB /\ n <= md_n dB) ->
    v <= 0 ->
    f <= 0 ->
    0 <= sub_abs_PHI dX dA dB ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              xs3 (Z_to_bv 64 (md_addr dA + 10)) (Z_to_bv 64 NA) xs6 SB (Z_to_bv 64 (4 * n)) (SHA (md_addr dB)) xs10 (SHA (md_addr dA + 10)) xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e610) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX RA RB HN NA16 VA1 VA2 VB1 VB2 BV BF PHI0.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (BF' : f <= sub_abs_FR d) by (unfold sub_abs_FR, calls_FR, fr_charge; clear - BF D0; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - HN NA16; lia).
    { eapply sa_ret with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| right; left; reflexivity| clear - BV PHI0; lia| exact BF']. }
    (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN; [exfalso; clear - KN X0; lia|].
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite land7_mod in KA; clear - KA XAL; lia|].
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [jk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
    clear MU WM. pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : mem_inv asegs m1 |- _ => rename H into MIs end.
    match goal with H : HM asegs R HIA hc LBc LF m1 |- _ => rename H into HHs end.
    match goal with H : stk asegs m1 lo (bv_unsigned sp + -112) |- _ => rename H into STs end.
    match goal with H : rw_cells asegs m1 (bv_unsigned sp + -112) _ |- _ => rename H into SPL1 end.
    assert (STs' : stk asegs m1 lo (bv_unsigned sp - 104)) by (stk_top STs SPL1 (bv_unsigned sp - 104); clear - SLO2 NEEDR; lia).
    pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m1 J0 MU WM MIs STs' HHs ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as Js.
    pose proof (rideS_stk_munch dA _ _ _ _ _ _ (bv_unsigned sp + -112) (bv_unsigned sp + -104) m1 J0 RA ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia) MU WM) as RAs.
    pose proof (rideS_stk_munch dB _ _ _ _ _ _ (bv_unsigned sp + -112) (bv_unsigned sp + -104) m1 J0 RB ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia) MU WM) as RBs.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in Js, RAs, RBs.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - HN NA16 NR1; lia).
    - eapply (sa_TAIL n NA); [exact Js| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact SPL1| exact RAs| exact RBs| exact HN| cbn [md_n]; clear - K1; lia| | exact VA1| exact VA2| intros E; exact (proj1 (VB1 E))| exact VB2| clear - BV PHI0; lia| exact BF'].
      cbn [md_own]. intros H1. destruct own; [exfalso; ddestruct (OWN0 eq_refl) as (_ & E0 & _); clear - E0 H1 K1; lia| reflexivity| exfalso; exact (NS1 eq_refl)].
    - eapply (sa_GROW n NA); [apply sa_TAIL| exact Js| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact SPL1| exact RAs| exact RBs| exact HN| cbn [md_n]; clear - K0 K1; lia| exact VA1| exact VA2| exact VB1| exact VB2| exact BV| exact BF].
    all: match goal with |- ?g => idtac "J1-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@L11007909341.4  L12530932062.2  L14714961187.3  L1770629485.4   L19050221415.2  L19056427139.186L22606344295.2  L23461302312.182L24982576641.183L26168871548.12 L26479600656.3  L29012665503.186L29465010999.3  L31813109760.2  L3519677831.4   L3519677875.4   L35663928186.7  L39280637297.0  L40155635431.5  L41422232819.4  L44691115017.2  L58641002120.186L58641003121.183L59308630368.3  L59308632045.3  L60098763854.3  L60976047698.7  L67080090232.4  Q18135196125.187Q18136070698.185Q18136087844.188Q34224942935.185Q34421655807.187Q39212284437.188Q58692335428.188Q60511567613.188Q64768105610.188Q9538458057.185 00000=00F00P00X00a01?01H01h02A02k03503X03a03i04604B04W04X04f04g05005P06006;06E06O06f07107B07S07d08508F08W08k09909J09XS1r2na4NARg1KS3dXc3NR1S1X2dA3SXBS1r2na1KS2na4NARgS2ra2sp1X3xs02dA2xs2zs2na4NARgS2na4NARgS2ra2sp1X3xs02dA2xs2zs2na2A03A16S2ra2sp1X3xs02dA2xs2zs2naS1X2sX2nX2pX3xs04padX4ownX2dA2dB1v2BV4PHI0S1X2dB3SXBS2ra2sp1X3xs02dA2xs1r2zs2HR2na4RB10S1r2zs2HRS2dA3NRES2dB1r2HR3NRES1N1r2HR3NR1S1R3HIA1h2sp2lo3TOP1HSS1r2zs2HR2na1KSS2na4NARgS2ra2sp1X3xs02dA2xs2zs2na2A03A16S2ra2sp1X3xs02dA2xs2zs2na2A03A16S2dA3AAL2KAS2dA2A02KNS1R2lo3LOSS2dA2dB1r2na3ABD3HI22PWS1d2D01f2BFS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2na2A0S3xs02xs2zs2naS3xs02dA2xs2zs2naS3xs02xs2zs2na". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC AMS C24H JC TPV UWX D0 BUD BUDF SLO2 A47"] Lemma sa_FOUND : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (r : Z) (zs : list word)
      (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    (md_addr dB = X -> zs = md_limbs dXc) ->
    (md_addr dB <> X -> zs = md_limbs dB) ->
    limbs_val zs = mpd_abs dB ->
    0 <= r <= Z.of_nat (length zs) ->
    lval zs r = limbs_val zs ->
    (1 <= r -> 2 ^ (32 * (r - 1)) <= limbs_val zs) ->
    (md_addr dA = X -> limbs_val (md_limbs dXc) = mpd_abs dA) ->
    v <= 0 ->
    f <= 0 ->
    0 <= sub_abs_PHI dX dA dB ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 r) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              xs3 xs4 xs5 xs6 SB (Z_to_bv 64 (4 * r)) (SHA (md_addr dB)) xs10 xs11 xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e5e4) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX RA RB ZBX ZBR VZ HR LVR HIGH VAX BV BF PHI0.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    (* [comment removed for export] *)
    assert (AF : exists na, (md_addr dA = X -> md_n dXc = na) /\ (md_addr dA <> X -> md_n dA = na) /\ 0 <= na <= 10000 /\ mpd_abs dA < 2 ^ (32 * na)
                 /\ exists pa sa pda, rw_cells asegs mc (md_addr dA) (mpi_cells pa (Z_to_bv 64 sa) na pda) /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dA) 16
                                      /\ 0 < md_addr dA /\ md_addr dA + 16 <= 2^64).
    { destruct (rideS_view dA _ _ _ _ _ _ 0 J0 RA ltac:(clear; lia) ltac:(intros _; clear - NR1; lia)
                  ltac:(intros C; destruct RA as [E|[DBJ B]]; [exfalso; exact (C E)| pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & _ & NRE & _); clear - NRE; lia]))
        as (pa & sa & na & pda & ysA & CEA & OEA & A0 & A16 & AAL & _ & _ & _ & _ & _ & _ & _ & _ & _ & NAX & NAR).
      exists na. destruct RA as [E|[DBJ B]].
      - pose proof (NAX E) as ENa. subst na. split; [intros _; reflexivity|]. split; [intros C; exfalso; exact (C E)|]. split; [exact NR1|].
        split; [rewrite <- (VAX E), <- LEN1; apply limbs_val_bound| dexists pa, sa, pda; split; [exact CEA| split; [exact OEA| split; [exact A0| exact A16]]]].
      - pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & LENE & NRE & _).
        assert (ENX : md_addr dA <> X) by (destruct DBJ as [_ _ _ _ SXB _]; cbn [md_addr] in SXB; clear - SXB; lia).
        pose proof (NAR ENX) as ENa. subst na. split; [intros E; exfalso; exact (ENX E)|]. split; [intros _; reflexivity|]. split; [exact NRE|].
        split; [unfold mpd_abs; rewrite <- LENE; apply limbs_val_bound| dexists pa, sa, pda; split; [exact CEA| split; [exact OEA| split; [exact A0| exact A16]]]]. }
    ddestruct AF as (na & NAX & NAR & NARg & ABD & pa & sa & pda & CEA & OEA & A0 & A16).
    assert (AAL : md_addr dA mod 8 = 0).
    { destruct (rideS_view dA _ _ _ _ _ _ 0 J0 RA ltac:(clear; lia) ltac:(intros _; clear - NR1; lia)
                  ltac:(intros C; destruct RA as [E|[DBJ B]]; [exfalso; exact (C E)| pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & _ & NRE & _); clear - NRE; lia]))
        as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AAL & _). exact AAL. }
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1, CEA.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (RB10 : r <= 10000).
    { destruct RB as [E|[DBJ B]]; [rewrite (ZBX E), LEN1 in HR; clear - HR NR1; lia|].
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & LENE & NRE & _).
      assert (ENX : md_addr dB <> X) by (destruct DBJ as [_ _ _ _ SXB _]; cbn [md_addr] in SXB; clear - SXB; lia).
      rewrite (ZBR ENX), LENE in HR. clear - HR NRE; lia. }
    (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN; [exfalso; clear - KN A0; lia|].
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite land7_mod in KA; clear - KA AAL; lia|].
    zstep. zstep. zstep. shadow_chk OEA (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 na)) with (Z_to_bv 64 na) by (unfold zx16; rewrite !unsigned_lit by (clear - NARg; lia); rewrite Z.mod_small by (clear - NARg; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (clear - NARg HR RB10; lia); swap 1 2.
    - eapply (sa_J1 _ _ _ _ _ _ r na); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact RA| exact RB| clear - HR K; lia| clear - NARg; lia| | exact NAR| | | exact BV| exact BF| exact PHI0].
      + intros E. split; [exact (NAX E)| exact (VAX E)].
      + intros E. cbn [md_limbs md_n]. rewrite <- (ZBX E). split; [rewrite LVR; exact VZ| rewrite <- LEN1, <- (ZBX E); clear - HR; lia].
      + intros NE. rewrite <- (ZBR NE). split; [rewrite LVR; exact VZ|].
        destruct RB as [E|[DBJ B]]; [exfalso; exact (NE E)|].
        pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & LENE & _). rewrite <- LENE, <- (ZBR NE). clear - HR; lia.
    - (* [comment removed for export] *)
      eapply sa_ret with (r := MBEDTLS_ERR_MPI_NEGATIVE_VALUE); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| right; right; split; [reflexivity|]| clear - BV PHI0; lia| unfold sub_abs_FR, calls_FR, fr_charge; clear - BF D0; lia].
      pose proof (HIGH ltac:(clear - K NARg; lia)) as HI2. rewrite VZ in HI2.
      assert (PW : 2 ^ (32 * na) <= 2 ^ (32 * (r - 1))) by (apply Z.pow_le_mono_r; clear - K NARg; lia).
      clear - ABD HI2 PW. lia.
    all: match goal with |- ?g => idtac "FOUND-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L10642089944.1L59315053158.1000004007S2zsS1C". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC AMS C24H JC TPV UWX D0 BUD BUDF SLO2 A47"] Lemma sa_ZERO : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (zs : list word)
      (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    (md_addr dB = X -> zs = md_limbs dXc) ->
    (md_addr dB <> X -> zs = md_limbs dB) ->
    limbs_val zs = mpd_abs dB ->
    limbs_val zs = 0 ->
    (md_addr dA = X -> limbs_val (md_limbs dXc) = mpd_abs dA) ->
    v <= 0 ->
    f <= 0 ->
    0 <= sub_abs_PHI dX dA dB ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 0) xa0 xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (md_addr dA))
              xs3 xs4 xs5 xs6 SB (Z_to_bv 64 0) (SHA (md_addr dB)) xs10 xs11 xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e5e4) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX RA RB ZBX ZBR VZ Z0 VAX BV BF PHI0.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply (sa_FOUND v f hc LBc mc dXc 0 zs); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact RA| exact RB| exact ZBX| exact ZBR| exact VZ| clear; lia
                                               | rewrite lval_0, Z0; reflexivity| intros C; exfalso; clear - C; lia| exact VAX| exact BV| exact BF| exact PHI0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@L10085909942.2  L10087490804.168L11001440307.160L11001441077.158L11014202208.4  L17262411808.17 L21041645149.3  L21631969095.2  L33640162935.4  L36692919369.2  L40221208850.1  L41418085197.2  L42608597650.1  L42975777126.4  L45942564770.161L45942685932.164L46801668076.2  L53519021073.158L54427748396.2  L55661584342.152L55661584342.154L55715311926.161L58177949655.158L58667209005.3  L59279886471.160L59279887233.158L59308628179.5  L59309021520.4  L59309021649.7  L59309021782.3  L59310648043.7  L66151410442.5  L67418292019.3  Q12761110700.165Q1959514726.158 Q21750569356.159Q21754796437.158Q26295627581.165Q31703824854.162Q36646300200.159Q37759476334.159Q4465582534.167 Q49433500843.159Q50458135125.165Q5179132400.162 Q5179290953.165 Q53100800868.158Q57811535654.165Q8943495454.162 Q9135435409.167 00000600S01Q02S02`03=03E03K03Y03`03c03d03g04505306106806U06\07K08A08^09;09C0:<0;90;I0;V0;m0<90<S0<`0<j0=D0=V0=h0>:0>I0>b0?40?50?J0@50@G0@\0A10AC0A\0Ak0BDS2pb1rS2ra2sp1X3xs02dB1k2zs2pb1r2HkS2ra2sp1X3xs02dB1k2zs2pb3NBv1r2Hk4LENZ2B02HR2X03SPR2EB4PB0'2S1S2ra2sp1X3xs02dB1k2zs2pb3NBv1r2Hk4LENZ2B02HR2X03SPR2EB3HR14PB0'2S1S3NBv1r2HR2K0S2pb1r2r13PBL1q2r01H2H02q02H4S1k1r2HkS2zs1rS3NBv1r2HR3HR1S1r3HR1S1rSS1rS3NBv1r2HR3HR1S2ra2sp1X3xs02dB1k2zs2pb3NBv1r2Hk4LENZ2B02HR2X03SPR2EB4PB0'2S1S2ra2sp1X3xs02dB1k2zs2pb3NBv1r2Hk4LENZ2B02HR2X03SPR2EB4PB0'2S1S2zs2ZAS2ra2sp1X3xs02dB1k2zs2pb1r2HkS1r3HR1S2ra2sp1X3xs02dB2zs2pb3NBv1r2Hk2B02HR2X03SPR2EBS2ra2sp1X3xs02dB1k2zs2pb3NBv1r2Hk4NB102B02HR2X03SPR2EBS2ra2sp1X3xs02dB1k2zs2pb1r2HkS2ra2sp1X3xs02dB1k2zs2pb1r2HkS1w2WR1HS2ra2sp1X3xs02dB1k2zs2pb3NBv1r2Hk4LENZ2B02HR2X03SPR2EB2S1S2ra2sp1X3xs02dB1k2zs2pb3NBv1r2Hk4LENZ2B02HR2X03SPR2EB3HR12S1S3NBv1r2Hk2HR2K0S2pb1r3HR12S1S2pb1r3HR11H2H02S24PB0'S2pb4PB0'2S3S2zs3NBv1r4LENZ2HR3HR13NTHS3NBv1r2HR2K0S3NBv1r2HRS3xs01k2zs2pb1r2Hk4PB0'2S1S3xs02dB1k2zs1r2HkS3xs02dB1k2zs1r2HkS3xs02dB1k2zs1r2HkS3xs01k2zs1r2HkS3xs01k2zs2pb3NBv1r2Hk2HRS3xs02dB1k2zs1r2HkFS3xs01k2zs2pb1r2Hk2S1S2ra2sp1X3xs02dB1k2zs2pb1r2Hk2B03BAL2X03SPRS3xs01k2zs2pb1r2HkS3xs01k2zs2pb1r2Hk2S1S3xs01k2zs2pb1r2Hk2S1S3xs02dB1k2zs1r2HkS3xs01k2zs2pb3NBv1r2Hk2HRS3xs01k2zs1r2HkS3xs01k2zs2pb3NBv1r2Hk2HR". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC AMS C24H JC TPV UWX D0 BUD BUDF SLO2 A47"] Lemma sa_SCANLOOP : forall (k : nat) (zs : list word) (pb NBv sbv : Z) (pdb : word) (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (r : Z)
      (xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs1 xs3 xs4 xs5 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    r <= Z.of_nat k ->
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    (md_addr dB = X -> zs = md_limbs dXc) ->
    (md_addr dB <> X -> zs = md_limbs dB) ->
    limbs_val zs = mpd_abs dB ->
    bytes_at asegs mc pb (u32s zs) ->
    Z.of_nat (length zs) = NBv ->
    NBv <= 10000 ->
    (1 <= NBv -> 0 < pb) ->
    (1 <= NBv -> aobj asegs AL (hcs asegs R HIA hc) mc pb (4 * NBv)) ->
    pb mod 4 = 0 ->
    rw_cells asegs mc (md_addr dB) (mpi_cells pb (Z_to_bv 64 sbv) NBv pdb) ->
    aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dB) 16 ->
    0 < md_addr dB ->
    md_addr dB mod 8 = 0 ->
    0 <= r <= NBv ->
    lval zs r = limbs_val zs ->
    (md_addr dA = X -> limbs_val (md_limbs dXc) = mpd_abs dA) ->
    v <= 0 ->
    f <= 0 ->
    0 <= sub_abs_PHI dX dA dB ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 r) (Z_to_bv 64 (4 * r)) (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 (md_addr dA)) xs3 xs4 xs5 xs6 SB xs8 (SHA (md_addr dB)) xs10 xs11 xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e568) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 NGX RA RB ZBX ZBR VZ EBY LENZ NB10 PB0 OEL PBL CEB OEB B0 BAL HR ZA VAX BV BF PHI0;
      jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR;
      basic_factsA hc;
      pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1;
      pose proof (u32ro_bound _ _ _ _ EBY) as EB;
      pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV;
      pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM;
      pose proof CEB as CEB'; unfold mpi_cells in CEB';
      (* [comment removed for export] *)
      zstep; zstep; zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - HR NB10; lia).
    (* [comment removed for export] *)
    1, 3: assert (E0 : r = 0) by (clear - K0 HR NB10; lia); subst r; rewrite lval_0 in ZA;
          eapply (sa_ZERO v f hc LBc mc dXc zs); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact RA| exact RB| exact ZBX| exact ZBR| exact VZ| clear - ZA; lia| exact VAX| exact BV| exact BF| exact PHI0].
    1: exfalso; clear - K0 HR Hk; lia.
    (* [comment removed for export] *)
    assert (HR1 : 1 <= r) by (clear - K0 HR; lia).
    pose proof (OEL ltac:(clear - HR HR1; lia)) as OEL'. pose proof (PB0 ltac:(clear - HR HR1; lia)) as PB0'.
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases S1; zify_cond S1; [exfalso; clear - S1 HR1; lia|].
    zstep. zstep. zstep. zstep. if_cases S2; zify_cond S2; [exfalso; clear - S2 HR1 PB0'; chk_ltb S2; lia|].
    zstep. if_cases S3; zify_cond S3; [exfalso; clear - S3 PB0'; lia|].
    zstep. zstep. zstep. zstep. if_cases S4; zify_cond S4; [exfalso; apply S4; rewrite land3_mod; clear - PBL; Z.div_mod_to_equations; lia|].
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (pb + 4 * r + -4)) with (Z_to_bv 64 (pb + 4 * (r - 1))) by (f_equal; clear; lia).
    zstep. zstep. shadow_chk OEL' (pb + 4 * (r - 1)) 4.
    (* [comment removed for export] *)
    destruct (nth_error zs (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR HR1; lia].
    pose proof (u32ro_read asegs mc pb zs (r - 1) w _ EBY NTH ltac:(clear - HR1; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_w32_nth zs (Z.to_nat (r - 1)) w NTH) as LW. pose proof (w32_range w) as WR.
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1; rewrite bv_unsigned_sx32 in K1; fold (w32 w) in K1.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ WR)) in K1.
      assert (ZA' : lval zs (r - 1) = limbs_val zs).
      { rewrite <- ZA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ zs (r - 1)) by (clear - HR1; lia). rewrite LW, K1. clear; lia. }
      replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 (r - 1)) by (f_equal; clear; lia).
      replace (Z_to_bv 64 (4 * r + -4)) with (Z_to_bv 64 (4 * (r - 1))) by (f_equal; clear; lia).
      eapply (IH zs pb NBv sbv pdb _ _ _ _ _ _ (r - 1)); try eassumption; [clear - Hk; lia| clear - HR HR1; lia].
    - (* [comment removed for export] *)
      zstep.
      eapply (sa_FOUND _ _ _ _ _ _ r zs); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact RA| exact RB| exact ZBX| exact ZBR| exact VZ| rewrite LENZ; clear - HR; lia| exact ZA| | exact VAX| exact BV| exact BF| exact PHI0].
      intros _. rewrite <- ZA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ zs (r - 1)) by (clear - HR1; lia). rewrite LW.
      pose proof (lval_range zs (r - 1) ltac:(clear - HR1; lia)) as [G _].
      assert (W1 : 1 <= w32 w) by (assert (w32 w <> 0) by (intros E; apply K1; apply (proj2 (sxz_zero_iff _ WR)); exact E); clear - H WR; lia).
      assert (P0' : 0 < 2 ^ (32 * (r - 1))) by (apply Z.pow_pos_nonneg; clear - HR1; lia). clear - G W1 P0'. nia.
    all: match goal with |- ?g => idtac "SCANLOOP-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L13964994716.4  L15657432408.4  L26479600656.3  L39172636981.0  L43589977339.4  L45826653953.4  L48359981522.2  L48364306413.156L51668879259.3  L51916100306.2  L66990418839.156L67890589356.1  Q42658418930.158Q64808403539.15800000=00E00O00P00Q00^00h01K01X01b02C02H02W02fS3NBv2zs4NB10S3NBv2zsS1X2dB3SXBSFS3NBv2zs4NB10S3NBv4NB10S2ra2sp1X3xs02dB3dXc3NBv2pb2zs4NB10S3NBv2zs4LENZS3NBv4NB10S2ra2sp1X3xs02dB3dXc2pb2zs2B03B16S3NBvS3xs02dB3dXc2zsS3xs02dB3dXc2zs". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC AMS C24H JC TPV UWX D0 BUD BUDF SLO2 A47"] Lemma sa_SCAN : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs1 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    XJ0 v f hc LBc mc dXc ->
    md_n dXc <= NZB ->
    rideS dA hc LBc mc dXc ->
    rideS dB hc LBc mc dXc ->
    (md_addr dA = X -> limbs_val (md_limbs dXc) = mpd_abs dA) ->
    (md_addr dB = X -> limbs_val (md_limbs dXc) = mpd_abs dB) ->
    v <= 0 ->
    f <= 0 ->
    0 <= sub_abs_PHI dX dA dB ->
    aevtA asegs (KF asegs R HIA hc mo) SA_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (md_addr dB + 10)) xa1 (Z_to_bv 64 (md_addr dB)) xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 (md_addr dA)) xs3 xs4 xs5 xs6 SB xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x9e558) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX RA RB VAX VBX BV BF PHI0.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    (* [comment removed for export] *)
    assert (BFX : exists (NBv pb sb : Z) (pdb : word) (zs : list word),
                   rw_cells asegs mc (md_addr dB) (mpi_cells pb (Z_to_bv 64 sb) NBv pdb) /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dB) 16
                   /\ 0 < md_addr dB /\ md_addr dB + 16 <= 2^64 /\ md_addr dB mod 8 = 0 /\ bytes_at asegs mc pb (u32s zs) /\ Z.of_nat (length zs) = NBv /\ 0 <= NBv <= 10000
                   /\ (1 <= NBv -> 0 < pb) /\ (1 <= NBv -> aobj asegs AL (hcs asegs R HIA hc) mc pb (4 * NBv)) /\ pb mod 4 = 0
                   /\ (md_addr dB = X -> zs = md_limbs dXc) /\ (md_addr dB <> X -> zs = md_limbs dB)).
    { destruct RB as [E|[DBJ B]].
      - destruct (rideS_view dB _ _ _ _ _ _ (md_n dXc) J0 (or_introl E) (proj1 NR1) ltac:(intros _; apply Z.le_refl) ltac:(intros C; exfalso; exact (C E)))
          as (pb & sb & nb & pdb & zs & CEB & OEB & B0 & B16 & BAL & ZB & _ & _ & PBL & PB0 & _ & OBL & ZBX & ZBR & NBX & _).
        pose proof (ZBX E) as EZ. pose proof (NBX E) as ENb. subst zs nb. dexists (md_n dXc), pb, sb, pdb, (md_limbs dXc).
        split; [exact CEB|]. split; [exact OEB|]. split; [exact B0|]. split; [exact B16|]. split; [exact BAL|]. split; [exact ZB|]. split; [exact LEN1|]. split; [exact NR1|].
        split; [exact PB0|]. split; [exact OBL|]. split; [exact PBL|]. split; [intros _; reflexivity| intros C; exfalso; exact (C E)].
      - pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & LENE & NRE & _).
        assert (ENX : md_addr dB <> X) by (destruct DBJ as [_ _ _ _ SXB _]; cbn [md_addr] in SXB; clear - SXB; lia).
        destruct (rideS_view dB _ _ _ _ _ _ (md_n dB) J0 (or_intror (conj DBJ B)) (proj1 NRE) ltac:(intros C; exfalso; exact (ENX C)) ltac:(intros _; apply Z.le_refl))
          as (pb & sb & nb & pdb & zs & CEB & OEB & B0 & B16 & BAL & ZB & _ & _ & PBL & PB0 & _ & OBL & ZBX & ZBR & _ & NBR).
        pose proof (ZBR ENX) as EZ. pose proof (NBR ENX) as ENb. subst zs nb. dexists (md_n dB), pb, sb, pdb, (md_limbs dB).
        split; [exact CEB|]. split; [exact OEB|]. split; [exact B0|]. split; [exact B16|]. split; [exact BAL|]. split; [exact ZB|]. split; [exact LENE|]. split; [exact NRE|].
        split; [exact PB0|]. split; [exact OBL|]. split; [exact PBL|]. split; [intros C; exfalso; exact (ENX C)| intros _; reflexivity]. }
    ddestruct BFX as (NBv & pb & sb & pdb & zs & CEB & OEB & B0 & B16 & BAL & ZB & LENZ & NB10 & PB0 & OBL & PBL & ZBX & ZBR).
    assert (VZ : limbs_val zs = mpd_abs dB) by (destruct (Z.eq_dec (md_addr dB) X) as [E|NE]; [rewrite (ZBX E); exact (VBX E)| rewrite (ZBR NE); reflexivity]).
    pose proof CEB as CEB'; unfold mpi_cells in CEB'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 NBv)) with (Z_to_bv 64 NBv) by (unfold zx16; rewrite !unsigned_lit by (clear - NB10; lia); rewrite Z.mod_small by (clear - NB10; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    replace (Z_to_bv 64 (NBv * 4)) with (Z_to_bv 64 (4 * NBv)) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply (sa_SCANLOOP (Z.to_nat NBv) zs pb NBv sb pdb _ _ _ _ _ _ NBv); try eassumption;
      first [ clear - NB10 LENZ; lia | unfold lval; rewrite firstn_all2 by (clear - LENZ; lia); reflexivity ].
    all: match goal with |- ?g => idtac "SCAN-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579668.400000=S1X2Ea3SXE2H5". (* [comment removed for export] *)
  #[using="IMG"] Lemma mk_JBd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PdE,$7.Pm1,P,(3.&40.)(5.(3.&8.))P,(<.$4;.VR,VLF,Vm,VLB,(=.&40.Vsp,)R2.)P,(14.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.Vlo,(=.&40.Vsp,))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.R4.)+10.)P,P,(10.$11.(12.R5.)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.R6.)(1<.+4.(1=.R6.)))P,(21.(22.(23.VX,+10.)(19.R6.))(22.(23.(19.R6.)+10.)VX,))P,P,(10.$11.(12.R7.)$13.)P,Pi,$8.P,(2?.(22.=R1.)(30.R1.(1<.+4.(1=.R9.))))(10.$31.(32.$4;.(33.(23.(1;.R:.)R2.)))$34.)(10.$31.(35.(1;.R9.)(1<.+4.(1=.R9.)))$34.)P,(6<.$4;.(2=.VR,)(2>.$4;.VR,VHIA,Vh,)R7.(19.R8.)+10.)P,P,(10.$11.(12.R9.)$13.)(6<.$4;.(2=.VR,)(2>.$4;.VR,VHIA,Vh,)R9.(1;.R:.)(1<.+4.(1=.R:.)))P,(9.$4;.VR,VHIA,Vh,VLB,VLF,R9.)P,(<.$4;.VR,VLF,R:.VLB,(=.&40.Vsp,)R;.)(2?.(82.$4;.VR,VHIA,VLB,VLF,Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R<.)(83.$4;.VR,VHIA,VLF,Vsp,R<.Vh,VLB,R;.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros dE m1; intros ME OE CRE CREL SXE IE OEs OEl HM1 ME1. dpose OE as (OE1 & OE2 & OE3 & OE4 & OE5).
    destruct dE as [Ea sE nE pE zs0 padE ownE].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    split.
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
      intros EO RO hc LBc mc HMc. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IE EO RO)].
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + exact ME1.
      + exact OE2.
      + intros EOX EN. destruct OE3 as [C|[C|[C|C]]]; [exfalso; injection C; intros; clear - SXE H5; lia| exfalso; exact (C EOX)| exfalso; exact (EN C)| exact C].
      + exact OEs.
      + intros EN. pose proof (opnd_viewA _ _ _ _ _ _ _ ME1) as [(_ & _ & _ & _ & _ & OW) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OW.
        destruct ownE; [exfalso; exact (EN eq_refl)| |].
        * ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HM1| exact EIN].
        * exact (OEl eq_refl).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01i0@D29135648175.163D29135648175.164D35881667587.163D35881667587.164K14554379081.163K14554379081.164K68206801384.163K68206801384.164L11146937588.151L11378246744.151L14550820926.2  L14661052148.151L17168748916.151L17305750384.4  L19431261630.4  L19945316590.2  L20671329140.151L23179669492.151L24982576641.171L26696925684.151L29206723700.150L29683898328.150L33244072664.151L35653441506.7  L36822076888.151L3842217688.151 L38996969702.159L39994890072.151L40384348376.151L40834179097.172L41243174772.151L4240068184.151 L42479632545.4  L43059266230.157L43556112984.151L43671330526.3  L43962352600.151L44778233891.3  L47256598004.151L5119243892.151 L51314995137.6  L53284291188.151L57609403830.1  L58641002120.174L58641003121.171L59288287602.183L59294568692.151L59308630368.3  L59308632045.3  L59314955108.4  L59865231950.1  L60098763854.3  L6482734895.4   L66990877462.170L677792600.151  L68211501598.2  L7420217816.151 L7818068312.151 L8303040740.2   L8633419892.151 Q14340732701.181Q15643324129.159Q18365925601.160Q18378753154.160Q18696178937.181Q20454051255.184Q21879645826.160Q23625086249.181Q24330906857.181Q24389563138.160Q25513505925.162Q25513505925.163Q25664655150.181Q27584944865.160Q27907200258.160Q29505479905.160Q30415036802.160Q31226806957.181Q31271525473.160Q31577534880.181Q32655500769.160Q33918256002.160Q35016597915.181Q36425882626.160Q3830427394.160 Q39212284437.184Q39939554818.160Q41152393185.160Q42656338381.184Q42658486014.181Q44648843873.160Q4533518817.160 Q4744161290.181 Q49698585326.161Q49698585326.162Q50301746444.181Q51235796833.160Q52101170785.160Q52936356637.181Q53490882541.181Q53971922166.181Q54127189757.181Q54485784450.160Q55637628457.181Q59256763233.160Q59843137889.160Q60511257090.160Q60511567613.184Q60511891042.162Q60511891042.163Q61800111021.181Q61996794748.181Q64253583609.181Q65201207496.184Q66522067074.160Q67528989526.163Q67528989526.164Q68587509587.160Q68587509587.161Q9538458057.181 Q9843367298.159 00001;02l03b05>06:07Y08U0:40:O0:j0:k0;F0;a0;m0<;0<B0<]0=80=S0=n0>I0>d0??0?W0@20@M0@h0AC0A^0B;0BV0C10C=0D50DP0DX0E30E;0EV0F10FE0F`0Fd0GB0G`0HK0Hf0I10I;0IH0IL0IV0Id0JB0J]0J^0K90KT0K]0L80LK0Ld0M=0M[0N50NK0Ni0OC0OD0Ob0PM0Q[0Q\0R50RS0Rl0SJ0Se0T>0TQ0Tj0UH0Uc0VA0V_0W20WP0Wi0X<0XO0Xh0YA0YB0Yf0ZJ0ZK0Zd0[=0[>0[?0[Z0\40\R0\S0\l0]E0]c0^60^f0`90`:0`;0`<0`O0`m0a]0c00cI0cb0d50dSS1R2ra2sp1X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R3HIA1h2ra2sp1X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDFS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dA2lo1HS2sp2dA2lo3OA4S2sp2loS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dB2lo1HS1R2ra2sp1X3xs02dA2dB2lo4SLO25NEEDR2X03SPR2A02B03ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1X2dA1DS2ra2sp1X3xs02dA2dB3ABD3BBDS1X2dB1DS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R2sp2lo4SLO25NEEDRS2ra2sp1X3xs02dA2dB3ABD3BBDS2spS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X2nX3xs02dA2dB2X03SPR2A02B03ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2dB3BAL2KAS2dB2B02KNS1X2dA1D1E2dBS2spS1R2lo3LOSS2sp2dB2lo3OB4S2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDFS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2dA4NRA'S2ra2sp1X3xs02dA2dB3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS3xs02dA2dB2B03ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2ra2sp3xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS3xs02dA2dB3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFFS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS3xs02dA2dB3ABD3BBDS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FFFS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp3xs02dA2dB3ABD3BBD2HBS2sp3xs02dA2dB3ABD3BBD2HBS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBD". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC AMS C24H JC TPV UWX D0 BUD BUDF SLO2 A47"] Lemma sa_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(:.$4;.VR,VHIA,Vh,Vmo,)P,(<.$4;.VR,VLF,Vm,VLB,(=.&40.Vsp,)VdA,)P,(<.$4;.VR,VLF,Vm,VLB,(=.&40.Vsp,)VdB,)P,(>.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)P,(>.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,)P,(>.VdA,VdB,)P,(14.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,Vlo,(=.&40.Vsp,))P,(14.(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,Vlo,(=.&40.Vsp,))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.VdA,)+10.)P,P,(10.$11.(12.VdA,)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.VdA,)(1<.+4.(1=.VdA,)))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.VdB,)+10.)P,P,(10.$11.(12.VdB,)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.VdB,)(1<.+4.(1=.VdB,)))P,(24.$4;.Vm,Vlo,(=.&40.Vsp,))P,(2;.$4;.Vm,)P,(2<.$4;.(2=.VR,)(2>.$4;.VR,VHIA,Vh,)Vm,(4<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(2<.$4;.(2=.VR,)(2>.$4;.VR,VHIA,Vh,)Vm,VdA,)P,(2<.$4;.(2=.VR,)(2>.$4;.VR,VHIA,Vh,)Vm,VdB,)P,P,(10.$11.(12.VdA,)$13.)P,Pi,$8.P,(2?.(22.=R1.)(30.R1.(1<.+4.(1=.VdA,))))(10.$31.(32.$4;.(33.(23.(1;.VdA,)R2.)))$34.)(10.$31.(35.(1;.VdA,)(1<.+4.(1=.VdA,)))$34.)P,P,(10.$11.(12.VdB,)$13.)P,Pi,$8.P,(2?.(22.=R1.)(30.R1.(1<.+4.(1=.VdB,))))(10.$31.(32.$4;.(33.(23.(1;.VdB,)R2.)))$34.)(10.$31.(35.(1;.VdB,)(1<.+4.(1=.VdB,)))$34.)(43.$4;.$58.(46.(47.(48.Vra,Vsp,Vgp,Vtp,R1?.R1>.R1=.Vs0,Vs1,(29.&40.VX,)(29.&40.(19.VdA,))(29.&40.(19.VdB,))R1<.R1;.R1:.R19.R18.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(29.&40.$84.)Vfc,(49.(3.&40.))Vm,(4:.$4;.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK MA0 MB0 SXA SXB SAB OA OB CRA CRAL CRB CRBL ST MI OXA OAA OBA IA2 IB2. unfold A_MPI_SUB_ABS.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (opnd_viewA _ _ _ _ _ _ _ MA0) as [(CA0 & AAL & A0 & LENA & NRA' & OWNA) SGA]. pose proof (opnd_viewA _ _ _ _ _ _ _ MB0) as [(CB0 & BAL & B0 & LENB & NRB & OWNB) SGB]. unfold MPI_MAX_LIMBS in NRA', NRB.
    pose proof (rw_cells_bound _ _ _ _ CA0) as ABD. pose proof (rw_cells_bound _ _ _ _ CB0) as BBD. unfold mpi_cells in ABD, BBD. cbn [cells_size csize Nat.add] in ABD, BBD.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. pose proof OBA as [OBs OBl]. cbn [md_addr] in OX.
    pose proof SXA as SXA0. unfold mpd_sep in SXA, SXB, SAB. cbn [md_addr] in SXA, SXB, SAB.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 128%nat ST.
    (* [comment removed for export] *)
    do 14 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 24 ?jk :: _) =>
      change (rw_cells asegs m1 (bv_unsigned sp + -128) ([CB 24 jk] ++ SA_FRAME_A)) in FR end.
    apply rw_cells_app in FR. destruct FR as [SLOT FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -128 + Z.of_nat 24) with (bv_unsigned sp - 104) in FR by (clear; lia).
    lazymatch type of SLOT with rw_cells _ _ _ [CB 24 ?jk] => set (slot0 := jk) in SLOT end.
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp - 104)).
    { eapply stk_merge; [exact ST| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 24 slot0])) by (cbn; clear; lia).
      eapply stk_of_rw_cells. exact SLOT. }
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    (* [comment removed for export] *)
    assert (MA1 : opnd_atA asegs R LF m1 LB (bv_unsigned sp) dA).
    { eapply opnd_atA_munch_any; [exact MA0| exact MU| exact WM| cbn; split; [clear - OA4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OA5 ON); clear - H; lia| exact I]. }
    assert (MB1 : opnd_atA asegs R LF m1 LB (bv_unsigned sp) dB).
    { eapply opnd_atA_munch_any; [exact MB0| exact MU| exact WM| cbn; split; [clear - OB4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OB5 ON); clear - H; lia| exact I]. }
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    assert (OAl1 : md_own dA = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dA) (4 * md_n dA)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OAl E)]).
    assert (OBl1 : md_own dB = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dB) (4 * md_n dB)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OBl E)]).
    (* [comment removed for export] *)
    assert (IDA : md_addr dA = X -> dA = dX) by (intros E; destruct SXA as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    assert (IDB : md_addr dB = X -> dB = dX) by (intros E; destruct SXB as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    assert (JBA : md_addr dA <> X -> JBE dA /\ BJE dA h LB m1 dX).
    { intros NE. eapply mk_JBd; try eassumption.
      all: destruct SXA as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| clear - D; lia]. }
    assert (JBB : md_addr dB <> X -> JBE dB /\ BJE dB h LB m1 dX).
    { intros NE. eapply mk_JBd; try eassumption.
      all: destruct SXB as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| clear - D; lia]. }
    assert (RA : rideS dA h LB m1 dX) by (destruct (Z.eq_dec (md_addr dA) X) as [E|NE]; [left; exact E| right; exact (JBA NE)]).
    assert (RB : rideS dB h LB m1 dX) by (destruct (Z.eq_dec (md_addr dB) X) as [E|NE]; [left; exact E| right; exact (JBB NE)]).
    assert (PHI0 : 0 <= sub_abs_PHI dX dA dB) by (unfold sub_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA'; lia).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN; [exfalso; clear - KN B0; lia|].
    zstep. zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite land7_mod in KA; clear - KA BAL; lia|].
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OBs (md_addr dB + 10) 2.
    eapply sa_SCAN; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold sub_abs_nz in *; lia)]| exact RA| exact RB| | | apply Z.le_refl| apply Z.le_refl| exact PHI0].
    - intros E. rewrite (IDA E). reflexivity.
    - intros E. rewrite (IDB E). reflexivity.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MAIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WS.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L23460287817.0L49264482736.500000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Lemma A_mpi_sub_abs_spec_oz_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PR,$85.PHIA,(86.$4;.R1.)P,(87.(2=.R2.))P,(88.$4;.R3.R2.$89.)P,(10.$8.(8:.R4.)$8;.)P,(10.$8.(8<.R5.)$8=.)P,(10.$8.(8>.R6.)$8?.)P,(22.=(27.R7.))P,Ph,(0.$4;.R8.R7.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$4;.R<.R;.R4.R3.R2.R1.)(90.$8.(91.(66.$8.$8.)$8.(92.$8.$8.)R4.))P,(2?.(22.(93.(16.R9.))(94.(16.R9.)))(22.(95.(16.R9.))(96.(16.R9.))))P,Pa,$8.P,(10.$31.(32.$4;.(33.R1.))$34.)P,(2?.(22.=R2.)(30.R2.(36.+2.+40.)))(2?.(22.(93.(16.R=.))R3.)(30.R3.(96.(16.R=.))))(97.$4;.R;.R:.$84.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMC AMS NEEDR HND DIMG ROIMG. unfold mpi_sub_abs_stmtA_oz_c.
  intros until d. intros HH HK MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA2 IB2 A47s BUD UW UWX UWA UWB BUDF C24H -> -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 104 (SA_FRAME_A ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  assert (A47 : md_own dA <> LNull -> md_p dA + 4 * md_n dA + 8 <= 2^47).
  { intros NN. pose proof (opnd_viewA _ _ _ _ _ _ _ MA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dA) eqn:EO; [exfalso; apply NN; reflexivity| | exact (A47s eq_refl)].
    ddestruct OW as (_ & EIN & _). exact (blk_top47 asegs R HIA h LB LF m _ _ HH EIN). }
  eapply sa_main; try eassumption.
  all: try exact (uw_obj_nonneg _ _ _ _ UWX).
  all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_SUB_ABS_c, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "SPEC-LEFT:" g end ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma A_mpi_sub_abs_spec_z_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_sz_c24 ()) "PR,$85.PHIA,(86.$4;.R1.)P,(87.(2=.R2.))P,(88.$4;.R3.R2.$89.)P,(10.$8.(8:.R4.)$8;.)P,(10.$8.(8<.R5.)$8=.)P,(10.$8.(8>.R6.)$8?.)P,(22.=(27.R7.))P,Ph,(0.$4;.R8.R7.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$4;.R<.R;.R4.R3.R2.R1.)(90.$8.(91.(66.$8.$8.)$8.(92.$8.$8.)R4.))P,(2?.(22.(93.(16.R9.))(94.(16.R9.)))(22.(95.(16.R9.))(96.(16.R9.))))P,Pa,$8.P,(10.$31.(32.$4;.(33.R1.))$34.)P,(2?.(22.=R2.)(30.R2.(36.+2.+40.)))(2?.(22.(93.(16.R=.))R3.)(30.R3.(96.(16.R=.))))(98.$4;.R;.R:.$84.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMC AMS NEEDR HND DIMG ROIMG. unfold mpi_sub_abs_stmtA_z_c. intros.
  eapply (A_mpi_sub_abs_spec_oz_c R HIA IMG ZF CAL AMC AMS NEEDR HND DIMG ROIMG); try eassumption.
  all: apply opnd_atA_mpd; assumption.
Qed.
