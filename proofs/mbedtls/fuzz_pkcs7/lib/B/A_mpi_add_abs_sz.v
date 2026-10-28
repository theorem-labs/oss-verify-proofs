(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_add_abs_W P_mpi_add_abs_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_journey A_mpi_core_add A_mpi_copy A_mpi_read_binary_stmt A_mpi_stmtA_sz A_mpi_add_abs_W.
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
Ltac2 gd_tbl_A_mpi_add_abs_sz () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_opnd.opnd_atA"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_abs_W.add_abs_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_abs_W.add_abs_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.add_abs_Rsz"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "WA.AA_FRAME_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.addsub_nz"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "WA.AA_VAL_A"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "WA.AA_POST_A"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.BJA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "WA.aaV1"; "WA.aaF1"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JBA"; "WA.K1A_stmt"; "WA.aaM"; "WA.aaV0"; "WA.aaF0"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "WA.opnd2A"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_ADD_ABS"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"].


Definition mpi_add_abs_stmtA_oz (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(;.O4.R:.R2=.R7.)P,(<.O4.O3.R2=.R;.R2>.(=.&40.R2;.)R7.)P,(>.R:.R9.)P,(>.R;.R9.)P,(>.R;.R:.)P,(?.(10.$11.(12.R=.)$13.))P,(14.R>.R=.R;.(=.&40.R30.))P,(14.R?.R=.R<.(=.&40.R31.))P,(15.(16.O3.)(17.$2.R35.(18.R34.))R=.(19.R?.)+10.)P,P,(10.$11.(12.R10.)$1:.)(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(1;.R11.)(1<.+4.(1=.R11.)))P,(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(19.R10.)+10.)P,P,(10.$11.(12.R11.)$1:.)(15.(16.O3.)(17.$2.R39.(18.R38.))R11.(1;.R12.)(1<.+4.(1=.R12.)))P,(1>.O3.R39.R38.(=.&40.R36.)(1?.O4.O3.O2.R3:.)R14.)P,P,(?.(10.$11.(12.R15.)$20.))(21.(22.(23.(1;.R16.)(1<.+4.(1=.R16.)))R13.)(22.(=.&40.R38.)(1;.R16.)))P,(24.O4.R18.R13.(=.&40.R38.))P,(22.(25.O3.)R14.)P,(22.R15.(26.(26.(=.&40.R3:.)+130.)(27.O3.)))P,(22.(=.&40.R3;.)(1?.O4.O3.O2.R3?.))P,(10.$8.(28.(=.&40.R3<.)+10.)=)P,(10.(3.&40.)R3;.(29.&40.(2:.O3.)))P,(2;.O4.R1>.)P,(10.$8.(28.(=.&40.R40.)+2.)=)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R44.)R20.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R45.)R21.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R46.)R22.R1>.)P,P,(?.(10.$8.(19.R20.)(19.R21.)))P,(10.$11.(12.R21.)$13.)(10.$2?.(30.(1;.R22.)(1<.+4.(1=.R22.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,(22.(23.(36.O4.O3.O2.R4:.)(37.R24.R23.R22.))$38.)P,(39.O4.R27.(25.O3.)(3:.O4.O3.O2.R4;.)(=.&40.R41.)(=.&40.R47.)R21.)P,(3;.O3.(19.R26.)+10.R22.)P,(3;.O3.(19.R26.)+10.R23.)P,(3;.O3.(19.R26.)+10.R24.)P,(22.(23.(3<.O4.O3.O2.R4?.)(3=.R25.))$3>.)P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))(3?.O4.(40.O4.O3.O2.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R53.R52.R51.R2=.(41.R52.R2=.R2<.R2;.)(37.R2=.R2<.R2;.)(3=.R29.)R2:.R2?.R2>.)(42.(43.(44.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(29.&40.O1.)R30.(45.(3.&40.))R2?.(46.O4.))R2>.))")
(* [comment removed for export] *).

Definition mpi_add_abs_stmtA_z (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(;.O4.R:.R2=.R7.)P,(;.O4.R;.R2>.R7.)P,(>.R:.R9.)P,(>.R;.R9.)P,(>.R;.R:.)P,(?.(10.$11.(12.R=.)$13.))P,(14.R>.R=.R;.(=.&40.R30.))P,(14.R?.R=.R<.(=.&40.R31.))P,(15.(16.O3.)(17.$2.R35.(18.R34.))R=.(19.R?.)+10.)P,P,(10.$11.(12.R10.)$1:.)(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(1;.R11.)(1<.+4.(1=.R11.)))P,(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(19.R10.)+10.)P,P,(10.$11.(12.R11.)$1:.)(15.(16.O3.)(17.$2.R39.(18.R38.))R11.(1;.R12.)(1<.+4.(1=.R12.)))P,(1>.O3.R39.R38.(=.&40.R36.)(1?.O4.O3.O2.R3:.)R14.)P,P,(?.(10.$11.(12.R15.)$20.))(21.(22.(23.(1;.R16.)(1<.+4.(1=.R16.)))R13.)(22.(=.&40.R38.)(1;.R16.)))P,(24.O4.R18.R13.(=.&40.R38.))P,(22.(25.O3.)R14.)P,(22.R15.(26.(26.(=.&40.R3:.)+130.)(27.O3.)))P,(22.(=.&40.R3;.)(1?.O4.O3.O2.R3?.))P,(10.$8.(28.(=.&40.R3<.)+10.)=)P,(10.(3.&40.)R3;.(29.&40.(2:.O3.)))P,(2;.O4.R1>.)P,(10.$8.(28.(=.&40.R40.)+2.)=)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R44.)R20.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R45.)R21.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R46.)R22.R1>.)P,P,(?.(10.$8.(19.R20.)(19.R21.)))P,(10.$11.(12.R21.)$13.)(10.$2?.(30.(1;.R22.)(1<.+4.(1=.R22.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,(22.(23.(36.O4.O3.O2.R4:.)(37.R24.R23.R22.))$38.)P,(39.O4.R27.(25.O3.)(3:.O4.O3.O2.R4;.)(=.&40.R41.)(=.&40.R47.)R21.)P,(3;.O3.(19.R26.)+10.R22.)P,(3;.O3.(19.R26.)+10.R23.)P,(3;.O3.(19.R26.)+10.R24.)P,(22.(23.(3<.O4.O3.O2.R4?.)(3=.R25.))$3>.)P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))(3?.O4.(40.O4.O3.O2.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R53.R52.R51.R2=.(41.R52.R2=.R2<.R2;.)(37.R2=.R2<.R2;.)(3=.R29.)R2:.R2?.R2>.)(42.(43.(44.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(29.&40.O1.)R30.(45.(3.&40.))R2?.(46.O4.))R2>.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Section WA.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Hypothesis C24T : c24_transition.   (* [comment removed for export] *)
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_AA.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_AA.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition AA_FRAME_A := aa_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.

  Local Notation NZB := (addsub_nz nX (md_n dA) (md_n dB)).
  Definition AA_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "(40.$47.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(41.VLB,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(3=.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Definition AA_VAL_A := mpd_abs dA + mpd_abs dB.

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A []).

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Ltac ub_clear :=
    repeat match goal with
    | H : ?T |- _ =>
        lazymatch T with
        | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail
        | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
        | _ => match type of T with Prop => clear H end
        end
    end.
  Local Ltac ub_dec K :=
    repeat match type of K with
    | context [Z.ltb ?a ?b] =>
        first [ rewrite (proj2 (Z.ltb_lt a b)) in K by (ub_clear; lia)
              | rewrite (proj2 (Z.ltb_ge a b)) in K by (ub_clear; lia) ]
    | context [Z.leb ?a ?b] =>
        first [ rewrite (proj2 (Z.leb_le a b)) in K by (ub_clear; lia)
              | rewrite (proj2 (Z.leb_gt a b)) in K by (ub_clear; lia) ]
    end; cbn [Z.b2z Z.lxor] in K.
  Local Ltac ub_m0 K :=
    repeat match type of K with
    | context [?a mod 4] => lazymatch a with 0 => fail | _ => replace (a mod 4) with 0 in K by (ub_clear; lia) end
    | context [?a mod 8] => lazymatch a with 0 => fail | _ => replace (a mod 8) with 0 in K by (ub_clear; lia) end
    end; rewrite ?Z.lor_0_l, ?Z.lor_0_r in K.
  Local Ltac ub_solve K :=
    ub_dec K; zify_cond K; rewrite ?Z.land_lor_distr_l, ?aa_land3, ?aa_land7 in K; ub_m0 K;
    repeat (rewrite zb_lxor_ones in K by (ub_clear; lia)); ub_dec K;
    first [ discriminate K | ub_clear; lia | let T := type of K in idtac "UBCHK-LEFT:" T; fail ].
  Local Ltac ubchk :=
    lazymatch goal with
    | |- _ (MS _ _ (if ?c then Z_to_bv 64 648136 else _) _ _ _ _) =>
        let K := fresh "UB" in destruct c eqn:K; [exfalso; ub_solve K| clear K]
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L22163852504.140L22972055896.140L25741856728.140L29428324939.5  L31421052760.140L33232266840.140L34987518552.140L35663928186.7  L40379729343.139L42842486707.140L48958709976.140L52536714200.140L54486063391.140L57408231128.140L60098763854.3  L60968405464.140L6141606276.1   L64900869464.140L68463140952.140Q15643598972.140Q18366170748.140Q18378508831.140Q21879891999.140Q24389844383.140Q27585188988.140Q27906956191.140Q29505727100.140Q30415318815.140Q31271277308.140Q32655747964.140Q33918012703.140Q36425601695.140Q3830178207.140 Q39939305631.140Q41152143740.140Q44648563964.140Q4533800828.140 Q51235551740.140Q52101417212.140Q54486063391.140Q59257011708.140Q59842863100.140Q60511538335.140Q66521824799.140Q9843086111.140 00000700>00E00W00^00e00l01A01H01O01V01]02702>02H02O02S02Z02a02h02o03B03U03h03o04B04I04\04c04j05=05P05c06606=06D06K06R06Y06l07307:07M07`083S2ra2spS2ra2spS2ra2spS1R2lo3LOS3ALO3ACPS2ra2spS2ra2spS2ra2spS1R3HIA1h2sp2lo3TOP1HS2ra2spS2ra2spS2ra2spS2ra2spS1R2ra2sp2lo5NEEDR3SLO3SPRS2ra2spS1R2lo3LOSS2ra2spS2spS2ra2spS2ra2spS2sp2loS2sp2loS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS2sp2loS1R2sp2lo5NEEDR3SLOS2sp2loS1R2sp2lo5NEEDR3SLOS2sp2loS2sp2loS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS2sp2loS2sp2loS2sp2loS2sp2loS2sp2loS1R2sp2lo5NEEDR3SLOS2sp2loS2sp2loS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLO". (* [comment removed for export] *)
  #[using="IMG JC"] Lemma aa_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R22.R21.R20.R1?.R1>.R1=.)P,(22.(1=.R1>.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(21.(32.(10.$8.R1>.=)(32.(10.$8.(4=.R1?.)$4>.)(10.$8.(4?.R1?.)+1.)))(10.$8.R1>.$50.))P,(22.R25.(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(22.R25.(3=.Vd,))(51.$47.(52.$47.VR,VHIA,R25.Vmo,)$53.(43.(44.R20.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1?.R1>.R1=.R1<.R1;.R1:.(29.&40.R21.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)VF,(29.&40.+9>388.)Vfc,(45.(3.&40.))R23.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J NGX HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold AA_FRAME_A, aa_frame in FR1. replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep.
    do 13 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold AA_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [| cbn [md_n]; exact NGX]. split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG JC"] Lemma aa_ret0 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R22.R21.R20.R1?.R1>.R1=.)P,(22.(1=.R1>.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(10.$8.(4=.R1?.)$4>.)P,(10.$8.(4?.R20.)+1.)P,(22.R26.(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(22.R26.(3=.Vd,))(51.$47.(52.$47.VR,VHIA,R26.Vmo,)$53.(43.(44.R22.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(29.&40.+9>384.)Vfc,(45.(3.&40.))R24.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J NGX HV HS BV BF. basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep. eapply aa_ret; [exact J| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| left; split; [reflexivity| split; [exact HV| exact HS]]| exact BV| exact BF].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG JC"] Lemma aa_retm16 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R22.R21.R20.R1?.R1>.R1=.)P,(22.(1=.R1>.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(22.R24.(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(22.R24.(3=.Vd,))(51.$47.(52.$47.VR,VHIA,R24.Vmo,)$53.(43.(44.R20.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)VF,(29.&40.+9>07<.)Vfc,(45.(3.&40.))R22.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J NGX BV BF. basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep. zstep. eapply aa_ret; [exact J| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| right; reflexivity| exact BV| exact BF].
  Qed.
  Hypothesis BUD : havol asegs R HIA h + add_abs_PHI dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + add_abs_FR d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - MPI_ADD_ABS_STACK_A - arl_need_rt R.
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Local Notation SH10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Local Notation SHE E := (Z_to_bv 64 (Z.shiftr E 3 + al_sb AL)).
  Local Notation XJ1 An cnt := (XJA asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A [(An, 4 * cnt)]).
  Local Notation FB0 := (FBA asegs R LB LF dX lo).
  Local Notation XD0 := (XDA asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A).
  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).
  (* [comment removed for export] *)
  Definition aaM : Z := Z.max (md_n dA) (md_n dB).
  Definition aaV0 : Z := grow_PHI (md_n dA).
  Definition aaV1 : Z := grow_PHI (md_n dA) + grow_PHI (aaM + 2).
  Definition aaF0 : Z := calls_FR 2 d.                     (* [comment removed for export] *)
  Definition aaF1 : Z := calls_FR 2 d + calls_FR 2 d.
  Local Ltac xa_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  Definition K1A_stmt (dE : mpd) (j : Z) (vv : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs5,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R18.R17.R16.R15.R14.R13.)P,(22.(1=.R14.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(54.$47.VR,VHIA,VLF,Vsp,O3.R18.R17.R16.R15.)P,(10.$11.(12.R16.)$1:.)P,(22.O2.(1=.R17.))P,(10.$8.(4?.R18.)+1.)P,(10.$8.(55.(56.R19.))O1.)P,(22.R1?.$57.)P,(22.R1?.$58.)(51.$47.(52.$47.VR,VHIA,R1?.Vmo,)$53.(43.(44.R1;.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1:.R19.R18.(29.&40.VX,)(29.&40.(23.VX,+:.))R17.R16.R15.R14.R13.R12.R11.R10.(29.&40.O2.)(29.&40.(23.O2.+1.))(29.&40.(19.O3.))R?.(29.&40.(59.(2=.VR,)))(29.&40.(23.(1<.+4.O2.)+4.))(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(5:.VX,+3.))(29.&40.(23.(5:.(19.O3.)+3.)(59.(2=.VR,))))R>.R=.R<.R;.R:.)VF,(29.&40.+9>120.)Vfc,(45.(3.&40.))R1=.(46.$47.)))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "04b0@C17025492443.269C17025492443.270C17025492443.271C53526081063.272C53526081063.273C53526081063.274D1705053216.297 D1705053216.304 D20257660871.302D21651009785.210D22466435734.275D24976250634.231D24976250634.307D28229479954.302D35106100313.296D35106100313.298D35106100313.303D35110411000.207D35110411000.210D3580721273.210 D3585062616.301 D376593230.275  D50797141399.231D50797141399.232D50797141399.307D52014138856.231D52014138856.232D52014138856.307D59228252318.307D60109446735.275D62155808737.232D62155808737.307D7340709316.275 D939044794.275  K1307012896.269 K1307012896.270 K1307012896.271 K1329197271.272 K1329197271.273 K1329197271.274 K2612272047.271 K2612272047.275 K3345721225.232 K3345721225.307 K3345721225.308 K38856059124.308K46911551239.231K46911551239.232K46911551239.307K46911551239.308K59925691872.271K59925691872.275K7412424035.275 L10307112399.6  L11928294055.230L11928294055.305L12755534717.11 L12755534717.9  L12876274804.4  L1294499141.2   L1342025005.3   L14051382136.11 L14748712526.19 L14751320984.1  L14760987928.8  L15182060769.7  L15477852824.1  L15649680808.1  L16473205958.7  L16473494895.4  L16809010849.0  L1705495428.5   L17585880332.15 L18490995735.210L18826226759.8  L18929185109.35 L19277739793.9  L20257806435.5  L20803911415.2  L2166243551.4   L22479292268.1  L23100341967.219L23100341967.224L23100341967.258L23100341967.291L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.8  L25044269509.2  L25046775673.257L25047280258.244L26063715927.5  L2607826517.4   L26502719108.5  L26950159893.14 L27481632834.8  L27481632834.9  L28231168598.1  L28655862141.3  L29059042772.8  L29211043776.6  L30889444302.10 L31060952619.9  L31325970818.4  L3260869064.15  L3352129893.15  L34412813842.37 L34424803280.3  L34443775772.19 L34444340830.3  L34445885352.35 L34456730698.8  L35298821793.4  L35655538624.7  L35655538630.7  L35663928186.7  L35697213963.5  L35975126990.5  L3667582691.3   L381020265.6    L38235734261.1  L38868673902.3  L38868673902.5  L39172636981.0  L39436426759.7  L40294887048.3  L40386985651.8  L40437308144.3  L40449602357.4  L41389564045.12 L43625157983.1  L43631939593.37 L43878034250.5  L45270628691.35 L46061234176.4  L46160487540.224L46160487540.245L46160487540.292L46380960401.4  L46389908878.16 L46754254770.242L46756382136.219L46917722603.2  L46948640662.37 L47401054516.1  L48154966246.219L48157095910.242L49578233423.224L49578233423.291L49579218529.37 L49807695752.8  L5098421631.4   L5098421631.5   L5261871668.3   L52707865424.1  L547707976.3    L54802045807.163L55715400192.243L5572256557.16  L59308633593.3  L59308925409.163L59308972243.3  L59912711553.4  L59925822865.8  L60098763854.3  L6141606276.1   L61564783896.35 L62018535662.1  L64679905332.163L64811930313.12 L64934269637.2  L65348482612.1  L65351313219.35 L65361700727.37 L65908464690.37 L65908727780.10 L65912630450.19 L65913187379.4  L66661851587.4  L67601363691.1  L7400112281.3   L7429484350.35  L8016725142.2   L9784908726.304 L9951453048.13  O17025492443.269O17025492443.270O17025492443.271O22987107037.271O22987107037.275O32329373691.275O37539299629.269O37539299629.270O37539299629.271O45218884275.271O45218884275.275O47864099224.273O53526081063.272O53526081063.273O53526081063.274O65801484870.274P1307012896.269 P1307012896.270 P1307012896.271 P1329197271.272 P1329197271.273 P1329197271.274 P38856059124.232P38856059124.308P40437264079.269P40437264079.270P40437264079.271P40441743114.273P46402209908.274P7412424035.275 Q12370813529.224Q12370813529.229Q12370813529.269Q12370813529.304Q17205055869.303Q17205141463.228Q17207432298.223Q17207432298.268Q22466435734.275Q24974040330.231Q24974040330.307Q26207421841.228Q26207421841.254Q26207721832.229Q26207721832.255Q26207721832.305Q26207967338.226Q26207967338.268Q26207967338.302Q26209519061.304Q26209835253.252Q31651985788.304Q31653536963.268Q31654082872.228Q31654082872.254Q3667187378.301 Q37321635735.197Q37321635735.293Q37321652361.255Q37323914291.275Q37323914293.179Q37623358517.228Q37623376543.303Q37625261960.223Q37625261960.268Q376593230.275  Q38248387216.275Q39212284437.229Q39212284437.255Q39212284437.305Q42081808994.229Q42081808994.305Q43879899724.275Q43925228937.229Q43925228937.255Q43925228937.305Q52016320488.231Q52016320488.306Q52016320488.307Q5483308162.303 Q5483358760.228 Q5485126037.223 Q5485126037.268 Q5485174314.224 Q5485174314.229 Q5485174314.269 Q5485174314.304 Q5573176188.302 Q6027349519.231 Q6027349519.232 Q6027349519.306 Q6027349519.307 Q60511567613.229Q60511567613.255Q60511567613.305Q60697995187.229Q60697995187.255Q60697995187.305Q6143569392.224 Q6143569392.229 Q6143569392.269 Q6143569392.304 Q62157788641.231Q62157788641.306Q62965564504.230Q62965564504.305Q62965564504.306Q64295054172.299Q64295054172.300Q64295054172.301Q64299361789.208Q64299361789.209Q7891539809.229 Q7891539809.304 Q8880503606.226 Q8880503606.302 Q8882895785.252 Q9538787269.226 Q9538787269.302 Q9540589402.252 00000100200300400500600700800900O01<01f02]03E03F03G03H03I03J03`04H05N06Z07d09@09j0:R0;I0;J0<@0<h0=_0=`0>^0>_0>`0>a0>b0>c0>d0?U0@F0AE0BU0CZ0C[0DS0EL0FP0GQ0HK0IE0IF0IZ0J^0L30L40L50LC0LD0LE0Le0M50M60M70MD0MH0MK0M`0Ma0Mb0Mc0Md0N:0NP0No0OK0OL0OM0O]0Oa0P:0PS0Q20QZ0Qd0R10R20R30R<0Rc0ST0Sd0Se0T90T:0T;0T<0T@0TA0TY0Tj0Tk0UG0UR0UY0UZ0Un0Uo0VE0VF0Vb0Vc0Vn0WI0Wd0X90XK0X\0X]0Xn0Y20Y30Y40Y50YK0YN0Y_0Y`0Ya0Yb0Yc0ZE0ZL0Zk0[30[S0\G0]60]70]80^B0_]0_^0`W0`[0`\0aa0b:0bb0cO0cP0c]0cn0d80d;0dE0e90ef0eg0f20fT0f_0f`0g40g>0gB0h<0h?0i40iL0iU0iV0ih0j:0jR0jS0je0jf0k60k;0k<0ki0l00lX0lY0lZ0l[0l\0l]0l^0l_0l`0la0lb0lc0ld0le0lf0lg0lh0li0lj0lk0ll0lm0ln0lo0m00m10mo0nm0ok11012512612V13613\14K14c15015=15L15j16H16o17<17Y17f18C18[18h19719O19g1:D1:\1:k1;81;U1<M1=<1>61?81@21@a1@n1AF1AS1Ab1BH1Bf1C31CP1Ch1D;1DY1E:1EG1Ed1F<1F]1GG1Gn1HF1HS1H`1Ho1I<1II1IX1J01Jh1KF1Ke1LL1M61MA1M\1N21NB1Nb1O=1OJ1OW1Of1P>1P]1QG1Qa1RF1Rk1Rl1Rm1Rn1Ro1S01SC1Sa1Sn1TF1Tc1Tn1UD1U_FFFFFFFFFS2ra2sp1X3xs02Ea2zs2xsS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4SLEN4DLENS2ra2sp1X3xs02Ea2zs1j2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENFFFFFS2ra2sp1X3xs02Ea2zs2xsS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03SPR2E02An3An02N12P04Fcnt4SLEN4DLENS1R2ra2sp1X3xs02lo4SLO22Ea2zs1j2xs5NEEDR3LOS2X03SPR2E02An3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22Ea2zs2xs5NEEDR3LOS2X03SPR2E02An3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22Ea2zs1j3nXc3pXc2xs5NEEDR3LOS2X03SPR2E02An3An02P04ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo2Ea2zs1j3nXc3pXc2xs3LOS2An4SLEN4DLENS2ra2sp1X3xs02Ea2zs2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stFS1R3HIA2ra2sp1X3xs02lo2Ea2zs1j3nXc3pXc2xs2h22An4TOP24SLEN4DLENFFFFFFS3xs02pE2zs1j3nXc3pXc2xs4LEN12An2N14SLEN4DLEN3SEPS3xs02pE2zs1j3nXc3pXc2xs4LEN12An2N14SLEN4DLEN3SEPS1R2sp1X3xs02lo4SLO22pE2zs1j2xs5NEEDR3FSZ3DSX2HB5Ha_st5Hl_st2AnS1R2sp1X3xs02lo4SLO22pE2zs1j3nXc2xs5NEEDR3FSZ3DSX4LEN12An2N14ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22pE2zs1j3nXc2xs5NEEDR3FSZ3DSX4ZLEN2HB5Ha_st5Hl_stFS1R2sp1X3xs02lo4SLO22pE2zs1j2xs5NEEDR3DSX2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22pE2zs2xs5NEEDR3DSX2An2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22pE2zs1j3nXc2xs5NEEDR3DSX2An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22pE2zs1j3nXc2xs5NEEDR3DSX4ZLEN2HB5Ha_st5Hl_stS1R2sp3xs02lo2zs1j3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo2zs1j3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENFS1R2sp2lo4SLO25NEEDRS2ra2sp1X2nX3xs02dA2dB2Ea2nE2zs1j3nXc2xs3CNT2EM2X03SPR2E02An3An03NM1S2ra2sp1X2nX3xs02dA2dB2Ea2nE2zs1j3nXc3pXc2xs3CNT2EM2X03SPR4LEN12E02An3An02P04ZLEN3ZN1FFS2sp2lo2zq3Hz2FFS2dA2dB2nE1j1v3nXc3CNT2EM2BV3NR1S2sp3nXc3SPR3NR1FFS2sp2lo2Ea2ESS2spS1jS2nE1j3nXc3CNT2An3A47FSFFS2ra2sp1X3xs02Ea2zs2xsS2nE2pE1j3nXc3CNT2An1HS2sp2dA2dB2nE1j3nXc3CNT3SPR3NRES2dA2dB2nE1j1v3nXc3CNT2EM2BVFFS3nXc2xs4LEN12N1S2AnS2ra2sp1X3xs02Ea2zs2xs2AnS2ra2sp1X3xs02Ea2zs2xs2AnS2ra2sp1X3xs02Ea2zs1j3pXc2xs2AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENS1R3HIA2hcS3nXc3pXc3P47FFS3nXc3NR1S2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs3NR12AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs3NR12An4SLEN4DLENS1R3HIA1h2sp3TOPFS1R2sp2lo4SLO25NEEDRFFFS2spFS2Ea2nE1j3nXc3CNT2An3ESAS2nE1j3nXc3CNT2AnFS2dA2dB2nE1j1v3nXc3CNT2EM2BVS1d2D01f2BFS2sp2loFS1R2sp2dA2dB2lo4SLO2FS1R2sp2lo4SLO23NRA3SPRFS1R2sp2dA2dB2lo4SLO23NRM3SPRFS1d2D01f2BFS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HS2nE1j3nXc3CNT3NRES2nE1j3nXc3CNT2N1FS2nE1j3nXc3CNT2AnS2loFFSS1R3nXc3pXc2N12P02PC1HS1XS2sp2lo2nE2pE3EL5FFFFS2sp2dA2dB2nE1j3nXc3CNT3SPR3NRE2N1S2sp2loS2sp2dA2dB2nE1j3nXc3CNT3SPR3NR1S1d1f2BFS2ra2sp1X3xs02Ea2zs2xs2X03X162AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03X162An4SLEN4DLENS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03X162An4ZLENFFS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03SPR2E02An3An02N12P04Fcnt4SLEN4DLEN3A47S1R2ra2sp1X2nX3xs02lo4SLO22Ea2nE2zs1j3nXc2xs3CNT5NEEDR3LOS2X03LEN3ALO3SPR2E02An3An03AnC3NM1FS1R3HIA1h2sp2dA2dB3BUD2nE1j1v3nXc3CNT2EM2BV3SPR2h22N13HV1S2spFS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03SPR2E02An3An02N12P03P474SLEN4DLENS2ra2sp1X3xs02Ea2zs2xs2AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2BF3SPR2h24HFR1FS3nXc2xs4LEN1S2nE1j3nXc3CNT2N1S1X2X03X16S1jS1R3HIA2h2S2ra2sp1X3xs02Ea2zs1j3pXc2xs2X03SPR2E02An3An02P03FalS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4SLEN4DLENFS2An3An02KZS2ra2sp1X3xs02Ea2zs1j3pXc2xs2An2UBS3pXc2KP2P0FS2sp2lo3nXc3pXc4XLScS1R2lo3LOSS2spS1R3HIA1h2sp2dA2dB3BUD2nE1j1v2hc3nXc3CNT2EM2BV3SPR3NR13HV1S1RS2ra2sp1X3xs02Ea2zs1j3pXc2xs2X03SPR2E02An3An04XPAL2P0S2lo2nE1j3nXc3CNT2An3FloS3nXc3NR1FS2sp2dA2dB3SPA3SPRS2sp2dA2dB3SPA3SPRS1R3HIA2sp2dA2dB2h24TOP2FS1R3HIA2sp2h24TOP2FS3nXc3pXc2An3SEPS3nXcFS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2hc2BF3SPR4HFR1S2sp2loS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENFFFFFFFFFFFFFFFFFFFFFFFFFS1R2sp3xs02lo2zs1j3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo2zs1j3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo2zs1j3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENFS2ra2sp1X3xs02Ea2zs2xs2X03XAL2AnS2ra2sp1X3xs02Ea2zs2xs2X03XAL2AnS2ra2sp1X3xs02Ea2zs1j3pXc2xs2X03XAL2AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03XAL2An4ZLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS3xs02zs1j3nXc2xs2An4SLEN4DLENS1X3xs02zs1j2xs2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j2xsS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1R2sp3xs02lo4SLO22zs1j3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENS1R2sp3xs02lo4SLO22zs2xs5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22zs2xs5NEEDR3LOS4SP643ALO3ACPS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs1j2xsS3xs02zs1j3nXc2xs2An2N14Fcnt4SLEN4DLENS3xs02lo2zs1j3nXc2xs4SLEN4DLENS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xs2X02HBS1X3xs02zs1j3nXc2xs2X04ZLEN2HBS2sp3xs02lo2zs1j3nXc2xs4SLEN4DLENS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j2xs2HB5Ha_st5Hl_st2AnS1X3xs02zs1j3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs1j3nXc2xs4ZLENS1R2sp3xs02lo4SLO22zs1j3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENS1X3xs02zs1j2xs2HB5Ha_st5Hl_stS1X3xs02zs2xs2An2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS3xs02zs2xsS3xs02zs1j3nXc2xs4SLEN4DLENS3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xs2X0S1X3xs02zs1j3nXc2xs2X04SLEN4DLENS1X3xs02zs1j3nXc2xs2X04ZLENS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xs2An2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs2xs3X162HB5Ha_stS1X3xs02zs1j3nXc2xs3X164ZLEN2HB5Ha_stS1X3xs02zs1j3nXc2xs3X164ZLEN2HB5Ha_stFFFFFS1X3xs02zs2xs2X02HBS1X3xs02zs1j3nXc2xs2X04ZLEN2HBS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j3nXc2xs4SLEN4DLENS3xs02zs2xsS3xs02zs1j3nXc2xs4ZLENS3xs02zs1j3nXc2xs4SLEN4DLEN". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2"] Lemma aa_G1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "PdE,$7.Pj,$8.Pvv,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs5,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(5;.$47.VR,VHIA,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R1;.)P,(5<.R1<.R1;.R1:.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1:.R19.R18.R17.R16.R15.)P,(22.(1=.R16.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(54.$47.VR,VHIA,VLF,Vsp,R1?.R1:.R19.R18.R17.)P,(32.(33.(1=.R18.)R1?.)(22.R1?.(1=.R20.)))P,(22.(1=.R21.)$5=.)P,(10.$8.(4?.R1:.)+1.)P,(10.$8.(55.(56.R1;.))R21.)P,(22.R21.$5>.)P,(22.R21.$5?.)(51.$47.(52.$47.VR,VHIA,R21.Vmo,)$53.(43.(44.R1=.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1<.R1;.R1:.(29.&40.VX,)(29.&40.(23.VX,+:.))R19.R18.R17.R16.R15.R14.R13.R12.(29.&40.R25.)(29.&40.(23.R25.+1.))(29.&40.(19.R26.))R11.(29.&40.(59.(2=.VR,)))(29.&40.(23.(1<.+4.R25.)+4.))(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(5:.VX,+3.))(29.&40.(23.(5:.(19.R26.)+3.)(59.(2=.VR,))))R10.R?.R>.R=.R<.)VF,(29.&40.+9>0:4.)Vfc,(45.(3.&40.))R1?.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros DBJ K1 J NGX B CNT EM SG1 HVV BV BF. jc_open. unfold K1A_stmt in K1.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC dE DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    destruct dE as [Ea sE nE pE zs padE ownE]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := j) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity.
      all: try (apply c24_of_transition; exact C24T).   (* [comment removed for export] *)
      all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: unfold aaV0, aaF0, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT EM NR1 NR NRE LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp + -104)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT. }
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply aa_retm16; [exact J2| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| |].
      + unfold aaV0, aaM, add_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT EM NRE NR1. lia.
      + unfold aaF0, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace (j * 4) with (4 * j) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An j J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT NRE; lia)) as [J2 F2].
      pose proof (bja_transport _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ J B HP2' MI2 HCS2 HH2 ltac:(intros b Hb; right; exact Hb)) as B2.
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J B. try clear MI1; try clear ST1; try clear STc; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1; try clear CX1; try clear OWN0; try clear OWN1;
      xa_open J2.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
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
        pose proof (bja_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ D2 B2 MU WM) as B5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5.
        eapply K1; [exact J5| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| exact B5| reflexivity| cbn [md_n]; clear; lia| reflexivity| | |].
        * cbn [md_limbs]. rewrite limbs_val_repeat0. rewrite EL in HVV. cbn [limbs_val] in HVV. exact HVV.
        * unfold aaV0, aaV1, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT EM. lia.
        * unfold aaF0, aaF1, calls_FR, fr_charge in *. clear - BF D0. lia.
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
        replace (Init.Nat.min (Z.to_nat nXc) (Z.to_nat j)) with (Z.to_nat nXc) in DST, DLEN by (clear - CNT N1; lia).
        (* [comment removed for export] *)
        zstep. zstep. zstep. ubchk.
        shadow_chk OX1 (X + 10) 2.
        zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_AA) as SPC. unfold A_ASAN_MEMCPY_AA in SPC.
        apply (u8arr_of_rw_cells asegs) in DST.
        (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl [(An, An + 4 * nXc); (lo, bv_unsigned sp + -112)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        acallxA_sp (bv_unsigned sp + -112)
          (eapply SPC with (h := h2) (LB := (An, 4 * j) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * nXc) (lo := lo)
                            (ss := u32s xs);
           rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
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
                 | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo (bv_unsigned sp + -112) |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
        assert (ST3' : stk asegs m3 lo (bv_unsigned sp + -104)).
        { eapply stk_merge; [exact ST3| | clear - SLO2 NEEDR LOSP; lia].
          replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
          apply stk_of_rw_cells. exact SLOT. }
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        replace (4 * length xs)%nat with (Z.to_nat (4 * nXc)) in HPA by (clear - LEN1 N1; lia).
        assert (MU' : munch [(An, An + 4 * nXc); (lo, bv_unsigned sp - 104)] m2 m3)
          by (eapply munch_weaken; [| exact MU]; intros zq Hzq; cbn [outside] in Hzq |- *; destruct Hzq as (Hz1 & Hz2 & _); split; [exact Hz1| split; [clear - Hz2; lia| exact I]]).
        destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU' WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
        pose proof (bja_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ J2 F2 B2) as [ESA ELA].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ESA, ELA.
        pose proof (bja_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 J2 B2 MU WM
                      ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OA| clear; lia| clear - CNT N1; lia]|];
                            apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]| apply Forall_nil])
                      ltac:(cbn; split; [clear - ESA CNT N1; lia|]; split; [clear - ES SLO2 NEEDR; lia| exact I])
                      ltac:(intros BN; cbn; split; [pose proof (ELA BN); clear - H CNT N1; lia|]; split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5 SLO2 NEEDR; lia| exact I])) as B3.
        clear J2 F2 B2 OA OP' SBY SLEN DLEN INA INP.
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
        try clear CX2. pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
        (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep. zstep. zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
        destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
        pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
        eapply aevtA_call.
        { intros mo3 [HK3 MF3].
          eapply SPZ with (h := h2) (LB := (An, 4 * j) :: LBc) (LF := LF) (buf := pXc) (len := 4 * nXc) (lo := lo) (d := d) (junk := u32s xs);
            rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity.
          all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
          all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
          all: try (f_equal; clear; lia).
          all: unfold aaV0, aaF0, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
               clear - CNT EM NR1 NR NRE N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
          all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
        clear SPZ.
        (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
        destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by qlia.
        ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
        match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
        presA_transport HP4.
        assert (ST4' : stk asegs m4 lo (bv_unsigned sp + -104)).
        { eapply stk_merge; [exact ST4| | clear - SLO2 NEEDR LOSP; lia].
          replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
          apply stk_of_rw_cells. exact SLOT. }
        assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * j) :: LBc)) LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA h2)
                         [(pXc, pXc + 4 * nXc)] m3 m4).
        { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
        pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
        pose proof (bja_zfree _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 B3 eq_refl HP4' MI4 HCS4 HH4) as B4.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4, B4.
        assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
        apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
        clear CSOK SB64 SCS0 SCS HTOP2.
        pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
        assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 B3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2.
        pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM. unfold mpi_cells in DCX.
        pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
        assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
        pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
        rewrite <- HT4h in CW5.
        pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        (* [comment removed for export] *)
        shadow_chk DOX (X + 10) 2.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
        pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        pose proof (bja_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ D4 B4 MU WM) as B5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5.
        eapply K1; [exact J5| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| exact B5| reflexivity| cbn [md_n]; clear; lia| reflexivity| | |].
        * cbn [md_limbs]. rewrite skipn_repeat, limbs_val_app_zeros. exact HVV.
        * unfold aaV0, aaV1, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT EM. lia.
        * unfold aaF0, aaF1, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: match goal with |- ?g => idtac "G1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis VALM : AA_VAL_A < 2 ^ (32 * (aaM + 1)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0510@C17025492443.250C17025492443.251C17025492443.252C40893063684.296C53526081063.253C53526081063.254C53526081063.255D1701036673.199 D1705053216.276 D1705053216.283 D17975678776.256D20257660871.281D21651009785.202D22466435734.256D24976250634.287D28229479954.281D35106100313.275D35106100313.277D35106100313.282D35110411000.198D35110411000.202D3580721273.202 D3585062616.280 D50797141399.287D52014138856.287D59228252318.287D60109446735.256D61815348395.295D62155808737.287D6762693186.295 D7340709316.256 D939044794.256  K1307012896.250 K1307012896.251 K1307012896.252 K1329197271.253 K1329197271.254 K1329197271.255 K23468015258.296K2612272047.252 K2612272047.256 K3345721225.287 K3345721225.288 K38856059124.288K46911551239.287K46911551239.288K52322685826.296K59925691872.252K59925691872.256K7412424035.256 L10307112399.6  L10559054258.4  L10703980452.281L11656196980.1  L12416934887.5  L12755534717.8  L12755534717.9  L12876274804.4  L12905641847.4  L1294499141.2   L1342025005.2   L14051382092.8  L15477852824.1  L16473205958.5  L16473494895.4  L1705495428.5   L17585880332.13 L17703443598.3  L17830241467.3  L18587013051.13 L18966192929.0  L20257806435.5  L20630580640.10 L20803911415.2  L21073294716.9  L21086251255.8  L21297056158.4  L22479292268.1  L23083716406.283L23100341967.226L23100341967.240L23100341967.274L23455462144.3  L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.6  L24799912036.4  L24918931886.203L25119086869.34 L25132156744.1  L25138051168.17 L25138248375.8  L25142208316.1  L26063715927.5  L2607826517.4   L26228513507.2  L26502719108.5  L26660323117.1  L26673455472.32 L27572020408.8  L27686051247.3  L27747017808.5  L27835269521.2  L27836715734.227L27837255469.239L28231168598.1  L28504058434.9  L28655862141.3  L28671776394.4  L28923357568.281L30483066123.4  L30902300697.10 L31325970818.4  L32027975233.0  L3260869064.15  L3352129893.15  L34412813842.34 L34424803280.3  L34444340830.3  L34456469404.32 L34456534685.17 L34456730698.8  L35655538624.7  L35655538630.7  L35663928186.7  L3669771752.3   L38235734261.1  L38868673902.4  L39172636981.0  L40294887048.3  L40437308144.3  L40449602357.4  L4079695450.2   L4079999236.292 L43565739985.293L43878034250.5  L44196988417.11 L44611170703.5  L4482322106.10  L46160487540.228L46160487540.275L46380960401.4  L46389908878.16 L46754302522.273L46756153760.203L46756153760.281L46756187949.225L46756382136.226L46917722603.2  L46948640662.34 L47401054516.1  L48154966246.226L48155162489.225L49150310671.4  L49578233423.274L49579218529.34 L51751604631.202L52318461464.3  L5261871668.3   L53314392638.2  L53404598366.8  L54204283681.16 L547707976.3    L54802045807.151L54817154178.3  L55188957896.280L55190858076.286L55191156004.283L5570525222.16  L55715400192.226L55715400192.281L59308632307.3  L59308633593.3  L59308925409.151L59308925409.203L59308925409.206L59914681105.4  L59925822865.8  L60098763854.3  L6141606276.1   L61562785068.32 L62018535662.1  L63654471873.2  L63849440564.1  L64679905332.151L65348482612.1  L65361700727.32 L65361700727.34 L65496508708.4  L65908464690.34 L65908530483.17 L65913187379.10 L65913187379.4  L66581468868.32 L66661851587.4  L67180826602.3  L67180826602.4  L67725245073.2  L7400112281.3   L7419031306.32  L7704260991.4   L8016725142.2   L8890516472.1   O17025492443.250O17025492443.251O17025492443.252O22987107037.252O22987107037.256O32329373691.256O37539299629.250O37539299629.251O37539299629.252O45218884275.252O45218884275.256O47864099224.254O53526081063.253O53526081063.254O53526081063.255O65801484870.255P1307012896.250 P1307012896.251 P1307012896.252 P1329197271.253 P1329197271.254 P1329197271.255 P23468015258.296P27698597941.296P38856059124.288P40437264079.250P40437264079.251P40437264079.252P40441743114.254P46402209908.255P54191666875.296P7412424035.256 Q10203249998.291Q11801279589.295Q12370813529.234Q12370813529.248Q12370813529.284Q17205055869.283Q17207432298.233Q17207432298.247Q17975678776.256Q22466435734.256Q22642964918.294Q24974040330.287Q26207421841.235Q26207721832.236Q26207721832.285Q26207967338.233Q26207967338.247Q26207967338.282Q26209519061.284Q26295627581.291Q31651985788.284Q31653536963.247Q31654082872.235Q3667187378.280 Q37321635735.189Q37321635735.272Q37321652361.236Q37323914291.254Q37323914293.171Q37623376543.283Q37625261960.233Q37625261960.247Q38248387216.256Q39212284437.236Q39212284437.285Q42081808994.285Q42652628345.291Q42656805252.291Q43879899724.256Q43925228937.236Q43925228937.285Q49291908042.291Q49306541890.293Q49861398996.234Q50033073131.291Q50045673238.291Q50458135125.291Q52016320488.286Q52016320488.287Q52580266574.288Q5483308162.283 Q5485126037.233 Q5485126037.247 Q5485174314.234 Q5485174314.248 Q5485174314.284 Q5573176188.281 Q59703481013.234Q6027349519.286 Q6027349519.287 Q60511567613.236Q60511567613.285Q60697995187.236Q60697995187.285Q6143569392.234 Q6143569392.248 Q6143569392.284 Q61813135019.295Q62157788641.286Q62965564504.285Q62965564504.286Q64295054172.278Q64295054172.279Q64295054172.280Q64299361789.200Q64299361789.201Q6764644418.295 Q6775135803.291 Q6777346592.288 Q7891539809.284 Q8880503606.233 Q8880503606.282 Q8945815996.288 Q9538787269.233 Q9538787269.282 00000100200300400500600700800900:00^00_01601Z02H02g02h02i02j02k02l03C03b05205`05a06N06m07[08M08N09C09D09E09F09G09H09I09J0:50:`0;j0<f0<g0=b0>Z0?80?o0@f0@g0A;0AB0B>0BB0BR0BS0BT0Bb0C10C20C30CI0CM0CX0CY0CZ0C[0Cb0Ci0Cj0Ck0Cl0D:0D;0D<0D=0DL0DP0Do0ES0Em0FL0FM0FW0Fc0Fd0Fe0G40Gl0HD0HE0HT0HU0HV0Hf0Hg0Hn0IB0IC0IT0IU0IV0Ia0Ii0JU0K70K;0KY0KZ0Ki0LH0LS0LT0L_0L`0Lg0Lh0M<0M=0M>0MZ0N00N10NL0Ng0O<0O=0OA0OB0OC0OF0OG0OH0OO0On0Q00Q70Q80QG0QH0R30RY0RZ0R[0SQ0TG0UG0V@0W90W:0Wi0Wm0Xf0Y_0Y`0Z?0Zl0[C0[D0[N0[U0[k0[l0\60\h0]00]k0^f0_a0_b0`F0`e0a00a;0aX0b90bZ0b[0bn0c80c<0cl0co0d60d70dj0dk0e=0eO0e^0f60fH0fI0fJ0f_0fn0g50gA0gI0gJ0h70h80h?0hC0hD0hE0hF0hG0hH0hI0hJ0hK0hL0hM0hN0hO0hP0hQ0hR0hS0hT0hU0hV0hW0hX0hY0hZ0iP0iQ0j30jU0k70l50m30mi0mj0n=0nP0o>0o_10E10W10n11;11S11k12B12c13:13Q13c14:14G14Y14k15;15M15Z16116c17R18F19B1:61:e1;71;N1;[1<31<J1<\1=41=G1=Z1>51>L1>^1??1?f1?g1@?1@W1@j1AN1Ao1BB1BT1Bk1C81CO1C\1Cn1D`1Da1EB1Ef1F;1FK1Fe1G:1GQ1G^1H01HC1Hg1IF1Ie1If1Ig1Ih1Ii1Ij1JB1JZ1K21KJ1Ka1L31LC1LX1LhFFFFFFFFFFS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENFS2ra2sp1X3xs02xs3pXc2jnS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs3pXc2jn2An4ZLENFFFFFS2ra2sp1X3xs02xs3pXc2jnS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS1R2ra2sp1X3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS2X03SPR2P02An3An04ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs3pXc2jn2An4ZLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo2xs3pXc2jn3LOS2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An04ZLENFS1R3HIA2ra2sp1X3xs02lo2xs3pXc2jn2h22An4TOP24SLEN4DLENFFFFFFFS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS1R2sp1X3xs02lo4SLO22xs2jn2JM5NEEDR3FSZ3DSX4LEN12N12An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3FSZ3DSX4ZLEN2HB5Ha_st5Hl_stFS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3DSX2An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3DSX4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4LEN12An3FXS4ZLENS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENFS1R2sp2lo4SLO25NEEDRS2jn2AnS1R2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An04ZLEN3AC53ACVS2jnS1X2jn2N12An3FXSFFS2sp2lo2zq3Hz2S2xs2jn4LEN12N1FFS2dA2dB1v2jn2JM2BV3NR1S2spS2jn2An3A47FFFS2jn2N1S2jn2N1FSFS2lo2jn2An3FloFFFS2xs2jn4LEN12N1S2AnS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2AnS2ra2sp1X3xs02xs3pXc2jn2An4ZLENFS1R3HIA2hcS3pXc2jn3P47FFS2xs2jn4LEN12N1S2ra2sp1X3xs02xs3pXc2jn2JM2X03SPR2P02An3An03Fal3ZN14LEN5S2sp2dA2dB2jn3CNT3SPR2N1FS2sp2jn3CNT3SPRFFS1R3HIA1h2sp3TOPFS2jn2N1S1R2sp2lo4SLO25NEEDRFS2sp2dA2dB2jn3NR1FFS2xs2jn3HVVS2jn3NR1S2ra2sp1X3xs02xs3pXc2jn3CNT3NR12An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn3CNT3NR12AnS2spS1R2sp2lo4SLO22jn5NEEDR2An3FloFS2xs2jn4LEN12N1S2ra2sp1X3xs02xs3pXc2jn2An4ZLENS1d2D01f2BFFS1d2D01f2BFSS2sp2loFS1R2sp2dA2dB2lo4SLO2FFS1R2sp2dA2dB2lo4SLO23NRM3SPRS1R2sp2lo4SLO23NRA3SPRFS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HFS2loFSS1XFFS2jn2AnS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS2ra2sp1X2nX3xs02dA2dB2xs3pXc2jn2JM2X03SPR4LEN12P02An3An04ZLEN3ZN1S2sp2loFS2jn2N12An1a2NOFS2ra2sp1X3xs02xs3pXc2jn2X03X162An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2X03X162An4ZLENFFS2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLENS1R2ra2sp1X3xs02xs3pXc2jn2X03SPR2P02An3An03ZN13AC53ACVS1R2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN3AC53ACVS2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P02An3An04SLEN4DLEN3A47S2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P02An3An04SLEN4DLEN3A47FS1R3HIA1h2sp2dA2dB3BUD1v2jn2JM2BV3SPR2N12h23HV1S2spS2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P03P472An3An04SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P03P472An3An04SLEN4DLENFS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2BF3SPR2h24HFR1S2ra2sp1X3xs02xs3pXc2jnFS1X2X03X16S2jn2AnS2dA2dB1v2jn2JM2BV3NR1FS1R3HIA2h2S2ra2sp1X3xs02xs3pXc2jn2JM2X03SPR2N12P02An3An03FalS2jn3CNTS2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN4LEN5S2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN4LEN5S2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN4LEN5FS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS3pXc2P02KPS2An3An02KZS2ra2sp1X3xs02xs3pXc2jn2An2UBS2ra2sp1X3xs02xs3pXc2jn2An3A472UBS2ra2sp1X3xs02xs3pXc2jn2An3A472UBFS2sp2lo3pXc2jn4XLScS1R2lo3LOSS2spS1R3HIA1h2sp2dA2dB3BUD1v2hc2jn2JM2BV3SPR3NR13HV1S1RS2jn2N1FS2ra2sp1X3xs02xs3pXc2jn2JM2X03SPR2N12P02An3An04XPALFS2sp2dA2dB3SPA3SPRS2sp2dA2dB3SPA3SPRS2xs2jn4LEN12N1S1R3HIA2sp2dA2dB2h24TOP2S1R3HIA2sp2h24TOP2FFS2sp2dA2dB2jn3CNT3SPRS3pXc2jn2An3SEPS2jn2N1S2xs2jn4LEN1S2jn3NR1FS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2hc2BF3SPR4HFR1FS2sp2loS2jnFFFFFFFFFFFFFFFFFFFFFFFS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2An3Flo4ZLEN3AC5FS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2N12An3AnC3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2N12An3AnC3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2An3Flo4ZLEN3AC5FS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs3pXc2jn2X03XAL2N12An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2X03XAL2AnS2ra2sp1X3xs02xs3pXc2jn2X03XAL2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An3A474ZLENS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jnS1X3xs02xs2jn4SLEN4DLENS1R2sp3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS3ALO2PC4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS3xs02lo2xs2jn4SLEN4DLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn2X04ZLEN2HBS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS2sp3xs02lo2xs2jn4SLEN4DLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS3xs02xs2jn4LEN12An3An04ZLEN4LEN5S3xs02xs2jn4LEN12An3An04ZLEN4LEN55HBarrFS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS3xs02xs2jn2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1R2sp3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS3ALO2PC4ZLENFS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS3xs02xs2jn4SLEN4DLENS3xs02xs2jn4ZLENS1X3xs02xs2jn2X04SLEN4DLENS1X3xs02xs2jn2X04ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stFFFFFS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS1X3xs02xs2jn2X04ZLEN2HBS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS3xs02xs2jn4ZLENS3xs02xs2jn4SLEN4DLENS3xs02xs2jn4ZLEN". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2"] Lemma aa_G3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.Pjn,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1;.R1:.R19.R18.R17.(48.VX,+1.R14.R15.R16.VpadX,$1:.))P,(22.R15.(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(22.(23.R16.+1.)+2710.)P,(22.R17.$5=.)P,(10.$8.(23.(55.R1:.)(60.+2.(1<.+20.R18.)))$4>.)P,(22.R20.$57.)P,(22.R20.$58.)(51.$47.(52.$47.VR,VHIA,R20.Vmo,)$53.(43.(44.R1:.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R19.R18.R17.(29.&40.VX,)(29.&40.(23.VX,+:.))R16.R15.(29.&40.+1.)R14.R13.R12.R11.R10.(29.&40.R1;.)(29.&40.(23.R1;.+1.))R?.R>.(29.&40.(59.(2=.VR,)))(29.&40.(23.(1<.+4.R1;.)+4.))(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(23.(5:.VX,+3.)(59.(2=.VR,))))R=.R<.R;.R:.R9.R8.)VF,(29.&40.+9>194.)Vfc,(45.(3.&40.))R1>.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J NGX CNT JM HVV BV BF. jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc. pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (jn + 1)) with (Z_to_bv 64 (jn + 1)) by reflexivity.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := jn + 1) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity.
      all: try (apply c24_of_transition; exact C24T).   (* [comment removed for export] *)
      all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: try (f_equal; clear; lia).
      all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT JM NR1 NR LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp + -104)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT. }
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply aa_retm16; [exact J2| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| |].
      + unfold aaV1, aaM, add_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      + unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace ((jn + 1) * 4) with (4 * (jn + 1)) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An (jn + 1) J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT NR1; lia)) as [J2 F2].
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J. try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. try clear STc; try clear CX1.
      xa_open J2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & _ & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2, OWN1. unfold mpi_cells in CX2.
      try clear XIN; try clear XPAL; try clear XARR; try clear PI; try clear OP. ddestruct (OWN1 ltac:(discriminate)) as (_ & _ & XIN & XPAL & XARR & _ & _ & _ & OP & _). clear OWN1.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
      destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl)
        as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
      rewrite firstn_length in DST, DLEN. rewrite repeat_length in DST, DLEN.
      replace (Init.Nat.min (Z.to_nat jn) (Z.to_nat (jn + 1))) with (Z.to_nat jn) in DST, DLEN by (clear - CNT N1; lia).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP; [exfalso; first [rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia) | idtac]; clear - KP P0; lia|]. clear KP.
      (* [comment removed for export] *)
      zstep. zstep. zstep. ubchk.
      shadow_chk OX1 (X + 10) 2.
      zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_AA) as SPC. unfold A_ASAN_MEMCPY_AA in SPC.
      apply (u8arr_of_rw_cells asegs) in DST.
      clear MU WM. pose proof (munch_refl [(An, An + 4 * jn); (lo, bv_unsigned sp + -112)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      acallxA_sp (bv_unsigned sp + -112)
        (eapply SPC with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * jn) (lo := lo)
                          (ss := u32s xs);
         rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
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
               | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
      clear SPC.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
      match goal with H : stk asegs m3 lo (bv_unsigned sp + -112) |- _ => rename H into ST3 end.
      match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
      assert (ST3' : stk asegs m3 lo (bv_unsigned sp + -104)).
      { eapply stk_merge; [exact ST3| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SLOT. }
      apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
      replace (4 * length xs)%nat with (Z.to_nat (4 * jn)) in HPA by (clear - LEN1 N1; lia).
      assert (MU' : munch [(An, An + 4 * jn); (lo, bv_unsigned sp - 104)] m2 m3)
        by (eapply munch_weaken; [| exact MU]; intros zq Hzq; cbn [outside] in Hzq |- *; destruct Hzq as (Hz1 & Hz2 & _); split; [exact Hz1| split; [clear - Hz2; lia| exact I]]).
      destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU' WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
      clear J2 F2 OA OP' SBY SLEN DLEN INA INP.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      try clear CX2. pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
      (* [comment removed for export] *)
      clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      zstep. zstep. zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (buf := pXc) (len := 4 * jn) (lo := lo) (d := d) (junk := u32s xs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity.
        all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
        all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
        all: try (f_equal; clear; lia).
        all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
             clear - CNT JM NR1 NR N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by qlia.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      presA_transport HP4.
      assert (ST4' : stk asegs m4 lo (bv_unsigned sp + -104)).
      { eapply stk_merge; [exact ST4| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SLOT. }
      assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * (jn + 1)) :: LBc)) LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA h2)
                       [(pXc, pXc + 4 * jn)] m3 m4).
      { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
      pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4.
      assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
      assert (HS4h : hstkhi asegs R HIA h4 = hstkhi asegs R HIA h) by (rewrite HS4; exact HS1).
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
      clear CSOK SB64 SCS0 SCS HTOP2.
      pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
      assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2.
      pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM, DARR, DLEN4. unfold mpi_cells in DCX.
      pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
      assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
      pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
      rewrite <- HT4h in CW5.
      pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      (* [comment removed for export] *)
      zstep.
      shadow_chk DOX (X + 10) 2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
      pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5. rewrite skipn_repeat in J5.
      replace (Z.to_nat (jn + 1) - Z.to_nat jn)%nat with 1%nat in J5 by (clear - CNT N1; lia). cbn [repeat] in J5.
      clear D4 DST4 DFR DHT DHS DHF DHCS DHV DHFR DSG DSUB DKEEP DGONE DNEW DAPART DLEN4 DCNT DXS DPRES DFRESH DAL DLO DNM CW5.
      try clear DMI; try clear DARR; try clear DCX; try clear DOX; try clear DHM.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1.
      xa_open J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J5) as (_ & LEN5 & _ & _ & CX5 & _ & OWN5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX5, LEN5, OWN5. unfold mpi_cells in CX5.
      ddestruct (OWN5 ltac:(discriminate)) as (_ & _ & AIN & _ & AARR & _ & AC5 & _ & OA5 & _). clear OWN5.
      assert (CWA : client_wrange L (((An, 4 * (jn + 1)) :: lb_remove pXc LBc) ++ fdata LF) (arl_stklo R) (htop asegs R HIA h4) An (4 * (jn + 1)))
        by (eapply client_wrange_block; [left; reflexivity| clear; lia| clear; lia]).
      assert (NTH : nth_error (xs ++ [Z_to_bv 64 0]) (Z.to_nat jn) = Some (Z_to_bv 64 0)).
      { rewrite nth_error_app2 by (clear - LEN1 N1; lia). replace (Z.to_nat jn - length xs)%nat with 0%nat by (clear - LEN1 N1; lia). reflexivity. }
      clear MU WM. pose proof (munch_refl [(An + 4 * jn, An + 4 * jn + 4)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      (* [comment removed for export] *)
      pose proof (alloc_ceiling_val R) as ACV.
      zstep. ubchk. zstep. zstep.
      replace (Z_to_bv 64 (An + (4 * jn + 4) + -4)) with (Z_to_bv 64 (An + 4 * jn)) by (f_equal; clear; lia).
      zstep. zstep. ubchk. zstep.
      try replace (Z_to_bv 64 (An + (4 * jn + 4) + -4)) with (Z_to_bv 64 (An + 4 * jn)) by (f_equal; clear; lia).
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OA5 (An + 4 * jn) 4.
      (* [comment removed for export] *)
      pose proof (u32arr_read asegs m5 An (xs ++ [Z_to_bv 64 0]) jn (Z_to_bv 64 0) _ AARR NTH ltac:(clear - N1; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof (u32arr_store_ok asegs m5 An (xs ++ [Z_to_bv 64 0]) jn _ AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia) ltac:(f_equal; clear; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
        pose proof (u32arr_write asegs m5 An (xs ++ [Z_to_bv 64 0]) jn vv AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia)) as AARR' end.
      store_done.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
      match goal with H : HM asegs R HIA h4 _ LF m6 |- _ => rename H into HH6 end.
      assert (HW6 : forall a, ~ outside [(An + 4 * jn, An + 4 * jn + 4)] a -> (LHeap = LHeap /\ An <= a < An + 4 * (jn + 1)) \/ lo <= a < bv_unsigned sp - 104).
      { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO N1. lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J5 MU WM MI6 ST6 HH6 HW6
                    ltac:(cbn; split; [clear - Flo SLO2 NEEDR N1; lia| exact I]) ltac:(cbn; split; [clear - FXS N1; lia| exact I]) AARR'
                    ltac:(rewrite upd_length; reflexivity)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      (* [comment removed for export] *)
      zstep. ubchk. zstep.
      eapply aa_ret0; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| | reflexivity| |].
      * unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_upd by (rewrite length_app; cbn [length]; clear - LEN1 N1; lia).
        rewrite (limb32_w32_nth _ _ _ NTH).
        change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1))) mod 2 ^ 32)
          with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1)))).
        rewrite w32_incr. unfold w32. rewrite (unsigned_lit 0) by (clear; lia).
        change ((0 mod 2 ^ 32 + 1) mod 2 ^ 32) with 1. change (0 mod 2 ^ 32) with 0.
        rewrite limbs_val_app. cbn [limbs_val]. rewrite ?(unsigned_lit 0) by (clear; lia). change (0 mod 2 ^ 32) with 0.
        replace (Z.of_nat (Z.to_nat jn)) with jn by (clear - N1; lia). rewrite LEN1. clear - HVV. lia.
      * unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      * unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: match goal with |- ?g => idtac "G3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04k0@C17025492443.248C17025492443.249C17025492443.250C40893063684.292C53526081063.251C53526081063.252C53526081063.253D1701036673.198 D1705053216.274 D1705053216.281 D17975678776.254D20257660871.279D21651009785.201D22466435734.254D24976250634.283D28229479954.279D35106100313.273D35106100313.275D35106100313.280D35110411000.197D35110411000.201D3580721273.201 D3585062616.278 D50797141399.283D52014138856.283D59228252318.283D60109446735.254D61815348395.291D62155808737.283D6762693186.291 D7340709316.254 D939044794.254  K1307012896.248 K1307012896.249 K1307012896.250 K1329197271.251 K1329197271.252 K1329197271.253 K23468015258.292K2612272047.250 K2612272047.254 K3345721225.283 K3345721225.284 K38856059124.284K46911551239.283K46911551239.284K52322685826.292K59925691872.250K59925691872.254K7412424035.254 L10307112399.6  L10559054258.4  L10703980452.277L11656196980.1  L12416934887.5  L12755534717.8  L12755534717.9  L12876274804.4  L12905641847.4  L1294499141.2   L1342025005.2   L14051382092.8  L15198982830.3  L15477852824.1  L16473205958.5  L16473494895.4  L1705495428.5   L17585880332.13 L17703443598.3  L17830241467.3  L18587013051.13 L20257806435.5  L20630580640.10 L20803911415.2  L21073294716.9  L21086251255.8  L21297056158.4  L22479292268.1  L23100341967.225L23100341967.238L23100341967.270L23455462144.3  L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.6  L24799912036.4  L24918931886.199L25119086869.34 L25132156744.1  L25138051168.17 L25138248375.8  L25142208316.1  L26063715927.5  L2607826517.4   L26228513507.2  L26502719108.5  L26660323117.1  L26673455472.32 L27572020408.8  L27686051247.3  L27747017808.5  L27835269521.2  L27835396370.225L27837255469.237L28231168598.1  L28504058434.9  L28655862141.3  L28671776394.4  L28923357568.277L30483066123.4  L30902300697.10 L31325970818.4  L31772774807.201L32027975233.0  L3260869064.15  L3352129893.15  L34412813842.34 L34424803280.3  L34444340830.3  L34456469404.32 L34456534685.17 L34456730698.8  L35655538624.7  L35655538630.7  L35663928186.7  L3669771752.3   L38235734261.1  L38868673902.4  L39172636981.0  L39188636933.0  L40294887048.3  L40437308144.3  L40449602357.4  L43565739985.289L43878034250.5  L44196988417.11 L44569460897.0  L44611170703.5  L4482322106.10  L46380960401.4  L46389908878.16 L46754302522.269L46754328850.225L46756153760.199L46756153760.277L46756382136.225L46917722603.2  L46948640662.34 L47401054516.1  L48154966246.225L48157018438.225L49150310671.4  L49578233423.270L49579218529.34 L52318461464.3  L5261871668.3   L53314392638.2  L53404598366.8  L54204283681.16 L547707976.3    L54802045807.151L54817154178.3  L55188957896.276L55190858076.282L55191156004.279L5570525222.16  L55715400192.226L55715400192.277L59308632307.3  L59308633593.3  L59308925409.151L59308925409.199L59308925409.202L59914681105.4  L59925822865.8  L60098763854.3  L6141606276.1   L61562785068.32 L62018535662.1  L63654471873.2  L63849440564.1  L64679905332.151L65348482612.1  L65361700727.32 L65361700727.34 L65496508708.4  L65908464690.34 L65908530483.17 L65913187379.10 L65913187379.4  L66581468868.32 L66661851587.4  L67180826602.3  L67180826602.4  L67725245073.2  L7400112281.3   L7419031306.32  L7704260991.4   L8016725142.2   L8356420534.281 L8890516472.1   O17025492443.248O17025492443.249O17025492443.250O22987107037.250O22987107037.254O32329373691.254O37539299629.248O37539299629.249O37539299629.250O45218884275.250O45218884275.254O47864099224.252O53526081063.251O53526081063.252O53526081063.253O65801484870.253P1307012896.248 P1307012896.249 P1307012896.250 P1329197271.251 P1329197271.252 P1329197271.253 P23468015258.292P27698597941.292P38856059124.284P40437264079.248P40437264079.249P40437264079.250P40441743114.252P46402209908.253P54191666875.292P7412424035.254 Q10203249998.287Q11801279589.291Q12370813529.233Q12370813529.246Q12370813529.280Q17205055869.279Q17207432298.232Q17207432298.245Q17975678776.254Q22466435734.254Q22642964918.290Q24416901192.233Q24418772599.280Q24418818504.234Q24418818504.281Q24974040330.283Q26207967338.245Q26207967338.280Q26209773141.233Q26295627581.287Q29201240740.233Q29203049627.280Q31651666684.233Q31653536963.245Q31653536963.280Q36081244985.234Q36081244985.281Q3667187378.278 Q37321635735.188Q37321635735.270Q37321652361.234Q37323914291.252Q37323914293.170Q37623376543.279Q37625261960.232Q37625261960.245Q38248387216.254Q42081808994.281Q42766971027.234Q43879899724.254Q46720892458.234Q49291908042.287Q49306541890.289Q49861398996.233Q50458135125.287Q52016320488.282Q52016320488.283Q52580266574.284Q5483308162.279 Q5485126037.232 Q5485126037.245 Q5485174314.233 Q5485174314.246 Q5485174314.280 Q5573176188.279 Q56512145356.234Q56512145356.281Q59703481013.233Q6027349519.282 Q6027349519.283 Q6143569392.233 Q6143569392.246 Q6143569392.280 Q61813135019.291Q61815603366.287Q61819782235.287Q62157788641.282Q62965564504.281Q62965564504.282Q64295054172.276Q64295054172.277Q64295054172.278Q64299361789.199Q64299361789.200Q6762438223.287 Q6764644418.291 Q6775036594.287 Q6775135803.287 Q6777346592.284 Q7891539809.280 Q8945815996.284 00000100200300400500600700800900:00^00_01601Z02H02g02h02i02j02k02l03C03b05205`05a06N06m07[08M08N09C09D09E09F09G09H09I09J0:50:`0;j0<f0<g0=b0>Z0?80?o0@f0@g0A;0AB0B>0BB0BR0BS0BT0Bb0C10C20C30CI0CR0CV0Ca0Cb0Cc0Cd0Ck0D20D30D40DB0DC0DD0DE0DT0DX0E<0EV0F50F60F@0FL0FM0FN0F]0GU0Gm0Gn0H=0H>0H?0HO0HP0HW0Hk0Hl0I=0I>0I?0IJ0IR0J>0J`0Jd0KB0KC0KR0L10L<0L=0LH0L_0L`0Lg0Lh0M<0M=0M>0MZ0N00N10NL0Ng0O<0O=0OA0OB0OC0OD0OG0OH0OI0PK0PR0PS0PT0Pc0Pd0Pe0Pf0Q\0RU0SK0TK0UD0UE0V40V80W10Wj0Wk0XJ0Y70Y80YB0YI0Y_0Y`0Yj0Z\0Zd0[_0\Z0]U0]V0^:0^Y0^d0^o0_L0_m0`N0`O0`b0`l0a00a`0ac0aj0ak0b^0b_0c10cC0cR0cj0d<0d=0d>0dS0db0di0e50e=0e>0ek0el0f30fR0fV0fW0fX0fY0fZ0f[0f\0f]0f^0f_0f`0fa0fb0fc0fd0fe0ff0fg0fh0fi0fj0fk0fl0fm0gc0gd0hF0hh0iJ0jH0kF0l<0l=0lP0lc0mQ0n20nX0nj0oA0oN0of10>10U10l11>11U11g12H12U12g13>13N13e14714N14[14m15D15V16H17717k18g19[1:J1:\1;31;@1;X1<01<11<L1<M1<n1=U1=V1=i1>M1>n1?A1?S1?j1@71@N1@[1@m1A_1B[1CW1CX1D91D]1E41EA1ES1Ef1F91FL1G01GO1Gn1Go1H01H11H21H31HK1Hc1I;1IS1Ik1JC1JSFFFFFFFFFFS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENFS2ra2sp1X3xs02xs3pXc2jnS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs3pXc2jn2An4ZLENFFFFFS2ra2sp1X3xs02xs3pXc2jnS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS1R2ra2sp1X3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS2X03SPR2P02An3An04ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs3pXc2jn2An4ZLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo2xs3pXc2jn3LOS2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An04ZLENFS1R3HIA2ra2sp1X3xs02lo2xs3pXc2jn2h22An4TOP24SLEN4DLENFFFFFFFS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS1R2sp1X3xs02lo4SLO22xs2jn2JM5NEEDR3FSZ3DSX4LEN12N12An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3FSZ3DSX4ZLEN2HB5Ha_st5Hl_stFS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3DSX2An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3DSX4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4LEN12An3FXS4ZLENS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENFS1R2sp2lo4SLO25NEEDRS2jn2AnS1R2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An04ZLEN3AC53ACVS2jnS1X2jn2N12An3FXSFFS2sp2lo2zq3Hz2S2xs2jn4LEN12N1FFS2dA2dB1v2jn2JM2BV3NR1S1R1X3XALS2spS2jn2An3A47FFFS2jn2N1S2jn2N1FFS2lo2jn2An3FloFFFS2xs2jn4LEN12N1S2AnS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2AnS2ra2sp1X3xs02xs3pXc2jn2An4ZLENFS1R3HIA2hcS3pXc2jn3P47FFS2xs2jn4LEN12N1S2ra2sp1X3xs02xs3pXc2jn2JM2X03SPR2P02An3An03Fal3ZN14LEN5S2sp2dA2dB2jn3CNT3SPR2N1FS2sp2jn3CNT3SPRFFS1R3HIA1h2sp3TOPFS2jn2N1S1R2sp2lo4SLO25NEEDRFS2sp2dA2dB2jn3NR1FFS2xs2jn3HVVS2jn3NR1S2ra2sp1X3xs02xs3pXc2jn3CNT3NR12An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn3CNT3NR12AnS2spS1R2sp2lo4SLO22jn5NEEDR2An3FloFS2xs2jn4LEN12N1S2ra2sp1X3xs02xs3pXc2jn2An4ZLENS1d2D01f2BFFS1d2D01f2BFS2ra2sp1X3xs02xs3pXc2jnSS2sp2loFS1R2sp2dA2dB2lo4SLO2FFS1R2sp2dA2dB2lo4SLO23NRM3SPRS1R2sp2lo4SLO23NRA3SPRFS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HFS2loFSSS1XFFS2ra2sp1X2nX3xs02dA2dB2xs3pXc2jn2JM2X03SPR4LEN12P02An3An04ZLEN3ZN1S2sp2loFSS2jn2N12An1a2NOFFFS2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLENS2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P02An3An04SLEN4DLEN3A47S1R2ra2sp1X3xs02xs3pXc2jn2X03SPR2P02An3An03ZN13AC53ACVS1R2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN3AC53ACVS2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P02An3An04SLEN4DLEN3A47FS1R3HIA1h2sp2dA2dB3BUD1v2jn2JM2BV3SPR2N12h23HV1S2spS2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P03P472An3An04SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P03P472An3An04SLEN4DLENFS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2BF3SPR2h24HFR1FS1X2X03X16S2jn2AnS2dA2dB1v2jn2JM2BV3NR1FS1R3HIA2h2S2ra2sp1X3xs02xs3pXc2jn2JM2X03SPR2N12P02An3An03FalS2jn3CNTS2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN4LEN5S2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN4LEN5S2ra2sp1X3xs02xs3pXc2jn2X03SPR4LEN12P02An3An03A474ZLEN4LEN5FS2ra2sp1X3xs02xs3pXc2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS3pXc2P02KPS2An3An02KZS2ra2sp1X3xs02xs3pXc2jn2An2UBS2ra2sp1X3xs02xs3pXc2jn2An3A472UBS2ra2sp1X3xs02xs3pXc2jn2An3A472UBFS2sp2lo3pXc2jn4XLScS1R2lo3LOSS2spS1R3HIA1h2sp2dA2dB3BUD1v2hc2jn2JM2BV3SPR3NR13HV1S1RS2jn2N1FS2ra2sp1X3xs02xs3pXc2jn2JM2X03SPR2N12P02An3An04XPALFS2sp2dA2dB3SPA3SPRS2sp2dA2dB3SPA3SPRS2xs2jn4LEN12N1S1R3HIA2sp2dA2dB2h24TOP2S1R3HIA2sp2h24TOP2FFS2sp2dA2dB2jn3CNT3SPRS3pXc2jn2An3SEPS2jn2N1S2xs2jn4LEN1S2jn3NR1FS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2hc2BF3SPR4HFR1FS2sp2loS2ra2sp1X3xs02xs3pXc2jn2An4ZLENS2jnFFFFFFFFFFFFFFFFFFFFFFFS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2An3Flo4ZLEN3AC5FS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2N12An3AnC3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2N12An3AnC3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2An3Flo4ZLEN3AC5FS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs3pXc2jn2X03XAL2N12An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2X03XAL2AnS2ra2sp1X3xs02xs3pXc2jn2X03XAL2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An3A474ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1R2sp3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS3ALO2PC4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS3xs02lo2xs2jn4SLEN4DLENS1X3xs02xs2jn2X04ZLEN2HBFS2sp3xs02lo2xs2jn4SLEN4DLENFS3xs02xs2jn4LEN12An3An04ZLEN4LEN5S3xs02xs2jn4LEN12An3An04ZLEN4LEN55HBarrFS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS3xs02xs2jn2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1R2sp3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS3ALO2PC4ZLENS2ra2sp1X3xs02xs3pXc2jn2JM2X03XAL3SPR2N12P02An3An04SLEN4DLENS2ra2sp1X3xs02xs3pXc2jn2JM2X03XAL3SPR4LEN12N12P02An3An04ZLENFS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stFFFFFS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS1X3xs02xs2jn2X04ZLEN2HBS3xs02xs2jn4ZLEN". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2"] Lemma aa_G2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.Pjn,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs5,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1:.R19.R18.R17.R16.(48.VX,+1.R13.R14.R15.VpadX,$1:.))P,(22.R14.(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(22.(23.R15.+1.)+2710.)P,(22.R16.$5=.)P,(10.$8.(23.(55.R19.)(60.+2.(1<.+20.R17.)))$4>.)P,(22.R1?.$57.)P,(22.R1?.$58.)(51.$47.(52.$47.VR,VHIA,R1?.Vmo,)$53.(43.(44.R19.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R18.R17.R16.(29.&40.VX,)(29.&40.(23.VX,+:.))R15.R14.R13.R12.R11.R10.R?.R>.(29.&40.(26.R1:.+1.))(29.&40.(23.R1:.+1.))(29.&40.-5.)R=.(29.&40.(59.(2=.VR,)))(29.&40.(1<.+4.R1:.))(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(23.(5:.VX,+3.)(59.(2=.VR,))))R<.(29.&40.R1:.)R;.R:.R9.R8.)VF,(29.&40.+9>298.)Vfc,(45.(3.&40.))R1=.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J NGX CNT JM HVV BV BF. jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc. pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := jn + 1) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity.
      all: try (apply c24_of_transition; exact C24T).   (* [comment removed for export] *)
      all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: try (f_equal; clear; lia).
      all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT JM NR1 NR LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp + -104)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT. }
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply aa_retm16; [exact J2| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| |].
      + unfold aaV1, aaM, add_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      + unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace ((jn + 1) * 4) with (4 * (jn + 1)) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An (jn + 1) J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT NR1; lia)) as [J2 F2].
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J. try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. try clear STc; try clear CX1.
      xa_open J2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & _ & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2, OWN1. unfold mpi_cells in CX2.
      try clear XIN; try clear XPAL; try clear XARR; try clear PI; try clear OP. ddestruct (OWN1 ltac:(discriminate)) as (_ & _ & XIN & XPAL & XARR & _ & _ & _ & OP & _). clear OWN1.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
      destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl)
        as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
      rewrite firstn_length in DST, DLEN. rewrite repeat_length in DST, DLEN.
      replace (Init.Nat.min (Z.to_nat jn) (Z.to_nat (jn + 1))) with (Z.to_nat jn) in DST, DLEN by (clear - CNT N1; lia).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP; [exfalso; first [rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia) | idtac]; clear - KP P0; lia|]. clear KP.
      (* [comment removed for export] *)
      assert (E10 : Z.shiftr (X + 10) 3 + al_sb AL = Z.shiftr X 3 + al_sb AL + 1)
        by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - XAL; lia).
      zstep. zstep. zstep. ubchk.
      rewrite E10. zstep. zstep.
      zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_AA) as SPC. unfold A_ASAN_MEMCPY_AA in SPC.
      apply (u8arr_of_rw_cells asegs) in DST.
      clear MU WM. pose proof (munch_refl [(An, An + 4 * jn); (lo, bv_unsigned sp + -112)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      acallxA_sp (bv_unsigned sp + -112)
        (eapply SPC with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * jn) (lo := lo)
                          (ss := u32s xs);
         rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
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
               | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
      clear SPC.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
      match goal with H : stk asegs m3 lo (bv_unsigned sp + -112) |- _ => rename H into ST3 end.
      match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
      assert (ST3' : stk asegs m3 lo (bv_unsigned sp + -104)).
      { eapply stk_merge; [exact ST3| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SLOT. }
      apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
      replace (4 * length xs)%nat with (Z.to_nat (4 * jn)) in HPA by (clear - LEN1 N1; lia).
      assert (MU' : munch [(An, An + 4 * jn); (lo, bv_unsigned sp - 104)] m2 m3)
        by (eapply munch_weaken; [| exact MU]; intros zq Hzq; cbn [outside] in Hzq |- *; destruct Hzq as (Hz1 & Hz2 & _); split; [exact Hz1| split; [clear - Hz2; lia| exact I]]).
      destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU' WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
      clear J2 F2 OA OP' SBY SLEN DLEN INA INP.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      try clear CX2. pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
      (* [comment removed for export] *)
      clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      zstep. zstep. zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (buf := pXc) (len := 4 * jn) (lo := lo) (d := d) (junk := u32s xs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity.
        all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
        all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
        all: try (f_equal; clear; lia).
        all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
             clear - CNT JM NR1 NR N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by qlia.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      presA_transport HP4.
      assert (ST4' : stk asegs m4 lo (bv_unsigned sp + -104)).
      { eapply stk_merge; [exact ST4| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SLOT. }
      assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * (jn + 1)) :: LBc)) LF (bv_unsigned sp - 104) (arl_stklo R) (hstkhi asegs R HIA h2)
                       [(pXc, pXc + 4 * jn)] m3 m4).
      { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
      pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4.
      assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
      assert (HS4h : hstkhi asegs R HIA h4 = hstkhi asegs R HIA h) by (rewrite HS4; exact HS1).
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
      clear CSOK SB64 SCS0 SCS HTOP2.
      pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
      assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2.
      pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM, DARR, DLEN4. unfold mpi_cells in DCX.
      pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
      assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
      pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
      rewrite <- HT4h in CW5.
      pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      (* [comment removed for export] *)
      rewrite ?E10. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
      pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5. rewrite skipn_repeat in J5.
      replace (Z.to_nat (jn + 1) - Z.to_nat jn)%nat with 1%nat in J5 by (clear - CNT N1; lia). cbn [repeat] in J5.
      clear D4 DST4 DFR DHT DHS DHF DHCS DHV DHFR DSG DSUB DKEEP DGONE DNEW DAPART DLEN4 DCNT DXS DPRES DFRESH DAL DLO DNM CW5.
      try clear DMI; try clear DARR; try clear DCX; try clear DOX; try clear DHM.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1.
      xa_open J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J5) as (_ & LEN5 & _ & _ & CX5 & _ & OWN5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX5, LEN5, OWN5. unfold mpi_cells in CX5.
      ddestruct (OWN5 ltac:(discriminate)) as (_ & _ & AIN & _ & AARR & _ & AC5 & _ & OA5 & _). clear OWN5.
      assert (CWA : client_wrange L (((An, 4 * (jn + 1)) :: lb_remove pXc LBc) ++ fdata LF) (arl_stklo R) (htop asegs R HIA h4) An (4 * (jn + 1)))
        by (eapply client_wrange_block; [left; reflexivity| clear; lia| clear; lia]).
      assert (NTH : nth_error (xs ++ [Z_to_bv 64 0]) (Z.to_nat jn) = Some (Z_to_bv 64 0)).
      { rewrite nth_error_app2 by (clear - LEN1 N1; lia). replace (Z.to_nat jn - length xs)%nat with 0%nat by (clear - LEN1 N1; lia). reflexivity. }
      clear MU WM. pose proof (munch_refl [(An + 4 * jn, An + 4 * jn + 4)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      (* [comment removed for export] *)
      pose proof (alloc_ceiling_val R) as ACV.
      zstep. ubchk. zstep. zstep. zstep. ubchk.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OA5 (An + 4 * jn) 4.
      (* [comment removed for export] *)
      pose proof (u32arr_read asegs m5 An (xs ++ [Z_to_bv 64 0]) jn (Z_to_bv 64 0) _ AARR NTH ltac:(clear - N1; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      (* [comment removed for export] *)
      zstep.
      pose proof (u32arr_store_ok asegs m5 An (xs ++ [Z_to_bv 64 0]) jn _ AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia) ltac:(f_equal; clear; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
        pose proof (u32arr_write asegs m5 An (xs ++ [Z_to_bv 64 0]) jn vv AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia)) as AARR' end.
      store_done.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
      match goal with H : HM asegs R HIA h4 _ LF m6 |- _ => rename H into HH6 end.
      assert (HW6 : forall a, ~ outside [(An + 4 * jn, An + 4 * jn + 4)] a -> (LHeap = LHeap /\ An <= a < An + 4 * (jn + 1)) \/ lo <= a < bv_unsigned sp - 104).
      { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO N1. lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J5 MU WM MI6 ST6 HH6 HW6
                    ltac:(cbn; split; [clear - Flo SLO2 NEEDR N1; lia| exact I]) ltac:(cbn; split; [clear - FXS N1; lia| exact I]) AARR'
                    ltac:(rewrite upd_length; reflexivity)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      (* [comment removed for export] *)
      zstep. ubchk. zstep. zstep. zstep. zstep. zstep.
      eapply aa_ret; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| left; split; [reflexivity| split; [| reflexivity]]| |].
      * unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_upd by (rewrite length_app; cbn [length]; clear - LEN1 N1; lia).
        rewrite (limb32_w32_nth _ _ _ NTH).
        change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1))) mod 2 ^ 32)
          with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1)))).
        rewrite w32_incr. unfold w32. rewrite (unsigned_lit 0) by (clear; lia).
        change ((0 mod 2 ^ 32 + 1) mod 2 ^ 32) with 1. change (0 mod 2 ^ 32) with 0.
        rewrite limbs_val_app. cbn [limbs_val]. rewrite ?(unsigned_lit 0) by (clear; lia). change (0 mod 2 ^ 32) with 0.
        replace (Z.of_nat (Z.to_nat jn)) with jn by (clear - N1; lia). rewrite LEN1. clear - HVV. lia.
      * unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      * unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: match goal with |- ?g => idtac "G2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01O0@C11264064775.182D33619324555.181D8561475640.181 K10699400504.182K46334092739.182K65977458927.182L10688772806.16 L11030354103.6  L12515801992.3  L13604857769.4  L14518907549.3  L14948330784.178L15198982830.3  L15663651505.3  L15840915687.5  L20859654516.1  L27742581695.6  L29526146055.2  L2970692150.2   L29763661393.2  L29765672786.164L29765672786.166L32076862224.4  L35663928186.7  L39188636933.0  L41074412576.166L41074420074.169L41074717970.178L41416003690.6  L42470618843.183L42633816569.1  L42657875443.1  L43092657406.3  L44015168660.3  L45116040325.165L45116040325.167L46323497533.3  L51267807018.15 L5554128658.1   L55715400192.167L56872727135.122L5775036390.2   L57930138456.3  L5800431574.6   L58609956177.2  L58636003124.1  L59308628179.5  L59308925409.122L59308925409.129L59308975210.7  L59310648043.7  L60098763854.3  L61553859661.6  L61827434946.164L61827434946.166L64826979730.11 L65528204888.4  L65971322641.3  L67417882581.7  L8328083279.7   L9570690066.2   P46334092739.182Q11801279589.181Q20962640553.174Q20964724257.179Q24418818504.169Q24418818504.171Q24419214967.168Q24419214967.170Q26207754346.168Q26207754346.170Q26295627581.174Q29203131547.168Q29203131547.170Q31653749955.168Q31653749955.170Q32494403506.171Q33606497915.176Q33619063430.177Q33621337227.181Q36081244985.169Q36081244985.171Q42766971027.169Q42766971027.171Q50458135125.174Q56512145356.169Q56512145356.171Q60196163333.180Q61218916524.174Q8561220661.177 Q8563657272.181 Q8565397704.176 Q8565759041.174 Q8565809916.171 Q8943627034.171 00000100c01R02M02N03703803>03G03R03Z03[03d03m04704:04F04M04T04[05:05[05f06;06<07007d08`08a09@09E09H09P09Q0:=0:k0:l0;B0;E0;b0<T0<[0<c0=60==0=@0=K0=k0>d0?30?J0?T0?g0@S0AA0Ah0B30B40BI0B]0Bc0Bd0C;0CY0D70DH0D[0Dl0E?0EP0Ec0F40FE0FX0Fi0G<0GZ0H80HV0I60IG0IZ0I[0I\0J10J`0KQ0Km0LK0Lf0MC0M^0N90NT0NeFS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR1w2P02JM2K0S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR1w2P02JMS1R2sp3xs02lo4SLO21k2xs3pXc1N1J2Hk5NEEDR3LOS3ALO1w2N12PC2K0FS1X3xs01k2xs3pXc1N1J2Hk2HJ1w2N13XPc2JM2K0FS1J2GTS1w2WR2NZS1N1J2HJ2K0S1N1J2HJFS1R1X3XALS1w2WR2KBS1k1N1J2HkS1JS2xs1J3HVV1wS3pXc1JS3pXc1NS1N3NR1S2ra2sp1X3xs02xs3pXc1N1J2Hk3NR1S2ra2sp1X3xs01k2xs3pXc1N1J2Hk3NR1S1N1J2HJ2K0S1R3HIA1h2sp2lo3TOP1HSS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P472JM2K0S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P472JM2K0S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR1w2N12P03P472JM2K02WRSS2ra2sp1X3xs01k2xs3pXc1N1J2Hk1wS3pXcS1JS1N1J2HJSS2ra2sp1X3xs02xs3pXc1N1J2Hk2HJ2X03SPR2P03P47S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P47FS2dA2dB1v1N1J2HJ2BV2JMS1JS2ra2sp1X3xs01k2xs3pXc1N1J2HkS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR4XPAL2P02JMS3pXc1JS1N1J2HJS2xs1N1J2HJ4LEN12K0S1N3NR1S1JS1N1J2Hk2K0S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2UBS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2X03SPR1w2N12P03P472K02WR2UBS2xs1J2VN2VM2PGS2xs1N1J2HJ4LEN12K03NTHS1R2lo3LOSS2xs1N1J2HJ4LEN12K0S2ra2sp1X3xs02xs3pXc1N1J2Hk2HJ2X03SPR2P03P47S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P47S1R2sp2lo4SLO23pXc1N1J2HJ5NEEDR4XLSc2K0S1d2D01f2BFFS1X3pXc1N1J2HJ3XPc2K0S3pXc1N1J2HJ2K01a2NOS1N2K1FS3xs01k2xs3pXc1N1J2Hk1wS3xs01k2xs3pXc1N1J2Hk2HJ2P02JMS3xs01k2xs3pXc1N1J2Hk2HJ2P02JMS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ1w2JM2K0S1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkFFS3xs01k2xs3pXc1N1J2HkS2ra2sp1X3xs02xs3pXc1N1J2Hk2HJ2X03XAL3SPR2P02JMS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03XAL3SPR2P02JMS3xs01k2xs3pXc1N1J2Hk3P472K0S3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs3pXc1N1J2Hk2HJ1w2JMS3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs1N1J2Hk". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_LOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pk,$61.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.PN,$8.PJ,$8.Pr2,(3.&40.)Pr10,(3.&40.)Pr24,(3.&40.)Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs5,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(22.(26.R17.R16.)(62.R1?.))P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1?.R1>.R1=.R1<.R1;.(48.VX,+1.R18.R19.R1:.VpadX,$1:.))P,(22.R19.(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(32.(22.+1.R19.)(22.R19.R1:.))P,(10.$8.(23.(55.R1=.)(60.+2.(1<.+20.R1:.)))$4>.)P,(22.R23.$57.)P,(22.R23.$58.)P,(10.(3.&40.)R1<.(29.&40.(26.R1=.+1.)))P,(10.(3.&40.)R1<.(29.&40.(26.(23.R20.(1<.+4.R1>.))+4.)))P,(10.(3.&40.)R1<.(29.&40.(1<.+4.R1?.)))(51.$47.(52.$47.VR,VHIA,R26.Vmo,)$53.(43.(44.R1<.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1;.R1:.R19.(29.&40.VX,)(29.&40.(23.VX,+:.))R1>.R18.R17.R16.R15.R14.R13.R12.R1?.R11.(29.&40.-5.)R10.(29.&40.(59.(2=.VR,)))R1=.(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(23.(5:.VX,+3.)(59.(2=.VR,))))(29.&40.+270>.)R?.R>.R=.R<.R;.)VF,(29.&40.+9>274.)Vfc,(45.(3.&40.))R24.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 NGX HJ HVV BV BF -> -> ->.
    all: jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
         cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    all: basic_factsA hc.
    all: pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    all: pose proof J0 as JX; xa_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47); clear OWN0 OWN1.
    all: pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc; unfold mpi_cells in CX1.
    all: pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    all: assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    all: pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    all: pose proof (munch_refl [(pXc + 4 * J, pXc + 4 * J + 4)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    all: assert (E10 : Z.shiftr (X + 10) 3 + al_sb AL = Z.shiftr X 3 + al_sb AL + 1)
           by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - XAL; lia).
    (* [comment removed for export] *)
    all: assert (JM : J <= aaM) by
      (pose proof (limbs_val_nonneg xs) as VN; pose proof VALM as VM; rewrite <- HVV in VM;
       destruct (Z_le_gt_dec J aaM) as [|GT]; [assumption| exfalso];
       assert (PG : 2 ^ (32 * (aaM + 1)) <= 2 ^ (32 * J)) by (apply Z.pow_le_mono_r; clear - GT HJ; lia); clear - PG VN VM; lia).
    (* [comment removed for export] *)
    all: rewrite E10; zstep; zstep; zstep.
    all: replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    (* [comment removed for export] *)
    all: zstep; try replace (Z_to_bv 64 (J - 1 + 1)) with (Z_to_bv 64 J) by (f_equal; clear; lia).
    all: zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - NR1 HJ; lia).
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *) eapply aa_retm16; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
      zstep. try replace (Z_to_bv 64 (J - 1 + 2)) with (Z_to_bv 64 (J + 1)) by (f_equal; clear; lia).
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      rewrite <- E10. eapply aa_G2; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - K1; lia| exact JM| exact HVV| exact BV| exact BF].
    - (* [comment removed for export] *) exfalso. clear - K0 Hk HJ. lia.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *) eapply aa_retm16; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
      zstep. try replace (Z_to_bv 64 (J - 1 + 2)) with (Z_to_bv 64 (J + 1)) by (f_equal; clear; lia).
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      rewrite <- E10. eapply aa_G2; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - K1; lia| exact JM| exact HVV| exact BV| exact BF].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 (pXc + 4 * J - 4 + 4)) with (Z_to_bv 64 (pXc + 4 * J)) by (f_equal; clear; lia).
      (* [comment removed for export] *)
      zstep. zstep. ubchk. zstep. zstep. shadow_chk OP (pXc + 4 * J) 4.
      (* [comment removed for export] *)
      destruct (nth_error xs (Z.to_nat J)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 K0 HJ; lia].
      pose proof (u32arr_read asegs mc pXc xs J w _ XARR NTH ltac:(clear - HJ; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      (* [comment removed for export] *)
      zstep.
      assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
        by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
      pose proof (u32arr_store_ok asegs mc pXc xs J _ XARR ltac:(clear - HJ K0 LEN1; lia) ltac:(f_equal; clear; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
        pose proof (u32arr_write asegs mc pXc xs J vv XARR ltac:(clear - HJ K0 LEN1; lia)) as XARR' end.
      store_done.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
      match goal with H : HM asegs R HIA hc _ LF m6 |- _ => rename H into HH6 end.
      assert (HW6 : forall a, ~ outside [(pXc + 4 * J, pXc + 4 * J + 4)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
      { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO HJ K0. lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6 HH6 HW6
                    ltac:(cbn; split; [clear - XLSc SLO2 NEEDR HJ K0; lia| exact I]) ltac:(cbn; split; [clear - XPc HJ K0; lia| exact I]) XARR'
                    ltac:(rewrite upd_length; reflexivity)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      pose proof (limb32_w32_nth xs (Z.to_nat J) w NTH) as LW. pose proof (w32_range w) as WR.
      assert (LVU : limbs_val (upd xs (Z.to_nat J) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                    = limbs_val xs + 2 ^ (32 * J) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
      { rewrite limbs_val_upd by (clear - HJ K0 LEN1; lia).
        change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))) mod 2 ^ 32) with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
        rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat J)) with J by (clear - HJ; lia). reflexivity. }
      (* [comment removed for export] *)
      zstep. ubchk. zstep. zstep. zstep. zstep. if_cases KB; zify_cond KB; rewrite incr_mod64 in KB.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_zero_iff _ ltac:(clear; apply Z.mod_pos_bound; lia))) in KB.
        rewrite <- E10. eapply (IH _ _ _ _ _ _ _ N (J + 1)); [clear - Hk K0; lia| exact J6| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - HJ K0; lia| | exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia].
        rewrite LVU, KB. replace (32 * (J + 1)) with (32 * J + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
        assert (w32 w = 2 ^ 32 - 1) by (clear - KB WR; lia). clear - HVV H. nia.
      + (* [comment removed for export] *)
        assert (NZ : (w32 w + 1) mod 2 ^ 32 <> 0) by (intros E; apply KB; rewrite E; reflexivity).
        zstep.
        eapply aa_ret; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| | clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia].
        left. split; [reflexivity|]. split; [| reflexivity].
        unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR NZ; lia). clear - HVV. lia.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@C11264064775.178D16239083480.177D33619324555.177K10699400504.178K46334092739.178K65977458927.178L10688244390.16 L10870553235.5  L12513621947.3  L12609438262.173L12609438262.174L12616134508.2  L13015518834.1  L14948330784.177L15661554330.3  L16539540349.3  L17027684244.1  L24178789648.3  L27742581695.6  L2970692150.2   L35663928186.7  L41074406303.162L41074420074.165L41074717970.177L41416003690.6  L41652918740.1  L42468637902.178L42468653803.180L42633816569.1  L43021235637.5  L44015168660.3  L45272757598.3  L46158395431.178L46322969181.3  L46950334807.6  L51267807018.15 L55715400192.163L56872727135.119L59308925409.119L59308925409.127L59308975210.7  L59310648043.6  L60098763854.3  L6027026214.2   L60326389651.5  L62785188115.3  L64814171975.10 L65071520974.5  L65528204888.4  L65971842929.3  L67416084352.6  L67663008344.3  L8328083279.6   P46334092739.178Q11801279589.177Q16226608033.170Q16226640547.167Q16237098456.177Q18928692618.172Q18941258103.173Q26295627581.170Q32494403597.167Q33621337227.177Q50458135125.170Q54682954785.173Q54687164636.172Q60196163333.176Q61218916524.170Q7974808257.175 Q7981049417.170 Q8943604901.167 00000100[01E02;02<02]02^02k03503K03a03h03k03l04604>04A04F04R04Y04n05Z06F07:07;07>07V07n08308C08D08L08k08l09209H09^0:K0:d0;X0;g0<;0<E0<L0<]0<e0=I0=Y0=d0=e0>70>?0>P0>Q0>a0?70?M0?e0@;0@Q0@[0A10AI0AW0Am0BC0BZ0C00CI0Cb0ClFS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR1w2P02JMS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR1w2P02JMS1R2sp3xs02lo4SLO22xs3pXc1N1j2HJ5NEEDR3LOS3ALO1w2N12PCFS1X3xs02xs3pXc1N1j2HJ1w2N13XPc2JMFS1w3SZ22SR2KBS1w2WR3KB'S2ra2sp1X3xs02xs3pXc1jS2ra2sp1X3xs02xs3pXc1jS3pXc1jS1jFS1w2WR3KB'S1N1j2HJS1jS1N1jS2xs1j3HVV1wS3pXc1NS1R3HIA1h2sp2lo3TOP1HS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR2P03P472JMS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR2P03P472JMS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR1w2N12P03P472JM2WRSS1jS2ra2sp1X3xs02xs3pXc1j1wS2ra2sp1X3xs02xs3pXc1j1wS3pXcS2xs1N1j2HJ4LEN1SS1N1j2HJS2ra2sp1X3xs02xs3pXc1j2X03X161wFS1j2GTS2dA2dB1v1N1j2HJ2BV2JMS2ra2sp1X3xs02xs3pXc1jS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR4XPAL2P02JMS2ra2sp1X3xs02xs3pXc1j2UBS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR1w2N12P03P472WR2UBS2xs1j2VN2VM2PGS2xs1N1j2HJ4LEN13NTHS1R2lo3LOSS3pXc1jS1w3SZ13SZ22SR2KBS1N1j2HJS1R2sp2lo4SLO23pXc1N1j2HJ5NEEDR4XLScS2xs1N1j2HJ4LEN1S1d2D01f2BFFS1X3pXc1N1j2HJ3XPcS1N1j2HJS3pXc1N1j2HJ1a2NOFS3xs02xs3pXc1j1wS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ1w2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs1jS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ1w2JMS3xs02xs3pXc1jS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ3P47S3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2P02JMS3xs02xs3pXc1N1j2HJ2P02JMS3xs02xs1j". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_ITER1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.PN,$8.Pj,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1<.R1;.R1:.R19.R18.(48.VX,+1.R15.R16.R17.VpadX,$1:.))P,(22.R16.(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(32.(22.+1.R16.)(33.R16.R17.))P,(10.$8.(23.(55.R1:.)(60.+2.(1<.+20.R17.)))$4>.)P,(22.R20.$57.)P,(22.R20.$58.)(51.$47.(52.$47.VR,VHIA,R20.Vmo,)$53.(43.(44.R19.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R18.R17.R16.(29.&40.VX,)(29.&40.(23.VX,+:.))R15.R14.(29.&40.+1.)R13.R12.R11.R10.R?.(29.&40.R1:.)R>.R=.(29.&40.R1<.)(29.&40.(59.(2=.VR,)))(29.&40.(23.(1<.+4.R1:.)+4.))(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(23.(5:.VX,+3.)(59.(2=.VR,))))R<.R;.R:.R9.R8.R7.)VF,(29.&40.+9>224.)Vfc,(45.(3.&40.))R1>.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX HJ HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J0 as JX; xa_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47); clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc; unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl [(pXc + 4 * j, pXc + 4 * j + 4)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (JM : j <= aaM).
    { pose proof (limbs_val_nonneg xs) as VN; pose proof VALM as VM; rewrite <- HVV in VM.
      destruct (Z_le_gt_dec j aaM) as [|GT]; [assumption| exfalso].
      assert (PG : 2 ^ (32 * (aaM + 1)) <= 2 ^ (32 * j)) by (apply Z.pow_le_mono_r; clear - GT HJ; lia). clear - PG VN VM; lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (Z_to_bv 64 (pXc + (4 * j + 4) + -4)) with (Z_to_bv 64 (pXc + 4 * j)) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. ubchk. zstep.
    try replace (Z_to_bv 64 (pXc + (4 * j + 4) + -4)) with (Z_to_bv 64 (pXc + 4 * j)) by (f_equal; clear; lia).
    zstep. zstep. shadow_chk OP (pXc + 4 * j) 4.
    (* [comment removed for export] *)
    destruct (nth_error xs (Z.to_nat j)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 HJ; lia].
    pose proof (u32arr_read asegs mc pXc xs j w _ XARR NTH ltac:(clear - HJ; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. zstep.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof (u32arr_store_ok asegs mc pXc xs j _ XARR ltac:(clear - HJ LEN1; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mc pXc xs j vv XARR ltac:(clear - HJ LEN1; lia)) as XARR' end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
    match goal with H : HM asegs R HIA hc _ LF m6 |- _ => rename H into HH6 end.
    assert (HW6 : forall a, ~ outside [(pXc + 4 * j, pXc + 4 * j + 4)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
    { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO HJ. lia. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6 HH6 HW6
                  ltac:(cbn; split; [clear - XLSc SLO2 NEEDR HJ; lia| exact I]) ltac:(cbn; split; [clear - XPc HJ; lia| exact I]) XARR'
                  ltac:(rewrite upd_length; reflexivity)) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    pose proof (limb32_w32_nth xs (Z.to_nat j) w NTH) as LW. pose proof (w32_range w) as WR.
    assert (LVU : limbs_val (upd xs (Z.to_nat j) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                  = limbs_val xs + 2 ^ (32 * j) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
    { rewrite limbs_val_upd by (clear - HJ LEN1; lia).
      change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))) mod 2 ^ 32) with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
      rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat j)) with j by (clear - HJ; lia). reflexivity. }
    (* [comment removed for export] *)
    pose proof (sxz_zero_iff ((w32 w + 1) mod 2 ^ 32) ltac:(apply Z.mod_pos_bound; lia)) as [SZ1 SZ2].
    pose proof (sxz_range ((w32 w + 1) mod 2 ^ 32) ltac:(apply Z.mod_pos_bound; lia)) as SR.
    zstep. ubchk. zstep. if_cases KB; zify_cond KB; rewrite ?incr_mod64 in KB.
    - (* [comment removed for export] *)
      assert (KB' : (w32 w + 1) mod 2 ^ 32 <> 0) by (clear - KB SZ1 SZ2 SR; lia).
      eapply aa_ret0; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| | reflexivity| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR KB'; lia). clear - HVV. lia.
    - (* [comment removed for export] *)
      assert (KB' : (w32 w + 1) mod 2 ^ 32 = 0) by (clear - KB SZ1 SZ2 SR; lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      eapply (aa_LOOP (Z.to_nat (N - (j + 1))) _ _ _ _ _ _ _ N (j + 1));
        [clear - HJ; lia| exact J6| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - HJ; lia| | exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia].
      rewrite LVU. replace (32 * (j + 1)) with (32 * j + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
      assert (w32 w = 2 ^ 32 - 1) by (clear - KB' WR; lia). assert ((w32 w + 1) mod 2 ^ 32 = 0) by (rewrite H; reflexivity). clear - HVV H H0. nia.
    all: match goal with |- ?g => idtac "ITER1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11001467780.163L22550422114.3  L22704838960.4  L29763661393.2  L29765672786.163L32954672962.163L35907725488.163L35963164448.5  L46160487540.163L46965806005.163L48155193844.163L51267939251.14 L51267939251.15 L55345850227.163L55784711535.5  L58609956177.2  L59308925409.120L60208222901.4  L65528204888.4  L9570690066.3   Q26207421841.165Q26207721832.166Q26207967338.163Q31654082872.165Q39212284437.166Q43925228937.166Q60511567613.166Q60697995187.166Q8880503606.163 Q9538787269.163 00000_00h01301:01V02B02n03803U03V04?04S04i05D05P05W06B06M06X06b06n07:07F07R07^07j08408C08O08YS2ra2sp1X3xs02xs3pXc1N1j2HJ2JM2X03SPR2N12P03P47S1c2HC2KCS1N1j2HJ2K0S1N3NR1S2ra2sp1X3xs02xs3pXc1N1j3NR1S2ra2sp1X3xs02xs3pXc1N1j2HJ2JM2X03SPR2P03P47S2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR2N12P03P47S2xs1j3HVVS2ra2sp1X3xs02xs3pXc1j2X03X16FS2ra2sp1X3xs02xs3pXc1N1j2X03SPR2N12P03P47S2dA2dB1v1N2JM2HJ2BVS2dA2dB1v1N1j2HJ2JM2BVS2ra2sp1X3xs02xs3pXc1j1c2HCS2xs1j3HVV1NS1N3NR1S2ra2sp1X3xs02xs3pXc1N1j2HJ2JM2X03SPR2P02UBS1N1j2HJ2K0S1d2D01f2BFS1N3NR12K1S1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS3xs02xs1jS1X3xs02xs1j2X0S1X3xs02xs1jS3xs02xs1j". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_FIRST : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.PN,$8.Pj,$8.Pc,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1<.R1;.R1:.R19.R18.(48.VX,+1.R15.R16.R17.VpadX,$1:.))P,(22.R16.(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(32.(22.+1.R16.)(22.R16.R17.))P,(32.(22.=R16.)(22.R16.+1.))P,(22.R18.$5=.)P,(10.$8.(23.(55.R1<.)(1<.R18.(60.+2.(1<.+20.R19.))))$4>.)P,(22.R22.$57.)P,(22.R22.$58.)(51.$47.(52.$47.VR,VHIA,R22.Vmo,)$53.(43.(44.R1:.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R19.R18.R17.(29.&40.VX,)(29.&40.(23.VX,+:.))(29.&40.R1;.)R16.R15.R14.R13.R12.R11.R10.(29.&40.R1<.)(29.&40.(23.R1<.+1.))R?.(29.&40.R1>.)(29.&40.(59.(2=.VR,)))(29.&40.(23.(1<.+4.R1<.)+4.))(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(23.(5:.VX,+3.)(59.(2=.VR,))))R>.R=.R<.R;.R:.R9.)VF,(29.&40.+9>14<.)Vfc,(45.(3.&40.))R20.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX HJ HC JM HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J0 as JX; xa_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47); clear OWN0 OWN1.
    unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ubchk. zstep. ubchk. zstep. zstep. zstep. zstep. ubchk.
    zstep. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by (clear - HC; lia).
    { eapply aa_ret0; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| | reflexivity| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite KC in HVV. clear - HVV. lia. }
    assert (EC : c = 1) by (clear - KC HC; lia). subst c. clear KC HC.
    (* [comment removed for export] *)
    shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - NR1 HJ; lia).
    { (* [comment removed for export] *)
      eapply aa_ITER1; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - K0 HJ; lia| clear - HVV; lia| exact BV| exact BF]. }
    assert (EJ : j = N) by (clear - K0 HJ; lia). subst j.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      eapply aa_retm16; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
    (* [comment removed for export] *)
    eapply aa_G3; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - K1 NR1; lia| exact JM| clear - HVV; lia| exact BV| exact BF].
    all: match goal with |- ?g => idtac "FIRST-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L15528730518.60L45272754978.60L59549403627.60L9132507695.60 00000J00_01401IS2ra2xs3xs'2zs1j1c4Hlen2HvS2ra2xs3xs'1j2Hj4HlenS2ra2xs3xs'1j2Hl4HlenS2ra2xs3xs'1j2Hl4Hlen". (* [comment removed for export] *)
  #[using="ra dA dB"] Lemma limbs_val_core_addA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pxs,(1.(3.&40.))Pxs',(1.(3.&40.))Pzs,(1.(3.&40.))Pj,$8.Pc,$8.P,(22.=R2.)P,(22.R3.(62.(63.(3.&40.)R6.)))P,(10.$61.(63.(3.&40.)R6.)(63.(3.&40.)R7.))P,(10.(1.(3.&40.))(64.(3.&40.)(65.R5.)R7.)(64.(3.&40.)(65.R5.)R8.))P,(10.$8.(23.(66.R8.R6.)(1<.R5.(60.+2.(1<.+20.R6.))))(23.(66.R9.R6.)(66.R7.R6.)))(10.$8.(23.(55.R9.)(1<.R6.(60.+2.(1<.+20.R7.))))(23.(55.R:.)(66.R8.R7.)))")
(* [comment removed for export] *).
  Proof.
    intros xs xs' zs j c Hj Hl Hlen Hs Hv.
    rewrite (limbs_val_split xs j), (limbs_val_split xs' j) by lia. rewrite Hs. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition opnd2A (dE : mpd) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop :=
    (JBE dE /\ BJE dE hc LBc mc dXc) \/ dE = dXc.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02I0@C24112444547.204D24502936410.204D30202740417.204D30213615715.208D42633159082.204D42643779336.208D62012212072.208D64065028362.208D66314653779.208D7230003330.204 K11420089551.204K28284592895.202K28284592895.203K28441636224.205K36247032466.206K3664959506.206 K45908760803.207K45908760803.209K48349884702.202K48349884702.203K61717199003.205L10307112399.6  L11379748202.3  L11416546478.3  L14183750181.16 L14183782691.14 L14534815260.8  L15477852824.1  L16399517397.15 L16399549907.16 L20343950113.0  L23100341967.183L23643762344.6  L23846304344.7  L2617640871.5   L26502719108.5  L2695949673.2   L27155623132.7  L27158027645.13 L27158060667.12 L28029610798.11 L28270437390.4  L28452252428.2  L29525427416.7  L29527684735.11 L29527717241.13 L2975768925.2   L33908884245.1  L35663928186.7  L36248605795.16 L3667582691.3   L36721400998.11 L36721500064.13 L38235734261.1  L39463202031.1  L41117966897.183L41128898453.2  L42633816569.1  L43878034250.5  L45272757598.3  L45558987916.9  L45913639042.4  L45916029979.4  L47401054516.1  L47797436189.12 L48338281339.2  L49206922459.2  L53336534921.12 L53351395297.8  L53351542265.8  L5865530840.11  L59310763475.6  L59378981895.1  L59549313838.11 L59553535406.5  L59824495762.8  L59824839701.8  L59826908467.16 L59827007029.14 L60098763854.3  L60283674290.11 L60451539393.3  L6141606276.1   L61711433322.3  L64201493914.6  L64714233749.10 L64720328165.8  L65349212151.12 L65351099990.5  L65351280337.6  L66151427842.16 L66151427842.17 L6880072876.14  L8906764216.6   L9832141279.10  O14737164687.206O24112444547.204O27573497883.202O27573497883.203O35105909750.205O43419437345.205O43841349487.207O43841349487.209O44282969958.206O48319976166.206O54539614568.202O54539614568.203P11385514907.206P11420089551.204P28441636224.205P45908760803.207P45908760803.209P48349884702.202P48349884702.203Q12370813529.191Q1334646057.213 Q15148415212.191Q17207432298.190Q18347242623.212Q18468912438.213Q23773721554.210Q23773721554.211Q23773721554.212Q30213615715.213Q3477013320.190 Q36708691079.213Q37323683587.191Q37625261960.190Q39314530340.191Q41888233245.213Q42643779336.213Q4511369453.191 Q46978751216.191Q46978803023.190Q47588311916.209Q47588311916.210Q47588311916.211Q47588311916.212Q5485126037.190 Q5485174314.191 Q59703481013.191Q6143569392.191 Q61889752670.211Q61889752670.212Q62701122256.190Q64065028362.213Q64443693026.191Q64835987202.191Q66314653779.213Q9827600259.209 Q9827600259.210 Q9827600259.211 Q9827600259.212 00000101?02E03A03j04G04f04g04h06706806g07V07W08Q09K09L09M09N09O0:K0:_0:`0:a0:b0:c0:d0:h0:i0:j0:k0;H0;Z0<40<@0<T0<U0<V0<W0<X0<m0<n0<o0=00=10=20=90==0=R0=S0=T0=U0=V0=Z0=^0>;0><0>A0>H0>P0>h0>i0>j0>n0>o0?00?10?20?P0?Q0?c0@80@<0@O0@_0@`0@a0@b0@c0@m0AQ0A[0A_0A`0Am0BT0BU0BV0Bb0Bc0CC0CD0CH0C\0D@0DA0DB0DC0DD0DE0DF0DG0DH0DI0DJ0DK0DL0DM0DN0DO0DP0DQ0DR0DS0E70E80El0F90F:0F;0F<0F=0F>0FZ0Fh0Fi0GX0Ge0Gf0Gg0H60H70HE0HS0HT0HU0HV0HW0Hd0I10I20I?0I@0IA0IO0IP0I^0I_0I`0Ia0Ib0Ic0IdFS1R3HIA1h2ra2sp1X3xs02Ea2pE1j2hc3pXc2xs2zs3TOP2X03SPR3EP03E0'3HT12P04xs6l4LEN6S2ra2sp1X3xs02Ea2pE1j1N3pXc2xs2zs2HJ2JM2X03SPR3EP03E0'2N12P04xs6l4LEN6S2ra2sp1X3xs02Ea2pE1j1N3pXc2xs2zs2HJ2JM2X03SPR3EP03E0'2N12P0S2ra2sp1X3xs02Ea2pE1j3pXc2xs2zs4xs6l4LEN6S2ra2sp1X3xs02Ea2pE3pXc2xs2zsS1R2ra2sp1X3xs02Ea2pE3pXc2xs2zsFFS1R2ra2sp1X3xs02lo4SLO22Ea2pE1j3pXc2xs2zs5NEEDR3LOS2X03SPR3EP03E0'2P04xs6l4LEN6FS1R2sp3xs02lo1j1N3pXc2xs2zs2HJ2JM3LOS3ALO2N12PCS1R2sp3xs02lo1j1N3pXc2xs2zs2HJ2JM3LOS3ALO2N12PCFS1R2sp3xs02lo4SLO21j1N3pXc2xs2zs2HJ2JM5NEEDR3LOS3ALO2N12PCS1R2sp3xs02lo4SLO21j1N3pXc2xs2zs2HJ2JM5NEEDR3LOS3ALO2N12PCFFFFS2sp1X3xs02lo1j1N3pXc2xs2zs2HJ2JM3x142N13XPc2x23x153x164POSTS1R2sp2lo4SLO25NEEDRFFFFFS2spFFSS2ra2sp1X3xs02Ea2pE3pXc2xs2zsS1X1j1N3pXc2HJ3XPcS1R2sp1X2lo4SLO25NEEDR3DSXS1j1N3pXc2HJS1R2sp2lo4SLO25NEEDRFFFFS2nE1j2xs2zs3HJE4LENZFFFFFS1N3pXcS2spS1R3HIA1h2sp2lo3TOP1HFFFFS2loS2spS2ra2sp1X3xs02Ea2pE3pXc2xs2zsFS3pXcS2sp2loS1j1N2HJS1j2xs2zs3HVV1c4xs6l3LVCFFS2spFFFFS1R2sp2lo4SLO22pE2zs5NEEDR3ESKFS1j1N2xs2zs2HJ3NR1S2dE1j3dXc2HJ3HJE3EZ0S2pES1j1N2xs2zs2HJ4LEN1S1j1N2xs2HJ4LEN1FFFFS1R2lo3LOSS1R2sp2lo4SLO21j1N3pXc2HJ5NEEDR1a2NOS2dE3dXc1HS2spFS2nE2pE1j3HJES1R2sp2lo4SLO21N3pXc2xs5NEEDR4LEN14XLScFFS2sp3SPA3SPRFS3dXc2r04XPAL1q1r1H2H02q02H43pXcFS2spS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO21j1N3pXc2HJ5NEEDR4XLScFFFFFFFFFFFFFFFFFFFS2ra2sp1X3xs02Ea2pE3pXc2xs2zs2X03XALFS2ra2sp1X3xs02Ea2pE3pXc2xs2zs2X03SPR3EP03E0'4EAL'2P0S1X3xs02xs2zsFFFFFS3xs01j1N3pXc2xs2zs2HJ2JM2N1S3xs02Ea2xs2zsFS1R2sp3xs02lo4SLO22xs2zs5NEEDR3LOS4SP643ALO3ACPS1X3xs02xs2zsFFS3xs03pXc2xs2zsFS3xs02Ea2xs2zsS3xs02Ea2xs2zsFFFFS1X3xs02xs2zsS1X3xs02xs2zsFS1X3xs02xs2zsFFS3xs02Ea2xs2zsFS3xs02Ea2xs2zsFFFFFF". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_CALL : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "PdE,$7.Pj,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs5,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R18.R17.R16.R15.R14.R13.)P,(22.(1=.R14.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(67.R1<.R18.R17.R16.R15.)P,(10.$11.(12.R16.)$1:.)P,(32.(22.+1.R1=.)(22.R1=.(1=.R17.)))P,(22.R1>.(1=.R1?.))P,(22.R1?.$5=.)P,(10.$8.(4?.R1:.)+1.)P,(10.$8.(23.(55.(56.R1;.))(66.(56.R22.)R21.))$4>.)P,(22.R21.$57.)P,(22.R21.$58.)(51.$47.(52.$47.VR,VHIA,R21.Vmo,)$53.(43.(44.R1=.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1<.R1;.R1:.(29.&40.VX,)(29.&40.(23.VX,+:.))R19.R18.R17.R16.R15.R14.R13.R12.(29.&40.R24.)(29.&40.(23.R24.+1.))(29.&40.(19.R25.))R11.(29.&40.(59.(2=.VR,)))(29.&40.(23.(1<.+4.R24.)+4.))(29.&40.(23.(5:.(23.VX,+:.)+3.)(59.(2=.VR,))))(29.&40.(5:.VX,+3.))(29.&40.(23.(5:.(19.R25.)+3.)(59.(2=.VR,))))R10.R?.R>.R=.R<.)VF,(29.&40.+9>120.)Vfc,(45.(3.&40.))R1?.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX OPD EO HJ HJE JM SG1 HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    (* [comment removed for export] *)
    assert (EF : exists zs, md_limbs dE = zs /\ bytes_at asegs mc (md_p dE) (u32s zs) /\ Z.of_nat (length zs) = md_n dE
                 /\ ((md_p dE = md_p dXc /\ zs = md_limbs dXc) \/ md_p dE + 4 * Z.of_nat (length zs) <= md_p dXc \/ md_p dXc + 4 * Z.of_nat (length (md_limbs dXc)) <= md_p dE)
                 /\ md_p dE mod 4 = 0 /\ 0 < md_p dE /\ (md_p dE + 4 * Z.of_nat (length zs) <= lo \/ bv_unsigned sp <= md_p dE)
                 /\ rw_cells asegs mc (md_addr dE) (mpi_cells (md_p dE) (Z_to_bv 64 (md_sg dE)) (md_n dE) (md_pad dE))
                 /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dE) 16
                 /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_p dE) (4 * md_n dE)
                 /\ 0 < md_addr dE /\ md_addr dE + 16 <= 2 ^ 64 /\ md_addr dE mod 8 = 0 /\ (md_addr dE + 16 <= lo \/ bv_unsigned sp <= md_addr dE)).
    { ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
      destruct OPD as [[DBJ B]| ->].
      - pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
        assert (EN : md_own dE <> LNull) by (intros C; destruct (OWNE0 C) as [_ EZ0]; clear - HJ HJE EZ0; lia).
        ddestruct (OWNE1 EN) as (_ & EP0 & EPAL & EBY & ESK & _).
        pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B)) as [(CE & _) _].
        exists (md_limbs dE). split; [reflexivity|]. split; [exact EBY|]. split; [exact LENE|].
        split; [right; rewrite LENE, LEN1; pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B EO EN); clear - H; lia|].
        split; [exact EPAL|]. split; [exact EP0|]. split; [rewrite LENE; exact ESK|]. split; [exact CE|].
        split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)|]. split; [exact (bj_aobjL _ _ _ _ _ _ _ _ _ _ B EN)|].
        split; [exact E0|]. split; [exact E16|]. split; [exact EAL| exact ES].
      - pose proof (xa_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as ADc. pose proof (xa_pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as PDc. rewrite ADc, PDc.
        exists (md_limbs dXc). split; [reflexivity|]. split; [apply u32arr_ro; exact XARR|]. split; [exact LEN1|].
        split; [left; split; reflexivity|]. split; [clear - XPAL; Z.div_mod_to_equations; lia|]. split; [exact P0|].
        split; [rewrite LEN1; exact (xa_XLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0 ltac:(rewrite EO; discriminate))|].
        split; [exact CX1|]. split; [exact (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0)|]. split; [exact OP|].
        split; [exact X0|]. split; [exact X16|]. split; [exact XAL| exact DSX]. }
    ddestruct EF as (zs & EZ & EBY & LENZ & SEPZ & EPAL & EP0 & ESK & CE & OE & OEL & E0' & E16' & EAL' & ES'). rewrite EZ in HVV.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg own.
    destruct dE as [Ea sE nE pE zs0 padE ownE]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst zs0.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1 OPD.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc. unfold mpi_cells in CX1, CE.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * j); (bv_unsigned sp + -112 - MPI_CORE_ADD_STACK_A, bv_unsigned sp + -112)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (A_mpi_core_add_spec AL IMG) as SPC. unfold mpi_core_add_stmtA, A_MPI_CORE_ADD in SPC.
    acallxA_sp (bv_unsigned sp + -112)
      (eapply SPC with (X := pXc) (A := pXc) (B := pE) (n := j) (lo := lo) (xs := xs) (ys := xs) (zs := zs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
       try eassumption; try reflexivity;
       first [ apply u32arr_ro; exact XARR
             | left; split; reflexivity
             | clear - HJ HJE LEN1 LENZ N1 NR1; lia
             | clear - XPAL; Z.div_mod_to_equations; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HJ N1; lia]
             | eapply aobj_sub; [exact OEL| clear; lia| clear - HJ HJE; lia]
             | unfold MPI_CORE_ADD_STACK_A; clear - SLO2 NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
             | unfold MPI_CORE_ADD_STACK_A; left; rewrite LEN1; clear - XLSc SLO2 NEEDR; lia
             | unfold MPI_CORE_ADD_STACK_A; clear - XLSc LEN1 SLO2 NEEDR; lia
             | unfold MPI_CORE_ADD_STACK_A; clear - ESK SLO2 NEEDR; lia
             | match goal with |- ?g => idtac "CADD-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CADD-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned sp + -112) |- _ => rename H into ST6 end.
    match goal with H : u32arr asegs m6 pXc ?l, H2 : length ?l = length xs |- _ => rename H into XARR6; rename H2 into LEN6; rename l into xs6l end.
    match goal with H : lval xs6l j + ?cc * 2 ^ (32 * j) = _, H2 : 0 <= ?cc <= 1, H3 : skipn _ xs6l = _ |- _ => rename H into LV6; rename H2 into HC6; rename H3 into SK6; rename cc into c end.
    (* [comment removed for export] *)
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * j); (bv_unsigned sp + -112 - MPI_CORE_ADD_STACK_A, bv_unsigned sp + -112)] mc m6) in HH6;
      [| exact MU| exact WM| unfold MPI_CORE_ADD_STACK_A; solve_w_writable].
    assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
    { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT. }
    assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * j); (bv_unsigned sp + -112 - MPI_CORE_ADD_STACK_A, bv_unsigned sp + -112)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
    { intros a NO. cbn [outside] in NO. unfold MPI_CORE_ADD_STACK_A in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HJ SLO2 NEEDR; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6
                  ltac:(cbn; unfold MPI_CORE_ADD_STACK_A; split; [clear - XLSc SLO2 NEEDR HJ; lia| split; [clear; lia| exact I]])
                  ltac:(cbn; unfold MPI_CORE_ADD_STACK_A; split; [clear - XPc HJ; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]) XARR6
                  ltac:(exact LEN6)) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    subst x2.
    eapply aa_FIRST; [exact J6| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| exact HJ| exact HC6| exact JM| | exact BV| exact BF].
    pose proof (limbs_val_core_addA xs xs6l zs j c ltac:(clear - HJ; lia) ltac:(clear - HJ LEN1; lia) LEN6 SK6 LV6) as LVC. clear - LVC HVV. lia.
    all: match goal with |- ?g => idtac "CALL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0@L13642871129.5  L14679198811.6  L20447459013.4  L20851361989.6  L27038138034.3  L27243017426.5  L32954672833.164L32954672962.167L36618624197.2  L46160478397.164L46160487540.167L48662239157.5  L51269834902.12 L5260339702.166 L55408706463.3  L58293195749.2  L59308546259.6  L59308628179.4  L65448092613.2  L65450267334.167L65530246509.5  Q26207421841.168Q26207721832.169Q26207774294.166Q31654082872.168Q39212284437.169Q43925228937.169Q60511567613.169Q60697995187.169Q8880817418.166 Q9538464249.166 00000@00R00\00h01101A01i02E02N02f03>03H03X04004904?04R04_04h05=05L05W05b05m06806C06N06W06e070079S2dE1j3dXc2HJ2K0S2dA2dB2dE1j2HJ2EMS1f2BF3F01S2dE1j2HJ2EMS2dE1j2HJS2dE1j3dXc2HJ2K0S2ra2sp1X3xs02dE1j3dXc2HJ2EM2X03SPR4NE10S2ra2sp1X3xs02dE1j3dXc2HJ2K1S3dXc3NR1S2ra2sp1X3xs03dXc2X03X16S2ra2sp1X3xs03dXc2X03X16S1v2BV3V01S2dA2dB1v2BV3V01S2ra2sp1X3xs03dXc2X03X16S2dE1j2HJS1d2D0S2dE1j3dXc2HJ2K02N0S1j3dXc2HJ2K0S3dXc3NR1S2ra2sp1X3xs03dXc3NR1S1d2D01f2BF3F01S1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS3xs03dXcS1X3xs03dXc2X0S1X3xs03dXcS3xs03dXc". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_J1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "PdE,$7.Pj,$8.Pvv,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs5,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1<.R1;.R1:.R19.R18.R17.)P,(22.(1=.R18.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(67.R21.R1<.R1;.R1:.R19.)P,(32.(22.+1.R21.)(22.R21.(1=.R22.)))P,(22.(1=.R23.)$5=.)P,(10.$8.(4?.R1<.)+1.)P,(10.$8.(55.(56.R1=.))R23.)P,(10.$8.(23.R24.(66.(56.R26.)R25.))$4>.)P,(22.R24.$5>.)P,(22.R24.$5?.)(51.$47.(52.$47.VR,VHIA,R24.Vmo,)$53.(43.(44.R20.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1?.R1>.R1=.(29.&40.VX,)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.(29.&40.(23.R28.+1.))(29.&40.(19.R29.))R12.(29.&40.(59.(2=.VR,)))(29.&40.(23.(1<.+4.R28.)+4.))R11.R10.(29.&40.(23.(5:.(19.R29.)+3.)(59.(2=.VR,))))R?.R>.R=.R<.R;.)VF,(29.&40.+9>06<.)Vfc,(45.(3.&40.))R22.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX OPD HJ EM SG1 HVv HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX1.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (NE10 : 0 <= md_n dE <= 10000).
    { destruct OPD as [[DBJ B]| EQ]; [pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & _ & NRE & _); exact NRE| rewrite EQ; exact NR1]. }
    assert (V01 : aaV0 <= aaV1) by (clear - EM HJ; unfold aaV0, aaV1, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia).
    assert (F01 : aaF0 <= aaF1) by (clear - D0; unfold aaF0, aaF1, calls_FR, fr_charge in *; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1; rewrite ?Z.mod_small in K1 by (clear - HJ NE10; lia).
    2: { (* [comment removed for export] *) eapply aa_retm16; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| clear - BV V01; unfold aaV0, aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF F01 D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep. replace (zx16 (Z_to_bv 64 (md_n dXc))) with (Z_to_bv 64 (md_n dXc)) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?Z.mod_small in K0 by (clear - HJ NE10 NR1; lia).
    - (* [comment removed for export] *)
      assert (EO : md_own dXc = LHeap).
      { destruct (md_own dXc) eqn:E; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. destruct (OWN0 eq_refl) as [_ [N0 _]]. clear - N0 K0 HJ. lia. }
      replace (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)) with SH10 by reflexivity.
      eapply aa_CALL; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| exact OPD| exact EO| clear - HJ K0; lia| clear - HJ; lia| clear - HJ EM; lia| exact SG1| rewrite HVv; exact HVV| clear - BV V01; lia| clear - BF F01; lia].
    - (* [comment removed for export] *)
      destruct OPD as [[DBJ B]| EQ]; [| exfalso; subst dE; clear - K0 HJ; lia].
      eapply aa_G1; [exact DBJ| | exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| exact B| clear - K0 HJ; lia| exact EM| exact SG1| exact HVv| exact BV| exact BF].
      unfold K1A_stmt. intros. eapply aa_CALL; try eassumption; [left; split; assumption| | clear - HJ; lia| clear - HJ EM; lia|].
      + split; [clear - HJ; lia| assumption].
      + match goal with H : limbs_val _ = vv |- _ => rewrite H; exact HVV end.
    all: match goal with |- ?g => idtac "J1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5386298158.5300000;S2ra2zs1n1H". (* [comment removed for export] *)
  #[using="ra dA dB"] Lemma lval_fullA : forall zs n, Z.of_nat (length zs) = n -> lval zs n = limbs_val zs.
  Proof. intros zs n H. unfold lval. replace (Z.to_nat n) with (length zs) by lia. rewrite firstn_all. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@L19001281403.118L21041645149.3  L21631969095.2  L2252592338.1   L28445359368.119L30999486262.149L31009716740.6  L35907686528.158L36459744067.150L41797317486.149L41799774684.150L42608597650.1  L46776308753.156L46783133011.2  L51267939251.14 L52513850880.150L53517176338.149L54425651213.3  L55715400192.150L59308583409.4  L59308925409.119L59310648043.6  L60008970178.5  L62624701883.1  L63187757423.118L63362628785.118L65528204888.4  L780814420.5    L8927197090.149 L8929159528.152 L8929654032.150 Q2183115807.153 Q22043167663.153Q23074121587.155Q23829912507.150Q26295627581.153Q27210147641.153Q27212325380.150Q30075774172.155Q34423045936.151Q35453294111.150Q4447376314.151 Q50458135125.153Q59030962408.151Q59032828776.150Q68617181559.150Q8945848474.150 00000N00V00\00_01R02I02X03L03f04]05T05W06106706L06f07@07I07c07o08a09609B09E09F0::0:E0:Q0;H0<?0=60=N0=o0>L0>^0>m0?J0?g0@D0@V0A30A\0An0B@0BR0Bd0C3S2ra2sp1X3xs01k2dE2zs1r2Hk3EP0S1k1r2HkS2zs1rS1rS2ra2sp1X3xs01k2dE2zs1r2Hk2EM3EP03EPA2HR2X03SPR3EA0S2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EB3EA0S2zs2vv3HVV3ZA'S2ra2sp1X3xs01k2dE2zs1r2Hk2EM3EP02HR2X03SPR4NE103EA0S2ra2sp1X3xs01k2dE2zs1r2HkS2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EB3EA0S2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EB3EA0S1rS2ra2sp1X3xs01k2dE2zs1r2HkS2dE1rS2dA2dB2dE1v2EM2HR2BVS2ra2sp1X3xs01k2dE2zs1r2HkS2ra2sp1X3xs01k2dE2zs1r2HkS2dE1r2HRS2ra2sp1X3xs01k2dE2zs1r2HkS2dE1r2Hk2HRS2ra2sp1X3xs01k2dE2zs1r2Hk2EM3EP02HR2X03SPR3EA02UBS2dE2zs1r4LENZ2HR3NTHS2dE1r2HR2K2S1rFS2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR3EA0S1d2D01f2BFS2dE1r2HR2K2S2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EB3EA0S2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EB3EA0S2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EB3EA0S3xs01k2dE2zs1r2Hk2EM2HRS3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HRS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2HkS3xs01k2zs1r2HkS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2HkS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS2ra2sp1X3xs01k2dE2zs1r2Hk2X03SPR3EAL3EA0S3xs01k2dE2zs1r2HkS3xs01k2dE2zs1r2HkS3xs01k2dE2zs1r2HkS3xs01k2dE2zs1r2HkS3xs01k2zs1r2Hk". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_SCANLOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pk,$61.PdE,$7.Pzs,(1.(3.&40.))Pvv,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pr2,(3.&40.)Pr24,(3.&40.)Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs5,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(22.R18.(62.R22.))P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1?.R1>.R1=.R1<.R1;.R1:.)P,(22.(1=.R1;.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(67.R24.R1?.R1>.R1=.R1<.)P,(10.$8.(4?.R1=.)+1.)P,(10.(1.(3.&40.))(56.R26.)R25.)P,(68.$47.R20.(1;.R27.)(69.R26.))P,(10.$8.(62.(63.(3.&40.)R27.))(1=.R28.))P,(22.(1=.R29.)$5=.)P,(33.=(1;.R2:.))P,(6:.$47.(2=.VR,)(2>.$47.VR,VHIA,R26.)R24.(1;.R2;.)(1<.+4.(1=.R2;.)))P,(6>.$47.R25.(19.R2<.)(6=.(1;.R2<.)(29.&40.(4?.R2<.))(1=.R2<.)(6<.R2<.)))P,(6:.$47.(2=.VR,)(2>.$47.VR,VHIA,R28.)R26.(19.R2=.)+10.)P,(10.$8.(28.(1;.R2>.)+4.)=)P,(32.(22.+1.R26.)(22.R26.(1=.R2?.)))P,(10.$8.(66.R2?.R27.)(55.R2?.))P,(10.$8.(55.(56.R29.))R2?.)P,(10.$8.(23.R30.(55.R31.))$4>.)P,(22.R30.$5>.)P,(22.R30.$5?.)P,(10.(3.&40.)R2;.(29.&40.(23.R2<.+2.)))P,(10.(3.&40.)R2;.(29.&40.(23.(1<.+4.R2=.)+8.)))(51.$47.(52.$47.VR,VHIA,R32.Vmo,)$53.(43.(44.R2;.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R2:.R29.R28.(29.&40.VX,)R27.R26.(29.&40.+8.)R25.R24.R23.R22.R21.R20.R1?.R2=.(29.&40.(19.R37.))R1>.(29.&40.(59.(2=.VR,)))R2<.R1=.R1<.(29.&40.(23.(5:.(19.R37.)+3.)(59.(2=.VR,))))R1;.R1:.R19.R18.R17.)VF,(29.&40.+9=??<.)Vfc,(45.(3.&40.))R30.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 NGX OPD SG1 EZ EBY LENZ EM EP0 OEL CE OE EPA HR ZA HVv HVV BV BF -> ->; [exfalso; clear - Hk HR; lia|].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (NE10 : 0 <= md_n dE <= 10000).
    { destruct OPD as [[DBJ B]| EQ]; [pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & _ & NRE & _); exact NRE
      | rewrite EQ; pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (_ & _ & NR1 & _); exact NR1]. }
    assert (EAL : md_addr dE mod 8 = 0 /\ 0 < md_addr dE).
    { destruct OPD as [[DBJ B]| EQ]; [pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (EA0 & _ & EAL & _); split; assumption
      | subst dE; pose proof (xa_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as AD; rewrite AD; cbn [md_addr]; split; assumption]. }
    destruct EAL as [EAL EA0]. pose proof CE as CE0. unfold mpi_cells in CE.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. zstep.
    replace (Z_to_bv 64 (md_p dE + (4 * r + 8) + -12)) with (Z_to_bv 64 (md_p dE + 4 * (r - 1))) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    zstep. ubchk. zstep. zstep. zstep. zstep. ubchk. zstep. ubchk. zstep. zstep. zstep. zstep. ubchk.
    zstep. zstep. shadow_chk OEL (md_p dE + 4 * (r - 1)) 4.
    (* [comment removed for export] *)
    destruct (nth_error zs (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dE) zs (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_w32_nth zs (Z.to_nat (r - 1)) w NTH) as LW. pose proof (w32_range w) as WR.
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite bv_unsigned_sx32 in K0; fold (w32 w) in K0.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ WR)) in K0.
      assert (ZA' : lval zs (r - 1) = limbs_val zs).
      { rewrite <- ZA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ zs (r - 1)) by (clear - HR; lia). rewrite LW, K0. clear; lia. }
      (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2.
      + assert (r = 1) as -> by (clear - K2 HR NE10; lia). change (1 - 1) with 0 in ZA'. rewrite lval_0 in ZA'.
        eapply aa_ret0; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| | exact SG1| |].
        * unfold mpd_val. rewrite SG1, HVv. clear - HVV ZA'. lia.
        * clear - BV EM HR; unfold aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia.
        * clear - BF D0; unfold aaF0, add_abs_FR, calls_FR, fr_charge in *; lia.
      + (* [comment removed for export] *)
        eapply (IH _ _ _ _ _ _ _ _ _ (r - 1)); try eassumption; [clear - Hk; lia| clear - HR K2 NE10; lia| f_equal; clear; lia| f_equal; clear; lia].
    - (* [comment removed for export] *)
      zstep.
      eapply aa_J1; [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| exact OPD| exact HR| exact EM| exact SG1| exact HVv| rewrite EZ, ZA; exact HVV| exact BV| exact BF].
    all: match goal with |- ?g => idtac "SCANLOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01L0@D24976250634.171D50797141399.171D52014138856.171K3345721225.171 L1164172544.1   L18200423630.1  L24982609536.164L24982609536.168L24982609536.185L26418096262.134L29074096193.163L29074168500.166L33085536913.2  L3352129893.15  L33524413741.2  L35006717247.3  L35663928186.7  L35839507041.2  L35963164448.4  L37070357933.2  L39172636981.0  L39397588054.186L39397715809.2  L43935878786.170L43935878786.187L44822572454.2  L46160487540.170L46160821889.167L47182164405.4  L47434218903.1  L49584625515.2  L49639216613.184L49639411472.187L51269970326.14 L51269970338.14 L52514260748.185L52514292097.184L52515888190.186L5259801613.163 L5259801613.167 L5259833984.164 L5259833984.168 L5262436786.169 L59308546259.3  L59308628179.4  L59308925409.120L59308925409.122L59308925409.134L59310763475.3  L59833689021.3  L60098763854.3  L61931164306.169L61931815313.2  L64182719253.2  L65528204888.4  L68605167589.120L68605167589.122Q22285631880.168Q22285648010.165Q22286196081.167Q24974040330.170Q26207721832.172Q26207967338.169Q26209519061.171Q2656781204.190 Q2656862870.193 Q2658344491.192 Q31651985788.171Q39212284437.168Q39212284437.172Q39212284437.193Q42081808994.168Q42951517552.190Q43925228937.172Q45029911549.193Q4926406185.168 Q52016320488.170Q54253886744.167Q56761401107.168Q6027349519.171 Q60511567613.168Q60511567613.172Q60511567613.193Q60697995187.172Q62965564504.169Q63231501142.165Q67099234674.192Q67530527544.193Q8880503606.169 Q9538787269.165 Q9538787269.169 Q9538787269.190 00000O01I01h02^02a02d03403D03Z04>04U04l05305405<05F05[05c05k06306406Q06Y07I08808>08U08l09709;09A09^0:;0:P0:f0;C0;`0<=0<T0<k0=B0=Y0>00>90>R0>h0?>0?Z0?e0?j0@40@J0@Q0@Y0@d0A;0AR0A\0Af0B00BI0BS0B]0Bg0C50CC0CQ0C[0Ce0Co0D=0DM0D[0De0E30E=0EV0E`0Em0FF0FN0FV0Fa0Fn0GE0GO0G]0Gn0H80H@0HH0HSS2ra2sp1X3xs02xs2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22xs5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO21p2xs5NEEDR3FSZ3DSX2HB5Ha_st5Hl_stS1XS1nS2ra2sp1X3xs02xsS2ra2sp1X3xs02xsS2ra2sp1X3xs02Ea2zs2xsS2ra2sp1X3xs02Ea2zs2xs2X03SPR2E03EALS2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S1n3NR1FS1p4XPALS1X2Ea3SXBS1R3HIA1h2sp2lo3TOP1HS2nE3NRES2xs3HVVS2nE3NE1SS2ra2sp1X3xs02Ea2nE2zs2xs3NRES2nE3NRES2ra2sp1X2nX3xs01n2xs2EM2X03LEN3SPR3NR13NM14LEN1S2ra2sp1X3xs02Ea2nE2zs2xs2EM2X03SPR2E04LENE3NRES1n2N1S2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S1X2nE2pE1HS2nES1n2N1S2ra2sp1X3xs02Ea2zs2xs2E03E16S2ra2sp1X3xs02Ea2zs2xs2E03E16S2dA2dB1v1n2EM2BV3NR1S2dA2dB2nE1v2EM2BV3NRES2ra2sp1X3xs02Ea2zs2xs2E03E16S2ra2sp1X3xs02Ea2zs2xs2E03E16S2ra2sp1X3xs02Ea2zs2xs2E03E16S2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S1n2K02N0S2nE2zs4LENE2K01n2xs4LEN1S2ra2sp1X3xs02xs2X02UBS2ra2sp1X3xs02xs2X02UBS2ra2sp1X3xs02Ea2zs2xs2E02UBS2nE2K03EZ0S3HVVS1R2lo3LOSS2ra2sp1X3xs01n2xs3NR1S1n3NR1S2nE3NE1S1d2D01f2BFS2ra2sp1X3xs02xs2X03XALS2ra2sp1X3xs02xs2X03XALS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xs2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xsS1X3xs02xsS3xs02Ea2zs2xsS3xs02Ea2zs2xsS3xs02Ea2zs2xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS3xs02Ea2zs2xsS1X3xs02xs2X02HBS3xs02Ea2zs2xsS1X3xs02xsS3xs02Ea2zs2xsS1X3xs02xsS1X3xs02xs2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xs2X0S1X3xs02xs2HB5Ha_st5Hl_stS3xs02xsS3xs02xsS3xs02zs2xsS1X3xs02xs2X0S1X3xs02xs3X162HB5Ha_stS1X3xs02xsS3xs02Ea2zs2xsS3xs02Ea2zs2xs2E0S1X3xs02xsS3xs02xsS3xs02xsS3xs02zs2xs". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_SCAN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs5,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4:.(4;.$2.)R1?.R1>.R1=.R1<.R1;.R1:.)P,(22.(1=.R1;.)(4<.VnX,(1=.VdA,)(1=.VdB,)))P,(67.R22.R1?.R1>.R1=.R1<.)P,(22.(1=.R23.)$5=.)P,(10.$8.(23.(55.(56.R1>.))(55.(56.R24.)))$4>.)P,(22.R24.$5>.)P,(22.R24.$5?.)(51.$47.(52.$47.VR,VHIA,R24.Vmo,)$53.(43.(44.R20.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1?.R1>.R1=.(29.&40.VX,)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.(29.&40.(19.R27.))R11.(29.&40.(59.(2=.VR,)))R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(29.&40.+9=?94.)Vfc,(45.(3.&40.))R22.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX OPD EM HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
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
    zstep. ubchk. zstep. zstep. ubchk. zstep. zstep. zstep. shadow_chk OX1 (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : HM asegs R HIA hc LBc LF m2 |- _ => rename H into HH2 end.
    match goal with H : aobj asegs AL (hcs asegs R HIA hc) m2 X 16 |- _ => rename H into OX2 end.
    match goal with H : rw_cells asegs m2 X _ |- _ => rename H into CX2 end.
    pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ 1 J0 MU WM MI2 CX2 ltac:(left; reflexivity) HH2 OX2) as J2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J2.
    destruct OPD as [[DBJ B]|EQ].
    - (* [comment removed for export] *)
      destruct dE as [Ea sE nE pE zs padE ownE]. pose proof (jb_OB _ _ _ _ _ _ _ _ _ _ DBJ) as (OB1 & OB2 & OB3 & OB4 & OB5). pose proof (jb_SXB _ _ _ _ _ _ _ _ _ _ DBJ) as SXB.
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (bja_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 J0 B MU WM
                    ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX2| apply Forall_nil])
                    ltac:(cbn; split; [clear - SXB; lia| exact I]) ltac:(intros EN; cbn; split; [pose proof (OB1 EN); clear - H; lia| exact I])) as B2.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B2.
      assert (B2' : BJE (mkMPD Ea sE nE pE zs padE ownE) hc LBc m2 (mkMPD X 1 n p xs padX own)) by (destruct B2 as [b1 b2 b3 b4 b5]; constructor; assumption).
      clear B2. rename B2' into B2.
      pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B2)) as [(CE2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CE2. unfold mpi_cells in CE2.
      pose proof (bj_aobj _ _ _ _ _ _ _ _ _ _ B2) as OE2. cbn [md_addr] in OE2.
      clear MU WM B J0 JX. try clear CX1; try clear OX1. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. ubchk. zstep. zstep. ubchk. zstep. zstep. zstep. shadow_chk OE2 (Ea + 10) 2.
      (* [comment removed for export] *)
      zstep. replace (zx16 (Z_to_bv 64 nE)) with (Z_to_bv 64 nE) by (unfold zx16; rewrite !unsigned_lit by (clear - NRE; lia); rewrite Z.mod_small by (clear - NRE; lia); reflexivity).
      (* [comment removed for export] *)
      zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
      zstep. if_cases K0; zify_cond K0; rewrite ?Z.mod_small in K0 by (clear - NRE; lia).
      { (* [comment removed for export] *)
        eapply aa_ret0; [exact J2| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| | reflexivity| clear - BV EM NRE; unfold aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF0, add_abs_FR, calls_FR, fr_charge in *; lia].
        unfold mpd_val. cbn [md_sg md_limbs].
        destruct zs; [cbn [limbs_val] in HVV; clear - HVV; lia| exfalso; cbn [length] in LENE; clear - LENE K0; lia]. }
      assert (EN : ownE <> LNull) by (intros C; destruct (OWNE0 C) as [_ EZ0]; clear - K0 EZ0; lia).
      ddestruct (OWNE1 EN) as (NE1 & EP0 & EPAL & _ & ESK & _).
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B2) as (_ & _ & _ & _ & _ & _ & _ & OWNE2). ddestruct (OWNE2 EN) as (_ & _ & _ & EBY2 & _).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in EBY2.
      pose proof (bj_aobjL _ _ _ _ _ _ _ _ _ _ B2 EN) as OEL2. cbn [md_p md_n] in OEL2.
      (* [comment removed for export] *)
      eapply (aa_SCANLOOP (Z.to_nat nE) (mkMPD Ea sE nE pE zs padE ownE) zs) with (r := nE); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [clear - NE1; lia| exact J2| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| left; split; [exact DBJ| exact B2]| reflexivity| reflexivity| exact EBY2| exact LENE| exact EM| exact EP0| exact OEL2
        | exact CE2| exact OE2| exact EPAL
        | clear - NE1; lia| apply lval_fullA; exact LENE| reflexivity| exact HVV| exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia].
    - (* [comment removed for export] *)
      subst dE. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2' & OWN2 & OWN2'). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2', OWN2, OWN2'. unfold mpi_cells in CX2'.
      pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2) as OX2'. cbn [md_addr] in OX2'.
      clear MU WM J0 JX. try clear CX1; try clear OX1. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. ubchk. zstep. zstep. ubchk. zstep. zstep. zstep. shadow_chk OX2' (X + 10) 2.
      zstep. replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
      zstep. if_cases K0; zify_cond K0; rewrite ?Z.mod_small in K0 by (clear - NR1; lia).
      { eapply aa_ret0; [exact J2| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| | reflexivity| clear - BV EM NR1; unfold aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF0, add_abs_FR, calls_FR, fr_charge in *; lia].
        unfold mpd_val. cbn [md_sg md_limbs].
        destruct xs; [cbn [limbs_val] in HVV |- *; clear - HVV; lia| exfalso; cbn [length] in LEN1; clear - LEN1 K0; lia]. }
      assert (ON : own <> LNull) by (intros C; destruct (OWN2 C) as [_ [N0 _]]; clear - K0 N0; lia).
      ddestruct (OWN2' ON) as (EO & N1 & XIN & XPAL & ARR2 & P0 & PC & PI & OP2 & P47). subst own.
      eapply (aa_SCANLOOP (Z.to_nat n) (mkMPD X 1 n p xs padX LHeap) xs) with (r := n); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [clear - N1; lia| exact J2| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| right; reflexivity| reflexivity| reflexivity| apply u32arr_ro; exact ARR2| exact LEN1| exact EM| exact P0| exact OP2
        | exact CX2'| exact OX2'| clear - XPAL; lia
        | clear - N1; lia| apply lval_fullA; exact LEN1| reflexivity| exact HVV| exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "SCAN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579668.400000=S1X2Ea3SXE2H5". (* [comment removed for export] *)
  #[using="IMG"] Lemma mk_JBd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "PdE,$7.Pm1,P,(3.&40.)(5.(3.&8.))P,(<.$47.VR,VLF,Vm,VLB,(=.&40.Vsp,)R2.)P,(14.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.Vlo,(=.&40.Vsp,))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.R4.)+10.)P,P,(10.$11.(12.R5.)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.R6.)(1<.+4.(1=.R6.)))P,(21.(22.(23.VX,+10.)(19.R6.))(22.(23.(19.R6.)+10.)VX,))P,P,(10.$11.(12.R7.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R9.))))(10.$2?.(34.$47.(35.(23.(1;.R:.)R2.)))$31.)(10.$2?.(30.(1;.R9.)(1<.+4.(1=.R9.)))$31.)P,(6:.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)R7.(19.R8.)+10.)P,P,(10.$11.(12.R9.)$13.)(6:.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)R9.(1;.R:.)(1<.+4.(1=.R:.)))P,(9.$47.VR,VHIA,Vh,VLB,VLF,R9.)P,(<.$47.VR,VLF,R:.VLB,(=.&40.Vsp,)R;.)(32.(5;.$47.VR,VHIA,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R<.)(54.$47.VR,VHIA,VLF,Vsp,R<.Vh,VLB,R;.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
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

  Hypothesis COPY : mpi_copy_stmtA asegs R HIA A_MPI_COPY.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02m0@D11157215372.221D11157215372.222D11157215372.223D11157215372.226D11157215372.227D11157215372.228D11157215372.229D12056100143.224D2597768731.221 D2597768731.227 D28231426868.227D30895958932.220D30895958932.226D35104119167.219D3582819326.227 D35881667587.165D35881667587.166D43120647727.221D43120647727.222D43120647727.223D43120647727.226D43120647727.227D43120647727.228D43120647727.229D51794440367.165D51794440367.166D66909274523.225K14554379081.165K14554379081.166K68206801384.165K68206801384.166L13098889560.153L14550820926.2  L14714826937.3  L14795424372.153L15282565064.2  L17305750384.4  L17767458348.225L17767458348.226L18868739288.153L19431261630.4  L19945316590.2  L20806881524.153L2138888664.153 L21541644120.153L23459206846.174L23459206846.175L24026950640.22 L26063552453.22 L26479207440.3  L26828156276.153L26983617546.4  L2759026548.153 L29010569984.215L29834048600.153L2998330202.2   L3043381336.153 L3070335905.4   L30902068878.7  L31743414849.8  L31743414976.8  L31755912410.7  L32855866356.153L34456472569.2  L34936451766.1  L35609665496.153L35653441506.7  L38282648152.153L38866126964.153L40834179097.174L40834179097.175L41670789057.6  L41672855235.5  L42479632545.4  L43059266230.159L43112965553.186L43117078192.187L43117078192.188L43671330526.3  L44506986788.15 L44778233891.3  L44807604259.22 L44891662068.153L45674082520.153L47401587060.153L48406759151.7  L50786303024.2  L50903118708.152L52361663192.152L5259987632.175 L5259987632.176 L5262094874.174 L5262094874.175 L5262098304.173 L53388880400.227L53410279412.153L53982396750.1  L54106875608.153L55013023064.153L59308628433.4  L59308632561.1  L59314955108.4  L59438513268.153L60098763854.3  L60330452198.161L62417105880.153L62998362800.22 L64491265552.2  L6482734895.4   L65351313222.22 L65451395828.153L66988777498.173L66990871850.175L66990871850.176L68211501598.2  L7038532778.5   L8303040740.2   L8769959412.153 P2999985744.227 P44505005102.227Q14340403473.182Q15643324129.161Q18365925601.162Q18378753154.162Q18694078840.183Q18694180728.184Q21879645826.162Q23625282341.182Q24328806760.183Q24329039720.184Q24389563138.162Q25513505925.164Q25513505925.165Q25662327983.184Q25662554799.183Q27584944865.162Q27907200258.162Q29505479905.162Q2999985744.227 Q30415036802.162Q31228739884.184Q31228907308.183Q31271525473.162Q32655500769.162Q33918256002.162Q35014402586.184Q35014503450.183Q36425882626.162Q37321848340.227Q37321848598.192Q3830427394.162 Q39939554818.162Q41152393185.162Q44505005102.227Q44648843873.162Q4533518817.162 Q4743835142.182 Q49698585326.163Q49698585326.164Q50299420301.184Q50299646093.183Q51235796833.162Q52101170785.162Q52936815889.182Q53490553313.182Q53711815251.162Q53711815251.163Q53969792887.184Q53969822071.183Q53972118266.182Q54127253745.182Q54485784450.162Q55637823525.182Q59256763233.162Q59843137889.162Q60511257090.162Q61802108972.184Q61802206764.183Q61996729712.182Q64255452024.184Q64255683960.183Q64297264762.222Q64297264762.223Q65925244770.164Q65925244770.165Q66522067074.162Q67528989526.165Q67528989526.166Q9843367298.161 00000100200R00S00T00U01501601701801S01T01U01V02102g04C04D04d04e04f04g05G05H06S08D08E09A0:`0;\0=;0=V0=W0=a0><0>C0>O0?L0@L0@g0A50A<0AW0B20BM0Bk0CI0Ch0D>0DH0Dc0Do0EJ0EK0Ef0Eg0FB0FN0FW0G40GQ0Gk0HF0HM0HQ0Hl0ID0I_0J:0JW0K40KH0K\0Kh0L`0MU0NJ0O?0OG0OH0OP0Od0P?0PZ0Q50QC0QI0Qd0R?0Ra0SC0Se0TG0Ti0UD0U_0Uc0V>0VY0Vf0Vj0W70WR0W\0X70XR0Y20Y80YF0YX0Z30ZQ0Zo0[M0[N0[R0[[0\60]50^80^K0^d0_=0_[0`50`O0`m0aG0aH0aI0ag0bR0c`0ca0cb0d;0dY0e20e30eQ0el0fG0f`0g90gW0h20hM0hk0ib0jY0k70kU0kn0ko0lH0la0lb0mF0mj0mk0ml0nE0n^0n_0n`0o90oR0om10H10c11=11[11\12512N12l12m12n12o13013113213313c15615T16D17W185FFS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFFFS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFFFS2ra2sp1X3xs02dA2dB3ABD3BBDFFFS2ra2sp1X3xs02dA2dB3ABD3BBDS1R3HIA1h2ra2sp1X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFFFS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFS1R2ra2sp1X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FS1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2ra2sp1X3xs02dA2dB3ABD3BBDFS1X2dA3KAXS2ra2sp1X3xs02dA2dB3ABD3BBDS2dA2dBS2sp2dA2lo1HS2ra2sp1X2nX3xs02dA2dB2X03SPR2A04LENA2B04LENB3ABD3BBD3dX23CNFS2ra2sp1X2nX3xs02dA2dB2X03LEN3SPR2A04LENA2B04LENB3ABD3BBD3dX22CNS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dA2lo3OA4S2sp2loS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB2A03ABD3BBDS2ra2sp1X3xs02dA2dB2A03ABD3BBDS1R3HIA1h2sp2dA2dB3BUD3SPR4NRA'S1R3HIA1h2sp2dA2dB3TOPS1X2dB3KXBS2ra2sp1X3xs02dA2dB3ABD3BBDS2dA2A01a2HaS2ra2sp1X3xs02dA2dB3ABD3BBDFS2ra2sp1X3xs02dA2dB3ABD3BBDFS2ra2sp1X3xs02dA2dB3ABD3BBDS2dA2dB4NRA'S2sp2dA1HS1X2sX2nX2pX3xs04padX4ownX2dAS1X2sX2nX2pX3xs04padX4ownX2dBS1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X3xs02dA2dB3ABD3BBDS2dA2dBS2spS2ra2sp1X3xs02dA2dB3ABD3BBDS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R2ra2sp1X3xs02dA2dB3ABD3BBDS1R2ra2sp1X3xs02dA2dB3ABD3BBDS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS2sp2dB2lo1HS1R2ra2sp1X3xs02dA2dB2lo4SLO25NEEDR2X03SPR2A02B03ABD3BBDS2ra2sp1X2nX3xs02dA2dB2X03SPR2A04LENA2B04LENB3ABD3BBDS2ra2sp1X2nX3xs02dA2dB2X03SPR2A04LENA2B04LENB3ABD3BBDS2ra2sp1X2nX3xs02dA2dB2X03SPR2A04LENA2B04LENB3ABD3BBDS1X2dA1DFS1X2dB1DS1R2sp2dA2dB2lo4SLO2S2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dA2lo3OA4S1d2D0S2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2spS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1X2dB3KXB2K2S2KRS1X2dA1D1E2dBS2ra2sp1X3xs02dA2dB3ABD3BBDS1R2lo3LOSS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R3HIA1h2sp2dA2dB1d2D04BUDF3SPRS1d2D0S2sp2dB2lo3OB4S2sp2dA2dB3SPA3SPRS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDFS2spS2dA4NRA'S2ra2sp1X3xs02dA2dB3ABD3BBDS1R2sp1X3xs02dA2dB2lo4SLO25NEEDR3DSX3ABD3BBD3OA43OB43KXB3KAX2K2S1R2sp1X3xs02dA2dB2lo4SLO25NEEDR3FSZ3DSX3ABD3BBD3OA43OB43KXB3KAX2K2S3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDFFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2ra2sp3xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R2sp3xs02dA2dB2lo4SLO25NEEDR3LOS4SP643ALO3ACP3ABD3BBDS1R2sp3xs02dA2dB2lo4SLO25NEEDR3LOS4SP643ALO3ACP3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stFFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFFS2sp3xs02dA2dB3ABD3BBD2HBS2sp3xs02dA2dB3ABD3BBD2HBS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFFFFFFFS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp3xs02dA2dB2lo4LOSP3ABD3BBD". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM COPY"] Lemma aa_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_sz ()) "Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(:.$47.VR,VHIA,Vh,Vmo,)P,(;.$47.Vm,VLB,VdA,)P,(<.$47.VR,VLF,Vm,VLB,(=.&40.Vsp,)VdB,)P,(>.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)P,(>.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,)P,(>.VdA,VdB,)P,(14.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,Vlo,(=.&40.Vsp,))P,(14.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,Vlo,(=.&40.Vsp,))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.VdA,)+10.)P,P,(10.$11.(12.VdA,)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.VdA,)(1<.+4.(1=.VdA,)))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.VdB,)+10.)P,P,(10.$11.(12.VdB,)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.VdB,)(1<.+4.(1=.VdB,)))P,(24.$47.Vm,Vlo,(=.&40.Vsp,))P,(2;.$47.Vm,)P,(2<.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(2<.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)Vm,VdA,)P,(2<.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)Vm,VdB,)P,P,(?.(10.$8.(19.VdA,)(19.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))))P,(10.$11.(12.VdA,)$13.)(10.$2?.(30.(1;.VdA,)(1<.+4.(1=.VdA,)))$31.)P,P,(10.$11.(12.VdA,)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.VdA,))))(10.$2?.(34.$47.(35.(23.(1;.VdA,)R2.)))$31.)(10.$2?.(30.(1;.VdA,)(1<.+4.(1=.VdA,)))$31.)P,P,(10.$11.(12.VdB,)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.VdB,))))(10.$2?.(34.$47.(35.(23.(1;.VdB,)R2.)))$31.)(10.$2?.(30.(1;.VdB,)(1<.+4.(1=.VdB,)))$31.)(3?.$47.$53.(42.(43.(44.Vra,Vsp,Vgp,Vtp,R20.R1?.R1>.Vs0,Vs1,(29.&40.VX,)(29.&40.(19.VdA,))(29.&40.(19.VdB,))R1=.R1<.R1;.R1:.R19.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R18.R17.R16.R15.)VF,(29.&40.$6;.)Vfc,(45.(3.&40.))Vm,(46.$47.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK MA0 MB0 SXA SXB SAB OA OB CRA CRAL CRB CRBL ST MI OXA OAA OBA IA1 IA2 IB2. unfold A_MPI_ADD_ABS.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof MA0 as [(CA0 & AAL & A0 & LENA & NRA' & OWNA) SGA]. pose proof (opnd_viewA _ _ _ _ _ _ _ MB0) as [(CB0 & BAL & B0 & LENB & NRB & OWNB) SGB]. unfold MPI_MAX_LIMBS in NRA', NRB.
    pose proof (rw_cells_bound _ _ _ _ CA0) as ABD. pose proof (rw_cells_bound _ _ _ _ CB0) as BBD. unfold mpi_cells in ABD, BBD. cbn [cells_size csize Nat.add] in ABD, BBD.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. pose proof OBA as [OBs OBl]. cbn [md_addr] in OX.
    pose proof SXA as SXA0. unfold mpd_sep in SXA, SXB, SAB. cbn [md_addr] in SXA, SXB, SAB.
    assert (VAL : AA_VAL_A = limbs_val (md_limbs dA) + limbs_val (md_limbs dB)) by (unfold AA_VAL_A, mpd_abs; reflexivity).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 112%nat ST.
    (* [comment removed for export] *)
    do 14 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jk :: _) =>
      change (rw_cells asegs m1 (bv_unsigned sp + -112) ([CB 8 jk] ++ AA_FRAME_A)) in FR end.
    apply rw_cells_app in FR. destruct FR as [SLOT FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp - 104) in FR by (clear; lia).
    lazymatch type of SLOT with rw_cells _ _ _ [CB 8 ?jk] => set (slot0 := jk) in SLOT end.
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp - 104)).
    { eapply stk_merge; [exact ST| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 slot0])) by (cbn; clear; lia).
      eapply stk_of_rw_cells. exact SLOT. }
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    (* [comment removed for export] *)
    assert (MA1 : mpd_at asegs m1 LB dA).
    { eapply mpd_at_munch_any; [exact MA0| exact MU| exact WM| cbn; split; [clear - OA4; lia| exact I]|].
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
    pose proof (opnd_atA_mpd asegs R LF m LB (bv_unsigned sp) dA MA0) as MA0o. pose proof (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dA MA1) as MA1o.
    assert (JBA : md_addr dA <> X -> JBE dA /\ BJE dA h LB m1 dX).
    { intros NE. eapply mk_JBd; try eassumption. all: try (intros EO RO; exact (IA2 EO RO)).
      all: destruct SXA as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| clear - D; lia]. }
    assert (JBB : md_addr dB <> X -> JBE dB /\ BJE dB h LB m1 dX).
    { intros NE. eapply mk_JBd; try eassumption. all: try (intros EO RO; exact (IB2 EO RO)).
      all: destruct SXB as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| clear - D; lia]. }
    assert (BV0 : 0 <= aaV0) by (unfold aaV0, grow_PHI; unfold AVOL_CALL; clear - NRA'; lia).
    assert (BF0 : 0 <= aaF0) by (unfold aaF0, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KXB; zify_cond KXB; rewrite ?Z.mod_small in KXB by (clear - BBD X16 X0; lia).
    - (* [comment removed for export] *)
      pose proof (IDB (eq_sym KXB)) as EDB.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KAX; zify_cond KAX; rewrite ?Z.mod_small in KAX by (clear - ABD X16 X0; lia).
      + (* [comment removed for export] *)
        pose proof (IDA KAX) as EDA. rewrite KAX.
        eapply aa_SCAN with (dE := dX); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| right; reflexivity| unfold aaM; rewrite <- EDA; clear; lia| | exact BV0| exact BF0].
        rewrite VAL, ?EDA, ?EDB. clear; lia.
      + (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by (clear - BBD X16 X0; lia); [| exfalso; clear - K2 KXB; lia].
        destruct (JBA ltac:(clear - KAX; lia)) as [DBJ B].
        eapply aa_SCAN with (dE := dA); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| left; split; [exact DBJ| exact B]| unfold aaM; clear; lia| | exact BV0| exact BF0].
        rewrite VAL, ?EDB. clear; lia.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KAX; zify_cond KAX; rewrite ?Z.mod_small in KAX by (clear - ABD X16 X0; lia).
      + (* [comment removed for export] *)
        pose proof (IDA KAX) as EDA.
        destruct (JBB ltac:(clear - KXB; lia)) as [DBJ B].
        eapply aa_SCAN with (dE := dB); [exact J0| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| left; split; [exact DBJ| exact B]| unfold aaM; clear; lia| | exact BV0| exact BF0].
        rewrite VAL, ?EDA. clear; lia.
      + (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by (clear - BBD X16 X0; lia); [exfalso; clear - K2 KXB; lia|].
        zstep. zstep.
        destruct (JBB ltac:(clear - KXB; lia)) as [DBJ B].
        pose proof (xa_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MX1.
        destruct XW as [CW DXP].
        clear MU WM.
        assert (CSEP : P_mpi_copy.copy_sep dX dA lo (bv_unsigned sp + -112)).
        { unfold P_mpi_copy.copy_sep. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4 SLO2 NEEDR; lia|].
          split; [intros AN; destruct (OA5 AN); [left; assumption| right; clear - H SLO2 NEEDR; lia]| intros a Ha; clear - Ha A0; lia]. }
        eapply aevtA_call.
        { intros mo1 [HK1 MF1]. pose proof COPY as CP. unfold mpi_copy_stmtA, mpi_copy_stmtA_gen in CP.
          eapply CP with (h := h) (LB := LB) (LF := LF) (dX := dX) (dY := dA) (lo := lo) (d := d);
            rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity.
          all: try (unfold P_mpi_copy.copy_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; split; [exact OA1|]; split; [exact OA2|]; split; [exact OA3|];
                    split; [clear - OA4 SLO2 NEEDR; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H SLO2 NEEDR; lia]]).
          all: try (split; [eapply client_wrange_sp_mono; [| exact CW]; clear - SLO2 NEEDR; lia| exact DXP]).
          all: try (rewrite unsigned_lit by (clear; lia); reflexivity).
          all: try (intros EO; apply IA1; [cbn [md_addr]; clear - KAX; lia| exact EO]).
          all: unfold copy_PHI, copy_FR, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AVOL_CALL in *;
               clear - LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF D0 LOSP TOP NRA' NRB; try lia.
          all: match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end. }
        (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
        ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
        injection E as E1 E2. subst ms' mo'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        presA_transport HP2.
        assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 104)).
        { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
          replace (bv_unsigned sp - 104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 slot0])) by (cbn; clear; lia).
          apply stk_of_rw_cells. exact SLOT. }
        unfold P_mpi_copy.copy_R in CR. ddestruct CR as (CR1 & CAD & CPD & CFR).
        assert (BK : binop_keep LB dX dX2).
        { split; [exact CAD|]. split; [exact CPD|]. split; [exact CFR|]. destruct CR1 as [(_ & _ & Bn & _)|(_ & En & _)]; [exact Bn| rewrite En; apply Z.le_refl]. }
        pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -112) (copy_PHI dA) (copy_FR d) J0 ltac:(clear - SLO2 NEEDR; lia)
                      ltac:(unfold copy_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA'; lia) ltac:(unfold copy_FR, calls_FR, fr_charge; clear - D0; lia)
                      MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
        pose proof (bja_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ (bv_unsigned sp + -112) J0 B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
        apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
        pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KR; zify_cond KR.
        * (* [comment removed for export] *)
          destruct CR1 as [(-> & _)|(-> & CNF & _)]; [exfalso; apply KR; reflexivity|].
          eapply aa_ret; [exact J1| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| right; reflexivity| unfold copy_PHI, aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; clear - NRA' NRB; lia
                         | unfold copy_FR, add_abs_FR, calls_FR, fr_charge in *; clear - D0; lia].
        * destruct CR1 as [(-> & CV & CN)|(-> & _)]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
          eapply aa_SCAN with (dE := dB); [exact J1| first [exact NGX | (cbn [md_n] in *; unfold addsub_nz, aaM in *; lia)]| left; split; [exact DBJ| exact B1]| unfold aaM; clear; lia| | unfold copy_PHI, aaV0; apply Z.le_refl| unfold copy_FR, aaF0; apply Z.le_refl].
          rewrite VAL. pose proof (mpd_val_abs dX2 (proj2 MX2)) as VX. pose proof (mpd_val_abs dA SGA) as VA. unfold mpd_abs in VX, VA.
          rewrite <- VX, CV, VA. reflexivity.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WA.


(* [comment removed for export] *)
