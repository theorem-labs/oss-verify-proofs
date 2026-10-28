(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_ecp_group_init P_ecp_group_free P_ecp_group_load.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_copy A_mpi_bitlen A_mpi_init A_free_seq A_ecp_group_init A_ecp_group_free A_ecp_defs A_ecp_statics A_ecp_group_load_c1 A_ecp_group_load_c2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_ecp_group_load.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_ecp_group_load_main () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load.gl_init_cells"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.GF_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.GF_FR"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.group_load_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.group_load_FRn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.C24_ECP_GROUP_LOAD"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_group_load_postA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "A_GL_CASE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load.gl_sw_post"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.ecp_group_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.A_ECP_GROUP_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_init.ecp_group_init_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_init.A_ECP_GROUP_INIT"; "gl_case_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_group_load_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_GROUP_LOAD_E"].


Definition A_GL_CASE (id : Z) : Z :=
  match id with 1 => A_GL_CASE1 | 2 => A_GL_CASE2 | 3 => A_GL_CASE3 | 4 => A_GL_CASE4 | 5 => A_GL_CASE5 | 6 => A_GL_CASE6 | 7 => A_GL_CASE7
              | 8 => A_GL_CASE8 | 9 => A_GL_CASE9 | 10 => A_GL_CASE10 | 11 => A_GL_CASE11 | 12 => A_GL_CASE12 | 13 => A_GL_CASE13 | _ => 0 end.

Section GLM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.

  (* [comment removed for export] *)
  Definition gl_case_stmtA (id : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_main ()) "Ph,(0.$1.VR,VHIA,)Ph2,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))Pm3,P,(4.&40.)(6.(4.&8.))Pmo,$7.PA,$8.Pg,$9.Plo,$8.Pd,$8.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(:.$1.VR,VHIA,R35.(;.R1<.R34.)R33.R1?.)P,(<.R20.R1>.O1.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(=.$8.(>.R1?.+8.)=)P,(?.=R20.)P,(10.$1.R23.(11.(12.&40.R35.)-20.)(13.$14.(15.R30.)(13.$14.(15.R31.)(13.$14.(15.R32.)(13.$14.(15.R36.)(16.$14.))))))P,(17.$1.R24.R20.(11.(12.&40.R36.)-20.))P,(18.(19.VR,)R21.)P,(18.R22.(1:.(1:.(12.&40.R38.)+<0.)(1;.VR,)))P,(18.(12.&40.R39.)(1<.$1.VR,VHIA,R3>.))P,(=.$8.(>.(12.&40.R3:.)+10.)=)P,(1=.(18.(11.R27.+<0.)R25.)(18.(12.&40.R3;.)R27.))P,(=.(4.&40.)R3:.(1>.&40.(1?.VR,)))P,(20.$1.R2;.)P,(=.$8.(>.(12.&40.R3?.)+2.)=)P,(21.$1.(22.VR,)(23.$1.VR,VHIA,R43.)R2=.R2;.+<0.)P,(24.(23.$1.VR,VHIA,R45.)R2<.+<0.)P,(25.(26.VR,)(27.$3.(;.R2<.R44.)(28.R43.))(12.&40.R41.)(1<.$1.VR,VHIA,R46.)R2=.+<0.)P,(29.VR,R2>.+<0.R2;.)P,(2:.$1.VR,VHIA,R48.(;.R2>.R46.)R45.(12.&40.R43.)(19.VR,)(13.(2;.$8.$8.)(2<.$8.$8.R2?.(11.R2?.+<0.))(16.(2;.$8.$8.)))R32.R31.)P,(=.$8.(1<.$1.VR,VHIA,R48.)(1<.$1.VR,VHIA,R49.))P,(=.$8.(2=.$1.VR,VHIA,R49.)(2=.$1.VR,VHIA,R4:.))P,(=.$8.(2>.$1.VR,VHIA,R4:.)(2>.$1.VR,VHIA,R4;.))P,Px,$8.P,(23.$1.VR,VHIA,R4=.R1.)(23.$1.VR,VHIA,R4=.R2.)P,(18.(2?.$1.VR,VHIA,R4<.)(11.(2?.$1.VR,VHIA,R4=.)$30.))P,(18.(31.$1.VR,VHIA,R4=.)(11.(31.$1.VR,VHIA,R4>.)(32.R32.)))P,(18.(11.(2?.$1.VR,VHIA,R4?.)$33.)$34.)P,(18.(11.(31.$1.VR,VHIA,R50.)(35.R34.))$36.)P,(18.(11.(37.R4?.)$38.)$39.)(3:.$1.(3;.$1.VR,VHIA,R51.R3:.)(3<.$1.VR,VHIA,$3=.$3>.$3?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R52.R50.R4?.R39.R38.O1.R37.R36.R3<.R3:.)(40.(41.R2<.(1>.&40.(11.(12.&40.R4=.)-20.))R4<.R4;.R2;.R2:.R29.(1>.&40.R39.)(1>.&40.O1.)R28.R27.R26.R25.R24.R23.R22.R21.(1>.&40.(42.(22.VR,)))R47.R46.R45.R44.R43.R42.R41.R40.R3?.R20.R1?.R1>.R1=.)R3>.(1>.&40.(43.O1.))R3=.(44.(4.&40.))R3;.(45.$1.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition gl_sw_case_evt (id : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_main ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$8.Plo,$8.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(:.$1.VR,VHIA,R31.R30.R2?.R<.)P,(<.R=.R<.O1.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(=.$8.(>.R=.+8.)=)P,(?.=R>.)P,(10.$1.R10.(11.(12.&40.R31.)-20.)(13.$14.(15.R21.)(13.$14.(15.R2:.)(13.$14.(15.R2;.)(13.$14.(15.R32.)(16.$14.))))))P,(17.$1.R11.R?.(11.(12.&40.R32.)-20.))P,(18.(19.VR,)R10.)P,(18.R11.(1:.(1:.(12.&40.R34.)+20.)+40.))P,(18.(12.&40.R35.)(1<.$1.VR,VHIA,R39.))P,(=.$8.(>.(12.&40.R36.)+10.)=)P,(1=.(18.(11.R15.+<0.)R14.)(18.(12.&40.R37.)R15.))P,(20.$1.R17.)P,(21.$1.(22.VR,)(23.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(25.(26.VR,)(27.$3.R3=.(28.R3<.))(19.VR,)(1<.$1.VR,VHIA,R3>.)R18.+<0.)P,(=.$8.(>.(12.&40.R3<.)+2.)=)(46.$1.(22.VR,)(23.$1.VR,VHIA,R40.)(47.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.O1.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(40.(41.R1>.(1>.&40.(11.(12.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(1>.&40.R1:.)(1>.&40.O1.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(1>.&40.(42.(22.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(1>.&40.(43.O1.))R1<.(44.(4.&40.))R1;.(45.$1.)))")
(* [comment removed for export] *).

  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L11969688250.7 L15756354262.4 L19052871347.2 L19666039969.0 L20911126033.1 L21376922785.0 L25696891297.0 L26368079009.0 L30162977185.0 L32027975233.0 L3241391265.0  L34120414369.0 L35655538570.8 L37714553091.1 L39111570593.0 L39231752993.0 L40065549985.0 L45556701510.1 L47216798497.0 L47443067297.0 L48834180257.0 L4952274081.0  L50545063073.0 L50790761713.7 L50845182722.2 L51416933285.6 L54928643099.13L54949972769.0 L55536219297.0 L60098763854.3 L66567143888.2 L66610753222.5 L66969711777.0 L8453145377.0  L8939493197.1  00000F00T00\00]00`00a00b00c00d00e00f00g01C01F01G01H01I01L01M01N01O01P01Q01l02302J02K02L02M02W02_02o030031034S1R3HIA1h2h21d4HFR22D0S1R2lo3LOS3ALOS2id3IDBSS1ASSSSSSSS1R3HIA1h2h22sp2lo3TOP5HTOPxS1ASSSS1ASSSSSS1R5NEEDR2sp2lo3LOS3SLO3NERS2sp2loS1R5NEEDR2sp2lo3SLO3NERFSSS1R2lo3LOSS2id3IDBS1R3HIA1h2h23HV2SSS1A". (* [comment removed for export] *)
  #[using="NEEDR DIMG"] Lemma gl_sw_wrap : forall id, is_sw id = true -> 1 <= id <= 13 -> gl_sw_case_evt id -> gl_case_stmtA id.
  Proof.
    intros id SWC IDB HC. unfold gl_case_stmtA. intros until t6.
    intros HH2 CELLS AL8 POS FR ST LOS SLO TOP SPA DS TPV MI3 RAE OA CRA CWA UWO PXA HT2 HS2 HF2 HCS2 HV2 HFR2 BUD BUDF C24H.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    pose proof (hm_top asegs R HIA h2 _ _ _ HH2) as HTOP2. rewrite HT2, HS2 in HTOP2.
    set (LBf := grp_free_LB g LB) in *.
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo).
    { eapply HC with (h := h2) (LB := LBf) (LF := LF) (lo := lo);
        first [ exact HH2 | exact CELLS | exact AL8 | exact POS | exact FR | exact ST | exact LOS | exact SPA | exact DS | exact MI3 | exact OA | exact RAE
              | (rewrite HT2; exact TOP) | (clear - SLO NER NEEDR; lia)
              | (rewrite HT2; eapply (client_wrange_weak L); [exact CWA| intros b Hb; exact Hb| clear - LOS SLO NER NEEDR; lia| clear; lia| clear; lia])
              | match goal with |- ?gg => idtac "WRAP-PRE-LEFT:" gg end ]. }
    cbv beta. intros ms' PO. unfold gl_sw_post in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & -> & MU & WM & MI' & CELLS' & ST' & HH').
    ddestruct CELLS' as (HD & HP & HA & HB & HX & HY & HZ & HN & HT).
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h2 _ _ _ HH2) as HTOPx.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)).
    { eapply crange_sub; [exact SCS0| clear - LOS; lia|]. rewrite <- HS2. rewrite HT2 in HTOPx. clear - TOP HTOPx. lia. }
    assert (WC : w_client (hcs asegs R HIA h) [(A, A + 192); (lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (A + 192 - A) with 192 by (clear; lia); exact CRA|]. apply Forall_cons; [cbn [fst snd]; exact SCS| apply Forall_nil]. }
    assert (WC2 : w_client (hcs asegs R HIA h2) [(A, A + 192); (lo, bv_unsigned sp)]).
    { unfold w_client in *. eapply Forall_impl; [| exact WC]. intros iv Hiv. eapply crange_mono; [exact HCS2| exact Hiv]. }
    assert (PXA' : presW asegs R HIA h LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m').
    { eapply presW_munch; [exact PXA| exact MU| exact WM| exact WC|].
      apply Forall_cons; [cbn [fst snd]; apply wcover_inside; cbn [inside fst snd]; left; clear; lia|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      ddestruct PXA as (_ & _ & _ & BLOW). eapply wcover_stack; [exact BLOW| | clear - ALO LOS; lia| clear; lia].
      exact (art_data_lo asegs R HIA). }
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold ecp_group_load_postA, ECP_GROUP_SIZE.
    deexists 14. dexists m', mo9, h2, 0, (grp_sw id (A_CA id) A_ONE A idpad pP pA pB pX pY pZ pN hpad), ([] : list blk), LBf.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MF9|].
    split; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ PXA')|].
    split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|]. split; [exact HCS2|].
    split; [unfold group_load_PHI, GF_PHI in *; unfold grow_PHI; unfold AVOL_CALL in *; clear - HV2; lia|].
    split; [unfold group_load_FRn, GF_FR, calls_FR, fr_charge in *; clear - HFR2 D0; lia|].
    split; [exact HH'|].
    split; [intros b; cbn [In]; tauto|]. split; [intros b Hb; destruct Hb|].
    assert (MPB : 0 <= ca_modp (A_CA id) < 2^64 /\ 0 <= ca_T (A_CA id) < 2^64 /\ (ca_modp (A_CA id) = 0 \/ In (ca_modp (A_CA id), (ca_P (A_CA id), cP id)) A_MT)).
    { assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by (clear - IDB; lia).
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]; try discriminate SWC;
        (split; [cbn; clear; lia|]); (split; [cbn; clear; lia|]); cbn -[c1_P c2_P c3_P c4_P c5_P c9_P c10_P c11_P c12_P c13_P]; auto 20. }
    ddestruct MPB as (MB & TBB & MODP).
    split.
    { eapply grp_sw_at; [exact SWC| clear - IDB; lia| exact (A_curve_statics m' id MI' IDB)| exact MODP| exact MB| exact TBB
                        | exact HD| exact AL8| exact POS| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT]. }
    split. { intros d1 d2 H1 H2 NE O1 O2. exfalso. unfold grp_mpds, grp_sw, pt_mpds in H1. cbn -[smpd mpd_init has_A] in H1.
             destruct (has_A id); unfold smpd, mpd_init in H1; cbn in H1;
             (destruct H1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O1; discriminate O1). }
    split. { unfold grp_blocks, grp_mpds, grp_sw, pt_mpds. cbn -[smpd mpd_init has_A]. destruct (has_A id); reflexivity. }
    split. { left. split; [reflexivity|]. split; [exact SWC|]. split; [exact IDB|]. split; [reflexivity|]. deexists 9. reflexivity. }
    eapply (aobj_munch asegs AL _ (hcs_ok asegs R HIA h2) _ m3 m'); [exact WC2| exact MU| exact OA].
    all: match goal with |- ?gg => idtac "WRAP-LEFT:" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis GF : ecp_group_free_stmtA asegs R HIA A_MT A_ECP_GROUP_FREE.
  Hypothesis GI : ecp_group_init_stmtA asegs R HIA A_MT A_ECP_GROUP_INIT.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Hypothesis HCASE : forall id, 1 <= id <= 13 -> gl_case_stmtA id.

  Local Ltac2 Set LiaOrc.tbl := fun () => "04M0@D21329468335.107D21329468335.108D23379772182.108D35881667587.107D35881667587.108D41568344648.175D41568344648.177D50797141399.175D50797141399.177D62364551523.175D62364551523.177D831362248.175  D831362248.177  K56805637772.175K56805637772.177L11608468103.4  L11973804984.7  L12286268936.8  L12808385313.0  L12955032374.1  L1429900444.1   L15756354262.4  L16086204375.5  L16511405110.1  L18033969518.174L18199801473.11 L18199877676.4  L18201925559.8  L19052871331.2  L19093615534.174L20067778870.1  L20491550261.174L20911126033.1  L21765854580.104L21887662552.103L21887662552.173L22377460530.174L23204654197.174L24266973557.174L25296973522.0  L26397299566.174L26977931445.174L27462778286.174L27775132660.104L28522407662.174L28812006459.170L29698248437.174L32109246386.174L32195670001.171L32195670001.173L32506135547.10 L33510041944.104L33510041944.173L33720279442.0  L34150196914.174L34290115814.103L34678196278.1  L35653441506.7  L35744910738.0  L36837110646.7  L37714553091.1  L38234586422.1  L38235734261.1  L3848171822.174 L3860859083.7   L39020528466.0  L39939650836.173L40011557266.0  L40281191306.3  L40285201202.174L40834179097.107L41562522425.172L41598571912.8  L41644840430.174L41784667702.1  L41942189128.1  L42036188562.0  L43055340993.101L43712168354.7  L43884818473.2  L44306232309.174L4453263026.174 L44767745618.0  L45290867399.7  L45556701510.1  L46460681476.4  L47026086197.174L47875574894.174L4840117301.174 L4911553134.174 L49122142130.174L49154504626.174L49738096501.174L50008104942.174L50012526354.0  L50219795154.0  L50790761713.7  L50845182722.2  L51073644590.174L51161527090.174L51643331647.3  L51647477002.2  L52037157650.0  L52343458874.8  L52458016437.174L53511422901.174L54748384003.104L54930779452.17 L54931304123.11 L54931304123.14 L55867396914.174L56217006898.174L56231227893.174L5631186743.171 L5631186743.173 L56511072978.0  L56795178491.2  L57784374802.0  L59242620976.1  L59308628304.1  L59315053158.3  L5977539758.174 L59949296182.1  L60098763854.3  L62018535662.1  L6269429426.174 L63507783478.1  L64202225454.174L66083662040.104L66083662040.173L66151427842.16 L66457424050.174L66527532485.172L66610753222.5  L66748138130.6  L68354050849.0  L68362534512.1  L7192832788.10  L7262368338.0   L7551582837.174 L8800852016.1   L8826111922.174 L8939493197.1   L9569258675.6   L9716869748.103 L9962237875.104 L9962237875.173 Q10337572782.173Q10478161754.108Q11413810414.173Q12043094861.173Q12941545869.173Q14007824077.173Q14749744826.173Q15067252493.173Q15643289079.173Q15643324129.103Q16858559674.173Q18034340698.173Q18235909853.107Q18694146040.107Q19094030746.173Q19195952558.173Q19210079851.173Q20272159470.173Q21106421178.173Q21798041355.107Q22712450012.107Q22712450012.108Q23512175082.105Q24273904250.173Q24665950363.107Q24665950363.108Q2498330362.173 Q25157988860.107Q25513505925.106Q25513505925.107Q25662358575.107Q26396879194.173Q27463124890.173Q27574715499.173Q27668705378.106Q27668705378.107Q28522831066.173Q28638896811.173Q29704633323.173Q31228709292.107Q31394594844.107Q31830858926.173Q32655339255.173Q32655500769.104Q32899233262.173Q33964954158.173Q34362328320.107Q34362328320.108Q34362328320.175Q34362328320.177Q34594270861.173Q35014437530.107Q35657893837.173Q35765334355.104Q35765334355.105Q36100285562.173Q36197446906.173Q36552412173.173Q37618689357.173Q37708009648.172Q37708009648.174Q37710196405.171Q37710310660.173Q3830195220.173 Q3830427394.104 Q3847801626.173 Q3964111339.173 Q3967391067.173 Q3967801066.171 Q39759059149.173Q39939554818.104Q39939650836.173Q41645207514.173Q41761254827.173Q42347221818.173Q42755330731.173Q42755330731.175Q42823333934.173Q42837723883.173Q44648677751.173Q44648843873.104Q45124942924.172Q45124942924.174Q46277511482.173Q46778560378.173Q47875749466.173Q4911980634.173 Q49698585326.105Q49698585326.106Q50007746010.173Q50125892523.173Q5029865003.173 Q51073991194.173Q51190038763.173Q51235796833.104Q51236027511.173Q52266522923.173Q52770801210.173Q53969758199.107Q53971971953.173Q54057591853.107Q55441726254.173Q55882693690.173Q56505905262.173Q58200941837.173Q58640001006.173Q59111977549.173Q5977718426.173 Q60176124045.173Q6098222955.173 Q61241876941.173Q62362305379.174Q62362305379.176Q62364551523.175Q62364551523.177Q62405693620.172Q62405693620.174Q6416456232.107 Q64202640666.173Q64875421251.173Q64875798002.171Q65364254318.173Q65388898347.173Q6544224762.173 Q66522037140.173Q66522067074.104Q67426116409.107Q67528989526.107Q67528989526.108Q68077988642.172Q68077988642.174Q831362248.175  Q831362248.177  Q833576648.174  Q833576648.176  Q9273424238.173 Q9843367298.103 Q9843398292.173 00000j01j02g03P04B04C04D05A06;06Y07407R07m08^09L09[0:10:M0:N0:Q0:U0:c0;50;80;D0;E0;Q0;R0;Z0;f0;i0<50<80<D0<P0<\0<h0=40=@0=A0=M0=Y0=e0>10>=0>M0>Y0>e0?10?=0?>0?J0?V0?W0?c0?o0@20@L0@M0@Y0@\0@_0@c0@o0AJ0AK0B20B30B<0BH0BV0Bb0C90CE0CH0CL0CM0D40DI0DP0D\0Dh0Di0Dj0Dm0E:0EF0ER0E^0Ej0F60FB0FN0FZ0F[0F\0G70G>0GJ0GV0Gb0Gh0Gi0HE0HQ0H]0Hi0Hj0Hk0Hl0I80ID0IP0I\0Ih0Ii0Ij0Ik0In0Io0J80JD0JG0JQ0JT0J`0Jc0Jo0K;0KG0Ka0Km0Kn0L>0LQ0LR0LU0M<0M=0MI0ML0MX0M[0Ml0N80ND0NP0N\0OR0O^0O_0O`0Oa0Om0On0P:0PF0PR0PX0PY0Pe0Pk0Q70Q80QD0QP0QQ0Ql0RM0RY0Re0S[0TT0T`0Tl0UJ0Un0Uo0V50V;0V<0Vj0W[0Wa0Wb0Wc0X10X70XC0XO0X[0Xg0Y30Y40Y50YM0Yb0Yc0Z10Z20Z>0ZJ0ZV0Zb0Zc0Zd0Zj0[00[60[<0[X0\40\:0\;0\A0\G0\H0\d0]@0]F0]G0]S0]b0^10^=0^>0^J0^V0^n0_F0_R0_^0_d0_j0`@0`V0`\0`]0`^0`d0`e0a10a=0a>0aJ0aX0af0ag0b30b?0bK0bL0bX0bY0b_0b`0ba0bb0c:0cO0cg0d<0dI0dV0db0dh0dn0e40e@0eA0eM0ei0fE0g30ga0hU0h[0ha0i90iN0if0j;0jG0jc0k?S1R5NEEDR2ra2sp1A2lo3LOS3SLO3NER3SPR3POS2TB2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp2s01A2lo3LOS3SLO3NER3SPR3POS2TB2HB5Ha_st5Hl_st2s1S1R5NEEDR2ra2sp2s21A2lo3LOS3SLO3NER3SPR3POS2TB2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1A5SPTOP2TB2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01A5SPTOP2TB2HB5Ha_st5Hl_st2s12s2FFS1R5NEEDR2ra2sp1A2id2lo3LOS3SLO3NER3SPR3POS2TB2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1A2lo3LOS3SLO3NER3SPR3POS2TB2HB5Ha_st5Hl_stS2ra2sp1A2id2TB2HB5Ha_st5Hl_stS2ra2sp1A2TB2HB5Ha_st5Hl_stS2ra2sp1A2id2TB2HB5Ha_st5Hl_stS2ra2sp1A2TB2HB5Ha_st5Hl_stS1R5NEEDR2sp1A2id2lo2SX3SLO3NER2TB2HB5Ha_st5Hl_stS1R5NEEDR2sp1A2lo2SX3SLO3NER2TB2HB5Ha_st5Hl_stS2id3IDB2K13NE0S1R3HIA1h1d2D02h24HFR2S1R5NEEDR2sp1A2lo2SX3SLO3NERSS1AS2spS1R2lo3LOS3ALOS1R3HIA1h2sp5SPTOPS1AS2ra2sp1A2TBFS2sp1A2lo2SXFS2id3IDRS2ra2sp1A2TBS1AS2ra2sp1A2TBS1AS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBSS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBFS2ra2sp1A2TBS2ra2sp1A2TBSS2ra2sp1A2TBS2ra2sp1A2TBS1AS1R3HIA1h2sp2lo5SPTOP4HTOPSS2sp1A2lo2SXS1AS1AS2loS2ra2sp1A2TBS1R5NEEDR2sp2lo3LOS3SLO3NERSS1R5NEEDR2ra2sp1A2lo3SLO3NER3SPR3POS2TBSS1R3HIA1hS2ra2sp1A2TBS1R2ra2sp1A2TBS2ra2sp1A2TBS1R2sp2lo3LOS3ALO2dd2I4S2ra2sp1A2TBS1AS2spSS1R5NEEDR2ra2sp1A2lo3SLO3NER3SPR3POS2TBS1R2sp2lo3SLO3NER3NEAS2sp2loS2ra2sp1A2TBS2ra2sp1A2TBSFS1AS1R3HIA1h3BUDS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBSSS1R5NEEDR2sp2lo3LOS3SLO3NERS2sp2loS2ra2sp1A2TBS2ra2sp1A2TBS2id3IDB3NE0S2id1CSS1R5NEEDR2sp1A2lo2SX3SLO3NERS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBFFFS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBSFSS1AFS2id2K11CS2ra2sp1A2TBS1AS1R2lo3LOSS1RS2ra2sp1A2TBS1AS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2sp2r03SPA1q1r1H2H02q02H4S2ra2sp1A2TBFS1R3HIA1h2h23HV2S1R3HIA1h1d4BUDF2D0SS1RS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACP3NER3SPRSS2ra2sp1A2TBS1AS2ra2sp1A2TBS1AS1R2sp2lo3SLO3NERS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1R1A3ELO2TBS1R5NEEDR2sp2s21A2lo3LOS3SLO3ALO3NER2TB2HB5Ha_st5Hl_stS1R1A3ELO2TBFFFS1R1A3EHI2TBFS2sp1A2lo2TBS2sp1A2lo2TBS1R1A3EHI2TBS1A2TBFS1R1A3EHI2TBS1A2TBS1R1A3ELO2TBFS1R1A3ELO2TBS1R1A3EHI2TBFS2ra2sp1A2TB2HB5Ha_st5Hl_stS2sp2s01A2TB2HB5Ha_st5Hl_st2s12s2S2sp1A2TB2HBS1R1A3EHI2TBS1R5NEEDR2ra2sp1A2lo3LOS3SLO3ALO3NER2TB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01A2lo3LOS3SLO3ALO3NER2TB2HB5Ha_st5Hl_st2s1S1R1A3EHI2TBS1R1A3EHI2TBS2ra2sp1A2lo2TB2HB5Ha_st5Hl_stS2sp2s01A2lo2TB2HB5Ha_st5Hl_st2s12s2FS1A2TBS1A2TBFS1R5NEEDR2ra2sp1A2lo3SLO3NER2TB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01A2lo3SLO3NER2TB2HB5Ha_st5Hl_st2s1S1A2TBFFS1R1A5ALWF'2TBS1A2TBS1R1A3ELO2TBS2sp1A2lo2TBS2sp1A2lo2TBS1R1A3ELO2TBS1R1A3ELO2TBFFS1A2id2TB2HB5Ha_st5Hl_stS1A2TB2HB5Ha_st5Hl_stFS1R1A5ALWF'2TBFS2sp1A2TB2HBS2sp1A2TB2HBS1R1A3EHI2TBS1R1A3EHI2TBFFS1A2TBS1A2TBS1A2TBS1A2TBS1R5NEEDR2sp1A2lo3SLO3NER2TBS1R5NEEDR2sp1A2lo3SLO3NER2TBS1A2TBFS1A2TBS1A2TBFS1R5NEEDR2sp1A2lo3SLO3NER2TBS1R5NEEDR2sp1A2lo3SLO3NER2TBS1A2TBFS1R1A3EHI2TBS1A2TB2HB5Ha_stS1A2TB2HB5Ha_stS1R1A3ELO2TBFS2sp1A2lo2TBS2sp1A2lo2TBS2ra2sp1A3SPR3AL83POS2TBS2ra2sp1A3SPR3AL83POS2TBS1R1A3EHI2TBS1R1A3EHI2TBS1A2TBS1A2TBS2sp1A3SPR2TB2HB5Ha_stS2sp1A3SPR2TB2HB5Ha_stS1A2TBFFS1A2TBFS2sp1A2lo2TBS2sp1A2lo2TBFS1R1A3EHI2TBS1R1A5ALWF'2TBS1R1A5ALWF'2TBFS1R1A3ELO2TBS1R1A3EHI2TBS1R1A3ELO2TBFS1R1A3ELO2TBFS1A2TBFFFS1A2id2TB2HB5Ha_st5Hl_stS1A2TB2HB5Ha_st5Hl_stS1A2id2TB2HB5Ha_st5Hl_stS1A2TB2HB5Ha_st5Hl_stS1A3POS2TB2HBS1A3POS2TB2HBS1R1A3ELO2TBS1A2TBS1A2TBS1A2TBS1R1A3ELO2TBFS1R1A3EHI2TBS1R5NEEDR2sp1A2lo3SLO3NER2TBS1R5NEEDR2sp1A2lo3SLO3NER2TBS1R5NEEDR2sp2s21A2lo3SLO3NER2TB2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1A2lo3SLO3NER2TB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01A2lo3SLO3NER2TB2HB5Ha_st5Hl_st2s12s2S1A2TBS1A2TBS1A2id2TB2HB5Ha_st5Hl_stS1A2TB2HB5Ha_st5Hl_stS1A2id2TB2HB5Ha_st5Hl_stS1A2TB2HB5Ha_st5Hl_stS1R1A3ELO2TBS1R5NEEDR2sp1A2lo3SLO3NER2TBS1R5NEEDR2sp1A2lo3SLO3NER2TB". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG GF GI HCASE"] Lemma A_ecp_group_load_walk : ecp_group_load_stmtA asegs R HIA A_MT A_CA A_ONE A_ECP_GROUP_LOAD_E.
  Proof.
    unfold ecp_group_load_stmtA, A_ECP_GROUP_LOAD_E, ECP_GROUP_SIZE. intros until d.
    intros HH HK0 G DIS CW SX OBJ IDB ST LOS SLO SPTOP SPA TP MI RAE BUD UWO BUDF C24H -> ->.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (arl_need_ecp_rt R) as NER.
    assert (NEA : arl_need_amem R <= arl_need_rt R) by (unfold arl_need_rt; clear; lia).
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR HAP]. change (blkfacts L (LB ++ LF)) in HBR.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. ddestruct IMG' as (EGOT & ELO & EHI).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    dpose G as (_ & AL8 & POS & _).
    dpose G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT0 & _). pose proof (rw_cells_bound _ _ _ _ HT0) as TB. cbn [cells_size csize Nat.add length grp_tail_cells] in TB. clear HT0.
    pose proof (aobj_crange _ _ _ _ _ _ OBJ) as CRA.
    set (LBf := grp_free_LB g LB) in *.
    assert (SUBF : forall b, In b LBf -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (presW_sub_blocks asegs R HIA h LB LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] HH ltac:(clear; lia)) SUBF) as PXA.
    pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (conj MI I) as MIbox. pose proof (conj G I) as Gbox. clear G.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    do 7 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
        pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB
      end end.
    rewrite EGOT in GOT.
    (* [comment removed for export] *)
    do 3 zstep. clear GOT GSB AB.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct MIbox as [MIm _]. destruct Gbox as (G & _).
    assert (G1 : ecp_group_at asegs A_MT m1 LB A g).
    { eapply ecp_group_at_munch; [exact G| exact MU0| exact WM0| exact MIm| assumption| cbn; clear - SX ALO LOS; lia|].
      intros dd Hd O. ddestruct (mpdr_blk_factsA asegs L m LB (LB ++ LF) dd) as (_ & _ & I3 & I4 & _); [| exact O| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| cbn; clear - I3 I4 ALO LOS; lia].
      ddestruct G as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX' & MY' & MZ') & MN & _).
      unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    clear MU0 WM0 MIm G.
    (* [comment removed for export] *)
    zstep.
    pose proof GF as SG. unfold ecp_group_free_stmtA, A_ECP_GROUP_FREE, ECP_GROUP_SIZE in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG with (h := h) (LB := LB) (LF := LF) (A := A) (g := g) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia);
        first [ exact HK1 | exact G1 | exact DIS | exact LOS | exact TP | exact UWO | reflexivity
              | lazymatch goal with
                | |- HM _ _ _ h LB LF _ => assumption
                | |- client_wrange _ _ _ _ A 192 => eapply (client_wrange_weak L); [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia]
                | |- A + 192 <= lo \/ _ => clear - SX; lia
                | |- aobj _ _ _ _ A 192 => assumption
                | |- stk _ _ lo _ => assumption
                | |- lo <= _ => clear - SLO NEEDR NER; lia
                | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- mem_inv _ _ => assumption
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold group_load_PHI in BUD; unfold GF_PHI, grow_PHI in *; unfold AVOL_CALL in *; clear - BUD; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold group_load_FRn, calls_FR in BUDF; unfold GF_FR, fr_charge in *; clear - BUDF D0; lia
                end
              | match goal with |- ?gg => idtac "GF-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXg & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & GZ & GZC).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, PXg by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia).
    unfold ECP_GROUP_SIZE in PXg. change (grp_free_LB g LB) with LBf in HH2, GZ, PXg.
    replace (ret_pc (Z_to_bv 64 0xd09b4)) with (Z_to_bv 64 0xd09b4 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (CRS : client_range L (LBf ++ fdata LF) (bv_unsigned sp + -32) A 192).
    { eapply (client_range_of_wrange L); [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia]. }
    lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -32) _ |- _ =>
      pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ PXg FRx ltac:(apply client_range_stack; cbn; clear; lia) ltac:(cbn; clear - SX SLO NEEDR NER; lia)) as FR2; clear FRx end.
    assert (PXA2 : presW asegs R HIA h LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m2).
    { eapply presW_call; [exact PXA| exact PXg| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
      intros x Hx. exact Hx. }
    assert (OBJ2 : aobj asegs AL (hcs asegs R HIA h) m2 A 192).
    { lazymatch goal with OBJx : aobj _ _ (hcs _ _ _ h) m1 A 192 |- _ =>
        eapply (presA_aobj asegs R (hcs asegs R HIA h)); [exact CSOK| exact PXg| exact OBJx| exact CRS| clear - LOS SLO NEEDR NER; lia| intros x Hx; eapply hcs_below_top; exact Hx] end. }
    clear PXA GZ PXg G1 SG.
    repeat match goal with H : aobj _ _ _ m1 _ _ |- _ => clear H | H : stk _ m1 _ _ |- _ => clear H | H : mem_inv _ m1 |- _ => clear H | H : HM _ _ _ _ _ _ m1 |- _ => clear H
                         | H : ainv_laws _ _ |- _ => clear H | H : kinv_laws _ _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (hcs_ok asegs R HIA h2) as CSOKc.
    pose proof (crange_mono _ _ _ _ HCS2 SCS) as SCSc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OBJ2) as OBJc.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof GI as SI. unfold ecp_group_init_stmtA, A_ECP_GROUP_INIT, ECP_GROUP_SIZE in SI.
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo).
    { eapply SI with (h := h2) (LB := LBf) (LF := LF) (A := A) (lo := lo) (LBg := LBf) (junk := repeat (Z_to_bv 8 0) 192);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia);
        first [ exact HH2 | exact GZC | exact AL8 | exact POS | exact ST2 | exact LOS | exact MI2 | exact OBJc | reflexivity
              | (rewrite HT2; clear - SPTOP; lia) | (clear - SLO NEEDR NER NEA; lia) | (clear - SPA; Z.div_mod_to_equations; lia) | (clear - SX; lia)
              | (rewrite HT2; eapply (client_wrange_weak L); [exact CW| intros b Hb; exact Hb| clear - LOS SLO NER NEEDR; lia| clear; lia| clear; lia])
              | match goal with |- ?gg => idtac "GI-LEFT:" gg end ]. }
    clear SI. cbv beta. intros ms' PO. unfold ecp_group_init_postA, ECP_GROUP_SIZE in PO.
    ddestruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & ip & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hp & -> & MUi & WMi & MI3 & GIc & ST3 & HH3).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MUi, ST3 by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia).
    replace (ret_pc (Z_to_bv 64 0xd09bc)) with (Z_to_bv 64 0xd09bc : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (WC : w_client (hcs asegs R HIA h) [(A, A + 192); (lo, bv_unsigned sp + -32)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (A + 192 - A) with 192 by (clear; lia); exact CRA|]. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
      eapply crange_sub; [exact SCS| clear; lia| clear; lia]. }
    assert (WC2 : w_client (hcs asegs R HIA h2) [(A, A + 192); (lo, bv_unsigned sp + -32)]).
    { unfold w_client in *. eapply Forall_impl; [| exact WC]. intros iv Hiv. eapply crange_mono; [exact HCS2| exact Hiv]. }
    eapply (rw_cells_transport asegs) in FR2; [| exact MUi| exact WMi| cbn [disjoint_from fst snd cells_size csize Nat.add]; clear - SX SLO NEEDR NER; lia].
    assert (PXA3 : presW asegs R HIA h LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m3).
    { eapply presW_munch; [exact PXA2| exact MUi| exact WMi| exact WC|].
      apply Forall_cons; [cbn [fst snd]; apply wcover_inside; cbn [inside fst snd]; left; clear; lia|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      ddestruct PXA2 as (_ & _ & _ & BLOW). eapply wcover_stack; [exact BLOW| exact (art_data_lo asegs R HIA)| clear - ALO LOS; lia| clear; lia]. }
    pose proof (aobj_munch asegs AL _ CSOKc _ m2 m3 _ _ WC2 MUi OBJc) as OBJ3.
    clear PXA2 MUi WMi OBJc OBJ2 GZC ST2 MI2 HH2 MU WM.
    (* [comment removed for export] *)
    ddestruct GIc as (HD & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & HT & _).
    apply proj1 in MP. apply proj1 in MA. apply proj1 in MB. apply proj1 in MX. apply proj1 in MY. apply proj1 in MZ. apply proj1 in MN.
    cbn [md_addr mpd_init grp_init g_P g_A g_B g_G g_N pt_X pt_Y pt_Z pt_init md_p md_sg md_n md_pad] in MP, MA, MB, MX, MY, MZ, MN.
    replace (A + 56 + 16) with (A + 72) in MY by (clear; lia). replace (A + 56 + 32) with (A + 88) in MZ by (clear; lia).
    unfold grp_tail_cells, grp_init in HT. cbn [g_pbits g_nbits g_h g_hpad g_modp g_tpre g_tpost g_tdata g_T g_Tsize] in HT. unfold grp_head_cells, grp_init in HD. cbn [g_id g_idpad] in HD.
    pose proof (munch_refl [(A, A + 192)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    pose proof (hm_wlow asegs R HIA h2 _ _ m3 HH3) as WL3.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by (clear - POS TB; lia); clear - K0 POS; lia]. clear K0.
    zstep.
    assert (AL7 : Z.land A 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact AL8 | clear - AL8; Z.div_mod_to_equations; lia]).
    zstep. if_cases KA; zify_cond KA; [| exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia]. clear KA AL7.
    do 8 zstep.
    if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (IDR : 1 <= id <= 13).
      { rewrite ?unsigned_lit_wrap in K1. destruct (Z.eq_dec id 0) as [E0|NE0]; [subst id; exfalso; vm_compute in K1; clear - K1; first [lia | discriminate K1 | (apply K1; reflexivity)]|].
        rewrite ?Z.mod_small in K1 by (clear - IDB NE0; lia). clear - K1 IDB NE0. lia. }
      clear K1.
      assert (CELLS : forall idv, id = idv -> gl_init_cells m0 A idv ip p1 p2 p3 p4 p5 p6 p7 hp).
      { intros idv <-. unfold gl_init_cells. split; [exact HD|]. split; [exact MP|]. split; [exact MA|]. split; [exact MB|]. split; [exact MX|]. split; [exact MY|]. split; [exact MZ|]. split; [exact MN| exact HT]. }
      assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by (clear - IDR; lia).
      destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]; subst id.
      (* [comment removed for export] *)
      all: do 7 zstep.
      1: eapply (HCASE 1 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 1 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 2 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 2 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 3 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 3 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 4 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 4 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 5 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 5 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 6 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 6 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 7 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 7 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 8 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 8 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 9 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 9 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 10 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 10 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 11 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 11 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 12 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 12 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      1: eapply (HCASE 13 ltac:(clear; lia)) with (h := h) (h2 := h2) (g := g) (lo := lo) (d := d) (m := m);
         first [ exact (CELLS 13 eq_refl) | exact AL8 | exact POS | exact FR2 | exact LOS | exact SLO | exact SPTOP | exact SPA | exact SX | exact TP | exact RAE
               | exact CRA | exact CW | exact UWO | exact PXA3 | exact HT2 | exact HS2 | exact HF2 | exact HCS2 | exact HV2 | exact HFR2 | exact BUD | exact BUDF | exact C24H
               | assumption | match goal with |- ?gg => idtac "CASE-PRE-LEFT:" gg end ].
      all: match goal with |- ?gg => idtac "DISPATCH-LEFT:" gg end.
    -
      (* [comment removed for export] *)
      assert (NID : ~ (1 <= id <= 13)).
      { intros C. rewrite Z.mod_small in K1 by (clear - C; lia). clear - K1 C. lia. }
      clear K1.
      do 12 zstep.
      lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp); rename STx into STf end.
      zstep.
      lazymatch goal with |- _ (MS ?RR _ _ _ _ _ _) => let v0 := getx RR 10%positive in replace v0 with (Z_to_bv 64 (-20096)) by (apply bv_eq; vm_compute; reflexivity) end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold ecp_group_load_postA, ECP_GROUP_SIZE.
      deexists 14. dexists m9, mo9, h2, (-20096), (grp_init A ip p1 p2 p3 p4 p5 p6 p7 hp), ([] : list blk), LBf.
      split; [reflexivity|]. split; [assumption|]. split; [exact STf|]. split; [exact MF9|].
      split; [lazymatch goal with PXx : presW _ _ _ h LBf LF _ _ _ m m9 |- _ => exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ PXx) end|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|]. split; [exact HCS2|].
      split; [unfold group_load_PHI, GF_PHI in *; unfold grow_PHI; unfold AVOL_CALL in *; clear - HV2; lia|].
      split; [unfold group_load_FRn, GF_FR, calls_FR, fr_charge in *; clear - HFR2 D0; lia|].
      split; [assumption|].
      split; [intros b; cbn [In]; tauto|]. split; [intros b Hb; destruct Hb|].
      split; [eapply ecp_group_at_init; [eassumption| exact AL8| exact POS| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption]|].
      split. { intros d1 d2 H1 H2 NE O1 O2. exfalso. unfold grp_mpds, grp_init, pt_mpds, pt_init, mpd_init in H1. cbn in H1.
               destruct H1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O1; discriminate O1. }
      split; [reflexivity|].
      split. { right. right. left. split; [reflexivity|]. split; [exact NID|]. split; [reflexivity|]. deexists 9. split; [reflexivity| exact I]. }
      assumption.
    all: match goal with |- ?gg => idtac "MAIN-LEFT:" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GLM.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00<0>L19052882261.2L25296973522.0L33720279442.0L39020528466.0L40011557266.0L42036188562.0L44767745618.0L50012526354.0L50219795154.0L52037157650.0L56511072978.0L7262368338.0 00000800900:00;00<00=00>00?00@00A00B00CS2id3HidSSSSSSSSSSS". (* [comment removed for export] *)
Theorem A_ecp_group_load_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_main ()) "PR,$48.PHIA,(49.$1.R1.)P,(4:.(22.R2.))P,(18.=(4;.R3.))P,(18.=(4<.R4.))P,(4=.(18.(4>.(26.R5.))(4?.(26.R5.)))(18.(50.(26.R5.))(51.(26.R5.))))P,Ph,(0.$1.R6.R5.)PLB,(2.$3.)PLF,(2.$3.)Pm,P,(4.&40.)(6.(4.&8.))P,(:.$1.R:.R9.R4.R3.R2.R1.)(52.$8.(53.(2;.$8.$8.)$8.(54.$8.$8.)R4.))P,(55.$1.R7.R6.$3=.$56.)P,(57.$1.R8.R7.$3=.$58.)P,(59.R9.R8.+9.)P,(59.R:.R9.+=.)(5:.$1.R;.R:.$3=.$3>.$3?.$5;.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG NEEDR NEEDA DIMG HMND GF GI H9 H13.
  eapply A_ecp_group_load_walk; try eassumption.
  intros id Hid.
  assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by (clear - Hid; lia).
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case1 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case2 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case3 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case4 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case5 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case6 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case7 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case8 R HIA IMG)].
  - exact H9.
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case10 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case11 R HIA IMG)].
  - apply gl_sw_wrap; [exact NEEDR| exact DIMG| reflexivity| clear; lia| exact (case12 R HIA IMG)].
  - exact H13.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
