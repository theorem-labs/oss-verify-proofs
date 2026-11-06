(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_add_abs_W P_mpi_add_abs_C P_mpi_sub_abs_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_journey
     A_mpi_core_sub A_mpi_core_sub_int A_amemset A_amemcpy A_mpi_add_abs_W A_mpi_sub_abs A_mpi_sub_abs_ng A_mpi_add_sub A_mpi_stmtA_sz A_mpi_stmtA_ng_sz.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_mpi_sub_abs_ng_sz () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.A.A_mpi_opnd.opnd_atA"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.A.A_mpi_sub_abs_ng.sub_abs_PHI0"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.A.A_mpi_sub_abs_ng.sub_abs_FR0"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.A.A_mpi_stmtA_ng_sz.sub_abs_ng_Rsz"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "WS.SA_FRAME_A"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_NEGATIVE_VALUE"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "WS.SA_POST_A"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.A.A_mpi_core_sub.MPI_CORE_SUB_STACK_A"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.A.A_mpi_core_sub.A_MPI_CORE_SUB"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lseg"; "WS.rideS"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.A.A_mpi_journey.JBA"; "OSSVerify.KrLib.A.A_mpi_journey.BJA"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_SUB_ABS"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.A.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "OSSVerify.KrLib.LibA.ARt.arl_calloc"; "OSSVerify.KrLib.A.A_mpi_sub_abs.A_WRAP_CALLOC_SA"; "OSSVerify.KrLib.LibA.ARt.arl_amemcpy"; "OSSVerify.KrLib.A.A_mpi_sub_abs.A_ASAN_MEMCPY_SA"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_mpi_sub_abs.A_ASAN_MEMSET_SA"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "mpi_sub_abs_ng_stmtA_oz"; "OSSVerify.KrLib.A.A_mpi_stmtA_ng_sz.mpi_sub_abs_ng_stmtA_sz"].


Definition mpi_sub_abs_ng_stmtA_oz (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(<.O4.O3.R2<.R:.R2=.(=.&40.R2:.)R7.)P,(<.O4.O3.R2=.R;.R2>.(=.&40.R2;.)R7.)P,(>.R:.R9.)P,(>.R;.R9.)P,(>.R;.R:.)P,(?.(10.$11.(12.R=.)$13.))P,(14.(15.R=.)(15.R>.))P,(16.R?.R>.R<.(=.&40.R31.))P,(16.R10.R>.R=.(=.&40.R32.))P,(17.(18.O3.)(19.$2.R36.(1:.R35.))R>.(1;.R10.)+10.)P,P,(10.$11.(12.R11.)$1<.)(17.(18.O3.)(19.$2.R38.(1:.R37.))R10.(1=.R12.)(1>.+4.(15.R12.)))P,(17.(18.O3.)(19.$2.R38.(1:.R37.))R10.(1;.R11.)+10.)P,P,(10.$11.(12.R12.)$1<.)(17.(18.O3.)(19.$2.R3:.(1:.R39.))R12.(1=.R13.)(1>.+4.(15.R13.)))P,(1?.O3.R3:.R39.(=.&40.R37.)(20.O4.O3.O2.R3;.)R15.)P,P,(?.(10.$11.(12.R16.)$21.))(22.(14.(23.(1=.R17.)(1>.+4.(15.R17.)))R14.)(14.(=.&40.R39.)(1=.R17.)))P,(24.O4.R19.R14.(=.&40.R39.))P,(14.(25.O3.)R15.)P,(14.R16.(26.(26.(=.&40.R3;.)+90.)(27.O3.)))P,(14.(=.&40.R3<.)(20.O4.O3.O2.R40.))P,(10.$8.(28.(=.&40.R3=.)+10.)=)P,(10.(3.&40.)R3<.(29.&40.(2:.O3.)))P,(2;.O4.R1?.)P,(10.$8.(28.(=.&40.R41.)+2.)=)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R45.)R21.R1?.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R46.)R22.R1?.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R47.)R23.R1?.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(2?.(14.=R1.)(30.R1.(1>.+4.(15.R23.))))(10.$31.(32.O4.(33.(23.(1=.R24.)R2.)))$34.)(10.$31.(35.(1=.R23.)(1>.+4.(15.R23.)))$34.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(2?.(14.=R1.)(30.R1.(1>.+4.(15.R23.))))(10.$31.(32.O4.(33.(23.(1=.R24.)R2.)))$34.)(10.$31.(35.(1=.R23.)(1>.+4.(15.R23.)))$34.)P,P,(10.$11.(12.R23.)$13.)(14.(23.(23.(1=.R24.)(1>.+4.(15.R24.)))+8.)(36.+2.+2?.))P,(14.(23.(37.O4.O3.O2.R4;.)(38.R25.R24.R23.))$39.)P,(3:.O4.R28.(25.O3.)(3;.O4.O3.O2.R4<.)(=.&40.R42.)(=.&40.R48.)R22.)P,(3<.O3.(1;.R27.)+10.R23.)P,(3<.O3.(1;.R27.)+10.R24.)P,(3<.O3.(1;.R27.)+10.R25.)P,(14.(23.(3=.O4.O3.O2.R50.)(3>.R26.))$3?.)P,(10.(3.&40.)R45.(29.&40.(1;.R2;.)))P,(10.(3.&40.)R45.(29.&40.(1;.R2;.)))P,(10.(3.&40.)R45.(29.&40.(1;.R2;.)))(40.O4.(41.O4.O3.O2.R51.R50.R4?.R4>.R4:.R49.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R32.R31.R54.R53.R52.R2>.(42.R53.R2>.R2=.R2<.)(38.R2>.R2=.R2<.)(3>.R2:.)R2;.R30.R2?.)(43.(44.(45.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R32.(29.&40.O1.)R31.(46.(3.&40.))R30.(47.O4.))R2?.))")
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
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition SA_FRAME_A := aa_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BUD : havol asegs R HIA h + sub_abs_PHI0 dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + sub_abs_FR0 d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 144 - arl_need_rt R.
  (* [comment removed for export] *)
  Hypothesis NGN : md_n dA <= nX.

  Definition SA_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "(41.$48.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(42.VLB,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(3>.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A []).
  Local Notation XJ1 An cnt := (XJA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A [(An, 4 * cnt)]).
  Local Notation XD0 := (XDA asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A).
  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Local Notation SH10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Local Notation SHA E := (Z_to_bv 64 (Z.shiftr E 3 + al_sb AL)).
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
  #[using="IMG JC SLO2"] Lemma sa_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R22.R21.R20.R1?.R1>.R1=.)P,(14.(15.R1>.)VnX,)P,(22.(2?.(10.$8.R1>.=)(2?.(10.$8.(4=.R1?.)(26.(4>.VdA,)(4>.VdB,)))(10.$8.(4?.R1?.)+1.)))(22.(10.$8.R1>.$50.)(2?.(10.$8.R1>.$51.)(30.(4>.VdA,)(4>.VdB,)))))P,(14.R25.(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(14.R25.(3>.Vd,))(52.$48.(53.$48.VR,VHIA,R25.Vmo,)$54.(44.(45.R20.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1?.R1>.R1=.R1<.R1;.(29.&40.R21.)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)VF,(29.&40.+9>2:<.)Vfc,(46.(3.&40.))R23.(47.$48.)))")
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
  #[using="IMG JC SLO2"] Lemma sa_SIGN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R20.R1?.R1>.R1=.R1<.R1;.)P,(14.(15.R1<.)VnX,)P,(10.$8.(55.(56.R1=.))(26.(4>.VdA,)(4>.VdB,)))P,(14.R23.(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(14.R23.(3>.Vd,))(52.$48.(53.$48.VR,VHIA,R23.Vmo,)$54.(44.(45.R1?.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1>.R1=.R1<.(29.&40.VX,)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.(29.&40.(57.(2=.VR,)))R<.R;.R:.R9.R8.R7.R6.)VF,(29.&40.+9>28<.)Vfc,(46.(3.&40.))R21.(47.$48.)))")
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
    eapply sa_ret; [exact J2| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| left; split; [reflexivity| split; [unfold mpd_val; cbn [md_sg md_limbs]; rewrite HVV; clear; lia| reflexivity]]| exact BV| exact BF].
    all: match goal with |- ?g => idtac "SIGN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02I0@C11264273767.193C11264273767.194C237391055.195  D17444351834.194D26345934764.197D26351829262.194D27787129986.194D32872594577.194D32879014451.197D62012212072.197D64065028362.197D66314653779.197K19167344963.191K19167344963.192K25382859142.196K28441636224.196K36226586886.196K46334408099.193K46334408099.194K48349884702.191K48349884702.192K5410285399.195 K65977774223.196L10255219601.7  L10307112399.6  L1286294210.5   L146940511.10   L14858295739.5  L15477852824.1  L15721821085.5  L19173860537.5  L2188786020.3   L23100341967.173L23672846821.3  L2424955998.3   L25238078280.6  L25371356284.17 L26349732406.4  L26502719108.5  L2803465242.13  L2805482148.16  L28452252428.2  L2975768925.2   L29763661393.2  L29765106966.172L31411798818.8  L3370416396.3   L34125036709.12 L34401375065.9  L34403668265.10 L35663928186.7  L36237362428.4  L36721400998.14 L36723565080.10 L38235734261.1  L39463202031.1  L40613469158.2  L41126667518.5  L41590708471.3  L42633816569.1  L43178104794.9  L43343125556.5  L43878034250.5  L44631303542.4  L45586019928.7  L46160487540.173L46323034201.4  L47401054516.1  L47439038290.12 L47440770549.7  L47441212786.8  L47441213932.21 L47441213932.9  L48338281339.2  L49788159649.0  L53234647444.6  L5416286893.4   L54976812668.3  L56386468090.3  L57054567352.6  L57860742933.1  L58024129985.10 L58024409560.8  L58026150783.14 L58609956177.2  L59824495762.8  L59824836747.13 L59824839701.8  L59827007029.17 L60098763854.3  L60283674290.11 L60973657551.4  L61145405211.197L6141606276.1   L61929067222.172L65351099990.5  L65351280337.6  L65351281231.9  L65971907957.4  L66151427842.19 L66151427842.20 L68065932444.8  L68151462958.5  L6880072876.14  L7406239801.8   L9244221278.6   O11264273767.193O11264273767.194O237391055.195  O35105909750.196O36019832244.196O36632239767.191O36632239767.192O48199580980.196O50423766113.196O54539614568.191O54539614568.192P28441636224.196P46334408099.193P46334408099.194P48349884702.191P48349884702.192P5410285399.195 Q12370813529.176Q17207350632.177Q18468912438.200Q26207421841.177Q26207721832.178Q26222528972.175Q26345934764.200Q31654082872.177Q32879014451.200Q35717815871.199Q36708691079.200Q37323683587.178Q37618859566.175Q38669227488.198Q38669227488.199Q39212284437.178Q43925228937.178Q49149041523.198Q49149041523.199Q5470531635.175 Q5485174314.176 Q5485600919.177 Q59703481013.176Q60511567613.178Q60697995187.178Q6143569392.176 Q64065028362.200Q66314653779.200Q8886708880.175 Q9536767587.175 00000100200301201W02I03I03k04C04[04\04]05C05i06W06X07F07G07H07I07J07K08A08V08j09:09^09n0:20:B0:C0:O0:e0:m0;50;G0;H0;T0;h0;i0;j0;k0<20<90<U0<a0<i0=M0=N0>20>G0>H0>I0>J0>N0>R0>W0>X0>a0>f0>g0?70?>0?M0?g0@D0@E0@I0@J0@K0@L0@e0@f0@g0@h0A10A20A:0AB0AV0AZ0A[0A\0A]0Ad0Ae0Af0Ag0Ah0B20BV0Bc0Bd0Bh0CU0Ca0Cb0Cc0Cd0DB0DC0DR0Db0Df0Dl0E@0EA0EB0EC0ED0EE0EF0EG0EH0EI0EJ0EK0EL0EM0EN0EO0EP0EQ0En0F:0F;0FG0FS0F_0G20G>0GN0GO0GP0H>0HJ0HK0HL0HX0Hd0He0Hf0I20I>0IJ0IK0IU0Id0J00J10J20J>0JHFFFS1R3HIA1h2ra2sp1X3xs02hc1N3pXc2xs1n3TOP2X03SPR3HT12P04xs6h4LEN6S2ra2sp1X3xs01N3pXc2xs1n2HN2X03SPR2P0S2ra2sp1X3xs01N3pXc2xs1n2HN2X03SPR2N12P04xs6h4LEN6S1R2ra2sp1X3xs02lo4SLO21N3pXc2xs1n5NEEDR3LOS2X03SPR2P04xs6h4LEN6S2ra2sp1X3xs01N3pXc2xs1n4xs6h4LEN6S2ra2sp1X3xs01N3pXc2xs1nS1R2ra2sp1X3xs03pXc2xs1nFFS1R2sp3xs02lo1N3pXc2xs1n2HN3LOS3ALO2PCS1R2sp3xs02lo1N3pXc2xs1n2HN3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n5NEEDR3LOS3ALO2PCFS1R2sp3xs02lo4SLO21N3pXc2xs1n5NEEDR3LOS3ALO2PCFFFFFS2sp1X3xs02lo1N3pXc2xs1n2HN3x142N13XPc2x23x153x164POSTS2dA2dB1N2xs1n3HVV2c'S1R2sp2lo4SLO25NEEDRS1N2xs1n2HN4LEN1S1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScS1N2xs1n2HN4LEN1S2spS1N2xs1n2HN4LEN1FS2c'3HC03HC1S2ra2sp1X3xs03pXc2xs1nS1N1n2HNS1N1n2HNS1X1N3pXc1n2HN3XPcFS1N3pXc1n2HNS1R2sp2lo4SLO25NEEDRFFFS1N3pXcS1N3NR1S2ra2sp1X3xs01N3pXc2xs1n3NR1S1N2xs1n3LHIS1N1n2HNS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScFS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScS1R3HIA1h2sp2lo3TOP1HFFFS2loS2spS1N1nFS2dA2dB1NS3pXcFS1N2xs1n2HN4LEN1S2sp2loS2c'3HC03HC12KCS1R2sp1X2lo4SLO25NEEDR3DSXS2ra2sp1X3xs03pXc2xs1n2X03X16FS2spFFFS2sp1N3pXc2xs1n2HN3SPR2P0FFSS1N3pXc1nFS1N1n2HNS1N1n2HNS1R2sp2lo4SLO25NEEDRS2spFFFS1N3NR1FFFFS1R2lo3LOSS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR1a2NOS2dA2dB1N3BNDFS2spS2ra2sp1X3xs01N3pXc2xs1n2HN2X03SPR2P03P473LHIS2sp3SPA3SPRFFFS3pXc1n2r04XPAL1q1r1H2H02q02H4FS1N2xs1n2HN3NR1S1N2xs1n2HN4LEN1S2spS2xs1nS1N2xs1n2c'4xs6h3LV6FFFFFFFFFFFFFFFFFS2ra2sp1X3xs03pXc2xs1n2X03XALS1X3xs02xs1nFS1X3xs02xs1nS1X3xs02xs1nS1X3xs02xs1nS3xs01N3pXc2xs1n2HNS1X3xs02xs1nS3xs01N3pXc2xs1nFFS1R2sp3xs02lo4SLO22xs1n5NEEDR3LOS4SP643ALO3ACPS1X3xs02xs1nFFS1X3xs02xs1nS1X3xs02xs1nFFS1X3xs02xs1nS1X3xs02xs1nS1X3xs02xs1nFS3xs02xs1nS1X3xs02xs1n2X0S1X3xs02xs1nFFS1X3xs02xs1nS3xs02xs1n". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma sa_SUBINT : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pn,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs5,(3.&40.)Pxs7,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R1;.R1:.R19.R18.R17.R16.)P,(14.(15.R17.)VnX,)P,(10.$11.(12.R18.)$1<.)P,(2?.(14.+1.R18.)(14.R18.(15.R19.)))P,(10.$8.(55.(56.R1:.))(23.(26.(4>.VdA,)(4>.VdB,))(36.+2.(1>.+20.R19.))))P,(14.R20.(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(14.R20.(3>.Vd,))(52.$48.(53.$48.VR,VHIA,R20.Vmo,)$54.(44.(45.R1;.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1:.R19.R18.(29.&40.VX,)R17.(29.&40.+1.)R16.R15.R14.R13.R12.R11.R10.R?.(29.&40.R1<.)(29.&40.(23.VX,+:.))R>.(29.&40.(1>.+4.R1<.))R=.(29.&40.(57.(2=.VR,)))(29.&40.(23.(58.(23.VX,+:.)+3.)(57.(2=.VR,))))(29.&40.(23.(58.VX,+3.)(57.(2=.VR,))))R<.R;.R:.R9.R8.)VF,(29.&40.+9>254.)Vfc,(46.(3.&40.))R1>.(47.$48.)))")
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
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
    (* [comment removed for export] *)
    pose proof XARR as PU. rewrite <- (firstn_skipn (Z.to_nat n) xs) in PU. apply u32arr_app in PU. destruct PU as [PUlo PUhi].
    rewrite firstn_length_le in PUhi by (clear - HN LEN1; lia). replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) in PUhi by (clear - HN; lia).
    assert (LHI : Z.of_nat (length (skipn (Z.to_nat n) xs)) = N - n) by (rewrite length_skipn; clear - HN LEN1; lia).
    pose proof (munch_refl [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -112 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -112)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj PUlo I) as PUlo'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep. replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep. zstep. zstep. zstep.
    pose proof (A_mpi_core_sub_int_spec AL IMG) as SPC. unfold mpi_core_sub_int_stmtA, A_MPI_CORE_SUB_INT in SPC.
    acallxA_sp (bv_unsigned sp + -112)
      (eapply SPC with (X := pXc + 4 * n) (A := pXc + 4 * n) (n := N - n) (c := 1) (lo := lo) (xs := skipn (Z.to_nat n) xs) (ys := skipn (Z.to_nat n) xs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
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
             | match goal with |- ?g => idtac "CSI-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CSI-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned sp + -112) |- _ => rename H into ST6 end.
    match goal with H : u32arr asegs m6 (pXc + 4 * n) ?l, H2 : length ?l = length _ |- _ => rename H into XHI6; rename H2 into LEN6; rename l into xs6h end.
    match goal with H : lval xs6h (N - n) - ?cc * _ = _, H2 : 0 <= ?cc, H3 : ?cc <= 1 \/ ?cc = 1 |- _ => rename H into LV6; rename H2 into HC0; rename H3 into HC1; rename cc into c' end.
    (* [comment removed for export] *)
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -112 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -112)] mc m6) in HH6;
      [| exact MU| exact WM| unfold MPI_CORE_SUB_INT_STACK_A; solve_w_writable].
    match goal with H : rw_cells asegs m6 (bv_unsigned sp + -112) _ |- _ => rename H into SL6 end.
    assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
    { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SL6. }
    destruct PUlo' as [PUlo _].
    pose proof (u32arr_transport asegs _ mc m6 _ _ PUlo MU WM) as PUlo6. rewrite firstn_length_le in PUlo6 by (clear - HN LEN1; lia).
    specialize (PUlo6 ltac:(cbn [disjoint_from]; unfold MPI_CORE_SUB_INT_STACK_A; clear - HN XLSc SLO2 NEEDR P0 NR1; lia)).
    assert (XARR6 : u32arr asegs m6 pXc (firstn (Z.to_nat n) xs ++ xs6h)).
    { apply u32arr_app. split; [exact PUlo6|]. rewrite firstn_length_le by (clear - HN LEN1; lia). replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) by (clear - HN; lia). exact XHI6. }
    assert (HW6 : forall a, ~ outside [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -112 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -112)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
    { intros a NO. cbn [outside] in NO. unfold MPI_CORE_SUB_INT_STACK_A in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN SLO2 NEEDR; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    assert (DJF : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -112 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -112)] (bv_unsigned sp - 104) 104).
    { cbn; unfold MPI_CORE_SUB_INT_STACK_A. split; [clear - XLSc SLO2 NEEDR HN; lia| split; [clear; lia| exact I]]. }
    assert (DJX : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (N - n)); (bv_unsigned sp + -112 - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp + -112)] X 16).
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
    zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      eapply sa_SIGN; [exact J6| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| cbn [md_limbs]; rewrite VNEW; rewrite ?Z.mod_small in KC by (clear - HC0 HC1; lia); rewrite KC; clear; lia| exact BV| exact BF].
    - (* [comment removed for export] *)
      zstep. zstep.
      eapply sa_ret; [exact J6| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| right; right; split; [reflexivity|]| exact BV| exact BF].
      pose proof (limbs_val_bound (firstn (Z.to_nat n) xs ++ xs6h)) as BND.
      rewrite length_app, LEN6, firstn_length_le, length_skipn in BND by (clear - HN LEN1; lia).
      rewrite ?Z.mod_small in KC by (clear - HC0 HC1; lia).
      assert (C1 : c' = 1) by (clear - KC HC0 HC1; lia).
      rewrite VNEW, C1 in BND. replace (Z.of_nat (Z.to_nat n + (length xs - Z.to_nat n))) with N in BND by (clear - HN LEN1; lia).
      clear - BND. lia.
    all: match goal with |- ?g => idtac "SUBINT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L17897333080.102L17897333080.103L3074395878.101 L35116208202.102L35146090740.102L50393421374.99 L65305649816.101Q11801279589.105Q17056504010.101Q17056504010.102Q27566990629.104Q37145055361.101Q37145055361.102Q45914037331.102Q49698585326.103Q61867076138.10400000<00H00T00g01301F01R01j02602B02^02g03003803K03jS2ra3xra3xspS2ra3xra3xspS2ra3xra3xspS2ra3xra3xsp3lo'2LOS2ra3xra3xspS2ra3xra3xsp3lo'2LOS2ra3xra3xspS3xra3xsp2HB5Ha_st5Hl_stS3xsp3lo'2LOS3xsp3lo'2LOS3xra3xsp3lo'2HB5Ha_st5Hl_stS3xsp3lo'S3xsp3lo'S3xsp2HBS3xsp4SPR'2HB5Ha_stS3xra3xsp3lo'2LO2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="HIA IMG ra"] Lemma core_sub_n0A : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "PCS,P,$8.SpPxra,(3.&40.)Pxsp,(3.&40.)Pxgp,(3.&40.)Pxtp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Py0,(3.&40.)Py1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Py2,(3.&40.)Py3,(3.&40.)Py4,(3.&40.)Py5,(3.&40.)Py6,(3.&40.)Py7,(3.&40.)Py8,(3.&40.)Py9,(3.&40.)Py10,(3.&40.)Py11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PFF,(4.&5.(3.&40.))Pffc,(3.&20.)Pmm,P,(3.&40.)(5.(3.&8.))Plo',$8.P,(59.(2=.VR,)R24.)P,(2;.$48.R3.)P,(24.$48.R4.R3.(=.&40.R24.))P,(14.R4.(26.(=.&40.R25.)$5:.))P,(10.$8.(28.(=.&40.R26.)+10.)=)P,(5;.R29.R6.(26.(=.&40.R27.)R6.))P,(10.$8.(28.(=.&40.R29.)+2.)=)P,(10.(3.&40.)R1>.(29.&40.=))(5<.$48.(2=.VR,)R2<.Lms',$5=.(5>.(3.&40.)La6',(3.&40.)(5>.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(2?.(10.$5=.R3.(44.(45.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.(29.&40.=)R24.R23.R22.R21.R20.R2.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(5?.R2>.)R>.(46.(3.&40.))R1.(47.$48.)))(2?.(60.(61.(62.$8.$8.)(63.$8.$8.(26.(=.&40.R2=.)$5:.)(=.&40.R2=.))(4<.(62.$8.$8.)))R=.R1.)(2?.(64.$48.R=.R1.)(2?.(2;.$48.R1.)(24.$48.R1.R<.(=.&40.R2=.))))))))(44.(45.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(29.&40.$65.)R;.(46.(3.&40.))R:.(47.$48.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo'; intros CSOK' MI ST LO SPA16 SCS' RAE' ->. unfold A_MPI_CORE_SUB. unfold MPI_CORE_SUB_STACK_A in *.
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (cs_ok_sb _ _ CSOK') as SB64'.
    pose proof (bv_unsigned_in_range 64 xsp) as SPR'. unfold bv_modulus in SPR'. cbn [Z.pow Z.of_N Pos.pow] in SPR'.
    pose proof (proj1 ST) as LO0'.
    pose proof (munch_refl [(bv_unsigned xsp - 16, bv_unsigned xsp)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned xsp).
    finish.
    all: match goal with |- ?g => idtac "N0-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03\0@C24112444547.220D17444351834.189D17444351834.220D27787129986.189D27787129986.220D30202740417.220D30213615715.226D42633159082.220D42643779336.226D62012212072.226D64065028362.199D64065028362.226D66314653779.226K10771443815.225K10771443815.227K11420089551.220K28284592895.218K28284592895.219K28441636224.196K28441636224.223K36247032466.223K3664959506.223 K37146771504.198K37146771504.200K48349884702.192K48349884702.193K48349884702.218K48349884702.219K48868404123.224K48868404123.226K61717199003.223K8420855378.197 K8420855378.199 L10307112399.6  L10781994143.4  L10786545777.4  L11410546997.3  L1282143298.11  L1286294210.5   L14249421094.3  L15477852824.1  L16811220711.14 L16811253217.16 L18141400273.11 L19188710447.4  L22550422114.3  L22770371543.8  L22782984400.10 L22782984400.8  L23100341967.193L23643762344.6  L2424955998.3   L2428946895.12  L2428979913.10  L25299220370.2  L25858625233.2  L26502719108.5  L26589659220.5  L28231168598.1  L28274540293.4  L28452252428.2  L29146453537.8  L29150616870.8  L29525427416.7  L29527684735.11 L29527717241.13 L2975768925.2   L29971684470.4  L35663928186.7  L36252569448.16 L3671934440.3   L36721400998.11 L36721500064.13 L37156412616.3  L37158973457.12 L37159006999.13 L37160767526.3  L37161403062.7  L38213925978.12 L38214025052.10 L38235734261.1  L39463202031.1  L41128898453.2  L41590179991.3  L41670789057.6  L42633816569.1  L43629307734.4  L43878034250.5  L45586019928.7  L47401054516.1  L47797436189.12 L48296763010.2  L48338281339.2  L48857545612.4  L48862050147.4  L49929943149.15 L49930042219.16 L50001859045.8  L50007823253.8  L51284464315.193L53982396750.1  L55345850227.216L57050337471.5  L57054567352.6  L57860742933.1  L58177949655.193L59824495762.8  L59824839701.8  L59826908467.16 L59827007029.14 L60098763854.3  L60283674290.11 L60447858056.11 L60611602004.3  L61136745943.3  L6141606276.1   L61651670997.2  L61707527521.3  L62729654052.16 L62729686050.15 L65032630433.0  L65349212151.12 L65351099990.5  L65351280337.6  L66151427842.16 L66151427842.17 L66990418839.192L6880072876.14  L8405802565.3   L8406224084.7   L8408153715.12  L8408251765.13  L8409780906.3   L9832141279.10  O14042253711.224O14042253711.226O14272372170.195O22331808284.221O24112444547.220O27573497883.218O27573497883.219O30481499798.198O30481499798.200O35105909750.196O35105909750.223O41080831185.225O41080831185.227O43419437345.223O44282969958.223O48091478445.222O48319976166.223O54539614568.192O54539614568.193O54539614568.218O54539614568.219O54736301905.194O62994492140.197O62994492140.199P10771443815.225P10771443815.227P11420089551.220P14260335836.221P25287359492.195P28441636224.196P28441636224.223P37146771504.198P37146771504.200P48292894101.194P48349884702.192P48349884702.193P48349884702.218P48349884702.219P48868404123.224P48868404123.226P61147129901.222P8420855378.197 P8420855378.199 Q10044758524.198Q12370813529.199Q17207432298.198Q18347242623.230Q18468912438.203Q18468912438.231Q1946824128.198 Q21750490675.198Q21750569356.199Q30213615715.231Q33478850983.199Q36646300200.199Q36708691079.200Q36708691079.201Q36708691079.202Q36708691079.203Q36708691079.231Q37321652361.197Q37323683587.209Q37625261960.198Q3777752941.201 Q3777752941.202 Q3777752941.203 Q3777752941.231 Q39016945843.229Q39016945843.230Q40106689634.228Q40106689634.229Q40106689634.230Q42643779336.231Q47588311916.227Q47588311916.228Q47588311916.229Q47588311916.230Q49058237960.199Q49433500843.199Q53113263298.198Q53728288634.202Q53728288634.203Q53728288634.231Q5485126037.198 Q5485174314.199 Q60807234163.199Q61264001456.199Q61264037391.198Q6143569392.199 Q64065028362.200Q64065028362.201Q64065028362.202Q64065028362.203Q64065028362.231Q66314653779.231Q66375044744.199Q67329072568.198Q8222473558.199 Q9827600259.227 Q9827600259.228 Q9827600259.229 Q9827600259.230 00000101=02[03h05G06Z07d08W09A09m09n09o0:00:10:20:30:d0;U0;V0;W0<S0=O0=P0=Q0=R0=S0=T0=U0=V0=W0>X0>Y0>Z0>n0>o0?00?10?I0?Y0?Z0?^0?_0?`0@D0@O0@Y0@Z0@[0A:0A`0B20B:0B;0B<0B=0B>0BR0Bb0Bf0Bg0Bh0Bi0CH0CI0CJ0CK0CR0C]0D20D30D40D50D60D70D80D90D:0D;0D<0D=0DA0DE0DF0DO0Dc0Dh0E40E;0EU0EY0EZ0E[0E\0E]0E^0E_0E`0Ea0F@0Ff0Fj0Gc0H70HK0HO0I50I60I70I80I90IC0Ig0J>0JG0JH0JL0JM0JN0JO0JP0JQ0JR0J^0J_0K;0K<0Ki0Km0Kn0Ko0L00L10L20LV0LW0LX0LY0LZ0L[0L\0L]0L^0L_0L`0La0Lb0Lc0Ld0Le0Lf0Lg0Lh0Li0Lj0Lk0Ll0Lm0Ln0Lo0M00M10M20M30M40M50M60M70M80M90M:0M;0M<0M=0M>0M?0M@0MA0MV0NC0NW0NX0NY0NZ0No0OD0OY0P70P80PM0PN0PO0PP0PQ0PR0Q>0R40RH0RI0RJ0RK0RL0RM0RN0RO0RP0RQ0Rg0Rh0Ri0Rj0Rk0Rl0Sc0T80T90T:0T;0TO0Tc0Td0U90UN0Ub0Uc0Ud0Ue0Uf0Ug0Uh0V=0VR0WF0WG0WH0WI0WJFS1R3HIA1h2ra2sp1X3xs02dA2dB2hc2xs2pa2pb3ysA3zsB2A02B03TOP2X03SPR3HT13YAB3ZBBS1R3HIA1h2ra2sp1X3xs02dA2dB2hc3pXc2xs1n2pa2pb3ysA3zsB2A02B03TOP2X03SPR3HT13YAB3ZBB2P03xs64LEN6S1R2ra2sp1X3xs02dA2dB2lo4SLO22xs2pa2pb3ysA3zsB2A02B05NEEDR3LOS2X03SPR3YAB3ZBBS1R2ra2sp1X3xs02dA2dB2lo4SLO23pXc2xs1n2pa2pb3ysA3zsB2A02B05NEEDR3LOS2X03SPR3YAB3ZBB2P03xs64LEN6S2ra2sp1X3xs02dA2dB1N3pXc2xs1n2pa2pb3ysA3zsB2HN2A02B02X03SPR3YAB3ZBB2N12P03xs64LEN6S2ra2sp1X3xs02dA2dB1N3pXc2xs1n2pa2pb3ysA3zsB2HN2A02B02X03SPR3YAB3ZBB2N12P0S2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsB3xs64LEN6S2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsBS1R2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsBFFFFFFS1R2sp3xs02lo1N3pXc2xs1n3ysA3zsB2HN3LOS3ALO2N12PCS1R2sp3xs02lo1N3pXc2xs1n3ysA3zsB2HN3LOS3ALO2N12PCFFS1R2sp3xs02lo4SLO21N3pXc2xs1n3ysA3zsB2HN5NEEDR3LOS3ALO2N12PCS1R2sp3xs02lo4SLO21N3pXc2xs1n3ysA3zsB2HN5NEEDR3LOS3ALO2N12PCFFFFFFFFS2sp1X3xs02lo1N3pXc2xs1n3ysA3zsB2HN3x142NZ2N13XPc2x23x153x164POSTFFS1R2sp2lo4SLO25NEEDRFFFS1N2xs1n3ysA3zsB2HN4LEN1S1N2xs1n2HN4LEN1FS2spFFS2dA2dB2xs1n3ysA3zsB2VA2VB1c3xs63LV6S1N1n2HN2NZS1c3HC62KCFFS1R2sp2lo4SLO22pb3zsB3ZBS5NEEDRS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsBS1X1N3pXc1n2HN3XPcS1N1n2HNFFFFS1R2sp2lo4SLO25NEEDRS2dA2dB2xs2VB2VAS2spFFFS1R2sp2lo4SLO22pa3ysA3YAS5NEEDRFFFS1N3pXcS1N1n2HN2NZS1R3HIA1h2sp2lo3TOP1HFFFFFFFFFFFS2loS2spFS2dA2dB1nS1R2sp2lo4SLO25NEEDRS3pXcS1N3pXc1n2HNS2sp2loS1R2sp1X2lo4SLO25NEEDR3DSXS2spFFFFFFFFS1R2sp2lo4SLO21N3pXc5NEEDR4XLScS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsBS2spS2ra2sp1X3xs02dA2dB3pXc2xs1n2pa2pb3ysA3zsB1c3xs63HC64LEN6S1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS2spS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsBFFFFS1R2lo3LOSS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR1a2NOS1N2xs1n3ysA3zsB2HN3NR1S2dA2dB1nFS2spFFFFSFS2sp3SPA3SPRFS3pXc2r04XPAL1q1r1H2H02q02H4FS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsB2B03B16S2spFFFFFS1R2sp2lo4SLO21N3pXc1n2HN5NEEDR4XLScFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS3xs02dA2xs1n3ysA3zsBS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsB2X03XALS1X3xs02xs1n3ysA3zsBFFFS3xs02dB2xs1n3ysA3zsBS3xs02dB2xs1n3ysA3zsBS3xs02dB2xs1n3ysA3zsBS3xs01N3pXc2xs1n3ysA3zsB2HN2N1FS3xs02dB2xs1n3ysA3zsBFFFFFS1R2sp3xs02lo4SLO22xs5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22xs1n3ysA3zsB5NEEDR3LOS4SP643ALO3ACPS1X3xs02xs1n3ysA3zsBFFFFFFFFFS3xs03pXc2xs1n3ysA3zsBFFFFFS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsB2A02B03BAL2X03SPRS3xs02dB2xs1n3ysA3zsBFFFS1X3xs02xs1n3ysA3zsBS1X3xs02xs1n3ysA3zsBFS3xs02dA2xs1n3ysA3zsBS3xs02dA2xs1n3ysA3zsBS1X3xs02xs1n3ysA3zsBFFFFFFS3xs02dA2xs1n3ysA3zsBS3xs02dA2xs1n3ysA3zsBS2ra2sp1X3xs02dA2dB2xs1n2pa2pb3ysA3zsB2A03AAL2X03SPRFFFF". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma sa_CSUB : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pn,$8.Ppa,$8.Psa,$8.Pna,$8.Ppda,(3.&40.)Ppb,$8.Psb,$8.Pnb,$8.Ppdb,(3.&40.)PysA,(1.(3.&40.))PzsB,(1.(3.&40.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs5,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R23.R22.R21.R20.R1?.R1>.)P,(14.(15.R1?.)VnX,)P,(2?.(14.=R1?.)(14.R1?.(15.R20.)))P,P,(14.+1.R20.)(10.$11.(12.R22.)$1<.)P,(66.$48.R23.(1;.VdA,)(67.R20.(29.&40.R1?.)R1>.R1=.))P,(68.$48.(2=.VR,)(2>.$48.VR,VHIA,R26.)R24.(1;.VdA,)+10.)P,(30.=(1;.VdA,))P,(14.(23.(1;.VdA,)+10.)(36.+2.+40.))P,(10.$8.(28.(1;.VdA,)+8.)=)P,(69.$48.R28.R25.(6:.R1=.))P,(14.R27.(6;.(6<.(3.&40.)R1>.)))P,(22.(2?.(10.$8.R27.(1=.R29.))(10.(1.(3.&40.))R1?.(56.R29.)))(22.(14.(23.R27.(1>.+4.(6;.(6<.(3.&40.)R1?.))))(1=.R29.))(14.(23.(1=.R29.)(1>.+4.(15.R29.)))R27.)))P,(10.$8.(28.R28.+4.)=)P,P,(14.+1.R2:.)(30.=R2:.)P,(22.(14.(23.R2:.(1>.+4.(6;.(6<.(3.&40.)R22.))))Vlo,)(14.(=.&40.Vsp,)R2:.))P,P,(14.+1.R2<.)(68.$48.(2=.VR,)(2>.$48.VR,VHIA,R31.)R2?.R2<.(1>.+4.R2=.))P,(66.$48.R2?.(1;.VdB,)(67.R28.(29.&40.R27.)R26.R25.))P,(68.$48.(2=.VR,)(2>.$48.VR,VHIA,R32.)R30.(1;.VdB,)+10.)P,(30.=(1;.VdB,))P,(14.(23.(1;.VdB,)+10.)(36.+2.+40.))P,(10.$8.(28.(1;.VdB,)+8.)=)P,(69.$48.R34.R2=.(6:.R28.))P,(14.R33.(6;.(6<.(3.&40.)R29.)))P,(22.(2?.(10.$8.R2?.(1=.R35.))(10.(1.(3.&40.))R2:.(56.R35.)))(22.(14.(23.R2?.(1>.+4.(6;.(6<.(3.&40.)R2:.))))(1=.R35.))(14.(23.(1=.R35.)(1>.+4.(15.R35.)))R2?.)))P,(10.$8.(28.R30.+4.)=)P,P,(14.+1.R36.)(30.=R32.)P,(22.(14.(23.R32.(1>.+4.(6;.(6<.(3.&40.)R2=.))))Vlo,)(14.(=.&40.Vsp,)R32.))P,P,(14.+1.R38.)(68.$48.(2=.VR,)(2>.$48.VR,VHIA,R3=.)R3;.R34.(1>.+4.R39.))P,(10.$8.(23.(6=.R30.R39.)(1>.(36.+2.(1>.+20.R39.))(55.(6>.(3.&40.)(6?.R39.)(56.R3:.)))))(4>.VdA,))P,(10.$8.(6=.R30.R3:.)(4>.VdB,))P,(14.R41.(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(14.R41.(3>.Vd,))(52.$48.(53.$48.VR,VHIA,R41.Vmo,)$54.(44.(45.R32.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R31.R30.R2?.(29.&40.VX,)(29.&40.(1;.VdB,))R2>.R2=.R2<.R2;.R2:.R29.R28.R27.(29.&40.(1;.VdA,))(29.&40.R3=.)(29.&40.(23.VX,+:.))R26.(29.&40.(1>.+4.R3=.))(29.&40.(58.(1;.VdA,)+3.))(29.&40.(57.(2=.VR,)))(29.&40.(23.(58.(23.VX,+:.)+3.)(57.(2=.VR,))))(29.&40.(58.VX,+3.))R25.R24.R23.R22.R21.)VF,(29.&40.+9>214.)Vfc,(46.(3.&40.))R3?.(47.$48.)))")
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
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
    pose proof (u32ro_bound _ _ _ _ YA) as YAB. pose proof (u32ro_bound _ _ _ _ ZB) as ZBB.
    pose proof (munch_refl [(pXc, pXc + 4 * n); (bv_unsigned sp + -112 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -112)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec n 0) as [EN0|NZ].
    - (* [comment removed for export] *)
      subst n. clear MU WM. pose proof (munch_refl [(bv_unsigned sp + -112 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -112)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
      zstep.
      acallxA_sp (bv_unsigned sp + -112)
        (eapply core_sub_n0A with (lo' := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia; try eassumption; try reflexivity;
         first [ unfold MPI_CORE_SUB_STACK_A; clear - SLO2 NEEDR LOS; lia
               | clear - SPA SPR LOSP; lia
               | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
               | match goal with |- ?g => idtac "N0CALL-PRE-LEFT:" g end ]).
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-N0CALL-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo (bv_unsigned sp + -112) |- _ => rename H into ST6 end.
      match goal with H : rw_cells asegs m6 (bv_unsigned sp + -112) _ |- _ => rename H into SL6 end.
      pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
      apply (hm_munch asegs R HIA hc LBc LF [(bv_unsigned sp + -112 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -112)] mc m6) in HH6;
        [| exact MU| exact WM| unfold MPI_CORE_SUB_STACK_A; solve_w_writable].
      assert (ST6' : stk asegs m6 lo (bv_unsigned sp - 104)).
      { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp - 104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SL6. }
      pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m6 J0 MU WM MI6 ST6' HH6
                    ltac:(unfold MPI_CORE_SUB_STACK_A; clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      (* [comment removed for export] *)
      zstep.
      eapply sa_SIGN; [exact J6| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| cbn [md_limbs]| exact BV| exact BF].
      rewrite lval_0 in VA, VB. change (skipn (Z.to_nat 0) xs) with xs in VA. rewrite Z.mul_0_r, Z.pow_0_r in VA. clear - VA VB. lia.
    - (* [comment removed for export] *)
      pose proof (EOn ltac:(clear - NZ HN; lia)) as EO. subst own.
      ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
      pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
      assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
        by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
      pose proof (A_mpi_core_sub_spec AL IMG) as SPC. unfold mpi_core_sub_stmtA, A_MPI_CORE_SUB in SPC.
      zstep.
      acallxA_sp (bv_unsigned sp + -112)
        (eapply SPC with (X := pXc) (A := pa) (B := pb) (n := n) (lo := lo) (xs := xs) (ys := ysA) (zs := zsB);
         rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
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
               | match goal with |- ?g => idtac "CSUBCALL-PRE-LEFT:" g end ]).
      clear SPC.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CSUBCALL-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo (bv_unsigned sp + -112) |- _ => rename H into ST6 end.
      match goal with H : rw_cells asegs m6 (bv_unsigned sp + -112) _ |- _ => rename H into SL6 end.
      match goal with H : u32arr asegs m6 pXc ?l, H2 : length ?l = length xs |- _ => rename H into XARR6; rename H2 into LEN6; rename l into xs6 end.
      match goal with H : lval xs6 n - ?cc * _ = _, H2 : 0 <= ?cc <= 1, H3 : skipn _ xs6 = _ |- _ => rename H into LV6; rename H2 into HC6; rename H3 into SK6; rename cc into c end.
      pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
      apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * n); (bv_unsigned sp + -112 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -112)] mc m6) in HH6;
        [| exact MU| exact WM| unfold MPI_CORE_SUB_STACK_A; solve_w_writable].
      assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
      { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SL6. }
      assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * n); (bv_unsigned sp + -112 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -112)] a ->
                    (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
      { intros a NO. cbn [outside] in NO. unfold MPI_CORE_SUB_STACK_A in NO.
        assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN SLO2 NEEDR; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc, pXc + 4 * n); (bv_unsigned sp + -112 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -112)] (bv_unsigned sp - 104) 104).
      { cbn; unfold MPI_CORE_SUB_STACK_A. split; [clear - XLSc SLO2 NEEDR HN; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc, pXc + 4 * n); (bv_unsigned sp + -112 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -112)] X 16).
      { cbn; unfold MPI_CORE_SUB_STACK_A. split; [clear - XPc HN; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6 DJF DJX XARR6 LEN6) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      assert (VNEW : limbs_val xs6 = mpd_abs dA - mpd_abs dB + c * 2 ^ (32 * n)).
      { rewrite (limbs_val_split xs6 n ltac:(clear - HN; lia) ltac:(rewrite LEN6; clear - HN LEN1; lia)). rewrite SK6.
        clear - LV6 VA VB. lia. }
      subst x2.
      (* [comment removed for export] *)
      zstep. if_cases KC; zify_cond KC; rewrite ?Z.mod_small in KC by (clear - HC6; lia).
      + eapply sa_SIGN; [exact J6| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| cbn [md_limbs]; rewrite VNEW, KC; clear; lia| exact BV| exact BF].
      + assert (C1 : c = 1) by (clear - KC HC6; lia). rewrite C1.
        eapply sa_SUBINT; [exact J6| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| reflexivity| cbn [md_n]; clear - HN NZ; lia| cbn [md_limbs]; rewrite VNEW, C1; clear; lia| exact BV| exact BF].
    all: match goal with |- ?g => idtac "CSUB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L26547048773.56L53778998493.56L64577079243.5600000>00M00\S2ra2xs2na3HnaS2ra2xs2na1n2HnS2ra2xs2na1n2Hn". (* [comment removed for export] *)
  #[using="ra"] Lemma zext_low : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pxs,(1.(3.&40.))Pna,$8.Pn,$8.Pk,$70.P,(2?.(14.=R2.)(14.R2.R3.))P,(14.R4.(6;.(6<.(3.&40.)R5.)))(10.$8.(6=.(19.(3.&40.)(71.(3.&40.)(6?.R5.)R6.)(72.(3.&40.)(29.&40.=)R3.))R4.)(6=.R6.R4.))")
(* [comment removed for export] *).
  Proof.
    intros xs na n k Hn Hna. apply lval_ext. rewrite firstn_app, firstn_firstn, firstn_length_le by lia.
    replace (Z.to_nat n - Z.to_nat na)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L26547048773.56L43727839089.56L64577079243.5600000>00M00\S2ra2xs2na3HnaS2ra2xs2na1n2HnS2ra2xs2na1n2Hn". (* [comment removed for export] *)
  #[using="ra"] Lemma zext_high : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pxs,(1.(3.&40.))Pna,$8.Pn,$8.Pk,$70.P,(2?.(14.=R2.)(14.R2.R3.))P,(14.R4.(6;.(6<.(3.&40.)R5.)))(10.$8.(55.(6>.(3.&40.)(6?.R4.)(19.(3.&40.)(71.(3.&40.)(6?.R5.)R6.)(72.(3.&40.)(29.&40.=)R3.))))(73.R6.R4.R5.))")
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

  
  
  
  (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L62463072682.3000009S2xs1n2Hn". (* [comment removed for export] *)
    #[using="Type"] Lemma lval_app_l : forall (xs zs : list word) n, 0 <= n <= Z.of_nat (length xs) -> lval (xs ++ zs) n = lval xs n.
  Proof. intros xs zs n Hn. unfold lval. rewrite firstn_app. replace (Z.to_nat n - length xs)%nat with 0%nat by (clear - Hn; lia). cbn [firstn]. rewrite app_nil_r. reflexivity. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition KJ_stmt (n NA : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs7,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R18.R17.R16.R15.R14.R13.)P,(14.(15.R14.)VnX,)P,(74.VdA,R18.R17.R16.R15.)P,(74.VdB,R19.R18.R17.R16.)P,(2?.(14.=O2.)(14.O2.O1.))P,(14.O1.(15.R18.))P,P,(14.+1.O1.)(10.$11.(12.R1:.)$1<.)P,P,(10.$8.(1;.VdA,)VX,)(2?.(10.$8.(15.R1;.)O1.)(10.$8.(55.(56.R1;.))(4>.VdA,)))P,P,(?.(10.$8.(1;.VdA,)VX,))(10.$8.(15.VdA,)O1.)P,P,(10.$8.(1;.VdB,)VX,)(10.$8.(6=.(56.R1=.)O2.)(4>.VdB,))P,P,(?.(10.$8.(1;.VdB,)VX,))(2?.(10.$8.(6=.(56.VdB,)O2.)(4>.VdB,))(14.O2.(15.VdB,)))P,(14.R23.(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(14.R23.(3>.Vd,))(52.$48.(53.$48.VR,VHIA,R23.Vmo,)$54.(44.(45.R1?.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1>.R1=.R1<.(29.&40.VX,)(29.&40.(1;.VdB,))R1;.R1:.R19.R18.R17.R16.R15.R14.(29.&40.(1;.VdA,))(29.&40.O2.)(29.&40.(23.VX,+:.))(29.&40.(23.(1;.VdA,)+:.))(29.&40.O1.)R13.(29.&40.(57.(2=.VR,)))(29.&40.(23.(58.(23.VX,+:.)+3.)(57.(2=.VR,))))(29.&40.(58.VX,+3.))R12.R11.R10.R?.R>.)VF,(29.&40.+9>178.)Vfc,(46.(3.&40.))R21.(47.$48.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L12528478301.2 L30274085261.3 L32027975233.0 L33655257162.3 L38569812941.1 L39280637297.0 L46832644263.3 L54742304139.2 L57140746179.2 L57140746204.3 L59031206751.1 L59308579152.3 L59310766035.4 L60016188669.2 L60456143867.3 L62357985085.2 L66151427842.1600000800B00C00N00S00T00^00f00m01401801F01U01]01i02202NS3dXc2P0S2dE1n3HnESS3dXc1n3HnXS3dXcSS1X2dE3SXBS2lo3LO0S1n3HnES1n3HnXS2dES1n3HnX2H13HnES2dE1l4LENE3En0S2dE3EP0S2dE3dXc3SL2S3dXc3PX0S3dXc2r04XPAL1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="JC"] Lemma rideS_view : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pn,$8.P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R7.R6.R5.R4.R3.R2.)P,(74.R9.R6.R5.R4.R3.)P,(14.=R3.)P,P,(10.$8.(1;.R;.)VX,)(14.R5.(15.R6.))P,P,(?.(10.$8.(1;.R<.)VX,))(14.R6.(15.R=.))(5>.$8.Lpe,$8.(5>.$8.Lse,$8.(5>.$8.Lne,$8.(5>.(3.&40.)Lpde,(3.&40.)(5>.(1.(3.&40.))Lys,(1.(3.&40.))(2?.(66.$48.R=.(1;.R12.)(67.R5.(29.&40.R4.)R3.R2.))(2?.(68.$48.(2=.VR,)(2>.$48.VR,VHIA,R?.)R=.(1;.R12.)+10.)(2?.(30.=(1;.R12.))(2?.(14.(23.(1;.R12.)+10.)(36.+2.+40.))(2?.(10.$8.(28.(1;.R12.)+8.)=)(2?.(69.$48.R=.R5.(6:.R1.))(2?.(14.R;.(6;.(6<.(3.&40.)R1.)))(2?.(22.(2?.(10.$8.R5.(1=.R<.))(10.(1.(3.&40.))R1.(56.R<.)))(22.(14.(23.R5.(1>.+4.(6;.(6<.(3.&40.)R1.))))(1=.R<.))(14.(23.(1=.R<.)(1>.+4.(15.R<.)))R5.)))(2?.(10.$8.(28.R5.+4.)=)(2?.P,(14.+1.R;.)(30.=R6.)(2?.(22.(14.(23.R5.(1>.+4.(6;.(6<.(3.&40.)R1.))))Vlo,)(14.(=.&40.Vsp,)R5.))(2?.P,(14.+1.R;.)(68.$48.(2=.VR,)(2>.$48.VR,VHIA,R10.)R>.R6.(1>.+4.R<.))(2?.P,(10.$8.(1;.R12.)VX,)(10.(1.(3.&40.))R2.(56.R=.))(2?.P,(?.(10.$8.(1;.R12.)VX,))(10.(1.(3.&40.))R2.(56.R13.))(2?.P,(10.$8.(1;.R12.)VX,)(10.$8.R4.(15.R=.))P,(?.(10.$8.(1;.R12.)VX,))(10.$8.R4.(15.R13.))))))))))))))))))))))")
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
  #[using="IMG JC SLO2"] Lemma sa_CSUBr : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pn,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs5,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R19.R18.R17.R16.R15.R14.)P,(14.(15.R15.)VnX,)P,(74.VdA,R19.R18.R17.R16.)P,(74.VdB,R1:.R19.R18.R17.)P,(2?.(14.=R17.)(14.R17.(15.R18.)))P,P,(14.+1.R18.)(10.$11.(12.R1:.)$1<.)P,P,(10.$8.(1;.VdA,)VX,)(10.$8.(55.(56.R1;.))(4>.VdA,))P,P,(?.(10.$8.(1;.VdA,)VX,))(2?.(14.R1;.(15.VdA,))(10.$8.(23.(6=.(56.VdA,)R1;.)(1>.(36.+2.(1>.+20.R1;.))(55.(6>.(3.&40.)(6?.R1;.)(56.R1<.)))))(4>.VdA,)))P,P,(10.$8.(1;.VdB,)VX,)(10.$8.(6=.(56.R1=.)R1<.)(4>.VdB,))P,P,(?.(10.$8.(1;.VdB,)VX,))(2?.(14.R1=.(15.VdB,))(10.$8.(6=.(56.VdB,)R1=.)(4>.VdB,)))P,(14.R23.(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(14.R23.(3>.Vd,))(52.$48.(53.$48.VR,VHIA,R23.Vmo,)$54.(44.(45.R1>.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1=.R1<.R1;.(29.&40.VX,)(29.&40.(1;.VdB,))R1:.R19.R18.R17.R16.R15.R14.R13.(29.&40.(1;.VdA,))(29.&40.R1?.)(29.&40.(23.VX,+:.))R12.(29.&40.(1>.+4.R1?.))(29.&40.(58.(1;.VdA,)+3.))(29.&40.(57.(2=.VR,)))(29.&40.(23.(58.(23.VX,+:.)+3.)(57.(2=.VR,))))(29.&40.(58.VX,+3.))R11.R10.R?.R>.R=.)VF,(29.&40.+9>214.)Vfc,(46.(3.&40.))R21.(47.$48.)))")
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
    all: match goal with |- ?g => idtac "CSUBR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L18311971322.4L19148630698.4L23648481964.8L33358731881.5L35655538626.8L50758139803.8L53591371865.3L60098763854.300000=00K00`00l01E01Z01d01nS2sp2lo2dE2ESS2sp2lo2dE3EL5S2dE3dXc1a1b2Ha2Hb2S2S3dXc1a1b2HbS1R3HIA1h2sp2lo3TOP5HTOP0S2dE3dXc1a1b2Ha2Hb2S1S3dXc1a2HaS1R2lo3LOS". (* [comment removed for export] *)
  #[using="JC"] Lemma rideS_xl_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pa,$8.Pb,$8.Pxs',(1.(3.&40.))Pm3,P,(3.&40.)(5.(3.&8.))P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R:.R9.R8.R7.R6.R5.)P,(74.R<.R9.R8.R7.R6.)P,(10.$11.(12.R7.)$1<.)P,(14.(1=.R8.)R7.)P,(14.R8.R7.)P,(14.R8.(23.(1=.R:.)(1>.+4.(15.R:.))))P,(60.(61.(62.$8.$8.)(63.$8.$8.R:.R9.)(61.(62.$8.$8.)(63.$8.$8.Vlo,(23.(=.&40.Vsp,)-70.))(4<.(62.$8.$8.))))R<.R7.)P,(64.$48.R=.R8.)(74.R13.R10.R?.R9.(49.(1;.R=.)(4?.R=.)(15.R=.)(1=.R=.)R:.(75.R=.)(12.R=.)))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "02?0@C11264273767.212C11264273767.213C17025492443.210C17025492443.211C237391055.214  D32879014451.214D39122030177.214D56475227919.214D60109446735.214K1307012896.210 K1307012896.211 K19167344963.210K19167344963.211K25382859142.214K36226586886.214K46334408099.212K46334408099.213K65977774223.214K7472647416.214 L10307112399.6  L11950189345.0  L12530932062.2  L12904683780.8  L1294499141.2   L146940511.12   L14769340704.4  L14858295739.5  L15477852824.1  L16192802388.7  L18820853705.2  L19171242580.5  L1981962437.8   L21812184103.188L21812701729.5  L21820691587.174L21824805693.6  L21825511751.19 L23002796746.5  L23004893895.3  L23100341967.189L25238078280.8  L25369787025.17 L26063715927.5  L26502719108.5  L27791514431.4  L284732655.188  L2975768925.2   L29763661393.2  L29767770607.174L29776081227.188L32371227958.4  L34125036709.14 L34444340830.3  L34456730698.19 L35663928186.7  L35978283095.4  L36230550033.4  L37231249068.3  L38129129185.3  L38235734261.1  L39109575675.4  L39172636981.0  L39280637297.0  L40145318023.3  L40597388054.15 L407990430.7    L41126667518.5  L42633816569.1  L43878034250.5  L46160487540.172L46329855668.4  L47401054516.1  L49245743301.2  L49655171755.3  L53234661796.3  L53236858660.6  L5414710336.4   L56598719221.7  L58609956177.2  L58641002120.174L59308660947.6  L59308661072.4  L59944282246.2  L60098763854.3  L60283674290.10 L6141606276.1   L61714773053.6  L62959842117.3  L64045840071.2  L64049675681.19 L65973484440.4  L67970915500.7  L6880799821.3   L7476911773.3   L8016725142.2   L8265267294.0   O11264273767.212O11264273767.213O17025492443.210O17025492443.211O237391055.214  O36019832244.214O36632239767.210O36632239767.211O48199580980.214O50423766113.214O57399310481.214P1307012896.210 P1307012896.211 P46334408099.212P46334408099.213Q12370813529.194Q17201186252.193Q18133098905.175Q18135196125.173Q18136087844.176Q26207721832.174Q26207721832.175Q26207967338.171Q31653717441.175Q32879014451.214Q34225026208.173Q34419558587.175Q37323683593.194Q37618859566.193Q38248387216.214Q39122030177.214Q39212284437.174Q39212284437.176Q43879899724.214Q43925228937.174Q5470531635.193 Q5485174314.194 Q58692335428.176Q59703481013.194Q60511567613.174Q60511567613.176Q60697995187.174Q6143569392.194 Q64768105610.176Q8880503606.171 Q9538243134.173 Q9538787269.171 00000100200300400500S01?02>02c02d02e03K04104b05S05T05U06G06`07407507>07?07@07g08308C08G08^08f08g09<0:60:70:l0;?0;]0;l0<40<P0<e0<f0=60=J0=U0>K0>R0>Y0?20?T0?a0@C0@D0@Z0@o0A;0A<0AD0AE0AI0AV0AW0AX0Aa0Ah0B60B70B<0BC0B]0B^0Bb0Bh0C00C:0CD0CE0CW0C^0D80DH0DS0DZ0Dd0E>0EB0EU0E^0E_0F50F60FC0FL0FM0FT0FU0FV0FW0FX0FY0Fn0Fo0G00G10G20G30G40G50G60G70G80G[0Gj0H50H@0HK0HU0H_0Hi0I30IF0IQ0I\0JM0J\0Jl0K@0KJ0KU0Kh0L20LA0LP0L^0L_0Lg0Lo0M<0MK0MV0M`0Mh0N0FFFFFS2ra2sp1X3xs02dA1N3pXc2xs1n2NAS2ra2sp1X3xs02dA3pXc2xs1n2NA2HN2X03SPR2A02P0S1R3HIA1h2ra2sp1X3xs02dA2lo2hc3pXc2xs1n2NA3TOP2X03SPR2A03HT12P0S1R2ra2sp1X3xs02dA2lo3pXc2xs1n2NA3LOSFFS1R2sp3xs02lo1N3pXc2xs1n2NA3LOS3ALO2PCS1R2sp3xs02lo1N3pXc2xs1n2NA3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n2NA5NEEDR3LOS3ALO2PCS1R2sp3xs02lo4SLO21N3pXc2xs1n2NA5NEEDR3LOS3ALO2PCFFS1X3xs02dA1N3pXc2xs1n2NA2HN3VA14LEN11K3XPc3ANX3LHIS2sp1X3xs02lo2xs1n2NA3DSXS1R2sp2lo4SLO25NEEDRSS3dXc3NR1FFS1R2sp2lo4SLO21N3pXc1n2NA2HN5NEEDR4XLScS1N2NA3HNA1KS1N2xs1n2HN4LEN1S2spS1N2xs1n2NA2HN3HNA4LEN1S3pXc2NAFS1N2xs1n2NA2HN4LEN11KS2ra2sp1X2nX3xs02dA3NGN3pXc2xs1n2NA2HN2X02NR3SPR2A02P03ENaFS2ra2sp1X2nX3xs02dA1N2xs1n2NA3NGX2HN3HNA2X02NR3SPR2A0S1N1n2NA2HN3HNA3NR1S2sp2lo1N3pXc1n2NA2HN3SPR4XLScS1N1n2NA2HN3HNAS1N1n2HNS2ra2sp1X3xs02dA3pXc2xs1n2NAS1X1N3pXc1n2NA2HN3XPcFS1R3HIA1h2sp3TOPS1R2sp2lo4SLO25NEEDRS1N1n2HN2H1S2ra2sp1X3xs02dA1N3pXc2xs1n2NA2HN3HNA2X03SPR2A02P03P47S1N3pXcS1N3NR1S2ra2sp1X3xs02dA1N2xs3NR1S2ra2sp1X3xs02dA1N3pXc2xs1n2NA3NR1S2sp1X2lo3DSXS2sp2lo1N3pXc1n2NA2HN3HNA3NR14XLScFS1R2sp2lo4SLO23NRA3SPRS1R3HIA1h2sp2lo3TOP1HS1N3pXc2NA1KFS1N1n2HNFS2loS3pXc1n2NA2HNSSS1n2NA2HNS2sp2loS1N3pXc2NA3P47FS3pXcS2sp2loS2ra2sp1X3xs02dA2xs2X03X16FS2spS1N2NAS1N2NA1KS1N3pXc2NAS1N3pXc2NAFS1N2xs2NA3HNA4LEN1S1N3NR1S2ra2sp1X3xs02dA2xs2A03A16S1N1n2NA2HN1K2E0S1N2NA1K2E1S2sp2loS1R2lo3LOSS2sp2lo1N3pXc1n2NA2HN1a2NOS2spS1N1n2NA2HN3HNA3NR1S1n2NA2HNFS2sp1N1n2NA2HN3SPR3NR1FS1N2xs2NA3LHIS1n2NA2HNFS2sp2loSFFFFS1N3pXc2xs1n2NA1K3LHIFFFFFFFFFFS2ra2sp1X3xs02dA3pXc2xs1n2NA2X03XALS1X3xs02xs1n2NAS3xs02dA2xsS3xs02dA2xsS3xs02dA2xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS3xs01N3pXc2xs1n2NAS3xs02dA2xsS3xs02dA2xsS1R2sp3xs02lo4SLO22xs1n2NA5NEEDR3LOS4SP643ALO3ACPS1X3xs02xs1n2NAS3xs02lo2xs1n2NAS3xs03pXc2xs1n2NA2HNS1X3xs02xsS3xs02dA2xsS2sp3xs02lo2xs1n2NAS1X3xs02xsS1X3xs02xs1n2NAS1X3xs02xs1n2NAS3xs02dA2xs2A0FS3xs02xsS3xs02xsS1X3xs02xs2X0S1X3xs02xs1n2NAS3xs02dA2xsS1X3xs02xsS3xs02xsS3xs02xs". (* [comment removed for export] *)
  #[using="IMG AMS JC SLO2 NGN"] Lemma sa_MEMSET : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pn,$8.PNA,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R18.R17.R16.R15.R14.R13.)P,(14.(15.R14.)VnX,)P,(74.VdA,R18.R17.R16.R15.)P,(74.VdB,R19.R18.R17.R16.)P,(2?.(14.=R16.)(14.R16.R15.))P,(14.R16.(15.R18.))P,P,(14.+1.R17.)(10.$11.(12.R1:.)$1<.)P,P,(10.$8.(1;.VdA,)VX,)(2?.(10.$8.(15.R1;.)R19.)(10.$8.(55.(56.R1;.))(4>.VdA,)))P,P,(?.(10.$8.(1;.VdA,)VX,))(2?.(10.$8.(15.VdA,)R1:.)(10.$8.(23.(6=.(56.VdA,)R1;.)(1>.(36.+2.(1>.+20.R1;.))(73.(56.R1<.)R1;.R1:.)))(4>.VdA,)))P,P,(10.$8.(1;.VdB,)VX,)(10.$8.(6=.(56.R1=.)R1<.)(4>.VdB,))P,P,(?.(10.$8.(1;.VdB,)VX,))(2?.(14.R1=.(15.VdB,))(10.$8.(6=.(56.VdB,)R1=.)(4>.VdB,)))P,(14.R23.(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(14.R23.(3>.Vd,))(52.$48.(53.$48.VR,VHIA,R23.Vmo,)$54.(44.(45.R1=.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1<.R1;.R1:.(29.&40.VX,)(29.&40.(1;.VdB,))R19.R18.R17.R16.R15.R14.R13.R12.(29.&40.(1;.VdA,))(29.&40.R1?.)(29.&40.(23.VX,+:.))(29.&40.(23.(1;.VdA,)+:.))(29.&40.(1>.+4.R1?.))(29.&40.(58.(1;.VdA,)+3.))(29.&40.(57.(2=.VR,)))(29.&40.(23.(58.(23.VX,+:.)+3.)(57.(2=.VR,))))(29.&40.(58.VX,+3.))(29.&40.(23.(58.(23.(1;.VdA,)+:.)+3.)(57.(2=.VR,))))R11.R10.R?.R>.)VF,(29.&40.+9>1=0.)Vfc,(46.(3.&40.))R21.(47.$48.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX RA RB HN HNA EOn VA1 VA2 VB1 VB2 BV BF.
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
      eapply sa_CSUBr; [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| cbn [md_n]; clear - HN; lia| cbn [md_own]; intros H1; apply EOn; clear - H1 HN; lia
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
      destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
      replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
      (* [comment removed for export] *)
      pose proof XARR as PU. rewrite <- (firstn_skipn (Z.to_nat NA) xs) in PU. apply u32arr_app in PU. destruct PU as [PUlo PUhi].
      rewrite firstn_length_le in PUhi by (clear - HN HNA LEN1; lia). replace (4 * Z.of_nat (Z.to_nat NA)) with (4 * NA) in PUhi by (clear - HN; lia).
      assert (LHI : Z.of_nat (length (skipn (Z.to_nat NA) xs)) = N - NA) by (rewrite length_skipn; clear - HN HNA LEN1; lia).
      pose proof (conj PUlo I) as PUlo'. clear CEA OEA.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      zstep. zstep.
      clear MU WM. pose proof (munch_refl [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -112)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
      pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_SA) as SPM. unfold A_ASAN_MEMSET_SA in SPM.
      acallxA_sp (bv_unsigned sp + -112)
        (eapply SPM with (h := hc) (LB := LBc) (LF := LF) (DST := pXc + 4 * NA) (v := 0) (n := 4 * (N - NA)) (lo := lo) (ds := u32s (skipn (Z.to_nat NA) xs));
         rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
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
               | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
      clear SPM.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo (bv_unsigned sp + -112) |- _ => rename H into ST6 end.
      match goal with H : u8arr asegs m6 (pXc + 4 * NA) _ |- _ => rename H into HPZ end.
      match goal with H : HM asegs R HIA hc LBc LF m6 |- _ => rename H into HH6 end.
      match goal with H : rw_cells asegs m6 (bv_unsigned sp + -112) _ |- _ => rename H into SL6 end.
      assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
      { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
        replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
        apply stk_of_rw_cells. exact SL6. }
      destruct PUlo' as [PUlo _].
      pose proof (u32arr_transport asegs _ mc m6 _ _ PUlo MU WM) as PUlo6. rewrite firstn_length_le in PUlo6 by (clear - HN HNA LEN1; lia).
      specialize (PUlo6 ltac:(cbn [disjoint_from]; clear - HN HNA XLSc SLO2 NEEDR P0 NR1; lia)).
      replace (Z.to_nat (4 * (N - NA))) with (4 * Z.to_nat (N - NA))%nat in HPZ by (clear - K; lia).
      apply (rw_cells_of_u8arr asegs) in HPZ.
      assert (XARR6 : u32arr asegs m6 pXc (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA)))).
      { apply u32arr_app. split; [exact PUlo6|]. rewrite firstn_length_le by (clear - HN HNA LEN1; lia). replace (4 * Z.of_nat (Z.to_nat NA)) with (4 * NA) by (clear - HN; lia).
        eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]. }
      assert (HW6 : forall a, ~ outside [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -112)] a ->
                    (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
      { intros a NO. cbn [outside] in NO.
        assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN HNA; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -112)] (bv_unsigned sp - 104) 104).
      { cbn. split; [clear - XLSc SLO2 NEEDR HN HNA; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc + 4 * NA, pXc + 4 * NA + 4 * (N - NA)); (lo, bv_unsigned sp + -112)] X 16).
      { cbn. split; [clear - XPc HN HNA; lia| split; [clear - DSX; lia| exact I]]. }
      assert (LEN6' : length (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA))) = length xs).
      { rewrite length_app, repeat_length, firstn_length_le by (clear - HN HNA LEN1; lia). clear - HN HNA LEN1 K; lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6 DJF DJX XARR6 LEN6') as J6.
      pose proof (rideS_xl_munch dA _ _ _ _ _ _ (pXc + 4 * NA) (pXc + 4 * NA + 4 * (N - NA)) (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA))) m6 J0 RA eq_refl
                    ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear; lia) MU WM) as RA6.
      pose proof (rideS_xl_munch dB _ _ _ _ _ _ (pXc + 4 * NA) (pXc + 4 * NA + 4 * (N - NA)) (firstn (Z.to_nat NA) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (N - NA))) m6 J0 RB eq_refl
                    ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear; lia) MU WM) as RB6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6, RA6, RB6.
      eapply sa_CSUBr; [exact J6| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA6| exact RB6| cbn [md_n]; clear - HN HNA; lia| intros _; reflexivity
                       | intros E; exfalso; exact (ANX E)| | | exact VB2| exact BV| exact BF].
      + intros _. split; [rewrite ENa; clear - HN; lia|]. cbn [md_limbs]. rewrite (zext_high xs NA n _ HN ltac:(rewrite LEN1; exact HNA)). exact VA.
      + intros E. cbn [md_limbs]. rewrite (zext_low xs NA n _ HN ltac:(rewrite LEN1; exact HNA)). exact (VB1 E).
    all: match goal with |- ?g => idtac "MEMSET-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis A47 : md_own dA <> LNull -> md_p dA + 4 * md_n dA + 8 <= 2^47.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02[0@C11264273767.233C11264273767.234C17025492443.231C17025492443.232C237391055.235  D49149041523.237K1307012896.231 K1307012896.232 K14404318560.236K14404318560.238K19167344963.231K19167344963.232K21825380662.236K25382859142.236K34781802463.238K36226586886.236K37145934365.236K46334408099.233K46334408099.234K47640792208.236K65977774223.236K7472647416.236 L10307112399.6  L12530932062.2  L1294499141.2   L13194033576.4  L14399007128.5  L14402745233.4  L146940511.12   L15477852824.1  L15732191779.8  L17363933084.3  L17899959536.3  L19169968050.5  L21185175647.13 L21811226567.5  L21812184615.210L21813457239.6  L21820691587.187L21824805693.6  L21825511751.22 L22648980509.4  L23100341967.211L23461305150.176L23461383506.175L23648853855.210L24912882372.1  L25075940858.17 L25238078280.8  L25367656311.17 L26063715927.5  L26349732406.4  L26502719108.5  L26711796672.7  L30116386634.3  L31344024617.5  L31660590328.4  L32371227958.4  L3370416396.3   L34125036709.14 L34444340830.3  L34456730698.22 L34781933486.22 L34788029223.5  L34794874056.5  L35663928186.7  L36233404407.4  L37159364728.3  L38126476039.3  L38129129185.3  L38235734261.1  L38419819008.4  L38857383769.14 L39172636981.0  L39280637297.0  L40145318023.3  L40597388054.15 L41126667518.5  L41435825861.1  L414529038.13   L43082406170.1  L43343125556.7  L43878034250.5  L44359877029.4  L44608837741.2  L46329554370.4  L47401054516.1  L47638170209.4  L51271499937.0  L51284464315.211L51337770057.14 L5260001178.176 L53236858660.5  L53236858660.6  L53611082567.22 L53615638561.2  L5413828406.4   L55376803619.3  L56339604272.4  L57129482334.4  L58640675965.173L58641002120.176L59308873939.7  L59944282246.2  L60098763854.3  L60283674290.10 L6141606276.1   L61714773053.6  L61927706159.187L61929067222.175L61935918219.210L65976202878.4  L67229871644.4  L67699444668.5  L7458806278.5   L7476911773.3   L8016725142.2   O10808784559.236O11264273767.233O11264273767.234O15317411454.238O16243737850.236O16578584084.236O17025492443.231O17025492443.232O237391055.235  O36019832244.236O36632239767.231O36632239767.232O48199580980.236O50423766113.236O57399310481.236O8875751214.236 O8875751214.238 P1307012896.231 P1307012896.232 P14404318560.236P21825380662.236P46334408099.233P46334408099.234Q10038479450.218Q12370813529.219Q17201186764.218Q18135743526.175Q18136070065.178Q18136087844.178Q26345934764.237Q32879014451.237Q34224482651.175Q34422627987.178Q37323683587.217Q37618859054.218Q38248387216.237Q39095944126.219Q39212284437.178Q40278613695.219Q43879899724.237Q5470532147.218 Q5485174314.219 Q58692335428.178Q59703481013.219Q60511567613.178Q60807234163.219Q61261927849.218Q61264001456.219Q6143569392.219 Q64768105610.178Q66375044744.219Q67339669022.218Q8222473558.219 Q9538787269.175 00000100200300400500600700800901D02C03B03C04M05E06O07>07?07@08O09X0:90:M0:V0:W0:c0:d0:e0;P0;T0;m0<50<=0<>0<]0<^0=^0=_0>R0>e0?G0?P0@10@K0@e0Ac0Af0BN0Bg0Bh0C80CE0CY0D00D90DE0DQ0D^0Dg0EI0EJ0E`0F>0F?0F@0FU0FV0FW0FX0FY0F]0Fh0Fi0Fj0Fk0G40G;0G<0G?0G_0Gc0H:0HA0HM0HS0HT0HX0HY0HZ0I;0I<0IV0If0J60JP0JQ0J^0Jg0K20K=0KW0L10LF0LM0LW0M50M90ML0N90Nh0Om0On0Oo0P00P10P20P90P:0P;0P<0P=0P>0P?0P@0PA0PX0PY0PZ0P[0P\0P]0P^0P_0P`0Pa0Pb0Pc0Pd0Pe0Pf0Q;0Qe0R<0RG0RR0R]0S;0Sg0T20T=0U80UO0Ug0Uh0V30V40VO0Vf0W=0WK0WL0WT0WU0Wj0X?0XV0Xa0Y60YK0Z?0ZGFFFFFFFFFS1X3xs02dA1n2NA1N3pXc2xs2HN3HNA3VA14LEN12KX4LENE3ENa1K3EP04SEPL4LMID1l4SLENS1R2sp2nX3xs02dA2lo3NGN1n2NA1N3pXc2xs3LOS3ALO3NM13ENa1K2PC4LMIDS1R2sp2nX3xs02dA2lo3NGN1n2NA1N3pXc2xs3LOS3ALO3NM13ENa1K2PC4LMIDFS1R2sp2nX3xs02dA2lo4SLO23NGN1n2NA1N3pXc2xs5NEEDR3LOS3ALO3NM13ENa1K2PC4LMIDS2sp1X3xs02dA2lo1n2NA2xs2HN2KX3ENa1K3EP03ESK4LMID1l4SLENS1R2sp2nX3xs02dA2lo4SLO23NGN1n2NA1N3pXc2xs5NEEDR3LOS3ALO3NM13ENa1K2PC4LMIDS2sp1X3xs02dA2lo1n2NA2xs2KX4LENE1K3EP03ESK4LMIDFFS1X2nX3xs02dA3NGN1n2NA1N3pXc2xs2HN3HNA3VA14LEN13NM12KX4LENE3ENa1K3EP04SEPL4LMIDS1X2nX3xs02dA3NGN1n2NA1N3pXc2xs2HN3HNA3VA13NM12KX4LENE3ENa1K3EP03XPc4LMIDS2sp1X3xs02dA2lo1n2NA2xs3DSX4LMIDS1R2sp2lo4SLO25NEEDRS3dXc3NR1FS2dA1n2NA2HNFFS1R2sp2lo4SLO21n2NA1N3pXc2HN3HNA5NEEDR4XLScS2spS1n2NA1N2xs2HN3HNA4LEN11KS1n2NA1KS1n2NA1KFS2dA1n2NA1N3pXc2HN3HNA3ENa4SEPLFS2ra2sp1X3xs02dA1n2NA3pXc2xs2HN2X03SPR2A03ENa1K3EP02P04A47'4LMIDFS2ra2sp1X2nX3xs02dA3NGN2NA2xs2X02NR3SPR2A04LENE3ENaS1n2NA1N2HN3HNA3NR1S2sp2lo1n2NA1N3pXc2HN3HNA3SPR4XLScS2dA1n2NAS2ra2sp1X3xs02dA1n2NA3pXc2xs4LMIDS2ra2sp1X3xs02dA2xs2A03A16S2ra2sp1X3xs02dA2xs2A03A16S2ra2sp1X3xs02dA1n2NA3pXc2xs2HN2X03SPR2A03ENa3EP02P04A47'4LMIDS1nS2sp2lo1n2NA1N3pXc2xs2HN3HNA4LEN11K4XLScS1X1n2NA1N3pXc2HN3HNA3XPcFS1R3HIA1h2sp3TOPS1n2NA3pXc2HNS1R2sp2lo4SLO25NEEDRS1n2NA1N2xs2HN3HNA4LEN1S1n2NA2HNS1n2NA3pXc1KS1n2NA3pXc1KS2sp1X2lo3DSXS1n2NA2HNS2sp2lo1n2NA1N3pXc2HN3HNA3NR14XLScFS1R2sp2lo4SLO23NRA3SPRS2sp2dA2lo1n2NA2HN3SPR3ENa3ESKFFS1R3HIA1h2sp2lo3TOP1HFFFFS2loS1n2NA2HN1KFSSS1n2NA2HNS2sp2loFS1nS1n2NA1N3pXc3HNA3P472dA3ENa4A47'S2NAS1n2NA1N2xs2HN3HNA4LEN1S2sp2loS2dA1n2NA2HNS1n2NAFS2spFSS2ra2sp1X3xs02dA1n2NA3pXc2xs4LMIDFS2ra2sp1X3xs02dA2xs2X03X16S1n2NA1N3pXc3HNAS1n2NA1N3pXc3HNAS2sp1n2NA1N2HN3HNA3SPR3NR1FS1n2NA3pXc2xsS1n2NA2HNS1n2NA2HN1KS1n2NA2HN1KS2ra2sp1X3xs02dA2xs2A03A16S2ra2sp1X3xs02dA2xs2A03A16S2dA1n2NA2HN3ENa1K2Z0S2sp2loS1R2lo3LOSS2sp2lo1n2NA1N3pXc2HN3HNA1a2NOS2spS1n2NA1N2HN3HNA3NR1S2ra2sp1X3xs02dA1n2NA2xs2HN2X03SPR2A03NRE3ENaS2ra2sp1X3xs02dA1n2NA1N2xs2HN3HNA2X03SPR3NR12A0S2ra2sp1X3xs02dA1n2NA3pXc2xs2HN2X03SPR2A03ENa1K3EP02P04A47'4LMID4SLENFFFFFS2sp2loFFFFFFFFS2dA1n2NA3pXc2xs1K4LMIDFFFFFFFFFFFFFFS3xs02dA1n2NA2xs4LMIDS2ra2sp1X3xs02dA1n2NA3pXc2xs2X03XAL1K4LMIDS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2xsS3xs02dA2xsS3xs02dA2xsS3xs02dA1n2NA3pXc2xs2HN1K4LMIDS2nX3xs02dA3NGN1n2NA1N3pXc2xs3NM13ENa1K4LMIDS3xs02dA2xsS3xs02dA2xsS1R2sp3xs02dA2lo4SLO21n2NA2xs5NEEDR3LOS4SP643ALO3ACP1K4LMIDS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2lo1n2NA2xs4LMIDFS3xs02dA2xsFS2sp3xs02dA2lo1n2NA2xs4LMIDS1X3xs02dA1n2NA2xs4LMIDS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2xs2A0FS3xs02xsFS3xs02dA1n2NA2xs4LMIDS3xs02dA1n2NA2xs4LMIDS1X3xs02dA1n2NA2xs4LMIDS3xs02dA2xsS3xs02dA1n2NA2xs4LMIDS3xs02dA1n2NA2xs4LMIDS2ra2sp1X3xs02dA1n2NA3pXc2xs2X03SPR2A03AAL1K2P04LMIDS3xs02xs". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 NGN A47"] Lemma sa_TAIL : forall n NA, KJ_stmt n NA.
  Proof.
    unfold KJ_stmt. intros n NA. intros until xt6; intros J0 NGX RA RB HN HNA EOn VA1 VA2 VB1 VB2o BV BF.
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
    zstep. zstep. shadow_chk OEA (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    replace (Z_to_bv 64 (n * 4)) with (Z_to_bv 64 (4 * n)) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    zstep. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear - A0 A16 X0 X16; lia).
    - (* [comment removed for export] *)
      eapply sa_MEMSET; [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| exact HN| exact HNA| exact EOn| exact VA1| | exact VB1| exact VB2| exact BV| exact BF].
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
        eapply sa_MEMSET; [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| right; split; [exact DBJA| exact BA]| exact RB| exact HN| exact HNA| exact EOn| exact VA1| | exact VB1| exact VB2| exact BV| exact BF].
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
        destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
        replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STc, SLOT by (clear; lia).
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
        zstep. zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
        clear CE OEA.
        clear MU WM. pose proof (munch_refl [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -112)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_SA) as SPC. unfold A_ASAN_MEMCPY_SA in SPC.
        acallxA_sp (bv_unsigned sp + -112)
          (eapply SPC with (h := hc) (LB := LBc) (LF := LF) (DST := pXc + 4 * n) (SRC := md_p dA + 4 * n) (n := 4 * (NA - n)) (lo := lo)
                            (ds := u32s (firstn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) xs))) (ss := u32s (firstn (Z.to_nat (NA - n)) (skipn (Z.to_nat n) (md_limbs dA))));
           rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by qlia;
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
                 | match goal with |- ?g => idtac "TCOPY-PRE-LEFT:" g end ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-TCOPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
        match goal with H : stk asegs m6 lo (bv_unsigned sp + -112) |- _ => rename H into ST6 end.
        match goal with H : u8arr asegs m6 (pXc + 4 * n) _ |- _ => rename H into HPA end.
        match goal with H : HM asegs R HIA hc LBc LF m6 |- _ => rename H into HH6 end.
        match goal with H : rw_cells asegs m6 (bv_unsigned sp + -112) _ |- _ => rename H into SL6 end.
        assert (ST6' : stk asegs m6 lo (bv_unsigned sp + -104)).
        { eapply stk_merge; [exact ST6| | clear - SLO2 NEEDR LOSP; lia].
          replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
          apply stk_of_rw_cells. exact SL6. }
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
        assert (HW6 : forall a, ~ outside [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -112)] a ->
                      (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 104).
        { intros a NO. cbn [outside] in NO.
          assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 104) by (clear - NO HN HNA; lia).
          destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
        assert (DJF : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -112)] (bv_unsigned sp - 104) 104).
        { cbn. split; [clear - XLSc SLO2 NEEDR HN HNA; lia| split; [clear; lia| exact I]]. }
        assert (DJX : disjoint_from [(pXc + 4 * n, pXc + 4 * n + 4 * (NA - n)); (lo, bv_unsigned sp + -112)] X 16).
        { cbn. split; [clear - XPc HN HNA; lia| split; [clear - DSX; lia| exact I]]. }
        assert (LEN6' : length (firstn (Z.to_nat n) xs ++ (Amid ++ HI)) = length xs).
        { rewrite !length_app, LAM, firstn_length_le by (clear - HN HNA LEN1; lia). subst HI. rewrite !length_skipn. clear - HN HNA LEN1 K; lia. }
        pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6 DJF DJX XARR6 LEN6') as J6.
        pose proof (rideS_xl_munch dA _ _ _ _ _ _ (pXc + 4 * n) (pXc + 4 * n + 4 * (NA - n)) (firstn (Z.to_nat n) xs ++ (Amid ++ HI)) m6 J0 (or_intror (conj DBJA BA)) eq_refl
                      ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear - HNA; lia) MU WM) as RA6.
        pose proof (rideS_xl_munch dB _ _ _ _ _ _ (pXc + 4 * n) (pXc + 4 * n + 4 * (NA - n)) (firstn (Z.to_nat n) xs ++ (Amid ++ HI)) m6 J0 RB eq_refl
                      ltac:(cbn [md_p]; clear - HN; lia) ltac:(clear - K; lia) ltac:(cbn [md_p md_n]; clear - HNA; lia) MU WM) as RB6.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6, RA6, RB6.
        eapply sa_MEMSET; [exact J6| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA6| exact RB6| exact HN| cbn [md_n]; exact HNA| intros _; reflexivity
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L11132759166.4  L21826988606.168L21826988989.171L26168871548.12 L29763661393.2  L29765672657.171L3465864266.3   L35663928186.7  L46160478526.168L46160487540.171L5260339702.170 L58609956177.2  L59308660947.5  L59314955108.4  L59314955108.8  L60098763854.3  Q26207421841.172Q26207721832.173Q26207774677.170Q31654082872.172Q39212284437.173Q43925228937.173Q60511567613.173Q60697995187.173Q8880817289.170 Q9538463866.170 00000600Z01>01h01o02E02N02c03:03Q03h03o04>04I04b04l05605@05J05T05^05h06006=06G06OS1f2BFS2ra2sp1X3xs02xs1n2NA2HN4NA162X03SPRS2ra2sp1X3xs02xs1n2NA2HN4NA162X03SPRS1X2sX2nX2pX3xs04padX4ownX2dA2dB1v2BV4PHI0S1N3NR1S2ra2sp1X3xs01N2xs3NR1S1N2NA2K1S1R3HIA1h2sp2lo3TOP1HS2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S1N3NR1S1N2NA2K12H12E0S1N2NA2K11ES2nX2dA3NGN1N2NA3NM12K11ES1R2lo3LOSS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS3xs02xsS1X3xs02xs2X0S1X3xs02xsS3xs02xs". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 NGN A47"] Lemma sa_J1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pn,$8.PNA,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R1=.R1<.R1;.R1:.R19.R18.)P,(14.(15.R19.)VnX,)P,(74.VdA,R1=.R1<.R1;.R1:.)P,(74.VdB,R1>.R1=.R1<.R1;.)P,(2?.(14.=R1;.)(14.R1;.R1:.))P,(30.R1;.(36.+2.+10.))P,P,(10.$8.(1;.VdA,)VX,)(2?.(10.$8.(15.R1?.)R1=.)(10.$8.(55.(56.R1?.))(4>.VdA,)))P,P,(?.(10.$8.(1;.VdA,)VX,))(10.$8.(15.VdA,)R1>.)P,P,(10.$8.(1;.VdB,)VX,)(2?.(10.$8.(6=.(56.R21.)R20.)(4>.VdB,))(14.R20.(15.R21.)))P,P,(?.(10.$8.(1;.VdB,)VX,))(2?.(10.$8.(6=.(56.VdB,)R21.)(4>.VdB,))(14.R21.(15.VdB,)))P,(14.R27.=)P,(14.R27.=)P,(14.=(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))(52.$48.(53.$48.VR,VHIA,R28.Vmo,)$54.(44.(45.R22.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R21.R20.R1?.(29.&40.VX,)(29.&40.(1;.VdB,))R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(29.&40.(1;.VdA,))(29.&40.R24.)R16.(29.&40.(23.(1;.VdA,)+:.))(29.&40.R23.)R15.(29.&40.(57.(2=.VR,)))R14.R13.R12.R11.R10.R?.R>.)VF,(29.&40.+9>0=4.)Vfc,(46.(3.&40.))R26.(47.$48.)))")
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
    assert (BF' : f <= sub_abs_FR0 d) by (unfold sub_abs_FR0, calls_FR, fr_charge; clear - BF D0; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - HN NA16; lia).
    { eapply sa_ret with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| right; left; reflexivity| clear - BV PHI0; lia| exact BF']. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - HN NA16 NR1; lia).
    - eapply (sa_TAIL n NA); [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| exact HN| cbn [md_n]; clear - K1; lia| | exact VA1| exact VA2| intros E; exact (proj1 (VB1 E))| exact VB2| clear - BV PHI0; lia| exact BF'].
      cbn [md_own]. intros H1. destruct own; [exfalso; ddestruct (OWN0 eq_refl) as (_ & E0 & _); clear - E0 H1 K1; lia| reflexivity| exfalso; exact (NS1 eq_refl)].
    - (* [comment removed for export] *)
      exfalso. destruct (Z.eq_dec (md_addr dA) X) as [EAX|NAX]; [destruct (VA1 EAX) as [E _]; cbn [md_n] in E; clear - E K1; lia|].
      pose proof (VA2 NAX) as E. clear - E K1 NGN NM1. lia.
    all: match goal with |- ?g => idtac "J1-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@L11007909341.4  L11132759166.4  L12530932062.2  L14714961187.3  L1770629485.4   L19050221415.2  L19056427139.185L22606344295.2  L26168871548.12 L26479600656.3  L29012665503.185L29465010999.3  L31813109760.2  L3519677831.4   L3519677875.4   L35663928186.7  L39280637297.0  L40155635431.5  L41422232819.4  L44691115017.2  L58641002120.185L58644810306.182L60098763854.3  L60976047698.7  Q18123063833.184Q18135196125.186Q18136087844.187Q34211977060.184Q34421655807.186Q39212284437.187Q58692335428.187Q60511567613.187Q64768105610.187Q9534646778.184 00000=00C00L00V00^00g01B01K02502?02_02h03003=03I03^03_03m03n04704W05705A05X05i06:06K06\06m07>07R07`08108?S1r2na4NARg1KS1f2BFS3dXc3NR1S1X2dA3SXBS1r2na1KS2na4NARgS2ra2sp1X3xs02xs2zs2na4NARgS2na4NARgS1X2sX2nX2pX3xs04padX4ownX2dA2dB1v2BV4PHI0S1X2dB3SXBS2ra2sp1X3xs02xs1r2zs2HR2na4RB10S1r2zs2HRS2dA3NRES2dB1r2HR3NRES1N1r2HR3NR1S1R3HIA1h2sp2lo3TOP1HSS1r2zs2HR2na1KSS2na4NARgS2ra2sp1X3xs02dA2xs2zs2na2A03A16S2ra2sp1X3xs02dA2xs2zs2na2A03A16S1R2lo3LOSS2dA2dB1r2na3ABD3HI22PWS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2naS3xs02dA2xs2zs2na2A0S3xs02xs2zs2naS3xs02dA2xs2zs2naS3xs02xs2zs2na". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 NGN A47"] Lemma sa_FOUND : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pzs,(1.(3.&40.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R1?.R1>.R1=.R1<.R1;.R1:.)P,(14.(15.R1;.)VnX,)P,(74.VdA,R1?.R1>.R1=.R1<.)P,(74.VdB,R20.R1?.R1>.R1=.)P,P,(10.$8.(1;.VdB,)VX,)(10.(1.(3.&40.))R1=.(56.R1?.))P,P,(?.(10.$8.(1;.VdB,)VX,))(10.(1.(3.&40.))R1>.(56.VdB,))P,(10.$8.(55.R1>.)(4>.VdB,))P,(2?.(14.=R20.)(14.R20.(6;.(6<.(3.&40.)R1?.))))P,(10.$8.(6=.R20.R21.)(55.R20.))P,P,(14.+1.R22.)(14.(36.+2.(1>.+20.(26.R23.+1.)))(55.R22.))P,P,(10.$8.(1;.VdA,)VX,)(10.$8.(55.(56.R25.))(4>.VdA,))P,(14.R2:.=)P,(14.R2:.=)P,(14.=(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))(52.$48.(53.$48.VR,VHIA,R2;.Vmo,)$54.(44.(45.R25.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R24.R23.R22.(29.&40.VX,)(29.&40.(1;.VdB,))R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(29.&40.(1;.VdA,))(29.&40.R27.)R19.R18.R17.R16.(29.&40.(57.(2=.VR,)))R15.R14.R13.R12.R11.R10.R?.)VF,(29.&40.+9>098.)Vfc,(46.(3.&40.))R29.(47.$48.)))")
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
    zstep. zstep. zstep. shadow_chk OEA (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 na)) with (Z_to_bv 64 na) by (unfold zx16; rewrite !unsigned_lit by (clear - NARg; lia); rewrite Z.mod_small by (clear - NARg; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (clear - NARg HR RB10; lia).
    - eapply (sa_J1 _ _ _ _ _ _ r na); [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| clear - HR K; lia| clear - NARg; lia| | exact NAR| | | exact BV| exact BF| exact PHI0].
      + intros E. split; [exact (NAX E)| exact (VAX E)].
      + intros E. cbn [md_limbs md_n]. rewrite <- (ZBX E). split; [rewrite LVR; exact VZ| rewrite <- LEN1, <- (ZBX E); clear - HR; lia].
      + intros NE. rewrite <- (ZBR NE). split; [rewrite LVR; exact VZ|].
        destruct RB as [E|[DBJ B]]; [exfalso; exact (NE E)|].
        pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & LENE & _). rewrite <- LENE, <- (ZBR NE). clear - HR; lia.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply sa_ret with (r := MBEDTLS_ERR_MPI_NEGATIVE_VALUE); [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| right; right; split; [reflexivity|]| clear - BV PHI0; lia| unfold sub_abs_FR0, calls_FR, fr_charge; clear - BF D0; lia].
      pose proof (HIGH ltac:(clear - K NARg; lia)) as HI2. rewrite VZ in HI2.
      assert (PW : 2 ^ (32 * na) <= 2 ^ (32 * (r - 1))) by (apply Z.pow_le_mono_r; clear - K NARg; lia).
      clear - ABD HI2 PW. lia.
    all: match goal with |- ?g => idtac "FOUND-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L12530932062.2  L14714961187.3  L19050221415.2  L22606344295.2  L268303811.2    L31813109760.2  L32121500971.2  L35663928186.7  L39280637297.0  L44691115017.2  L58640675965.175L58641002120.178L58772975347.2  L60098763854.3  Q18135196125.179Q18135743526.177Q18136087844.180Q34224482651.177Q34421655807.179Q39212284437.180Q58692335428.180Q60511567613.180Q64768105610.180Q9538787269.177 00000900C00L00U00\00d00l01A01B01K01h02E02N02X02f03403B03P03^03l04=04H04V04aS3dXc3NR1S1X2dA3SXBS2na4NARgS2na4NARgS1N3NR1S2dA3NRES2dB3NRES1R3HIA1h2sp2lo3TOP1HSS2na4NARgS2ra2sp1X3xs02dA2xs2na2A03A16S2ra2sp1X3xs02dA2xs2na2A03A16S2na4NARgS1R2lo3LOSS3xs02dA2xs2naS3xs02dA2xs2naS3xs02dA2xs2naS3xs02dA2xs2naS3xs02dA2xs2naS3xs02dA2xs2naS3xs02dA2xs2na2A0S3xs02xs2naS3xs02dA2xs2naS3xs02xs2na". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 NGN A47"] Lemma sa_ZERO : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R1>.R1=.R1<.R1;.R1:.R19.)P,(14.(15.R1:.)VnX,)P,(74.VdA,R1>.R1=.R1<.R1;.)P,(74.VdB,R1?.R1>.R1=.R1<.)P,(10.$8.(4>.VdB,)=)P,P,(10.$8.(1;.VdA,)VX,)(10.$8.(55.(56.R1?.))(4>.VdA,))P,(14.R24.=)P,(14.R24.=)P,(14.=(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))(52.$48.(53.$48.VR,VHIA,R25.Vmo,)$54.(44.(45.R21.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R20.R1?.R1>.(29.&40.VX,)(29.&40.(1;.VdB,))R1=.R1<.R1;.R1:.R19.R18.R17.R16.(29.&40.(1;.VdA,))R15.R14.R13.R12.R11.(29.&40.(57.(2=.VR,)))R10.R?.R>.R=.R<.R;.R:.)VF,(29.&40.+9>0;8.)Vfc,(46.(3.&40.))R23.(47.$48.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 NGX RA RB VZ0 VAX BV BF PHI0.
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
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1, CEA.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OEA (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 na)) with (Z_to_bv 64 na) by (unfold zx16; rewrite !unsigned_lit by (clear - NARg; lia); rewrite Z.mod_small by (clear - NARg; lia); reflexivity).
    zstep.
    eapply (sa_J1 _ _ _ _ _ _ 0 na); [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| clear - NARg; lia| clear - NARg; lia| | exact NAR| | | exact BV| exact BF| exact PHI0].
    - intros E. split; [exact (NAX E)| exact (VAX E)].
    - intros _. cbn [md_limbs md_n]. split; [rewrite VZ0; reflexivity| clear - NR1; lia].
    - intros NE. split; [rewrite VZ0; reflexivity|].
      destruct RB as [E|[DBJ B]]; [exfalso; exact (NE E)|].
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & _ & NRE & _). clear - NRE; lia.
    all: match goal with |- ?g => idtac "ZERO-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L10085909942.2  L21041645149.3  L21631969095.2  L23970764156.154L36695016552.3  L41415988076.3  L42608597650.1  L45942495769.145L45942685932.148L54425651213.3  L58667209005.3  L59308583409.4  L59310648043.6  L61217976771.4  L67418292019.3  L780814420.4    Q12761110700.149Q26295627581.149Q28698763987.151Q31703745645.146Q50458135125.149Q5179077707.146 Q5179126208.151 Q5179290953.149 Q57811535654.149Q8943555749.146 00000600>00D01801B01C01F02:02n03803@03M03c04004:04G04d05305L05e06706P06i07B07[07jS2pb1rS1k1r2HkS2zs1rS2ra2sp1X3xs01k2zs2pb3NBv1r2Hk4LENZ3PB02HR2X03SPR2EBS3NBv1r2HRSS1rS2ra2sp1X3xs01k2zs2pb3NBv1r2Hk4LENZ3PB02HR2X03SPR2EBS2ra2sp1X3xs01k2zs2pb3NBv1r2Hk4LENZ3PB02HR2X03SPR2EBS3NBv1r2HRS1w2WR1HS3NBv1r2Hk2HRS2zs3NBv1r4LENZ2HR3NTHS3NBv1r2HR2K2S3NBv1r2HRS3NBv1r2HR2K2S3xs01k2zs2pb3NBv1r2Hk3PB02HRS3xs01k2zs1r2HkS3xs01k2zs2pb3NBv1r2Hk2HRS3xs01k2zs2pb3NBv1r2Hk2HRS3xs01k2zs2pb1r2HkS3xs01k2zs2pb3NBv1r2Hk2HRS3xs01k2zs2pb3NBv1r2Hk2HRS3xs01k2zs2pb3NBv1r2Hk2HRS3xs01k2zs2pb3NBv1r2Hk2HRS3xs01k2zs1r2Hk". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 NGN A47"] Lemma sa_SCANLOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pk,$70.Pzs,(1.(3.&40.))Ppb,$8.PNBv,$8.Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(14.R16.(6;.R20.))P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R1=.R1<.R1;.R1:.R19.R18.)P,(14.(15.R19.)VnX,)P,(74.VdA,R1=.R1<.R1;.R1:.)P,(74.VdB,R1>.R1=.R1<.R1;.)P,P,(10.$8.(1;.VdB,)VX,)(10.(1.(3.&40.))R25.(56.R1=.))P,P,(?.(10.$8.(1;.VdB,)VX,))(10.(1.(3.&40.))R26.(56.VdB,))P,(10.$8.(55.R26.)(4>.VdB,))P,(69.$48.R20.R26.(6:.R27.))P,(10.$8.(6;.(6<.(3.&40.)R28.))R26.)P,(14.R27.+2710.)P,(30.=R29.)P,(68.$48.(2=.VR,)(2>.$48.VR,VHIA,R26.)R24.R2:.(1>.+4.R29.))P,(2?.(14.+1.R23.)(14.R23.R2:.))P,(10.$8.(6=.R2=.R24.)(55.R2=.))P,P,(10.$8.(1;.VdA,)VX,)(10.$8.(55.(56.R27.))(4>.VdA,))P,(14.R2<.=)P,(14.R2<.=)P,(14.=(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))(52.$48.(53.$48.VR,VHIA,R2=.Vmo,)$54.(44.(45.R28.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R27.R26.R25.(29.&40.VX,)(29.&40.(1;.VdB,))(29.&40.(23.R31.(1>.+4.(26.R29.+1.))))(29.&40.(23.R31.(1>.+4.(26.R29.+1.))))R24.R23.R22.R21.R20.R1?.(29.&40.(1;.VdA,))(29.&40.R29.)R1>.R1=.R1<.R1;.(29.&40.(57.(2=.VR,)))R1:.R19.R18.R17.R16.R15.R14.)VF,(29.&40.+9>05<.)Vfc,(46.(3.&40.))R2;.(47.$48.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 NGX RA RB ZBX ZBR VZ EBY LENZ NB10 PB0 OEL HR ZA VAX BV BF PHI0; [exfalso; clear - Hk HR; lia|].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 SA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEL (pb + 4 * (r - 1)) 4.
    (* [comment removed for export] *)
    destruct (nth_error zs (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc pb zs (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_w32_nth zs (Z.to_nat (r - 1)) w NTH) as LW. pose proof (w32_range w) as WR.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite bv_unsigned_sx32 in K0; fold (w32 w) in K0.
    - (* [comment removed for export] *)
      eapply (sa_FOUND _ _ _ _ _ _ r zs); [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| exact ZBX| exact ZBR| exact VZ| rewrite LENZ; clear - HR; lia| exact ZA| | exact VAX| exact BV| exact BF| exact PHI0].
      intros _. rewrite <- ZA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ zs (r - 1)) by (clear - HR; lia). rewrite LW.
      pose proof (lval_range zs (r - 1) ltac:(clear - HR; lia)) as [G _].
      assert (W1 : 1 <= w32 w) by (assert (w32 w <> 0) by (intros E; apply K0; apply (proj2 (sxz_zero_iff _ WR)); exact E); clear - H WR; lia).
      assert (P0' : 0 < 2 ^ (32 * (r - 1))) by (apply Z.pow_pos_nonneg; clear - HR; lia). clear - G W1 P0'. nia.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ WR)) in K0.
      assert (ZA' : lval zs (r - 1) = limbs_val zs).
      { rewrite <- ZA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ zs (r - 1)) by (clear - HR; lia). rewrite LW, K0. clear; lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - HR NB10; lia).
      + replace (Z_to_bv 64 (pb + 4 * (r - 1) + -4)) with (Z_to_bv 64 (pb + 4 * (r - 1 - 1))) by (f_equal; clear; lia).
        replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 (r - 1)) by (f_equal; clear; lia).
        eapply (IH zs pb NBv _ _ _ _ _ _ (r - 1)); try eassumption; [clear - Hk; lia| clear - HR K2; lia].
      + (* [comment removed for export] *)
        assert (r = 1) as -> by (clear - K2 HR; lia). change (1 - 1) with 0 in ZA'. rewrite lval_0 in ZA'.
        zstep.
        eapply sa_ZERO; [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| rewrite <- VZ, <- ZA'; reflexivity| exact VAX| exact BV| exact BF| exact PHI0].
    all: match goal with |- ?g => idtac "SCANLOOP-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L10087976358.2  L10642089944.1  L13964994716.2  L15657432408.2  L26479600656.3  L33642305396.3  L39172636981.0  L48359981522.2  L48364224594.155L51668879259.3  L51916100306.2  L58177949655.156L59308628179.4  L59315053158.1  L5966144285.3   L66990871592.155L9659381246.2   Q1947013759.157 Q21750159756.157Q21750569356.158Q36646300200.158Q42658418930.156Q49433500843.158Q53113203581.157Q64808403539.15600000800<00F00K00U00b00c00m01M01Z01d02;02K02N02[03903A03P03_03n04=04L05105@05OS3NBv2pbS2zsS3NBv4NB10S3NBvS1X2dB3SXBS3NBv4NB102K0SS3NBv4NB10S2ra2sp1X3xs02dB3dXc3NBv2zs4NB10S3NBv2zs4LENZS3NBv4NB10S2ra2sp1X3xs02dB3dXc2zsS3NBv2zs4LENZ2K0S1CS3NBv4NB102K0S2ra2sp1X3xs02dB3dXc2zs2B03B16S3NBv2K0S3xs02dB3dXc2zsS3xs02dB3dXc2zsS3xs02dB3dXc2zsS3xs02dB3dXc2zsS3xs02dB3dXc2zsS2ra2sp1X3xs02dB3dXc2X03SPR2zs2B03BALS3xs02dB3dXc2zsS3xs02dB3dXc2zs". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 NGN A47"] Lemma sa_SCAN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pv,$8.Pf,$8.Phc,(0.$48.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(4:.$48.VR,VHIA,Vh,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$4;.(4<.$2.)R1=.R1<.R1;.R1:.R19.R18.)P,(14.(15.R19.)VnX,)P,(74.VdA,R1=.R1<.R1;.R1:.)P,(74.VdB,R1>.R1=.R1<.R1;.)P,P,(10.$8.(1;.VdA,)VX,)(10.$8.(55.(56.R1=.))(4>.VdA,))P,P,(10.$8.(1;.VdB,)VX,)(10.$8.(55.(56.R1>.))(4>.VdB,))P,(14.R23.=)P,(14.R23.=)P,(14.=(38.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))(52.$48.(53.$48.VR,VHIA,R24.Vmo,)$54.(44.(45.R20.(29.&40.(23.(=.&40.Vsp,)-70.))Vgp,Vtp,R1?.R1>.R1=.(29.&40.VX,)(29.&40.(1;.VdB,))R1<.(29.&40.(23.(1;.VdB,)+:.))R1;.R1:.R19.R18.R17.R16.(29.&40.(1;.VdA,))R15.R14.R13.R12.R11.(29.&40.(57.(2=.VR,)))R10.R?.R>.R=.R<.R;.R:.)VF,(29.&40.+9>030.)Vfc,(46.(3.&40.))R22.(47.$48.)))")
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
                   /\ (1 <= NBv -> 0 < pb) /\ (1 <= NBv -> aobj asegs AL (hcs asegs R HIA hc) mc pb (4 * NBv))
                   /\ (md_addr dB = X -> zs = md_limbs dXc) /\ (md_addr dB <> X -> zs = md_limbs dB)).
    { destruct RB as [E|[DBJ B]].
      - destruct (rideS_view dB _ _ _ _ _ _ (md_n dXc) J0 (or_introl E) (proj1 NR1) ltac:(intros _; apply Z.le_refl) ltac:(intros C; exfalso; exact (C E)))
          as (pb & sb & nb & pdb & zs & CEB & OEB & B0 & B16 & BAL & ZB & _ & _ & _ & PB0 & _ & OBL & ZBX & ZBR & NBX & _).
        pose proof (ZBX E) as EZ. pose proof (NBX E) as ENb. subst zs nb. dexists (md_n dXc), pb, sb, pdb, (md_limbs dXc).
        split; [exact CEB|]. split; [exact OEB|]. split; [exact B0|]. split; [exact B16|]. split; [exact BAL|]. split; [exact ZB|]. split; [exact LEN1|]. split; [exact NR1|].
        split; [exact PB0|]. split; [exact OBL|]. split; [intros _; reflexivity| intros C; exfalso; exact (C E)].
      - pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & LENE & NRE & _).
        assert (ENX : md_addr dB <> X) by (destruct DBJ as [_ _ _ _ SXB _]; cbn [md_addr] in SXB; clear - SXB; lia).
        destruct (rideS_view dB _ _ _ _ _ _ (md_n dB) J0 (or_intror (conj DBJ B)) (proj1 NRE) ltac:(intros C; exfalso; exact (ENX C)) ltac:(intros _; apply Z.le_refl))
          as (pb & sb & nb & pdb & zs & CEB & OEB & B0 & B16 & BAL & ZB & _ & _ & _ & PB0 & _ & OBL & ZBX & ZBR & _ & NBR).
        pose proof (ZBR ENX) as EZ. pose proof (NBR ENX) as ENb. subst zs nb. dexists (md_n dB), pb, sb, pdb, (md_limbs dB).
        split; [exact CEB|]. split; [exact OEB|]. split; [exact B0|]. split; [exact B16|]. split; [exact BAL|]. split; [exact ZB|]. split; [exact LENE|]. split; [exact NRE|].
        split; [exact PB0|]. split; [exact OBL|]. split; [intros C; exfalso; exact (ENX C)| intros _; reflexivity]. }
    ddestruct BFX as (NBv & pb & sb & pdb & zs & CEB & OEB & B0 & B16 & BAL & ZB & LENZ & NB10 & PB0 & OBL & ZBX & ZBR).
    assert (VZ : limbs_val zs = mpd_abs dB) by (destruct (Z.eq_dec (md_addr dB) X) as [E|NE]; [rewrite (ZBX E); exact (VBX E)| rewrite (ZBR NE); reflexivity]).
    unfold mpi_cells in CEB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 NBv)) with (Z_to_bv 64 NBv) by (unfold zx16; rewrite !unsigned_lit by (clear - NB10; lia); rewrite Z.mod_small by (clear - NB10; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - NB10; lia).
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 NBv) with (Z_to_bv 64 0) by (f_equal; clear - K0; lia).
      assert (EZ : zs = []) by (destruct zs; [reflexivity| exfalso; cbn [length] in LENZ; clear - LENZ K0; lia]).
      eapply (sa_FOUND _ _ _ _ _ _ 0 zs); [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| exact ZBX| exact ZBR| exact VZ| clear; lia| rewrite EZ; reflexivity| intros C; exfalso; clear - C; lia| exact VAX| exact BV| exact BF| exact PHI0].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
      replace (Z_to_bv 64 (pb + NBv * 4 + -4)) with (Z_to_bv 64 (pb + 4 * (NBv - 1))) by (f_equal; clear; lia).
      eapply (sa_SCANLOOP (Z.to_nat NBv) zs pb NBv _ _ _ _ _ _ NBv); try eassumption;
        [clear - NB10; lia| clear - NB10; lia| apply PB0; clear - K0 NB10; lia| apply OBL; clear - K0 NB10; lia| clear - K0 NB10; lia| unfold lval; rewrite firstn_all2 by (clear - LENZ; lia); reflexivity].
    all: match goal with |- ?g => idtac "SCAN-LEFT:" end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579668.400000=S1X2Ea3SXE2H5". (* [comment removed for export] *)
  #[using="IMG"] Lemma mk_JBd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "PdE,$7.Pm1,P,(3.&40.)(5.(3.&8.))P,(<.$48.VR,VLF,Vm,VLB,(=.&40.Vsp,)R2.)P,(16.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.Vlo,(=.&40.Vsp,))P,(17.(18.VR,)(19.$2.VLB,(1:.VLF,))Vlo,(1;.R4.)+10.)P,P,(10.$11.(12.R5.)$1<.)(17.(18.VR,)(19.$2.VLB,(1:.VLF,))Vlo,(1=.R6.)(1>.+4.(15.R6.)))P,(22.(14.(23.VX,+10.)(1;.R6.))(14.(23.(1;.R6.)+10.)VX,))P,P,(10.$11.(12.R7.)$13.)P,Pi,$8.P,(2?.(14.=R1.)(30.R1.(1>.+4.(15.R9.))))(10.$31.(32.$48.(33.(23.(1=.R:.)R2.)))$34.)(10.$31.(35.(1=.R9.)(1>.+4.(15.R9.)))$34.)P,(68.$48.(2=.VR,)(2>.$48.VR,VHIA,Vh,)R7.(1;.R8.)+10.)P,P,(10.$11.(12.R9.)$13.)(68.$48.(2=.VR,)(2>.$48.VR,VHIA,Vh,)R9.(1=.R:.)(1>.+4.(15.R:.)))P,(9.$48.VR,VHIA,Vh,VLB,VLF,R9.)P,(<.$48.VR,VLF,R:.VLB,(=.&40.Vsp,)R;.)(2?.(76.$48.VR,VHIA,VLB,VLF,Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R<.)(77.$48.VR,VHIA,VLF,Vsp,R<.Vh,VLB,R;.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01d0@D35881667587.163D35881667587.164D51794440367.163D51794440367.164K14554379081.163K14554379081.164K68206801384.163K68206801384.164L13098889560.151L14550820926.2  L14795424372.151L15032647579.2  L17305750384.4  L18868739288.151L19431261630.4  L19945316590.2  L20806881524.151L2138888664.151 L21541644120.151L26828156276.151L2759026548.151 L29834048600.151L3043381336.151 L32855866356.151L34936451766.1  L35609665496.151L35653441506.7  L38282648152.151L38866126964.151L40834179097.170L41670789057.6  L42479632545.4  L43059266230.157L43671330526.3  L44778233891.3  L44891662068.151L45674082520.151L47401587060.151L50903118708.150L52361663192.150L53410279412.151L53982396750.1  L54106875608.151L55013023064.151L58640675965.169L58641002120.172L59314955108.4  L59438513268.151L60098763854.3  L60330452198.159L62417105880.151L6482734895.4   L65451395828.151L68211501598.2  L8769959412.151 Q10333294960.179Q15643324129.159Q18365925601.160Q18378753154.160Q18696506101.179Q20454051255.182Q21800401414.179Q21879645826.160Q24330840805.179Q24389563138.160Q25160350961.179Q25513505925.162Q25513505925.163Q25664719138.179Q27584944865.160Q27907200258.160Q29505479905.160Q30415036802.160Q31226872993.179Q31271525473.160Q31396957457.179Q31577733036.179Q32655500769.160Q33918256002.160Q35016271767.179Q35715139857.179Q36425882626.160Q36426122721.179Q3830427394.160 Q39212284437.182Q39939554818.160Q41152393185.160Q4141071397.179 Q42656338381.182Q42658418930.179Q44648843873.160Q4533518817.160 Q49698585326.161Q49698585326.162Q50301287168.179Q51235796833.160Q52101170785.160Q53711815251.160Q53711815251.161Q53972118266.179Q54485784450.160Q59256763233.160Q59843137889.160Q60511257090.160Q60511567613.182Q61800308129.179Q6414620453.179 Q64253126389.179Q65201207496.182Q65925244770.162Q65925244770.163Q66522067074.160Q67528989526.163Q67528989526.164Q9538787269.179 Q9843367298.159 00000f02B03M05>06:07Y08U0:40:O0:P0:k0:l0;80;S0;a0;h0<C0<^0=90=T0=o0>J0>e0?@0?D0?_0@70@R0@m0AJ0A^0Aj0Bb0Bj0C20CM0Ch0DC0D^0E90ET0EX0F30FN0Fl0GJ0GW0H20H<0HW0I20I@0I[0I\0J70J80JQ0Jj0KH0Kb0L80L90LW0LX0M60MP0N;0OI0OJ0Oc0PA0PZ0Q80QS0Ql0R?0RR0Rk0SI0Sd0Se0TC0TD0Tb0U50US0Ul0Um0V@0VS0Vl0WE0Wi0XM0XN0Xg0Y@0YY0Z20ZM0Zk0[D0[]0\;0\N0\O0\i0\j0]=0]m0_@0_^0`N0aa0b40bRS1R3HIA1h2ra2sp1X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R2ra2sp1X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2ra2sp1X3xs02dA2dB3ABD3BBDFS2ra2sp1X3xs02dA2dB3ABD3BBDSS2sp2dA2lo1HS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dA2lo3OA4S2sp2loS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2spS2ra2sp1X3xs02dA2dB3ABD3BBDS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R2ra2sp1X3xs02dA2dB3ABD3BBDS1R2sp2lo4SLO25NEEDRS2sp2dB2lo1HS1R2ra2sp1X3xs02dA2dB2lo4SLO25NEEDR2X03SPR2A02B03ABD3BBDS1X2dA1DS1X2dB1DS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2spS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS1X2dA1D1E2dBS2ra2sp1X3xs02dA2dB3ABD3BBDS1R2lo3LOSS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dB2lo3OB4S2ra2sp1X3xs02dA2dB3ABD3BBDFS2ra2sp1X3xs02dA2dB3ABD3BBDFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS3xs02dA2dB2B03ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS2ra2sp3xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS3xs02dA2dB3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFS3xs02dA2dB3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB3ABD3BBD2HBS2sp3xs02dA2dB3ABD3BBD2HBS1R3xs02dA2dB5ALWF'3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS3xs02dA2dB3ABD3BBDFS1R3xs02dA2dB4IMG'3ABD3BBDFS3xs02dA2dB3ABD3BBDS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBD". (* [comment removed for export] *)
  #[using="IMG AMC AMS JC SLO2 NGN A47"] Lemma sa_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(:.$48.VR,VHIA,Vh,Vmo,)P,(<.$48.VR,VLF,Vm,VLB,(=.&40.Vsp,)VdA,)P,(<.$48.VR,VLF,Vm,VLB,(=.&40.Vsp,)VdB,)P,(>.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)P,(>.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,)P,(>.VdA,VdB,)P,(16.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,Vlo,(=.&40.Vsp,))P,(16.(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,Vlo,(=.&40.Vsp,))P,(17.(18.VR,)(19.$2.VLB,(1:.VLF,))Vlo,(1;.VdA,)+10.)P,P,(10.$11.(12.VdA,)$1<.)(17.(18.VR,)(19.$2.VLB,(1:.VLF,))Vlo,(1=.VdA,)(1>.+4.(15.VdA,)))P,(17.(18.VR,)(19.$2.VLB,(1:.VLF,))Vlo,(1;.VdB,)+10.)P,P,(10.$11.(12.VdB,)$1<.)(17.(18.VR,)(19.$2.VLB,(1:.VLF,))Vlo,(1=.VdB,)(1>.+4.(15.VdB,)))P,(24.$48.Vm,Vlo,(=.&40.Vsp,))P,(2;.$48.Vm,)P,(2<.$48.(2=.VR,)(2>.$48.VR,VHIA,Vh,)Vm,(49.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(2<.$48.(2=.VR,)(2>.$48.VR,VHIA,Vh,)Vm,VdA,)P,(2<.$48.(2=.VR,)(2>.$48.VR,VHIA,Vh,)Vm,VdB,)P,P,(10.$11.(12.VdA,)$13.)P,Pi,$8.P,(2?.(14.=R1.)(30.R1.(1>.+4.(15.VdA,))))(10.$31.(32.$48.(33.(23.(1=.VdA,)R2.)))$34.)(10.$31.(35.(1=.VdA,)(1>.+4.(15.VdA,)))$34.)P,P,(10.$11.(12.VdB,)$13.)P,Pi,$8.P,(2?.(14.=R1.)(30.R1.(1>.+4.(15.VdB,))))(10.$31.(32.$48.(33.(23.(1=.VdB,)R2.)))$34.)(10.$31.(35.(1=.VdB,)(1>.+4.(15.VdB,)))$34.)(40.$48.$54.(43.(44.(45.Vra,Vsp,Vgp,Vtp,R1?.R1>.R1=.Vs0,Vs1,(29.&40.VX,)(29.&40.(1;.VdA,))(29.&40.(1;.VdB,))R1<.R1;.R1:.R19.R18.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(29.&40.$78.)Vfc,(46.(3.&40.))Vm,(47.$48.))Vmo,))")
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
    carve_frame 112%nat ST.
    (* [comment removed for export] *)
    do 14 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jk :: _) =>
      change (rw_cells asegs m1 (bv_unsigned sp + -112) ([CB 8 jk] ++ SA_FRAME_A)) in FR end.
    apply rw_cells_app in FR. destruct FR as [SLOT FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp - 104) in FR by (clear; lia).
    lazymatch type of SLOT with rw_cells _ _ _ [CB 8 ?jk] => set (slot0 := jk) in SLOT end.
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp - 104)).
    { eapply stk_merge; [exact ST| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 8 slot0])) by (cbn; clear; lia).
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
    assert (PHI0 : 0 <= sub_abs_PHI0 dX dA dB) by (unfold sub_abs_PHI0, grow_PHI; unfold AVOL_CALL; clear - NRA'; lia).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OBs (md_addr dB + 10) 2.
    eapply sa_SCAN; [exact J0| solve [exact NGX | cbn [md_n]; exact NGX | cbn [md_n] in NGX |- *; exact NGX | cbn [md_n] in NGX |- *; lia | cbn [md_n]; apply Z.le_refl]| exact RA| exact RB| | | apply Z.le_refl| apply Z.le_refl| exact PHI0].
    - intros E. rewrite (IDA E). reflexivity.
    - intros E. rewrite (IDB E). reflexivity.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WS.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L23460287817.0L49264482736.500000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Lemma A_mpi_sub_abs_ng_spec_oz : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "PR,$79.PHIA,(7:.$48.R1.)P,(7;.(2=.R2.))P,(7<.$48.R3.R2.$7=.)P,(10.$8.(7>.R4.)$7?.)P,(10.$8.(80.R5.)$81.)P,(10.$8.(82.R6.)$83.)P,(14.=(27.R7.))P,Ph,(0.$48.R8.R7.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$48.R<.R;.R4.R3.R2.R1.)(84.$8.(85.(62.$8.$8.)$8.(86.$8.$8.)R4.))P,(2?.(14.(87.(18.R9.))(88.(18.R9.)))(14.(89.(18.R9.))(8:.(18.R9.))))P,Pa,$8.P,(10.$31.(32.$48.(33.R1.))$34.)P,(2?.(14.=R2.)(30.R2.(36.+2.+40.)))(2?.(14.(87.(18.R=.))R3.)(30.R3.(8:.(18.R=.))))(8;.$48.R;.R:.$78.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMC AMS NEEDR HND DIMG ROIMG. unfold mpi_sub_abs_ng_stmtA_oz.
  intros until d. intros HH HK MX MA MB SXA SXB SAB NST NGN OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA2 IB2 A47s BUD UW UWX UWA UWB BUDF -> -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 104 (SA_FRAME_A ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  assert (A47 : md_own dA <> LNull -> md_p dA + 4 * md_n dA + 8 <= 2^47).
  { intros NN. pose proof (opnd_viewA _ _ _ _ _ _ _ MA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dA) eqn:EO; [exfalso; apply NN; reflexivity| | exact (A47s eq_refl)].
    ddestruct OW as (_ & EIN & _). exact (blk_top47 asegs R HIA h LB LF m _ _ HH EIN). }
  eapply sa_main; try eassumption.
  all: try exact (uw_obj_nonneg _ _ _ _ UWX).
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L9571355814.500000@S1R2sp2lo3SLO2NE". (* [comment removed for export] *)
Theorem A_mpi_sub_abs_ng_sz_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_sub_abs_ng_sz ()) "PR,$79.PHIA,(7:.$48.R1.)P,(7;.(2=.R2.))P,(7<.$48.R3.R2.$7=.)P,(10.$8.(7>.R4.)$7?.)P,(10.$8.(80.R5.)$81.)P,(10.$8.(82.R6.)$83.)P,(14.=(27.R7.))P,Ph,(0.$48.R8.R7.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$48.R<.R;.R4.R3.R2.R1.)(84.$8.(85.(62.$8.$8.)$8.(86.$8.$8.)R4.))P,(2?.(14.(87.(18.R9.))(88.(18.R9.)))(14.(89.(18.R9.))(8:.(18.R9.))))P,Pa,$8.P,(10.$31.(32.$48.(33.R1.))$34.)P,(2?.(14.=R2.)(30.R2.(36.+2.+40.)))(2?.(14.(87.(18.R=.))R3.)(30.R3.(8:.(18.R=.))))(8<.$48.R;.R:.$78.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMC AMS NEEDR HND DIMG ROIMG. unfold mpi_sub_abs_ng_stmtA_sz, mpi_binop_ng_stmtA_sz.
  intros until d. intros HH HK MX MA MB SXA SXB SAB NST PRE OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IMA IMB BUD UW UWX UWA UWB BUDF E0 E1 E2.
  pose proof (arl_need_ecp_rt R) as NE.
  eapply (A_mpi_sub_abs_ng_spec_oz R HIA IMG ZF CAL AMC AMS NEEDR HND DIMG ROIMG) with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
    first [ eassumption | (apply opnd_atA_mpd; assumption) | (intros O _; exact (IMA O)) | (intros O _; exact (IMB O))
          | (intros O; exact (A_mpi_add_sub.mpd_at_static47 _ _ _ MA O)) | (clear - SLO NE; lia)
          | match goal with |- ?g => idtac "SZ-LEFT:" g end ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
