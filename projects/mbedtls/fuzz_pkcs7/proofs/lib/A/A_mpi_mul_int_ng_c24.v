(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_copy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2
     A_mpi_zeroize_and_free A_mpi_copy A_mpi_core_mla A_mpi_add_abs_W A_mpi_mul_int.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_mpi_stmtA_c24 A_mpi_journey_c24 A_mpi_copy_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_mpi_mul_int_ng.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_mul_int_ng_c24 () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.nth_error"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibA.ARt.htop"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.A.A_mpi_mul_int_ng.mul_int_PHI0"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.A.A_mpi_mul_int_ng.mul_int_FR0"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.ACnt24.cnt24"; "OSSVerify.KrLib.A.A_mpi_mul_int.C24_MUL_INT"; "OSSVerify.KrLib.LibA.ACnt24.C24MAX"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.A.A_mpi_mul_int.mul_int_Rz"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "WM.MI_FRAME_A"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.max"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "WM.MI_POST_A"; "OSSVerify.KrLib.A.A_mpi_journey2.rideA"; "WM.miV1"; "WM.miF1"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "WM.copy_self_postA"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_COPY"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.A.A_mpi_opnd.opnd_atA"; "OSSVerify.KrLib.A.A_mpi_journey.JBA"; "OSSVerify.KrLib.A.A_mpi_journey.BJA"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_MUL_INT"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_mpi_mul_int.A_ASAN_MEMSET_MI"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "mpi_mul_int_ng_stmtA"].



Definition mpi_mul_int_ng_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.Pb,$8.Plo,$8.Pd,$8.PU,$8.P,(9.O4.O3.O2.R2<.R2;.R2:.R8.)P,(:.O4.O3.O2.R2=.R8.)P,(;.O4.R:.R2=.R8.)P,(;.O4.R;.R2>.R8.)P,(<.R:.R9.)P,(=.(>.$?.(10.R;.)$11.))P,(>.$8.(12.R;.)(12.R<.))P,(13.+1.(14.R=.))P,(13.=R9.)P,(13.(15.R:.+1.)(14.R?.))P,Pi,$8.Pw,(3.&40.)P,(13.R=.R2.)P,(>.(5.(3.&40.))(16.(3.&40.)(17.R12.)(18.R3.))(19.(3.&40.)R2.))(>.$8.(1:.(1;.&40.R3.)(1<.+2.+20.))=)P,(1=.R11.R10.R>.(1;.&40.R33.))P,(1>.(1?.O3.)(20.$2.R37.(21.R36.))R?.(12.R11.)+10.)P,P,(>.$?.(10.R12.)$22.)(1>.(1?.O3.)(20.$2.R39.(21.R38.))R11.(23.R13.)(24.+4.(14.R13.)))P,(25.O3.R39.R38.(1;.&40.R36.)(26.O4.O3.O2.R3:.)R14.)P,(27.(13.=R13.)(28.R13.(1<.+2.+20.)))P,P,(=.(>.$?.(10.R16.)$29.))(2:.(13.(15.(23.R17.)(24.+4.(14.R17.)))R14.)(13.(1;.&40.R39.)(23.R17.)))P,(2;.O4.R19.R14.(1;.&40.R39.))P,(13.(2<.O3.)R15.)P,(13.R16.(2=.(2=.(1;.&40.R3;.)+>0.)(2>.O3.)))P,(13.(1;.&40.R3<.)(26.O4.O3.O2.R40.))P,(>.$8.(1:.(1;.&40.R3=.)+10.)=)P,(>.(3.&40.)R3<.(2?.&40.(30.O3.)))P,(31.O4.R1?.)P,(>.$8.(1:.(1;.&40.R41.)+2.)=)P,(32.O4.(33.O3.)(34.O4.O3.O2.R45.)R21.R1?.)P,(32.O4.(33.O3.)(34.O4.O3.O2.R46.)R22.R1?.)P,P,(=.(>.$8.(12.R20.)(12.R21.)))P,(>.$?.(10.R21.)$11.)(>.$35.(36.(23.R22.)(24.+4.(14.R22.)))$37.)P,P,(>.$?.(10.R21.)$11.)P,Pi,$8.P,(27.(13.=R1.)(28.R1.(24.+4.(14.R23.))))(>.$35.(38.O4.(39.(15.(23.R24.)R2.)))$37.)(>.$35.(36.(23.R23.)(24.+4.(14.R23.)))$37.)P,(13.(15.(3:.O4.O3.O2.R49.)(3;.R23.R22.))$3<.)P,(3=.O4.R26.(2<.O3.)(3>.O4.O3.O2.R4:.)(1;.&40.R40.)(1;.&40.R46.)R20.)P,(3?.O3.(12.R25.)+10.R21.)P,(3?.O3.(12.R25.)+10.R22.)P,(13.(15.(40.O4.O3.O2.R4=.)(41.R23.))$42.)P,(13.(15.(43.R4=.)$44.)$45.)P,(>.$8.(1:.(1;.&40.R41.)(1<.+2.+20.))R27.)P,(46.(>.$8.(1;.&40.R42.)=)(>.$8.R28.=))P,(>.(3.&40.)R45.(2?.&40.(12.R2;.)))P,(>.(3.&40.)R45.(2?.&40.(12.R2;.)))(47.O4.(48.O4.O3.O2.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R53.R52.R51.R2=.(49.R2;.R52.R2=.R2<.)(3;.R2=.R2<.)(41.R29.)R2:.R2?.R2>.)(4:.(4;.(4<.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(2?.&40.O1.)R30.(4=.(3.&40.))R2?.(4>.O4.))R2>.))")
(* [comment removed for export] *).

Section WM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis COPY : mpi_copy_stmtA_c asegs R HIA A_MPI_COPY.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_MI.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_MI.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_MI.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Hypothesis C24H : cnt24 LB + C24_MUL_INT <= C24MAX.     (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA : mpd) (lo d b : Z) (wb : word).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition MI_FRAME_A := aa_frame96 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BB : 0 <= b < 2^32.
  Hypothesis WB1 : bv_unsigned wb mod 2^32 = b.
  Hypothesis WB0 : bv_unsigned wb = 0 <-> b = 0.
  Hypothesis NRA : 0 <= md_n dA <= 10000.
  (* [comment removed for export] *)
  Variable U : Z.
  Hypothesis NGA : md_addr dA = X.
  Hypothesis NG1 : 1 <= nX.
  Hypothesis NGU0 : 0 <= U.
  Hypothesis NGU : U + 1 <= nX.
  Hypothesis NGZ : forall i w, U <= i -> nth_error (md_limbs dA) (Z.to_nat i) = Some w -> bv_unsigned w mod 2^32 = 0.

  Definition MI_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "(48.$4?.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(49.Vb,VLB,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)(3;.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)(41.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -96)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A []).

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAm; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L19687428440.151L25465666776.151L28125529944.151L29025845208.151L29428324939.5  L29762660275.151L31686769240.151L35663928186.7  L36180290948.1  L52253708504.151L60098763854.3  L60511538335.151L60692334296.151L61601561944.151L62505661912.151L64270350808.151L65178513496.151L947156799.150  Q15643598972.151Q18366170748.151Q18378508831.151Q21879891999.151Q24389844383.151Q27585188988.151Q27906956191.151Q30415318815.151Q31271277308.151Q32655747964.151Q33918012703.151Q36425601695.151Q3830178207.151 Q39939305631.151Q41152143740.151Q44648563964.151Q4533800828.151 Q51235551740.151Q52101417212.151Q59257011708.151Q59842863100.151Q60511538335.151Q66521824799.151Q9843086111.151 00000@00P00`01001B01R01b02702;02K02U03;03K03[03k04;04K04[04k05;05Z06906X06h07G07f08608F08e09D09c0:B0:R0:b0;20;B0;R0;b0<20<Q0=00=OS2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S1R2lo3LOS3ALO3ACPS2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S1R3HIA1h2sp2lo3TOP1HS2spS2ra2sp1b2wb3WB0S1R2lo3LOSS1R2ra2sp2lo1b2wb2BB3WB05NEEDR3SLO3SPRS2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLO". (* [comment removed for export] *)
  #[using="IMG wb JC BB WB0"] Lemma mi_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pv,$8.Pf,$8.Phc,(0.$4?.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(51.$4?.VR,VHIA,Vh,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$52.(53.$2.)R21.R20.R1?.R1>.R1=.R1<.)P,(2:.(27.(>.$8.R1<.=)(27.P,(>.$8.Vb,=)(>.$8.(54.R1>.)=)(13.(14.R1=.)(55.VnX,(15.(14.VdA,)+1.)))))(>.$8.R1<.$56.))P,(13.R23.(3;.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,))P,(13.R23.(41.Vd,))(57.$4?.(58.$4?.VR,VHIA,R23.Vmo,)$59.(4;.(4<.R1>.(2?.&40.(15.(1;.&40.Vsp,)-60.))Vgp,Vtp,R1=.R1<.R1;.R1:.R19.(2?.&40.R1?.)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.Vs11,R8.R7.R6.R5.)VF,(2?.&40.+9<:84.)Vfc,(4=.(3.&40.))R21.(4>.$4?.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold MI_FRAME_A, aa_frame96 in FR1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 12 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold MI_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis BUD : havol asegs R HIA h + mul_int_PHI0 dX dA <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + mul_int_FR0 d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 224 - arl_need_rt R.
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Local Notation SH10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Local Notation SHA := (Z_to_bv 64 (Z.shiftr (md_addr dA) 3 + al_sb AL)).
  Local Notation XJ1 An cnt := (XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [(An, 4 * cnt)]).
  Local Notation FB0 := (FBA asegs R LB LF dX lo).
  Local Notation XD0 := (XDA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A).
  Local Notation RIDE := (rideA R HIA LB LF m dX sp lo dA).
  (* [comment removed for export] *)
  Definition miV1 : Z := 0.
  Definition miF1 : Z := 0.
  Local Ltac xa_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  Definition KC_stmt (n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pv,$8.Pf,$8.Phc,(0.$4?.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(51.$4?.VR,VHIA,Vh,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$52.(53.$2.)R19.R18.R17.R16.R15.R14.)P,(5:.VR,VHIA,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdA,R18.R17.R16.R15.)P,(>.$?.(10.R16.)$22.)P,(13.(15.O1.+1.)(14.R17.))P,(13.(14.R18.)(55.VnX,(15.O1.+1.)))P,(13.R1>.$5;.)P,(13.R1>.$5<.)(57.$4?.(58.$4?.VR,VHIA,R1>.Vmo,)$59.(4;.(4<.R1:.(2?.&40.(15.(1;.&40.Vsp,)-60.))Vgp,Vtp,R19.R18.R17.(2?.&40.VX,)(2?.&40.O1.)R16.(2?.&40.(12.VdA,))R15.R14.R13.R12.R11.R10.(2?.&40.(15.VX,+:.))R?.R>.(2?.&40.(5=.(33.VR,)))(2?.&40.(15.(5>.(12.VdA,)+3.)(5=.(33.VR,))))(2?.&40.(15.(5>.(15.VX,+:.)+3.)(5=.(33.VR,))))Vwb,R=.R<.Vs11,R;.R:.R9.R8.)VF,(2?.&40.+9<938.)Vfc,(4=.(3.&40.))R1<.(4>.$4?.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02b0@C24112444547.216D19095312002.214D22752211978.220D30202740417.214D30213615715.220D38874475859.220D42633159082.214D42643779336.220D601287770.214  D62012212072.220K11420089551.216K25384422162.217K28284592895.215K41585169438.215K47544724259.219K47544724259.221K52581815936.217L11092957035.11 L11093884473.5  L11093884473.6  L11416546478.3  L1286294210.5   L14245130797.3  L14249998533.4  L15167829154.4  L15169948178.7  L15180368418.3  L17803185913.5  L17809411522.9  L17813258712.7  L17813606089.8  L17815712639.11 L17815810169.6  L21273698895.4  L21286247631.5  L21286346697.10 L21288444543.7  L23100341967.197L23560010593.8  L23561906969.8  L23643762344.4  L25399627235.15 L25721347477.8  L25735831525.8  L25881510713.2  L2625810293.3   L28270437390.4  L29534616704.4  L2975768925.2   L29763661393.2  L3481485179.12  L3482279739.6   L3482279739.7   L3482279739.8   L35065298922.8  L35069606260.5  L35663928186.7  L36145034931.8  L36147066499.10 L36147132693.8  L36147476882.8  L36149152565.14 L36149250099.8  L36180290948.1  L38235734261.1  L38330469153.0  L39363785272.11 L39363785272.9  L39364434794.16 L39569505368.7  L41112052343.4  L41114152401.6  L41114214983.6  L41114660182.5  L41116278007.4  L41128898453.2  L41580512891.2  L42633816569.1  L43631404864.4  L43878034250.5  L46160487540.197L4735037479.2   L4735039273.4   L47532522306.4  L47534962651.4  L47784804765.4  L47795356077.6  L47797436189.4  L51284464315.197L52592168972.2  L5259801613.194 L54434634207.8  L54473544495.13 L58609956177.2  L58720988025.3  L59310763475.5  L60098763854.3  L60283674290.9  L60445729592.5  L60447858056.4  L61263298563.1  L61429820693.1  L62228711352.6  L65446478210.2  L66151427842.16 L66151427842.17 L9285596192.5   L9287758864.7   L9289747104.5   L9289845158.11  O22331808284.218O24112444547.216O24729331311.219O24729331311.221O27573497883.215O31435371494.217O35105909750.217O54539614568.215O54736301905.218P11420089551.216P14260335836.218P41585169438.215P47544724259.219P47544724259.221P52581815936.217P65433701013.218Q10045260807.203Q12370813529.202Q17207350632.203Q1738401673.225 Q18347242623.222Q21831343660.204Q22752211978.223Q22752211978.224Q22752211978.225Q26207421841.203Q26207721832.204Q26207967338.201Q30213615715.223Q30213615715.224Q30213615715.225Q31222125165.224Q31222125165.225Q31654082872.203Q37625261960.201Q38874475859.223Q38874475859.224Q38874475859.225Q39212284437.204Q40036871097.202Q40278613695.202Q42252534531.204Q42643779336.223Q42643779336.224Q42643779336.225Q43925228937.204Q45875552310.223Q45875552310.224Q45875552310.225Q47588311916.221Q47588311916.222Q5485126037.201 Q5485600919.203 Q60511567613.204Q60697995187.204Q61263535092.203Q61264001456.204Q61465870571.202Q66375044744.204Q67329605699.203Q8222473558.204 Q8880503606.201 Q9285269895.223 Q9285269895.224 Q9285269895.225 Q9538787269.201 Q9827600259.221 Q9827600259.222 00000101M01N02C02n02o03b04K05f06Q06R07S08I08J08K08L08M08N08O08P08Q08b08c08o09009109<09=09>09?09@09A09B09C09D09E09F09o0:M0:N0:[0:\0;;0;<0;=0;F0;G0;U0;\0;c0;d0;e0;f0;g0<50<E0<Z0<[0<\0<]0<^0<_0<`0<d0<h0<i0<j0<k0<l0=F0=G0=H0=I0=U0=V0=W0=X0=]0=j0>10>d0>k0?80?90?:0?;0?<0?=0?f0?g0@Z0A90A=0AD0AN0A`0Aj0BI0B[0B\0B`0Bd0C80C90CU0CV0CW0CX0CY0CZ0C[0C\0C]0C^0C_0C`0Ca0Cb0Cc0Cd0E@0EA0EB0EC0ED0EE0E_0FR0Fn0Fo0G00G10G20G30G40GP0Gl0HH0Hh0IH0Ih0Ii0Ij0JF0Jb0Jc0Jd0Je0KA0Kd0LG0MH0Mf0ND0Nb0O>0O?0O@0OA0OB0OC0O_0P;0PU0Q70QQ0Qk0Ql0RF0R`0S_0T;0T<0T=0T>0TX0TY0TZFS1R2ra2sp1X2nX3xs02dA2lo1b2wb2BB3WB04SLO23pXc2xs5NEEDR3LOS2X03SPR2P02pe2ys3EP03E0'4xs6l4LEN6FS2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2pe2ys4xs6l4LEN6S2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2pe2ysFS2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ys4xs6l4LEN6S2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysS1R3HIA1h2ra2sp1X2nX3xs02dA1b2wb2BB3WB02hc3pXc2xs3TOP2X03SPR3HT12P02pe2ys3EP03E0'4xs6l4LEN6S1R2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysFS1R2sp2nX3xs02dA2lo1b2wb2BB3WB04SLO21N3pXc2xs5NEEDR3LOS3ALO2PC2ysS1R2sp2nX3xs02dA2lo1b2wb2BB3WB01N3pXc2xs3LOS3ALO2PC2ysFFFFFFFFS1n1N2xs3HNX4LEN1FS2dA1N3pXc1KFFS1N2xs4LEN1FFFFFFFFFFS2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysS1R2sp2lo4SLO25NEEDR2pe2ys3ESKFS1X1N3pXc3XPcFS1R2sp2lo4SLO21N3pXc5NEEDR4XLScFFS1n1N3HNXFS2dA1n3HN13HNAS1N3pXcS1N3NR1FFFFS1R1N3pXc2PC1HS1R1N3pXc2PC3ACVS1R3HIA1h2sp2lo3TOP1HFFFFFFS2spS2loSFFFS1R2sp1X2lo4SLO25NEEDR3DSXFFFS2sp3SPA3SPRFFFS3pXcS1n1N3pXc3HNXS2sp2loS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03X162pe2ysS2dA2HIS1R2dA3ACV2HCFFFFFS2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysFS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03X162pe2ysS1R2sp2lo4SLO21N3pXc5NEEDR4XLScS2spS1N3NR1S2dA1n3HNAS2dA1n3HN13HNA3EZ0S1R2lo3LOSS1R2sp2lo4SLO21N3pXc5NEEDR1a2NOS2dA3NRA1n3HN13HNAFS2dAS2spS1R2sp2lo4SLO25NEEDRFS3pXc2r04XPAL1q1r1H2H02q02H4FFFFFFFFFFFFFFFS1R2sp1X2nX3xs02dA2lo1b2wb2BB3WB03NGA4SLO21N3pXc2xs3BNZ5NEEDR3LOS3ALO2PC3XPc2ys3x143x154POSTFFFFFS2nX3xs02dA1b2wb3WB02xs2ysS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03XAL2pe2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFFFFFFS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysS2nX3xs02dA1b2wb3WB01N3pXc2xs2ysS2nX3xs02dA1b2wb3WB01N3pXc2xs2ysS2nX3xs02dA1b2wb3WB01N3pXc2xs2ysFFS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFFFS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb2BB3WB03NGA2xs2ysS1X2nX3xs02dA1b2wb2BB3WB03NGA2xs2ysS1R2sp2nX3xs02dA2lo1b2wb2BB3WB04SLO22xs5NEEDR3LOS4SP643ALO3ACV2ysS2nX3xs02dA1b2wb3WB03pXc2xs2ysS2nX3xs02dA1b2wb3WB03pXc2xs2ysS2nX3xs02dA1b2wb3WB03pXc2xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFFFFFS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysS2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb2BB3WB02xs2X02ysS2nX3xs02dA1b2wb3WB02xs2ysS2nX3xs02dA1b2wb3WB02xs2ysFS2nX3xs02dA1b2wb3WB02xs2ysS2nX3xs02dA1b2wb3WB02xs2ysS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03SPR2P02pe2ys3E0'4EAL'S1X2nX3xs02dA1b2wb3WB02xs2ysFFFS2nX3xs02dA1b2wb3WB02xs2ysFF". (* [comment removed for export] *)
  #[using="IMG JC BB WB0 NRA NGA SLO2"] Lemma mi_MLA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pn,$8.Pv,$8.Pf,$8.Phc,(0.$4?.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(51.$4?.VR,VHIA,Vh,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$52.(53.$2.)R19.R18.R17.R16.R15.R14.)P,(5:.VR,VHIA,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdA,R18.R17.R16.R15.)P,(>.$?.(10.R16.)$22.)P,(13.+1.R1=.)P,(13.(15.R1>.+1.)(14.R18.))P,(13.R1?.(14.VdA,))P,(13.(14.R1:.)(55.VnX,(15.(14.VdA,)+1.)))P,(=.(>.$8.Vb,=))P,(13.R21.(3;.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,))P,(13.R21.(41.Vd,))(57.$4?.(58.$4?.VR,VHIA,R21.Vmo,)$59.(4;.(4<.R1=.(2?.&40.(15.(1;.&40.Vsp,)-60.))Vgp,Vtp,R1<.R1;.R1:.(2?.&40.VX,)(2?.&40.R24.)R19.R18.R17.R16.R15.R14.R13.R12.(2?.&40.(15.VX,+:.))(2?.&40.(12.VdA,))R11.(2?.&40.(5=.(33.VR,)))(2?.&40.(15.(5>.(12.VdA,)+3.)(5=.(33.VR,))))(2?.&40.(15.(5>.(15.VX,+:.)+3.)(5=.(33.VR,))))Vwb,R10.R?.Vs11,R>.R=.R<.R;.)VF,(2?.&40.+9<948.)Vfc,(4=.(3.&40.))R1?.(4>.$4?.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 RA EO HN1 HNX HNA NMAX BNZ BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc. unfold mpi_cells in CX1.
    pose proof (alloc_ceiling_val R) as ACV.
    (* [comment removed for export] *)
    assert (EF : exists pe ys se ne pde, bytes_at asegs mc pe (u32s ys) /\ n <= Z.of_nat (length ys)
                 /\ ((pe = pXc /\ ys = xs) \/ pe + 4 * Z.of_nat (length ys) <= pXc \/ pXc + 4 * Z.of_nat (length xs) <= pe)
                 /\ pe mod 4 = 0 /\ 0 < pe /\ (pe + 4 * Z.of_nat (length ys) <= lo \/ bv_unsigned sp <= pe) /\ pe + 4 * Z.of_nat (length ys) < 2^64
                 /\ rw_cells asegs mc (md_addr dA) [C8 (Z_to_bv 64 pe); C2 (Z_to_bv 64 se); C2 (Z_to_bv 64 ne); C4 pde]
                 /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dA) 16 /\ aobj asegs AL (hcs asegs R HIA hc) mc pe (4 * n)
                 /\ 0 < md_addr dA /\ md_addr dA + 16 <= 2^64 /\ md_addr dA mod 8 = 0).
    { destruct RA as [EAX|[DBJ B]].
      - dexists pXc, xs, sg, N, padX. rewrite EAX.
        split; [apply u32arr_ro; exact XARR|]. split; [clear - LEN1 HNX; lia|]. split; [left; split; reflexivity|].
        split; [clear - XPAL; Z.div_mod_to_equations; lia|]. split; [exact P0|]. split; [rewrite LEN1; exact XLSc|].
        split; [rewrite LEN1; clear - PC ACV; lia|]. split; [exact CX1|]. split; [exact OX1|].
        split; [eapply aobj_sub; [exact OP| clear; lia| clear - HNX; lia]|]. split; [exact X0|]. split; [exact X16| exact XAL].
      - pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
        assert (EN : md_own dA <> LNull) by (intros C; destruct (OWNE0 C) as [_ EZ0]; clear - HN1 HNA EZ0; lia).
        ddestruct (OWNE1 EN) as (_ & EP0 & EPAL & EBY & ESK & BHP & BST).
        pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B)) as [(CE & _) _]. unfold mpi_cells in CE.
        dexists (md_p dA), (md_limbs dA), (md_sg dA), (md_n dA), (md_pad dA).
        split; [exact EBY|]. split; [rewrite LENE; exact HNA|].
        split; [right; rewrite LENE, LEN1; pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B eq_refl EN) as K; cbn [md_p md_n] in K; clear - K; lia|].
        split; [exact EPAL|]. split; [exact EP0|]. split; [rewrite LENE; exact ESK|].
        split.
        { rewrite LENE. destruct (md_own dA) eqn:EOA; [exfalso; exact (EN eq_refl)| |].
          - destruct (BHP eq_refl) as [_ BINc]. destruct (hm_apart asegs R HIA hc LBc LF mc HH1) as [HBR _]. rewrite Forall_forall in HBR.
            destruct (HBR _ ltac:(apply in_app_iff; left; exact BINc)) as (_ & _ & HC & _). cbn [fst snd] in HC. clear - HC ACV. lia.
          - destruct (BST eq_refl) as [BRO|[_ BH]]; [| exact BH].
            destruct (A_mpi_copy.static_limbs_low (Z_to_bv 64 0) mc _ _ _ EBY LENE ltac:(clear - HN1 HNA; lia) BRO) as [_ HI]. clear - HI. lia. }
        split; [exact CE|]. split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)|].
        split; [eapply aobj_sub; [exact (bj_aobjL _ _ _ _ _ _ _ _ _ _ B EN)| clear; lia| clear - HNA; lia]|]. split; [exact E0|]. split; [exact E16| exact EAL]. }
    ddestruct EF as (pe & ys & se & ne & pde & EBY & LENY & SEPZ & EPAL & EP0 & ESK & E64 & CE & OE & OEL & E0' & E16' & EAL').
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (bv_unsigned sp + -96 - MPI_CORE_MLA_STACK_A, bv_unsigned sp + -96)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep. zstep. zstep. zstep.
    pose proof (A_mpi_core_mla_spec AL IMG) as SPC. unfold mpi_core_mla_stmtA, A_MPI_CORE_MLA in SPC.
    acallxA_sp (bv_unsigned sp + -96)
      (eapply SPC with (D := pXc) (dl := N) (S := pe) (sl := n) (lo := lo) (ds := xs) (ss := ys);
       rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
       try eassumption; try reflexivity;
       first [ clear - NR1 N1; lia
             | clear - HN1 HNA NRA; lia
             | clear - LEN1; lia
             | exact SEPZ
             | clear - XPAL; Z.div_mod_to_equations; lia
             | right; exact EP0
             | rewrite LEN1; clear - PC ACP' P0 N1; pose proof (alloc_ceiling_val R); lia
             | exact E64
             | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
             | replace (Z.min N n) with n by (clear - HNX; lia); exact OEL
             | unfold MPI_CORE_MLA_STACK_A; clear - SLO2 NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
             | unfold MPI_CORE_MLA_STACK_A; rewrite LEN1; clear - XLSc SLO2 NEEDR; lia
             | unfold MPI_CORE_MLA_STACK_A; clear - ESK SLO2 NEEDR; lia
             | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MLA-PRE-LEFT:" g end ] ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MLA-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned sp + -96) |- _ => rename H into ST6 end.
    match goal with H : u32arr asegs m6 pXc ?l, H2 : length ?l = length xs |- _ => rename H into XARR6; rename H2 into LEN6; rename l into xs6l end.
    (* [comment removed for export] *)
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * N); (bv_unsigned sp + -96 - MPI_CORE_MLA_STACK_A, bv_unsigned sp + -96)] mc m6) in HH6;
      [| exact MU| exact WM| unfold MPI_CORE_MLA_STACK_A; solve_w_writable].
    pose proof ST6 as ST6'.
    assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * N); (bv_unsigned sp + -96 - MPI_CORE_MLA_STACK_A, bv_unsigned sp + -96)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
    { intros a NO. cbn [outside] in NO. unfold MPI_CORE_MLA_STACK_A in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 96) by (clear - NO SLO2 NEEDR; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6
                  ltac:(cbn; unfold MPI_CORE_MLA_STACK_A; split; [clear - XLSc SLO2 NEEDR; lia| split; [clear; lia| exact I]])
                  ltac:(cbn; unfold MPI_CORE_MLA_STACK_A; split; [clear - XPc; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]) XARR6
                  ltac:(exact LEN6)) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply mi_ret; [exact J6| left; split; [reflexivity| split; [intros B0; exfalso; exact (BNZ B0)| cbn [md_n]; exact NMAX]]| exact BV| exact BF].
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MLA-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition copy_self_postA (xra xsp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (lo0 : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Lms',$5?.(60.(3.&40.)Lt0,(3.&40.)(60.(3.&40.)Lt1,(3.&40.)(60.(3.&40.)Lt2,(3.&40.)(60.(3.&40.)La1,(3.&40.)(60.(3.&40.)La2,(3.&40.)(60.(3.&40.)La3,(3.&40.)(60.(3.&40.)La4,(3.&40.)(60.(3.&40.)La5,(3.&40.)(60.(3.&40.)La6,(3.&40.)(60.(3.&40.)La7,(3.&40.)(60.(3.&40.)Lt3,(3.&40.)(60.(3.&40.)Lt4,(3.&40.)(60.(3.&40.)Lt5,(3.&40.)(60.(3.&40.)Lt6,(3.&40.)(60.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(27.(>.$5?.R10.(4;.(4<.O10.O?.Vgp,Vtp,R?.R>.R=.O>.O=.(2?.&40.=)R<.R;.R:.R9.R8.R7.R6.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.R5.R4.R3.R2.)VF,(61.O10.)Vfc,(4=.(3.&40.))R1.(4>.$4?.)))(27.(62.(63.(64.$8.$8.)(65.$8.$8.(2=.(1;.&40.O?.)+50.)(1;.&40.O?.))(53.(64.$8.$8.)))O1.R1.)(27.(66.$4?.O1.R1.)(27.(31.$4?.R1.)(2;.$4?.R1.O2.(1;.&40.O?.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01F0@L10013191668.111L13679629912.111L13679629912.112L16024124020.111L20817808472.111L20817808472.112L22051162356.111L24693561020.110L29502821080.111L29502821080.112L37623267032.111L39788318758.105L3991920500.111 L41391506051.111L42606771444.110L44235170136.111L44235170136.112L45988853080.110L45988853080.112L46254298584.111L46254298584.112L48636430708.111L53392477144.111L53392477144.112L54646761460.111L60674471028.111L62842592998.107L65656017752.111L65656017752.112L66683159284.111L7522693171.111 L7522693171.112 L8090362072.111 L8090362072.112 Q11040878936.111Q11047091911.110Q11801279589.113Q11801279589.114Q17057885511.110Q17059930840.111Q19565771207.110Q19567916632.111Q21542576304.111Q21548953391.110Q23077295192.111Q23083408327.110Q23580411907.112Q23580411907.113Q25586850776.111Q25593320519.110Q29094213191.110Q29096229336.111Q31988680623.110Q31990990896.111Q32464959152.111Q32471038255.110Q35115543384.111Q35122046151.110Q37623267032.111Q37629604167.110Q40016974384.111Q40019025327.110Q40550671471.112Q40550671471.113Q41141296344.111Q41143309127.110Q45469487279.110Q45471637296.111Q49698585326.111Q49698585326.112Q52876753840.111Q52878668847.110Q5300226131.110 Q5300226131.111 Q54126458602.111Q64997424432.111Q64999568047.110Q66001486466.113Q66245698095.110Q66252074416.111Q6697503024.111 Q6699665458.109 Q67723680344.111Q67725581146.109Q7198696624.111 Q7204776751.110 00000E00Z00o01D01Y01n02C02X02m03B03c04D04Y04n05C05X05m06B06W06l07A07V07k08@08U08j09?09T09i0:>0:S0:h0;=0;R0;l0<F0<g0=h0>B0>\0?60?P0?b0@40@N0@h0AU0B^0C80CR0Cl0DF0DX0Dj0E<0EN0Eh0FB0F\0G60GH0GZ0H?0ID0I^0J80JJ0J\0K:0KX0Kj0L<0LP0Ld0M80MJ0M\0NI0N[0Nm0O?0OQ0Ok0PE0PW0PiS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb2BB3WB03xra3xsp3lo04SLO0S2ra1b2wb2BB3WB03xra3xsp3lo04SLO0S2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xra3xsp2HB5Ha_st5Hl_stS1b2wb3WB03xsp3xs12HB5Ha_st5Hl_st3xs23xs33xs43xs53xs63xs73xs83xs9S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xra3xsp3lo04SLO02HB5Ha_st5Hl_stS1b2wb2BB3WB03xsp3xs13lo04SLO02HB5Ha_st5Hl_st3xs23xs33xs43xs53xs63xs73xs8S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xra3xsp3lo02HB5Ha_st5Hl_stS1b2wb3WB03xsp3xs13lo02HB5Ha_st5Hl_st3xs23xs33xs43xs53xs63xs73xs83xs9S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3SPR2HB5Ha_stS1b2wb2BB3WB03xsp3SPR2HB5Ha_stS1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp2HBS1b2wb2BB3WB03xsp2HBS1b2wb2BB3WB03xsp2HBS1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3xs93lo04SLO02HB5Ha_st5Hl_stS1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0". (* [comment removed for export] *)
  #[using="HIA IMG ra b wb BB WB0"] Lemma A_copy_self : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "PCS,P,$8.SpPxra,(3.&40.)Pxsp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pxs0,(3.&40.)Pxs1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxs11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Pm0,P,(3.&40.)(5.(3.&8.))Plo0,$8.P,(31.$4?.R2.)P,(2;.$4?.R3.R2.(1;.&40.R1?.))P,(13.R3.(2=.(1;.&40.R20.)+50.))P,(13.=R4.)P,(>.$8.(1:.(1;.&40.R22.)+10.)=)P,(67.(33.VR,)R25.)P,(68.R26.R7.(2=.(1;.&40.R24.)R7.))P,(>.$8.(1:.(1;.&40.R26.)+2.)=)P,(>.(3.&40.)R20.R1?.)(69.$4?.(33.VR,)R29.(6:.R28.R27.R23.R22.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R:.R;.)(4;.(4<.R28.R27.Vgp,Vtp,R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)VF,(2?.&40.$6;.)Vfc,(4=.(3.&40.))R;.(4>.$4?.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo0. intros MI0 ST0 SLO0 LO00 SPA0 CSOK SCS RA0 ->. unfold A_MPI_COPY.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 xsp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
    (* [comment removed for export] *)
    zstep. carve_frame 80%nat ST0.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(bv_unsigned xsp - 80, bv_unsigned xsp)] mx) as MU; pose proof (wmono_refl asegs mx) as WM end.
    do 10 zstep.
    (* [comment removed for export] *)
    zstep. try (if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]).
    (* [comment removed for export] *)
    zstep. do 10 zstep. zstep.
    release_frame FR ST0 (bv_unsigned xsp).
    zstep.
    apply evtA_done. unfold copy_self_postA. deexists 14. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis MA0 : mpd_at asegs m LB dA.
  Hypothesis IA1 : md_addr dA <> X -> md_own dA = LStatic -> AImgGlobals.img_norz (md_p dA) (4 * md_n dA) = true.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@D24502936414.191D31131462022.191L11132759166.4  L18895178867.6  L19556266785.0  L27966909654.1  L29428551881.9  L29971584610.3  L35663928186.7  L36180290948.1  L38005716811.3  L38235734261.1  L41114660182.9  L42252534548.5  L43878034250.5  L5541292479.5   L5545796159.9   L59311123684.4  L60098763854.3  L61303668286.4  00000l01i01o02D02E02I02T02]03203603?03C03c04704>04R04j05805B05HS1R3HIA1h2ra2sp1X2nX3xs01b2wb2BB3WB01n2hc3dXc3TOP2X03SPR3HT1S1R2ra2sp1X2nX3xs02lo1b2wb2BB3WB04SLO21n3dXc5NEEDR3LOS2X03SPRS1f2BFS2nX2dA1n2HN3dXc4NMAXSS2spS2sp2lo3LO0S2dA1n2HNS1R3HIA1h2sp2lo3TOP1HS2spS2dA1n2HNS2loS1R2sp2lo4SLO25NEEDR3SPA3LO03SPRS2sp2lo3LO04LOSP3SPRS2sp2loS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDR3SPRS1X2dA3NGA3SXES1R2lo3LOSS1v2BV". (* [comment removed for export] *)
  #[using="IMG JC BB WB0 NRA NGA SLO2"] Lemma mi_COPY : forall n, 1 <= n <= md_n dA -> b <> 0 -> KC_stmt n.
  Proof.
    intros n HN BNZ. unfold KC_stmt. intros until xt6. intros J RA EO HNX NMAX BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. xa_open JX.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    assert (SPR' : 0 <= bv_unsigned sp + -96 < 2^64) by (clear - SPR LOSP LO0; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    clear MU WM.
    destruct RA as [EAX|[DBJ B]].
    - (* [comment removed for export] *)
      eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
      { eapply (A_copy_self (hcs asegs R HIA hc)) with (lo0 := lo);
          rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by exact SPR';
          first [ exact MI1 | exact ST1 | exact CSOK | reflexivity | (rewrite EAX; reflexivity)
                | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
                | clear - SLO2 NEEDR LOS SPA SPR LO0; lia
                | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "CSELF-PRE-LEFT:" g end ] ]. }
      cbv beta. intros ms' PO. unfold copy_self_postA in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in MU2, ST2 by exact SPR'.
      replace (ret_pc (Z_to_bv 64 0x9c944)) with (Z_to_bv 64 0x9c944 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof HH1 as HH2.
      apply (hm_munch asegs R HIA hc LBc LF [(bv_unsigned sp + -96 - 80, bv_unsigned sp + -96)] mc m2) in HH2;
        [| exact MU2| exact WM2| solve_w_writable].
      pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m2 J MU2 WM2 MI2 ltac:(replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by (clear; lia); exact ST2) HH2
                    ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as J2.
      assert (EDX : mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) (md_limbs dXc) (md_pad dXc) (md_own dXc) = dXc) by (destruct dXc; reflexivity).
      rewrite EDX in J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep.
      eapply mi_MLA with (n := n); [exact J2| left; exact EAX| exact EO| clear - HN; lia| exact HNX| clear - HN; lia| | exact BNZ| |].
      + clear - NMAX HN. lia.
      + unfold miV1, mul_int_PHI0, copy_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV NRA. lia.
      + unfold miF1, mul_int_FR0, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      exfalso. pose proof DBJ as [MB0 OB CRB CRBL SXB BIMG]. cbn [md_addr] in SXB.
      destruct SXB as [SXE|SXE]; clear - SXE NGA; lia.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "COPY-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02=0@C17025492443.202C24112444547.203C26381392939.202C26381392939.203D24976250634.204D36455618899.201D50797141399.204D52014138856.204D64152481649.201D9827600259.204 K11420089551.203K22413380088.203K25384422162.203K25953536645.202K25953536645.203K28284592895.202K6379668000.202 K68655443531.203L10642801822.2  L11416546478.3  L13023482647.2  L1685717371.0   L21847519070.3  L21860433226.15 L22401653661.3  L23100341967.179L23100341967.191L23190362336.5  L23643762344.4  L24313534829.3  L24575809296.199L25399627235.15 L25939631124.2  L27214106967.5  L28270437390.4  L28457445181.2  L29074096193.193L29074168500.196L29476485921.0  L2968662070.7   L2975768925.2   L29763661393.2  L29765106966.178L32754825233.4  L32761511569.15 L34107323466.3  L35663928186.7  L35794219356.1  L36180290948.1  L37969064749.4  L38235734261.1  L39172636981.0  L41128898453.2  L42633816569.1  L43878034250.5  L44084513735.9  L44604979078.2  L45918878996.1  L46160487540.179L48154963340.193L48155162489.190L48288935062.14 L48349305323.4  L5259801613.176 L54434634207.8  L54811923132.1  L54822575959.15 L58609956177.2  L59308664813.3  L60098763854.3  L60283674290.6  L6384586821.2   L68665096410.2  L8265267294.0   L8328083279.5   O17025492443.202O24112444547.203O27573497883.202O31435371494.203O57399310481.203P11420089551.203P25953536645.202P25953536645.203P6379668000.202 Q10235026062.195Q12370813529.182Q17207350632.183Q17207432298.195Q18701365324.204Q22285631880.201Q22285648010.198Q22288293174.200Q22955808635.201Q24974040330.203Q2544291370.201 Q26207421841.183Q26207721832.184Q26207967338.181Q26295627581.198Q30213615715.204Q31654082872.183Q36453634899.202Q37625261960.181Q38248387216.204Q39212284437.184Q39212284437.201Q42081808994.201Q42252534537.184Q42631062289.198Q42631275027.195Q42643779336.204Q42643792741.198Q43879899724.204Q43925228937.184Q45054200725.198Q4926406185.201 Q52016320488.203Q53153893485.198Q54255983967.200Q54627523118.200Q5485126037.181 Q5485126037.195 Q5485174314.182 Q5485600919.183 Q56761401107.201Q59703481013.182Q6027349519.204 Q60498968964.204Q60511567613.184Q60511567613.201Q60697995187.184Q6143569392.182 Q62868926301.198Q62965564504.202Q63231501142.198Q64154756465.202Q68717453381.198Q8880503606.181 Q8943555749.195 Q9538787269.181 Q9538787269.198 00000100200300400k01S02k03b04Z04[04\05B06@06A06B07507607e07k07l07m07n07o08F08G08j09R09b09o0::0:b0:c0:d0;40;50;;0;m0<_0<`0<m0=40=;0=g0=h0>:0>E0>Z0>_0>c0>d0>h0>i0>j0>o0?60?X0?_0?b0@O0AK0BG0BN0B\0CI0Ch0Ci0D70D>0DG0DQ0Dc0Dd0De0Df0E50E60E70E80E90E:0E;0E<0E=0E>0Ed0FQ0Fj0GH0Gk0HI0Hg0IE0Io0J\0K<0KU0Kn0LG0Lc0M@0MY0N90NR0Nl0OE0Oc0PJ0QH0Qh0RH0Rc0SC0S`0T90TY0U70Ud0VJ0Vh0WN0Wg0XE0X^0Y70Y[0Y\0ZI0[60[M0[i0\H0\a0]G0^50^S0_90__0`80`T0`k0aGFFFFS2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2LQ2HB5Ha_st5Hl_stS2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS1R2ra2sp1X2nX3xs02dA2lo1b2wb2BB3WB04SLO21N3pXc2xs5NEEDR3LOS2X03SPR2P02LQ2HB5Ha_st5Hl_stS2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2LQ2HB5Ha_st5Hl_stS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2X03SPR2N12P02LQFFS2sp1X2nX3xs02dA2lo1b2wb2BB3WB02xs3DSXS1R2sp2nX3xs02dA2lo1b2wb2BB3WB04SLO21N3pXc2xs5NEEDR3LOS3ALO2PCFFS1R2sp2nX3xs02dA2lo1b2wb2BB3WB01N3pXc2xs3LOS3ALO2PCFS1X2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2N12P03XPc2LQS1N2N1FFSFS1R2sp2lo4SLO24NRAm3SPRFS2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xsS2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS1X1N3pXc2N13XPcS1X1N3pXc3XPcS1N3pXc3P47S2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2LQFFS1R3HIA1h2sp3TOPFS1N2N1S2ra2sp1X2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2X03X162LQS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2X03X162LQSS2sp1X2lo3DSXS1N3pXcS1N3NR1S2ra2sp1X2nX3xs02dA1b2wb2BB3WB01N3pXc2xs3NR1FS2sp2lo1N3pXc4XLScS1N2xs4LEN1S1R3HIA1h2sp2lo3TOP1HS3pXcS2spFS2loSFS3pXcS2sp2loS1R2sp2lo4SLO21N3pXc5NEEDR2N14XLScS2sp2loS1NS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03X16S2ra2sp1X2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2X03SPR2N12P03P472LQS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2X03SPR2N12P03P472LQS2sp2loS1N2xs4LEN12N1S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03X16S1R2sp2lo4SLO21N3pXc5NEEDR4XLScFS2sp1N3SPR3NR1S1N3NR1S1N2N12ENS1R2lo3LOSS2sp2lo1N3pXc1a2NOFFSS1N3pXc2N11a2NOFFFFFFFFFS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2N12LQS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03XALS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB01N2xs2LQS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2N1S1X2nX3xs02dA1b2wb3WB01N2xs2LQS1X2nX3xs02dA1b2wb3WB01N2xs2LQS1X2nX3xs02dA1b2wb3WB01N2xs2LQS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2N13P472LQS1X2nX3xs02dA1b2wb3WB01N2xs2LQ2HB5Ha_st5Hl_stS2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB01N2xs2LQS2nX3xs02dA1b2wb3WB01N3pXc2xsS1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA2lo1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB01N2xs2LQS1X2nX3xs02dA1b2wb2BB3WB01N2xs2X02LQ2HBS1R2sp2nX3xs02dA2lo1b2wb2BB3WB04SLO22xs5NEEDR3LOS4SP643ALO3ACPS2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS2nX3xs02dA1b2wb3WB03pXc2xsS2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS2sp2nX3xs02dA2lo1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB01N3pXc2xs2LQS1X2nX3xs02dA1b2wb3WB01N2xs2LQS1X2nX3xs02dA1b2wb3WB01N2xs2LQ2HB5Ha_st5Hl_stS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2P02LQS1X2nX3xs02dA1b2wb3WB01N2xs2LQS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2P02LQS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB01N2xs2LQS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb2BB3WB01N2xs2X02LQFS1X2nX3xs02dA1b2wb3WB01N2xs2LQ2HB5Ha_st5Hl_stS1R2sp2nX3xs02dA2lo1b2wb2BB3WB04SLO22xs5NEEDRS2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB01N2xs2LQS1X2nX3xs02dA1b2wb2BB3WB02xs2X0S1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2N12LQS1X2nX3xs02dA1b2wb2BB3WB01N2xs3X162LQ2HB5Ha_stS1X2nX3xs02dA1b2wb3WB01N2xs2LQS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2N12LQS2nX3xs02dA1b2wb2BB3WB01N3pXc2xs2N12LQS1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB01N2xs2LQS2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB01N2xs2LQ". (* [comment removed for export] *)
  #[using="IMG AMS wb JC BB WB0 SLO2"] Lemma mi_LSET2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pv,$8.Pf,$8.Phc,(0.$4?.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs4,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(51.$4?.VR,VHIA,Vh,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$52.(53.$2.)R1=.R1<.R1;.R1:.R19.R18.)P,(>.$?.(10.R19.)$22.)P,(13.(14.R1:.)(55.VnX,(15.(14.VdA,)+1.)))P,(13.R20.(3;.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,))P,(13.R20.(41.Vd,))(57.$4?.(58.$4?.VR,VHIA,R20.Vmo,)$59.(4;.(4<.R1<.(2?.&40.(15.(1;.&40.Vsp,)-60.))Vgp,Vtp,R1;.R1:.R19.(2?.&40.VX,)(2?.&40.(15.VX,+:.))R18.R17.R16.R15.R14.R13.R12.R11.R10.(2?.&40.(15.(5>.(15.VX,+:.)+3.)(5=.(33.VR,))))R?.(2?.&40.(5=.(33.VR,)))R>.R=.R<.R;.R:.Vs11,R9.R8.R7.R6.)VF,(2?.&40.+9<:20.)Vfc,(4=.(3.&40.))R1>.(4>.$4?.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 EO NMAX BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
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
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_MI) as SPM. unfold A_ASAN_MEMSET_MI in SPM.
    acallxA_sp (bv_unsigned sp + -96)
      (eapply SPM with (h := hc) (LB := LBc) (LF := LF) (DST := pXc) (v := 0) (n := 4 * N) (lo := lo) (ds := u32s xs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; exact XARR
             | rewrite u32s_length; clear - LEN1; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
             | eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
             | rewrite HT1; clear - TOP; lia
             | f_equal; clear; lia
             | right; clear - P47; lia
             | clear - XLSc SLO2 NEEDR N1 NR1 NRAm LOS SPA SPR LOSP; lia
             | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ] ]).
    clear SPM.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned sp + -96) |- _ => rename H into ST6 end.
    match goal with H : u8arr asegs m6 pXc _ |- _ => rename H into HPZ end.
    match goal with H : HM asegs R HIA hc LBc LF m6 |- _ => rename H into HH6 end.
    replace (Z.to_nat (4 * N)) with (4 * Z.to_nat N)%nat in HPZ by (clear - N1; lia).
    apply (rw_cells_of_u8arr asegs) in HPZ.
    assert (XARR6 : u32arr asegs m6 pXc (repeat (Z_to_bv 64 0) (Z.to_nat N))).
    { eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]. }
    assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
    { intros a NO. cbn [outside] in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 96) by (clear - NO; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    pose proof ST6 as ST6'.
    assert (LQ : length (repeat (Z_to_bv 64 0) (Z.to_nat N)) = length xs) by (rewrite repeat_length; clear - LEN1 N1; lia).
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6
                  ltac:(cbn; split; [clear - XLSc SLO2 NEEDR; lia| split; [clear; lia| exact I]])
                  ltac:(cbn; split; [clear - XPc; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]) XARR6
                  LQ) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    (* [comment removed for export] *)
    clear MU WM CX1 OX1 HPZ.
    try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear XP1; try clear XLS1; try clear NM1.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J6) as (_ & LEN6 & _ & _ & CX6 & _ & OWN6).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LEN6, CX6, OWN6. unfold mpi_cells in CX6.
    ddestruct (OWN6 ltac:(discriminate)) as (_ & _ & _ & _ & XARR6' & _ & _ & _ & OP6 & _).
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6) as OX6. cbn [md_addr] in OX6.
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6) as HH6'. cbn [app] in HH6'.
    pose proof (xa_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6) as HT6.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof (munch_refl [(pXc, pXc + 4)] m6) as MU; pose proof (wmono_refl asegs m6) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OP6 pXc 4.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok asegs m6 pXc (repeat (Z_to_bv 64 0) (Z.to_nat N)) 0 _ XARR6' ltac:(rewrite repeat_length; clear - N1; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs m6 pXc (repeat (Z_to_bv 64 0) (Z.to_nat N)) 0 vv XARR6' ltac:(rewrite repeat_length; clear - N1; lia)) as XARR7 end.
    replace (pXc + 4 * 0) with (pXc + 0) in XARR7 by (clear; lia).
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : mem_inv asegs m7 |- _ => rename H into MI7 end.
    match goal with H : stk asegs m7 lo _ |- _ => rename H into ST7 end.
    match goal with H : HM asegs R HIA hc _ LF m7 |- _ => rename H into HH7 end.
    assert (HW7 : forall a, ~ outside [(pXc, pXc + 4)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
    { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO N1. lia. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m7 _ J6 MU WM MI7 ST7 HH7 HW7
                  ltac:(cbn; split; [clear - XLSc SLO2 NEEDR N1; lia| exact I]) ltac:(cbn; split; [clear - XPc N1; lia| exact I]) XARR7
                  ltac:(rewrite upd_length; reflexivity)) as J7.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J7.
    (* [comment removed for export] *)
    clear MU WM. try clear CX6; try clear OX6; try clear XARR6'; try clear XARR7; try clear OP6; try clear HH6'.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J7) as (_ & _ & _ & _ & CX7 & _ & _).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX7. unfold mpi_cells in CX7.
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J7) as OX7. cbn [md_addr] in OX7.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J7) as CWX. cbn [md_addr] in CWX. rewrite <- HT6 in CWX.
    pose proof (munch_refl [(X, X + 16)] m7) as MU; pose proof (wmono_refl asegs m7) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX7 (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    match goal with H : mem_inv asegs m8 |- _ => rename H into MI8 end.
    match goal with H : HM asegs R HIA hc LBc LF m8 |- _ => rename H into HH8 end.
    match goal with H : aobj asegs AL (hcs asegs R HIA hc) m8 X 16 |- _ => rename H into OX8 end.
    match goal with H : rw_cells asegs m8 X _ |- _ => rename H into CX8 end.
    pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ 1 J7 MU WM MI8 CX8 (or_introl eq_refl) HH8 OX8) as J8.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J8.
    eapply mi_ret; [exact J8| left; split; [reflexivity| split; [intros _| cbn [md_n]; exact NMAX]]| exact BV| exact BF].
    unfold mpd_val. cbn [md_sg md_limbs].
    assert (EUPD : upd (repeat (Z_to_bv 64 0) (Z.to_nat N)) (Z.to_nat 0) (Z_to_bv 64 0) = repeat (Z_to_bv 64 0) (Z.to_nat N)).
    { destruct (Z.to_nat N) eqn:EN; [exfalso; clear - EN N1; lia| reflexivity]. }
    rewrite EUPD, limbs_val_repeat0. reflexivity.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "LSET2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L11132759166.4  L25044269509.2  L25046317048.175L35663928186.7  L46160487540.175L46164803833.172L59308632045.6  L59308664813.3  L60098763854.3  L61303668286.4  L64934269637.2  Q26207421841.176Q26207721832.177Q26220226066.174Q31654082872.176Q39212284437.177Q43925228937.177Q60511567613.177Q60697995187.177Q8884880718.174 Q9534400957.174 00000600?00i01>01g02P02c02n03803>03G03`04904R04k05D05]06406S06l07CS1f2BFS3nXc3NR1S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03nXc2xs3NR1S1R3HIA1h2sp2lo3TOP1HS2ra2sp1X2nX3xs02dA1b2wb2BB3WB02xs2X03X16S2ra2sp1X2nX3xs02dA1b2wb2BB3WB02xs2X03X16S2nX3NG13nXc3NM12KNS3nXc2KN2ENS1R2lo3LOSS1v2BVS3nXc3NR1S1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB02xsS1X2nX3xs02dA1b2wb2BB3WB02xs2X0S1X2nX3xs02dA1b2wb3WB02xsS2nX3xs02dA1b2wb3WB02xs". (* [comment removed for export] *)
  #[using="IMG AMS wb JC BB WB0 NG1 SLO2"] Lemma mi_LSET : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pv,$8.Pf,$8.Phc,(0.$4?.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1',(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(51.$4?.VR,VHIA,Vh,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$52.(53.$2.)R1?.R1>.R1=.R1<.R1;.R1:.)P,(13.(14.R1;.)(55.VnX,(15.(14.VdA,)+1.)))P,(13.R21.=)P,(13.R21.=)(57.$4?.(58.$4?.VR,VHIA,R21.Vmo,)$59.(4;.(4<.R1=.(2?.&40.(15.(1;.&40.Vsp,)-60.))Vgp,Vtp,R1<.R1;.R1:.(2?.&40.VX,)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.(2?.&40.(5=.(33.VR,)))R=.R<.R;.R:.R9.Vs11,R8.R7.R6.R5.)VF,(2?.&40.+9<98<.)Vfc,(4=.(3.&40.))R1?.(4>.$4?.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J NMAX BV BF. jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof CX1 as CX1u. unfold mpi_cells in CX1u.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep. if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NR1; lia).
    { (* [comment removed for export] *)
      assert (EO : own = LHeap).
      { destruct own; [exfalso; ddestruct (OWN0 eq_refl) as (_ & EN & _); clear - EN KN; lia| reflexivity| exfalso; exact (NS1 eq_refl)]. }
      clear CX1u. eapply mi_LSET2; [exact J| exact EO| exact NMAX| |].
      - unfold mul_int_PHI0, copy_PHI, grow_PHI; unfold AVOL_CALL. clear - BV NRA. lia.
      - unfold mul_int_FR0, calls_FR, fr_charge. clear - BF D0. lia. }
    (* [comment removed for export] *)
    exfalso. clear - KN NR1 NM1 NG1. lia.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "LSET-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0@L11132759166.4  L22593291094.4  L25694054625.3  L29008356616.175L29010568605.176L29010568859.179L35663928186.7  L36618624197.2  L39268637205.0  L40497504664.12 L46158332094.176L46160487540.179L59308631146.8  L59308664813.6  L60098763854.3  L61303668286.4  L65448092613.2  L65450274431.179Q26207421841.180Q26207721832.181Q26209920597.178Q31654082872.180Q39212284437.181Q43925228937.181Q60511567613.181Q60697995187.181Q8882996489.178 Q9540479482.178 00000600E00O01N02M03=03R03[03\03l04V05@05[05n06806>06G06n07H07b08<08V09009J09b0:B0:\0;4S1f2BFS2nX1r3dXc4NXLES1r3dXc2KGS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01U3NGU1r3dXc2HR2RU2X02NR3SPR3WBRS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01U3NGU1r3dXc2HR2RU2X02NR3SPR3WBRS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01r3dXc2HR3WBR3N10S1R3HIA1h2sp2lo3TOP1HS3dXc3NR1SS1r1q2KM2r01H2H0S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03dXc2X03X16S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03dXc2X03X16S2nX1U3NGU1r3dXc2RU4NM1x2KGS2dA1r3dXc2HR2KG2ENS1R2lo3LOSS1v2BVS3dXc3NR1S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03dXc3NR1S1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb2BB3WB03dXc2X0S1X2nX3xs02dA1b2wb3WB03dXcS2nX3xs02dA1b2wb3WB03dXc". (* [comment removed for export] *)
  #[using="IMG AMS JC BB WB0 NRA NGA NG1 NGU SLO2"] Lemma mi_FOUND : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pr,$8.Pv,$8.Pf,$8.Phc,(0.$4?.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(51.$4?.VR,VHIA,Vh,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$52.(53.$2.)R1;.R1:.R19.R18.R17.R16.)P,(5:.VR,VHIA,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdA,R1:.R19.R18.R17.)P,(13.(14.R18.)(55.VnX,(15.(14.VdA,)+1.)))P,(13.(14.R19.)VnX,)P,(27.(13.+1.R20.)(13.R20.(14.VdA,)))P,(13.R21.VU,)P,(13.R21.=)P,(13.R21.=)(57.$4?.(58.$4?.VR,VHIA,R21.Vmo,)$59.(4;.(4<.R1=.(2?.&40.(15.(1;.&40.Vsp,)-60.))Vgp,Vtp,R1<.R1;.R1:.(2?.&40.VX,)(2?.&40.R24.)R19.(2?.&40.(12.VdA,))Vwb,R18.R17.R16.R15.R14.R13.R12.R11.(2?.&40.(5=.(33.VR,)))(2?.&40.(15.(5>.(12.VdA,)+3.)(5=.(33.VR,))))R10.R?.R>.R=.Vs11,R<.R;.R:.R9.)VF,(2?.&40.+9<878.)Vfc,(4=.(3.&40.))R1?.(4>.$4?.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA NMAX NXLE HR RU BV BF. jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. xa_open JX.
    pose proof NM1 as NM1x. cbn [md_n] in NM1x. unfold mpi_cells in CX1. rewrite ?AD1 in CX1. cbn [md_addr] in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    cbn [md_addr] in OX1.
    pose proof (bv_unsigned_in_range 64 wb) as WBR. unfold bv_modulus in WBR. cbn [Z.pow Z.of_N Pos.pow] in WBR.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *)
      eapply mi_LSET; [exact J| exact NMAX| exact BV| exact BF]. }
    assert (BNZ : b <> 0) by (intros B0; apply KB; apply (proj2 WB0); exact B0).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by (clear - HR NRA; rewrite ?Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    { (* [comment removed for export] *)
      eapply mi_ret; [exact J| right; reflexivity| |].
      - unfold mul_int_PHI0, copy_PHI, grow_PHI; unfold AVOL_CALL. clear - BV NRA. lia.
      - unfold mul_int_FR0, calls_FR, fr_charge. clear - BF D0. lia. }
    assert (N10 : r + 1 <= 10000).
    { rewrite Z.shiftr_div_pow2 in KM by (clear; lia). change (2 ^ 4) with 16 in KM. clear - KM HR NRA. Z.div_mod_to_equations. lia. }
    clear KM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    zstep. zstep.
    replace (zx16 (Z_to_bv 64 (md_n dXc))) with (Z_to_bv 64 (md_n dXc))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases KG; zify_cond KG; rewrite ?unsigned_lit in KG by (clear - HR NRA NR1; lia).
    - (* [comment removed for export] *)
      assert (EO : md_own dXc = LHeap).
      { destruct (md_own dXc) eqn:EOX; [exfalso; ddestruct (OWN0 eq_refl) as (_ & EN & _); clear - EN KG HR; lia| reflexivity| exfalso; exact (NS1 eq_refl)]. }
      eapply (mi_COPY r HR BNZ); [exact J| exact RA| exact EO| clear - KG; lia| clear - NXLE; lia| |].
      + unfold miV1, grow_PHI; unfold AVOL_CALL. clear - BV NRA. lia.
      + unfold miF1, calls_FR, fr_charge. clear - BF D0. lia.
    - (* [comment removed for export] *)
      exfalso. clear - KG RU NGU NM1x. lia.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "FOUND-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L21041645149.3  L21774718167.2  L23120643753.4  L23120701814.4  L23970764156.152L34764071861.3  L48367540261.4  L48367597562.3  L54425651213.3  L56104965185.0  L59308583409.4  L59310648043.5  L8929159528.149 L8929620893.146 Q26295627581.150Q34291222827.147Q34291305632.152Q34291402793.150Q42131479398.152Q48338484555.150Q49424719380.147Q50458135125.150Q53360483131.150Q8943555749.147 00000800>00?00K01G01O01P01Q01Z01[01g02903504104L04m05N05o06P07507V08108R08mS1k1r2HkS2dA1rFS2dA1r2HR2K2S2ra2sp1X2nX3xs02dA1b2wb2BB3WB01k1r2Hk4LENZ3EP02HR2X03SPR2EBS1U1r2RUFFS2dA1r2HRSS2dA1r2Hk2HRS2dA1r4LENZ2HR3NTHS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01k1r2Hk4LENZ3EP02HR2X03SPR2EBS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01k1r2Hk4LENZ3EP02HR2X03SPR2EBS2nX3xs02dA1b2wb3WB01k1r2HkS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk3EP02HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb3WB01k1r2HkS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb3WB01k1r2Hk". (* [comment removed for export] *)
  #[using="IMG AMS JC BB WB0 NRA U NGA NG1 NGU NGZ SLO2"] Lemma mi_SCANLOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pk,$6<.Pv,$8.Pf,$8.Phc,(0.$4?.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pr1,(3.&40.)Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(13.R15.(6=.R1<.))P,(51.$4?.VR,VHIA,Vh,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$52.(53.$2.)R1<.R1;.R1:.R19.R18.R17.)P,(5:.VR,VHIA,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdA,R1;.R1:.R19.R18.)P,(13.(14.R19.)(55.VnX,(15.(14.VdA,)+1.)))P,(13.(14.R1:.)VnX,)P,(6>.$4?.R1<.(23.VdA,)(6?.(17.VdA,)))P,(>.$8.(6=.(70.(3.&40.)(17.VdA,)))(14.VdA,))P,(28.=(23.VdA,))P,(71.$4?.(33.VR,)(34.$4?.VR,VHIA,R21.)R1?.(23.VdA,)(24.+4.(14.VdA,)))P,(27.(13.+1.R1>.)(13.R1>.(14.VdA,)))P,(13.R25.=)P,(13.R25.=)P,(>.(3.&40.)R20.(2?.&40.R21.))(57.$4?.(58.$4?.VR,VHIA,R26.Vmo,)$59.(4;.(4<.R20.(2?.&40.(15.(1;.&40.Vsp,)-60.))Vgp,Vtp,R1?.R1>.R1=.(2?.&40.VX,)R21.(2?.&40.(15.(23.VdA,)(24.+4.(2=.R22.+1.))))(2?.&40.(12.VdA,))Vwb,(2?.&40.(15.(23.VdA,)(24.+4.(2=.R22.+1.))))R1<.R1;.R1:.R19.R18.R17.R16.(2?.&40.(5=.(33.VR,)))(2?.&40.(15.(5>.(12.VdA,)+3.)(5=.(33.VR,))))R15.R14.R13.R12.Vs11,R11.R10.R?.R>.)VF,(2?.&40.+9<83<.)Vfc,(4=.(3.&40.))R24.(4>.$4?.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 RA NMAX NXLE EBY LENZ EP0 OEL HR BV BF ->; [exfalso; clear - Hk HR; lia|].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEL (md_p dA + 4 * (r - 1)) 4.
    (* [comment removed for export] *)
    destruct (nth_error (md_limbs dA) (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dA) (md_limbs dA) (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      eapply mi_FOUND; [exact J0| exact RA| exact NMAX| exact NXLE| exact HR| | exact BV| exact BF].
      destruct (Z_le_gt_dec r U) as [RU|RU]; [exact RU| exfalso].
      pose proof (NGZ (r - 1) w ltac:(clear - RU; lia) NTH) as WZ.
      apply K0. rewrite bv_unsigned_sx32, WZ. apply (proj2 (sxz_zero_iff 0 ltac:(clear; lia))). reflexivity.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - HR NRA; lia).
      + replace (Z_to_bv 64 (md_p dA + 4 * (r - 1) + -4)) with (Z_to_bv 64 (md_p dA + 4 * (r - 1 - 1))) by (f_equal; clear; lia).
        eapply (IH _ _ _ _ _ _ (r - 1)); try eassumption; first [clear - Hk; lia| clear - HR K2; lia| (f_equal; clear; lia)| reflexivity].
      + (* [comment removed for export] *)
        zstep.
        eapply mi_LSET; [exact J0| exact NMAX| exact BV| exact BF].
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "SCANLOOP-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579668.400000=S1X2Ea3SXE2H5". (* [comment removed for export] *)
  #[using="IMG"] Lemma mk_JBd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "PdE,$7.Pm1,P,(3.&40.)(5.(3.&8.))P,(72.$4?.VR,VLF,Vm,VLB,(1;.&40.Vsp,)R2.)P,(1=.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.Vlo,(1;.&40.Vsp,))P,(1>.(1?.VR,)(20.$2.VLB,(21.VLF,))Vlo,(12.R4.)+10.)P,P,(>.$?.(10.R5.)$22.)(1>.(1?.VR,)(20.$2.VLB,(21.VLF,))Vlo,(23.R6.)(24.+4.(14.R6.)))P,(2:.(13.(15.VX,+10.)(12.R6.))(13.(15.(12.R6.)+10.)VX,))P,P,(>.$?.(10.R7.)$11.)P,Pi,$8.P,(27.(13.=R1.)(28.R1.(24.+4.(14.R9.))))(>.$35.(38.$4?.(39.(15.(23.R:.)R2.)))$37.)(>.$35.(36.(23.R9.)(24.+4.(14.R9.)))$37.)P,(71.$4?.(33.VR,)(34.$4?.VR,VHIA,Vh,)R7.(12.R8.)+10.)P,P,(>.$?.(10.R9.)$11.)(71.$4?.(33.VR,)(34.$4?.VR,VHIA,Vh,)R9.(23.R:.)(24.+4.(14.R:.)))P,(9.$4?.VR,VHIA,Vh,VLB,VLF,R9.)P,(72.$4?.VR,VLF,R:.VLB,(1;.&40.Vsp,)R;.)(27.(73.$4?.VR,VHIA,VLB,VLF,Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R<.)(74.$4?.VR,VHIA,VLF,Vsp,R<.Vh,VLB,R;.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros dE m1; intros ME OE CRE CREL SXE IE OEs OEl HM1 ME1. dpose OE as (OE1 & OE2 & OE3 & OE4 & OE5).
    destruct dE as [Ea sE nE pE zs0 padE ownE].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    split.
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
      intros EO RO hc LBc mc HMc. eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IE EO RO)].
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01l0@D35881667587.152D35881667587.153D51255084822.153D61949433775.152D61949433775.153K14554379081.152K14554379081.153L11075936116.145L14550820926.2  L17097338356.145L17305700853.4  L19431261630.4  L19687428440.145L19945316590.2  L21772258342.1  L23124392564.145L23459140778.163L23459159589.2  L23461302312.159L25465666776.145L27017364261.2  L28125529944.145L29025845208.145L29135309044.145L29532535949.3  L29762660275.145L31686769240.145L35161367924.145L35653441506.7  L36180999398.148L39172636981.0  L39280637297.0  L40834179097.158L41172169716.145L43059266230.146L43110360625.2  L43112818177.4  L43671330526.3  L43679985268.144L5065130740.145 L51284464315.164L52253708504.145L55563306247.3  L55720577396.145L58640675965.155L58641002120.158L59310645584.3  L60098763854.3  L60692334296.145L61601561944.145L61747685364.145L62042415875.145L62505661912.144L62562505368.3  L64270350808.145L65178513496.145L67758486644.145Q10042269183.168Q10333294960.162Q15643324129.148Q18133842458.163Q18133990681.163Q18135743526.160Q18365925601.149Q18378753154.149Q18696506101.162Q21800401414.162Q21879645826.149Q24389563138.149Q25160350961.162Q25513505925.151Q25513505925.152Q25664719138.162Q27584944865.149Q27907200258.149Q30415036802.149Q31226872993.162Q31271525473.149Q31396957457.162Q32655500769.149Q33918256002.149Q34224482651.160Q34420396856.163Q35016271767.162Q35715139857.162Q36425882626.149Q3830427394.149 Q39212284437.163Q39517585209.152Q39939554818.149Q41152393185.149Q4141071397.162 Q44648843873.149Q4533518817.149 Q49698585326.150Q49698585326.151Q50301287168.162Q51235796833.149Q52101170785.149Q53972118266.162Q55780705378.151Q55780705378.152Q58692335428.163Q59256763233.149Q59843137889.149Q60511257090.149Q60511567613.163Q61264001456.169Q61265740300.168Q61800308129.162Q63856323923.149Q63856323923.150Q6414620453.162 Q64253126389.162Q64333403626.150Q64766008503.163Q66375044744.169Q66522067074.149Q67327367611.168Q67528989526.152Q67528989526.153Q8222473558.169 Q9538787269.160 Q9843367298.148 00000k02H03Y04f06Q07R09209O09P09m0:90:G0:d0:k0:o0;L0<30<;0<_0=<0=D0=a0>>0>[0>f0?C0?`0@=0@U0A20A30A40AS0B00BX0B_0Bf0Bn0CK0Ch0DE0Db0Dj0EG0Ej0FM0FY0Fc0G@0G]0H:0HW0I40I<0IY0J60JS0Jh0Ji0KD0KY0Kn0LC0L^0MA0M`0Ma0ND0Ng0OF0P30Q?0Q@0Q[0R>0Ra0SA0S\0T10TL0To0UD0UY0V90V:0V]0W@0WU0XK0Xn0YI0YJ0Ye0Z@0Zi0[R0[S0[n0\I0\i0]^0^n0_I0_d0`?0`b0a70aL0aa0ab0b@0b^0c=0c>0c\0d10dF0di0e>0f30gG0h50hJ0hmS1R3HIA1h2ra2sp1X3xs02dA1b2wb2BB3WB03TOP3ABD2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs02dA1b2wb2BB3WB03TOP3ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S1R2ra2sp3s101X3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3LOS2X03SPR2A03ABD2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3LOS2X03SPR2A03ABD2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3LOS2X03SPR2A03ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S1R2ra2sp3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3ABD3OA42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3ABD3OA42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S2ra2sp1X3xs02dA1b2wb3WB03ABDFS2ra2sp1X3xs02dA1b2wb3WB03ABDS2sp2dA2lo1KS2sp2dA2lo3OA4S2ra2sp1X3xs02dA1b2wb3WB03ABDS2sp2loS2dAS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb2BB3WB02A03ABD3NRAS2dA3NRAS2ra2sp1X3xs02dA1b2wb2BB3WB03NRA3ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NRAS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NRA2KNS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3xs02dA1b2wb3WB03ABDSSS1R2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2nX2dAS2nX2dAS1X2dA1DS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NA1S2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb2BB3WB02A03ABDS2ra2sp1X3xs02dA1b2wb2BB3WB02A03ABDS2dA3EZ03NA1S1R2lo3LOSS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NA1S2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDFS2sp3xs02dA2lo1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS1R3xs02dA1b2wb2BB3WB04IMG'3ABDFS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS1R3xs02dA1b2wb2BB3WB04IMG'3ABDS2ra2sp3xs02dA2lo1b2wb3WB03ABD2HB5Ha_st5Hl_stS2sp2s03xs02dA2lo1b2wb3WB03ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10FS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS1R3xs02dA1b2wb2BB3WB05ALWF'3ABDS2sp3xs02dA2lo1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS1R3xs02dA1b2wb2BB3WB05ALWF'3ABDFS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS2sp3s103xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_stS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb3WB03ABDFS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA1b2wb2BB3WB04SP643ABD2HB5Ha_stS2sp3xs02dA1b2wb2BB3WB04SP643ABD2HB5Ha_stFS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS1R3xs02dA1b2wb2BB3WB05ALWF'3ABDS2ra2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_stS2sp2s03xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S3xs02dA1b2wb2BB3WB02A03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDFS2sp3xs02dA1b2wb2BB3WB03ABD2HBS2sp3xs02dA1b2wb2BB3WB03ABD2HBS1R3xs02dA1b2wb2BB3WB04IMG'3ABDFS2sp3xs02dA1b2wb2BB3WB03ABD2HBS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS2ra2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_stS2sp2s03xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S2ra2sp1X3xs02dA1b2wb2BB3WB02X03SPR3AAL2A03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABD". (* [comment removed for export] *)
  #[using="IMG AMS JC BB WB0 NRA U NGA NG1 NGU NGZ SLO2 MA0 IA1"] Lemma mi_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(:.$4?.VR,VHIA,Vh,Vmo,)P,(<.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)P,(1=.(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,Vlo,(1;.&40.Vsp,))P,(1>.(1?.VR,)(20.$2.VLB,(21.VLF,))Vlo,(12.VdA,)+10.)P,P,(>.$?.(10.VdA,)$22.)(1>.(1?.VR,)(20.$2.VLB,(21.VLF,))Vlo,(23.VdA,)(24.+4.(14.VdA,)))P,(2;.$4?.Vm,Vlo,(1;.&40.Vsp,))P,(31.$4?.Vm,)P,(32.$4?.(33.VR,)(34.$4?.VR,VHIA,Vh,)Vm,(50.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(32.$4?.(33.VR,)(34.$4?.VR,VHIA,Vh,)Vm,VdA,)P,P,(>.$?.(10.VdA,)$11.)P,Pi,$8.P,(27.(13.=R1.)(28.R1.(24.+4.(14.VdA,))))(>.$35.(38.$4?.(39.(15.(23.VdA,)R2.)))$37.)(>.$35.(36.(23.VdA,)(24.+4.(14.VdA,)))$37.)(47.$4?.$59.(4:.(4;.(4<.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(2?.&40.VX,)(2?.&40.(12.VdA,))Vwb,R13.R12.R11.R10.R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(2?.&40.$75.)Vfc,(4=.(3.&40.))Vm,(4>.$4?.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK SXA OA CRA CRAL ST MI OXA OAA IA2. unfold A_MPI_MUL_INT.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof MA0 as [(CA0 & AAL & A0 & LENA & NRA' & OWNA) SGA]. unfold MPI_MAX_LIMBS in NRA'.
    pose proof (rw_cells_bound _ _ _ _ CA0) as ABD. unfold mpi_cells in ABD. cbn [cells_size csize Nat.add] in ABD.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. cbn [md_addr] in OX.
    pose proof SXA as SXA0. unfold mpd_sep in SXA. cbn [md_addr] in SXA.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 96%nat ST.
    (* [comment removed for export] *)
    do 13 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    change (rw_cells asegs m1 (bv_unsigned sp + -96) MI_FRAME_A) in FR.
    pose proof ST as ST1.
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    (* [comment removed for export] *)
    assert (MA1 : mpd_at asegs m1 LB dA).
    { eapply mpd_at_munch_any; [exact MA0| exact MU| exact WM| cbn; split; [clear - OA4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OA5 ON) as [K|K]; clear - K; lia| exact I]. }
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    pose proof OAs as OAs1.
    assert (OAl1 : md_own dA = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dA) (4 * md_n dA)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OAl E)]).
    pose proof (opnd_atA_mpd asegs R LF m LB (bv_unsigned sp) dA MA0) as MA0o. pose proof (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dA MA1) as MA1o.
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH1. cbn [app] in HH1.
    assert (RA : RIDE h LB m1 dX).
    { destruct (Z.eq_dec (md_addr dA) X) as [E|NE]; [left; exact E| right].
      eapply mk_JBd; try eassumption. all: try (intros EO RO; exact (IA2 EO RO)).
      all: destruct SXA as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| clear - D; lia]. }
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH1) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OAs1 (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    pose proof MA1 as [(CA1 & _) _]. unfold mpi_cells in CA1.
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dA))) with (Z_to_bv 64 (md_n dA))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NRA; lia); rewrite Z.mod_small by (clear - NRA; lia); reflexivity).
    zstep. if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NRA; lia).
    { (* [comment removed for export] *)
      eapply mi_LSET; [exact J0| cbn [md_n]; clear; lia| clear; lia| clear; lia]. }
    assert (NA1 : 1 <= md_n dA) by (clear - KN NRA; lia). clear KN.
    assert (AN : md_own dA <> LNull) by (intros C; rewrite C in OWNA; destruct OWNA as [_ EZ0]; clear - EZ0 NA1; lia).
    (* [comment removed for export] *)
    assert (EF : bytes_at asegs m1 (md_p dA) (u32s (md_limbs dA)) /\ 0 < md_p dA).
    { pose proof MA1 as [(_ & _ & _ & _ & _ & OW1) _]. destruct (md_own dA) eqn:EOA; [exfalso; exact (AN eq_refl)| |].
      - ddestruct OW1 as (_ & AIN & _ & AARR). split; [apply u32arr_ro; exact AARR|].
        destruct (hm_apart asegs R HIA h LB LF m1 HH1) as [HBR _]. rewrite Forall_forall in HBR.
        destruct (HBR _ ltac:(apply in_app_iff; left; exact AIN)) as (B0 & _). cbn [fst] in B0. exact B0.
      - ddestruct OW1 as (_ & _ & AP0 & ABY & _). split; [exact ABY| exact AP0]. }
    destruct EF as [EBY EP0].
    assert (OEL : aobj asegs AL (hcs asegs R HIA h) m1 (md_p dA) (4 * md_n dA)).
    { eapply (mpd_aobjA_limbs asegs R HIA h LB LF m1 dA HH1 MA1); [split; [exact OAs1| exact OAl1]| exact AN]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    zstep. zstep. zstep.
    replace (Z_to_bv 64 (md_p dA + md_n dA * 4 + -4)) with (Z_to_bv 64 (md_p dA + 4 * (md_n dA - 1))) by (f_equal; clear; lia).
    eapply (mi_SCANLOOP (Z.to_nat (md_n dA))) with (r := md_n dA);
      first [ exact J0 | exact RA | exact EBY | exact LENA | exact EP0 | exact OEL | reflexivity
            | cbn [md_n]; clear - NA1 NRA; lia | clear - NA1 NRA; lia
            | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MAIN-SIDE-LEFT:" g end ] ].
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MAIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End WM.


Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L23332287433.0L42243864624.500000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Theorem A_mpi_mul_int_ng_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_ng_c24 ()) "PR,$76.PHIA,(77.$4?.R1.)P,(78.(33.R2.))P,(>.$8.(79.R3.)$7:.)P,(13.=(2>.R4.))P,Ph,(0.$4?.R5.R4.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$4?.R9.R8.R4.R3.R2.R1.)(7;.$8.(7<.(64.$8.$8.)$8.(7=.$8.$8.)R4.))P,(27.(13.(7>.(1?.R6.))(7?.(1?.R6.)))(13.(80.(1?.R6.))(81.(1?.R6.))))P,Pa,$8.P,(>.$35.(38.$4?.(39.R1.))$37.)P,(27.(13.=R2.)(28.R2.(1<.+2.+40.)))(27.(13.(7>.(1?.R:.))R3.)(28.R3.(81.(1?.R:.))))(82.$4?.R8.R7.$75.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS NEEDR HND DIMG ROIMG. unfold mpi_mul_int_ng_stmtA.
  intros until U. intros HH HK MX MA SXA NST NGA NG1 NGU0 NGU NGZ OA CRA CRAL XW BB XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA IA1 IA2 BUD UW UWX UWA BUDF C24H WB1 WB0 -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 96 (aa_frame96 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  pose proof MA as [(_ & _ & _ & _ & NRA & _) _]. unfold MPI_MAX_LIMBS in NRA.
  eapply mi_main with (b := b) (U := U); try eassumption.
  all: try exact (uw_obj_nonneg _ _ _ _ UWX).
  all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "SPEC-LEFT:" g end ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
