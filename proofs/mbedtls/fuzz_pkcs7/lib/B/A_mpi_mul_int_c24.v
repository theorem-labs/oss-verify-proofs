(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_copy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_zeroize_and_free A_mpi_copy A_mpi_core_mla A_mpi_add_abs_W A_mpi_lset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_journey_c24 A_mpi_copy_c24 A_mpi_mul_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_mul_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_mul_int_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int.mul_int_Rz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int.mul_int_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int.mul_int_FR"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "WM.MI_FRAME_A"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "WM.MI_POST_A"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey2.rideA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "WM.miV1"; "WM.miF1"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.shiftr"; "WM.KC_stmt"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WM.copy_self_postA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_COPY"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_opnd.opnd_atA"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JBA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.BJA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_MUL_INT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy_c24.mpi_copy_stmtA_c"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int.A_WRAP_CALLOC_MI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int.A_ASAN_MEMCPY_MI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int.A_ASAN_MEMSET_MI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int.mpi_mul_int_stmtA"].


(* [comment removed for export] *)



Section WM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis COPY : mpi_copy_stmtA_c asegs R HIA A_MPI_COPY.
  Hypothesis LSET : mpi_lset_stmtA_v asegs R HIA A_MPI_LSET.
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
  Hypothesis UWC0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BB : 0 <= b < 2^32.
  Hypothesis WB1 : bv_unsigned wb mod 2^32 = b.
  Hypothesis WB0 : bv_unsigned wb = 0 <-> b = 0.
  Hypothesis NRA : 0 <= md_n dA <= 10000.

  Definition MI_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_c24 ()) "(0.$1.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(3.Vb,VLB,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)(4.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)(5.Vd,)Vlo,Vm,Vmo,)")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L19687428440.145L25465666776.145L28125529944.145L29025845208.145L29428324939.5  L29762660275.145L31686769240.145L35663928186.7  L36180290948.1  L52253708504.145L60098763854.3  L60511538335.145L60692334296.145L61601561944.145L62505661912.145L64270350808.145L65178513496.145L947156799.144  Q15643598972.145Q18366170748.145Q18378508831.145Q21879891999.145Q24389844383.145Q27585188988.145Q27906956191.145Q30415318815.145Q31271277308.145Q32655747964.145Q33918012703.145Q36425601695.145Q3830178207.145 Q39939305631.145Q41152143740.145Q44648563964.145Q4533800828.145 Q51235551740.145Q52101417212.145Q59257011708.145Q59842863100.145Q60511538335.145Q66521824799.145Q9843086111.145 00000@00P00`01001B01R01b02702;02K02U03;03K03[03k04;04K04[04k05;05Z06906X06h07G07f08608F08e09D09c0:B0:R0:b0;20;B0;R0;b0<20<Q0=00=OS2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S1R2lo3LOS3ALO3ACPS2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S1R3HIA1h2sp2lo3TOP1HS2spS2ra2sp1b2wb3WB0S1R2lo3LOSS1R2ra2sp2lo1b2wb2BB3WB05NEEDR3SLO3SPRS2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2ra2sp1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S2sp2lo1b2wb3WB0S1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLOS1R2sp2lo1b2wb2BB3WB05NEEDR3SLO". (* [comment removed for export] *)
  #[using="IMG wb JC BB WB0"] Lemma mi_ret : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (r : Z)
      (xra xt0 xt1 xt2 xs0' xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [] v f hc LBc mc dXc ->
    (r = 0 /\ (b = 0 -> mpd_val dXc = 0) /\ md_n dXc <= Z.max nX (md_n dA + 1)) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED ->
    v <= mul_int_PHI dX dA -> f <= mul_int_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) MI_POST_A
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp xt0 xt1 xt2 xs0' xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 (Z_to_bv 64 r) xs6 xs7 xs8 xs9 xs10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9cbb8) fc None mc (seg_rom asegs))
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
    zstep. do 12 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold MI_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis BUD : havol asegs R HIA h + mul_int_PHI dX dA <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + mul_int_FR d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 272 - arl_need_rt R.
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Local Notation SH10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Local Notation SHA := (Z_to_bv 64 (Z.shiftr (md_addr dA) 3 + al_sb AL)).
  Local Notation XJ1 An cnt := (XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [(An, 4 * cnt)]).
  Local Notation FB0 := (FBA asegs R LB LF dX lo).
  Local Notation XD0 := (XDA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A).
  Local Notation RIDE := (rideA R HIA LB LF m dX sp lo dA).
  (* [comment removed for export] *)
  Definition miV1 : Z := grow_PHI (md_n dA + 1).
  Definition miF1 : Z := calls_FR 2 d.
  Local Ltac xa_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  Definition KC_stmt (n : Z) : Prop := forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs10 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [] v f hc LBc mc dXc ->
    rideA R HIA LB LF m dX sp lo dA hc LBc mc dXc ->
    md_own dXc = LHeap -> n + 1 <= md_n dXc -> md_n dXc <= Z.max nX (n + 1) -> v <= miV1 -> f <= miF1 ->
    aevtA asegs (KF asegs R HIA hc mo) MI_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 n) (Z_to_bv 64 (X + 10)) (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA))
             xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 SB SHA SH10 wb xs10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9cb68) fc None mc (seg_rom asegs))
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04F0@C17025492443.258C17025492443.259C17025492443.260C53526081063.261C53526081063.262C53526081063.263D17975678776.264D21361708665.198D22466435734.264D24976250634.220D24976250634.293D27965255826.288D34348047352.196D34348047352.198D34352354649.282D34352354649.284D34352354649.289D37969448224.283D37969448224.290D50797141399.220D50797141399.221D50797141399.293D52014138856.220D52014138856.221D52014138856.293D59228252318.293D60109446735.264D62155808737.221D62155808737.293D7340709316.264 D8414535367.288 D939044794.264  K1329197271.261 K1329197271.262 K1329197271.263 K2612272047.260 K2612272047.264 K32761642720.260K32761642720.264K38856059124.294K61206821897.221K61206821897.293K61206821897.294K6379668000.258 K6379668000.259 K6379668000.260 K7412424035.264 L10947173192.14 L12755534717.10 L12755534717.9  L1342025005.3   L14748712526.18 L14751320984.1  L14760987928.8  L1511883768.1   L16473205958.6  L16473494895.4  L17585880332.14 L17979450399.5  L19279770932.10 L20558904555.4  L20803911415.2  L2166243551.4   L21847519070.3  L21848002076.18 L21860433226.8  L21860695708.34 L22479292268.1  L2297886500.5   L23075920487.7  L23100341967.209L23100341967.214L23100341967.246L23100341967.279L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.7  L25044269509.2  L25046775673.245L25047280258.234L25511149886.4  L25560626977.4  L2607826517.4   L26950159893.14 L27214106967.5  L27481632834.8  L27481632834.9  L27557763503.2  L27966909654.1  L28655862141.3  L32756788865.4  L32761511569.8  L34412813842.36 L34424803280.3  L35655538624.7  L35655538630.7  L35663928186.7  L36180290948.1  L37969005188.5  L38235734261.1  L38240354370.4  L38868673902.3  L38868673902.5  L39172636981.0  L39436426759.7  L40294887048.3  L40449602357.4  L41112120439.34 L41112120439.36 L41116237108.1  L41389564045.11 L43289142152.4  L43625157983.1  L43631939593.36 L43878034250.5  L45199987735.198L46160487540.214L46160487540.235L46160487540.280L46380960401.4  L46756382136.209L46948640662.36 L48003016234.1  L48154966246.209L49578233423.214L49578233423.279L49579218529.36 L49807695752.8  L5098421631.4   L51211863758.10 L5259801613.208 L5261871668.3   L542086852.34   L547707976.3    L57258774030.15 L59308633593.3  L59308972243.3  L60098763854.3  L60345419574.290L60858800200.1  L61212928741.14 L61562785068.34 L62018535662.1  L63070224179.4  L63070715826.18 L63074667748.10 L63074930482.36 L63408433385.7  L63442736301.15 L6384586821.2   L64600040930.4  L64811930313.11 L64934269637.2  L65708990832.34 L66661851587.4  L67601363691.1  L7400112281.3   L7419031306.34  L7484103457.0   L8414648675.5   L9951453048.12  O17025492443.258O17025492443.259O17025492443.260O22987107037.260O22987107037.264O32329373691.264O37539299629.258O37539299629.259O37539299629.260O41427663046.263O45218884275.260O45218884275.264O53526081063.261O53526081063.262O53526081063.263P1329197271.261 P1329197271.262 P1329197271.263 P38856059124.221P38856059124.294P40437264079.258P40437264079.259P40437264079.260P57246471156.263P6379668000.258 P6379668000.259 P6379668000.260 P7412424035.264 Q12370813529.213Q12370813529.218Q12370813529.255Q12370813529.290Q17205055869.289Q17205141463.217Q17207432298.212Q17207432298.254Q17975678776.264Q22466435734.264Q24974040330.220Q24974040330.293Q26207421841.217Q26207421841.243Q26207721832.218Q26207721832.244Q26207721832.291Q26207967338.215Q26207967338.254Q26207967338.288Q26209519061.290Q26209835253.241Q31651985788.290Q31653536963.254Q31654082872.217Q31654082872.243Q37623358517.217Q37623376543.289Q37625261960.212Q37625261960.254Q38248387216.264Q39212284437.218Q39212284437.244Q39212284437.291Q42081808994.218Q42081808994.291Q42250421143.185Q42250421143.279Q42250505353.244Q42252699699.261Q42252699701.167Q43879899724.264Q43925228937.218Q43925228937.244Q43925228937.291Q52016320488.220Q52016320488.292Q52016320488.293Q5483308162.289 Q5483358760.217 Q5485126037.212 Q5485126037.254 Q5485174314.213 Q5485174314.218 Q5485174314.255 Q5485174314.290 Q6027349519.220 Q6027349519.221 Q6027349519.292 Q6027349519.293 Q60511567613.218Q60511567613.244Q60511567613.291Q60697995187.218Q60697995187.244Q60697995187.291Q6143569392.213 Q6143569392.218 Q6143569392.255 Q6143569392.290 Q62157788641.220Q62157788641.292Q62965564504.219Q62965564504.291Q62965564504.292Q63442345212.288Q68317669980.285Q68317669980.286Q68317669980.287Q68330333437.197Q7891539809.218 Q7891539809.290 Q8880503606.215 Q8880503606.288 Q8882895785.241 Q9538787269.215 Q9538787269.288 Q9540589402.241 00000100200300400500601?01X02H03503o04Z04[04\04]04^04_04`04a06007=08\09I0:40:n0:o0;k0<V0=P0=Q0=R0>V0>W0>X0>Y0?P0@G0AJ0BM0BN0CS0Di0F40F50F60F70F80F?0F@0FA0FB0FR0FS0FT0FW0Fi0Fj0Fk0G90GH0GP0GQ0Ga0Gb0H90H:0HP0HT0Hb0I10IM0Ii0JK0K60K@0KM0KN0KO0KX0LE0M<0MJ0MX0MY0MZ0Mj0Mk0Ml0N20N60N70N80NL0NZ0N[0O60OQ0Of0Oj0Ok0Oo0P:0P;0P<0P=0PS0PV0PW0Pc0Po0Q00Q10Q@0QA0QZ0Qa0R:0R`0SZ0TO0TP0U_0VH0VK0VL0Vh0WS0X:0X;0XQ0XR0Y80YB0YP0YZ0Y[0Yf0Z10Z;0Zf0Zj0Zk0[T0[W0[X0[j0[k0\=0\L0\M0\N0\Y0\n0]70]D0]T0]Y0]Z0^A0^B0^C0^D0^E0^F0^G0^H0^I0^J0^K0^L0^M0^N0^O0^P0^Q0^R0^S0^T0^U0^V0^W0^X0_Q0`J0aC0bQ0bR0bS0bT0bU0c;0ca0dM0eB0e`0f30fF0f[0gJ0gn0hR0i?0iR0j50jH0jk0kI0k\0l10lO0lm0mP0mn0nC0nV0o90oL0oj10=10R11611I11l12J12f13M14E15H16S17V18N19519H19k1:I1;01;`1<M1<k1=>1=Q1=f1>91>L1>a1??1?c1@H1A51Ae1B61BW1C31CL1D51DY1Dl1E?1ET1F21FW1GG1Gj1HX1IF1JG1JH1JI1JJ1JK1Jg1KN1Ka1L?1Lb1M31MO1N0FFFFFFS2ra2sp1X3xs01b2wb2BB3WB01n3nXc3pXc2xs2X03SPR2An3An02N12P04Fcnt4SLEN4DLENS2ra2sp1X3xs01b2wb3WB02xsS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4SLEN4DLENS2ra2sp1X3xs01b2wb3WB01n2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4ZLENFFFFFFFS1R2ra2sp1X3xs02lo1b2wb2BB3WB04SLO21n2xs5NEEDR3LOS2X03SPR2An3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo1b2wb2BB3WB04SLO22xs5NEEDR3LOS2X03SPR2An3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo1b2wb2BB3WB04SLO21n3nXc3pXc2xs5NEEDR3LOS2X03SPR2An3An02P04ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs01b2wb3WB01n2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs01b2wb3WB02xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo1b2wb2BB3WB01n3nXc3pXc2xs3LOS2An4SLEN4DLENS2ra2sp1X3xs01b2wb3WB02xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stFFS1R3HIA2ra2sp1X3xs02lo1b2wb2BB3WB01n3nXc3pXc2xs2h22An4TOP24SLEN4DLENFFFS3xs01b2wb2BB3WB01n3nXc3pXc2xs4LEN12An2N14SLEN4DLEN3SEPS3xs01b2wb2BB3WB01n3nXc3pXc2xs4LEN12An2N14SLEN4DLEN3SEPS1R2sp3xs02lo1b2wb2BB3WB01n3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo1b2wb2BB3WB01n3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENFS1R2sp1X3xs02lo1b2wb2BB3WB04SLO21n2xs5NEEDR3FSZ3DSX2HB5Ha_st5Hl_st2AnS1R2sp1X3xs02lo1b2wb2BB3WB04SLO21n3nXc2xs5NEEDR3FSZ3DSX4LEN12An2N14ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo1b2wb2BB3WB04SLO21n3nXc2xs5NEEDR3FSZ3DSX4ZLEN2HB5Ha_st5Hl_stFFFFS2sp2loFFFS2sp3nXc3SPR3NR1FFS1nS1n3nXc3CNT2An3A47FFS1n3nXc3CNT2AnS2dA1n1v3N1A2BVS1d1f2BFFS3nXc2xs4LEN12N1FS1R2sp2lo4SLO24NRAm3SPRFS1R2sp2lo4SLO23NRM3SPRS2AnS1n3nXc3CNT2AnS2dA1n1v3N1A2BVS2ra2sp1X3xs01b2wb3WB02xs2AnS2ra2sp1X3xs01b2wb3WB02xs2AnS2ra2sp1X3xs01b2wb3WB01n3pXc2xs2AnS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4ZLENS1R3HIA2hcS3nXc3pXc3P47FFS3nXc3NR1S2ra2sp1X3xs01b2wb2BB3WB01n3nXc3pXc2xs3NR12AnS2ra2sp1X3xs01b2wb2BB3WB01n3nXc3pXc2xs3NR12An4SLEN4DLENS1n3nXc3CNT2N1S1n3nXc3CNT2N1FFS1R3HIA1h2sp3TOPFFS2nX1nS2spFFS2sp2lo3nXc3pXc4XLScS1R2sp2lo4SLO2FS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HS2spFS2loS1d2D01f2BFFFSS1R3nXc3pXc2N12P02PC1HS1XFS2sp3SPA3SPRS2sp3SPA3SPRFFS1n3nXc3CNT3N10FS2sp1n3nXc3CNT3N103SPR2N1S2sp2loS2ra2sp1X3xs01b2wb3WB02xsS2ra2sp1X3xs01b2wb2BB3WB02xs2X03X162AnS2ra2sp1X3xs01b2wb2BB3WB01n3nXc3pXc2xs2X03X162An4SLEN4DLENS2ra2sp1X3xs01b2wb2BB3WB01n3nXc3pXc2xs2X03X162An4ZLENFS1R2ra2sp1X3xs02dA2lo1b2wb2BB3WB04SLO21n2xs3N1A5NEEDR3LOS2X03ALO3SPR2An3An03AnCS1R3HIA1h2sp2dA3BUD1n1v3N1A2BV3SPR2h23HV1S1nFS2ra2sp1X3xs01b2wb3WB02xs2AnS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4ZLENS1R3HIA1h2sp1d2D04BUDF1f2BF3SPR2h24HFR1FS1n3nXc3CNT2N12xs4LEN1FS2ra2sp1X3xs01b2wb2BB3WB02xs2X03X162AnS1X2X03X16S2sp1n3N103SPRS1R3HIA2h2FS2An3An02KZS3pXc2KP2P0S1R2lo3LOSS2ra2sp1X3xs01b2wb3WB01n3nXc3pXc2xs2An4ZLENS2spFS1R3HIA1h2sp2dA3BUD1n1v2hc3N1A2BV3SPR3HV1S1RFS1R3HIA2sp2h24TOP2FS1R3HIA2sp2h24TOP2S2dA1n1v3N1A2BVFFS1d2D01f2BFS2lo1n3nXc3CNT2An3FloS3nXc3NR1S2sp2dA1n3N1AS3nXc3pXc2An3SEPS3nXcFS1R3HIA1h2sp1d2D04BUDF1f2hc2BF3SPR4HFR1SFFFFFFFFFFFFFFFFFFFFFFS2sp3xs02lo1b2wb2BB3WB01n3nXc2xs2An2N14Fcnt3Flo4SLEN4DLENS2sp3xs02lo1b2wb2BB3WB01n3nXc2xs2An2N14Fcnt3Flo4SLEN4DLENS2sp3xs02lo1b2wb2BB3WB01n3nXc2xs2An2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo1b2wb2BB3WB04SLO21n3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENFFFFS2ra2sp1X3xs01b2wb2BB3WB02xs2X03XAL2AnS2ra2sp1X3xs01b2wb2BB3WB02xs2X03XAL2AnS2ra2sp1X3xs01b2wb2BB3WB01n3pXc2xs2X03XAL2AnS2ra2sp1X3xs01b2wb2BB3WB01n3nXc3pXc2xs2X03XAL2An4ZLENS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n2xsS3xs01b2wb2BB3WB01n3nXc2xs2An2N14Fcnt4SLEN4DLENS3xs01b2wb3WB01n3nXc2xs2An4SLEN4DLENS1X3xs01b2wb3WB01n2xs2HB5Ha_st5Hl_stS1X3xs01b2wb3WB01n3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n2xsS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB01n2xsS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n2xsS3xs02lo1b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb2BB3WB02xs2X02HBS1X3xs01b2wb2BB3WB01n3nXc2xs2X04ZLEN2HBS1R2sp3xs02lo1b2wb2BB3WB04SLO22xs5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo1b2wb2BB3WB04SLO21n3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo1b2wb2BB3WB04SLO21n3nXc2xs5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo1b2wb2BB3WB04SLO21n3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo1b2wb2BB3WB04SLO22xs5NEEDR3LOS4SP643ALO3ACPS2sp3xs02lo1b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB01n2xs2HB5Ha_st5Hl_st2AnS1X3xs01b2wb3WB01n3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs01b2wb3WB01n3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n2xsS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n2xsS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB01n2xs2HB5Ha_st5Hl_stS1X3xs01b2wb3WB02xs2An2HB5Ha_st5Hl_stS1X3xs01b2wb3WB01n3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs01b2wb3WB01n3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS3xs01b2wb3WB02xsS3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb2BB3WB02xs2X0S1X3xs01b2wb2BB3WB01n3nXc2xs2X04SLEN4DLENS1X3xs01b2wb2BB3WB01n3nXc2xs2X04ZLENS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n2xsS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB02xs2An2HB5Ha_st5Hl_stS1X3xs01b2wb3WB01n3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs01b2wb2BB3WB02xs3X162HB5Ha_stS1X3xs01b2wb2BB3WB01n3nXc2xs3X164ZLEN2HB5Ha_stS1X3xs01b2wb2BB3WB01n3nXc2xs3X164ZLEN2HB5Ha_stS1R2sp3xs02lo1b2wb2BB3WB04SLO21n3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENFFFFS1X3xs01b2wb2BB3WB02xs2X02HBS1X3xs01b2wb2BB3WB01n3nXc2xs2X04ZLEN2HBS1X3xs01b2wb3WB02xsS1X3xs01b2wb3WB01n3nXc2xs4ZLENS1X3xs01b2wb3WB01n3nXc2xs4SLEN4DLENS3xs01b2wb3WB02xsS3xs01b2wb3WB01n3nXc2xs4ZLENS3xs01b2wb3WB01n3nXc2xs4SLEN4DLEN". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC C24H JC TPV UWX D0 BB WB0 BUD BUDF SLO2"] Lemma mi_G1 : forall (n v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs10 xt3 xt4 xt5 xt6 : word),
    KC_stmt n ->
    XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [] v f hc LBc mc dXc ->
    rideA R HIA LB LF m dX sp lo dA hc LBc mc dXc ->
    1 <= n <= md_n dA -> md_n dXc < n + 1 -> n + 1 <= 10000 -> v <= 0 -> f <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo) MI_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 n) (Z_to_bv 64 (X + 10)) (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA))
             xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 (Z_to_bv 64 (-16)) SB SHA SH10 wb xs10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9cacc) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros K1 J RA N1A CNT N10 BV BF. jc_open. unfold KC_stmt in K1.
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
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := n + 1) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
      all: try ((intros _; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ])).   (* [comment removed for export] *)
      all: try (apply uwc_data; [clear - D0; lia| rewrite unsigned_lit by (clear - N10 N1A; lia); pose proof (alloc_ceiling_val R) as ACV; clear - N10 N1A ALO ACV; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: unfold mul_int_PHI, mul_int_FR, copy_PHI, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT N1A N10 NR1 NR NRA LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof ST2 as ST2'.
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros bq Hb; exact Hb| intros bq Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep.
      eapply mi_ret; [exact J2| right; reflexivity| |].
      + unfold mul_int_PHI, copy_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT N1A N10 NRA NR1. lia.
      + unfold mul_int_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace ((n + 1) * 4) with (4 * (n + 1)) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An (n + 1) J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT N10; lia)) as [J2 F2].
      pose proof (rideA_transport R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC dA _ _ _ _ _ _ _ _ _ _ J RA HP2' MI2 HCS2 HH2 ltac:(intros b' Hb; right; exact Hb)) as RA2.
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J RA. try clear MI1; try clear ST1; try clear STc; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1;
      try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1; try clear CX1; try clear OWN0;
      try clear OWN1.
      xa_open J2.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      zstep. zstep.
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
        pose proof (rideA_finish R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC dA _ _ _ _ _ _ _ _ _ _ D2 RA2 MU WM) as RA5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA5.
        eapply K1; [exact J5| exact RA5| reflexivity| cbn [md_n]; clear; lia| cbn [md_n]; clear; lia| |].
        * unfold miV1, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT N1A. lia.
        * unfold miF1, calls_FR, fr_charge in *. clear - BF D0. lia.
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
        replace (Init.Nat.min (Z.to_nat nXc) (Z.to_nat (n + 1))) with (Z.to_nat nXc) in DST, DLEN by (clear - CNT N1; lia).
        assert (LQ : Z.land (Z.lor pXc An) 3 = 0).
        { rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2). rewrite !Z.land_ones by (clear; lia). change (2 ^ 2) with 4.
          replace (pXc mod 4) with 0 by (clear - XPAL; Z.div_mod_to_equations; lia).
          replace (An mod 4) with 0 by (clear - A16; Z.div_mod_to_equations; lia). reflexivity. }
        zstep. zstep. zstep. if_cases KQ; zify_cond KQ; [exfalso; clear - KQ LQ; rewrite ?LQ in KQ; rewrite ?Zmod_0_l in KQ; lia|].
        (* [comment removed for export] *)
        shadow_chk OX1 (X + 10) 2.
        zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_MI) as SPC. unfold A_ASAN_MEMCPY_MI in SPC.
        apply (u8arr_of_rw_cells asegs) in DST.
        (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl [(An, An + 4 * nXc); (lo, bv_unsigned sp + -96)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        acallxA_sp (bv_unsigned sp + -96)
          (eapply SPC with (h := h2) (LB := (An, 4 * (n + 1)) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * nXc) (lo := lo)
                            (ss := u32s xs);
           rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
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
                 | clear - NR1 N1 CNT LOS SLO SLO2 NEEDR NRAm TOP2 SPA SPR; lia
                 | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ] ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
        pose proof ST3 as ST3'.
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        replace (4 * length xs)%nat with (Z.to_nat (4 * nXc)) in HPA by (clear - LEN1 N1; lia).
        destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
        assert (WC3 : w_client (hcs asegs R HIA h2) [(An, An + 4 * nXc); (lo, bv_unsigned sp + -96)]).
        { unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OA| clear; lia| clear - CNT N1; lia]|].
          apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]| apply Forall_nil]. }
        pose proof (rideA_fresh_munch R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC dA _ _ _ _ _ _ _ _ _ (4 * nXc) m3 (bv_unsigned sp + -96) J2 F2 RA2 ltac:(clear - CNT N1; lia) ltac:(clear; lia) MU WM WC3) as RA3.
        clear J2 F2 RA2 WC3 OA OP' SBY SLEN DLEN INA INP.
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear
        PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs
        md_pad md_own] in *.
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
          eapply SPZ with (h := h2) (LB := (An, 4 * (n + 1)) :: LBc) (LF := LF) (buf := pXc) (len := 4 * nXc) (lo := lo) (d := d) (junk := u32s xs);
            rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
          all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
          all: try (apply uwc_data; [clear - D0; lia| rewrite unsigned_lit by (clear - N10 N1A; lia); pose proof (alloc_ceiling_val R) as ACV; clear - N10 N1A ALO ACV; lia]).
          all: try (f_equal; clear; lia).
          all: unfold mul_int_PHI, mul_int_FR, copy_PHI, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
               clear - CNT N1A N10 NR1 NR NRA N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
          all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end ]. }
        clear SPZ.
        (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
        destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
        ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
        match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
        presA_transport HP4.
        pose proof ST4 as ST4'.
        assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * (n + 1)) :: LBc)) LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA h2)
                         [(pXc, pXc + 4 * nXc)] m3 m4).
        { eapply presA_weaken; [exact HP4| intros bq Hb; exact Hb| intros bq Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
        pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
        pose proof (rideA_zfree R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC dA _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 RA3 eq_refl HP4' MI4 HCS4 HH4) as RA4.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4, RA4.
        assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
        apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
        clear CSOK SB64 SCS0 SCS HTOP2.
        pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
        assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear
        PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 RA3 HP4 HP4'. try clear ZCH; try clear ZB;
        try clear XARR; try clear OP; try clear HH2.
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
        pose proof (rideA_finish R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC dA _ _ _ _ _ _ _ _ _ _ D4 RA4 MU WM) as RA5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA5.
        eapply K1; [exact J5| exact RA5| reflexivity| cbn [md_n]; clear; lia| cbn [md_n]; clear; lia| |].
        * unfold miV1, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT N1A. lia.
        * unfold miF1, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MIG1-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02a0@C24112444547.210D19095312002.208D22752211978.214D30202740417.208D30213615715.214D38874475859.214D42633159082.208D42643779336.214D601287770.208  D62012212072.214K11420089551.210K25384422162.211K28284592895.209K41585169438.209K47544724259.213K47544724259.215K52581815936.211L11092957035.11 L11093884473.5  L11093884473.6  L11416546478.3  L1286294210.5   L14245130797.3  L14249998533.4  L15167829154.4  L15169948178.7  L15180368418.3  L17803185913.5  L17809411522.9  L17813258712.7  L17813606089.8  L17815712639.11 L17815810169.6  L21273698895.4  L21286247631.5  L21286346697.10 L21288444543.7  L23100341967.191L23560010593.8  L23561906969.8  L23643762344.4  L25399627235.15 L25721347477.8  L25735831525.8  L25881510713.2  L2625810293.3   L28270437390.4  L29534616704.4  L2975768925.2   L29763661393.2  L3481485179.12  L3482279739.6   L3482279739.7   L3482279739.8   L35065298922.8  L35069606260.5  L35663928186.7  L36145034931.8  L36147066499.10 L36147132693.8  L36147476882.8  L36149152565.14 L36149250099.8  L36180290948.1  L38235734261.1  L38330469153.0  L39363785272.11 L39363785272.9  L39364434794.16 L39569505368.7  L41112052343.4  L41114152401.6  L41114214983.6  L41114660182.5  L41116278007.4  L41128898453.2  L41580512891.2  L42633816569.1  L43631404864.4  L43878034250.5  L46160487540.191L4735037479.2   L4735039273.4   L47532522306.4  L47534962651.4  L47784804765.4  L47795356077.6  L47797436189.4  L51284464315.191L52592168972.2  L5259801613.188 L54434634207.8  L54473544495.13 L58609956177.2  L58720988025.3  L59310763475.5  L60098763854.3  L60283674290.9  L60445729592.5  L60447858056.4  L61263298563.1  L61429820693.1  L62228711352.6  L66151427842.16 L66151427842.17 L9285596192.5   L9287758864.7   L9289747104.5   L9289845158.11  O22331808284.212O24112444547.210O24729331311.213O24729331311.215O27573497883.209O31435371494.211O35105909750.211O54539614568.209P11420089551.210P14260335836.212P41585169438.209P47544724259.213P47544724259.215P52581815936.211Q10045260807.197Q12370813529.196Q17207350632.197Q1738401673.219 Q18347242623.216Q21831343660.198Q22752211978.217Q22752211978.218Q22752211978.219Q26207421841.197Q26207721832.198Q26207967338.195Q30213615715.217Q30213615715.218Q30213615715.219Q31222125165.218Q31222125165.219Q31654082872.197Q37625261960.195Q38874475859.217Q38874475859.218Q38874475859.219Q39212284437.198Q40278613695.196Q42252534531.198Q42643779336.217Q42643779336.218Q42643779336.219Q43925228937.198Q45875552310.217Q45875552310.218Q45875552310.219Q47588311916.215Q47588311916.216Q5485126037.195 Q5485174314.196 Q5485600919.197 Q59703481013.196Q60511567613.198Q60697995187.198Q61263535092.197Q61264001456.198Q6143569392.196 Q61465870571.196Q66375044744.198Q67329605699.197Q8222473558.198 Q8880503606.195 Q9285269895.217 Q9285269895.218 Q9285269895.219 Q9538787269.195 Q9827600259.215 Q9827600259.216 00000101M01N02C02n02o03b04K05f06Q06R07S08I08J08K08L08M08N08O08P08Q08b08c08o09009109<09=09>09?09@09A09B09C09D09E09F09o0:M0:N0:[0:\0;;0;<0;=0;F0;G0;U0;\0;c0;d0;e0;f0;g0<50<E0<Z0<[0<\0<]0<^0<_0<`0<d0<h0<i0<j0<k0<l0=F0=G0=H0=I0=U0=V0=W0=X0=]0=j0>10>d0>k0?80?90?:0?;0?<0?=0?f0?g0@Z0A90A=0AD0AN0A`0Aj0BI0B[0B\0B`0Bd0C80CT0CU0CV0CW0CX0CY0CZ0C[0C\0C]0C^0C_0C`0Ca0Cb0Cc0Cd0Ce0Cf0Cg0DA0E40EP0EQ0ER0ES0ET0EU0EV0F20FN0Fj0GJ0Gj0HJ0HK0HL0Hh0ID0IE0IF0IG0Ic0Id0Je0KC0Ka0L?0L[0L\0L]0L^0L_0L`0M<0MX0N40N50NO0O10OK0Oe0PA0PB0P\0Q60R50RQ0RR0RS0RT0Rn0Ro0S0FS1R2ra2sp1X2nX3xs02dA2lo1b2wb2BB3WB04SLO23pXc2xs5NEEDR3LOS2X03SPR2P02pe2ys3EP03E0'4xs6l4LEN6FS2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2pe2ys4xs6l4LEN6S2ra2sp1X2nX3xs02dA1b2wb3WB01N3pXc2xs2pe2ysFS2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ys4xs6l4LEN6S2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysS1R3HIA1h2ra2sp1X2nX3xs02dA1b2wb2BB3WB02hc3pXc2xs3TOP2X03SPR3HT12P02pe2ys3EP03E0'4xs6l4LEN6S1R2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysFS1R2sp2nX3xs02dA2lo1b2wb2BB3WB04SLO21N3pXc2xs5NEEDR3LOS3ALO2PC2ysS1R2sp2nX3xs02dA2lo1b2wb2BB3WB01N3pXc2xs3LOS3ALO2PC2ysFFFFFFFFS1n1N2xs3HNX4LEN1FS2dA1N3pXc1KFFS1N2xs4LEN1FFFFFFFFFFS2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysS1R2sp2lo4SLO25NEEDR2pe2ys3ESKFS1X1N3pXc3XPcFS1R2sp2lo4SLO21N3pXc5NEEDR4XLScFFS1n1N3HNXFS2dA1n3HN13HNAS1N3pXcS1N3NR1FFFFS1R1N3pXc2PC1HS1R1N3pXc2PC3ACVS1R3HIA1h2sp2lo3TOP1HFFFFFFS2spS2loSFFFS1R2sp1X2lo4SLO25NEEDR3DSXFFFS2sp3SPA3SPRFFFS3pXcS1n1N3pXc3HNXS2sp2loS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03X162pe2ysS2dA2HIS1R2dA3ACV2HCFFFFFS2ra2sp1X2nX3xs02dA1b2wb3WB03pXc2xs2pe2ysFS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03X162pe2ysS1R2sp2lo4SLO21N3pXc5NEEDR4XLScS2spS1N3NR1S2dA1n3HNAS2dA1n3HN13HNA3EZ0S1R2lo3LOSS1R2sp2lo4SLO21N3pXc5NEEDR1a2NOS2dA3NRA1n3HN13HNAFS2dAS2spS1R2sp2lo4SLO25NEEDRS3pXc2r04XPAL1q1r1H2H02q02H4FFFFFFFFFFFFFFFFFFFS2nX3xs02dA1b2wb3WB02xs2ysS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03XAL2pe2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFFFFFFS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysS2nX3xs02dA1b2wb3WB01N3pXc2xs2ysS2nX3xs02dA1b2wb3WB01N3pXc2xs2ysS2nX3xs02dA1b2wb3WB01N3pXc2xs2ysFFS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFFFS1X2nX3xs02dA1b2wb3WB02xs2ysFS1R2sp2nX3xs02dA2lo1b2wb2BB3WB04SLO22xs5NEEDR3LOS4SP643ALO3ACV2ysS2nX3xs02dA1b2wb3WB03pXc2xs2ysS2nX3xs02dA1b2wb3WB03pXc2xs2ysS2nX3xs02dA1b2wb3WB03pXc2xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFFFFFS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFS2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb2BB3WB02xs2X02ysS2nX3xs02dA1b2wb3WB02xs2ysS2nX3xs02dA1b2wb3WB02xs2ysS1X2nX3xs02dA1b2wb3WB02xs2ysFS2nX3xs02dA1b2wb3WB02xs2ysS2nX3xs02dA1b2wb3WB02xs2ysS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03pXc2xs2X03SPR2P02pe2ys3E0'4EAL'S1X2nX3xs02dA1b2wb3WB02xs2ysFFFS2nX3xs02dA1b2wb3WB02xs2ysFF". (* [comment removed for export] *)
  #[using="IMG JC BB WB0 NRA SLO2"] Lemma mi_MLA : forall (n v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs10 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [] v f hc LBc mc dXc ->
    rideA R HIA LB LF m dX sp lo dA hc LBc mc dXc ->
    md_own dXc = LHeap -> 1 <= n -> n + 1 <= md_n dXc -> n <= md_n dA -> md_n dXc <= Z.max nX (md_n dA + 1) -> b <> 0 ->
    v <= mul_int_PHI dX dA -> f <= mul_int_FR d ->
    aevtA asegs (KF asegs R HIA hc mo) MI_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 n) (Z_to_bv 64 (X + 10)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) xs4 xs5 SB SHA SH10 wb xs10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9cb78) fc None mc (seg_rom asegs))
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
    zstep.
    eapply mi_ret; [exact J6| left; split; [reflexivity| split; [intros B0; exfalso; exact (BNZ B0)| cbn [md_n]; exact NMAX]]| exact BV| exact BF].
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "MLA-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition copy_self_postA (xra xsp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (lo0 : Z) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                  t3 t4 t5 t6) F (ret_pc xra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned xsp - 96, bv_unsigned xsp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo0 (bv_unsigned xsp)
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01F0@L10013191668.105L13679629912.105L13679629912.106L16024124020.105L20817808472.105L20817808472.106L22051162356.105L24693561020.104L29502821080.105L29502821080.106L37623267032.105L39788318758.99 L3991920500.105 L41391506051.105L42606771444.104L44235170136.105L44235170136.106L45988853080.104L45988853080.106L46254298584.105L46254298584.106L48636430708.105L53392477144.105L53392477144.106L54646761460.105L60674471028.105L62842592998.101L65656017752.105L65656017752.106L66683159284.105L7522693171.105 L7522693171.106 L8090362072.105 L8090362072.106 Q11040878936.105Q11047091911.104Q11801279589.107Q11801279589.108Q17057885511.104Q17059930840.105Q19565771207.104Q19567916632.105Q21542576304.105Q21548953391.104Q23077295192.105Q23083408327.104Q23580411907.106Q23580411907.107Q25586850776.105Q25593320519.104Q29094213191.104Q29096229336.105Q31988680623.104Q31990990896.105Q32464959152.105Q32471038255.104Q35115543384.105Q35122046151.104Q37623267032.105Q37629604167.104Q40016974384.105Q40019025327.104Q40550671471.106Q40550671471.107Q41141296344.105Q41143309127.104Q45469487279.104Q45471637296.105Q49698585326.105Q49698585326.106Q52876753840.105Q52878668847.104Q5300226131.104 Q5300226131.105 Q54126458602.105Q64997424432.105Q64999568047.104Q66001486466.107Q66245698095.104Q66252074416.105Q6697503024.105 Q6699665458.103 Q67723680344.105Q67725581146.103Q7198696624.105 Q7204776751.104 00000E00Z00o01D01Y01n02C02X02m03B03c04D04Y04n05C05X05m06B06W06l07A07V07k08@08U08j09?09T09i0:>0:S0:h0;=0;R0;l0<F0<g0=h0>B0>\0?60?P0?b0@40@N0@h0AU0B^0C80CR0Cl0DF0DX0Dj0E<0EN0Eh0FB0F\0G60GH0GZ0H?0ID0I^0J80JJ0J\0K:0KX0Kj0L<0LP0Ld0M80MJ0M\0NI0N[0Nm0O?0OQ0Ok0PE0PW0PiS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb2BB3WB03xra3xsp3lo04SLO0S2ra1b2wb2BB3WB03xra3xsp3lo04SLO0S2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS2ra1b2wb3WB03xra3xspS1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xra3xsp2HB5Ha_st5Hl_stS1b2wb3WB03xsp3xs12HB5Ha_st5Hl_st3xs23xs33xs43xs53xs63xs73xs83xs9S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xra3xsp3lo04SLO02HB5Ha_st5Hl_stS1b2wb2BB3WB03xsp3xs13lo04SLO02HB5Ha_st5Hl_st3xs23xs33xs43xs53xs63xs73xs8S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xra3xsp3lo02HB5Ha_st5Hl_stS1b2wb3WB03xsp3xs13lo02HB5Ha_st5Hl_st3xs23xs33xs43xs53xs63xs73xs83xs9S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3SPR2HB5Ha_stS1b2wb2BB3WB03xsp3SPR2HB5Ha_stS1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp2HBS1b2wb2BB3WB03xsp2HBS1b2wb2BB3WB03xsp2HBS1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3xs93lo04SLO02HB5Ha_st5Hl_stS1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb2BB3WB03xsp3lo04SLO0S1b2wb3WB03xsp3lo0S1b2wb3WB03xsp3lo0". (* [comment removed for export] *)
  #[using="HIA IMG ra b wb BB WB0"] Lemma A_copy_self : forall (CS : Z -> Prop)
      (xra xsp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 : word)
      (m0 : mem) (lo0 : Z),
    mem_inv asegs m0 -> stk asegs m0 lo0 (bv_unsigned xsp) -> lo0 <= bv_unsigned xsp - 96 -> 0 <= lo0 ->
    bv_unsigned xsp mod 16 = 0 -> cs_ok AL CS -> crange CS lo0 (bv_unsigned xsp - lo0) -> bv_unsigned xra mod 2 = 0 ->
    a0 = a1 ->
    evtA asegs AL CS (copy_self_postA xra xsp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 lo0 m0)
      (MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_MPI_COPY) fc None m0 (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until lo0. intros MI0 ST0 SLO0 LO00 SPA0 CSOK SCS RA0 ->. unfold A_MPI_COPY.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 xsp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
    (* [comment removed for export] *)
    zstep. carve_frame 96%nat ST0.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(bv_unsigned xsp - 96, bv_unsigned xsp)] mx) as MU; pose proof (wmono_refl asegs mx) as WM end.
    do 11 zstep.
    (* [comment removed for export] *)
    zstep. try (if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]).
    (* [comment removed for export] *)
    zstep. do 11 zstep. zstep.
    release_frame FR ST0 (bv_unsigned xsp).
    zstep.
    apply evtA_done. unfold copy_self_postA. deexists 14. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis MA0 : mpd_at asegs m LB dA.
  Hypothesis IA1 : md_addr dA <> X -> md_own dA = LStatic -> AImgGlobals.img_norz (md_p dA) (4 * md_n dA) = true.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@D24502936414.185D31131462022.185L14714961187.3  L16017091139.5  L17767589936.8  L18895178867.6  L19556266785.0  L21193854616.4  L21361983004.4  L23705426692.4  L26983617546.4  L27214106967.5  L27966909654.1  L28036980531.4  L28704391748.3  L29010569984.232L29428551881.9  L29971584610.3  L33150002250.3  L35663928186.7  L36180290948.1  L38005716811.3  L38235734261.1  L41114660182.9  L42252534548.5  L43675701464.3  L43878034250.5  L44801100179.4  L5541292479.5   L5545796159.9   L55529081155.6  L57263286428.9  L59308546259.8  L59308632561.1  L60098763854.3  L60858800200.1  L64491265552.2  L66151427842.16 L68690341806.10 L7693689550.4   L8288358478.2   00000l01i02302G02c03803903D03L03Z03f04604:04G04S04T04_04h05105F05J05S05W06706K06U06\06j07>07V07k08G08b08f09009409:09T0:10:>0:FS1R3HIA1h2ra2sp1X2nX3xs01b2wb2BB3WB01n2hc3dXc3TOP2X03SPR3HT1S1R2ra2sp1X2nX3xs02lo1b2wb2BB3WB04SLO21n3dXc5NEEDR3LOS2X03SPRS1X2dA3SXBS1R2sp2lo4SLO25NEEDRS2nX2dA1n2HN3dXc4NMAX3dX22CNS2nX2dA1n2HN3dXc4NMAXSS1d2D01f2BFS1d1f2BFS2sp2dA2lo3ESKS2dA2E01a2HaS1R3HIA1h2sp3TOPS2spS2dA3NRA1v2BVS2sp2lo4LOSPFS2sp2lo3LO0S2dA1n2HNS2dA1v2BVS1R3HIA1h2sp2lo3TOP1HS2spS2dA1n2HNS2loS1R2sp2lo4SLO25NEEDR3SPA3LO03SPRS2sp2lo3LO04LOSP3SPRS1X2dA3SXBS2sp2loS1R2sp2lo4SLO2S1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDR3SPRS2dA1n3dXc3HNX3dX22CNS1R3HIA1h2dA3BUD1v2hc2BV3HV1S2dA1n2HN3dXc3HNX3dX22CN2N0S2KRS1R2lo3LOSS2spS1d2D0S2sp2r03SPA1q1r1H2H02q02H4S1R3HIA1h1d4BUDF1f2hc2BF4HFR1S2sp2dA2lo2ESS2dA3NRA". (* [comment removed for export] *)
  #[using="IMG COPY C24H JC TPV UWX D0 BB WB0 NRA BUD BUDF SLO2 MA0 IA1"] Lemma mi_COPY : forall n, 1 <= n <= md_n dA -> b <> 0 -> KC_stmt n.
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
    zstep. zstep.
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
      replace (ret_pc (Z_to_bv 64 0x9cb70)) with (Z_to_bv 64 0x9cb70 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof HH1 as HH2.
      apply (hm_munch asegs R HIA hc LBc LF [(bv_unsigned sp + -96 - 96, bv_unsigned sp + -96)] mc m2) in HH2;
        [| exact MU2| exact WM2| solve_w_writable].
      pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m2 J MU2 WM2 MI2 ltac:(replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by (clear; lia); exact ST2) HH2
                    ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as J2.
      assert (EDX : mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) (md_limbs dXc) (md_pad dXc) (md_own dXc) = dXc) by (destruct dXc; reflexivity).
      rewrite EDX in J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep.
      eapply mi_MLA with (n := n); [exact J2| left; exact EAX| exact EO| clear - HN; lia| exact HNX| clear - HN; lia| | exact BNZ| |].
      + clear - NMAX HN. lia.
      + unfold miV1, mul_int_PHI, copy_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV NRA. lia.
      + unfold miF1, mul_int_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
      pose proof DBJ as [MB0 OB CRB CRBL SXB BIMG]. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_own md_p md_n] in SXB, OB1, OB2, OB3, OB4, OB5, AD1.
      pose proof (opnd_atA_mpd_back _ _ _ _ _ _ _ _ _ MA0 (bj_at _ _ _ _ _ _ _ _ _ _ B)) as MA1.
      destruct (bja_client _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ [] v f hc LBc mc dXc LBc lo J B ltac:(intros bq Hb _; exact Hb) ltac:(clear - LOSP; lia)) as [CRA1 CRAL1].
      pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
      pose proof COPY as CP. unfold mpi_copy_stmtA_c, mpi_copy_stmtA_gen_c in CP.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply CP with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (dY := dA) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by exact SPR'; rewrite ?AD1;
          first [ exact HH1 | exact HK1 | exact MX1 | exact NS1 | exact MA1 | exact CRA1 | exact CRAL1 | exact ST1 | exact LOS | exact TPV | exact MI1 | exact OX1 | exact UWX | reflexivity
                | exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)
                | lazymatch goal with
                  | |- mpd_sep dXc dA => right; rewrite AD1; clear - SXB; lia
                  | |- copy_sep dXc dA _ _ =>
                      unfold P_mpi_copy.copy_sep; rewrite ?AD1;
                      split; [exact OB1|]; split; [exact (bj_sepS _ _ _ _ _ _ _ _ _ _ B)|];
                      split; [right; destruct (md_own dA) eqn:EOA; [right; left; reflexivity| |];
                              right; right; apply (bj_sepL _ _ _ _ _ _ _ _ _ _ B EO); first [discriminate| rewrite EOA; discriminate]|];
                      split; [clear - ES; lia|]; split; [intros AN; ddestruct (OWNE1 AN) as (_ & _ & _ & _ & ESK & _); clear - ESK; lia| intros a Ha; clear - Ha E0; lia]
                  | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear; lia| rewrite AD1; exact XP1]
                  | |- _ <= bv_unsigned sp + -96 - 112 - _ => clear - SLO2; lia
                  | |- bv_unsigned sp + -96 <= htop _ _ _ _ => rewrite HT1; clear - TOP; lia
                  | |- (bv_unsigned sp + -96) mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                  | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                  | |- md_own dA = LStatic -> _ => intros EOA; apply IA1; [clear - SXB; lia| exact EOA]
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold miV1, mul_int_PHI in *; clear - BV BUD HV1; lia
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold miF1, mul_int_FR, copy_FR, calls_FR, fr_charge in *; clear - BF BUDF HFR1 D0; lia
                  end
                | first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end ] ]. }
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HP2 by exact SPR'. rewrite AD1 in HP2.
      replace (ret_pc (Z_to_bv 64 0x9cb70)) with (Z_to_bv 64 0x9cb70 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof ST2 as ST2'.
      unfold P_mpi_copy.copy_R in CR. ddestruct CR as (CR1 & CAD & CPD & CFR).
      assert (BK : binop_keep LBc dXc dX2).
      { split; [exact CAD|]. split; [exact CPD|]. split; [exact CFR|]. destruct CR1 as [(_ & _ & Bn & _)|(_ & En & _)]; [exact Bn| rewrite En; apply Z.le_refl]. }
      pose proof (xa_call asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -96) (copy_PHI dA) (copy_FR d) J ltac:(clear - SLO2 NEEDR; lia)
                    ltac:(unfold copy_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA; lia) ltac:(unfold copy_FR, calls_FR, fr_charge; clear - D0; lia)
                    MI2 ltac:(replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by (clear; lia); exact ST2') HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
      pose proof (bja_call asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC dA DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -96) J B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
      pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        destruct CR1 as [(-> & _)|(-> & _)]; [exfalso; apply KR; reflexivity|].
        eapply mi_ret; [exact J1| right; reflexivity| |].
        * unfold miV1, mul_int_PHI in *. clear - BV. lia.
        * unfold miF1, mul_int_FR, copy_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
      + destruct CR1 as [(-> & CV & CN)|(-> & _)]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
        assert (EO2 : md_own dX2 = LHeap).
        { pose proof MX2 as [(_ & _ & _ & _ & _ & OW2) _]. pose proof (xa_nst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1) as NS2.
          destruct (md_own dX2); [exfalso; destruct OW2 as [_ N0]; clear - N0 CN HNX HN; lia| reflexivity| exfalso; exact (NS2 eq_refl)]. }
        eapply mi_MLA with (n := n); [exact J1| right; split; [exact DBJ| exact B1]| exact EO2| clear - HN; lia| clear - CN HNX; lia| clear - HN; lia| | exact BNZ| |].
        * clear - CN NMAX HN. lia.
        * unfold miV1, mul_int_PHI in *. clear - BV. lia.
        * unfold miF1, mul_int_FR, copy_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "COPY-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG LSET JC TPV RAE UWX UWC0 D0 BB WB0 NRA BUD BUDF SLO2"] Lemma mi_TAIL : forall (mc : mem)
      (xra xt0 xt1 xt2 xs0' xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [] 0 0 h LB mc dX ->
    uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtA asegs (KF asegs R HIA h mo) MI_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0' xs1 (Z_to_bv 64 X) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x9cbf4) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *)
    (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *)
    (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *)
    (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *)
    (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *)
    intros mc xra xt0 xt1 xt2 xs0' xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 J UWc.
    jc_open. basic_factsA h.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA h LB LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    unfold MI_FRAME_A, aa_frame96 in FR1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep. do 12 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof LSET as HC. unfold mpi_lset_stmtA_v, mpi_xop_stmtA in HC.
      eapply HC with (h := h) (LB := LB) (LF := LF) (dX := dX) (v := 0) (lo := lo) (d := d).
      - exact HH1.
      - exact HK1.
      - exact MX1.
      - exact NS1.
      - cbv beta. clear. lia.
      - exact XW.
      - exact XLS.
      - exact ST1.
      - exact LOS.
      - exact SLO.
      - exact TOP.
      - exact SPA.
      - exact TPV.
      - exact MI1.
      - exact RAE.
      - split; [exact OX1| intros E; exfalso; exact (NS1 E)].
      - cbv beta. unfold mul_int_PHI, copy_PHI, grow_PHI, AVOL_CALL in BUD |- *. clear - BUD NRA. lia.
      - exact UWc.
      - exact UWX.
      - unfold lset_FR, mul_int_FR, calls_FR, fr_charge in BUDF |- *. clear - BUDF D0. lia.
      - reflexivity.
      - reflexivity. }
    intros ms' mo' (mo1 & [HK1 MF1] & PO). unfold mpi_binop_postA in PO.
    destruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & RR2).
    injection E as E1 E2. subst ms' mo'.
    apply aevtS_now. unfold MI_POST_A, mpi_binop_postA.
    exists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m2, mo2, h2, LB2, dX2, r.
    split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split; [exact (mo_frame_trans _ _ _ MF1 MF2)|].
    split; [eapply presA_trans; [exact HPX1| exact HP2]|].
    split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK2|]. split; [exact HCS2|].
    split; [cbv beta in HV2; unfold mul_int_PHI, copy_PHI, grow_PHI, AVOL_CALL in HV2 |- *; clear - HV2 NRA; lia|].
    split; [unfold lset_FR, mul_int_FR, calls_FR, fr_charge in HFR2 |- *; clear - HFR2 D0; lia|].
    split; [exact HH2|]. split; [exact MX2|]. split; [exact OUT2|]. split; [exact FRA2|].
    cbv beta in RR2. destruct RR2 as [LR RZ]. unfold P_mpi_lset.lset_R in LR. unfold mul_int_Rz, binop_keep.
    destruct LR as [[(R0 & N' & OWN' & (w0 & LIMBS') & SG' & PAD') | (RF & EQ)] (ADDR' & BLK')].
    - subst r. split; [left; split; [reflexivity| split; [intros _; apply RZ; reflexivity| rewrite N'; cbn [md_n]; clear - NRA; lia]]|].
      split; [exact ADDR'|]. split; [exact PAD'|]. split; [exact BLK'| rewrite N'; cbn [md_n]; clear; lia].
    - subst dX2. split; [right; exact RF|].
      split; [reflexivity|]. split; [reflexivity|]. split; [intros bk HB; left; exact HB| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L12401343277.3  L21193854616.4  L22593291094.4  L25694054625.3  L28036980531.4  L29008356616.167L29010568605.168L29010568859.171L35663928186.7  L36618624197.2  L39268637205.0  L40497504664.12 L46158332094.168L46160487540.171L56971279505.4  L59308664813.6  L60098763854.3  L65448092613.2  L65450274431.171L67080090232.4  Q26207421841.172Q26207721832.173Q26209920597.170Q31654082872.172Q39212284437.173Q43925228937.173Q60511567613.173Q60697995187.173Q8882996489.170 Q9540479482.170 00000:00E00T00^00k01e02_03O03d03m03n04>04h05R05_06206<06E06l07707Q07k08E08_09909S09k0:K0:e0;=S1r3dXc2KGS1d2D01f2BFS2nX1r3dXc4NXLES1r3dXc2KGS2dA3NRA1v2BVS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03NRA1r3dXc2HR2X02NR3SPR3WBRS2ra2sp1X2nX3xs02dA1b2wb2BB3WB03NRA1r3dXc2HR2X02NR3SPR3WBRS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01r3dXc2HR3WBR3N10S1R3HIA1h2sp2lo3TOP1HS3dXc3NR1SS1r1q2KM2r01H2H0S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03dXc2X03X16S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03dXc2X03X16S2dA3NRA1v2BVS2dA1r3dXc2HR2KG2ENS1R2lo3LOSS3dXc3NR1S2ra2sp1X2nX3xs02dA1b2wb2BB3WB03dXc3NR1S1d2D01f2BFS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb3WB03dXcS2nX3xs02dA1b2wb3WB03dXcS1X2nX3xs02dA1b2wb2BB3WB03dXc2X0S1X2nX3xs02dA1b2wb3WB03dXcS2nX3xs02dA1b2wb3WB03dXc". (* [comment removed for export] *)
  #[using="IMG ZF COPY LSET CALLOC AMC AMS C24H JC TPV RAE UWX UWC0 D0 BB WB0 NRA BUD BUDF SLO2 MA0 IA1"] Lemma mi_FOUND : forall (r : Z) (mc : mem) (r0 : word)
      (xra xt0 xt1 xt2 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [] 0 0 h LB mc dX ->
    rideA R HIA LB LF m dX sp lo dA h LB mc dX ->
    uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    1 <= r <= md_n dA -> r0 = Z_to_bv 64 r ->
    aevtA asegs (KF asegs R HIA h mo) MI_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 r0 xs1 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) wb xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 SB SHA xs8 xs9 xs10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x9ca88) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA UWC HR R0. subst r0. jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. xa_open JX. unfold mpi_cells in CX1. rewrite ?AD1 in CX1. cbn [md_addr] in CX1.
    pose proof (hm_top asegs R HIA h LB LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite ?HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    cbn [md_addr] in OX1.
    pose proof (bv_unsigned_in_range 64 wb) as WBR. unfold bv_modulus in WBR. cbn [Z.pow Z.of_N Pos.pow] in WBR.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *)
      eapply mi_TAIL; [exact J| exact UWC]. }
    assert (BNZ : b <> 0) by (intros B0; apply KB; apply (proj2 WB0); exact B0).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by (clear - HR NRA; rewrite ?Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    { (* [comment removed for export] *)
      eapply mi_ret; [exact J| right; reflexivity| |].
      - unfold mul_int_PHI, copy_PHI, grow_PHI; unfold AVOL_CALL. clear - NRA. lia.
      - unfold mul_int_FR, calls_FR, fr_charge. clear - D0. lia. }
    assert (N10 : r + 1 <= 10000).
    { rewrite Z.shiftr_div_pow2 in KM by (clear; lia). change (2 ^ 4) with 16 in KM. clear - KM HR NRA. Z.div_mod_to_equations. lia. }
    clear KM.
    (* [comment removed for export] *)
    assert (XL7 : Z.land X 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact XAL | clear - XAL; Z.div_mod_to_equations; lia]).
    zstep. if_cases KZ; zify_cond KZ;
      [exfalso; clear - KZ X0 X16; rewrite ?unsigned_lit in KZ by lia; rewrite ?Z.mod_small in KZ by lia; lia|].
    clear KZ.
    zstep. zstep. if_cases KA; zify_cond KA;
      [exfalso; clear - KA XL7 X0 X16; rewrite ?unsigned_lit in KA by lia; rewrite ?(Z.mod_small X) in KA by lia;
       rewrite ?XL7 in KA; rewrite ?Zmod_0_l in KA; lia|].
    clear KA.
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    zstep. zstep.
    lazymatch goal with
    | |- context [zx16 (Z_to_bv 64 ?k)] =>
        replace (zx16 (Z_to_bv 64 k)) with (Z_to_bv 64 k)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; cbn [md_n] in *; lia);
              rewrite Z.mod_small by (clear - NR1; cbn [md_n] in *; lia); reflexivity)
    end.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KG; zify_cond KG; rewrite ?unsigned_lit in KG by (clear - HR NRA NR1; cbn [md_n] in *; lia).
    - (* [comment removed for export] *)
      assert (EO : md_own dX = LHeap).
      { destruct (md_own dX) eqn:EOX; [exfalso| reflexivity| exfalso].
        - first [ddestruct (OWN0 EOX) as (_ & EN & _) | ddestruct (OWN0 eq_refl) as (_ & EN & _)].
          clear - EN KG HR. cbn [md_n] in *. lia.
        - first [exact (NS1 EOX) | exact (NS1 eq_refl)]. }
      eapply (mi_COPY r HR BNZ); [exact J| exact RA| exact EO| clear - KG; cbn [md_n] in *; lia| cbn [md_n]; lia| |].
      + unfold miV1, grow_PHI; unfold AVOL_CALL. clear - NRA. lia.
      + unfold miF1, calls_FR, fr_charge. clear - D0. lia.
    - (* [comment removed for export] *)
      eapply mi_G1; [exact (mi_COPY r HR BNZ)| exact J| exact RA| exact HR| clear - KG; cbn [md_n] in *; lia| exact N10| lia| lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L21041645149.3  L21774718167.2  L23120643753.4  L23120701814.4  L23970764156.146L48367540261.4  L48367597562.3  L54425651213.3  L59308583409.4  L59310648043.5  L8929159528.143 L8929620893.140 Q26295627581.144Q34291222827.141Q34291305632.146Q34291402793.144Q42131479398.146Q48338484555.144Q49424719380.141Q50458135125.144Q53360483131.144Q8943555749.141 00000800>00?00K01G01H01I01R01^02002l03h04C04d05E05f06G06l07M07h08I08dS1k1r2HkS2dA1rFS2dA1r2HR2K2S2ra2sp1X2nX3xs02dA1b2wb2BB3WB01k1r2Hk4LENZ3EP02HR2X03SPR2EBFFS2dA1r2HRS2dA1r2Hk2HRS2dA1r4LENZ2HR3NTHS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01k1r2Hk4LENZ3EP02HR2X03SPR2EBS2ra2sp1X2nX3xs02dA1b2wb2BB3WB01k1r2Hk4LENZ3EP02HR2X03SPR2EBS2nX3xs02dA1b2wb3WB01k1r2HkS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk3EP02HRS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb3WB01k1r2HkS2nX3xs02dA1b2wb2BB3WB01k1r2Hk2HRS2nX3xs02dA1b2wb3WB01k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ZF COPY LSET CALLOC AMC AMS C24H JC TPV RAE UWX UWC0 D0 BB WB0 NRA BUD BUDF SLO2 MA0 IA1"] Lemma mi_SCANLOOP : forall (r : Z) (mc : mem)
      (xra xt0 xt1 xt2 xs1 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 96 MI_FRAME_A [] 0 0 h LB mc dX ->
    rideA R HIA LB LF m dX sp lo dA h LB mc dX ->
    uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    mpd_at asegs mc LB dA -> aobj asegs AL (hcs asegs R HIA h) mc (md_addr dA) 16 ->
    (1 <= md_n dA -> bytes_at asegs mc (md_p dA) (u32s (md_limbs dA)) /\ 0 < md_p dA /\
       aobj asegs AL (hcs asegs R HIA h) mc (md_p dA) (4 * md_n dA)) ->
    0 <= r <= md_n dA ->
    aevtA asegs (KF asegs R HIA h mo) MI_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (r + 1)) xs1 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) wb
             xa3 (Z_to_bv 64 (-4)) (Z_to_bv 64 (4 * r - 4)) xa6 xa7
             xs2 xs3 xs4 xs5 SB SHA xs8 xs9 xs10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x9ca18) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros r. destruct (Z_lt_le_dec r 0) as [RN|RN]; [intros until xt6; intros _ _ _ _ _ _ HR; exfalso; clear - RN HR; lia|].
    pattern r; apply Z_lt_induction; [|exact RN]. clear r RN. intros r IH.
    intros until xt6; intros J0 RA UW MA OA EL HR.
    basic_factsA h.
    pose proof (AIh_laws asegs R HIA h) as LAWS; pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof MA as [(CA & AAL & A0 & LENA & NRA' & OWNA) SGA]. unfold mpi_cells in CA.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      eapply mi_TAIL; [exact J0| exact UW].
    - destruct (EL ltac:(clear - HR K0; lia)) as (EBY & EP0 & OEL).
      pose proof (u32ro_bound _ _ _ _ EBY) as EB. assert (R1 : 1 <= r) by (clear - HR K0; lia).
      assert (PAL : md_p dA mod 4 = 0).
      { destruct (md_own dA); [destruct OWNA as [_ E0]; clear - E0 R1 HR; exfalso; lia| destruct OWNA as (_ & _ & P16 & _); clear - P16; lia| destruct OWNA as (_ & P4 & _); exact P4]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      zstep. if_cases K1; zify_cond K1; [exfalso; clear - K1 R1; lia|].
      zstep. zstep. zstep.
      zstep. if_cases K2; zify_cond K2.
      { exfalso. rewrite (proj2 (Z.ltb_lt 0 (md_p dA)) EP0), (proj2 (Z.ltb_ge (md_p dA + (4 * r - 4)) 1) ltac:(clear - EP0 R1; lia)) in K2. cbn in K2. discriminate K2. }
      zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 EP0; lia|].
      zstep. zstep. zstep. if_cases K4; zify_cond K4.
      { exfalso. rewrite (Z.land_ones _ 2) in K4 by (clear; lia). change (2 ^ 2) with 4 in K4. clear - K4 PAL. apply K4. rewrite Z.add_mod, PAL by (clear; lia). rewrite Z.add_0_r, Z.mod_mod by (clear; lia). replace (4 * r - 4) with ((r - 1) * 4) by (clear; lia). apply Z.mod_mul. clear; lia. }
      clear K1 K2 K3 K4.
      assert (LR : md_p dA + (4 * r - 4) + 4 <= md_p dA + 4 * md_n dA) by (clear - HR; lia).
      zstep. zstep. shadow_chk OEL (md_p dA + (4 * r - 4)) 4.
      (* [comment removed for export] *)
      destruct (nth_error (md_limbs dA) (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENA R1 HR; lia].
      pose proof (u32ro_read asegs mc (md_p dA) (md_limbs dA) (r - 1) w (Z_to_bv 64 (md_p dA + (4 * r - 4))) EBY NTH ltac:(clear - R1; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
      zstep. clear RD.
      zstep. zstep. zstep. if_cases K5.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 r) with (Z_to_bv 64 (r - 1 + 1)) by (f_equal; clear; lia).
        replace (Z_to_bv 64 (4 * r - 4 + -4)) with (Z_to_bv 64 (4 * (r - 1) - 4)) by (f_equal; clear; lia).
        eapply (IH (r - 1) ltac:(clear - R1; lia)); [exact J0| exact RA| exact UW| exact MA| exact OA| exact EL| clear - R1 HR; lia].
      + (* [comment removed for export] *)
        zstep.
        eapply (mi_FOUND r); [exact J0| exact RA| exact UW| clear - R1 HR; lia| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579668.400000=S1X2Ea3SXE2H5". (* [comment removed for export] *)
  #[using="IMG"] Lemma mk_JBd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_int_c24 ()) "PdE,$<.Pm1,P,(:.&40.)(;.(:.&8.))P,(4:.$1.VR,VLF,Vm,VLB,(1?.&40.Vsp,)R2.)P,(4;.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.Vlo,(1?.&40.Vsp,))P,(4<.(4=.VR,)(4>.$9.VLB,(4?.VLF,))Vlo,(28.R4.)+10.)P,P,(12.$23.(24.R5.)$25.)(4<.(4=.VR,)(4>.$9.VLB,(4?.VLF,))Vlo,(43.R6.)(49.+4.(15.R6.)))P,(10.(14.(17.VX,+10.)(28.R6.))(14.(17.(28.R6.)+10.)VX,))P,P,(12.$23.(24.R7.)$50.)P,Pi,$6.P,(11.(14.=R1.)(2=.R1.(49.+4.(15.R9.))))(12.$51.(52.$1.(53.(17.(43.R:.)R2.)))$54.)(12.$51.(55.(43.R9.)(49.+4.(15.R9.)))$54.)P,(47.$1.(2:.VR,)(48.$1.VR,VHIA,Vh,)R7.(28.R8.)+10.)P,P,(12.$23.(24.R9.)$50.)(47.$1.(2:.VR,)(48.$1.VR,VHIA,Vh,)R9.(43.R:.)(49.+4.(15.R:.)))P,(56.$1.VR,VHIA,Vh,VLB,VLF,R9.)P,(4:.$1.VR,VLF,R:.VLB,(1?.&40.Vsp,)R;.)(11.(57.$1.VR,VHIA,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R<.)(58.$1.VR,VHIA,VLF,Vsp,R<.Vh,VLB,R;.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros dE m1; intros ME OE CRE CREL SXE IE OEs OEl HM1 ME1. dpose OE as (OE1 & OE2 & OE3 & OE4 & OE5).
    destruct dE as [Ea sE nE pE zs0 padE ownE].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    split.
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
      intros EO RO hc LBc mc HMc. eapply (AImgGlobals.aobj_img asegs AL); [apply (B.A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IE EO RO)].
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01l0@D35881667587.146D35881667587.147D51255084822.147D61949433775.146D61949433775.147K14554379081.146K14554379081.147L11075936116.139L14550820926.2  L17097338356.139L17305700853.4  L19431261630.4  L19687428440.139L19945316590.2  L21772258342.1  L23124392564.139L23459140778.157L23459159589.2  L23461302312.153L25465666776.139L27017364261.2  L28125529944.139L29025845208.139L29135309044.139L29532535949.3  L29762660275.139L31686769240.139L35161367924.139L35653441506.7  L36180999398.142L39172636981.0  L39280637297.0  L40834179097.152L41172169716.139L43059266230.140L43110360625.2  L43112818177.4  L43671330526.3  L43679985268.138L5065130740.139 L51284464315.158L52253708504.139L55563306247.3  L55720577396.139L58640675965.149L58641002120.152L59310645584.3  L60098763854.3  L60692334296.139L61601561944.139L61747685364.139L62042415875.139L62505661912.138L62562505368.3  L64270350808.139L65178513496.139L67758486644.139Q10042269183.162Q10333294960.156Q15643324129.142Q18133842458.157Q18133990681.157Q18135743526.154Q18365925601.143Q18378753154.143Q18696506101.156Q21800401414.156Q21879645826.143Q24389563138.143Q25160350961.156Q25513505925.145Q25513505925.146Q25664719138.156Q27584944865.143Q27907200258.143Q30415036802.143Q31226872993.156Q31271525473.143Q31396957457.156Q32655500769.143Q33918256002.143Q34224482651.154Q34420396856.157Q35016271767.156Q35715139857.156Q36425882626.143Q3830427394.143 Q39212284437.157Q39517585209.146Q39939554818.143Q41152393185.143Q4141071397.156 Q44648843873.143Q4533518817.143 Q49698585326.144Q49698585326.145Q50301287168.156Q51235796833.143Q52101170785.143Q53972118266.156Q55780705378.145Q55780705378.146Q58692335428.157Q59256763233.143Q59843137889.143Q60511257090.143Q60511567613.157Q61264001456.163Q61265740300.162Q61800308129.156Q63856323923.143Q63856323923.144Q6414620453.156 Q64253126389.156Q64333403626.144Q64766008503.157Q66375044744.163Q66522067074.143Q67327367611.162Q67528989526.146Q67528989526.147Q8222473558.163 Q9538787269.154 Q9843367298.142 00000k02H03Y04f06Q07R09209O09P09m0:90:G0:d0:k0:o0;L0<30<;0<_0=<0=D0=a0>>0>[0>f0?C0?`0@=0@U0A20A30A40AS0B00BX0B_0Bf0Bn0CK0Ch0DE0Db0Dj0EG0Ej0FM0FY0Fc0G@0G]0H:0HW0I40I<0IY0J60JS0Jh0Ji0KD0KY0Kn0LC0L^0MA0M`0Ma0ND0Ng0OF0P30Q?0Q@0Q[0R>0Ra0SA0S\0T10TL0To0UD0UY0V90V:0V]0W@0WU0XK0Xn0YI0YJ0Ye0Z@0Zi0[R0[S0[n0\I0\i0]^0^n0_I0_d0`?0`b0a70aL0aa0ab0b@0b^0c=0c>0c\0d10dF0di0e>0f30gG0h50hJ0hmS1R3HIA1h2ra2sp1X3xs02dA1b2wb2BB3WB03TOP3ABD2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs02dA1b2wb2BB3WB03TOP3ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S1R2ra2sp3s101X3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3LOS2X03SPR2A03ABD2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3LOS2X03SPR2A03ABD2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3LOS2X03SPR2A03ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S1R2ra2sp3xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3ABD3OA42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2lo1b2wb2BB3WB04SLO25NEEDR3ABD3OA42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S2ra2sp1X3xs02dA1b2wb3WB03ABDFS2ra2sp1X3xs02dA1b2wb3WB03ABDS2sp2dA2lo1KS2sp2dA2lo3OA4S2ra2sp1X3xs02dA1b2wb3WB03ABDS2sp2loS2dAS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb2BB3WB02A03ABD3NRAS2dA3NRAS2ra2sp1X3xs02dA1b2wb2BB3WB03NRA3ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NRAS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NRA2KNS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3xs02dA1b2wb3WB03ABDSSS1R2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2nX2dAS2nX2dAS1X2dA1DS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NA1S2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb2BB3WB02A03ABDS2ra2sp1X3xs02dA1b2wb2BB3WB02A03ABDS2dA3EZ03NA1S1R2lo3LOSS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2dA3NA1S2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS2ra2sp1X3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDFS2sp3xs02dA2lo1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS1R3xs02dA1b2wb2BB3WB04IMG'3ABDFS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS1R3xs02dA1b2wb2BB3WB04IMG'3ABDS2ra2sp3xs02dA2lo1b2wb3WB03ABD2HB5Ha_st5Hl_stS2sp2s03xs02dA2lo1b2wb3WB03ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10FS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS1R3xs02dA1b2wb2BB3WB05ALWF'3ABDS2sp3xs02dA2lo1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS1R3xs02dA1b2wb2BB3WB05ALWF'3ABDFS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS2sp3s103xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_stS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS2sp3xs02dA2lo1b2wb3WB03ABDFS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA1b2wb2BB3WB04SP643ABD2HB5Ha_stS2sp3xs02dA1b2wb2BB3WB04SP643ABD2HB5Ha_stFS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS1R3xs02dA1b2wb2BB3WB05ALWF'3ABDS2ra2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_stS2sp2s03xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S3xs02dA1b2wb2BB3WB02A03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDFS2sp3xs02dA1b2wb2BB3WB03ABD2HBS2sp3xs02dA1b2wb2BB3WB03ABD2HBS1R3xs02dA1b2wb2BB3WB04IMG'3ABDFS2sp3xs02dA1b2wb2BB3WB03ABD2HBS3xs02dA1b2wb3WB03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABDS3xs02dA1b2wb3WB03ABDS2ra2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_stS2sp2s03xs02dA2lo1b2wb2BB3WB04LOSP3ABD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S2ra2sp1X3xs02dA1b2wb2BB3WB02X03SPR3AAL2A03ABDS3xs02dA1b2wb3WB03ABDS2sp3xs02dA2lo1b2wb2BB3WB04LOSP3ABD". (* [comment removed for export] *)
  #[using="IMG ZF COPY LSET CALLOC AMC AMS C24H JC TPV RAE UWX UWC0 D0 BB WB0 NRA BUD BUDF SLO2 MA0 IA1"] Lemma mi_ENTRY : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mpd_sep dX dA -> opnd_sep dX dA lo (bv_unsigned sp) ->
    client_range (arl_L R) (LB ++ fdata LF) lo (md_addr dA) 16 ->
    (md_own dA = LHeap -> client_range (arl_L R) (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA)) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    mpd_aobjA asegs AL (hcs asegs R HIA h) m dX -> mpd_aobjA asegs AL (hcs asegs R HIA h) m dA ->
    (md_own dA = LStatic -> (forall i, 0 <= i < 4 * md_n dA -> ro_addr asegs (wa (md_p dA + i)) = true) ->
       AImgGlobals.img_norz (md_p dA) (4 * md_n dA) = true) ->
    aevtA asegs (KF asegs R HIA h mo) MI_POST_A
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) wb a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_MUL_INT) fc None m (seg_rom asegs)).
  Proof.
    intros until t6; intros SXA OA CRA CRAL ST MI OXA OAA IA2. unfold A_MPI_MUL_INT.
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
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply uwc_munch; [exact UWC0| exact MU| clear - LO0 LOSP; lia| apply hstkhi_le64; clear - LOS LOSP SP64; lia|].
      intros a Ha. cbn [outside fst snd]. split; [clear - Ha; lia| exact I]. }
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH1) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    assert (AL7 : Z.land (md_addr dA) 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact AAL | clear - AAL; Z.div_mod_to_equations; lia]).
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ A0 ABD; rewrite ?Z.mod_small in KZ by lia; lia|]. clear KZ.
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA.
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OAs1 (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    pose proof MA1 as [(CA1 & _) _]. unfold mpi_cells in CA1.
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dA))) with (Z_to_bv 64 (md_n dA))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NRA; lia); rewrite Z.mod_small by (clear - NRA; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    replace (Z_to_bv 64 (md_n dA * 4 + -4)) with (Z_to_bv 64 (4 * md_n dA - 4)) by (f_equal; clear; lia).
    eapply (mi_SCANLOOP (md_n dA)); [exact J0| exact RA| exact UW1| exact MA1| exact OAs1| | clear - NRA; lia].
    intros NA1.
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
    split; [exact EBY| split; [exact EP0| exact OEL]].
  Qed.

  #[using="IMG ZF COPY LSET CALLOC AMC AMS C24H JC TPV RAE UWX UWC0 D0 BB WB0 NRA BUD BUDF SLO2 MA0 IA1"] Lemma mi_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HK asegs R HIA h mo ->
    mpd_sep dX dA -> opnd_sep dX dA lo (bv_unsigned sp) ->
    client_range (arl_L R) (LB ++ fdata LF) lo (md_addr dA) 16 ->
    (md_own dA = LHeap -> client_range (arl_L R) (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA)) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    mpd_aobjA asegs AL (hcs asegs R HIA h) m dX -> mpd_aobjA asegs AL (hcs asegs R HIA h) m dA ->
    (md_own dA = LStatic -> (forall i, 0 <= i < 4 * md_n dA -> ro_addr asegs (wa (md_p dA + i)) = true) ->
       AImgGlobals.img_norz (md_p dA) (4 * md_n dA) = true) ->
    aevtS asegs MI_POST_A (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) wb a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_MUL_INT) fc None m (seg_rom asegs)) mo)
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HK SXA OA CRA CRAL ST MI OXA OAA IA2.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    exact (mi_ENTRY t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SXA OA CRA CRAL ST MI OXA OAA IA2).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End WM.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L23332287433.0L42243864624.500000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Theorem A_mpi_mul_int_spec_c : forall (R : art_layout) (HIA : artA asegs R),
  asan_img_ok (arl_AL R) ->
  zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE ->
  mpi_copy_stmtA_c asegs R HIA A_MPI_COPY ->
  mpi_lset_stmtA_v asegs R HIA A_MPI_LSET ->
  arl_calloc R = A_WRAP_CALLOC_MI ->
  arl_amemcpy R = A_ASAN_MEMCPY_MI ->
  arl_amemset R = A_ASAN_MEMSET_MI ->
  0 <= arl_need_rt R ->
  (forall (h : HST asegs R HIA) (LB LF : list blk) (m : mem), HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
  hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
  (forall a : Z, ro_addr asegs (wa a) = true -> 0 <= a < 2 ^ 64 -> hl_img_lo (arl_L R) <= a < hl_img_hi (arl_L R)) ->
  mpi_mul_int_stmtA asegs R HIA A_MPI_MUL_INT
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF COPY LSET CAL AMC AMS NEEDR HND DIMG ROIMG. unfold mpi_mul_int_stmtA.
  intros until d. intros HH HK MX MA SXA NST OA CRA CRAL XW BB XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA IA1 IA2 BUD UW UWX UWA BUDF C24H WB1 WB0 -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 96 (aa_frame96 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  pose proof MA as [(_ & _ & _ & _ & NRA & _) _]. unfold MPI_MAX_LIMBS in NRA.
  eapply mi_main with (b := b); try eassumption.
  all: try exact (uw_obj_nonneg _ _ _ _ UWX).
  all: first [ exact C24H | (lazymatch goal with |- context [cnt24] => idtac end; first [ clear - C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia | match goal with J : XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => let CI := fresh "CI" in pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CI; clear - CI C24H; unfold C24_MUL_INT, C24_COPY_c in *; lia end ]) | match goal with |- ?g => idtac "SPEC-LEFT:" g end ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
