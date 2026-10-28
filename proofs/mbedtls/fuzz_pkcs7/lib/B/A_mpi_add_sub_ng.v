(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg BX_mpi_cmp_abs_stmt AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_add_abs_W A_mpi_sub_abs A_mpi_add_sub A_mpi_sub_abs_ng.
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
Ltac2 gd_tbl_A_mpi_add_sub_ng () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.add_sub_mpi_R"; "add_sub_PHI0"; "add_sub_FR0"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "WAS.AS_FRAME_A"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "WAS.AS_VAL_A"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "WAS.AS_POST_A"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_opnd.opnd_atA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "WAS.at1"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_ng.mpi_sub_abs_ng_stmtA_o"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_ABS"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "add_sub_mpi_ng_stmtA_o"; "mpi_add_mpi_ng_stmtA_o"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_ADD_MPI"; "mpi_sub_mpi_ng_stmtA_o"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_MPI"; "RocqVerifyHarness.AgentSubmission.B.BX_mpi_cmp_abs_stmt.mpi_cmp_abs_raw_stmtA"; "RocqVerifyHarness.AgentSubmission.B.BX_mpi_cmp_abs_stmt.BX_MPI_CMP_ABS"].


Definition add_sub_PHI0 (dX dA dB : mpd) : Z := 0.
Definition add_sub_FR0 (d : Z) : Z := 0.

Section WAS.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis HSUB : mpi_sub_abs_ng_stmtA_o asegs R HIA A_MPI_SUB_ABS.
  Hypothesis HCMP : mpi_cmp_abs_raw_stmtA asegs AL BX_MPI_CMP_ABS.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d flip : Z).
  Variable j8 : list byte.
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition AS_FRAME_A := as_frame j8 ra s0 s1 s2 s3 s4 s5.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis UWA : uw_obj R (md_addr dA) 16 d.
  Hypothesis UWB : uw_obj R (md_addr dB) 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis FLIP : flip = 1 \/ flip = -1.
  Hypothesis BUD : havol asegs R HIA h + add_sub_PHI0 dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + add_sub_FR0 d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 368 - arl_need_rt R.
  (* [comment removed for export] *)
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis SAB : mpd_sep dA dB.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L (LB ++ fdata LF) lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L (LB ++ fdata LF) lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dB) (4 * md_n dB).
  Hypothesis IA1 : md_addr dA <> X -> md_own dA = LStatic -> AImgGlobals.img_norz (md_p dA) (4 * md_n dA) = true.
  Hypothesis IA2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "P,(0.$1.(2.VdA,)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.VdA,))))(0.$:.(;.$<.(=.(>.(?.VdA,)R2.)))$10.)(0.$:.(11.(?.VdA,)(8.+4.(9.VdA,)))$10.)")
(* [comment removed for export] *).
  Hypothesis IB2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "P,(0.$1.(2.VdB,)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.VdB,))))(0.$:.(;.$<.(=.(>.(?.VdB,)R2.)))$10.)(0.$:.(11.(?.VdB,)(8.+4.(9.VdB,)))$10.)")
(* [comment removed for export] *).
  Hypothesis A47A : md_own dA = LStatic -> md_p dA + 4 * md_n dA + 8 <= 2^47.
  Hypothesis A47B : md_own dB = LStatic -> md_p dB + 4 * md_n dB + 8 <= 2^47.
  Hypothesis SGA : md_sg dA = 1 \/ md_sg dA = -1.
  Hypothesis SGB : md_sg dB = 1 \/ md_sg dB = -1.
  Hypothesis NRA : 0 <= md_n dA <= 10000.
  Hypothesis NRB : 0 <= md_n dB <= 10000.
  (* [comment removed for export] *)
  Hypothesis NGS : flip * md_sg dB = - md_sg dA.
  Hypothesis NGAB : mpd_abs dB <= mpd_abs dA -> md_n dA <= nX.
  Hypothesis NGBA : mpd_abs dA < mpd_abs dB -> md_n dB <= nX.

  Definition AS_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "(12.$<.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(14.Vflip,VLB,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(15.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(16.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Definition AS_VAL_A := mpd_val dA + flip * mpd_val dB.

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A []).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAM; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  #[using="IMG JC SLO2"] Lemma as_ret : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (r : Z)
      (xra xt0 xt1 xt2 xs0' xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A [] v f hc LBc mc dXc ->
    (r = 0 /\ mpd_val dXc = AS_VAL_A) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED ->
    v <= add_sub_PHI0 dX dA dB -> f <= add_sub_FR0 d ->
    aevtA asegs (KF asegs R HIA hc mo) AS_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0' xs1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9eaf4) fc None mc (seg_rom asegs)).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold AS_FRAME_A, as_frame in FR1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 7 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold AS_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.

  #[using="IMG JC SLO2"] Lemma as_FIN : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (w sg : Z)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A [] v f hc LBc mc dXc ->
    w mod 2 ^ 16 = sg mod 2 ^ 16 -> sg = 1 \/ sg = -1 -> sg * mpd_abs dXc = AS_VAL_A ->
    v <= add_sub_PHI0 dX dA dB -> f <= add_sub_FR0 d ->
    aevtA asegs (KF asegs R HIA hc mo) AS_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 SB (Z_to_bv 64 w) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9ea84) fc None mc (seg_rom asegs)).
  Proof.
    intros until xt6; intros J0 WS SG HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg0 n p xs pad' own]. pose proof J0 as JX; pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
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
    match type of CX2 with rw_cells _ _ _ [C8 _; C2 (Z_to_bv 64 ?v); _; _] =>
      pose proof (rw_cells_C2_congr asegs m2 X [C8 (Z_to_bv 64 p)] v sg [C2 (Z_to_bv 64 n); C4 padX] CX2) as CX3 end.
    cbn [app] in CX3.
    pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ sg J0 MU WM MI2 (CX3 WS) SG HH2 OX2) as J2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J2.
    eapply as_ret; [exact J2| left; split; [reflexivity|]| exact BV| exact BF].
    unfold mpd_val, mpd_abs in *. cbn [md_sg md_limbs] in *. exact HVV.
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.

  #[using="IMG JC SLO2"] Lemma as_FIN0 : forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (w sg : Z)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 : word),
    XJA asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A [] v f hc LBc mc dXc ->
    w mod 2 ^ 16 = sg mod 2 ^ 16 -> sg = 1 \/ sg = -1 -> sg * mpd_abs dXc = AS_VAL_A ->
    v <= add_sub_PHI0 dX dA dB -> f <= add_sub_FR0 d ->
    aevtA asegs (KF asegs R HIA hc mo) AS_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 SB (Z_to_bv 64 w) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9ea78) fc None mc (seg_rom asegs)).
  Proof.
    intros until xt6; intros J0 WS SG HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    assert (XL7 : Z.land X 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact XAL | clear - XAL; Z.div_mod_to_equations; lia]).
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ X0 X16; rewrite ?Z.mod_small in KZ by lia; lia|].
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA XL7; rewrite ?XL7 in KA; rewrite ?Zmod_0_l in KA; lia|].
    eapply as_FIN; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition at1 (m1 : mem) : Prop :=
    XJA asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A [] 0 0 h LB m1 dX /\ mpd_at asegs m1 LB dA
    /\ opnd_atA asegs R LF m1 LB (bv_unsigned sp) dB
    /\ mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dA /\ mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dB.

  (* [comment removed for export] *)
  #[using="IMG JC SLO2 OA OB"] Lemma at1_scratch : forall m1 m2 : mem,
    at1 m1 -> munch [(lo, bv_unsigned sp + -64)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
    stk asegs m2 lo (bv_unsigned sp + -64) -> at1 m2.
  Proof.
    intros m1 m2 [J0 [MA1 [MB1 [OAA1 OBA1]]]] MU WM MI2 ST2.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (WC : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp + -64)]).
    { unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros x Hx. apply SCS. clear - Hx LOSP. lia. }
    assert (HH2 : HM asegs R HIA h LB LF m2).
    { eapply (hm_munch asegs R HIA h LB LF [(lo, bv_unsigned sp + -64)] m1 m2 HH1 MU WM).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. clear - Ha LOS TOP. lia. }
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ lo (bv_unsigned sp + -64) m2 J0 MU WM MI2 ST2 HH2 ltac:(clear; lia) ltac:(clear; lia)) as J2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J2.
    split; [exact J2|]. split; [| split; [| split]].
    - eapply mpd_at_munch_any; [exact MA1| exact MU| exact WM| cbn; split; [clear - OA4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OA5 ON); clear - H; lia| exact I].
    - eapply opnd_atA_munch_any; [exact MB1| exact MU| exact WM| cbn; split; [clear - OB4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OB5 ON); clear - H; lia| exact I].
    - destruct OAA1 as [OAs OAl]. split; [eapply (aobj_munch asegs AL _ CSOK); [exact WC| exact MU| exact OAs]|].
      intros E. eapply (aobj_munch asegs AL _ CSOK); [exact WC| exact MU| exact (OAl E)].
    - destruct OBA1 as [OBs OBl]. split; [eapply (aobj_munch asegs AL _ CSOK); [exact WC| exact MU| exact OBs]|].
      intros E. eapply (aobj_munch asegs AL _ CSOK); [exact WC| exact MU| exact (OBl E)].
  Qed.

  (* [comment removed for export] *)
  Local Ltac call_side :=
    first [ eassumption | reflexivity | exact BUD | exact BUDF | exact IA1 | exact UWX
          | (rewrite unsigned_lit by (clear; lia); reflexivity)
          | (apply mpd_sep_symA; eassumption)
          | (eapply opnd_sep_sp_le; [eassumption| clear; lia])
          | (eapply opnd_atA_SP_le; [first [eassumption| apply opnd_atA_mpd; eassumption]| clear; lia])
          | (apply opnd_atA_mpd; eassumption) ].


  (* [comment removed for export] *)
  #[using="IMG HSUB JC TPV UWX UWA UWB D0 BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA2 IB2 A47A FLIP SGA SGB NRA NRB NGAB"]
  Lemma as_KSUBAB : forall (m1 : mem) (w c : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    at1 m1 -> w mod 2 ^ 16 = md_sg dA mod 2 ^ 16 -> flip * md_sg dB = - md_sg dA ->
    mpd_abs dB <= mpd_abs dA -> c = Z.sgn (mpd_abs dA - mpd_abs dB) ->
    aevtA asegs (KF asegs R HIA h mo) AS_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 c) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB)) SB (Z_to_bv 64 w) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9eac0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until xt6; (intros dd_H; ddestruct dd_H as (J0 & MA1 & MB1 & OAA1 & OBA1); intros WS SGN LE HC).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST1 by (clear; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (XW1 : mpd_writableA R LB LF (bv_unsigned sp + -64) (htop asegs R HIA h) dX) by (eapply mpd_writableA_sp_mono; [exact XW| clear; lia]).
    assert (XLS1' : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp + -64 <= md_p dX) by (intros N; destruct (XLS N); [left; assumption| right; clear - H; lia]).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX) by (split; [exact OX1| intros E; exfalso; exact (NST E)]).
    assert (PHI0 : 0 <= sub_abs_PHI0 dX dA dB) by (unfold sub_abs_PHI0, grow_PHI; unfold AVOL_CALL; clear - NRA; lia).
    assert (FR0 : 0 <= sub_abs_FR0 d) by (unfold sub_abs_FR0, calls_FR, fr_charge; clear - D0; lia).
    assert (PHI1 : sub_abs_PHI0 dX dA dB <= add_sub_PHI0 dX dA dB) by (unfold sub_abs_PHI0, add_sub_PHI0, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA NRB; lia).
    assert (FR1' : sub_abs_FR0 d <= add_sub_FR0 d) by (unfold sub_abs_FR0, add_sub_FR0, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HSUB as SPc. unfold mpi_sub_abs_ng_stmtA_o in SPc.
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; try call_side.
      all: try (rewrite ?(unsigned_lit X) by qlia; eapply uw_obj_uwc; [exact UWX| clear; lia]).
      all: try (clear - SLO2 NEEDR TOP SPR LOS LOSP; lia).
      all: try (clear - SPA; replace (bv_unsigned sp + -64) with (bv_unsigned sp + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact SPA).
      all: try (clear - BUD PHI1; lia). all: try (clear - BUDF FR1'; lia).
      all: try (cbn [md_n]; apply NGAB; exact LE).
      all: match goal with |- ?g => idtac "KSUBAB-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct CR as [CR1 BK].
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -64) (sub_abs_PHI0 dX dA dB) (sub_abs_FR0 d) J0 ltac:(clear - SLO2 NEEDR; lia)
                  PHI0 FR0 MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - destruct CR1 as [(-> & _)|[-> |[-> LT]]]; [exfalso; apply KR; reflexivity| | exfalso; clear - LT LE; lia].
      eapply as_ret; [exact J1| right; reflexivity| clear - PHI1; lia| clear - FR1'; lia].
    - destruct CR1 as [(-> & CV & CSG)|[-> |[-> LT]]];
        [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LE; lia].
      unfold mpd_val in CV. rewrite CSG in CV.
      assert (VX : mpd_abs dX2 = mpd_abs dA - mpd_abs dB) by (unfold mpd_abs in *; clear - CV; lia).
      destruct (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as [[CP CE]|[[CP CE]|[CP CE]]]; rewrite CE in HC; subst c;
        [| | exfalso; clear - CP LE; lia].
      + (* [comment removed for export] *)
        zstep. try (if_cases K2; zify_cond K2; [| exfalso; clear - K2; lia]).
        eapply as_FIN0 with (sg := md_sg dA); [exact J1| exact WS| exact SGA| | clear - PHI1; lia| clear - FR1'; lia].
        unfold AS_VAL_A. rewrite VX. unfold mpd_val, mpd_abs.
        replace (flip * (md_sg dB * limbs_val (md_limbs dB))) with ((flip * md_sg dB) * limbs_val (md_limbs dB)) by (clear; lia). rewrite SGN. clear; lia.
      + (* [comment removed for export] *)
        zstep. try (if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|]).
        zstep. zstep.
        eapply (as_FIN0 _ _ _ _ _ _ 1 1); [exact J1| reflexivity| left; reflexivity| | clear - PHI1; lia| clear - FR1'; lia].
        unfold AS_VAL_A. rewrite VX. unfold mpd_val, mpd_abs. unfold mpd_abs in CP.
        replace (limbs_val (md_limbs dB)) with (limbs_val (md_limbs dA)) by (clear - CP; lia).
        replace (flip * (md_sg dB * limbs_val (md_limbs dA))) with ((flip * md_sg dB) * limbs_val (md_limbs dA)) by (clear; lia). rewrite SGN. clear; lia.
    all: match goal with |- ?g => idtac "KSUBAB-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG HSUB JC TPV UWX UWA UWB D0 BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA2 IB2 A47B FLIP SGA SGB NRA NRB NGBA"]
  Lemma as_KSUBBA : forall (m1 : mem) (w : Z) (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    at1 m1 -> w mod 2 ^ 16 = md_sg dA mod 2 ^ 16 -> 0 <= w < 2 ^ 16 -> flip * md_sg dB = - md_sg dA ->
    mpd_abs dA < mpd_abs dB ->
    aevtA asegs (KF asegs R HIA h mo) AS_POST_A
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB)) SB (Z_to_bv 64 w) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9eae0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until xt6; (intros dd_H; ddestruct dd_H as (J0 & MA1 & MB1 & OAA1 & OBA1); intros WS WB SGN LT).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    assert (XL7 : Z.land X 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact XAL | clear - XAL; Z.div_mod_to_equations; lia]).
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST1 by (clear; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (XW1 : mpd_writableA R LB LF (bv_unsigned sp + -64) (htop asegs R HIA h) dX) by (eapply mpd_writableA_sp_mono; [exact XW| clear; lia]).
    assert (XLS1' : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp + -64 <= md_p dX) by (intros N; destruct (XLS N); [left; assumption| right; clear - H; lia]).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX) by (split; [exact OX1| intros E; exfalso; exact (NST E)]).
    assert (PHI0 : 0 <= sub_abs_PHI0 dX dB dA) by (unfold sub_abs_PHI0, grow_PHI; unfold AVOL_CALL; clear - NRB; lia).
    assert (FR0 : 0 <= sub_abs_FR0 d) by (unfold sub_abs_FR0, calls_FR, fr_charge; clear - D0; lia).
    assert (PHI1 : sub_abs_PHI0 dX dB dA <= add_sub_PHI0 dX dA dB) by (unfold sub_abs_PHI0, add_sub_PHI0, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA NRB; lia).
    assert (FR1' : sub_abs_FR0 d <= add_sub_FR0 d) by (unfold sub_abs_FR0, add_sub_FR0, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HSUB as SPc. unfold mpi_sub_abs_ng_stmtA_o in SPc.
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dB) (dB := dA) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; try call_side.
      all: try (rewrite ?(unsigned_lit X) by qlia; eapply uw_obj_uwc; [exact UWX| clear; lia]).
      all: try (clear - SLO2 NEEDR TOP SPR LOS LOSP; lia).
      all: try (clear - SPA; replace (bv_unsigned sp + -64) with (bv_unsigned sp + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact SPA).
      all: try (clear - BUD PHI1; lia). all: try (clear - BUDF FR1'; lia).
      all: try (cbn [md_n]; apply NGBA; assumption).
      all: match goal with |- ?g => idtac "KSUBBA-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct CR as [CR1 BK].
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -64) (sub_abs_PHI0 dX dB dA) (sub_abs_FR0 d) J0 ltac:(clear - SLO2 NEEDR; lia)
                  PHI0 FR0 MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - destruct CR1 as [(-> & CV & CSG)|[-> |[-> LT']]];
        [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LT'; lia].
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ X0 X16; rewrite ?Z.mod_small in KZ by lia; lia|].
      zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA XL7; rewrite ?XL7 in KA; rewrite ?Zmod_0_l in KA; lia|].
      zstep. zstep.
      eapply (as_FIN _ _ _ _ _ _ (0 - w) (- md_sg dA)); [exact J1| | clear - SGA; lia| | clear - PHI1; lia| clear - FR1'; lia].
      + rewrite Zminus_mod, WS, <- Zminus_mod. reflexivity.
      + unfold AS_VAL_A. unfold mpd_val in CV. rewrite CSG in CV.
        replace (mpd_abs dX2) with (mpd_abs dB - mpd_abs dA) by (unfold mpd_abs in *; clear - CV; lia).
        unfold mpd_val, mpd_abs.
        replace (flip * (md_sg dB * limbs_val (md_limbs dB))) with ((flip * md_sg dB) * limbs_val (md_limbs dB)) by (clear; lia). rewrite SGN. clear; lia.
    - destruct CR1 as [(-> & _)|[-> |[-> LT']]]; [exfalso; apply KR; reflexivity| | exfalso; clear - LT LT'; lia].
      eapply as_ret; [exact J1| right; reflexivity| clear - PHI1; lia| clear - FR1'; lia].
    all: match goal with |- ?g => idtac "KSUBBA-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308546259.300000:S2dE2N12N0". (* [comment removed for export] *)
  #[using="Type"] Lemma opnd_aobjA_limbs : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Phc,(17.$<.VR,VHIA,)PLBc,(18.$19.)Pmc,P,(1:.&40.)(1;.(1:.&8.))PSPx,$4.PdE,$1<.P,(3;.$<.VR,VHIA,R5.R4.VLF,R3.)P,(33.$<.VR,VLF,R4.R5.R3.R2.)P,(34.$<.(31.VR,)(35.$<.VR,VHIA,R7.)R5.R3.)P,(6.+1.(9.R4.))(3<.$<.(31.VR,)(35.$<.VR,VHIA,R9.)R7.(?.R5.)(8.+4.(9.R5.)))")
(* [comment removed for export] *).
  Proof.
    intros hc LBc mc SPx dE HMc ME [_ OL] N1. pose proof (opnd_viewA _ _ _ _ _ _ _ ME) as [(_ & _ & _ & _ & _ & OW) _].
    destruct (md_own dE) eqn:EO.
    - exfalso. destruct OW as [_ N0]. clear - N0 N1. lia.
    - ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HMc| exact EIN].
    - exact (OL eq_refl).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG HSUB HCMP JC TPV UWX UWA UWB D0 FLIP BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA1 IA2 IB2 A47A A47B SGA SGB NRA NRB NGS NGAB NGBA"]
  Lemma as_main : forall (junk : list byte) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HK asegs R HIA h mo -> mpd_at asegs m LB dA -> opnd_atA asegs R LF m LB (bv_unsigned sp) dB ->
    stk asegs m lo (bv_unsigned sp - 64) -> rw_cells asegs m (bv_unsigned sp - 64) [CB 8 j8; CB 56 junk] ->
    mem_inv asegs m ->
    mpd_aobjA asegs AL (hcs asegs R HIA h) m dX -> mpd_aobjA asegs AL (hcs asegs R HIA h) m dA ->
    mpd_aobjA asegs AL (hcs asegs R HIA h) m dB ->
    aevtS asegs AS_POST_A
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 flip)
                      a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 A_ADD_SUB_MPI) fc None m (seg_rom asegs)) mo).
  Proof.
    intros until t6; intros HK MA0 MB0 ST FR MI OXA OAA OBA. unfold A_ADD_SUB_MPI.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h. pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. pose proof OBA as [OBs OBl]. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST, FR by (clear; lia).
    (* [comment removed for export] *)
    do 8 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    change (rw_cells asegs m1 (bv_unsigned sp + -64) AS_FRAME_A) in FR.
    pose proof ST as ST1.
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
    assert (AT : at1 m1) by (split; [exact J0| split; [exact MA1| split; [exact MB1| split; [split; [exact OAs| exact OAl1]| split; [exact OBs| exact OBl1]]]]]).
    (* [comment removed for export] *)
    destruct (hm_apart asegs R HIA h LB LF m1 HH) as [HF0 _]. rewrite Forall_forall in HF0.
    pose proof (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dA MA1) as MA1o.
    assert (PA0 : md_own dA = LHeap -> 0 < md_p dA).
    { intros EO. pose proof (opnd_viewA _ _ _ _ _ _ _ MA1o) as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. ddestruct OW as (_ & AIN & _).
      destruct (HF0 _ ltac:(apply in_or_app; left; exact AIN)) as (R0 & _). exact R0. }
    assert (PB0 : md_own dB = LHeap -> 0 < md_p dB).
    { intros EO. pose proof (opnd_viewA _ _ _ _ _ _ _ MB1) as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. ddestruct OW as (_ & BIN & _).
      destruct (HF0 _ ltac:(apply in_or_app; left; exact BIN)) as (R0 & _). exact R0. }
    destruct (opnd_rawA _ _ _ _ _ _ _ MA1o PA0) as (CEA & ABY & LENA & NRA1 & _ & ABD & PAB).
    destruct (opnd_rawA _ _ _ _ _ _ _ MB1 PB0) as (CEB & BBY & LENB & NRB1 & _ & BBD & PBB).
    pose proof (proj1 (proj2 (proj1 (opnd_viewA _ _ _ _ _ _ _ MA1o)))) as ALA. pose proof (proj1 (proj2 (proj1 (opnd_viewA _ _ _ _ _ _ _ MB1)))) as ALB.
    pose proof (bytes_at_bound _ _ _ _ ABY) as PABB. rewrite u32s_length in PABB.
    pose proof (bytes_at_bound _ _ _ _ BBY) as PBBB. rewrite u32s_length in PBBB.
    assert (OALn : 1 <= md_n dA -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dA) (4 * md_n dA)) by (intros N1; eapply (opnd_aobjA_limbs h LB m1 _ dA HH MA1o); [split; [exact OAs| exact OAl1]| exact N1]).
    assert (OBLn : 1 <= md_n dB -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dB) (4 * md_n dB)) by (intros N1; eapply (opnd_aobjA_limbs h LB m1 _ dB HH MB1); [split; [exact OBs| exact OBl1]| exact N1]).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    pose proof (proj1 (proj2 (proj2 (proj1 (opnd_viewA _ _ _ _ _ _ _ MA1o))))) as APOS.
    pose proof (proj1 (proj2 (proj2 (proj1 (opnd_viewA _ _ _ _ _ _ _ MB1))))) as BPOS.
    assert (AL7 : Z.land (md_addr dA) 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact ALA | clear - ALA; Z.div_mod_to_equations; lia]).
    assert (BL7 : Z.land (md_addr dB) 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact ALB | clear - ALB; Z.div_mod_to_equations; lia]).
    assert (PDA : 1 <= md_n dA -> md_p dA + 4 * md_n dA <= lo \/ bv_unsigned sp <= md_p dA).
    { intros N1. apply OA5. intros EO. pose proof (opnd_viewA _ _ _ _ _ _ _ MA1o) as [(_ & _ & _ & _ & _ & OW) _].
      rewrite EO in OW. destruct OW as [_ N0]. clear - N0 N1. lia. }
    assert (PDB : 1 <= md_n dB -> md_p dB + 4 * md_n dB <= lo \/ bv_unsigned sp <= md_p dB).
    { intros N1. apply OB5. intros EO. pose proof (opnd_viewA _ _ _ _ _ _ _ MB1) as [(_ & _ & _ & _ & _ & OW) _].
      rewrite EO in OW. destruct OW as [_ N0]. clear - N0 N1. lia. }
    (* [comment removed for export] *)
    zstep. if_cases KZA; zify_cond KZA; [exfalso; clear - KZA APOS ABD; rewrite ?Z.mod_small in KZA by lia; lia|].
    zstep. zstep. zstep. if_cases KAA; zify_cond KAA; [exfalso; clear - KAA AL7; rewrite ?AL7 in KAA; rewrite ?Zmod_0_l in KAA; lia|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OAs (md_addr dA + 8) 2.
    (* [comment removed for export] *)
    zstep. if_cases KZB; zify_cond KZB; [exfalso; clear - KZB BPOS BBD; rewrite ?Z.mod_small in KZB by lia; lia|].
    zstep. zstep. if_cases KAB; zify_cond KAB; [exfalso; clear - KAB BL7; rewrite ?BL7 in KAB; rewrite ?Zmod_0_l in KAB; lia|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OBs (md_addr dB + 8) 2.
    (* [comment removed for export] *)
    zstep.
    pose proof (mpd_abs_lval dA LENA) as EVA. pose proof (mpd_abs_lval dB LENB) as EVB.
    pose proof (mpd_abs_nonneg dA) as NNA. pose proof (mpd_abs_nonneg dB) as NNB.
    pose proof SGA as SGA'. pose proof SGB as SGB'. pose proof FLIP as FLIP'.
    destruct SGA' as [EA|EA]; destruct SGB' as [EB|EB]; destruct FLIP' as [EF|EF]; rewrite ?EA, ?EB, ?EF; rewrite ?sx16_small by (clear; lia).
    (* [comment removed for export] *)
    all: zstep; zstep; zstep; zstep; zstep.
    all: try (if_cases K0; zify_cond K0; try (exfalso; clear - K0; lia)).
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- aevtA _ _ _ (MS _ _ (Z_to_bv 64 0x9ea6c) _ _ _ _) =>
             exfalso; pose proof NGS as NGS'; rewrite EA, EB, EF in NGS'; clear - NGS'; lia
         | |- _ => idtac end.
    (* [comment removed for export] *)
    all: zstep; zstep; zstep; zstep; zstep.
    all: pose proof HCMP as HC'; unfold mpi_cmp_abs_raw_stmtA in HC'.
    all: eapply (aevtA_cut_evtA_KF asegs R HIA h mo);
      [ eapply HC' with (CS := hcs asegs R HIA h) (lo := lo)
          (X := md_addr dA) (P := md_p dA) (n := md_n dA) (sg := md_sg dA) (xs := md_limbs dA) (pad := md_pad dA)
          (Y := md_addr dB) (Q := md_p dB) (n' := md_n dB) (sg' := md_sg dB) (ys := md_limbs dB) (pad' := md_pad dB);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
          first [ exact CEA | exact ABY | exact LENA | exact NRA1 | exact PAB | exact APOS | exact ALA
                | exact CEB | exact BBY | exact LENB | exact NRB1 | exact PBB | exact BPOS | exact ALB
                | exact MI | exact ALWF | exact CSOK | exact AB | exact OAs | exact OBs | exact OALn | exact OBLn
                | exact ST | exact LO0 | reflexivity
                | (clear - SLO2 NEEDR LOSP; lia)
                | (unfold MPI_CMP_ABS_STACK_A; clear - SLO2 NEEDR LOSP; lia)
                | (clear - SPA; replace (bv_unsigned sp + -64) with (bv_unsigned sp + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact SPA)
                | (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP SP64; lia])
                | (clear - OA4; lia) | (clear - OB4; lia)
                | (intros N1; destruct (PDA N1) as [PD|PD]; [left| right]; clear - PD; lia)
                | (intros N1; destruct (PDB N1) as [PD|PD]; [left| right]; clear - PD; lia)
                | match goal with |- ?g => idtac "CMP-PRE-LEFT:" g end ]
      | ].
    all: cbv beta; intros ms' PC; unfold OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B.A_mpi_cmp_mpi.mpi_cmp_postA in PC.
    all: ddestruct PC as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & -> & MUc & WMc & MIc & STc).
    all: rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MUc, STc by qlia.
    all: lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    all: pose proof (at1_scratch m1 m2 AT MUc WMc MIc STc) as AT2.
    all: rewrite <- EVA, <- EVB.
    all: destruct (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as [[CP CE]|[[CP CE]|[CP CE]]]; rewrite CE.
    (* [comment removed for export] *)
    all: zstep.
    all: try (if_cases K1; zify_cond K1; try (exfalso; clear - K1; lia)).
    all: lazymatch goal with
         | |- aevtA _ _ _ (MS _ _ (Z_to_bv 64 0x9eae0) _ _ _ _) =>
             eapply (as_KSUBBA m2); [exact AT2| rewrite EA; vm_compute; reflexivity| vm_compute; split; [discriminate| reflexivity]
                                    | rewrite EA, EB, EF; reflexivity| clear - CP; lia]
         | |- _ =>
             zstep; eapply (as_KSUBAB m2); [exact AT2| rewrite EA; vm_compute; reflexivity| rewrite EA, EB, EF; reflexivity
                                           | clear - CP; lia| rewrite CE; reflexivity]
         end.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WAS.

Definition add_sub_mpi_ng_stmtA_o (flip : Z) (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Ph,(17.O4.O3.O2.)PLB,(18.$19.)PLF,(18.$19.)Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(43.&5.(1:.&40.))Pfc,(1:.&20.)Pm,P,(1:.&40.)(1;.(1:.&8.))Pmo,$44.PdX,$1<.PdA,$1<.PdB,$1<.Plo,$4.Pd,$4.P,(3;.O4.O3.O2.R2;.R2:.R29.R7.)P,(3=.O4.O3.O2.R2<.R7.)P,(32.O4.R9.R2<.R7.)P,(32.O4.R:.R2=.R7.)P,(33.O4.O3.R2=.R;.R2>.(2:.&40.R2;.)R7.)P,(45.R:.R9.)P,(45.R;.R9.)P,(45.R;.R:.)P,(46.(0.$1.(2.R=.)$3.))P,(0.$4.(8.O5.(37.R<.))(38.(37.R=.)))P,P,(6.(2?.R=.)(2?.R>.))(6.(9.R?.)(9.R10.))P,P,(7.(2?.R?.)(2?.R>.))(6.(9.R?.)(9.R11.))P,(47.R11.R10.R>.(2:.&40.R33.))P,(47.R12.R10.R?.(2:.&40.R34.))P,(48.(49.O3.)(4:.$19.R38.(4;.R37.))R10.(3:.R12.)+10.)P,P,(0.$1.(2.R13.)$4<.)(48.(49.O3.)(4:.$19.R3:.(4;.R39.))R12.(?.R14.)(8.+4.(9.R14.)))P,(48.(49.O3.)(4:.$19.R3:.(4;.R39.))R12.(3:.R13.)+10.)P,P,(0.$1.(2.R14.)$4<.)(48.(49.O3.)(4:.$19.R3<.(4;.R3;.))R14.(?.R15.)(8.+4.(9.R15.)))P,(4=.O3.R3<.R3;.(2:.&40.R39.)(4>.O4.O3.O2.R3=.)R17.)P,P,(46.(0.$1.(2.R18.)$4?.))(20.(6.(>.(?.R19.)(8.+4.(9.R19.)))R16.)(6.(2:.&40.R3;.)(?.R19.)))P,(3>.O4.R1;.R16.(2:.&40.R3;.))P,(6.(50.O3.)R17.)P,(6.R18.(39.(39.(2:.&40.R3=.)+170.)(51.O3.)))P,(6.(2:.&40.R3>.)(4>.O4.O3.O2.R42.))P,(0.$4.(2=.(2:.&40.R3?.)+10.)=)P,(0.(1:.&40.)R3>.(29.&40.(52.O3.)))P,(3?.O4.R21.)P,(0.$4.(2=.(2:.&40.R43.)+2.)=)P,(34.O4.(31.O3.)(35.O4.O3.O2.R47.)R23.R21.)P,(34.O4.(31.O3.)(35.O4.O3.O2.R48.)R24.R21.)P,(34.O4.(31.O3.)(35.O4.O3.O2.R49.)R25.R21.)P,P,(46.(0.$4.(3:.R23.)(3:.R24.)))P,(0.$1.(2.R24.)$3.)(0.$:.(11.(?.R25.)(8.+4.(9.R25.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O4.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O4.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R25.)$3.)(6.(>.(>.(?.R26.)(8.+4.(9.R26.)))+8.)(2>.+2.+2?.))P,(6.(>.(53.O4.O3.O2.R4>.)(15.R28.R27.R26.))$54.)P,(55.O4.R2;.(50.O3.)(56.O4.O3.O2.R4?.)(2:.&40.R45.)(2:.&40.R4;.)R25.)P,(57.O3.(3:.R2:.)+10.R26.)P,(57.O3.(3:.R2:.)+10.R27.)P,(57.O3.(3:.R2:.)+10.R28.)P,(6.(>.(58.O4.O3.O2.R53.)(16.R29.))$59.)P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.O5.))(40.O4.(12.O4.O3.O2.R55.R54.R53.R52.R4>.R4=.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R36.R35.R58.R57.R56.R32.(14.O5.R57.R32.R31.R30.)(15.R32.R31.R30.)(16.R2>.)R2?.R34.R33.)(41.(27.(28.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.)R36.(29.&40.O1.)R35.(2;.(1:.&40.))R34.(2<.O4.))R33.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24356290505.0L43712349232.500000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Lemma A_add_sub_mpi_ng_spec_o : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Pflip,$4.P,(20.(0.$4.R1.+1.)(0.$4.R1.-1.))PR,$5:.PHIA,(5;.$<.R1.)P,(5<.(31.R2.))P,(5=.$<.R3.R2.$5>.)P,(6<.$<.(31.R4.)$6=.)P,(6.=(51.R5.))P,Ph,(17.$<.R6.R5.)PLB,(18.$19.)PLF,(18.$19.)Pm,P,(1:.&40.)(1;.(1:.&8.))P,(3;.$<.R:.R9.R4.R3.R2.R1.)(5?.$4.(60.(61.$4.$4.)$4.(62.$4.$4.)R4.))P,(5.(6.(63.(49.R7.))(64.(49.R7.)))(6.(65.(49.R7.))(66.(49.R7.))))P,Pa,$4.P,(0.$:.(;.$<.(=.R1.))$10.)P,(5.(6.=R2.)(7.R2.(2>.+2.+40.)))(5.(6.(63.(49.R;.))R3.)(7.R3.(66.(49.R;.))))(67.R;.$<.R9.R8.$42.)")
(* [comment removed for export] *).
Proof.
  intros flip FLIP R HIA IMG HSUB HCMP NEEDR HND DIMG ROIMG. unfold add_sub_mpi_ng_stmtA_o.
  intros until d. intros HH HK MX MA MB SXA SXB SAB NST NGS NGAB NGBA OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA1 IA2 IB2 A47B BUD UW UWX UWA UWB BUDF -> -> -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  destruct (stk_carve asegs m lo (bv_unsigned sp) 56 ST ltac:(clear - SLO NEEDR; lia)) as [ST1 [junk FR1]].
  change (Z.of_nat 56) with 56 in ST1, FR1.
  destruct (stk_carve asegs m lo (bv_unsigned sp - 56) 8 ST1 ltac:(clear - SLO NEEDR; lia)) as [ST2 [j8 FR2]].
  change (Z.of_nat 8) with 8 in ST2, FR2.
  replace (bv_unsigned sp - 56 - 8) with (bv_unsigned sp - 64) in ST2, FR2 by (clear; lia).
  assert (FRJ : rw_cells asegs m (bv_unsigned sp - 64) [CB 8 j8; CB 56 junk]).
  { apply (proj2 (rw_cells_app asegs m (bv_unsigned sp - 64) [CB 8 j8] [CB 56 junk])). split; [exact FR2|].
    cbn [cells_size csize Nat.add]. replace (bv_unsigned sp - 64 + Z.of_nat 8) with (bv_unsigned sp - 56) by (cbn; lia). exact FR1. }
  clear ST ST1 FR1 FR2.
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (as_frame j8 ra s0 s1 s2 s3 s4 s5)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  pose proof MA as [(_ & _ & _ & _ & NRA & _) SGA]. pose proof (opnd_viewA _ _ _ _ _ _ _ MB) as [(_ & _ & _ & _ & NRB & _) SGB]. unfold MPI_MAX_LIMBS in NRA, NRB.
  eapply as_main; try eassumption.
  all: try exact (uw_obj_nonneg _ _ _ _ UWX).
  all: try (intros E; eapply mpd_at_static47; eassumption).
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mpi_addsub_pub_ng_stmtA_o (flip : Z) (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z)
    (Rr : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Ph,(17.O5.O4.O3.)PLB,(18.$19.)PLF,(18.$19.)Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(43.&5.(1:.&40.))Pfc,(1:.&20.)Pm,P,(1:.&40.)(1;.(1:.&8.))Pmo,$44.PdX,$1<.PdA,$1<.PdB,$1<.Plo,$4.Pd,$4.P,(3;.O5.O4.O3.R2;.R2:.R29.R7.)P,(3=.O5.O4.O3.R2<.R7.)P,(32.O5.R9.R2<.R7.)P,(32.O5.R:.R2=.R7.)P,(33.O5.O4.R2=.R;.R2>.(2:.&40.R2;.)R7.)P,(45.R:.R9.)P,(45.R;.R9.)P,(45.R;.R:.)P,(46.(0.$1.(2.R=.)$3.))P,(0.$4.(8.O6.(37.R<.))(38.(37.R=.)))P,P,(6.(2?.R=.)(2?.R>.))(6.(9.R?.)(9.R10.))P,P,(7.(2?.R?.)(2?.R>.))(6.(9.R?.)(9.R11.))P,(47.R11.R10.R>.(2:.&40.R33.))P,(47.R12.R10.R?.(2:.&40.R34.))P,(48.(49.O4.)(4:.$19.R38.(4;.R37.))R10.(3:.R12.)+10.)P,P,(0.$1.(2.R13.)$4<.)(48.(49.O4.)(4:.$19.R3:.(4;.R39.))R12.(?.R14.)(8.+4.(9.R14.)))P,(48.(49.O4.)(4:.$19.R3:.(4;.R39.))R12.(3:.R13.)+10.)P,P,(0.$1.(2.R14.)$4<.)(48.(49.O4.)(4:.$19.R3<.(4;.R3;.))R14.(?.R15.)(8.+4.(9.R15.)))P,(4=.O4.R3<.R3;.(2:.&40.R39.)(4>.O5.O4.O3.R3=.)R17.)P,P,(46.(0.$1.(2.R18.)$4?.))(20.(6.(>.(?.R19.)(8.+4.(9.R19.)))R16.)(6.(2:.&40.R3;.)(?.R19.)))P,(3>.O5.R1;.R16.(2:.&40.R3;.))P,(6.(50.O4.)R17.)P,(6.R18.(39.(39.(2:.&40.R3=.)+170.)(51.O4.)))P,(6.(2:.&40.R3>.)(4>.O5.O4.O3.R42.))P,(0.$4.(2=.(2:.&40.R3?.)+10.)=)P,(0.(1:.&40.)R3>.(29.&40.(52.O4.)))P,(3?.O5.R21.)P,(0.$4.(2=.(2:.&40.R43.)+2.)=)P,(34.O5.(31.O4.)(35.O5.O4.O3.R47.)R23.R21.)P,(34.O5.(31.O4.)(35.O5.O4.O3.R48.)R24.R21.)P,(34.O5.(31.O4.)(35.O5.O4.O3.R49.)R25.R21.)P,P,(46.(0.$4.(3:.R23.)(3:.R24.)))P,(0.$1.(2.R24.)$3.)(0.$:.(11.(?.R25.)(8.+4.(9.R25.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O5.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O5.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R25.)$3.)(6.(>.(>.(?.R26.)(8.+4.(9.R26.)))+8.)(2>.+2.+2?.))P,(6.(>.(53.O5.O4.O3.R4>.)(15.R28.R27.R26.))$54.)P,(55.O5.R2;.(50.O4.)(56.O5.O4.O3.R4?.)(2:.&40.R45.)(2:.&40.R4;.)R25.)P,(57.O4.(3:.R2:.)+10.R26.)P,(57.O4.(3:.R2:.)+10.R27.)P,(57.O4.(3:.R2:.)+10.R28.)P,(6.(>.(58.O5.O4.O3.R53.)(16.R29.))$59.)P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))(40.O5.(12.O5.O4.O3.R54.R53.R52.R51.R4=.R4<.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R35.R34.R57.R56.R55.R31.A4.O1.R56.R31.R30.R2?.(15.R31.R30.R2?.)(16.R2=.)R2>.R33.R32.)(41.(27.(28.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.)R35.(29.&40.O2.)R34.(2;.(1:.&40.))R33.(2<.O5.))R32.))")
(* [comment removed for export] *).

(* [comment removed for export] *)

Definition mpi_add_mpi_ng_stmtA_o segs R HIA ENTRY := mpi_addsub_pub_ng_stmtA_o 1 segs R HIA ENTRY add_mpi_R.
Definition mpi_sub_mpi_ng_stmtA_o segs R HIA ENTRY := mpi_addsub_pub_ng_stmtA_o (-1) segs R HIA ENTRY sub_mpi_R.

Lemma A_mpi_add_mpi_ng_spec_o : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "PR,$5:.PHIA,(5;.$<.R1.)P,(67.+1.$<.R2.R1.$42.)(68.$<.R3.R2.$69.)")
(* [comment removed for export] *).
Proof.
  intros R HIA HAS. unfold mpi_add_mpi_ng_stmtA_o, mpi_addsub_pub_ng_stmtA_o, A_MPI_ADD_MPI.
  intros until d. intros HH HK MX MA MB SXA SXB SAB NST NGS NGAB NGBA OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA1 IA2 IB2 A47B BUD UW UWX UWA UWB BUDF -> -> ->.
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
  apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep.
  intros mo1 [HK1 MF1].
  eapply aevtS_mono.
  { unfold add_sub_mpi_ng_stmtA_o in HAS.
    eapply HAS with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d); try eassumption; try reflexivity. }
  intros c PO. eapply binop_postA_mono; [exact MF1| | exact PO]. intros r dd. apply wrap_R_add.
Qed.

Lemma A_mpi_sub_mpi_ng_spec_o : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "PR,$5:.PHIA,(5;.$<.R1.)P,(67.-1.$<.R2.R1.$42.)(6:.$<.R3.R2.$6;.)")
(* [comment removed for export] *).
Proof.
  intros R HIA HAS. unfold mpi_sub_mpi_ng_stmtA_o, mpi_addsub_pub_ng_stmtA_o, A_MPI_SUB_MPI.
  intros until d. intros HH HK MX MA MB SXA SXB SAB NST NGS NGAB NGBA OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA1 IA2 IB2 A47B BUD UW UWX UWA UWB BUDF -> -> ->.
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
  apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep.
  intros mo1 [HK1 MF1].
  eapply aevtS_mono.
  { unfold add_sub_mpi_ng_stmtA_o in HAS.
    eapply HAS with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d); try eassumption; try reflexivity. }
  intros c PO. eapply binop_postA_mono; [exact MF1| | exact PO]. intros r dd. apply wrap_R_sub.
Qed.
