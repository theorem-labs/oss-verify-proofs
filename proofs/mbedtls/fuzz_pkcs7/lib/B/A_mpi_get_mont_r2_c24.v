(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_lset P_mpi_shift_l P_mpi_shrink P_mpi_divmod_stmt P_mpi_get_mont_r2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_copy A_mpi_journey A_mpi_journey2 A_mpi_add_abs_W A_mpi_lset A_mpi_shift_l A_mpi_shrink A_mpi_div_stmtA A_mpi_mod_stmtA A_mpi_mod_mpi_sz A_frame_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_shift_l_c24 A_mpi_shrink_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_get_mont_r2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AEvtS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_get_mont_r2_c24 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_xop_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_c24.mpi_xop_stmtA_c"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_get_mont_r2.mont_r2_R"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.get_mont_r2_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.get_mont_r2_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.gm_frame"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "WGM.GM_POST_A"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.binop_keep"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JBA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.BJA"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_mpi_sz.mod_mpi_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_mpi_sz.mod_mpi_FR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.mod_mpi_Rs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.A_MPI_MOD_MPI_E"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shrink.shrink_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shrink.shrink_FR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SHRINK"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.A_MPI_GET_MONT_R2"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset.mpi_lset_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_l_c24.mpi_shift_l_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SHIFT_L"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.mpi_mod_mpi_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shrink_c24.mpi_shrink_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.mpi_get_mont_r2_stmtA"].



(* [comment removed for export] *)



(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma mpi_xop_stmtA_c_of : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)PENTRY,$4.PSTACK,$4.PC24,$4.PP,P,$4.SpPPHI,P,$5.P,$4.$4.PFRC,P,$4.$4.PRr,P,(0.$6.)P,$5.P,$4.P,$4.P,$5.SpP,(7.R:.R9.R8.R7.R6.R4.R3.R2.R1.)(8.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros segs R HIA ENTRY STACK C24 P PHI FRC Rr H. unfold mpi_xop_stmtA_c. intros. eapply H; eassumption. Qed.


Section WGM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis HSHL : mpi_shift_l_stmtA_c asegs R HIA A_MPI_SHIFT_L.
  Hypothesis HMOD : mpi_mod_mpi_stmtA asegs R HIA A_MPI_MOD_MPI_E mod_mpi_PHI mod_mpi_FR.
  Hypothesis HSHR : mpi_shrink_stmtA_c asegs R HIA A_MPI_SHRINK.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dN : mpd) (lo slo d F0 : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation GM_FRAME := (gm_frame ra s0 s1 s2 s3).
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 40 GM_FRAME.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis UWN : uw_obj R (md_addr dN) 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) F0 d.
  Hypothesis F0SP : bv_unsigned sp <= F0.
  Hypothesis F0X : X + 16 <= F0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - MPI_GET_MONT_R2_STACK_A - arl_need_rt R.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 544 - arl_need_smalloc R.
  Hypothesis LFN : (length LF < 511)%nat.
  Hypothesis C24H : cnt24 LB + C24_GET_MONT_R2 <= C24MAX.
  Hypothesis MN0 : mpd_at asegs m LB dN.
  Hypothesis NRN : 0 <= md_n dN <= 10000.
  Hypothesis IN2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "P,(9.$:.(;.VdN,)$<.)P,Pi,$4.P,(=.(>.=R1.)(?.R1.(10.+4.(11.VdN,))))(9.$12.(13.$14.(15.(16.(17.VdN,)R2.)))$18.)(9.$12.(19.(17.VdN,)(10.+4.(11.VdN,)))$18.)")
(* [comment removed for export] *).
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Local Notation PHIb := (get_mont_r2_PHI dX dN).
  Local Notation FRb := (get_mont_r2_FR dX dN d).
  Local Notation G := (gmr2_G nX (md_n dN)).
  Hypothesis BUD : havol asegs R HIA h + PHIb <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FRb <= FR_MAX.

  Definition GM_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "(1:.$14.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(1<.VLB,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,)(1=.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,)(1>.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 40 GM_FRAME []).
  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation Nv := (Z_to_bv 64 (md_addr dN)).

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAM; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L12276552127.146L23050452915.148L29428324939.5  L31826389380.1  L33918012703.147L36792457560.148L61322865240.148L62784354520.148L66361310168.148Q29963071266.147Q33963780182.147Q36223636898.147Q3859172566.147 Q39849717666.147Q39974853590.147Q45996133718.147Q49411331106.147Q546509986.147  Q9887022678.147 00000J00d01601:01h02B02\03603P04B05005b06P07B08008^09P0:B0;0S2LF2ra2sp2s02s12s22s33LFNS2LF2ra2sp2s02s12s22s33LFNS1R2lo3LOS3ALO3ACPS2spS1R2LF2ra2sp2s02s12s22s32lo4SLO23LFN5NEEDR3SPRS2LF2ra2sp2s02s12s22s33LFNS2LF2ra2sp2s02s12s22s33LFNS2LF2ra2sp2s02s12s22s33LFNS2LF2ra2sp2s02s12s22s33LFNS1R3HIA1h2LF2ra2sp2s02s12s22s33LFN3TOP2hc3HT14HTOPS1R2LF2ra2sp2s02s12s22s32lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2ra2sp2s02s12s22s33LFN3TOP2hc3HT14HTOPS1R2LF2ra2sp2s02s12s22s32lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2ra2sp2s02s12s22s33LFN3TOP2hc3HT14HTOPS1R2LF2ra2sp2s02s12s22s32lo4SLO23LFN5NEEDR3LOSS1R2LF2ra2sp2s02s12s22s32lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2ra2sp2s02s12s22s33LFN3TOP2hc3HT14HTOPS1R3HIA1h2LF2ra2sp2s02s12s22s33LFN3TOP2hc3HT14HTOPS1R2LF2ra2sp2s02s12s22s32lo4SLO23LFN5NEEDR3LOS". (* [comment removed for export] *)
  #[using="IMG JC SLO2 LFN"] Lemma gm_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "Pv,$4.Pf,$4.Phc,(1?.$14.VR,VHIA,)PLBc,(0.$6.)Pmc,P,(20.&40.)(21.(20.&8.))PdXc,$5.Pr,$4.Pxra,(20.&40.)Pxt0,(20.&40.)Pxt1,(20.&40.)Pxt2,(20.&40.)Pxs0',(20.&40.)Pxs1',(20.&40.)Pxa1,(20.&40.)Pxa2,(20.&40.)Pxa3,(20.&40.)Pxa4,(20.&40.)Pxa5,(20.&40.)Pxa6,(20.&40.)Pxa7,(20.&40.)Pxs2',(20.&40.)Pxs3',(20.&40.)Pxt3,(20.&40.)Pxt4,(20.&40.)Pxt5,(20.&40.)Pxt6,(20.&40.)P,(22.$14.VR,VHIA,Vh,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.(23.Vra,Vs0,Vs1,Vs2,Vs3,)(24.$6.)R1:.R19.R18.R17.R16.R15.)P,(25.(9.$4.R15.=))P,(=.(?.(26.(27.+2.+1?.))R16.)(>.R16.=))P,(>.R1=.(1=.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,))P,(>.R1=.(1>.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,Vd,))(28.$14.(29.$14.VR,VHIA,R1=.Vmo,)$2:.(2;.(2<.R18.(2=.&40.(16.(2>.&40.Vsp,)-30.))Vgp,Vtp,R17.R16.R15.R14.R13.(2=.&40.R19.)R12.R11.R10.R?.R>.R=.R<.R;.R:.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(2=.&40.+:58?0.)Vfc,(2?.(20.&40.))R1;.(30.$14.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J RNZ HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold gm_frame in FR1. replace (bv_unsigned sp - 40) with (bv_unsigned sp + -40) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 5 zstep. zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold GM_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [split; [intros E; exfalso; exact (RNZ E)| exact HR]|]. split; [exact AD1|]. split; [exact PD1| exact FRS1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39220637093.0L58421668439.500000100BSS2LB3LBc3dXc1C2C1". (* [comment removed for export] *)
  #[using="JC"] Lemma gm_cnt24 : forall v f hc LBc mc dXc, XJ0 v f hc LBc mc dXc -> cnt24 LBc <= cnt24 LB + 1.
  Proof.
    intros v f hc LBc mc dXc J.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & _). cbn [app] in ND1. apply NoDup_map_inv in ND1.
    pose proof (xa_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as (_ & _ & O3 & _).
    assert (INC : incl LBc (LB ++ mpd_blk dXc)) by (intros b Hb; apply in_or_app; destruct (O3 b Hb) as [K|K]; [left; exact K| right; exact K]).
    pose proof (cnt24_incl _ _ ND1 INC) as C. rewrite cnt24_app in C.
    assert (C1 : cnt24 (mpd_blk dXc) <= 1).
    { unfold mpd_blk. destruct (md_own dXc); try (rewrite cnt24_nil; clear; lia).
      pose proof (cnt24_cons_le (md_p dXc, 4 * md_n dXc) []) as C2. rewrite cnt24_nil in C2. exact (proj2 C2). }
    clear - C C1. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L14497671162.18L14790846228.8 L18974673869.6 L19652550953.3 L21160436186.8 L22358645037.6 L25675610318.19L25953659214.1 L28119628375.5 L29307822744.1 L31826389380.1 L40290687782.1 L49631015752.1 L52332629803.3 L5261871668.3  L66151427842.16L67124785796.5 L67915715521.6 L67917781699.5 00000m01I01f01o02I02b03d03h04804<04@04C04G04Q04[05505I05]061S1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN1d4BUDF3FRx1f2hc2BF4HFR1S1R2sp2lo4SLO25NEEDR3LO03SPRS2LB4C24H4C24x5HC24x3LBc4C24cS2sp1a2HaS1R2sp1X2lo4SLO25NEEDR3DSXS1R2sp2lo4SLO25STACK4HSTKS1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN3BUD4PHIx3val1v2hc3dXc2BV3HV1S2spS1R3HIA1h2sp3TOPS2spS2spS1XS2spS2sp3dXc1QS1X2X03X16S2sp2r03SPA1q1r1H2H02q02H4S1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDR". (* [comment removed for export] *)
  #[using="IMG JC TPV UWX SLO2 C24H BUD BUDF"] Lemma gm_xop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "PENTRY,$4.PSTACK,$4.PC24x,$4.PP,P,$4.SpPPHIx,P,$5.P,$4.$4.PFRx,P,$4.$4.PRr,P,(0.$6.)P,$5.P,$4.P,$4.P,$5.SpP,(8.$14.VR,VHIA,R7.R6.R5.R4.R3.R2.R1.)P,(>.R7.+2=0.)P,(>.R7.+10.)P,PLBq,(0.$6.)Pdq,$5.Pvq,$4.Pr,$4.Pdq',$5.P,A5.R9.R5.R4.R3.R2.R1.(31.R6.R5.R2.)Pretpc,$4.Pval,$4.Pv,$4.Pf,$4.Phc,(1?.$14.VR,VHIA,)PLBc,(0.$6.)Pmc,P,(20.&40.)(21.(20.&8.))PdXc,$5.Pxt0,(20.&40.)Pxt1,(20.&40.)Pxt2,(20.&40.)Pxs1,(20.&40.)Pxa2,(20.&40.)Pxa3,(20.&40.)Pxa4,(20.&40.)Pxa5,(20.&40.)Pxa6,(20.&40.)Pxa7,(20.&40.)Pxs2,(20.&40.)Pxs3,(20.&40.)Pxt3,(20.&40.)Pxt4,(20.&40.)Pxt5,(20.&40.)Pxt6,(20.&40.)P,(22.$14.VR,VHIA,Vh,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.(23.Vra,Vs0,Vs1,Vs2,Vs3,)(24.$6.)R16.R15.R14.R13.R12.R11.)P,(32.$14.VR,VHIA,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdN,)P,(33.$14.VR,VHIA,VLF,Vsp,VdN,R16.R15.R14.R13.)P,A1.R23.R1:.P,(=.(>.=R1<.)(?.R1<.(27.+2.+40.)))P,(9.$4.(34.R1=.+2.)=)P,(>.=A2.R25.R17.R1=.)P,(>.=A1.R25.Vd,)P,(>.(16.R1>.A2.R27.R19.R1?.)(1=.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,))P,(>.(16.R1>.A1.R27.Vd,)(1>.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,Vd,))P,Pr,$4.Ph2,(1?.$14.VR,VHIA,)PLB2,(0.$6.)Pm2,P,(20.&40.)(21.(20.&8.))PdX2,$5.Py0,(20.&40.)Py1,(20.&40.)Py2,(20.&40.)Pya1,(20.&40.)Pya2,(20.&40.)Pya3,(20.&40.)Pya4,(20.&40.)Pya5,(20.&40.)Pya6,(20.&40.)Pya7,(20.&40.)Py3,(20.&40.)Py4,(20.&40.)Py5,(20.&40.)Py6,(20.&40.)P,(22.$14.VR,VHIA,Vh,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.(23.Vra,Vs0,Vs1,Vs2,Vs3,)(24.$6.)(16.R33.A2.R3<.R2>.R34.)(16.R32.A1.R3;.Vd,)R12.R11.R10.R?.)P,(33.$14.VR,VHIA,VLF,Vsp,VdN,R13.R12.R11.R10.)P,A5.R3<.R32.R30.R36.R15.R11.(28.$14.(29.$14.VR,VHIA,R15.Vmo,)$2:.(2;.(2<.(2=.&40.R38.)(2=.&40.(16.(2>.&40.Vsp,)-30.))Vgp,Vtp,R11.R10.R?.(2=.&40.VX,)R2=.(2=.&40.R16.)R>.R=.R<.R;.R:.R9.R8.R26.R25.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(2=.&40.R38.)Vfc,(2?.(20.&40.))R13.(30.$14.)))(28.$14.(29.$14.VR,VHIA,R1?.Vmo,)$2:.(2;.(2<.(2=.&40.R23.)(2=.&40.(16.(2>.&40.Vsp,)-30.))Vgp,Vtp,R1;.R1:.R19.(2=.&40.VX,)R18.(2=.&40.VX,)(2=.&40.R22.)R17.R16.R15.R14.R13.R12.R11.R10.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(2=.&40.R2>.)Vfc,(2?.(20.&40.))R1=.(30.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros ENTRY STACK C24x P PHIx FRx Rr HXOP HSTK HC24x KEEP. intros until xt6. intros J DBJ B PV RPC RPE PHI0 FR0 BV BF K.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    replace (bv_unsigned sp - 40) with (bv_unsigned sp + -40) in ST1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -40) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -40 - Z.of_nat 8) with (bv_unsigned sp + -48) in STc, SLOT by (clear; lia).
    assert (SPR' : 0 <= bv_unsigned sp + -48 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    pose proof HXOP as SPc. unfold mpi_xop_stmtA_c in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (v := val) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by exact SPR'; rewrite ?AD1;
        first [ exact HH1 | exact HK1 | exact MX1 | exact NS1 | exact PV | exact STc | exact LOS | exact TPV | exact MI1 | exact UWX | reflexivity
              | lazymatch goal with
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear; lia| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- _ <= bv_unsigned sp + -48 - STACK - _ => clear - SLO2 HSTK; lia
                | |- bv_unsigned sp + -48 <= htop _ _ _ _ => rewrite HT1; clear - TOP; lia
                | |- (bv_unsigned sp + -48) mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 retpc) mod 2 = 0 => rewrite unsigned_lit by exact RPC; exact RPE
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (NS1 E)]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BV BUD HV1; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BF BUDF HFR1; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite ?(unsigned_lit X) by (clear - X0 X16; lia); eapply uw_obj_uwc; [exact UWX| clear; lia]
                end
              | (lazymatch goal with |- context [cnt24] => idtac end; match goal with Jx : _ |- _ => let C := fresh "C24c" in pose proof (gm_cnt24 _ _ _ _ _ _ Jx) as C; clear - C C24H HC24x; unfold C24_GET_MONT_R2 in C24H; lia end) | match goal with |- ?g => idtac "XOP-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2, HP2 by exact SPR'. rewrite AD1 in HP2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    pose proof (KEEP _ _ _ _ _ CR) as BK.
    assert (SLOT2 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 8 junk]).
    { eapply presA_rw_cells; [exact HP2| exact SLOT| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia|].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - DSX LOSP SLO2 NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 40)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT2. }
    pose proof (xa_call asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -48) (PHIx dXc val) (FRx d) J ltac:(clear - SLO2 NEEDR; lia)
                  PHI0 FR0 MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    pose proof (bja_call asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC dN DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -48) J B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J1| exact B1| exact CR].
    all: match goal with |- ?g => idtac "XOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0?L13659323240.18L14790846228.8 L19652550953.3 L21160436186.8 L21502385847.4 L25953659214.1 L28119628375.5 L28131752567.6 L28704391748.3 L29307822744.1 L31826389380.1 L37702038419.4 L3809880505.4  L38569812941.1 L40290687782.1 L41886271693.1 L45709246995.4 L48452373949.4 L49459626090.3 L49547649940.4 L49631015752.1 L52332629803.3 L5261871668.3  L54669551926.5 L59321673169.3 L62281765211.17L63541775392.7 L66151427842.16L67124785796.5 L67915715521.6 L67917781699.5 00000m01I01R01l02<02@02P02f03203603:03H03V03[03^03c04004B04L04Z04^04h05205?05I06B06_07907M07a085S1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN1d4BUDF1f2hc3dXc2BF4HFR1S1R2sp2lo4SLO25NEEDR3LO03SPRS2sp1a2HaS1R2sp1X2lo4SLO25NEEDR3DSXS2dN3NRN3dXc3NR1S2spS1R3HIA1h2sp3TOPS1R3HIA1h2sp3TOP5HTOP0S2sp2lo4LOSPS2spS2spS1R2sp2lo4SLO2S2sp2dN2lo3ESKS3dXcS1XS3dXcS2sp2dN2lo2ESS2LB4C24H3LBc4C24cS1X2dN3SXBS1R2sp2lo4SLO3S2spS2sp3dXc1QS1X2X03X16S2sp1X2lo3DSXS1X2dN3SXBS1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN3BUD1v2hc3dXc2BV3HV1S1R2sp2lo3slo4SLO24SLOL5NEEDRS2sp2r03SPA1q1r1H2H02q02H4S1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDR". (* [comment removed for export] *)
  #[using="IMG HMOD JC TPV UWX UWN D0 SLO2 SLO3 LFN C24H MN0 NRN IN2 SLOS SLOL BUD BUDF"] Lemma gm_mod : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "Pretpc,$4.Pv,$4.Pf,$4.Phc,(1?.$14.VR,VHIA,)PLBc,(0.$6.)Pmc,P,(20.&40.)(21.(20.&8.))PdXc,$5.Pxt0,(20.&40.)Pxt1,(20.&40.)Pxt2,(20.&40.)Pxs1,(20.&40.)Pxa3,(20.&40.)Pxa4,(20.&40.)Pxa5,(20.&40.)Pxa6,(20.&40.)Pxa7,(20.&40.)Pxs2,(20.&40.)Pxs3,(20.&40.)Pxt3,(20.&40.)Pxt4,(20.&40.)Pxt5,(20.&40.)Pxt6,(20.&40.)P,(22.$14.VR,VHIA,Vh,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.(23.Vra,Vs0,Vs1,Vs2,Vs3,)(24.$6.)R15.R14.R13.R12.R11.R10.)P,(32.$14.VR,VHIA,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdN,)P,(33.$14.VR,VHIA,VLF,Vsp,VdN,R15.R14.R13.R12.)P,(35.$14.(36.VR,)Vm,Vslo,(2>.&40.Vsp,))P,(=.(>.=R1:.)(?.R1:.(27.+2.+40.)))P,(9.$4.(34.R1;.+2.)=)P,(>.(16.R1;.(37.R16.R16.VdN,))(1=.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,))P,(>.(16.R1;.(38.R17.R17.VdN,Vd,))(1>.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,Vd,))P,Pr,$4.Ph2,(1?.$14.VR,VHIA,)PLB2,(0.$6.)Pm2,P,(20.&40.)(21.(20.&8.))PdX2,$5.Py0,(20.&40.)Py1,(20.&40.)Py2,(20.&40.)Pya1,(20.&40.)Pya2,(20.&40.)Pya3,(20.&40.)Pya4,(20.&40.)Pya5,(20.&40.)Pya6,(20.&40.)Pya7,(20.&40.)Py3,(20.&40.)Py4,(20.&40.)Py5,(20.&40.)Py6,(20.&40.)P,(22.$14.VR,VHIA,Vh,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.(23.Vra,Vs0,Vs1,Vs2,Vs3,)(24.$6.)(16.R30.(37.R2;.R2;.VdN,))(16.R2?.(38.R2;.R2;.VdN,Vd,))R12.R11.R10.R?.)P,(33.$14.VR,VHIA,VLF,Vsp,VdN,R13.R12.R11.R10.)P,(39.R2?.R2=.R2=.VdN,R15.R11.)(28.$14.(29.$14.VR,VHIA,R15.Vmo,)$2:.(2;.(2<.(2=.&40.R34.)(2=.&40.(16.(2>.&40.Vsp,)-30.))Vgp,Vtp,R11.R10.R?.(2=.&40.VX,)R2:.(2=.&40.R16.)R>.R=.R<.R;.R:.R9.R8.R24.R23.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(2=.&40.R34.)Vfc,(2?.(20.&40.))R13.(30.$14.)))(28.$14.(29.$14.VR,VHIA,R1<.Vmo,)$2:.(2;.(2<.(2=.&40.R1?.)(2=.&40.(16.(2>.&40.Vsp,)-30.))Vgp,Vtp,R18.R17.R16.(2=.&40.VX,)R15.(2=.&40.VX,)(2=.&40.VX,)(2=.&40.(3:.VdN,))R14.R13.R12.R11.R10.R?.R>.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(2=.&40.$3;.)Vfc,(2?.(20.&40.))R1:.(30.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J DBJ B SSH RPC RPE BV BF K.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1, HPX1.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP0.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof DBJ as [MBj OB CRB CRBL SXB BIMG]. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    cbn [md_addr md_own md_p md_n] in SXB, OB1, OB2, OB3, OB4, OB5.
    destruct (bja_client _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ [] v f hc LBc mc dXc LBc lo J B ltac:(intros bq Hb _; exact Hb) ltac:(clear - LOSP; lia)) as [CRB1 CRBL1].
    pose proof (opnd_atA_mpd_back _ _ _ _ _ _ _ _ _ MN0 (bj_at _ _ _ _ _ _ _ _ _ _ B)) as MN1.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    pose proof (xa_crX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ lo J ltac:(clear - LOSP; lia)) as CRX1. cbn [app] in CRX1.
    replace (bv_unsigned sp - 40) with (bv_unsigned sp + -40) in ST1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -40) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -40 - Z.of_nat 8) with (bv_unsigned sp + -48) in STc, SLOT by (clear; lia).
    assert (SPR' : 0 <= bv_unsigned sp + -48 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    (* [comment removed for export] *)
    assert (SSH1 : sshad asegs AL mc slo (bv_unsigned sp + -48)).
    { destruct (sshad_split asegs AL m slo (bv_unsigned sp + -48) (bv_unsigned sp) SSH ltac:(clear - SLOL SLO2 NEEDR; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia)) as [SSa _].
      eapply (presA_sshad asegs R); [exact HPX1| exact SSa| exact SLOS| clear - TOP HTOP0; lia]. }
    pose proof (gm_cnt24 _ _ _ _ _ _ J) as C24c.
    assert (PHI0' : 0 <= mod_mpi_PHI dXc dXc dN) by (rewrite mod_mpi_PHI_val; clear - NR1 NRN; lia).
    assert (FR0' : 0 <= mod_mpi_FR dXc dXc dN d) by (rewrite mod_mpi_FR_val; clear - NR1 D0; nia).
    pose proof HMOD as SPc. unfold mpi_mod_mpi_stmtA in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (dA := dXc) (dB := dN) (lo := lo) (slo := slo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by exact SPR'; rewrite ?AD1;
        first [ exact HH1 | exact HK1 | exact LFN | exact MX1 | exact MN1 | exact NS1 | exact STc | exact LOS | exact SSH1 | exact SLOS | exact SLOL | exact TPV | exact MI1 | exact UWX | exact UWN
              | exact CRX1 | exact CRB1 | exact CRBL1 | exact IN2 | reflexivity
              | lazymatch goal with
                | |- mpd_sep dXc dXc => left; reflexivity
                | |- mpd_sep dXc dN => right; rewrite AD1; clear - SXB; lia
                | |- X <> md_addr dN => clear - SXB; lia
                | |- opnd_sep dXc dXc _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [intros NN; destruct (OWN1 NN) as (EH & _); exact (XP1 EH)|];
                    split; [exact XP1|]; split; [left; reflexivity|]; split; [clear - DSX LOSP; lia|];
                    intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- opnd_sep dXc dN _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [exact OB1|]; split; [exact (bj_sepS _ _ _ _ _ _ _ _ _ _ B)|];
                    split; [right; destruct (md_own dXc) eqn:EOX; [left; discriminate| | left; discriminate];
                            destruct (md_own dN) eqn:EOB; [right; left; reflexivity| |];
                            right; right; apply (bj_sepL _ _ _ _ _ _ _ _ _ _ B EOX); rewrite EOB; discriminate|];
                    split; [clear - ES; lia|]; intros BN; ddestruct (OWNE1 BN) as (_ & _ & _ & _ & ESK & _); clear - ESK; lia
                | |- md_own dXc = LHeap -> client_range _ _ _ (md_p dXc) _ =>
                    intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & XIN & _);
                    eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear; lia| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- _ <= bv_unsigned sp + -48 - MPI_MOD_MPI_STACK_A - _ => clear - SLO2; lia
                | |- _ <= bv_unsigned sp + -48 - 496 - _ => clear - SLO3; lia
                | |- bv_unsigned sp + -48 <= htop _ _ _ _ => rewrite HT1; clear - TOP; lia
                | |- (bv_unsigned sp + -48) mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 retpc) mod 2 = 0 => rewrite unsigned_lit by exact RPC; exact RPE
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (NS1 E)]
                | |- mpd_aobjA _ _ _ _ dN => split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)| intros E; apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B); rewrite E; discriminate]
                | |- md_own dXc = LStatic -> _ => intros E; exfalso; exact (NS1 E)
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BV BUD HV1; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BF BUDF HFR1; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_DIV_MPI; unfold C24_GET_MONT_R2 in C24H; clear - C24c C24H; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite ?(unsigned_lit X) by (clear - X0 X16; lia); eapply uw_obj_uwc; [exact UWX| clear; lia]
                end
              | match goal with |- ?g => idtac "MOD-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2, HP2 by exact SPR'. rewrite AD1 in HP2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    pose proof CR as [[_ BK] _].
    assert (SLOT2 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 8 junk]).
    { eapply presA_rw_cells; [exact HP2| exact SLOT| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia|].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - DSX LOSP SLO2 NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 40)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size [CB 8 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT2. }
    pose proof (xa_call asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -48) (mod_mpi_PHI dXc dXc dN) (mod_mpi_FR dXc dXc dN d) J ltac:(clear - SLO2 NEEDR; lia)
                  PHI0' FR0' MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    pose proof (bja_call asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC dN DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -48) J B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J1| exact B1| exact CR].
    all: match goal with |- ?g => idtac "MOD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L10718258113.1 L2397676628.0  L26892418956.1 L29956516996.0 L33440820996.4 L35549650514.4 L40281191306.3 L40738020909.4 L40995609823.18L42229184147.4 L50735688570.18L52437841502.8 L5299041245.17 L59308660947.1 L62018535662.1 L62037211595.6 L62484994806.2 L64491265552.2 L7717366441.17 L8288358526.4  00000400500900:00J00V00_01101m02;03703N04G04K04N04d04l05205k067S2spSS2spSS2sp2F04F0SP3SPRS2sp2lo4LOSPS1R3HIA1hS2LB4C24H3LBc4C24cS1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN1v2hc3dXc2BV3HV12h23HV2S1R2sp2lo4SLO2S1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN1d1f2hc2BF4HFR12h24HFR2S1R3HIA1h1X2F03F0X1a2HaS1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN3BUD1v2hc3dXc2BV3HV1S2E0S1RS1R2sp2lo3LOS4LOSP3SPRS2dN3NRNS1d2D0S1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dN1d4BUDF1f2hc2BF4HFR1S2dN3NRN3dXc". (* [comment removed for export] *)
  #[using="IMG HSHR F0 JC TPV RAE UWX D0 UW F0SP F0X SLO2 C24H NRN BUD BUDF"] Lemma gm_tail : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "Pv,$4.Pf,$4.Phc,(1?.$14.VR,VHIA,)PLBc,(0.$6.)Pmc,P,(20.&40.)(21.(20.&8.))PdXc,$5.Pxt0,(20.&40.)Pxt1,(20.&40.)Pxt2,(20.&40.)Pxa2,(20.&40.)Pxa3,(20.&40.)Pxa4,(20.&40.)Pxa5,(20.&40.)Pxa6,(20.&40.)Pxa7,(20.&40.)Pxt3,(20.&40.)Pxt4,(20.&40.)Pxt5,(20.&40.)Pxt6,(20.&40.)P,(22.$14.VR,VHIA,Vh,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.(23.Vra,Vs0,Vs1,Vs2,Vs3,)(24.$6.)R13.R12.R11.R10.R?.R>.)P,(>.(16.R14.(3<.R?.(11.VdN,)))(1=.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,))P,(>.(16.R14.(3=.Vd,))(1>.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdN,Vd,))(28.$14.(29.$14.VR,VHIA,R14.Vmo,)$2:.(2;.(2<.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,(2=.&40.VX,)(2=.&40.(11.VdN,))R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(2=.&40.$3>.)Vfc,(2?.(20.&40.))R12.(30.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1, HPX1.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP0.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    (* [comment removed for export] *)
    assert (STS : stk asegs mc lo (bv_unsigned sp)).
    { pose proof (stk_release asegs mc lo (bv_unsigned sp - 40) GM_FRAME ST1 FR1 ltac:(clear - LOSP LO0; lia)) as ST. rewrite FSZ in ST.
      replace (bv_unsigned sp - 40 + 40) with (bv_unsigned sp) in ST by (clear; lia). exact ST. }
    (* [comment removed for export] *)
    assert (UWc : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned s0) (bv_unsigned sp) d).
    { rewrite HS1. eapply uwc_floor; [| exact F0SP].
      eapply (uwc_presA R); [exact HPX1| exact UW| exact F0SP| intros a Ha; cbn [outside fst snd]; split; [clear - Ha F0X; lia| exact I]| clear - F0SP SPR; lia|].
      apply hstkhi_le64. clear - LOS LOSP SPR; lia. }
    assert (PHI0' : 0 <= shrink_PHI dXc (md_n dN)) by (unfold shrink_PHI, grow_PHI; unfold AVOL_CALL; clear - NR1 NRN; lia).
    assert (FR0' : 0 <= shrink_FR d) by (unfold shrink_FR, calls_FR, fr_charge; clear - D0; lia).
    pose proof HSHR as SPc. unfold mpi_shrink_stmtA_c, mpi_xop_stmtA_c in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (v := md_n dN) (lo := lo) (d := d); rewrite ?AD1;
        first [ exact HH1 | exact HK1 | exact MX1 | exact NS1 | exact STS | exact LOS | exact TPV | exact MI1 | exact UWX | exact UWc | exact RAE | exact SPA | reflexivity
              | lazymatch goal with
                | |- 0 <= md_n dN < 2^64 => clear - NRN; lia
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; exact CWX| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => exact XLS1
                | |- _ <= bv_unsigned sp - 96 - _ => clear - SLO2; lia
                | |- bv_unsigned sp <= htop _ _ _ _ => rewrite HT1; exact TOP
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (NS1 E)]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BV BUD HV1; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BF BUDF HFR1; lia
                end
              | (lazymatch goal with |- context [cnt24] => idtac end; match goal with Jx : _ |- _ => let C := fresh "C24c" in pose proof (gm_cnt24 _ _ _ _ _ _ Jx) as C; clear - C C24H; unfold C24_SHRINK_c; unfold C24_GET_MONT_R2 in C24H; lia end) | match goal with |- ?g => idtac "TAIL-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). apply aevtS_now. unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    rewrite AD1 in HP2.
    unfold GM_POST_A, mpi_binop_postA. dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m2, mo2, h2, LB2, dX2, r.
    dpose OUT2 as (OA & ONS & O3 & O4 & O5).
    split; [exact E|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact (mo_frame_trans _ _ _ MF1 MF2)|].
    split.
    { eapply presA_trans; [exact HPX1|]. rewrite HS1 in HP2.
      eapply presA_weaken; [exact HP2| intros b Hb; eapply xa_keep_keep; [exact J| exact Hb]| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    split; [rewrite HT2; exact HT1|]. split; [rewrite HS2; exact HS1|]. split; [rewrite HF2; exact HF1|]. split; [exact HK2|].
    split; [intros x Hx; apply HCS2, HCS1, Hx|]. split; [clear - HV2 HV1 BV; lia|]. split; [clear - HFR2 HFR1 BF; lia|].
    split; [exact HH2|]. split; [exact MX2|].
    split.
    { eapply mpd_out_trans; [exact OUT1| exact OUT2| exact FRS1|].
      intros b Hb. unfold mpd_blk in Hb. pose proof MX as [(_ & _ & _ & _ & _ & OW) _]. cbn [md_own md_p md_n] in OW, Hb. destruct ownX; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)). }
    split; [exact (xa_fresh_call asegs R HIA h LB LF m dX sp lo 40 GM_FRAME _ _ _ _ _ _ _ J FRA2)|].
    (* [comment removed for export] *)
    destruct CR as [CR1 CFR].
    assert (FRS2 : forall b, In b (mpd_blk dX2) -> In b (mpd_blk dX) \/ ~ In b LB).
    { intros b Hb. destruct (CFR b Hb) as [C|C]; [exact (FRS1 b C)|].
      destruct (in_dec blk_eq_dec b LB) as [Hin|Hnin]; [| right; exact Hnin].
      left. destruct (in_dec blk_eq_dec b (mpd_blk dX)) as [Hx|Hx]; [exact Hx|]. exfalso.
      dpose OUT1 as (_ & _ & _ & P4 & _). exact (C (P4 b Hin Hx)). }
    unfold mont_r2_R. cbn [md_addr md_pad].
    destruct CR1 as [(-> & SG2 & PD2 & VAL2 & NB2 & _)|(-> & ->)].
    - split; [split; [intros _; exact NB2| clear; lia]|]. split; [rewrite OA; exact AD1|]. split; [rewrite PD2; exact PD1| exact FRS2].
    - split; [split; [intros E0; exfalso; clear - E0; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in E0; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]|].
      split; [exact AD1|]. split; [exact PD1| exact FRS2].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma lset_keep : forall LBq dq vq r dq', lset_R vq dq LBq r dq' -> binop_keep LBq dq dq'.
  Proof.
    intros LBq dq vq r dq' [CR1 [CA CF]]. split; [exact CA|]. destruct CR1 as [(_ & EN & _ & _ & _ & EP)|(_ & ->)].
    - split; [exact EP|]. split; [exact CF|]. rewrite EN. apply Z.le_max_l.
    - split; [reflexivity|]. split; [exact CF| apply Z.le_refl].
  Qed.

  Hypothesis SXN : mpd_sep dX dN.
  Hypothesis NEN : X <> md_addr dN.
  Hypothesis ON : opnd_sep dX dN lo (bv_unsigned sp).
  Hypothesis CRN : client_range L (LB ++ fdata LF) lo (md_addr dN) 16.
  Hypothesis CRNL : md_own dN = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dN) (4 * md_n dN).

  (* [comment removed for export] *)
  #[using="IMG MN0 IN2 SXN NEN ON CRN CRNL"] Lemma gm_mkJB : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "Pm1,P,(20.&40.)(21.(20.&8.))P,(3?.$14.(36.VR,)(40.$14.VR,VHIA,Vh,)R1.(3:.VdN,)+10.)P,P,(9.$:.(;.VdN,)$<.)(3?.$14.(36.VR,)(40.$14.VR,VHIA,Vh,)R3.(17.VdN,)(10.+4.(11.VdN,)))P,(41.$14.VR,VHIA,Vh,VLB,VLF,R3.)P,(42.$14.R4.VLB,VdN,)(=.(32.$14.VR,VHIA,VLB,VLF,Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdN,)(33.$14.VR,VHIA,VLF,Vsp,VdN,Vh,VLB,R5.(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros m1 OEs OEl HM1 ME1'. dpose ON as (OE1 & OE2 & OE3 & OE4 & OE5).
    pose proof (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dN ME1') as ME1.
    assert (SXE : X + 16 <= md_addr dN \/ md_addr dN + 16 <= X).
    { destruct SXN as [E|D']; [exfalso; apply NEN; rewrite <- E; reflexivity| cbn [md_addr] in D'; exact D']. }
    split.
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
      + apply opnd_atA_mpd. exact MN0.
      + intros EO RO hc LBc mc HMc. eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IN2 EO RO)].
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + exact ME1.
      + exact OE2.
      + intros EOX EN. destruct OE3 as [C|[C|[C|C]]]; [exfalso; apply NEN; rewrite <- C; reflexivity| exfalso; exact (C EOX)| exfalso; exact (EN C)| exact C].
      + exact OEs.
      + intros EN. pose proof ME1' as [(_ & _ & _ & _ & _ & OW) _].
        destruct (md_own dN) eqn:EOB; [exfalso; exact (EN eq_refl)| |].
        * ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HM1| exact EIN].
        * exact (OEl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02:0@D11189028015.143D11189028015.144D35881667587.143D35881667587.144L10665155323.0  L11741095640.137L13645206873.0  L14186142497.0  L15213661085.4  L16673921450.10 L16777705924.6  L18457785511.0  L19354909044.138L19864887895.6  L19945316590.2  L2026054197.5   L22594986486.2  L23050452915.256L24348682763.0  L25075866052.4  L25382082548.138L25953659214.1  L26924648792.138L2710430330.6   L27164244425.0  L2818029122.6   L29008472870.247L29008472871.215L29010569984.177L29956516996.0  L30264455194.0  L31378308326.139L31392867444.138L31826389380.1  L34519741522.6  L35653441506.7  L36792457560.256L37414286068.138L37957693920.4  L39236637173.0  L40065549985.0  L40359052201.0  L40460783479.3  L40834179097.151L41124400531.4  L43059266230.137L43101472727.6  L43442376564.137L43645687862.1  L43654564952.138L50971777526.0  L52179438016.2  L54728834635.6  L55800229587.7  L5581275937.0   L57174599625.0  L57234917278.7  L58641002120.185L58641002120.256L58643001982.182L59308632561.1  L59310729686.1  L59499841752.138L60098763854.3  L61277434550.1  L61322865240.256L62483286412.184L62784354520.256L66187946659.1  L66361310168.256L67915715521.6  L7510805464.138 L8288018255.5   Q15640968643.258Q15643324129.139Q16285785003.188Q16285785003.259Q17968854497.187Q17970951589.258Q17971112229.188Q17971112229.259Q17971162649.185Q17971209889.256Q18364619715.258Q18365925601.140Q18696506101.153Q21800401414.153Q24793689041.153Q25160350961.153Q25513505925.142Q25513505925.143Q25604052563.140Q25604052563.141Q25664719138.153Q26649242741.153Q31226872993.153Q31396957457.153Q31814220267.185Q31814234451.256Q32653145795.258Q32655500769.140Q33915375776.258Q33918256002.140Q35016271767.153Q35715139857.153Q37821600610.142Q37821600610.143Q3830427394.140 Q3831741472.258 Q39212284437.188Q39212284437.259Q39939554818.140Q39941909792.258Q4141071397.153 Q44648843873.140Q44651206979.258Q49698585326.141Q49698585326.142Q51233956931.258Q51235796833.140Q51750120816.258Q51752217908.187Q53972118266.153Q60303346116.188Q60303346116.259Q60511567613.188Q60511567613.259Q61800308129.153Q6414620453.153 Q64253126389.153Q66522067074.140Q66524423072.258Q67528989526.143Q67528989526.144Q9540606334.256 Q9540653510.185 Q9841528480.258 Q9843367298.139 00001:02D03?04:04;04[04\04]04i05H05^05_06?06T06[06m07507]07^07e08E08I08i09?09@09U09V09W09X09Y09Z0::0:Z0:^0;30;K0<30<S0<a0<b0<c0<d0<o0=Q0=_0>V0>f0?F0?J0?j0?k0@30@F0@[0@\0@]0A30A`0BO0C<0C@0CE0Ce0Co0D30D[0EE0Em0F10FY0Fm0GM0G_0HC0Hd0IH0Il0JM0Jn0KO0L00LQ0M20MV0N70NY0NZ0N[0O=0Om0P]0Q>0Q_0Q`0Qa0RD0R_0S@0Sa0TE0Tf0UO0V50VX0VY0WN0XC0Xi0YR0Z30ZT0[:0[c0[d0\E0\i0]U0^A0^e0_F0_g0`H0`k0aL0am0bK0bi0bj0cL0cM0d30d\0eQ0fF0fd0gB0gk0hQS1R2LF2ra2sp2s02s12s22s31X3xs02lo4SLO23LFN5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R2LF2ra2sp2s02s12s22s31X3xs02lo4SLO23LFN5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s02s12s22s31X3xs03LFN3TOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s02s12s22s31X3xs03LFN3TOP2HB5Ha_st5Hl_stSS2LF2ra2sp2s02s12s22s31X3xs03LFNSSS2sp2dN2lo1HS2nX2dN2G13dX22N23dX33dX42V32N4S2nX2dN3dX22N23SUB3SLBSS2LF2ra2sp2s02s12s22s31X3xs03LFNS2nX2dN3dX23dX32V22N3S2sp2loS2nX2dN3dX22N23SUBS2dN3NRNS2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN1rSS2nX2dNS2LF2ra2sp2s02s12s22s31X3xs03LFNS2spS2LF2ra2sp2s02s12s22s31X3xs03LFNS2nX2dN3NRN3dX22N23SUBSS2nX2dN3NRN2G13dX22V2FFFSSS2LF2ra2sp2s02s12s22s31X3xs03LFNS2LF2ra2sp2s02s12s22s31X3xs03LFNS2spS2nX2dN2G13dX23dX32V3S1R3HIA1h2sp2lo3TOP4HTOPS2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN1rS2LF2ra2sp2s02s12s22s31X3xs03LFNS2nX2dN3NRN2G1SSSS2nX2dN3NRNS1R2LF2ra2sp2s02s12s22s31X3xs03LFNS2sp2dN2lo3ON4S1R2LF2ra2sp2s02s12s22s31X3xs02lo4SLO23LFN5NEEDR2X03SPRS2nX2dN1d3dX32F3S2LF2ra2sp2s02s12s22s31X3xs03LFNS2dNS2LF2ra2sp2s02s12s22s31X3xs03LFNSS2dN3NRNS2nX2dN1d2D03dX32F3S2nX2dN3dX23dX32V22N3SSS2nX2dN3dX32N33dX43SZ4S2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN2E03E16S2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN2E03E161rS2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN2E03E16S2KRS3KR3S2LF2ra2sp2s02s12s22s31X3xs03LFNS1R2lo3LOSS2spS2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN1rS2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN3NRNS2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN1rS2spS2LF2ra2sp2s02s12s22s31X2nX3xs02dN3LFN1rS1R2sp2lo4SLO25NEEDRS2LF2ra2sp2s02s12s22s31X3xs03LFNS2nX2dN3dX22N23SLBS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFNS2LF2ra2sp2s02s12s22s33xs02lo3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFN2E0S2LF2ra2s02s12s22s32nX3xs02dN3LFN2E0S2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFNS2LF2ra2sp2s02s12s22s33xs02lo3LFNS1R2LF2ra2s02s12s22s33xs03LFN4IMG'FFS1R2LF2ra2s02s12s22s33xs03LFN4IMG'S2LF2ra2sp2s02s12s22s33xs02lo3LFN2HB5Ha_st5Hl_stS2LF2ra2sp2s02s12s22s33xs02lo3LFN2HB5Ha_st5Hl_stS2LF2ra2sp2s02s12s22s33xs03LFN2HBS2LF2ra2sp2s02s12s22s33xs03LFN2HBFFS1R2LF2ra2s02s12s22s33xs03LFN5ALWF'S2LF2ra2s02s12s22s33xs03LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFNS2LF2ra2sp2s02s12s22s33xs02lo3LFNS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFN4LOSPS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSPS1R2LF2ra2s02s12s22s33xs03LFN5ALWF'FS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSP2HB5Ha_st5Hl_stS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSP2HB5Ha_st5Hl_stS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSPS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFN4LOSPS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSPS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFN4LOSPFS2LF2ra2sp2s02s12s22s33xs02lo3LFNS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFNS2LF2ra2sp2s02s12s22s33xs03LFN4SP642HB5Ha_stS2LF2ra2sp2s02s12s22s33xs03LFN4SP642HB5Ha_stS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFNS2LF2ra2sp2s02s12s22s33xs02lo3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS1R2LF2ra2s02s12s22s33xs03LFN5ALWF'S2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs02dN3LFNS2LF2ra2s02s12s22s32nX3xs03LFNS2LF2ra2s02s12s22s32nX3xs03LFNFS1R2LF2ra2s02s12s22s33xs03LFN4IMG'FS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSPS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFN4LOSPS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSP2HB5Ha_st5Hl_stS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSP2HB5Ha_st5Hl_stS2LF2ra2s02s12s22s32nX3xs03LFNS2LF2ra2s02s12s22s32nX3xs03LFNS2LF2ra2sp2s02s12s22s32nX3xs02lo3LFN4LOSPS2LF2ra2sp2s02s12s22s33xs02lo3LFN4LOSP". (* [comment removed for export] *)
  #[using="IMG HLSET HSHL HMOD HSHR F0 JC TPV RAE UWX UWN D0 UW F0SP F0X SLO2 SLO3 LFN C24H MN0 NRN IN2 SLOS SLOL BUD BUDF SXN NEN ON CRN CRNL"] Lemma gm_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)P,(43.$14.VR,VHIA,Vh,Vmo,)P,(44.$14.Vm,Vlo,(2>.&40.Vsp,))P,(45.$14.Vm,)P,(35.$14.(36.VR,)Vm,Vslo,(2>.&40.Vsp,))P,(46.$14.(36.VR,)(40.$14.VR,VHIA,Vh,)Vm,(1;.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(46.$14.(36.VR,)(40.$14.VR,VHIA,Vh,)Vm,VdN,)(47.$14.$2:.(48.(2;.(2<.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(2=.&40.VX,)(2=.&40.(3:.VdN,))R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(2=.&40.$49.)Vfc,(2?.(20.&40.))Vm,(30.$14.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK ST MI SSH OXA ONA. unfold A_MPI_GET_MONT_R2.
    pose proof (SSH : gm_keep _) as SSHm. clear SSH.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 40 GM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    dpose ON as (ON1 & ON2 & ON3 & ON4 & ON5).
    pose proof OXA as [OX _]. pose proof ONA as [ONs ONl]. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    do 6 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jk :: _) =>
      change (rw_cells asegs m1 (bv_unsigned sp + -48) ([CB 8 jk] ++ GM_FRAME)) in FR end.
    apply rw_cells_app in FR. destruct FR as [SLOT FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp - 40) in FR by (clear; lia).
    lazymatch type of SLOT with rw_cells _ _ _ [CB 8 ?jk] => set (slot0 := jk) in SLOT end.
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp - 40)).
    { eapply stk_merge; [exact ST| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size [CB 8 slot0])) by (cbn; clear; lia).
      eapply stk_of_rw_cells. exact SLOT. }
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    assert (MN1 : mpd_at asegs m1 LB dN).
    { eapply mpd_at_munch_any; [exact MN0| exact MU| exact WM| cbn; split; [clear - ON4; lia| exact I]|].
      intros ONN. cbn. split; [destruct (ON5 ONN); clear - H; lia| exact I]. }
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    assert (ONl1 : md_own dN = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dN) (4 * md_n dN)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (ONl E)]).
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH1. cbn [app] in HH1.
    destruct (gm_mkJB m1 ONs ONl1 HH1 MN1) as [DBJ B0].
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH1) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. clear GOT GSB. zstep. zstep. zstep.
    assert (G1 : 1 <= G) by (unfold gmr2_G; clear - NRN; lia).
    eapply (gm_xop A_MPI_LSET _ 1 _ _ _ _ (mpi_xop_stmtA_c_of _ _ _ _ _ 1 _ _ _ _ HLSET) ltac:(clear; lia) ltac:(clear; lia) lset_keep 0xa58a4 1);
      [exact J0| exact DBJ| exact B0| cbv beta; clear; lia| clear; lia| reflexivity| unfold grow_PHI; unfold AVOL_CALL; clear; lia| unfold lset_FR, calls_FR, fr_charge; clear; lia
      | unfold get_mont_r2_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]; clear - G1 NRN; lia| unfold get_mont_r2_FR, lset_FR, calls_FR, fr_charge; cbn [md_n]; clear - G1 D0; nia|].
    intros r h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 J2 B2 CR2.
    pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2. pose proof (hcs_ok asegs R HIA h2) as CSOK2.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { ddestruct CR2 as [[(-> & _)|(-> & _)] _]; [exfalso; apply KR; reflexivity|].
      eapply gm_ret; [exact J2| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
      - unfold get_mont_r2_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]; clear - G1 NRN; lia.
      - unfold get_mont_r2_FR, lset_FR, calls_FR, fr_charge; cbn [md_n]; clear - G1 D0; nia. }
    ddestruct CR2 as [[(-> & EN2 & _)|(-> & _)] _]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
    cbn [md_n] in EN2.
    assert (N2 : 0 <= md_n dX2 /\ md_n dX2 + 2 * md_n dN <= G) by (unfold gmr2_G; rewrite EN2; clear - NR NRN; lia).
    (* [comment removed for export] *)
    pose proof (bj_aobj _ _ _ _ _ _ _ _ _ _ B2) as ONs2.
    pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B2)) as [(CN2 & _) _]. unfold mpi_cells in CN2.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B2) as (E0 & E16 & EAL & _).
    pose proof MN0 as [(NRW8 & NAL8 & NPOS8 & _) _]. apply rw_cells_bound in NRW8.
    assert (NL7 : Z.land (md_addr dN) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact NAL8).
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ NPOS8 NRW8; rewrite ?Z.mod_small in KZ by lia; lia|].
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA NL7 NPOS8 NRW8; rewrite ?Z.mod_small in KA by lia; rewrite ?NL7 in KA; rewrite ?Zmod_0_l in KA; lia|].
    zstep. zstep. zstep. shadow_chk ONs2 (md_addr dN + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - NRN; lia). zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 6) with 64. replace (md_n dN * 64) with (64 * md_n dN) by (clear; lia).
    pose proof (shift_l_n_ub (md_n dN) dX2 (proj1 N2) (proj1 NRN)) as SUB. pose proof (shift_l_n_range (64 * md_n dN) dX2 (proj1 N2)) as SLB.
    eapply (gm_xop A_MPI_SHIFT_L _ _ _ _ _ _ HSHL ltac:(clear; lia) ltac:(unfold C24_SHIFT_L_c; clear; lia) (fun _ _ _ _ _ HR => proj2 HR) 0xa58d8 (64 * md_n dN));
      [exact J2| exact DBJ| exact B2| cbv beta; clear - NRN; lia| clear; lia| reflexivity| unfold shift_l_PHI, grow_PHI; unfold AVOL_CALL; clear - SLB N2; lia| unfold shift_l_FR, fr_charge; clear; lia
      | unfold get_mont_r2_PHI, shift_l_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]; clear - SUB N2 NRN; lia
      | unfold get_mont_r2_FR, lset_FR, shift_l_FR, calls_FR, fr_charge; cbn [md_n]; clear - G1 D0; nia|].
    intros r h3 LB3 m3 dX3 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 J3 B3 CR3.
    pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo) as KINV3.
    pose proof (munch_refl ([] : list ivl) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    assert (V2 : 0 + grow_PHI 1 + shift_l_PHI dX2 (64 * md_n dN) <= 8 + 8 * G) by (unfold shift_l_PHI, grow_PHI; unfold AVOL_CALL; clear - SUB N2; lia).
    assert (F2 : 0 + lset_FR d + shift_l_FR = 9) by (unfold lset_FR, shift_l_FR, calls_FR, fr_charge; clear; lia).
    (* [comment removed for export] *)
    zstep. if_cases KR3; zify_cond KR3.
    { ddestruct CR3 as [[(-> & _)| ->] _]; [exfalso; apply KR3; reflexivity|].
      eapply gm_ret; [exact J3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
      - unfold get_mont_r2_PHI; cbn [md_n]; clear - V2 G1 NRN; lia.
      - rewrite F2. unfold get_mont_r2_FR; cbn [md_n]; clear - G1 D0; nia. }
    ddestruct CR3 as [[(-> & _ & _ & EN3)| ->] _]; [| exfalso; clear - KR3; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR3; vm_compute in KR3; lia].
    assert (N3 : 0 <= md_n dX3 <= G) by (rewrite EN3; clear - SUB SLB N2; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    eapply (gm_mod 0xa58ec); [exact J3| exact DBJ| exact B3| exact SSHm| clear; lia| reflexivity
      | rewrite mod_mpi_PHI_val; unfold get_mont_r2_PHI; cbn [md_n]; clear - V2 N3 NRN; lia
      | rewrite mod_mpi_FR_val, F2; unfold get_mont_r2_FR; cbn [md_n]; clear - N3 D0; nia|].
    intros r h4 LB4 m4 dX4 w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 J4 B4 CR4.
    pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo) as KINV4. pose proof (hcs_ok asegs R HIA h4) as CSOK4.
    assert (SCS4 : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)).
    { eapply crange_sub; [exact (hcs_stack asegs R HIA h4)| clear - LOS; lia| rewrite (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J4); clear - TOP HTOP; lia]. }
    pose proof (munch_refl ([] : list ivl) m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
    ddestruct CR4 as [[[_ RR4] _] SZ4].
    assert (V3 : 0 + grow_PHI 1 + shift_l_PHI dX2 (64 * md_n dN) + mod_mpi_PHI dX3 dX3 dN <= 8 + 8 * G + (1200136 * G + 48 * md_n dN + 80088))
      by (rewrite mod_mpi_PHI_val; clear - V2 N3; lia).
    assert (F3 : 0 + lset_FR d + shift_l_FR + mod_mpi_FR dX3 dX3 dN d <= 9 + (G * (20 * d + 118) + 17 * d + 105))
      by (rewrite mod_mpi_FR_val, F2; clear - N3 D0; nia).
    (* [comment removed for export] *)
    zstep. if_cases KR4; zify_cond KR4.
    2:{ eapply gm_ret; [exact J4| intros E; apply KR4; rewrite E; reflexivity| exact RR4| |].
        - unfold get_mont_r2_PHI; cbn [md_n]; clear - V3 G1; lia.
        - unfold get_mont_r2_FR; cbn [md_n]; clear - F3 D0; lia. }
    assert (N4 : md_n dX4 <= G + 2) by (unfold div_mpi_nz in SZ4; unfold gmr2_G in *; clear - SZ4 N3 NRN; lia).
    (* [comment removed for export] *)
    pose proof (bj_aobj _ _ _ _ _ _ _ _ _ _ B4) as ONs4.
    pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B4)) as [(CN4 & _) _]. unfold mpi_cells in CN4.
    pose proof J4 as [MI4' ST4 FR4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    unfold gm_frame in FR4. replace (bv_unsigned sp - 40) with (bv_unsigned sp + -40) in FR4, ST4 by (clear; lia).
    shadow_chk ONs4 (md_addr dN + 10) 2.
    zstep. rewrite zx16_small by (clear - NRN; lia). zstep.
    do 5 zstep. zstep. zstep.
    replace (Z_to_bv 64 (bv_unsigned sp + -48 + 48)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; clear; lia).
    eapply gm_tail; [exact J4| |].
    - unfold shrink_PHI, grow_PHI in *; unfold AVOL_CALL in *. unfold get_mont_r2_PHI; cbn [md_n]. clear - V3 N4 N2 NRN G1. lia.
    - unfold shrink_FR, calls_FR, fr_charge. unfold get_mont_r2_FR; cbn [md_n]. clear - F3 D0. lia.
    all: match goal with |- ?g => idtac "GMAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WGM.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24484290889.0L3553797552.5 00000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Theorem A_mpi_get_mont_r2_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_get_mont_r2_c24 ()) "PR,$2.PHIA,(3.$14.R1.)P,(4:.(36.R2.))P,(4;.$14.R3.R2.$4<.)P,(4=.$14.R4.R3.$4>.)P,(4?.$14.R5.R4.$3;.$37.$38.)P,(50.$14.R6.R5.$3>.)P,(>.=(51.R7.))P,Ph,(1?.$14.R8.R7.)PLB,(0.$6.)PLF,(0.$6.)Pm,P,(20.&40.)(21.(20.&8.))P,(41.$14.R<.R;.R4.R3.R2.R1.)(52.$4.(53.(54.$4.$4.)$4.(55.$4.$4.)R4.))P,(=.(>.(56.(57.R9.))(58.(57.R9.)))(>.(59.(57.R9.))(5:.(57.R9.))))P,Pa,$4.P,(9.$12.(13.$14.(15.R1.))$18.)P,(=.(>.=R2.)(?.R2.(27.+2.+40.)))(=.(>.(56.(57.R=.))R3.)(?.R3.(5:.(57.R=.))))(5;.$14.R;.R:.$49.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG HLSET HSHL HMOD HSHR NEEDR HND DIMG ROIMG. unfold mpi_get_mont_r2_stmtA.
  intros until F0. intros HH HK LFN MX MN SXN NEN NST ON CRN CRNL XW XLS ST LOS SLO SLO3 SSH SLOS SLOL TOP SPA TPV MI RAE OXA ONA IN2 BUD UW F0SP F0X UWX UWN BUDF C24H -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 40 (gm_frame ra s0 s1 s2 s3)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  pose proof MN as [(_ & _ & _ & _ & NRN & _) _]. unfold MPI_MAX_LIMBS in NRN.
  pose proof (uw_obj_nonneg _ _ _ _ UWX) as D0.
  eapply gm_main with (slo := slo) (F0 := F0); try eassumption.
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
