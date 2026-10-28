(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free P_ecp_point_free.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_free A_platform_zeroize A_free_seq.
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
Ltac2 gd_tbl_A_ecp_point_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_point_free.pt_free_LB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_POINT_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "PF_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "PF_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_point_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_pt"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_freeable"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ecp_point_free_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "ecp_point_free_stmtA"; "A_ECP_POINT_FREE"].


Definition A_ECP_POINT_FREE : Z := 0xcb03c.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation ECP_POINT_FREE_STACK_A := 80 (only parsing).
Definition PF_PHI : Z := 3 * AVOL_CALL.
Definition PF_FR (d : Z) : Z := 3 * fr_charge d.

Definition ecp_point_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (p : ecp_pt) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1>.O1=.O1<.)Lh',(5.O1>.O1=.O1<.)(6.(7.$0.R13.(8.(9.(:.O18.O17.O16.O15.R12.R11.R10.O14.O13.R?.R>.R=.R<.R;.R:.R9.R8.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R7.R6.R5.R4.)O8.(;.O18.)O7.(<.(2.&40.))R3.(=.O1>.))R2.))(6.(>.O1>.R3.)(6.(?.O1>.R3.O4.(10.&40.O17.))(6.(11.O1.R2.)(6.(12.O1>.O1=.(13.O5.O1:.)O19.(10.&40.O17.)(14.O1=.)(15.O1>.O1=.O1<.O1;.)(16.(17.$18.$18.)(19.$18.$18.O6.(1:.O6.$1;.))(1<.(17.$18.$18.)))O2.R3.)(6.(7.$18.(1=.O1>.O1=.O1<.R1.)(1=.O1>.O1=.O1<.O1;.))(6.(7.$18.(15.O1>.O1=.O1<.R1.)(15.O1>.O1=.O1<.O1;.))(6.(7.$18.(1>.O1>.O1=.O1<.R1.)(1>.O1>.O1=.O1<.O1;.))(6.(1?.O1>.O1=.O1<.R1.R2.)(6.Px,$18.P,(20.O1>.O1=.O1<.O1;.R1.)(20.O1>.O1=.O1<.R3.R2.)(6.(21.(22.O1>.O1=.O1<.R1.)(1:.(22.O1>.O1=.O1<.O1;.)$23.))(6.(21.(24.O1>.O1=.O1<.R1.)(1:.(24.O1>.O1=.O1<.O1;.)(25.O3.)))(6.(26.O1>.O1=.O1<.R1.(13.O5.O1:.)O19.R3.)(27.O1>.R3.(13.O5.O1:.)O6.(28.O6.(29.(2:.O5.))(29.(2;.O5.))(29.(2<.O5.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_point_free_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_free ()) "Ph,(5.O4.O3.O2.)PLB,(2=.$2>.)PLF,(2=.$2>.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PA,$18.Pp,$30.Plo,$18.Pd,$18.P,(26.O4.O3.O2.R2:.R29.R28.R6.)P,(1?.O4.O3.O2.R2;.R6.)P,(27.O4.R8.R2;.R6.R5.)P,(31.R6.)P,(32.(33.R7.))P,(34.(35.O3.)(36.$2>.(13.R8.R2>.)(37.R2=.))(10.&40.R2;.)(1=.O4.O3.O2.R2?.)R9.$1;.)P,(38.(21.(1:.R:.$1;.)R8.)(21.(10.&40.R2<.)R:.))P,(39.O4.(3:.O3.)(20.O4.O3.O2.R31.)R=.R;.$1;.)P,(?.O4.R>.R:.(10.&40.R2>.))P,(21.(14.O3.)R;.)P,(21.R<.(3;.(3;.(10.&40.R30.)+50.)(3<.O3.)))P,(21.(10.&40.R31.)(1=.O4.O3.O2.R35.))P,(7.$18.(3=.(10.&40.R32.)+10.)=)P,(7.(2.&40.)R31.(3>.&40.(3?.O3.)))P,(>.O4.R14.)P,(21.(1:.(22.O4.O3.O2.R39.)$23.)$40.)P,(41.O3.R14.$1;.R11.)P,(21.(1:.(24.O4.O3.O2.R3;.)(25.R12.))$42.)P,(7.(2.&40.)R30.(3>.&40.R16.))(43.O4.(44.O4.O3.O2.R3=.R3<.R3;.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R14.R19.R18.)(8.(9.(:.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(3>.&40.O1.)R1:.(<.(2.&40.))R19.(=.O4.))R18.))")
(* [comment removed for export] *).

Section PTF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis MPIFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).

  Ltac fsA_in ::= cbn; inl.
  Ltac fsA_addr ::= cbn [md_addr mpd_init];
    match goal with EX : md_addr (pt_X ?p) = _, EY : md_addr (pt_Y ?p) = _, EZ : md_addr (pt_Z ?p) = _ |- _ =>
      rewrite ?EX, ?EY, ?EZ | _ => idtac end.

  Ltac pfA_free1 spo md X rest :=
    lazymatch goal with
    | HH : HM _ _ _ ?xhc ?xLBc _ ?xmc, PXA : presW _ _ _ ?xh0 ?xLBf _ ?xSP _ [(?xA, _)] ?xm0 _, UWO : uw_obj _ _ 48 ?xd, ST : stk _ _ ?xlo _,
      HBR : blkfacts _ (?xLB ++ _), DISF : mpds_apart ?xFR |- _ =>
        eapply (free_stepA R HIA A_MPI_FREE MPIFREE NEEDR DIMG) with
          (d0 := md) (X0 := X) (A := xA) (sz := 48) (d := xd) (SP := xSP) (h0 := xh0) (m0 := xm0) (LBf := xLBf) (lo := xlo) (LBall := xLB) (FR := xFR);
        [ fsA_side spo rest .. | ]
    end;
    lazymatch goal with
    | |- forall _, _ =>
        lazymatch goal with HH : HM _ _ _ _ _ _ _, LIV : Forall (mpdr_at _ _ _) _, CH : Forall _ _, PXA : presW _ _ _ _ _ _ _ _ _ _ _,
                            HTc : htop _ _ _ _ = _, HSc : hstkhi _ _ _ _ = _, HFc : hflag _ _ _ _ = _, HCSc : (forall x, hcs _ _ _ _ x -> hcs _ _ _ _ x),
                            HV : havol _ _ _ _ <= _, HFR : hfr _ _ _ _ <= _, OBJ : aobj _ _ _ _ _ 48, ST : stk _ _ _ _, MI : mem_inv _ _ |- _ =>
          fsA_post HH HTc HSc HFc HCSc HV HFR LIV CH PXA OBJ ST MI
        end
    | |- ?gg => idtac "pfA_free1: free_stepA left goal" gg
    end.

  #[using="MPIFREE NEEDR DIMG HMND"] Lemma A_ecp_point_free_walk : ecp_point_free_stmtA asegs R HIA A_ECP_POINT_FREE.
  Proof.
    unfold ecp_point_free_stmtA, A_ECP_POINT_FREE. intros until d.
    intros HH HK0 PT FRB DIS CW SX OBJ ST LOS SLO SPTOP SPA TP MI BUD UWO BUDF ->.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof (HMND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2]. pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR HAP]. change (blkfacts L (LB ++ LF)) in HBR.
    unfold ECP_POINT_SIZE in CW, SX, OBJ, UWO.
    ddestruct PT as (EX & EY & EZ & MX & MY & MZ).
    dpose MX as (CHX & AL8 & POS & _). unfold mpdr_at in CHX. rewrite EX in AL8, POS.
    pose proof MZ as (CHZ & _). rewrite EZ in CHZ. pose proof (rw_cells_bound _ _ _ _ CHZ) as KB. cbn [cells_size csize Nat.add length mpi_cells] in KB. clear CHZ CHX.
    assert (SUBF : forall b, In b (pt_free_LB p LB) -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    set (FRL := pt_mpds p) in *.
    assert (FRB' : Forall mpd_freeable [pt_X p; pt_Y p; pt_Z p]) by exact FRB.
    assert (NI : forall dd, In dd FRL -> md_own dd = LHeap -> ~ In (md_p dd, 4 * md_n dd) (pt_free_LB p LB)).
    { intros dd Hd O. unfold pt_free_LB. apply lb_free_mpds_notin; [exact NDL| exact Hd| exact O]. }
    assert (ACLsp : alloc_ceiling <= bv_unsigned sp) by (clear - ALO LOS SLO NEEDR; lia).
    pose proof (free_facts_introA asegs R HIA h LB LF (pt_free_LB p LB) m (bv_unsigned sp) _ A 48 FRL HH NDL
                  ltac:(intros dd Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[]]]]; assumption) CW SUBF NI ACLsp ltac:(lia) DI1 DI2) as FF1.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (presW_sub_blocks asegs R HIA h LB (pt_free_LB p LB) LF (bv_unsigned sp) (arl_stklo R) [(A, A + 48)] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 48)] HH ltac:(clear; lia)) SUBF) as PXA.
    pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (conj MI I) as MIbox. pose proof (conj MX (conj MY MZ)) as Gbox. clear MX MY MZ.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - POS KB; lia); clear - K0 POS; lia|]. clear K0.
    (* [comment removed for export] *)
    assert (AL7 : Z.land A 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact AL8 | clear - AL8; Z.div_mod_to_equations; lia]).
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct MIbox as [MIm _]. ddestruct Gbox as (MX & MY & MZ).
    assert (LIV : Forall (mpdr_at asegs m1 LB) [pt_X p; pt_Y p; pt_Z p]).
    { eapply (lives_munchA asegs L m m1 LB (LB ++ LF)); [| exact MU0| exact WM0| exact MIm| assumption| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| | intros a n Ha Hn; cbn; clear - Ha Hn ALO LOS; lia].
      - repeat apply Forall_cons; try apply Forall_nil; assumption.
      - repeat apply Forall_cons; try apply Forall_nil; rewrite ?EX, ?EY, ?EZ; cbn; clear - SX ALO LOS; lia. }
    clear MU0 WM0 MIm MX MY MZ.
    lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -16) _ |- _ => rename FRx into FR1 end.
    assert (CH : Forall (fun ac => rw_cells asegs m1 (fst ac) (snd ac)) [(bv_unsigned sp - 16, [C8 s0; C8 ra])]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. exact FR1. }
    clear FR1.
    assert (HTc : htop asegs R HIA h = htop asegs R HIA h) by reflexivity.
    assert (HSc : hstkhi asegs R HIA h = hstkhi asegs R HIA h) by reflexivity.
    assert (HFc : hflag asegs R HIA h = hflag asegs R HIA h) by reflexivity.
    assert (HCSc : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h x) by (intros x Hx; exact Hx).
    assert (HV : havol asegs R HIA h <= havol asegs R HIA h) by lia.
    assert (HFR : hfr asegs R HIA h <= hfr asegs R HIA h) by lia.
    unfold PF_PHI in BUD. unfold PF_FR in BUDF.
    (* [comment removed for export] *)
    zstep. pfA_free1 (bv_unsigned sp + -16) (pt_X p) A [pt_Y p; pt_Z p].
    zstep. zstep. pfA_free1 (bv_unsigned sp + -16) (pt_Y p) (A + 16) [pt_Z p].
    (* [comment removed for export] *)
    fa_get CH 2%nat CFR. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) in CFR by lia.
    zstep. zstep. zstep. zstep. release_frame CFR ST (bv_unsigned sp).
    try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    lazymatch type of CH with Forall ?P ?CS =>
      let pre := eval cbn [removelast] in (removelast CS) in
      assert (CH' : Forall P pre) by (apply (proj1 (proj1 (Forall_app P pre [(bv_unsigned sp - 16, [C8 s0; C8 ra])]) CH)));
      clear CH; rename CH' into CH end.
    zstep. pfA_free1 (bv_unsigned sp) (pt_Z p) (A + 32) ([] : list mpd).
    (* [comment removed for export] *)
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold ecp_point_free_postA. deexists 15.
    lazymatch goal with HH : HM _ _ _ ?hf _ _ ?mf |- _ => exists mf, mo9, hf end.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF9|].
    split; [unfold ECP_POINT_SIZE; exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ PXA)|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
    split; [unfold PF_PHI; clear - HV; lia|]. split; [unfold PF_FR; clear - HFR; lia|].
    split. { lazymatch type of HH with HM _ _ _ _ ?l _ _ => change l with (pt_free_LB p LB) in HH end. exact HH. }
    fa_get CH 0%nat CQZ. fa_get CH 1%nat CQY. fa_get CH 2%nat CQX.
    unfold ecp_point_at, pt_init; cbn [pt_X pt_Y pt_Z md_addr mpd_init].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [| split]; (apply mpdr_at_init; [assumption| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia]).
  Qed.
End PTF.

Lemma A_ecp_point_free_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_free ()) "PR,$45.PHIA,(46.$47.R1.)P,(48.(3:.R2.))P,(49.$47.R3.R2.$4:.)P,(21.=(3<.R4.))P,(6.(21.(4;.(35.R5.))(4<.(35.R5.)))(21.(4=.(35.R5.))(4>.(35.R5.))))P,Ph,(5.$47.R6.R5.)PLB,(2=.$2>.)PLF,(2=.$2>.)Pm,P,(2.&40.)(3.(2.&8.))P,(26.$47.R:.R9.R4.R3.R2.R1.)(4?.$18.(50.(17.$18.$18.)$18.(51.$18.$18.)R4.))(52.$47.R7.R6.$53.)")
(* [comment removed for export] *).
Proof. intros. eapply A_ecp_point_free_walk; eauto. Qed.
