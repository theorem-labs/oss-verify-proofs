(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey
     A_mpi_add_abs_W A_mpi_sub_abs A_mpi_add_sub A_mpi_sub_abs_ng.
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
Ltac2 gd_tbl_A_mpi_add_sub_ng () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_mpi_addsub.add_sub_mpi_R"; "add_sub_PHI0"; "add_sub_FR0"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "WAS.AS_FRAME_A"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "WAS.AS_VAL_A"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "WAS.AS_POST_A"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.A.A_mpi_opnd.opnd_atA"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.hcs"; "WAS.at1"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_ADD_SUB_MPI"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.Spec.Rep.LNull"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.A.A_mpi_sub_abs_ng.mpi_sub_abs_ng_stmtA_o"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_SUB_ABS"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "add_sub_mpi_ng_stmtA_o"; "mpi_add_mpi_ng_stmtA_o"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_ADD_MPI"; "mpi_sub_mpi_ng_stmtA_o"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_SUB_MPI"].


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
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d flip : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition AS_FRAME_A := as_frame ra s0 s1 s2.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis UWA : uw_obj R (md_addr dA) 16 d.
  Hypothesis UWB : uw_obj R (md_addr dB) 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis FLIP : flip = 1 \/ flip = -1.
  Hypothesis BUD : havol asegs R HIA h + add_sub_PHI0 dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + add_sub_FR0 d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 256 - arl_need_rt R.
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
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A []).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAM; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L21887662552.151L29428324939.5  L33510041944.151L34289808772.1  L39939305631.154L41562522431.153L66083662040.151L9962237875.151 Q29963071266.154Q33963780182.154Q3859172566.154 Q39849717666.154Q39974853590.154Q45996133718.154Q49411331106.154Q546509986.154  00000700I00P00T00o01601=01D01`02802P02l03D03\04804TS2ra2spS1R2lo3LOS3ALO3ACPS2ra2spS2spS1R2ra2sp2lo4SLO25NEEDR3SPRS2ra2spS2ra2spS2ra2spS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R3HIA1h2sp3TOP2hc3HT14HTOP". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma as_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Pv,$4.Pf,$4.Phc,(17.$<.VR,VHIA,)PLBc,(18.$19.)Pmc,P,(1:.&40.)(1;.(1:.&8.))PdXc,$1<.Pr,$4.Pxra,(1:.&40.)Pxt0,(1:.&40.)Pxt1,(1:.&40.)Pxt2,(1:.&40.)Pxs0',(1:.&40.)Pxs1,(1:.&40.)Pxa1,(1:.&40.)Pxa2,(1:.&40.)Pxa3,(1:.&40.)Pxa4,(1:.&40.)Pxa5,(1:.&40.)Pxa6,(1:.&40.)Pxa7,(1:.&40.)Pxs2,(1:.&40.)Pxt3,(1:.&40.)Pxt4,(1:.&40.)Pxt5,(1:.&40.)Pxt6,(1:.&40.)P,(1=.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+20.$1>.(1?.$19.)R19.R18.R17.R16.R15.R14.)P,(20.(5.(0.$4.R14.=)(0.$4.(21.R15.)$22.))(0.$4.R14.$23.))P,(6.R1;.(15.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(6.R1;.(16.Vd,))(24.$<.(25.$<.VR,VHIA,R1;.Vmo,)$26.(27.(28.R16.(29.&40.(>.(2:.&40.Vsp,)-20.))Vgp,Vtp,R15.R14.R13.R12.R11.(29.&40.R17.)R10.R?.R>.R=.R<.R;.R:.R9.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(29.&40.+9>5>4.)Vfc,(2;.(1:.&40.))R19.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold AS_FRAME_A, as_frame in FR1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 4 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold AS_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@D24976250634.183D50797141399.183D52014138856.183K43040026633.183L29074096193.171L29074168500.174L35663928186.7  L43046430437.6  L60098763854.3  Q22285631880.180Q22285648010.177Q22286196081.179Q24974040330.182Q39212284437.180Q42081808994.180Q4926406185.180 Q52016320488.182Q54253886744.179Q56761401107.180Q6027349519.183 Q60511567613.180Q62965564504.181Q63231501142.177Q9538787269.177 00000T01S02702o03K03g04<04=04G04Q04[04e05@05J05Z05d06?06I06V07107907P07Z07bS2ra2sp1X3xs02xs1w2sg2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22xs1w2sg5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs1w2sg2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO21p2xs1w5NEEDR3FSZ3DSX2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs1w2sg2X03X16S2ra2sp1X3xs02xs1w2sg2X03X16S1R3HIA1h2sp2lo3TOP1HFS1R2lo3LOSS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xs1w2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xs2X02HBS1X3xs02xsS1X3xs02xs1w2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xs2X0S1X3xs02xs1w2HB5Ha_st5Hl_stS3xs02xsS1X3xs02xs3X162HB5Ha_stS1X3xs02xsS3xs02xs". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma as_FIN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Pv,$4.Pf,$4.Phc,(17.$<.VR,VHIA,)PLBc,(18.$19.)Pmc,P,(1:.&40.)(1;.(1:.&8.))PdXc,$1<.Pw,$4.Psg,$4.Pxra,(1:.&40.)Pxt0,(1:.&40.)Pxt1,(1:.&40.)Pxt2,(1:.&40.)Pxa0,(1:.&40.)Pxa1,(1:.&40.)Pxa2,(1:.&40.)Pxa3,(1:.&40.)Pxa4,(1:.&40.)Pxa5,(1:.&40.)Pxa6,(1:.&40.)Pxa7,(1:.&40.)Pxt3,(1:.&40.)Pxt4,(1:.&40.)Pxt5,(1:.&40.)Pxt6,(1:.&40.)P,(1=.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+20.$1>.(1?.$19.)R18.R17.R16.R15.R14.R13.)P,(0.$4.(2=.R13.(2>.+2.+10.))(2=.R12.(2>.+2.+10.)))P,(20.(0.$4.R13.+1.)(0.$4.R13.-1.))P,(0.$4.(8.R14.(2?.R16.))$22.)P,(6.R1<.(15.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(6.R1<.(16.Vd,))(24.$<.(25.$<.VR,VHIA,R1<.Vmo,)$26.(27.(28.R16.(29.&40.(>.(2:.&40.Vsp,)-20.))Vgp,Vtp,R15.R14.R13.(29.&40.VX,)(29.&40.(30.(31.VR,)))R12.R11.R10.R?.R>.R=.R<.R;.(29.&40.R18.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(29.&40.+9>5<8.)Vfc,(2;.(1:.&40.))R1:.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 WS SG HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
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
    zstep. zstep.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition at1 (m1 : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "(5.(1=.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+20.$1>.(1?.$19.)==Vh,VLB,O1.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(5.(32.$<.O1.VLB,VdA,)(5.(33.$<.VR,VLF,O1.VLB,(2:.&40.Vsp,)VdB,)(5.(34.$<.(31.VR,)(35.$<.VR,VHIA,Vh,)O1.VdA,)(34.$<.(31.VR,)(35.$<.VR,VHIA,Vh,)O1.VdB,)))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac call_side :=
    first [ eassumption | reflexivity | exact BUD | exact BUDF | exact IA1 | exact UWX
          | (rewrite unsigned_lit by (clear; lia); reflexivity)
          | (apply mpd_sep_symA; eassumption)
          | (eapply opnd_sep_sp_le; [eassumption| clear; lia])
          | (eapply opnd_atA_SP_le; [first [eassumption| apply opnd_atA_mpd; eassumption]| clear; lia])
          | (apply opnd_atA_mpd; eassumption) ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L11794092686.2  L15045051906.2  L15047325488.4  L15047325489.2  L16073620949.11 L17829113186.9  L18283994230.2  L1880064794.19  L1894445729.14  L1894731451.14  L29010569984.204L34289808772.1  L36560747987.4  L37463353716.10 L37463353716.2  L40290687782.1  L41942189128.1  L45290914134.11 L47026640784.207L48740486386.10 L5266079642.1   L59308518135.4  L59308632561.1  L63632471619.5  L9568782131.11  L9847631648.2   Q5261966311.172 Q7190997524.207 Q7192832867.172 00000800900:00;00K00j01301401501601701;01I01M01Q01T01X01Y01k02P02Q02^02b03603D03K03b04T05FS1d4FR1'SSSS1R3HIA1h2sp3TOPS2sp1X2sX2nX2pX3xs04padX4ownX1HS2dB4flipFFFFS2spS2dA2dB3dX22CVS2spS2spS1XS2spFS2ra2sp1X3xs01w2sgS1X2sX2nX2pX3xs04padX4ownX2dA2dB4PHI1FS2dA2dB2LE2LTS2KRS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO2S2dA2dBS1X3xs02dA2dB2LE2X03X16S1R2sp3xs02dA2dB2lo4SLO22LE5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02dA2dB2lo4SLO22LE5NEEDR3LOS4SP643ALO3ACP". (* [comment removed for export] *)
  #[using="IMG HSUB JC TPV UWX UWA UWB BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA2 IB2 A47A NGAB"] Lemma as_KSUBAB : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Pm1,P,(1:.&40.)(1;.(1:.&8.))Pw,$4.Psg,$4.Pxra,(1:.&40.)Pxt0,(1:.&40.)Pxt1,(1:.&40.)Pxt2,(1:.&40.)Pxa0,(1:.&40.)Pxa3,(1:.&40.)Pxa4,(1:.&40.)Pxa5,(1:.&40.)Pxa6,(1:.&40.)Pxa7,(1:.&40.)Pxt3,(1:.&40.)Pxt4,(1:.&40.)Pxt5,(1:.&40.)Pxt6,(1:.&40.)P,(36.R11.)P,(0.$4.(2=.R11.(2>.+2.+10.))(2=.R10.(2>.+2.+10.)))P,(20.(0.$4.R11.+1.)(0.$4.R11.-1.))P,(0.$4.(8.Vflip,(37.VdB,))(38.(37.VdA,)))P,(6.(2?.VdB,)(2?.VdA,))P,(0.$4.(8.R14.(39.(2?.VdA,)(2?.VdB,)))(8.(37.VdA,)(39.(2?.VdA,)(2?.VdB,))))(24.$<.(25.$<.VR,VHIA,Vh,Vmo,)$26.(27.(28.R14.(29.&40.(>.(2:.&40.Vsp,)-20.))Vgp,Vtp,R13.R12.R11.(29.&40.VX,)(29.&40.(30.(31.VR,)))R10.(29.&40.(3:.VdA,))(29.&40.(3:.VdB,))R?.R>.R=.R<.R;.(29.&40.R16.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(29.&40.+9>598.)Vfc,(2;.(1:.&40.))R17.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; (intros dd_H; ddestruct dd_H as (J0 & MA1 & MB1 & OAA1 & OBA1); intros WS SG SGN LE HVS).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in ST1 by (clear; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (XW1 : mpd_writableA R LB LF (bv_unsigned sp + -32) (htop asegs R HIA h) dX) by (eapply mpd_writableA_sp_mono; [exact XW| clear; lia]).
    assert (XLS1' : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp + -32 <= md_p dX) by (intros N; destruct (XLS N); [left; assumption| right; clear - H; lia]).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX) by (split; [exact OX1| intros E; exfalso; exact (NST E)]).
    assert (PHI0 : 0 <= sub_abs_PHI0 dX dA dB) by (unfold sub_abs_PHI0, grow_PHI; unfold AVOL_CALL; clear - NRA; lia).
    assert (FR0 : 0 <= sub_abs_FR0 d) by (unfold sub_abs_FR0, calls_FR, fr_charge; clear - D0; lia).
    assert (PHI1 : sub_abs_PHI0 dX dA dB <= add_sub_PHI0 dX dA dB) by (unfold sub_abs_PHI0, add_sub_PHI0, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA NRB; lia).
    assert (FR1' : sub_abs_FR0 d <= add_sub_FR0 d) by (unfold sub_abs_FR0, add_sub_FR0, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HSUB as SPc. unfold mpi_sub_abs_ng_stmtA_o in SPc.
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by qlia; try call_side.
      all: try (rewrite ?(unsigned_lit X) by qlia; eapply uw_obj_uwc; [exact UWX| clear; lia]).
      all: try (clear - SLO2 NEEDR TOP SPR LOS LOSP; lia).
      all: try (clear - SPA; replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact SPA).
      all: try (clear - BUD PHI1; lia). all: try (clear - BUDF FR1'; lia).
      all: try (cbn [md_n]; apply NGAB; exact LE).
      all: match goal with |- ?g => idtac "KSUBAB-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct CR as [CR1 BK].
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -32) (sub_abs_PHI0 dX dA dB) (sub_abs_FR0 d) J0 ltac:(clear - SLO2 NEEDR; lia)
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
      (* [comment removed for export] *)
      zstep.
      eapply as_FIN with (sg := sg); [exact J1| exact WS| exact SG| | clear - PHI1; lia| clear - FR1'; lia].
      unfold AS_VAL_A. unfold mpd_val in CV. rewrite CSG in CV.
      replace (mpd_abs dX2) with (mpd_abs dA - mpd_abs dB) by (unfold mpd_abs in *; clear - CV; lia).
      rewrite HVS. unfold mpd_val, mpd_abs.
      replace (flip * (md_sg dB * limbs_val (md_limbs dB))) with ((flip * md_sg dB) * limbs_val (md_limbs dB)) by (clear; lia). rewrite SGN. clear; lia.
    all: match goal with |- ?g => idtac "KSUBAB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0@L11794092686.2  L15045051906.2  L15047325488.2  L15047325488.4  L16073620949.11 L17578730821.2  L17829113186.9  L18283994230.2  L19489910334.2  L29010569984.203L34289808772.1  L36560747987.4  L3698155343.19  L3699912436.14  L3700265710.14  L37463353716.10 L37463353716.2  L40290687782.1  L41942189128.1  L42290037104.10 L45290914134.11 L5231095820.204 L5266079642.1   L59308632561.1  L59310615242.4  L63632471619.5  L7441479568.205 L9568782131.11  Q5261966311.170 Q7190997524.205 Q7192832867.170 00000800900:00;00K00R01101:01B01C01G01U01V01W01X01\01`01c01g02L02M02b02c02g03503I03[03i04@05205dS1d4FR1'SSSS1R3HIA1h2sp3TOPS2dA2dBS2sp1X2sX2nX2pX3xs04padX4ownX1HS2dB4flipS2dA3SGAFS2spS2dA2dB3dX22CVFFFS2spS2spS1XS2spS1X2sX2nX2pX3xs04padX4ownX2dA2dB4PHI1FS2ra2sp1X3xs02dA1w2WBFS2KRS2dA2dB2LT3LT'S1R2sp2lo4SLO25NEEDRS2ra2sp1X3xs02dA1wS1R2sp2lo4SLO2S1X3xs02dA2dB2LT2X03X16S1R2sp3xs02dA2dB2lo4SLO22LT5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02dA2dB2lo4SLO22LT5NEEDR3LOS4SP643ALO3ACP". (* [comment removed for export] *)
  #[using="IMG HSUB JC TPV UWX UWA UWB BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA2 IB2 A47B SGA NGBA"] Lemma as_KSUBBA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Pm1,P,(1:.&40.)(1;.(1:.&8.))Pw,$4.Pxra,(1:.&40.)Pxt0,(1:.&40.)Pxt1,(1:.&40.)Pxt2,(1:.&40.)Pxa0,(1:.&40.)Pxa3,(1:.&40.)Pxa4,(1:.&40.)Pxa5,(1:.&40.)Pxa6,(1:.&40.)Pxa7,(1:.&40.)Pxt3,(1:.&40.)Pxt4,(1:.&40.)Pxt5,(1:.&40.)Pxt6,(1:.&40.)P,(36.R10.)P,(0.$4.(2=.R10.(2>.+2.+10.))(2=.(37.VdA,)(2>.+2.+10.)))P,(5.(6.=R11.)(7.R11.(2>.+2.+10.)))P,(0.$4.(8.Vflip,(37.VdB,))(38.(37.VdA,)))P,(7.(2?.VdA,)(2?.VdB,))(24.$<.(25.$<.VR,VHIA,Vh,Vmo,)$26.(27.(28.R13.(29.&40.(>.(2:.&40.Vsp,)-20.))Vgp,Vtp,R12.R11.R10.(29.&40.VX,)(29.&40.(30.(31.VR,)))R?.(29.&40.(3:.VdA,))(29.&40.(3:.VdB,))R>.R=.R<.R;.R:.(29.&40.R14.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(29.&40.+9>5:<.)Vfc,(2;.(1:.&40.))R15.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; (intros dd_H; ddestruct dd_H as (J0 & MA1 & MB1 & OAA1 & OBA1); intros WS WB SGN LT).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in ST1 by (clear; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (XW1 : mpd_writableA R LB LF (bv_unsigned sp + -32) (htop asegs R HIA h) dX) by (eapply mpd_writableA_sp_mono; [exact XW| clear; lia]).
    assert (XLS1' : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp + -32 <= md_p dX) by (intros N; destruct (XLS N); [left; assumption| right; clear - H; lia]).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX) by (split; [exact OX1| intros E; exfalso; exact (NST E)]).
    assert (PHI0 : 0 <= sub_abs_PHI0 dX dB dA) by (unfold sub_abs_PHI0, grow_PHI; unfold AVOL_CALL; clear - NRB; lia).
    assert (FR0 : 0 <= sub_abs_FR0 d) by (unfold sub_abs_FR0, calls_FR, fr_charge; clear - D0; lia).
    assert (PHI1 : sub_abs_PHI0 dX dB dA <= add_sub_PHI0 dX dA dB) by (unfold sub_abs_PHI0, add_sub_PHI0, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA NRB; lia).
    assert (FR1' : sub_abs_FR0 d <= add_sub_FR0 d) by (unfold sub_abs_FR0, add_sub_FR0, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HSUB as SPc. unfold mpi_sub_abs_ng_stmtA_o in SPc.
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dB) (dB := dA) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by qlia; try call_side.
      all: try (rewrite ?(unsigned_lit X) by qlia; eapply uw_obj_uwc; [exact UWX| clear; lia]).
      all: try (clear - SLO2 NEEDR TOP SPR LOS LOSP; lia).
      all: try (clear - SPA; replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact SPA).
      all: try (clear - BUD PHI1; lia). all: try (clear - BUDF FR1'; lia).
      all: try (cbn [md_n]; apply NGBA; assumption).
      all: match goal with |- ?g => idtac "KSUBBA-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct CR as [CR1 BK].
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -32) (sub_abs_PHI0 dX dB dA) (sub_abs_FR0 d) J0 ltac:(clear - SLO2 NEEDR; lia)
                  PHI0 FR0 MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - destruct CR1 as [(-> & _)|[-> |[-> LT']]]; [exfalso; apply KR; reflexivity| | exfalso; clear - LT LT'; lia].
      eapply as_ret; [exact J1| right; reflexivity| clear - PHI1; lia| clear - FR1'; lia].
    - destruct CR1 as [(-> & CV & CSG)|[-> |[-> LT']]];
        [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LT'; lia].
      (* [comment removed for export] *)
      zstep.
      eapply (as_FIN _ _ _ _ _ _ (0 - w) (- md_sg dA)); [exact J1| | clear - SGA; lia| | clear - PHI1; lia| clear - FR1'; lia].
      + rewrite Zminus_mod, WS, <- Zminus_mod. reflexivity.
      + unfold AS_VAL_A. unfold mpd_val in CV. rewrite CSG in CV.
        replace (mpd_abs dX2) with (mpd_abs dB - mpd_abs dA) by (unfold mpd_abs in *; clear - CV; lia).
        unfold mpd_val, mpd_abs.
        replace (flip * (md_sg dB * limbs_val (md_limbs dB))) with ((flip * md_sg dB) * limbs_val (md_limbs dB)) by (clear; lia). rewrite SGN. clear; lia.
    all: match goal with |- ?g => idtac "KSUBBA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01M0@D21329468335.155D21329468335.156D23379772182.156D35881667587.155D35881667587.156L13720147517.4  L17305750384.4  L19431261630.4  L19945316590.2  L21765854580.145L21887662552.144L22366621351.0  L27775132660.145L33478855426.4  L33510041944.145L34290115814.151L35653441506.7  L3680515908.3   L40834179097.176L42479632545.4  L43059266230.149L43935804614.175L43935886280.176L43935886280.178L43936346429.173L54383256528.1  L54748384003.145L59321133642.1  L60098763854.3  L60814849355.3  L60976029790.4  L6419290535.0   L6482734895.4   L66083662040.145L9716869748.144 L9962237875.145 Q10333294960.185Q13280261335.186Q13715427560.188Q15643324129.151Q18696506101.185Q20498771212.187Q21800401414.185Q22053704889.186Q22053704889.187Q22056211846.183Q23512175082.153Q24267381591.188Q24330840805.185Q25160350961.185Q25513505925.154Q25513505925.155Q25664719138.185Q27668705378.154Q27668705378.155Q31226872993.185Q31396957457.185Q32655500769.152Q35016271767.185Q35715139857.185Q35765334355.152Q35765334355.153Q36426122721.185Q37374748791.185Q3830427394.152 Q38735600301.187Q38736348717.188Q38737697513.185Q39212284437.186Q39212284437.188Q39939554818.152Q4141071397.185 Q44648843873.152Q45399902939.187Q49698585326.153Q49698585326.154Q50301287168.185Q51235796833.152Q53972118266.185Q54209832123.183Q60511567613.186Q60511567613.188Q61800308129.185Q62495047012.186Q6414620453.185 Q64253126389.185Q66522067074.152Q67426116409.155Q67528989526.155Q67528989526.156Q9538243134.185 Q9538787269.183 Q9843367298.151 00000g01d02^03F04704A04M04[04b04o05<05=05J05W05d06106I06W07607B07W08808Y09:09[09_09l0:20:<0:J0:T0:U0:c0;00;=0;J0;K0;`0<50<@0<\0=10=20=G0=\0>10><0>U0>V0?20?O0@20@30@U0A:0AW0Al0B70BT0BU0B`0Bk0Bl0CA0CQ0Cf0D;0DP0De0E:0EJ0EK0EV0Ek0FA0FW0FX0Fc0G@0GU0Gj0H?0H@0HY0I50I60IF0Ih0JJ0K20KG0K\0KlS1R2ra2sp1X3xs02lo4SLO25NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02lo4SLO25NEEDR3LOS2X03SPR2HB5Ha_st5Hl_st2s1S1R2ra2sp2s21X3xs02lo4SLO25NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X3xs03TOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs03TOP2HB5Ha_st5Hl_st2s12s2S2dA2dB2C0S2sp2dA2lo1HS2sp2dA2lo3OA4S2sp2loS2ra2sp1X3xs0S2ra2sp1X3xs0SS2ra2sp1X3xs0S2dA2dB2C02C1S2ra2sp1X3xs0S2ra2sp1X3xs0S1R3HIA1h2sp2lo3TOP4HTOPS2dA4LENA4PABBS1R2ra2sp1X3xs02dA2dB4PABB4PBBBS2sp2dB2lo1HS2ra2sp1X3xs02lo4LOSPS2ra2sp1X3xs02dA2dB3BBD4PABB4PBBBS2ra2sp1X3xs02dA2dB3ABD4PABB4PBBBS2ra2sp1X3xs02dA2dB3BBD4PABB4PBBBS2ra2sp1X3xs02dA2dB3ABD4PABB4PBBBS2dAS2ra2sp1X3xs0S4NGS'S1R2lo3LOSS2dB4LENB4PBBBS2dA2dB2CmSS2sp2dB2lo3OB4S2ra2sp1X3xs0S2ra2sp1X3xs0S2ra2sp1X3xs0FS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02loS1R3xs02dA2dB4IMG'4PABB4PBBBS3xs02dA2dB4PABB4PBBBFS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02HBS3xs02dA2dB3BBD4PABB4PBBBFS1R3xs02dA2dB4IMG'4PABB4PBBBS2ra2sp3xs02lo2HB5Ha_st5Hl_stS2sp2s03xs02lo2HB5Ha_st5Hl_st2s12s2FS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s1S1R3xs02dA2dB5ALWF'4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02loS1R3xs02dA2dB5ALWF'4PABB4PBBBFS2sp3xs02HBS2sp3xs02HBFS3xs02dA2dB4PABB4PBBBS2sp3xs02lo4LOSPS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02lo4LOSPFS2sp3xs02loS3xs02dA2dB4PABB4PBBBS2sp3xs04SP642HB5Ha_stS2sp3xs04SP642HB5Ha_stFS2sp3xs02loS1R3xs02dA2dB5ALWF'4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBFS3xs02dA2dB3ABD4PABB4PBBBS1R3xs02dA2dB4IMG'4PABB4PBBBFS2sp3xs02lo4LOSPS2sp2s23xs02lo4LOSP2HB5Ha_st5Hl_stS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s2S3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02lo4LOSP". (* [comment removed for export] *)
  #[using="IMG HSUB JC TPV UWX UWA UWB FLIP BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA2 IB2 A47A A47B SGA SGB NGS NGAB NGBA"] Lemma as_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)P,(3=.$<.VR,VHIA,Vh,Vmo,)P,(32.$<.Vm,VLB,VdA,)P,(33.$<.VR,VLF,Vm,VLB,(2:.&40.Vsp,)VdB,)P,(3>.$<.Vm,Vlo,(2:.&40.Vsp,))P,(3?.$<.Vm,)P,(34.$<.(31.VR,)(35.$<.VR,VHIA,Vh,)Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(34.$<.(31.VR,)(35.$<.VR,VHIA,Vh,)Vm,VdA,)P,(34.$<.(31.VR,)(35.$<.VR,VHIA,Vh,)Vm,VdB,)(40.$<.$26.(41.(27.(28.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(29.&40.VX,)(29.&40.(3:.VdA,))(29.&40.(3:.VdB,))(29.&40.Vflip,)R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(29.&40.$42.)Vfc,(2;.(1:.&40.))Vm,(2<.$<.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK MA0 MB0 ST MI OXA OAA OBA. unfold A_ADD_SUB_MPI.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h. pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. pose proof OBA as [OBs OBl]. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    change (rw_cells asegs m1 (bv_unsigned sp + -32) AS_FRAME_A) in FR.
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
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OAs (md_addr dA + 8) 2.
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
         | |- aevtA _ _ _ (MS _ _ (Z_to_bv 64 0x09e48c) _ _ _ _) =>
             exfalso; pose proof NGS as NGS'; rewrite EA, EB, EF in NGS'; clear - NGS'; lia
         | |- _ => idtac end.
    (* [comment removed for export] *)
    all: eapply (aevtA_cut_evtA_KF asegs R HIA h mo);
      [ eapply (c_cmp AL IMG ALWF (hcs asegs R HIA h) CSOK) with (ys := md_limbs dA) (zs := md_limbs dB);
          [exact CEA| exact ABY| exact LENA| exact NRA1| exact ABD| exact PAB| exact ALA| exact OAs| exact OALn| clear - PABB LENA; lia
          | exact CEB| exact BBY| exact LENB| exact NRB1| exact BBD| exact PBB| exact ALB| exact OBs| exact OBLn| clear - PBBB LENB; lia]
      | ].
    all: cbv beta; intros ms' PC; unfold cmpw_postA in PC; ddestruct PC as (y0 & y1 & b0 & b3 & b4 & b5 & b6 & b7 & w & pc & -> & CASES).
    all: rewrite <- EVA, <- EVB in CASES.
    all: destruct CASES as [(-> & [[C1 ->]|[C0 ->]])|(-> & Cm & ->)].
    all: try (eapply (as_KSUBBA m1); [exact AT| rewrite EA; vm_compute; reflexivity| vm_compute; split; [discriminate| reflexivity]| rewrite EA, EB, EF; reflexivity
                                    | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; clear - Cm SS; lia]).
    all: try (eapply (as_KSUBAB m1) with (sg := 1); [exact AT| vm_compute; reflexivity| left; reflexivity| rewrite EA, EB, EF; reflexivity
              | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; clear - C0 SS; lia
              | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; replace (mpd_abs dA - mpd_abs dB) with 0 by (clear - C0 SS; lia); clear; lia]).
    all: try (eapply (as_KSUBAB m1) with (sg := md_sg dA); [exact AT| rewrite EA; vm_compute; reflexivity| exact SGA| rewrite EA, EB, EF; reflexivity
              | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; clear - C1 SS; lia
              | reflexivity]).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WAS.

Definition add_sub_mpi_ng_stmtA_o (flip : Z) (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Ph,(17.O4.O3.O2.)PLB,(18.$19.)PLF,(18.$19.)Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(43.&5.(1:.&40.))Pfc,(1:.&20.)Pm,P,(1:.&40.)(1;.(1:.&8.))Pmo,$44.PdX,$1<.PdA,$1<.PdB,$1<.Plo,$4.Pd,$4.P,(3;.O4.O3.O2.R2;.R2:.R29.R7.)P,(3=.O4.O3.O2.R2<.R7.)P,(32.O4.R9.R2<.R7.)P,(32.O4.R:.R2=.R7.)P,(33.O4.O3.R2=.R;.R2>.(2:.&40.R2;.)R7.)P,(45.R:.R9.)P,(45.R;.R9.)P,(45.R;.R:.)P,(46.(0.$1.(2.R=.)$3.))P,(0.$4.(8.O5.(37.R<.))(38.(37.R=.)))P,P,(6.(2?.R=.)(2?.R>.))(6.(9.R?.)(9.R10.))P,P,(7.(2?.R?.)(2?.R>.))(6.(9.R?.)(9.R11.))P,(47.R11.R10.R>.(2:.&40.R33.))P,(47.R12.R10.R?.(2:.&40.R34.))P,(48.(49.O3.)(4:.$19.R38.(4;.R37.))R10.(3:.R12.)+10.)P,P,(0.$1.(2.R13.)$4<.)(48.(49.O3.)(4:.$19.R3:.(4;.R39.))R12.(?.R14.)(8.+4.(9.R14.)))P,(48.(49.O3.)(4:.$19.R3:.(4;.R39.))R12.(3:.R13.)+10.)P,P,(0.$1.(2.R14.)$4<.)(48.(49.O3.)(4:.$19.R3<.(4;.R3;.))R14.(?.R15.)(8.+4.(9.R15.)))P,(4=.O3.R3<.R3;.(2:.&40.R39.)(4>.O4.O3.O2.R3=.)R17.)P,P,(46.(0.$1.(2.R18.)$4?.))(20.(6.(>.(?.R19.)(8.+4.(9.R19.)))R16.)(6.(2:.&40.R3;.)(?.R19.)))P,(3>.O4.R1;.R16.(2:.&40.R3;.))P,(6.(50.O3.)R17.)P,(6.R18.(39.(39.(2:.&40.R3=.)+100.)(51.O3.)))P,(6.(2:.&40.R3>.)(4>.O4.O3.O2.R42.))P,(0.$4.(2=.(2:.&40.R3?.)+10.)=)P,(0.(1:.&40.)R3>.(29.&40.(52.O3.)))P,(3?.O4.R21.)P,(0.$4.(2=.(2:.&40.R43.)+2.)=)P,(34.O4.(31.O3.)(35.O4.O3.O2.R47.)R23.R21.)P,(34.O4.(31.O3.)(35.O4.O3.O2.R48.)R24.R21.)P,(34.O4.(31.O3.)(35.O4.O3.O2.R49.)R25.R21.)P,P,(46.(0.$4.(3:.R23.)(3:.R24.)))P,(0.$1.(2.R24.)$3.)(0.$:.(11.(?.R25.)(8.+4.(9.R25.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O4.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O4.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R25.)$3.)(6.(>.(>.(?.R26.)(8.+4.(9.R26.)))+8.)(2>.+2.+2?.))P,(6.(>.(53.O4.O3.O2.R4>.)(15.R28.R27.R26.))$54.)P,(55.O4.R2;.(50.O3.)(56.O4.O3.O2.R4?.)(2:.&40.R45.)(2:.&40.R4;.)R25.)P,(57.O3.(3:.R2:.)+10.R26.)P,(57.O3.(3:.R2:.)+10.R27.)P,(57.O3.(3:.R2:.)+10.R28.)P,(6.(>.(58.O4.O3.O2.R53.)(16.R29.))$59.)P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.O5.))(40.O4.(12.O4.O3.O2.R55.R54.R53.R52.R4>.R4=.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R36.R35.R58.R57.R56.R32.(14.O5.R57.R32.R31.R30.)(15.R32.R31.R30.)(16.R2>.)R2?.R34.R33.)(41.(27.(28.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.)R36.(29.&40.O1.)R35.(2;.(1:.&40.))R34.(2<.O4.))R33.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24356290505.0L43712349232.500000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Lemma A_add_sub_mpi_ng_spec_o : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Pflip,$4.P,(20.(0.$4.R1.+1.)(0.$4.R1.-1.))PR,$5:.PHIA,(5;.$<.R1.)P,(5<.(31.R2.))P,(5=.$<.R3.R2.$5>.)P,(6.=(51.R4.))P,Ph,(17.$<.R5.R4.)PLB,(18.$19.)PLF,(18.$19.)Pm,P,(1:.&40.)(1;.(1:.&8.))P,(3;.$<.R9.R8.R4.R3.R2.R1.)(5?.$4.(60.(61.$4.$4.)$4.(62.$4.$4.)R4.))P,(5.(6.(63.(49.R6.))(64.(49.R6.)))(6.(65.(49.R6.))(66.(49.R6.))))P,Pa,$4.P,(0.$:.(;.$<.(=.R1.))$10.)P,(5.(6.=R2.)(7.R2.(2>.+2.+40.)))(5.(6.(63.(49.R:.))R3.)(7.R3.(66.(49.R:.))))(67.R:.$<.R8.R7.$42.)")
(* [comment removed for export] *).
Proof.
  intros flip FLIP R HIA IMG HSUB NEEDR HND DIMG ROIMG. unfold add_sub_mpi_ng_stmtA_o.
  intros until d. intros HH HK MX MA MB SXA SXB SAB NST NGS NGAB NGBA OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA1 IA2 IB2 A47B BUD UW UWX UWA UWB BUDF -> -> -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 32 (AS_FRAME_A ra s0 s1 s2)).
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
    (Rr : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_ng ()) "Ph,(17.O5.O4.O3.)PLB,(18.$19.)PLF,(18.$19.)Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(43.&5.(1:.&40.))Pfc,(1:.&20.)Pm,P,(1:.&40.)(1;.(1:.&8.))Pmo,$44.PdX,$1<.PdA,$1<.PdB,$1<.Plo,$4.Pd,$4.P,(3;.O5.O4.O3.R2;.R2:.R29.R7.)P,(3=.O5.O4.O3.R2<.R7.)P,(32.O5.R9.R2<.R7.)P,(32.O5.R:.R2=.R7.)P,(33.O5.O4.R2=.R;.R2>.(2:.&40.R2;.)R7.)P,(45.R:.R9.)P,(45.R;.R9.)P,(45.R;.R:.)P,(46.(0.$1.(2.R=.)$3.))P,(0.$4.(8.O6.(37.R<.))(38.(37.R=.)))P,P,(6.(2?.R=.)(2?.R>.))(6.(9.R?.)(9.R10.))P,P,(7.(2?.R?.)(2?.R>.))(6.(9.R?.)(9.R11.))P,(47.R11.R10.R>.(2:.&40.R33.))P,(47.R12.R10.R?.(2:.&40.R34.))P,(48.(49.O4.)(4:.$19.R38.(4;.R37.))R10.(3:.R12.)+10.)P,P,(0.$1.(2.R13.)$4<.)(48.(49.O4.)(4:.$19.R3:.(4;.R39.))R12.(?.R14.)(8.+4.(9.R14.)))P,(48.(49.O4.)(4:.$19.R3:.(4;.R39.))R12.(3:.R13.)+10.)P,P,(0.$1.(2.R14.)$4<.)(48.(49.O4.)(4:.$19.R3<.(4;.R3;.))R14.(?.R15.)(8.+4.(9.R15.)))P,(4=.O4.R3<.R3;.(2:.&40.R39.)(4>.O5.O4.O3.R3=.)R17.)P,P,(46.(0.$1.(2.R18.)$4?.))(20.(6.(>.(?.R19.)(8.+4.(9.R19.)))R16.)(6.(2:.&40.R3;.)(?.R19.)))P,(3>.O5.R1;.R16.(2:.&40.R3;.))P,(6.(50.O4.)R17.)P,(6.R18.(39.(39.(2:.&40.R3=.)+100.)(51.O4.)))P,(6.(2:.&40.R3>.)(4>.O5.O4.O3.R42.))P,(0.$4.(2=.(2:.&40.R3?.)+10.)=)P,(0.(1:.&40.)R3>.(29.&40.(52.O4.)))P,(3?.O5.R21.)P,(0.$4.(2=.(2:.&40.R43.)+2.)=)P,(34.O5.(31.O4.)(35.O5.O4.O3.R47.)R23.R21.)P,(34.O5.(31.O4.)(35.O5.O4.O3.R48.)R24.R21.)P,(34.O5.(31.O4.)(35.O5.O4.O3.R49.)R25.R21.)P,P,(46.(0.$4.(3:.R23.)(3:.R24.)))P,(0.$1.(2.R24.)$3.)(0.$:.(11.(?.R25.)(8.+4.(9.R25.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O5.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R24.)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.R26.))))(0.$:.(;.O5.(=.(>.(?.R27.)R2.)))$10.)(0.$:.(11.(?.R26.)(8.+4.(9.R26.)))$10.)P,P,(0.$1.(2.R25.)$3.)(6.(>.(>.(?.R26.)(8.+4.(9.R26.)))+8.)(2>.+2.+2?.))P,(6.(>.(53.O5.O4.O3.R4>.)(15.R28.R27.R26.))$54.)P,(55.O5.R2;.(50.O4.)(56.O5.O4.O3.R4?.)(2:.&40.R45.)(2:.&40.R4;.)R25.)P,(57.O4.(3:.R2:.)+10.R26.)P,(57.O4.(3:.R2:.)+10.R27.)P,(57.O4.(3:.R2:.)+10.R28.)P,(6.(>.(58.O5.O4.O3.R53.)(16.R29.))$59.)P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))P,(0.(1:.&40.)R48.(29.&40.(3:.R2>.)))(40.O5.(12.O5.O4.O3.R54.R53.R52.R51.R4=.R4<.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R35.R34.R57.R56.R55.R31.A4.O1.R56.R31.R30.R2?.(15.R31.R30.R2?.)(16.R2=.)R2>.R33.R32.)(41.(27.(28.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.)R35.(29.&40.O2.)R34.(2;.(1:.&40.))R33.(2<.O5.))R32.))")
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
