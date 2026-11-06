(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_divmod_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_copy A_mpi_journey A_mpi_journey2
     A_mpi_add_abs_W A_mpi_sub_abs A_mpi_add_sub A_mpi_add_sub_ng A_mpi_add_sub_ng_sz A_mpi_stmtA_sz A_mpi_add_sub_stmtSZ A_mpi_div_stmtA A_mpi_mod_stmtA A_mpi_mod_mpi_C.
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
Ltac2 gd_tbl_A_mpi_mod_mpi () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.A.A_mpi_mod_stmtA.mod_mpi_Rs"; "OSSVerify.KrLib.A.A_mpi_add_sub.add_sub_FR"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "WMD.MD_FRAME_A"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.A.A_mpi_div_stmtA.div_mpi_nz"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "WMD.MD_POST_A"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.A.A_mpi_journey.JBA"; "OSSVerify.KrLib.A.A_mpi_journey.BJA"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "OSSVerify.KrLib.A.A_mpi_add_sub_ng_sz.add_sub_mpi_ng_Rsz"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_ADD_SUB_MPI"; "OSSVerify.KrLib.A.A_mpi_add_sub.add_sub_PHI"; "OSSVerify.KrLib.A.A_mpi_add_sub_stmtSZ.add_sub_mpi_Rsz"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.sshad"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.A.A_mpi_mod_stmtA.A_MPI_MOD_MPI_E"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.A.A_mpi_div_stmtA.mpi_div_mpi_stmtA"; "OSSVerify.KrLib.A.A_mpi_div_stmtA.A_MPI_DIV_MPI_E"; "OSSVerify.KrLib.A.A_mpi_add_sub_ng_sz.add_sub_mpi_ng_stmtA_oz"; "OSSVerify.KrLib.A.A_mpi_add_sub_stmtSZ.add_sub_mpi_stmtA_osz"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.A.A_mpi_mod_stmtA.mpi_mod_mpi_stmtA"; "mod_mpi_PHIg"; "mod_mpi_FRg"].


Section WMD.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variables (PHIf : mpd -> mpd -> mpd -> Z) (FRf : mpd -> mpd -> mpd -> Z -> Z).
  Hypothesis HDIV : mpi_div_mpi_stmtA asegs R HIA A_MPI_DIV_MPI_E PHIf FRf.
  Hypothesis HASN : forall flip, flip = 1 \/ flip = -1 -> add_sub_mpi_ng_stmtA_oz flip asegs R HIA A_ADD_SUB_MPI.
  Hypothesis HADD : add_sub_mpi_stmtA_osz 1 asegs R HIA A_ADD_SUB_MPI.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo slo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition MD_FRAME_A := aa_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis UWB : uw_obj R (md_addr dB) 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis SLO2 : lo <= bv_unsigned sp - MPI_MOD_MPI_STACK_A - arl_need_rt R.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 464 - arl_need_smalloc R.
  Hypothesis LFN : (length LF < 512)%nat.
  Hypothesis C24H : cnt24 LB + C24_DIV_MPI <= C24MAX.
  Hypothesis MB0 : mpd_at asegs m LB dB.
  Hypothesis NRB : 0 <= md_n dB <= 10000.
  Hypothesis IB2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "P,(0.$1.(2.VdB,)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.VdB,))))(0.$:.(;.$<.(=.(>.(?.VdB,)R2.)))$10.)(0.$:.(11.(?.VdB,)(8.+4.(9.VdB,)))$10.)")
(* [comment removed for export] *).
  Local Notation PHId := (PHIf dX dA dB).
  Local Notation FRd := (FRf dX dA dB d).
  Local Notation PHIb := (PHIf dX dA dB + (32 * md_n dB + 48)).
  Local Notation FRb := (FRf dX dA dB d + add_sub_FR d).
  Hypothesis PHId0 : 0 <= PHId.
  Hypothesis FRd0 : 0 <= FRd.
  Hypothesis BUD : havol asegs R HIA h + PHIb <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FRb <= FR_MAX.
  Local Notation NZ := (div_mpi_nz nX (md_n dA) (md_n dB)).

  Definition MD_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "(12.$<.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(14.VLB,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,(>.(8.+20.(9.VdB,))+30.))(>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,(15.Vd,))Vlo,Vm,Vmo,)")
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -144)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A []).
  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation Bv := (Z_to_bv 64 (md_addr dB)).
  Local Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Local Notation SHX8 := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL + 1)).
  Local Notation SHB := (Z_to_bv 64 (Z.shiftr (md_addr dB) 3 + al_sb AL)).
  Local Notation SHB8 := (Z_to_bv 64 (Z.shiftr (md_addr dB) 3 + al_sb AL + 1)).


  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAM; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@L22163852504.155L22972055896.155L25741856728.155L29428324939.5  L31421052760.155L33232266840.155L34987518552.155L40379729343.153L42842486707.155L48958709976.155L52536714200.155L54486063391.154L57408231128.155L60968405464.155L6141606276.1   L64900869464.155L68463140952.155Q15899910614.154Q20510050466.154Q21926974294.154Q24435349718.154Q29963071266.154Q30445619798.154Q33963780182.154Q36223636898.154Q38324966690.154Q3859172566.154 Q39849717666.154Q39974853590.154Q43352947362.154Q4524655138.154 Q45996133718.154Q48510014166.154Q49411331106.154Q53371831074.154Q54531556438.154Q546509986.154  Q55602980898.154Q60541843414.154Q66569427286.154Q6961619874.154 Q7051364770.154 Q9887022678.154 00000>00L00Z00l01:01H01V01d02202@02N03003>03L03P03^03l04K04n05M05l06O06n07M08008S09209U0:40:W0;:0;Y0<80<[0=>0=]0>@0>c0?B0?a0@D0@g0AFS2LF2ra2sp3LFNS2LF2ra2sp3LFNS2LF2ra2sp3LFNS1R2lo3LOS3ALO3ACPS2LF2ra2sp3LFNS2LF2ra2sp3LFNS2LF2ra2sp3LFNS2LF2ra2sp3LFNS2LF2ra2sp3LFNS2LF2ra2sp3LFNS2LF2ra2sp3LFNS1R2LF2ra2sp2lo4SLO23LFN5NEEDR3SPRS2LF2ra2sp3LFNS2LF2ra2sp3LFNS2spS2LF2ra2sp3LFNS2LF2ra2sp3LFNS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R2LF2sp2lo4SLO23LFN5NEEDR3LOSS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R3HIA1h2LF2sp3LFN3TOP2hc3HT14HTOPS1R2LF2sp2lo4SLO23LFN5NEEDR3LOS". (* [comment removed for export] *)
  #[using="IMG JC SLO2 LFN"] Lemma md_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pr,$4.Pxra,(19.&40.)Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxs0',(19.&40.)Pxs1,(19.&40.)Pxa1,(19.&40.)Pxa2,(19.&40.)Pxa3,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs2,(19.&40.)Pxs3,(19.&40.)Pxs4,(19.&40.)Pxs5,(19.&40.)Pxs6,(19.&40.)Pxs7,(19.&40.)Pxs8,(19.&40.)Pxs9,(19.&40.)Pxs10,(19.&40.)Pxs11,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R22.R21.R20.R1?.R1>.R1=.)P,P,(0.$4.R1=.=)(5.(6.=(1?.R1?.))(7.(1?.R1?.)(20.VdB,)))P,(5.(7.(21.(22.+2.+1?.))R1>.)(6.R1>.=))P,(6.(9.R20.)(23.VnX,(9.VdA,)(9.VdB,)))P,(6.R26.(>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,(>.(8.+20.(9.VdB,))+30.)))P,(6.R26.(>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,(15.Vd,)))(24.$<.(25.$<.VR,VHIA,R26.Vmo,)$26.(27.(28.R21.(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R20.R1?.R1>.R1=.R1<.(29.&40.R22.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(29.&40.+:0204.)Vfc,(2;.(19.&40.))R24.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HRV HR HSZ HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold MD_FRAME_A, aa_frame in FR1. replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 13 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold MD_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [| cbn [md_n]; exact HSZ]. split; [split; [exact HRV| exact HR]|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39220637093.0L58421668439.500000100BSS2LB3LBc3dXc1C2C1". (* [comment removed for export] *)
  #[using="JC"] Lemma xa_cnt24 : forall v f hc LBc mc dXc, XJ0 v f hc LBc mc dXc -> cnt24 LBc <= cnt24 LB + 1.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L12128799109.1 L12595581774.1 L13323801016.1 L14047678426.8 L1595225453.19 L15987599189.4 L1609906029.18 L21544288248.8 L23925662431.4 L26502719108.5 L28704391748.3 L34148321367.5 L38569812941.1 L38794418998.5 L39280637297.0 L41630738217.3 L41630738217.4 L41886271693.1 L44773699109.3 L4909293332.8  L53152672072.1 L55466006827.3 L56133118659.5 L56135246785.6 L6141606276.1  L62331028632.1 L66151427842.16L66668349941.1 L66988545454.3 L68583578771.4 00000300700;00U01U01c02`03:03G03[03g04704<04I04J04S04_04d04n05J05N05X05l06@06D06H06b06e07007>S1fS2spS2dBS1R2sp1X2lo4SLO25NEEDR3DSXS1R3HIA3FRf1h1X2sX2nX2pX3xs04padX4ownX2dA2dB1d4BUDF1f2hc2BF4HFR1S2sp2dB2lo3ESKS1R3HIA4PHIf1h1X2sX2nX2pX3xs04padX4ownX2dA2dB3BUD1v2hc2BV3HV1S1R2sp1X2lo4SLO25NEEDR3DSXS2sp2dB2lo2ESS1R2sp2lo4SLO25NEEDRS2sp2lo4LOSPS1R3HIA1h2sp3TOPS3dXcS2sp1X2lo3DSXSS2sp1a2HaS2sp2cs1a2HaS3dXcS1X2dB3SXBS1R2sp2lo4SLO25NEEDR3LO03SPRS2spS2sp3dXc1QS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS2spS2spS2sp2r03SPA1q1r1H2H02q02H4S1vS2dB2E03E16S1R2sp2lo4SLO2". (* [comment removed for export] *)
  #[using="IMG HASN JC TPV UWX UWB SLO2 MB0 IB2 BUD BUDF"] Lemma md_call_ng : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pflip,$4.Pretpc,$4.Pcs,(17.$2=.)Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxs1,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs2,(19.&40.)Pxs3,(19.&40.)Pxs4,(19.&40.)Pxs5,(19.&40.)Pxs6,(19.&40.)Pxs7,(19.&40.)Pxs8,(19.&40.)Pxs9,(19.&40.)Pxs10,(19.&40.)Pxs11,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R1<.R1;.R1:.R19.R18.R17.)P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R1<.R1;.R1:.R19.)P,(30.(0.$4.R22.+1.)(0.$4.R22.-1.))P,(0.$4.(8.R23.(31.VdB,))(21.(31.R1;.)))P,P,(7.(20.R1<.)(20.VdB,))(6.(9.VdB,)(9.R1=.))P,(5.(6.=R24.)(7.R24.(22.+2.+40.)))P,(0.$4.(32.R25.+2.)=)P,(33.$<.R20.(>.(2:.&40.Vsp,)-70.)R25.)P,(0.$4.(34.(35.R26.))+8.)P,(6.R26.(>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,(>.(8.+20.(9.VdB,))+30.)))P,(6.R26.(>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,(15.Vd,)))P,Pr,$4.Ph2,(16.$<.VR,VHIA,)PLB2,(17.$18.)Pm2,P,(19.&40.)(1:.(19.&8.))PdX2,$1;.Py0,(19.&40.)Py1,(19.&40.)Py2,(19.&40.)Pya1,(19.&40.)Pya2,(19.&40.)Pya3,(19.&40.)Pya4,(19.&40.)Pya5,(19.&40.)Pya6,(19.&40.)Pya7,(19.&40.)Py3,(19.&40.)Py4,(19.&40.)Py5,(19.&40.)Py6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R3;.R3:.R12.R11.R10.R?.)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R13.R12.R11.R10.)P,(33.$<.R12.(>.(2:.&40.Vsp,)-70.)R3>.)P,(36.R41.R3;.R39.R39.VdB,R16.R12.)(24.$<.(25.$<.VR,VHIA,R16.Vmo,)$26.(27.(28.(29.&40.R41.)(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R12.R11.R10.(29.&40.(37.VdB,))R36.(29.&40.R17.)R?.R>.R=.R<.R;.R:.R9.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R8.R7.R6.R5.)VF,(29.&40.R41.)Vfc,(2;.(19.&40.))R14.(2<.$<.)))(24.$<.(25.$<.VR,VHIA,R27.Vmo,)$26.(27.(28.(29.&40.R2;.)(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R23.R22.R21.(29.&40.(37.VdB,))R20.(29.&40.VX,)(29.&40.VX,)(29.&40.(37.VdB,))(29.&40.R2<.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)VF,(29.&40.$38.)Vfc,(2;.(19.&40.))R25.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J DBJ B FLIP NGS NGBA RPC RPE SLC SLN BV BF K.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof DBJ as [MBj OB CRB CRBL SXB BIMG]. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    cbn [md_addr md_own md_p md_n] in SXB, OB1, OB2, OB3, OB4, OB5.
    destruct (bja_client _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ [] v f hc LBc mc dXc LBc lo J B ltac:(intros bq Hb _; exact Hb) ltac:(clear - LOSP; lia)) as [CRB1 CRBL1].
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    pose proof (xa_crX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ lo J ltac:(clear - LOSP; lia)) as CRX1. cbn [app] in CRX1.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 40 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 40) with (bv_unsigned sp + -144) in STc, SLOT by (clear; lia).
    assert (SPR' : 0 <= bv_unsigned sp + -144 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    pose proof (HASN flip FLIP) as SPc. unfold add_sub_mpi_ng_stmtA_oz in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (dA := dXc) (dB := dB) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by exact SPR'; rewrite ?AD1;
        first [ exact HH1 | exact HK1 | exact MX1 | exact NS1 | exact STc | exact LOS | exact TPV | exact MI1 | exact UWX | exact UWB | exact NGS | exact NGBA | exact CRX1 | exact CRB1 | exact CRBL1 | exact IB2 | reflexivity
              | lazymatch goal with
                | |- opnd_atA _ _ _ _ _ _ dB => eapply opnd_atA_SP_le; [exact (bj_at _ _ _ _ _ _ _ _ _ _ B)| clear; lia]
                | |- mpd_sep dXc dXc => left; reflexivity
                | |- mpd_sep dXc dB => right; rewrite AD1; clear - SXB; lia
                | |- opnd_sep dXc dXc _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [intros NN; destruct (OWN1 NN) as (EH & _); exact (XP1 EH)|];
                    split; [exact XP1|]; split; [left; reflexivity|]; split; [clear - DSX LOSP; lia|];
                    intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- opnd_sep dXc dB _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [exact OB1|]; split; [exact (bj_sepS _ _ _ _ _ _ _ _ _ _ B)|];
                    split; [right; destruct (md_own dXc) eqn:EOX; [left; discriminate| | left; discriminate];
                            destruct (md_own dB) eqn:EOB; [right; left; reflexivity| |];
                            right; right; apply (bj_sepL _ _ _ _ _ _ _ _ _ _ B EOX); rewrite EOB; discriminate|];
                    split; [clear - ES; lia|]; intros BN; ddestruct (OWNE1 BN) as (_ & _ & _ & _ & ESK & _); clear - ESK; lia
                | |- md_own dXc = LHeap -> client_range _ _ _ (md_p dXc) _ =>
                    intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & XIN & _);
                    eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear; lia| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- _ <= bv_unsigned sp + -144 - 256 - _ => clear - SLO2; lia
                | |- bv_unsigned sp + -144 <= htop _ _ _ _ => rewrite HT1; clear - TOP; lia
                | |- (bv_unsigned sp + -144) mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 retpc) mod 2 = 0 => rewrite unsigned_lit by exact RPC; exact RPE
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (NS1 E)]
                | |- mpd_aobjA _ _ _ _ dB => split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)| intros E; apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B); rewrite E; discriminate]
                | |- X <> X -> _ => intros NE; exfalso; exact (NE eq_refl)
                | |- md_own dXc = LStatic -> _ => intros E; exfalso; exact (NS1 E)
                | |- md_own dB = LStatic -> _ + 8 <= 2^47 => intros E; eapply mpd_at_static47; [exact MB0| exact E]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold add_sub_PHI0; clear - BV BUD HV1; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold add_sub_FR0; clear - BF BUDF HFR1; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite ?(unsigned_lit (md_addr dB)) by (clear - E0 E16; lia); eapply uw_obj_uwc; [exact UWB| clear; lia]
                end
              | match goal with |- ?g => idtac "CALLNG-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST2, HP2 by exact SPR'. rewrite AD1 in HP2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    pose proof CR as [[CR1 BK] NGX].
    (* [comment removed for export] *)
    assert (SLOT2 : rw_cells asegs m2 (bv_unsigned sp + -144) [CB 40 junk]).
    { eapply presA_rw_cells; [exact HP2| exact SLOT| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia|].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - DSX LOSP SLO2 NEEDR; lia| exact I]. }
    assert (SLC2 : rw_cells asegs m2 (bv_unsigned sp + -112) cs).
    { eapply presA_rw_cells; [exact HP2| exact SLC| intros a Ha; left; clear - Ha; lia|].
      cbn [disjoint_from]. rewrite SLN. split; [clear - DSX LOSP SLO2 NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 104)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -144 + Z.of_nat (cells_size [CB 40 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT2. }
    pose proof (xa_call asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -144) 0 0 J ltac:(clear - SLO2 NEEDR; lia)
                  ltac:(clear; lia) ltac:(clear; lia) MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    replace (v + 0) with v in J1 by (clear; lia). replace (f + 0) with f in J1 by (clear; lia).
    pose proof (bja_call asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC dB DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -144) J B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J1| exact B1| exact SLC2| exact CR].
    all: match goal with |- ?g => idtac "CALLNG-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L12595581774.1 L13323801016.1 L14047678426.8 L15987599189.4 L19808959472.4 L21544288248.8 L23925662431.4 L26502719108.5 L28704391748.3 L34148321367.5 L38569812941.1 L38794418998.5 L41630738217.3 L41630738217.4 L41886271693.1 L44773699109.3 L4909293332.8  L53152672072.1 L55466006827.3 L55658718845.4 L56133118659.5 L56135246785.6 L59124818608.2 L60162944383.19L6141606276.1  L62331028632.1 L66151427842.16L66988545454.3 L68583578771.4 L7717366441.19 00000400800R00`00l01F01S01g02302C02H02U02^02j02o03903U03Y03c04504I04]04c05d05h05l06F06Q06_07_S2spS2dBS1R2sp1X2lo4SLO25NEEDR3DSXS2sp2dB2lo3ESKS2dB3dXc3NR1S1R2sp1X2lo4SLO25NEEDR3DSXS2sp2dB2lo2ESS1R2sp2lo4SLO25NEEDRS2sp2lo4LOSPS1R3HIA1h2sp3TOPS3dXcS2sp1X2lo3DSXS2sp1a2HaS2sp2cs1a2HaS3dXcS1X2dB3SXBS1R2sp2lo4SLO25NEEDR3LO03SPRS2spS2sp3dXc1QS2LB4C24H3LBc4C24cS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS1d2D0S1R3HIA4PHIf1h1X2sX2nX2pX3xs04padX4ownX2dA2dB3BUD1v2hc3dXc2BV3HV1S2spS2spS2sp2r03SPA1q1r1H2H02q02H4S2dB2E03E16S1R2sp2lo4SLO2S1R3HIA3FRf1h1X2sX2nX2pX3xs04padX4ownX2dA2dB1d4BUDF1f2hc2BF4HFR1". (* [comment removed for export] *)
  #[using="IMG HADD JC TPV UWX UWB D0 SLO2 C24H MB0 IB2 BUD BUDF"] Lemma md_call_al : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pretpc,$4.Pcs,(17.$2=.)Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxs1,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs2,(19.&40.)Pxs3,(19.&40.)Pxs4,(19.&40.)Pxs5,(19.&40.)Pxs6,(19.&40.)Pxs7,(19.&40.)Pxs8,(19.&40.)Pxs9,(19.&40.)Pxs10,(19.&40.)Pxs11,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R1<.R1;.R1:.R19.R18.R17.)P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R1<.R1;.R1:.R19.)P,(5.(6.=R21.)(7.R21.(22.+2.+40.)))P,(0.$4.(32.R22.+2.)=)P,(33.$<.R1=.(>.(2:.&40.Vsp,)-70.)R22.)P,(0.$4.(34.(35.R23.))+8.)P,(6.(>.R23.(39.R1>.R1>.VdB,))(>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,(>.(8.+20.(9.VdB,))+30.)))P,(6.(>.R23.(15.Vd,))(>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,(15.Vd,)))P,Pr,$4.Ph2,(16.$<.VR,VHIA,)PLB2,(17.$18.)Pm2,P,(19.&40.)(1:.(19.&8.))PdX2,$1;.Py0,(19.&40.)Py1,(19.&40.)Py2,(19.&40.)Pya1,(19.&40.)Pya2,(19.&40.)Pya3,(19.&40.)Pya4,(19.&40.)Pya5,(19.&40.)Pya6,(19.&40.)Pya7,(19.&40.)Py3,(19.&40.)Py4,(19.&40.)Py5,(19.&40.)Py6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)(>.R38.(39.R33.R33.VdB,))(>.R37.(15.Vd,))R12.R11.R10.R?.)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R13.R12.R11.R10.)P,(33.$<.R12.(>.(2:.&40.Vsp,)-70.)R3;.)P,(3:.+1.R38.R36.R36.VdB,R16.R12.)(24.$<.(25.$<.VR,VHIA,R16.Vmo,)$26.(27.(28.(29.&40.R3>.)(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R12.R11.R10.(29.&40.(37.VdB,))R33.(29.&40.R17.)R?.R>.R=.R<.R;.R:.R9.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R8.R7.R6.R5.)VF,(29.&40.R3>.)Vfc,(2;.(19.&40.))R14.(2<.$<.)))(24.$<.(25.$<.VR,VHIA,R24.Vmo,)$26.(27.(28.(29.&40.R28.)(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R20.R1?.R1>.(29.&40.(37.VdB,))R1=.(29.&40.VX,)(29.&40.VX,)(29.&40.(37.VdB,))(29.&40.+1.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)VF,(29.&40.$38.)Vfc,(2;.(19.&40.))R22.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J DBJ B RPC RPE SLC SLN BV BF K.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof DBJ as [MBj OB CRB CRBL SXB BIMG]. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    cbn [md_addr md_own md_p md_n] in SXB, OB1, OB2, OB3, OB4, OB5.
    destruct (bja_client _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ [] v f hc LBc mc dXc LBc lo J B ltac:(intros bq Hb _; exact Hb) ltac:(clear - LOSP; lia)) as [CRB1 CRBL1].
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    pose proof (xa_crX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ lo J ltac:(clear - LOSP; lia)) as CRX1. cbn [app] in CRX1.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 40 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -104 - Z.of_nat 40) with (bv_unsigned sp + -144) in STc, SLOT by (clear; lia).
    assert (SPR' : 0 <= bv_unsigned sp + -144 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    pose proof HADD as SPc. unfold add_sub_mpi_stmtA_osz in SPc.
    pose proof (xa_cnt24 _ _ _ _ _ _ J) as C24c.
    assert (PHI0' : 0 <= add_sub_PHI dXc dXc dB) by (unfold add_sub_PHI, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NR1 NRB; lia).
    assert (FR0' : 0 <= add_sub_FR d) by (unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (dA := dXc) (dB := dB) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by exact SPR'; rewrite ?AD1;
        first [ exact HH1 | exact HK1 | exact MX1 | exact NS1 | exact STc | exact LOS | exact TPV | exact MI1 | exact UWX | exact UWB | exact CRX1 | exact CRB1 | exact CRBL1 | exact IB2 | reflexivity
              | lazymatch goal with
                | |- opnd_atA _ _ _ _ _ _ dB => eapply opnd_atA_SP_le; [exact (bj_at _ _ _ _ _ _ _ _ _ _ B)| clear; lia]
                | |- mpd_sep dXc dXc => left; reflexivity
                | |- mpd_sep dXc dB => right; rewrite AD1; clear - SXB; lia
                | |- opnd_sep dXc dXc _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [intros NN; destruct (OWN1 NN) as (EH & _); exact (XP1 EH)|];
                    split; [exact XP1|]; split; [left; reflexivity|]; split; [clear - DSX LOSP; lia|];
                    intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- opnd_sep dXc dB _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [exact OB1|]; split; [exact (bj_sepS _ _ _ _ _ _ _ _ _ _ B)|];
                    split; [right; destruct (md_own dXc) eqn:EOX; [left; discriminate| | left; discriminate];
                            destruct (md_own dB) eqn:EOB; [right; left; reflexivity| |];
                            right; right; apply (bj_sepL _ _ _ _ _ _ _ _ _ _ B EOX); rewrite EOB; discriminate|];
                    split; [clear - ES; lia|]; intros BN; ddestruct (OWNE1 BN) as (_ & _ & _ & _ & ESK & _); clear - ESK; lia
                | |- md_own dXc = LHeap -> client_range _ _ _ (md_p dXc) _ =>
                    intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & XIN & _);
                    eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear; lia| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- _ <= bv_unsigned sp + -144 - 256 - _ => clear - SLO2; lia
                | |- bv_unsigned sp + -144 <= htop _ _ _ _ => rewrite HT1; clear - TOP; lia
                | |- (bv_unsigned sp + -144) mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 retpc) mod 2 = 0 => rewrite unsigned_lit by exact RPC; exact RPE
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (NS1 E)]
                | |- mpd_aobjA _ _ _ _ dB => split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)| intros E; apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B); rewrite E; discriminate]
                | |- X <> X -> _ => intros NE; exfalso; exact (NE eq_refl)
                | |- md_own dXc = LStatic -> _ => intros E; exfalso; exact (NS1 E)
                | |- md_own dB = LStatic -> _ + 8 <= 2^47 => intros E; eapply mpd_at_static47; [exact MB0| exact E]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BV BUD HV1; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BF BUDF HFR1; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_ADDSUB; unfold C24_DIV_MPI in C24H; clear - C24c C24H; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite ?(unsigned_lit (md_addr dB)) by (clear - E0 E16; lia); eapply uw_obj_uwc; [exact UWB| clear; lia]
                end
              | match goal with |- ?g => idtac "CALLAL-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST2, HP2 by exact SPR'. rewrite AD1 in HP2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    pose proof CR as [[CR1 BK] NGX].
    (* [comment removed for export] *)
    assert (SLOT2 : rw_cells asegs m2 (bv_unsigned sp + -144) [CB 40 junk]).
    { eapply presA_rw_cells; [exact HP2| exact SLOT| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia|].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - DSX LOSP SLO2 NEEDR; lia| exact I]. }
    assert (SLC2 : rw_cells asegs m2 (bv_unsigned sp + -112) cs).
    { eapply presA_rw_cells; [exact HP2| exact SLC| intros a Ha; left; clear - Ha; lia|].
      cbn [disjoint_from]. rewrite SLN. split; [clear - DSX LOSP SLO2 NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 104)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -144 + Z.of_nat (cells_size [CB 40 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT2. }
    pose proof (xa_call asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -144) (add_sub_PHI dXc dXc dB) (add_sub_FR d) J ltac:(clear - SLO2 NEEDR; lia)
                  PHI0' FR0' MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    pose proof (bja_call asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC dB DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -144) J B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J1| exact B1| exact SLC2| exact CR].
    all: match goal with |- ?g => idtac "CALLAL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L56052655885.3L59308546259.300000?00JS3dXc4LENc4PBBcS3dXc2N12N0". (* [comment removed for export] *)
  #[using="JC"] Lemma md_viewX : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R6.R5.R4.R3.R2.R1.)(5.(33.$<.R3.VX,(3;.$2=.(3<.(29.&40.(?.R2.)))(3;.$2=.(3=.(29.&40.(31.R2.)))(3;.$2=.(3=.(29.&40.(9.R2.)))(3;.$2=.(3>.VpadX,)(1>.$2=.))))))(5.(3?.$<.R3.(?.R2.)(40.(41.R2.)))(5.(0.$4.(34.(42.(19.&40.)(41.R2.)))(9.R2.))(5.(5.(6.=(9.R2.))(6.(9.R2.)+2710.))(5.(30.(0.$4.(31.R2.)+1.)(0.$4.(31.R2.)-1.))(5.(30.(0.$4.(9.R2.)=)(5.(7.=(?.R2.))(0.$4.(32.(?.R2.)+4.)=)))(5.(43.$<.(44.VR,)(45.$<.VR,VHIA,R5.)R3.VX,+10.)(5.P,(6.+1.(9.R2.))(43.$<.(44.VR,)(45.$<.VR,VHIA,R6.)R4.(?.R3.)(8.+4.(9.R3.)))(5.(6.=(?.R2.))(6.(>.(?.R2.)(8.+4.(9.R2.)))(22.+2.+40.)))))))))))")
(* [comment removed for export] *).
  Proof.
    intros v f hc LBc mc dXc J.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    cbn [md_addr md_pad] in AD1, PD1, OX1, CX1.
    assert (PNZ : md_own dXc = LHeap -> 0 < md_p dXc) by (intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & _ & _ & _ & P0 & _); exact P0).
    destruct (opnd_rawA _ _ _ _ _ _ _ (opnd_atA_mpd asegs R LF mc LBc (bv_unsigned sp) dXc MX1) PNZ) as (CE & BY & LENc & NRc & SGc & BD & PBc).
    rewrite AD1, PD1 in CE.
    pose proof (bytes_at_bound _ _ _ _ BY) as PBBc. rewrite u32s_length in PBBc.
    split; [exact CE|]. split; [exact BY|]. split; [exact LENc|]. split; [exact NRc|]. split; [exact SGc|]. split; [exact PBc|]. split; [exact OX1|].
    split; [| clear - PBBc LENc; lia].
    intros N1. destruct (md_own dXc) eqn:EO; [exfalso; ddestruct (OWN0 eq_refl) as (_ & N0 & _); clear - N0 N1; lia| | exfalso; exact (NS1 eq_refl)].
    ddestruct (OWN1 ltac:(discriminate)) as (_ & _ & _ & _ & _ & _ & _ & _ & OB & _). exact OB.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L13122345613.3L59308546259.3L60814849324.300000;00E00SS2dB2E03E16S2dB2N12N0S2dB4LENc4PBBc". (* [comment removed for export] *)
  #[using="h ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 JC"] Lemma md_viewB : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R5.R4.R3.R2.)(5.(33.$<.R4.(37.VdB,)(3;.$2=.(3<.(29.&40.(?.VdB,)))(3;.$2=.(3=.(29.&40.(31.VdB,)))(3;.$2=.(3=.(29.&40.(9.VdB,)))(3;.$2=.(3>.(46.VdB,))(1>.$2=.))))))(5.(3?.$<.R4.(?.VdB,)(40.(41.VdB,)))(5.(0.$4.(34.(42.(19.&40.)(41.VdB,)))(9.VdB,))(5.(30.(0.$4.(31.VdB,)+1.)(0.$4.(31.VdB,)-1.))(5.(5.(7.=(37.VdB,))(6.(>.(37.VdB,)+10.)(22.+2.+40.)))(5.(30.(0.$4.(9.VdB,)=)(5.(7.=(?.VdB,))(0.$4.(32.(?.VdB,)+4.)=)))(5.(0.$4.(32.(37.VdB,)+8.)=)(5.(43.$<.(44.VR,)(45.$<.VR,VHIA,R6.)R4.(37.VdB,)+10.)(5.P,(6.+1.(9.VdB,))(43.$<.(44.VR,)(45.$<.VR,VHIA,R7.)R5.(?.VdB,)(8.+4.(9.VdB,)))(5.(6.=(?.VdB,))(6.(>.(?.VdB,)(8.+4.(9.VdB,)))(22.+2.+40.))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros hc LBc mc dXc DBJ B.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    assert (PNZ : md_own dB = LHeap -> 0 < md_p dB) by (intros EH; ddestruct (OWNE1 ltac:(rewrite EH; discriminate)) as (_ & P0 & _); exact P0).
    destruct (opnd_rawA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B) PNZ) as (CE & BY & LENc & NRc & SGc & BD & PBc).
    pose proof (bytes_at_bound _ _ _ _ BY) as PBBc. rewrite u32s_length in PBBc.
    split; [exact CE|]. split; [exact BY|]. split; [exact LENc|]. split; [exact SGc|]. split; [clear - E0 E16; lia|]. split; [exact PBc|]. split; [exact EAL|].
    split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)|]. split; [| clear - PBBc LENc; lia].
    intros N1. apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B). intros EN. destruct (OWNE0 EN) as (_ & N0). clear - N0 N1. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mdL2_stmt (D : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pxra,(19.&40.)Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxa0,(19.&40.)Pxa1,(19.&40.)Pxa2,(19.&40.)Pxa3,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R16.R15.R14.R13.R12.R11.)P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R16.R15.R14.R13.)P,(33.$<.R15.(>.(2:.&40.Vsp,)-70.)(3;.$2=.(3<.(29.&40.(>.(>.(47.(37.VdB,)+3.)(48.(44.VR,)))+1.)))(1>.$2=.)))P,(0.$4.(31.VdB,)+1.)P,(7.=(20.VdB,))P,(5.(6.=(1?.R17.))(7.(1?.R17.)(8.(34.O1.)(20.VdB,))))P,(6.(9.R18.)(23.VnX,(9.VdA,)(9.VdB,)))P,(6.R1>.(>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,(>.(8.+20.(9.VdB,))+30.)))P,(6.R1>.(>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,(15.Vd,)))(24.$<.(25.$<.VR,VHIA,R1>.Vmo,)$26.(27.(28.R1:.(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R19.R18.R17.(29.&40.(37.VdB,))(29.&40.(>.(37.VdB,)+:.))R16.R15.R14.R13.R12.R11.R10.R?.(29.&40.VX,)(29.&40.(>.VX,+8.))(29.&40.(>.VX,+:.))(29.&40.(>.(37.VdB,)+8.))(29.&40.(48.(44.VR,)))(29.&40.(>.(>.(47.(37.VdB,)+3.)(48.(44.VR,)))+1.))(29.&40.(>.(47.VX,+3.)(48.(44.VR,))))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))(29.&40.(>.(47.(37.VdB,)+3.)(48.(44.VR,))))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))R>.R=.R<.R;.)VF,(29.&40.+:0374.)Vfc,(2;.(19.&40.))R1<.(2<.$<.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L11390543143.7  L15213097033.1  L19666039969.0  L2259963747.5   L2397676628.0   L28477359117.5  L29010569984.219L29956516996.0  L35663928186.7  L48472061479.1  L4909293332.8   L50652850439.1  L52084259491.6  L52086196796.7  L53920529339.3  L58407100145.3  L58413510254.4  L59308518135.5  L59308632561.1  L59308943857.3  L59314955108.1  L59323343227.6  L60098763854.3  L64822816191.5  L7750571571.2   00000J00N00O00`00a01201301401I01M01i01m01n01o02902F02G02\02`02k02n03I03S03g03nS2nX2dA2dB3dXc3HSZ3dX23NGXS2dBSS2dB1D3dXc2VR3VGESS2dB1D3dXc2VR3VLTFSS1R3HIA1h2sp2lo3TOP1HS2dBS1R2sp2lo4SLO25NEEDR3LO03SPRS2spFFS1X2X03X16S2sp3SPR4SPR'FS2dB3dXc3VGE5EVALX2LTS2KRS2dB3dXc2VRS1ES2dB3dXc4BPOS3NNX3VGE5EVALXS1R2lo3LOSS1R2sp2lo4SLO25NEEDRS2sp2lo". (* [comment removed for export] *)
  #[using="IMG HASN JC TPV UWX UWB SLO2 LFN MB0 NRB IB2 BUD BUDF"] Lemma md_L2 : forall D, mdL2_stmt D.
  Proof.
    induction D as [|D IH]; unfold mdL2_stmt; intros until xt6; intros J DBJ B SL32 SGB BPOS VR HSZ BV BF; [exfalso; clear - VR; lia|].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc. pose proof (art_alwf asegs R HIA) as ALWF.
    destruct (md_viewX _ _ _ _ _ _ J) as (CEX & XBY & LENX & NRX & SGX & PBX & OXs & OXl & PBBX).
    destruct (md_viewB _ _ _ _ DBJ B) as (CEB & BBY & LENB & SGB' & BBD & PBB & ALB & OBs & OBl & PBBB).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    assert (SLC : crange (hcs asegs R HIA hc) (bv_unsigned sp + -144 + 32) 8) by (eapply crange_sub; [exact SCS| clear - SLO2 NEEDR; lia| clear; lia]).
    assert (SPR' : 0 <= bv_unsigned sp + -144 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    pose proof (mpd_abs_lval dXc LENX) as EVX. pose proof (mpd_abs_lval dB LENB) as EVB.
    pose proof (mpd_abs_nonneg dXc) as NNX.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { eapply (cm_RB AL IMG ALWF (hcs asegs R HIA hc) CSOK) with (xs := md_limbs dXc) (ys := md_limbs dB) (sg := md_sg dXc) (sg' := md_sg dB);
        rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by exact SPR';
        first [ exact CEX | exact XBY | exact LENX | exact NRX | exact SGX | exact PBX | exact XAL | exact OXs | exact OXl | exact PBBX
              | exact CEB | exact BBY | exact LENB | exact NRB | exact SGB' | exact BBD | exact PBB | exact ALB | exact OBs | exact OBl | exact PBBB
              | exact SLC | (clear - X0 X16; lia) | (clear - SPR SPR'; lia)
              | (replace (bv_unsigned sp + -144 + 32) with (bv_unsigned sp + -112) by (clear; lia); exact SL32)
              | match goal with |- ?g => idtac "L2-CUT-LEFT:" g end ]. }
    cbv beta. intros ms' PC. unfold cmRB_post in PC. ddestruct PC as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & pc & -> & CASES).
    rewrite <- EVX, <- EVB in CASES. fold (mpd_val dXc) in CASES.
    assert (EVALB : md_sg dB * mpd_abs dB = mpd_abs dB) by (rewrite SGB; clear; lia).
    assert (EVALX : md_sg dXc * mpd_abs dXc = mpd_val dXc) by (unfold mpd_val, mpd_abs; reflexivity).
    rewrite EVALB, EVALX in CASES.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    destruct CASES as [(-> & VGE)|(-> & VLT)].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      assert (SX1 : md_sg dXc = 1) by (destruct SGX as [E|E]; [exact E| exfalso; rewrite E in EVALX; clear - EVALX VGE BPOS NNX; lia]).
      eapply (md_call_ng (-1) 0x0a0370 [C8 SHB8]); [exact J| exact DBJ| exact B| right; reflexivity| rewrite SGB, SX1; reflexivity| | clear; lia| reflexivity| exact SL32| reflexivity| exact BV| exact BF|].
      { intros LT. exfalso. rewrite SX1 in EVALX. clear - LT EVALX VGE. lia. }
      intros r h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 J2 B2 SL2 [[CR1 BK] NGX].
      pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
      pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
      (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR.
      + destruct CR1 as [(-> & _)| ->]; [exfalso; apply KR; reflexivity|].
        eapply md_ret; [exact J2| intros E; exfalso; clear - E; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in E; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| clear - NGX HSZ; lia| exact BV| exact BF].
      + destruct CR1 as [(-> & CV)| ->]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
        eapply IH; [exact J2| exact DBJ| exact B2| exact SL2| exact SGB| exact BPOS| | clear - NGX HSZ; lia| exact BV| exact BF].
        assert (VB : mpd_val dB = mpd_abs dB) by (unfold mpd_val, mpd_abs; rewrite SGB; clear; lia).
        rewrite CV, VB. clear - VR VGE. lia.
    - (* [comment removed for export] *)
      zstep. zstep.
      eapply md_ret; [exact J| intros _; clear - VR VLT; lia| clear; lia| exact HSZ| exact BV| exact BF].
    all: match goal with |- ?g => idtac "L2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mdL2S_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pxra,(19.&40.)Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxa0,(19.&40.)Pxa1,(19.&40.)Pxa2,(19.&40.)Pxa3,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs5,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R17.R16.R15.R14.R13.R12.)P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R17.R16.R15.R14.)P,(0.$4.(31.VdB,)+1.)P,(7.=(20.VdB,))P,(6.=(1?.R17.))P,(6.(9.R18.)(23.VnX,(9.VdA,)(9.VdB,)))P,(6.R1>.(>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,(>.(8.+20.(9.VdB,))+30.)))P,(6.R1>.(>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,(15.Vd,)))(24.$<.(25.$<.VR,VHIA,R1>.Vmo,)$26.(27.(28.R1:.(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R19.R18.R17.(29.&40.(37.VdB,))(29.&40.(>.(37.VdB,)+:.))R16.R15.R14.R13.R12.R11.R10.R?.(29.&40.VX,)(29.&40.(>.VX,+8.))(29.&40.(>.VX,+:.))R>.(29.&40.(48.(44.VR,)))(29.&40.(>.(>.(47.(37.VdB,)+3.)(48.(44.VR,)))+1.))(29.&40.(>.(47.VX,+3.)(48.(44.VR,))))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))(29.&40.(47.(37.VdB,)+3.))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))R=.R<.R;.R:.)VF,(29.&40.+:0320.)Vfc,(2;.(19.&40.))R1<.(2<.$<.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01:0@D15901575446.181D26091612182.182D45160003990.182D50818716548.181D50818716548.182D61461898774.182L15477852824.1  L15721268557.5  L18411264003.177L18485485645.7  L20515953304.1  L21677780975.7  L23332241046.14 L23999514035.177L24692878938.2  L26165518232.1  L26442769048.1  L26502719108.5  L28927958424.1  L31233870980.5  L33177208579.177L35663928186.7  L36655483780.5  L37333429517.1  L37667531699.176L39925338375.1  L41672855235.5  L41684946381.5  L43936270986.176L44946460034.5  L4909293332.8   L4931458125.5   L50764594099.177L52259572182.1  L53932552967.1  L54336572163.177L54543337739.1  L54742141067.1  L55610740483.176L5699518471.1   L58642696772.176L59796868531.177L60025644926.2  L60098763854.3  L60511993092.5  L61316141063.1  L6141606276.1   L65413378443.1  L65603665675.1  L65925215236.5  L68232397517.5  L7555946507.1   Q11801279589.181Q11801279589.182Q19413019498.179Q23865888313.181Q25513505925.180Q25513505925.181Q29323018297.181Q34060184889.180Q361544426.179  Q44959003810.178Q48474655784.178Q49698585326.179Q49698585326.180Q5059831365.178 Q50854279243.178Q50969789734.178Q5677550785.178 Q56993377951.177Q5829129450.179 Q58874076138.178Q63331163577.181Q63333451516.17700001802<03@04G05J06N06R06f07=07X07\08608:08Q08X08\08`09409809L09c0:80:L0:P0:g0:k0;?0;S0<10<E0<a0=50=L0=P0=T0=k0=o0>30>J0>N0>l0?C0?I0?S0?g0?k0?o0@30@70@K0@_0@c0AH0Ak0BE0C60C^0DD0E50Ej0FD0Ff0GH0Gh0HH0H]0I20IT0Ii0JK0Je0K?0L00LES1R2LF2ra2sp1X3xs02dB2lo4SLO23LFN3xs55NEEDR3LOS2X03SPR2E02HB5Ha_st5Hl_stS1R2LF2ra2sp1X3xs02dB2lo4SLO23LFN5NEEDR3LOS2X03SPR2E02HB5Ha_st5Hl_stS1R2LF2ra2sp1X3xs02dB2lo4SLO23LFN5NEEDR3LOS2X03SPR2E02HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1X3xs02dB3LFN2hc3xs53TOP2X03SPR2E03HT12HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1X3xs02dB3LFN2hc3TOP2X03SPR2E03HT12HB5Ha_st5Hl_stS1R2LF2ra2sp1X3xs02dB2lo4SLO23LFN5NEEDR3LOS2X03SPR2E02HB5Ha_st5Hl_stS2spS1R2sp2lo4SLO25NEEDRS2LF2ra2sp1X3xs02dB3LFNS1R2sp2dB2lo4SLO25NEEDR3ESKS2spS1R2sp2dB2lo4SLO25NEEDR2ESS2spS2LF2ra2sp1X3xs02dB3LFNS2sp2loS2spS2spS1R2sp2lo4SLO25NEEDRS2spS1R2sp2lo4SLO25NEEDRS2LF2ra2sp1X3xs02dB3LFNS1R3HIA1h2sp2lo3TOP1HS1R2sp2lo4SLO25NEEDRS2spS2LF2ra2sp1X3xs02dB3LFNS2spS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS2LF2ra2sp1X3xs02dB3LFN2E03E16S1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDR3LO03SPRS1R2sp2lo4SLO25NEEDRS2LF2ra2sp1X3xs02dB3LFNS2spS2spS2LF2ra2sp1X3xs02dB3LFNS2spS2spS2LF2ra2sp1X3xs02dB3LFNS2spS2LF2ra2sp1X3xs02dB3LFN2E03E16S2LF2ra2sp1X3xs02dB3LFNS1R2dBS1R2lo3LOSS1R2sp2lo4SLO25NEEDRS2spS2spS2spS2spS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS2spS2LF2sp3xs02dB3LFN3xs52HB5Ha_st5Hl_stS2LF2sp3xs02dB3LFN2HB5Ha_st5Hl_st1RS2LF2sp3xs02dB3LFN4SPR'2HBS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDR2HB5Ha_st5Hl_stS2LF2sp3xs02dB2lo3LFN3xs52HB5Ha_st5Hl_stS2LF2sp3xs02dB2lo3LFN2HB5Ha_st5Hl_st1RS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDR2HB5Ha_st5Hl_stS1R2LF2sp3xs02dB2lo4SLO23LFN3xs55NEEDR2HB5Ha_st5Hl_stS2LF2sp3xs02dB3LFN4SPR'2HBS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDRS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDRS2LF2sp3xs02dB3LFN4SP642HB5Ha_stS2LF2sp3xs02dB3LFN4SP642HB5Ha_stS2LF2sp3xs02dB2lo3LFNS2LF2sp3xs02dB2lo3LFNS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDRS2LF2sp3xs02dB2lo3LFNS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDRS2LF2sp3xs02dB3LFN4SPR'2HBS2LF2sp3xs02dB3LFN4SPR'2HBS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDR2HB5Ha_st5Hl_stS2LF2sp3xs02dB2lo3LFN". (* [comment removed for export] *)
  #[using="IMG HASN JC TPV UWX UWB SLO2 LFN MB0 NRB IB2 BUD BUDF"] Lemma md_L2S : mdL2S_stmt.
  Proof.
    unfold mdL2S_stmt; intros until xt6; intros J DBJ B SGB BPOS VR HSZ BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    assert (SPR' : 0 <= bv_unsigned sp + -144 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STa [j32 S32]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STa, S32 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -112) 8 STa ltac:(clear - SLO2 NEEDR; lia)) as [STb [j24 S24]].
    replace (bv_unsigned sp + -112 - Z.of_nat 8) with (bv_unsigned sp + -120) in STb, S24 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -120) 8 STb ltac:(clear - SLO2 NEEDR; lia)) as [STc [j16 S16]].
    replace (bv_unsigned sp + -120 - Z.of_nat 8) with (bv_unsigned sp + -128) in STc, S16 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -128) 8 STc ltac:(clear - SLO2 NEEDR; lia)) as [STd [j8 S8]].
    replace (bv_unsigned sp + -128 - Z.of_nat 8) with (bv_unsigned sp + -136) in STd, S8 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -136) 8 STd ltac:(clear - SLO2 NEEDR; lia)) as [STe [j0 S0]].
    replace (bv_unsigned sp + -136 - Z.of_nat 8) with (bv_unsigned sp + -144) in STe, S0 by (clear; lia).
    clear STa STb STc STd.
    pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -104)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ST1' : stk asegs m1 lo (bv_unsigned sp - 104)).
    { pose proof (stk_of_rw_cells asegs _ _ _ S0) as T0. pose proof (stk_of_rw_cells asegs _ _ _ S8) as T8. pose proof (stk_of_rw_cells asegs _ _ _ S16) as T16.
      pose proof (stk_of_rw_cells asegs _ _ _ S24) as T24. pose proof (stk_of_rw_cells asegs _ _ _ S32) as T32.
      cbn [cells_size csize Nat.add] in T0, T8, T16, T24, T32. change (Z.of_nat 8) with 8 in T0, T8, T16, T24, T32.
      replace (bv_unsigned sp + -144 + 8) with (bv_unsigned sp + -136) in T0 by (clear; lia).
      replace (bv_unsigned sp + -136 + 8) with (bv_unsigned sp + -128) in T8 by (clear; lia).
      replace (bv_unsigned sp + -128 + 8) with (bv_unsigned sp + -120) in T16 by (clear; lia).
      replace (bv_unsigned sp + -120 + 8) with (bv_unsigned sp + -112) in T24 by (clear; lia).
      replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp - 104) in T32 by (clear; lia).
      eapply stk_merge; [| exact T32| clear - SLO2 NEEDR; lia]. eapply stk_merge; [| exact T24| clear - SLO2 NEEDR; lia].
      eapply stk_merge; [| exact T16| clear - SLO2 NEEDR; lia]. eapply stk_merge; [| exact T8| clear - SLO2 NEEDR; lia].
      eapply stk_merge; [exact STe| exact T0| clear - SLO2 NEEDR; lia]. }
    pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m1 J MU WM MI1 ST1' HH1 ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as J2.
    assert (EDX : mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) (md_limbs dXc) (md_pad dXc) (md_own dXc) = dXc) by (destruct dXc; reflexivity).
    rewrite EDX in J2.
    pose proof (bja_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J B MU WM
                  ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear - SLO2 NEEDR; lia| clear; lia]| apply Forall_nil])
                  ltac:(cbn; split; [clear - ES SLO2 NEEDR; lia| exact I])
                  ltac:(intros EN; cbn; split; [ddestruct (OWNE1 EN) as (_ & _ & _ & _ & ESK & _); clear - ESK SLO2 NEEDR; lia| exact I])) as B2.
    replace (Z.shiftr (md_addr dB + 8) 3 + al_sb AL) with (Z.shiftr (md_addr dB) 3 + al_sb AL + 1) in * by (rewrite (shr3_8 (md_addr dB) EAL); clear; lia).
    eapply (md_L2 (S (Z.to_nat (mpd_val dXc)))); [exact J2| exact DBJ| exact B2| exact S32| exact SGB| exact BPOS| | exact HSZ| exact BV| exact BF].
    split; [exact VR|]. clear - VR BPOS. nia.
    all: match goal with |- ?g => idtac "L2S-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation L1ST xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 mc :=
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 Bv (Z_to_bv 64 (md_addr dB + 10)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 X) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 (X + 10)) xs5 SB SHB8 SHX SHX8 (Z_to_bv 64 (Z.shiftr (md_addr dB) 3)) SHX8 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x0a0274) fc None mc (seg_rom asegs)).

  Local Ltac l1_cut J DBJ B :=
    eapply (aevtA_cut_evtA_KF asegs R HIA _ mo);
    [ eapply (ci_R AL IMG (art_alwf asegs R HIA) (hcs asegs R HIA _) (hcs_ok asegs R HIA _)) with (xs := md_limbs _) (sg := md_sg _) (ys := md_limbs dB) (Y := md_addr dB)
    | ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L45885450108.55L53920529339.3 L59308517619.3 00000100;00FFS1X2X03X16S3dXc2VR2LP". (* [comment removed for export] *)
  #[using="IMG HASN JC TPV UWX UWB SLO2 LFN MB0 NRB IB2 BUD BUDF"] Lemma md_L1_nonneg : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pxra,(19.&40.)Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxa0,(19.&40.)Pxa1,(19.&40.)Pxa2,(19.&40.)Pxa3,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs5,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R17.R16.R15.R14.R13.R12.)P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R17.R16.R15.R14.)P,(0.$4.(31.VdB,)+1.)P,(7.=(20.VdB,))P,(6.=(1?.R17.))P,(6.(9.R18.)(23.VnX,(9.VdA,)(9.VdB,)))P,(6.R1>.(>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,(>.(8.+20.(9.VdB,))+30.)))P,(6.R1>.(>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,(15.Vd,)))(24.$<.(25.$<.VR,VHIA,R1>.Vmo,)$26.(27.(28.R1:.(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R19.R18.R17.(29.&40.(37.VdB,))(29.&40.(>.(37.VdB,)+:.))R16.R15.R14.R13.R12.R11.R10.R?.(29.&40.VX,)(29.&40.(>.VX,+8.))(29.&40.(>.VX,+:.))R>.(29.&40.(48.(44.VR,)))(29.&40.(>.(>.(47.(37.VdB,)+3.)(48.(44.VR,)))+1.))(29.&40.(>.(47.VX,+3.)(48.(44.VR,))))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))(29.&40.(47.(37.VdB,)+3.))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))R=.R<.R;.R:.)VF,(29.&40.+:0274.)Vfc,(2;.(19.&40.))R1<.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J DBJ B SGB BPOS VR HSZ BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    destruct (md_viewX _ _ _ _ _ _ J) as (CEX & XBY & LENX & NRX & SGX & PBX & OXs & OXl & PBBX).
    destruct (md_viewB _ _ _ _ DBJ B) as (CEB & BBY & LENB & SGB' & BBD & PBB & ALB & OBs & OBl & PBBB).
    pose proof (mpd_abs_lval dXc LENX) as EVX. pose proof (mpd_abs_nonneg dXc) as NNX.
    l1_cut J DBJ B.
    { first [ exact CEX | exact XBY | exact LENX | exact NRX | exact SGX | exact PBX | exact XAL | exact OXs | exact OXl | exact PBBX | exact BBD
            | (clear - X0 X16; lia) | match goal with |- ?g => idtac "L1N-CUT-LEFT:" g end ]. }
    all: try first [ exact CEX | exact XBY | exact LENX | exact NRX | exact SGX | exact PBX | exact XAL | exact OXs | exact OXl | exact PBBX | exact BBD | (clear - X0 X16; lia) ].
    cbv beta. intros ms' PC. unfold ciR_post in PC. ddestruct PC as (b0 & b1 & b2 & b3 & b4 & pc & -> & CASES).
    rewrite <- EVX in CASES.
    destruct CASES as [(-> & _)|(-> & SN & LP)].
    - eapply md_L2S; [exact J| exact DBJ| exact B| exact SGB| exact BPOS| exact VR| exact HSZ| exact BV| exact BF].
    - exfalso. unfold mpd_val in VR. rewrite SN in VR. unfold mpd_abs in LP. clear - VR LP. lia.
    all: match goal with |- ?g => idtac "L1N-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition mdL1_stmt (D : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pxra,(19.&40.)Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxa0,(19.&40.)Pxa1,(19.&40.)Pxa2,(19.&40.)Pxa3,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs5,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R17.R16.R15.R14.R13.R12.)P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R17.R16.R15.R14.)P,(0.$4.(31.VdB,)+1.)P,(7.=(20.VdB,))P,(7.(21.(1?.R17.))(8.(34.O1.)(20.VdB,)))P,(6.(9.R18.)(23.VnX,(9.VdA,)(9.VdB,)))P,(6.R1>.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)P,(6.R1>.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,)(24.$<.(25.$<.VR,VHIA,R1>.Vmo,)$26.(27.(28.R1:.(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R19.R18.R17.(29.&40.(37.VdB,))(29.&40.(>.(37.VdB,)+:.))R16.R15.R14.R13.R12.R11.R10.R?.(29.&40.VX,)(29.&40.(>.VX,+8.))(29.&40.(>.VX,+:.))R>.(29.&40.(48.(44.VR,)))(29.&40.(>.(>.(47.(37.VdB,)+3.)(48.(44.VR,)))+1.))(29.&40.(>.(47.VX,+3.)(48.(44.VR,))))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))(29.&40.(47.(37.VdB,)+3.))(29.&40.(>.(>.(47.VX,+3.)(48.(44.VR,)))+1.))R=.R<.R;.R:.)VF,(29.&40.+:0274.)Vfc,(2;.(19.&40.))R1<.(2<.$<.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L11390543143.7  L12528441727.3  L12901507639.4  L15213097033.1  L15477852824.1  L17091650993.13 L1967622487.14  L20944725665.0  L26502719108.5  L29010569984.216L29010569984.217L29010569984.219L29956516996.0  L3041163862.7   L31835123200.2  L34488012176.1  L3620002362.3   L37446158749.1  L38483850804.5  L45885450108.55 L53920529339.3  L59308518135.4  L59308632561.1  L59314955108.1  L6141606276.1   L64861823320.13 L931176162.14   00000J00U00a00e00i01W02J02K02_02`02a02b02c03=03F03K03W03\03i03j04404C04G04J04N05905gS2nX2dA2dB3dXc3HSZ3dX23NGXS2dB3dXc2VRS2dB3dXc3NLTS2dBS2spS4PHIf1X2sX2nX2pX3xs04padX4ownX2dA2dB3NRB1v2BVS4PHIf1X2sX2nX2pX3xs04padX4ownX2dA2dB1v3dXc2BV4PHIASS1R2sp2lo4SLO25NEEDRFFFSS2nX2dA2dB3dXc3NLT3dX23NGXS3dXc3NNXS3dXcS2dB3dXc3ALTS3dXcS2dB1D3dXc2VRFS1X2X03X16S2dB3dXc3AGE2LTS2KRS1ES2spS3FRf1X2sX2nX2pX3xs04padX4ownX2dA2dB1d1f2BFS3FRf1X2sX2nX2pX3xs04padX4ownX2dA2dB1d2D01f2BF". (* [comment removed for export] *)
  #[using="IMG HASN HADD JC TPV UWX UWB D0 SLO2 LFN C24H MB0 NRB IB2 BUD BUDF"] Lemma md_L1 : forall D, mdL1_stmt D.
  Proof.
    induction D as [|D IH]; unfold mdL1_stmt; intros until xt6; intros J DBJ B SGB BPOS VR HSZ BV BF.
    - (* [comment removed for export] *)
      eapply md_L1_nonneg; [exact J| exact DBJ| exact B| exact SGB| exact BPOS| clear - VR; lia| exact HSZ| clear - BV NRB; lia|].
      unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge. clear - BF D0. lia.
    - jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
        cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
      destruct (md_viewX _ _ _ _ _ _ J) as (CEX & XBY & LENX & NRX & SGX & PBX & OXs & OXl & PBBX).
      destruct (md_viewB _ _ _ _ DBJ B) as (CEB & BBY & LENB & SGB' & BBD & PBB & ALB & OBs & OBl & PBBB).
      pose proof (mpd_abs_lval dXc LENX) as EVX. pose proof (mpd_abs_nonneg dXc) as NNX.
      assert (BV' : v <= PHIb) by (clear - BV NRB; lia).
      assert (BF' : f <= FRb) by (unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - BF D0; lia).
      assert (VB : mpd_val dB = mpd_abs dB) by (unfold mpd_val, mpd_abs; rewrite SGB; clear; lia).
      l1_cut J DBJ B.
      { first [ exact CEX | exact XBY | exact LENX | exact NRX | exact SGX | exact PBX | exact XAL | exact OXs | exact OXl | exact PBBX | exact BBD
              | (clear - X0 X16; lia) | match goal with |- ?g => idtac "L1-CUT-LEFT:" g end ]. }
      all: try first [ exact CEX | exact XBY | exact LENX | exact NRX | exact SGX | exact PBX | exact XAL | exact OXs | exact OXl | exact PBBX | exact BBD | (clear - X0 X16; lia) ].
      cbv beta. intros ms' PC. unfold ciR_post in PC. ddestruct PC as (b0 & b1 & b2 & b3 & b4 & pc & -> & CASES).
      rewrite <- EVX in CASES.
      destruct CASES as [(-> & NNEG)|(-> & SN & LP)].
      + (* [comment removed for export] *)
        eapply md_L2S; [exact J| exact DBJ| exact B| exact SGB| exact BPOS| | exact HSZ| exact BV'| exact BF'].
        unfold mpd_val. fold (mpd_abs dXc). destruct NNEG as [Z0|S1]; [rewrite Z0; clear; lia| rewrite S1; clear - NNX; lia].
      + (* [comment removed for export] *)
        pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
        basic_factsA hc.
        pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
        pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
        zstep. zstep. zstep. zstep. zstep.
        replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1 by (clear; lia).
        destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [_ [j32 S32]].
        replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in S32 by (clear; lia).
        assert (VX : mpd_val dXc = - mpd_abs dXc) by (unfold mpd_val, mpd_abs; rewrite SN; clear; lia).
        destruct (Z_lt_le_dec (mpd_abs dXc) (mpd_abs dB)) as [ALT|AGE]; [destruct (Z_lt_le_dec (md_n dXc) (md_n dB)) as [NLT|NGE]|].
        * (* [comment removed for export] *)
          assert (PHIA : add_sub_PHI dXc dXc dB <= 32 * md_n dB + 48).
          { unfold add_sub_PHI, add_abs_PHI, grow_PHI; unfold AVOL_CALL. clear - NLT NRX. lia. }
          eapply (md_call_al 0x0a0300 [CB 8 j32]); [exact J| exact DBJ| exact B| clear; lia| reflexivity| exact S32| reflexivity| clear - BV PHIA; lia| clear - BF; lia|].
          intros r h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 J2 B2 SL2 [[CR1 BK] NGX].
          assert (HSZ2 : md_n dX2 <= NZ) by (unfold addsub_nz in NGX; unfold div_mpi_nz; clear - NGX NLT; lia).
          pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
          pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
          (* [comment removed for export] *)
          zstep. if_cases KR; zify_cond KR.
          -- destruct CR1 as [(-> & CV)| ->]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
             eapply md_L1_nonneg; [exact J2| exact DBJ| exact B2| exact SGB| exact BPOS| | exact HSZ2| clear - BV PHIA; lia| clear - BF; lia].
             rewrite CV, VB, VX. clear - ALT. lia.
          -- destruct CR1 as [(-> & _)| ->]; [exfalso; apply KR; reflexivity|].
             zstep.
             eapply md_ret; [exact J2| intros E; exfalso; clear - E; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in E; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| exact HSZ2| clear - BV PHIA; lia| clear - BF; lia].
        * (* [comment removed for export] *)
          eapply (md_call_ng 1 0x0a0300 [CB 8 j32]); [exact J| exact DBJ| exact B| left; reflexivity| rewrite SGB, SN; reflexivity| intros _; exact NGE| clear; lia| reflexivity| exact S32| reflexivity| exact BV'| exact BF'|].
          intros r h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 J2 B2 SL2 [[CR1 BK] NGX].
          pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
          pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
          zstep. if_cases KR; zify_cond KR.
          -- destruct CR1 as [(-> & CV)| ->]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
             eapply IH; [exact J2| exact DBJ| exact B2| exact SGB| exact BPOS| | clear - NGX HSZ; lia| exact BV| exact BF].
             rewrite CV, VB. clear - VR BPOS. lia.
          -- destruct CR1 as [(-> & _)| ->]; [exfalso; apply KR; reflexivity|].
             zstep.
             eapply md_ret; [exact J2| intros E; exfalso; clear - E; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in E; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| clear - NGX HSZ; lia| exact BV'| exact BF'].
        * (* [comment removed for export] *)
          eapply (md_call_ng 1 0x0a0300 [CB 8 j32]); [exact J| exact DBJ| exact B| left; reflexivity| rewrite SGB, SN; reflexivity| intros LT; exfalso; clear - LT AGE; lia| clear; lia| reflexivity| exact S32| reflexivity| exact BV'| exact BF'|].
          intros r h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 J2 B2 SL2 [[CR1 BK] NGX].
          pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
          pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
          zstep. if_cases KR; zify_cond KR.
          -- destruct CR1 as [(-> & CV)| ->]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
             eapply IH; [exact J2| exact DBJ| exact B2| exact SGB| exact BPOS| | clear - NGX HSZ; lia| exact BV| exact BF].
             rewrite CV, VB. clear - VR BPOS. lia.
          -- destruct CR1 as [(-> & _)| ->]; [exfalso; apply KR; reflexivity|].
             zstep.
             eapply md_ret; [exact J2| intros E; exfalso; clear - E; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in E; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| clear - NGX HSZ; lia| exact BV'| exact BF'].
    all: match goal with |- ?g => idtac "L1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mdL1S_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pv,$4.Pf,$4.Phc,(16.$<.VR,VHIA,)PLBc,(17.$18.)Pmc,P,(19.&40.)(1:.(19.&8.))PdXc,$1;.Pxra,(19.&40.)Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxa0,(19.&40.)Pxa1,(19.&40.)Pxa2,(19.&40.)Pxa3,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs3,(19.&40.)Pxs4,(19.&40.)Pxs5,(19.&40.)Pxs8,(19.&40.)Pxs9,(19.&40.)Pxs11,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)R1<.R1;.R1:.R19.R18.R17.)P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,R1<.R1;.R1:.R19.)P,(0.$4.(31.VdB,)+1.)P,(7.=(20.VdB,))P,(6.(9.R1<.)(23.VnX,(9.VdA,)(9.VdB,)))P,(6.R22.A3.VPHIf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)P,(6.R22.A4.VFRf,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,Vd,)(24.$<.(25.$<.VR,VHIA,R22.Vmo,)$26.(27.(28.R1>.(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R1=.R1<.R1;.(29.&40.(37.VdB,))(29.&40.(>.(37.VdB,)+:.))R1:.R19.R18.R17.R16.R15.R14.R13.(29.&40.VX,)R12.R11.R10.(29.&40.(48.(44.VR,)))(29.&40.(>.(>.(47.(37.VdB,)+3.)(48.(44.VR,)))+1.))R?.R>.(29.&40.(47.(37.VdB,)+3.))R=.R<.R;.R:.R9.)VF,(29.&40.+:0240.)Vfc,(2;.(19.&40.))R20.(2<.$<.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@D22000850582.179D50818716548.179L15477852824.1  L16962092547.174L18485485645.7  L21677780975.7  L23332241046.14 L24692878938.2  L26502719108.5  L28927958424.1  L29074096193.173L35663928186.7  L37079340467.174L37333429517.1  L39925338375.1  L41672855235.5  L44946460034.5  L46160821889.173L4909293332.8   L4931458125.5   L52259572182.1  L5259801613.173 L60022696548.2  L60098763854.3  L6141606276.1   L65603665675.1  L65925215236.5  Q11801279589.179Q25513505925.178Q35074966634.176Q42453173279.175Q49698585326.177Q53367281020.175Q58585641145.17800001402702;02R02m03G03K03R03f03j04H04]05405805<05P05d06B06^07207607T07Y07c07g07k08?08b09H09b0:D0:d0;90;lS1R2LF2ra2sp1X3xs02dB2lo4SLO23LFN5NEEDR3LOS2X03SPR2E02HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1X3xs02dB3LFN2hc3TOP2X03SPR2E03HT12HB5Ha_st5Hl_stS2spS2LF2ra2sp1X3xs02dB3LFNS1R2sp2dB2lo4SLO25NEEDR3ESKS1R2sp2dB2lo4SLO25NEEDR2ESS2spS2sp2loS1R2sp2lo4SLO25NEEDRS2spS2LF2ra2sp1X3xs02dB3LFN2X03X16S1R3HIA1h2sp2lo3TOP1HS2LF2ra2sp1X3xs02dB3LFNS2spS2spS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS2LF2ra2sp1X3xs02dB3LFN2X03X16S1R2sp2lo4SLO25NEEDR3LO03SPRS1R2sp2lo4SLO25NEEDRS2spS2LF2ra2sp1X3xs02dB3LFN2X03X16S1R1XS1R2lo3LOSS2spS2spS1R2sp2lo4SLO25NEEDRS2LF2sp1X3xs02dB3LFN2HB5Ha_st5Hl_stS2LF2sp1X3xs02dB2lo3LFN2HB5Ha_st5Hl_stS2LF2sp3xs02dB3LFN4SPR'2HBS1R2LF2sp3xs02dB2lo4SLO23LFN5NEEDRS2LF2sp3xs02dB3LFN4SP642HB5Ha_stS2LF2sp3xs02dB2lo3LFNS1R2LF2sp1X3xs02dB2lo4SLO23LFN5NEEDR2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG HASN HADD JC TPV UWX UWB D0 SLO2 LFN C24H MB0 NRB IB2 BUD BUDF"] Lemma md_L1S : mdL1S_stmt.
  Proof.
    unfold mdL1S_stmt; intros until xt6; intros J DBJ B SGB BPOS HSZ BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    assert (SPR' : 0 <= bv_unsigned sp + -144 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in ST1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -104) 8 ST1 ltac:(clear - SLO2 NEEDR; lia)) as [STa [j32 S32]].
    replace (bv_unsigned sp + -104 - Z.of_nat 8) with (bv_unsigned sp + -112) in STa, S32 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -112) 8 STa ltac:(clear - SLO2 NEEDR; lia)) as [STb [j24 S24]].
    replace (bv_unsigned sp + -112 - Z.of_nat 8) with (bv_unsigned sp + -120) in STb, S24 by (clear; lia).
    clear STa.
    pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -104)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 12 zstep.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ST1' : stk asegs m1 lo (bv_unsigned sp - 104)).
    { pose proof (stk_of_rw_cells asegs _ _ _ S24) as T24. pose proof (stk_of_rw_cells asegs _ _ _ S32) as T32.
      cbn [cells_size csize Nat.add] in T24, T32. change (Z.of_nat 8) with 8 in T24, T32.
      replace (bv_unsigned sp + -120 + 8) with (bv_unsigned sp + -112) in T24 by (clear; lia).
      replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp - 104) in T32 by (clear; lia).
      eapply stk_merge; [| exact T32| clear - SLO2 NEEDR; lia]. eapply stk_merge; [exact STb| exact T24| clear - SLO2 NEEDR; lia]. }
    pose proof (xa_scratch _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m1 J MU WM MI1 ST1' HH1 ltac:(clear - SLO2 NEEDR; lia) ltac:(clear; lia)) as J2.
    assert (EDX : mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) (md_limbs dXc) (md_pad dXc) (md_own dXc) = dXc) by (destruct dXc; reflexivity).
    rewrite EDX in J2.
    pose proof (bja_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J B MU WM
                  ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear - SLO2 NEEDR; lia| clear; lia]| apply Forall_nil])
                  ltac:(cbn; split; [clear - ES SLO2 NEEDR; lia| exact I])
                  ltac:(intros EN; cbn; split; [ddestruct (OWNE1 EN) as (_ & _ & _ & _ & ESK & _); clear - ESK SLO2 NEEDR; lia| exact I])) as B2.
    replace (Z.shiftr (X + 10) 3 + al_sb AL) with (Z.shiftr X 3 + al_sb AL + 1) by (rewrite (shr3_10 X XAL); clear; lia).
    replace (Z.shiftr (X + 8) 3 + al_sb AL) with (Z.shiftr X 3 + al_sb AL + 1) by (rewrite (shr3_8 X XAL); clear; lia).
    eapply (md_L1 (S (Z.to_nat (Z.abs (mpd_val dXc))))); [exact J2| exact DBJ| exact B2| exact SGB| exact BPOS| | exact HSZ| exact BV| exact BF].
    clear - BPOS. nia.
    all: match goal with |- ?g => idtac "L1S-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis SAB : mpd_sep dA dB.
  Hypothesis NEB : X <> md_addr dB.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L (LB ++ fdata LF) lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L (LB ++ fdata LF) lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dB) (4 * md_n dB).
  Hypothesis IA2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "P,(0.$1.(2.VdA,)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.VdA,))))(0.$:.(;.$<.(=.(>.(?.VdA,)R2.)))$10.)(0.$:.(11.(?.VdA,)(8.+4.(9.VdA,)))$10.)")
(* [comment removed for export] *).
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.

  (* [comment removed for export] *)
  #[using="IMG MB0 IB2 SXB NEB OB CRB CRBL"] Lemma md_mkJB : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pm1,P,(19.&40.)(1:.(19.&8.))P,(43.$<.(44.VR,)(45.$<.VR,VHIA,Vh,)R1.(37.VdB,)+10.)P,P,(0.$1.(2.VdB,)$3.)(43.$<.(44.VR,)(45.$<.VR,VHIA,Vh,)R3.(?.VdB,)(8.+4.(9.VdB,)))P,(49.$<.VR,VHIA,Vh,VLB,VLF,R3.)P,(4:.$<.R4.VLB,VdB,)(5.(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)(2?.$<.VR,VHIA,VLF,Vsp,VdB,Vh,VLB,R5.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros m1 OEs OEl HM1 ME1'. dpose OB as (OE1 & OE2 & OE3 & OE4 & OE5).
    pose proof (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dB ME1') as ME1.
    assert (SXE : X + 16 <= md_addr dB \/ md_addr dB + 16 <= X).
    { destruct SXB as [E|D']; [exfalso; apply NEB; rewrite <- E; reflexivity| cbn [md_addr] in D'; exact D']. }
    split.
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
      + apply opnd_atA_mpd. exact MB0.
      + intros EO RO hc LBc mc HMc. eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IB2 EO RO)].
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + exact ME1.
      + exact OE2.
      + intros EOX EN. destruct OE3 as [C|[C|[C|C]]]; [exfalso; apply NEB; rewrite <- C; reflexivity| exfalso; exact (C EOX)| exfalso; exact (EN C)| exact C].
      + exact OEs.
      + intros EN. pose proof ME1' as [(_ & _ & _ & _ & _ & OW) _].
        destruct (md_own dB) eqn:EOB; [exfalso; exact (EN eq_refl)| |].
        * ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HM1| exact EIN].
        * exact (OEl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L12595581774.1  L13323801016.1  L13917980321.0  L14047678426.8  L25028196929.12 L25116178193.11 L28377212835.10 L29010569984.224L34148321367.5  L34932287481.9  L41630738217.3  L4909293332.8   L53152672072.1  L56072333459.4  L56133118659.5  L56135246785.6  L59321329782.3  L6004115675.11  L62312621010.15 L66151426447.10 L66151427842.16 L66988545454.3  L67922155668.4  L7044995239.16  00000400800900S01<01b02G02H02X03703@03\03`03n04B04V04b05K06@06P06j07507C089S2spS2dBSS1R2sp1X2lo4SLO25NEEDR3DSXS3FRf1X2sX2nX2pX3xs04padX4ownX2dA2dB1d2D0S3FRf1X2sX2nX2pX3xs04padX4ownX2dA2dB1dS4PHIf1X2sX2nX2pX3xs04padX4ownX2dA2dBFS1R3HIA1h2sp3TOPS2sp1X2sX2nX2pX3xs04padX4ownX1QS2sp1a2HaS1R2sp2lo4SLO25NEEDR3LO03SPRS2spS1R2sp2lo4SLO2S1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO25NEEDRS2dB2Z04BPOSS4PHIf1X2sX2nX2pX3xs04padX4ownX2dA2dB3NRBS1R3HIA4PHIf1h1X2sX2nX2pX3xs04padX4ownX2dA2dB3NRB3BUDS1r2RR2r02KR1q1HS2sp2r03SPA1q1r1H2H02q02H4S2dB2E03E16S1R2sp2lo4SLO3S1R3HIA3FRf1h1X2sX2nX2pX3xs04padX4ownX2dA2dB1d2D04BUDF". (* [comment removed for export] *)
  #[using="IMG HDIV HASN HADD JC TPV UWX UWB D0 SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"] Lemma md_DIV : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pm1,P,(19.&40.)(1:.(19.&8.))Pjunk,(17.(19.&8.))Pxra,(19.&40.)Pxt0,(19.&40.)Pxt1,(19.&40.)Pxt2,(19.&40.)Pxa0,(19.&40.)Pxa1,(19.&40.)Pxa3,(19.&40.)Pxa4,(19.&40.)Pxa5,(19.&40.)Pxa6,(19.&40.)Pxa7,(19.&40.)Pxs3,(19.&40.)Pxs4,(19.&40.)Pxs5,(19.&40.)Pxs8,(19.&40.)Pxs9,(19.&40.)Pxs11,(19.&40.)Pxt3,(19.&40.)Pxt4,(19.&40.)Pxt5,(19.&40.)Pxt6,(19.&40.)P,(1<.$<.VR,VHIA,Vh,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+68.$1=.(1>.$18.)==Vh,VLB,R17.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(2>.$<.VR,VHIA,VLB,VLF,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdB,)P,(2?.$<.VR,VHIA,VLF,Vsp,VdB,Vh,VLB,R19.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(4:.$<.R1:.VLB,VdA,)P,(4:.$<.R1;.VLB,VdB,)P,(4;.$<.(44.VR,)(45.$<.VR,VHIA,Vh,)R1<.VdA,)P,(4;.$<.(44.VR,)(45.$<.VR,VHIA,Vh,)R1=.VdB,)P,(4<.$<.(44.VR,)R1>.Vslo,(>.(2:.&40.Vsp,)-90.))P,(33.$<.R1?.(>.(2:.&40.Vsp,)-90.)(3;.$2=.(4=.#28.R1>.)(1>.$2=.)))P,(4>.$<.R20.Vlo,(>.(2:.&40.Vsp,)-90.))P,(30.(0.$4.(20.VdB,)=)(0.$4.(31.VdB,)+1.))(24.$<.(25.$<.VR,VHIA,Vh,Vmo,)$26.(27.(28.R20.(29.&40.(>.(2:.&40.Vsp,)-90.))Vgp,Vtp,R1?.R1>.R1=.(29.&40.(37.VdB,))(29.&40.(>.(37.VdB,)+:.))R1<.R1;.(29.&40.(37.VdA,))R1:.R19.R18.R17.R16.(29.&40.VX,)R15.R14.R13.(29.&40.(48.(44.VR,)))(29.&40.(>.(>.(47.(37.VdB,)+3.)(48.(44.VR,)))+1.))R12.R11.(29.&40.(47.(37.VdB,)+3.))R10.R?.R>.R=.R<.)VF,(29.&40.+:01?0.)Vfc,(2;.(19.&40.))R22.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J DBJ B MA1 MB1 OAA1 OBA1 SSH1 SLOT STc BSG.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    assert (SPR' : 0 <= bv_unsigned sp + -144 < 2^64) by (clear - SPR LOSP LO0 SLO2 NEEDR; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    pose proof HDIV as SPc. unfold mpi_div_mpi_stmtA in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (slo := slo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by exact SPR'; cbn [md_addr];
        first [ exact HH1 | exact HK1 | exact LFN | exact MX1 | exact MA1 | exact MB1 | exact SXA | exact SXB | exact SAB | exact NST | exact NEB | exact CRA | exact CRAL | exact CRB | exact CRBL
              | exact STc | exact LOS | exact SSH1 | exact SLOS | exact SLOL | exact TPV | exact MI1 | exact OAA1 | exact OBA1 | exact IA2 | exact IB2 | exact UWX | exact C24H | reflexivity
              | lazymatch goal with
                | |- opnd_sep dX dA _ _ => eapply opnd_sep_sp_le; [exact OA| clear; lia]
                | |- opnd_sep dX dB _ _ => eapply opnd_sep_sp_le; [exact OB| clear; lia]
                | |- mpd_writableA _ _ _ _ _ dX => eapply mpd_writableA_sp_mono; [exact XW| clear; lia]
                | |- md_own dX <> LNull -> _ => intros NN; destruct (XLS NN) as [Q|Q]; [left; exact Q| right; clear - Q; lia]
                | |- _ <= bv_unsigned sp + -144 - 576 - _ => clear - SLO2; lia
                | |- _ <= bv_unsigned sp + -144 - 320 - _ => clear - SLO3; lia
                | |- bv_unsigned sp + -144 <= htop _ _ _ _ => clear - TOP; lia
                | |- (bv_unsigned sp + -144) mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- mpd_aobjA _ _ _ _ dX => split; [exact OX1| intros E; exfalso; exact (NST E)]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD NRB; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge in BUDF; clear - BUDF D0; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite ?(unsigned_lit (md_addr dB)) by (clear - E0 E16; lia); eapply uw_obj_uwc; [exact UWB| clear; lia]
                end
              | match goal with |- ?g => idtac "DIV-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST2, HP2 by exact SPR'. cbn [md_addr] in HP2.
    replace (ret_pc (Z_to_bv 64 0xa0200)) with (Z_to_bv 64 0xa0200 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    ddestruct CR as [[[RR RB] BK] HSZ2]. cbn [md_n] in HSZ2.
    assert (SLOT2 : rw_cells asegs m2 (bv_unsigned sp + -144) [CB 40 junk]).
    { eapply presA_rw_cells; [exact HP2| exact SLOT| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia|].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - DSX LOSP SLO2 NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 104)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -144 + Z.of_nat (cells_size [CB 40 junk])) by (cbn; clear; lia).
      apply stk_of_rw_cells. exact SLOT2. }
    pose proof (xa_call asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -144) PHId FRd J ltac:(clear - SLO2 NEEDR; lia)
                  PHId0 FRd0 MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    cbn [Z.add] in J1.
    pose proof (bja_call asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC dB DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 (bv_unsigned sp + -144) J B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      assert (R0 : r = 0) by (clear - KR RR; Z.div_mod_to_equations; lia). subst r.
      pose proof (RB eq_refl) as BPOS.
      assert (SGB : md_sg dB = 1) by (destruct BSG as [Z0|S1]; [exfalso; clear - Z0 BPOS; lia| exact S1]).
      eapply md_L1S; [exact J1| exact DBJ| exact B1| exact SGB| exact BPOS| exact HSZ2| clear; lia| clear; lia].
    - eapply md_ret; [exact J1| intros E; exfalso; apply KR; rewrite E; reflexivity| exact RR| exact HSZ2| clear - NRB; lia|].
      unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge. clear - D0. lia.
    all: match goal with |- ?g => idtac "DIV-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01^0@D18963879599.158D18963879599.159D35881667587.158D35881667587.159L10824412760.151L11898879434.13 L12029260276.151L1229529432.151 L12595581774.1  L13470696480.7  L14008232408.151L14536420468.151L17305750384.4  L17962591320.151L18241568998.154L19431261630.4  L19522073816.150L19945316590.2  L20127843869.12 L20547877620.151L2495824244.150 L26573346676.151L26660252376.151L32583673332.151L33411004248.151L33804722392.151L35653441506.7  L38611382900.151L40834179097.167L42479632545.4  L43059266230.152L43407470040.151L44632654068.151L50141506136.151L50545648600.151L50644114804.151L50667210948.0  L51992981696.3  L53920529339.3  L56135246785.6  L56669580276.151L59179427444.151L59314955108.1  L6001025908.151 L60098763854.3  L62812924760.151L6482734895.4   L65188263156.151L65978332888.151L66151427842.16 L67754954934.1  Q10333294960.171Q15643324129.154Q18365925601.155Q18378753154.155Q18696506101.171Q1936945506.157 Q1936945506.158 Q21800401414.171Q21879645826.155Q24330840805.171Q24389563138.155Q25160350961.171Q25513505925.157Q25513505925.158Q25664719138.171Q27584944865.155Q27907200258.155Q29505479905.155Q30415036802.155Q31226872993.171Q31271525473.155Q31396957457.171Q32655500769.155Q33918256002.155Q35016271767.171Q35715139857.171Q36425882626.155Q36426122721.171Q3830427394.155 Q39939554818.155Q41152393185.155Q4141071397.171 Q42439443119.158Q42439443119.159Q44648843873.155Q4533518817.155 Q49698585326.156Q49698585326.157Q50301287168.171Q51235796833.155Q52101170785.155Q53972118266.171Q54485784450.155Q58443002963.155Q58443002963.156Q59256763233.155Q59843137889.155Q59865321072.158Q59865321072.159Q60511257090.155Q61800308129.171Q6414620453.171 Q64253126389.171Q64683667846.158Q64683667846.159Q66522067074.155Q67528989526.158Q67528989526.159Q9843367298.154 00000n02R03A04V04j05X05l06@06D06a07507I07U07i08=08K08_08f09U09i0:=0:Q0:e0;90;M0;a0<90<M0<c0<o0=Z0=n0>B0>V0>j0?>0??0?I0?S0?g0@;0@O0@R0@f0A00AD0AR0Af0B:0BT0BX0BY0Bk0C=0CT0Cg0DP0E\0E]0F40F50FL0F_0GC0HJ0HK0H]0I40IF0I]0J10JC0JO0Ja0K80KL0KM0Kd0Ke0L<0LS0Le0Lf0MR0Na0O30OE0Ob0P?0P@0PR0Pd0Q80QO0Qa0R30RE0RW0RX0RY0S00S10SD0SE0T;0UT0Uk0VT0W`0X7S1R2LF2ra2sp1X3xs02lo4SLO23LFN5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R2LF2ra2sp2s01X3xs02lo4SLO23LFN5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1R3HIA1h2LF2ra2sp1X3xs03LFN3TOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s01X3xs03LFN3TOP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2LF2ra2sp1X3xs03LFNS3FRf1X2sX2nX2pX3xs04padX4ownX2dA2dB1d2D04FRd0S2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2spS1R2sp2lo3slo4SLO24SLOL5NEEDRS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2sp2dA2lo1HS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2sp2dA2lo3OA4S2LF2ra2sp1X3xs03LFNS2sp2loS4PHIf1X2sX2nX2pX3xs04padX4ownX2dA2dB3NRB5PHId0S2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS1R3HIA1h2sp2lo3TOP4HTOPS2LF2ra2sp1X3xs03LFNS1R2LF2ra2sp1X3xs03LFNS2sp2dB2lo1HS1R2LF2ra2sp1X3xs02lo4SLO23LFN5NEEDR2X03SPRS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNSS2nX2dA2dBS1X2X03X16S1R2sp2lo4SLO25NEEDRS2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS1ES2LF2ra2sp1X3xs03LFNS1R2lo3LOSS2LF2ra2sp1X3xs03LFNS2sp2dB2lo3OB4S2LF2ra2sp1X3xs03LFNS2LF2ra2sp1X3xs03LFNS2sp2r03SPA1q1r1H2H02q02H4S2spFS2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFN4LOSPS1R2LF3xs03LFN4IMG'S2LF2ra2sp3xs02lo3LFN4LOSP2HB5Ha_st5Hl_stS2LF2sp2s03xs02lo3LFN4LOSP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FS2LF2sp3xs02lo3LFN4LOSPFS2LF2sp3xs02lo3LFN4LOSPS1R2LF3xs03LFN4IMG'S2LF2ra2sp3xs02lo3LFN2HB5Ha_st5Hl_stS2LF2sp2s03xs02lo3LFN2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11FS2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFN4LOSPS2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFN4LOSPS1R2LF3xs03LFN5ALWF'S2LF2sp3xs02lo3LFNS2LF3xs03LFNS2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFN4LOSPS1R2LF3xs03LFN5ALWF'FS2LF2sp3xs02lo3LFN4LOSPFS2LF2sp3xs02lo3LFN4LOSPS2LF2sp3xs02lo3LFN4LOSPS2LF2sp3xs02lo3LFNFS1R2LF2ra2sp3xs03slo3LFN4SLOS2HB5Ha_st5Hl_stS1R2LF2sp2s03xs03slo3LFN4SLOS2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFNS2LF2sp3xs03LFN4SP642HB5Ha_stS2LF2sp3xs03LFN4SP642HB5Ha_stFS2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFNS1R2LF3xs03LFN5ALWF'S2LF2sp3xs02lo3LFN4LOSPS2LF2sp3xs03LFN2HBS2LF2sp3xs03LFN2HBS2LF2sp3xs02lo3LFNS2LF2sp3xs02lo3LFNFFS2LF2sp3xs02lo3LFN4LOSPFS1R2LF3xs03LFN4IMG'FS1R3HIA1h2LF2ra2sp3xs03slo3LFN3TOP4HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2s03xs03slo3LFN3TOP4HTOP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2LF2sp3xs02lo3LFN4LOSPS2LF2ra2sp3xs02lo3LFN4LOSP2HB5Ha_st5Hl_stS2LF2sp2s03xs02lo3LFN4LOSP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2LF2sp3xs02lo3LFN4LOSP". (* [comment removed for export] *)
  #[using="IMG HDIV HASN HADD JC TPV UWX UWB D0 SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"] Lemma md_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "Pt0,(19.&40.)Pt1,(19.&40.)Pt2,(19.&40.)Pa3,(19.&40.)Pa4,(19.&40.)Pa5,(19.&40.)Pa6,(19.&40.)Pa7,(19.&40.)Pt3,(19.&40.)Pt4,(19.&40.)Pt5,(19.&40.)Pt6,(19.&40.)P,(4?.$<.VR,VHIA,Vh,Vmo,)P,(4:.$<.Vm,VLB,VdA,)P,(4>.$<.Vm,Vlo,(2:.&40.Vsp,))P,(50.$<.Vm,)P,(4<.$<.(44.VR,)Vm,Vslo,(2:.&40.Vsp,))P,(4;.$<.(44.VR,)(45.$<.VR,VHIA,Vh,)Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(4;.$<.(44.VR,)(45.$<.VR,VHIA,Vh,)Vm,VdA,)P,(4;.$<.(44.VR,)(45.$<.VR,VHIA,Vh,)Vm,VdB,)(51.$<.$26.(52.(27.(28.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(29.&40.VX,)(29.&40.(37.VdA,))(29.&40.(37.VdB,))R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(29.&40.$53.)Vfc,(2;.(19.&40.))Vm,(2<.$<.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK MA0 ST MI SSH OXA OAA OBA. unfold A_MPI_MOD_MPI_E.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 104 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h. pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. pose proof OBA as [OBs OBl]. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 144%nat ST.
    (* [comment removed for export] *)
    do 14 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 40 ?jk :: _) =>
      change (rw_cells asegs m1 (bv_unsigned sp + -144) ([CB 40 jk] ++ MD_FRAME_A)) in FR end.
    apply rw_cells_app in FR. destruct FR as [SLOT FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp - 104) in FR by (clear; lia).
    lazymatch type of SLOT with rw_cells _ _ _ [CB 40 ?jk] => set (slot0 := jk) in SLOT end.
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp - 104)).
    { eapply stk_merge; [exact ST| | clear - SLO2 NEEDR LOSP; lia].
      replace (bv_unsigned sp - 104) with (bv_unsigned sp + -144 + Z.of_nat (cells_size [CB 40 slot0])) by (cbn; clear; lia).
      eapply stk_of_rw_cells. exact SLOT. }
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    (* [comment removed for export] *)
    assert (MA1 : mpd_at asegs m1 LB dA).
    { eapply mpd_at_munch_any; [exact MA0| exact MU| exact WM| cbn; split; [clear - OA4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OA5 ON); clear - H; lia| exact I]. }
    assert (MB1 : mpd_at asegs m1 LB dB).
    { eapply mpd_at_munch_any; [exact MB0| exact MU| exact WM| cbn; split; [clear - OB4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OB5 ON); clear - H; lia| exact I]. }
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    assert (OAl1 : md_own dA = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dA) (4 * md_n dA)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OAl E)]).
    assert (OBl1 : md_own dB = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dB) (4 * md_n dB)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OBl E)]).
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH1. cbn [app] in HH1.
    destruct (md_mkJB m1 OBs OBl1 HH1 MB1) as [DBJ B0].
    (* [comment removed for export] *)
    assert (SSH1 : sshad asegs AL m1 slo (bv_unsigned sp + -144)).
    { destruct (sshad_split asegs AL m1 slo (bv_unsigned sp + -144) (bv_unsigned sp) SSH ltac:(clear - SLOL SLO2 NEEDR; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia)) as [SSa _]. exact SSa. }
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH1) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. clear GOT GSB.
    destruct (md_viewB _ _ _ _ DBJ B0) as (CEB & BBY & LENB & SGB' & BBD & PBB & ALB & OBs1 & OBl1' & PBBB).
    pose proof (mpd_abs_lval dB LENB) as EVB.
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (ci_B AL IMG ALWF (hcs asegs R HIA h) CSOK) with (ys := md_limbs dB) (sg' := md_sg dB) (X := X) (xs := xs0);
        first [ exact CEB | exact BBY | exact LENB | exact NRB | exact SGB' | exact BBD | exact PBB | exact ALB | exact OBs1 | exact OBl1' | exact PBBB
              | (clear - X0 X16; lia) | match goal with |- ?g => idtac "MAIN-CUT-LEFT:" g end ]. }
    cbv beta. intros ms' PC. unfold ciB_post in PC. ddestruct PC as (b0 & b1 & b3 & b4 & b5 & pc & -> & CASES).
    rewrite <- EVB in CASES.
    destruct CASES as [(-> & BSG)|(-> & BNEG)].
    - eapply (md_DIV m1 slot0); [exact J0| exact DBJ| exact B0| exact MA1| exact MB1| split; [exact OAs| exact OAl1]| split; [exact OBs| exact OBl1]| exact SSH1| exact SLOT| exact ST| exact BSG].
    - (* [comment removed for export] *)
      zstep. zstep.
      eapply md_ret; [exact J0| intros E; exfalso; clear - E; lia| clear; lia| cbn [md_n]; unfold div_mpi_nz; clear; lia| clear - PHId0 NRB; lia|].
      unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge. clear - FRd0 D0. lia.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WMD.

(* [comment removed for export] *)
Definition mod_mpi_PHIg (PHIf : mpd -> mpd -> mpd -> Z) (dX dA dB : mpd) : Z := PHIf dX dA dB + (32 * md_n dB + 48).
Definition mod_mpi_FRg (FRf : mpd -> mpd -> mpd -> Z -> Z) (dX dA dB : mpd) (d : Z) : Z := FRf dX dA dB d + add_sub_FR d.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L23460287817.0L49264482736.500000100>SS1R2sp2lo3SLO". (* [comment removed for export] *)
Theorem A_mpi_mod_mpi_spec_g : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "PR,$54.PHIA,(55.$<.R1.)PPHIf,P,$1;.P,$1;.P,$1;.$4.PFRf,P,$1;.P,$1;.P,$1;.P,$4.$4.P,(56.(44.R4.))P,(57.$<.R5.R4.$58.R3.R2.)P,PdX,$1;.PdA,$1;.PdB,$1;.P,(5.(6.=(9.R2.))(6.(9.R2.)+2710.))P,(5.(6.=(9.R2.))(6.(9.R2.)+2710.))(6.=A3.R9.R5.R4.R3.)P,PdX,$1;.PdA,$1;.PdB,$1;.Pd,$4.P,(5.(6.=(9.R3.))(6.(9.R3.)+2710.))P,(6.=R2.)(6.=A4.R:.R6.R5.R4.R3.)P,Pflip,$4.P,(30.(0.$4.R1.+1.)(0.$4.R1.-1.))(59.R2.$<.R:.R9.$38.)P,(5:.+1.$<.R9.R8.$38.)P,(6.=(5;.R:.))P,Ph,(16.$<.R;.R:.)PLB,(17.$18.)PLF,(17.$18.)Pm,P,(19.&40.)(1:.(19.&8.))P,(49.$<.R?.R>.R4.R3.R2.R1.)(5<.$4.(5=.(5>.$4.$4.)$4.(5?.$4.$4.)R4.))P,(5.(6.(60.(61.R<.))(62.(61.R<.)))(6.(63.(61.R<.))(64.(61.R<.))))P,Pa,$4.P,(0.$:.(;.$<.(=.R1.))$10.)P,(5.(6.=R2.)(7.R2.(22.+2.+40.)))(5.(6.(60.(61.R10.))R3.)(7.R3.(64.(61.R10.))))(65.$<.R>.R=.$53.(66.R<.)(67.R;.))")
(* [comment removed for export] *).
Proof.
  intros R HIA PHIf FRf IMG HDIV PHI0 FR0 HASN HADD NEEDR HND DIMG ROIMG. unfold mpi_mod_mpi_stmtA, mod_mpi_PHIg, mod_mpi_FRg.
  intros until d. intros HH HK LFN MX MA MB SXA SXB SAB NST NEB OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO SLO3 SSH SLOS SLOL TOP SPA TPV MI RAE OXA OAA OBA IA2 IB2 BUD UW UWX UWB BUDF C24H -> -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 104 (MD_FRAME_A ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  pose proof MA as [(_ & _ & _ & _ & NRA & _) _]. pose proof MB as [(_ & _ & _ & _ & NRB & _) _]. unfold MPI_MAX_LIMBS in NRA, NRB.
  pose proof (uw_obj_nonneg _ _ _ _ UWX) as D0.
  eapply md_main with (slo := slo); try eassumption.
  all: try (apply PHI0; assumption). all: try (apply FR0; assumption).
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
