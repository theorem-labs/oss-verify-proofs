(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_lset P_mpi_free P_ecp_group_init P_ecp_group_free P_ecp_group_load.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_copy A_mpi_bitlen A_mpi_init A_mpi_lset A_mpi_free A_free_seq A_ecp_group_init A_ecp_group_free A_ecp_defs A_ecp_statics A_ecp_group_load_mxpre A_ecp_group_load_main.
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
Ltac2 gd_tbl_A_ecp_group_load_mx () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.curve_addrs"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.grp_mxi"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_P"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.cP"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_N"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.cN"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.mx_nbits"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_modp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.Spec.EcpLoad.mx_field"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.GF_PHI"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.GF_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.option"; "GLMX.mx_st"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_group_load_postA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.heap1"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.ecp_group_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.A_ECP_GROUP_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_init.ecp_group_init_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_init.A_ECP_GROUP_INIT"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset.mpi_lset_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_group_load_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_GROUP_LOAD_E"].


(* [comment removed for export] *)
Lemma grp_mxi_heapA : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "Pid,$0.Pca,$1.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PdA,$3.PdX,$3.PdZ,$3.Pd,$3.P,(4.$3.R1.(5.(6.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)))P,(7.$8.(9.R2.)$:.)(;.(7.$3.R3.R6.)(;.(7.$3.R3.R5.)(7.$3.R3.R4.)))")
(* [comment removed for export] *).
Proof.
  intros until d. intros Hd O. unfold grp_mpds, grp_mxi, pt_mpds in Hd. cbn -[smpd mpd_init] in Hd. unfold smpd, mpd_init in Hd.
  destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O; try discriminate O; auto.
Qed.

Lemma grp_mxi_apartA : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "Pid,$0.Pca,$1.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PdA,$3.PdX,$3.PdZ,$3.P,P,(7.$8.(9.R3.)$:.)P,(7.$8.(9.R3.)$:.)(<.(7.$0.(=.R5.)(=.R4.)))P,P,(7.$8.(9.R4.)$:.)P,(7.$8.(9.R3.)$:.)(<.(7.$0.(=.R6.)(=.R4.)))P,P,(7.$8.(9.R4.)$:.)P,(7.$8.(9.R4.)$:.)(<.(7.$0.(=.R6.)(=.R5.)))(>.(5.(6.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)))")
(* [comment removed for export] *).
Proof.
  intros until dZ. intros NAX NAZ NXZ d1 d2 H1 H2 NE O1 O2.
  destruct (grp_mxi_heapA _ _ _ _ _ _ _ _ _ _ _ _ _ H1 O1) as [->|[->| ->]];
  destruct (grp_mxi_heapA _ _ _ _ _ _ _ _ _ _ _ _ _ H2 O2) as [->|[->| ->]]; try (exfalso; apply NE; reflexivity); auto using not_eq_sym.
Qed.

Lemma grp_mxi_blocks : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "Pid,$0.Pca,$1.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PdA,$3.PdX,$3.PdZ,$3.(7.(?.$10.)(11.(6.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(12.$10.(13.R3.)(12.$10.(13.R2.)(13.R1.))))")
(* [comment removed for export] *).
Proof. intros. unfold grp_blocks, grp_mpds, grp_mxi, pt_mpds. cbn -[mpd_blk]. unfold mpd_blk at 1 3 5 7. cbn. rewrite app_nil_r. reflexivity. Qed.

Section GLMX.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis GF : ecp_group_free_stmtA asegs R HIA A_MT A_ECP_GROUP_FREE.
  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis MFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.

  (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model).
  Variables (A : Z) (g : ecp_grp) (id lo d : Z).
  Local Notation LBf := (grp_free_LB g LB).
  Hypothesis IDC : id = 9 \/ id = 13.
  Hypothesis AL8 : A mod 8 = 0.
  Hypothesis POS : 0 < A.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - ECP_GROUP_LOAD_STACK_A - arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS : A + 192 <= lo \/ bv_unsigned sp <= A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis CRA : crange (hcs asegs R HIA h) A 192.
  Hypothesis CWA : client_wrange L (LBf ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) A 192.
  Hypothesis UWO : uw_obj R A 192 d.
  Hypothesis BUD : havol asegs R HIA h + group_load_PHI <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + group_load_FRn d <= FR_MAX.

  Local Notation POST := (ecp_group_load_postA asegs R HIA A_MT A_CA A_ONE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF A g id lo d m mo).

  (* [comment removed for export] *)
  Definition mx_st (hk : HST asegs R HIA) (LBk : list blk) (nl : Z) (idpad pP pB pY pN hpad : word) (dA dX dZ : mpd) (mk : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "Zca,$1.(14.Vid,)ZNBk,(?.$10.)(12.$10.(13.O4.)(12.$10.(13.O3.)(13.O2.)))(15.(16.$17.VR,VHIA,O=.O<.VLF,O1.)(15.Pb,$10.(18.(4.$10.R1.O<.)(;.(4.$10.R1.R2.)(4.$10.R1.(19.Vg,VLB,))))(15.Pb,$10.P,(4.$10.R1.R2.)(15.(<.(4.$10.R2.(19.Vg,VLB,)))(1:.VR,(19.Vg,VLB,)VLF,(1;.$0.$0.R2.)(1<.$0.$0.R2.)))(15.(15.P,(7.$8.(9.O4.)$:.)P,(7.$8.(9.O3.)$:.)(<.(7.$0.(=.O4.)(=.O3.)))(15.P,(7.$8.(9.O4.)$:.)P,(7.$8.(9.O2.)$:.)(<.(7.$0.(=.O4.)(=.O2.)))P,(7.$8.(9.O3.)$:.)P,(7.$8.(9.O2.)$:.)(<.(7.$0.(=.O3.)(=.O2.)))))(15.(15.(1=.$17.O1.VA,(1>.$1?.(20.(21.&40.Vid,))(1>.$1?.(20.O:.)(22.$1?.))))(15.(1=.$17.O1.(23.VA,+8.)(24.(25.R2.)(21.&40.+1.)(26.(27.(2.&40.)(28.Vid,)))O9.))(15.(1=.$17.O1.(23.VA,+28.)(24.=(21.&40.+1.)=O8.))(15.(1=.$17.O1.(23.VA,+48.)(24.=(21.&40.+1.)=O7.))(15.(1=.$17.O1.(23.VA,+68.)(24.(29.R2.)(21.&40.+1.)(26.(27.(2.&40.)(2:.Vid,)))O6.))(1=.$17.O1.(23.VA,+78.)(1>.$1?.(2;.(21.&40.(2<.(28.Vid,)(26.(27.(2.&40.)(28.Vid,))))))(1>.$1?.(2;.(21.&40.(2=.Vid,)))(1>.$1?.(20.(21.&40.+2.))(1>.$1?.(20.O5.)(1>.$1?.(2;.(21.&40.(2>.R2.)))(1>.$1?.(2;.(21.&40.=))(1>.$1?.(2;.(21.&40.=))(1>.$1?.(2;.(21.&40.=))(1>.$1?.(2;.(21.&40.=))(1>.$1?.(2;.(21.&40.=))(22.$1?.)))))))))))))))))(15.(15.(2?.$17.O1.O<.O4.)(30.(23.VA,+18.)O4.))(15.(15.(2?.$17.O1.O<.O3.)(30.(23.VA,+38.)O3.))(15.(15.(2?.$17.O1.O<.O2.)(30.(23.VA,+58.)O2.))(15.(1=.$17.O1.(23.(31.&40.Vsp,)-20.)(1>.$1?.(2;.Vs2,)(1>.$1?.(2;.Vs1,)(1>.$1?.(2;.Vs0,)(1>.$1?.(2;.Vra,)(22.$1?.))))))(15.(32.$17.O1.Vlo,(23.(31.&40.Vsp,)-20.))(15.(33.$17.O1.)(15.(34.$17.(35.VR,)(36.$17.VR,VHIA,O=.)O1.VA,+<0.)(15.(37.$17.VR,VHIA,Vh,(19.Vg,VLB,)VLF,(31.&40.Vsp,)(38.VR,)(1>.(39.$0.$0.)(3:.$0.$0.VA,(23.VA,+<0.))(22.(39.$0.$0.)))Vm,O1.)(15.(7.$0.(3;.$17.VR,VHIA,O=.)(3;.$17.VR,VHIA,Vh,))(15.(7.$0.(3<.$17.VR,VHIA,O=.)(3<.$17.VR,VHIA,Vh,))(15.(7.$0.(3=.$17.VR,VHIA,O=.)(3=.$17.VR,VHIA,Vh,))(15.Px,$0.P,(36.$17.VR,VHIA,Vh,R1.)(36.$17.VR,VHIA,O=.R2.)(15.(3>.(3?.$17.VR,VHIA,O=.)(23.(23.(3?.$17.VR,VHIA,Vh,)$40.)(41.O;.(42.+1.))))(3>.(43.$17.VR,VHIA,O=.)(23.(23.(43.$17.VR,VHIA,Vh,)(44.Vd,))(41.O;.+3.)))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="NEEDR DIMG HMND GF IDC AL8 POS LOS SLO TOP SPA DS TPV CWA UWO BUD BUDF"] Lemma mx_fail : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "Phk,(45.$17.VR,VHIA,)PLBk,(?.$10.)Pnl,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PdA,$3.PdX,$3.PdZ,$3.Pmk,P,(2.&40.)(46.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pxs1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pxs2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pr,$0.P,(47.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)P,(15.(3>.=R1>.)(3>.R1>.+3.))P,(7.$0.R3.$48.)(49.$17.(4:.$17.VR,VHIA,R22.Vmo,)(4;.$17.VR,VHIA,$4<.$14.$4=.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VA,Vg,Vid,Vlo,Vd,Vm,Vmo,)(4>.(4?.R15.(21.&40.(23.(31.&40.Vsp,)-20.))Vgp,Vtp,R14.R13.R12.(21.&40.VA,)R11.(21.&40.R4.)R10.R?.R>.R=.R<.R;.R:.R9.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(21.&40.+=3158.)Vfc,(50.(2.&40.))R16.(51.$17.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros STT NL Er. unfold mx_st in STT. cbv zeta in STT.
    ddestruct STT as (HH & IFF & FRESH & (NAX & NAZ & NXZ) & (HD & HP & HB & HY & HN & HT) & (MA & FA) & (MX & FX) & (MZ & FZ) & FR & ST & MI & OA & PXA
                     & HT2 & HS2 & HF2 & HCS2 & HV2 & HFR2).
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA hk _ _ _ HH) as HTOPk. rewrite HT2, HS2 in HTOPk.
    destruct (hm_apart asegs R HIA hk LBk LF mk HH) as [HBR HAP]. change (blkfacts L (LBk ++ LF)) in HBR.
    pose proof (HMND _ _ _ _ HH) as NDc.
    pose proof (hcs_ok asegs R HIA hk) as CSOK.
    assert (SCS : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCS2|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. clear - TOP HTOPk. lia. }
    set (gc := grp_mxi id (A_CA id) A idpad pP pB pY pN hpad dA dX dZ) in *.
    assert (MPB : 0 <= ca_modp (A_CA id) < 2^64 /\ In (ca_modp (A_CA id), (ca_P (A_CA id), cP id)) A_MT).
    { destruct IDC as [-> | ->]; cbn -[c9_P c13_P]; (split; [clear; lia| auto 20]). }
    destruct MPB as [MB MODP].
    assert (G : ecp_group_at asegs A_MT mk LBk A gc).
    { eapply grp_mxi_at; first [exact IDC| exact MODP| exact MB| exact HD| exact AL8| exact POS| exact HP| exact HB| exact HY| exact HN| exact HT
                               | exact MA| exact MX| exact MZ| exact FA| exact FX| exact FZ
                               | exact (A_curve_statics mk id MI ltac:(clear - IDC; lia)) ]. }
    assert (DISc : mpds_apart (grp_mpds gc)) by (apply grp_mxi_apartA; assumption).
    assert (BLKc : grp_blocks gc = mpd_blk dA ++ mpd_blk dX ++ mpd_blk dZ) by apply grp_mxi_blocks.
    (* [comment removed for export] *)
    assert (HEAPIN : forall dd, In dd (grp_mpds gc) -> md_own dd = LHeap -> In (md_p dd, 4 * md_n dd) LBk).
    { intros dd Hd O. destruct (grp_mxi_heapA _ _ _ _ _ _ _ _ _ _ _ _ _ Hd O) as [->|[->| ->]];
        [destruct (mpdr_blk_factsA asegs L _ _ _ _ MA O HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (I1 & _)
        |destruct (mpdr_blk_factsA asegs L _ _ _ _ MX O HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (I1 & _)
        |destruct (mpdr_blk_factsA asegs L _ _ _ _ MZ O HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (I1 & _)]; exact I1. }
    assert (KEEPf : forall b, In b LBf -> In b (grp_free_LB gc LBk)).
    { intros [B k] Hb. unfold grp_free_LB. apply lb_free_mpds_keep; [apply (proj2 (IFF _)); right; exact Hb|].
      intros dd Hd O E. subst B.
      assert (GINd : In dd (grp_mpds gc)).
      { unfold grp_free_mpds in Hd. unfold grp_mpds. destruct (g_h gc =? 1); [destruct Hd|]. destruct (g_h gc =? 2); cbn -[gc] in Hd |- *; clear - Hd; tauto. }
      pose proof (HEAPIN dd GINd O) as INc.
      assert (INb : In (md_p dd, k) LBk) by (apply (proj2 (IFF _)); right; exact Hb).
      assert (k = 4 * md_n dd).
      { clear - NDc INc INb. induction LBk as [|[C j] LBc IH]; [destruct INc|]. cbn in NDc. apply List.NoDup_cons_iff in NDc as [Hni ND'].
        destruct INc as [E1|INc]; destruct INb as [E2|INb].
        - congruence.
        - injection E1; intros; subst. exfalso. apply Hni. apply in_map_iff. exists (md_p dd, k). auto.
        - injection E2; intros; subst. exfalso. apply Hni. apply in_map_iff. exists (md_p dd, 4 * md_n dd). auto.
        - apply IH; assumption. }
      subst k.
      assert (INN : In (md_p dd, 4 * md_n dd) (mpd_blk dA ++ mpd_blk dX ++ mpd_blk dZ)).
      { rewrite <- BLKc. unfold grp_blocks. apply in_flat_map. exists dd. split; [exact GINd|]. unfold mpd_blk. rewrite O. left. reflexivity. }
      exact (proj1 (FRESH _ INN) Hb). }
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof GF as SG. unfold ecp_group_free_stmtA, A_ECP_GROUP_FREE, ECP_GROUP_SIZE in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG with (h := hk) (LB := LBk) (LF := LF) (A := A) (g := gc) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia);
        first [ exact HK1 | exact G | exact DISc | exact LOS | exact TPV | exact UWO | exact HH | exact OA | exact ST | exact MI | reflexivity
              | lazymatch goal with
                | |- client_wrange _ _ _ _ A 192 => rewrite HT2; eapply (client_wrange_weak L); [exact CWA| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply KEEPf; exact Hb| right; exact Hb]| clear; lia| clear; lia| clear; lia]
                | |- A + 192 <= lo \/ _ => clear - DS; lia
                | |- lo <= _ => clear - SLO NEEDR NER; lia
                | |- _ <= htop _ _ _ _ => rewrite HT2; clear - TOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold group_load_PHI in BUD; unfold GF_PHI, grow_PHI in *; unfold AVOL_CALL in *; clear - BUD HV2 NL; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold group_load_FRn, calls_FR in BUDF; unfold GF_FR, fr_charge in *; clear - BUDF HFR2 D0 NL; lia
                end
              | match goal with |- ?gg => idtac "GF-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXg & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & GZ & GZC).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, PXg by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia).
    unfold ECP_GROUP_SIZE in PXg.
    replace (ret_pc (Z_to_bv 64 0xd3164)) with (Z_to_bv 64 0xd3164 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (CRS : client_range L (grp_free_LB gc LBk ++ fdata LF) (bv_unsigned sp + -32) A 192).
    { eapply (client_range_of_wrange L); [exact CWA| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply KEEPf; exact Hb| right; exact Hb]| clear; lia| clear; lia| clear; lia]. }
    pose proof (presA_rw_cells asegs R _ _ _ _ _ _ mk m2 _ _ PXg FR ltac:(apply client_range_stack; cbn; clear; lia) ltac:(cbn; clear - DS SLO NEEDR NER; lia)) as FR2.
    assert (PXA2 : presW asegs R HIA h LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m2).
    { eapply presW_call; [exact PXA| exact PXg| exact KEEPf| intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia|].
      intros x Hx. exact Hx. }
    assert (OBJ2 : aobj asegs AL (hcs asegs R HIA hk) m2 A 192).
    { eapply (presA_aobj asegs R (hcs asegs R HIA hk)); [exact CSOK| exact PXg| exact OA| exact CRS| clear - LOS SLO NEEDR NER; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    clear PXA PXg G SG FR ST MI HH OA LAWS KINV MU WM.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (hcs_ok asegs R HIA h2) as CSOKc.
    pose proof (crange_mono _ _ _ _ HCS3 SCS) as SCSc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS3 OBJ2) as OBJc.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    do 7 zstep.
    lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp); rename STx into STf end.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold ecp_group_load_postA, ECP_GROUP_SIZE.
    deexists 14. dexists m9, mo9, h2, r, (grp_zero A), ([] : list blk), (grp_free_LB gc LBk).
    split; [reflexivity|]. split; [assumption|]. split; [exact STf|]. split; [exact MF9|].
    split; [lazymatch goal with PXx : presW _ _ _ h LBf LF _ _ _ m m9 |- _ => exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ PXx) end|].
    split; [rewrite HT3; exact HT2|]. split; [rewrite HS3; exact HS2|]. split; [rewrite HF3; exact HF2|]. split; [exact HK9|].
    split; [intros x Hx; apply HCS3, HCS2, Hx|].
    split; [unfold group_load_PHI, GF_PHI in *; unfold grow_PHI in *; unfold AVOL_CALL in *; clear - HV2 HV3 NL; lia|].
    split; [unfold group_load_FRn, GF_FR, calls_FR, fr_charge in *; clear - HFR2 HFR3 D0 NL; lia|].
    split; [assumption|].
    split. { intros b. split; [| intros [[]|Hb]; apply KEEPf; exact Hb]. intros Hb. right.
             assert (INc : In b LBk) by (unfold grp_free_LB in Hb; eapply lb_free_mpds_sub; exact Hb).
             destruct (proj1 (IFF b) INc) as [Hg|Hf]; [| exact Hf]. exfalso.
             rewrite <- BLKc in Hg. unfold grp_blocks in Hg. apply in_flat_map in Hg. ddestruct Hg as (dd & Hd & Hbd).
             unfold mpd_blk in Hbd. destruct (md_own dd) eqn:O; try (destruct Hbd; fail). destruct Hbd as [<-|[]].
             unfold grp_free_LB in Hb. eapply (lb_free_mpds_notin _ LBk dd); [exact NDc| | exact O| exact Hb].
             destruct (grp_mxi_heapA _ _ _ _ _ _ _ _ _ _ _ _ _ Hd O) as [->|[->| ->]]; unfold grp_free_mpds, gc, grp_mxi, pt_mpds; cbn -[mpd_init]; tauto. }
    split; [intros b Hb; destruct Hb|].
    split; [assumption|].
    split. { intros d1 d2 H1 H2 NE O1 O2. exfalso. unfold grp_mpds, grp_zero, pt_mpds, pt_zero in H1. cbn -[mpd_zero] in H1. unfold mpd_zero in H1.
             destruct H1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O1; discriminate O1. }
    split; [reflexivity|].
    split. { right. right. right. auto. }
    assumption.
    all: match goal with |- ?gg => idtac "FAIL-LEFT:" gg end.
  Qed.

  (* [comment removed for export] *)
  #[using="NEEDR DIMG HLSET POS LOS SLO TOP SPA DS TPV CWA UWO BUD BUDF"] Lemma mx_lset : forall (k X0 : Z) (hk : HST asegs R HIA) (LBk : list blk) (nl : Z) (idpad pP pB pY pN hpad : word) (dA dX dZ : mpd) (pad : word) (mk : mem)
      (RET v : Z) (t0 t1 t2 xs1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 : word),
    mx_st hk LBk nl idpad pP pB pY pN hpad dA dX dZ mk -> 0 <= nl <= 2 -> X0 = A + 24 + 32 * k ->
    ((k = 0 /\ dA = mpd_init (A + 24) pad) \/ (k = 1 /\ dX = mpd_init (A + 56) pad) \/ (k = 2 /\ dZ = mpd_init (A + 88) pad)) ->
    0 <= v < 2^31 -> 0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall (hk' : HST asegs R HIA) (LBk' : list blk) (dN : mpd) (mk' : mem) (r : Z) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : word),
        mx_st hk' LBk' (nl + 1) idpad pP pB pY pN hpad (if k =? 0 then dN else dA) (if k =? 1 then dN else dX) (if k =? 2 then dN else dZ) mk' ->
        ((r = 0 /\ exists P w, dN = heap1 X0 P w pad) \/ (r = MBEDTLS_ERR_MPI_ALLOC_FAILED /\ dN = mpd_init X0 pad)) ->
        aevtA asegs (KF asegs R HIA hk' mo) POST
          (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y0 y1 y2 (Z_to_bv 64 A) xs1 (Z_to_bv 64 r) y3 y4 y5 y6 y7 y8 y9
                   xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y10 y11 y12 y13)
              F (Z_to_bv 64 RET) fc None mk' (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hk mo) POST
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) xs1 (Z_to_bv 64 X0) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
               xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_MPI_LSET) fc None mk (seg_rom asegs)).
  Proof.
    intros until t6. intros STT NL EX0 SEL Vr RETr RETe CONT. unfold mx_st in STT. cbv zeta in STT.
    ddestruct STT as (HH & IFF & FRESH & (NAX & NAZ & NXZ) & (HD & HP & HB & HY & HN & HT) & (MA & FA) & (MX & FX) & (MZ & FZ) & FR & ST & MI & OA & PXA
                     & HT2 & HS2 & HF2 & HCS2 & HV2 & HFR2).
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA hk _ _ _ HH) as HTOPk. rewrite HT2, HS2 in HTOPk.
    destruct (hm_apart asegs R HIA hk LBk LF mk HH) as [HBR HAP]. change (blkfacts L (LBk ++ LF)) in HBR.
    pose proof (hcs_ok asegs R HIA hk) as CSOK.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    assert (K02 : k = 0 \/ k = 1 \/ k = 2) by (clear - SEL; destruct SEL as [[-> _]|[[-> _]|[-> _]]]; lia).
    assert (MT0 : mpdr_at asegs mk LBk (mpd_init X0 pad)).
    { rewrite EX0. destruct SEL as [[-> ->]|[[-> ->]|[-> ->]]];
        [replace (A + 24 + 32 * 0) with (A + 24) by (clear; lia); exact MA| replace (A + 24 + 32 * 1) with (A + 56) by (clear; lia); exact MX
        | replace (A + 24 + 32 * 2) with (A + 88) by (clear; lia); exact MZ]. }
    assert (SUBk : forall b, In b LBf -> In b LBk) by (intros b Hb; apply (proj2 (IFF b)); right; exact Hb).
    assert (SUBkk : forall b, In b (LBf ++ fdata LF) -> In b (LBk ++ fdata LF)).
    { intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBk; exact Hb| right; exact Hb]. }
    (* [comment removed for export] *)
    pose proof HLSET as SL. unfold mpi_lset_stmtA, mpi_xop_stmtA in SL.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SL with (h := hk) (LB := LBk) (LF := LF) (dX := mpd_init X0 pad) (v := v) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia);
        cbn [md_own md_addr md_p md_n mpd_init];
        first [ exact HK1 | exact HH | exact LOS | exact TPV | exact ST | exact MI | reflexivity
              | lazymatch goal with
                | |- mpd_at _ _ _ _ => apply mpd_of_mpdr; [exact MT0| left; reflexivity]
                | |- LNull <> LStatic => discriminate
                | |- - 2 ^ 31 <= v < 2 ^ 31 => clear - Vr; lia
                | |- mpd_writableA _ _ _ _ _ _ => split; cbn [md_own md_addr md_p md_n mpd_init]; [rewrite HT2; eapply (client_wrange_weak L); [exact CWA| exact SUBkk| clear; lia| clear - EX0 K02; lia| clear - EX0 K02; lia]| intros C; discriminate C]
                | |- LNull <> LNull -> _ => intros C; exfalso; apply C; reflexivity
                | |- lo <= _ => clear - SLO NEEDR NER; lia
                | |- _ <= htop _ _ _ _ => rewrite HT2; clear - TOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 RET) mod 2 = 0 => rewrite unsigned_lit by (clear - RETr; lia); exact RETe
                | |- mpd_aobjA _ _ _ _ _ => split; cbn [md_own md_addr md_p md_n mpd_init]; [eapply aobj_sub; [exact OA| clear - EX0 K02; lia| clear - EX0 K02; lia]| intros C; discriminate C]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold group_load_PHI in BUD; unfold GF_PHI, grow_PHI in *; unfold AVOL_CALL in *; clear - BUD HV2 NL; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite (unsigned_lit A) by (clear - POS TB; lia); eapply (uw_obj_uwc asegs R); [exact UWO| clear; lia]
                | |- uw_obj _ _ _ _ => eapply uw_obj_sub; [exact UWO| clear - EX0 K02; lia| clear - EX0 K02; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => rewrite lset_FR_val; unfold group_load_FRn, calls_FR in BUDF; unfold GF_FR, fr_charge in *; clear - BUDF HFR2 D0 NL; lia
                end
              | match goal with |- ?gg => idtac "LSET-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & mo2 & h2 & LB2 & dN & r & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & MN2 & OUT & FRA & LR).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, PXl by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia).
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    unfold mpd_keep in PXl, FRA. cbn [md_own md_addr md_p md_n mpd_init mpd_blk] in PXl, FRA, OUT.
    ddestruct OUT as (EN & ON & OUT1 & OUT2 & OUT3). cbn [md_own md_addr md_p md_n mpd_init mpd_blk] in EN, OUT1, OUT2, OUT3.
    ddestruct LR as (LR & _ & FRN). cbn [md_own md_addr md_p md_n mpd_init mpd_blk] in LR, FRN.
    assert (SUB2 : forall b, In b LBk -> In b LB2) by (intros b Hb; apply OUT2; [exact Hb| intros []]).
    (* [comment removed for export] *)
    assert (RES : (r = 0 /\ exists P w, dN = heap1 X0 P w pad) \/ (r = MBEDTLS_ERR_MPI_ALLOC_FAILED /\ dN = mpd_init X0 pad)).
    { destruct LR as [(Er & Zn & Zo & Zl & Zs & Zpd) | [Er EdN]]; [left| right; split; assumption].
      split; [exact Er|]. replace (if v <? 0 then -1 else 1) with 1 in Zs by (destruct (Z.ltb_spec v 0); [clear - Vr H; lia| reflexivity]).
      destruct (lset_heap1 dN X0 Zn Zo Zl Zs EN) as [w EdN]. dexists (md_p dN), w. rewrite Zpd in EdN. exact EdN. }
    assert (FN : mx_field X0 dN).
    { destruct RES as [(_ & P & w & ->)|[_ ->]]; [apply mx_field_heap1| apply mx_field_init]. }
    assert (G1 : forall b, In b LB2 <-> In b (mpd_blk dN) \/ In b LBk).
    { intros b. split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hc]; [right; exact Hc| left; exact Hc]|].
      intros [Hb|Hb]; [| apply SUB2; exact Hb]. pose proof MN2 as [(_ & _ & _ & _ & _ & HO) _]. unfold mpd_blk in Hb. destruct (md_own dN); try (destruct Hb; fail).
      destruct Hb as [<-|[]]. exact (proj1 (proj2 HO)). }
    assert (G2 : forall b, In b (mpd_blk dN) -> ~ In b LBk /\ fresh_apart R LBf LF (fst b) (snd b)).
    { intros b Hb. destruct (FRN b Hb) as [[]|NI]. split; [exact NI|]. destruct (FRA b Hb) as [[]|(F0 & F1 & F2 & F3)].
      split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. intros B j Hj. apply F3. apply SUBkk. exact Hj. }
    (* [comment removed for export] *)
    assert (CRk : forall a n, A <= a -> a + n <= A + 192 -> client_range L (LBk ++ fdata LF) (bv_unsigned sp + -32) a n).
    { intros a n H1 H2. eapply (client_range_of_wrange L); [exact CWA| exact SUBkk| clear; lia| exact H1| exact H2]. }
    assert (KEEP : forall o dd, mpdr_at asegs mk LBk dd -> mx_field (A + o) dd -> (dd = dA \/ dd = dX \/ dd = dZ) -> 0 <= o -> o + 16 <= 192 ->
                   (A + o + 16 <= X0 \/ X0 + 16 <= A + o) -> mpdr_at asegs m2 LB2 dd).
    { intros o dd Md Fd WH O1 O2 OD. pose proof Fd as [Ed _].
      eapply (mpdr_at_presA asegs L mk m2 LBk LB2 (LBk ++ fdata LF)); [exact Md| exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXl)| exact MI| exact MI2| | |].
      - rewrite Ed. apply CRk; [clear - O1; lia| clear - O2; lia].
      - rewrite Ed. cbn [disjoint_from]. split; [clear - OD; lia| exact I].
      - intros O. destruct (mpdr_blk_factsA asegs L _ _ _ _ Md O HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (I1 & I2 & I3 & I4 & I5).
        split; [apply SUB2; exact I1|]. split; [eapply client_range_block; [apply in_app_iff; left; exact I1| clear; lia| clear; lia]|].
        cbn [disjoint_from]. split; [| exact I].
        assert (CWx : client_wrange L (LBf ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X0 16) by (eapply (client_wrange_weak L); [exact CWA| intros b Hb; exact Hb| clear; lia| clear - EX0 K02; lia| clear - EX0 K02; lia]).
        assert (INN : In (md_p dd, 4 * md_n dd) (mpd_blk dA ++ mpd_blk dX ++ mpd_blk dZ)).
        { assert (Hb : In (md_p dd, 4 * md_n dd) (mpd_blk dd)) by (unfold mpd_blk; rewrite O; left; reflexivity).
          rewrite !in_app_iff. clear - Hb WH. destruct WH as [<-|[<-| <-]]; auto. }
        pose proof (proj1 (FRESH _ INN)) as NIf.
        destruct (client_apart_blockA L LBf LBk LF (bv_unsigned sp) (htop asegs R HIA h) X0 16 (md_p dd) (4 * md_n dd) CWx SUBk HBR HAP I1 NIf ltac:(clear - I2; lia) ltac:(clear; lia)
                    ltac:(clear - ALO LOS SLO NEEDR NER; lia) (proj1 DIMG) (proj2 DIMG)) as [Q|Q]; clear - Q; lia. }
    assert (TRC : forall a cs, rw_cells asegs mk a cs -> A <= a -> a + Z.of_nat (cells_size cs) <= A + 192 ->
                    (a + Z.of_nat (cells_size cs) <= X0 \/ X0 + 16 <= a) -> rw_cells asegs m2 a cs).
    { intros a cs Hc H1 H2 H3. eapply (presA_rw_cells asegs R); [exact PXl| exact Hc| apply CRk; [exact H1| exact H2]| cbn [disjoint_from]; split; [exact H3| exact I]]. }
    pose proof (TRC _ _ HD ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear - EX0 K02; lia)) as HD2.
    pose proof (TRC _ _ HP ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear - EX0 K02; lia)) as HP2.
    pose proof (TRC _ _ HB ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear - EX0 K02; lia)) as HB2.
    pose proof (TRC _ _ HY ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear - EX0 K02; lia)) as HY2.
    pose proof (TRC _ _ HN ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear - EX0 K02; lia)) as HN2.
    pose proof (TRC _ _ HT ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear - EX0 K02; lia)) as HTc2.
    pose proof (presA_rw_cells asegs R _ _ _ _ _ _ mk m2 _ _ PXl FR ltac:(apply client_range_stack; cbn; clear; lia) ltac:(cbn; clear - DS SLO NEEDR NER EX0 K02; lia)) as FR2.
    assert (PXA2 : presW asegs R HIA h LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m2).
    { eapply presW_call; [exact PXA| exact PXl| exact SUBk| intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia|].
      intros x Hx. cbn [outside] in Hx |- *. clear - Hx EX0 K02. lia. }
    assert (OBJ2 : aobj asegs AL (hcs asegs R HIA h2) m2 A 192).
    { eapply aobj_cs_mono; [exact HCS3|].
      eapply (presA_aobj asegs R (hcs asegs R HIA hk)); [exact CSOK| exact PXl| exact OA| apply CRk; clear; lia| clear - LOS SLO NEEDR NER; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    assert (FRN' : forall b, In b (mpd_blk dN) -> ~ In b LBf /\ fresh_apart R LBf LF (fst b) (snd b)).
    { intros b Hb. destruct (G2 b Hb) as [NI FRb]. split; [intros C; apply NI, SUBk, C| exact FRb]. }
    assert (APN : forall o dd, (dd = dA \/ dd = dX \/ dd = dZ) -> mpdr_at asegs mk LBk dd -> mx_field (A + o) dd -> md_own dd = LHeap -> md_own dN = LHeap -> md_p dd <> md_p dN).
    { intros o dd WH Md Fd O1 O2 EP.
      destruct (mpdr_blk_factsA asegs L _ _ _ _ Md O1 HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (I1 & _).
      assert (N1 : md_n dd = 1) by (ddestruct Fd as [_ [[pd ->]|(P & w & pd & ->)]]; [discriminate O1| reflexivity]).
      assert (N2 : md_n dN = 1) by (ddestruct FN as [_ [[pd ->]|(P & w & pd & ->)]]; [discriminate O2| reflexivity]).
      apply (proj1 (G2 (md_p dN, 4 * md_n dN) ltac:(unfold mpd_blk; rewrite O2; left; reflexivity))). rewrite <- EP, N2, <- N1. exact I1. }
    pose proof (mpdr_of_mpd asegs _ _ _ MN2) as MNr.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply (CONT h2 LB2 dN m2 r); [| exact RES].
    unfold mx_st. cbv zeta.
    split; [exact HH2|].
    split. { intros b. rewrite (G1 b), (IFF b), !in_app_iff. clear - SEL. destruct SEL as [[-> ->]|[[-> ->]|[-> ->]]]; cbn [Z.eqb mpd_blk md_own mpd_init In]; tauto. }
    split. { intros b Hb. rewrite !in_app_iff in Hb.
             assert (C : In b (mpd_blk dN) \/ In b (mpd_blk dA ++ mpd_blk dX ++ mpd_blk dZ)).
             { rewrite !in_app_iff. clear - SEL Hb. destruct SEL as [[-> ->]|[[-> ->]|[-> ->]]]; cbn [Z.eqb mpd_blk md_own mpd_init In] in *; tauto. }
             destruct C as [C|C]; [apply FRN'; exact C| apply FRESH; exact C]. }
    split. { destruct SEL as [[-> ->]|[[-> ->]|[-> ->]]]; cbn [Z.eqb].
             - split; [intros O1 O2; apply not_eq_sym; eapply (APN 56 dX); auto| split; [intros O1 O2; apply not_eq_sym; eapply (APN 88 dZ); auto| exact NXZ]].
             - split; [intros O1 O2; eapply (APN 24 dA); auto| split; [exact NAZ| intros O1 O2; apply not_eq_sym; eapply (APN 88 dZ); auto]].
             - split; [exact NAX| split; [intros O1 O2; eapply (APN 24 dA); auto| intros O1 O2; eapply (APN 56 dX); auto]]. }
    split; [repeat (split; [assumption|]); assumption|].
    assert (KA : k <> 0 -> mpdr_at asegs m2 LB2 dA) by (intros NE; eapply (KEEP 24 dA); [exact MA| exact FA| auto| clear; lia| clear; lia| clear - EX0 K02 NE; lia]).
    assert (KX : k <> 1 -> mpdr_at asegs m2 LB2 dX) by (intros NE; eapply (KEEP 56 dX); [exact MX| exact FX| auto| clear; lia| clear; lia| clear - EX0 K02 NE; lia]).
    assert (KZ : k <> 2 -> mpdr_at asegs m2 LB2 dZ) by (intros NE; eapply (KEEP 88 dZ); [exact MZ| exact FZ| auto| clear; lia| clear; lia| clear - EX0 K02 NE; lia]).
    split. { destruct (Z.eqb_spec k 0) as [E0|NE]; [split; [exact MNr| replace (A + 24) with X0 by (clear - EX0 E0; lia); exact FN]| split; [exact (KA NE)| exact FA]]. }
    split. { destruct (Z.eqb_spec k 1) as [E0|NE]; [split; [exact MNr| replace (A + 56) with X0 by (clear - EX0 E0; lia); exact FN]| split; [exact (KX NE)| exact FX]]. }
    split. { destruct (Z.eqb_spec k 2) as [E0|NE]; [split; [exact MNr| replace (A + 88) with X0 by (clear - EX0 E0; lia); exact FN]| split; [exact (KZ NE)| exact FZ]]. }
    split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact OBJ2|]. split; [exact PXA2|].
    split; [rewrite HT3; exact HT2|]. split; [rewrite HS3; exact HS2|]. split; [rewrite HF3; exact HF2|].
    split; [intros x Hx; apply HCS3, HCS2, Hx|].
    split; [clear - HV2 HV3; lia|].
    rewrite lset_FR_val in HFR3. clear - HFR2 HFR3. lia.
    all: match goal with |- ?gg => idtac "LSET2-LEFT:" gg end.
  Qed.

  (* [comment removed for export] *)
  #[using="NEEDR DIMG MFREE IDC AL8 POS LOS SLO TOP SPA DS TPV CWA UWO BUD BUDF"] Lemma mx_ok : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "Phk,(45.$17.VR,VHIA,)PLBk,(?.$10.)Pnl,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PPA,$0.PPX,$0.PPZ,$0.PwA,(2.&40.)PwX,(2.&40.)PwZ,(2.&40.)PpA,(2.&40.)PpX,(2.&40.)PpZ,(2.&40.)Pmk,P,(2.&40.)(46.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pxs1,(2.&40.)Pxa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pxs2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(47.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.(52.(23.VA,+18.)R1<.R19.R16.)(52.(23.VA,+38.)R1;.R18.R15.)(52.(23.VA,+58.)R1:.R17.R14.)R13.)P,(15.(3>.=R24.)(3>.R24.+3.))(49.$17.(4:.$17.VR,VHIA,R27.Vmo,)(4;.$17.VR,VHIA,$4<.$14.$4=.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VA,Vg,Vid,Vlo,Vd,Vm,Vmo,)(4>.(4?.R14.(21.&40.(23.(31.&40.Vsp,)-20.))Vgp,Vtp,R13.R12.R11.(21.&40.VA,)R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(21.&40.+=316<.)Vfc,(50.(2.&40.))R15.(51.$17.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros STT NL. unfold mx_st in STT. cbv zeta in STT.
    set (dA := heap1 (A + 24) PA wA pA) in *. set (dX := heap1 (A + 56) PX wX pX) in *. set (dZ := heap1 (A + 88) PZ wZ pZ) in *.
    ddestruct STT as (HH & IFF & FRESH & (NAX & NAZ & NXZ) & (HD & HP & HB & HY & HN & HT) & (MA & FA) & (MX & FX) & (MZ & FZ) & FR & ST & MI & OA & PXA
                     & HT2 & HS2 & HF2 & HCS2 & HV2 & HFR2).
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA hk _ _ _ HH) as HTOPk. rewrite HT2, HS2 in HTOPk.
    destruct (hm_apart asegs R HIA hk LBk LF mk HH) as [HBR HAP]. change (blkfacts L (LBk ++ LF)) in HBR.
    pose proof (hcs_ok asegs R HIA hk) as CSOK.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    assert (SCS : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCS2|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. clear - TOP HTOPk. lia. }
    assert (SUBk : forall b, In b LBf -> In b LBk) by (intros b Hb; apply (proj2 (IFF b)); right; exact Hb).
    assert (SUBkk : forall b, In b (LBf ++ fdata LF) -> In b (LBk ++ fdata LF)).
    { intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBk; exact Hb| right; exact Hb]. }
    assert (MPB : 0 <= ca_modp (A_CA id) < 2^64 /\ In (ca_modp (A_CA id), (ca_P (A_CA id), cP id)) A_MT).
    { destruct IDC as [-> | ->]; cbn -[c9_P c13_P]; (split; [clear; lia| auto 20]). }
    destruct MPB as [MB MODP].
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    zstep. zstep.
    (* [comment removed for export] *)
    pose proof MFREE as SF. unfold mpi_free_stmtA in SF.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SF with (h := hk) (LB := LBk) (LF := LF) (X := A + 72) (sw := Z_to_bv 64 1) (own := LNull) (P := 0) (n := 0) (limbs := []) (pad := pY) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia);
        cbn [mpi_free_LB];
        first [ exact HK1 | exact HH | exact LOS | exact TPV | exact ST | exact MI | reflexivity
              | exact (mpdr_at_init _ _ LBk _ _ HY ltac:(clear - AL8; Z.div_mod_to_equations; lia) ltac:(clear - POS; lia))
              | lazymatch goal with
                | |- LNull <> LStatic => discriminate
                | |- client_wrange _ _ _ _ _ _ => rewrite HT2; eapply (client_wrange_weak L); [exact CWA| exact SUBkk| clear; lia| clear; lia| clear; lia]
                | |- LNull = LHeap -> _ => intros C; discriminate C
                | |- lo <= _ => clear - SLO NEEDR NER; lia
                | |- _ <= htop _ _ _ _ => rewrite HT2; clear - TOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- aobj _ _ _ _ _ _ => eapply aobj_sub; [exact OA| clear; lia| clear; lia]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold group_load_PHI in BUD; unfold GF_PHI, grow_PHI in *; unfold AVOL_CALL in *; clear - BUD HV2 NL; lia
                | |- uw_obj _ _ _ _ => eapply uw_obj_sub; [exact UWO| clear; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold group_load_FRn, calls_FR in BUDF; unfold GF_FR, fr_charge in *; clear - BUDF HFR2 D0 NL; lia
                end
              | match goal with |- ?gg => idtac "MFREE-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & HY2).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, PXl by (clear - SPR SLO NEEDR NER LOS ALO ACP; lia).
    cbn [mpi_free_LB mpi_free_X] in PXl, HH2.
    replace (ret_pc (Z_to_bv 64 0xd3174)) with (Z_to_bv 64 0xd3174 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (CRk : forall a n, A <= a -> a + n <= A + 192 -> client_range L (LBk ++ fdata LF) (bv_unsigned sp + -32) a n).
    { intros a n H1 H2. eapply (client_range_of_wrange L); [exact CWA| exact SUBkk| clear; lia| exact H1| exact H2]. }
    assert (KEEP : forall o dd, mpdr_at asegs mk LBk dd -> mx_field (A + o) dd -> (dd = dA \/ dd = dX \/ dd = dZ) -> 0 <= o -> o + 16 <= 192 ->
                   (A + o + 16 <= A + 72 \/ A + 72 + 16 <= A + o) -> mpdr_at asegs m2 LBk dd).
    { intros o dd Md Fd WH O1 O2 OD. pose proof Fd as [Ed _].
      eapply (mpdr_at_presA asegs L mk m2 LBk LBk (LBk ++ fdata LF)); [exact Md| exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXl)| exact MI| exact MI2| | |].
      - rewrite Ed. apply CRk; [clear - O1; lia| clear - O2; lia].
      - rewrite Ed. cbn [disjoint_from]. split; [clear - OD; lia| exact I].
      - intros O. destruct (mpdr_blk_factsA asegs L _ _ _ _ Md O HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (I1 & I2 & I3 & I4 & I5).
        split; [exact I1|]. split; [eapply client_range_block; [apply in_app_iff; left; exact I1| clear; lia| clear; lia]|].
        cbn [disjoint_from]. split; [| exact I].
        assert (CWx : client_wrange L (LBf ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) (A + 72) 16) by (eapply (client_wrange_weak L); [exact CWA| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia]).
        assert (INN : In (md_p dd, 4 * md_n dd) (mpd_blk dA ++ mpd_blk dX ++ mpd_blk dZ)).
        { assert (Hb : In (md_p dd, 4 * md_n dd) (mpd_blk dd)) by (unfold mpd_blk; rewrite O; left; reflexivity).
          rewrite !in_app_iff. clear - Hb WH. destruct WH as [<-|[<-| <-]]; auto. }
        pose proof (proj1 (FRESH _ INN)) as NIf.
        destruct (client_apart_blockA L LBf LBk LF (bv_unsigned sp) (htop asegs R HIA h) (A + 72) 16 (md_p dd) (4 * md_n dd) CWx SUBk HBR HAP I1 NIf ltac:(clear - I2; lia) ltac:(clear; lia)
                    ltac:(clear - ALO LOS SLO NEEDR NER; lia) (proj1 DIMG) (proj2 DIMG)) as [Q|Q]; clear - Q; lia. }
    assert (TRC : forall a cs, rw_cells asegs mk a cs -> A <= a -> a + Z.of_nat (cells_size cs) <= A + 192 ->
                    (a + Z.of_nat (cells_size cs) <= A + 72 \/ A + 72 + 16 <= a) -> rw_cells asegs m2 a cs).
    { intros a cs Hc H1 H2 H3. eapply (presA_rw_cells asegs R); [exact PXl| exact Hc| apply CRk; [exact H1| exact H2]| cbn [disjoint_from]; split; [exact H3| exact I]]. }
    pose proof (TRC _ _ HD ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as HD2.
    pose proof (TRC _ _ HP ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as HP2.
    pose proof (TRC _ _ HB ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as HB2.
    pose proof (TRC _ _ HN ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as HN2.
    pose proof (TRC _ _ HT ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as HTc2.
    pose proof (presA_rw_cells asegs R _ _ _ _ _ _ mk m2 _ _ PXl FR ltac:(apply client_range_stack; cbn; clear; lia) ltac:(cbn; clear - DS SLO NEEDR NER; lia)) as FR2.
    assert (PXA2 : presW asegs R HIA h LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m2).
    { eapply presW_call; [exact PXA| exact PXl| exact SUBk| intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia|].
      intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
    assert (OBJ2 : aobj asegs AL (hcs asegs R HIA hk) m2 A 192).
    { eapply (presA_aobj asegs R (hcs asegs R HIA hk)); [exact CSOK| exact PXl| exact OA| apply CRk; clear; lia| clear - LOS SLO NEEDR NER; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    pose proof (KEEP 24 dA MA FA ltac:(auto) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as MA2.
    pose proof (KEEP 56 dX MX FX ltac:(auto) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as MX2.
    pose proof (KEEP 88 dZ MZ FZ ltac:(auto) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as MZ2.
    clear PXA PXl SF FR ST MI HH OA LAWS KINV MU WM KEEP TRC HD HP HB HN HT HY MA MX MZ.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (hcs_ok asegs R HIA h2) as CSOKc.
    pose proof (crange_mono _ _ _ _ HCS3 SCS) as SCSc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS3 OBJ2) as OBJc.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    do 7 zstep.
    lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp); rename STx into STf end.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold ecp_group_load_postA, ECP_GROUP_SIZE.
    deexists 14. dexists m9, mo9, h2, 0, (grp_mx id (A_CA id) A idpad pP pA pB pX pY pZ pN hpad PA PX PZ wA wX wZ), [(PA, 4); (PX, 4); (PZ, 4)], LBk.
    split; [reflexivity|]. split; [assumption|]. split; [exact STf|]. split; [exact MF9|].
    split; [lazymatch goal with PXx : presW _ _ _ h LBf LF _ _ _ m m9 |- _ => exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ PXx) end|].
    split; [rewrite HT3; exact HT2|]. split; [rewrite HS3; exact HS2|]. split; [rewrite HF3; exact HF2|]. split; [exact HK9|].
    split; [intros x Hx; apply HCS3, HCS2, Hx|].
    split; [unfold group_load_PHI, GF_PHI in *; unfold grow_PHI in *; unfold AVOL_CALL in *; clear - HV2 HV3 NL; lia|].
    split; [unfold group_load_FRn, GF_FR, calls_FR, fr_charge in *; clear - HFR2 HFR3 D0 NL; lia|].
    split; [assumption|].
    split; [exact IFF|].
    split; [exact FRESH|].
    split. { unfold grp_mx. eapply grp_mxi_at; first [exact IDC| exact MODP| exact MB| exact AL8| exact POS| exact FA| exact FX| exact FZ| eassumption
                               | (lazymatch goal with MIx : mem_inv _ m9 |- curve_statics _ _ _ _ _ => exact (A_curve_statics m9 id MIx ltac:(clear - IDC; lia)) end) ]. }
    split; [unfold grp_mx; apply grp_mxi_apartA; assumption|].
    split; [reflexivity|].
    split. { right. left. split; [reflexivity|]. split; [exact IDC|]. deexists 15. split; reflexivity. }
    assumption.
    all: match goal with |- ?gg => idtac "OK-LEFT:" gg end.
  Qed.

  (* [comment removed for export] *)
  #[using="NEEDR DIMG HMND GF HLSET MFREE IDC AL8 POS LOS SLO TOP SPA DS TPV CWA UWO BUD BUDF"] Lemma mx_third : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "Phk,(45.$17.VR,VHIA,)PLBk,(?.$10.)Pnl,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PPA,$0.PPX,$0.PwA,(2.&40.)PwX,(2.&40.)PpA,(2.&40.)PpX,(2.&40.)PpZ,(2.&40.)Pmk,P,(2.&40.)(46.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pxs1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pxs2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(47.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.(52.(23.VA,+18.)R1:.R18.R16.)(52.(23.VA,+38.)R19.R17.R15.)(53.(23.VA,+58.)R14.)R13.)P,(15.(3>.=R22.)(3>.R22.+2.))(49.$17.(4:.$17.VR,VHIA,R25.Vmo,)(4;.$17.VR,VHIA,$4<.$14.$4=.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VA,Vg,Vid,Vlo,Vd,Vm,Vmo,)(4>.(4?.R14.(21.&40.(23.(31.&40.Vsp,)-20.))Vgp,Vtp,R13.R12.R11.(21.&40.VA,)R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(21.&40.+=3148.)Vfc,(50.(2.&40.))R15.(51.$17.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros STT NL.
    pose proof STT as STT0. unfold mx_st in STT0. cbv zeta in STT0.
    ddestruct STT0 as (HH & _ & _ & _ & (_ & _ & _ & _ & _ & HT) & _).
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB. clear HT.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply (mx_lset 2 (A + 88)) with (pad := pZ) (RET := 0xd3154) (v := 1);
      first [ exact STT | exact NL | (clear; lia) | reflexivity | (right; right; split; reflexivity) | idtac ].
    cbn [Z.eqb]. intros hk' LBk' dN mk' r y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 ST' RES.
    clear STT HH LAWS KINV MU WM.
    pose proof (AIh_laws asegs R HIA hk') as LAWS. pose proof (KF_kinv asegs R HIA hk' mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk') as MU. pose proof (wmono_refl asegs mk') as WM.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - destruct RES as [(Er & P & w & ->)|[Er _]]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K0; vm_compute in K0; first [discriminate K0| (apply K0; reflexivity)| congruence]].
      eapply mx_ok; [exact ST'| clear - NL; lia].
    - destruct RES as [(Er & _)|[Er ->]]; [exfalso; subst r; first [apply K0; reflexivity| (vm_compute in K0; congruence)]|].
      eapply mx_fail; [exact ST'| clear - NL; lia| exact Er].
    all: match goal with |- ?gg => idtac "THIRD-LEFT:" gg end.
  Qed.
End GLMX.

Section GLMXC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis GF : ecp_group_free_stmtA asegs R HIA A_MT A_ECP_GROUP_FREE.
  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis MFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.

  (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HMND GF HLSET MFREE"] Lemma mx_case9 : gl_case_stmtA R HIA 9.
  Proof.
    unfold gl_case_stmtA. intros until t6.
    intros HH2 CELLS AL8 POS FR ST LOS SLO TOP SPA DS TPV MI3 RAE OA CRA CWA UWO PXA HT2 HS2 HF2 HCS2 HV2 HFR2 BUD BUDF C24H.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    pose proof (hm_top asegs R HIA h2 _ _ _ HH2) as HTOP2. rewrite HT2, HS2 in HTOP2.
    set (LBf := grp_free_LB g LB) in *.
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo).
    { eapply (mxpre9 R HIA IMG) with (h := h2) (LB := LBf) (LF := LF) (lo := lo);
        first [ exact HH2 | exact CELLS | exact AL8 | exact POS | exact FR | exact ST | exact LOS | exact SPA | exact DS | exact MI3 | exact OA | exact RAE
              | (rewrite HT2; exact TOP) | (clear - SLO NER NEEDR; lia)
              | (rewrite HT2; eapply (client_wrange_weak L); [exact CWA| intros b Hb; exact Hb| clear - LOS SLO NER NEEDR; lia| clear; lia| clear; lia])
              | match goal with |- ?gg => idtac "PRE-LEFT:" gg end ]. }
    cbv beta. intros ms' PO. unfold gl_mx_pre_post in PO.
    ddestruct PO as (y0 & y1 & y2 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & -> & MU & WM & MI' & CELLS' & FR' & ST' & HH').
    ddestruct CELLS' as (HD & HP & HA & HB & HX & HY & HZ & HN & HT).
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)).
    { eapply crange_sub; [exact SCS0| clear - LOS; lia|]. clear - TOP HTOP2. lia. }
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
    pose proof (aobj_munch asegs AL _ (hcs_ok asegs R HIA h2) _ m3 m' _ _ WC2 MU OA) as OA'.
    assert (MA0 : forall o pd, rw_cells asegs m' (A + o) (mpi_cells 0 (Z_to_bv 64 1) 0 pd) -> 0 <= o -> (A + o) mod 8 = 0 -> mpdr_at asegs m' LBf (mpd_init (A + o) pd)).
    { intros o pd Hc Ho Ha. apply mpdr_at_init; [exact Hc| exact Ha| clear - POS Ho; lia]. }
    assert (ST0 : mx_st R HIA h LB LF ra sp s0 s1 s2 m A g 9 lo d h2 LBf 0 idpad pP pB pY pN hpad (mpd_init (A + 24) pA) (mpd_init (A + 56) pX) (mpd_init (A + 88) pZ) m').
    { unfold mx_st. cbv zeta. cbn [mpd_blk md_own mpd_init app].
      split; [exact HH'|]. split; [intros b; cbn [In]; tauto|]. split; [intros b []|].
      split; [repeat split; intros C; discriminate C|].
      split; [repeat (split; [assumption|]); assumption|].
      split; [split; [apply (MA0 24); [exact HA| clear; lia| clear - AL8; Z.div_mod_to_equations; lia]| apply mx_field_init]|].
      split; [split; [apply (MA0 56); [exact HX| clear; lia| clear - AL8; Z.div_mod_to_equations; lia]| apply mx_field_init]|].
      split; [split; [apply (MA0 88); [exact HZ| clear; lia| clear - AL8; Z.div_mod_to_equations; lia]| apply mx_field_init]|].
      split; [exact FR'|]. split; [exact ST'|]. split; [exact MI'|]. split; [exact OA'|]. split; [exact PXA'|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HCS2|].
      split; [clear - HV2; lia| clear - HFR2; lia]. }
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    clear HD HP HA HB HX HY HZ HN HT FR' ST' MI' OA' PXA' HH' MA0 MU WM FR ST MI3 OA PXA HH2 CELLS.
    change (gl_mx_ret 9) with 0xd3134.
    (* [comment removed for export] *)
    eapply (mx_lset R HIA NEEDR DIMG HLSET) with (k := 0) (X0 := A + 24) (pad := pA) (RET := 0xd3134) (v := mx_a24 9) (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
      first [ exact ST0 | exact POS | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact CWA | exact UWO | exact BUD | exact BUDF
            | reflexivity | (left; split; reflexivity)
            | lazymatch goal with |- 0 <= mx_a24 9 < 2 ^ 31 => (vm_compute; split; [intros C; discriminate C| reflexivity]) | |- 0 <= 864564 < _ => (clear; lia) | |- 864564 mod 2 = 0 => reflexivity
                                | |- 0 <= _ <= 2 => (clear; lia) | |- @eq Z _ _ => (clear; lia) end
            | idtac ].
    cbn [Z.eqb]. intros hk1 LB1 dN1 m1 r1 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 ST1 RES1.
    clear ST0.
    pose proof (AIh_laws asegs R HIA hk1) as LAWS. pose proof (KF_kinv asegs R HIA hk1 mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - destruct RES1 as [(Er & _)|[Er ->]]; [exfalso; subst r1; first [apply K0; reflexivity| (vm_compute in K0; congruence)]|].
      eapply (mx_fail R HIA NEEDR DIMG HMND GF) with (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
        first [ exact ST1 | exact Er | exact POS | exact AL8 | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact RAE | exact CRA | exact CWA | exact UWO | exact BUD | exact BUDF
              | (left; reflexivity) | lazymatch goal with |- 0 <= _ <= 3 => (clear; lia) end | match goal with |- ?gg => idtac "C9F1-LEFT:" gg end ].
    - destruct RES1 as [(Er & P1 & w1 & ->)|[Er _]]; [| exfalso; subst r1; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K0; vm_compute in K0; first [discriminate K0| (apply K0; reflexivity)| congruence]].
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply (mx_lset R HIA NEEDR DIMG HLSET) with (k := 1) (X0 := A + 56) (pad := pX) (RET := 0xd3144) (v := 9) (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
        first [ exact ST1 | exact POS | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact CWA | exact UWO | exact BUD | exact BUDF
              | reflexivity | (right; left; split; reflexivity)
              | lazymatch goal with |- 0 <= 9 < 2 ^ 31 => (clear; lia) | |- 0 <= 864580 < _ => (clear; lia) | |- 864580 mod 2 = 0 => reflexivity
                                  | |- 0 <= _ <= 2 => (clear; lia) | |- @eq Z _ _ => (clear; lia) end
              | idtac ].
      cbn [Z.eqb]. intros hk2 LB2 dN2 m2 r2 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 ST2 RES2.
      clear ST1 LAWS KINV MU WM.
      pose proof (AIh_laws asegs R HIA hk2) as LAWS. pose proof (KF_kinv asegs R HIA hk2 mo) as KINV.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      + destruct RES2 as [(Er2 & _)|[Er2 ->]]; [exfalso; subst r2; first [apply K1; reflexivity| (vm_compute in K1; congruence)]|].
        eapply (mx_fail R HIA NEEDR DIMG HMND GF) with (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
          first [ exact ST2 | exact Er2 | exact POS | exact AL8 | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact RAE | exact CRA | exact CWA | exact UWO | exact BUD | exact BUDF
                | (left; reflexivity) | lazymatch goal with |- 0 <= _ <= 3 => (clear; lia) end | match goal with |- ?gg => idtac "C9F2-LEFT:" gg end ].
      + destruct RES2 as [(Er2 & P2 & w2 & ->)|[Er2 _]]; [| exfalso; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; vm_compute in K1; first [discriminate K1| (apply K1; reflexivity)| congruence]].
        eapply (mx_third R HIA NEEDR DIMG HMND GF HLSET MFREE) with (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
          first [ exact ST2 | exact POS | exact AL8 | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact RAE | exact CRA | exact CWA | exact UWO | exact BUD | exact BUDF
                | (left; reflexivity) | lazymatch goal with |- 0 <= _ <= 2 => (clear; lia) end | match goal with |- ?gg => idtac "C9T-LEFT:" gg end ].
    all: match goal with |- ?gg => idtac "C9-LEFT:" gg end.
  Qed.
  (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HMND GF HLSET MFREE"] Lemma mx_case13 : gl_case_stmtA R HIA 13.
  Proof.
    unfold gl_case_stmtA. intros until t6.
    intros HH2 CELLS AL8 POS FR ST LOS SLO TOP SPA DS TPV MI3 RAE OA CRA CWA UWO PXA HT2 HS2 HF2 HCS2 HV2 HFR2 BUD BUDF C24H.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    pose proof (hm_top asegs R HIA h2 _ _ _ HH2) as HTOP2. rewrite HT2, HS2 in HTOP2.
    set (LBf := grp_free_LB g LB) in *.
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo).
    { eapply (mxpre13 R HIA IMG) with (h := h2) (LB := LBf) (LF := LF) (lo := lo);
        first [ exact HH2 | exact CELLS | exact AL8 | exact POS | exact FR | exact ST | exact LOS | exact SPA | exact DS | exact MI3 | exact OA | exact RAE
              | (rewrite HT2; exact TOP) | (clear - SLO NER NEEDR; lia)
              | (rewrite HT2; eapply (client_wrange_weak L); [exact CWA| intros b Hb; exact Hb| clear - LOS SLO NER NEEDR; lia| clear; lia| clear; lia])
              | match goal with |- ?gg => idtac "PRE-LEFT:" gg end ]. }
    cbv beta. intros ms' PO. unfold gl_mx_pre_post in PO.
    ddestruct PO as (y0 & y1 & y2 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & -> & MU & WM & MI' & CELLS' & FR' & ST' & HH').
    ddestruct CELLS' as (HD & HP & HA & HB & HX & HY & HZ & HN & HT).
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)).
    { eapply crange_sub; [exact SCS0| clear - LOS; lia|]. clear - TOP HTOP2. lia. }
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
    pose proof (aobj_munch asegs AL _ (hcs_ok asegs R HIA h2) _ m3 m' _ _ WC2 MU OA) as OA'.
    assert (MA0 : forall o pd, rw_cells asegs m' (A + o) (mpi_cells 0 (Z_to_bv 64 1) 0 pd) -> 0 <= o -> (A + o) mod 8 = 0 -> mpdr_at asegs m' LBf (mpd_init (A + o) pd)).
    { intros o pd Hc Ho Ha. apply mpdr_at_init; [exact Hc| exact Ha| clear - POS Ho; lia]. }
    assert (ST0 : mx_st R HIA h LB LF ra sp s0 s1 s2 m A g 13 lo d h2 LBf 0 idpad pP pB pY pN hpad (mpd_init (A + 24) pA) (mpd_init (A + 56) pX) (mpd_init (A + 88) pZ) m').
    { unfold mx_st. cbv zeta. cbn [mpd_blk md_own mpd_init app].
      split; [exact HH'|]. split; [intros b; cbn [In]; tauto|]. split; [intros b []|].
      split; [repeat split; intros C; discriminate C|].
      split; [repeat (split; [assumption|]); assumption|].
      split; [split; [apply (MA0 24); [exact HA| clear; lia| clear - AL8; Z.div_mod_to_equations; lia]| apply mx_field_init]|].
      split; [split; [apply (MA0 56); [exact HX| clear; lia| clear - AL8; Z.div_mod_to_equations; lia]| apply mx_field_init]|].
      split; [split; [apply (MA0 88); [exact HZ| clear; lia| clear - AL8; Z.div_mod_to_equations; lia]| apply mx_field_init]|].
      split; [exact FR'|]. split; [exact ST'|]. split; [exact MI'|]. split; [exact OA'|]. split; [exact PXA'|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HCS2|].
      split; [clear - HV2; lia| clear - HFR2; lia]. }
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    clear HD HP HA HB HX HY HZ HN HT FR' ST' MI' OA' PXA' HH' MA0 MU WM FR ST MI3 OA PXA HH2 CELLS.
    change (gl_mx_ret 13) with 0xd1530.
    (* [comment removed for export] *)
    eapply (mx_lset R HIA NEEDR DIMG HLSET) with (k := 0) (X0 := A + 24) (pad := pA) (RET := 0xd1530) (v := mx_a24 13) (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
      first [ exact ST0 | exact POS | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact CWA | exact UWO | exact BUD | exact BUDF
            | reflexivity | (left; split; reflexivity)
            | lazymatch goal with |- 0 <= mx_a24 13 < 2 ^ 31 => (vm_compute; split; [intros C; discriminate C| reflexivity]) | |- 0 <= 857392 < _ => (clear; lia) | |- 857392 mod 2 = 0 => reflexivity
                                | |- 0 <= _ <= 2 => (clear; lia) | |- @eq Z _ _ => (clear; lia) end
            | idtac ].
    cbn [Z.eqb]. intros hk1 LB1 dN1 m1 r1 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 ST1 RES1.
    clear ST0.
    pose proof (AIh_laws asegs R HIA hk1) as LAWS. pose proof (KF_kinv asegs R HIA hk1 mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; cycle 1.
    - destruct RES1 as [(Er & _)|[Er ->]]; [exfalso; subst r1; first [apply K0; reflexivity| (vm_compute in K0; congruence)]|].
      zstep.
      eapply (mx_fail R HIA NEEDR DIMG HMND GF) with (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
        first [ exact ST1 | exact Er | exact POS | exact AL8 | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact RAE | exact CRA | exact CWA | exact UWO | exact BUD | exact BUDF
              | (right; reflexivity) | lazymatch goal with |- 0 <= _ <= 3 => (clear; lia) end | match goal with |- ?gg => idtac "C13F1-LEFT:" gg end ].
    - destruct RES1 as [(Er & P1 & w1 & ->)|[Er _]]; [| exfalso; subst r1; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K0; vm_compute in K0; first [discriminate K0| (apply K0; reflexivity)| congruence]].
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply (mx_lset R HIA NEEDR DIMG HLSET) with (k := 1) (X0 := A + 56) (pad := pX) (RET := 0xd1544) (v := 5) (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
        first [ exact ST1 | exact POS | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact CWA | exact UWO | exact BUD | exact BUDF
              | reflexivity | (right; left; split; reflexivity)
              | lazymatch goal with |- 0 <= 5 < 2 ^ 31 => (clear; lia) | |- 0 <= 857412 < _ => (clear; lia) | |- 857412 mod 2 = 0 => reflexivity
                                  | |- 0 <= _ <= 2 => (clear; lia) | |- @eq Z _ _ => (clear; lia) end
              | idtac ].
      cbn [Z.eqb]. intros hk2 LB2 dN2 m2 r2 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 ST2 RES2.
      clear ST1 LAWS KINV MU WM.
      pose proof (AIh_laws asegs R HIA hk2) as LAWS. pose proof (KF_kinv asegs R HIA hk2 mo) as KINV.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; cycle 1.
      + destruct RES2 as [(Er2 & _)|[Er2 ->]]; [exfalso; subst r2; first [apply K1; reflexivity| (vm_compute in K1; congruence)]|].
        zstep.
        eapply (mx_fail R HIA NEEDR DIMG HMND GF) with (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
          first [ exact ST2 | exact Er2 | exact POS | exact AL8 | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact RAE | exact CRA | exact CWA | exact UWO | exact BUD | exact BUDF
                | (right; reflexivity) | lazymatch goal with |- 0 <= _ <= 3 => (clear; lia) end | match goal with |- ?gg => idtac "C13F2-LEFT:" gg end ].
      + destruct RES2 as [(Er2 & P2 & w2 & ->)|[Er2 _]]; [| exfalso; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; vm_compute in K1; first [discriminate K1| (apply K1; reflexivity)| congruence]].
        zstep.
        eapply (mx_third R HIA NEEDR DIMG HMND GF HLSET MFREE) with (LB := LB) (g := g) (h := h) (d := d) (lo := lo);
          first [ exact ST2 | exact POS | exact AL8 | exact LOS | exact SLO | exact TOP | exact SPA | exact DS | exact TPV | exact RAE | exact CRA | exact CWA | exact UWO | exact BUD | exact BUDF
                | (right; reflexivity) | lazymatch goal with |- 0 <= _ <= 2 => (clear; lia) end | match goal with |- ?gg => idtac "C13T-LEFT:" gg end ].
    all: match goal with |- ?gg => idtac "C13-LEFT:" gg end.
  Qed.
End GLMXC.

(* [comment removed for export] *)
Theorem A_ecp_group_load_spec_closed : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mx ()) "PR,$54.PHIA,(55.$17.R1.)P,(56.(35.R2.))P,(3>.=(57.R3.))P,(3>.=(58.R4.))P,(15.(3>.(59.(5:.R5.))(5;.(5:.R5.)))(3>.(5<.(5:.R5.))(5=.(5:.R5.))))P,Ph,(45.$17.R6.R5.)PLB,(?.$10.)PLF,(?.$10.)Pm,P,(2.&40.)(46.(2.&8.))P,(16.$17.R:.R9.R4.R3.R2.R1.)(5>.$0.(5?.(39.$0.$0.)$0.(1;.$0.$0.)R4.))P,(60.$17.R7.R6.$4<.$61.)P,(62.$17.R8.R7.$4<.$63.)P,(64.$17.R9.R8.$65.)P,(66.$17.R:.R9.$67.)(68.$17.R;.R:.$4<.$14.$4=.$69.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG NEEDR NEEDA DIMG HMND GF GI HLSET MFREE.
  apply A_ecp_group_load_spec; try assumption.
  - exact (mx_case9 R HIA IMG NEEDR DIMG HMND GF HLSET MFREE).
  - exact (mx_case13 R HIA IMG NEEDR DIMG HMND GF HLSET MFREE).
Qed.
