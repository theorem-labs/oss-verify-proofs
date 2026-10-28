(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_cmp P_ecp_group_free P_ecp_red P_ecp_mul_mod P_ecp_sw_rhs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_stmtA_ng_sz A_ecp_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_mpi_cmp_mpi A_mpi_cmp_int A_ecp_mul_mod A_ecp_journey.
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
Ltac2 gd_tbl_A_ecp_sw_rhs () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_mul_mod_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_MUL_COUNT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.sw_rhs_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.sw_rhs_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_sz"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "SR.SRI"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.binop_keep"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "SR.sr_src"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_binop_stmtA_sz"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_ng_sz.mpi_binop_ng_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_intop_stmtA_sz"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_PHIn"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_mul_mod.mul_mod_R"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_nz"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_MUL_MOD"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.ej_ext"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi.A_MPI_CMP_MPI_E"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int.A_MPI_CMP_INT_E"; "SR.SR_POST"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.addsub_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.addsub_FRn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.intop_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.intop_FRn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_SW_RHS"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_mul_mod_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_add_mpi_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_ADD_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_ng_sz.mpi_add_mpi_ng_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_ng_sz.mpi_sub_abs_ng_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_ABS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_sub_int_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_INT"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_sw_rhs_stmtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int.A_UAR_GOT_CI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int.A_SMALLOC_0_CI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L15886808310.14L34250851938.14L57395763234.14L6043853893.15 00000H00Q00W011S1x1a1b2x'2a'2b'1H2H02H1S1p2p'2H2S1d2H3S1x1a1b1p1d2x'2a'2b'2p'2H4". (* [comment removed for export] *)
Lemma mm_FRn_mono : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Px,$0.Pa,$0.Pb,$0.Pp,$0.Pd,$0.Px',$0.Pa',$0.Pb',$0.Pp',$0.P,(1.(2.=R9.)(2.R9.R4.))P,(1.(2.=R9.)(2.R9.R4.))P,(1.(2.=R9.)(2.R9.R4.))P,(2.R9.R4.)P,(2.=R9.)(2.(3.R>.R=.R<.R;.R:.)(3.R9.R8.R7.R6.R:.))")
(* [comment removed for export] *).
Proof.
  intros. unfold mm_FRn.
  pose proof (mod_mpi_FRn_mono (mul_mpi_nz x a b) p d (mul_mpi_nz x' a' b') p' d ltac:(unfold mul_mpi_nz; lia) ltac:(lia) ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section SR.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variable MT : list modp_ent.
  Hypothesis HMM : ecp_mul_mod_stmtA asegs R HIA MT A_ECP_MUL_MOD A_MUL_COUNT.
  Hypothesis HADD : mpi_add_mpi_stmtA_sz asegs R HIA A_MPI_ADD_MPI.
  Hypothesis HADDNG : mpi_add_mpi_ng_stmtA_sz asegs R HIA A_MPI_ADD_MPI.
  Hypothesis HSUBANG : mpi_sub_abs_ng_stmtA_sz asegs R HIA A_MPI_SUB_ABS.
  Hypothesis HSUBI : mpi_sub_int_stmtA_sz asegs R HIA A_MPI_SUB_INT.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_CI.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0_CI.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (dA : mpd) (G : Z) (g : ecp_grp) (N lo d slo : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX LNull).
  Local Notation MC := A_MUL_COUNT.
  Local Notation XO := [(X, X + 16); (MC, MC + 8)].
  Definition SR_FRAME : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis EC : ECA R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis GRP : ecp_grp_preA asegs R HIA MT h LB LF m G g MC lo (bv_unsigned sp) d.
  Hypothesis OSEP : ecp_out_sepA dX G MC.
  Hypothesis MX0 : mpd_at asegs m LB dX.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis EXTA : ext_opndA asegs R HIA h LB LF m dX dA MC (bv_unsigned sp) lo d.
  Hypothesis SGA : md_sg (g_A g) = 1.
  Hypothesis SGB : md_sg (g_B g) = 1.
  Hypothesis VP : 1 <= mpd_val (g_P g).
  Hypothesis NLE : grp_nle g N.
  Hypothesis NA : md_n dA <= N.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 1104 - arl_need_ecp R.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO3 : slo <= lo.
  Hypothesis BUD : havol asegs R HIA h + sw_rhs_PHIn N <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + sw_rhs_FRn N d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_SW_RHS <= C24MAX.
  Hypothesis LFB : (length LF + 2 <= 512)%nat.

  Definition SR_POST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "(4.$5.VR,VHIA,VMT,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6.VX,VsX,VnX,VpX,Vxs0,VpadX,$7.)VG,Vg,$8.(9.VN,)(:.VN,Vd,)(;.VN,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Local Notation EJ0 := (EJ R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC).
  Local Ltac ec_open := pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].

  (* [comment removed for export] *)
  Record SRI (v f : Z) (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (dXk : mpd) : Prop := {
    sr_j : EJ0 v f hk LBk mk;
    sr_t : ejtmp R HIA LB LF hk LBk mk X dXk;
    sr_cov : forall b, In b LBk -> In b LB \/ In b (mpd_blk dXk);
    sr_pad : md_pad dXk = padX }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L19002855022.6L38948636245.0L43781953404.6L43782036732.2L45374716082.2L45376729506.3L45377042978.7L54100662224.6L774551903.6  00000=00>00?00G00M00N00O00g01?S1R5NEEDR3NERSFS2sp3SPRS1X2XBFFS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  #[using="HIA h LB LF m ra s0 s1 s2 s3 s4 s5 s6 sX nX pX xs0 padX EC MX0 XW SLO2"] Lemma sr_base : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "(1.(2.=Vlo,)(1.(2.Vlo,(<.(=.&40.Vsp,)+450.))(1.(>.(=.&40.Vsp,)(?.+2.+40.))(1.(10.(2.(11.VX,+10.)Vlo,)(2.(=.&40.Vsp,)VX,))(1.(>.=VX,)(1.(2.(11.VX,+10.)(?.+2.+40.))(1.(2.=(12.VR,))(2.(13.VR,)Vlo,))))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER. destruct XW as [CW _]. cbn [md_addr] in CW.
    pose proof MX0 as [(CX & _ & X0 & _) _]. pose proof (rw_cells_bound _ _ _ _ CX) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add md_addr] in XB, X0.
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO2 NER NEEDR; lia]. }
    repeat split; try assumption; first [clear - SLO2 NER NEEDR; lia | clear - SPR; lia | clear - XB; lia | clear - NER NEEDR; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L1175746480.1  L26909113247.38L30972483634.5 L48942359028.2 L66022206678.1 L66267159430.5 L9320373330.5  00000400500J00Q00U00g01:S2spFS2sp2lo3LO04LOSP4SP64S1X3OS3S2spS2sp1X2lo4LOSP3DSXS1R2sp2lo4LOSP4LOS'". (* [comment removed for export] *)
  #[using="sX nX pX xs0 G EC OSEP MX0 XW SLO2"] Lemma sr_after : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pdv,$0.Pdf,$0.PRr,P,$0.P,$19.SpPRET,$0.Pc0,(17.&40.)Pc1,(17.&40.)Pc2,(17.&40.)Pc3,(17.&40.)Pc4,(17.&40.)Pc5,(17.&40.)Pc6,(17.&40.)Pc7,(17.&40.)Pc8,(17.&40.)Pc9,(17.&40.)Pc10,(17.&40.)Pc11,(17.&40.)PQ,P,$1:.SpP,(1;.R17.R16.R15.R14.R13.R12.)P,(2.=R12.)P,(2.=R12.)P,(1.(2.=R11.)(>.R11.(?.+2.+40.)))P,(1<.$0.(1=.R12.+2.)=)P,Pr,$0.PdX',$19.P,A2.R16.R2.R1.(1>.R1<.R1:.R2.)P,Ph',(14.$5.VR,VHIA,)PLB',(15.$16.)Pm',P,(17.&40.)(18.(17.&8.))PdX',$19.Pr,$0.Pt0',(17.&40.)Pt1',(17.&40.)Pt2',(17.&40.)Pa1',(17.&40.)Pa2',(17.&40.)Pa3',(17.&40.)Pa4',(17.&40.)Pa5',(17.&40.)Pa6',(17.&40.)Pa7',(17.&40.)Pt3',(17.&40.)Pt4',(17.&40.)Pt5',(17.&40.)Pt6',(17.&40.)P,(1;.(11.R30.R2:.)(11.R2?.R29.)R13.R12.R11.R10.)P,A2.R29.R10.R11.(1?.$5.(20.$5.VR,VHIA,R15.Vmo,)R1<.(21.(22.(23.&40.R29.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R10.R?.R>.R28.R27.(23.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R6.R5.R4.R3.)VF,(23.&40.R29.)Vfc,(24.(17.&40.))R13.(25.$5.)))Pms',$26.Pmo',$27.P,(28.$27.Lmo1,$27.(1.(20.$5.VR,VHIA,R1?.Vmo,R1.)(29.$5.VR,VHIA,(23.&40.R18.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.VF,Vfc,R1?.R1>.VLF,R1<.R19.R1;.R1:.Vlo,R1=.R1.(2:.R3.R2.))))(2;.$5.R;.(2:.R3.R2.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    intros until Q. (intros S Hdv Hdf HRET HRE HBK K ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'.
    destruct S as [J T COV PAD]. dpose T as (MYk & EAk & NSk & FRSk & OAk).
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by (clear - LO0 LOSP SP64; lia). rewrite EAk in HP2.
    rewrite (ret_pc_even RET HRET HRE).
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST2' by (clear; lia).
    assert (OA2 : aobj asegs AL (hcs asegs R HIA h2) m2 X 16).
    { eapply (ej_aobj_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk m2 h2 (bv_unsigned sp + -64) _ J T (proj1 XW) ltac:(clear - LOSP LOS'; lia) HP2 HCS2). }
    assert (MC2 : exists c, rw_cells asegs m2 MC [C8 c]).
    { eapply (ej_mc_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk m2 (bv_unsigned sp + -64) _ J T HP2).
      cbn [disjoint_from fst snd]. split; [clear - OS3; lia| exact I]. }
    destruct (ej_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk m2 h2 LB2 dX2 (bv_unsigned sp + -64) dv df [(X, X + 16)] J T
                ltac:(clear; lia) Hdv Hdf MI2 ST2' HP2) as [J2 T2];
      first [ assumption | solve [intros x Hx; cbn [outside fst snd] in *; tauto]
            | solve [cbn [disjoint_from fst snd]; split; [clear - DSX LOSP; lia| exact I]] | solve [clear - LOSP; lia] | idtac ].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [| exact GR].
    pose proof (HBK _ _ GR) as (_ & BP & _). dpose OUT2 as (_ & _ & O3 & _ & O5).
    constructor; [exact J2| exact T2| | rewrite BP; exact PAD].
    intros b Hb. destruct (O3 b Hb) as [K1|K1]; [| right; exact K1].
    destruct (COV b K1) as [K2|K2]; [left; exact K2| right]. rewrite (O5 b K2 Hb). exact K2.
    all: match goal with |- ?g => idtac "AFTER-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition sr_src (dXk e : mpd) : Prop := e = dXk \/ ej_ext R HIA h LB LF m (bv_unsigned sp) lo XO X e.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L13904249762.300000<S2sp2lo4LOSP". (* [comment removed for export] *)
  #[using="sX nX pX xs0 EC MX0 XW SLO2"] Lemma sr_opX : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.P,(1;.R6.R5.R4.R3.R2.R1.)(1.(2<.$5.R3.R4.R2.)(1.(2=.(1<.$2>.(2?.R2.)$30.))(1.(1<.$0.(31.R2.)VX,)(1.(32.R2.R2.Vlo,(11.(=.&40.Vsp,)-40.))(1.(33.(34.VR,)(35.$16.R4.(36.VLF,))Vlo,VX,+10.)(1.P,(1<.$2>.(2?.R2.)$37.)(33.(34.VR,)(35.$16.R5.(36.VLF,))Vlo,(38.R3.)(39.+4.(3:.R3.)))(1.(3;.VR,R4.VLF,(11.(=.&40.Vsp,)-40.)(3<.$5.VR,VHIA,R5.)R2.)(1.P,(2=.(1<.$2>.(2?.R2.)$7.))(10.(2.(11.(38.R3.)(39.+4.(3:.R3.)))Vlo,)(2.(11.(=.&40.Vsp,)-40.)(38.R3.)))(1.(3=.$5.(3>.VR,)(3?.$5.VR,VHIA,R5.)R3.R2.)(40.R2.))))))))))")
(* [comment removed for export] *).
  Proof.
    intros v f hk LBk mk dXk [J T _ _]. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    exact (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk (bv_unsigned sp + -64) J T (proj1 XW) DSX ltac:(clear - LOSP; lia)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L13904249762.300000<S2sp2lo4LOSP". (* [comment removed for export] *)
  #[using="IMG sX nX pX xs0 EC MX0 XW SLO2"] Lemma sr_opnd : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pe,$19.P,(1;.R7.R6.R5.R4.R3.R2.)P,(41.R3.R2.)(1.(2<.$5.R5.R6.R3.)(1.(42.R4.R3.)(1.(32.R4.R3.Vlo,(11.(=.&40.Vsp,)-40.))(1.(33.(34.VR,)(35.$16.R6.(36.VLF,))Vlo,(31.R3.)+10.)(1.P,(1<.$2>.(2?.R3.)$37.)(33.(34.VR,)(35.$16.R7.(36.VLF,))Vlo,(38.R4.)(39.+4.(3:.R4.)))(1.(3=.$5.(3>.VR,)(3?.$5.VR,VHIA,R7.)R5.R3.)(40.R3.)))))))")
(* [comment removed for export] *).
  Proof.
    intros v f hk LBk mk dXk e S [E|EX].
    - subst e. ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
      split; [exact XM|]. split; [left; reflexivity|]. split; [exact XOS|]. split; [rewrite XAD; exact XCR|]. split; [exact XCRL|]. split; [exact XAO| exact XIM].
    - pose proof S as [J T _ _]. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
      ddestruct (ej_opE R HIA IMG h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk e (bv_unsigned sp + -64) J T EX ltac:(clear - LOSP; lia)) as (EM & ESEP & _ & EOS & ECR & ECRL & EAO).
      split; [exact EM|]. split; [exact ESEP|]. split; [exact EOS|]. split; [exact ECR|]. split; [exact ECRL|]. split; [exact EAO|].
      ddestruct EX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & IME). exact IME.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="EC"] Lemma sr_cnt24 : forall v f hk LBk mk dXk, SRI v f hk LBk mk dXk -> cnt24 LBk <= cnt24 LB + 1.
  Proof.
    intros v f hk LBk mk dXk [J _ COV _].
    pose proof (ej_cnt24 R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk [dXk] J) as C.
    cbn [flat_map length app] in C. rewrite app_nil_r in C. specialize (C COV). cbn in C. exact C.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L1175746480.1  L22358645037.6 L30596128356.12L30972483634.5 L36440111669.11L40290687782.1 L49959034121.5 L5261871668.3  L57835863895.5 L66151427842.1600000400M01301H01k01n02D02N02^038S2spS1R2sp2lo4SLO25STACK4HSTKS1R3HIA1h1d3FRC1f2hk3dXk2eA2eB2HF4HFRkS2sp2lo3LO04LOSP4SP64S1R3HIA1h3PHI1v2hk3dXk2eA2eB2HV3HVkS1XS2LB3C243LBk4HC244C24kS1X2X03X16S1R3HIA1h2sp3TOPS2sp2r03SPA1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="IMG sX nX pX xs0 G slo EC TPV UWX OSEP MX0 XW SLO2 SPA"] Lemma sr_binop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "PENTRY,$0.PSTACK,$0.PNF,$43.PC24,$0.PPHI,P,$19.P,$19.P,$19.$0.PFRC,P,$19.P,$19.P,$19.P,$0.$0.PRr,P,(15.$16.)P,$19.P,$19.P,$19.P,$0.P,$19.SpP,(44.$5.VR,VHIA,R7.R6.R5.R4.$45.$45.R3.R2.R1.)Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.PeA,$19.PeB,$19.PRET,$0.Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pc1,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pc2,(17.&40.)Pc3,(17.&40.)Pc4,(17.&40.)Pc5,(17.&40.)Pc6,(17.&40.)Pc7,(17.&40.)Pc8,(17.&40.)Pc9,(17.&40.)Pc10,(17.&40.)Pc11,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)PQ,P,$1:.SpP,(1;.R23.R22.R21.R20.R1?.R1>.)P,(41.R1?.R1>.)P,(41.R20.R1>.)P,(42.R20.R1?.)P,(46.VR,(31.R21.)+10.Vd,)P,(46.VR,(31.R21.)+10.Vd,)P,(2.R30.+410.)P,(47.(48.(49.$16.VLF,)R30.)#200.)P,(2.=A3.R2?.R26.R25.R24.)P,(2.=A4.R2?.R27.R26.R25.Vd,)P,(2.(11.(4:.$5.VR,VHIA,Vh,)(11.R2=.A3.R31.R28.R27.R26.))$4;.)P,(2.(11.(4<.$5.VR,VHIA,Vh,)(11.R2=.A4.R31.R29.R28.R27.Vd,))$4=.)P,(2.(11.(11.(4>.VLB,)+1.)R34.)$4?.)P,(1.(2.=R28.)(>.R28.(?.+2.+40.)))P,(1<.$0.(1=.R29.+2.)=)P,Pr,$0.PdX',$19.P,A6.R36.R31.R2?.R2>.R2=.R2.R1.(1>.R32.R30.R2.)P,Ph',(14.$5.VR,VHIA,)PLB',(15.$16.)Pm',P,(17.&40.)(18.(17.&8.))PdX',$19.Pr,$0.Pt0',(17.&40.)Pt1',(17.&40.)Pt2',(17.&40.)Pa1',(17.&40.)Pa2',(17.&40.)Pa3',(17.&40.)Pa4',(17.&40.)Pa5',(17.&40.)Pa6',(17.&40.)Pa7',(17.&40.)Pt3',(17.&40.)Pt4',(17.&40.)Pt5',(17.&40.)Pt6',(17.&40.)P,(1;.(11.R46.A3.R4:.R41.R40.R3?.)(11.R45.A4.R49.R41.R40.R3?.Vd,)R13.R12.R11.R10.)P,A6.R49.R44.R42.R41.R40.R10.R11.(1?.$5.(20.$5.VR,VHIA,R15.Vmo,)R26.(21.(22.(23.&40.R40.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R10.R?.R>.(23.&40.VX,)R3<.(23.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R6.R5.R4.R3.)VF,(23.&40.R40.)Vfc,(24.(17.&40.))R13.(25.$5.)))P,(1<.(17.&40.)R27.(23.&40.(31.R2>.)))P,(1<.(17.&40.)R27.(23.&40.(31.R2>.)))(1?.$5.(20.$5.VR,VHIA,R34.Vmo,)R14.(21.(22.(23.&40.R2>.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R2=.R2<.R2;.(23.&40.VX,)R2:.(23.&40.VX,)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)VF,(23.&40.R3>.)Vfc,(24.(17.&40.))R32.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    intros ENTRY STACK NF C24 PHI FRC Rr HC. intros until Q. intros S SA SB SAB UWA UWB HSTK HNF HPHI HFRC HV HF HC24 HRET HRE HBK K E1 E2. subst xa1 xa2.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (sr_opnd v f hk LBk mk dXk eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM).
    ddestruct (sr_opnd v f hk LBk mk dXk eB S SB) as (BM & BSEP & BOS & BCR & BCRL & BAO & BIM).
    pose proof (sr_cnt24 v f hk LBk mk dXk S) as C24k. pose proof S as [J T COV PAD].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_binop_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := dXk) (dA := eA) (dB := eB) (lo := lo) (d := d) (slo := slo);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - LO0 LOSP SP64; lia).
      - exact HHk.
      - exact HK1.
      - exact HNF.
      - exact XM.
      - exact AM.
      - exact BM.
      - exact ASEP.
      - exact BSEP.
      - exact SAB.
      - exact XNS.
      - intros C; discriminate C.
      - exact AOS.
      - exact BOS.
      - exact ACR.
      - exact ACRL.
      - exact BCR.
      - exact BCRL.
      - exact XWR.
      - exact XLSq.
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 HSTK. lia.
      - intros C; discriminate C.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact BAO.
      - exact AIM.
      - exact BIM.
      - clear - HV HVk. lia.
      - eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia].
      - rewrite XAD. exact UWX.
      - exact UWA.
      - exact UWB.
      - clear - HF HFRk. lia.
      - clear - HC24 C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (sr_after v f hk LBk mk dXk (PHI dXk eA eB) (FRC dXk eA eB d) (Rr LBk dXk eA eB) RET); try eassumption.
    all: match goal with |- ?g => idtac "BINOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L1175746480.1  L19617693571.43L22358645037.6 L30972483634.5 L39280637297.0 L40290687782.1 L46010382811.7 L46012480475.7 L5261871668.3  L57835863895.5 L66151427842.1600000400500N00c00d00g01=01R01\01l02FS2spFS1R2sp2lo4SLO25STACK4HSTKS2sp2lo3LO04LOSP4SP64SS1XS1R3HIA1h1f2hk2HF4HFRkS1R3HIA1h1v2hk2HV3HVkS1X2X03X16S1R3HIA1h2sp3TOPS2sp2r03SPA1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="IMG sX nX pX xs0 G EC TPV UWX OSEP MX0 XW SLO2 SPA"] Lemma sr_binop_ng : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "PENTRY,$0.PSTACK,$0.PPRE,P,$19.P,$19.P,$19.SpPRr,P,(15.$16.)P,$19.P,$19.P,$19.P,$0.P,$19.SpP,(50.$5.VR,VHIA,R4.R3.R2.R1.)Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.PeA,$19.PeB,$19.PRET,$0.Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pc1,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pc2,(17.&40.)Pc3,(17.&40.)Pc4,(17.&40.)Pc5,(17.&40.)Pc6,(17.&40.)Pc7,(17.&40.)Pc8,(17.&40.)Pc9,(17.&40.)Pc10,(17.&40.)Pc11,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)PQ,P,$1:.SpP,(1;.R23.R22.R21.R20.R1?.R1>.)P,(41.R1?.R1>.)P,(41.R20.R1>.)P,(42.R20.R1?.)P,(46.VR,(31.R21.)+10.Vd,)P,(46.VR,(31.R21.)+10.Vd,)P,(2.R2=.+410.)P,A3.R2=.R25.R24.R23.P,(2.(11.(4:.$5.VR,VHIA,Vh,)R2;.)$4;.)P,(2.(11.(4<.$5.VR,VHIA,Vh,)R2;.)$4=.)P,(1.(2.=R25.)(>.R25.(?.+2.+40.)))P,(1<.$0.(1=.R26.+2.)=)P,Pr,$0.PdX',$19.P,A6.R33.R2>.R2<.R2;.R2:.R2.R1.(1>.R2?.R2=.R2.)P,Ph',(14.$5.VR,VHIA,)PLB',(15.$16.)Pm',P,(17.&40.)(18.(17.&8.))PdX',$19.Pr,$0.Pt0',(17.&40.)Pt1',(17.&40.)Pt2',(17.&40.)Pa1',(17.&40.)Pa2',(17.&40.)Pa3',(17.&40.)Pa4',(17.&40.)Pa5',(17.&40.)Pa6',(17.&40.)Pa7',(17.&40.)Pt3',(17.&40.)Pt4',(17.&40.)Pt5',(17.&40.)Pt6',(17.&40.)P,(1;.R43.R42.R13.R12.R11.R10.)P,A6.R46.R41.R3?.R3>.R3=.R10.R11.(1?.$5.(20.$5.VR,VHIA,R15.Vmo,)R23.(21.(22.(23.&40.R3=.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R10.R?.R>.(23.&40.VX,)R39.(23.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R6.R5.R4.R3.)VF,(23.&40.R3=.)Vfc,(24.(17.&40.))R13.(25.$5.)))P,(1<.(17.&40.)R24.(23.&40.(31.R2;.)))P,(1<.(17.&40.)R24.(23.&40.(31.R2;.)))(1?.$5.(20.$5.VR,VHIA,R31.Vmo,)R11.(21.(22.(23.&40.R2;.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R2:.R29.R28.(23.&40.VX,)R27.(23.&40.VX,)R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)VF,(23.&40.R38.)Vfc,(24.(17.&40.))R2?.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    intros ENTRY STACK PRE Rr HC. intros until Q. intros S SA SB SAB UWA UWB HSTK HPRE HV HF HRET HRE HBK K E1 E2. subst xa1 xa2.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (sr_opnd v f hk LBk mk dXk eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM).
    ddestruct (sr_opnd v f hk LBk mk dXk eB S SB) as (BM & BSEP & BOS & BCR & BCRL & BAO & BIM).
    pose proof (sr_cnt24 v f hk LBk mk dXk S) as C24k. pose proof S as [J T COV PAD].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_binop_ng_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := dXk) (dA := eA) (dB := eB) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - LO0 LOSP SP64; lia).
      - exact HHk.
      - exact HK1.
      - exact XM.
      - exact AM.
      - exact BM.
      - exact ASEP.
      - exact BSEP.
      - exact SAB.
      - exact XNS.
      - exact HPRE.
      - exact AOS.
      - exact BOS.
      - exact ACR.
      - exact ACRL.
      - exact BCR.
      - exact BCRL.
      - exact XWR.
      - exact XLSq.
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 HSTK. lia.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact BAO.
      - exact AIM.
      - exact BIM.
      - clear - HV HVk. lia.
      - eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia].
      - rewrite XAD. exact UWX.
      - exact UWA.
      - exact UWB.
      - clear - HF HFRk. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (sr_after v f hk LBk mk dXk 0 0 (Rr LBk dXk eA eB) RET); try eassumption; try (clear; lia).
    intros h' LB' m' dX' r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S' GR'. rewrite !Z.add_0_r in S'. eapply K; eassumption.
    all: match goal with |- ?g => idtac "NG-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L10949429466.10L1175746480.1  L22358645037.6 L29558281123.9 L30972483634.5 L40290687782.1 L49959034121.5 L5261871668.3  L57835863895.5 L66151427842.1600000P00T00m01I01^01a02702A02Q02kS1R3HIA1h3PHI1v2hk3dXk2eA2HV3HVkS2spS1R2sp2lo4SLO25STACK4HSTKS1R3HIA1h1d3FRC1f2hk2HF4HFRkS2sp2lo3LO04LOSP4SP64S1XS2LB3C243LBk4HC244C24kS1X2X03X16S1R3HIA1h2sp3TOPS2sp2r03SPA1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="IMG sX nX pX xs0 G EC TPV UWX OSEP MX0 XW SLO2 SPA"] Lemma sr_intop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "PENTRY,$0.PSTACK,$0.PNF,$43.PC24,$0.PPHI,P,$19.P,$19.$0.PFRC,P,$0.$0.PRr,P,(15.$16.)P,$19.P,$19.P,$0.P,$0.P,$19.SpP,(51.$5.VR,VHIA,R7.R6.R5.R4.R3.R2.R1.)Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.PeA,$19.Pb,$0.PRET,$0.Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pc1,(17.&40.)Pxa1,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pc2,(17.&40.)Pc3,(17.&40.)Pc4,(17.&40.)Pc5,(17.&40.)Pc6,(17.&40.)Pc7,(17.&40.)Pc8,(17.&40.)Pc9,(17.&40.)Pc10,(17.&40.)Pc11,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)PQ,P,$1:.SpP,(1;.R22.R21.R20.R1?.R1>.R1=.)P,(41.R1>.R1=.)P,(46.VR,(31.R1>.)+10.Vd,)P,(1.(2.(52.(?.+2.+1?.))R1>.)(>.R1>.(?.+2.+1?.)))P,(2.R2=.+410.)P,(47.(48.(49.$16.VLF,)R2=.)#200.)P,(2.=A2.R2<.R23.R22.)P,(2.=A1.R2<.Vd,)P,(2.(11.(4:.$5.VR,VHIA,Vh,)(11.R2:.A2.R2>.R25.R24.))$4;.)P,(2.(11.(4<.$5.VR,VHIA,Vh,)(11.R2:.A1.R2>.Vd,))$4=.)P,(2.(11.(11.(4>.VLB,)+1.)R31.)$4?.)P,(1.(2.=R25.)(>.R25.(?.+2.+40.)))P,(1<.$0.(1=.R26.+2.)=)P,Pr,$0.PdX',$19.P,A6.R33.R2>.R2<.R2;.R2:.R2.R1.(1>.R2?.R2=.R2.)P,Ph',(14.$5.VR,VHIA,)PLB',(15.$16.)Pm',P,(17.&40.)(18.(17.&8.))PdX',$19.Pr,$0.Pt0',(17.&40.)Pt1',(17.&40.)Pt2',(17.&40.)Pa1',(17.&40.)Pa2',(17.&40.)Pa3',(17.&40.)Pa4',(17.&40.)Pa5',(17.&40.)Pa6',(17.&40.)Pa7',(17.&40.)Pt3',(17.&40.)Pt4',(17.&40.)Pt5',(17.&40.)Pt6',(17.&40.)P,(1;.(11.R43.A2.R47.R3>.R3=.)(11.R42.A1.R46.Vd,)R13.R12.R11.R10.)P,A6.R46.R41.R3?.R3>.R3=.R10.R11.(1?.$5.(20.$5.VR,VHIA,R15.Vmo,)R24.(21.(22.(23.&40.R3=.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R10.R?.R>.(23.&40.VX,)R39.(23.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R6.R5.R4.R3.)VF,(23.&40.R3=.)Vfc,(24.(17.&40.))R13.(25.$5.)))P,(1<.(17.&40.)R24.(23.&40.(31.R2;.)))(1?.$5.(20.$5.VR,VHIA,R30.Vmo,)R11.(21.(22.(23.&40.R2:.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R29.R28.R27.(23.&40.VX,)R26.(23.&40.VX,)R25.(23.&40.R2;.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)VF,(23.&40.R3:.)Vfc,(24.(17.&40.))R2>.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    intros ENTRY STACK NF C24 PHI FRC Rr HC. intros until Q. intros S SA UWA HB HSTK HNF HPHI HFRC HV HF HC24 HRET HRE HBK K E1. subst xa1.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (sr_opnd v f hk LBk mk dXk eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM).
    pose proof (sr_cnt24 v f hk LBk mk dXk S) as C24k. pose proof S as [J T COV PAD].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_intop_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := dXk) (dA := eA) (b := b) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - LO0 LOSP SP64; lia).
      - exact HHk.
      - exact HK1.
      - exact HNF.
      - exact XM.
      - exact AM.
      - exact ASEP.
      - exact XNS.
      - exact AOS.
      - exact ACR.
      - exact ACRL.
      - exact XWR.
      - exact HB.
      - exact XLSq.
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 HSTK. lia.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact AIM.
      - clear - HV HVk. lia.
      - eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia].
      - rewrite XAD. exact UWX.
      - exact UWA.
      - clear - HF HFRk. lia.
      - clear - HC24 C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (sr_after v f hk LBk mk dXk (PHI dXk eA) (FRC d) (Rr LBk dXk eA b) RET); try eassumption.
    all: match goal with |- ?g => idtac "INTOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L37225234467.2000005S1e1K". (* [comment removed for export] *)
  #[using="sX nX pX xs0 G EC OSEP MX0 XW SLO2"] Lemma sr_src_mc : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pe,$19.P,(1;.R7.R6.R5.R4.R3.R2.)P,(41.R3.R2.)(10.(2.(11.$8.+8.)(31.R3.))(2.(11.(31.R3.)+10.)$8.))")
(* [comment removed for export] *).
  Proof.
    intros v f hk LBk mk dXk e S [E|EX].
    - subst e. ddestruct (sr_opX v f hk LBk mk dXk S) as (_ & _ & XAD & _). rewrite XAD.
      ddestruct OSEP as (_ & _ & OS3). cbn [md_addr] in OS3. exact OS3.
    - ddestruct EX as (_ & _ & _ & _ & EXO & _). cbn [disjoint_from fst snd] in EXO. ddestruct EXO as (_ & K & _). clear - K. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L1175746480.1  L13447073325.2 L14758514579.4 L15756354262.4 L26909113247.38L30047739285.7 L30972483634.5 L33119465378.11L34286087040.3 L34632335171.4 L35693534892.2 L38180633941.0 L38323340141.4 L40290687782.1 L50187530160.8 L5261871668.3  L57835863895.5 L57859093306.4 L59542742483.2 L59673527198.3 L62189453987.3 L62706248482.5 L66022206678.1 L66151427842.16L66267159430.5 L66574693495.12L67996112456.1 L9101908665.4  L9320373330.5  00000400:00H00V00W00l01A01b01l02=02D02E02W02Z03503?03O03P03X03a03k04@04D04^05005T05X05c066S2spS1g2NPS1R2sp2lo4SLO2S1R2lo3LOS3ALOFS1g1d2D03dXk2eA2eB2P1S2sp2lo3LO04LOSP4SP64S1R3HIA1h1g1v2hk3dXk2eA2eB2HV3HVkS1G3dXk2K1S2sp2lo4LOSP4MCLOS1G3GMCSS2LB4C24H3LBk4C24kS1XS1g3dXk2eA2eB3NA03NB02NP2P1S1X2X03X16S1R3HIA1h2sp3TOPFS3dXk2N1S1X1G3OS1S1G3dXk2K1S2sp2lo3slo4SLO34LOSPS2spS2sp2r03SPA1q1r1H2H02q02H4S2sp1X2lo4LOSP3DSXS1R3HIA1h1g1d1f2hk3dXk2eA2eB2HF4HFRkS2spS3dXk2eA2eBS1R2sp2lo4LOSP4LOS'". (* [comment removed for export] *)
  #[using="IMG MT HMM sX nX pX xs0 slo EC TPV UWX D0 GRP OSEP MX0 XW SLO2 SPA SSH SLO1 SLO3 C24H LFB"] Lemma sr_mulmod : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.PeA,$19.PeB,$19.PRET,$0.Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pc1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pc2,(17.&40.)Pc3,(17.&40.)Pc4,(17.&40.)Pc5,(17.&40.)Pc6,(17.&40.)Pc7,(17.&40.)Pc8,(17.&40.)Pc9,(17.&40.)Pc10,(17.&40.)Pc11,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)PQ,P,$1:.SpP,(1;.R22.R21.R20.R1?.R1>.R1=.)P,(41.R1>.R1=.)P,(41.R1?.R1=.)P,(42.R1?.R1>.)P,(46.VR,(31.R20.)+10.Vd,)P,(46.VR,(31.R20.)+10.Vd,)P,(2.=(3:.R23.))P,(2.=(3:.R23.))P,(2.=(3:.R23.))P,(2.(11.(4:.$5.VR,VHIA,Vh,)(11.R2;.(53.(3:.R26.)(3:.R25.)(3:.R24.)(3:.(54.Vg,)))))$4;.)P,(2.(11.(4<.$5.VR,VHIA,Vh,)(11.R2;.(3.(3:.R27.)(3:.R26.)(3:.R25.)(3:.(54.Vg,))Vd,)))$4=.)P,(1.(2.=R25.)(>.R25.(?.+2.+40.)))P,(1<.$0.(1=.R26.+2.)=)P,Ph',(14.$5.VR,VHIA,)PLB',(15.$16.)Pm',P,(17.&40.)(18.(17.&8.))PdX',$19.Pr,$0.Pt0',(17.&40.)Pt1',(17.&40.)Pt2',(17.&40.)Pa1',(17.&40.)Pa2',(17.&40.)Pa3',(17.&40.)Pa4',(17.&40.)Pa5',(17.&40.)Pa6',(17.&40.)Pa7',(17.&40.)Pt3',(17.&40.)Pt4',(17.&40.)Pt5',(17.&40.)Pt6',(17.&40.)P,(1;.(11.R42.(53.(3:.R3=.)(3:.R3<.)(3:.R3;.)(3:.(54.Vg,))))(11.R41.(3.(3:.R3=.)(3:.R3<.)(3:.R3;.)(3:.(54.Vg,))Vd,))R13.R12.R11.R10.)P,(55.R40.R3>.R10.R11.)P,(2.(3:.R12.)(56.(3:.R3?.)(3:.R3>.)(3:.R3=.)(3:.(54.Vg,))))(1?.$5.(20.$5.VR,VHIA,R16.Vmo,)R24.(21.(22.(23.&40.R3=.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R11.R10.R?.(23.&40.VX,)R39.(23.&40.R12.)R>.R=.R<.R;.R:.R9.R8.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R7.R6.R5.R4.)VF,(23.&40.R3=.)Vfc,(24.(17.&40.))R14.(25.$5.)))P,(1<.(17.&40.)R23.(23.&40.(31.R2:.)))P,(1<.(17.&40.)R23.(23.&40.(31.R2:.)))(1?.$5.(20.$5.VR,VHIA,R30.Vmo,)R11.(21.(22.(23.&40.R2:.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R29.R28.R27.(23.&40.VX,)R26.(23.&40.VG,)(23.&40.VX,)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)VF,(23.&40.$57.)Vfc,(24.(17.&40.))R2>.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    dpose (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros until Q. intros S SA SB SAB UWA UWB NX0 NA0 NB0 HV HF HRET HRE K E1 E2. subst xa2 xa3.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (sr_opnd v f hk LBk mk dXk eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM).
    ddestruct (sr_opnd v f hk LBk mk dXk eB S SB) as (BM & BSEP & BOS & BCR & BCRL & BAO & BIM).
    pose proof (sr_src_mc v f hk LBk mk dXk eA S SA) as AMC. pose proof (sr_src_mc v f hk LBk mk dXk eB S SB) as BMC.
    pose proof (sr_cnt24 v f hk LBk mk dXk S) as C24k. pose proof S as [J T COV PAD].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    dpose GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    assert (DXG : disjoint_from XO G 192) by (cbn [disjoint_from fst snd]; split; [clear - OS1; lia| split; [clear - GMC; lia| exact I]]).
    pose proof (ej_grp_pre R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC MT v f hk LBk mk G g (bv_unsigned sp + -64) d J GRP DXG ltac:(clear; lia)) as GRPk.
    pose proof (ej_sshad R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk slo J SSH SLO1) as SSk.
    assert (M8 : (bv_unsigned sp + -64) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
    pose proof (sshad_split asegs AL mk slo (bv_unsigned sp + -64) (bv_unsigned sp) SSk ltac:(clear - SLO3 LOSP; lia) M8) as [SS1 _].
    assert (OSk : ecp_out_sepA dXk G MC).
    { unfold ecp_out_sepA. rewrite XAD. split; [exact OS1|]. split; [| exact OS3].
      intros EO. ddestruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk J T EO) as (_ & N1 & _ & _ & _ & _ & FRA).
      destruct (fresh_apart_client R LB LF lo G 192 _ _ FRA GCR ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K1|K1]; [right| left]; clear - K1; lia. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HMM as HC. unfold ecp_mul_mod_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := dXk) (dA := eA) (dB := eB) (G := G) (g := g) (cnt := ck) (lo := lo) (d := d) (slo := slo);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - LO0 LOSP SP64; lia).
      - exact HHk.
      - exact HK1.
      - exact LFB.
      - exact GRPk.
      - exact OSk.
      - exact XM.
      - exact AM.
      - exact BM.
      - exact ASEP.
      - exact BSEP.
      - exact SAB.
      - exact XNS.
      - exact AOS.
      - exact BOS.
      - exact ACR.
      - exact ACRL.
      - exact BCR.
      - exact BCRL.
      - exact AMC.
      - exact BMC.
      - exact XWR.
      - exact XLSq.
      - exact MCk.
      - exact MCOK.
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2. lia.
      - exact SS1.
      - exact SLO1.
      - exact SLO3.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact BAO.
      - exact AIM.
      - exact BIM.
      - clear - HV HVk. lia.
      - eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia].
      - rewrite XAD. exact UWX.
      - exact UWA.
      - exact UWB.
      - clear - HF HFRk. lia.
      - unfold C24_ECP_MUL_MOD, C24_ECP_SW_RHS in *. clear - C24H C24k. lia.
      - reflexivity.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold ecp_mul_mod_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & cnt2 & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR2 & MCC2 & MR2 & SZ2).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by (clear - LO0 LOSP SP64; lia). rewrite XAD in HP2.
    rewrite (ret_pc_even RET HRET HRE).
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST2' by (clear; lia).
    assert (OA2 : aobj asegs AL (hcs asegs R HIA h2) m2 X 16).
    { eapply (ej_aobj_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk m2 h2 (bv_unsigned sp + -64) _ J T (proj1 XW) ltac:(clear - LOSP LOS'; lia) HP2 HCS2). }
    assert (PHI0' : 0 <= mm_PHIn (md_n dXk) (md_n eA) (md_n eB) (md_n (g_P g))).
    { dpose GAT as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & NP & _) & _).
      unfold mm_PHIn, red_PHIn, mul_mpi_PHIn. pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (md_n dXk) (md_n eA) (md_n eB)) (md_n (g_P g)) ltac:(unfold mul_mpi_nz; clear - NX0; lia) ltac:(clear - NP; lia)) as P1.
      unfold grow_PHI. unfold AVOL_CALL. clear - P1 NA0 NB0 NP. lia. }
    assert (FR0' : 0 <= mm_FRn (md_n dXk) (md_n eA) (md_n eB) (md_n (g_P g)) d).
    { unfold mm_FRn, red_FRn, mul_mpi_FRn. pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (md_n dXk) (md_n eA) (md_n eB)) (md_n (g_P g)) d ltac:(unfold mul_mpi_nz; clear - NX0; lia) D0) as P1.
      unfold calls_FR, fr_charge. clear - P1 D0. lia. }
    destruct (ej_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk m2 h2 LB2 dX2 (bv_unsigned sp + -64) _ _ XO J T
                ltac:(clear; lia) PHI0' FR0' MI2 ST2' HP2) as [J2 T2];
      first [ assumption | solve [intros x Hx; exact Hx]
            | solve [cbn [disjoint_from fst snd]; split; [clear - DSX LOSP; lia| split; [clear - MCLO LOSP; lia| exact I]]] | solve [clear - LOSP; lia]
            | solve [exists cnt2; exact MCC2] | idtac ].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [| exact MR2| exact SZ2].
    dpose MR2 as (_ & _ & BP & _). dpose OUT2 as (_ & _ & O3 & _ & O5).
    constructor; [exact J2| exact T2| | rewrite BP; exact PAD].
    intros b Hb. destruct (O3 b Hb) as [K1|K1]; [| right; exact K1].
    destruct (COV b K1) as [K2|K2]; [left; exact K2| right]. rewrite (O5 b K2 Hb). exact K2.
    all: match goal with |- ?g => idtac "MM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L1175746480.1 L2333536794.9 L38235734261.1L66022206678.100000400P00T00XS2spS1R3HIA1h2sp2lo3LOS3TOP1a2HaS2loS2sp". (* [comment removed for export] *)
  #[using="sX nX pX xs0 EC MX0 XW SLO2"] Lemma sr_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pm',P,(17.&40.)(18.(17.&8.))P,(1;.R7.R6.R5.R4.R3.R2.)P,(58.(59.(5:.$0.$0.)(5;.$0.$0.Vlo,(11.(=.&40.Vsp,)-40.))(5<.(5:.$0.$0.)))R4.R2.)P,(5=.$5.R5.R3.)P,(5>.$5.R4.)P,(5?.$5.R5.Vlo,(11.(=.&40.Vsp,)-40.))(1;.R<.R;.R:.R9.R6.R7.)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    intros v f hk LBk mk dXk m' [J T COV PAD] MU WM MI' ST'.
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (HH' : HM asegs R HIA hk LBk LF m').
    { eapply (hm_munch asegs R HIA hk LBk LF [(lo, bv_unsigned sp + -64)] mk m' HHk MU WM).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite HTk. clear - Ha LOS TOP. lia. }
    replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST' by (clear; lia).
    destruct (ej_scratch R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk lo (bv_unsigned sp + -64) m' J T DSX MU WM MI' ST' HH' ltac:(clear; lia) ltac:(clear; lia)) as [J' T'].
    constructor; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L1175746480.1  L19095841334.4 L30972483634.5 L35653327737.7 L39831058109.3 L59308660947.3 L60098763854.3 L66151427842.1600000400A00V00j01601C01M01gS2spS2sp1X2lo3DSXS2sp2lo3LO04LOSP4SP64S1R3HIA1h2sp2lo4SPHIS2sp2lo4LOSPS3dXk2N12E01eS1R2lo3LOSS2sp2r03SPA1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="IMG sX nX pX xs0 EC MX0 XW SLO2 SPA"] Lemma sr_cmp : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pe,$19.PRET,$0.Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pc1,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pc2,(17.&40.)Pc3,(17.&40.)Pc4,(17.&40.)Pc5,(17.&40.)Pc6,(17.&40.)Pc7,(17.&40.)Pc8,(17.&40.)Pc9,(17.&40.)Pc10,(17.&40.)Pc11,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)PQ,P,$1:.SpP,(1;.R22.R21.R20.R1?.R1>.R1=.)P,(60.VR,VHIA,Vh,VLB,VLF,Vm,(=.&40.Vsp,)Vlo,(59.(5:.$0.$0.)(5;.$0.$0.VX,(11.VX,+10.))(59.(5:.$0.$0.)(5;.$0.$0.$8.(11.$8.+8.))(5<.(5:.$0.$0.))))VX,R1=.)P,(1.(2.=R1=.)(>.R1=.(?.+2.+40.)))P,(1<.$0.(1=.R1>.+2.)=)P,Pm',P,(17.&40.)(18.(17.&8.))Pt0',(17.&40.)Pt1',(17.&40.)Pt2',(17.&40.)Pa1',(17.&40.)Pa2',(17.&40.)Pa3',(17.&40.)Pa4',(17.&40.)Pa5',(17.&40.)Pa6',(17.&40.)Pa7',(17.&40.)Pt3',(17.&40.)Pt4',(17.&40.)Pt5',(17.&40.)Pt6',(17.&40.)P,(1;.R35.R34.R33.R32.R?.R30.)(1?.$5.(20.$5.VR,VHIA,R34.Vmo,)R15.(21.(22.(23.&40.R2?.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R?.R>.R=.(23.&40.VX,)R2;.(23.&40.(61.(<.(62.R31.)(62.R30.))))R<.R;.R:.R9.R8.R7.R6.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R5.R4.R3.R2.)VF,(23.&40.R2?.)Vfc,(24.(17.&40.))R10.(25.$5.)))P,(1<.(17.&40.)R1;.(23.&40.(31.R21.)))(1?.$5.(20.$5.VR,VHIA,R26.Vmo,)R7.(21.(22.(23.&40.R21.)(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R20.R1?.R1>.(23.&40.VX,)R1=.(23.&40.VX,)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(23.&40.$63.)Vfc,(24.(17.&40.))R24.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    dpose (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros until Q. intros S EX HRET HRE K E1. subst xa1.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (sr_opnd v f hk LBk mk dXk e S (or_intror EX)) as (EM & ESEP & EOS & ECR & ECRL & EAO & EIM).
    pose proof S as [J T COV PAD]. pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    dpose EOS as (_ & _ & _ & EO4 & EO5).
    assert (SCS : crange (hcs asegs R HIA hk) lo (bv_unsigned sp + -64 - lo)).
    { eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI LOSP; lia]. }
    assert (XNL : 1 <= md_n dXk -> md_own dXk = LHeap).
    { intros N1. pose proof XM as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dXk); [exfalso; destruct OW as [_ E0]; clear - E0 N1; lia| reflexivity| exfalso; exact (XNS eq_refl)]. }
    assert (ENL : 1 <= md_n e -> md_own e <> LNull).
    { intros N1 C. pose proof EM as [(_ & _ & _ & _ & _ & OW) _]. rewrite C in OW. destruct OW as [_ E0]. clear - E0 N1. lia. }
    pose proof (A_mpi_cmp_mpi_spec AL IMG) as SPC. unfold mpi_cmp_mpi_stmtA in SPC.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { eapply SPC with (LB := LBk) (dX := dXk) (dY := e) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - LO0 LOSP SP64; lia).
      - exact XM.
      - exact EM.
      - intros EO. ddestruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk J T EO) as (_ & _ & P0 & _). exact P0.
      - intros EO. pose proof EM as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. ddestruct OW as (_ & IN & _).
        destruct (hm_apart asegs R HIA hk LBk LF mk HHk) as [HF0 _]. rewrite Forall_forall in HF0.
        destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (B0 & _). exact B0.
      - exact MIk.
      - exact (art_alwf asegs R HIA).
      - exact (hcs_ok asegs R HIA hk).
      - exact (hm_abase asegs R HIA hk LBk LF mk HHk).
      - pose proof (proj1 XAO) as OXk. rewrite XAD in OXk. rewrite ?XAD. exact OXk.
      - exact (proj1 EAO).
      - intros N1. pose proof (XNL N1) as EO. destruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk J T EO) as (IN & _).
        eapply hm_aobj_block; [exact HHk| exact IN].
      - intros N1. eapply (mpd_aobjA_limbs asegs R HIA hk LBk LF mk e HHk EM EAO (ENL N1)).
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact STk.
      - exact LO0.
      - clear - LOSP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact SCS.
      - rewrite XAD. clear - DSX. lia.
      - exact EO4.
      - intros N1. apply XLSq. rewrite (XNL N1). discriminate.
      - intros N1. exact (EO5 (ENL N1)).
      - rewrite XAD. reflexivity.
      - reflexivity. }
    intros ms' PO. unfold mpi_cmp_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MU2, ST2 by (clear - LO0 LOSP SP64; lia).
    rewrite (ret_pc_even RET HRET HRE).
    eapply K. exact (sr_scratch v f hk LBk mk dXk m2 S MU2 WM2 MI2 ST2).
    all: match goal with |- ?g => idtac "CMP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L1175746480.1  L19095841334.4 L30972483634.5 L35653327737.7 L38691415991.0 L39831058109.3 L59308660947.3 L60098763854.3 L66151427842.1600000400A00V00j00k01701B01L01fS2spS2sp1X2lo3DSXS2sp2lo3LO04LOSP4SP64S1R3HIA1h2sp2lo4SPHISS2sp2lo4LOSPS3dXk2N12E0S1R2lo3LOSS2sp2r03SPA1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 sX nX pX xs0 EC TPV MX0 XW SLO2 SPA SSH SLO1 SLO3 LFB"] Lemma sr_cmpint : forall (v f : Z) (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (dXk : mpd) (RET : Z) (xt0 xt1 xt2 c1 xa2 xa3 xa4 xa5 xa6 xa7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 xt3 xt4 xt5 xt6 : word) (Q : config -> Prop), SRI v f hk LBk mk dXk -> 0 <= RET /\ RET < 2 ^ 64 -> RET mod 2 = 0 -> (forall (hq : HST asegs R HIA) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), SRI v f hq LBk m' dXk -> aevtA asegs (KF asegs R HIA hq mo) Q (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 X) c1 (Z_to_bv 64 (Z.sgn (mpd_val dXk - 0))) a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3' t4' t5' t6') F (Z_to_bv 64 RET) fc None m' (seg_rom asegs))) -> aevtA asegs (KF asegs R HIA hk mo) Q (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp xt0 xt1 xt2 (Z_to_bv 64 X) c1 (Z_to_bv 64 X) (Z_to_bv 64 0) xa2 xa3 xa4 xa5 xa6 xa7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 A_MPI_CMP_INT_E) fc None mk (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    dpose (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros until Q. intros S HRET HRE K.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof S as [J T COV PAD]. pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (XNL : 1 <= md_n dXk -> md_own dXk = LHeap).
    { intros N1. pose proof XM as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dXk); [exfalso; destruct OW as [_ E0]; clear - E0 N1; lia| reflexivity| exfalso; exact (XNS eq_refl)]. }
    pose proof (arl_need_ecp_smalloc R) as NES.
    pose proof (ej_sshad R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk slo J SSH SLO1) as SSk.
    assert (M8 : (bv_unsigned sp + -64) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
    pose proof (sshad_split asegs AL mk slo (bv_unsigned sp + -64) (bv_unsigned sp) SSk ltac:(clear - SLO3 LOSP; lia) M8) as [SS1 _].
    pose proof (A_mpi_cmp_int_spec R HIA IMG UARG SM0 NS1) as SPC. unfold mpi_cmp_int_stmtA in SPC.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { eapply SPC with (LB := LBk) (LF := LF) (dX := dXk) (z := 0) (lo := lo) (slo := slo); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - LO0 LOSP SP64; lia).
      - exact HHk.
      - clear - LFB. lia.
      - exact XM.
      - intros EO. ddestruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk J T EO) as (_ & _ & P0 & _). exact P0.
      - clear; lia.
      - exact MIk.
      - pose proof (proj1 XAO) as OXk. rewrite XAD in OXk. rewrite ?XAD. exact OXk.
      - intros N1. pose proof (XNL N1) as EO. destruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk J T EO) as (IN & _).
        eapply hm_aobj_block; [exact HHk| exact IN].
      - rewrite XAD. exact XCR.
      - intros C. exfalso. exact (XNS C).
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact STk.
      - exact LOS.
      - clear - LOSP. lia.
      - clear - SLO2 NES NS1. lia.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact SS1.
      - exact SLO1.
      - clear - SLO3 LOSP. lia.
      - rewrite XAD. clear - DSX. lia.
      - intros N1. apply XLSq. rewrite (XNL N1). discriminate.
      - rewrite XAD. reflexivity.
      - reflexivity. }
    intros ms' PO. unfold mpi_cmp_int_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & h2 & E & MI2 & ST2 & HP2 & HCS2 & HT2 & HS2 & HF2 & HV2 & HFR2 & HK2 & HH2). subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by (clear - LO0 LOSP SP64; lia).
    rewrite (ret_pc_even RET HRET HRE).
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST2' by (clear; lia).
    assert (PK : presA asegs R (mpd_keep LBk dXk) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA hk) [] mk m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact (A_mpi_read_binary_stmt.In_mpd_keep _ _ _ Hb)| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x Hx; exact Hx]. }
    assert (MX2 : mpd_at asegs m2 LBk dXk).
    { eapply (mpd_at_heap_presx asegs (arl_L R) mk m2 LBk (LBk ++ fdata LF) LBk (bv_unsigned sp + -64) [] dXk XM (presA_presx asegs R _ _ _ _ _ _ _ _ HP2) MIk MI2).
      - eapply client_range_sep; [rewrite XAD; exact XCR| intros b Hb; exact Hb| rewrite XAD; clear - DSX; lia].
      - intros EO. pose proof (XLSq ltac:(rewrite EO; discriminate)) as K1.
        eapply client_range_sep; [exact (XCRL EO)| intros b Hb; exact Hb| clear - K1; lia].
      - exact I.
      - intros _. exact I.
      - intros b Hb. destruct (mpd_blk_heapE _ _ Hb) as [EO ->].
        destruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk J T EO) as (IN & _). exact IN. }
    assert (OA2 : aobj asegs AL (hcs asegs R HIA h2) m2 X 16).
    { eapply (ej_aobj_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC v f hk LBk mk X dXk m2 h2 (bv_unsigned sp + -64) _ J T (proj1 XW) ltac:(clear - LOSP LOS'; lia) PK).
      intros x Hx. rewrite HCS2. exact Hx. }
    assert (MC2 : exists c, rw_cells asegs m2 MC [C8 c]).
    { eapply (ej_mc_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk m2 (bv_unsigned sp + -64) _ J T PK). exact I. }
    assert (OUT2 : mpd_out LBk dXk LBk dXk).
    { unfold mpd_out. split; [reflexivity|]. split; [exact XNS|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb| intros b _ _; reflexivity]. }
    destruct (ej_call R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC v f hk LBk mk X dXk m2 h2 LBk dXk (bv_unsigned sp + -64) 0 0 [] J T
                ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) MI2 ST2' PK (fun x _ => I) I ltac:(clear - LOSP; lia)
                HT2 HS2 HF2 ltac:(intros x Hx; rewrite HCS2; exact Hx) ltac:(rewrite HV2; clear; lia) ltac:(rewrite HFR2; clear; lia)
                HH2 MX2 OUT2 (fun b Hb => or_introl Hb) OA2 MC2) as [J2 T2].
    rewrite !Z.add_0_r in J2.
    assert (S2 : SRI v f h2 LBk m2 dXk) by (constructor; [exact J2| exact T2| exact COV| exact PAD]).
    intros mo1 [HKm MFm].
    refine (K h2 m2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 S2 mo1 _).
    split; [apply HK2; exact HKm| exact MFm].
    all: match goal with |- ?g => idtac "CMPI-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0@L12283411672.174L14106684376.174L17645738372.1  L20181524131.1  L26892418956.1  L29311425660.4  L35663928186.7  L35693534892.2  L36674788157.8  L38041015762.4  L40229485618.1  L41288976216.174L44866992728.174L48429268312.174L5145216728.174 L59673527198.3  L60098763854.3  L61063055714.9  L67158371251.174L8722184664.174 Q15645341323.178Q18359718027.178Q21890219752.178Q27909213544.178Q31256953867.178Q32657489291.178Q33911823336.178Q36436182120.178Q3836573544.178 Q39937631848.178Q41141761931.178Q44655022603.178Q51221294859.178Q59828537611.178Q66536663272.178Q9837151720.178 00000>00L00P00T00X00h01=01D01[01g01k02902G02U02c02l03603P03^03l04:04H04Z04l05:05H05Z05l06>06P06^06l07:07H07Z07lS2LF2ra2sp3LFBS2LF2ra2sp3LFBS2spS2spS2spS2nX3dXk3NX03NRkS1R3HIA1h2sp2lo3TOP1HS1G3GMCS1R3HIA1h1N1v2hk2HV3HVkS2sp2lo4LOSPS2spS2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LF2ra2sp3LFBS1X1G3OS1S1R2lo3LOSS1R3HIA1h1N1d1f2hk2HF4HFRkS2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LF2sp2lo3LFBS2LF2sp2lo3LFBS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFBS2LF2sp2lo3LFBS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFBS2LF2sp2lo3LFBS2LF2sp2lo3LFBS2LF2sp2lo3LFBS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFB3SLO". (* [comment removed for export] *)
  #[using="IMG EC GRP OSEP MX0 XW SLO2 LFB"] Lemma sr_exit : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pr,$0.Pxra,(17.&40.)Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pxs0',(17.&40.)Pxs1,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pxs2,(17.&40.)Pxs3,(17.&40.)Pxs4,(17.&40.)Pxs5,(17.&40.)Pxs6,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)P,(1;.R1=.R1<.R1;.R1:.R19.R18.)P,(1.(>.(52.(?.+2.+1?.))R18.)(2.R18.=))P,(2.R1?.(9.VN,))P,(2.R1?.(:.VN,Vd,))P,(2.(3:.R1<.)(;.VN,))(1?.$5.(20.$5.VR,VHIA,R20.Vmo,)$65.(21.(22.R1;.(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R1:.R19.R18.R17.R16.(23.&40.R1<.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(23.&40.+<>>30.)Vfc,(24.(17.&40.))R1>.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS').
    intros until xt6. intros S HR HV HF HSZ. basic_factsA hk.
    pose proof S as [J T COV PAD]. pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose T as (MYk & EAk & NSk & FRSk & OAk).
    dpose GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    dpose OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    assert (DXG : disjoint_from XO G 192) by (cbn [disjoint_from fst snd]; split; [clear - OS1; lia| split; [clear - GMC; lia| exact I]]).
    pose proof (ej_grp_pre R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC MT v f hk LBk mk G g (bv_unsigned sp) d J GRP DXG ltac:(clear; lia)) as (GATk & _).
    pose proof (hm_top asegs R HIA hk LBk LF mk HHk) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HSk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (stk_release asegs mk lo (bv_unsigned sp - 64) SR_FRAME STk FRk ltac:(clear - LOSP LO0; lia)) as STR.
    unfold SR_FRAME in FRk, STR. cbn [cells_size csize Nat.add] in STR. replace (bv_unsigned sp - 64 + Z.of_nat 64) with (bv_unsigned sp) in STR by (clear; lia).
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in FRk, STk by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    pose proof (conj MCk I) as MCbox. pose proof (conj GATk I) as GRbox. pose proof (conj MYk I) as MXbox. clear S J T MYk MCk GATk.
    do 8 zstep.
    zstep.
    replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold SR_POST, ecp_mul_mod_postA.
    destruct MCbox as [MC1' _]. destruct GRbox as [GR1' _]. destruct MXbox as [MX1' _].
    pose proof MX0 as [(_ & _ & _ & _ & _ & OW0) _]. cbn [md_own md_n md_p] in OW0. destruct OW0 as [_ NX0].
    pose proof MX1' as [(_ & _ & _ & _ & NRk & _) _].
    deexists 14. dexists mk, mo9, hk, LBk, dXk, r, ck.
    split; [reflexivity|]. split; [exact MIk|]. split; [exact STR|]. split; [exact MF9|]. split; [exact PXk|].
    split; [exact HTk|]. split; [exact HSk|]. split; [exact HFk|]. split; [exact HK9|]. split; [exact HCSk|].
    split; [clear - HVk HV; lia|]. split; [clear - HFRk HF; lia|]. split; [exact HHk|]. split; [exact MX1'|].
    split; [split; [exact EAk| split; [exact NSk| split; [exact COV| split; [intros b Hb _; exact (SUBk b Hb)| intros b Hb; destruct Hb]]]]|].
    split; [intros b Hb; right; exact (proj2 (FRSk b Hb))|].
    split; [exact GR1'|]. split; [exact MC1'|].
    split; [| exact HSZ].
    split; [exact HR|]. split; [exact EAk|]. split; [exact PAD|]. split; [intros b Hb; right; exact (proj1 (FRSk b Hb))|].
    cbn [md_n]. clear - NX0 NRk. lia.
    all: match goal with |- ?g => idtac "EXIT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L14228548876.5L35693534892.2L59673527198.300000@00G00PS1R1G3off2O13GU1S1G3GMCS1X1G3OS1". (* [comment removed for export] *)
  #[using="IMG MT ra s0 s1 s2 s3 s4 s5 s6 sX nX pX xs0 padX EC GRP OSEP MX0"] Lemma sr_fld : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pe,$19.Poff,$0.P,(66.$19.R2.(67.Vg,))P,(1<.$0.(31.R3.)(11.VG,R2.))P,(2.=R3.)P,(2.(11.R4.+10.)+<0.)P,(10.(1<.$0.(68.R6.)+1.)(1<.$0.(68.R6.)-1.))(1.(60.VR,VHIA,Vh,VLB,VLF,Vm,(=.&40.Vsp,)Vlo,(59.(5:.$0.$0.)(5;.$0.$0.VX,(11.VX,+10.))(59.(5:.$0.$0.)(5;.$0.$0.$8.(11.$8.+8.))(5<.(5:.$0.$0.))))VX,R7.)(46.VR,(31.R7.)+10.Vd,))")
(* [comment removed for export] *).
  Proof.
    intros e off He EAD O0 O1 ESG.
    dpose GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    dpose OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    assert (DXG : disjoint_from XO G 192) by (cbn [disjoint_from fst snd]; split; [clear - OS1; lia| split; [clear - GMC; lia| exact I]]).
    pose proof MX0 as [(CX & _) _]. cbn [md_addr] in CX.
    split.
    - eapply (ej_grp_ext R HIA IMG h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC MT G g d X e off _ GRP DXG He EAD O0 O1 ESG OS1 CX). reflexivity.
    - rewrite EAD. destruct GUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1 O1; lia| exact GU2]| right; exact GU].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L28553454490.0L39332637397.0000001002SS". (* [comment removed for export] *)
  #[using="IMG MT ra s0 s1 s2 s3 s4 s5 s6 sX nX pX xs0 padX G EC GRP OSEP MX0"] Lemma sr_P_ext : ej_ext R HIA h LB LF m (bv_unsigned sp) lo XO X (g_P g) /\ uw_obj R (md_addr (g_P g)) 16 d.
  Proof.
    dpose GRP as (GAT & _ & GPS & _). dpose GAT as (_ & _ & _ & EP & _).
    eapply (sr_fld (g_P g) 8); [unfold grp_mpds; left; reflexivity| exact EP| clear; lia| clear; lia| left; exact GPS].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39076636629.0L55570919066.0000001002SS". (* [comment removed for export] *)
  #[using="IMG MT ra s0 s1 s2 s3 s4 s5 s6 sX nX pX xs0 padX G EC GRP OSEP MX0 SGA"] Lemma sr_A_ext : ej_ext R HIA h LB LF m (bv_unsigned sp) lo XO X (g_A g) /\ uw_obj R (md_addr (g_A g)) 16 d.
  Proof.
    pose proof GRP as (GAT & _). dpose GAT as (_ & _ & _ & _ & EA & _).
    eapply (sr_fld (g_A g) 24); [unfold grp_mpds; right; left; reflexivity| exact EA| clear; lia| clear; lia| left; exact SGA].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38820635861.0L59974880666.0000001002SS". (* [comment removed for export] *)
  #[using="IMG MT ra s0 s1 s2 s3 s4 s5 s6 sX nX pX xs0 padX G EC GRP OSEP MX0 SGB"] Lemma sr_B_ext : ej_ext R HIA h LB LF m (bv_unsigned sp) lo XO X (g_B g) /\ uw_obj R (md_addr (g_B g)) 16 d.
  Proof.
    pose proof GRP as (GAT & _). dpose GAT as (_ & _ & _ & _ & _ & EB & _).
    eapply (sr_fld (g_B g) 40); [unfold grp_mpds; right; right; left; reflexivity| exact EB| clear; lia| clear; lia| left; exact SGB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L13688701875.2L32569056601.3L53711973945.3L8426021307.7 00000800B00J00cS2dA3AMCS1X2dA3SXAS1X2dA1KS1R2dA3DI13DI23MC13MC22BI". (* [comment removed for export] *)
  #[using="ra s0 s1 s2 s3 s4 s5 s6 sX nX pX xs0 padX EC EXTA"] Lemma sr_dA_ext : ej_ext R HIA h LB LF m (bv_unsigned sp) lo XO X dA /\ uw_obj R (md_addr dA) 16 d.
  Proof.
    ec_open. ddestruct EXTA as (MA & SXA & OA & CRA & CRAL & AMC & OAA & IMA & UWA). cbn [md_addr] in SXA.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). cbn [md_addr md_own md_p md_n] in OA1.
    ddestruct MCOK as (MC1 & MC2 & _).
    split; [| exact UWA]. unfold ej_ext.
    split; [exact MA|]. split; [exact CRA|]. split; [exact OA4|]. split; [exact OA5|].
    split; [cbn [disjoint_from fst snd]; split; [clear - SXA; lia| split; [clear - AMC; lia| exact I]]|].
    split.
    { intros EO. pose proof MA as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. ddestruct OW as (N1 & IN & _).
      destruct (hm_apart asegs R HIA h LB LF m HH) as [HF0 _]. rewrite Forall_forall in HF0.
      destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (_ & _ & _ & BI). cbn [fst snd] in BI.
      cbn [disjoint_from fst snd]. split; [pose proof (OA1 ltac:(rewrite EO; discriminate)) as K; clear - K; lia|].
      split; [destruct DIMG as [DI1 DI2]; clear - BI MC1 MC2 DI1 DI2; lia| exact I]. }
    split; [exact SXA|]. split; [exact OA1|]. split; [exact OAA| exact IMA].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation dP := (g_P g).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L15184440848.72L9666687772.72 00000E00ZS2LF2ra2sp3LFB1a1b2LTS2LF2ra2sp3LFB1a1b2GT". (* [comment removed for export] *)
  #[using="LF ra sp LFB"] Lemma sgn_cases : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pa,$0.Pb,$0.(10.(1.(1<.$0.(61.(<.R2.R1.))-1.)(>.R2.R1.))(10.(1.(1<.$0.(61.(<.R2.R1.))=)(1<.$0.R2.R1.))(1.(1<.$0.(61.(<.R2.R1.))+1.)(>.R1.R2.))))")
(* [comment removed for export] *).
  Proof. intros a b. destruct (Z.compare_spec a b) as [E|LT|GT]; [right; left; split; [rewrite E, Z.sub_diag; reflexivity| exact E]| left; split; [apply Z.sgn_neg; lia| exact LT]| right; right; split; [apply Z.sgn_pos; lia| exact GT]]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L14674883745.0  L23447727684.0  L2397676628.0   L26604177103.8  L29010569984.185L2965695311.7   L29956516996.0  L39280637297.0  L42848429313.4  L42848462470.4  L46089397449.0  L50667210948.0  L59107603233.0  L59308665200.5  L59308665200.6  L59308698359.5  L59308698359.6  L61441268058.5  L6929933546.6   L6929966957.6   00000100200300J00K00_00`00a00n01;01<01=01>01P01Q01c01d02702H02YSFSS1R3HIA1h1N1d4BUDF1f2HFFS1R3HIA1h1N3BUD1v2HVSSS1g2VP3dXk2GTS1g2VP3dXk2EQSSSS1g2VP3dXk4HVAL2EQFS1g2VP3dXk4HVAL2GTFS1N3dXk3HSZ3dX23SZ2S1g2VP1n3dXk4HVALS1g1n3dXk4HVAL2EQ". (* [comment removed for export] *)
  #[using="IMG HSUBANG EC TPV UWX GRP OSEP MX0 XW VP SLO2 SPA BUD BUDF LFB"] Lemma sr_loop3 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pn,$43.Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pxra,(17.&40.)Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pxa0,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pxs2,(17.&40.)Pxs3,(17.&40.)Pxs4,(17.&40.)Pxs5,(17.&40.)Pxs6,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)P,(1;.R1;.R1:.R19.R18.R17.R16.)P,(2.(62.R17.)(69.R1=.))P,(2.R1=.(9.VN,))P,(2.R1=.(:.VN,Vd,))P,(2.(3:.R1:.)(;.VN,))(1?.$5.(20.$5.VR,VHIA,R1>.Vmo,)$65.(21.(22.R1:.(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R19.R18.R17.(23.&40.VX,)(23.&40.(31.(54.Vg,)))R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(23.&40.+<>?60.)Vfc,(24.(17.&40.))R1<.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until xt6; intros S HVAL HV HF HSZ.
    all: ec_open; dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS'); basic_factsA hk;
         destruct sr_P_ext as [PEXT PUW];
         pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV;
         pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM;
         pose proof (conj S I) as Sbox; clear S.
    all: zstep; zstep; zstep.
    all: destruct Sbox as [S _].
    all: eapply (sr_cmp v f hk LBk mk dXk dP 0xcef6c); [exact S| exact PEXT| clear; lia| reflexivity| | reflexivity].
    all: intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S'.
    all: destruct (sgn_cases (mpd_val dXk) (mpd_val dP)) as [[SG LT]|[[SG EQ]|[SG GT]]]; rewrite SG.
    all: try (exfalso; cbn [Z.of_nat] in HVAL; first [clear - HVAL VP EQ; lia | clear - HVAL VP GT; lia]; fail).
    all: clear MU WM; pose proof (munch_refl ([] : list ivl) m') as MU; pose proof (wmono_refl asegs m') as WM.
    all: pose proof (conj S' I) as Sbox'; clear S S'.
    1, 2: zstep; zstep; zstep; destruct Sbox' as [S' _];
          (eapply (sr_exit v f hk LBk m' dXk 0); [exact S'| clear; lia| exact HV| exact HF| exact HSZ]).
    all: zstep; zstep; zstep; zstep; zstep.
    all: destruct Sbox' as [S' _].
    all: ddestruct (sr_opX v f hk LBk m' dXk S') as (XM & XNS & XAD & _).
    all: eapply (sr_binop_ng A_MPI_SUB_ABS _ _ _ HSUBANG v f hk LBk m' dXk dXk dP 0xcef80);
         [exact S'| left; reflexivity| right; exact PEXT| exact (proj1 (proj2 (sr_opnd v f hk LBk m' dXk dP S' (or_intror PEXT))))| rewrite XAD; exact UWX| exact PUW
         | clear; lia| cbv beta; apply Z.le_refl
         | pose proof (mod_mpi_PHIn_nonneg 0 0 ltac:(clear; lia) ltac:(clear; lia)) as _; clear - HV BUD; lia| clear - HF BUDF; lia| clear; lia| reflexivity
         | intros r0 dX0' [[_ BK0] _]; exact BK0| | rewrite XAD; reflexivity| reflexivity].
    all: intros h2 LB2 m2 dX2 r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S2 [[RV BK2] SZ2].
    all: clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
         pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    all: pose proof (conj S2 I) as Sbox2; clear S2.
    all: zstep; if_cases KR; zify_cond KR; destruct Sbox2 as [S2 _].
    all: dpose GRP as (_ & _ & GPS & _); pose proof (P_ecp_sw_rhs.mpd_val_sg1 dP GPS) as VPA.
    all: assert (XPOS : mpd_abs dXk = mpd_val dXk) by (destruct (P_ecp_sw_rhs.mpd_val_pos_abs dXk (proj2 XM) ltac:(first [clear - VP EQ; lia | clear - VP GT; lia])) as [K _]; exact K).
    1, 3: (destruct RV as [(R0 & RVAL & _)|[RF|[RF _]]];
           [| exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; discriminate KR
            | exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_NEGATIVE_VALUE in KR; vm_compute in KR; discriminate KR];
           eapply (IH v f h2 LB2 m2 dX2); [exact S2| rewrite RVAL, XPOS, <- VPA; first [clear - HVAL VP EQ; lia | clear - HVAL VP GT; lia]| exact HV| exact HF| clear - SZ2 HSZ; lia]).
    all: zstep.
    all: eapply (sr_exit v f h2 LB2 m2 dX2 r); [exact S2| | exact HV| exact HF| clear - SZ2 HSZ; lia].
    all: destruct RV as [(R0 & _)|[RF|[RF _]]]; subst r; first [exfalso; apply KR; reflexivity | unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia | unfold MBEDTLS_ERR_MPI_NEGATIVE_VALUE; clear; lia].
    all: match goal with |- ?g => idtac "LOOP3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation EZ := (ecp_sz N).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L29349923730.1100000SS2dA1g1N2NA3NA02NP3NAg3NBg2N12N22N3". (* [comment removed for export] *)
  #[using="R HIA MT h LB LF m sp X sX nX pX xs0 padX G lo d GRP EXTA NLE NA"] Lemma sr_sizes : 0 <= N /\ 0 <= md_n dA /\ 0 <= md_n dP <= N /\ 0 <= md_n (g_A g) <= N /\ 0 <= md_n (g_B g) <= N.
  Proof.
    destruct EXTA as (MA & _). pose proof MA as [(_ & _ & _ & _ & NA0 & _) _].
    pose proof GRP as (GAT & _). dpose GAT as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & NP & _) & (_ & _ & _ & _ & NAg & _) & (_ & _ & _ & _ & NBg & _) & _).
    ddestruct NLE as (N1 & N2 & N3). clear - NA0 NP NAg NBg N1 N2 N3 NA. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@L10470257411.196L14556351945.0  L16106703178.8  L18865000865.0  L19806849779.2  L19808960241.5  L24026654016.13 L24026817857.12 L29010569984.165L29331976539.9  L29699359420.6  L29770752369.3  L29770752369.6  L29956516996.0  L41053667674.2  L41550010864.12 L42846217080.2  L46370743117.8  L46947521211.8  L46947619916.10 L48038176869.10 L51311702794.12 L52192842782.8  L52248105850.2  L52547738034.8  L55832289796.1  L59124818608.2  L6106346273.0   L61801965447.8  L64587340256.13 L64732282853.10 L9185298818.9   00000100200L00M00S00^01G01k01l02I02U02a02m02n03603[03d04204;04D04V05<05U05^06506:06@06A06M07507E07`FSS1g1N3NBg3dX24SZ2'3dX33SZ3SS1N2N0S1g3dX23NX2S1R3HIA1h2dA1g1N3BUD1v3dXk2HV3PM13dX23PM2S1R3HIA1h2dA1g1N1d4BUDF1f3dXk2HF3FM1FS2dA1g1N1v3dXk2HV3PM13dX23PM2S1g1N2N03NBgS1N3dX24SZ2'S1N3dX24SZ2'SS2LF3LFBS1R3HIA1h2dA1g1N3BUD1v3dXk2HV3PM13AP0S3dXk3NXkS1N2N03dXk3HSZS1g1N3NP0S1g1N3NP0S1N2N03dXk3HSZ3NXkS2dA1g1N2NA2N03NA03NP03dXk3HSZ3dX23SZ2S2dA1g1N1v3dXk2HV3PM13AP0S2LB4C24HS2dA1g1N1d1f3dXk2HF3FM1S3dX3S1d2D0SS2dA1N2NA2N0S1R3HIA1h2dA1g1N1d4BUDF1f3dXk2HF3FM13AF0S2dA1N2NA2N03NA0S2dA1g1N1d1f3dXk2HF3FM13AF0". (* [comment removed for export] *)
  #[using="IMG HMM HADD HSUBANG slo EC TPV UWX D0 GRP OSEP MX0 XW EXTA SGB VP NLE NA SLO2 SPA SSH SLO1 SLO3 BUD BUDF C24H LFB"] Lemma sr_tail : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pxra,(17.&40.)Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pxa0,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pxs3,(17.&40.)Pxs4,(17.&40.)Pxs5,(17.&40.)Pxs6,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)P,(1;.R1:.R19.R18.R17.R16.R15.)P,(2.(3:.R16.)(11.(39.+2.VN,)+5.))P,(2.(11.R1<.(11.(53.(;.VN,)(;.VN,)(;.VN,)VN,)(6:.(;.VN,)(;.VN,))))(9.VN,))P,(2.(11.R1<.(11.(3.(;.VN,)(;.VN,)(;.VN,)VN,Vd,)(6;.Vd,)))(:.VN,Vd,))(1?.$5.(20.$5.VR,VHIA,R1<.Vmo,)$65.(21.(22.R18.(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R17.R16.R15.(23.&40.VX,)(23.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.(23.&40.(31.VdA,))R<.R;.R:.R9.Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(23.&40.+<>?30.)Vfc,(24.(17.&40.))R1:.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS'). dpose sr_sizes as (N0 & NA0 & NP0 & NAg & NBg).
    intros until xt6. intros S HSZ HV HF.
    destruct sr_dA_ext as [AEXT AUW]. destruct sr_B_ext as [BEXT BUW].
    pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & _). pose proof XM as [(_ & _ & _ & _ & NXk & _) _].
    pose proof (conj S I) as Sbox; clear S.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    destruct Sbox as [S _].
    assert (PM1 : mm_PHIn (md_n dXk) (md_n dXk) (md_n dA) (md_n dP) <= mm_PHIn EZ EZ EZ N) by (apply mm_PHIn_mono; unfold ecp_sz; clear - HSZ NA NP0 N0; lia).
    assert (FM1 : mm_FRn (md_n dXk) (md_n dXk) (md_n dA) (md_n dP) d <= mm_FRn EZ EZ EZ N d) by (apply mm_FRn_mono; unfold ecp_sz; first [exact D0 | clear - HSZ NA NP0 N0 NXk NA0; lia]).
    assert (AP0 : 0 <= addsub_PHIn EZ EZ) by (unfold addsub_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; clear - N0; lia).
    assert (AF0 : 0 <= addsub_FRn d) by (unfold addsub_FRn, calls_FR, fr_charge; clear - D0; lia).
    eapply (sr_mulmod v f hk LBk mk dXk dXk dA 0xcef44);
      [exact S| left; reflexivity| right; exact AEXT| exact (proj1 (proj2 (sr_opnd v f hk LBk mk dXk dA S (or_intror AEXT))))| rewrite XAD; exact UWX| exact AUW
      | clear - NXk; lia| clear - NXk; lia| exact NA0
      | clear - HV PM1 AP0 BUD; lia| clear - HF FM1 AF0 BUDF; lia| clear; lia| reflexivity| | rewrite XAD; reflexivity| reflexivity].
    intros h2 LB2 m2 dX2 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S2 [RR BK2] SZ2.
    clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
      pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    assert (SZ2' : md_n dX2 <= 3 * N + 7) by (unfold mm_nz, mul_mpi_nz in SZ2; clear - SZ2 HSZ NA NP0 N0 NXk NA0; lia).
    pose proof (conj S2 I) as Sbox2; clear S2.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR; destruct Sbox2 as [S2 _].
    - eapply (sr_exit _ _ h2 LB2 m2 dX2 r); [exact S2| exact RR| clear - HV PM1 AP0; lia| clear - HF FM1 AF0; lia| unfold ecp_sz; clear - SZ2'; lia].
    - destruct (sr_opX _ _ h2 LB2 m2 dX2 S2) as (XM2 & XNS2 & XAD2 & _). pose proof XM2 as [(_ & _ & _ & _ & NX2 & _) _].
      pose proof GRP as (GAT & _). dpose GAT as (_ & _ & _ & _ & _ & EB & _).
      pose proof (conj S2 I) as Sbox2; clear S2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      destruct Sbox2 as [S2 _].
      assert (PM2 : addsub_PHIn (md_n dX2) (md_n (g_B g)) <= addsub_PHIn EZ EZ) by (apply addsub_PHIn_mono; unfold ecp_sz; clear - SZ2' NBg N0; lia).
      eapply (sr_binop A_MPI_ADD_MPI _ _ _ _ _ _ HADD _ _ h2 LB2 m2 dX2 dX2 (g_B g) 0xcef58);
        [exact S2| left; reflexivity| right; exact BEXT| exact (proj1 (proj2 (sr_opnd _ _ h2 LB2 m2 dX2 (g_B g) S2 (or_intror BEXT))))| rewrite XAD2; exact UWX| exact BUW
        | clear; lia| clear - LFB; lia
        | cbv beta; unfold addsub_PHIn, grow_PHI; unfold AVOL_CALL; clear - NX2 NBg; lia| cbv beta; exact AF0
        | cbv beta; clear - HV PM1 PM2 BUD; lia| cbv beta; clear - HF FM1 BUDF; lia
        | unfold C24_ADDSUB, C24_ECP_SW_RHS in *; clear - C24H; lia| clear; lia| reflexivity
        | intros r0 dX0' [[_ BK0] _]; exact BK0| | rewrite XAD2; reflexivity| rewrite EB; reflexivity].
      cbv beta. intros h3 LB3 m3 dX3 r3 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S3 [[RV3 BK3] SZ3].
      clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo) as KINV;
        pose proof (munch_refl ([] : list ivl) m3) as MU; pose proof (wmono_refl asegs m3) as WM.
      assert (SZ3' : md_n dX3 <= EZ) by (unfold addsub_nz in SZ3; unfold ecp_sz; clear - SZ3 SZ2' NBg N0; lia).
      pose proof (conj S3 I) as Sbox3; clear S3.
      (* [comment removed for export] *)
      zstep. if_cases KR3; zify_cond KR3; destruct Sbox3 as [S3 _].
      + eapply (sr_exit _ _ h3 LB3 m3 dX3 r3); [exact S3| | clear - HV PM1 PM2; lia| clear - HF FM1; lia| exact SZ3'].
        destruct RV3 as [(R0 & _)|RF]; subst r3; [exfalso; apply KR3; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia].
      + (* [comment removed for export] *)
        pose proof GRP as (GAT' & _). dpose GAT' as (_ & _ & _ & EP & _).
        zstep. rewrite <- EP.
        eapply (sr_loop3 (Z.to_nat (Z.max 0 (mpd_val dX3))) _ _ h3 LB3 m3 dX3); [exact S3| clear; lia| clear - HV PM1 PM2; lia| clear - HF FM1; lia| exact SZ3'].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L18397519197.5  L23447727684.0  L26601852921.9  L27694950586.5  L28442596129.0  L29010569984.190L2967661161.8   L29772846442.6  L29956516996.0  L31099715771.4  L42848429313.4  L42848462470.4  L46089397449.0  L48303896707.2  L48823579041.0  L50181624331.3  L50667210948.0  L59308665200.5  L59308665200.6  L59308698359.5  L59308698359.6  L6929933546.6   L6929966957.6   L9763814982.4   00000>00?00Z00m00n00o01G01]01^01h02502B02C02I02J02R02S02e02f03803903J03[03gS1N1d1f2HF3FT0FS1R3HIA1h1N1d4BUDF1f2HF3FT0S1N3dXk3HSZ3dX23SZ2SFS1R3HIA1h1N3BUD1v2HV3PT0S1N3dXk3HSZ2N03dX23SZ2SS1N1d2D01HS1g2VP3dXk2GTS1g2VP3dXk2EQSS1N2N0SS1N2N01HSS1g2VP3dXk4HVAL2EQFS1g2VP3dXk4HVAL2GTFS1g2VP1n3dXk4HVALS1g1n3dXk4HVAL2EQS1N1v2HV3PT0". (* [comment removed for export] *)
  #[using="IMG HMM HADD HSUBANG slo EC TPV UWX D0 GRP OSEP MX0 XW EXTA SGB VP NLE NA SLO2 SPA SSH SLO1 SLO3 BUD BUDF C24H LFB"] Lemma sr_loop1 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pn,$43.Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pxra,(17.&40.)Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pxa0,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pxs4,(17.&40.)Pxs5,(17.&40.)Pxs6,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)P,(1;.R19.R18.R17.R16.R15.R14.)P,(2.(62.R15.)(69.R1;.))P,(2.(11.R1;.(11.(53.(;.VN,)(;.VN,)(;.VN,)VN,)(6:.(;.VN,)(;.VN,))))(9.VN,))P,(2.(11.R1;.(11.(3.(;.VN,)(;.VN,)(;.VN,)VN,Vd,)(6;.Vd,)))(:.VN,Vd,))P,(2.(3:.R18.)(11.(39.+2.VN,)+5.))(1?.$5.(20.$5.VR,VHIA,R1<.Vmo,)$65.(21.(22.R18.(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R17.R16.R15.(23.&40.VX,)(23.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.(23.&40.(31.VdA,))(23.&40.(31.(54.Vg,)))R<.R;.R:.Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(23.&40.+<>>90.)Vfc,(24.(17.&40.))R1:.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until xt6; intros S HVAL HV HF HSZ.
    all: ec_open; dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS'); dpose sr_sizes as (N0 & NA0 & NP0 & NAg & NBg); basic_factsA hk;
         assert (PT0 : 0 <= mm_PHIn EZ EZ EZ N + addsub_PHIn EZ EZ) by (unfold mm_PHIn, red_PHIn, mul_mpi_PHIn, addsub_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N0; lia) N0); clear - H N0; lia);
         assert (FT0 : 0 <= mm_FRn EZ EZ EZ N d + addsub_FRn d) by (unfold mm_FRn, red_FRn, mul_mpi_FRn, addsub_FRn, calls_FR, fr_charge, ecp_sz; pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N d ltac:(unfold mul_mpi_nz; clear - N0; lia) D0); clear - H D0; lia);
         destruct sr_P_ext as [PEXT PUW];
         pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV;
         pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM;
         pose proof (conj S I) as Sbox; clear S.
    all: zstep; zstep; zstep.
    all: destruct Sbox as [S _].
    all: eapply (sr_cmp v f hk LBk mk dXk dP 0xcee9c); [exact S| exact PEXT| clear; lia| reflexivity| | reflexivity].
    all: intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S'.
    all: destruct (sgn_cases (mpd_val dXk) (mpd_val dP)) as [[SG LT]|[[SG EQ]|[SG GT]]]; rewrite SG.
    all: try (exfalso; cbn [Z.of_nat] in HVAL; first [clear - HVAL VP EQ; lia | clear - HVAL VP GT; lia]; fail).
    all: clear MU WM; pose proof (munch_refl ([] : list ivl) m') as MU; pose proof (wmono_refl asegs m') as WM.
    all: pose proof (conj S' I) as Sbox'; clear S S'.
    1, 2: zstep; destruct Sbox' as [S' _];
          (eapply (sr_tail v f hk LBk m' dXk); [exact S'| exact HSZ| exact HV| exact HF]).
    all: zstep; zstep; zstep; zstep; zstep.
    all: destruct Sbox' as [S' _].
    all: ddestruct (sr_opX v f hk LBk m' dXk S') as (XM & XNS & XAD & _).
    all: eapply (sr_binop_ng A_MPI_SUB_ABS _ _ _ HSUBANG v f hk LBk m' dXk dXk dP 0xceeb0);
         [exact S'| left; reflexivity| right; exact PEXT| exact (proj1 (proj2 (sr_opnd v f hk LBk m' dXk dP S' (or_intror PEXT))))| rewrite XAD; exact UWX| exact PUW
         | clear; lia| cbv beta; apply Z.le_refl
         | clear - HV BUD PT0; lia| clear - HF BUDF FT0; lia| clear; lia| reflexivity
         | intros r0 dX0' [[_ BK0] _]; exact BK0| | rewrite XAD; reflexivity| reflexivity].
    all: intros h2 LB2 m2 dX2 r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S2 [[RV BK2] SZ2].
    all: clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
         pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    all: pose proof (conj S2 I) as Sbox2; clear S2.
    all: zstep; if_cases KR; zify_cond KR; destruct Sbox2 as [S2 _].
    all: dpose GRP as (_ & _ & GPS & _); pose proof (P_ecp_sw_rhs.mpd_val_sg1 dP GPS) as VPA.
    all: assert (XPOS : mpd_abs dXk = mpd_val dXk) by (destruct (P_ecp_sw_rhs.mpd_val_pos_abs dXk (proj2 XM) ltac:(first [clear - VP EQ; lia | clear - VP GT; lia])) as [K _]; exact K).
    1, 3: (destruct RV as [(R0 & RVAL & _)|[RF|[RF _]]];
           [| exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; discriminate KR
            | exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_NEGATIVE_VALUE in KR; vm_compute in KR; discriminate KR];
           eapply (IH v f h2 LB2 m2 dX2); [exact S2| rewrite RVAL, XPOS, <- VPA; first [clear - HVAL VP EQ; lia | clear - HVAL VP GT; lia]| exact HV| exact HF| clear - SZ2 HSZ; lia]).
    all: zstep.
    all: eapply (sr_exit v f h2 LB2 m2 dX2 r); [exact S2| | clear - HV PT0; lia| clear - HF FT0; lia| unfold ecp_sz; clear - SZ2 HSZ N0; lia].
    all: destruct RV as [(R0 & _)|[RF|[RF _]]]; subst r; first [exfalso; apply KR; reflexivity | unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia | unfold MBEDTLS_ERR_MPI_NEGATIVE_VALUE; clear; lia].
    all: match goal with |- ?g => idtac "LOOP3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac sr_merge_a0 c k HK :=
    lazymatch goal with
    | |- aevtA ?segs (KF _ ?R0 ?HIA0 ?h0 ?mo0) ?Q (MS ?RR ?F0 (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc0 ?rv ?mm ?ro) =>
        let pk := eval vm_compute in (bv_key (Z_to_bv 5 10)) in
        eapply (aevtA_cut_evtA_KF segs R0 HIA0 h0 mo0 (fun ms' => exists vk : word, ms' = MS (tset pk vk RR) F0 (Z_to_bv 64 fast) fc0 rv mm ro));
        [ let Kz := fresh "Kz" in
          if_cases Kz; zify_cond Kz;
          [ shadow_merge_slow c k HK Kz; apply evtA_done; eexists; reflexivity
          | apply evtA_done; eexists; reflexivity ]
        | let ms' := fresh "ms'" in let vk := fresh "vk" in
          intros ms' (vk & ->); cbv beta iota delta [tset]; try clear HK; try clear k ]
    end.

  Local Notation AST := (addsub_PHIn EZ EZ).
  Local Notation TLP := (mm_PHIn EZ EZ EZ N + addsub_PHIn EZ EZ).
  Local Notation TLF := (mm_FRn EZ EZ EZ N d + addsub_FRn d).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00l0@L10413849587.6  L1358641953.0   L14556351945.0  L18397519197.5  L19806849779.2  L19808960174.5  L26466616993.0  L26601852921.10 L27694950586.5  L27694950586.7  L29010569984.210L29010569984.212L29331976539.6  L2967661161.9   L29699782311.6  L29770752369.4  L29772846442.6  L29956516996.0  L30912701369.3  L31099715771.4  L33708522798.3  L34488012184.1  L35813674810.5  L37600193098.5  L39564502624.7  L40882467136.3  L41053667674.2  L41550255730.11 L46356063461.6  L48303896707.2  L50181624331.3  L50930870522.4  L52248105850.2  L59124818608.2  L59308628179.4  L59308698359.4  L59315053158.3  L59315053158.4  L64587387104.9  L9763814982.4   Q22286193128.153Q22286193128.155Q22287729128.155Q22287729128.157Q22289915901.152Q22289915901.154Q39212284437.155Q39212284437.157Q4924309065.155 Q4924309065.157 Q54253883777.153Q54253883777.155Q56761401107.155Q56761401107.157Q60511567613.155Q60511567613.157Q63218990113.152Q63218990113.154Q9534654642.152 Q9534654642.154 00000F00G00H00V00\00g00h01H01\02602702802K02h03403C03Z03[03f04004<04A04P04d05;05@05H05k06:06@06H06S06\06b07107B07N07[08708C08M08W08a08k09509?09I09S09]09g0:10:;0:H0:U0:]0:e0:o0;90;A0;IS1g2VP1n3dXk3VPA5HABS2SSS1N1d1f2HF3FT0S1N2N0S1g3dXk3NXkSS1R3HIA1h1N1d4BUDF1f3HF23AF03FT0S1N3dXk4HSZ23dX23SZ2S1g1N3dXk3NP04HSZ23dX23SZ2FFS1g1N1v3dXk3HV23PM2S1R3HIA1h1N3BUD1v3HV23AP03PT0S1g1N2N03NP0S1N2N03dX24SZ2'S1N3dXk2N04HSZ23dX23SZ2SS1g3dXk3LTPS1N1d2D01HS3dX24ABS21CS3dXkS1N1d1f3HF23FT0S1N3dXk4HSZ23dX23SZ2S1g1N1v3dXk3HV23PT03PM2S3dX2S2LF3LFBS1R3HIA1h1g1N3BUD1v3dXk3HV23PT03PM2S1N3dXk2N04HSZ2S1N2N0S1N2N01HS1N1d1f3HF2S2LB4C24HS1d2D0S3dXk3VAL2LT2K0S3dXk3VAL4ABS02GTS3dX24POS21CS1g3dXk3GEP1CS1R3HIA1h1N1d4BUDF1f3HF23FT0S1N1v2HV3PT0S2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFBS2LF1X3LFB2X0S2LF1X3LFB2X0S2LF3LFBS2LF3LFBS2LF1X3LFBS2LF1X3LFBS2LF3LFBS2LF3LFB". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 HMM HADD HADDNG HSUBANG slo EC TPV UWX D0 GRP OSEP MX0 XW EXTA SGB VP NLE NA SLO2 SPA SSH SLO1 SLO3 BUD BUDF C24H LFB"] Lemma sr_loop2 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pn,$43.Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pxra,(17.&40.)Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pxa0,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)P,(1;.R16.R15.R14.R13.R12.R11.)P,P,(>.(62.R12.)=)(2.(6<.R13.)(69.R19.))P,(2.(11.R18.(11.(53.(;.VN,)(;.VN,)(;.VN,)VN,)(6:.(;.VN,)(;.VN,))))(9.VN,))P,P,(>.(62.R14.)=)(2.(11.R1:.(11.(6:.(;.VN,)(;.VN,))(11.(53.(;.VN,)(;.VN,)(;.VN,)VN,)(6:.(;.VN,)(;.VN,)))))(9.VN,))P,(2.(11.R19.(11.(3.(;.VN,)(;.VN,)(;.VN,)VN,Vd,)(6;.Vd,)))(:.VN,Vd,))P,P,(>.(62.R16.)=)(2.(11.R1;.(11.(6;.Vd,)(11.(3.(;.VN,)(;.VN,)(;.VN,)VN,Vd,)(6;.Vd,))))(:.VN,Vd,))P,(2.(3:.R17.)(11.(39.+2.VN,)+5.))P,P,(>.(62.R18.)=)(2.(3:.R19.)(11.(39.+2.VN,)+4.))(1?.$5.(20.$5.VR,VHIA,R1<.Vmo,)$65.(21.(22.R18.(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R17.R16.R15.(23.&40.VX,)(23.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.(23.&40.(31.VdA,))(23.&40.(11.VX,+8.))(23.&40.(31.(54.Vg,)))(23.&40.(11.(6=.(11.VX,+8.)+3.)(6>.(3>.VR,))))(23.&40.(11.(6?.(11.VX,+8.)+7.)+1.))Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(23.&40.+<>>><.)Vfc,(24.(17.&40.))R1:.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until xt6; intros S HABS HV HVn HF HFn HSZ HSZn.
    all: ec_open; dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS'); dpose sr_sizes as (N0 & NA0 & NP0 & NAg & NBg); basic_factsA hk;
         destruct sr_P_ext as [PEXT PUW];
         pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV;
         pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM;
         ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & _ & _ & _ & _ & _ & XAO & _);
         pose proof (proj1 XAO) as OXk; rewrite XAD in OXk;
         pose proof XM as [(CXk & _) SGk]; unfold mpi_cells in CXk; rewrite XAD in CXk;
         pose proof (hm_abase asegs R HIA hk LBk LF mk (ej_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sr_j _ _ _ _ _ _ S))) as AB;
         pose proof (conj S I) as Sbox; clear S.
    (* [comment removed for export] *)
    all: shadow_byte OXk (X + 8) 2 as k RD HKk.
    all: zstep; clear RD; zstep.
    all: sr_merge_a0 (X + 8) k HKk.
    (* [comment removed for export] *)
    all: zstep.
    all: destruct SGk as [SGk|SGk]; rewrite SGk.
    all: zstep.
    1, 3: destruct Sbox as [S _]; (eapply (sr_tail v f hk LBk mk dXk); [exact S| exact HSZ| exact HV| exact HF]).
    (* [comment removed for export] *)
    all: zstep; zstep; zstep.
    all: destruct Sbox as [S _].
    all: eapply (sr_cmpint v f hk LBk mk dXk 0xcef08); [exact S| clear; lia| reflexivity|].
    all: intros hq m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S'.
    all: assert (VAL : mpd_val dXk = - mpd_abs dXk) by (unfold mpd_val, mpd_abs; rewrite SGk; clear; lia).
    all: pose proof (P_ecp_sw_rhs.mpd_abs_nonneg dXk) as ABS0.
    all: destruct (sgn_cases (mpd_val dXk) 0) as [[SG LT]|[[SG EQ]|[SG GT]]]; rewrite SG; [| | exfalso; clear - GT VAL ABS0; lia].
    all: clear MU WM LAWS KINV; pose proof (AIh_laws asegs R HIA hq) as LAWS; pose proof (KF_kinv asegs R HIA hq mo) as KINV; pose proof (munch_refl ([] : list ivl) m') as MU; pose proof (wmono_refl asegs m') as WM.
    all: pose proof (conj S' I) as Sbox'; clear S S'.
    all: zstep.
    2, 4: destruct Sbox' as [S' _]; (eapply (sr_tail v f hq LBk m' dXk); [exact S'| exact HSZ| exact HV| exact HF]).
    1: exfalso; pose proof (HABS LT) as K0; cbn [Z.of_nat] in K0; clear - K0 VAL LT; lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct Sbox' as [S' _].
    ddestruct (sr_opX v f hq LBk m' dXk S') as (XM' & _ & XAD' & _). pose proof XM' as [(_ & _ & _ & _ & NXk & _) _].
    dpose GRP as (_ & _ & GPS & _). pose proof (P_ecp_sw_rhs.mpd_val_sg1 dP GPS) as VPA.
    pose proof (HVn LT) as HV2. pose proof (HFn LT) as HF2. pose proof (HSZn LT) as HSZ2. pose proof (HABS LT) as HABS2.
    assert (AP0 : 0 <= AST) by (unfold addsub_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; clear - N0; lia).
    assert (AF0 : 0 <= addsub_FRn d) by (unfold addsub_FRn, calls_FR, fr_charge; clear - D0; lia).
    assert (PT0 : 0 <= TLP) by (unfold mm_PHIn, red_PHIn, mul_mpi_PHIn, addsub_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N0; lia) N0); clear - H N0; lia).
    assert (FT0 : 0 <= TLF) by (unfold mm_FRn, red_FRn, mul_mpi_FRn, addsub_FRn, calls_FR, fr_charge, ecp_sz; pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N d ltac:(unfold mul_mpi_nz; clear - N0; lia) D0); clear - H D0; lia).
    destruct (Z_le_gt_dec (mpd_abs dP) (mpd_abs dXk)) as [GEP|LTP].
    - (* [comment removed for export] *)
      eapply (sr_binop_ng A_MPI_ADD_MPI _ _ _ HADDNG v f hq LBk m' dXk dXk dP 0xcef1c);
        [exact S'| left; reflexivity| right; exact PEXT| exact (proj1 (proj2 (sr_opnd v f hq LBk m' dXk dP S' (or_intror PEXT))))| rewrite XAD'; exact UWX| exact PUW
        | clear; lia| cbv beta; split; [rewrite GPS, SGk; reflexivity| split; [intros _; apply Z.le_refl| intros C; exfalso; clear - C GEP; lia]]
        | clear - HV2 BUD AP0 PT0; lia| clear - HF2 BUDF AF0 FT0; lia| clear; lia| reflexivity
        | intros r0 dX0' [[_ BK0] _]; exact BK0| | rewrite XAD'; reflexivity| reflexivity].
      intros h2 LB2 m2 dX2 r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S2 [[RV BK2] SZ2].
      clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
        pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      pose proof (conj S2 I) as Sbox2; clear S2.
      zstep. if_cases KR; zify_cond KR; destruct Sbox2 as [S2 _].
      + destruct RV as [(R0 & RVAL)|RF]; [| exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; discriminate KR].
        destruct (sr_opX v f h2 LB2 m2 dX2 S2) as (XM2 & _). pose proof (P_ecp_sw_rhs.mpd_abs_nonneg dX2) as ABS2.
        assert (NEG2 : mpd_val dX2 < 0 -> mpd_abs dX2 = - mpd_val dX2).
        { intros C. destruct (proj2 XM2) as [SG2|SG2]; unfold mpd_val, mpd_abs in *; rewrite SG2 in *; clear - C ABS2; lia. }
        eapply (IH v f h2 LB2 m2 dX2); [exact S2| | exact HV| intros _; exact HV2| exact HF| intros _; exact HF2| clear - SZ2 HSZ2; lia| intros _; clear - SZ2 HSZ2; lia].
        intros C. rewrite (NEG2 C), RVAL, VAL, VPA. rewrite Nat2Z.inj_succ in HABS2. clear - HABS2 VP VPA. lia.
      + zstep.
        eapply (sr_exit v f h2 LB2 m2 dX2 r); [exact S2| | clear - HV PT0; lia| clear - HF FT0; lia| unfold ecp_sz; clear - SZ2 HSZ2 N0; lia].
        destruct RV as [(R0 & _)|RF]; subst r; [exfalso; apply KR; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia].
    -
      assert (PM2 : addsub_PHIn (md_n dXk) (md_n dP) <= AST) by (apply addsub_PHIn_mono; unfold ecp_sz; clear - HSZ2 NP0 N0; lia).
      eapply (sr_binop A_MPI_ADD_MPI _ _ _ _ _ _ HADD v f hq LBk m' dXk dXk dP 0xcef1c);
        [exact S'| left; reflexivity| right; exact PEXT| exact (proj1 (proj2 (sr_opnd v f hq LBk m' dXk dP S' (or_intror PEXT))))| rewrite XAD'; exact UWX| exact PUW
        | clear; lia| clear - LFB; lia
        | cbv beta; unfold addsub_PHIn, grow_PHI; unfold AVOL_CALL; clear - NXk NP0; lia| cbv beta; exact AF0
        | cbv beta; clear - HV2 PM2 PT0 BUD; lia| cbv beta; clear - HF2 FT0 BUDF; lia
        | unfold C24_ADDSUB, C24_ECP_SW_RHS in *; clear - C24H; lia| clear; lia| reflexivity
        | intros r0 dX0' [[_ BK0] _]; exact BK0| | rewrite XAD'; reflexivity| reflexivity].
      cbv beta. intros h2 LB2 m2 dX2 r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S2 [[RV BK2] SZ2].
      clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
        pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      assert (SZ2' : md_n dX2 <= 2 * N + 5) by (unfold addsub_nz in SZ2; clear - SZ2 HSZ2 NP0; lia).
      pose proof (conj S2 I) as Sbox2; clear S2.
      zstep. if_cases KR; zify_cond KR; destruct Sbox2 as [S2 _].
      + destruct RV as [(R0 & RVAL)|RF]; [| exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; discriminate KR].
        assert (POS2 : 0 < mpd_val dX2) by (rewrite RVAL, VAL, VPA; clear - LTP; lia).
        eapply (IH _ _ h2 LB2 m2 dX2); [exact S2| intros C; exfalso; clear - C POS2; lia| clear - HV2 PM2; lia| intros C; exfalso; clear - C POS2; lia
                                      | clear - HF2; lia| intros C; exfalso; clear - C POS2; lia| exact SZ2'| intros C; exfalso; clear - C POS2; lia].
      + zstep.
        eapply (sr_exit _ _ h2 LB2 m2 dX2 r); [exact S2| | clear - HV2 PM2 PT0; lia| clear - HF2 FT0; lia| unfold ecp_sz; clear - SZ2' N0; lia].
        destruct RV as [(R0 & _)|RF]; subst r; [exfalso; apply KR; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia].
    all: match goal with |- ?g => idtac "LOOP2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0@L19806849779.2  L19808960174.2  L22890275614.2  L23333302074.2  L27688656033.3  L29010569984.161L29059358588.163L29331976546.5  L29331976546.6  L29770752369.4  L29956516996.0  L31099715771.4  L32449447369.0  L3260619388.7   L35813674810.6  L36062169889.0  L37600193098.6  L41550255691.11 L46370743117.4  L48303896707.2  L4952090732.2   L50181624331.3  L50928773326.4  L50930723064.5  L59124818608.2  L62948672147.2  L64587387104.10 L64770242407.0  00000600?00E00N00Z00[01401D01X01g01h02202302K02]02^03403X03f03l04104904C04Q04W04_05>05?S1N2N0S3dXk3NXkS1d2D0S2LB4C24HS1N3dX24SZ2'FS2LF2ra2sp1X3LFB2X03X161rS1N1v3dXk2HV3PMIS1N1v3dXk2HV3AP03PMIS1N2N03dX24SZ2'SS1N1d2D01HSS1N1v3dXk2HV3AP03PT03PMIS1N1d1f2HF3AF03FT0SS1N2N03dXk3HSZ3dX23SZ2S1R3HIA1h1N3BUD1v3dXk2HV3AP03PT03PMIS1N2N03dXk3HSZS1N2N0S3dX2S1N2N01HS1N1d1f2HFS1N1d1f2HF3AF0S1d2D0S2LF3LFBS1R3HIA1h1N1d4BUDF1f2HF3AF03FT0S". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 HMM HADD HADDNG HSUBANG HSUBI slo EC TPV UWX D0 GRP OSEP MX0 XW EXTA SGB VP NLE NA SLO2 SPA SSH SLO1 SLO3 BUD BUDF C24H LFB"] Lemma sr_minus3 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pv,$0.Pf,$0.Phk,(14.$5.VR,VHIA,)PLBk,(15.$16.)Pmk,P,(17.&40.)(18.(17.&8.))PdXk,$19.Pxra,(17.&40.)Pxt0,(17.&40.)Pxt1,(17.&40.)Pxt2,(17.&40.)Pxa0,(17.&40.)Pxa1,(17.&40.)Pxa2,(17.&40.)Pxa3,(17.&40.)Pxa4,(17.&40.)Pxa5,(17.&40.)Pxa6,(17.&40.)Pxa7,(17.&40.)Pxs3,(17.&40.)Pxs4,(17.&40.)Pxs6,(17.&40.)Pxt3,(17.&40.)Pxt4,(17.&40.)Pxt5,(17.&40.)Pxt6,(17.&40.)P,(1;.R19.R18.R17.R16.R15.R14.)P,(2.(3:.R15.)(11.(39.+2.VN,)+3.))P,(2.(11.R1;.(11.(70.(;.VN,))(11.(6:.(;.VN,)(;.VN,))(11.(53.(;.VN,)(;.VN,)(;.VN,)VN,)(6:.(;.VN,)(;.VN,))))))(9.VN,))P,(2.(11.R1;.(11.(71.Vd,)(11.(6;.Vd,)(11.(3.(;.VN,)(;.VN,)(;.VN,)VN,Vd,)(6;.Vd,)))))(:.VN,Vd,))(1?.$5.(20.$5.VR,VHIA,R1;.Vmo,)$65.(21.(22.R17.(23.&40.(11.(=.&40.Vsp,)-40.))Vgp,Vtp,R16.R15.R14.(23.&40.VX,)(23.&40.VG,)R13.R12.R11.R10.R?.R>.R=.R<.(23.&40.(31.VdA,))R;.R:.(23.&40.(6>.(3>.VR,)))R9.Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(23.&40.+<>>;8.)Vfc,(24.(17.&40.))R19.(25.$5.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS'). dpose sr_sizes as (N0 & NA0 & NP0 & NAg & NBg).
    intros until xt6. intros S HSZ HV HF.
    pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM.
    ddestruct (sr_opX v f hk LBk mk dXk S) as (XM & XNS & XAD & _). pose proof XM as [(_ & _ & _ & _ & NXk & _) _].
    assert (AP0 : 0 <= AST) by (unfold addsub_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; clear - N0; lia).
    assert (AF0 : 0 <= addsub_FRn d) by (unfold addsub_FRn, calls_FR, fr_charge; clear - D0; lia).
    assert (PT0 : 0 <= TLP) by (unfold mm_PHIn, red_PHIn, mul_mpi_PHIn, addsub_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N0; lia) N0); clear - H N0; lia).
    assert (FT0 : 0 <= TLF) by (unfold mm_FRn, red_FRn, mul_mpi_FRn, addsub_FRn, calls_FR, fr_charge, ecp_sz; pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N d ltac:(unfold mul_mpi_nz; clear - N0; lia) D0); clear - H D0; lia).
    assert (IP0 : 0 <= intop_FRn d) by (unfold intop_FRn, calls_FR, fr_charge; clear - D0; lia).
    assert (PMI : intop_PHIn (md_n dXk) <= intop_PHIn EZ) by (apply intop_PHIn_mono; unfold ecp_sz; clear - HSZ N0; lia).
    pose proof (conj S I) as Sbox; clear S.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct Sbox as [S _].
    eapply (sr_intop A_MPI_SUB_INT _ _ _ _ _ _ HSUBI v f hk LBk mk dXk dXk 3 0xceec8);
      [exact S| left; reflexivity| rewrite XAD; exact UWX| clear; lia
      | clear; lia| clear - LFB; lia
      | cbv beta; unfold intop_PHIn, grow_PHI; unfold AVOL_CALL; clear - NXk; lia| exact IP0
      | cbv beta; clear - HV PMI AP0 PT0 BUD; lia| clear - HF AF0 FT0 BUDF; lia
      | unfold C24_INTOP, C24_ECP_SW_RHS in *; clear - C24H; lia| clear; lia| reflexivity
      | intros r0 dX0' [[_ BK0] _]; exact BK0| | rewrite XAD; reflexivity].
    cbv beta. intros h2 LB2 m2 dX2 r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S2 [[RV BK2] SZ2].
    clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
      pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    assert (SZ2' : md_n dX2 <= 2 * N + 4) by (unfold intop_nz in SZ2; clear - SZ2 HSZ N0; lia).
    pose proof (conj S2 I) as Sbox2; clear S2.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR; destruct Sbox2 as [S2 _].
    - eapply (sr_exit _ _ h2 LB2 m2 dX2 r); [exact S2| | clear - HV PMI AP0 PT0; lia| clear - HF AF0 FT0; lia| unfold ecp_sz; clear - SZ2' N0; lia].
      destruct RV as [(R0 & _)|RF]; subst r; [exfalso; apply KR; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia].
    - pose proof GRP as (GAT' & _). dpose GAT' as (_ & _ & _ & EP & _).
      pose proof (conj S2 I) as Sbox2; clear S2.
      (* [comment removed for export] *)
      assert (AL7 : Z.land X 7 = 0)
        by (pose proof MX0 as [(_ & XAL & _) _]; cbn [md_addr] in XAL; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact XAL | clear - XAL; Z.div_mod_to_equations; lia]).
      zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA AL7.
      zstep. zstep. zstep. zstep. zstep. zstep.
      destruct Sbox2 as [S2 _]. rewrite <- EP.
      eapply (sr_loop2 (Z.to_nat (mpd_abs dX2)) _ _ h2 LB2 m2 dX2); [exact S2| intros _; pose proof (P_ecp_sw_rhs.mpd_abs_nonneg dX2); clear - H; lia
        | clear - HV PMI AP0; lia| intros _; clear - HV PMI; lia| clear - HF AF0; lia| intros _; clear - HF; lia| clear - SZ2'; lia| intros _; exact SZ2'].
    all: match goal with |- ?g => idtac "MINUS3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01k0@D13554616751.149D13554616751.150D30841324822.150D35881667587.149D35881667587.150L10470257411.220L10798115971.3  L1175746480.1   L12283411672.146L13301871092.146L14106684376.145L14412480506.8  L14556351945.0  L15922346800.6  L15922346801.10 L16075573881.191L16121396950.4  L16133916880.8  L17646078182.145L17746767258.11 L19806849779.2  L19808960241.5  L2224152947.191 L22890275614.2  L23418271921.4  L24026654016.14 L24026817857.13 L26892418956.1  L28516968417.6  L29010569984.190L29699359420.6  L29770752369.4  L29770752369.6  L29956516996.0  L30938037993.9  L34994544387.146L35653441506.7  L35693534892.2  L39887139444.146L40834179097.153L41041641302.4  L41053667674.2  L41231258181.12 L41231487557.13 L41288976216.146L41314381969.8  L42157884193.0  L43059266230.143L44866992728.146L45898055924.146L46947619857.8  L46947619857.9  L48303896707.2  L48429268312.146L5145216728.146 L51925114228.146L52248105850.2  L5572102932.8   L55832289796.1  L57933933556.146L59124818608.2  L59673527198.3  L60098763854.3  L60925191675.9  L61801931053.8  L62268830454.7  L63192237729.0  L63306561278.2  L63962036340.145L64732282808.9  L65135876312.190L6623080680.9   L66758331116.9  L67158371251.146L7274816372.146 L8722184664.146 Q15457446739.146Q15457446739.147Q15643324129.145Q18365925601.146Q18700768642.153Q18703874042.194Q19120365881.149Q21804524913.153Q21879645826.146Q25156215686.153Q25513505925.148Q25513505925.149Q25660593749.153Q27907200258.146Q31231138774.153Q31271525473.146Q31401087590.153Q31664292632.194Q32655500769.146Q33918256002.146Q35028793568.153Q35702494822.153Q36425882626.146Q37004003535.195Q3830427394.146 Q39939554818.146Q40279478779.195Q40279892185.194Q41152393185.146Q4128416594.153 Q43928033258.147Q44648843873.146Q49698585326.147Q49698585326.148Q51235796833.146Q53959472525.153Q59843137889.146Q61493743899.195Q61796041430.153Q6418745426.153 Q64240613762.153Q66522067074.146Q67528989526.149Q67528989526.150Q7377275490.148 Q7377275490.149 Q9843367298.145 00000i02403003Y04W04X04`04d05205@05N05h05i06<06_06`06o07H07V08708=08H08^08d09109`0:J0:N0:d0:e0;10;@0;O0;P0;m0<;0<S0<Z0<h0=80=B0=J0>10>[0>i0?D0?E0?Z0?h0@60@?0@H0@N0@\0@j0A80AA0AN0AS0Aa0Ag0B00B:0BY0Be0C:0C;0CC0CQ0Ca0D:0DW0Dd0E20E@0EN0E\0Ej0F80FF0FU0Fc0GG0GH0GZ0Gi0HI0I;0I<0IN0I^0Il0J40JB0JP0Jb0K20K30KE0KS0Ke0L70LE0LS0La0Lb0M00M>0MW0N00N>0NN0N\0OL0OM0O\0O]0Oo0PS0QI0Qm0R`0S2S1R2LF2ra2sp2lo3LFB4LOSP4LOS'4IMG'3SPR3MC42HB5Ha_st5Hl_stS1R2LF2ra2sp2s02lo3LFB4LOSP4LOS'4IMG'3SPR3MC42HB5Ha_st5Hl_st2s12s22s32s42s5S1R2LF2ra2sp2s62lo3LFB4LOSP4LOS'4IMG'3SPR3MC42HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3LFB3TOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s03LFB3TOP2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS1N2N01HS2spS2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LF2ra2sp3LFBS1g1N3NAg3dX24SZ2'3dX33SZ3SS2nX2dA1g1N3AP03PM1S2nX2dA1g1N3MM03AP03IP03PM13dX23PM2FS1N2N03dX34SZ3'S2nX2dA1g1N1d3AF03IF03FM1S2LF2ra2sp3LFBS2nX2dA1g1N2NA2N03NP03NX03dX23SZ2S1N2N0S1g3dX23NX2S2LF2ra2sp1G3LFB1r3CABS1d2D0S2sp1X2lo3DSXS1R3HIA1h2nX2dA1g1N3BUD3MM03AP03IP03PM13dX23PM2S1R3HIA1h2nX2dA1g1N1d4BUDF3MF03AF03IF03FM1S2spS1R2lo3LOS3ALO3MC23DLOFS1g1N2N03NAgS1N2N03dX24SZ2'S1N2N03dX24SZ2'SS2nX2dA1g1N1d3MF03AF03IF03FM1S2LF2ra2sp3LFBS1R3HIA1h2sp2lo3TOP4HTOPS1G3GMCS2LF2ra2sp3LFBS1R2LF2ra2sp3LFBS1N1d2D01HS2LF3LFBS1R3HIA1h2nX2dA1g1N3BUD3MM03AP03IP03PM1S1R3HIA1h2nX2dA1g1N1d4BUDF3MF03AF03IF03FM1S2LF2ra2sp3LFBS2nX2dA1g1N3MM03AP03IP03PM1SS2LF2ra2sp2lo3LFB3SLOS2LF2ra2sp3LFBS2LF2ra2sp3LFBS1g1N3NP0S1g1N3NP0S1N2N0S2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LB4C24HS2nX1N2N03NX0S3dX3S2LF2ra2sp3LFBS1d2D0S1X1G3OS1S1R2lo3LOSS2nX2dA1g1N3AP03IP03PM13dX23PM2S2dA1N2NA2N0S2nX2dA1g1N1d3AF03FM1SS2nX3NX0S2LF2ra2sp3LFBS2dA1N2NA2N03NA0S2LF2ra2sp1G3LFB1r2G03CABS2nX2dA1g1N1d3MF03AF03IF03FM1S2nX1N2N03NX0S2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LF2ra2sp3LFBS2LF2sp3LFB2HBS2LF2sp3LFB2HBS2LF2sp2lo3LFBS2LF2sp2lo3LFBS1R2LF3LFB4IMG'S2LF1G3LFB3CABS2LF2sp2s62lo3LFB3SLO2HB5Ha_st5Hl_stFS2LF2sp2lo3LFB3SLOS1R2LF3LFB4IMG'S2LF2ra2sp2lo3LFB2HB5Ha_st5Hl_stS2LF2sp2s02lo3LFB2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS2LF2sp2lo3LFB3SLOS1R2LF3LFB5ALWF'S2LF2sp2lo3LFBS2LF3LFBS2LF1G3LFB3CABS2LF2sp2lo3LFBS2LF2sp2lo3LFB3SLOS1R2LF3LFB5ALWF'FS2LF2sp2lo3LFB3SLOS2LF1G3LFB3CABS2LF2sp2lo3LFB3SLOS2LF2sp2lo3LFB3SLOS2LF1G3LFB3CABS2LF1G3LFB3CABS2LF2sp2lo3LFBFS2LF2sp3LFB2HBS2LF2sp2lo3LFBS2LF2sp3LFB4SP642HB5Ha_stS2LF2sp3LFB4SP642HB5Ha_stS2LF2sp2lo3LFBS1R2LF3LFB5ALWF'S2LF2sp2lo3LFBS1R2LF2ra2sp1G3LFB4IMG'3SPR3MC43MC61r3GAL2G03CABFS1R2LF3LFB4IMG'FS2LF2sp2lo3LFB3SLOS2LF2ra2sp2lo3LFB3SLO2HB5Ha_st5Hl_stS2LF2sp2s02lo3LFB3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2LF2ra2sp2lo3LFB3SLO2HB5Ha_st5Hl_stS2LF2sp2s02lo3LFB3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2sp2lo3LFB3SLO". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 HMM HADD HADDNG HSUBANG HSUBI slo EC TPV UWX D0 GRP OSEP MX0 XW EXTA SGA SGB VP NLE NA SLO2 SPA SSH SLO1 SLO3 BUD BUDF C24H LFB"] Lemma sr_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Pa3,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)Pcnt,(17.&40.)Pm0,P,(17.&40.)(18.(17.&8.))P,(1<.P,(17.&40.)(18.(17.&8.))R1.Vm,)P,(72.$5.VR,VHIA,Vh,Vmo,)P,(5?.$5.Vm,Vlo,(=.&40.Vsp,))P,(73.$5.Vm,$8.(59.$74.(75.R5.)(5<.$74.)))P,(3=.$5.(3>.VR,)(3?.$5.VR,VHIA,Vh,)Vm,(6.VX,VsX,VnX,VpX,Vxs0,VpadX,$7.))(2;.$5.$65.(2:.(21.(22.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(23.&40.VG,)(23.&40.VX,)(23.&40.(31.VdA,))R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(23.&40.$76.)Vfc,(24.(17.&40.))R6.(25.$5.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until m0; intros EM HK ST MC0 OXA. unfold A_ECP_SW_RHS.
    ec_open. dpose sr_base as (LO0 & LOSP & SP64 & DSX & X0 & X16 & NE0 & LOS'). dpose sr_sizes as (N0 & NA0 & NP0 & NAg & NBg).
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof OXA as [OX _]. cbn [md_addr] in OX.
    dpose MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6). pose proof (art_data_lo asegs R HIA) as DLO.
    assert (MCLOW : MC + 8 <= lo) by (clear - MC2 DLO ALO LOS; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    (* [comment removed for export] *)
    pose proof MIm as MI0. rewrite <- EM in HH, ST, OX, MI0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    carve_frame 64%nat ST.
    do 9 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    subst m0.
    replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in FR, ST by (clear; lia).
    assert (S0 : SRI 0 0 h LB mP dX).
    { constructor.
      - fold SR_FRAME in FR. exact (ej_start R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC mP cnt MU WM HH MI0 ST FR MC0).
      - split; [| split; [reflexivity| split; [discriminate| split; [intros b []| exact OX]]]].
        eapply mpd_at_munch_any; [exact MX0| exact MU| exact WM| cbn [md_addr disjoint_from fst snd]; split; [clear - DSX; lia| exact I]|].
        intros C. exfalso. apply C. reflexivity.
      - intros b Hb. left. exact Hb.
      - reflexivity. }
    destruct sr_dA_ext as [AEXT AUW]. destruct sr_A_ext as [GAEXT GAUW].
    pose proof MX0 as [(_ & _ & _ & _ & _ & OW0) _]. cbn [md_own md_n md_p] in OW0. destruct OW0 as [_ NX0].
    pose proof (hm_abase asegs R HIA h LB LF mP HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) mP) as MU; pose proof (wmono_refl asegs mP) as WM.
    pose proof (conj S0 I) as Sbox. clear S0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. clear GOT GSB AB. zstep. zstep. zstep. zstep.
    destruct Sbox as [S0 _].
    assert (MM0 : 0 <= mm_PHIn EZ EZ EZ N) by (unfold mm_PHIn, red_PHIn, mul_mpi_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N0; lia) N0); clear - H N0; lia).
    assert (MF0 : 0 <= mm_FRn EZ EZ EZ N d) by (unfold mm_FRn, red_FRn, mul_mpi_FRn, calls_FR, fr_charge, ecp_sz; pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N d ltac:(unfold mul_mpi_nz; clear - N0; lia) D0); clear - H D0; lia).
    assert (AP0 : 0 <= AST) by (unfold addsub_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; clear - N0; lia).
    assert (AF0 : 0 <= addsub_FRn d) by (unfold addsub_FRn, calls_FR, fr_charge; clear - D0; lia).
    assert (IP0 : 0 <= intop_PHIn EZ) by (unfold intop_PHIn, grow_PHI, ecp_sz; unfold AVOL_CALL; clear - N0; lia).
    assert (IF0 : 0 <= intop_FRn d) by (unfold intop_FRn, calls_FR, fr_charge; clear - D0; lia).
    assert (PM1 : mm_PHIn nX (md_n dA) (md_n dA) (md_n dP) <= mm_PHIn EZ EZ EZ N) by (apply mm_PHIn_mono; unfold ecp_sz; clear - NX0 NA NP0 N0; lia).
    assert (FM1 : mm_FRn nX (md_n dA) (md_n dA) (md_n dP) d <= mm_FRn EZ EZ EZ N d) by (apply mm_FRn_mono; unfold ecp_sz; first [exact D0 | clear - NX0 NA NP0 N0 NA0; lia]).
    unfold sw_rhs_PHIn in BUD. unfold sw_rhs_FRn in BUDF.
    eapply (sr_mulmod 0 0 h LB mP dX dA dA 0xcee2c);
      [exact S0| right; exact AEXT| right; exact AEXT| left; reflexivity| exact AUW| exact AUW
      | cbn [md_n]; clear - NX0; lia| exact NA0| exact NA0
      | cbn [md_n]; clear - PM1 MM0 AP0 IP0 BUD; lia| cbn [md_n]; clear - FM1 MF0 AF0 IF0 BUDF; lia| clear; lia| reflexivity| | reflexivity| reflexivity].
    cbn [md_n]. intros h2 LB2 m2 dX2 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S2 [RR BK2] SZ2.
    clear LAWS KINV MU WM CSOK SB64 SCS0 SCS. pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
      pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    assert (SZ2' : md_n dX2 <= 2 * N + 3) by (unfold mm_nz, mul_mpi_nz in SZ2; clear - SZ2 NX0 NA NP0 N0 NA0; lia).
    pose proof GRP as (GAT0 & _). dpose GAT0 as (_ & GAL & G0 & _ & EA & _).
    dpose OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    dpose GRP as (_ & _ & _ & _ & _ & _ & GMC & _).
    assert (DXG : disjoint_from XO G 192) by (cbn [disjoint_from fst snd]; split; [clear - OS1; lia| split; [clear - GMC; lia| exact I]]).
    pose proof (ej_grp_pre R HIA h LB LF m (bv_unsigned sp) lo 64 SR_FRAME XO MC EC MT _ _ h2 LB2 m2 G g (bv_unsigned sp) d (sr_j _ _ _ _ _ _ S2) GRP DXG ltac:(clear; lia)) as (GAT2 & _ & _ & _ & _ & _ & _ & GOB2 & _).
    dpose GAT2 as (_ & _ & _ & _ & _ & _ & _ & _ & MA2 & _). destruct MA2 as (CA2 & _). unfold mpi_cells in CA2. rewrite EA in CA2.
    pose proof (rw_cells_bound _ _ _ _ CA2) as CAB. cbn [cells_size csize Nat.add] in CAB.
    pose proof (conj S2 I) as Sbox2; clear S2.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      assert (GAL7 : Z.land G 7 = 0)
        by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact GAL | clear - GAL; Z.div_mod_to_equations; lia]).
      zstep. zstep. if_cases KG; zify_cond KG; [exfalso; clear - KG GAL7; rewrite ?GAL7 in KG; rewrite ?Zmod_0_l in KG; lia|]. clear KG GAL7.
      zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KA; zify_cond KA; destruct Sbox2 as [S2 _].
      +
        eapply (sr_minus3 _ _ h2 LB2 m2 dX2); [exact S2| exact SZ2'| unfold sw_rhs_PHIn; clear - PM1 AP0; lia| unfold sw_rhs_FRn; clear - FM1 AF0; lia].
      + destruct (sr_opX _ _ h2 LB2 m2 dX2 S2) as (XM2 & XNS2 & XAD2 & _). pose proof XM2 as [(_ & _ & _ & _ & NX2 & _) _].
        pose proof (conj S2 I) as Sbox2; clear S2.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        destruct Sbox2 as [S2 _].
        assert (PM2 : addsub_PHIn (md_n dX2) (md_n (g_A g)) <= AST) by (apply addsub_PHIn_mono; unfold ecp_sz; clear - SZ2' NAg N0; lia).
        eapply (sr_binop A_MPI_ADD_MPI _ _ _ _ _ _ HADD _ _ h2 LB2 m2 dX2 dX2 (g_A g) 0xcee88);
          [exact S2| left; reflexivity| right; exact GAEXT| exact (proj1 (proj2 (sr_opnd _ _ h2 LB2 m2 dX2 (g_A g) S2 (or_intror GAEXT))))| rewrite XAD2; exact UWX| exact GAUW
          | clear; lia| clear - LFB; lia
          | cbv beta; unfold addsub_PHIn, grow_PHI; unfold AVOL_CALL; clear - NX2 NAg; lia| cbv beta; exact AF0
          | cbv beta; clear - PM1 PM2 MM0 AP0 IP0 BUD; lia| cbv beta; clear - FM1 MF0 AF0 IF0 BUDF; lia
          | unfold C24_ADDSUB, C24_ECP_SW_RHS in *; clear - C24H; lia| clear; lia| reflexivity
          | intros r0 dX0' [[_ BK0] _]; exact BK0| | rewrite XAD2; reflexivity| rewrite EA; reflexivity].
        cbv beta. intros h3 LB3 m3 dX3 r3 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S3 [[RV3 BK3] SZ3].
        clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo) as KINV;
          pose proof (munch_refl ([] : list ivl) m3) as MU; pose proof (wmono_refl asegs m3) as WM.
        assert (SZ3' : md_n dX3 <= 2 * N + 5) by (unfold addsub_nz in SZ3; clear - SZ3 SZ2' NAg N0; lia).
        pose proof (conj S3 I) as Sbox3; clear S3.
        (* [comment removed for export] *)
        zstep. if_cases KR3; zify_cond KR3; destruct Sbox3 as [S3 _].
        * eapply (sr_exit _ _ h3 LB3 m3 dX3 r3); [exact S3| | unfold sw_rhs_PHIn; clear - PM1 PM2 MM0 AP0 IP0; lia| unfold sw_rhs_FRn; clear - FM1 MF0 AF0 IF0; lia| unfold ecp_sz; clear - SZ3' N0; lia].
          destruct RV3 as [(R0 & _)|RF]; subst r3; [exfalso; apply KR3; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia].
        * (* [comment removed for export] *)
          dpose GAT0 as (_ & _ & _ & EP & _).
          zstep. rewrite <- EP.
          eapply (sr_loop1 (Z.to_nat (Z.max 0 (mpd_val dX3))) _ _ h3 LB3 m3 dX3); [exact S3| clear; lia| unfold sw_rhs_PHIn; clear - PM1 PM2 AP0 IP0; lia| unfold sw_rhs_FRn; clear - FM1 AF0 IF0; lia| exact SZ3'].
    - destruct Sbox2 as [S2 _].
      eapply (sr_exit _ _ h2 LB2 m2 dX2 r); [exact S2| exact RR| unfold sw_rhs_PHIn; clear - PM1 MM0 AP0 IP0; lia| unfold sw_rhs_FRn; clear - FM1 MF0 AF0 IF0; lia| unfold ecp_sz; clear - SZ2' N0; lia].
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End SR.

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L27883368372.3L38043081936.6L40228640085.000000800O00PS1X1a2HaS1R5NEEDR2sp2lo3SLO3NERS". (* [comment removed for export] *)
Theorem A_ecp_sw_rhs_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_rhs ()) "PR,$77.PHIA,(78.$5.R1.)PMT,(15.$79.)P,(7:.(3>.R3.))P,(7;.$5.R4.R3.R2.$57.$8.)P,(7<.$5.R5.R4.$7=.)P,(7>.$5.R6.R5.$7=.)P,(7?.$5.R7.R6.$80.)P,(81.$5.R8.R7.$82.)P,(1<.$0.(91.R9.)$92.)P,(1<.$0.(93.R:.=)$94.)P,(2.=(95.R;.))P,(2.=(83.R<.))P,Ph,(14.$5.R=.R<.)PLB,(15.$16.)PLF,(15.$16.)Pm,P,(17.&40.)(18.(17.&8.))P,(84.$5.R11.R10.R4.R3.R2.R1.)(85.$0.(86.(5:.$0.$0.)$0.(87.$0.$0.)R4.))P,(1.(2.(88.(34.R>.))(89.(34.R>.)))(2.(8:.(34.R>.))(8;.(34.R>.))))P,Pa,$0.P,(1<.$8<.(8=.$5.(8>.R1.))$8?.)P,(1.(2.=R2.)(>.R2.(?.+2.+40.)))(1.(2.(88.(34.R12.))R3.)(>.R3.(8;.(34.R12.))))(90.$5.R10.R?.R>.$76.$8.)")
(* [comment removed for export] *).
Proof.
  intros R HIA MT IMG HMM HADD HADDNG HSUBANG HSUBI UARG SM0 NS1 NEEDR HND DIMG ROIMG. unfold ecp_sw_rhs_stmtA, ecp_rhs_stmtA.
  intros until slo. cbv iota.
  intros HH HK LFB GRP OSEP SGA SGB VP _ NLE NA MX EO XW EXTA MC0 MCOK ST LOS SLO SSH SLO1 SLO3 TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24H -> [-> ->].
  destruct dX as [X sX nX pX xs0 padX ownX]. cbn [md_own] in EO. subst ownX.
  pose proof (arl_need_ecp_rt R) as NER.
  assert (EC : ECA R HIA h LB LF m (bv_unsigned sp) lo 64 (SR_FRAME ra s0 s1 s2 s3 s4 s5 s6) [(X, X + 16); (A_MUL_COUNT, A_MUL_COUNT + 8)] A_MUL_COUNT).
  { constructor; try assumption; try reflexivity; [clear; lia| clear - SLO NEEDR NER; lia|].
    intros a Ha. cbn [outside fst snd] in Ha. clear - Ha. lia. }
  cbn [md_addr] in *.
  eapply (sr_main R HIA IMG MT HMM HADD HADDNG HSUBANG HSUBI UARG SM0 NS1 h LB LF m mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X sX nX pX xs0 padX dA G g N lo d slo EC)
    with (m0 := m) (cnt := cnt);
    first [ eassumption | reflexivity | eapply uwc_nonneg; exact UW | clear - SLO; lia | idtac ].
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

