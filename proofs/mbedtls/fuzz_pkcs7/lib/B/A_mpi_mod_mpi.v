(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_divmod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_copy A_mpi_journey A_mpi_journey2
     A_mpi_add_abs_W A_mpi_sub_abs A_mpi_add_sub A_mpi_add_sub_ng A_mpi_add_sub_ng_sz A_mpi_stmtA_sz A_mpi_add_sub_stmtSZ A_mpi_div_stmtA A_mpi_mod_stmtA A_mpi_mod_mpi_C A_mpi_cmp_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
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
Ltac2 gd_tbl_A_mpi_mod_mpi () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.mod_mpi_Rs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub.add_sub_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "WMD.MD_FRAME_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.div_mpi_nz"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "WMD.MD_POST_A"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JBA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.BJA"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_ng_sz.add_sub_mpi_ng_Rsz"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub.add_sub_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_stmtSZ.add_sub_mpi_Rsz"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.A_MPI_MOD_MPI_E"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.mpi_div_mpi_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.A_MPI_DIV_MPI_E"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_ng_sz.add_sub_mpi_ng_stmtA_oz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_stmtSZ.add_sub_mpi_stmtA_osz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mod_stmtA.mpi_mod_mpi_stmtA"; "mod_mpi_PHIg"; "mod_mpi_FRg"].


Section WMD.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_MD.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0_MD.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis CMP : mpi_cmp_mpi_stmtA asegs AL A_MPI_CMP_MPI_E.
  Variables (PHIf : mpd -> mpd -> mpd -> Z) (FRf : mpd -> mpd -> mpd -> Z -> Z).
  Hypothesis HDIV : mpi_div_mpi_stmtA asegs R HIA A_MPI_DIV_MPI_E PHIf FRf.
  Hypothesis HASN : forall flip, flip = 1 \/ flip = -1 -> add_sub_mpi_ng_stmtA_oz flip asegs R HIA A_ADD_SUB_MPI.
  Hypothesis HADD : add_sub_mpi_stmtA_osz 1 asegs R HIA A_ADD_SUB_MPI.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo slo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition MD_FRAME_A := aa_frame96 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 96 MD_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis UWB : uw_obj R (md_addr dB) 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis SLO2 : lo <= bv_unsigned sp - MPI_MOD_MPI_STACK_A - arl_need_rt R.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 496 - arl_need_smalloc R.
  Hypothesis LFN : (length LF < 511)%nat.
  Hypothesis C24H : cnt24 LB + C24_DIV_MPI <= C24MAX.
  Hypothesis MB0 : mpd_at asegs m LB dB.
  Hypothesis NRB : 0 <= md_n dB <= 10000.
  Hypothesis IB2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi ()) "P,(0.$1.(2.VdB,)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.VdB,))))(0.$:.(;.$<.(=.(>.(?.VdB,)R2.)))$10.)(0.$:.(11.(?.VdB,)(8.+4.(9.VdB,)))$10.)")
(* [comment removed for export] *).
  Local Notation PHId := (PHIf dX dA dB).
  Local Notation FRd := (FRf dX dA dB (d + 1)).
  Local Notation PHIb := (PHIf dX dA dB + (32 * md_n dB + 48)).
  Local Notation FRb := (FRf dX dA dB (d + 1) + add_sub_FR (d + 1)).
  Hypothesis PHId0 : 0 <= PHId.
  Hypothesis FRd0 : 0 <= FRd.
  Hypothesis BUD : havol asegs R HIA h + PHIb <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FRb <= FR_MAX.
  Local Notation NZ := (div_mpi_nz nX (md_n dA) (md_n dB)).

  Definition MD_POST_A := mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX (mod_mpi_Rs LB dX dA dB) PHIb FRb lo m mo
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].


  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAM; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  Local Notation SHB0 := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 243)].
  Local Notation SHB := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                         C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243)].

  Definition MD_BASE (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) : Prop :=
    bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128 /\ sp1 mod 32 = 0
    /\ FB mod 64 = 0 /\ fresh_apart R LB LF FB 64
    /\ JCA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A
    /\ presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1
    /\ hcs asegs R HIA h1 = hcs asegs R HIA h /\ htop asegs R HIA h1 = htop asegs R HIA h
    /\ hstkhi asegs R HIA h1 = hstkhi asegs R HIA h /\ hflag asegs R HIA h1 = hflag asegs R HIA h
    /\ havol asegs R HIA h1 = havol asegs R HIA h /\ hfr asegs R HIA h1 = hfr asegs R HIA h
    /\ (forall mo', HK asegs R HIA h1 mo' <-> HK asegs R HIA h mo').

  Definition MD_CELLS (mc : mem) (FB : Z) (shb : list cell) : Prop :=
    (exists w0 w1 w2 : word, rw_cells asegs mc FB [C8 w0; C8 w1; C8 w2])
    /\ rw_cells asegs mc (Z.shiftr FB 3 + al_sb AL) shb
    /\ (exists wl : word, rw_cells asegs mc (FB + 32) [C4 wl])
    /\ sshad asegs AL mc slo (bv_unsigned sp).

  #[using="Type"] Lemma d4_ba_app2 : forall (L1 L2 : list blk) (B j FB n : Z),
      blocks_apart (L1 ++ L2) -> In (B, j) L1 -> In (FB, n) L2 -> FB + n <= B \/ B + j <= FB.
  Proof.
    induction L1 as [|[A k] L1 IH]; intros L2 B j FB n BA H1 H2; [destruct H1|].
    cbn [app blocks_apart] in BA. destruct BA as [BH BR]. destruct H1 as [E|H1].
    - injection E as <- <-. destruct (BH FB n ltac:(apply in_or_app; right; exact H2)) as [Hd|Hd]; [right; exact Hd| left; exact Hd].
    - exact (IH L2 B j FB n BR H1 H2).
  Qed.

  #[using="Type"] Lemma d4_fresh_relist : forall (hq : HST asegs R HIA) (LBq : list blk) (mq : mem) (FB n : Z),
      fresh_apart R LB LF FB n -> HM asegs R HIA hq LBq ((FB, n) :: LF) mq -> fresh_apart R LBq LF FB n.
  Proof.
    intros hq LBq mq FB n (F0 & F1 & F2 & F3) HH. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
    intros B0 j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; right; exact Hb].
    destruct (hm_apart asegs R HIA hq _ _ _ HH) as [_ BA].
    exact (d4_ba_app2 LBq ((FB, n) :: LF) B0 j FB n BA Hb ltac:(left; reflexivity)).
  Qed.

  #[using="Type"] Lemma d4_fresh_drop : forall (LBk LFk : list blk) (N k FB n : Z),
      fresh_apart R LBk ((FB, n) :: LFk) N k -> fresh_apart R LBk LFk N k.
  Proof.
    intros LBk LFk N k FB n (F0 & F1 & F2 & F3). split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
    intros B0 j Hb. apply F3. apply fdata_cons_sub. exact Hb.
  Qed.

  #[using="Type"] Lemma d4_fdata_sub2 : forall (LFk : list blk) (b : blk), In b (fdata LFk) ->
      exists fb : blk, In fb LFk /\ fst fb <= fst b /\ fst b + snd b <= fst fb + snd fb.
  Proof.
    induction LFk as [|[FB n] r IH]; intros b Hb; [destruct Hb|].
    cbn [fdata] in Hb. destruct Hb as [E|[E|Hb]].
    - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. split; [apply Z.le_refl|].
      pose proof (Z.le_min_r 24 n) as ZM. clear - ZM. lia.
    - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. clear. lia.
    - ddestruct (IH b Hb) as (fb & H1 & H2). exists fb. split; [right; exact H1| exact H2].
  Qed.

  #[using="Type"] Lemma d4_presW_at : forall (hq : HST asegs R HIA) (LBq LFh LFk : list blk) (mq : mem) (SP SSP : Z) (W : list ivl),
      HM asegs R HIA hq LBq LFh mq -> (forall fb, In fb LFk -> In fb LFh) -> arl_stklo R <= SSP ->
      presW asegs R HIA hq LBq LFk SP SSP W mq mq.
  Proof.
    intros hq LBq LFh LFk mq SP SSP W HH HF HSSP.
    split; [apply presA_refl|]. split; [| split].
    - intros c Hc. destruct Hc as [X0|[X0|[X0|X0]]].
      + apply (hcs_stack asegs R HIA hq). clear - X0 HSSP. lia.
      + ddestruct X0 as ([B j] & Hb & Hr). cbn in Hr. eapply (hcs_block asegs R HIA hq _ _ mq B j HH Hb). exact Hr.
      + ddestruct X0 as ([B j] & Hb & Hr). cbn in Hr. eapply (hcs_fake asegs R HIA hq _ _ mq B j HH (HF _ Hb)). exact Hr.
      + apply hcs_static. exact X0.
    - intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + eapply hcs_block; [exact HH| exact Hb].
      + destruct (d4_fdata_sub2 LFk _ Hb) as ([FB' n'] & HFB & H1 & H2). cbn [fst snd] in H1, H2.
        eapply crange_sub; [eapply hcs_fake; [exact HH| exact (HF _ HFB)]| exact H1| exact H2].
    - pose proof (hm_blocks_low asegs R HIA hq _ _ _ HH) as BL. intros B j Hb. apply BL.
      apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; exact (HF _ Hb)].
  Qed.

  #[using="Type"] Lemma d4_presW_hmono : forall (h0 h' : HST asegs R HIA) (LBk LFk : list blk) (SP SSP : Z) (W : list ivl) (m0 m' : mem),
      presW asegs R HIA h0 LBk LFk SP SSP W m0 m' -> (forall x, hcs asegs R HIA h0 x -> hcs asegs R HIA h' x) ->
      hstkhi asegs R HIA h' = hstkhi asegs R HIA h0 -> presW asegs R HIA h' LBk LFk SP SSP W m0 m'.
  Proof.
    intros h0 h' LBk LFk SP SSP W m0 m' HP HS ET. destruct HP as (P0 & C1 & C2 & C3). unfold presW. rewrite ET.
    split; [exact P0|]. split; [intros c Hc; apply HS, C1, Hc|].
    split; [intros B j Hb; eapply crange_mono; [exact HS| apply (C2 B j Hb)]| exact C3].
  Qed.

  #[using="Type"] Lemma d4_crw : forall (LBF : list blk) (lo0 TOP A n : Z),
      client_wrange L LBF lo0 TOP A n -> client_range L LBF lo0 A n.
  Proof.
    intros LBF lo0 TOP A n CW x Hx. destruct (CW x Hx) as [X0|[X0|X0]]; [left; clear - X0; lia| right; left; exact X0| right; right; exact X0].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma md_join : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc : mem) (dXc : mpd) (r : Z)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      (r = 0 -> 0 <= mpd_val dXc < mpd_abs dB) ->
      - 2 ^ 31 < r <= 0 ->
      md_n dXc <= NZ -> v <= PHIb -> f <= FRb ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 (Z_to_bv 64 FB) xs3 xs4 xs5 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) xs8 xs9 xs10 s11
                 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa0690) fc None mc (seg_rom asegs)).
  Proof.
    intros h1 m1 FB sp1 v f hc LBc mc dXc r xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6
      MB J MC HRV HR HSZ HV HF.
    jc_open. basic_factsA hc.
    destruct MB as (SP1 & SP1M & F64 & FRSH & JC1 & PRES & Ecs & Etop & Estk & Eflag & Evol & Efr & HKI).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NST1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    cbn [app] in HH1. clear J.
    destruct MC as ((w0 & w1 & w2 & FHD) & FSH & (wl & LIMB) & SSH). clear LIMB SSH OX1.
    pose proof JC1 as [_ _ _ _ HH0 _ _ _ _ _ _ _ _ _ _].
    pose proof (hm_top asegs R HIA hc _ _ _ HH1) as HTOPc.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1, Estk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof FRSH as (F0 & F1 & F2 & F3).
    assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA hc _ _ mc FB 64 HH1 INF) as CFBc.
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
    assert (SBND : hl_data_hi L <= Z.shiftr FB 3 + al_sb AL /\ Z.shiftr FB 3 + al_sb AL + 8 <= alloc_ceiling).
    { pose proof (hcs_shadow_band asegs R HIA hc FB (CFBc FB ltac:(clear; lia))) as SBlo.
      pose proof (hcs_shadow_band asegs R HIA hc (FB + 8 * 7) (CFBc (FB + 8 * 7) ltac:(clear; lia))) as SBhi.
      rewrite shadow_of_plus in SBhi. unfold shadow_of in SBlo, SBhi. rewrite <- SHFB in SBlo, SBhi. clear - SBlo SBhi. lia. }
    assert (APS : Z.shiftr FB 3 + al_sb AL + 8 <= FB \/ FB + 64 <= Z.shiftr FB 3 + al_sb AL).
    { pose proof (apart_shadow_client AL (hcs asegs R HIA hc) FB 64 FB (shadow_of AL FB) 8 CSOK CFBc CFBc eq_refl
                    ltac:(clear; lia) ltac:(clear; lia)) as K.
      unfold shadow_of in K. rewrite <- SHFB in K. clear - K. lia. }
    assert (INH : In (FB, 24) (LBc ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
    assert (IND : In (FB + 32, 24) (LBc ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
    pose proof (hm_fresh_frame_apart asegs R HIA hc LBc LF mc FB 64 HH1) as AP.
    pose proof (d4_fresh_relist hc LBc mc FB 64 FRSH HH1) as FRSHc.
    pose proof (fresh_apart_keep R LB LF dX FB 64 FRSH) as FRSHk.
    assert (PA0 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { eapply presA_weaken; [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| intros b' Hb; eapply In_mpd_keep; exact Hb
                           | intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
    assert (PA1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m1 mc).
    { rewrite <- Estk. eapply presA_weaken; [exact HPX1| intros b' Hb; exact Hb| intros b' Hb; right; exact Hb| clear; lia| clear; lia| clear; lia
                                            | intros x Hx; exact Hx]. }
    pose proof (presW_sub_blocks asegs R HIA h LB (mpd_keep LB dX) LF _ _ _ m m1 PRES ltac:(intros b' Hb; eapply In_mpd_keep; exact Hb))
      as (_ & C1 & C2 & C3).
    assert (PRESa : presW asegs R HIA hc (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) [(X, X + 16)] m mc).
    { eapply (d4_presW_hmono h hc); [split; [eapply presA_trans; [exact PA0| exact PA1]| split; [exact C1| split; [exact C2| exact C3]]]| |].
      - intros x Hx. apply HCS1. rewrite Ecs. exact Hx.
      - rewrite HS1. exact Estk. }
    clear PA0 PA1 C1 C2 C3 HPX1.
    assert (PRES2 : presW asegs R HIA hc LBc LF (bv_unsigned sp) (arl_stklo R) [] mc mc)
      by (eapply d4_presW_at; [exact HH1| intros fb Hfb; right; exact Hfb| clear; lia]).
    unfold MD_FRAME_A, aa_frame96 in FR1.
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FR1, ST1 by (clear; lia).
    pose proof MI1 as MI0.
    assert (BQ : bv_eqb (Z_to_bv 64 FB) (Z_to_bv 64 0) = false).
    { rewrite bv_eqb_Z, (unsigned_lit FB), (unsigned_lit 0) by (clear - F0 FBLO SLO NEEDR SPR; lia). apply Z.eqb_neq. clear - F0; lia. }
    zstep. zstep. zstep. zstep.
    rewrite BQ.
    cbv iota beta.
    do 9 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    destruct (hm_fake_free asegs R HIA hc LBc ((FB, 64) :: LF) me FB 64 HH1 INF)
      as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
    replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp. clear Hold.
    assert (SUB1 : forall b', In b' (mpd_keep LB dX ++ fdata LF) -> In b' (LBc ++ fdata ((FB, 64) :: LF))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact OUT1| exact Hb]| right].
      eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
    assert (SUB2 : forall b', In b' (LBc ++ fdata LF) -> In b' (LBc ++ fdata ((FB, 64) :: LF)))
      by (intros b' Hb; apply fdata_cons_sub; exact Hb).
    assert (NP5 : bv_unsigned sp + -96 + 96 <= p \/ p + 1 <= bv_unsigned sp + -96).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p);
        [exact NCp| apply client_range_stack; clear - SLO LOS NEEDR; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp1 : wcover R (mpd_keep LB dX) LF (bv_unsigned sp) [(X, X + 16)] p 1)
      by (eapply wcover_nc; [exact NCp| exact SUB1| clear - LOS SLO NEEDR; lia]).
    assert (WCp2 : wcover R LBc LF (bv_unsigned sp) [] p 1)
      by (eapply wcover_nc; [exact NCp| exact SUB2| clear - LOS SLO NEEDR; lia]).
    clear HH1 NCp NSp FHD FSH.
    zstep. zstep.
    fake_free_done p HSp.
    cbn [lb_remove fst] in HM4. rewrite Z.eqb_refl in HM4.
    do 15 zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold MD_POST_A, mpi_binop_postA.
    do 14 eexists. exists mf, mo9, h4, LBc, dXc, r.
    split; [reflexivity|].
    split; [exact MI0|]. split; [exact ST1|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRESa) as HPF; rewrite HS1, Estk in HPF; exact HPF|].
    split; [rewrite E4top, HT1; exact Etop|]. split; [rewrite E4stk, HS1; exact Estk|]. split; [rewrite E4flag, HF1; exact Eflag|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; apply HCS1; rewrite Ecs; exact Hx|].
    split; [rewrite E4vol; clear - HV1 Evol HV; lia|].
    split; [rewrite E4fr; clear - HFR1 Efr HF; lia|].
    split; [exact HM4|].
    split.
    { pose proof MX1 as [(CX3 & _ & _ & _ & _ & OWN3) _]. pose proof OUT1 as [OU1 _].
      eapply (mpd_at_heap_presx asegs L) with (LBp := LBc ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
        [exact MX1| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2))| exact MI1| exact MI0
        | | | exact I| intros _; exact I|].
      - rewrite OU1. eapply client_range_temp; [eapply d4_crw; eapply mpd_writableA_keep; exact XW| clear; lia|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff.
        destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact OUT1| exact Hb]| right; exact Hb].
      - intros EO. rewrite EO in OWN3. destruct OWN3 as (N1 & XIN & _).
        eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia].
      - intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dXc) eqn:EO; try (destruct Hb; fail).
        destruct Hb as [<-|[]]. destruct OWN3 as (_ & XIN & _). exact XIN. }
    split; [exact OUT1|].
    split; [intros b Hb; destruct (FRA1 b Hb) as [K|K]; [left; exact K| right; eapply d4_fresh_drop; exact K]|].
    split; [| cbn [md_n]; exact HSZ]. split; [split; [exact HRV| exact HR]|]. split; [exact AD1|]. split; [exact PD1|].
    split; [exact FRS1| exact NM1].
  Qed.

  #[using="Type"] Lemma d3_uwc_presA : forall (LBq LFq : list blk) (SPq SSPq TOPq : Z) (Wq : list ivl) (mq mq' : mem) (vq Fq dq : Z),
      presA asegs R LBq LFq SPq SSPq TOPq Wq mq mq' -> uwc asegs mq (arl_stklo R) TOPq vq Fq dq -> SPq <= Fq ->
      (forall a, Fq <= a < TOPq -> outside Wq a) -> 0 <= Fq -> TOPq <= 2^64 -> uwc asegs mq' (arl_stklo R) TOPq vq Fq dq.
  Proof.
    intros LBq LFq SPq SSPq TOPq Wq mq mq' vq Fq dq [P _] UW0 HSP HW HF0 HT. eapply uwc_transport; [exact UW0|].
    intros a Ha. apply (proj1 (P a ltac:(clear - Ha HSP HF0 HT; lia) ltac:(left; clear - Ha HSP; lia) (HW a Ha))).
  Qed.

  #[using="Type"] Lemma d3_uwc_frame_save : forall (mq : mem) (TOPq : Z) (w0 : word) (spv spq dq : Z),
      ro_cells asegs mq (spv - 16) [C8 w0] -> uwc asegs mq (arl_stklo R) TOPq (bv_unsigned w0) spv dq ->
      spq + 16 <= spv -> spv mod 8 = 0 -> 0 <= dq -> uwc asegs mq (arl_stklo R) TOPq spv spq (dq + 1).
  Proof.
    intros mq TOPq w0 spv spq dq RO UW0 H1 H2 Hd.
    pose proof (bv_unsigned_in_range 64 w0) as XR. unfold bv_modulus in XR. cbn [Z.pow Z.of_N Pos.pow] in XR.
    rewrite <- (Z_to_bv_bv_unsigned w0) in RO.
    eapply uwc_frame; [exact H1| exact H2| exact XR| exact Hd| exact RO| exact UW0].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d3_step : forall (D : nat) (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z),
      MD_BASE h1 m1 FB sp1 ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      md_sg dB = 1 -> 0 < mpd_abs dB ->
      (forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
         XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
         BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
         MD_CELLS mc FB SHB ->
         0 <= mpd_val dXc < Z.of_nat D * mpd_abs dB ->
         md_n dXc <= NZ -> v <= PHIb -> f <= FRb ->
         aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
           (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) xs5 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                    (Z_to_bv 64 FB) xs8 xs9 xs10 s11 xt3 xt4 xt5 xt6)
               F (Z_to_bv 64 0xa0674) fc None mc (seg_rom asegs))) ->
      forall (v f : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd)
        (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
        XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
        BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
        MD_CELLS mc FB SHB ->
        0 <= mpd_val dXc < Z.of_nat (S D) * mpd_abs dB ->
        md_n dXc <= NZ -> v <= PHIb -> f <= FRb ->
        aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
          (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) xs5 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                   (Z_to_bv 64 FB) xs8 xs9 xs10 s11 xt3 xt4 xt5 xt6)
              F (Z_to_bv 64 0xa0674) fc None mc (seg_rom asegs)).
  Proof.
    intros D h1 m1 FB sp1 MB DBJ SGB BPOS IH v f hc LBc mc dXc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6
      J B MC VR HSZ HV HF.
    jc_open. basic_factsA hc. pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof MB as MB'. unfold MD_BASE in MB'.
    destruct MB' as (SP1 & SP1M & F64 & FRSH & JC1 & PRES & Ecs & Etop & Estk & Eflag & Evol & Efr & HKI).
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO2 & ACP2 & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NSX OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    cbn [app] in HH1. cbn [md_addr md_pad] in AD1, PD1, OX1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO3 NS1 LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1, Estk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    assert (SCSa : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]).
    destruct (stk_split asegs mc lo sp1 (bv_unsigned sp - 96) ST1 ltac:(clear - SP1 SLO2 NEEDR; lia)) as [STa STb].
    assert (NNX : 1 <= md_n dXc -> md_own dXc <> LNull) by (intros N1 EN; destruct (OWN0 EN) as (_ & N0 & _); clear - N0 N1; lia).
    assert (NNB : 1 <= md_n dB -> md_own dB <> LNull) by (intros N1 EN; destruct (OWNE0 EN) as [_ N0]; clear - N0 N1; lia).
    assert (PX : md_own dXc = LHeap -> 0 < md_p dXc)
      by (intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & _ & _ & _ & P0 & _); exact P0).
    assert (PB : md_own dB = LHeap -> 0 < md_p dB)
      by (intros EH; ddestruct (OWNE1 ltac:(rewrite EH; discriminate)) as (_ & P0 & _); exact P0).
    assert (OXL : 1 <= md_n dXc -> aobj asegs AL (hcs asegs R HIA hc) mc (md_p dXc) (4 * md_n dXc))
      by (intros N1; ddestruct (OWN1 (NNX N1)) as (_ & _ & _ & _ & _ & _ & _ & _ & OB' & _); exact OB').
    assert (OBL : 1 <= md_n dB -> aobj asegs AL (hcs asegs R HIA hc) mc (md_p dB) (4 * md_n dB))
      by (intros N1; apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B); exact (NNB N1)).
    assert (XLX : 1 <= md_n dXc -> md_p dXc + 4 * md_n dXc <= lo \/ sp1 <= md_p dXc)
      by (intros N1; destruct (XLS1 (NNX N1)) as [K|K]; [left; exact K| right; clear - K SP1; lia]).
    assert (XLB : 1 <= md_n dB -> md_p dB + 4 * md_n dB <= lo \/ sp1 <= md_p dB)
      by (intros N1; ddestruct (OWNE1 (NNB N1)) as (_ & _ & _ & _ & K & _); destruct K as [K|K]; [left; exact K| right; clear - K SP1; lia]).
    pose proof (opnd_atA_mpd_back _ _ _ _ _ _ _ _ _ MB0 (bj_at _ _ _ _ _ _ _ _ _ _ B)) as MBc.
    zstep. zstep. zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { pose proof CMP as CMPc. unfold mpi_cmp_mpi_stmtA in CMPc.
      eapply (CMPc (hcs asegs R HIA hc)) with (LB := LBc) (dX := dXc) (dY := dB) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD1;
        first [ exact MX1 | exact MBc | exact PX | exact PB | exact MI1 | exact CSOK | exact ALWF
              | exact (hm_abase asegs R HIA hc LBc _ mc HH1)
              | exact OX1 | exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B) | exact OXL | exact OBL | exact XLX | exact XLB
              | exact STa | exact SCSa | reflexivity
              | (clear - LO0; lia)
              | (clear - SLO2 SP1 NEEDR; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (destruct DSX as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (destruct ES as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | match goal with |- ?g => idtac "D3CMP-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold mpi_cmp_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    pose proof FRSH as (F0 & F1 & F2 & F3).
    assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA hc _ _ mc FB 64 HH1 INF) as CFBc.
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
    assert (SBND : hl_data_hi L <= Z.shiftr FB 3 + al_sb AL /\ Z.shiftr FB 3 + al_sb AL + 8 <= alloc_ceiling).
    { pose proof (hcs_shadow_band asegs R HIA hc FB (CFBc FB ltac:(clear; lia))) as SBlo.
      pose proof (hcs_shadow_band asegs R HIA hc (FB + 8 * 7) (CFBc (FB + 8 * 7) ltac:(clear; lia))) as SBhi.
      rewrite shadow_of_plus in SBhi. unfold shadow_of in SBlo, SBhi. rewrite <- SHFB in SBlo, SBhi. clear - SBlo SBhi. lia. }
    assert (FSHLO : Z.shiftr FB 3 + al_sb AL + 8 <= lo) by (clear - SBND ALO2 LOS; lia).
    assert (HH2 : HM asegs R HIA hc LBc ((FB, 64) :: LF) m2).
    { eapply hm_munch; [exact HH1| exact MU2| exact WM2|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite ?HT1, ?Etop. clear - Ha LOS SP1 TOP. lia. }
    assert (WC2 : w_client (hcs asegs R HIA hc) [(lo, sp1)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; exact SCSa| apply Forall_nil]. }
    pose proof (stk_transport_disjoint asegs [(lo, sp1)] mc m2 _ _ STb MU2 WM2
                  ltac:(cbn [disjoint_from]; split; [right; clear; lia| exact I])) as STb2.
    assert (STc2 : stk asegs m2 lo (bv_unsigned sp - 96)) by (eapply stk_merge; [exact ST2| exact STb2| clear - SP1 SLO2 NEEDR; lia]).
    assert (ETA : mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) (md_limbs dXc) (md_pad dXc) (md_own dXc) = dXc)
      by (destruct dXc; reflexivity).
    pose proof (xa_scratch asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 [] v f hc LBc mc dXc lo sp1 m2
                  J MU2 WM2 MI2 STc2 HH2 (Z.le_refl lo) ltac:(clear - SP1; lia)) as XJ2.
    rewrite ETA in XJ2.
    assert (B2 : BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc m2 dXc).
    { eapply bja_munch; first [exact J | exact B | exact MU2 | exact WM2 | exact WC2 | idtac].
      - cbn [disjoint_from]. split; [clear - ES SP1; lia| exact I].
      - intros BN. ddestruct (OWNE1 BN) as (_ & _ & _ & _ & K & _). cbn [disjoint_from]. split; [clear - K SP1; lia| exact I]. }
    assert (MC2 : MD_CELLS m2 FB SHB).
    { destruct MC as ((w0 & w1 & w2 & FHD) & FSH & (wl & LIMB) & SSH).
      split; [exists w0, w1, w2; eapply (rw_cells_transport asegs [(lo, sp1)] mc m2); [exact FHD| exact MU2| exact WM2|];
              change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2])) with 24; cbn [disjoint_from]; split; [left; clear - FBLO; lia| exact I]|].
      split; [eapply (rw_cells_transport asegs [(lo, sp1)] mc m2); [exact FSH| exact MU2| exact WM2|];
              change (Z.of_nat (cells_size SHB)) with 8; cbn [disjoint_from]; split; [left; clear - FSHLO; lia| exact I]|].
      split; [exists wl; eapply (rw_cells_transport asegs [(lo, sp1)] mc m2); [exact LIMB| exact MU2| exact WM2|];
              change (Z.of_nat (cells_size [C4 wl])) with 4; cbn [disjoint_from]; split; [left; clear - FBLO; lia| exact I]|].
      eapply sshad_munch; [exact CSOK| exact WC2| | exact MU2| exact WM2| exact SSH].
      eapply crange_sub; [exact SCS0| clear - SLOS; lia| rewrite HS1, Estk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]. }
    assert (VB : mpd_val dB = mpd_abs dB) by (unfold mpd_val, mpd_abs; rewrite SGB; clear; lia).
    zstep. if_cases KS; zify_cond KS.
    - assert (GE : mpd_val dB <= mpd_val dXc).
      { destruct (Z.sgn_spec (mpd_val dXc - mpd_val dB)) as [[Hn Hs]|[[Hn Hs]|[Hn Hs]]]; rewrite Hs in KS;
          [clear - Hn; lia| clear - Hn; lia| exfalso; clear - KS; Z.div_mod_to_equations; lia]. }
      pose proof (mpd_abs_nonneg dXc) as NNA.
      assert (EVX : mpd_val dXc = md_sg dXc * mpd_abs dXc) by reflexivity.
      assert (SX1 : md_sg dXc = 1).
      { destruct SG1' as [E|E]; [exact E| exfalso]. rewrite E in EVX. clear - EVX GE VB BPOS NNA. lia. }
      pose proof FR1 as SV. unfold MD_FRAME_A, aa_frame96 in SV.
      chunk_split SV 10%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp - 96 + 80) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      assert (T64 : hstkhi asegs R HIA h <= 2^64) by (apply hstkhi_le64; clear - LOS LOSP SPR; lia).
      assert (UWc : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { destruct UWX as [[XL _]|D28]; [| apply uwc_cap; exact D28].
        eapply (d3_uwc_presA _ _ (bv_unsigned sp) (arl_stklo R) _ [(X, X + 16)] m1 mc);
          [rewrite <- Estk; exact HPX1| | clear; lia| intros a Ha; cbn [outside]; split; [clear - XL Ha LOS LOSP; lia| exact I]| clear - SPR; lia| exact T64].
        eapply (d3_uwc_presA _ _ (bv_unsigned sp) (arl_stklo R) _ [] m m1);
          [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear; lia| intros a Ha; exact I| clear - SPR; lia| exact T64]. }
      assert (UWF : uwc asegs m2 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
      { eapply (uwc_munch asegs [(lo, sp1)] mc m2); [| exact MU2| clear - SP1R; lia| exact T64| intros a Ha; cbn [outside]; split; [clear - Ha; lia| exact I]].
        eapply (d3_uwc_frame_save mc _ s0 (bv_unsigned sp) sp1 d); [exact (proj1 SV0)| exact UWc| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
      pose proof XJ2 as [_ _ _ _ _ _ _ _ _ _ MX2 _ _ _ _ _ _ _ OX2 _ _ _].
      pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ XJ2) as CWX. rewrite <- HT1 in CWX.
      pose proof (xa_crX _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ lo XJ2 ltac:(clear - LOSP; lia)) as CRX1. cbn [app] in CRX1.
      destruct (bja_client _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ DBJ [] v f hc LBc m2 dXc LBc lo XJ2 B2 ltac:(intros bq Hb _; exact Hb) ltac:(clear - LOSP; lia))
        as [CRB1 CRBL1].
      pose proof DBJ as [MBj OBj CRBj CRBLj SXBj BIMGj]. dpose OBj as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_own md_p md_n] in SXBj, OB1, OB2, OB3, OB4, OB5.
      pose proof (HASN (-1) (or_intror eq_refl)) as SPc. unfold add_sub_mpi_ng_stmtA_oz in SPc.
      zstep. zstep. zstep. zstep. zstep.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply SPc with (h := hc) (LB := LBc) (LF := (FB, 64) :: LF) (dX := dXc) (dA := dXc) (dB := dB) (lo := lo) (d := d + 1);
          rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD1;
          first [ exact HH2 | exact HK1 | exact MX2 | exact NSX | exact ST2 | exact LOS | exact TPV | exact MI2 | exact CRX1 | exact CRB1 | exact CRBL1
                | exact IB2 | reflexivity
                | lazymatch goal with
                  | |- opnd_atA _ _ _ _ _ _ dB => eapply opnd_atA_SP_le; [exact (bj_at _ _ _ _ _ _ _ _ _ _ B2)| clear - SP1; lia]
                  | |- mpd_sep dXc dXc => left; reflexivity
                  | |- mpd_sep dXc dB => right; rewrite AD1; clear - SXBj; lia
                  | |- opnd_sep dXc dXc _ _ =>
                      unfold opnd_sep; rewrite ?AD1;
                      split; [intros NN; destruct (OWN1 NN) as (EH & _); exact (XP1 EH)|];
                      split; [exact XP1|]; split; [left; reflexivity|]; split; [clear - DSX SP1; lia|];
                      intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia]
                  | |- opnd_sep dXc dB _ _ =>
                      unfold opnd_sep; rewrite ?AD1;
                      split; [exact OB1|]; split; [exact (bj_sepS _ _ _ _ _ _ _ _ _ _ B2)|];
                      split; [right; destruct (md_own dXc) eqn:EOX; [left; discriminate| | left; discriminate];
                              destruct (md_own dB) eqn:EOB; [right; left; reflexivity| |];
                              right; right; apply (bj_sepL _ _ _ _ _ _ _ _ _ _ B2 EOX); rewrite EOB; discriminate|];
                      split; [clear - ES SP1; lia|]; intros BN; ddestruct (OWNE1 BN) as (_ & _ & _ & _ & ESK & _); clear - ESK SP1; lia
                  | |- md_own dXc = LHeap -> client_range _ _ _ (md_p dXc) _ =>
                      intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & XIN & _);
                      eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
                  | |- mpd_writableA _ _ _ _ _ dXc =>
                      split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear - SP1; lia| rewrite AD1; exact XP1]
                  | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia]
                  | |- _ <= sp1 - _ - _ => clear - SLO2 SP1; lia
                  | |- sp1 <= htop _ _ _ _ => rewrite HT1, Etop; clear - SP1 TOP; lia
                  | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                  | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX2| intros E; exfalso; exact (NSX E)]
                  | |- mpd_aobjA _ _ _ _ dB =>
                      split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B2)| intros E; apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B2); rewrite E; discriminate]
                  | |- X <> X -> _ => intros NE; exfalso; exact (NE eq_refl)
                  | |- md_own dXc = LStatic -> _ => intros E; exfalso; exact (NSX E)
                  | |- md_own dB = LStatic -> _ + 8 <= 2^47 => intros E; eapply mpd_at_static47; [exact MB0| exact E]
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold add_sub_PHI0; clear - BUD HV HV1 Evol; lia
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold add_sub_FR0; clear - BUDF HF HFR1 Efr; lia
                  | |- uwc _ _ _ _ _ _ _ => rewrite HS1, Estk; exact UWF
                  | |- uw_obj _ X 16 _ => pose proof UWX as U; unfold uw_obj in U |- *; clear - U; lia
                  | |- uw_obj _ (md_addr dB) 16 _ => pose proof UWB as U; unfold uw_obj in U |- *; clear - U; lia
                  | |- _ * md_sg dB = - md_sg dXc => rewrite SGB, SX1; reflexivity
                  | |- mpd_abs dB <= mpd_abs dXc -> _ => intros _; clear; lia
                  | |- mpd_abs dXc < mpd_abs dB -> _ => intros LT; exfalso; rewrite SX1 in EVX; clear - LT EVX GE VB; lia
                  end
                | match goal with |- ?g => idtac "D3ASN-PRE-LEFT:" g end ]. }
      cbv beta. intros ms3 mo3 dd_H. ddestruct dd_H as (mo1 & [HK1 MF1] & PO). unfold mpi_binop_postA in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m3 & mo2 & h2 & LB2 & dX2 & r
                       & E & MI3 & ST3 & MF2 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRA3 & CR).
      injection E as E1 E2. subst ms3 mo3.
      rewrite ?(unsigned_lit sp1) in ST3, HP3 by exact SP1R. rewrite AD1 in HP3.
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?z)] =>
        replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      pose proof CR as [[CR1 BK] NSZ].
      assert (CRX : client_range L (LB ++ fdata LF) lo X 16).
      { pose proof XW as [CW _]. intros a Ha. destruct (CW a Ha) as [C|[C|C]];
          [left; clear - C SLO NEEDR FS16; lia| right; left; exact C| right; right; exact C]. }
      assert (APX : X + 16 <= FB \/ FB + 64 <= X).
      { destruct (fresh_apart_client R LB LF lo X 16 FB 64 FRSH CRX ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO2 LOS; lia)) as [C|C];
          [right; exact C| left; exact C]. }
      pose proof (presA_stk asegs R _ _ _ _ _ _ m2 m3 sp1 (bv_unsigned sp - 96) HP3 STb2 (Z.le_refl sp1)
                    ltac:(cbn [disjoint_from md_addr]; split; [clear - DSX SP1 SLO2 NEEDR; lia| exact I])) as STb3.
      assert (ST3' : stk asegs m3 lo (bv_unsigned sp - 96)) by (eapply stk_merge; [exact ST3| exact STb3| clear - SP1 SLO2 NEEDR; lia]).
      pose proof (xa_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 _ _ _ _ _ _ m3 h2 LB2 dX2 sp1
                    (add_sub_PHI0 dXc dXc dB) (add_sub_FR0 (d + 1)) XJ2 ltac:(clear - SP1 SLO2 NEEDR; lia)
                    ltac:(unfold add_sub_PHI0; clear; lia) ltac:(unfold add_sub_FR0; clear; lia)
                    MI3 ST3' HP3 HT3 HS3 HF3 HCS3 HV3 HFR3 HH3 MX3 OUT3 BK FRA3) as J3.
      pose proof (bja_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 dB DBJ _ _ _ _ _ _ m3 h2 LB2 dX2 sp1
                    XJ2 B2 ltac:(clear - SP1 SLO2 NEEDR; lia) MI3 HP3 HCS3 HH3 MX3 OUT3 FRA3) as B3.
      assert (MC3 : MD_CELLS m3 FB SHB).
      { destruct MC2 as ((w0 & w1 & w2 & FHD) & FSH & (wl & LIMB) & SSH).
        split; [exists w0, w1, w2; eapply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 FB _ HP3); [exact FHD| |];
                cbn [cells_size csize Nat.add];
                [eapply client_range_block; [apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia]
                | cbn [disjoint_from md_addr]; split; [clear - APX; lia| exact I]]|].
        split; [eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) _ _ _ _ _ _ m2 m3 FB SHB CSOK);
                [cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFBc| clear; lia| clear; lia]
                | clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP3| exact FSH
                | intros c Hc; cbn [cells_size csize Nat.add] in Hc; right; right; left; exists (FB, 64);
                  split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia]]|].
        split; [exists wl; eapply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 (FB + 32) _ HP3); [exact LIMB| |];
                cbn [cells_size csize Nat.add];
                [eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia]
                | cbn [disjoint_from md_addr]; split; [clear - APX; lia| exact I]]|].
        eapply (presA_sshad asegs R); [exact HP3| exact SSH| exact SLOS|].
        rewrite HS1, Estk. pose proof (hm_top asegs R HIA h LB LF m HH). clear - H TOP. lia. }
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK3 (mo_frame_trans _ _ _ MF1 MF2))).
      pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
      pose proof (munch_refl ([] : list ivl) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
      assert (VR' : mpd_val dXc < Z.of_nat D * mpd_abs dB + mpd_abs dB)
        by (pose proof (proj2 VR) as K; rewrite Nat2Z.inj_succ, Z.mul_succ_l in K; exact K).
      zstep. if_cases KR; zify_cond KR;
        destruct CR1 as [(-> & CV)| ->];
        first [ exfalso; apply KR; reflexivity
              | exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; first [discriminate KR| lia| congruence]
              | idtac ].
      all: first
        [ eapply (IH (v + add_sub_PHI0 dXc dXc dB) (f + add_sub_FR0 (d + 1)) h2 LB2 m3 dX2);
            [exact J3| exact B3| exact MC3| rewrite CV; clear - VR VR' GE VB; lia| clear - NSZ HSZ; lia
            | unfold add_sub_PHI0; clear - HV; lia| unfold add_sub_FR0; clear - HF; lia]
        | eapply (md_join h1 m1 FB sp1 (v + add_sub_PHI0 dXc dXc dB) (f + add_sub_FR0 (d + 1)) h2 LB2 m3 dX2 MBEDTLS_ERR_MPI_ALLOC_FAILED);
            [exact MB| exact J3| exact MC3| intros E; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in E; clear - E; lia
            | unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| clear - NSZ HSZ; lia
            | unfold add_sub_PHI0; clear - HV; lia| unfold add_sub_FR0; clear - HF; lia]
        | match goal with |- ?g => idtac "D3BR-LEFT:" g end ].
    - zstep. zstep.
      eapply (md_join h1 m1 FB sp1 v f hc LBc m2 dXc 0); [exact MB| exact XJ2| exact MC2| | clear; lia| exact HSZ| exact HV| exact HF].
      intros _. split; [exact (proj1 VR)|]. rewrite <- VB.
      destruct (Z.sgn_spec (mpd_val dXc - mpd_val dB)) as [[Hn Hs]|[[Hn Hs]|[Hn Hs]]]; rewrite Hs in KS;
        [exfalso; clear - KS; Z.div_mod_to_equations; lia| exfalso; clear - KS; Z.div_mod_to_equations; lia| clear - Hn; lia].
    all: match goal with |- ?g => idtac "D3-LEFT:" g end.
  Qed.

  Definition mdL2_stmt (D : nat) : Prop :=
    forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA) (LBc : list blk)
      (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      md_sg dB = 1 -> 0 < mpd_abs dB ->
      0 <= mpd_val dXc < Z.of_nat D * mpd_abs dB ->
      md_n dXc <= NZ -> v <= PHIb -> f <= FRb ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) xs5 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                 (Z_to_bv 64 FB) xs8 xs9 xs10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa0674) fc None mc (seg_rom asegs)).
  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"] Lemma md_L2 : forall D, mdL2_stmt D.
  Proof.
    induction D as [|D IH]; unfold mdL2_stmt;
      intros h1 m1 FB sp1 v f hc LBc mc dXc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6
        MB J DBJ B MC SGB BPOS VR HSZ HV HF.
    - exfalso. clear - VR. lia.
    - unfold mdL2_stmt in IH.
      eapply (d3_step D h1 m1 FB sp1 MB DBJ SGB BPOS); [| exact J| exact B| exact MC| exact VR| exact HSZ| exact HV| exact HF].
      intros v' f' hc' LBc' mc' dXc' yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys8 ys9 ys10 y3 y4 y5 y6 J' B' MC' VR' HSZ' HV' HF'.
      exact (IH h1 m1 FB sp1 v' f' hc' LBc' mc' dXc' yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys8 ys9 ys10 y3 y4 y5 y6
                MB J' DBJ B' MC' SGB BPOS VR' HSZ' HV' HF').
  Qed.

  #[using="Type"] Lemma d2_rb_wa : forall x : word, wa (bv_unsigned x) = x.
  Proof.
    intros x. apply bv_eq. rewrite wa_unsigned; [reflexivity|].
    pose proof (bv_unsigned_in_range 64 x) as HR. unfold bv_modulus in HR. exact HR.
  Qed.

  #[using="Type"] Lemma d2_rb_wv : forall (m0 m2 : mem) (x : word), m0 x = m2 x -> wview asegs m0 x = wview asegs m2 x.
  Proof. intros m0 m2 x E. unfold wview. rewrite E. reflexivity. Qed.

  #[using="Type"] Lemma d2_rb_wr : forall (m0 : mem) (A n : Z) (x : word), wr_at asegs m0 A n ->
      A <= bv_unsigned x < A + n -> wview asegs m0 x <> None.
  Proof.
    intros m0 A n x (_ & _ & H) Hx. rewrite <- (d2_rb_wa x).
    replace (bv_unsigned x) with (A + (bv_unsigned x - A)) by (clear; lia). apply H. clear - Hx. lia.
  Qed.

  #[using="Type"] Lemma d2_rb_mk : forall (m0 m2 : mem) (a b : Z), exists m3 : mem, forall x : word,
      (a <= bv_unsigned x < b /\ m3 x = m2 x) \/ (~ (a <= bv_unsigned x < b) /\ m3 x = m0 x).
  Proof.
    intros m0 m2 a b.
    exists (fun x => if ((a <=? bv_unsigned x) && (bv_unsigned x <? b))%bool then m2 x else m0 x).
    intros x. cbv beta. clear - x.
    destruct (Z.leb_spec a (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) b); cbn [andb];
      first [left; split; [lia| reflexivity] | right; split; [lia| reflexivity]].
  Qed.

  #[using="Type"] Lemma d2_rb_mk2 : forall (m0 m2 : mem) (a b a2 b2 : Z), exists m3 : mem, forall x : word,
      ((a <= bv_unsigned x < b \/ a2 <= bv_unsigned x < b2) /\ m3 x = m2 x)
      \/ (~ (a <= bv_unsigned x < b) /\ ~ (a2 <= bv_unsigned x < b2) /\ m3 x = m0 x).
  Proof.
    intros m0 m2 a b a2 b2.
    exists (fun x => if ((a <=? bv_unsigned x) && (bv_unsigned x <? b) || (a2 <=? bv_unsigned x) && (bv_unsigned x <? b2))%bool
                     then m2 x else m0 x).
    intros x. cbv beta. clear - x.
    destruct (Z.leb_spec a (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) b);
      destruct (Z.leb_spec a2 (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) b2); cbn [andb orb];
      first [left; split; [lia| reflexivity] | right; split; [lia| split; [lia| reflexivity]]].
  Qed.

  #[using="Type"] Lemma d2_rb_mi : forall (m0 m2 m3 : mem), mem_inv asegs m0 -> mem_inv asegs m2 ->
      (forall x : word, m3 x = m0 x \/ m3 x = m2 x) -> mem_inv asegs m3.
  Proof.
    intros m0 m2 m3 H0 H2 G a b E. destruct (G a) as [G'|G']; rewrite G' in E; [exact (H0 a b E)| exact (H2 a b E)].
  Qed.

  #[using="Type"] Lemma d2_rb_g_pt : forall (m1 mc mc' m1' : mem) (W : list ivl) (x : word),
      munch W mc mc' -> mc x = m1 x -> (m1' x = mc' x \/ (outside W (bv_unsigned x) /\ m1' x = m1 x)) ->
      mc' x = m1' x /\ (wview asegs m1' x <> None -> wview asegs mc' x <> None).
  Proof.
    intros m1 mc mc' m1' W x MU E G.
    assert (E' : mc' x = m1' x).
    { destruct G as [G|[O G]]; [symmetry; exact G| rewrite G, <- E; apply MU; exact O]. }
    split; [exact E'|]. rewrite (d2_rb_wv mc' m1' x E'). auto.
  Qed.

  #[using="Type"] Lemma d2_rb_presA_graft : forall (K LFk : list blk) (SPk SSP TOP : Z) (W0 W : list ivl) (m1 mc mc' m1' : mem),
      presA asegs R K LFk SPk SSP TOP W0 m1 mc -> munch W mc mc' ->
      (forall x : word, m1' x = mc' x \/ (outside W (bv_unsigned x) /\ m1' x = m1 x)) ->
      presA asegs R K LFk SPk SSP TOP W0 m1' mc'.
  Proof.
    intros K LFk SPk SSP TOP W0 W m1 mc mc' m1' HP MU G.
    destruct HP as [HP1 HP2]. split.
    - intros x Hx Hc Ho. destruct (HP1 x Hx Hc Ho) as [E _]. exact (d2_rb_g_pt m1 mc mc' m1' W (wa x) MU E (G (wa x))).
    - intros c Hc Hr. destruct (HP2 c Hc Hr) as [E _]. exact (d2_rb_g_pt m1 mc mc' m1' W _ MU E (G _)).
  Qed.

  #[using="Type"] Lemma d2_rb_presA_irr : forall (LBk LFk : list blk) (SPk SSP TOP : Z) (W0 W : list ivl) (m0 m2 m3 : mem),
      presA asegs R LBk LFk SPk SSP TOP W0 m0 m2 -> munch W m2 m3 -> wmono asegs m2 m3 ->
      (forall a, 0 <= a < 2^64 -> client_addr L (LBk ++ fdata LFk) SPk a -> outside W a) ->
      (forall c, cshd R LBk LFk SSP TOP c -> outside W (shadow_of AL c)) ->
      presA asegs R LBk LFk SPk SSP TOP W0 m0 m3.
  Proof.
    intros LBk LFk SPk SSP TOP W0 W m0 m2 m3 [P SH] MU WM HC HS. split.
    - intros x Hx Hcl Ho. destruct (P x Hx Hcl Ho) as [E1 W1]. split; [| intros Hw; apply WM; apply W1; exact Hw].
      rewrite <- E1. apply MU. rewrite wa_unsigned by (clear - Hx; lia). exact (HC x Hx Hcl).
    - intros c Hc Hr. destruct (SH c Hc Hr) as [E1 W1]. split; [| intros Hw; apply WM; apply W1; exact Hw].
      rewrite <- E1. apply MU. rewrite wa_unsigned by (clear - Hr; lia). exact (HS c Hc).
  Qed.

  #[using="Type"] Lemma d2_rb_dj : forall (CS : Z -> Prop) (FB A n : Z), cs_ok AL CS -> crange CS (FB + 32) 8 ->
      crange CS A n -> 0 < n -> (A + n <= FB \/ FB + 64 <= A) -> FB mod 64 = 0 ->
      disjoint_from [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] A n.
  Proof.
    intros CS FB A n OK CF CA Hn HA F64.
    assert (ESH : Z.shiftr FB 3 + al_sb AL + 4 = shadow_of AL (FB + 32)).
    { clear. unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      replace (FB + 32) with (FB + 4 * 8) by lia. rewrite Z.div_add by lia. lia. }
    cbn [disjoint_from]. split; [clear - HA; lia|]. split; [| exact I].
    destruct (apart_client_shadow AL CS A n (FB + 32) _ 1 OK CA ltac:(intros x Hx; exact (CF x ltac:(clear - Hx; lia))) ESH Hn ltac:(clear; lia))
      as [K|K]; clear - K; lia.
  Qed.

  #[using="Type"] Lemma d2_rb_aobj : forall (CS : Z -> Prop) (FB : Z) (m0 m2 : mem) (A n : Z), cs_ok AL CS ->
      crange CS (FB + 32) 8 -> FB mod 64 = 0 -> (A + n <= FB \/ FB + 64 <= A) ->
      munch [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] m0 m2 ->
      aobj asegs AL CS m0 A n -> aobj asegs AL CS m2 A n.
  Proof.
    intros CS FB m0 m2 A n OK CF F64 HA MU [HC HS]. split; [exact HC|].
    intros a Ha. destruct (HS a Ha) as (k & RD & HK). exists k. split; [| exact HK].
    eapply bytes_at_transport; [exact RD| exact MU|]. cbn [length Z.of_nat Pos.of_succ_nat].
    destruct OK as (K1 & _). destruct (K1 a (HC a Ha)) as (R0 & R1 & R2 & NCS).
    cbn [disjoint_from]. split; [| split; [| exact I]].
    - destruct (Z_lt_le_dec (shadow_of AL a) (FB + 32)) as [L1|L1]; [left; clear - L1; lia|].
      destruct (Z_lt_le_dec (shadow_of AL a) (FB + 36)) as [L2|L2]; [| right; clear - L2; lia].
      exfalso. apply NCS. exact (CF (shadow_of AL a) ltac:(clear - L1 L2; lia)).
    - clear - Ha HA F64. unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma d2_rb_wrfa : forall (LBk LFk : list blk) (SPk TOP A n N k : Z),
      fresh_apart R LBk LFk N k -> client_wrange L (LBk ++ fdata LFk) SPk TOP A n ->
      alloc_ceiling <= SPk -> 0 < n -> 0 < k -> A + n <= N \/ N + k <= A.
  Proof.
    intros LBk LFk SPk TOP A n N k (F0 & F1 & F2 & F3) CW HSP Hn Hk.
    apply (apart_by_pred (fun x => client_waddr L (LBk ++ fdata LFk) SPk TOP x) A n N k); [exact CW| | exact Hn| exact Hk].
    intros x Hx Hc. destruct Hc as [Hs|[[Hd _]|([Bb jb] & Hb & Hr)]]; [clear - Hx Hs F1 HSP; lia| clear - Hx Hd F2; lia|].
    cbn [fst snd] in Hr. destruct (F3 Bb jb Hb) as [K|K]; clear - K Hx Hr; lia.
  Qed.

  #[using="Type"] Lemma d2_rb_heapblk : forall (m0 : mem) (LBk : list blk) (d0 : mpd), mpd_at asegs m0 LBk d0 ->
      md_own d0 <> LNull -> md_own d0 <> LStatic -> 1 <= md_n d0 /\ In (md_p d0, 4 * md_n d0) LBk.
  Proof.
    intros m0 LBk d0 [(_ & _ & _ & _ & _ & OW) _] N1 N2. revert OW. destruct (md_own d0) eqn:EO; intros OW.
    all: first [ exfalso; first [exact (N1 EO)| exact (N1 eq_refl)| exact (N2 EO)| exact (N2 eq_refl)]
               | destruct OW as (K1 & K2 & _); split; [exact K1| exact K2] ].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d2_rb_dBfb : forall (h1 : HST asegs R HIA) (m1 : mem) (FB : Z),
      HM asegs R HIA h1 LB ((FB, 64) :: LF) m1 -> fresh_apart R LB LF FB 64 -> md_own dB <> LNull ->
      1 <= md_n dB /\ (md_p dB + 4 * md_n dB <= FB \/ FB + 64 <= md_p dB).
  Proof.
    intros h1 m1 FB HH1 (F0 & F1 & F2 & F3) NN. jc_open.
    pose proof MB0 as [(_ & _ & _ & LENB & _ & OW) _]. revert OW. destruct (md_own dB) eqn:EOB; intros OW.
    - exfalso. first [exact (NN EOB)| exact (NN eq_refl)].
    - destruct OW as (N1 & IN & _). split; [exact N1|].
      destruct (F3 (md_p dB) (4 * md_n dB) ltac:(apply in_or_app; left; exact IN)) as [K|K]; [right| left]; clear - K; lia.
    - destruct OW as (N1 & _ & P0 & BY & RO). split; [exact N1|].
      pose proof (u32ro_bound _ _ _ _ BY) as BB.
      pose proof (ROIMG (md_p dB + 0) (RO 0 ltac:(clear - N1; lia)) ltac:(clear - BB P0 N1 LENB; lia)) as I0.
      pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) (RO (4 * md_n dB - 1) ltac:(clear - N1; lia)) ltac:(clear - BB P0 N1 LENB; lia)) as I1.
      destruct (hm_apart asegs R HIA h1 _ _ _ HH1) as [HF _]. rewrite Forall_forall in HF.
      destruct (HF (FB, 64) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & AI). cbn [fst snd] in AI.
      clear - I0 I1 AI N1. lia.
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d2_rebase : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc mc' : mem) (dXc : mpd),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      munch [(lo, bv_unsigned sp - 96); (FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] mc mc' ->
      wmono asegs mc mc' -> mem_inv asegs mc' -> stk asegs mc' lo (bv_unsigned sp - 96) ->
      HM asegs R HIA hc LBc ((FB, 64) :: LF) mc' ->
      rw_cells asegs mc' (FB + 32) [C4 (Z_to_bv 64 0)] ->
      MD_CELLS mc' FB SHB ->
      exists m1' : mem,
        MD_BASE h1 m1' FB sp1
        /\ XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1' dX sp lo 96 MD_FRAME_A [] v f hc LBc mc' dXc
        /\ JBA asegs R HIA LB ((FB, 64) :: LF) m1' dX sp lo dB
        /\ BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc' dXc.
  Proof.
    intros h1 m1 FB sp1 v f hc LBc mc mc' dXc BASE XJ JB HBJ CELLS MU WM MI' ST' HH' RW0 CELLS'.
    pose proof BASE as (SP1 & SP1M & F64 & FRSH & JC1 & PRES1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI).
    pose proof FRSH as (F0 & F1 & F2 & F3).
    pose proof (art_lo asegs R HIA) as ALO.
    jc_open.
    pose proof JC1 as [Q1 Q2 Q3 Q4 HH1 MXd NSTd Q8 Q9 Q10 Q11 Q12 TOP1 Q14 Q15].
    pose proof XJ as [cMI cST cFR cHH cHT cHS cHF cHCS cHV cHFR cMX cAD cPD cNS cOUT cFRS cFRA cHPX cOX cXP cXLS cNM].
    pose proof HBJ as [BA BS BL BO BOL].
    pose proof JB as [JB0 JB1 JB2 JB3 JB4 JB5].
    dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    destruct XW as [CW _].
    assert (ACL : alloc_ceiling <= lo) by (clear - ALO LOS; lia).
    assert (LOSP : lo <= bv_unsigned sp - 96) by (clear - SLO NEEDR; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ACL; lia).
    pose proof (hcs_ok asegs R HIA hc) as OKc.
    pose proof (hcs_fake asegs R HIA hc ([] ++ LBc) ((FB, 64) :: LF) mc FB 64 cHH ltac:(left; reflexivity)) as CFc.
    assert (CF8 : crange (hcs asegs R HIA hc) (FB + 32) 8) by (intros x Hx; exact (CFc x ltac:(clear - Hx; lia))).
    pose proof (hcs_fake asegs R HIA h1 LB ((FB, 64) :: LF) m1 FB 64 HH1 ltac:(left; reflexivity)) as CF1.
    assert (ESH : Z.shiftr FB 3 + al_sb AL + 4 = shadow_of AL (FB + 32)).
    { clear. unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      replace (FB + 32) with (FB + 4 * 8) by lia. rewrite Z.div_add by lia. lia. }
    pose proof (hcs_shadow_band asegs R HIA hc (FB + 32) (CF8 (FB + 32) ltac:(clear; lia))) as SB.
    assert (SHLO : Z.shiftr FB 3 + al_sb AL + 5 <= lo) by (clear - SB ESH ACL; lia).
    assert (AX : X + 16 <= FB \/ FB + 64 <= X).
    { exact (d2_rb_wrfa LB LF (bv_unsigned sp) (htop asegs R HIA h) X 16 FB 64 FRSH CW
               ltac:(clear - ACL LOSP; lia) ltac:(clear; lia) ltac:(clear; lia)). }
    assert (AB : md_addr dB + 16 <= FB \/ FB + 64 <= md_addr dB).
    { destruct (fresh_apart_client0 R LB LF lo (md_addr dB) 16 FB 64 FRSH CRB ltac:(clear; lia) ltac:(clear; lia) ACL)
        as [K|[K|K]]; clear - K; lia. }
    pose proof (d2_rb_dBfb h1 m1 FB HH1 FRSH) as ABL.
    assert (DXh : disjoint_from [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] X 16).
    { exact (d2_rb_dj (hcs asegs R HIA hc) FB X 16 OKc CF8 (proj1 cOX) ltac:(clear; lia) AX F64). }
    assert (DBh : disjoint_from [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] (md_addr dB) 16).
    { exact (d2_rb_dj (hcs asegs R HIA hc) FB (md_addr dB) 16 OKc CF8 (proj1 BO) ltac:(clear; lia) AB F64). }
    assert (DBl : md_own dB <> LNull ->
                  disjoint_from [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] (md_p dB) (4 * md_n dB)).
    { intros NN. destruct (ABL NN) as [N1 AP].
      exact (d2_rb_dj (hcs asegs R HIA hc) FB (md_p dB) (4 * md_n dB) OKc CF8 (proj1 (BOL NN)) ltac:(clear - N1; lia) AP F64). }
    destruct (d2_rb_mk mc' mc lo (bv_unsigned sp - 96)) as (mc3 & G3).
    destruct (d2_rb_mk2 m1 mc' (FB + 32) (FB + 36) (Z.shiftr FB 3 + al_sb AL + 4) (Z.shiftr FB 3 + al_sb AL + 5)) as (m1' & G1).
    exists m1'.
    assert (MU1 : munch [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] m1 m1').
    { intros x O. cbn [outside] in O. destruct O as (O1 & O2 & _).
      destruct (G1 x) as [[IN _]|(_ & _ & E)]; [exfalso; destruct IN as [IN|IN]; [exact (O1 IN)| exact (O2 IN)]| exact E]. }
    assert (MU3 : munch [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] mc mc3).
    { intros x O. cbn [outside] in O. destruct O as (O1 & O2 & _).
      destruct (G3 x) as [[_ E]|[NS E]]; [exact E| rewrite E; apply MU; cbn [outside]; exact (conj NS (conj O1 (conj O2 I)))]. }
    assert (MU3' : munch [(lo, bv_unsigned sp - 96)] mc3 mc').
    { intros x O. cbn [outside] in O. destruct O as [O _].
      destruct (G3 x) as [[IN _]|[_ E]]; [exfalso; exact (O IN)| exact (eq_sym E)]. }
    assert (WM3 : wmono asegs mc mc3).
    { intros x Hw. destruct (G3 x) as [[_ E]|[_ E]]; rewrite (d2_rb_wv mc3 _ x E); [exact Hw| exact (WM x Hw)]. }
    assert (WM3' : wmono asegs mc3 mc').
    { intros x Hw. destruct (G3 x) as [[_ E]|[_ E]]; rewrite (d2_rb_wv mc3 _ x E) in Hw; [exact (WM x Hw)| exact Hw]. }
    assert (WVc : forall x : word, (FB + 32 <= bv_unsigned x < FB + 36
                                    \/ Z.shiftr FB 3 + al_sb AL + 4 <= bv_unsigned x < Z.shiftr FB 3 + al_sb AL + 5) ->
                                   wview asegs mc' x <> None).
    { intros x [IN|IN].
      - destruct RW0 as [_ WR]. apply (d2_rb_wr mc' (FB + 32) _ x WR).
        assert (SZ4 : Z.of_nat (cells_size [C4 (Z_to_bv 64 0)]) = 4) by reflexivity. clear - IN SZ4. lia.
      - destruct CELLS' as (_ & SH' & _ & _). destruct SH' as [_ WR]. apply (d2_rb_wr mc' _ _ x WR).
        assert (SZ8 : Z.of_nat (cells_size SHB) = 8) by reflexivity. clear - IN SZ8. lia. }
    assert (WM1 : wmono asegs m1 m1').
    { intros x Hw. destruct (G1 x) as [[IN E]|(_ & _ & E)]; rewrite (d2_rb_wv m1' _ x E); [exact (WVc x IN)| exact Hw]. }
    assert (MI3 : mem_inv asegs mc3).
    { apply (d2_rb_mi mc mc' mc3 cMI MI'). intros x. destruct (G3 x) as [[_ E]|[_ E]]; [left| right]; exact E. }
    assert (ST3 : stk asegs mc3 lo (bv_unsigned sp - 96)).
    { apply (stk_transport_disjoint asegs _ mc mc3 lo _ cST MU3 WM3). cbn [disjoint_from].
      split; [right; clear - FBLO; lia| split; [right; clear - SHLO; lia| exact I]]. }
    assert (FR3 : rw_cells asegs mc3 (bv_unsigned sp - 96) MD_FRAME_A).
    { apply (rw_cells_transport asegs _ mc mc3 _ _ cFR MU3 WM3). rewrite FSZ. cbn [disjoint_from].
      split; [right; clear - FBLO LOSP; lia| split; [right; clear - SHLO LOSP; lia| exact I]]. }
    assert (HMW : forall (LBk : list blk) (TOPk : Z),
               Forall (fun iv : ivl => forall a, fst iv <= a < snd iv -> hm_writable R LBk ((FB, 64) :: LF) TOPk a)
                 [(FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)]).
    { intros LBk TOPk. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; intros a Ha; unfold hm_writable.
      - left. right. right. exists (FB + 32, 64 - 40).
        split; [apply in_or_app; right; right; left; reflexivity| cbn [fst snd]; clear - Ha; lia].
      - right. exists (FB + 32).
        split; [right; exists (FB, 64); split; [left; reflexivity| cbn [fst snd]; clear; lia]| rewrite <- ESH; clear - Ha; lia]. }
    assert (HH3 : HM asegs R HIA hc ([] ++ LBc) ((FB, 64) :: LF) mc3).
    { eapply hm_munch; [exact cHH| exact MU3| exact WM3| exact (HMW ([] ++ LBc) (htop asegs R HIA hc))]. }
    assert (MX3 : mpd_at asegs mc3 LBc dXc).
    { eapply (mpd_at_munch_any asegs mc mc3 LBc dXc); [exact cMX| exact MU3| exact WM3| rewrite cAD; exact DXh|].
      intros NN. destruct (d2_rb_heapblk mc LBc dXc cMX NN cNS) as [N1 IN].
      destruct (hm_apart asegs R HIA hc _ _ _ cHH) as [_ BAc].
      destruct (d4_ba_app2 ([] ++ LBc) ((FB, 64) :: LF) _ _ FB 64 BAc IN ltac:(left; reflexivity)) as [K|K];
        exact (d2_rb_dj (hcs asegs R HIA hc) FB (md_p dXc) (4 * md_n dXc) OKc CF8
                 (hcs_block asegs R HIA hc ([] ++ LBc) ((FB, 64) :: LF) mc _ _ cHH IN) ltac:(clear - N1; lia) ltac:(clear - K; lia) F64). }
    assert (AO3 : aobj asegs AL (hcs asegs R HIA hc) mc3 X 16).
    { exact (d2_rb_aobj (hcs asegs R HIA hc) FB mc mc3 X 16 OKc CF8 F64 AX MU3 cOX). }
    assert (XJ3 : XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1' dX sp lo 96 MD_FRAME_A [] v f hc LBc mc3 dXc).
    { constructor; [exact MI3| exact ST3| exact FR3| exact HH3| exact cHT| exact cHS| exact cHF| exact cHCS| exact cHV| exact cHFR
                   | exact MX3| exact cAD| exact cPD| exact cNS| exact cOUT| exact cFRS| exact cFRA| | exact AO3| exact cXP| exact cXLS| exact cNM].
      apply (d2_rb_presA_graft _ _ _ _ _ _ _ m1 mc mc3 m1' cHPX MU3).
      intros x. destruct (G1 x) as [[IN E]|(N1 & N2 & E)].
      - left. rewrite E. destruct (G3 x) as [[IS _]|[_ E3]]; [exfalso; clear - IN IS FBLO SHLO; lia| exact (eq_sym E3)].
      - right. split; [cbn [outside]; exact (conj N1 (conj N2 I))| exact E]. }
    assert (MXd' : mpd_at asegs m1' LB dX).
    { eapply (mpd_at_munch_any asegs m1 m1' LB dX); [exact MXd| exact MU1| exact WM1| exact DXh|].
      intros NN. destruct (d2_rb_heapblk m1 LB dX MXd NN NSTd) as [N1 IN].
      destruct (F3 (md_p dX) (4 * md_n dX) ltac:(apply in_or_app; left; exact IN)) as [K|K];
        exact (d2_rb_dj (hcs asegs R HIA h1) FB (md_p dX) (4 * md_n dX) (hcs_ok asegs R HIA h1)
                 ltac:(intros y Hy; exact (CF1 y ltac:(clear - Hy; lia)))
                 (hcs_block asegs R HIA h1 LB ((FB, 64) :: LF) m1 _ _ HH1 IN) ltac:(clear - N1; lia) ltac:(clear - K; lia) F64). }
    assert (JC1' : JCA asegs R HIA h1 LB ((FB, 64) :: LF) m1' dX sp lo 96 MD_FRAME_A).
    { constructor; [exact Q1| exact Q2| exact Q3| exact Q4| | exact MXd'| exact NSTd| exact Q8| exact Q9| exact Q10| exact Q11| exact Q12
                   | exact TOP1| exact Q14| exact Q15].
      eapply hm_munch; [exact HH1| exact MU1| exact WM1| exact (HMW LB (htop asegs R HIA h1))]. }
    assert (PRES1' : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1').
    { destruct PRES1 as [PA (CSH & CRK & BLW)].
      pose proof (hcs_ok asegs R HIA h) as (K1h & _).
      assert (CFh : crange (hcs asegs R HIA h) FB 64) by (rewrite <- Ehcs; exact CF1).
      assert (NCS : ~ hcs asegs R HIA h (Z.shiftr FB 3 + al_sb AL + 4)).
      { rewrite ESH. destruct (K1h (FB + 32) (CFh (FB + 32) ltac:(clear; lia))) as (_ & _ & _ & K). exact K. }
      split; [| exact (conj CSH (conj CRK BLW))].
      apply (d2_rb_presA_irr _ _ _ _ _ _ _ m m1 m1' PA MU1 WM1).
      - intros a Ha Hc. cbn [outside]. split; [| split; [| exact I]]; intros IN.
        + destruct Hc as [Hs|[[Hd _]|([Bb jb] & Hb & Hr)]];
            [clear - Hs IN FBLO LOSP; lia| clear - Hd IN F2; lia
            | cbn [fst snd] in Hr; destruct (F3 Bb jb Hb) as [K|K]; clear - K Hr IN; lia].
        + apply NCS. replace (Z.shiftr FB 3 + al_sb AL + 4) with a by (clear - IN; lia).
          destruct Hc as [Hs|[Hd|([Bb jb] & Hb & Hr)]];
            [exfalso; clear - Hs IN SHLO LOSP; lia| apply (hcs_static asegs R HIA h); exact Hd| exact (CRK Bb jb Hb a Hr)].
      - intros c Hc. cbn [outside]. split; [| split; [| exact I]]; intros IN.
        + destruct (K1h c (CSH c Hc)) as (_ & _ & _ & K). apply K. exact (CFh (shadow_of AL c) ltac:(clear - IN; lia)).
        + assert (CR : FB + 32 <= c < FB + 40).
          { clear - IN F64. unfold shadow_of in IN. rewrite Z.shiftr_div_pow2 in IN by lia. change (2 ^ 3) with 8 in IN.
            Z.div_mod_to_equations. lia. }
          destruct Hc as [Hs|[([Bb jb] & Hb & Hr)|[([Bb jb] & Hb & Hr)|Hst]]].
          * clear - Hs CR F1 ALO. lia.
          * cbn [fst snd] in Hr. destruct (F3 Bb jb ltac:(apply in_or_app; left; exact Hb)) as [K|K]; clear - K Hr CR; lia.
          * cbn [fst snd] in Hr. destruct (hm_fresh_frame_apart asegs R HIA h1 LB LF m1 FB 64 HH1 Bb jb Hb) as [K|K]; clear - K Hr CR; lia.
          * destruct Hst as [Hd _]. clear - Hd CR F2. lia. }
    split.
    { exact (conj SP1 (conj SP1M (conj F64 (conj FRSH (conj JC1' (conj PRES1' (conj Ehcs (conj Ehtop (conj Estk (conj Eflag
               (conj Evol (conj Efr HKI)))))))))))). }
    assert (EDX : mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) (md_limbs dXc) (md_pad dXc) (md_own dXc) = dXc)
      by (destruct dXc; reflexivity).
    pose proof (xa_scratch asegs R HIA h1 LB ((FB, 64) :: LF) m1' dX sp lo 96 MD_FRAME_A JC1' [] v f hc LBc mc3 dXc lo (bv_unsigned sp - 96) mc'
                  XJ3 MU3' WM3' MI' ST' HH' (Z.le_refl lo) (Z.le_refl _)) as XJ'.
    rewrite EDX in XJ'.
    split; [exact XJ'|]. split.
    - constructor; [| exact JB1| exact JB2| exact JB3| exact JB4| exact JB5].
      eapply opnd_atA_munch_any; [exact JB0| exact MU1| exact WM1| exact DBh| exact DBl].
    - eapply bja_munch; [exact XJ3| | exact MU3'| exact WM3'| | |].
      + constructor; [| exact BS| exact BL| |].
        * eapply opnd_atA_munch_any; [exact BA| exact MU3| exact WM3| exact DBh| exact DBl].
        * exact (d2_rb_aobj (hcs asegs R HIA hc) FB mc mc3 _ 16 OKc CF8 F64 AB MU3 BO).
        * intros NN. destruct (ABL NN) as [_ AP]. exact (d2_rb_aobj (hcs asegs R HIA hc) FB mc mc3 _ _ OKc CF8 F64 AP MU3 (BOL NN)).
      + unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        pose proof (hm_top asegs R HIA h1 LB ((FB, 64) :: LF) m1 HH1) as HT0.
        eapply crange_sub; [exact (hcs_stack asegs R HIA hc)| clear - LOS; lia| rewrite cHS; clear - HT0 TOP1 LOSP; lia].
      + cbn [disjoint_from]. split; [destruct OB4 as [K|K]; [left; clear - K; lia| right; clear - K LOSP; lia]| exact I].
      + intros NN. cbn [disjoint_from]. split; [destruct (OB5 NN) as [K|K]; [left; clear - K; lia| right; clear - K LOSP; lia]| exact I].
  Qed.

  #[using="Type"] Lemma d2_hd_aobj_partial : forall (CS : Z -> Prop) (m0 : mem) (B : Z)
      (cs : list cell) (A : Z) (g0 : nat) (k : Z),
      cs_ok AL CS -> rw_cells asegs m0 (Z.shiftr B 3 + al_sb AL) cs -> crange CS A k -> B mod 8 = 0 -> 0 <= B ->
      A = B + 8 * Z.of_nat g0 -> 1 <= k <= 7 -> cell_at cs g0 = Some (C1 (Z_to_bv 8 k)) -> aobj asegs AL CS m0 A k.
  Proof.
    intros CS m0 B cs A g0 k OK H HC HB H0 HA Hk HZ. clear - OK H HC HB H0 HA Hk HZ.
    replace (Z.shiftr B 3 + al_sb AL) with (shadow_of AL B) in H
      by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    split; [exact HC|].
    intros a Ha. exists (Z_to_bv 8 k). split.
    - destruct OK as (K1 & _). destruct (K1 a (HC a Ha)) as (R0 & R1 & R2 & _).
      pose proof (rw_cells_read asegs m0 _ cs g0 _ H HZ) as RD. cbn [csize cbytes] in RD.
      assert (E : shadow_of AL a = shadow_of AL B + Z.of_nat g0).
      { unfold shadow_of. subst A.
        assert (E8 : a / 8 = B / 8 + Z.of_nat g0); [| rewrite E8; lia].
        pose proof (Z.div_mod B 8 ltac:(lia)) as DB. rewrite HB in DB.
        symmetry. apply (Z.div_unique a 8 (B / 8 + Z.of_nat g0) (a - B - 8 * Z.of_nat g0)); lia. }
      rewrite E. apply (bytes_at_of_read1 asegs); [lia| lia| exact RD].
    - right. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow]. rewrite (Z.mod_small k) by lia.
      subst A. pose proof (Z.div_mod B 8 ltac:(lia)) as DB. rewrite HB in DB.
      assert (EM : a mod 8 = a - B - 8 * Z.of_nat g0).
      { symmetry. apply (Z.mod_unique a 8 (B / 8 + Z.of_nat g0) (a - B - 8 * Z.of_nat g0)); lia. }
      rewrite EM. lia.
  Qed.

  #[using="Type"] Lemma d2_hd_mpd_at_cons : forall (mq : mem) (b : blk) (LBq : list blk) (dq : mpd),
      mpd_at asegs mq LBq dq -> mpd_at asegs mq (b :: LBq) dq.
  Proof.
    intros mq b LBq dq [(C & A8 & A0 & LEN & NR & OW) SG]. split; [| exact SG].
    split; [exact C|]. split; [exact A8|]. split; [exact A0|]. split; [exact LEN|]. split; [exact NR|].
    revert OW. destruct (md_own dq); intros OW; try exact OW.
    destruct OW as (N1 & IN & P16 & U). split; [exact N1|]. split; [right; exact IN|]. split; [exact P16| exact U].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d2_head : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA) (LBc : list blk)
      (mc : mem) (dXc : mpd) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      (forall (m1' mc' : mem) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
          MD_BASE h1 m1' FB sp1 ->
          XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1' dX sp lo 96 MD_FRAME_A [] v f hc LBc mc' dXc ->
          JBA asegs R HIA LB ((FB, 64) :: LF) m1' dX sp lo dB ->
          BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc' dXc ->
          MD_CELLS mc' FB SHB ->
          aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
            (MS (mkR (Z_to_bv 64 0xa0638) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1)
                     (Z_to_bv 64 (Z.sgn (mpd_val dXc))) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                     (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32))
                     (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537)
                     (Z_to_bv 64 (-8)) s11 y3 y4 y5 y6)
                F (Z_to_bv 64 0xa063c) fc None mc' (seg_rom asegs))) ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32))
                 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537)
                 (Z_to_bv 64 (-8)) s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa061c) fc None mc (seg_rom asegs)).
  Proof.
    intros until xt6. intros BASE J DBJ B CELLS K.
    pose proof CELLS as CELLSc.
    destruct BASE as (SP1 & SP1M & F64 & FRSH & JC1 & PRES0 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI).
    jc_open.
    pose proof JC1 as [_ _ _ _ HHm1 MXm1 _ _ _ _ _ _ _ _ _].
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NSX OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    destruct CELLS as ((w0 & w1 & w2 & HDR) & SHC & (wl & LMB) & SSH).
    basic_factsA hc.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof (hcs_fake asegs R HIA h1 LB ((FB, 64) :: LF) m1 FB 64 HHm1 (or_introl eq_refl)) as CFB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl [(lo, bv_unsigned sp - 96); (FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] mc) as MU.
    pose proof (wmono_refl asegs mc) as WM.
    destruct (stk_split asegs mc lo (sp1 + 32) (bv_unsigned sp - 96) ST1 ltac:(clear - SP1 SLO2 NEEDR; lia)) as [STa STb].
    destruct (stk_carve asegs mc lo (sp1 + 32) 16 STa ltac:(clear - SP1 SLO2 NEEDR; lia)) as [STc [jy YC]].
    replace (sp1 + 32 - Z.of_nat 16) with (sp1 + 16) in STc, YC by (clear; lia).
    clear ST1 STa.
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP'. pose proof (art_lo asegs R HIA) as ALO'.
    assert (SP1R : 0 <= sp1 /\ sp1 + 32 < 2^64) by (clear - SP1 SPR SLO2 NEEDR LOS ALO' ACP'; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO' LOS; lia).
    assert (CFBc : crange (hcs asegs R HIA hc) FB 64) by (intros x Hx; apply HCS1; apply CFB; exact Hx).
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)).
    { eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1, Estk; clear - TOP HTOP; lia]. }
    assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
    assert (CRX : client_range L (LB ++ fdata LF) lo X 16).
    { destruct XW as [CW _]. intros a Ha. destruct (CW a Ha) as [C|[C|C]];
        [left; clear - C SLO NEEDR FS16; lia| right; left; exact C| right; right; exact C]. }
    assert (APX : X + 16 <= FB \/ FB + 64 <= X).
    { destruct (fresh_apart_client R LB LF lo X 16 FB 64 FRSH CRX ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO' LOS; lia)) as [C|C];
        [right; exact C| left; exact C]. }
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO2 & ACP2 & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1.
    unfold MD_FRAME_A, aa_frame96 in FR1.
    assert (CWF : client_wrange L (LBc ++ fdata ((FB, 64) :: LF)) (arl_stklo R) (htop asegs R HIA hc) (FB + 32) 4).
    { intros a Ha. right. right. exists (FB + 32, 64 - 40). split; [apply in_or_app; right; cbn [fdata]; right; left; reflexivity| cbn [fst snd]; clear - Ha; lia]. }
    pose proof (hm_abase asegs R HIA hc LBc _ mc HH1) as AB.
    zstep. zstep. zstep. zstep. zstep. zstep.
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 4))) with (Z_to_bv 8 4) in SHC.
    zstep.
    pose proof (hcs_ok asegs R HIA hc) as OKc.
    assert (CF8 : crange (hcs asegs R HIA hc) (FB + 32) 8) by (intros x Hx; exact (CFBc x ltac:(clear - Hx; lia))).
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    destruct (stk_split asegs m2 lo sp1 (sp1 + 16) STc ltac:(clear - SP1 SLO2 NEEDR; lia)) as [STlo STy].
    assert (MXm : mpd_at asegs m2 LBc dXc).
    { eapply (mpd_at_munch_any asegs mc m2 LBc dXc); [exact MX1| exact MU| exact WM| |].
      - rewrite AD1. cbn [disjoint_from]. split; [clear - DSX; lia|].
        exact (d2_rb_dj (hcs asegs R HIA hc) FB X 16 CSOK CF8 (proj1 OX1) ltac:(clear; lia) APX F64).
      - intros NN. cbn [disjoint_from]. split; [destruct (XLS1 NN) as [K0|K0]; clear - K0; lia|].
        destruct (d2_rb_heapblk mc LBc dXc MX1 NN NSX) as [N1 IN].
        destruct (hm_apart asegs R HIA hc _ _ _ HH1) as [_ BAc].
        destruct (d4_ba_app2 LBc ((FB, 64) :: LF) _ _ FB 64 BAc IN ltac:(left; reflexivity)) as [K0|K0];
          exact (d2_rb_dj (hcs asegs R HIA hc) FB (md_p dXc) (4 * md_n dXc) CSOK CF8
                   (hcs_block asegs R HIA hc LBc ((FB, 64) :: LF) m2 _ _ HH1 IN) ltac:(clear - N1; lia) ltac:(clear - K0; lia) F64). }
    assert (XNN : 1 <= md_n dXc -> md_own dXc <> LNull).
    { intros N1 EO. pose proof MX1 as [(_ & _ & _ & _ & _ & OW) _]. revert OW. rewrite EO. intros [_ N0]. clear - N0 N1. lia. }
    assert (XP0 : md_own dXc = LHeap -> 0 < md_p dXc).
    { intros EO. pose proof MX1 as [(_ & _ & _ & _ & _ & OW) _]. revert OW. rewrite EO. intros (_ & IN & _).
      destruct (hm_apart asegs R HIA hc _ _ _ HH1) as [HF _]. rewrite Forall_forall in HF.
      destruct (HF _ (in_or_app _ _ _ (or_introl IN))) as [P0 _]. exact P0. }
    assert (OXs : aobj asegs AL (hcs asegs R HIA hc) m2 (md_addr dXc) 16) by (rewrite AD1; exact OX1).
    assert (OXL : 1 <= md_n dXc -> aobj asegs AL (hcs asegs R HIA hc) m2 (md_p dXc) (4 * md_n dXc)).
    { intros N1. destruct (d2_rb_heapblk mc LBc dXc MX1 (XNN N1) NSX) as [_ IN].
      eapply (hm_aobj_block asegs R HIA hc LBc ((FB, 64) :: LF) m2); [exact HH1| exact IN]. }
    assert (OY1 : aobj asegs AL (hcs asegs R HIA hc) m2 (sp1 + 16) 16).
    { change (aobj asegs AL (hcs asegs R HIA hc) m2 (sp1 + 16) (8 * Z.of_nat 2)).
      eapply (aobj_of_zero_shadow asegs AL (hcs asegs R HIA hc) m2 (sp1 + 16) (zcells 2) (sp1 + 16) 0 2 CSOK);
        [ exact CRG
        | clear - SP1M; Z.div_mod_to_equations; lia | clear; lia
        | apply (sshad_chunk asegs AL m2 slo (bv_unsigned sp) 1 (sp1 + 16) SSH);
          [clear - SP1 SLOL SLO2 NEEDR; lia| clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia]
        | intros i Hi; do 2 (destruct i as [|i]; [reflexivity| try (exfalso; clear - Hi; lia)]); exfalso; clear - Hi; lia ]. }
    assert (OQ1 : aobj asegs AL (hcs asegs R HIA hc) m2 (FB + 32) 4).
    { eapply (d2_hd_aobj_partial (hcs asegs R HIA hc) m2 FB _ (FB + 32) 4 4 CSOK SHC CRG1 F8 ltac:(clear - F0; lia));
        [clear; lia| clear; lia| reflexivity]. }
    set (padw := le_bytes_to_word (skipn 4 (skipn 8 jy))).
    set (dY := mkMPD (sp1 + 16) 1 1 (FB + 32) [Z_to_bv 64 0] padw LHeap).
    assert (MXy : mpd_at asegs m2 ((FB + 32, 4) :: LBc) dXc) by (apply d2_hd_mpd_at_cons; exact MXm).
    assert (MY1 : mpd_at asegs m2 ((FB + 32, 4) :: LBc) dY).
    { pose proof YC as [[YWF _] _]. cbn [cells_wf cell_wf] in YWF. destruct YWF as (_ & _ & YL & _).
      unfold mpd_at, mpi_at, dY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own length].
      split; [| left; reflexivity].
      split.
      { eapply rw_cells_reshape; [exact YC| cbn [mpi_cells cells_wf cell_wf]; tauto|].
        cbn [mpi_cells cells_bytes cbytes]. f_equal. unfold padw. rewrite le4_le_bytes_to_word by exact YL.
        rewrite app_assoc. f_equal. unfold le2, le4. cbn [Z_to_le_bytes app].
        repeat (apply (f_equal2 (@cons _)); [apply Z_to_bv8_mod; vm_compute; reflexivity|]). reflexivity. }
      split; [clear - SP1M; Z.div_mod_to_equations; lia|].
      split; [clear - SP1R; lia|].
      split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; clear; lia|].
      split; [clear; lia|]. split; [left; reflexivity|]. split; [clear - F64; Z.div_mod_to_equations; lia|].
      eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 0)));
        [eapply rw_cells_reshape; [exact LMB| cbn; split; [apply (length_le4 (Z_to_bv 64 0))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]
        | cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (EVY : mpd_val dY = 0).
    { unfold mpd_val, dY. cbn [md_sg md_limbs limbs_val]. rewrite (unsigned_lit 0) by (clear; lia). reflexivity. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { pose proof CMP as CMPc. unfold mpi_cmp_mpi_stmtA in CMPc.
      eapply (CMPc (hcs asegs R HIA hc)) with (LB := (FB + 32, 4) :: LBc) (dX := dXc) (dY := dY) (lo := lo);
        rewrite ?(unsigned_lit sp1) by (clear - SP1R; lia);
        first [ exact MXy | exact MY1 | exact XP0 | exact MI1 | exact CSOK | exact (art_alwf asegs R HIA) | exact OXs | exact OY1
              | exact OXL | exact STlo | exact AB
              | reflexivity
              | (intros _; exact OQ1)
              | (intros _; unfold dY; cbn [md_p]; clear - F0; lia)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO3 NS1 SP1; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
              | (rewrite AD1; destruct DSX as [K0|K0]; [left; exact K0| right; clear - K0 SP1; lia])
              | (right; unfold dY; cbn [md_addr]; clear; lia)
              | (intros N1; destruct (XLS1 (XNN N1)) as [K0|K0]; [left; exact K0| right; clear - K0 SP1; lia])
              | (intros _; left; unfold dY; cbn [md_p md_n]; clear - FBLO; lia)
              | (rewrite AD1; reflexivity) ]. }
    cbv beta. intros ms2 PO. unfold mpi_cmp_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    rewrite ?(unsigned_lit sp1) in MU3, ST3 by (clear - SP1R; lia).
    rewrite EVY, Z.sub_0_r.
    match goal with |- context [ret_pc ?r] => replace (ret_pc r) with r by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    assert (WC3 : w_client (hcs asegs R HIA hc) [(lo, sp1)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]| apply Forall_nil]. }
    pose proof (art_stk_high asegs R HIA) as STKH. pose proof (alloc_ceiling_val R) as ACV.
    assert (FSHLO : Z.shiftr FB 3 + al_sb AL + 8 <= lo).
    { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. change (2 ^ 44) with 17592186044416 in STKH.
      clear - F0 F1 ACV STKH LOS. Z.div_mod_to_equations. lia. }
    assert (STyc : stk asegs m2 (sp1 + 16) (sp1 + 32)).
    { match type of YC with rw_cells _ _ ?A0 ?cs0 =>
        replace (sp1 + 32) with (A0 + Z.of_nat (cells_size cs0)) by (cbn; clear; lia) end.
      apply stk_of_rw_cells. exact YC. }
    assert (STm : stk asegs m2 sp1 (bv_unsigned sp - 96)).
    { eapply stk_merge; [exact STy| eapply stk_merge; [exact STyc| exact STb| clear - SP1 SLO2 NEEDR; lia]| clear - SP1 SLO2 NEEDR; lia]. }
    pose proof (stk_transport_disjoint asegs [(lo, sp1)] m2 m3 _ _ STm MU3 WM3
                  ltac:(cbn [disjoint_from]; split; [right; clear; lia| exact I])) as STm3.
    assert (ST4 : stk asegs m3 lo (bv_unsigned sp - 96)).
    { eapply stk_merge; [exact ST3| exact STm3| clear - SP1 SLO2 NEEDR; lia]. }
    pose proof (rw_cells_transport asegs [(lo, sp1)] m2 m3 _ _ HDR MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; split; [left; clear - FBLO; lia| exact I])) as HDR3.
    pose proof (rw_cells_transport asegs [(lo, sp1)] m2 m3 _ _ SHC MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; split; [left; clear - FSHLO; lia| exact I])) as SHC3.
    pose proof (rw_cells_transport asegs [(lo, sp1)] m2 m3 _ _ LMB MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; split; [left; clear - FBLO; lia| exact I])) as LMB3.
    assert (SSH3 : sshad asegs AL m3 slo (bv_unsigned sp)).
    { eapply sshad_munch;
        [exact CSOK| exact WC3| eapply crange_sub; [exact SCS0| clear - SLOS; lia| rewrite HS1, Estk; clear - TOP HTOP; lia]
        | exact MU3| exact WM3| exact SSH]. }
    assert (HH3 : HM asegs R HIA hc LBc ((FB, 64) :: LF) m3).
    { eapply hm_munch; [exact HH1| exact MU3| exact WM3|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite HT1, Ehtop. clear - Ha LOS SP1 TOP. lia. }
    assert (MUc3 : munch [(lo, bv_unsigned sp - 96); (FB + 32, FB + 36); (Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 5)] mc m3).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU3].
      intros x O. cbn [outside] in O |- *. destruct O as (O1 & _). split; [intros IN; apply O1; clear - IN SP1; lia| exact I]. }
    pose proof (wmono_trans asegs mc m2 m3 WM WM3) as WMc3.
    clear MU WM MU3 WM3 HDR SHC LMB SSH HH1 MI1 STc STb STy STyc STm STm3 ST3 STlo YC OX1 OXs OY1 OQ1 AB MXm MXy MY1.
    zstep.
    replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))) with (Z_to_bv 8 248) in SHC3 by (apply Z_to_bv8_mod; vm_compute; reflexivity).
    assert (CELLS4 : MD_CELLS m0 FB SHB).
    { unfold MD_CELLS. split; [exists w0, w1, w2; exact HDR3|]. split; [exact SHC3|].
      split; [exists (Z_to_bv 64 0); exact LMB3| exact SSH3]. }
    assert (BASEc : MD_BASE h1 m1 FB sp1).
    { exact (conj SP1 (conj SP1M (conj F64 (conj FRSH (conj JC1 (conj PRES0 (conj Ehcs (conj Ehtop (conj Estk
               (conj Eflag (conj Evol (conj Efr HKI)))))))))))). }
    destruct (d2_rebase h1 m1 FB sp1 v f hc LBc mc m0 dXc BASEc J DBJ B CELLSc MUc3 WMc3 MI3 ST4 HH3 LMB3 CELLS4)
      as (m1' & BASE' & J' & DBJ' & B').
    eapply (K m1' m0); [exact BASE'| exact J'| exact DBJ'| exact B'| exact CELLS4].
  Qed.

  #[using="Type"] Lemma d2_uwc_frame_save : forall (m0 : mem) (TOP : Z) (w0 : word) (spv sp2 d0 : Z),
      ro_cells asegs m0 (spv - 16) [C8 w0] ->
      uwc asegs m0 (arl_stklo R) TOP (bv_unsigned w0) spv d0 ->
      sp2 + 16 <= spv -> spv mod 8 = 0 -> 0 <= d0 ->
      uwc asegs m0 (arl_stklo R) TOP spv sp2 (d0 + 1).
  Proof.
    intros m0 TOP w0 spv sp2 d0 RO UW0 H1 H2 Hd.
    pose proof (bv_unsigned_in_range 64 w0) as XR. unfold bv_modulus in XR. cbn [Z.pow Z.of_N Pos.pow] in XR.
    rewrite <- (Z_to_bv_bv_unsigned w0) in RO.
    eapply uwc_frame; [exact H1| exact H2| exact XR| exact Hd| exact RO| exact UW0].
  Qed.

  #[using="Type"] Lemma d2_uwc_presA : forall (LB0 LF0 : list blk) (SP SSP TOP : Z) (W : list ivl) (m0 m' : mem) (v0 F0 d0 : Z),
      presA asegs R LB0 LF0 SP SSP TOP W m0 m' ->
      uwc asegs m0 (arl_stklo R) TOP v0 F0 d0 ->
      SP <= F0 ->
      (forall a, F0 <= a < TOP -> outside W a) ->
      0 <= F0 -> TOP <= 2^64 ->
      uwc asegs m' (arl_stklo R) TOP v0 F0 d0.
  Proof.
    intros LB0 LF0 SP SSP TOP W m0 m' v0 F0 d0 [P _] UW0 HSP HW HF HT.
    eapply uwc_transport; [exact UW0|]. intros a Ha. apply (proj1 (P a ltac:(clear - HSP HF HT Ha; lia) ltac:(left; clear - HSP HF HT Ha; lia) (HW a Ha))).
  Qed.

  #[using="Type"] Lemma d2_xa_cnt24 : forall (h1 : HST asegs R HIA) (LF1 : list blk) (m1 : mem) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc : mem) (dXc : mpd),
      JCA asegs R HIA h1 LB LF1 m1 dX sp lo 96 MD_FRAME_A ->
      XJA asegs R HIA h1 LB LF1 m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      cnt24 LBc <= cnt24 LB + 1.
  Proof.
    intros h1 LF1 m1 v f hc LBc mc dXc JC1 J.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J) as (ND1 & _). cbn [app] in ND1. apply NoDup_map_inv in ND1.
    pose proof (xa_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as (_ & _ & O3 & _).
    assert (INC : incl LBc (LB ++ mpd_blk dXc)) by (intros b Hb; apply in_or_app; destruct (O3 b Hb) as [K|K]; [left; exact K| right; exact K]).
    pose proof (cnt24_incl _ _ ND1 INC) as C. rewrite cnt24_app in C.
    assert (C1 : cnt24 (mpd_blk dXc) <= 1).
    { unfold mpd_blk. destruct (md_own dXc); try (rewrite cnt24_nil; clear; lia).
      pose proof (cnt24_cons_le (md_p dXc, 4 * md_n dXc) []) as C2. rewrite cnt24_nil in C2. exact (proj2 C2). }
    clear - C C1. lia.
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d2_call_ng : forall (retpc : Z) (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc : mem) (dXc : mpd) (xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      md_sg dB = - md_sg dXc -> (mpd_abs dXc < mpd_abs dB -> md_n dB <= md_n dXc) ->
      0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
      v <= PHIb -> f <= FRb ->
      (forall (r : Z) (h2 : HST asegs R HIA) (LB2 : list blk) (m2 : mem) (dX2 : mpd)
          (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
          XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f h2 LB2 m2 dX2 ->
          BJA asegs R HIA ((FB, 64) :: LF) sp dB h2 LB2 m2 dX2 ->
          MD_CELLS m2 FB SHB ->
          add_sub_mpi_ng_Rsz 1 LBc dXc dXc dB r dX2 ->
          aevtA asegs (KF asegs R HIA h2 mo) MD_POST_A
            (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                     (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537) (Z_to_bv 64 (-8)) s11 y3 y4 y5 y6)
                F (Z_to_bv 64 retpc) fc None m2 (seg_rom asegs))) ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 X) (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 1) xa4 xa5 xa6 xa7
                 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537) (Z_to_bv 64 (-8)) s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 A_ADD_SUB_MPI) fc None mc (seg_rom asegs)).
  Proof.
    intros until xt6. intros BASE J DBJ B CELLS NGS NGBA RPC RPE BV BF K.
    destruct BASE as (SP1 & SP1M & F64 & FRSH & JC1 & PRES0 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI).
    jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof JC1 as [_ _ _ _ HHm1 _ _ _ _ _ _ _ _ _ _].
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 XNS OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1. cbn [md_addr] in HPX1.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof DBJ as [MBj OBj CRBj CRBLj SXBj BIMG]. dpose OBj as (OB1 & OB2 & OB3 & OB4 & OB5).
    cbn [md_addr md_own md_p md_n] in SXBj, OB1, OB2, OB3, OB4, OB5.
    destruct (bja_client _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ DBJ [] v f hc LBc mc dXc LBc lo J B ltac:(intros bq Hb _; exact Hb) ltac:(clear - LOSP; lia)) as [CRB1 CRBL1].
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    pose proof (xa_crX _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ lo J ltac:(clear - LOSP; lia)) as CRX1. cbn [app] in CRX1.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof SLO2 as SLO2'. change MPI_MOD_MPI_STACK_A with 864 in SLO2'.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SP64 SLO2' NEEDR LO0; lia).
    destruct (stk_split asegs mc lo sp1 (bv_unsigned sp - 96) ST1 ltac:(clear - SP1 SLO2' NEEDR; lia)) as [STc STfr].
    pose proof (hcs_fake asegs R HIA h1 LB ((FB, 64) :: LF) m1 FB 64 HHm1 (or_introl eq_refl)) as CFB.
    assert (CFBc : crange (hcs asegs R HIA hc) FB 64) by (intros x Hx; apply HCS1; apply CFB; exact Hx).
    assert (CRX : client_range L (LB ++ fdata LF) lo X 16).
    { destruct XW as [CW _]. intros a Ha. destruct (CW a Ha) as [C|[C|C]];
        [left; clear - C SLO NEEDR FS16; lia| right; left; exact C| right; right; exact C]. }
    assert (APX : X + 16 <= FB \/ FB + 64 <= X).
    { destruct (fresh_apart_client R LB LF lo X 16 FB 64 FRSH CRX ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as [C|C];
        [right; exact C| left; exact C]. }
    assert (UWc : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { destruct UWX as [[XLO _]|DCAP]; [|apply uwc_cap; clear - DCAP; lia].
      unfold MD_FRAME_A, aa_frame96 in FR1.
      pose proof (rw_cells_split3 asegs mc (bv_unsigned sp - 96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0] [C8 ra] FR1) as (_ & S0C & _).
      replace (bv_unsigned sp - 96 + Z.of_nat (cells_size [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) with (bv_unsigned sp - 16) in S0C by (cbn; clear; lia).
      assert (TOP64 : hstkhi asegs R HIA h <= 2^64) by (apply hstkhi_le64; clear - LOS LOSP SP64; lia).
      pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES0) as PA0.
      pose proof (d2_uwc_presA _ _ _ _ _ _ _ _ _ _ _ PA0 UW (Z.le_refl _) (fun a _ => I) ltac:(clear - LO0 LOSP; lia) TOP64) as UW1.
      rewrite <- Estk in UW1, TOP64.
      pose proof (d2_uwc_presA _ _ _ _ _ _ _ _ _ _ _ HPX1 UW1 (Z.le_refl _)
                    ltac:(intros a Ha; cbn [outside]; split; [clear - XLO Ha LOS LOSP; lia| exact I]) ltac:(clear - LO0 LOSP; lia) TOP64) as UW2.
      rewrite <- HS1 in UW2.
      exact (d2_uwc_frame_save mc _ s0 (bv_unsigned sp) sp1 d (proj1 S0C) UW2 ltac:(clear - SP1; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia) D0). }
    pose proof (HASN 1 (or_introl eq_refl)) as SPc. unfold add_sub_mpi_ng_stmtA_oz in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := (FB, 64) :: LF) (dX := dXc) (dA := dXc) (dB := dB) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD1;
        first [ exact HH1 | exact HK1 | exact MX1 | exact XNS | exact STc | exact LOS | exact TPV | exact MI1 | exact NGBA | exact CRX1 | exact CRB1 | exact CRBL1 | exact IB2 | exact UWc | reflexivity
              | lazymatch goal with
                | |- opnd_atA _ _ _ _ _ _ dB => eapply opnd_atA_SP_le; [exact (bj_at _ _ _ _ _ _ _ _ _ _ B)| clear - SP1; lia]
                | |- mpd_sep dXc dXc => left; reflexivity
                | |- mpd_sep dXc dB => right; rewrite AD1; clear - SXBj; lia
                | |- _ * md_sg dB = _ => clear - NGS; lia
                | |- _ -> md_n dXc <= md_n dXc => intros _; clear; lia
                | |- opnd_sep dXc dXc _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [intros NN; destruct (OWN1 NN) as (EH & _); exact (XP1 EH)|];
                    split; [exact XP1|]; split; [left; reflexivity|]; split; [clear - DSX SP1; lia|];
                    intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia]
                | |- opnd_sep dXc dB _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [exact OB1|]; split; [exact (bj_sepS _ _ _ _ _ _ _ _ _ _ B)|];
                    split; [right; destruct (md_own dXc) eqn:EOX; [left; discriminate| | left; discriminate];
                            destruct (md_own dB) eqn:EOB; [right; left; reflexivity| |];
                            right; right; apply (bj_sepL _ _ _ _ _ _ _ _ _ _ B EOX); rewrite EOB; discriminate|];
                    split; [clear - ES SP1; lia|]; intros BN; ddestruct (OWNE1 BN) as (_ & _ & _ & _ & ESK & _); clear - ESK SP1; lia
                | |- md_own dXc = LHeap -> client_range _ _ _ (md_p dXc) _ =>
                    intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & XIN & _);
                    eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear - SP1; lia| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia]
                | |- lo <= _ - 368 - _ => clear - SLO2' SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HT1, Ehtop; clear - TOP SP1; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 retpc) mod 2 = 0 => rewrite unsigned_lit by exact RPC; exact RPE
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (XNS E)]
                | |- mpd_aobjA _ _ _ _ dB => split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)| intros E; apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B); rewrite E; discriminate]
                | |- X <> X -> _ => intros NE; exfalso; exact (NE eq_refl)
                | |- md_own dXc = LStatic -> _ => intros E; exfalso; exact (XNS E)
                | |- md_own dB = LStatic -> _ + 8 <= 2^47 => intros E; eapply mpd_at_static47; [exact MB0| exact E]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold add_sub_PHI0; clear - BV BUD HV1 Evol; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold add_sub_FR0; clear - BF BUDF HFR1 Efr; lia
                | |- uw_obj _ _ _ _ => clear - UWX UWB; unfold uw_obj in *; lia
                end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite AD1 in HP2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    pose proof CR as [[CR1 BK] NGX].
    assert (STfr2 : stk asegs m2 sp1 (bv_unsigned sp - 96)).
    { eapply presA_stk; [exact HP2| exact STfr| clear; lia|]. cbn [disjoint_from]. split; [clear - DSX SP1 SLO2' NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 96)).
    { eapply stk_merge; [exact ST2| exact STfr2| clear - SP1 SLO2' NEEDR; lia]. }
    destruct CELLS as ((w0 & w1 & w2 & HDR) & SHC & (wl & LMB) & SSH).
    assert (CELLS2 : MD_CELLS m2 FB SHB).
    { unfold MD_CELLS. split; [|split; [|split]].
      - exists w0, w1, w2. eapply presA_rw_cells; [exact HP2| exact HDR| |].
        + change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2])) with 24.
          apply (client_range_block _ _ _ _ _ FB 24); [apply in_or_app; right; cbn [fdata]; left; reflexivity| clear; lia| clear; lia].
        + change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2])) with 24. cbn [disjoint_from]. split; [clear - APX; lia| exact I].
      - eapply presA_shadow_cells_sh; [exact CSOK| exact CFBc| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP2| exact SHC|].
        intros c Hc. change (8 * Z.of_nat (cells_size SHB)) with 64 in Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia].
      - exists wl. eapply presA_rw_cells; [exact HP2| exact LMB| |].
        + change (Z.of_nat (cells_size [C4 wl])) with 4.
          apply (client_range_block _ _ _ _ _ (FB + 32) 24); [apply in_or_app; right; cbn [fdata]; right; left; reflexivity| clear; lia| clear; lia].
        + change (Z.of_nat (cells_size [C4 wl])) with 4. cbn [disjoint_from]. split; [clear - APX; lia| exact I].
      - eapply presA_sshad; [exact HP2| exact SSH| exact SLOS|]. rewrite HS1, Estk. clear - TOP HTOP; lia. }
    pose proof (xa_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 _ _ _ _ _ _ m2 h2 LB2 dX2 sp1 0 0 J ltac:(clear - SP1 SLO2' NEEDR; lia)
                  ltac:(clear; lia) ltac:(clear; lia) MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    replace (v + 0) with v in J1 by (clear; lia). replace (f + 0) with f in J1 by (clear; lia).
    pose proof (bja_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 dB DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 sp1 J B ltac:(clear - SP1 SLO2' NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J1| exact B1| exact CELLS2| exact CR].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d2_call_al : forall (retpc : Z) (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc : mem) (dXc : mpd) (xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
      v + add_sub_PHI dXc dXc dB <= PHIb -> f + add_sub_FR (d + 1) <= FRb ->
      (forall (r : Z) (h2 : HST asegs R HIA) (LB2 : list blk) (m2 : mem) (dX2 : mpd)
          (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
          XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] (v + add_sub_PHI dXc dXc dB) (f + add_sub_FR (d + 1)) h2 LB2 m2 dX2 ->
          BJA asegs R HIA ((FB, 64) :: LF) sp dB h2 LB2 m2 dX2 ->
          MD_CELLS m2 FB SHB ->
          add_sub_mpi_Rsz 1 LBc dXc dXc dB r dX2 ->
          aevtA asegs (KF asegs R HIA h2 mo) MD_POST_A
            (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp y0 y1 y2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                     (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537) (Z_to_bv 64 (-8)) s11 y3 y4 y5 y6)
                F (Z_to_bv 64 retpc) fc None m2 (seg_rom asegs))) ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 X) (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 1) xa4 xa5 xa6 xa7
                 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537) (Z_to_bv 64 (-8)) s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 A_ADD_SUB_MPI) fc None mc (seg_rom asegs)).
  Proof.
    intros until xt6. intros BASE J DBJ B CELLS RPC RPE BV BF K.
    destruct BASE as (SP1 & SP1M & F64 & FRSH & JC1 & PRES0 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI).
    jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof JC1 as [_ _ _ _ HHm1 _ _ _ _ _ _ _ _ _ _].
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 XNS OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in AD1, OX1, XP1. cbn [md_addr] in HPX1.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof DBJ as [MBj OBj CRBj CRBLj SXBj BIMG]. dpose OBj as (OB1 & OB2 & OB3 & OB4 & OB5).
    cbn [md_addr md_own md_p md_n] in SXBj, OB1, OB2, OB3, OB4, OB5.
    destruct (bja_client _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ DBJ [] v f hc LBc mc dXc LBc lo J B ltac:(intros bq Hb _; exact Hb) ltac:(clear - LOSP; lia)) as [CRB1 CRBL1].
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J) as CWX. rewrite <- HT1 in CWX.
    pose proof (xa_crX _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ lo J ltac:(clear - LOSP; lia)) as CRX1. cbn [app] in CRX1.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof SLO2 as SLO2'. change MPI_MOD_MPI_STACK_A with 864 in SLO2'.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SP64 SLO2' NEEDR LO0; lia).
    destruct (stk_split asegs mc lo sp1 (bv_unsigned sp - 96) ST1 ltac:(clear - SP1 SLO2' NEEDR; lia)) as [STc STfr].
    pose proof (hcs_fake asegs R HIA h1 LB ((FB, 64) :: LF) m1 FB 64 HHm1 (or_introl eq_refl)) as CFB.
    assert (CFBc : crange (hcs asegs R HIA hc) FB 64) by (intros x Hx; apply HCS1; apply CFB; exact Hx).
    assert (CRX : client_range L (LB ++ fdata LF) lo X 16).
    { destruct XW as [CW _]. intros a Ha. destruct (CW a Ha) as [C|[C|C]];
        [left; clear - C SLO NEEDR FS16; lia| right; left; exact C| right; right; exact C]. }
    assert (APX : X + 16 <= FB \/ FB + 64 <= X).
    { destruct (fresh_apart_client R LB LF lo X 16 FB 64 FRSH CRX ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as [C|C];
        [right; exact C| left; exact C]. }
    assert (UWc : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { destruct UWX as [[XLO _]|DCAP]; [|apply uwc_cap; clear - DCAP; lia].
      unfold MD_FRAME_A, aa_frame96 in FR1.
      pose proof (rw_cells_split3 asegs mc (bv_unsigned sp - 96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0] [C8 ra] FR1) as (_ & S0C & _).
      replace (bv_unsigned sp - 96 + Z.of_nat (cells_size [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) with (bv_unsigned sp - 16) in S0C by (cbn; clear; lia).
      assert (TOP64 : hstkhi asegs R HIA h <= 2^64) by (apply hstkhi_le64; clear - LOS LOSP SP64; lia).
      pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES0) as PA0.
      pose proof (d2_uwc_presA _ _ _ _ _ _ _ _ _ _ _ PA0 UW (Z.le_refl _) (fun a _ => I) ltac:(clear - LO0 LOSP; lia) TOP64) as UW1.
      rewrite <- Estk in UW1, TOP64.
      pose proof (d2_uwc_presA _ _ _ _ _ _ _ _ _ _ _ HPX1 UW1 (Z.le_refl _)
                    ltac:(intros a Ha; cbn [outside]; split; [clear - XLO Ha LOS LOSP; lia| exact I]) ltac:(clear - LO0 LOSP; lia) TOP64) as UW2.
      rewrite <- HS1 in UW2.
      exact (d2_uwc_frame_save mc _ s0 (bv_unsigned sp) sp1 d (proj1 S0C) UW2 ltac:(clear - SP1; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia) D0). }
    pose proof (d2_xa_cnt24 h1 ((FB, 64) :: LF) m1 v f hc LBc mc dXc JC1 J) as C24c.
    assert (C24A : cnt24 LBc + C24_ADDSUB <= C24MAX).
    { pose proof C24H as C24H'. change C24_DIV_MPI with 16 in C24H'. change C24_ADDSUB with 4. clear - C24c C24H'; lia. }
    assert (PHI0' : 0 <= add_sub_PHI dXc dXc dB) by (unfold add_sub_PHI, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NR1 NRB; lia).
    assert (FR0' : 0 <= add_sub_FR (d + 1)) by (unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    pose proof HADD as SPc. unfold add_sub_mpi_stmtA_osz in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LBc) (LF := (FB, 64) :: LF) (dX := dXc) (dA := dXc) (dB := dB) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD1;
        first [ exact HH1 | exact HK1 | exact MX1 | exact XNS | exact STc | exact LOS | exact TPV | exact MI1 | exact CRX1 | exact CRB1 | exact CRBL1 | exact IB2 | exact UWc | exact C24A | reflexivity
              | lazymatch goal with
                | |- opnd_atA _ _ _ _ _ _ dB => eapply opnd_atA_SP_le; [exact (bj_at _ _ _ _ _ _ _ _ _ _ B)| clear - SP1; lia]
                | |- mpd_sep dXc dXc => left; reflexivity
                | |- mpd_sep dXc dB => right; rewrite AD1; clear - SXBj; lia
                | |- opnd_sep dXc dXc _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [intros NN; destruct (OWN1 NN) as (EH & _); exact (XP1 EH)|];
                    split; [exact XP1|]; split; [left; reflexivity|]; split; [clear - DSX SP1; lia|];
                    intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia]
                | |- opnd_sep dXc dB _ _ =>
                    unfold opnd_sep; rewrite ?AD1;
                    split; [exact OB1|]; split; [exact (bj_sepS _ _ _ _ _ _ _ _ _ _ B)|];
                    split; [right; destruct (md_own dXc) eqn:EOX; [left; discriminate| | left; discriminate];
                            destruct (md_own dB) eqn:EOB; [right; left; reflexivity| |];
                            right; right; apply (bj_sepL _ _ _ _ _ _ _ _ _ _ B EOX); rewrite EOB; discriminate|];
                    split; [clear - ES SP1; lia|]; intros BN; ddestruct (OWNE1 BN) as (_ & _ & _ & _ & ESK & _); clear - ESK SP1; lia
                | |- md_own dXc = LHeap -> client_range _ _ _ (md_p dXc) _ =>
                    intros EH; ddestruct (OWN1 ltac:(rewrite EH; discriminate)) as (_ & _ & XIN & _);
                    eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
                | |- mpd_writableA _ _ _ _ _ dXc => split; [rewrite AD1; eapply client_wrange_sp_mono; [| exact CWX]; clear - SP1; lia| rewrite AD1; exact XP1]
                | |- md_own dXc <> LNull -> _ => intros NN; destruct (XLS1 NN) as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia]
                | |- lo <= _ - 368 - _ => clear - SLO2' SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HT1, Ehtop; clear - TOP SP1; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 retpc) mod 2 = 0 => rewrite unsigned_lit by exact RPC; exact RPE
                | |- mpd_aobjA _ _ _ _ dXc => split; [rewrite AD1; exact OX1| intros E; exfalso; exact (XNS E)]
                | |- mpd_aobjA _ _ _ _ dB => split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)| intros E; apply (bj_aobjL _ _ _ _ _ _ _ _ _ _ B); rewrite E; discriminate]
                | |- X <> X -> _ => intros NE; exfalso; exact (NE eq_refl)
                | |- md_own dXc = LStatic -> _ => intros E; exfalso; exact (XNS E)
                | |- md_own dB = LStatic -> _ + 8 <= 2^47 => intros E; eapply mpd_at_static47; [exact MB0| exact E]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BV BUD HV1 Evol; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BF BUDF HFR1 Efr; lia
                | |- uw_obj _ _ _ _ => clear - UWX UWB; unfold uw_obj in *; lia
                end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite AD1 in HP2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    pose proof CR as [[CR1 BK] NGX].
    assert (STfr2 : stk asegs m2 sp1 (bv_unsigned sp - 96)).
    { eapply presA_stk; [exact HP2| exact STfr| clear; lia|]. cbn [disjoint_from]. split; [clear - DSX SP1 SLO2' NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 96)).
    { eapply stk_merge; [exact ST2| exact STfr2| clear - SP1 SLO2' NEEDR; lia]. }
    destruct CELLS as ((w0 & w1 & w2 & HDR) & SHC & (wl & LMB) & SSH).
    assert (CELLS2 : MD_CELLS m2 FB SHB).
    { unfold MD_CELLS. split; [|split; [|split]].
      - exists w0, w1, w2. eapply presA_rw_cells; [exact HP2| exact HDR| |].
        + change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2])) with 24.
          apply (client_range_block _ _ _ _ _ FB 24); [apply in_or_app; right; cbn [fdata]; left; reflexivity| clear; lia| clear; lia].
        + change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2])) with 24. cbn [disjoint_from]. split; [clear - APX; lia| exact I].
      - eapply presA_shadow_cells_sh; [exact CSOK| exact CFBc| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP2| exact SHC|].
        intros c Hc. change (8 * Z.of_nat (cells_size SHB)) with 64 in Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia].
      - exists wl. eapply presA_rw_cells; [exact HP2| exact LMB| |].
        + change (Z.of_nat (cells_size [C4 wl])) with 4.
          apply (client_range_block _ _ _ _ _ (FB + 32) 24); [apply in_or_app; right; cbn [fdata]; right; left; reflexivity| clear; lia| clear; lia].
        + change (Z.of_nat (cells_size [C4 wl])) with 4. cbn [disjoint_from]. split; [clear - APX; lia| exact I].
      - eapply presA_sshad; [exact HP2| exact SSH| exact SLOS|]. rewrite HS1, Estk. clear - TOP HTOP; lia. }
    pose proof (xa_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 _ _ _ _ _ _ m2 h2 LB2 dX2 sp1 (add_sub_PHI dXc dXc dB) (add_sub_FR (d + 1)) J
                  ltac:(clear - SP1 SLO2' NEEDR; lia) PHI0' FR0' MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    pose proof (bja_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 dB DBJ _ _ _ _ _ _ m2 h2 LB2 dX2 sp1 J B ltac:(clear - SP1 SLO2' NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J1| exact B1| exact CELLS2| exact CR].
  Qed.

  Local Ltac d2_br := zstep;
    try lazymatch goal with
    | |- _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let KB := fresh "KB" in if_cases KB; zify_cond KB; try (exfalso; clear - KB; lia); try cbv_concl_iota
    end.
  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d2_L1_nonneg :
    forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA) (LBc : list blk)
      (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      md_sg dB = 1 -> 0 < mpd_abs dB ->
      0 <= mpd_val dXc ->
      md_n dXc <= NZ -> v <= PHIb -> f <= FRb ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32))
                 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537)
                 (Z_to_bv 64 (-8)) s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa061c) fc None mc (seg_rom asegs)).
  Proof.
    intros h1 m1 FB sp1 v f hc LBc mc dXc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 BASE J DBJ B CELLS SGB BPOS VNN HSZ BV BF.
    eapply d2_head; [exact BASE| exact J| exact DBJ| exact B| exact CELLS|].
    intros m1' mc' y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 BASE' J' DBJ' B' CELLS'.
    pose proof (md_L2 (S (Z.to_nat (mpd_val dXc)))) as L2. unfold mdL2_stmt in L2.
    assert (VR2 : 0 <= mpd_val dXc < Z.of_nat (S (Z.to_nat (mpd_val dXc))) * mpd_abs dB).
    { split; [exact VNN|]. rewrite Nat2Z.inj_succ, Z2Nat.id by exact VNN. clear - VNN BPOS. nia. }
    destruct (Z.eq_dec (mpd_val dXc) 0) as [V0|VP].
    - replace (Z.sgn (mpd_val dXc)) with 0 by (rewrite V0; reflexivity).
      d2_br.
      eapply L2; [exact BASE'| exact J'| exact DBJ'| exact B'| exact CELLS'| exact SGB| exact BPOS| exact VR2| exact HSZ| exact BV| exact BF].
    - replace (Z.sgn (mpd_val dXc)) with 1 by (symmetry; apply Z.sgn_pos; clear - VNN VP; lia).
      d2_br.
      eapply L2; [exact BASE'| exact J'| exact DBJ'| exact B'| exact CELLS'| exact SGB| exact BPOS| exact VR2| exact HSZ| exact BV| exact BF].
  Qed.
  Definition mdL1_stmt (D : nat) : Prop :=
    forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA) (LBc : list blk)
      (mc : mem) (dXc : mpd)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      MD_CELLS mc FB SHB ->
      md_sg dB = 1 -> 0 < mpd_abs dB ->
      - mpd_val dXc < Z.of_nat D * mpd_abs dB ->
      md_n dXc <= NZ -> v <= PHId -> f <= FRd ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 32))
                 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 4) (Z_to_bv 64 65537)
                 (Z_to_bv 64 (-8)) s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa061c) fc None mc (seg_rom asegs)).
  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"] Lemma md_L1 : forall D, mdL1_stmt D.
  Proof.
    induction D as [|D IH]; unfold mdL1_stmt in *;
      intros h1 m1 FB sp1 v f hc LBc mc dXc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 BASE J DBJ B CELLS SGB BPOS VR HSZ BV BF.
    all: destruct (Z_le_gt_dec 0 (mpd_val dXc)) as [VNN|VNEG];
      [ eapply d2_L1_nonneg; [exact BASE| exact J| exact DBJ| exact B| exact CELLS| exact SGB| exact BPOS| exact VNN| exact HSZ| clear - BV NRB; lia|
          unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - BF D0; lia]
      | ].
    - exfalso. clear - VR VNEG. cbn [Z.of_nat] in VR. lia.
    - assert (VN : mpd_val dXc < 0) by (clear - VNEG; lia).
      pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NSX OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
      pose proof (mpd_abs_nonneg dXc) as NNX.
      assert (SN : md_sg dXc = -1).
      { pose proof MX1 as [_ SGX]. pose proof VN as VN'. unfold mpd_val in VN'. pose proof NNX as NNX'. unfold mpd_abs in NNX'.
        destruct SGX as [S|S]; [exfalso; rewrite S in VN'; clear - VN' NNX'; lia| exact S]. }
      assert (VX : mpd_val dXc = - mpd_abs dXc) by (unfold mpd_val, mpd_abs; rewrite SN; clear; lia).
      assert (VB : mpd_val dB = mpd_abs dB) by (unfold mpd_val, mpd_abs; rewrite SGB; clear; lia).
      clear MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NSX OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1.
      eapply d2_head; [exact BASE| exact J| exact DBJ| exact B| exact CELLS|].
      intros m1' mc' y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 BASE' J' DBJ' B' CELLS'.
      replace (Z.sgn (mpd_val dXc)) with (-1) by (symmetry; apply Z.sgn_neg; exact VN).
      d2_br.
      zstep. zstep. zstep. zstep. zstep.
      destruct (Z_lt_le_dec (mpd_abs dXc) (mpd_abs dB)) as [ALT|AGE]; [destruct (Z_lt_le_dec (md_n dXc) (md_n dB)) as [NLT|NGE]|].
      + assert (PHIA : add_sub_PHI dXc dXc dB <= 32 * md_n dB + 48).
        { unfold add_sub_PHI, add_abs_PHI, grow_PHI, AVOL_CALL. clear - NLT. lia. }
        eapply (d2_call_al 0xa0654); [exact BASE'| exact J'| exact DBJ'| exact B'| exact CELLS'| clear; lia| reflexivity| clear - BV PHIA; lia| clear - BF; lia|].
        intros r h2 LB2 m2 dX2 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 J2 B2 CELLS2 [[CR1 BK] NGX].
        assert (HSZ2 : md_n dX2 <= NZ) by (unfold addsub_nz in NGX; unfold div_mpi_nz; clear - NGX NLT; lia).
        destruct CR1 as [(-> & CV)| ->].
        * d2_br.
          eapply d2_L1_nonneg; [exact BASE'| exact J2| exact DBJ'| exact B2| exact CELLS2| exact SGB| exact BPOS| | exact HSZ2| clear - BV PHIA; lia| clear - BF; lia].
          rewrite CV, VB, VX. clear - ALT. lia.
        * unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. d2_br. d2_br.
          eapply md_join; [exact BASE'| exact J2| exact CELLS2| intros E; exfalso; clear - E; lia| clear; lia| exact HSZ2| clear - BV PHIA; lia| clear - BF; lia].
      + eapply (d2_call_ng 0xa0654); [exact BASE'| exact J'| exact DBJ'| exact B'| exact CELLS'| rewrite SGB, SN; reflexivity| intros _; exact NGE| clear; lia| reflexivity|
          clear - BV NRB; lia| unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - BF D0; lia|].
        intros r h2 LB2 m2 dX2 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 J2 B2 CELLS2 [[CR1 BK] NGX].
        destruct CR1 as [(-> & CV)| ->].
        * d2_br.
          eapply IH; [exact BASE'| exact J2| exact DBJ'| exact B2| exact CELLS2| exact SGB| exact BPOS| | clear - NGX HSZ; lia| exact BV| exact BF].
          rewrite CV, VB. clear - VR BPOS. first [lia| nia].
        * unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. d2_br. d2_br.
          eapply md_join; [exact BASE'| exact J2| exact CELLS2| intros E; exfalso; clear - E; lia| clear; lia| clear - NGX HSZ; lia|
            clear - BV NRB; lia| unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - BF D0; lia].
      + eapply (d2_call_ng 0xa0654); [exact BASE'| exact J'| exact DBJ'| exact B'| exact CELLS'| rewrite SGB, SN; reflexivity| intros LT; exfalso; clear - LT AGE; lia| clear; lia| reflexivity|
          clear - BV NRB; lia| unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - BF D0; lia|].
        intros r h2 LB2 m2 dX2 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 J2 B2 CELLS2 [[CR1 BK] NGX].
        destruct CR1 as [(-> & CV)| ->].
        * d2_br.
          eapply IH; [exact BASE'| exact J2| exact DBJ'| exact B2| exact CELLS2| exact SGB| exact BPOS| | clear - NGX HSZ; lia| exact BV| exact BF].
          rewrite CV, VB. clear - VR BPOS. first [lia| nia].
        * unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. d2_br. d2_br.
          eapply md_join; [exact BASE'| exact J2| exact CELLS2| intros E; exfalso; clear - E; lia| clear; lia| clear - NGX HSZ; lia|
            clear - BV NRB; lia| unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - BF D0; lia].
  Qed.

  #[using="Type"] Lemma d1b_uw_obj_mono_d : forall (A n d0 d' : Z), uw_obj R A n d0 -> d0 <= d' -> uw_obj R A n d'.
  Proof. intros A n d0 d' [[H Hd]|H] LE; [left; split; [exact H| clear - Hd LE; lia]| right; clear - H LE; lia]. Qed.

  #[using="Type"] Lemma d1b_uwc_frame_save : forall (m0 : mem) (TOP : Z) (w0 : word) (spv sp0 d0 : Z),
      ro_cells asegs m0 (spv - 16) [C8 w0] ->
      uwc asegs m0 (arl_stklo R) TOP (bv_unsigned w0) spv d0 ->
      sp0 + 16 <= spv -> spv mod 8 = 0 -> 0 <= d0 ->
      uwc asegs m0 (arl_stklo R) TOP spv sp0 (d0 + 1).
  Proof.
    intros m0 TOP w0 spv sp0 d0 RO UW0 H1 H2 Hd.
    pose proof (bv_unsigned_in_range 64 w0) as XR. unfold bv_modulus in XR. cbn [Z.pow Z.of_N Pos.pow] in XR.
    rewrite <- (Z_to_bv_bv_unsigned w0) in RO.
    eapply uwc_frame; [exact H1| exact H2| exact XR| exact Hd| exact RO| exact UW0].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d1_DIVCALL : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (hc : HST asegs R HIA) (mc : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] 0 0 hc LB mc dX ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LB mc dX ->
      mpd_at asegs mc LB dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dX ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dB ->
      MD_CELLS mc FB SHB ->
      0 <= mpd_val dB ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) xa0
                 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X)
                 (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 (-8))
                 xs9 xs10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa05f0) fc None mc (seg_rom asegs)).
  Proof.
    intros h1 m1 FB sp1 hc mc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xt3 xt4 xt5 xt6
      MB J DBJ B MA1 OXA OAA OBA MC VB0.
    jc_open. basic_factsA hc.
    pose proof MB as MB'.
    destruct MB' as (SP1 & SP1M & F64 & FRSH & JC1 & PRES & Ecs & Etop & Estk & Eflag & Evol & Efr & HKI).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NST1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    cbn [app] in HH1.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 MD_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO2 NEEDR LO0; lia).
    pose proof B as [BAT BSS BSL BAO BAL].
    assert (MBc : mpd_at asegs mc LB dB) by (eapply opnd_atA_mpd_back; [exact MB0| exact BAT]).
    destruct (stk_split asegs mc lo sp1 (bv_unsigned sp - 96) ST1 ltac:(clear - SP1 SLO2 NEEDR; lia)) as [STlo STmid].
    pose proof MC as (MCH & MCS & MCL & SSH).
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSH ltac:(clear - SP1 SLOL SLO2 NEEDR; lia)
                ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSHlo _].
    assert (UWF : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { pose proof UWX as UWX'. destruct UWX' as [[XS _]|D28]; [| apply uwc_cap; clear - D28; lia].
      rewrite HS1, Estk.
      pose proof FR1 as FS0. unfold MD_FRAME_A, aa_frame96 in FS0.
      chunk_split FS0 10%nat FSa FSb. chunk_split FSb 1%nat FS0' FSr. clear FSa FSr.
      replace (bv_unsigned sp - 96 + 80) with (bv_unsigned sp - 16) in FS0' by (clear; lia).
      pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SLO SPR NEEDR; lia)) as T64.
      pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as [P0 _].
      pose proof HPX1 as [P1 _].
      eapply d1b_uwc_frame_save; [exact (proj1 FS0')| | clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0].
      eapply uwc_transport; [exact UW|]. intros a Ha.
      assert (A64 : 0 <= a < 2^64) by (clear - Ha T64 SPR; lia).
      rewrite (proj1 (P1 a A64 ltac:(left; clear - Ha; lia) ltac:(cbn [outside md_addr]; split; [clear - Ha XS LOS SLO NEEDR; lia| exact I]))).
      exact (proj1 (P0 a A64 ltac:(left; clear - Ha; lia) I)). }
    pose proof XW as XW'. unfold mpd_writableA in XW'. destruct XW' as [XCW XP].
    assert (APX : FB + 64 <= X \/ X + 16 <= FB).
    { destruct (fresh_apart_client0 R LB LF (bv_unsigned sp) X 16 FB 64 FRSH (d4_crw _ _ _ _ _ XCW) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear - ALO LOS SLO NEEDR; lia)) as [C|[C|C]]; [clear - C; lia| left; exact C| right; exact C]. }
    pose proof FRSH as (F0 & F1 & F2 & F3).
    assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA hc _ _ mc FB 64 HH1 INF) as CFBc.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    zstep. zstep. zstep. zstep. zstep.
    pose proof HDIV as SPc. unfold mpi_div_mpi_stmtA in SPc.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPc with (h := hc) (LB := LB) (LF := (FB, 64) :: LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (slo := slo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; cbn [md_addr];
        first [ exact HH1 | exact HK1 | exact MX1 | exact MA1 | exact MBc | exact SXA | exact SXB | exact SAB | exact NST | exact NEB
              | exact STlo | exact LOS | exact SSHlo | exact SLOS | exact SLOL | exact TPV | exact MI1 | exact OXA | exact OAA | exact OBA
              | exact IA2 | exact IB2 | exact C24H | exact UWF | reflexivity
              | lazymatch goal with
                | |- (length _ < _)%nat => cbn [length]; clear - LFN; lia
                | |- opnd_sep dX dA _ _ => eapply opnd_sep_sp_le; [exact OA| clear - SP1; lia]
                | |- opnd_sep dX dB _ _ => eapply opnd_sep_sp_le; [exact OB| clear - SP1; lia]
                | |- client_range _ _ _ (md_addr dA) 16 => eapply client_range_temp; [exact CRA| clear; lia| intros b' Hb; apply fdata_cons_sub; exact Hb]
                | |- client_range _ _ _ (md_addr dB) 16 => eapply client_range_temp; [exact CRB| clear; lia| intros b' Hb; apply fdata_cons_sub; exact Hb]
                | |- md_own dA = LHeap -> _ => intros EO; eapply client_range_temp; [exact (CRAL EO)| clear; lia| intros b' Hb; apply fdata_cons_sub; exact Hb]
                | |- md_own dB = LHeap -> _ => intros EO; eapply client_range_temp; [exact (CRBL EO)| clear; lia| intros b' Hb; apply fdata_cons_sub; exact Hb]
                | |- mpd_writableA _ _ _ _ _ _ =>
                    split; [rewrite HT1, Etop; eapply client_wrange_sp_mono with (SP := bv_unsigned sp);
                            [clear - SP1; lia| eapply client_wrange_mono; [exact XCW| intros b' Hb; apply fdata_cons_sub; exact Hb]]
                           | exact XP]
                | |- md_own _ <> LNull -> _ => intros XN; destruct (XLS XN) as [K|K]; [left; exact K| right; clear - K SP1; lia]
                | |- lo <= sp1 - 720 - _ => clear - SLO2 SP1; lia
                | |- lo <= sp1 - 352 - _ => clear - SLO3 SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HT1, Etop; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD NRB HV1 Evol; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge in BUDF; clear - BUDF D0 HFR1 Efr; lia
                | |- uw_obj _ _ 16 _ => eapply d1b_uw_obj_mono_d; [exact UWX| clear; lia]
                end
              | match goal with |- ?g => idtac "DIV-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E
                     & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R. cbn [md_addr] in HP2.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
    ddestruct CR as [[[RR RB] BK] HSZ2]. cbn [md_n] in HSZ2.
    assert (ST2m : stk asegs m2 sp1 (bv_unsigned sp - 96)).
    { eapply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP2 STmid); [clear; lia|].
      cbn [disjoint_from]. split; [clear - DSX SP1 SLO2 NEEDR; lia| exact I]. }
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 96)) by (eapply stk_merge; [exact ST2| exact ST2m| clear - SP1 SLO2 NEEDR; lia]).
    pose proof (xa_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 0 0 hc LB mc dX m2 h2 LB2 dX2 sp1 PHId FRd J
                  ltac:(clear - SP1 SLO2 NEEDR; lia) PHId0 FRd0 MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    cbn [Z.add] in J1.
    pose proof (bja_call asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 dB DBJ 0 0 hc LB mc dX m2 h2 LB2 dX2 sp1 J B
                  ltac:(clear - SP1 SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
    assert (CELLS2 : MD_CELLS m2 FB SHB).
    { destruct MCH as (w0 & w1 & w2 & FHD). destruct MCL as (wl & FLB).
      split; [| split; [| split]].
      - exists w0, w1, w2. eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2 FHD).
        + cbn [cells_size csize Nat.add]. eapply client_range_block; [apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia].
        + cbn [disjoint_from cells_size csize Nat.add]. split; [clear - APX; lia| exact I].
      - eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) (mpd_keep LB dX) ((FB, 64) :: LF) sp1 (arl_stklo R)
                  (hstkhi asegs R HIA hc) [(X, X + 16)] mc m2 FB _ CSOK); [| | | exact HP2| exact MCS|].
        + cbn [cells_size csize Nat.add]. eapply crange_sub; [exact CFBc| clear; lia| clear; lia].
        + clear - F64. Z.div_mod_to_equations. lia.
        + clear - F0. lia.
        + intros c Hc. cbn [cells_size csize Nat.add] in Hc. right; right; left. exists (FB, 64).
          split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia].
      - exists wl. eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2 FLB).
        + cbn [cells_size csize Nat.add]. eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia].
        + cbn [disjoint_from cells_size csize Nat.add]. split; [clear - APX; lia| exact I].
      - eapply (presA_sshad asegs R _ _ _ _ _ _ mc m2 _ _ HP2 SSH); [exact SLOS|].
        rewrite HS1, Estk. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP. clear - HTOP TOP. lia. }
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    zstep. if_cases KR; zify_cond KR.
    - eapply (md_join h1 m1 FB sp1 _ _ h2 LB2 m2 dX2 r);
        [ exact MB | exact J1 | exact CELLS2 | intros E; exfalso; apply KR; rewrite E; reflexivity | exact RR | exact HSZ2
        | clear - NRB; lia | unfold add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - D0; lia ].
    - assert (R0 : r = 0) by (clear - KR RR; Z.div_mod_to_equations; lia). subst r.
      pose proof (RB eq_refl) as BPOS.
      assert (SGB : md_sg dB = 1).
      { destruct (proj2 MB0) as [S1|Sm]; [exact S1| exfalso].
        unfold mpd_val in VB0. unfold mpd_abs in BPOS. rewrite Sm in VB0. clear - VB0 BPOS. lia. }
      do 5 zstep.
      pose proof (md_L1 (S (Z.to_nat (Z.abs (mpd_val dX2))))) as HL1. unfold mdL1_stmt in HL1.
      eapply HL1; [ exact MB | exact J1 | exact DBJ | exact B1 | exact CELLS2 | exact SGB | exact BPOS | | exact HSZ2 | clear; lia | clear; lia ].
      rewrite Nat2Z.inj_succ, Z2Nat.id by (apply Z.abs_nonneg).
      pose proof (Z.abs_nonneg (mpd_val dX2)) as AB0.
      assert (AB1 : - mpd_val dX2 <= Z.abs (mpd_val dX2)) by (clear; lia).
      assert (K : Z.abs (mpd_val dX2) + 1 <= (Z.abs (mpd_val dX2) + 1) * mpd_abs dB) by (clear - AB0 BPOS; nia).
      clear - K AB1. lia.
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d1a_BR : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (hc : HST asegs R HIA) (mc : mem)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] 0 0 hc LB mc dX ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LB mc dX ->
      mpd_at asegs mc LB dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dX ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dB ->
      MD_CELLS mc FB SHB ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 (Z.sgn (mpd_val dB)))
                 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X)
                 (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 (-8))
                 xs9 xs10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa05ec) fc None mc (seg_rom asegs)).
  Proof.
    intros h1 m1 FB sp1 hc mc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xt3 xt4 xt5 xt6
      MB J JB BJ MA OXc OAc OBc MC.
    zstep.
    if_cases BR; zify_cond BR.
    - zstep.
      eapply (md_join h1 m1 FB sp1 0 0 hc LB mc dX (-10)); [exact MB| exact J| exact MC| | | | |].
      + intros E. clear - E. lia.
      + clear. lia.
      + unfold div_mpi_nz. cbn [md_n]. clear. lia.
      + clear - PHId0 NRB. lia.
      + unfold add_sub_FR, add_abs_FR. pose proof (calls_FR_nonneg 8 (d + 1)) as CF. clear - CF FRd0 D0. lia.
    - assert (BN : 0 <= mpd_val dB).
      { destruct (Z.lt_trichotomy (mpd_val dB) 0) as [N|[N|N]];
          [exfalso; rewrite (Z.sgn_neg _ N) in BR; clear - BR; Z.div_mod_to_equations; lia| clear - N; lia| clear - N; lia]. }
      eapply (d1_DIVCALL h1 m1 FB sp1 hc mc); [exact MB| exact J| exact JB| exact BJ| exact MA| exact OXc| exact OAc| exact OBc| exact MC| exact BN].
  Qed.

  Definition d1s_graft (a n : Z) (mn mo : mem) : mem :=
    fun x => if (a <=? bv_unsigned x) && (bv_unsigned x <? a + n) then mn x else mo x.

  #[using="Type"] Lemma d1s_g_pt : forall (m1 mc mc' : mem) (a n : Z) (x : word),
      munch [(a, a + n)] mc mc' -> mc x = m1 x ->
      mc' x = (if ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n))%bool then mc' x else m1 x)
      /\ (wview asegs (fun y => if ((a <=? bv_unsigned y) && (bv_unsigned y <? a + n))%bool then mc' y else m1 y) x <> None ->
          wview asegs mc' x <> None).
  Proof.
    intros m1 mc mc' a n x HM E.
    assert (G : mc' x = (if ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n))%bool then mc' x else m1 x)).
    { destruct ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n))%bool eqn:B; [reflexivity|].
      rewrite <- E. apply HM. cbn. split; [|exact I].
      apply andb_false_iff in B. clear - B. destruct B as [B|B]; [apply Z.leb_gt in B| apply Z.ltb_ge in B]; lia. }
    split; [exact G|]. unfold wview. cbn beta. rewrite <- G. auto.
  Qed.

  #[using="Type"] Lemma d1s_presA_graft : forall (K LFk : list blk) (SP SSP TOP : Z) (W0 : list ivl) (m1 mc mc' : mem) (a n : Z), presA asegs R K LFk SP SSP TOP W0 m1 mc -> munch [(a, a + n)] mc mc' -> 0 <= a -> a + n <= 2^64 -> presA asegs R K LFk SP SSP TOP W0 (fun x => if ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n))%bool then mc' x else m1 x) mc'.
  Proof.
    intros K LFk SP SSP TOP W0 m1 mc mc' a n HP HM Ha Han.
    destruct HP as [HP1 HP2]. split.
    - intros x Hx Hc Ho. destruct (HP1 x Hx Hc Ho) as [E _]. exact (d1s_g_pt m1 mc mc' a n (wa x) HM E).
    - intros c Hc Hr. destruct (HP2 c Hc Hr) as [E _]. exact (d1s_g_pt m1 mc mc' a n _ HM E).
  Qed.

  #[using="Type"] Lemma d1s_b_gin : forall (a n : Z) (mn mq : mem) (x : word), a <= bv_unsigned x < a + n -> d1s_graft a n mn mq x = mn x.
  Proof.
    intros a n mn mq x H. unfold d1s_graft. clear - H.
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity; exfalso; lia.
  Qed.

  #[using="Type"] Lemma d1s_b_gout : forall (a n : Z) (mn mq : mem) (x : word), ~ (a <= bv_unsigned x < a + n) -> d1s_graft a n mn mq x = mq x.
  Proof.
    intros a n mn mq x H. unfold d1s_graft. clear - H.
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity; exfalso; lia.
  Qed.

  #[using="Type"] Lemma d1s_b_wv : forall (m0 m' : mem) (x : word), m' x = m0 x -> wview asegs m' x = wview asegs m0 x.
  Proof. intros m0 m' x E. unfold wview. rewrite E. reflexivity. Qed.

  #[using="Type"] Lemma d1s_b_wa : forall x : word, wa (bv_unsigned x) = x.
  Proof. intros x. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

  #[using="Type"] Lemma d1s_b_wr : forall x : word, 0 <= bv_unsigned x < 2^64.
  Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

  #[using="Type"] Lemma d1s_b_disj : forall (A k lo0 hi0 a n : Z), (forall x, A <= x < A + k -> ~ (lo0 <= x < hi0)) ->
      0 < k -> lo0 < hi0 -> lo0 <= a -> a + n <= hi0 -> disjoint_from [(a, a + n)] A k.
  Proof.
    intros A k lo0 hi0 a n H K L0 L1 L2. clear - H K L0 L1 L2. cbn [disjoint_from]. split; [|exact I].
    destruct (Z_lt_le_dec lo0 (A + k)) as [H1|H1]; [|left; lia].
    destruct (Z_lt_le_dec A hi0) as [H2|H2]; [|right; lia].
    exfalso. destruct (Z_le_gt_dec A lo0) as [H3|H3]; [apply (H lo0)| apply (H A)]; lia.
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d1s_rebase_base : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc mc' : mem) (dXc : mpd) (a n : Z),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      0 <= n ->
      ((FB <= a /\ a + n <= FB + 24) \/ (FB + 32 <= a /\ a + n <= FB + 56) \/
       (Z.shiftr FB 3 + al_sb AL <= a /\ a + n <= Z.shiftr FB 3 + al_sb AL + 8)) ->
      munch [(a, a + n)] mc mc' -> wmono asegs mc mc' -> mem_inv asegs mc' ->
      HM asegs R HIA hc LBc ((FB, 64) :: LF) mc' ->
      MD_BASE h1 (d1s_graft a n mc' m1) FB sp1
      /\ JBA asegs R HIA LB ((FB, 64) :: LF) (d1s_graft a n mc' m1) dX sp lo dB.
  Proof.
    intros h1 m1 FB sp1 v f hc LBc mc mc' dXc a n MB J JB BJ N0 RNG MU WM MI' HH'.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NST1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    pose proof MB as (SP1 & SP1M & F64 & FRSH & JC1 & PRES & Ecs & Etop & Estk & Eflag & Evol & Efr & HKI).
    pose proof JC1 as [NEEDR HND DIMG ROIMG HH0 MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof JB as [JB1 JB2 JB3 JB4 JB5 JB6].
    pose proof JC as [_ _ _ _ _ _ _ XW0 _ _ _ _ _ _ _]. destruct XW0 as [CW _].
    pose proof (d4_crw _ _ _ _ _ CW) as CRX.
    pose proof FRSH as (F0 & F1 & F2 & F3).
    pose proof PRES as (P0 & C1 & C2 & C3).
    pose proof (art_lo asegs R HIA) as ALO.
    assert (SPGE : arl_stklo R <= bv_unsigned sp) by (clear - LOS SLO NEEDR; lia).
    assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
    rewrite SHFB in RNG.
    assert (DIV : forall k, (FB + 8 * k) / 8 = FB / 8 + k).
    { intros k. rewrite (Z.mul_comm 8 k), Z.div_add by lia; reflexivity. }
    pose proof (hcs_fake asegs R HIA h1 LB ((FB, 64) :: LF) m1 FB 64 HH0 ltac:(left; reflexivity)) as CFB. rewrite Ecs in CFB.
    assert (SBND : hl_data_hi L <= FB / 8 + al_sb AL /\ FB / 8 + al_sb AL + 8 <= alloc_ceiling).
    { pose proof (hcs_shadow_band asegs R HIA h FB (CFB FB ltac:(lia))) as SBlo.
      pose proof (hcs_shadow_band asegs R HIA h (FB + 8 * 7) (CFB (FB + 8 * 7) ltac:(lia))) as SBhi.
      unfold shadow_of in SBlo, SBhi. rewrite DIV in SBhi. clear - SBlo SBhi. lia. }
    assert (SHEQ : forall y, FB / 8 + al_sb AL <= y < FB / 8 + al_sb AL + 8 ->
                   FB <= FB + 8 * (y - (FB / 8 + al_sb AL)) < FB + 64 /\ shadow_of AL (FB + 8 * (y - (FB / 8 + al_sb AL))) = y).
    { intros y Hy. split; [lia|]. unfold shadow_of. rewrite DIV. lia. }
    assert (SHINV : forall c, FB / 8 + al_sb AL <= shadow_of AL c < FB / 8 + al_sb AL + 8 -> FB <= c < FB + 64).
    { intros c Hc. unfold shadow_of in Hc. clear - Hc F64. Z.div_mod_to_equations. lia. }
    assert (CLI : forall B y, arl_stklo R <= B -> client_addr L (LB ++ fdata LF) B y ->
                  ~ (FB <= y < FB + 64) /\ ~ (FB / 8 + al_sb AL <= y < FB / 8 + al_sb AL + 8)).
    { intros B y HB Hc. unfold client_addr in Hc. destruct Hc as [Hs|[(Hd1 & Hd2)|([B0 j] & Hb & Hr)]].
      - clear - Hs HB F1 ALO SBND. split; lia.
      - clear - Hd1 F2 SBND. split; lia.
      - cbn [fst snd] in Hr. split; [destruct (F3 B0 j Hb); lia|].
        intros Hy. destruct (SHEQ y Hy) as [Hc SHE].
        pose proof (C2 B0 j Hb y Hr) as HY. pose proof (CFB _ Hc) as HC.
        destruct (hcs_ok asegs R HIA h) as [OK1 _]. destruct (OK1 _ HC) as (_ & _ & _ & NC).
        rewrite SHE in NC. exact (NC HY). }
    assert (CSH : forall c, cshd R LB LF (arl_stklo R) (hstkhi asegs R HIA h) c ->
                  ~ (FB <= shadow_of AL c < FB + 64) /\ ~ (FB / 8 + al_sb AL <= shadow_of AL c < FB / 8 + al_sb AL + 8)).
    { intros c Hc. split.
      - intros Hin. pose proof (C1 c Hc) as HC. pose proof (CFB _ Hin) as HS.
        destruct (hcs_ok asegs R HIA h) as [OK1 _]. destruct (OK1 _ HC) as (_ & _ & _ & NC). exact (NC HS).
      - intros Hin. pose proof (SHINV c Hin) as Hf. unfold cshd, cstatic in Hc.
        pose proof (hm_fresh_frame_apart asegs R HIA h1 LB LF m1 FB 64 HH0) as FAP.
        destruct Hc as [Hs|[([B0 j] & Hb & Hr)|[([B0 j] & Hb & Hr)|(Hd1 & Hd2)]]].
        + clear - Hs Hf F1 ALO. lia.
        + cbn [fst snd] in Hr. destruct (F3 B0 j ltac:(apply in_app_iff; left; exact Hb)); lia.
        + cbn [fst snd] in Hr. destruct (FAP B0 j Hb); lia.
        + clear - Hd1 Hf F2. lia. }
    assert (RG : exists lo0 hi0, lo0 < hi0 /\ lo0 <= a /\ a + n <= hi0 /\
                 (forall y, lo0 <= y < hi0 -> FB <= y < FB + 64 \/ FB / 8 + al_sb AL <= y < FB / 8 + al_sb AL + 8)).
    { destruct RNG as [R1|[R2|R3]].
      - exists FB, (FB + 64). split; [lia|]. split; [lia|]. split; [lia|]. intros y Hy. left. lia.
      - exists FB, (FB + 64). split; [lia|]. split; [lia|]. split; [lia|]. intros y Hy. left. lia.
      - exists (FB / 8 + al_sb AL), (FB / 8 + al_sb AL + 8). split; [lia|]. split; [lia|]. split; [lia|]. intros y Hy. right. lia. }
    assert (NIR : forall y, ~ (FB <= y < FB + 64) /\ ~ (FB / 8 + al_sb AL <= y < FB / 8 + al_sb AL + 8) -> ~ (a <= y < a + n)).
    { intros y [N1 N2] Hy. destruct RG as (lo0 & hi0 & _ & L1 & L2 & L3).
      destruct (L3 y ltac:(lia)) as [H|H]; [exact (N1 H)| exact (N2 H)]. }
    assert (DISJ : forall A k, 0 < k ->
                   (forall y, A <= y < A + k -> ~ (FB <= y < FB + 64) /\ ~ (FB / 8 + al_sb AL <= y < FB / 8 + al_sb AL + 8)) ->
                   disjoint_from [(a, a + n)] A k).
    { intros A k K HP. destruct RG as (lo0 & hi0 & L0 & L1 & L2 & L3).
      apply (d1s_b_disj A k lo0 hi0 a n); [| exact K| exact L0| exact L1| exact L2].
      intros y Hy Hr. destruct (HP y Hy) as [N1 N2]. destruct (L3 y Hr) as [H|H]; [exact (N1 H)| exact (N2 H)]. }
    assert (SHW : forall y, FB / 8 + al_sb AL <= y < FB / 8 + al_sb AL + 8 -> wview asegs mc' (wa y) <> None).
    { intros y Hy. destruct (SHEQ y Hy) as [Hc SHE].
      pose proof (hcs_fake asegs R HIA hc LBc ((FB, 64) :: LF) mc' FB 64 HH' ltac:(left; reflexivity) _ Hc) as HC.
      destruct (hm_shadow_rd asegs R HIA hc LBc ((FB, 64) :: LF) mc' _ HH' HC) as (bb & _ & (_ & _ & WR)).
      pose proof (WR 0 ltac:(lia)) as W0. rewrite Z.add_0_r, SHE in W0. exact W0. }
    pose proof (presA_presx asegs R _ _ _ _ _ _ m1 mc HPX1) as HPXh.
    assert (INW : forall x : word, a <= bv_unsigned x < a + n -> wview asegs m1 x <> None -> wview asegs mc' x <> None).
    { intros x Hx Wm. destruct RNG as [R1|[R2|R3]].
      - assert (HO : outside [(md_addr dX, md_addr dX + 16)] (bv_unsigned x)).
        { cbn [outside]. split; [|exact I]. intros Hy. destruct (CLI _ _ SPGE (CRX _ Hy)) as [NF _]. apply NF. lia. }
        assert (HCa : client_addr L (mpd_keep LB dX ++ fdata ((FB, 64) :: LF)) (bv_unsigned sp) (bv_unsigned x)).
        { unfold client_addr. right. right. exists (FB, 24). split; [apply in_app_iff; right; left; reflexivity| cbn [fst snd]; lia]. }
        destruct (HPXh _ (d1s_b_wr x) HCa HO) as [_ W1]. rewrite d1s_b_wa in W1. exact (WM x (W1 Wm)).
      - assert (HO : outside [(md_addr dX, md_addr dX + 16)] (bv_unsigned x)).
        { cbn [outside]. split; [|exact I]. intros Hy. destruct (CLI _ _ SPGE (CRX _ Hy)) as [NF _]. apply NF. lia. }
        assert (HCa : client_addr L (mpd_keep LB dX ++ fdata ((FB, 64) :: LF)) (bv_unsigned sp) (bv_unsigned x)).
        { unfold client_addr. right. right. exists (FB + 32, 24). split; [apply in_app_iff; right; right; left; reflexivity| cbn [fst snd]; lia]. }
        destruct (HPXh _ (d1s_b_wr x) HCa HO) as [_ W1]. rewrite d1s_b_wa in W1. exact (WM x (W1 Wm)).
      - pose proof (SHW (bv_unsigned x) ltac:(lia)) as W0. rewrite d1s_b_wa in W0. exact W0. }
    assert (MUG : munch [(a, a + n)] m1 (d1s_graft a n mc' m1)).
    { intros x Ho. cbn [outside] in Ho. destruct Ho as [Ho _]. exact (d1s_b_gout a n mc' m1 x Ho). }
    assert (WMG : wmono asegs m1 (d1s_graft a n mc' m1)).
    { intros x Wm. destruct (Z_le_gt_dec a (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L2|L2]|].
      - rewrite (d1s_b_wv mc' (d1s_graft a n mc' m1) x (d1s_b_gin a n mc' m1 x (conj L1 L2))). exact (INW x (conj L1 L2) Wm).
      - rewrite (d1s_b_wv m1 (d1s_graft a n mc' m1) x (d1s_b_gout a n mc' m1 x ltac:(lia))). exact Wm.
      - rewrite (d1s_b_wv m1 (d1s_graft a n mc' m1) x (d1s_b_gout a n mc' m1 x ltac:(lia))). exact Wm. }
    assert (HMG : HM asegs R HIA h1 LB ((FB, 64) :: LF) (d1s_graft a n mc' m1)).
    { apply (hm_frame asegs R HIA h1 LB ((FB, 64) :: LF) m1 (d1s_graft a n mc' m1) HH0); [| exact WMG].
      intros y Hy NW. apply d1s_b_gout. rewrite (wa_unsigned y Hy). intros Hr. apply NW. unfold hm_writable.
      destruct RNG as [R1|[R2|R3]].
      - left. unfold client_waddr. right. right. exists (FB, 24).
        split; [apply in_app_iff; right; left; reflexivity| cbn [fst snd]; lia].
      - left. unfold client_waddr. right. right. exists (FB + 32, 24).
        split; [apply in_app_iff; right; right; left; reflexivity| cbn [fst snd]; lia].
      - right. destruct (SHEQ y ltac:(lia)) as [Hc SHE]. exists (FB + 8 * (y - (FB / 8 + al_sb AL))).
        split; [right; exists (FB, 64); split; [left; reflexivity| cbn [fst snd]; lia]| symmetry; exact SHE]. }
    assert (MXG : mpd_at asegs (d1s_graft a n mc' m1) LB dX).
    { apply (mpd_at_munch asegs m1 (d1s_graft a n mc' m1) LB dX [(a, a + n)] MX NST MUG WMG).
      - apply DISJ; [lia|]. intros y Hy. exact (CLI _ _ SPGE (CRX y Hy)).
      - intros EOH.
        pose proof (opnd_viewA asegs R LF m1 LB (bv_unsigned sp) dX (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dX MX)) as [(_ & _ & _ & _ & _ & OWN) _].
        rewrite EOH in OWN. destruct OWN as (N1 & IN & _).
        apply DISJ; [lia|]. intros y Hy. apply (CLI _ _ SPGE). unfold client_addr. right. right. exists (md_p dX, 4 * md_n dX).
        split; [apply in_app_iff; left; exact IN| cbn [fst snd]; lia]. }
    assert (OPG : opnd_atA asegs R ((FB, 64) :: LF) (d1s_graft a n mc' m1) LB (bv_unsigned sp) dB).
    { apply (opnd_atA_munch_any asegs R ((FB, 64) :: LF) m1 (d1s_graft a n mc' m1) LB (bv_unsigned sp) dB [(a, a + n)] JB1 MUG WMG).
      - apply DISJ; [lia|]. intros y Hy. exact (CLI _ _ LOS (CRB y Hy)).
      - intros NN.
        pose proof (opnd_viewA asegs R LF m LB (bv_unsigned sp) dB (opnd_atA_mpd asegs R LF m LB (bv_unsigned sp) dB MB0)) as [(_ & _ & _ & _ & _ & OWNB) _].
        case_eq (md_own dB); intros EOB; [exfalso; exact (NN EOB)| |].
        + rewrite EOB in OWNB. destruct OWNB as (N1 & _). apply DISJ; [lia|]. intros y Hy. exact (CLI _ _ LOS (CRBL EOB y Hy)).
        + rewrite EOB in OWNB. destruct OWNB as (N1 & _ & _ & _ & HRO). apply DISJ; [lia|]. intros y Hy.
          destruct HRO as [HRO|(HCR & _)].
          * pose proof (HRO (y - md_p dB) ltac:(lia)) as RO. replace (md_p dB + (y - md_p dB)) with y in RO by ring.
            split.
            -- intros Hin. pose proof (CFB _ Hin) as HC. destruct (hcs_ok asegs R HIA h) as [OK1 _]. destruct (OK1 _ HC) as (YR & _).
               destruct (ROIMG y RO YR) as [I1 I2]. destruct (hm_apart asegs R HIA h1 _ _ _ HH0) as [HAP _]. rewrite Forall_forall in HAP.
               destruct (HAP (FB, 64) ltac:(apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & IMGA). cbn [fst snd] in IMGA. lia.
            -- intros Hin. pose proof (SHW y Hin) as W0. destruct (mc' (wa y)) as [bb|] eqn:E.
               ++ rewrite (MI' _ _ E) in RO. discriminate.
               ++ rewrite (wview_not_ro asegs mc' (wa y) W0 E) in RO. discriminate.
          * apply (CLI _ _ SPGE). pose proof (HCR y Hy) as HC. unfold client_addr in HC |- *.
            destruct HC as [HC|[HC|([B0 j] & Hb & Hr)]];
              [left; exact HC| right; left; exact HC| right; right; exists (B0, j); split; [apply in_app_iff; right; exact Hb| exact Hr]]. }
    assert (PRG : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m (d1s_graft a n mc' m1)).
    { unfold presW. split; [| split; [exact C1| split; [exact C2| exact C3]]].
      unfold presA in P0 |- *. destruct P0 as [P1 P2]. split.
      - intros y Hy Hc Ho. destruct (P1 y Hy Hc Ho) as [E1 W1].
        assert (GE : d1s_graft a n mc' m1 (wa y) = m1 (wa y)).
        { apply d1s_b_gout. rewrite (wa_unsigned y Hy). apply NIR. exact (CLI _ _ SPGE Hc). }
        split; [rewrite GE; exact E1| intros Wm; rewrite (d1s_b_wv m1 _ (wa y) GE); exact (W1 Wm)].
      - intros c Hc Hr. destruct (P2 c Hc Hr) as [E1 W1].
        assert (GE : d1s_graft a n mc' m1 (wa (shadow_of AL c)) = m1 (wa (shadow_of AL c))).
        { apply d1s_b_gout. rewrite (wa_unsigned _ Hr). apply NIR. exact (CSH c Hc). }
        split; [rewrite GE; exact E1| intros Wm; rewrite (d1s_b_wv m1 _ _ GE); exact (W1 Wm)]. }
    split.
    - unfold MD_BASE.
      refine (conj SP1 (conj SP1M (conj F64 (conj FRSH (conj _ (conj PRG (conj Ecs (conj Etop (conj Estk (conj Eflag (conj Evol (conj Efr HKI)))))))))))).
      constructor; [exact NEEDR| exact HND| exact DIMG| exact ROIMG| exact HMG| exact MXG| exact NST| exact XW| exact XLS| exact LOS
                   | exact FS16| exact SLO| exact TOP| exact SPA| exact FSZ].
    - constructor; [exact OPG| exact JB2| exact JB3| exact JB4| exact JB5| exact JB6].
  Qed.

  #[using="Type"] Lemma d1s_x_crfb : forall (lo' A k FB : Z),
      fresh_apart R LB LF FB 64 -> FB + 64 <= lo' -> client_range L (LB ++ fdata LF) lo' A k -> 0 < k ->
      A + k <= FB \/ FB + 64 <= A.
  Proof.
    intros lo' A k FB FR LE CR K. destruct FR as (F0 & F1 & F2 & F3).
    destruct (Z_le_gt_dec (A + k) FB) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (FB + 64) A) as [H2|H2]; [right; exact H2|].
    exfalso. destruct (CR (Z.max A FB) ltac:(clear - H1 H2 K; lia)) as [C|[[C _]|([B j] & Hb & C)]].
    - clear - C LE H1 H2. lia.
    - clear - C F2 H1 H2. lia.
    - cbn [fst snd] in C. destruct (F3 B j Hb) as [E|E]; clear - C E H1 H2; lia.
  Qed.

  #[using="Type"] Lemma d1s_x_aobj : forall (CS : Z -> Prop) (mx mx' : mem) (A k FB a n : Z),
      cs_ok AL CS -> crange CS FB 64 -> FB mod 64 = 0 -> 0 <= n ->
      ((FB <= a /\ a + n <= FB + 64) \/ (Z.shiftr FB 3 + al_sb AL <= a /\ a + n <= Z.shiftr FB 3 + al_sb AL + 8)) ->
      munch [(a, a + n)] mx mx' -> (A + k <= FB \/ FB + 64 <= A) ->
      aobj asegs AL CS mx A k -> aobj asegs AL CS mx' A k.
  Proof.
    intros CS mx mx' A k FB a n CSOK CFB F64 N0 RG MU AP OBX.
    assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
    destruct RG as [[R1 R2]|[R1 R2]].
    - eapply (aobj_munch asegs AL CS CSOK [(a, a + n)] mx mx'); [| exact MU| exact OBX].
      unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros x Hx. apply CFB. clear - Hx R1 R2. lia.
    - destruct OBX as [HC HS]. split; [exact HC|]. unfold shadow_ok in HS |- *. intros c Hc.
      destruct (HS c Hc) as (b & RD & HB). exists b. split; [| exact HB].
      eapply bytes_at_transport; [exact RD| exact MU|]. cbn [disjoint_from length Z.of_nat Pos.of_succ_nat]. split; [| exact I].
      unfold shadow_of. rewrite SHFB in R1, R2. clear - R1 R2 AP Hc F64. Z.div_mod_to_equations. lia.
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d1s_rebase_xja : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc mc' : mem) (dXc : mpd) (a n : Z),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      0 <= n ->
      ((FB <= a /\ a + n <= FB + 24) \/ (FB + 32 <= a /\ a + n <= FB + 56) \/
       (Z.shiftr FB 3 + al_sb AL <= a /\ a + n <= Z.shiftr FB 3 + al_sb AL + 8)) ->
      munch [(a, a + n)] mc mc' -> wmono asegs mc mc' -> mem_inv asegs mc' ->
      HM asegs R HIA hc LBc ((FB, 64) :: LF) mc' ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) (d1s_graft a n mc' m1) dX sp lo 96 MD_FRAME_A [] v f hc LBc mc' dXc
      /\ BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc' dXc.
  Proof.
    intros h1 m1 FB sp1 v f hc LBc mc mc' dXc a n MB J JB BJ N0 RG MU WM MI' HH'.
    jc_open. basic_factsA hc.
    destruct MB as (SP1 & SP1M & F64 & FRSH & JC1 & PRES & Ecs & Etop & Estk & Eflag & Evol & Efr & HKI).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NST1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    pose proof BJ as [BA BS BL BO BOL].
    pose proof FRSH as (F0 & F1 & F2 & F3).
    assert (RG2 : (FB <= a /\ a + n <= FB + 64) \/ (Z.shiftr FB 3 + al_sb AL <= a /\ a + n <= Z.shiftr FB 3 + al_sb AL + 8))
      by (clear - RG; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
    assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA hc _ _ mc' FB 64 HH' INF) as CFB.
    assert (SBND : hl_data_hi L <= Z.shiftr FB 3 + al_sb AL /\ Z.shiftr FB 3 + al_sb AL + 8 <= alloc_ceiling).
    { pose proof (hcs_shadow_band asegs R HIA hc FB (CFB FB ltac:(clear; lia))) as SBlo.
      pose proof (hcs_shadow_band asegs R HIA hc (FB + 8 * 7) (CFB (FB + 8 * 7) ltac:(clear; lia))) as SBhi.
      rewrite shadow_of_plus in SBhi. unfold shadow_of in SBlo, SBhi. rewrite <- SHFB in SBlo, SBhi. clear - SBlo SBhi. lia. }
    assert (FB8 : 0 <= FB / 8) by (apply Z.div_pos; clear - F0; lia).
    assert (A0 : 0 <= a) by (clear - RG2 F0 FB8 SHFB SB64; lia).
    assert (AN : a + n <= 2 ^ 64) by (clear - RG2 SBND F1 ALO LOS SLO NEEDR SPR; lia).
    assert (SH : forall A k, crange (hcs asegs R HIA hc) A k -> 0 < k ->
                 Z.shiftr FB 3 + al_sb AL + 8 <= A \/ A + k <= Z.shiftr FB 3 + al_sb AL).
    { intros A k CA K.
      pose proof (apart_shadow_client AL (hcs asegs R HIA hc) A k FB (shadow_of AL FB) 8 CSOK CA CFB eq_refl K ltac:(clear; lia)) as P.
      unfold shadow_of in P. rewrite SHFB. clear - P. lia. }
    assert (DJ : forall A k, (A + k <= FB \/ FB + 64 <= A) ->
                 (Z.shiftr FB 3 + al_sb AL + 8 <= A \/ A + k <= Z.shiftr FB 3 + al_sb AL) ->
                 disjoint_from [(a, a + n)] A k).
    { intros A k P1 P2. cbn [disjoint_from]. split; [| exact I]. clear - RG2 P1 P2 N0. lia. }
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1, Estk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (SH lo (bv_unsigned sp - lo) SCS ltac:(clear - SLO NEEDR; lia)) as SHS.
    destruct XW as [CW _].
    pose proof (d1s_x_crfb (bv_unsigned sp) X 16 FB FRSH ltac:(clear - FBLO SLO NEEDR; lia) (d4_crw _ _ _ _ _ CW) ltac:(clear; lia)) as FBX.
    pose proof (SH X 16 (aobj_crange asegs AL _ _ _ _ OX1) ltac:(clear; lia)) as SHX.
    assert (XLIM : md_own dXc <> LNull -> 1 <= md_n dXc /\ In (md_p dXc, 4 * md_n dXc) LBc).
    { intros NN. pose proof MX1 as [(_ & _ & _ & _ & _ & OW) _].
      destruct (md_own dXc); [exfalso; exact (NN eq_refl)| exact (conj (proj1 OW) (proj1 (proj2 OW)))| exfalso; exact (NST1 eq_refl)]. }
    destruct (hm_apart asegs R HIA hc LBc ((FB, 64) :: LF) mc' HH') as [HFA BAP].
    rewrite Forall_forall in HFA. destruct (HFA (FB, 64) ltac:(apply in_or_app; right; exact INF)) as (_ & _ & _ & FIMG). cbn [fst snd] in FIMG.
    assert (FBXL : md_own dXc <> LNull -> md_p dXc + 4 * md_n dXc <= FB \/ FB + 64 <= md_p dXc).
    { intros NN. destruct (XLIM NN) as [_ XIN]. exact (blocks_apart_app_lr LBc ((FB, 64) :: LF) _ _ FB 64 BAP XIN INF). }
    assert (SHXL : md_own dXc <> LNull -> Z.shiftr FB 3 + al_sb AL + 8 <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= Z.shiftr FB 3 + al_sb AL).
    { intros NN. destruct (XLIM NN) as [N1 XIN]. apply SH; [exact (hcs_block asegs R HIA hc LBc _ mc' _ _ HH' XIN)| clear - N1; lia]. }
    pose proof (d1s_x_crfb lo (md_addr dB) 16 FB FRSH FBLO CRB ltac:(clear; lia)) as FBB.
    pose proof (SH (md_addr dB) 16 (aobj_crange asegs AL _ _ _ _ BO) ltac:(clear; lia)) as SHBs.
    assert (BLIM : md_own dB <> LNull -> 1 <= md_n dB /\ (md_p dB + 4 * md_n dB <= FB \/ FB + 64 <= md_p dB)).
    { intros NN. pose proof (BOL NN) as OBL. pose proof MB0 as [(_ & _ & _ & _ & _ & OW) _].
      destruct (md_own dB) eqn:EB; [exfalso; exact (NN eq_refl)| |].
      - destruct OW as (N1 & BIN & _). split; [exact N1|].
        destruct (F3 _ _ (in_or_app _ _ _ (or_introl BIN))) as [E|E]; [right; exact E| left; exact E].
      - destruct OW as (N1 & _ & _ & _ & RO). split; [exact N1|].
        pose proof (aobj_crange asegs AL _ _ _ _ OBL) as CRL.
        pose proof (hcs_app asegs R HIA hc _ _ CRL ltac:(clear - N1; lia)) as HAPP.
        pose proof (RO 0 ltac:(clear - N1; lia)) as RO0. rewrite Z.add_0_r in RO0.
        pose proof (RO (4 * md_n dB - 1) ltac:(clear - N1; lia)) as RO1.
        pose proof (ROIMG _ RO0 ltac:(clear - HAPP SB64 N1; lia)) as I0.
        pose proof (ROIMG _ RO1 ltac:(clear - HAPP SB64 N1; lia)) as I1.
        clear - I0 I1 FIMG N1. lia. }
    assert (SHBL : md_own dB <> LNull -> Z.shiftr FB 3 + al_sb AL + 8 <= md_p dB \/ md_p dB + 4 * md_n dB <= Z.shiftr FB 3 + al_sb AL).
    { intros NN. destruct (BLIM NN) as [N1 _]. apply SH; [exact (aobj_crange asegs AL _ _ _ _ (BOL NN))| clear - N1; lia]. }
    split.
    - constructor; [exact MI'| | | exact HH'| exact HT1| exact HS1| exact HF1| exact HCS1| exact HV1| exact HFR1| | exact AD1| exact PD1
                   | exact NST1| exact OUT1| exact FRS1| exact FRA1| | | exact XP1| exact XLS1| exact NM1].
      + eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply DJ; clear - FBLO SHS SLO NEEDR; lia.
      + eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. rewrite FSZ. apply DJ; clear - FBLO SHS SLO NEEDR; lia.
      + eapply (mpd_at_munch_any asegs mc mc' LBc dXc [(a, a + n)] MX1 MU WM).
        * rewrite AD1. cbn [md_addr]. apply DJ; clear - FBX SHX; lia.
        * intros NN. pose proof (FBXL NN) as P1. pose proof (SHXL NN) as P2. apply DJ; clear - P1 P2; lia.
      + exact (d1s_presA_graft _ _ _ _ _ _ _ _ _ _ _ HPX1 MU A0 AN).
      + exact (d1s_x_aobj _ mc mc' X 16 FB a n CSOK CFB F64 N0 RG2 MU FBX OX1).
    - constructor; [| exact BS| exact BL| |].
      + eapply (opnd_atA_munch_any asegs R ((FB, 64) :: LF) mc mc' LBc (bv_unsigned sp) dB [(a, a + n)] BA MU WM).
        * apply DJ; clear - FBB SHBs; lia.
        * intros NN. destruct (BLIM NN) as [_ P1]. pose proof (SHBL NN) as P2. apply DJ; clear - P1 P2; lia.
      + exact (d1s_x_aobj _ mc mc' _ _ FB a n CSOK CFB F64 N0 RG2 MU FBB BO).
      + intros NN. destruct (BLIM NN) as [_ P1]. exact (d1s_x_aobj _ mc mc' _ _ FB a n CSOK CFB F64 N0 RG2 MU P1 (BOL NN)).
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d1s_rebase : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (v f : Z) (hc : HST asegs R HIA)
      (LBc : list blk) (mc mc' : mem) (dXc : mpd) (a n : Z),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] v f hc LBc mc dXc ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc dXc ->
      0 <= n ->
      ((FB <= a /\ a + n <= FB + 24) \/ (FB + 32 <= a /\ a + n <= FB + 56) \/
       (Z.shiftr FB 3 + al_sb AL <= a /\ a + n <= Z.shiftr FB 3 + al_sb AL + 8)) ->
      munch [(a, a + n)] mc mc' -> wmono asegs mc mc' -> mem_inv asegs mc' ->
      HM asegs R HIA hc LBc ((FB, 64) :: LF) mc' ->
      exists m1' : mem,
        MD_BASE h1 m1' FB sp1
        /\ XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1' dX sp lo 96 MD_FRAME_A [] v f hc LBc mc' dXc
        /\ JBA asegs R HIA LB ((FB, 64) :: LF) m1' dX sp lo dB
        /\ BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LBc mc' dXc
        /\ (forall x, (a <= bv_unsigned x < a + n) -> m1' x = mc' x)
        /\ (forall x, ~ (a <= bv_unsigned x < a + n) -> m1' x = m1 x).
  Proof.
    intros h1 m1 FB sp1 v f hc LBc mc mc' dXc a n MB XJ JB BJ Hn Ha HM WM MI HMc.
    destruct (d1s_rebase_base h1 m1 FB sp1 v f hc LBc mc mc' dXc a n MB XJ JB BJ Hn Ha HM WM MI HMc) as [MB' JB'].
    destruct (d1s_rebase_xja h1 m1 FB sp1 v f hc LBc mc mc' dXc a n MB XJ JB BJ Hn Ha HM WM MI HMc) as [XJ' BJ'].
    exists (d1s_graft a n mc' m1).
    split; [exact MB'|]. split; [exact XJ'|]. split; [exact JB'|]. split; [exact BJ'|]. split.
    - intros x Hx. unfold d1s_graft.
      destruct ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n))%bool eqn:B; [reflexivity|]. exfalso.
      apply andb_false_iff in B. destruct B as [B|B]; [apply Z.leb_gt in B| apply Z.ltb_ge in B]; lia.
    - intros x Hx. unfold d1s_graft.
      destruct ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n))%bool eqn:B; [|reflexivity]. exfalso.
      apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hx. lia.
  Qed.

  #[using="Type"] Lemma d1s_d_apart : forall (CS : Z -> Prop) (c A n a : Z),
      cs_ok AL CS -> crange CS A n -> crange CS c 8 -> a = shadow_of AL c -> 0 < n ->
      disjoint_from [(a, a + 1)] A n.
  Proof.
    intros CS c A n a OK HA HC Ea Hn.
    assert (HC8 : crange CS c (8 * 1)) by (replace (8 * 1) with 8 by (clear; lia); exact HC).
    pose proof (apart_shadow_client AL CS A n c a 1 OK HA HC8 Ea Hn ltac:(clear; lia)) as K.
    cbn [disjoint_from]. split; [clear - K; lia| exact I].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma md_DIV : forall (h1 : HST asegs R HIA) (m1 : mem) (FB sp1 : Z) (hc : HST asegs R HIA) (mc : mem)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xt3 xt4 xt5 xt6 : word),
      MD_BASE h1 m1 FB sp1 ->
      XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] 0 0 hc LB mc dX ->
      JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB ->
      BJA asegs R HIA ((FB, 64) :: LF) sp dB hc LB mc dX ->
      mpd_at asegs mc LB dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dX ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA hc) mc dB ->
      MD_CELLS mc FB SHB0 ->
      aevtA asegs (KF asegs R HIA hc mo) MD_POST_A
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 (Z.sgn (mpd_val dB)))
                 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X)
                 (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 (-8))
                 xs9 xs10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa05e8) fc None mc (seg_rom asegs)).
  Proof.
    intros h1 m1 FB sp1 hc mc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xt3 xt4 xt5 xt6
      MB J JB BJ MA OXc OAc OBc MC.
    jc_open. basic_factsA hc.
    pose proof MB as MB'.
    destruct MB' as (SP1 & SP1M & F64 & FRSH & JC1 & PRES & Ecs & Etop & Estk & Eflag & Evol & Efr & HKI).
    pose proof J as [MI1 _ _ HH1 _ HS1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    cbn [app] in HH1.
    pose proof FRSH as (F0 & F1 & F2 & F3).
    assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA hc _ _ mc FB 64 HH1 INF) as CFBc.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    assert (FB8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (FBSLO : FB + 64 <= slo) by (clear - F1 ALO SLOS; lia).
    assert (SCS : crange (hcs asegs R HIA hc) slo (bv_unsigned sp - slo)).
    { eapply crange_sub; [exact SCS0| clear - SLOS; lia|].
      rewrite HS1, Estk. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP. clear - HTOP TOP. lia. }
    pose proof XW as XW'. unfold mpd_writableA in XW'. destruct XW' as [XCW _].
    assert (APX : FB + 64 <= md_addr dX \/ md_addr dX + 16 <= FB).
    { cbn [md_addr].
      destruct (fresh_apart_client0 R LB LF (bv_unsigned sp) X 16 FB 64 FRSH (d4_crw _ _ _ _ _ XCW) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear - ALO LOS SLO NEEDR; lia)) as [C|[C|C]]; [clear - C; lia| left; exact C| right; exact C]. }
    assert (APA : FB + 64 <= md_addr dA \/ md_addr dA + 16 <= FB).
    { destruct (fresh_apart_client0 R LB LF lo (md_addr dA) 16 FB 64 FRSH CRA ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear - ALO LOS; lia)) as [C|[C|C]]; [clear - C; lia| left; exact C| right; exact C]. }
    assert (APB : FB + 64 <= md_addr dB \/ md_addr dB + 16 <= FB).
    { destruct (fresh_apart_client0 R LB LF lo (md_addr dB) 16 FB 64 FRSH CRB ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear - ALO LOS; lia)) as [C|[C|C]]; [clear - C; lia| left; exact C| right; exact C]. }
    destruct OXc as [OXa _]. destruct OAc as [OAa OAl]. destruct OBc as [OBa OBl].
    pose proof MC as ((w0 & w1 & w2 & FHD) & MCS & (wl & LIMB) & SSH).
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL + 6, Z.shiftr FB 3 + al_sb AL + 6 + 1)] mc) as MU.
    pose proof (wmono_refl asegs mc) as WM.
    zstep.
    replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))) with (Z_to_bv 8 248) in MCS
      by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mn end.
    destruct (d1s_rebase h1 m1 FB sp1 0 0 hc LB mc mn dX (Z.shiftr FB 3 + al_sb AL + 6) 1 MB J JB BJ ltac:(clear; lia)
                ltac:(right; right; clear; lia) MU WM MI1 HH1) as (m1' & MB1 & J1 & JB1 & BJ1 & _ & _).
    assert (CA8 : crange (hcs asegs R HIA hc) (FB + 8 * 6) 8) by (eapply crange_sub; [exact CFBc| clear; lia| clear; lia]).
    pose proof (dt_sh_eqk AL FB 6) as EA.
    eapply (d1a_BR h1 m1' FB sp1 hc mn); [exact MB1| exact J1| exact JB1| exact BJ1| | | | | ].
    - eapply mpd_at_munch_any; [exact MA| exact MU| exact WM| |].
      + eapply (d1s_d_apart _ (FB + 8 * 6)); [exact CSOK| exact (aobj_crange _ _ _ _ _ _ OAa)| exact CA8| exact EA| clear; lia].
      + intros NN. pose proof MA as [(_ & _ & _ & _ & _ & OW) _]. revert OW.
        destruct (md_own dA) eqn:EO; intros OW; [exfalso; first [exact (NN EO)| exact (NN eq_refl)]| |].
        * destruct OW as (N1 & IN & _).
          eapply (d1s_d_apart _ (FB + 8 * 6)); [exact CSOK| | exact CA8| exact EA| clear - N1; lia].
          eapply aobj_crange. eapply (hm_aobj_block asegs R HIA hc LB ((FB, 64) :: LF) mn); [exact HH1| exact IN].
        * destruct OW as (N1 & _).
          assert (OAs : aobj asegs AL (hcs asegs R HIA hc) mc (md_p dA) (4 * md_n dA)) by first [exact (OAl EO)| exact (OAl eq_refl)].
          eapply (d1s_d_apart _ (FB + 8 * 6)); [exact CSOK| exact (aobj_crange _ _ _ _ _ _ OAs)| exact CA8| exact EA| clear - N1; lia].
    - split; [exact OXa| intros E; exfalso; exact (NST E)].
    - split; [exact OAa|]. intros EO.
      pose proof MA as [(_ & _ & _ & _ & _ & OW) _]. revert OW. rewrite EO. intros (_ & _ & _ & _ & RO).
      eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (IA2 EO RO)].
    - split; [exact OBa|]. intros EO.
      pose proof MB0 as [(_ & _ & _ & _ & _ & OW) _]. revert OW. rewrite EO. intros (_ & _ & _ & _ & RO).
      eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (IB2 EO RO)].
    - split; [exists w0, w1, w2; exact FHD| split; [exact MCS| split; [exists wl; exact LIMB| exact SSH]]].
  Qed.

  #[using="Type"] Lemma d0_kf : forall (h0 h' : HST asegs R HIA) (mo0 : Model) (Q : config -> Prop) (ms : machine_state),
      (forall mo', HK asegs R HIA h' mo' <-> HK asegs R HIA h0 mo') ->
      aevtA asegs (KF asegs R HIA h' mo0) Q ms -> aevtA asegs (KF asegs R HIA h0 mo0) Q ms.
  Proof.
    intros h0 h' mo0 Q ms HKI H. unfold aevtA in *. intros mo' [HK' FR'].
    apply H. split; [apply HKI; exact HK'| exact FR'].
  Qed.

  #[using="Type"] Lemma d0_mpd_at_cons : forall (mq : mem) (b : blk) (LBq : list blk) (dq : mpd),
      mpd_at asegs mq LBq dq -> mpd_at asegs mq (b :: LBq) dq.
  Proof.
    intros mq b LBq dq [(C & A8 & A0 & LEN & NR & OW) SG]. split; [| exact SG].
    split; [exact C|]. split; [exact A8|]. split; [exact A0|]. split; [exact LEN|]. split; [exact NR|].
    revert OW. destruct (md_own dq); intros OW; try exact OW.
    destruct OW as (N1 & IN & P16 & U). split; [exact N1|]. split; [right; exact IN|]. split; [exact P16| exact U].
  Qed.

  #[using="Type"] Lemma d0_cr_cons : forall (LBq LFq : list blk) (FBq n lo0 A k : Z),
      client_range L (LBq ++ fdata LFq) lo0 A k -> client_range L (LBq ++ fdata ((FBq, n) :: LFq)) lo0 A k.
  Proof.
    intros LBq LFq FBq n lo0 A k H a Ha. destruct (H a Ha) as [C|[C|(b & Hb & C)]];
      [left; exact C| right; left; exact C| right; right; exists b; split; [apply fdata_cons_sub; exact Hb| exact C]].
  Qed.

  Definition d0_P1 (ms : machine_state) : Prop :=
    exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (w0 w1 w2 wl padw : word)
           (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      ms = MS (mkR (Z_to_bv 64 0xa05e8) (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1)
                   (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (sp1 + 16)) xa2 xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 FB) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA))
                   (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 (-8)) s9 s10 s11
                   xt3 xt4 xt5 xt6)
              F (Z_to_bv 64 A_MPI_CMP_MPI_E) fc None m1 (seg_rom asegs)
      /\ MD_BASE h1 m1 FB sp1
      /\ rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) SHB0
      /\ rw_cells asegs m1 (FB + 32) [C4 wl]
      /\ mpd_at asegs m1 ((FB + 48, 4) :: LB) (mkMPD (sp1 + 16) 1 1 (FB + 48) [Z_to_bv 64 0] padw LHeap)
      /\ aobj asegs AL (hcs asegs R HIA h) m1 (sp1 + 16) 16
      /\ aobj asegs AL (hcs asegs R HIA h) m1 (FB + 48) 4
      /\ rw_cells asegs m1 (bv_unsigned sp - 96) MD_FRAME_A
      /\ stk asegs m1 lo sp1
      /\ stk asegs m1 sp1 (bv_unsigned sp - 96)
      /\ mem_inv asegs m1
      /\ sshad asegs AL m1 slo (bv_unsigned sp)
      /\ mpd_at asegs m1 LB dA
      /\ mpd_at asegs m1 LB dB
      /\ mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX
      /\ mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dA
      /\ mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dB.

  #[using="Type"] Lemma d0_cb4 : forall (segs : list Segment) (mq : mem) (A : Z) (pre : list cell) (bs : list byte)
      (post : list cell),
      rw_cells segs mq A (pre ++ CB 4 bs :: post) -> rw_cells segs mq A (pre ++ C4 (le_bytes_to_word bs) :: post).
  Proof.
    intros segs mq A pre bs post [[Hwf Hb] Hw].
    apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
    split; [split|].
    - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
    - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *.
      first [ rewrite le4_le_bytes_to_word by exact H2
            | lazymatch goal with |- context [?f (le_bytes_to_word bs)] => unfold f end; rewrite le4_le_bytes_to_word by exact H2 ].
      exact Hb.
    - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
  Qed.

  #[using="Type"] Lemma d0_cr_w : forall (LBq : list blk) (SPq TOPq A k : Z),
      client_wrange L LBq SPq TOPq A k -> client_range L LBq SPq A k.
  Proof.
    intros LBq SPq TOPq A k H a Ha. destruct (H a Ha) as [C|[C|C]]; [left; exact (proj1 C)| right; left; exact C| right; right; exact C].
  Qed.

  #[using="Type"] Lemma d0_mpd_pres : forall (hq : HST asegs R HIA) (LBq LFq : list blk) (SPq SSPq : Z) (mq mq' : mem)
      (dq : mpd),
      presW asegs R HIA hq LBq LFq SPq SSPq [] mq mq' -> mem_inv asegs mq -> mem_inv asegs mq' -> mpd_at asegs mq LBq dq ->
      client_range L (LBq ++ fdata LFq) SPq (md_addr dq) 16 -> mpd_at asegs mq' LBq dq.
  Proof.
    intros hq LBq LFq SPq SSPq mq mq' dq PW MI0 MI1 MD CR.
    pose proof MD as [(_ & _ & _ & _ & _ & OW) _].
    apply (mpd_at_heap_presx asegs L mq mq' LBq (LBq ++ fdata LFq) LBq SPq [] dq MD
             (presA_presx asegs R LBq LFq SPq SSPq (hstkhi asegs R HIA hq) [] mq mq' (proj1 PW)) MI0 MI1 CR).
    - intros EO. rewrite EO in OW. cbv beta iota in OW. destruct OW as (_ & IN & _).
      eapply client_range_block; [apply in_or_app; left; exact IN| apply Z.le_refl| apply Z.le_refl].
    - first [exact I | constructor | cbn; tauto].
    - intros _. first [exact I | constructor | cbn; tauto].
    - intros b Hb. unfold mpd_blk in Hb. revert Hb OW. destruct (md_own dq); intros Hb OW; try (destruct Hb; fail).
      destruct OW as (_ & IN & _). destruct Hb as [Hb|[]]. subst b. exact IN.
  Qed.

  #[using="Type"] Lemma d0_aobj_pres : forall (hq : HST asegs R HIA) (LBq LFq : list blk) (SPq SSPq : Z) (mq mq' : mem)
      (A n : Z),
      presW asegs R HIA hq LBq LFq SPq SSPq [] mq mq' -> aobj asegs AL (hcs asegs R HIA hq) mq A n ->
      client_range L (LBq ++ fdata LFq) SPq A n -> SSPq <= SPq -> aobj asegs AL (hcs asegs R HIA hq) mq' A n.
  Proof.
    intros hq LBq LFq SPq SSPq mq mq' A n PW OAq CRq HSP.
    eapply (presA_aobj0 asegs R); [exact (hcs_ok asegs R HIA hq)| exact (presW_presA asegs R HIA hq LBq LFq SPq SSPq [] mq mq' PW)
                                  | exact OAq| | right; split; [exact CRq| exact HSP]].
    intros xc Hxc. eapply hcs_below_top; exact Hxc.
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma d0_pro : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      mpd_at asegs m LB dA -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      sshad asegs AL m slo (bv_unsigned sp) ->
      mpd_aobjA asegs AL (hcs asegs R HIA h) m dX ->
      mpd_aobjA asegs AL (hcs asegs R HIA h) m dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA h) m dB ->
      evtA asegs AL (hcs asegs R HIA h) d0_P1
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB))
                 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_MPI_MOD_MPI_E) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MA0 ST MI SSH OXA OAA OBA. unfold A_MPI_MOD_MPI_E.
    assert (MIm : mem_inv asegs m /\ True) by (split; [exact MI| exact I]).
    jc_open. basic_factsA h. pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof (art_uar_img asegs R HIA) as UIMG. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo))
      by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
    destruct IMG' as (EGOT & ELO & EHI & EGSB).
    unfold A_UAR_GOT_MD in UARG. unfold A_SMALLOC_0_MD in SM0.
    zstep. carve_frame 128%nat ST.
    do 13 zstep.
    zstep. zstep.
    align32 (bv_unsigned sp + -128) sp1.
    assert (SP1 : bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128) by (clear - Hsp1 SPA SPR; subst sp1; lia).
    assert (SP1M : sp1 mod 32 = 0) by (clear - Hsp1 SPR; subst sp1; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO3 NS1 LOS ALO ACP; lia).
    clear Hsp1.
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
        pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
        destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
        pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
      end end.
    rewrite EGOT in GOT. rewrite UARG in UGOT.
    do 4 zstep. zstep. zstep. zstep. zstep.
    clear GOT GSB UGOT UFLAG AB FLIMG.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -128) ST ltac:(clear - SP1 SLO3 NS1; lia)) as [ST1 ST2]. clear ST.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      replace (Z_to_bv 64 pc) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity) end.
    lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
    callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64);
                [ exact HHc | clear - LFN; lia | clear; lia | clear; lia
                | rewrite (unsigned_lit sp1) by exact SP1R; exact ST1
                | exact LOS | rewrite (unsigned_lit sp1) by exact SP1R; clear - SLO3 SP1; lia
                | rewrite (unsigned_lit sp1) by exact SP1R; clear - SP1 TOP; lia
                | assumption | exact TPV | reflexivity ])
    end.
    clear ST1.
    lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
    clear HH.
    presA_transport HP1. clear HP1.
    lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
      destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
    destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
    change (64 * 2 ^ 0) with 64 in *.
    replace (Z.to_nat 64) with 64%nat in FRM by reflexivity.
    replace (Z.to_nat (8 * 2 ^ 0)) with 8%nat in FSH by reflexivity.
    cbn [zcells] in FSH.
    zstep. zstep.
    zstep. if_cases Kb; zify_cond Kb.
    2:{ exfalso. destruct FRSH as (F0 & F1 & _). rewrite Z.mod_small in Kb by (clear - F0 F1 ACV; lia). clear - Kb F0. lia. }
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [24; 8; 4; 12; 4; 12]%nat) in FRM; [| reflexivity].
    cbn [mk_CB_cells app] in FRM.
    chunk_split FRM 1%nat FHD FRM1. chunk_split FRM1 1%nat FG1 FRM2. chunk_split FRM2 1%nat FWL FRM3.
    chunk_split FRM3 1%nat FG2 FRM4. chunk_split FRM4 1%nat FLM FG3.
    lazymatch type of FWL with rw_cells _ _ ?a _ => replace a with (FB + 32) in FWL by (clear; lia) end.
    lazymatch type of FLM with rw_cells _ _ ?a _ => replace a with (FB + 48) in FLM by (clear; lia) end.
    clear FG1 FG2 FG3.
    lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -128) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
    replace (bv_unsigned sp + -128 + 32) with (bv_unsigned sp - 96) in SAVE by (clear; lia).
    release_frame FRa ST2 (bv_unsigned sp - 96).
    destruct (stk_split asegs m3 sp1 (sp1 + 32) (bv_unsigned sp - 96) ST2 ltac:(clear - SP1; lia)) as [STa SThi]. clear ST2.
    destruct (stk_carve asegs m3 sp1 (sp1 + 32) 24 STa ltac:(clear; lia)) as [STlo [jslot SLOT]].
    replace (sp1 + 32 - Z.of_nat 24) with (sp1 + 8) in STlo, SLOT by (clear; lia). clear STa.
    pose proof FRSH as (F0 & F1 & F2 & F3).
    pose proof (art_stk_high asegs R HIA) as STKH.
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (FSHLO : Z.shiftr FB 3 + al_sb AL + 8 <= lo).
    { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. change (2 ^ 44) with 17592186044416 in STKH.
      clear - F0 F1 ACV STKH LOS. Z.div_mod_to_equations. lia. }
    assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 64 HH1 INF) as CFB. rewrite Ehcs in CFB.
    assert (INH : In (FB, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
    assert (IND : In (FB + 32, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
    pose proof (hm_fresh_frame_apart asegs R HIA h1 LB LF m3 FB 64 HH1) as AP.
    assert (FSHSP : Z.shiftr FB 3 + al_sb AL + 8 <= sp1) by (clear - FSHLO SP1 SLO3 NS1; lia).
    do 35 zstep.
    norm_b8 FSH.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    assert (STF : stk asegs m9 sp1 (bv_unsigned sp - 96)).
    { pose proof (stk_of_rw_cells asegs m9 (sp1 + 8) _ SLOT) as STS.
      lazymatch type of STS with stk _ _ _ ?e => replace e with (sp1 + 32) in STS by (cbn; clear; lia) end.
      eapply stk_merge; [exact STlo| eapply stk_merge; [exact STS| exact SThi| clear - SP1; lia]| clear - SP1; lia]. }
    apply (d0_cb4 asegs m9 (sp1 + 8) [C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (FB + 48)); C4 _] _ []) in SLOT. cbn [app] in SLOT.
    chunk_split SLOT 1%nat SLOT1 YST.
    lazymatch type of YST with rw_cells _ _ ?a _ => replace a with (sp1 + 16) in YST by (clear; lia) end.
    lazymatch type of YST with rw_cells _ _ _ [?c8; C4 ?v; ?cp] =>
      apply (rw_cells_split_C4 asegs m9 (sp1 + 16) [c8] v [cp]) in YST; cbn [app] in YST end.
    lazymatch type of YST with rw_cells _ _ _ [?c8; C2 (Z_to_bv 64 ?v1); C2 (Z_to_bv 64 ?v2); ?cp] =>
      apply (rw_cells_C2_congr asegs m9 (sp1 + 16) [c8] v1 1 [C2 (Z_to_bv 64 v2); cp]) in YST;
      [| vm_compute; reflexivity]; cbn [app] in YST end.
    lazymatch type of YST with rw_cells _ _ _ [?c8; ?c2; C2 (Z_to_bv 64 ?v2); ?cp] =>
      apply (rw_cells_C2_congr asegs m9 (sp1 + 16) [c8; c2] v2 1 [cp]) in YST;
      [| vm_compute; reflexivity]; cbn [app] in YST end.
    assert (ULM : u32arr asegs m9 (FB + 48) [Z_to_bv 64 0]).
    { eapply (u32arr_of_cells asegs m9 (FB + 48) 4%nat); [| reflexivity].
      eapply rw_cells_reshape; [exact FLM| first [exact I | (vm_compute; repeat split) | (cbn; repeat split)]
                               | first [reflexivity | vm_compute; reflexivity]]. }
    apply (d0_cb4 asegs m9 (FB + 32) [] _ []) in FWL. cbn [app] in FWL.
    assert (HSSP : arl_stklo R <= bv_unsigned sp) by (clear - LOS SLO NEEDR; lia).
    assert (CRAs : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dA) 16).
    { destruct OA as (_ & _ & _ & OA4 & _). exact (client_range_sep L _ _ lo (bv_unsigned sp) (md_addr dA) 16 CRA (fun b Hb => Hb) OA4). }
    assert (CRBs : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dB) 16).
    { destruct OB as (_ & _ & _ & OB4 & _). exact (client_range_sep L _ _ lo (bv_unsigned sp) (md_addr dB) 16 CRB (fun b Hb => Hb) OB4). }
    assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) X 16) by (exact (d0_cr_w _ _ _ _ _ (proj1 XW))).
    assert (MXm : mpd_at asegs m9 LB dX) by (exact (d0_mpd_pres h LB LF (bv_unsigned sp) (arl_stklo R) m m9 dX PRES (proj1 MIm) PC MX CRXs)).
    assert (MAm : mpd_at asegs m9 LB dA) by (exact (d0_mpd_pres h LB LF (bv_unsigned sp) (arl_stklo R) m m9 dA PRES (proj1 MIm) PC MA0 CRAs)).
    assert (MBm : mpd_at asegs m9 LB dB) by (exact (d0_mpd_pres h LB LF (bv_unsigned sp) (arl_stklo R) m m9 dB PRES (proj1 MIm) PC MB0 CRBs)).
    assert (OXm : mpd_aobjA asegs AL (hcs asegs R HIA h) m9 dX).
    { destruct OXA as [OXs _]. split.
      - exact (d0_aobj_pres h LB LF (bv_unsigned sp) (arl_stklo R) m m9 X 16 PRES OXs CRXs HSSP).
      - intros E. exfalso. exact (NST E). }
    assert (OAm : mpd_aobjA asegs AL (hcs asegs R HIA h) m9 dA).
    { destruct OAA as [OAs _]. split.
      - exact (d0_aobj_pres h LB LF (bv_unsigned sp) (arl_stklo R) m m9 (md_addr dA) 16 PRES OAs CRAs HSSP).
      - intros EO. pose proof MA0 as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. cbv beta iota in OW.
        destruct OW as (_ & _ & _ & _ & RO). rewrite <- Ehcs.
        eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (IA2 EO RO)]. }
    assert (OBm : mpd_aobjA asegs AL (hcs asegs R HIA h) m9 dB).
    { destruct OBA as [OBs _]. split.
      - exact (d0_aobj_pres h LB LF (bv_unsigned sp) (arl_stklo R) m m9 (md_addr dB) 16 PRES OBs CRBs HSSP).
      - intros EO. pose proof MB0 as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. cbv beta iota in OW.
        destruct OW as (_ & _ & _ & _ & RO). rewrite <- Ehcs.
        eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (IB2 EO RO)]. }
    apply evtA_done. unfold d0_P1.
    exists FB, sp1, h1, m9.
    do 18 eexists.
    split; [reflexivity|].
    split.
    { unfold MD_BASE. split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|].
      split.
      { constructor; first [ exact NEEDR | exact HND | exact DIMG | exact ROIMG | exact HH1 | exact MXm | exact NST
                           | exact XLS | exact LOS | exact FS16 | exact SLO | exact SPA | exact FSZ | idtac ].
        - destruct XW as [XW1 XW2]. split; [| exact XW2]. rewrite Ehtop.
          eapply client_wrange_mono; [exact XW1| intros b Hb; apply fdata_cons_sub; exact Hb].
        - rewrite Ehtop. exact TOP. }
      split; [exact PRES|].
      split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|].
      split; [exact Evol|]. split; [exact Efr|]. exact HKI. }
    split; [exact FHD|].
    split; [exact FSH|].
    split; [exact FWL|].
    split.
    { split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact YST|]. split; [clear - SP1M; lia|]. split; [clear - SP1R SP1 SLO3 NS1 LOS ALO ACP; lia|].
      split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [lia|]. split; [left; reflexivity|]. split; [clear - F64; lia| exact ULM]. }
    split.
    { assert (CRY : crange (hcs asegs R HIA h) (sp1 + 16) 16)
        by (eapply crange_sub; [exact SCS| clear - SP1 SLO3 NS1; lia| clear - SP1; lia]).
      split; [exact CRY|]. intros a Ha. exists (Z_to_bv 8 0).
      pose proof CSOK as [OK1 _]. destruct (OK1 a (CRY a Ha)) as (R0 & R1 & R2 & _).
      pose proof SSH as (_ & _ & SH).
      specialize (SH (8 * (a / 8)) ltac:(clear - Ha SP1 SLO3 NS1 SLOL; Z.div_mod_to_equations; lia)
                    ltac:(clear - Ha SP1; Z.div_mod_to_equations; lia) ltac:(clear; Z.div_mod_to_equations; lia)).
      lazymatch type of SH with rw_cells _ _ (?f _ _) _ => unfold f in SH, R1, R2 |- * end.
      replace (8 * (a / 8) / 8) with (a / 8) in SH by (clear; Z.div_mod_to_equations; lia).
      pose proof (rw_cells_read asegs m9 _ [C1 (Z_to_bv 8 0)] 0 _ SH eq_refl) as RD. cbn [csize cbytes] in RD.
      replace (al_sb AL + a / 8 + Z.of_nat 0) with (al_sb AL + a / 8) in RD by (clear; lia).
      split; [apply bytes_at_of_read1; [exact R1| clear - R2; lia| exact RD]|].
      assert (E0 : bv_unsigned (Z_to_bv 8 0) = 0) by (vm_compute; reflexivity).
      left. exact E0. }
    split.
    { assert (CRL : crange (hcs asegs R HIA h) (FB + 48) 4) by (eapply crange_sub; [exact CFB| clear; lia| clear; lia]).
      split; [exact CRL|]. intros a Ha. exists (Z_to_bv 8 4).
      pose proof CSOK as [OK1 _]. destruct (OK1 a (CRL a Ha)) as (R0 & R1 & R2 & _).
      pose proof (rw_cells_read asegs m9 _ _ 6 _ FSH eq_refl) as RD. cbn [csize cbytes] in RD.
      lazymatch type of R1 with _ <= ?f _ _ => unfold f in R1, R2 |- * end.
      replace (Z.shiftr FB 3 + al_sb AL + Z.of_nat 6) with (al_sb AL + a / 8) in RD
        by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - Ha F64; Z.div_mod_to_equations; lia).
      split; [apply bytes_at_of_read1; [exact R1| clear - R2; lia| exact RD]|].
      assert (E4 : bv_unsigned (Z_to_bv 8 4) = 4) by (vm_compute; reflexivity).
      right. rewrite E4. clear - Ha F64. Z.div_mod_to_equations. lia. }
    split; [exact SAVE|].
    split; [exact PC0|].
    split; [exact STF|].
    split; [exact PC|].
    split; [exact SSH|].
    split; [exact MAm|]. split; [exact MBm|]. split; [exact OXm|]. split; [exact OAm| exact OBm].
  Qed.

  #[using="IMG UARG SM0 NS1 CMP HDIV HASN HADD JC TPV RAE UWX UWB D0 UW SLO2 SLO3 LFN C24H MB0 NRB IB2 PHId0 FRd0 BUD BUDF SXA SXB SAB NEB OA OB CRA CRAL CRB CRBL IA2 SLOS SLOL"]
  Lemma md_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      HK asegs R HIA h mo -> mpd_at asegs m LB dA -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      sshad asegs AL m slo (bv_unsigned sp) ->
      mpd_aobjA asegs AL (hcs asegs R HIA h) m dX ->
      mpd_aobjA asegs AL (hcs asegs R HIA h) m dA ->
      mpd_aobjA asegs AL (hcs asegs R HIA h) m dB ->
      aevtS asegs MD_POST_A
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB))
                        a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 A_MPI_MOD_MPI_E) fc None m (seg_rom asegs)) mo).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HK0 MA0 ST MI SSH OXA OAA OBA.
    jc_open. basic_factsA h. pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (alloc_ceiling_val R) as ACV.
    dpose OA as (OA1' & OA2' & OA3' & OA4' & OA5'). dpose OB as (OB1' & OB2' & OB3' & OB4' & OB5').
    assert (SXE : X + 16 <= md_addr dB \/ md_addr dB + 16 <= X).
    { destruct SXB as [E|D']; [exfalso; apply NEB; rewrite <- E; reflexivity| cbn [md_addr] in D'; exact D']. }
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply d0_pro; eassumption. }
    intros ms1 P1. unfold d0_P1 in P1.
    destruct P1 as (FB & sp1 & h1 & m1 & w0 & w1 & w2 & wl & padw & y0 & y1 & y2 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7
                    & y3 & y4 & y5 & y6 & -> & BASE & FHD & FSH & FLB & MY1 & OY1 & OQ1 & FR1 & STlo & STfr & MI1 & SSH1
                    & MA1 & MB1 & OXm & OAm & OBm).
    pose proof BASE as BASE'. unfold MD_BASE in BASE'.
    destruct BASE' as (SP1 & SP1M & F64 & FRSH & JC1 & PRES1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI).
    pose proof FRSH as (F0 & F1 & F2 & F3).
    pose proof JC1 as [_ _ _ _ HH1 _ _ _ _ _ _ _ _ _ _].
    destruct OXm as [OXs OXl]. destruct OAm as [OAs OAl]. destruct OBm as [OBs OBl].
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO3 NS1 LOS ALO ACP; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (FSHLO : Z.shiftr FB 3 + al_sb AL + 8 <= lo).
    { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. change (2 ^ 44) with 17592186044416 in STKH.
      clear - F0 F1 ACV STKH LOS. Z.div_mod_to_equations. lia. }
    assert (SCS : crange (hcs asegs R HIA h) lo (sp1 - lo)).
    { eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SP1 TOP HTOP; lia]. }
    assert (XJ0 : XJA asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A [] 0 0 h1 LB m1 dX).
    { eapply (xa_start asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 m1 HH1 MI1).
      - eapply stk_merge; [exact STlo| exact STfr| clear - SP1 SLO3 NS1; lia].
      - exact FR1.
      - rewrite Ehcs. exact OXs.
      - apply munch_refl.
      - apply wmono_refl. }
    assert (DBJ : JBA asegs R HIA LB ((FB, 64) :: LF) m1 dX sp lo dB).
    { constructor.
      - apply opnd_atA_mpd. exact MB1.
      - exact OB.
      - apply d0_cr_cons. exact CRB.
      - intros EO. apply d0_cr_cons. exact (CRBL EO).
      - exact SXE.
      - intros EO RO hc LBc mc0 HMc.
        eapply (AImgGlobals.aobj_img asegs AL);
          [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IB2 EO RO)]. }
    assert (BP0 : md_own dB = LHeap -> 0 < md_p dB).
    { intros EO. pose proof MB1 as [(_ & _ & _ & _ & _ & OW) _]. revert OW. rewrite EO. intros (_ & IN & _).
      destruct (hm_apart asegs R HIA h1 _ _ _ HH1) as [HF _]. rewrite Forall_forall in HF.
      destruct (HF _ (in_or_app _ _ _ (or_introl IN))) as [P0 _]. exact P0. }
    assert (BNN : 1 <= md_n dB -> md_own dB <> LNull).
    { intros N1 EO. pose proof MB1 as [(_ & _ & _ & _ & _ & OW) _]. revert OW. rewrite EO. intros [_ N0]. clear - N0 N1. lia. }
    assert (OBL1 : 1 <= md_n dB -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dB) (4 * md_n dB)).
    { intros N1. pose proof MB1 as [(_ & _ & _ & _ & _ & OW) _]. revert OW.
      destruct (md_own dB) eqn:EOB; intros OW.
      all: first [ exfalso; first [exact (BNN N1 EOB) | exact (BNN N1 eq_refl)]
                 | destruct OW as (_ & IN & _); rewrite <- Ehcs;
                   eapply (hm_aobj_block asegs R HIA h1 LB ((FB, 64) :: LF) m1); [exact HH1| exact IN]
                 | first [exact (OBl EOB) | exact (OBl eq_refl)] ]. }
    set (dY := mkMPD (sp1 + 16) 1 1 (FB + 48) [Z_to_bv 64 0] padw LHeap) in MY1.
    assert (MBy : mpd_at asegs m1 ((FB + 48, 4) :: LB) dB) by (apply d0_mpd_at_cons; exact MB1).
    assert (EVY : mpd_val dY = 0).
    { unfold mpd_val, dY. cbn [md_sg md_limbs limbs_val]. rewrite (unsigned_lit 0) by (clear; lia). reflexivity. }
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { pose proof CMP as CMPc. unfold mpi_cmp_mpi_stmtA in CMPc.
      eapply (CMPc (hcs asegs R HIA h)) with (LB := (FB + 48, 4) :: LB) (dX := dB) (dY := dY) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact MBy | exact MY1 | exact BP0 | exact MI1 | exact CSOK | exact ALWF | exact OBs | exact OY1
              | exact OBL1 | exact STlo | exact SCS
              | exact (hm_abase asegs R HIA h1 LB _ m1 HH1)
              | reflexivity
              | (intros _; exact OQ1)
              | (intros _; unfold dY; cbn [md_p]; clear - F0; lia)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO3 NS1 SP1; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (destruct OB4' as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (right; unfold dY; cbn [md_addr]; clear; lia)
              | (intros N1; destruct (OB5' (BNN N1)) as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (intros _; left; unfold dY; cbn [md_p md_n]; clear - FBLO; lia)
              | match goal with |- ?g => idtac "CMPPRE-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold mpi_cmp_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & mc & -> & MU2 & WM2 & MI2 & ST2).
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    rewrite EVY, Z.sub_0_r.
    replace (ret_pc (Z_to_bv 64 0xa05e8)) with (Z_to_bv 64 0xa05e8 : word)
      by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (HH2 : HM asegs R HIA h1 LB ((FB, 64) :: LF) mc).
    { eapply hm_munch; [exact HH1| exact MU2| exact WM2|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite Ehtop. clear - Ha LOS SP1 TOP. lia. }
    assert (WC2 : w_client (hcs asegs R HIA h) [(lo, sp1)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; exact SCS| apply Forall_nil]. }
    assert (DHD : disjoint_from [(lo, sp1)] FB (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2]))).
    { change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2])) with 24. cbn [disjoint_from]. split; [left; clear - FBLO; lia| exact I]. }
    assert (DSH : disjoint_from [(lo, sp1)] (Z.shiftr FB 3 + al_sb AL) (Z.of_nat (cells_size SHB0))).
    { change (Z.of_nat (cells_size SHB0)) with 8. cbn [disjoint_from]. split; [left; clear - FSHLO; lia| exact I]. }
    assert (DLB : disjoint_from [(lo, sp1)] (FB + 32) (Z.of_nat (cells_size [C4 wl]))).
    { change (Z.of_nat (cells_size [C4 wl])) with 4. cbn [disjoint_from]. split; [left; clear - FBLO; lia| exact I]. }
    assert (DFR : disjoint_from [(lo, sp1)] sp1 (bv_unsigned sp - 96 - sp1)).
    { cbn [disjoint_from]. split; [right; clear; lia| exact I]. }
    pose proof (rw_cells_transport asegs [(lo, sp1)] m1 mc _ _ FHD MU2 WM2 DHD) as FHDc.
    pose proof (rw_cells_transport asegs [(lo, sp1)] m1 mc _ _ FSH MU2 WM2 DSH) as FSHc.
    pose proof (rw_cells_transport asegs [(lo, sp1)] m1 mc _ _ FLB MU2 WM2 DLB) as FLBc.
    pose proof (stk_transport_disjoint asegs [(lo, sp1)] m1 mc _ _ STfr MU2 WM2 DFR) as STfrc.
    assert (STc : stk asegs mc lo (bv_unsigned sp - 96)).
    { eapply stk_merge; [exact ST2| exact STfrc| clear - SP1 SLO3 NS1; lia]. }
    pose proof (xa_scratch asegs R HIA h1 LB ((FB, 64) :: LF) m1 dX sp lo 96 MD_FRAME_A JC1 [] 0 0 h1 LB m1 dX lo sp1 mc
                  XJ0 MU2 WM2 MI2 STc HH2 (Z.le_refl lo) ltac:(clear - SP1; lia)) as XJc.
    assert (MAc : mpd_at asegs mc LB dA).
    { eapply mpd_at_munch_any; [exact MA1| exact MU2| exact WM2| cbn [disjoint_from]; split; [clear - OA4' SP1; lia| exact I]|].
      intros ON. cbn [disjoint_from]. split; [destruct (OA5' ON) as [K|K]; clear - K SP1; lia| exact I]. }
    assert (MBc : mpd_at asegs mc LB dB).
    { eapply mpd_at_munch_any; [exact MB1| exact MU2| exact WM2| cbn [disjoint_from]; split; [clear - OB4' SP1; lia| exact I]|].
      intros ON. cbn [disjoint_from]. split; [destruct (OB5' ON) as [K|K]; clear - K SP1; lia| exact I]. }
    assert (AM : forall A0 n0, aobj asegs AL (hcs asegs R HIA h) m1 A0 n0 -> aobj asegs AL (hcs asegs R HIA h) mc A0 n0).
    { intros A0 n0 HA. eapply (aobj_munch asegs AL _ CSOK); [exact WC2| exact MU2| exact HA]. }
    assert (OXc : mpd_aobjA asegs AL (hcs asegs R HIA h1) mc dX).
    { rewrite Ehcs. split; [exact (AM _ _ OXs)| intros E; exact (AM _ _ (OXl E))]. }
    assert (OAc : mpd_aobjA asegs AL (hcs asegs R HIA h1) mc dA).
    { rewrite Ehcs. split; [exact (AM _ _ OAs)| intros E; exact (AM _ _ (OAl E))]. }
    assert (OBc : mpd_aobjA asegs AL (hcs asegs R HIA h1) mc dB).
    { rewrite Ehcs. split; [exact (AM _ _ OBs)| intros E; exact (AM _ _ (OBl E))]. }
    assert (SSHc : sshad asegs AL mc slo (bv_unsigned sp)).
    { eapply sshad_munch;
        [exact CSOK| exact WC2| eapply crange_sub; [exact SCS0| clear - SLOS; lia| clear - TOP HTOP; lia]| exact MU2| exact WM2| exact SSH1]. }
    assert (CELLS : MD_CELLS mc FB SHB0).
    { unfold MD_CELLS. split; [exists w0, w1, w2; exact FHDc|]. split; [exact FSHc|]. split; [exists wl; exact FLBc| exact SSHc]. }
    assert (BJc : BJA asegs R HIA ((FB, 64) :: LF) sp dB h1 LB mc dX).
    { constructor.
      - apply opnd_atA_mpd. exact MBc.
      - exact OB2'.
      - intros EOX EN. destruct OB3' as [C|[C|[C|C]]];
          [exfalso; apply NEB; rewrite <- C; reflexivity| exfalso; exact (C EOX)| exfalso; exact (EN C)| exact C].
      - rewrite Ehcs. exact (AM _ _ OBs).
      - intros EN. pose proof MBc as [(_ & _ & _ & _ & _ & OW) _]. revert OW.
        destruct (md_own dB) eqn:EOB; intros OW.
        all: first [ exfalso; first [exact (EN EOB) | exact (EN eq_refl)]
                   | destruct OW as (_ & IN & _);
                     eapply (hm_aobj_block asegs R HIA h1 LB ((FB, 64) :: LF) mc); [exact HH2| exact IN]
                   | rewrite Ehcs; first [exact (AM _ _ (OBl EOB)) | exact (AM _ _ (OBl eq_refl))] ]. }
    apply (d0_kf h h1 mo _ _ HKI).
    eapply (md_DIV h1 m1 FB sp1 h1 mc);
      [ exact BASE | exact XJc | exact DBJ | exact BJc | exact MAc | exact OXc | exact OAc | exact OBc | exact CELLS ].
  Qed.
End WMD.

(* [comment removed for export] *)
Definition mod_mpi_PHIg (PHIf : mpd -> mpd -> mpd -> Z) (dX dA dB : mpd) : Z := PHIf dX dA dB + (32 * md_n dB + 48).
Definition mod_mpi_FRg (FRf : mpd -> mpd -> mpd -> Z -> Z) (dX dA dB : mpd) (d : Z) : Z := FRf dX dA dB (d + 1) + add_sub_FR (d + 1).

(* [comment removed for export] *)
Theorem A_mpi_mod_mpi_spec_g : forall (R : art_layout) (HIA : artA asegs R) (PHIf : mpd -> mpd -> mpd -> Z)
    (FRf : mpd -> mpd -> mpd -> Z -> Z),
    asan_img_ok (arl_AL R) ->
    arl_uar_got R = A_UAR_GOT_MD ->
    arl_smalloc R 0 = A_SMALLOC_0_MD ->
    0 <= arl_need_smalloc R ->
    mpi_div_mpi_stmtA asegs R HIA A_MPI_DIV_MPI_E PHIf FRf ->
    (forall dX dA dB : mpd, 0 <= md_n dA <= MPI_MAX_LIMBS -> 0 <= md_n dB <= MPI_MAX_LIMBS -> 0 <= PHIf dX dA dB) ->
    (forall (dX dA dB : mpd) (d : Z), 0 <= md_n dA <= MPI_MAX_LIMBS -> 0 <= d -> 0 <= FRf dX dA dB d) ->
    (forall flip : Z, flip = 1 \/ flip = -1 -> add_sub_mpi_ng_stmtA_oz flip asegs R HIA A_ADD_SUB_MPI) ->
    add_sub_mpi_stmtA_osz 1 asegs R HIA A_ADD_SUB_MPI ->
    0 <= arl_need_rt R ->
    (forall (h : HST asegs R HIA) (LB LF : list blk) (m : mem), HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
    hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
    (forall a : Z, ro_addr asegs (wa a) = true -> 0 <= a < 2 ^ 64 -> hl_img_lo (arl_L R) <= a < hl_img_hi (arl_L R)) ->
    mpi_mod_mpi_stmtA asegs R HIA A_MPI_MOD_MPI_E (mod_mpi_PHIg PHIf) (mod_mpi_FRg FRf).
(* [comment removed for export] *)
Proof.
  intros R HIA PHIf FRf IMG UARG SM0 NS1 HDIV PHI0 FR0 HASN HADD NEEDR HND DIMG ROIMG.
  unfold mpi_mod_mpi_stmtA, mod_mpi_PHIg, mod_mpi_FRg.
  intros until d. intros HH HK LFN MX MA MB SXA SXB SAB NST NEB OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO SLO3 SSH SLOS SLOL
    TOP SPA TPV MI RAE OXA OAA OBA IA2 IB2 BUD UW UWX UWB BUDF C24H -> -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 96
                 (MD_FRAME_A ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR; lia. }
  pose proof MA as [(_ & _ & _ & _ & NRA & _) _]. pose proof MB as [(_ & _ & _ & _ & NRB & _) _].
  unfold MPI_MAX_LIMBS in NRA, NRB.
  pose proof (uw_obj_nonneg _ _ _ _ UWX) as D0.
  pose proof (A_mpi_cmp_mpi_spec (arl_AL R) IMG) as CMP.
  eapply md_main with (slo := slo) (d := d); try eassumption.
  all: try (apply PHI0; assumption). all: try (apply FR0; [assumption| clear - D0; lia]).
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
(* [comment removed for export] *)
