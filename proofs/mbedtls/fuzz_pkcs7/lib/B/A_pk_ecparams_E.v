(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_ecp_point_free P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_ecp_grp_id_list P_ecp_mul_mod P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_defs A_pk_defs A_mpi_free A_mpi_lset A_mpi_bitlen A_mpi_cmp_mpi A_asn1_get_tag_stmt A_asn1_get_int_loops A_asn1_get_mpi A_oid A_oid_ec_grp A_ecp_group_init A_ecp_group_free A_ecp_point_free A_ecp_grp_id_list A_pk_ecparams_aux A_free_seq A_pk_ecc_set_group A_pk_ecc_set_pubkey A_ecp_grp_facts A_pk_tmp A_pk_ecparams_stmt A_pk_ecparams_A A_pk_ecparams_B A_pk_ecparams_C A_mpi_read_binary_stmt_c24 A_asn1_get_mpi_c24 A_pk_ecparams_D1 A_pk_ecparams_D2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_pk_ecparams_E () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_B.EB"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_init"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_D1.EP_SH_P"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_use_ecparams_postA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_int_loops.A_ASN1_GET_INT"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_D1.SPINV"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_D1.TAILV"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_FR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_D1.TAILF"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_FR"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "WalkEP.Call.GI_stmt"; "WalkEP.Call.F1C_stmt"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_A.EP_SH0"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_FR"; "WalkEP.Call.NAMED_stmt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_A.A_UAR_GOT_EP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_A.A_SMALLOC_4_EP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_setf5"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_setsh"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memcmp_i"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_ecc_set_group_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_pk_defs.A_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.A_PK_ECC_SET_GROUP"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_point_free.ecp_point_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_point_free.A_ECP_POINT_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.ecp_group_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.A_ECP_GROUP_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_group_load_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_GROUP_LOAD_E"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_init.ecp_group_init_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_init.A_ECP_GROUP_INIT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_id_list.ecp_grp_id_list_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_id_list.A_ECP_GRP_ID_LIST"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt_c24.mpi_read_binary_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_mpi_c24.asn1_get_mpi_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_mpi.A_ASN1_GET_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset.mpi_lset_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_tag_stmt.asn1_get_tag_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_tag_stmt.A_ASN1_GET_TAG"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_lookup1v_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_oid_ec_grp.A_OID_GET_EC_GRP"; "RocqVerifyHarness.AgentSubmission.B.A_oid_ec_grp.OID_EC_GRP_VALS"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_int_loops.asn1_get_int_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_use_ecparams_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.A_PK_USE_ECPARAMS"].



(* [comment removed for export] *)
Lemma aevtA_KF_switch : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "PR,$0.PHIA,(1.$2.R1.)Pha,(3.$2.R2.R1.)Phb,(3.$2.R3.R2.)Pmo0,$4.PQ,P,$5.SpPms,$6.P,Pmo,$4.(7.(8.$2.R8.R7.R5.R1.)(8.$2.R8.R7.R6.R1.))P,(9.$2.(:.$2.R8.R7.R5.R4.)R3.R2.)(9.$2.(:.$2.R9.R8.R7.R5.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros R HIA ha hb mo0 Q ms HKI H mo [K1 K2]. apply H. split; [apply (proj2 (HKI mo)); exact K1| exact K2]. Qed.


(* [comment removed for export] *)
Section WalkEP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variables (IDONE IDS : Z).
  Hypothesis IDOK : ids_okA R IDONE IDS.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PKA PAR lo d : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 640 - arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis HH0 : HM asegs R HIA h LB LF m.
  Hypothesis MI0 : mem_inv asegs m.
  (* [comment removed for export] *)
  Variables (FB sp1 : Z).
  Hypothesis SP1 : bv_unsigned sp - 272 <= sp1 <= bv_unsigned sp - 256.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 1024.

  Local Notation LF' := ((FB, 1024) :: LF).
  Local Notation SHB := (Z.shiftr FB 3 + al_sb AL).
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation W0 := [(IDONE, IDONE + 1); (IDS, IDS + 56)].

  Ltac rt_facts :=
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
  (* [comment removed for export] *)
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis LFB : (length LF + 1 < 512)%nat.
  Hypothesis SF5 : arl_setf5 R = 0x6b330.
  Hypothesis NSH : arl_need_setsh R <= arl_need_rt R.
  Variables (info C LEN : Z) (idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ : word).
  Local Notation KPI := (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Hypothesis HPKA0 : rw_cells asegs m PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)].
  Hypothesis CRP : client_range L (LB ++ fdata LF) lo PKA 16.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis DPI : PKA + 16 <= IDONE \/ IDS + 56 <= PKA.
  Hypothesis DPC : PKA + 16 <= C \/ C + 256 <= PKA.
  Hypothesis KP0 : ecp_keypair_at asegs A_MT m LB C KPI.
  Hypothesis INC : In (C, 256) LB.

  Local Notation WF := [(C, C + 192); (IDONE, IDONE + 1); (IDS, IDS + 56)].
  Local Notation POST := (pk_use_ecparams_postA asegs R HIA A_MT A_CA A_ONE IDONE IDS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF PKA info C KPI LEN lo d m mo0).


  Hypothesis CFB : crange CS FB 1024.
  Hypothesis HSG : pk_ecc_set_group_stmtA asegs R HIA A_MT A_CA A_ONE A_EC_INFOS A_PK_ECC_SET_GROUP.
  Hypothesis EI : In info A_EC_INFOS.
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis NZP : 0 < PKA.
  Hypothesis OPKA0 : aobj asegs AL CS m PKA 16.
  Hypothesis BUD : havol asegs R HIA h + pk_ecparams_PHI LEN <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + pk_ecparams_FR d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_PK_USE_ECPARAMS <= C24MAX.
  Hypothesis MFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Hypothesis D0 : 0 <= d.
  Local Notation G := (FB + 368).
  Hypothesis PFREE : ecp_point_free_stmtA asegs R HIA A_ECP_POINT_FREE.

  Ltac eb_open EBk :=
    destruct EBk as (HHk & (ETk & ESk & EFk) & HCSk & (HVk & HFk) & (w0 & w1 & w2 & FHD) & (FSH & NSH') & FSHR & SAVE & (SLOTS & NSL) & STlo & SThi & STb & MIk & PRES & IDSk & CHk & EXTk & FRk).

  Hypothesis HGF : ecp_group_free_stmtA asegs R HIA A_MT A_ECP_GROUP_FREE.
  Hypothesis HGL : ecp_group_load_stmtA asegs R HIA A_MT A_CA A_ONE A_ECP_GROUP_LOAD_E.
  Hypothesis IDSN : AImgGlobals.img_norz IDS 56 = true.
  Hypothesis HGI : ecp_group_init_stmtA asegs R HIA A_MT A_ECP_GROUP_INIT.
  Hypothesis HIDL : ecp_grp_id_list_stmtA asegs AL A_ECP_GRP_ID_LIST IDONE IDS.
  Local Notation REF := (FB + 32).
  Local Notation DS7 dN dP dA dB dX dY dZ := ([dN; dP; dA; dB; dX; dY; dZ] : list mpd) (only parsing).

  (* [comment removed for export] *)
  Variables (P : Z) (tg pd : word) (bs : list byte).
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis PR0 : 0 <= P.
  Hypothesis PNZ : (P = 0 /\ LEN = 0) \/ 0 < P.
  Hypothesis P47 : P + LEN + 8 <= 2^47.
  Hypothesis HPAR0 : rw_cells asegs m PAR (buf_cells tg pd LEN P).
  Hypothesis ALPAR : PAR mod 8 = 0.
  Hypothesis NZPAR : 0 < PAR.
  Hypothesis OPAR0 : aobj asegs AL CS m PAR 24.
  Hypothesis CRPAR : client_range L (LB ++ fdata LF) lo PAR 24.
  Hypothesis DSPAR : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DPARI : PAR + 24 <= IDONE \/ IDS + 56 <= PAR.
  Hypothesis IDS0 : ecp_ids_state asegs IDONE IDS m.
  Local Notation PEND := (P + LEN).
  Hypothesis HRB : mpi_read_binary_stmtA_c asegs R HIA A_MPI_READ_BINARY.
  Hypothesis HGM : asn1_get_mpi_stmtA_c asegs R HIA A_ASN1_GET_MPI A_MPI_READ_BINARY.
  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis UWC0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis HGT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis MCI : arl_memcmp_i R = 0x58704.
  Hypothesis SLOB : lo <= bv_unsigned sp - 336 - arl_need_bcmp R.
  Hypothesis NEEDB : 0 <= arl_need_bcmp R.
  Hypothesis HOG : oid_lookup1v_stmtA asegs R HIA A_OID_GET_EC_GRP 64 OID_EC_GRP_VALS.
  Hypothesis HGINT : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.
  Variable slo : Z.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLOK : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Local Notation EB := (A_pk_ecparams_B.EB R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1).
  Local Notation wx_fresh := (A_pk_ecparams_B.wx_fresh R LB LF FB).
  Local Notation presA_drop_wx := (A_pk_ecparams_B.presA_drop_wx R LB LF FB FRSH).
  Local Notation eb_frame_facts := (A_pk_ecparams_B.eb_frame_facts R HIA IMG NEEDR h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation eb_pres_step := (A_pk_ecparams_B.eb_pres_step R HIA IMG NEEDR h LB LF sp m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation ids_fresh_dj := (A_pk_ecparams_B.ids_fresh_dj R HIA IMG NEEDR h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation ids_presA_gen := (A_pk_ecparams_B.ids_presA_gen R IDONE IDS IDOK).
  Local Notation eb_step := (A_pk_ecparams_B.eb_step R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation ids_munch_sh := (A_pk_ecparams_B.ids_munch_sh R IDONE IDS IDOK FB).
  Local Notation ch_munch_sh := (A_pk_ecparams_B.ch_munch_sh R FB).
  Local Notation kp_block_facts := (A_pk_ecparams_B.kp_block_facts R HIA h LB LF m HH0 C INC).
  Local Notation ecp_group_at_relist := (A_pk_ecparams_B.ecp_group_at_relist R DIMG IDONE IDS sp PKA lo sp1 SP1 C DSP DPI DPC).
  Local Notation kp_presA := (A_pk_ecparams_B.kp_presA R DIMG IDONE IDS LF sp PKA lo sp1 SP1 C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ DSP DPI DPC).
  Local Notation ep_exit := (A_pk_ecparams_B.ep_exit R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP HH0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC INC CFB).
  Local Notation eb_entry_objs := (A_pk_ecparams_B.eb_entry_objs R HIA IMG NEEDR DIMG IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PKA lo LOS SLO HH0 MI0 FB sp1 SP1 F64 FRSH info C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC OPKA0).
  Local Notation ep_setgrp := (A_pk_ecparams_B.ep_setgrp R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H).
  Local Notation sh_aobj := (A_pk_ecparams_B.sh_aobj R HIA IMG NEEDR h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation eb_blk_apart := (A_pk_ecparams_B.eb_blk_apart R HIA LF FB).
  Local Notation eb_free1 := (A_pk_ecparams_B.eb_free1 R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF MFREE).
  Local Notation lb_ext_frees := (A_pk_ecparams_B.lb_ext_frees LB).
  Local Notation eb_pfree := (A_pk_ecparams_B.eb_pfree R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF PFREE).
  Local Notation ep_cleanup := (A_pk_ecparams_B.ep_cleanup R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE).
  Local Notation eb_scratch := (A_pk_ecparams_C.eb_scratch R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).
  Local Notation SLL := (A_pk_ecparams_C.SLL PKA FB).
  Local Notation LINV := (A_pk_ecparams_C.LINV R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PKA lo FB sp1).
  Local Notation idsb_presA := (A_pk_ecparams_C.idsb_presA R IDONE IDS IDOK).
  Local Notation ref_aobj := (A_pk_ecparams_C.ref_aobj R HIA IMG NEEDR IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation linv_gfree := (A_pk_ecparams_C.linv_gfree R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF HGF).
  Local Notation linv_gload := (A_pk_ecparams_C.linv_gload R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF C24H HGL).
  Local Notation own_iv := (A_pk_ecparams_C.own_iv R sp lo FB).
  Local Notation shb_eq := (A_pk_ecparams_C.shb_eq R FB).
  Local Notation own_iv_blk := (A_pk_ecparams_C.own_iv_blk R HIA LF sp lo LOS FB).
  Local Notation own_iv_data := (A_pk_ecparams_C.own_iv_data R HIA IMG NEEDR h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation own_iv_ids := (A_pk_ecparams_C.own_iv_ids R HIA IMG NEEDR IDONE IDS IDOK h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation ids_state_own := (A_pk_ecparams_C.ids_state_own R HIA IMG NEEDR IDONE IDS IDOK h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation tmp_ok_own := (A_pk_ecparams_C.tmp_ok_own R HIA LF sp lo LOS FB).
  Local Notation grp_at_own := (A_pk_ecparams_C.grp_at_own R HIA LF sp lo LOS FB).
  Local Notation ids_bytes_at := (A_pk_ecparams_C.ids_bytes_at IDS).
  Local Notation ids_aobj := (A_pk_ecparams_C.ids_aobj R HIA IMG IDS IDSN).
  Local Notation id_tail_fin := (A_pk_ecparams_C.id_tail_fin R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE).
  Local Notation id_tail := (A_pk_ecparams_C.id_tail R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF IDSN).
  Local Notation mpd_qpre := (A_pk_ecparams_C.mpd_qpre R HIA IMG NEEDR h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation linv_scratch := (A_pk_ecparams_C.linv_scratch R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PKA lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).
  Local Notation grp_mpd_at := (A_pk_ecparams_C.grp_mpd_at LF sp PKA FB sp1 LFB NZP).
  Local Notation grp_aobj := (A_pk_ecparams_C.grp_aobj R HIA IMG NEEDR IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation linv_opnd := (A_pk_ecparams_C.linv_opnd R HIA IMG NEEDR IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PKA lo LOS SLO FB sp1 SP1 F64 FRSH LFB NZP).
  Local Notation linv_cmp := (A_pk_ecparams_C.linv_cmp R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP HH0 FB sp1 SP1 SP1M F64 FRSH LFB info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ NZP).
  Local Notation linv_getbit := (A_pk_ecparams_C.linv_getbit R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP HH0 FB sp1 SP1 SP1M F64 FRSH LFB info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ NZP).
  Local Notation LST := (A_pk_ecparams_C.LST R IDS sp gp tp F fc FB sp1).
  Local Notation linv_slots := (A_pk_ecparams_C.linv_slots R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PKA lo FB sp1).
  Local Notation cmp_chain := (A_pk_ecparams_C.cmp_chain R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF IDSN).
  Local Notation iter_head := (A_pk_ecparams_C.iter_head R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF HGL IDSN).
  Local Notation linv_hids := (A_pk_ecparams_C.linv_hids R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PKA lo FB sp1).
  Local Notation loop_walk := (A_pk_ecparams_C.loop_walk R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF HGL IDSN).
  Local Notation eb_ch_incl := (A_pk_ecparams_C.eb_ch_incl R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1).
  Local Notation eb_step_ids := (A_pk_ecparams_C.eb_step_ids R HIA IMG NEEDR IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation eb_munch2 := (A_pk_ecparams_C.eb_munch2 R HIA IMG NEEDR DIMG IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PKA lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH C DSP DPI DPC).
  Local Notation data_iv := (A_pk_ecparams_C.data_iv R).
  Local Notation data_iv_blk := (A_pk_ecparams_C.data_iv_blk R HIA DIMG LF FB).
  Local Notation data_iv_frame := (A_pk_ecparams_C.data_iv_frame R HIA IMG NEEDR h LB LF sp lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation eb_ids_munch := (A_pk_ecparams_C.eb_ids_munch R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation idsearch_walk := (A_pk_ecparams_C.idsearch_walk R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF HGL IDSN HGI HIDL).
  Local Notation eb_ch_add := (A_pk_ecparams_D1.eb_ch_add R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1).
  Local Notation eb_ch_get := (A_pk_ecparams_D1.eb_ch_get R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1).
  Local Notation eb_munchF := (A_pk_ecparams_D1.eb_munchF R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).
  Local Notation sp_mpi_step := (A_pk_ecparams_D1.sp_mpi_step R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation SLP := (A_pk_ecparams_D1.SLP FB).
  Local Notation SPINV := (A_pk_ecparams_D1.SPINV R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1 LEN P).
  Local Notation SPINVx := (A_pk_ecparams_D1.SPINVx R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1 LEN P).
  Local Notation sp_err := (A_pk_ecparams_D1.sp_err R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE P bs).
  Local Notation sp_err94c := (A_pk_ecparams_D1.sp_err94c R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE P bs).
  Local Notation sp_err948 := (A_pk_ecparams_D1.sp_err948 R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE P bs).
  Local Notation swrap32_errsum_ep := (A_pk_ecparams_D1.swrap32_errsum_ep LF sp PKA FB sp1 LFB NZP bs).
  Local Notation sp_erradd := (A_pk_ecparams_D1.sp_erradd R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE P bs).
  Local Notation sp_errbac := (A_pk_ecparams_D1.sp_errbac R HIA IMG NEEDR DIMG HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 MI0 FB sp1 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE P bs).
  Local Notation eb_budget_mono := (A_pk_ecparams_D1.eb_budget_mono R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1).
  Local Notation tmp_upd7 := (A_pk_ecparams_D1.tmp_upd7 FB).
  Local Notation sh_zero_aobj := (A_pk_ecparams_D1.sh_zero_aobj R HIA IMG NEEDR IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation tmp_member := (A_pk_ecparams_D1.tmp_member R HIA IMG NEEDR IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation eb_uwc := (A_pk_ecparams_D1.eb_uwc R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo d LOS SLO SPA HH0 FB sp1 SP1 F64 FRSH C INC D0 UWC0).
  Local Notation sp_lset := (A_pk_ecparams_D1.sp_lset R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ INC BUD BUDF D0 HLSET UWC0).
  Local Notation sp_query := (A_pk_ecparams_D1.sp_query R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP HH0 FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Local Notation eb_own := (A_pk_ecparams_D1.eb_own R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).
  Local Notation tail_nonneg := (A_pk_ecparams_D1.tail_nonneg LEN LEN0).
  Local Notation eb_slots := (A_pk_ecparams_D1.eb_slots R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38973937698.5L50790761713.800000H00cS5IDONE3IDS3PAR5DPARI2I2S1R5NEEDR2sp2lo3LOS3SLO3NER". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO SP1 F64 FRSH HPAR0 OPAR0 CRPAR DSPAR DPARI"] Lemma eb_par : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "Phk,(3.$2.VR,VHIA,)PLBk,(;.$<.)Pmk,P,(=.&40.)(>.(=.&8.))Pv,$?.Pf,$?.PSH,(;.$10.)PSL,(;.$10.)PCH,(;.(11.$?.(;.$10.)))PT,(;.$<.)P,(12.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R9.R8.R7.R6.R5.R4.R3.R2.R1.(13.(11.$?.$?.)(14.$?.$?.VIDONE,(15.VIDONE,+1.))(13.(11.$?.$?.)(14.$?.$?.VIDS,(15.VIDS,+38.))(16.(11.$?.$?.)))))(17.(18.$2.R8.VPAR,(19.Vtg,Vpd,VLEN,VP,))(1:.$2.(1;.VR,)(1<.$2.VR,VHIA,R:.)R8.VPAR,+18.))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T EBk.
    ddestruct EBk as (HHk & (ETk & ESk & EFk) & HCSk & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIk & PRES & _ & _ & EXTk & _).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & _).
    ddestruct IDOK as (I1 & I2 & I3 & I4 & _).
    pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES) as HP.
    assert (CRPs : client_range L (LB ++ fdata LF) (bv_unsigned sp) PAR 24) by (eapply client_range_sep; [exact CRPAR| intros b Hb; exact Hb| exact DSPAR]).
    split. { eapply (presA_rw_cells asegs R _ _ _ _ _ _ m mk _ _ HP); [exact HPAR0| exact CRPs|].
             cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from buf_cells]. clear - DPARI I2. lia. }
    eapply aobj_cs_mono; [exact HCSk|].
    eapply (presA_aobj asegs R CS); [exact (hcs_ok asegs R HIA h)| exact HP| exact OPAR0| exact CRPs| clear - ALO LOS SLO NEEDR NER; lia| intros x Hx; rewrite ESk; eapply hcs_below_top; exact Hx].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L39076636629.0L55588686165.0L59314923118.1000001002005SSS1K". (* [comment removed for export] *)
  #[using="R HIA LB LF lo LOS FRSH CRPAR"] Lemma par_frame_apart : FB + 1024 <= PAR \/ PAR + 24 <= FB.
  Proof.
    destruct (frame_apart_obj0 R HIA LB LF lo PAR 24 FB 1024 FRSH CRPAR ltac:(clear; lia) ltac:(clear; lia) LOS) as [K|K]; [exfalso; clear - K; lia| exact K].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation aobj_sshad8 := (A_pk_ecparams_D1.aobj_sshad8 R).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0190@L10263310472.150L10449096553.148L14326362217.148L14420151913.148L15582884347.150L16031071368.150L17134108071.147L17447735401.148L18452158856.150L19136903363.150L21001741673.148L21520683369.148L21534729321.148L21929715305.148L22695630843.150L24955463785.148L25055282793.148L25076785769.148L25486355305.148L28509486441.148L28631332713.148L29042474089.148L29467976359.147L30972888743.147L32095684232.150L3336350057.148 L3362051433.148 L37303663811.150L3771619945.148 L38081820583.147L38184114599.147L39158276457.148L39595119209.148L39697293417.148L42716492393.148L43151746921.148L43247742569.148L43253937513.148L44410100419.150L44789732263.147L45534329480.150L46273120105.148L46666021225.148L47205300329.148L50326411369.148L50362582121.148L50763500905.148L51892492168.150L53780864873.148L53880679785.148L54567107904.152L57670472584.150L57768173161.148L59245064127.147L59308579027.149L59308579027.150L59308579027.152L59308579281.148L59310679309.148L59314873579.149L59314873579.150L61326893929.148L62572929787.150L64883012713.148L64983351913.148L65696688295.147L66131146235.150L6780316777.148 L67991802985.148L68387051113.148L68539471721.148L6892993129.148 L8807456703.147 00000Q00m01I01e02G02h03D03`04A04b05>05Z06606R07407P07l08H08d09@09\0:80:T0;00;Q0;m0<I0<j0=F0=b0>>0>Z0?60?R0?n0@J0@f0AB0Ac0B?0B`0C<0CX0D40DP0Dl0EH0Ei0FE0Fa0GH0Gi0HE0Ha0I@0I_0J@0J^0K>0K\0L:0LV0M80MT0N00NL0Nn0OJ0Of0PB0P^0Q:0QVS2LF2sp3PKA3PAR2FB3sp13LFB1A2d11HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d22H0S2LF2sp3PKA3PAR2FB3sp13LFB1A2d11HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d11HS2LF2sp3PKA3PAR2FB3sp13LFB1A2d21HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d22H0S2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d11HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d21HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d21HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d11HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d11HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d12d21H2H0S2LF2sp3PKA3PAR2FB3sp13LFB1A2d11HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2H0S2LF2sp3PKA3PAR2FB3sp13LFB1A2H0S2LF2sp3PKA3PAR2FB3sp13LFB1A1H2H0S2LF2sp3PKA3PAR2FB3sp13LFB1A1ES2LF2sp3PKA3PAR2FB3sp13LFB1A3HInS2LF2sp3PKA3PAR2FB3sp13LFB1A1HS2LF2sp3PKA3PAR2FB3sp13LFB1A1HS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d22H0S2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A2d22H0S2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1AS2LF2sp3PKA3PAR2FB3sp13LFB1A". (* [comment removed for export] *)
  #[using="LF sp PKA PAR FB sp1 LFB"] Lemma tmp_ok_init7A : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "Pmm,P,(=.&40.)(>.(=.&8.))PLBi,(;.$<.)PA,$?.Pidp,(=.&40.)PqP,(=.&40.)PqA,(=.&40.)PqB,(=.&40.)PqX,(=.&40.)PqY,(=.&40.)PqZ,(=.&40.)PqN,(=.&40.)Php,(=.&40.)P,(1=.$2.$1>.R<.R;.R:.(1?.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(17.(20.$2.R=.R<.R;.+<0.(13.$21.(22.(15.R;.+68.)R3.)(13.$21.(22.(15.R;.+8.)R9.)(13.$21.(22.(15.R;.+18.)R8.)(13.$21.(22.(15.R;.+28.)R7.)(13.$21.(22.(15.R;.+38.)R6.)(13.$21.(22.(15.R;.+48.)R5.)(13.$21.(22.(15.R;.+58.)R4.)(16.$21.)))))))))(18.$2.R=.(15.R;.+78.)(13.$10.(23.(24.&40.=))(13.$10.(23.(24.&40.=))(16.$10.)))))")
(* [comment removed for export] *).
  Proof.
    intros until hp. intros HG.
    dpose HG as (HD & ALx & POS & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & TL & _).
    cbn [grp_init g_P g_A g_B g_G g_N pt_init pt_X pt_Y pt_Z grp_head_cells grp_tail_cells g_id g_idpad g_pbits g_nbits g_h g_hpad g_modp g_tpre g_tpost g_tdata g_T g_Tsize] in HD, MP, MA, MB, MX, MY, MZ, MN, TL.
    replace (A + 56 + 16) with (A + 72) in MY by lia. replace (A + 56 + 32) with (A + 88) in MZ by lia.
    split.
    - split. { repeat apply Forall_cons; try apply Forall_nil; (split; [assumption| cbn; left; reflexivity]). }
      split. { repeat apply Forall_cons; try apply Forall_nil; cbn; (split; [discriminate| lia]). }
      split. { intros d1 d2 H1 H2 E. cbn in H1, H2. decompose [or] H1; decompose [or] H2; subst; try reflexivity; cbn in E; exfalso; lia. }
      split. { intros d1 d2 H1 H2 NE. cbn in H1, H2. decompose [or] H1; decompose [or] H2; subst; try (exfalso; apply NE; reflexivity); cbn; lia. }
      split. { intros d1 d2 H1 H2 _ O1 _. exfalso. cbn in H1. decompose [or] H1; subst; cbn in O1; first [discriminate O1| contradiction]. }
      cbn [map md_addr mpd_init]. repeat (constructor; [cbn; intros HIn; decompose [or] HIn; lia|]). constructor.
    - chunk_split TL 2%nat TL1 TL2. exact TL1.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Definition GI_stmt (Wok : Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "Phk,(3.$2.VR,VHIA,)PLBk,(;.$<.)Pmk,P,(=.&40.)(>.(=.&8.))Pv,$?.Pf,$?.PSL,(;.$10.)PCHr,(;.(11.$?.(;.$10.)))Pds,(;.$21.)Pvw,(=.&40.)Pvw',(=.&40.)PRET,$?.Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pxs0,(=.&40.)Pxs1,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pxs2,(=.&40.)Pxs3,(=.&40.)Pxs4,(=.&40.)Pxs5,(=.&40.)Pxs6,(=.&40.)Pxs7,(=.&40.)Pxs8,(=.&40.)Pxs9,(=.&40.)Pxs10,(=.&40.)Pxs11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)P,(12.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R23.R22.R21.R20.R1?.$25.R1>.(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+120.)(13.$10.(23.(24.&40.VP,))(16.$10.)))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+160.)(13.$10.(26.R1;.)(13.$10.(26.R1:.)(16.$10.))))R1=.))(27.R1<.)(13.(11.$?.$?.)(14.$?.$?.VIDONE,(15.VIDONE,+1.))(13.(11.$?.$?.)(14.$?.$?.VIDS,(15.VIDS,+38.))(16.(11.$?.$?.)))))P,(20.$2.R22.R23.(15.VFB,+170.)+<0.R1=.)P,(28.(11.$?.(;.$10.))Lac,(11.$?.(;.$10.))(29.(13.(11.$?.$?.)(14.$?.$?.(15.VFB,+120.)(15.(15.VFB,+120.)+8.))(13.(11.$?.$?.)(14.$?.$?.(15.VFB,+160.)(15.(15.VFB,+160.)+4.))(16.(11.$?.$?.))))(2:.$?.(;.$10.)R1.)(2;.(2<.(2=.$?.(;.$10.)R1.))))R1?.)P,(17.(2>.=R1<.)(2?.R1<.(30.+2.+40.)))P,(31.$?.(32.R1=.+2.)=)P,Pm2,P,(=.&40.)(>.(=.&8.))Pr,$?.Pp',$?.Pvw2,(=.&40.)Py0,(=.&40.)Py1,(=.&40.)Py2,(=.&40.)Py4,(=.&40.)Py5,(=.&40.)Py6,(=.&40.)Py7,(=.&40.)Py8,(=.&40.)Py9,(=.&40.)Py10,(=.&40.)Py11,(=.&40.)Py12,(=.&40.)Py13,(=.&40.)Py14,(=.&40.)P,(12.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R3:.R39.R12.R37.R36.$25.R35.(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+120.)(13.$10.(23.(24.&40.R10.))(16.$10.)))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+160.)(13.$10.(26.R?.)(13.$10.(26.R31.)(16.$10.))))R34.))(27.R33.)(13.(11.$?.$?.)(14.$?.$?.VIDONE,(15.VIDONE,+1.))(13.(11.$?.$?.)(14.$?.$?.VIDS,(15.VIDS,+38.))(16.(11.$?.$?.)))))P,(20.$2.R13.R3:.(15.VFB,+170.)+<0.R34.)P,(17.(2>.VP,R12.)(2>.R12.(15.VP,VLEN,)))P,(17.(2?.-7?.R14.)(2>.R14.=))P,P,(31.$?.R15.=)O1.(9.$2.(:.$2.VR,VHIA,R3?.Vmo0,)(33.$2.VR,VHIA,$1>.$34.$35.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(36.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(37.(38.(24.&40.R35.)(24.&40.Vsp1,)Vgp,Vtp,R13.R12.R11.R31.R30.(24.&40.R16.)R10.R?.R>.R=.R<.R;.R:.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R9.R8.R7.R6.)VF,(24.&40.R35.)Vfc,(39.(=.&40.))R17.(3:.$2.)))(9.$2.(:.$2.VR,VHIA,R29.Vmo0,)(33.$2.VR,VHIA,$1>.$34.$35.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(36.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(37.(38.(24.&40.R1?.)(24.&40.Vsp1,)Vgp,Vtp,R1>.R1=.R1<.R1;.R1:.(24.&40.(15.VFB,+120.))(24.&40.(15.VP,VLEN,))(24.&40.(15.VFB,+160.))R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(24.&40.$3;.)Vfc,(39.(=.&40.))R27.(3:.$2.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition F1C_stmt (Wok : Prop) : Prop :=
    forall (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (v f : Z) (dN dP dA dB dX dY dZ : mpd)
      (p : Z) (lnw vw vw' : word) (jref : list byte) (gid gj' pb nb : word) (v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 v16 v17 v18 : word) (K : Z)
      (xra t0 t1 t2 a0v a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 s10v : word),
    Wok ->
    SPINVx hk LBk mk v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 (Z_to_bv 64 PKA) v16 v17 v18 K ->
    K <= 0 -> md_own dX = LNull -> md_n dY <= 1 -> md_n dZ <= 1 ->
    v + 5 * MPI_RB_PHI LEN + 2 * grow_PHI 1 + TAILV <= pk_ecparams_PHI LEN ->
    f + 5 * MPI_RB_FR 0 + 6 + TAILF <= pk_ecparams_FR d ->
    aevtA asegs (KF asegs R HIA hk mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1 (Z_to_bv 64 (FB + 472)) a3 a4 a5 a6 a7 (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 288))
              (Z_to_bv 64 SHB) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (P + LEN)) (Z_to_bv 64 (FB + 352)) (Z_to_bv 64 (FB + 424)) (Z_to_bv 64 FB) s10v (Z_to_bv 64 (FB + 368)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xb1100) fc None mk (seg_rom asegs))
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308586248.2000006S1i2Hi". (* [comment removed for export] *)
  #[using="Type"] Lemma shg_grp : sh_zero EP_SH_G 46 24.
  Proof. intros i Hi. unfold EP_SH_G. do 24 (destruct i as [|i]; [reflexivity|]). exfalso. clear - Hi. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "07;0@C53807985733.263C53807985733.264C53807985733.298C53807985733.299D16670306730.297D17209380499.297D40016287967.297D46719952988.233D46719952988.234D46719952988.308D46719952988.309D50014262098.233D50014262098.234D50014262098.308D50014262098.309K19557566604.297L10256253743.1  L10383309542.1  L10739142159.2  L11524609299.5  L11666505806.284L11668947521.285L12469921329.0  L14352777733.296L14906048793.285L15045194536.296L15255282835.5  L1562719048.295 L15640438675.5  L1573061349.335 L1685717371.0   L16908924412.297L1788239501.1   L1818808183.3   L1824826089.1   L18994852257.0  L1952302030.335 L19553424250.2  L19561236329.1  L1958474339.295 L19661941075.5  L19767991565.1  L1986124813.1   L19980016842.7  L21444186492.224L21866712442.1  L21868500043.2  L22941438733.1  L24023900370.0  L24151807088.297L25874234871.1  L27731725267.5  L28432818399.285L28948604668.297L29010569984.301L29022582655.2  L29108451424.256L29108451424.257L29108451424.291L29108451424.292L29252150116.1  L30181597936.224L31077768787.5  L31384711054.7  L32369052471.335L32375749274.295L34135218423.1  L34259272700.223L34277987653.285L34288850762.284L34397423069.284L35668120898.7  L36095776413.3  L36192403312.297L36594645651.5  L37118870096.3  L38180633941.0  L38235734261.1  L38309573212.8  L39220637093.0  L39280637297.0  L41671895942.335L42128420922.11 L42128420922.13 L42219572720.297L42411609006.0  L4248698872.6   L42851534655.7  L45045350157.1  L45125364957.284L45497087078.1  L46204432317.2  L4681653737.1   L47513520362.256L47513520362.257L47513520362.291L47513520362.292L4916741879.1   L49379278409.0  L49730994409.1  L49738838761.1  L51038873259.1  L51543886882.6  L51624893551.3  L52010345249.0  L53504347694.284L58573668988.297L59308630368.6  L59410742007.1  L60098763854.3  L60690035770.1  L63667055128.0  L66151426447.10 L66151427842.16 L66155280105.1  L6897470952.1   L7462897247.3   L76975728.223   L7735748552.2   L7738195705.2   L8866281207.1   L9756297299.5   P21870859916.233P21870859916.234P21870859916.308P21870859916.309P22788237002.298P22788237002.299P22976122839.263P22976122839.264P22976122839.298P22976122839.299P29008688568.297P7750690063.234 P7750690063.235 P7750690063.297 P7750690063.309 Q10131420601.258Q10357626745.258Q10444871353.258Q10592318617.254Q11036308393.258Q11369794822.294Q11671739801.258Q11795115657.258Q11799173861.263Q11799173861.264Q11801279589.233Q11801279589.234Q11801279589.308Q11801279589.309Q11876874745.258Q1258610697.258 Q12832733304.305Q13145930644.258Q13236282377.258Q1345699856.230 Q13482002985.258Q13555290825.258Q15103077986.308Q15203692921.258Q15221952244.293Q15466186521.258Q15552199497.258Q15617776217.258Q15729554057.258Q16562189209.258Q16814055273.258Q16980098229.259Q17204041764.258Q17470962187.258Q17477203002.258Q17519604921.258Q17680877877.259Q18240541929.258Q18559763369.258Q19014026185.258Q19342238456.258Q19637463072.253Q19995118583.293Q20364844244.258Q2037562293.259 Q20377295058.260Q20554377257.258Q20580512354.233Q20580512354.234Q20580512354.297Q20580512354.308Q20580512354.309Q20676242079.256Q20748444521.258Q20759491593.258Q20981439801.258Q2128571384.234 Q21463481721.258Q21927380126.255Q22208514180.258Q22297922500.258Q22538495257.258Q22659823113.258Q22712450012.233Q22712450012.234Q22712450012.308Q22712450012.309Q22724788601.258Q2295878148.248 Q24018317481.258Q24086302601.258Q24100324249.258Q24132682908.257Q24251258485.233Q24251258485.234Q24259400297.258Q24348810665.258Q2485481321.258 Q24915829049.258Q25513505925.233Q25513505925.234Q25761932521.258Q26000592281.258Q26086659700.258Q26330853017.258Q26397936888.258Q26505119060.298Q26505119060.299Q26507224020.297Q26571749120.305Q26594187785.258Q27331632869.293Q27346281817.294Q2753228427.258 Q2767954106.258 Q28054021028.258Q28089869429.231Q28160402148.258Q28943296867.293Q29107305577.258Q2912538745.258 Q29170325656.257Q29742734937.258Q29864012617.258Q29934768537.258Q31072602457.258Q31214822484.258Q31421117353.258Q31549236021.259Q31624191881.258Q31848195257.258Q31934853531.259Q3203240366.231 Q3203240366.232 Q3203240366.306 Q32375247709.294Q33073221636.258Q33100832724.293Q33163963640.305Q33272590905.258Q33357214681.294Q33369542482.293Q33388514457.258Q33535083481.258Q33798455113.258Q33945187121.258Q34357517859.259Q34883213353.258Q35350640745.258Q3545121163.258 Q3551465402.258 Q35588501881.258Q35782559929.258Q3586009242.255 Q3591934522.258 Q3606699019.258 Q36186297499.259Q36240681831.305Q36628663401.258Q36867396889.258Q36918304889.258Q36936645108.258Q37043026228.258Q38293840537.258Q38610753881.258Q38817606697.258Q39035804557.230Q39291452345.258Q39380794105.258Q40607654361.258Q40724577528.258Q40795783737.258Q40801794329.258Q41218494256.297Q41220736304.296Q42079719380.258Q42155198537.258Q42185903892.258Q42276133095.305Q4338985465.258 Q4352828670.290 Q44071587417.258Q44139316665.258Q44298944140.249Q44298944140.259Q44301027056.263Q44301027056.264Q44301027056.298Q44301027056.299Q44458553465.258Q44580792331.258Q44591326778.258Q44673648888.258Q45057547415.234Q4510055513.258 Q45409338677.259Q45749969833.258Q45814952601.258Q4599398297.258 Q46453135609.258Q4655891641.258 Q4685173705.258 Q47176464681.258Q47228431932.263Q47228431932.264Q47228431932.298Q47228431932.299Q47409184484.296Q47411131620.297Q47717383321.258Q48117823211.297Q48119910507.263Q48119910507.264Q48119910507.298Q48119910507.299Q48174068169.258Q48226497179.256Q48263409929.258Q48293492255.305Q4879526665.258 Q49141762585.258Q49490279529.258Q49684412329.258Q49693087817.258Q49698585326.232Q49698585326.233Q49698585326.295Q49698585326.307Q49917092217.258Q49933378966.297Q50247582329.258Q50382389689.258Q50721477213.294Q50822246249.258Q51144219844.258Q51651739801.258Q51660690873.258Q52019673064.231Q52389960886.233Q52389960886.234Q52389960886.308Q52389960886.309Q53028314616.258Q53178279593.258Q53282365929.258Q53697455321.294Q53935010594.235Q54481541671.259Q54697560361.258Q54936293849.258Q54967541497.297Q54967541497.309Q55001772976.293Q55335753481.258Q55807754276.253Q5596578838.263 Q5596578838.264 Q5596578838.298 Q5596578838.299 Q56671730518.294Q56681749017.258Q56979388885.258Q57303113849.258Q57625797019.259Q57656407986.308Q57897686557.254Q58024378537.258Q58343358313.258Q58768111688.297Q58768111688.309Q58870687193.258Q59130206345.258Q59208011072.293Q59281792969.258Q59471812763.259Q5949421545.258 Q59617553652.258Q59619599045.258Q59825285692.295Q6017139401.258 Q60224107785.258Q60248277469.252Q60299548674.295Q6031165145.258 Q60340291561.258Q60536958456.258Q60715880925.294Q60781988089.258Q61992100932.258Q62098483076.258Q63014698011.258Q6339342500.258 Q63435846322.259Q63818869865.258Q64132581737.258Q64228675114.262Q64228675114.263Q64228675114.297Q64228675114.298Q64228946346.263Q64228946346.264Q64228946346.298Q64228946346.299Q64284167337.258Q64357616849.235Q64522028473.258Q64716168441.258Q65562267817.258Q65854010553.258Q65872527924.258Q65959841140.258Q66202517129.258Q6652800313.258 Q66901779611.259Q66942122546.249Q66954699982.297Q66954699982.309Q66956788302.263Q66956788302.264Q66956788302.298Q66956788302.299Q67210671833.258Q67762242825.258Q67854622564.258Q67979225478.294Q68316483385.258Q68423357273.252Q6846932089.258 Q6912043756.260 Q6912046254.297 Q6912046254.309 Q743355035.259  Q8017761716.258 Q8330954249.258 Q8479622473.258 Q945129225.258  Q9689710761.258 Q9883786217.258 Q9932861694.290 Q9934961264.293 Q9947771764.293 Q9947836772.248 00000100200300400501`03K06;08k0;S0>;0@^0CA0E\0H70I_0Ic0Ig0In0J20L10N00N10OK0Pe0R?0RC0RD0RH0RI0RJ0Sd0Sh0T30T70T80T90T:0T>0U_0Uc0Ug0Uk0VC0We0Wi0Wj0Wn0Wo0YI0YM0YQ0Zk0\E0\F0\G0\H0\I0\J0\K0\O0^10^50^J0^K0`_0`c0bE0d\0g30hX0ho0i<0jV0jZ0jf0jg0jk0kK0kL0kM0kN0l60l^0n80n90nN0nd0nh10M10Q10W10[12W14S16O18K18O18P18T18X18\18m1971981:R1;l1<;1<?1<I1<M1<N1<_1=A1=E1=I1=T1?61?71?81?<1?@1A?1CB1E=1G81Hf1JT1L:1M`1OF1Pl1S51Tc1VP1XQ1Z:1[I1\X1]g1_G1`V1bg1d61eE1fk1hQ1j71k^1m@1nb1nc20221E22T23c25Q26`26a28C29R2:a2<02=?2>N2?]2@l2B;2CO2D^2D_2D`2Eo2F02G?2G@2HO2I^2K>2LQ2M`2Ma2OA2PP2PQ2PR2PS2PT2PU2R52SD2SE2TT2TU2Ud2WD2XS2Yb2[12\@2]m2_[2aD2bm2bn2d=2eL2f[2f\2h<2j=2l=2mL2n[2oj31932j34Z34[35j37938H39W3;A3<k3>Q3?d3A33BF3CY3Dh3F73GF3Hd3J33KF3LU3Md3OD3PS3Qb3S13T@3UO3V^3V_3V`3Wo3YC3Z_3\;3]V3^i3`83aK3b^3cm3e@3fS3gb3i13j@3l<3mb3o140@40A40B41Q42`44@44A44B45V46i46j48949H4:W4;f4=54=64>E4?c4A24BA4CP4D_4D`4Eo4GO4Ho4J>4KM4L\4Mo4O>4PM4Q\4Rk4T?4US4W94X_4ZE4[k4[l4[m4[n4]=4]>4^M4^N4_]4_^4`m4b<4b=4cL4d[4fE4go4iY4kC4lc4nC4oR51P53R55T57V59X5:g5<G5=V5>i5@85AG5BV5Ce5Cf5EC5F`5H85IT5Jc5Jd5L35MB5Nb5P15Q@5RO5RP5T>5VF5XO5ZS5\W5]f5_55`D5ad5ae5cY5cZ5di5fI5gk5i:5jI5ki5kj5kk5kl5km5mB5mC5nR5oa5ob61D62d64364465T67668E69T6:g6<66=J6>Y6>Z6>[6@?6AN6B]6D=6Ea6Eb6G16G26HE6IT6Jc6L26M`6No6O06P?6QN6Sn6VN6Xn6[N6^46`Z6c@6ef6g56g66hE6iT6iU6jd6l36mB6nQ6o`71472H73h75J77078V7:<7;b7=17=27>A7@R7Aa7CA7DP7F07GP7I27JF7KU7Ld7N37OB7PQ7Q`7Ro7T>7UM7V\FFFFFS2LF2sp3PKA3PAR2FB3sp13LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA3PAR2FB3sp13LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R3HIA5NEEDR1h2LF2sp3PKA3PAR2lo3SLO3TOP2FB3sp13SP13LFB3NZP5NZPAR2hk2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v182F04FBLO4SP1R3NER3ETk4NSH'3NSL2HB5Ha_st5Hl_stS1R3HIA5NEEDR1h2LF2sp3PKA3PAR2lo3SLO3TOP2FB3sp13SP13LFB3NZP5NZPAR2hk2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v182F04FBLO4SP1R3NER3ETk4NSH'3NSL2HB5Ha_st5Hl_stS1R3HIA5NEEDR1h2LF2sp3PKA3PAR2lo3SLO3TOP2FB3sp13SP13LFB3NZP5NZPAR2hk2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04FBLO4SP1R3NER3ETk4NSH'3NSL2HB5Ha_st5Hl_stS1R3HIA5NEEDR1h2LF2sp3PKA3PAR2lo3SLO3TOP2FB3sp13SP13LFB3NZP5NZPAR2hk2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04FBLO4SP1R3NER3ETk4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA3PAR2lo3LOS3SLO2FB3sp13SP13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v182F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA3PAR2lo3LOS3SLO2FB3sp13SP13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v182F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA3PAR2lo3LOS3SLO2FB3sp13SP13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA3PAR2lo3LOS3SLO2FB3sp13SP13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA3PAR2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183PFA4NSH'3NSL2HB5Ha_st5Hl_stS2FBS2FBS2FB2F0S2FBS2LF2sp3PKA3PAR2FB3sp13LFB3LEN3NZP1P4LEN03PR03P475NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04SP1R4NSH'3NSLS2LF2sp3PKA3PAR2FB3sp13LFB3LEN3NZP1P4LEN03PR03P475NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04SP1R4NSH'3NSLFS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2FBFS2FBFSS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2FBS2FB2d03XB1S2FBSFFS2FBS2LF2sp3PKA3PAR2FB3sp13LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL4PPOSS2FBS2FBS2FBS1R3HIA1h2sp3TOP3sp13SP1S2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLS2FBFS2FBSS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2FBS2FBS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFFFFFFS2FBS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLS2FBS1R2lo3sp14SLO13NER1HFS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO2FB3sp13LFB3LEN3NZP1P4LEN05NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04FBLO4SP1R3NER4NSH'3NSL4PPOSS2FBS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO2FB3sp13LFB3LEN3NZP1P4LEN03PR03P475NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04FBLO4SP1R3NER4NSH'3NSLS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO2FB3sp13LFB3LEN3NZP1P4LEN03PR03P475NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04FBLO4SP1R3NER4NSH'3NSLS2LF2sp3PKA3PAR2FB3sp13LFB5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL4PARBS1R3HIA1h2sp2lo3TOP3HT0S2LB3LBk4C24kS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2FBS2lo2FB4FBLOSS2loS1R5NEEDR2sp2lo3sp13SP14SLO13NERSSFS1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2d03XB2S1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2d03XB2S2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLSS1R2FB3APS2d03XB13XB2S3LEN1v2VB3TV13RB03GP0S2FBS2LF2sp3PKA3PAR2FB3sp13LFB5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL4PARBS2FBS1R2FBS2FBS1R2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS2FBSS2FBS2FBS2FBS1d1f3FB'3TF13RF0S1R2FB3APSSS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS3LEN1P4LEN02KAS2FBS1R2lo3LOSS2FBSS1r3RR92r02KR1q1HS2FB2r02F81q1r1H2H02q02H43sp14SP1MS2FBS2FBS1r3RR93RNZS2LF2sp3PKA3PAR2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLFFS2FBS2FBS1R5NEEDR2LF2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184FBLO4SLO13NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184FBLO4SLO13NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184FBLO4SLO13NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184FBLO4SLO13NER4NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183PFA4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183PFA4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F13ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F13ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5ALPAR5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v183NER4NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFFFFFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v183NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v183NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp3PKA2lo3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3sp13LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp2lo3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS2LF3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184SP1R4NSH'3NSL2HBS2LF3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184SP1R4NSH'3NSL2HBS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184SP1R4NSH'3NSL2HBS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183NER4NSH'3NSL2HB5Ha_st5Hl_stS1R2LF2sp3PKA2lo2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF2sp2lo3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_stS2LF3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v183NER4NSH'3NSLS1R5NEEDR2LF2sp2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v183NER4NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F04NSH'3NSL2HBFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFFS1R2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA3PAR2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8stS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8stS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8stS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA3PAR2lo3SLO3SPA2FB3sp13LFB3NZP5ALPAR5NZPAR2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB1P2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL2HBS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v123v133v153v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGI tg pd bs LEN0 HPAR0 ALPAR NZPAR OPAR0 CRPAR DSPAR DPARI PR0 P47 PNZ"] Lemma spec_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "PWok,SpP,(4;.R1.)P,(4<.R2.)Phk,(3.$2.VR,VHIA,)PLBk,(;.$<.)Pmk,P,(=.&40.)(>.(=.&8.))Pv,$?.Pf,$?.Pv1,(=.&40.)Pv2,(=.&40.)Pv3,(=.&40.)Pv4,(=.&40.)Pv5,(=.&40.)Pv6,(=.&40.)Pv7,(=.&40.)Pv8,(=.&40.)Pv9,(=.&40.)Pv10,(=.&40.)Pv11,(=.&40.)Pv12,(=.&40.)Pv13,(=.&40.)Pv14,(=.&40.)Pv15,(=.&40.)Pv16,(=.&40.)Pv17,(=.&40.)Pv18,(=.&40.)Ppj,(=.&40.)Plj,(=.&40.)Pvj,(=.&40.)Pvj',(=.&40.)Pgj,(=.&40.)Pgj',(=.&40.)Pjref,(;.(=.&8.))Pjgrp,(;.(=.&8.))Pxra,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa0v,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Ps3v,(=.&40.)Ps10v,(=.&40.)Ps11v,(=.&40.)P,(12.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R32.R31.R30.R2?.R2>.$4=.(13.$10.(23.R2=.)(13.$10.(23.R2<.)(13.$10.(23.R2;.)(13.$10.(23.R2:.)(13.$10.(23.R29.)(13.$10.(23.R28.)(13.$10.(23.R27.)(13.$10.(23.R26.)(13.$10.(23.R25.)(13.$10.(23.R24.)(13.$10.(23.R23.)(13.$10.(23.R22.)(13.$10.(23.R21.)(13.$10.(23.R20.)(13.$10.(23.R1?.)(13.$10.(23.R1>.)(13.$10.(23.R1=.)(13.$10.(23.R1<.)(16.$10.)))))))))))))))))))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+120.)(13.$10.(23.R1;.)(16.$10.)))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+140.)(13.$10.(23.R1:.)(16.$10.)))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+160.)(13.$10.(26.R19.)(13.$10.(26.R18.)(16.$10.))))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+20.)(13.$10.(4>.#<0.R15.)(16.$10.)))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+270.)(13.$10.(26.R17.)(13.$10.(26.R16.)(16.$10.))))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+170.)(13.$10.(4>.#<0.R14.)(16.$10.)))(16.(11.$?.(;.$10.)))))))))(16.$<.)(13.(11.$?.$?.)(14.$?.$?.VIDONE,(15.VIDONE,+1.))(13.(11.$?.$?.)(14.$?.$?.VIDS,(15.VIDS,+38.))(16.(11.$?.$?.)))))P,(2>.(4?.R32.)(4?.VLB,))P,(2>.(15.(15.(15.R31.(41.+5.(42.VLEN,)))(41.+2.(43.+1.)))$44.)(45.VLEN,))P,(2>.(15.(15.(15.R31.(41.+5.(46.=)))+6.)$47.)(48.Vd,))(9.$2.(:.$2.VR,VHIA,R36.Vmo0,)(33.$2.VR,VHIA,$1>.$34.$35.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(36.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(37.(38.R17.(24.&40.Vsp1,)Vgp,Vtp,R16.R15.R14.Vsp,(24.&40.Vsp1,)R13.R12.R11.R10.R?.R>.R=.R<.(24.&40.VFB,)(24.&40.VPKA,)(24.&40.(15.(49.VFB,+3.)(4:.(1;.VR,))))(24.&40.(4:.(1;.VR,)))(24.&40.VPAR,)(24.&40.(15.VFB,+270.))R7.(24.&40.VFB,)R6.R5.R;.R:.R9.R8.)VF,(24.&40.+;0==0.)Vfc,(39.(=.&40.))R34.(3:.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros Wok GI F1C. intros until s11v. intros EBsave C24k VB FB'.
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof par_frame_apart as PFA.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof EBsave as EBk. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(sp1 + 8, sp1 + 152)] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    do 2 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (eb_slots hk LBk mk v f _ _ _ _ _ _ m5 EBsave MU WM ltac:(assumption) SLOTS eq_refl) as EB5.
    try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave. clear mk. rename m5 into mk. rename EB5 into EBsave.
    pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(SHB, SHB + 80)] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    dpose (Forall_inv CHk) as (PCELL & _ & _). dpose (Forall_inv (Forall_inv_tail CHk)) as (LCELL & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail CHk))) as (VCELL & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk)))) as (REFC & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk))))) as (GID & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk)))))) as (GRPC & _ & _).
    cbn [fst snd] in PCELL, LCELL, VCELL, REFC, GID, GRPC.
    pose proof (conj HHk (conj MIk (conj IDSk (conj CHk I)))) as BOX.
    unfold EP_SH0 in FSH. cbn [repeat app] in FSH.
    (* [comment removed for export] *)
    zstep. do 24 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH6 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ddestruct BOX as (HHk0 & MIk0 & IDSk0 & CHk0 & _).
    assert (OWN : Forall own_iv [(SHB, SHB + 80)]) by (apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    assert (EB6 : EB hk LBk m6 v f EP_SH_G [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10; C8 (Z_to_bv 64 PKA); C8 v12; C8 v13; C8 (Z_to_bv 64 (FB + 624)); C8 v15; C8 v16; C8 v17; C8 v18]
                    [(FB + 288, [C8 pj]); (FB + 320, [C8 lj]); (FB + 352, [C4 vj; C4 vj']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gj; C4 gj'])] [] W0).
    { unfold A_pk_ecparams_B.EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_G; cbn [repeat app firstn skipn]; exact FSH6| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [exact (ids_state_own hk LBk mk m6 _ HHk0 OWN IDSk0 MU WM)|].
      split; [eapply (ch_munch_sh mk m6 80); [| exact MU| exact WM| clear - APS; lia];
              repeat (apply Forall_cons; [first [exact (Forall_inv CHk0) | exact (Forall_inv (Forall_inv_tail CHk0)) | exact (Forall_inv (Forall_inv_tail (Forall_inv_tail CHk0)))
                                                | exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk0)))) | exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk0)))))]|]); apply Forall_nil|].
      split; [exact EXTk| exact FRk]. }
    pose proof (sh_zero_aobj _ _ _ _ _ _ _ _ _ _ 46 24 EB6 shg_grp ltac:(clear; lia)) as OGRP. change (FB + 8 * Z.of_nat 46) with G in OGRP. change (8 * Z.of_nat 24) with 192 in OGRP.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof HGI as SP. unfold ecp_group_init_stmtA in SP.
      eapply SP with (h := hk) (LB := LBk) (LF := LF') (A := G) (lo := lo) (LBg := LBk) (junk := jgrp); rewrite ?(unsigned_lit sp1) by exact SP1R; unfold ECP_GROUP_SIZE;
        first [ eassumption | exact OGRP | reflexivity
              | lazymatch goal with
                | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [exact IND| clear; lia| clear; lia]
                | |- _ \/ _ => left; clear - FBLO; lia
                | |- _ mod 8 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- 0 < _ => clear - F0; lia
                | |- lo <= _ => pose proof (arl_need_rt_amem R); clear - SLO1 NER NEEDR H; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                end
              | match goal with |- ?g => idtac "GI-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold ecp_group_init_postA in PO.
    ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m7 & gid0 & gP & gA & gB & gX & gY & gZ & gN & ghp
                    & E & MU7 & WM7 & MI7 & HG7 & ST7 & HH7). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU7, ST7 by exact SP1R. unfold ECP_GROUP_SIZE in MU7.
    replace (ret_pc (Z_to_bv 64 0xb0e44)) with (Z_to_bv 64 0xb0e44 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (eb_munch2 hk LBk m6 v f _ _ _ _ _ m7 G 192 lo EB6 MU7 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WM7 MI7 ST7
                  ltac:(repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]; split; [clear; lia| exact I]|]); apply Forall_nil)) as EB7.
    destruct (tmp_ok_init7A m7 LBk G gid0 gP gA gB gX gY gZ gN ghp HG7) as (TOK7 & PBN7).
    replace (G + 120) with (FB + 488) in PBN7 by (clear; lia).
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB7 PBN7 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB7b.
    destruct (eb_par _ _ _ _ _ _ _ _ _ EB7b) as (HPAR7 & OPAR7).
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EB6 OGRP OWN EBsave PCELL LCELL VCELL REFC GID GRPC FSH6 HHk0 MIk0 IDSk0 CHk0 EB7 HG7 HH7 MU7 WM7.
    pose proof EB7b as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(SHB, SHB + 80); (sp1 + 8, sp1 + 152); (FB + 288, FB + 296)] : list ivl) m7) as MU. pose proof (wmono_refl asegs m7) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m7 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m7 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    dpose (Forall_inv CHk) as (PBN & _ & _). dpose (Forall_inv (Forall_inv_tail CHk)) as (PCELL & _ & _). dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail CHk))) as (LCELL & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk)))) as (VCELL & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk))))) as (REFC & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk)))))) as (GID & _ & _).
    cbn [fst snd] in PBN, PCELL, LCELL, VCELL, REFC, GID.
    pose proof (conj TOK7 (conj HHk (conj MIk (conj IDSk I)))) as BOX.
    unfold EP_SH_G in FSH. unfold buf_cells in HPAR7.
    pose proof (rw_cells_bound _ _ _ _ HPAR7) as PARB. cbn [cells_size csize Nat.add] in PARB. change (Z.of_nat 24) with 24 in PARB.
    (* [comment removed for export] *)
    zstep. do 5 zstep. zstep. do 3 zstep. zstep. do 3 zstep. zstep. zstep.
    zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA PR0 LEN0 P47; Z.div_mod_to_equations; lia|]. clear KA.
    do 3 zstep. try decide_tests.
    zstep. try (if_cases KB; zify_cond KB; [exfalso;
      destruct PNZ as [(PZ & LZ) | PPOS]; [rewrite ?PZ, ?LZ in KB| ];
      repeat match type of KB with context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) in KB by lia end;
      repeat match type of KB with context [Z.eqb ?x ?y] => first [rewrite (proj2 (Z.eqb_eq x y)) in KB by lia | rewrite (proj2 (Z.eqb_neq x y)) in KB by lia] end;
      repeat match type of KB with context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) in KB by lia | rewrite (proj2 (Z.ltb_ge x y)) in KB by lia] end;
      first [discriminate KB | (vm_compute in KB; discriminate KB) | (cbn in KB; discriminate KB) | lia]|]; clear KB).
    zstep. zstep. zstep. zstep. do 4 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH8 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    ddestruct BOX as (TOK0 & HHk0 & MIk0 & IDSk0 & _).
    assert (OWN8 : Forall own_iv [(SHB, SHB + 80); (sp1 + 8, sp1 + 152); (FB + 288, FB + 296)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]]]. }
    assert (EB8 : EB hk LBk m8 v f EP_SH_P [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10; C8 (Z_to_bv 64 PKA); C8 v12; C8 v13; C8 (Z_to_bv 64 (FB + 624)); C8 v15; C8 v16; C8 v17; C8 v18]
                    ((FB + 288, [C8 (Z_to_bv 64 P)]) :: (FB + 352, [C4 vj; C4 vj']) :: [(FB + 320, [C8 lj]); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gj; C4 gj']); (FB + 488, [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])])
                    (tmp_blocks (DS7 (mpd_init (G + 104) gN) (mpd_init (G + 8) gP) (mpd_init (G + 24) gA) (mpd_init (G + 40) gB) (mpd_init (G + 56) gX) (mpd_init (G + 72) gY) (mpd_init (G + 88) gZ))) W0).
    { unfold A_pk_ecparams_B.EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_P; exact FSH8| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [exact (ids_state_own hk LBk m7 m8 _ HHk0 OWN8 IDSk0 MU WM)|].
      split; [repeat (apply Forall_cons; [split; [cbn [fst snd]; assumption| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]|]); apply Forall_nil|].
      split; [exact EXTk| exact FRk]. }
    assert (TOK8 : tmp_ok asegs m8 LBk G 192 (DS7 (mpd_init (G + 104) gN) (mpd_init (G + 8) gP) (mpd_init (G + 24) gA) (mpd_init (G + 40) gB) (mpd_init (G + 56) gX) (mpd_init (G + 72) gY) (mpd_init (G + 88) gZ))).
    { eapply (tmp_ok_own hk LBk m7 m8 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN8).
      intros d0 Hd. ddestruct TOK0 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2 APS; lia| split; [clear - XB1 XB2 FBLO SLO1 SP1 NER NEEDR; lia| split; [clear - XB1; lia| exact I]]]. }
    eapply (GI hk LBk m8 v f _ _ (DS7 (mpd_init (G + 104) gN) (mpd_init (G + 8) gP) (mpd_init (G + 24) gA) (mpd_init (G + 40) gB) (mpd_init (G + 56) gX) (mpd_init (G + 72) gY) (mpd_init (G + 88) gZ)) vj vj' 0xb0eb8); [exact EB8| exact TOK8| clear; repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]; repeat split; lia|]); apply Forall_nil| clear; lia| reflexivity|].
    intros m9 r p9 vw9 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB9 TOK9 PB9 RR9 ROK9.
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EB7b TOK7 EB8 TOK8 OWN8 PBN PCELL LCELL VCELL REFC GID FSH8 HHk0 MIk0 IDSk0 TOK0 HPAR7 OPAR7.
    pose proof EB9 as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(sp1 + 8, sp1 + 152)] : list ivl) m9) as MU. pose proof (wmono_refl asegs m9) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m9 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m9 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    do 8 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
    pose proof (eb_slots hk LBk m9 v f _ _ _ _ _ _ m10 EB9 MU WM ltac:(assumption) SLOTS eq_refl) as EB10a.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 288, [C8 (Z_to_bv 64 p9)]); (FB + 320, [C8 lj]); (FB + 352, [C4 vw9; C4 vj']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gj; C4 gj']); (FB + 488, [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])] _ _ EB10a
                  ltac:(intros c Hc; clear - Hc; cbn [In] in Hc |- *; tauto)) as EB10.
    assert (TOK10 : tmp_ok asegs m10 LBk G 192 (DS7 (mpd_init (G + 104) gN) (mpd_init (G + 8) gP) (mpd_init (G + 24) gA) (mpd_init (G + 40) gB) (mpd_init (G + 56) gX) (mpd_init (G + 72) gY) (mpd_init (G + 88) gZ))).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk m9 m10 _ _ HH0' TOK9 MU WM MI0' ltac:(assumption)).
      - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_nil].
      - intros d0 Hd. ddestruct TOK9 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO SLO1 NER NEEDR; lia| exact I]. }
    assert (SI10 : SPINVx hk LBk m10 v f (mpd_init (G + 104) gN) (mpd_init (G + 8) gP) (mpd_init (G + 24) gA) (mpd_init (G + 40) gB) (mpd_init (G + 56) gX) (mpd_init (G + 72) gY) (mpd_init (G + 88) gZ)
                     p9 lj vw9 vj' jref gj gj' (Z_to_bv 64 0) (Z_to_bv 64 0) v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 (Z_to_bv 64 PKA) v16 v17 v18 0).
    { split; [unfold A_pk_ecparams_D1.SLPx; exact EB10|].
      split; [exact TOK10|]. do 7 (split; [reflexivity|]). split; [exact PB9| clear - C24k; lia]. }
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - assert (RZ : r = 0) by (clear - KR RR9; Z.div_mod_to_equations; lia). subst r.
      eapply (F1C hk LBk m10 _ _ _ _ _ _ _ _ _ p9 lj vw9 vj' jref gj gj' (Z_to_bv 64 0) (Z_to_bv 64 0) v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v16 v17 v18 0);
        [exact (ROK9 eq_refl)| exact SI10| clear; lia| reflexivity| cbn [md_n mpd_init]; clear; lia| cbn [md_n mpd_init]; clear; lia| exact VB| exact FB'].
    - (* [comment removed for export] *)
      clear MU. pose proof (munch_refl ([] : list ivl) m10) as MU.
      eapply (sp_erradd hk LBk m10 _ _ _ _ _ _ _ _ _ p9 lj vw9 vj' jref gj gj' (Z_to_bv 64 0) (Z_to_bv 64 0) v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v16 v17 v18 0 r);
        [exact SI10| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      assert (RNZ : r <> 0) by (intros ->; clear - KR; first [apply KR; reflexivity| (vm_compute in KR; congruence)]). clear - RR9 RNZ. lia.
    all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11670714875.5 L12414522636.0 L13291347995.3 L2220721423.2  L29432667347.5 L38235734261.1 L38408712019.4 L3851014295.6  L5196155000.7  L52381995726.6 L54391830196.3 L59314923118.1 L60098763854.3 L63667055128.0 L66151427842.16L67228227629.9 00000D00E00O00V00f00j01901R01h02802D02G02Q02R03403SS3LEN1P4LEN03PR03P47SS3LEN1P2LZS2FB2F0S1R2lo3LOS3ALO1HS2loS2sp2lo3sp13SP1S1R5NEEDR2lo3sp14SLO13NERS2lo2FB3sp14FBLO1x3XB2S2lo2FB3sp14FBLOS3LEN1P4LEN0S1KS1R2lo3LOSSS2FB2r02F81q1r1H2H02q02H43sp14SP1MS1R3HIA1h2sp2lo3TOP3sp13SP13HT0". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 SP1M F64 FRSH LEN0 PR0 P47"] Lemma sp_getint_empty : LEN = 0 -> GI_stmt False.
  Proof.
    intros LZ. unfold GI_stmt. intros until t6. intros EBk TOK HCD RETr RETe CONT.
    pose proof (sh_zero_aobj _ _ _ _ _ _ _ _ _ _ 36 1 EBk shp_p ltac:(clear; lia)) as OPP. change (FB + 8 * Z.of_nat 36) with (FB + 288) in OPP. change (8 * Z.of_nat 1) with 8 in OPP.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as PCELL.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    assert (SCSk : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP SP1. lia. }
    replace (P + LEN) with P by (clear - LZ; lia).
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { eapply (A_asn1_get_int_empty AL IMG) with (CS := hcs asegs R HIA hk) (PP := FB + 288) (P := P) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact PCELL | exact MIk | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk)
              | exact (hm_abase asegs R HIA hk LBk LF' mk HHk) | exact OPP | exact STb | exact SCSk | reflexivity
              | lazymatch goal with
                | |- 0 <= P < 2^64 => clear - PR0 P47 LEN0; lia
                | |- _ mod 8 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- _ mod 2 = 0 => rewrite (unsigned_lit RET) by exact RETr; exact RETe
                | |- 0 < FB + _ => clear - F0; lia
                | |- 0 <= lo => clear - ALO LOS; pose proof (alloc_ceiling_pos (L := arl_L R)); lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ \/ _ => clear - FBLO SP1; lia
                end
              | match goal with |- ?g => idtac "GIE-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold pure_ret_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    eapply CONT; [exact (eb_scratch _ _ _ _ _ _ _ _ _ _ m2 lo EBk0 MU2 ltac:(clear; lia) WM2 MI2 ST2)| | clear - LEN0; lia| unfold ASN1_OUT_OF_DATA_U; clear; lia| unfold ASN1_OUT_OF_DATA_U; intros K; exfalso; clear - K; lia].
    eapply (tmp_ok_own hk LBk mk m2 _ _ HHk TOK MU2 WM2 MIk MI2).
    - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1; lia| apply Forall_nil].
    - intros x Hx. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO; lia| exact I].
    all: match goal with |- ?g => idtac "GIE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NAMED_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "P,(50.(31.(=.&40.)Vtg,(24.&40.=)))Phk,(3.$2.VR,VHIA,)PLBk,(;.$<.)Pmk,P,(=.&40.)(>.(=.&8.))Pv,$?.Pf,$?.Pv1,(=.&40.)Pv2,(=.&40.)Pv3,(=.&40.)Pv4,(=.&40.)Pv5,(=.&40.)Pv6,(=.&40.)Pv7,(=.&40.)Pv8,(=.&40.)Pv9,(=.&40.)Pv10,(=.&40.)Pv11,(=.&40.)Pv12,(=.&40.)Pv13,(=.&40.)Pv14,(=.&40.)Pv15,(=.&40.)Pv16,(=.&40.)Pv17,(=.&40.)Pv18,(=.&40.)Pgj,(=.&40.)Pgj',(=.&40.)Pxra,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa0v,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Ps3v,(=.&40.)Ps10v,(=.&40.)Ps11v,(=.&40.)P,(12.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R2<.R2;.R2:.R29.R28.$4=.(13.$10.(23.R27.)(13.$10.(23.R26.)(13.$10.(23.R25.)(13.$10.(23.R24.)(13.$10.(23.R23.)(13.$10.(23.R22.)(13.$10.(23.R21.)(13.$10.(23.R20.)(13.$10.(23.R1?.)(13.$10.(23.R1>.)(13.$10.(23.R1=.)(13.$10.(23.R1<.)(13.$10.(23.R1;.)(13.$10.(23.R1:.)(13.$10.(23.R19.)(13.$10.(23.R18.)(13.$10.(23.R17.)(13.$10.(23.R16.)(16.$10.)))))))))))))))))))(13.(11.$?.(;.$10.))(14.$?.(;.$10.)(15.VFB,+270.)(13.$10.(26.R15.)(13.$10.(26.R14.)(16.$10.))))(16.(11.$?.(;.$10.))))(16.$<.)(13.(11.$?.$?.)(14.$?.$?.VIDONE,(15.VIDONE,+1.))(13.(11.$?.$?.)(14.$?.$?.VIDS,(15.VIDS,+38.))(16.(11.$?.$?.)))))P,(2>.(15.R2:.$51.)(45.VLEN,))P,(2>.(15.R2:.$52.)(48.Vd,))(9.$2.(:.$2.VR,VHIA,R2?.Vmo0,)(33.$2.VR,VHIA,$1>.$34.$35.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(36.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(37.(38.R16.(24.&40.Vsp1,)Vgp,Vtp,R15.R14.R13.Vsp,(24.&40.Vsp1,)R12.R11.R10.R?.R>.R=.R<.R;.(24.&40.VFB,)(24.&40.VPKA,)(24.&40.(15.(49.VFB,+3.)(4:.(1;.VR,))))(24.&40.(4:.(1;.VR,)))(24.&40.VPAR,)(24.&40.(15.VFB,+270.))R6.(24.&40.VFB,)R5.R4.R:.R9.R8.R7.)VF,(24.&40.+;0=;4.)Vfc,(39.(=.&40.))R2=.(3:.$2.)))")
(* [comment removed for export] *).

  Ltac par_cut :=
    lazymatch goal with
    | |- aevtA ?segs _ _ (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
        let d1 := decode_at segs slow in
        lazymatch d1 with
        | Some (OpImm ALU_ADD ?tmp _ _, _) =>
            let pt := eval vm_compute in (bv_key tmp) in
            let d2 := decode_at segs (slow + 4)%Z in
            lazymatch d2 with
            | Some (Branch BC_LT _ ?kr _, _) =>
                let pk := eval vm_compute in (bv_key kr) in
                merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro)
            end
        end
    end.
  Ltac par_merge c k HK :=
    par_cut;
    [ let Kz := fresh "Kz" in
      if_cases Kz; zify_cond Kz;
      [ zstep; step_to_if;
        lazymatch goal with
        | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
            replace cnd with true by (symmetry; eapply (shadow_slow_takenN c _ k _ HK Kz); first [qlia | (rewrite land7_mod; clear - ALPAR; lia)]); cbv iota
        end;
        apply evtA_done; eexists; eexists; reflexivity
      | apply evtA_done; eexists; eexists; reflexivity ]
    | let ms' := fresh "ms'" in let vk := fresh "vk" in let vt := fresh "vt" in
      intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k ].
  Tactic Notation "par_chk" constr(H) constr(c) constr(n) :=
    let k := fresh "k" in let RD := fresh "RD" in let HK := fresh "HK" in
    shadow_byte H c n as k RD HK;
    zstep; clear RD; step_to_if;
    par_merge c k HK.
  Ltac all_cb8 H :=
    repeat (lazymatch type of H with
            | rw_cells _ _ _ ?cs =>
                let rec find pre l :=
                  lazymatch l with
                  | CB 8 ?bs :: ?post => cb8_to_c8 H pre
                  | ?c :: ?post => let pre' := eval cbv [app] in (pre ++ [c]) in find pre' post
                  end in
                find (@nil cell) cs
            end).


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L1824826089.1   L21986553321.1  L23915375263.2  L35668120898.7  L4681653737.1   L49379278409.0  L49730994409.1  L49738838761.1  L51358233881.1  L58789197907.238L58864221186.5  L60098763854.3  L61155907660.4  L64630569949.3  L66155280105.1  L68127077441.2  Q15171357177.247Q2467607158.247 Q26295627581.247Q51517590598.244Q60299859384.244Q60312050231.247Q60312995534.246Q6152620093.246 Q66162928518.247Q8956025384.244 00000400800>00U00Y00Z00^00b00g02S02h03203A03J03N03Y03Z05A06^08?09`0;A0<b0>C0?d0AAS2FBS2FBS1d2D0S1R3HIA1h2sp2lo3TOP3HT0S2FBSS2FBS2FBS3LENS2LF2sp3PKA3PAR2FB3sp13LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS3LEN3TV13RB03GP03BV5S1R2lo3LOSS1d3TF13RF03BF5S1R3HIA1hS2FBS3PAR5ALPARFS2LF3PAR2FB3LFB5NZPAR2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF3PAR2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF3PAR2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF3PAR2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF3PAR2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF3PAR2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF3PAR2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSLS2LF2FB3LFB2sv3sv03sv13sv23sv33sv43sv53sv63sv73sv83sv94sv104sv114sv124sv134sv144sv154NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGI pd bs LEN0 HPAR0 ALPAR NZPAR OPAR0 CRPAR DSPAR DPARI IDS0 PR0 P47 PNZ"] Lemma body_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "PWok,SpP,(4;.R1.)P,(4<.R2.)P,$53.Ph1,(3.$2.VR,VHIA,)Pm1,P,(=.&40.)(>.(=.&8.))Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Phw0,(=.&40.)Phw1,(=.&40.)Phw2,(=.&40.)Pjref,(;.(=.&8.))Pjgrp,(;.(=.&8.))Pjslots,(;.(=.&8.))Ppj,(=.&40.)Plj,(=.&40.)Pvj,(=.&40.)Pvj',(=.&40.)Pgj,(=.&40.)Pgj',(=.&40.)P,(54.$2.VR,VHIA,R19.VLB,(13.(11.$?.$?.)(14.$?.$?.VFB,+400.)VLF,)R18.)P,(31.P,$?.Sp(1<.$2.VR,VHIA,R1:.)(1<.$2.VR,VHIA,Vh,))P,(31.$?.(55.$2.VR,VHIA,R1;.)(55.$2.VR,VHIA,Vh,))P,(31.$?.(56.$2.VR,VHIA,R1<.)(56.$2.VR,VHIA,Vh,))P,(31.$?.(57.$2.VR,VHIA,R1=.)(57.$2.VR,VHIA,Vh,))P,(31.$?.(58.$2.VR,VHIA,R1>.)(58.$2.VR,VHIA,Vh,))P,(31.$?.(59.$2.VR,VHIA,R1?.)(59.$2.VR,VHIA,Vh,))P,(18.$2.R1?.VFB,(13.$10.(23.R13.)(13.$10.(23.R12.)(13.$10.(23.R11.)(16.$10.)))))P,(18.$2.R20.(15.VFB,+20.)(13.$10.(4>.#<0.R11.)(16.$10.)))P,(18.$2.R21.(15.VFB,+120.)(13.$10.(23.R?.)(16.$10.)))P,(18.$2.R22.(15.VFB,+140.)(13.$10.(23.R?.)(16.$10.)))P,(18.$2.R23.(15.VFB,+160.)(13.$10.(26.R?.)(13.$10.(26.R>.)(16.$10.))))P,(18.$2.R24.(15.VFB,+170.)(13.$10.(4>.#<0.R14.)(16.$10.)))P,(18.$2.R25.(15.VFB,+270.)(13.$10.(26.R?.)(13.$10.(26.R>.)(16.$10.))))P,(18.$2.R26.(15.(49.VFB,+3.)(4:.(1;.VR,)))$4=.)P,(18.$2.R27.(15.(15.(49.VFB,+3.)(4:.(1;.VR,)))+50.)(13.$10.(4>.#30.(5:.(=.&8.)(24.&8.=)#30.))(16.$10.)))P,(18.$2.R28.(15.(5;.&40.Vsp,)-68.)(13.$10.(23.Vs11,)(13.$10.(23.Vs10,)(13.$10.(23.Vs9,)(13.$10.(23.Vs8,)(13.$10.(23.Vs7,)(13.$10.(23.Vs6,)(13.$10.(23.Vs5,)(13.$10.(23.Vs4,)(13.$10.(23.Vs3,)(13.$10.(23.Vs2,)(13.$10.(23.Vs1,)(13.$10.(23.Vs0,)(13.$10.(23.Vra,)(16.$10.)))))))))))))))P,(18.$2.R29.(15.Vsp1,+8.)(13.$10.(4>.#88.R18.)(13.$10.(23.(24.&40.VFB,))(16.$10.))))P,(5<.$2.R2:.Vsp1,(15.Vsp1,+8.))P,(5<.$2.R2;.(15.Vsp1,+98.)(15.(5;.&40.Vsp,)-68.))P,(5<.$2.R2<.Vlo,Vsp1,)P,(5=.$2.R2=.)P,(5>.$2.VR,VHIA,Vh,VLB,VLF,(5;.&40.Vsp,)(5?.VR,)(16.$60.)Vm,R2>.)(9.$2.(:.$2.VR,VHIA,R30.Vmo0,)(33.$2.VR,VHIA,$1>.$34.$35.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(36.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(37.(38.(24.&40.+;0;=0.)(24.&40.Vsp1,)Vgp,Vtp,R2>.R2=.R2<.Vsp,(24.&40.Vsp1,)(24.&40.(49.VPAR,+3.))(24.&40.->.)(24.&40.=)(24.&40.-=.)R2;.R2:.R29.R28.(24.&40.VFB,)(24.&40.VPKA,)(24.&40.(15.(49.VFB,+3.)(4:.(1;.VR,))))(24.&40.(4:.(1;.VR,)))(24.&40.VPAR,)Vs7,Vs8,(24.&40.VFB,)Vs10,Vs11,R27.R26.R25.R24.)VF,(24.&40.+;0=98.)Vfc,(39.(=.&40.))R2?.(3:.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros Wok GI F1C NAMED. intros until gj'.
    intros HH1 Ehcs Ehtop Estk Eflag Evol Efr FHD1 REF1 PC1 LC1 VC1 GRP1 GID1 FSH1 FSHR1 SAVE1 SLOT1 STlo1 SThi1 STb1 MI1 PRES0.
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    assert (BV5 : 0 + 5 * MPI_RB_PHI LEN + 2 * grow_PHI 1 + TAILV <= pk_ecparams_PHI LEN) by (unfold TAILV, pk_ecparams_PHI; change AVOL_CALL with 0; clear; lia).
    assert (BF5 : 0 + 5 * MPI_RB_FR 0 + 6 + TAILF <= pk_ecparams_FR d) by (unfold TAILF, pk_ecparams_FR, MPI_RB_FR, GF_FR, group_load_FRn, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    pose proof SLOT1 as SLOTS1.
    lazymatch type of SLOTS1 with rw_cells ?sg ?mx ?A [CB 136 ?j; ?c] =>
      change (rw_cells sg mx A [CB 136 j; c]) with (rw_cells sg mx A ([] ++ CB 136 j :: [c])) in SLOTS1;
      apply (rw_cells_split_CB sg mx A [] 136 j [c] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in SLOTS1; [| reflexivity]; cbn [mk_CB_cells app] in SLOTS1
    end.
    all_cb8 SLOTS1.
    repeat match type of SLOTS1 with context [C8 (le_bytes_to_word ?bs)] => let w := fresh "sv" in set (w := le_bytes_to_word bs) in SLOTS1; clearbody w end.
    lazymatch type of SLOTS1 with rw_cells _ _ _ ?SL =>
    assert (EB1 : EB h1 LB m1 0 0 EP_SH0 SL
                    [(FB + 288, [C8 pj]); (FB + 320, [C8 lj]); (FB + 352, [C4 vj; C4 vj']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gj; C4 gj']); (FB + 368, [CB 192 jgrp])] [] W0) end.
    { unfold A_pk_ecparams_B.EB. split; [exact HH1|]. split; [exact (conj Ehtop (conj Estk Eflag))|]. split; [intros x Hx; rewrite Ehcs; exact Hx|].
      split; [rewrite Evol, Efr; split; clear; lia|].
      split; [dexists hw0, hw1, hw2; exact FHD1|]. split; [split; [exact FSH1| reflexivity]|]. split; [exact FSHR1|].
      split; [exact SAVE1|]. split; [split; [exact SLOTS1| reflexivity]|]. split; [exact STlo1|]. split; [exact SThi1|]. split; [exact STb1|]. split; [exact MI1|].
      split. { eapply (presW_hmono R HIA h h1); [| rewrite Ehcs; intros x Hx; exact Hx| exact Estk].
               ddestruct PRES0 as (PA & PC1' & PC2' & PC3'). split; [| exact (conj PC1' (conj PC2' PC3'))].
               eapply presA_weaken; [exact PA| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x _; exact I]. }
      split; [exact (ids_presA_gen _ _ _ _ _ [] m m1 IDS0 (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) I I)|].
      split; [repeat (apply Forall_cons; [split; [cbn [fst snd]; assumption| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]|]); apply Forall_nil|].
      split; [apply lb_ext_refl| intros b Hb; destruct Hb]. }
    destruct (eb_par _ _ _ _ _ _ _ _ _ EB1) as (HPAR1 & OPAR1).
    pose proof par_frame_apart as PFA.
    pose proof EB1 as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    pose proof (munch_refl ([(sp1 + 8, sp1 + 152)] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (SCSk : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h1 LB _ LF m1 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h1) h1 _ LF m1 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h1 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h1) as CSOKk.
    unfold buf_cells in HPAR1.
    pose proof (rw_cells_bound _ _ _ _ HPAR1) as PARB. cbn [cells_size csize Nat.add] in PARB. change (Z.of_nat 24) with 24 in PARB.
    clear FHD1 REF1 PC1 LC1 VC1 GRP1 GID1 FSH1 FSHR1 SAVE1 SLOT1 SLOTS1 STlo1 SThi1 STb1 PRES0.
    unfold EP_SH0 in FSH. cbn [repeat app] in FSH.
    (* [comment removed for export] *)
    zstep.
    par_chk OPAR1 PAR 4.
    (* [comment removed for export] *)
    do 4 zstep.
    rename m1 into m2. pose proof EB1 as EB2.
    if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      eapply (spec_walk Wok GI F1C h1 LB m2 0 0); [exact EB2| apply Z.le_refl| exact BV5| exact BF5].
    - (* [comment removed for export] *)
      assert (TGN : tg <> Z_to_bv 64 0) by (intros E; rewrite E in KT; vm_compute in KT; discriminate KT).
      eapply (NAMED TGN h1 LB m2 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gj gj');
        [eapply eb_ch_incl; [exact EB2| intros c Hc; clear - Hc; cbn [In] in Hc |- *; tauto]| clear - BV5 TV1 RB0 GP0; lia| clear - BF5 TF1 RF0; lia].
    all: match goal with |- ?g => idtac "BODY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable BUF : Z.
  Hypothesis HBS0 : bytes_at asegs m BUF bs.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis B47 : BUF + Z.of_nat (length bs) + 8 <= 2^47.
  Hypothesis CRB : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis DSB : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis DBC : BUF + Z.of_nat (length bs) <= C \/ C + 256 <= BUF.
  Hypothesis DBI : BUF + Z.of_nat (length bs) <= IDONE \/ IDS + 56 <= BUF.
  Hypothesis OBUF0 : aobj asegs AL CS m BUF (Z.of_nat (length bs)).
  Hypothesis BP : BUF <= P.
  Hypothesis PL : P + LEN <= BUF + Z.of_nat (length bs).
  Hypothesis BSNE : 0 < Z.of_nat (length bs).
  Local Notation eb_bytes := (A_pk_ecparams_D1.eb_bytes R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH BUF bs HBS0 CRB DSB DBI OBUF0).
  Local Notation buf_fresh_apart := (A_pk_ecparams_D1.buf_fresh_apart R HIA LB LF lo LOS BUF bs CRB BSNE).
  Local Notation sp_getmpi := (A_pk_ecparams_D1.sp_getmpi R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF P BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL HRB HGM BSNE slo SSH SLOK SLOL).
  Local Notation sp_readbin := (A_pk_ecparams_D1.sp_readbin R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF P BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL HRB BSNE).
  Local Notation sp_gettag := (A_pk_ecparams_D1.sp_gettag R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP HH0 FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ P BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL BSNE HGT).



  #[using="Type"] Lemma shp_ver : cell_at EP_SH_P 44 = Some (C1 (Z_to_bv 8 4)).
  Proof. reflexivity. Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L15362649509.3  L15756354262.4  L15844809021.14 L18901988838.1  L19405460375.6  L19405460375.9  L19715508571.11 L19969246536.1  L22148828439.11 L2220721423.2   L22252508346.1  L22775671055.2  L23430585573.3  L25635823004.14 L26492762802.10 L2697601136.14  L27782475962.1  L35226968475.1  L3581898027.1   L35915898997.14 L36901011823.1  L3851014295.9   L38551529394.0  L38673530624.258L4185783531.1   L42968013442.12 L48020887289.8  L52392417244.14 L53237926827.1  L54913609479.3  L55588686165.0  L58559132961.9  L58972524609.3  L60098763854.3  L63667055128.0  L66151427842.16 L67066520038.1  L67228227629.9  L67763520527.2  L846991845.3    L8981313288.1   L9631767084.2   00000;00I00c00g01@01_02G02K03303:03>03E03Q03d04E04L04P04T04X04g04k05J05K06806<06g07G07Z07^07j07k08F08R08\08]09?09C09b09j0:50:90:@S2FB2d03XB1S1R2lo3LOS3ALOS2sp2lo3sp13SP12bs3BUF3DSBS2FBS1R5NEEDR2lo3sp14SLO13NERS1R5NEEDR2sp2lo3SLO3sp13SP13NERS1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2d03XB2S2FBS1R5NEEDR2sp2lo3SLO3sp13SP13slo4SLOL3NERS2FB2F0S2FBS2FB2F0S2sp3sp13SP1S2lo2FB3sp12bs4FBLOS1R5NEEDR2lo2FB3sp14FBLO4SLO13NERS2FB2bsS2FBS2FBS2FBS2FB2bs3BUF3BFAS2FBS1R5NEEDR2sp2lo3SLO3sp13SP13NERSS2LF2sp3PKA3PAR2FB3sp13LFB2bs2SL3RET4NSH'3NSLS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3NER3ACPS1R5NEEDR2sp2lo3sp13SP14SLO13NERS2lo2FB3sp12bs4FBLOS2FBS3LEN1P4LEN0SS1R3HIA1h2sp3TOP2hk3ETk3HTkS2bs3BUF3B47S1R2lo3LOSSS3sp12r04SP1M1q1r1H2H02q02H42FB2F8S2FBS1R3HIA1h2sp2lo3TOP3sp13SP13HT0S2lo3sp1S2FB2d03XB1S2FBS2FB2F0". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK PAR LOS SLO TOP HH0 SP1 SP1M F64 FRSH LFB bs LEN0 HGINT BUF HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL BSNE slo SSH SLOK SLOL"] Lemma sp_getint : GI_stmt True.
  Proof.
    unfold GI_stmt. intros until t6. intros EBk TOK HCD RETr RETe CONT.
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EBk) as (HBSk & OBUFk & CRBk).
    pose proof (sh_zero_aobj _ _ _ _ _ _ _ _ _ _ 36 1 EBk shp_p ltac:(clear; lia)) as OPP. change (FB + 8 * Z.of_nat 36) with (FB + 288) in OPP. change (8 * Z.of_nat 1) with 8 in OPP.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_intror (or_introl eq_refl))) as VCELL.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ CHr _ _ EBk ltac:(intros c Hc; right; right; exact Hc)) as EBr.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (buf_fresh_apart FB 1024 FRSH ltac:(clear; lia)) as BFA.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    assert (CFBk : crange (hcs asegs R HIA hk) FB 1024) by (exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))).
    assert (SCSk : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP SP1. lia. }
    assert (SSk : sshad asegs AL mk slo (bv_unsigned sp)).
    { eapply (presA_sshad asegs R); [exact (presW_presA asegs R HIA hk LB LF _ _ _ m mk PRES)| exact SSH| exact SLOK|].
      pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTk. clear - HTk TOP ETk ESk. lia. }
    assert (OLEN : aobj asegs AL (hcs asegs R HIA hk) mk (sp1 - 48) 8).
    { pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
      eapply (aobj_sshad8 _ mk slo (bv_unsigned sp)); [exact CSOKk| exact SSk| clear - SLOL SLO SP1 SLO1 NER NEEDR; lia| clear - SP1; lia
      | clear - SP1M; Z.div_mod_to_equations; lia| clear - ACP ALO LOS SLO SP1 SLO1 NER NEEDR; lia
      | eapply crange_sub; [exact SCSk| clear - SLO SP1 SLO1 NER NEEDR; lia| clear; lia]]. }
    assert (OVP : aobj asegs AL (hcs asegs R HIA hk) mk (FB + 352) 4).
    { eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA hk) mk FB EP_SH_P (FB + 352) 44 4 CSOKk FSH);
        [eapply crange_sub; [exact CFBk| clear; lia| clear; lia]| exact F8| clear - F0; lia| clear; lia| clear; lia| exact shp_ver]. }
    pose proof VCELL as VC. chunk_split VC 1%nat VC1 VC2.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof HGINT as SP. unfold asn1_get_int_stmtA in SP.
      eapply SP with (CS := hcs asegs R HIA hk) (PP := FB + 288) (VALP := FB + 352) (P := P) (END := PEND) (BUF := BUF) (bs := bs) (lo := lo) (valv := vw);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact PCELL | exact VC1 | exact HBSk | exact MIk | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk)
              | exact (hm_abase asegs R HIA hk LBk LF' mk HHk) | exact OPP | exact OVP | exact OLEN | exact OBUFk | exact STb | exact SCSk | exact BUF0 | exact BP | exact PL | reflexivity
              | lazymatch goal with
                | |- P <= PEND => clear - LEN0; lia
                | |- BUF + _ < 2^63 => clear - B47; lia
                | |- _ mod 8 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- _ mod 4 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < FB + _ => clear - F0; lia
                | |- alloc_ceiling <= lo => clear - ALO LOS; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ \/ _ => clear - BFA FBLO DSB SP1 SLO1 NER NEEDR; lia
                end
              | match goal with |- ?g => idtac "GINT-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold asn1_get_int_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & r & p' & vw2 & E & MU2 & WM2 & MI2 & EA0 & RR2 & PC2 & VC2' & ST2 & PB2 & ROK). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R. subst y3.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    pose proof (eb_munchF hk LBk mk v f _ _ CHr _ _ m2 [(FB + 288, FB + 288 + 8); (FB + 352, FB + 352 + 4)] (sp1 - 64) EBr MU2 ltac:(clear - SLO SP1 SLO1 NER NEEDR; lia)
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]]) WM2 MI2 ST2 HCD) as EB2.
    assert (VCELL2 : rw_cells asegs m2 (FB + 352) [C4 vw2; C4 vw']).
    { pose proof (rw_cells_transport asegs _ mk m2 _ _ VC2 MU2 WM2
                    ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FBLO SP1 SLO1 NER NEEDR; lia)) as VC2t.
      chunk_join VC2' VC2t VJ. exact VJ. }
    eapply CONT; [| | exact PB2| exact RR2| intros _; exact I].
    - eapply eb_ch_add; [eapply eb_ch_add; [exact EB2| exact VCELL2| clear; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| exact PC2| clear; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia].
    - eapply (tmp_ok_own hk LBk mk m2 _ _ HHk TOK MU2 WM2 MIk MI2).
      + apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_cons; [right; right; cbn [fst snd]; clear - SLO1 NER NEEDR SP1; lia| apply Forall_nil]]].
      + intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
        cbn [disjoint_from app]. split; [clear - XB1; lia| split; [clear - XB1; lia| split; [clear - XB1 XB2 FBLO SLO1 NER NEEDR; lia| exact I]]].
    all: match goal with |- ?g => idtac "GINT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)



  #[using="Type"] Lemma shp0_gid : cell_at EP_SH0 78 = Some (C1 (Z_to_bv 8 4)).
  Proof. reflexivity. Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@L10515057222.4  L13270761728.274L14674883745.0  L15402558120.1  L16587152252.7  L19350634907.18 L19350864283.18 L19355338801.14 L1954509542.4   L19635281963.1  L19980016842.7  L20609655761.14 L20613147259.18 L20613311099.18 L23735153128.7  L24279760399.2  L24758909370.1  L25069483149.10 L25520894618.17 L29010568859.249L29392378332.17 L32497426948.6  L32586543723.0  L35668120898.7  L36586955419.1  L38235734261.1  L38551529394.0  L40927788160.9  L41472189527.10 L45249562219.6  L52798555062.2  L52920977579.1  L53958213612.6  L53958508524.4  L55588686165.0  L55607612363.18 L55830939759.1  L5697132701.4   L58065817182.17 L59308549093.1  L59309005011.1  L60098763854.3  L60818856973.17 L63216281462.7  L64933133993.0  L65562438374.1  L66151426447.10 L66151427842.16 L957827166.0    L9631767084.2   L978485628.17   00000?01g01h01l02902:02;02<02K02O02g02h02i02j03703>03B03R03a03b03n04D04E04\04`04d04e05@05^06306;06?06@06N06O07>07B07C07\07`07a07k08;08L08M08Q08b09D09E09L0:MS3LEN1v2VB4PSG0S2LF2sp3PKA3PAR2FB3sp13LFB2bs2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL2xsSS2FBS3LEN2bs4LEN0FFFS1P3BUF4BUF02BPS2FBS1R3HIA1h2sp3TOP3sp13SP1FFFS1P2bs3BUF2BPS2FB2F0S2FBS2lo2FB3sp14FBLOS2FB3LEN1P4DFPWFS3PAR2FB3PFAS1R2sp2lo3sp13SP14SLOBSS1R3HIA1h2sp2lo3TOP3HT0S2FBS2loSS2FB3LEN1P2bs3BUF2BP2PL3BFAS2sp2lo3LEN1P2bs3BUF3DSB2BP2PLS3LEN1P2bs3BUF3B472PLS2gv3INVS2FBFS1d1f3FB'4FSG0SS1C5idpad2pP2pA2pB2pX2pY2pZ2pN4hpad2qd2qX2qY2qZS2FBSS2sp3PAR2lo3sp13SP15DSPARS2NFFS1R2lo3LOSS2lo2FB3sp14FBLOS3LEN1P2bs3BUF2PLSS2FBS1r3RR22r02KG1q1HS2FB2r02F81q1r1H2H02q02H43sp14SP1MSS2FB2F0S1R5NEEDR2sp3PAR2lo2FB3sp13SP13LEN1P5DSPAR4DSPW3PFA4FBLO4SLO13NER". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H P pd bs LEN0 HPAR0 ALPAR NZPAR OPAR0 CRPAR DSPAR DPARI SLOB HOG BUF HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL BSNE"] Lemma named_walk : NAMED_stmt.
  Proof.
    unfold NAMED_stmt. intros _. intros until s11v. intros EBk VB FB'.
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EBk) as (HBSk & OBUFk & CRBk).
    pose proof (buf_fresh_apart FB 1024 FRSH ltac:(clear; lia)) as BFA.
    set (xs := firstn (Z.to_nat LEN) (skipn (Z.to_nat (P - BUF)) bs)).
    assert (LENX : Z.of_nat (length xs) = LEN) by (subst xs; apply P_asn1_get_mpi.bytes_at_sub_length; clear - BP PL LEN0; lia).
    assert (HXS : bytes_at asegs mk P xs) by (subst xs; eapply P_asn1_get_mpi.bytes_at_sub; [exact HBSk| | |]; clear - BP PL LEN0; lia).
    clearbody xs.
    assert (OPW : aobj asegs AL (hcs asegs R HIA hk) mk P LEN) by (eapply aobj_sub; [exact OBUFk| exact BP| exact PL]).
    assert (P0 : 0 < P) by (clear - BUF0 BP; lia).
    assert (P47' : P + LEN + 8 <= 2^47) by (clear - B47 PL; lia).
    assert (DSPW : P + LEN <= lo \/ bv_unsigned sp <= P) by (clear - DSB BP PL LEN0; lia).
    assert (DFPW : P + LEN <= FB \/ FB + 1024 <= P) by (clear - BFA BP PL LEN0; lia).
    destruct (eb_par _ _ _ _ _ _ _ _ _ EBk) as (HPARk & OPARk).
    pose proof par_frame_apart as PFA.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as GCELL.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ ([] : list (Z * list cell)) _ _ EBk ltac:(intros c Hc; destruct Hc)) as EBr.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    assert (CFBk : crange (hcs asegs R HIA hk) FB 1024) by (exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))).
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    assert (OEXT : aobj asegs AL (hcs asegs R HIA hk) mk (FB + 624) 4).
    { eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA hk) mk FB EP_SH0 (FB + 624) 78 4 CSOKk FSH);
        [eapply crange_sub; [exact CFBk| clear; lia| clear; lia]| exact F8| clear - F0; lia| clear; lia| clear; lia| exact shp0_gid]. }
    pose proof GCELL as GC. chunk_split GC 1%nat GC1 GC2.
    (* [comment removed for export] *)
    do 3 zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof HOG as SP. unfold oid_lookup1v_stmtA in SP.
      eapply SP with (h := hk) (LB := LBk) (LF := LF') (OID := PAR) (EXT := FB + 624) (P := P) (LEN := LEN) (lo := lo) (xs := xs) (tg := tg) (pd := pd) (v0 := gj);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHk | exact HPARk | exact HXS | exact LENX | exact GC1 | exact STb | exact LOS | exact MIk | exact OPARk | exact OPW | exact OEXT | exact ALPAR | exact NZPAR | exact P0 | exact P47' | reflexivity
              | lazymatch goal with
                | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia]
                | |- _ mod 4 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < FB + _ => clear - F0; lia
                | |- lo <= _ => clear - SLOB SP1; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ \/ _ => clear - PFA DFPW DSPW DSPAR FBLO SP1 SLO1 NER NEEDR; lia
                end
              | match goal with |- ?g => idtac "OG-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold oid_lookup1v_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya0 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & r & gv & E & MU2 & WM2 & MI2 & EA0 & RR2 & GC2' & VR & ST2 & HH2). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R. subst ya0.
    replace (ret_pc (Z_to_bv 64 0xb0dc0)) with (Z_to_bv 64 0xb0dc0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (eb_munchF hk LBk mk v f _ _ _ _ _ m2 [(FB + 624, FB + 624 + 4)] lo EBr MU2 ltac:(clear; lia)
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) WM2 MI2 ST2 ltac:(apply Forall_nil)) as EB2r.
    assert (GCELL2 : rw_cells asegs m2 (FB + 624) [C4 gv; C4 gj']).
    { pose proof (rw_cells_transport asegs _ mk m2 _ _ GC2 MU2 WM2
                    ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FBLO SP1 SLO1 NER NEEDR; lia)) as GC2t.
      chunk_join GC2' GC2t GJ. exact GJ. }
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB2r GCELL2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB2.
    clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb PRES CHk EXTk FRk LAWS KINV MU WM SCSk CSOKk CFBk OEXT GC1 GC2 GCELL EBr EB2r HPARk OPARk. try clear MIk. try clear IDSk. clear w0 w1 w2.
    pose proof EB2 as EBk. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KG; zify_cond KG.
    - (* [comment removed for export] *)
      assert (Z0 : r = 0) by (unfold P_oid.MBEDTLS_ERR_OID_NOT_FOUND in RR2; clear - KG RR2; Z.div_mod_to_equations; lia). subst r.
      destruct VR as [[NF _]|[_ INV]]; [exfalso; unfold P_oid.MBEDTLS_ERR_OID_NOT_FOUND in NF; clear - NF; lia|].
      assert (GVB : 0 <= bv_unsigned gv < 2^31) by (unfold OID_EC_GRP_VALS in INV; cbn [In] in INV; clear - INV; lia).
      rewrite <- (Z_to_bv_bv_unsigned gv) in EB2.
      eapply (ep_setgrp hk LBk m2 v f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned gv) gj'); [exact EB2| exact GVB| exact VB| exact FB'].
    - (* [comment removed for export] *)
      do 3 zstep.
      replace (Z_to_bv 64 18446744073709536768) with (Z_to_bv 64 (-14848)) by (apply bv_eq; reflexivity).
      destruct (eb_entry_objs _ _ _ _ _ _ _ _ _ EB2) as (_ & _ & KP2 & _ & _).
      assert (PSG0 : 0 <= pk_set_group_PHI) by (unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
      assert (FSG0 : 0 <= pk_set_group_FR) by (unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia).
      eapply (ep_exit hk LBk m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-14848) (kp_grp KPI) [] W0 _);
        first [ exact EB2 | (left; reflexivity) | exact KP2 | reflexivity | (clear - VB PSG0; lia) | (clear - FB' FSG0; lia) | (clear; lia)
              | (right; split; [clear; lia| split; reflexivity])
              | (intros R0; exfalso; clear - R0; lia)
              | idtac ].
      intros d1 d2 H1 H2 NE O1 O2. exfalso. rewrite (grp_init_noheap _ _ _ _ _ _ _ _ _ _ d1 H1) in O1. discriminate O1.
    all: match goal with |- ?g => idtac "NAMED-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.

  (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_EP.
  Hypothesis SM4 : arl_smalloc R 4 = A_SMALLOC_4_EP.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis SF5 : arl_setf5 R = 0x6b330.
  Hypothesis NSH : arl_need_setsh R <= arl_need_rt R.
  Hypothesis MCI : arl_memcmp_i R = 0x58704.
  Hypothesis NEEDB : 0 <= arl_need_bcmp R.
  Hypothesis IDSN : AImgGlobals.img_norz IDS 56 = true.
  Hypothesis HSG : pk_ecc_set_group_stmtA asegs R HIA A_MT A_CA A_ONE A_EC_INFOS A_PK_ECC_SET_GROUP.
  Hypothesis MFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Hypothesis PFREE : ecp_point_free_stmtA asegs R HIA A_ECP_POINT_FREE.
  Hypothesis HGF : ecp_group_free_stmtA asegs R HIA A_MT A_ECP_GROUP_FREE.
  Hypothesis HGL : ecp_group_load_stmtA asegs R HIA A_MT A_CA A_ONE A_ECP_GROUP_LOAD_E.
  Hypothesis HGI : ecp_group_init_stmtA asegs R HIA A_MT A_ECP_GROUP_INIT.
  Hypothesis HIDL : ecp_grp_id_list_stmtA asegs AL A_ECP_GRP_ID_LIST IDONE IDS.
  Hypothesis HRB : mpi_read_binary_stmtA_c asegs R HIA A_MPI_READ_BINARY.
  Hypothesis HGM : asn1_get_mpi_stmtA_c asegs R HIA A_ASN1_GET_MPI A_MPI_READ_BINARY.
  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis HGT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis HOG : oid_lookup1v_stmtA asegs R HIA A_OID_GET_EC_GRP 64 OID_EC_GRP_VALS.
  Hypothesis HGINT : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.


  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L14453869904.3L1954509542.4 L22246631052.5L24239607029.0L27348384304.4L2755080032.0 L45249267831.5L45249562219.6L59321329636.300000@00O00b00c01001101201G01RS3PAR5NZPAR4PARBS1P3BUF4BUF02BPS3LEN1P3BUF4BUF02BPSS1R2sp2lo3SLOSFS3LEN1P3BUF2bs3B472PLS2bs1K4BSNE". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK UARG SM4 NS1 SF5 NSH MCI IDSN HSG MFREE PFREE HGF HGL HGI HIDL HRB HGM HLSET HGT HOG HGINT"] Theorem pk_use_ecparams_spec_s : pk_use_ecparams_stmtA asegs R HIA A_MT A_CA A_ONE A_EC_INFOS IDONE IDS A_PK_USE_ECPARAMS.
  Proof.
    unfold pk_use_ecparams_stmtA. intros until qZ. cbv zeta.
    intros HH HK0 LFB HPKA ALP NZP EI OPKA CRP DSP DPC DPI KP INC HPAR ALPAR NZPAR OPAR CRPAR DSPAR DPARC DPARI HBS BUF0 B47 CRB DSB DBC DBI OBUF BSNE HBD LEN0 IDS0 _
           ST LOS SLO SLOB slo SSH SLOK SLOL TOP SPA TPV MI RA BUD UWC BUDF C24H -> ->.
    unfold ECP_KEYPAIR_SIZE in *.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UWC) as D0.
    pose proof (rw_cells_bound _ _ _ _ HPAR) as PARB. cbn [cells_size csize Nat.add buf_cells] in PARB.
    assert (SLO' : lo <= bv_unsigned sp - 640 - arl_need_ecp R) by (clear - SLO; lia).
    assert (OBUF' : aobj asegs (arl_AL R) (hcs asegs R HIA h) m BUF (Z.of_nat (length bs))) by (destruct OBUF as [K|K]; [exfalso; clear - K BSNE; lia| exact K]).
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (A_pk_ecparams_A.pro_walk R HIA IMG UARG SM4 NS1 NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PKA PAR lo);
        first [ eassumption | (clear - PARB NZPAR; lia) | match goal with |- ?g => idtac "PRO-LEFT:" g end ]. }
    intros ms1 S1. unfold A_pk_ecparams_A.S1P in S1.
    ddestruct S1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & w0 & w1 & w2 & jref & jgrp & jslots & pj & lj & vj & vj' & gj & gj'
                    & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & REF1 & PC1 & LC1 & VC1 & GRP1 & GID1 & FSH1 & FSHR1
                    & SAVE1 & SLOT1 & STlo1 & SThi1 & STb1 & MI1 & PRES0).
    subst ms1.
    apply (aevtA_KF_switch R HIA h h1 mo _ _ HKI).
    assert (CFB : crange (hcs asegs R HIA h) FB 1024) by (rewrite <- Ehcs; exact (hcs_fake asegs R HIA h1 LB _ m1 FB 1024 HH1 ltac:(left; reflexivity))).
    destruct HBD as [(P0 & L0 & TG0) | (BP & PL)].
    - (* [comment removed for export] *)
      subst P LEN tg.
      eapply body_walk with (Wok := False) (P := 0);
        first [ eassumption
              | (eapply sp_getint_empty; first [eassumption | reflexivity | (clear; lia)])
              | (unfold F1C_stmt; intros; exfalso; assumption)
              | (unfold NAMED_stmt; intros TGN; exfalso; apply TGN; reflexivity)
              | (clear; lia)
              | match goal with |- ?g => idtac "MAIN0-LEFT:" g end ].
    - eapply body_walk with (Wok := True) (P := P);
        first [ eassumption
              | (eapply sp_getint; first [eassumption | (clear - BUF0 BP; lia) | (clear - B47 PL; lia)])
              | (unfold F1C_stmt; intros until s10v; intros _; eapply stageF1; eassumption)
              | (eapply named_walk with (P := P); first [eassumption | (clear - BUF0 BP; lia) | (clear - B47 PL; lia)])
              | (clear - BUF0 BP; lia) | (clear - B47 PL; lia)
              | match goal with |- ?g => idtac "MAIN1-LEFT:" g end ].
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WalkEP.


(* [comment removed for export] *)
Theorem A_pk_use_ecparams_spec : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_E ()) "PR,$0.PHIA,(1.$2.R1.)PIDONE,$?.PIDS,$?.P,(61.(1;.R4.))P,(2>.=(62.R5.))P,(17.(2>.(63.(64.R6.))(65.(64.R6.)))(2>.(66.(64.R6.))(67.(64.R6.))))P,Ph,(3.$2.R7.R6.)PLB,(;.$<.)PLF,(;.$<.)Pm,P,(=.&40.)(>.(=.&8.))P,(54.$2.R;.R:.R4.R3.R2.R1.)(68.$?.(69.(11.$?.$?.)$?.(2:.$?.$?.)R4.))P,(31.$?.(6:.R8.)$6;.)P,(31.$?.(6<.R9.+4.)$6=.)P,(2>.=(6>.R:.))P,(31.$?.(6?.R;.)+6;330.)P,(2>.(70.R<.)(62.R<.))P,(31.$?.(71.R=.)+58704.)P,(31.$72.(73.R;.+38.)$74.)P,(75.$2.R?.R>.$1>.$34.$35.$76.$77.)P,(78.$2.R10.R?.$79.)P,(7:.$2.R11.R10.$7;.)P,(7<.$2.R12.R11.$1>.$7=.)P,(7>.$2.R13.R12.$1>.$34.$35.$7?.)P,(80.$2.R14.R13.$1>.$81.)P,(82.$2.(1;.R15.)$83.R13.R12.)P,(84.$2.R16.R15.$85.)P,(86.$2.R17.R16.$87.$85.)P,(88.$2.R18.R17.$89.)P,(8:.$2.(1;.R19.)$8;.)P,(8<.$2.R1:.R19.$8=.+40.$8>.)P,(8?.(64.R1;.)$2.(1;.R1;.)$3;.)(90.$2.R1<.R1;.$1>.$34.$35.$76.R1:.R19.$91.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IDONE IDS IMG NEEDR DIMG HND UARG SM4 NS1 SF5 NSH MCI IDSN HSG MFREE PFREE HGF HGL HGI HIDL HRB HGM HLSET HGT HOG HGINT.
  unfold pk_use_ecparams_stmtA. intros until qZ. cbv zeta.
  intros HH HK0 LFB HPKA ALP NZP EI OPKA CRP DSP DPC DPI KP INC HPAR ALPAR NZPAR OPAR CRPAR DSPAR DPARC DPARI HBS BUF0 B47 CRB DSB DBC DBI OBUF BSNE HBD LEN0 IDS0 IDOK.
  pose proof (pk_use_ecparams_spec_s R HIA IMG NEEDR DIMG HND IDONE IDS IDOK UARG SM4 NS1 SF5 NSH MCI IDSN HSG MFREE PFREE HGF HGL HGI HIDL HRB HGM HLSET HGT HOG HGINT) as S.
  unfold pk_use_ecparams_stmtA in S.
  eapply S; eassumption.
Qed.

(* [comment removed for export] *)
Definition pk_use_ecparams_spec := A_pk_use_ecparams_spec.
