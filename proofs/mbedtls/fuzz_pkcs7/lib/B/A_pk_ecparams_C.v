(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_ecp_point_free P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_ecp_grp_id_list P_ecp_mul_mod P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_defs A_pk_defs A_mpi_free A_mpi_lset A_mpi_bitlen A_mpi_cmp_mpi A_asn1_get_tag_stmt A_asn1_get_int_loops A_asn1_get_mpi A_oid A_oid_ec_grp A_ecp_group_init A_ecp_group_free A_ecp_point_free A_ecp_grp_id_list A_pk_ecparams_aux A_free_seq A_pk_ecc_set_group A_pk_ecc_set_pubkey A_ecp_grp_facts A_pk_tmp A_pk_ecparams_stmt A_pk_ecparams_A A_pk_ecparams_B.
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
Ltac2 gd_tbl_A_pk_ecparams_C () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_B.EB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.and"; "WalkEP.Call.EP_SH_GR"; "WalkEP.Call.SLL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_load.gl_result"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_grp_id_list.ecp_ids_bytes"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "WalkEP.Call.LINV"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.GF_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.GF_FR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_FR"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_zero"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_use_ecparams_postA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.A_ECP_GROUP_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.group_load_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.group_load_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_GROUP_LOAD_E"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Lists.ListDef.Forall"; "WalkEP.Call.own_iv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_grp_id_list.ecp_ids_state"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.P.P_pk_ecparams_D.IDWS"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_FR"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "WalkEP.Call.cmp_opnd"; "Stdlib.ZArith.BinInt.Z.sgn"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi.A_MPI_CMP_MPI_E"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.A_MPI_GET_BIT_Q"; "WalkEP.Call.LST"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_B.wx_fresh"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.lb_ext"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "WalkEP.Call.data_iv"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_B.EP_SH_G"].



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

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L12128799109.1L2333536794.13L36359398762.5L4800287082.3 L6203936179.1 L66668349941.1L900258061.9  00000300_01101;01@01C01eS1fS1R3HIA1h2sp2lo3LOS3TOP3sp13SP13lo'3LO'1a2HaS1R2lo3LOS3lo'3LO'S1R3HIA2hkS3sp1S1vS1R3HIA1h2sp3TOP3sp13SP13lo'5HTOP0". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 F64 FRSH"] Lemma eb_scratch : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pm2,P,(4.&40.)(5.(4.&8.))Plo',$6.P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(;.(<.(8.$6.$6.)(=.$6.$6.R2.Vsp1,)(>.(8.$6.$6.)))R;.R3.)P,(?.Vlo,R3.)P,(10.$1.R=.R5.)P,(11.$1.R6.)P,(12.$1.R7.Vlo,Vsp1,)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R12.R11.R8.R?.R>.R=.R<.R;.R:.R9.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE m2 lo' EBk MU LO' WM MI2 ST2.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTOPk. rewrite ETk, ESk in HTOPk.
    pose proof (hm_top asegs R HIA h _ _ _ HH0) as HTOP0.
    assert (HH2 : HM asegs R HIA hk LBk LF' m2).
    { eapply (hm_munch asegs R HIA hk LBk LF' [(lo', sp1)] mk m2 HHk MU WM).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite ETk. clear - Ha LOS LO' TOP SP1. lia. }
    assert (HP : presA asegs R LBk LF' sp1 (arl_stklo R) (hstkhi asegs R HIA hk) [] mk m2).
    { eapply (presA_drop_below asegs R HIA hk LBk LF' [] lo' sp1 mk mk m2 sp1 HHk); [| clear; lia| clear - LOS LO'; lia].
      eapply (presA_of_munch asegs R LBk LF' _ _ _ _ mk m2 (hcs asegs R HIA hk) (hcs_ok asegs R HIA hk)); [| | exact MU| exact WM].
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS LO'; lia| rewrite ESk; clear - HTOP0 TOP SP1; lia].
      - intros c0 Hc. eapply cshd_hcs; [exact HHk| apply Z.le_refl| exact Hc]. }
    pose proof (eb_step hk LBk mk v f SH SL CH T WE hk LBk m2 0 0 T LBk [] [] WE EBk0 HH2 MI2 ST2 HP eq_refl eq_refl eq_refl
                  ltac:(intros x Hx; exact Hx) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb])
                  ltac:(apply Forall_nil) ltac:(intros x _; exact I) ltac:(intros x Hx; exact Hx)
                  ltac:(apply Forall_nil) I I ltac:(apply Forall_nil)
                  ltac:(rewrite Forall_forall; intros ac _; exact I) EXTk FRk) as E2.
    replace (v + 0) with v in E2 by (clear; lia). replace (f + 0) with f in E2 by (clear; lia). exact E2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HGF : ecp_group_free_stmtA asegs R HIA A_MT A_ECP_GROUP_FREE.
  Hypothesis HGL : ecp_group_load_stmtA asegs R HIA A_MT A_CA A_ONE A_ECP_GROUP_LOAD_E.
  Hypothesis IDSN : AImgGlobals.img_norz IDS 56 = true.

  Local Notation REF := (FB + 32).
  Local Notation DS7 dN dP dA dB dX dY dZ := ([dN; dP; dA; dB; dX; dY; dZ] : list mpd) (only parsing).

  (* [comment removed for export] *)
  Definition EP_SH_GR : list cell := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "(<.$7.(13.(14.&8.+?1.))(<.$7.(13.(14.&8.+?1.))(<.$7.(13.(14.&8.+?1.))(<.$7.(13.(14.&8.+?1.))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?8.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?8.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?8.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.=))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+?2.))(<.$7.(13.(14.&8.+4.))(<.$7.(13.(14.&8.+?3.))(>.$7.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition SLL (v16 v17 v18 : word) : list cell := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "(<.$7.(15.(14.&40.(16.VFB,+1;8.)))(<.$7.(15.(14.&40.(16.VFB,+78.)))(<.$7.(15.(14.&40.(16.VFB,+1<8.)))(<.$7.(15.(14.&40.(16.VFB,+58.)))(<.$7.(15.(14.&40.(16.VFB,+88.)))(<.$7.(15.(14.&40.(16.VFB,+48.)))(<.$7.(15.(14.&40.(16.VFB,+38.)))(<.$7.(15.(14.&40.(16.VFB,+28.)))(<.$7.(15.(14.&40.(16.VFB,+1=8.)))(<.$7.(15.(14.&40.(16.VFB,+1:8.)))(<.$7.(15.(14.&40.VPKA,))(<.$7.(15.(14.&40.(16.VFB,+198.)))(<.$7.(15.(14.&40.(16.VFB,+188.)))(<.$7.(15.(14.&40.(16.VFB,+270.)))(<.$7.(15.(14.&40.(16.VFB,+178.)))(<.$7.(15.O3.)(<.$7.(15.O2.)(<.$7.(15.O1.)(>.$7.)))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition LINV (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (v f : Z) (gref : ecp_grp) (idg rg : Z)
      (dN dP dA dB dX dY dZ : mpd) (v16 v17 v18 gid gj' pb nb : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "(17.(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,O16.O15.O14.O13.O12.$18.(19.O7.O6.O5.)(<.(8.$6.(2.$7.))(=.$6.(2.$7.)(16.VFB,+270.)(<.$7.(1:.O4.)(<.$7.(1:.O3.)(>.$7.))))(<.(8.$6.(2.$7.))(=.$6.(2.$7.)(16.VFB,+1>8.)(<.$7.(15.O2.)(<.$7.(15.O1.)(>.$7.))))(>.(8.$6.(2.$7.)))))(1;.$3.(1<.(<.$1=.O>.(<.$1=.O=.(<.$1=.O<.(<.$1=.O;.(<.$1=.O:.(<.$1=.O9.(<.$1=.O8.(>.$1=.)))))))))(1>.O11.))(<.(8.$6.$6.)(=.$6.$6.VIDONE,(16.VIDONE,+1.))(<.(8.$6.$6.)(=.$6.$6.VIDS,(16.VIDS,+38.))(>.(8.$6.$6.)))))(17.(1?.$1.O14.O15.(16.VFB,+170.)+<0.(<.$1=.O>.(<.$1=.O=.(<.$1=.O<.(<.$1=.O;.(<.$1=.O:.(<.$1=.O9.(<.$1=.O8.(>.$1=.)))))))))(17.(20.$6.(21.O>.)(16.(16.VFB,+170.)+68.))(17.(20.$6.(21.O=.)(16.(16.VFB,+170.)+8.))(17.(20.$6.(21.O<.)(16.(16.VFB,+170.)+18.))(17.(20.$6.(21.O;.)(16.(16.VFB,+170.)+28.))(17.(20.$6.(21.O:.)(16.(16.VFB,+170.)+38.))(17.(20.$6.(21.O9.)(16.(16.VFB,+170.)+48.))(17.(20.$6.(21.O8.)(16.(16.VFB,+170.)+58.))(17.Pb,$3.P,(22.$3.R1.(1>.O11.))(23.(22.$3.R2.(1<.(<.$1=.O>.(<.$1=.O=.(<.$1=.O<.(<.$1=.O;.(<.$1=.O:.(<.$1=.O9.(<.$1=.O8.(>.$1=.)))))))))))(17.(24.$1.$25.O14.O15.(16.VFB,+20.)O11.)(17.(26.(27.O11.))(17.(28.$29.$2:.O10.(16.VFB,+20.)O?.O11.(1>.O11.))(17.(2;.$1.O14.VIDS,(<.$7.(2<.#38.$2=.)(>.$7.)))(17.(?.(2>.O15.)(16.(2>.VLB,)+5.))(2;.$1.O14.Vsp1,(<.$7.(15.(14.&40.(16.VFB,+68.)))(>.$7.))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2793096253.3 L52792927696.800000:00US3IDS1a2HaS1R5IDONE3IDS2I12I22I31a2Ha". (* [comment removed for export] *)
  #[using="IDONE IDOK"] Lemma idsb_presA : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "PLBp,(2.$3.)PLFx,(2.$3.)PSPx,$6.PSSPx,$6.PTOPx,$6.PWX,(2.$9.)Pma,P,(4.&40.)(5.(4.&8.))Pmb,P,(4.&40.)(5.(4.&8.))P,(2;.$1.R2.VIDS,(<.$7.(2<.#38.$2=.)(>.$7.)))P,(2?.$1.VR,R9.R8.R7.R6.R5.R4.R3.R2.)P,(30.R5.VIDS,+38.)(2;.$1.R4.VIDS,(<.$7.(2<.#38.$2=.)(>.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros LBp LFx SPx SSPx TOPx WX ma mb H2 HP D2. ddestruct IDOK as (I1 & I2 & I3 & I4 & _).
    eapply (presA_rw_cells asegs R); [exact HP| exact H2| | exact D2].
    intros a Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. right; left. split; [clear - Ha I1 I2 I3; lia| apply I4; right; clear - Ha; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma grp_zero_apart : forall A, mpds_apart (grp_mpds (grp_zero A)).
  Proof.
    intros A d1 d2 Q1 Q2 NE O1 O2. exfalso. revert Q1 O1. unfold grp_mpds, grp_zero.
    cbn [g_P g_A g_B g_G g_N pt_mpds pt_zero pt_X pt_Y pt_Z app In]. unfold mpd_zero.
    intros Q1 O1. decompose [or] Q1; subst; cbn in O1; try discriminate; contradiction.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L27830289819.1L59308586248.2L63667055128.000000400:00;S2FBS1i2HiS". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO SP1 F64 FRSH"] Lemma ref_aobj : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R9.R8.R7.R6.R5.$18.R4.R3.R2.R1.)(31.$1.(32.VR,)(33.$1.VR,VHIA,R:.)R8.(16.VFB,+20.)+<0.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SL CH T WE EBk. ddestruct EBk as (HHq & _ & _ & _ & _ & (FSHq & _) & _).
    change 192 with (8 * Z.of_nat 24).
    eapply (sh_aobj hk mk EP_SH_GR REF 4 24); [exact FSHq| exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHq ltac:(left; reflexivity))| clear; lia| clear; lia|].
    intros i Hi. unfold EP_SH_GR. do 24 (destruct i as [|i]; [reflexivity|]). exfalso. clear - Hi. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10383309542.1 L10596430123.1 L14648452628.6 L18140531390.9 L18794210039.1 L19980016842.7 L21358962534.1 L24264274256.3 L25897709499.9 L29294044996.1 L30410547336.1 L31985820203.8 L32454903270.1 L39280637297.0 L39738753993.3 L45379288988.10L52149871223.1 L52736311528.1 L57885184943.1 L5933138620.4  L6203936179.1  L635024086.1   L66151427842.16L6897470952.1  L8134657482.6  00000400800K00h00l01D01H01T02102402802T02X02Y02a03B03F03J03N03X03]03`04<04@04TS2FBS2FBS1R2lo3sp14SLO13NERS1R3HIA1h3LEN3BUD2hk1v3HVk2VBS2FBS1R3HIA1h2sp3TOP3sp13SP1S2FBS2lo2FB4FBLOS1R3HIA1h1d4BUDF2hk1f3HFk3FB'S1xS2FBS1R5IDONE3IDS2FB2F22I12I22I3S2FBSS2FB1x1KS1R5NEEDR2lo2FB3sp14FBLO4SLO13NERS2FBS2FBS2FBS2FB1x3XB1S3sp1S1xS3sp12r04SP1M1q1r1H2H02q02H4S2FBS2LB3LBk4C24k3LBf2CI". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO TOP TPV SP1 SP1M F64 FRSH BUD BUDF HGF"] Lemma linv_gfree : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(35.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(17.(?.=R1<.)(36.R1<.(37.+2.+40.)))P,(20.$6.(38.R1=.+2.)=)P,(?.(16.R31.$39.)(3:.VLEN,))P,(?.(16.R31.(3;.=))(3<.Vd,))P,Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py3,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(35.R12.R11.R10.(16.R45.$39.)(16.R44.(3;.=))(3=.(16.VFB,+20.))+9.$3>.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)(3?.$1.(40.$1.VR,VHIA,R13.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R33.)(14.&40.Vsp1,)Vgp,Vtp,R10.R?.R>.R2?.R2>.R=.R<.R;.R:.R9.R8.R7.R6.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R5.R4.R3.R2.)VF,(14.&40.R33.)Vfc,(45.(4.&40.))R11.(46.$1.)))(3?.$1.(40.$1.VR,VHIA,R37.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R21.)(14.&40.Vsp1,)Vgp,Vtp,R20.R1?.R1>.R1=.R1<.(14.&40.(16.VFB,+20.))R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(14.&40.$47.)Vfc,(45.(4.&40.))R35.(46.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. (intros dd_H; ddestruct dd_H as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & RT & HG & AP & GL & HIDS & C24k & SLP); intros RETr RETe VB FB' CONT).
    pose proof (ref_aobj _ _ _ _ _ _ _ _ _ EBk) as OREF.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTOPk. rewrite ETk, ESk in HTOPk.
    pose proof (HND _ _ _ _ HHk) as NDk.
    destruct (hm_apart asegs R HIA hk _ _ _ HHk) as [_ BAk].
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    pose proof (P_pk_ecparams_D.gl_free_set _ _ _ _ _ _ _ LBk GL NDk ltac:(intros b Hb; apply (proj2 (proj1 EXTk b)); left; apply in_app_iff; right; exact Hb)) as FS.
    pose proof HGF as SF. unfold ecp_group_free_stmtA in SF.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SF with (h := hk) (LB := LBk) (LF := LF') (A := REF) (g := gref) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold ECP_GROUP_SIZE;
        first [ exact HK1 | exact HHk | exact HG | exact AP | exact STb | exact LOS | exact TPV | exact MIk | exact OREF | reflexivity
              | lazymatch goal with
                | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia]
                | |- _ \/ _ => left; clear - FBLO; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVk VB; lia
                | |- uw_obj _ _ _ _ => eapply (uw_obj_block asegs R HIA hk LBk LF' mk FB 1024); [exact HHk| apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFk FB'; lia
                end
              | match goal with |- ?g => idtac "GF-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold ecp_group_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & HG2 & _).
    rewrite ?(unsigned_lit sp1) in ST2, PXl by exact SP1R. unfold ECP_GROUP_SIZE in PXl.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    set (LBf := grp_free_LB gref LBk) in *.
    assert (EXT2 : lb_ext LB (tmp_blocks (DS7 dN dP dA dB dX dY dZ) ++ grp_blocks (grp_zero REF)) LBf).
    { change (grp_blocks (grp_zero REF)) with (@nil blk). rewrite app_nil_r. destruct EXTk as [E1 E2]. split.
      - intros b. rewrite (FS b), (E1 b), in_app_iff. split.
        + (intros dd_H; ddestruct dd_H as [[[HT'|HR]|HL] NR]); [left; exact HT'| exfalso; exact (NR HR)| right; exact HL].
        + intros [HT'|HL]; [split; [left; left; exact HT'| intros HR; exact (RT _ HR HT')]| split; [right; exact HL| intros HR; apply (E2 b); [apply in_app_iff; right; exact HR| exact HL]]].
      - intros b HT'. apply E2. apply in_app_iff. left. exact HT'. }
    assert (SUBp : forall b, In b LB -> In b LBf) by (intros b Hb; eapply lb_ext_sub; [exact EXT2| exact Hb]).
    assert (FR2 : forall b, In b (tmp_blocks (DS7 dN dP dA dB dX dY dZ) ++ grp_blocks (grp_zero REF)) -> fresh_apart R LB LF (fst b) (snd b)).
    { change (grp_blocks (grp_zero REF)) with (@nil blk). rewrite app_nil_r. intros b Hb. apply FRk. apply in_app_iff. left. exact Hb. }
    assert (EB2 : EB h2 LBf m2 (v + GF_PHI) (f + GF_FR 0) EP_SH_GR (SLL v16 v17 v18) [(FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])]
                     (tmp_blocks (DS7 dN dP dA dB dX dY dZ) ++ grp_blocks (grp_zero REF)) W0).
    { eapply (eb_step hk LBk mk v f _ _ _ _ W0 h2 LBf m2 _ _ _ LBf [(REF, REF + 192)] [] W0);
        [exact EBk0| exact HH2| exact MI2| exact ST2| rewrite app_nil_r; exact PXl| exact HT3| exact HS3| exact HF3| exact HCS3| exact HV3| exact HFR3| exact SUBp
        | apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]
        | intros x _; exact I| intros x Hx; exact Hx| apply Forall_nil| exact I| exact I
        | rewrite app_nil_r; apply Forall_cons; [right; cbn [fst snd]; clear; lia| apply Forall_nil]
        | rewrite app_nil_r; repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]; split; [clear; lia| exact I]|]); apply Forall_nil
        | exact EXT2| exact FR2]. }
    assert (KEEPB : forall x, In x (DS7 dN dP dA dB dX dY dZ) -> md_own x = LHeap -> In (md_p x, 4 * md_n x) LBf /\ In (md_p x, 4 * md_n x) LBk /\ 1 <= md_n x).
    { intros x Hx Ox. pose proof (tmp_ok_in asegs _ _ _ _ _ _ TOK Hx) as MX. destruct (mpd_at_blk_in asegs mk LBk x MX Ox) as (Ix & Nx).
      split; [| split; [exact Ix| exact Nx]]. apply (proj2 (FS _)). split; [exact Ix|].
      intros HR. apply (RT _ HR). apply in_tmp_blocks. exists x. split; [exact Hx|]. rewrite (mpd_blk_heap _ Ox). left; reflexivity. }
    assert (TOK2 : tmp_ok asegs m2 LBf G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_presA asegs L mk m2 LBk LBf G 192 _ sp1 _ (LBf ++ fdata LF'));
        [exact TOK| exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXl)| exact MIk| exact MI2| | |].
      - eapply client_range_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia].
      - intros x Hx. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
        cbn [disjoint_from]. split; [clear - XB1 XB2; lia| exact I].
      - intros x Hx Ox. ddestruct (KEEPB x Hx Ox) as (I1 & I2 & N1). split; [exact I1|].
        split; [eapply client_range_block; [apply in_app_iff; left; exact I1| clear; lia| clear; lia]|].
        cbn [disjoint_from]. split; [| exact I]. destruct (eb_blk_apart hk LBk mk _ _ HHk I2) as [K|K]; clear - K; lia. }
    assert (HIDS2 : rw_cells asegs m2 IDS [CB 56 ecp_ids_bytes]).
    { eapply (idsb_presA _ _ _ _ _ _ mk m2 HIDS PXl). ddestruct IDOK as (I1 & I2 & I3 & _).
      cbn [disjoint_from]. split; [clear - F2 I1 I2 I3; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply CONT.
    split; [exact EB2|]. split; [exact TOK2|].
    split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
    split; [intros b Hb; change (grp_blocks (grp_zero REF)) with (@nil blk) in Hb; destruct Hb|].
    split; [exact HG2|]. split; [apply grp_zero_apart|].
    split; [right; right; right; split; [reflexivity| split; [left; reflexivity| split; [reflexivity| reflexivity]]]|].
    split; [exact HIDS2|]. split; [| eapply (presA_rw_cells asegs R); [exact PXl| exact SLP| apply client_range_stack; clear; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; split; [clear - FBLO SLO1 SP1 NER NEEDR; lia| exact I]]].
    pose proof (nodup_of_fst _ (HND _ _ _ _ HH2)) as ND2.
    pose proof (cnt24_incl LBf LBk ND2 ltac:(intros b Hb; exact (proj1 (proj1 (FS b) Hb)))) as CI. clear - CI C24k. lia.
    all: match goal with |- ?g => idtac "GF-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma gl_cnt24 : forall ca ONE id A r g NB, gl_result ca ONE id A r g NB -> cnt24 NB = 0.
  Proof. intros ca ONE id A r g NB RES. unfold gl_result in RES. decompose [and or ex] RES; subst; reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L10383309542.1 L10596430123.1 L18140531390.9 L18794210039.1 L19726054483.4 L19980016842.7 L20728787551.5 L21204209940.6 L21358962534.1 L24264274256.3 L25897709499.9 L29294044996.1 L30410547336.1 L31985820203.8 L32454903270.1 L39280637297.0 L39738753993.3 L45379288988.10L52149871223.1 L52736311528.1 L57885184943.1 L5933138620.4  L6203936179.1  L635024086.1   L66151427842.16L6897470952.1  00000400800U00Y00k01C01W01f01j02602S02V02Z03603:03;03C03d03h03l04004:04?04B04^04bS2FBS2FBS1R3HIA1h3LEN3BUD2hk1v3HVk2VBS2FBS2LB4C24H3LBk4C24kS1R3HIA1h2sp3TOP3sp13SP1S2LB3LBk4C24k3LB32CIS1R2lo3sp14SLO1S2FBS2lo2FB4FBLOS1R3HIA1h1d4BUDF2hk1f3HFk3FB'S1xS2FBS1R5IDONE3IDS2FB2F22I12I22I3S2FBSS2FB1x1KS1R5NEEDR2lo2FB3sp14FBLO4SLO13NERS2FBS2FBS2FBS2FB1x3XB1S3sp1S1xS3sp12r04SP1M1q1r1H2H02q02H4S2FB". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO TOP TPV SP1 SP1M F64 FRSH BUD BUDF C24H HGL"] Lemma linv_gload : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pid,$6.PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(35.R30.R2?.R2>.R2=.R2<.(3=.(16.VFB,+20.))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(17.(?.=R1<.)(36.R1<.(37.+2.+1?.)))P,(17.(?.=R1<.)(36.R1<.(37.+2.+40.)))P,(20.$6.(38.R1=.+2.)=)P,(?.(16.R31.$48.)(3:.VLEN,))P,(?.(16.R31.(49.=))(3<.Vd,))P,Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))Pr3,$6.Pg3,$34.Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(35.R13.R12.R11.(16.R46.$48.)(16.R45.(49.=))R?.R34.R10.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)(3?.$1.(40.$1.VR,VHIA,R14.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R34.)(14.&40.Vsp1,)Vgp,Vtp,R?.R>.R=.R30.R2?.(14.&40.R11.)R<.R;.R:.R9.R8.R7.R6.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R5.R4.R3.R2.)VF,(14.&40.R34.)Vfc,(45.(4.&40.))R12.(46.$1.)))(3?.$1.(40.$1.VR,VHIA,R37.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R21.)(14.&40.Vsp1,)Vgp,Vtp,R20.R1?.R1>.R1=.R1<.(14.&40.(16.VFB,+20.))(14.&40.R22.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(14.&40.$4:.)Vfc,(45.(4.&40.))R35.(46.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. (intros dd_H; ddestruct dd_H as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & RT & HG & AP & GL & HIDS & C24k & SLP); intros IDB RETr RETe VB FB' CONT).
    pose proof (ref_aobj _ _ _ _ _ _ _ _ _ EBk) as OREF.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTOPk. rewrite ETk, ESk in HTOPk.
    pose proof (HND _ _ _ _ HHk) as NDk.
    destruct (hm_apart asegs R HIA hk _ _ _ HHk) as [_ BAk].
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    change (grp_blocks (grp_zero REF)) with (@nil blk) in EXTk, FRk. rewrite app_nil_r in EXTk, FRk.
    pose proof HGL as SL'. unfold ecp_group_load_stmtA in SL'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SL' with (h := hk) (LB := LBk) (LF := LF') (A := REF) (g := grp_zero REF) (id := id) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold ECP_GROUP_SIZE;
        first [ exact HK1 | exact HHk | exact HG | exact AP | exact STb | exact LOS | exact TPV | exact MIk | exact OREF | exact IDB | reflexivity
              | lazymatch goal with
                | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia]
                | |- _ \/ _ => left; clear - FBLO; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => rewrite unsigned_lit by exact RETr; exact RETe
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVk VB; lia
                | |- uw_obj _ _ _ _ => eapply (uw_obj_block asegs R HIA hk LBk LF' mk FB 1024); [exact HHk| apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFk FB'; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_PK_USE_ECPARAMS in C24H; clear - C24H C24k; lia
                end
              | match goal with |- ?g => idtac "GL-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold ecp_group_load_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & r3 & g3 & NB & LB3 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & LEQ & LNEW & HG3 & AP3 & GB3 & RES & _).
    rewrite ?(unsigned_lit sp1) in ST2, PXl by exact SP1R. unfold ECP_GROUP_SIZE in PXl.
    change (grp_free_LB (grp_zero REF) LBk) with LBk in LEQ, LNEW, PXl.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    subst NB.
    assert (SUBk : forall b, In b LB -> In b LBk) by (intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb]).
    assert (EXT3 : lb_ext LB (tmp_blocks (DS7 dN dP dA dB dX dY dZ) ++ grp_blocks g3) LB3).
    { pose proof EXTk as [E1 E2]. split.
      - intros b. rewrite (LEQ b), (E1 b), in_app_iff. clear. tauto.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (E2 b Hb)|].
        intros HL. apply (proj1 (LNEW b Hb)). apply SUBk. exact HL. }
    assert (FR3 : forall b, In b (tmp_blocks (DS7 dN dP dA dB dX dY dZ) ++ grp_blocks g3) -> fresh_apart R LB LF (fst b) (snd b)).
    { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (FRk b Hb)|].
      destruct (LNEW b Hb) as [_ (G0 & G1 & G2 & G3)]. split; [exact G0|]. split; [exact G1|]. split; [exact G2|].
      intros B j Hj. apply G3. apply in_app_iff in Hj. apply in_app_iff. destruct Hj as [Hj|Hj]; [left; apply SUBk; exact Hj| right; eapply fdata_incl; [| exact Hj]; intros fb Hfb; right; exact Hfb]. }
    assert (EB2 : EB h2 LB3 m2 (v + group_load_PHI) (f + group_load_FRn 0) EP_SH_GR (SLL v16 v17 v18) [(FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])]
                     (tmp_blocks (DS7 dN dP dA dB dX dY dZ) ++ grp_blocks g3) W0).
    { eapply (eb_step hk LBk mk v f _ _ _ _ W0 h2 LB3 m2 _ _ _ LBk [(REF, REF + 192)] [] W0);
        [exact EBk0| exact HH2| exact MI2| exact ST2| rewrite app_nil_r; exact PXl| exact HT3| exact HS3| exact HF3| exact HCS3| exact HV3| exact HFR3| exact SUBk
        | apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]
        | intros x _; exact I| intros x Hx; exact Hx| apply Forall_nil| exact I| exact I
        | rewrite app_nil_r; apply Forall_cons; [right; cbn [fst snd]; clear; lia| apply Forall_nil]
        | rewrite app_nil_r; repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]; split; [clear; lia| exact I]|]); apply Forall_nil
        | exact EXT3| exact FR3]. }
    assert (TOK2 : tmp_ok asegs m2 LB3 G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_presA asegs L mk m2 LBk LB3 G 192 _ sp1 _ (LBk ++ fdata LF'));
        [exact TOK| exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXl)| exact MIk| exact MI2| | |].
      - eapply client_range_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia].
      - intros x Hx. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
        cbn [disjoint_from]. split; [clear - XB1 XB2; lia| exact I].
      - intros x Hx Ox. pose proof (tmp_ok_in asegs _ _ _ _ _ _ TOK Hx) as MX. destruct (mpd_at_blk_in asegs mk LBk x MX Ox) as (Ix & Nx).
        split; [apply (proj2 (LEQ _)); right; exact Ix|].
        split; [eapply client_range_block; [apply in_app_iff; left; exact Ix| clear; lia| clear; lia]|].
        cbn [disjoint_from]. split; [| exact I]. destruct (eb_blk_apart hk LBk mk _ _ HHk Ix) as [K|K]; clear - K; lia. }
    assert (HIDS2 : rw_cells asegs m2 IDS [CB 56 ecp_ids_bytes]).
    { eapply (idsb_presA _ _ _ _ _ _ mk m2 HIDS PXl). ddestruct IDOK as (I1 & I2 & I3 & _).
      cbn [disjoint_from]. split; [clear - F2 I1 I2 I3; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply CONT.
    split; [exact EB2|]. split; [exact TOK2|].
    split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
    split. { intros b Hb HTb. apply (proj1 (LNEW b Hb)). apply (proj2 (proj1 EXTk b)). left. exact HTb. }
    split; [exact HG3|]. split; [exact AP3|]. split; [exact RES|]. split; [exact HIDS2|].
    split; [| eapply (presA_rw_cells asegs R); [exact PXl| exact SLP| apply client_range_stack; clear; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; split; [clear - FBLO SLO1 SP1 NER NEEDR; lia| exact I]]].
    pose proof (nodup_of_fst _ (HND _ _ _ _ HH2)) as ND3.
    pose proof (cnt24_incl LB3 (grp_blocks g3 ++ LBk) ND3 ltac:(intros b Hb; apply in_app_iff; exact (proj1 (LEQ b) Hb))) as CI.
    rewrite cnt24_app, (gl_cnt24 _ _ _ _ _ _ _ RES) in CI. clear - CI C24k. lia.
    all: match goal with |- ?g => idtac "GL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition own_iv (w : ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "(4;.(17.(?.VFB,(4<.$6.$6.O1.))(?.(4=.$6.$6.O1.)(16.VFB,+400.)))(4;.(17.(?.(16.(4>.VFB,+3.)(4?.(32.VR,)))(4<.$6.$6.O1.))(?.(4=.$6.$6.O1.)(16.(16.(4>.VFB,+3.)(4?.(32.VR,)))+50.)))(17.(?.Vlo,(4<.$6.$6.O1.))(?.(4=.$6.$6.O1.)(50.&40.Vsp,)))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39188636933.0L8518658028.2 000001007SS1R2FB". (* [comment removed for export] *)
  #[using="Type"] Lemma shb_eq : SHB = shadow_of AL FB.
  Proof. unfold shadow_of. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. clear. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L39972639317.0L47617108161.1L54677079007.8L54677079007.9L64602661372.7L6899380056.1 00000100500K00j01@01DSS2FBS2FB1u1w1B1k3AP12W12W2S1R2FB1u1w1B1k3AP22W12W22lo3AP3S1R2lo3LOS1B1k3PAC3ALOS2FB". (* [comment removed for export] *)
  #[using="LOS"] Lemma own_iv_blk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))PW,(2.$9.)PB,$6.Pk,$6.P,(51.$1.VR,VHIA,R6.R5.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R4.)P,(22.(8.$6.$6.)(=.$6.$6.R3.R2.)R6.)P,(36.=R3.)P,(52.$9.$53.R6.)(30.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk W B k HH HIn K0 HW.
    pose proof (eb_blk_apart hk LBk mk B k HH HIn) as AP1.
    assert (AP2 : B + k <= SHB \/ SHB + 80 <= B).
    { rewrite shb_eq. eapply (apart_client_shadow AL (hcs asegs R HIA hk) B k FB _ 80 (hcs_ok asegs R HIA hk));
        [exact (hcs_block asegs R HIA hk LBk _ mk B k HH HIn)| | reflexivity| exact K0| clear; lia].
      eapply crange_sub; [exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HH ltac:(left; reflexivity))| clear; lia| clear; lia]. }
    assert (AP3 : B + k <= lo).
    { destruct (hm_apart asegs R HIA hk _ _ _ HH) as [HBR _]. rewrite Forall_forall in HBR.
      destruct (HBR _ ltac:(apply in_app_iff; left; exact HIn)) as (_ & _ & PAC & _). cbn [fst snd] in PAC.
      pose proof (art_lo asegs R HIA) as ALO. clear - PAC ALO LOS. lia. }
    induction W as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? Hw HWr]; subst.
    split; [| exact (IH HWr)]. destruct Hw as [[W1 W2]|[[W1 W2]|[W1 W2]]]; cbn [fst snd] in *; [clear - AP1 W1 W2; lia| clear - AP2 W1 W2; lia| clear - AP3 W1 W2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L18678489097.11L18680896816.11L49379278409.0 00000P010011S1R2lo3LOS1u1w1a1n2A22W13ALO3DHIS1R2FB1u1w1a1n2A12A22F22W12W22SBS". (* [comment removed for export] *)
  #[using="IMG NEEDR h LB LOS SLO sp1 SP1 F64 FRSH"] Lemma own_iv_data : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))PW,(2.$9.)Pa,$6.Pn,$6.P,(51.$1.VR,VHIA,R6.R5.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R4.)P,(52.$9.$53.R4.)P,(?.(54.(55.VR,))R4.)P,(?.(16.R5.R4.)(56.(55.VR,)))(30.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk W a n HH HW A1 A2. dpose eb_frame_facts as (F0 & F1 & F2 & F8 & _).
    pose proof (fresh_apart_relist_sg R HIA hk LB LBk LF mk FB 1024 FRSH HH) as FRSHk.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hk) hk LBk LF mk FB 1024 lo HH eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & _ & _ & _ & _ & _ & _ & _ & SBND & _).
    pose proof (proj1 SBND) as SB. clear SBND.
    induction W as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? Hw HWr]; subst.
    split; [| exact (IH HWr)]. destruct Hw as [[W1 W2]|[[W1 W2]|[W1 W2]]]; cbn [fst snd] in *; [clear - F2 A1 A2 W1 W2; lia| clear - SB A1 A2 W1 W2; lia|].
    pose proof (art_lo asegs R HIA) as ALO. pose proof (art_data_lo asegs R HIA) as DHI. clear - A2 W1 DHI ALO LOS. cbn in *. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L15721644297.500000CS1R5IDONE3IDS2I12I2". (* [comment removed for export] *)
  #[using="IMG NEEDR IDONE IDOK h LB LOS SLO sp1 SP1 F64 FRSH"] Lemma own_iv_ids : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))PW,(2.$9.)P,(51.$1.VR,VHIA,R4.R3.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R2.)P,(52.$9.$53.R2.)(30.R3.VIDS,+38.)")
(* [comment removed for export] *).
  Proof. intros hk LBk mk W HH HW. ddestruct IDOK as (I1 & I2 & I3 & _). eapply own_iv_data; [exact HH| exact HW| clear - I1 I2; lia| exact I3]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L61418634554.500000CS1R5IDONE3IDS2I22I3". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK h LB LOS SLO sp1 SP1 F64 FRSH"] Lemma ids_state_own : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))PW,(2.$9.)P,(51.$1.VR,VHIA,R5.R4.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R3.)P,(52.$9.$53.R2.)P,(57.$1.VIDONE,VIDS,R5.)P,(;.R4.R6.R5.)P,(10.$1.R7.R6.)(57.$1.VIDONE,VIDS,R7.)")
(* [comment removed for export] *).
  Proof.
    (intros hk LBk mk m' W HH HW dd_H; ddestruct dd_H as (b & bs & H1 & H2 & H3); intros MU WM). ddestruct IDOK as (I1 & I2 & I3 & _).
    dexists b, bs. split; [| split; [| exact H3]].
    - eapply (rw_cells_transport asegs); [exact H1| exact MU| exact WM|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
      eapply own_iv_data; [exact HH| exact HW| exact I1| clear - I2 I3; lia].
    - eapply (rw_cells_transport asegs); [exact H2| exact MU| exact WM|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      eapply own_iv_ids; [exact HH| exact HW].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7889766813.2000007S2d02Nx". (* [comment removed for export] *)
  #[using="LOS"] Lemma tmp_ok_own : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))Pds,(2.$1=.)PW,(2.$9.)P,(51.$1.VR,VHIA,R6.R5.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R4.)P,(1?.$1.R5.R6.(16.VFB,+170.)+<0.R3.)P,(;.R3.R6.R5.)P,(10.$1.R7.R6.)P,(11.$1.R8.)P,(11.$1.R8.)P,(52.$9.$53.R7.)P,Pd0,$1=.P,(22.$1=.R1.R:.)(30.R:.(21.R2.)+10.)(1?.$1.R;.R=.(16.VFB,+170.)+<0.R:.)")
(* [comment removed for export] *).
  Proof.
    (intros hk LBk mk m' ds W HH dd_H; ddestruct dd_H as (T1 & T2 & T3 & T4 & T5 & T6); intros MU WM MI MI' HW HD).
    split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
    apply Forall_forall. intros d0 Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
    split; [| exact SG]. eapply mpdr_at_munch; [exact MD| exact MU| exact WM| exact MI| exact MI'| exact (HD d0 Hd)|].
    intros O. destruct (mpd_at_blk_in asegs mk LBk d0 (conj MD SG) O) as (Ix & Nx).
    eapply (own_iv_blk hk LBk mk W _ _ HH Ix); [clear - Nx; lia| exact HW].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7889766813.2000007S2d02Nx". (* [comment removed for export] *)
  #[using="LOS"] Lemma grp_at_own : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))PA,$6.Pg,$34.PW,(2.$9.)P,(51.$1.VR,VHIA,R7.R6.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R5.)P,(24.$1.$25.R6.R7.R4.R3.)P,(;.R3.R7.R6.)P,(10.$1.R8.R7.)P,(11.$1.R9.)P,(11.$1.R9.)P,(52.$9.$53.R7.)P,(30.R8.R:.+<0.)(24.$1.$25.R<.R>.R;.R:.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk m' A g W HH HG MU WM MI MI' HW HD.
    eapply (ecp_group_at_munch asegs); [exact HG| exact MU| exact WM| exact MI| exact MI'| exact HD|].
    intros d0 Hd O. pose proof (ecp_group_at_heap_in asegs A_MT mk LBk A g d0 HG Hd O) as Ix.
    assert (Nx : 1 <= md_n d0).
    { ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & _).
      assert (MDe : mpdr_at asegs mk LBk d0) by (unfold grp_mpds, pt_mpds in Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption).
      ddestruct MDe as (_ & _ & _ & _ & _ & OW). rewrite O in OW. exact (proj1 OW). }
    eapply (own_iv_blk hk LBk mk W _ _ HH Ix); [clear - Nx; lia| exact HW].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma ids_bytes_at : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Pmm,P,(4.&40.)(5.(4.&8.))P,(2;.$1.R1.VIDS,(<.$7.(2<.#38.$2=.)(>.$7.)))(58.$1.R2.VIDS,(59.$5:.))")
(* [comment removed for export] *).
  Proof.
    intros mm H. destruct H as [[_ B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B.
    rewrite <- P_pk_ecparams_D.ids_bytes_u32s. exact B.
  Qed.

  #[using="IMG IDSN"] Lemma ids_aobj : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)PLFk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))P,(51.$1.VR,VHIA,R4.R3.R2.R1.)(31.$1.(32.VR,)(33.$1.VR,VHIA,R5.)R2.VIDS,+38.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk LFk mk HH.
    eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH| exact IDSN].
  Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02G0@C53807985733.206C53807985733.207L12916956843.1  L15195629121.1  L1685717371.0   L24023900370.0  L29108451424.203L29108451424.204L32781806251.1  L35668120898.7  L42411609006.0  L4248698872.6   L46204432317.2  L47513520362.203L47513520362.204L49379278409.0  L49629343297.1  L51624893551.3  L60098763854.3  L9786907307.1   P22976122839.206P22976122839.207Q11799173861.206Q11799173861.207Q117991File     Q11985496825.201Q12135202317.201Q13649235913.201Q14102793085.201Q15004325700.201Q15721825118.201Q15901874750.201Q1696393006.201 Q16990018393.201Q18668403881.201Q19765289966.201Q20377295060.203Q20851854948.201Q20868112649.201Q21141738973.201Q22835524217.201Q22985408909.201Q23427831342.201Q24784490574.201Q24804235293.201Q24969597693.201Q25854312132.201Q25870537193.201Q26751856062.201Q27854676697.201Q2799215689.201 Q28128303085.201Q29732439716.197Q3072796957.201 Q31716561380.201Q31718131849.201Q32171701309.201Q33700414969.201Q33790987294.201Q33947166577.201Q34347029405.202Q34877581972.201Q36737300841.201Q37453558366.201Q38721473113.201Q38921014052.201Q38995066733.201Q39125883166.202Q40599399476.201Q41054306893.201Q4139618244.201 Q41496990446.201Q42566809956.201Q42873128157.201Q43038498749.201Q44298944140.198Q44298944140.202Q44301027056.206Q44301027056.207Q44716880013.201Q44820754046.201Q45742289428.201Q45923577753.201Q46197199021.201Q46499103566.201Q47228431932.206Q47228431932.207Q47604089065.201Q4766626233.201 Q47801532788.201Q48119910507.206Q48119910507.207Q48472855173.201Q4871879646.201 Q4916249805.201 Q49785721508.201Q51449427892.201Q51769312953.201Q52346976878.201Q52946523988.201Q53723376733.201Q54487832473.202Q54783724863.201Q55256112523.202Q55522459422.201Q5596578838.206 Q5596578838.207 Q56592237972.201Q56790382361.201Q57063962669.201Q57366129358.201Q58668296436.201Q5941659220.201 Q59565891502.201Q59617553652.201Q59619599055.201Q60635707940.201Q60651936969.201Q60942287261.201Q61107394685.201Q62636076601.201Q62785781069.201Q63012415579.201Q63435846322.202Q63811190484.201Q6413378797.201 Q64228675114.205Q64228675114.206Q64228946346.206Q64228946346.207Q64568265742.201Q64751091846.201Q65654860420.201Q65672990121.201Q66372404894.201Q66552453502.201Q66942122546.198Q66942122546.202Q66956788302.206Q66956788302.207Q6715594638.201 Q67636351138.201Q67892150791.202Q6912043754.203 Q7785411076.201 Q7801640233.201 Q798847092.201  Q8682955006.201 Q9933143375.201 Q9947771764.201 Q9947836772.197 00000100200600:00;00<00=00>00B00Y00Z00o01502B03O03P03T03^03h03l04c05Z06Q07H07I07J07K07L07M07m07n07o08008108208308d09D09E09F09G09H09I09J09K09L09l09m09n09o0:00:10:Q0:R0;20;30;40;50;60<C0=:0=Z0=[0=\0=]0>=0>>0>?0>_0>`0?@0?A0?a0?b0?c0@H0@m0Ad0B[0B\0B]0C=0C>0C?0C@0D;0E60E70E80EX0Fk0H>0H?0H@0HA0Ha0IA0IB0IC0Ic0Id0Ji0KI0KJ0KK0KL0KM0Km0Kn0Ko0L00LP0M00M10M20M30MS0MT0MU0MV0MW0MX0NW0NX0O80O90Pd0RO0T@0V10V20V30VS0VT0VU0VV0W;0W`0XW0YN0YO0YP0YQ0ZB0Zb0Zc0[C0[D0[d0\D0\dFFS2FBS2FBSSFFS2FBS1R3HIA1h2sp2lo3TOP3HT0SS1R2FB3APS2d03XB13XB2S1R2FBS1R2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSS2FBS1R2FB3APSS1R2lo3LOSS2FBS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFFFFS2LF2FB3LFB3v163v173v184NSH'3NSLFFFFFFS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3NSLFFFFFFFFS2LF2FB3LFB3v163v173v184NSH'3NSLFFFFFS2LF2FB3LFB3v163v173v184NSH'3NSLFS2LF2FB3LFB3v163v173v184NSH'3NSLFFFFS1R5NEEDR2LF2sp2lo3SLO2FB3sp13SP13LFB3v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS1R2LF2sp2lo2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3NSLFFFS2LF2FB3LFB3v163v173v184NSH'3NSLFFS2LF2FB3LFB3v163v173v184NSH'3NSLFS2LF2FB3LFB3v163v173v184NSH'3NSLFS2LF2FB3LFB3v163v173v184NSH'3NSLFFS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFS2LF2FB3LFB3v163v173v184NSH'3NSLFFFS1R2LF2FB3LFB3v163v173v184NSH'3NSL3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB3v163v173v184NSH'3NSL3ALO2HB5Ha_st5Hl_st5SAEstFFS2LF2FB3LFB3v163v173v184NSH'3NSLS1R5NEEDR2LF2sp2lo3LOS3SLO2FB3LFB3v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp2lo3LOS3SLO2FB3LFB3v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_st5SAEstFFFS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSLFFS2LF2FB3LFB3v163v173v184NSH'3NSLFS1R5NEEDR2LF2sp2lo3SLO2FB3LFB3v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3NSLFFFFS2LF2FB3LFB3v163v173v184NSH'3NSLFFFS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSLFFFS2LF2FB3LFB3v163v173v184NSH'3NSLFFFFFS1R2LF2sp2lo2FB3sp13SP13LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF2FB3LFB3v163v173v184NSH'3NSLFS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP3v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP3v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP3v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEst5CM8stS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP3v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEst5CM8stFFS2LF2FB3LFB3v163v173v184NSH'3NSLFFFS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFFS1R2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3NSLFS2LF2FB3LFB3v163v173v184NSH'3NSLFS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE"] Lemma id_tail_fin : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pidj,$6.Pr,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps3v,(4.&40.)Ps5v,(4.&40.)Ps6v,(4.&40.)Ps11v,(4.&40.)Ps7v,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R28.R27.R26.R25.R24.$18.(19.R1<.R1;.R1:.)(<.(8.$6.(2.$7.))(=.$6.(2.$7.)(16.VFB,+270.)(<.$7.(1:.(14.&40.R16.))(<.$7.(1:.R19.)(>.$7.))))(<.(8.$6.(2.$7.))(=.$6.(2.$7.)(16.VFB,+1>8.)(<.$7.(15.R18.)(<.$7.(15.R17.)(>.$7.))))(>.(8.$6.(2.$7.)))))(1<.(<.$1=.R23.(<.$1=.R22.(<.$1=.R21.(<.$1=.R20.(<.$1=.R1?.(<.$1=.R1>.(<.$1=.R1=.(>.$1=.)))))))))(<.(8.$6.$6.)(=.$6.$6.VIDONE,(16.VIDONE,+1.))(<.(8.$6.$6.)(=.$6.$6.VIDS,(16.VIDS,+38.))(>.(8.$6.$6.)))))P,(1?.$1.R27.R28.(16.VFB,+170.)+<0.(<.$1=.R24.(<.$1=.R23.(<.$1=.R22.(<.$1=.R21.(<.$1=.R20.(<.$1=.R1?.(<.$1=.R1>.(>.$1=.)))))))))P,(20.$6.(21.R25.)(16.(16.VFB,+170.)+68.))P,(20.$6.(21.R25.)(16.(16.VFB,+170.)+8.))P,(20.$6.(21.R25.)(16.(16.VFB,+170.)+18.))P,(20.$6.(21.R25.)(16.(16.VFB,+170.)+28.))P,(20.$6.(21.R25.)(16.(16.VFB,+170.)+38.))P,(20.$6.(21.R25.)(16.(16.VFB,+170.)+48.))P,(20.$6.(21.R25.)(16.(16.VFB,+170.)+58.))P,(17.(36.(5;.(37.+2.+1?.))R1>.)(?.R1>.=))P,P,(20.$6.R1?.=)(17.(?.=R21.)(36.R21.(37.+2.+1?.)))P,(?.(16.R30.$5<.)(3:.VLEN,))P,(?.(16.(16.R30.+15.)$5=.)(3<.Vd,))(3?.$1.(40.$1.VR,VHIA,R35.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.R21.(14.&40.Vsp1,)Vgp,Vtp,R20.R1?.R1>.Vsp,(14.&40.Vsp1,)R1=.R1<.(14.&40.(16.VFB,+1=8.))R1;.R1:.R19.R18.R17.(14.&40.VFB,)R12.(14.&40.(16.(4>.VFB,+3.)(4?.(32.VR,))))R11.R10.R>.(14.&40.(16.VFB,+1:8.))(14.&40.VFB,)(14.&40.R22.)R?.R16.R15.R14.R13.)VF,(14.&40.+;1204.)Vfc,(45.(4.&40.))R33.(46.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s7v. intros EBk TOK EN EP EA EB' EX EY EZ RR IDR VB FB'.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl [(SHB, SHB + 80)] mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB LBk LF mk FB 1024 FRSH HHk) as FRSHk.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hk) hk LBk LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    pose proof (conj TOK (conj HHk (conj MIk I))) as BOX.
    unfold EP_SH_GR in FSH. unfold SLL in SLOTS.
    (* [comment removed for export] *)
    do 25 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH6 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    assert (OWN : Forall own_iv [(SHB, SHB + 80)]) by (apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    assert (EB6 : EB hk LBk m6 v f EP_SH_G
                    [C8 (Z_to_bv 64 (FB + 440)); C8 (Z_to_bv 64 (FB + 120)); C8 (Z_to_bv 64 (FB + 456)); C8 (Z_to_bv 64 (FB + 88));
                     C8 (Z_to_bv 64 (FB + 136)); C8 (Z_to_bv 64 (FB + 72)); C8 (Z_to_bv 64 (FB + 56)); C8 (Z_to_bv 64 (FB + 40));
                     C8 (Z_to_bv 64 (FB + 472)); C8 (Z_to_bv 64 (FB + 424)); C8 (Z_to_bv 64 PKA); C8 (Z_to_bv 64 (G + 40));
                     C8 (Z_to_bv 64 (G + 24)); C8 (Z_to_bv 64 (FB + 624)); C8 (Z_to_bv 64 (G + 8)); C8 v16; C8 v17; C8 v18]
                    [(FB + 624, [C4 (Z_to_bv 64 idj); C4 gj'])] (tmp_blocks (DS7 dN dP dA dB dX dY dZ)) W0).
    { replace (G + 40) with (FB + 408) by (clear; lia).
      replace (G + 24) with (FB + 392) by (clear; lia). replace (G + 8) with (FB + 376) by (clear; lia).
      unfold EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_G; cbn [repeat app]; exact FSH6| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [eapply (ids_munch_sh mk m6 80); [exact IDSk| exact MU| exact WM| exact (proj1 SBND)]|].
      split; [eapply (ch_munch_sh mk m6 80); [apply Forall_cons; [exact (Forall_inv CHk)| apply Forall_nil]| exact MU| exact WM| clear - APS; lia]|].
      split; [exact EXTk| exact FRk]. }
    assert (TOK6 : tmp_ok asegs m6 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct BOX as (TOK0 & HHk0 & MIk0 & _). eapply (tmp_ok_own hk LBk mk m6 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN).
      intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2 APS; lia| exact I]. }
    replace (FB + 472) with (G + 104) by (clear; lia). replace (FB + 424) with (G + 56) by (clear; lia).
    eapply (ep_cleanup hk LBk m6 v f dN dP dA dB dX dY dZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r idj gj');
      first [ exact EB6 | exact TOK6 | exact EN | exact EP | exact EA | exact EB' | exact EX | exact EY | exact EZ | exact RR | exact IDR | exact VB | exact FB' | idtac ].
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01U0@D40016287967.241D56708389779.241D58813623466.241L13499167864.242L14447004729.2  L14674883745.0  L14946148648.242L14948428072.242L1685717371.0   L17168671483.0  L1788239501.1   L19561236329.1  L21444186492.230L21866712442.1  L22409920380.180L2397676628.0   L24123163929.234L26430952671.234L28142564996.0  L29022582655.2  L32586543723.0  L33277649188.1  L35668120898.7  L35870121979.3  L35871956944.5  L35874835892.2  L36667852792.0  L41588182622.3  L42862037951.5  L44200638400.2  L45272789334.2  L46605397800.2  L46645889000.227L46647841290.230L46647841290.243L4681653737.1   L49379278409.0  L53516959912.242L53519239336.242L54013605813.5  L54025866170.3  L54258527414.4  L54992078076.234L59308549609.3  L59309005011.3  L59310695905.2  L59427879996.242L60098763854.3  L62195878002.1  L63825760836.2  L66572605252.10 L7738195705.2   L957827166.0    P14461423358.242P29008688568.241P63829871026.242P7750690063.241 Q11801279589.241Q13396600321.238Q16797194194.239Q16797194194.247Q19637298227.238Q20580512354.241Q20612713884.238Q22231028708.241Q22232979940.241Q23357214870.241Q26295627581.235Q26295627581.248Q26760973858.238Q28096309781.234Q35062870404.183Q41218494256.241Q41220736304.241Q41263643765.183Q42430292998.239Q42430292998.247Q42430557844.232Q42432487553.235Q42432487553.248Q42442974265.245Q46474998015.183Q48117823211.241Q49698585326.240Q50458135125.235Q50458135125.248Q51921884758.239Q52017756552.234Q54967541497.241Q58768111688.241Q6255721753.235 Q6255721753.248 Q6283001296.245 Q6287030141.232 Q63911392935.235Q63911392935.248Q66954699982.241Q6912046254.241 Q7379058664.183 Q8945834930.232 Q8958251295.245 00000n01l01m02`02a02b02c02d02e02f02j02n03Y03]04H04I05405_05`05a05b05f06=06F06G06H06I06V06e06n07407508?09I0:S0:W0:X0;C0;n0<<0<F0<Q0=<0=E0=F0=G0=H0=R0=S0=T0=d0=e0=f0?<0@R0@S0Aa0BT0CO0D50D[0E;0E<0Eg0FZ0GM0GN0Gk0HH0Hh0IS0J?0K20Ke0LP0M60M\0NB0Nh0ON0P40PZ0Qk0RT0S70SZ0T@0U;0Un0Va0WL0X70X]0YC0Yi0ZO0[B0\50]00]M0]jS2LF2sp3PKA2FB3sp13LFB3v163v173v183idj4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB3v163v173v183idj4NSH'3NSL2HB5Ha_st5Hl_stFS2LF2sp3PKA2FB3sp13LFB3v163v173v183idj4NSH'3NSL3IJBFSFFSSS2FBS2FBS2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLS2FBS2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLSS2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLSFSS2FBS1R3HIA1h2sp2lo3TOP3HT0S1d1f3FB'FFSS3idj3IJB3NZJS3LEN1v2VB4PSG0S3idj3IJBS1j2JBFS3IDS2LF2sp3PKA2FB3sp13LFB3NZP3v163v173v181j2JB2F04SP1R4IDLO4IDHI4NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB3NZP3v163v173v181j2JB2F04SP1R4IDLO4IDHI4NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB3NZP3v163v173v181j2JB2F04SP1R4IDLO4IDHI4NSH'3NSLS2FBSS2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLS1d1f3FB'4FSG0S3LEN1v2VBS2FB2d03XB2S2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLS1j2JB2NJFFFS1R2lo3LOSFFS2r12RR1r2KR1q1HFSS1R5NEEDR2LF2sp2lo3SLO2FB3sp13SP13LFB3v163v173v184FBLO3NER4NSH'3NSL3idj2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO2FB3sp13SP13LFB3v163v173v184FBLO3NER4NSH'3NSL3idj2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3SLO2FB3LFB3v163v173v184FBLO3NER4NSH'3idj3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v183idj4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3v163v173v183NER4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSLFS2LF2sp2lo3sp13SP13LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSL3idj2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v183idj4NSH'3NSL2HB5Ha_st5Hl_stFS2LF3LFB3v163v173v184NSH'3NSLS2LF3LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2sp2lo3sp13SP13LFB3v163v173v184NSH'3NSLS2LF2sp3sp13SP13LFB3v163v173v184NSH'3NSL3SPRS2LF2FB3LFB3v163v173v183idj4NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3NSL3idj2HB5Ha_st5Hl_stS2LF2sp2lo3sp13SP13LFB3v163v173v184NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS2LF3sp13LFB3v163v173v184NSH'3NSL4SP1RS1R5NEEDR2LF2sp2lo3LOS3SLO2FB3LFB3v163v173v183ALO3NER3idj4NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3NSL2HB5Ha_stS3IDS2LF3LFB3v163v173v181j4NSH'3NSLS3IDS2LF3LFB3v163v173v181j4NSH'3NSLS2LF2FB3LFB3v163v173v182F04NSH'3NSL2HBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3v163v173v183NER4NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3idj3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3idj3NSL2HB5Ha_st5Hl_stS3IDS2LF3LFB3v163v173v181j2JB4IDLO4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4IDLO4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS3IDS2LF3LFB3v163v173v181j2JB4NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3idj3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB3v163v173v184NSH'3idj3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3v163v173v184NSH'3NSL3NERS2LF3LFB3v163v173v184NSH'3NSLS2LF3LFB3v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF IDSN"] Lemma id_tail : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pj,$6.Pr1,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)P,(35.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,(17.(?.=R15.)(?.R15.+=.))P,(17.(36.(5;.(37.+2.+1?.))R15.)(?.R15.=))P,(?.(16.(16.R2:.$39.)$5<.)(3:.VLEN,))P,(?.(16.(16.(16.R2:.(3;.=))+15.)$5=.)(3<.Vd,))(3?.$1.(40.$1.VR,VHIA,R2?.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.R17.(14.&40.Vsp1,)Vgp,Vtp,R16.R15.R14.Vsp,(14.&40.Vsp1,)R13.R12.R11.R10.R?.R>.R=.R<.(14.&40.VFB,)(14.&40.(16.VFB,+20.))(14.&40.(16.(4>.VFB,+3.)(4?.(32.VR,))))(14.&40.(4?.(32.VR,)))(14.&40.(16.VIDS,(5>.+4.R19.)))R7.R6.(14.&40.VFB,)(14.&40.R18.)(14.&40.(16.VFB,+170.))R;.R:.R9.R8.)VF,(14.&40.+;11;4.)Vfc,(45.(4.&40.))R2=.(46.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s8v. intros LI JB RR VB FB'.
    assert (PSG0 : 0 <= pk_set_group_PHI) by (unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (FSG0 : 0 <= pk_set_group_FR) by (unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia).
    pose proof LI as (EBk & _).
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    unfold SLL in SLOTS.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply (linv_gfree hk LBk mk v f gref idg rg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb 0xb11c0);
      [exact LI| clear; lia| reflexivity| clear - VB PSG0 FSG0; lia| clear - FB' PSG0 FSG0; lia|].
    intros h2 LB2 m2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 LI2.
    clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM SCSk LI. clear w0 w1 w2.
    destruct (AImgGlobals.img_norz_sound _ _ IDSN) as (_ & IDLO & IDHI & _). unfold AImgGlobals.IMG_LO, AImgGlobals.IMG_HI in IDLO, IDHI.
    dpose LI2 as (EB2 & TOK2 & EN & EP & EA & EB' & EX & EY & EZ & RT2 & HG2 & AP2 & GL2 & HIDS2 & C24k2 & SLP2).
    change (grp_blocks (grp_zero REF)) with (@nil blk) in EB2. rewrite app_nil_r in EB2.
    pose proof EB2 as EBk0. eb_open EB2.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl [(FB + 624, FB + 628)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h2 LB LB2 LF m2 FB 1024 FRSH HHk) as FRSHk.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA h2) h2 LB2 LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h2 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h2) as CSOKk.
    pose proof (ids_aobj h2 LB2 LF' m2 HHk) as OIDS.
    dpose (Forall_inv CHk) as (GID & _ & _). dpose (Forall_inv (Forall_inv_tail CHk)) as (PBN & _ & _). cbn [fst snd] in GID, PBN.
    pose proof (conj TOK2 (conj HHk (conj MIk (conj HIDS2 (conj IDSk I))))) as BOX.
    unfold SLL in SLOTS. unfold EP_SH_GR in FSH.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk OIDS (IDS + 4 * j) 4.
    (* [comment removed for export] *)
    destruct (nth_error P_pk_ecparams_D.IDWS (Z.to_nat j)) as [w|] eqn:NJ; [| exfalso; apply nth_error_None in NJ; cbn in NJ; clear - NJ JB; lia].
    ddestruct (P_pk_ecparams_D.ids_nth j w NJ ltac:(clear - JB; lia)) as (idj & -> & IJB & IJZ & _).
    pose proof (u32ro_read asegs m2 IDS P_pk_ecparams_D.IDWS j _ (wa (IDS + 4 * j)) (ids_bytes_at m2 HIDS2) NJ ltac:(clear - JB; lia) eq_refl) as RDJ.
    zstep. clear RDJ. rewrite (sx32_small_ep idj) by (clear - IJB; lia).
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    ddestruct BOX as (TOK0 & HHk0 & MIk0 & HIDS0 & IDSk0 & _).
    assert (OWN : Forall own_iv [(FB + 624, FB + 628)]) by (apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    assert (EB3 : EB h2 LB2 m3 (v + GF_PHI) (f + GF_FR 0) EP_SH_GR (SLL v16 v17 v18) [(FB + 624, [C4 (Z_to_bv 64 idj); C4 gj']); (FB + 488, [C8 pb; C8 nb])]
                    (tmp_blocks (DS7 dN dP dA dB dX dY dZ)) W0).
    { unfold EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [exact FSH| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [exact (ids_state_own h2 LB2 m2 m3 _ HHk0 OWN IDSk0 MU WM)|].
      split; [apply Forall_cons; [split; [exact GID| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| apply Forall_cons; [split; [exact PBN| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| apply Forall_nil]]|].
      split; [exact EXTk| exact FRk]. }
    assert (TOK3 : tmp_ok asegs m3 LB2 G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_own h2 LB2 m2 m3 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN).
      intros d0 Hd. ddestruct TOK0 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2; lia| exact I]. }
    assert (HIDS3 : rw_cells asegs m3 IDS [CB 56 ecp_ids_bytes]).
    { eapply (rw_cells_transport asegs); [exact HIDS0| exact MU| exact WM|]. exact (own_iv_ids h2 LB2 m2 _ HHk0 OWN). }
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      assert (RNZ : r1 <> 0) by (intros ->; clear - KR; first [apply KR; reflexivity| (vm_compute in KR; congruence)]).
      eapply (id_tail_fin h2 LB2 m3 _ _ dN dP dA dB dX dY dZ v16 v17 v18 gj' pb nb idj r1);
        first [ exact EB3 | exact TOK3 | exact EN | exact EP | exact EA | exact EB' | exact EX | exact EY | exact EZ | exact RR
              | (intros R0; exfalso; exact (RNZ R0)) | (unfold GF_PHI, AVOL_CALL in *; clear - VB; lia) | (unfold GF_FR, fr_charge in *; clear - FB'; lia) | idtac ].
    - assert (RZ : r1 = 0) by (clear - KR RR; Z.div_mod_to_equations; lia). subst r1. clear KR.
      shadow_chk OIDS (IDS + 4 * j) 4.
      pose proof (u32ro_read asegs m3 IDS P_pk_ecparams_D.IDWS j _ (wa (IDS + 4 * j)) (ids_bytes_at m3 HIDS3) NJ ltac:(clear - JB; lia) eq_refl) as RDJ.
      clear HIDS3.
      zstep. clear RDJ. rewrite (sx32_small_ep idj) by (clear - IJB; lia).
      destruct (Z.eq_dec idj 0) as [EJ|NZJ].
      + rewrite EJ in *. do 5 zstep.
        match goal with |- context [Z_to_bv 64 (Z.land ?a ?b)] =>
          replace (Z_to_bv 64 (Z.land a b)) with (Z_to_bv 64 (-0x4E80)) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (id_tail_fin h2 LB2 m3 _ _ dN dP dA dB dX dY dZ v16 v17 v18 gj' pb nb 0 (-0x4E80));
          first [ exact EB3 | exact TOK3 | exact EN | exact EP | exact EA | exact EB' | exact EX | exact EY | exact EZ | (clear; lia)
                | (intros R0; exfalso; clear - R0; lia) | (unfold GF_PHI, AVOL_CALL in *; clear - VB; lia) | (unfold GF_FR, fr_charge in *; clear - FB'; lia) | idtac ].
      + do 5 zstep.
        replace (0 <? idj) with true by (symmetry; apply Z.ltb_lt; clear - IJB NZJ; lia).
        match goal with |- context [Z_to_bv 64 (Z.land ?a ?b)] =>
          replace (Z_to_bv 64 (Z.land a b)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (id_tail_fin h2 LB2 m3 _ _ dN dP dA dB dX dY dZ v16 v17 v18 gj' pb nb idj 0);
          first [ exact EB3 | exact TOK3 | exact EN | exact EP | exact EA | exact EB' | exact EX | exact EY | exact EZ | (clear; lia)
                | (intros _; clear - IJB; lia) | (unfold GF_PHI, AVOL_CALL in *; clear - VB; lia) | (unfold GF_FR, fr_charge in *; clear - FB'; lia) | idtac ].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L40560514702.6L40560890624.7L59308546384.300000E00^00hS1R2lo3LOS2d03ALO3PACS1R2lo3LOS2d03ALO3ACV3IHIS2d02N02N1". (* [comment removed for export] *)
  #[using="IMG NEEDR h LB sp LOS SLO SP1 F64 FRSH"] Lemma mpd_qpre : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pd0,$1=.P,(51.$1.VR,VHIA,R4.R3.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R2.)P,(5?.$1.R3.R4.R2.)P,(60.R3.)(17.P,(20.$61.(62.R4.)$63.)(36.=(64.R5.))(17.P,(?.+1.(65.R4.))(31.$1.(32.VR,)(33.$1.VR,VHIA,R8.)R6.(64.R5.)(5>.+4.(65.R5.)))P,(?.+1.(65.R4.))(4;.(?.(16.(64.R5.)(5>.+4.(65.R5.)))Vlo,)(?.Vsp1,(64.R5.)))))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk d0 HH MD IM. dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (alloc_ceiling_val R) as ACV.
    destruct (hm_apart asegs R HIA hk _ _ _ HH) as [HBR _]. rewrite Forall_forall in HBR.
    pose proof MD as [(_ & _ & _ & _ & _ & OW) _].
    destruct (md_own d0) eqn:O.
    - destruct OW as [_ N0]. split; [intros C'; discriminate C'|]. split; intros N1; exfalso; clear - N0 N1; lia.
    - ddestruct OW as (N1 & HIn & _).
      destruct (HBR _ ltac:(apply in_app_iff; left; exact HIn)) as (P0 & _ & PAC & _). cbn [fst snd] in P0, PAC.
      split; [intros _; exact P0|]. split; [intros _; exact (hm_aobj_block asegs R HIA hk LBk LF' mk _ _ HH HIn)|].
      intros _. left. clear - PAC ALO LOS. lia.
    - split; [intros C'; discriminate C'|].
      pose proof (IM O) as IMN. destruct (AImgGlobals.img_norz_sound _ _ IMN) as (_ & _ & IHI & _). unfold AImgGlobals.IMG_HI in IHI.
      split; [intros _; eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH| exact IMN]|].
      intros _. left. clear - IHI ACV ALO LOS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L16846365558.6 L3915770725.2  L43075060507.10L67810270356.10L9350677622.6  00000H00Q01601X020S2lo2FB3sp13lo'3LO'4FBLOS3sp13lo'S1R3IDS2lo3LOS3sp13lo'3LO'3ALO2I33DHIS1R2lo3LOS3sp13lo'3LO'3ALO1B1k3PACS2lo2FB3sp13lo'3LO'4FBLO". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 F64 FRSH"] Lemma linv_scratch : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pm2,P,(4.&40.)(5.(4.&8.))Plo',$6.P,(35.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(;.(<.(8.$6.$6.)(=.$6.$6.R2.Vsp1,)(>.(8.$6.$6.)))R17.R3.)P,(?.Vlo,R3.)P,(10.$1.R19.R5.)P,(11.$1.R6.)P,(12.$1.R7.Vlo,Vsp1,)(35.R1>.R1=.R8.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)")
(* [comment removed for export] *).
  Proof.
    intros until lo'. (intros dd_H; ddestruct dd_H as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & RT & HG & AP & GL & HIDS & C24k & SLP); intros MU LO' WM MI2 ST2).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    dpose EBk as (HHk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIk & _).
    destruct (hm_apart asegs R HIA hk _ _ _ HHk) as [HBR _]. rewrite Forall_forall in HBR.
    assert (DJB : forall B k, In (B, k) LBk -> disjoint_from [(lo', sp1)] B k).
    { intros B k HIn. destruct (HBR _ ltac:(apply in_app_iff; left; exact HIn)) as (_ & _ & PAC & _). cbn [fst snd] in PAC.
      cbn [disjoint_from]. split; [clear - PAC ALO LOS LO'; lia| exact I]. }
    split; [exact (eb_scratch _ _ _ _ _ _ _ _ _ _ m2 lo' EBk MU LO' WM MI2 ST2)|].
    split. { eapply (tmp_ok_munchA asegs mk m2 LBk G 192 _ _ TOK MU WM MIk MI2); [cbn [disjoint_from]; split; [clear - FBLO LO'; lia| exact I]|].
             intros d0 Hd O. pose proof (tmp_ok_in asegs _ _ _ _ _ _ TOK Hd) as MX. destruct (mpd_at_blk_in asegs mk LBk d0 MX O) as (Ix & _). exact (DJB _ _ Ix). }
    split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|]. split; [exact RT|].
    split. { eapply (ecp_group_at_munch asegs); [exact HG| exact MU| exact WM| exact MIk| exact MI2| cbn [disjoint_from]; split; [clear - FBLO LO'; lia| exact I]|].
             intros d0 Hd O. exact (DJB _ _ (ecp_group_at_heap_in asegs A_MT mk LBk REF gref d0 HG Hd O)). }
    split; [exact AP|]. split; [exact GL|].
    split; [| split; [exact C24k| eapply (rw_cells_transport asegs); [exact SLP| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; split; [clear; lia| exact I]]]].
    eapply (rw_cells_transport asegs); [exact HIDS| exact MU| exact WM|]. ddestruct IDOK as (I1 & I2 & I3 & _).
    pose proof (art_data_lo asegs R HIA) as DHI.
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [| exact I]. clear - I3 DHI ALO LOS LO'. cbn in *. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L11163333180.11100000dS2LF2sp3PKA2FB3sp13LFB3NZP1A1g2EP2EA3EB'2EX2EY2EZ2EN". (* [comment removed for export] *)
  #[using="LF sp PKA FB sp1 LFB NZP"] Lemma grp_mpd_at : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Psegs,(2.$66.)PMT,(2.$67.)Pmm,P,(4.&40.)(5.(4.&8.))PLBx,(2.$3.)PA,$6.Pg,$34.Pd0,$1=.P,(24.R7.R6.R5.R4.R3.R2.)P,(22.$1=.R2.(27.R3.))(17.(68.R9.R7.R6.R3.)(17.(?.(16.R5.+8.)(21.R3.))(?.(16.(21.R3.)+10.)(16.R5.+78.))))")
(* [comment removed for export] *).
  Proof.
    (intros segs MT mm LBx A g d0 dd_H; ddestruct dd_H as (_ & _ & _ & EP & EA & EB' & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & _); intros Hd).
    unfold grp_mpds, pt_mpds in Hd. cbn [app In] in Hd.
    destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (split; [assumption| lia]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L52469535387.1L59308586248.2L63667055128.000000400:00;S2FBS1i2HiS". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO SP1 F64 FRSH"] Lemma grp_aobj : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R9.R8.R7.R6.R5.$18.R4.R3.R2.R1.)(31.$1.(32.VR,)(33.$1.VR,VHIA,R:.)R8.(16.VFB,+170.)+<0.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SL CH T WE EBk. ddestruct EBk as (HHq & _ & _ & _ & _ & (FSHq & _) & _).
    change 192 with (8 * Z.of_nat 24).
    eapply (sh_aobj hk mk EP_SH_GR G 46 24); [exact FSHq| exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHq ltac:(left; reflexivity))| clear; lia| clear; lia|].
    intros i Hi. unfold EP_SH_GR. do 24 (destruct i as [|i]; [reflexivity|]). exfalso. clear - Hi. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cmp_opnd (gref : ecp_grp) (dN dP dA dB dX dY dZ d0 : mpd) : Prop :=
    In d0 (DS7 dN dP dA dB dX dY dZ) \/ In d0 (grp_mpds gref).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39859025780.6L54944737318.400000B00OS2lo2FB2d04FBLO2B2S2FB2d02B12B2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO SP1 F64 FRSH LFB NZP"] Lemma linv_opnd : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pd0,$1=.P,(35.R16.R15.R14.R13.R12.R11.R10.=R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(69.R12.R10.R?.R>.R=.R<.R;.R:.R2.)(17.(5?.$1.R16.R17.R3.)(17.P,(20.$61.(62.R3.)$63.)(36.=(64.R4.))(17.(31.$1.(32.VR,)(33.$1.VR,VHIA,R18.)R16.(21.R3.)+10.)(17.P,(?.+1.(65.R3.))(31.$1.(32.VR,)(33.$1.VR,VHIA,R19.)R17.(64.R4.)(5>.+4.(65.R4.)))(17.(4;.(?.(16.(21.R3.)+10.)Vlo,)(?.Vsp1,(21.R3.)))P,(?.+1.(65.R3.))(4;.(?.(16.(64.R4.)(5>.+4.(65.R4.)))Vlo,)(?.Vsp1,(64.R4.))))))))")
(* [comment removed for export] *).
  Proof.
    intros until d0. (intros dd_H; ddestruct dd_H as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & RT & HG & AP & GL & HIDS & C24k & SLP); intros OP).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof EBk as (HHk & _).
    pose proof (ref_aobj _ _ _ _ _ _ _ _ _ EBk) as OREF. pose proof (grp_aobj _ _ _ _ _ _ _ _ _ EBk) as OGRP.
    assert (K : mpd_at asegs mk LBk d0 /\ mpd_imgA d0 /\ ((G <= md_addr d0 /\ md_addr d0 + 16 <= G + 192) \/ (REF <= md_addr d0 /\ md_addr d0 + 16 <= REF + 192))).
    { destruct OP as [Hd|Hd].
      - split; [exact (tmp_ok_in asegs _ _ _ _ _ _ TOK Hd)|]. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (NS & XB1 & XB2).
        split; [intros O; exfalso; exact (NS O)| left; split; assumption].
      - destruct (grp_mpd_at _ _ _ _ _ _ _ HG Hd) as (MD & B1 & B2).
        split; [split; [exact MD| left; exact (P_pk_ecparams_D.gl_signs _ _ _ _ _ _ GL d0 Hd)]|].
        pose proof (grp_factsA_of_gl_result_at R HIA hk LBk LF' mk A_MT idg REF gref _ HHk HG GL) as (_ & _ & _ & _ & _ & IMGG & _).
        split; [exact (proj1 (Forall_forall _ _) IMGG _ Hd)| right; clear - B1 B2; lia]. }
    ddestruct K as (MD & IM & BND).
    ddestruct (mpd_qpre hk LBk mk d0 HHk MD IM) as (Q1 & Q2 & Q3).
    split; [exact MD|]. split; [exact Q1|].
    split; [destruct BND as [[B1 B2]|[B1 B2]]; [eapply aobj_sub; [exact OGRP| exact B1| exact B2]| eapply aobj_sub; [exact OREF| exact B1| exact B2]]|].
    split; [exact Q2|]. split; [left; destruct BND as [[B1 B2]|[B1 B2]]; clear - B1 B2 FBLO; lia| exact Q3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L27936558349.6 L27940850327.6 L29432667347.5 L3482346814.6  L3486638756.6  L38235734261.1 L60098763854.3 L66151427842.16L67228227629.9 00000100J00Z00[00\00`00j01F01eFS1R5NEEDR2lo3sp14SLO13NERS1R2lo3LOS3ALO1HFFS2loS1R2lo3LOSS3sp12r04SP1M1q1r1H2H02q02H4S1R3HIA1h2sp2lo3TOP3sp13SP13HT0". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 SP1M F64 FRSH LFB NZP"] Lemma linv_cmp : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)PdT,$1=.PdR,$1=.PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(35.R31.R30.R2?.R2>.R2=.R2<.R2;.=R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)P,(69.R2=.R2;.R2:.R29.R28.R27.R26.R25.R1=.)P,(69.R2>.R2<.R2;.R2:.R29.R28.R27.R26.R1=.)P,(17.(?.=R1=.)(36.R1=.(37.+2.+40.)))P,(20.$6.(38.R1>.+2.)=)P,Pm2,P,(4.&40.)(5.(4.&8.))Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(35.R45.R44.R?.R42.R41.R40.R3?.=R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)(3?.$1.(40.$1.VR,VHIA,R46.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R2?.)(14.&40.Vsp1,)Vgp,Vtp,R?.R>.R=.R2;.R2:.(14.&40.(6:.(6;.(6<.R31.)(6<.R30.))))R<.R;.R:.R9.R8.R7.R6.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R5.R4.R3.R2.)VF,(14.&40.R2?.)Vfc,(45.(4.&40.))R10.(46.$1.)))(3?.$1.(40.$1.VR,VHIA,R37.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R20.)(14.&40.Vsp1,)Vgp,Vtp,R1?.R1>.R1=.R1<.R1;.(14.&40.(21.R22.))(14.&40.(21.R21.))R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(14.&40.$6=.)Vfc,(45.(4.&40.))R35.(46.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros LI OT OR RETr RETe CONT.
    destruct (linv_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI OT) as (TM & TP & TO & TOL & TS & TSL).
    destruct (linv_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI OR) as (RM & RP & RO & ROL & RS & RSL).
    pose proof LI as (EBk & _). pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    assert (SCSk : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP SP1. lia. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof (A_mpi_cmp_mpi_spec AL IMG) as SP. unfold mpi_cmp_mpi_stmtA in SP.
      eapply SP with (CS := hcs asegs R HIA hk) (LB := LBk) (dX := dT) (dY := dR) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact TM | exact RM | exact TP | exact RP | exact MIk | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk)
              | exact (hm_abase asegs R HIA hk LBk LF' mk HHk) | exact TO | exact RO | exact TOL | exact ROL | exact STb | exact SCSk
              | exact TS | exact RS | exact TSL | exact RSL | reflexivity
              | (clear - ALO LOS; pose proof (alloc_ceiling_pos (L := arl_L R)); lia) | (clear - SLO1 NER NEEDR; lia) | (clear - SP1M; Z.div_mod_to_equations; lia)
              | match goal with |- ?g => idtac "CMP-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_cmp_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    eapply CONT. exact (linv_scratch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lo LI MU2 ltac:(clear; lia) WM2 MI2 ST2).
    all: match goal with |- ?g => idtac "CMP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L27936558349.6 L27940850327.6 L27940933942.2 L29431152682.1 L29432667347.5 L32027975233.0 L3482346814.6  L3483319967.1  L3486638756.6  L38235734261.1 L60098763854.3 L66151427842.16L67228227629.9 00000100J00K00L00\00]00^00_00`00d00n01J01iFS1R5NEEDR2lo3sp14SLO13NERFFS1R2lo3LOS3ALO1HSFFFS2loS1R2lo3LOSS3sp12r04SP1M1q1r1H2H02q02H4S1R3HIA1h2sp2lo3TOP3sp13SP13HT0". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 SP1M F64 FRSH LFB NZP"] Lemma linv_getbit : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pd0,$1=.PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(35.R30.R2?.R2>.R2=.R2<.R2;.R2:.=R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(69.R2<.R2:.R29.R28.R27.R26.R25.R24.R1<.)P,(17.(?.=R1<.)(36.R1<.(37.+2.+40.)))P,(20.$6.(38.R1=.+2.)=)P,Pm2,P,(4.&40.)(5.(4.&8.))Pr,$6.Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(35.R44.R43.R10.R41.R40.R3?.R3>.=R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.)P,(17.(?.=R10.)(?.R10.+1.))(3?.$1.(40.$1.VR,VHIA,R46.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R30.)(14.&40.Vsp1,)Vgp,Vtp,R10.R?.R>.R2<.R2;.(14.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R6.R5.R4.R3.)VF,(14.&40.R30.)Vfc,(45.(4.&40.))R12.(46.$1.)))(3?.$1.(40.$1.VR,VHIA,R35.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.(14.&40.R1?.)(14.&40.Vsp1,)Vgp,Vtp,R1>.R1=.R1<.R1;.R1:.(14.&40.(21.R20.))(14.&40.=)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)VF,(14.&40.$6>.)Vfc,(45.(4.&40.))R33.(46.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros LI OT RETr RETe CONT.
    destruct (linv_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI OT) as (TM & TP & TO & TOL & TS & TSL).
    pose proof LI as (EBk & _). pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    assert (SCSk : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP SP1. lia. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof (A_mpi_get_bit_spec AL IMG) as SP. unfold mpi_get_bit_stmtA, mpi_query_stmtA in SP.
      eapply SP with (CS := hcs asegs R HIA hk) (LB := LBk) (dX := d0) (v := 0) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact TM | exact TP | exact MIk | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk)
              | exact (hm_abase asegs R HIA hk LBk LF' mk HHk) | exact TO | exact TOL | exact STb | exact SCSk
              | exact TS | exact TSL | reflexivity | (cbv beta; clear; lia)
              | (clear - ALO LOS; pose proof (alloc_ceiling_pos (L := arl_L R)); lia) | (clear - SLO1 NER NEEDR; lia) | (clear - SP1M; Z.div_mod_to_equations; lia)
              | match goal with |- ?g => idtac "GB-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_query_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & r & E & MU2 & WM2 & MI2 & ST2 & RR). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    eapply CONT; [| exact RR]. exact (linv_scratch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lo LI MU2 ltac:(clear; lia) WM2 MI2 ST2).
    all: match goal with |- ?g => idtac "GB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition LST (pc : Z) (mk : mem) (i : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s10v : word) : machine_state := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "(43.(44.O11.(14.&40.Vsp1,)Vgp,Vtp,O10.O?.O>.Vsp,(14.&40.Vsp1,)O=.O<.O;.O:.O9.O8.O7.O6.(14.&40.VFB,)(14.&40.(16.VFB,+20.))(14.&40.(16.(4>.VFB,+3.)(4?.(32.VR,))))(14.&40.(4?.(32.VR,)))(14.&40.(16.VIDS,(5>.+4.O12.)))(14.&40.-4.)(14.&40.(16.VIDS,(5>.+4.O12.)))(14.&40.VFB,)O1.(14.&40.(16.VFB,+170.))O5.O4.O3.O2.)VF,(14.&40.O14.)Vfc,(45.(4.&40.))O13.(46.$1.))")
(* [comment removed for export] *).

  #[using="Type"] Lemma linv_slots : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)P,(35.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(2;.$1.R15.(16.Vsp1,+8.)(19.R8.R7.R6.))")
(* [comment removed for export] *).
  Proof. intros until nb. (intros dd_H; ddestruct dd_H as ((_ & _ & _ & _ & _ & _ & _ & _ & (S & _) & _) & _)). exact S. Qed.

  Ltac inlist := cbn [In app grp_mpds pt_mpds]; repeat (first [ left; reflexivity | right ]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01W0@L11440237739.1  L12808385313.0  L12916956843.1  L14077532924.219L14892571425.0  L15195629121.1  L15781436697.201L16075583565.249L16075583692.264L16075583823.219L16075583950.234L16075584073.189L16075584200.204L16908924412.174L18451338811.201L18451338938.202L20491039612.249L20652137081.1  L21485383339.1  L22151451819.1  L22409920380.234L2295337761.0   L23372322425.1  L23952587329.1  L2397676628.0   L24326207553.1  L28948604668.189L30656207425.1  L32781806251.1  L32930889387.1  L3519066119.1   L35539854113.0  L35668120898.7  L3621892907.298 L37251195161.201L40240748156.234L41260690497.1  L4606099115.1   L47216798497.0  L48937103345.282L49629343297.1  L50616353679.264L50671553195.1  L52220581018.202L53246223740.204L54048688929.0  L54101625409.1  L54992078076.219L55790407322.202L5581275937.0   L56494227009.1  L58573668988.204L59393203371.1  L60098763854.3  L60178444865.1  L60558678699.1  L61663431063.298L63586738753.1  L65096641020.189L66062374908.249L805459627.1    L8060680993.0   L882378613.2    L8848476737.1   L910584385.1    L9404489852.174 L9786907307.1   Q13394240522.222Q1433360151.207 Q15022709143.192Q15236711831.222Q15901829514.237Q19405276319.177Q20013594135.207Q20614549399.222Q21641572669.204Q21912640266.252Q27938377354.252Q30741491595.205Q32672170138.205Q33949708298.267Q34977081633.285Q35291925783.252Q36548891948.204Q37991553687.192Q3853489290.207 Q41259381015.237Q45987792415.177Q50734057021.204Q51727360410.205Q53876850434.177Q58026207754.192Q63185340972.204Q63755819927.267Q64054320522.207Q66561630474.192Q67147694615.237Q67302837634.177Q6739354144.285 Q68382001803.205Q7366406794.237 Q7526228119.252 Q9874769418.222 00000400500900O00P00T01?01@01A01B01C01D01E01[01\01]02302702;02?02U02V02Z02^02_02c03903=03A03E03I03J03a04=04h05>05B05F05G05]05a06706;06k07A07B07F07\08L08M08Q08g08k09509909=09Y09]0:30:I0:M0:N0:T0:X0:\0;20;60;\0<20<H0<^0=D0=j0>@0>V0?60?\0@B0@b0AB0Ah0BN0Bd0CD0CZ0D@0DV0E<0E\0F<0FR0G80GX0Gn0HT0I:0IP0If0J<0J\0KB0KX0L>S2FBSS2FBS2LF2sp3PKA2FB3sp13LFBSS2FBS2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLFFFFFFS2LF2sp3PKA2FB3sp13LFBFFS2LF2sp3PKA2FB3sp13LFBS2FBS2FBS2FBS2LF2sp3PKA2FB3sp13LFBSS2FBS2FBSS2FBS2LF2sp3PKA2FB3sp13LFBS2FBS2FBS2FBS2FBSS1R3HIA1h2sp2lo3TOP3HT0S2LF2sp3PKA2FB3sp13LFB2b22B2S2LF2sp3PKA2FB3sp13LFB3v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFBS2FBS2FBSS2LF2sp3PKA2FB3sp13LFBS2FBS2LF2sp3PKA2FB3sp13LFBS2FBS2LF2sp3PKA2FB3sp13LFB4gref3v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFBSS2FBS2LF2sp3PKA2FB3sp13LFBS2LF2sp3PKA2FB3sp13LFB4gref3v163v173v184NSH'3NSLSS2FBS2LF2sp3PKA2FB3sp13LFBS2FBS1R2lo3LOSS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2b12B1S2FBS2LF2sp3PKA2FB3sp13LFBS2LF2sp3PKA2FB3sp13LFBS2FBSS1i2IBS2FBS2FBS2LF2sp3PKA2FB3sp13LFBS2FBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2sp2lo3sp13SP13LFBS2LF2sp2lo3sp13SP13LFBS2LF2sp2lo3sp13SP13LFBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2sp2lo3sp13SP13LFBS2LF2sp2lo3sp13SP13LFBS2LF2FB3LFB3v163v173v184NSH'3NSLS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSLS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2sp2lo3sp13SP13LFBS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2sp2lo3sp13SP13LFBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2sp2lo3sp13SP13LFBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2sp2lo3sp13SP13LFBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2FB3LFB3v163v173v184NSH'3NSLS2LF2sp2lo3sp13SP13LFBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2sp2lo3sp13SP13LFBS2LF2sp2lo3sp13SP13LFBS2LF2sp2lo3sp13SP13LFBS2LF2FB3LFB3v163v173v184NSH'3NSLS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NERS2LF2sp2lo3sp13SP13LFBS1R5NEEDR2LF2sp2lo3SLO3sp13SP13LFB3NER". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF IDSN"] Lemma cmp_chain : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pi,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps10v,(4.&40.)P,(35.R27.R26.R25.R24.R23.R22.R21.=R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)P,(17.(?.=R13.)(?.R13.+<.))P,(?.(16.(16.R26.$39.)$5<.)(3:.VLEN,))P,(?.(16.(16.(16.R26.(3;.=))+15.)$5=.)(3<.Vd,))P,Pm',P,(4.&40.)(5.(4.&8.))Py,(4.&40.)Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Pya0,(4.&40.)Pya1,(4.&40.)Pya2,(4.&40.)Pya3,(4.&40.)Pya4,(4.&40.)Pya5,(4.&40.)Pya6,(4.&40.)Pya7,(4.&40.)Py3,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Pys10,(4.&40.)P,(35.R3=.R3<.R12.R3:.R39.R38.R37.=R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)(3?.$1.(40.$1.VR,VHIA,R3>.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(6?.+;10;0.R13.R29.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.))(3?.$1.(40.$1.VR,VHIA,R2<.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(6?.+;1018.R2:.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros LI IB VB FB' NEXT.
    dpose LI as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & RT & HG & AP & GL & HIDS & C24k & SLP).
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    assert (CFBk : crange (hcs asegs R HIA hk) FB 1024) by (exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))).
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    dpose (Forall_inv (Forall_inv_tail CHk)) as (PBN & _ & _). cbn [fst snd] in PBN.
    pose proof HG as HGc. ddestruct HGc as (_ & _ & _ & EgP & EgA & EgB & EgN & _ & _ & _ & (EgX & EgY & EgZ & _ & _ & _) & _ & HGT & _).
    unfold grp_tail_cells in HGT. replace (REF + 120) with (FB + 152) in HGT by (clear; lia).
    unfold SLL in SLOTS. unfold LST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { eapply NEXT. exact LI. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    { eapply NEXT. exact LI. }
    clear K1 K2.
    clear HHk FHD FSH NSH' FSHR SAVE NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk PBN HGT EBk0 TOK RT HG AP GL HIDS C24k SLP.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 376) with (md_addr dP) by (rewrite EP; clear; lia). replace (FB + 40) with (md_addr (g_P gref)) by (rewrite EgP; clear; lia).
    eapply (linv_cmp hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb dP (g_P gref) 725052); [exact LI| left; inlist| right; inlist| clear; lia| reflexivity|].
    intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI1. clear SLOTS MU WM LI.
    replace (md_addr dP) with (FB + 376) by (rewrite EP; clear; lia). replace (md_addr (g_P gref)) with (FB + 40) by (rewrite EgP; clear; lia).
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI1) as SLOTS. unfold SLL in SLOTS.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. if_cases K1; zify_cond K1.
    { eapply NEXT. exact LI1. }
    clear K1.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 392) with (md_addr dA) by (rewrite EA; clear; lia). replace (FB + 56) with (md_addr (g_A gref)) by (rewrite EgA; clear; lia).
    eapply (linv_cmp hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb dA (g_A gref) 725068); [exact LI1| left; inlist| right; inlist| clear; lia| reflexivity|].
    intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI2. clear SLOTS MU WM LI1.
    replace (md_addr dA) with (FB + 392) by (rewrite EA; clear; lia). replace (md_addr (g_A gref)) with (FB + 56) by (rewrite EgA; clear; lia).
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI2) as SLOTS. unfold SLL in SLOTS.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. if_cases K2; zify_cond K2.
    { eapply NEXT. exact LI2. }
    clear K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 408) with (md_addr dB) by (rewrite EB'; clear; lia). replace (FB + 72) with (md_addr (g_B gref)) by (rewrite EgB; clear; lia).
    eapply (linv_cmp hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb dB (g_B gref) 725084); [exact LI2| left; inlist| right; inlist| clear; lia| reflexivity|].
    intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI3. clear SLOTS MU WM LI2.
    replace (md_addr dB) with (FB + 408) by (rewrite EB'; clear; lia). replace (md_addr (g_B gref)) with (FB + 72) by (rewrite EgB; clear; lia).
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI3) as SLOTS. unfold SLL in SLOTS.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. if_cases K3; zify_cond K3.
    { eapply NEXT. exact LI3. }
    clear K3.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 472) with (md_addr dN) by (rewrite EN; clear; lia). replace (FB + 136) with (md_addr (g_N gref)) by (rewrite EgN; clear; lia).
    eapply (linv_cmp hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb dN (g_N gref) 725100); [exact LI3| left; inlist| right; inlist| clear; lia| reflexivity|].
    intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI4. clear SLOTS MU WM LI3.
    replace (md_addr dN) with (FB + 472) by (rewrite EN; clear; lia). replace (md_addr (g_N gref)) with (FB + 136) by (rewrite EgN; clear; lia).
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI4) as SLOTS. unfold SLL in SLOTS.
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    zstep. if_cases K4; zify_cond K4.
    { eapply NEXT. exact LI4. }
    clear K4.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 424) with (md_addr dX) by (rewrite EX; clear; lia). replace (FB + 88) with (md_addr (pt_X (g_G gref))) by (rewrite EgX; clear; lia).
    eapply (linv_cmp hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb dX (pt_X (g_G gref)) 725116); [exact LI4| left; inlist| right; inlist| clear; lia| reflexivity|].
    intros m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI5. clear SLOTS MU WM LI4.
    replace (md_addr dX) with (FB + 424) by (rewrite EX; clear; lia). replace (md_addr (pt_X (g_G gref))) with (FB + 88) by (rewrite EgX; clear; lia).
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI5) as SLOTS. unfold SLL in SLOTS.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    zstep. if_cases K5; zify_cond K5.
    { eapply NEXT. exact LI5. }
    clear K5.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 456) with (md_addr dZ) by (rewrite EZ; clear; lia). replace (FB + 120) with (md_addr (pt_Z (g_G gref))) by (rewrite EgZ; clear; lia).
    eapply (linv_cmp hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb dZ (pt_Z (g_G gref)) 725132); [exact LI5| left; inlist| right; inlist| clear; lia| reflexivity|].
    intros m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI6. clear SLOTS MU WM LI5.
    replace (md_addr dZ) with (FB + 456) by (rewrite EZ; clear; lia). replace (md_addr (pt_Z (g_G gref))) with (FB + 120) by (rewrite EgZ; clear; lia).
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI6) as SLOTS. unfold SLL in SLOTS.
    pose proof (munch_refl ([] : list ivl) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    zstep. if_cases K6; zify_cond K6.
    { eapply NEXT. exact LI6. }
    clear K6.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 440) with (md_addr dY) by (rewrite EY; clear; lia).
    eapply (linv_getbit hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb dY 0xb109c); [exact LI6| left; inlist| clear; lia| reflexivity|].
    intros m7 b1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI7 B1. clear SLOTS MU WM LI6.
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI7) as SLOTS. unfold SLL in SLOTS.
    pose proof LI7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL0).
    pose proof (munch_refl ([] : list ivl) m7) as MU. pose proof (wmono_refl asegs m7) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (FB + 104) with (md_addr (pt_Y (g_G gref))) by (rewrite EgY; clear; lia).
    eapply (linv_getbit hk LBk _ v f gref idg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb (pt_Y (g_G gref)) 0xb10ac); [exact LI7| right; inlist| clear; lia| reflexivity|].
    intros m8 b2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI8 B2. clear SLOTS SL0 MU WM LI7.
    pose proof (linv_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI8) as SLOTS. unfold SLL in SLOTS.
    pose proof (munch_refl ([] : list ivl) m8) as MU. pose proof (wmono_refl asegs m8) as WM.
    (* [comment removed for export] *)
    zstep. if_cases K7; zify_cond K7.
    - (* [comment removed for export] *)
      zstep.
      eapply (id_tail hk LBk m8 v f gref idg 0 dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb i 0);
        [exact LI8| clear - IB; lia| clear; lia| exact VB| exact FB'].
    - eapply NEXT. exact LI8.
    all: match goal with |- ?g => idtac "CHAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@L10351576259.2  L10472354596.192L1256012732.0   L14186142497.0  L26316482715.0  L28717461921.0  L31998781128.6  L32586543723.0  L35870121979.3  L42862020415.6  L44056310188.3  L44200638400.2  L44200638449.2  L46595161198.6  L46647841290.196L46650066845.193L54013620277.6  L54611502733.5  L59308549609.3  L62586290822.10 L882378613.2    L957827166.0    Q16797194194.203Q26295627581.199Q29563946216.199Q50458135125.199Q57754508096.196Q57756423456.199Q57758421415.203Q6282819336.196 Q63911392935.199Q8958434247.196 00000600700800900:00;00N00O00X01101;01D01M01a02c03e04=04O04X04i04o05005V06306^07A07g08M09309Y0:?0:\S1i2IBFSSSSS1d1f3FB'4FSG04GFF0SS1d1f3FB'S3LEN1v2VB4PSG04GLP04GFP0S3LEN1v2VBS3idj3IJBS3idj3IJ1S3LEN1v2VB4PSG04GFP0S3IDS2LF2sp3PKA2FB3sp13LFB3NZP3v163v173v181i2IB4IDLO4IDHI4NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB3NZP3v163v173v181i2IB4IDLO4IDHI4NSH'3NSLS1d1f3FB'4FSG04GLF04GFF0S1i2IB3idj3IJB3IJZS1i2IB2NJS2r33RR31r2KR1q1HS1i2IBSS3IDS2LF3LFB3v163v173v181i2IB4NSH'3NSLS2LF3LFB3v163v173v184NSH'3NSLS3IDS2LF3LFB3v163v173v181i2IB4IDLO4NSH'3NSLS3IDS2LF3LFB3v163v173v181i4NSH'3NSLS3IDS2LF3LFB3v163v173v181i2IB4NSH'3NSLS3IDS2LF3LFB3v163v173v181i2IB4NSH'3NSLS3IDS2LF3LFB3v163v173v181i2IB4NSH'3NSLS3IDS2LF3LFB3v163v173v181i2IB4NSH'3NSLS3IDS2LF3LFB3v163v173v181i2IB4NSH'3NSLS2LF3LFB3v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF HGL IDSN"] Lemma iter_head : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pi,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps10v,(4.&40.)P,(35.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)P,(17.(?.=R13.)(?.R13.+<.))P,(?.(16.(16.(16.(16.R27.$39.)$48.)$39.)$5<.)(3:.VLEN,))P,(?.(16.(16.(16.(16.(16.R27.(3;.=))(49.=))(3;.=))+15.)$5=.)(3<.Vd,))P,Ph',(0.$1.VR,VHIA,)PLB',(2.$3.)Pm',P,(4.&40.)(5.(4.&8.))Pg',$34.Pidj,$6.Py,(4.&40.)Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Pya0,(4.&40.)Pya1,(4.&40.)Pya2,(4.&40.)Pya3,(4.&40.)Pya4,(4.&40.)Pya5,(4.&40.)Pya6,(4.&40.)Pya7,(4.&40.)Py3,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Pys10,(4.&40.)P,(35.R16.R15.R14.(16.(16.R3?.$39.)$48.)(16.(16.R3>.(3;.=))(49.=))R13.R12.=R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)P,(20.(5.(4.&40.))(70.(4.&40.)$5:.(71.R2=.))(72.(4.&40.)(14.&40.R13.)))P,(17.(?.+1.R14.)(?.R14.+=.))(3?.$1.(40.$1.VR,VHIA,R19.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(6?.+;1018.R17.R2?.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.))(3?.$1.(40.$1.VR,VHIA,R2=.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(6?.+;0??0.R2;.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros LI IB VB FB' K.
    assert (PSG0 : 0 <= pk_set_group_PHI) by (unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (FSG0 : 0 <= pk_set_group_FR) by (unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia).
    assert (GLP0 : 0 <= group_load_PHI) by (unfold group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (GLF0 : 0 <= group_load_FRn 0) by (unfold group_load_FRn, calls_FR, fr_charge; clear; lia).
    assert (GFP0 : 0 <= GF_PHI) by (unfold GF_PHI, AVOL_CALL; clear; lia).
    assert (GFF0 : 0 <= GF_FR 0) by (unfold GF_FR, fr_charge; clear; lia).
    destruct (AImgGlobals.img_norz_sound _ _ IDSN) as (_ & IDLO & IDHI & _). unfold AImgGlobals.IMG_LO, AImgGlobals.IMG_HI in IDLO, IDHI.
    pose proof LI as (EBk & _). pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    unfold LST.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply (linv_gfree hk LBk mk v f gref idg rg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb 0xb0ff8);
      [exact LI| clear; lia| reflexivity| clear - VB PSG0 GLP0 GFP0; lia| clear - FB' FSG0 GLF0 GFF0; lia|].
    intros h2 LB2 m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI2.
    clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM LI. clear w0 w1 w2.
    dpose LI2 as (EBk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIDS2 & _). pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    pose proof (ids_aobj h2 LB2 LF' m2 HHk) as OIDS.
    pose proof (hcs_ok asegs R HIA h2) as CSOKk.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk OIDS (IDS + 4 * i) 4.
    (* [comment removed for export] *)
    destruct (nth_error P_pk_ecparams_D.IDWS (Z.to_nat i)) as [w|] eqn:NJ; [| exfalso; apply nth_error_None in NJ; cbn in NJ; clear - NJ IB; lia].
    ddestruct (P_pk_ecparams_D.ids_nth i w NJ ltac:(clear - IB; lia)) as (idj & -> & IJB & IJZ & _).
    assert (IJ1 : 1 <= idj <= 13) by (clear - IJB IJZ IB; lia).
    pose proof (u32ro_read asegs m2 IDS P_pk_ecparams_D.IDWS i _ (wa (IDS + 4 * i)) (ids_bytes_at m2 HIDS2) NJ ltac:(clear - IB; lia) eq_refl) as RDJ.
    clear HIDS2.
    zstep. clear RDJ. rewrite (sx32_small_ep idj) by (clear - IJB; lia).
    (* [comment removed for export] *)
    zstep. zstep.
    eapply (linv_gload h2 LB2 m2 _ _ 9 MBEDTLS_ERR_MPI_ALLOC_FAILED dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb idj 0xb1014);
      [exact LI2| clear - IJ1; lia| clear; lia| reflexivity| clear - VB PSG0 GLP0 GFP0; lia| clear - FB' FSG0 GLF0 GFF0; lia|].
    intros h3 LB3 m3 r3 g3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? LI3.
    clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM LI2 OIDS CSOKk. clear w0 w1 w2.
    dpose LI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GL3 & _).
    pose proof (P_pk_ecparams_B.gl_result_range _ _ _ _ _ _ _ GL3) as RR3.
    pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      zstep. zstep.
      eapply (id_tail h3 LB3 m3 _ _ g3 idj r3 dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb i r3);
        [exact LI3| clear - IB; lia| exact RR3| clear - VB; lia| clear - FB'; lia].
    - assert (Z0 : r3 = 0) by (clear - KR RR3; Z.div_mod_to_equations; lia).
      subst r3. eapply K; [exact LI3| first [exact NJ| reflexivity]| exact IJ1].
    all: match goal with |- ?g => idtac "HEAD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma linv_hids : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)P,(35.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(17.(51.$1.VR,VHIA,R17.R16.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R15.)(2;.$1.R15.VIDS,(<.$7.(2<.#38.$2=.)(>.$7.))))")
(* [comment removed for export] *).
  Proof. intros until nb. (intros dd_H; ddestruct dd_H as ((HH & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIDS & _)). exact (conj HH HIDS). Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@L1256012732.0   L12795156921.2  L14788517257.5  L22182338953.2  L2397676628.0   L26316482715.0  L32586543723.0  L34680481239.2  L35086271488.3  L35870121953.4  L35870121979.5  L35872073442.7  L35872073442.8  L35907695816.205L35913851231.202L41249998872.2  L44054213021.4  L44056119454.7  L44056119454.8  L44056310188.5  L45665642841.2  L46647837673.203L49279378576.2  L51649090198.3  L52707436972.208L59308597729.3  L59308633210.6  L59310646736.3  L62101380686.0  L7048586559.2   L957827166.0    Q16180368849.208Q26295627581.208Q27535561811.205Q36346228993.211Q50458135125.208Q5053260098.208 Q59799641920.211Q59801377735.208Q59803588007.205Q8958434247.205 00000100800I00P00Q00R00S00Y00d00o01=01Q01b02U03H03N03[04104D04S04^05Q05Z05c06I06S06e06o07007;07<07^08408N08h09B09\0:90:V0;30;ISS3IDS1iS1i2IB3idn3INZ2NZS3IDS1iSSSS1i2IBS3IDS1i3I12S1d1i1f3FB1S1d2pf1i1f3FB'S1d2pv2pf1i1f3FB12M0S1d2pv1i1f3FB12M0S3IDS2LF2sp3PKA2FB3sp13LFB3NZP1n1i3EN'2IB4IDLO4IDHIS3IDS2LF2sp3PKA2FB3sp13LFB3NZP1n1i3EN'2IB4IDLO4IDHIS1i2IBS3LEN1i1v3VB1S3LEN2pv2pf1i1v3VB12M0S3LEN2pf1i1v3VB12M0S3LEN2pv1i1v2VBS4GLP04GFP0S3IDS2LF2sp3PKA2FB3sp13LFB3NZP1n1i3EN'2IB4IDLO4IDHIS3idn3INBS1n1i3EN'S2LF2sp3PKA2FB3sp13LFB1n1i3EN'3idn3INBS1i3EN'2IBS3IDS1i2IB4IDHI2KWS1i2IB3NJ1SS4GLF04GFF0SS3IDS2LF3LFB1n2pv2pf1i3EN'2IB4IDLOS2LF3LFB1n2pv2pf1i3EN'S3IDS2LF3LFB1n2pv2pf1i3EN'S3IDS2LF3LFB1n2pv2pf1i3EN'S3IDS2LF3LFB1n2pv2pf1i3EN'S3IDS2LF3LFB1n2pv2pf1i3EN'S3IDS2LF3LFB1n2pv2pf1i3EN'2IBS3IDS2LF3LFB1n2pv2pf1i3EN'2IBS3IDS2LF3LFB1n2pv2pf1i3EN'2IBS2LF3LFB1n2pv2pf1i3EN'". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF HGL IDSN"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Pn,$73.Pi,$6.Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pgref,$34.Pidg,$6.Prg,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps10v,(4.&40.)P,(20.$6.(74.R29.)(6;.+=.R28.))P,(17.(?.=R29.)(?.R29.+<.))P,(35.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)P,(?.(16.(16.(16.R27.(5>.(6;.+=.R2;.)(16.$39.$48.)))$39.)$5<.)(3:.VLEN,))P,(?.(16.(16.(16.(16.R27.(5>.(6;.+=.R2<.)(16.(3;.=)(49.=))))(3;.=))+15.)$5=.)(3<.Vd,))(3?.$1.(40.$1.VR,VHIA,R2<.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(6?.+;0??0.R2:.R2=.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until s10v; intros EN' IB LI VB FB'; [exfalso; clear - EN' IB; lia|].
    assert (PSG0 : 0 <= pk_set_group_PHI) by (unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (FSG0 : 0 <= pk_set_group_FR) by (unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia).
    assert (GLP0 : 0 <= group_load_PHI) by (unfold group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (GLF0 : 0 <= group_load_FRn 0) by (unfold group_load_FRn, calls_FR, fr_charge; clear; lia).
    assert (GFP0 : 0 <= GF_PHI) by (unfold GF_PHI, AVOL_CALL; clear; lia).
    assert (GFF0 : 0 <= GF_FR 0) by (unfold GF_FR, fr_charge; clear; lia).
    set (pv := GF_PHI + group_load_PHI) in *. set (pf := GF_FR 0 + group_load_FRn 0) in *.
    assert (PV0 : 0 <= pv) by (unfold pv; clear - GLP0 GFP0; lia). assert (PF0 : 0 <= pf) by (unfold pf; clear - GLF0 GFF0; lia).
    assert (VB1 : v + pv + (13 - (i + 1)) * pv + GF_PHI + pk_set_group_PHI <= pk_ecparams_PHI LEN) by (clear - VB; lia).
    assert (FB1 : f + pf + (13 - (i + 1)) * pf + GF_FR 0 + 21 + pk_set_group_FR <= pk_ecparams_FR d) by (clear - FB'; lia).
    assert (M0 : 0 <= (13 - (i + 1)) * pv /\ 0 <= (13 - (i + 1)) * pf) by (split; apply Z.mul_nonneg_nonneg; first [exact PV0| exact PF0| clear - IB; lia]).
    destruct (AImgGlobals.img_norz_sound _ _ IDSN) as (_ & IDLO & IDHI & _). unfold AImgGlobals.IMG_LO, AImgGlobals.IMG_HI in IDLO, IDHI.
    eapply (iter_head hk LBk mk v f gref idg rg dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb i);
      [exact LI| exact IB| unfold pv in *; clear - VB1 M0 PSG0 GFP0; lia| unfold pf in *; clear - FB1 M0 FSG0 GFF0; lia|].
    intros h' LB' m' g' idj y y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 ys10 LI' NJ IJ1.
    fold pv in LI'. fold pf in LI'.
    eapply (cmp_chain h' LB' m' _ _ g' idj dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb i);
      [exact LI'| exact IB| clear - VB1 M0; lia| clear - FB1 M0; lia|].
    intros m2 z z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 zs10 LI2.
    (* [comment removed for export] *)
    destruct (linv_hids _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI2) as (HHk & HIDS2).
    pose proof (AIh_laws asegs R HIA h') as LAWS. pose proof (KF_kinv asegs R HIA h' mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    pose proof (ids_aobj h' LB' LF' m2 HHk) as OIDS.
    pose proof (hcs_ok asegs R HIA h') as CSOKk.
    unfold LST.
    zstep. if_cases KW; zify_cond KW; [exfalso; clear - KW IDLO IDHI IB; rewrite ?unsigned_lit in KW by lia; first [lia | (Z.div_mod_to_equations; lia)]|]. clear KW.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    shadow_chk OIDS (IDS + 4 * i + 4) 4.
    (* [comment removed for export] *)
    destruct (nth_error P_pk_ecparams_D.IDWS (Z.to_nat (i + 1))) as [w|] eqn:NJ1; [| exfalso; apply nth_error_None in NJ1; cbn in NJ1; clear - NJ1 IB; lia].
    ddestruct (P_pk_ecparams_D.ids_nth (i + 1) w NJ1 ltac:(clear - IB; lia)) as (idn & -> & INB & INZ & _).
    pose proof (u32ro_read asegs m2 IDS P_pk_ecparams_D.IDWS (i + 1) _ (wa (IDS + 4 * i + 4)) (ids_bytes_at m2 HIDS2) NJ1 ltac:(clear - IB; lia) ltac:(f_equal; clear; lia)) as RDJ.
    clear HIDS2.
    zstep. zstep. clear RDJ. rewrite (sx32_small_ep idn) by (clear - INB; lia).
    zstep. zstep. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      assert (NZ : idn <> 0) by (intros ->; clear - KN; first [apply KN; reflexivity| (vm_compute in KN; congruence)]).
      assert (IB1 : 0 <= i + 1 <= 12) by (clear - IB INZ NZ; lia).
      replace (IDS + 4 * i + 4) with (IDS + 4 * (i + 1)) by (clear; lia).
      eapply (IH (i + 1) h' LB' m2 _ _ g' idj 0 dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb);
        [clear - EN'; lia| exact IB1| exact LI2| unfold pv in *; clear - VB1; lia| unfold pf in *; clear - FB1; lia].
    - (* [comment removed for export] *)
      assert (Z0 : idn = 0) by (first [exact KN| clear - KN INB; Z.div_mod_to_equations; lia]).
      assert (I12 : i + 1 = 13) by (apply INZ; exact Z0).
      zstep. zstep.
      replace (IDS + 4 * i + 4) with (IDS + 4 * 13) by (clear - I12; lia).
      eapply (id_tail h' LB' m2 _ _ g' idj 0 dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb 13 0);
        [exact LI2| clear; lia| clear; lia| clear - VB1 M0; lia| clear - FB1 M0; lia].
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma eb_ch_incl : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PCH',(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R;.R:.R9.R8.R7.R6.R5.R4.R2.R1.)P,Pc,(8.$6.(2.$7.))P,(22.(8.$6.(2.$7.))R1.R5.)(22.(8.$6.(2.$7.))R2.R7.)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R=.R<.R;.R:.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH CH' T WE EBk INC'. eb_open EBk.
    unfold EB. split; [exact HHk|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
    split; [dexists w0, w1, w2; exact FHD|]. split; [exact (conj FSH NSH')|]. split; [exact FSHR|].
    split; [exact SAVE|]. split; [exact (conj SLOTS NSL)|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [exact MIk|].
    split; [exact PRES|]. split; [exact IDSk|].
    split; [rewrite Forall_forall in CHk |- *; intros c Hc; exact (CHk c (INC' c Hc))|].
    split; [exact EXTk| exact FRk].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L12241130255.2 L13948747720.1 L1540877545.3  L16255647091.3 L18678294768.11L18678294768.16L18678294768.19L20728242168.9 L2184537823.10 L24128180555.1 L27797056548.10L3177134184.1  L33177279630.3 L37312170392.9 L52045659405.3 L53577728712.1 L54971811087.1 L565330731.1   L56813410348.10L56887394084.10L6203936179.1  L66151427842.16L67028776265.0 L68694423824.2 L6899380056.1  L8464343071.10 L9631767084.2  00000700<00H00Q00b01901Q01m02U02Y03:03>03H03d04004504904=04H04i04n05G05H05N05R06306:S2FB2F0S3sp1S2sp3sp13SP1S2FB1c2HcS1R1u1w1a1n2A12HwS1R2FB1u1w2F11a1n2A12W2S1R1u1w1a1n2A11N1k2FC2W2S1R3HIA1h2hk1v2h22dv3HVk3HV2S1R5NEEDR2sp2lo3LOS3sp13SP13ALO4SLO13NERS2FBS1R5NEEDR2lo3LOS3sp13ALO4SLO13NERS2FBS2FB2ac2B2S1R3HIA1h2hk1f2h22df3HFk3HF2S2sp3sp13SP1S3sp1S2FBS2FBS2FB1u1w2HwS1R5NEEDR2lo3LOS3sp13ALO4SLO13NERS3sp1S2FB2r02F81q1r1H2H02q02H4SS1R2FBS2FBS1R5NEEDR2lo3LOS3sp13ALO4SLO13NERS2FB2F0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO SP1 F64 FRSH"] Lemma eb_step_ids : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))Pdv,$6.Pdf,$6.PT2,(2.$3.)PLBp,(2.$3.)PWXf,(2.$9.)PWXe,(2.$9.)PWE',(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)P,(51.$1.VR,VHIA,R;.R:.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R9.)P,(11.$1.R:.)P,(12.$1.R;.Vlo,Vsp1,)P,(2?.$1.VR,R8.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)Vsp1,(75.VR,)(76.$1.VR,VHIA,R18.)(1;.$9.R7.R6.)R16.R<.)P,(20.$6.(77.$1.VR,VHIA,R?.)(77.$1.VR,VHIA,R19.))P,(20.$6.(76.$1.VR,VHIA,R10.)(76.$1.VR,VHIA,R1:.))P,(20.$6.(78.$1.VR,VHIA,R11.)(78.$1.VR,VHIA,R1;.))P,Px,$6.P,(33.$1.VR,VHIA,R1=.R1.)(33.$1.VR,VHIA,R14.R2.)P,(?.(79.$1.VR,VHIA,R13.)(16.(79.$1.VR,VHIA,R1=.)R10.))P,(?.(7:.$1.VR,VHIA,R14.)(16.(7:.$1.VR,VHIA,R1>.)R10.))P,Pb,$3.P,(22.$3.R1.VLB,)(22.$3.R2.R11.)P,(52.$9.(7;.VR,VLB,VLF,VFB,)R?.)P,Px,$6.P,(7<.R?.R1.)(7<.R11.R2.)P,Px,$6.P,(7<.R10.R1.)(7<.R1;.R2.)P,(52.(8.$6.$6.)Lw,(8.$6.$6.)(?.(4=.$6.$6.R1.)(7=.(55.VR,)))R11.)P,(57.$1.VIDONE,VIDS,R18.)P,(52.(8.$6.$6.)Lw,(8.$6.$6.)(4;.(?.(4=.$6.$6.R1.)VFB,)(?.(16.VFB,+18.)(4<.$6.$6.R1.)))(1;.$9.R14.R13.))P,(52.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(30.(1;.$9.R16.R15.)(4<.$6.(2.$7.)R1.)(74.(7>.(4=.$6.(2.$7.)R1.))))R1?.)P,(7?.VLB,R18.R1<.)P,Pb,$3.P,(22.$3.R1.R1:.)(80.VR,VLB,VLF,(4<.$6.$6.R2.)(4=.$6.$6.R2.))(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R1?.R1>.R1=.(16.R26.R1<.)(16.R25.R1;.)R24.R23.R22.R1:.R16.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE h2 LB2 m2 dv df T2 LBp WXf WXe WE' EBk HH2 MI2 ST2 HP ET ES EF HCS2 HV2 HF2 SUB HWX HE1 HE2 HWC IDS2 HWH HCD EXT2 FR2.
    set (WX := WXf ++ WXe) in *.
    ddestruct EBk as (HHk & (ETk & ESk & EFk) & HCSk & (HVk & HFk) & (w0 & w1 & w2 & FHD) & (FSH & NSH') & FSHR & SAVE & (SLOTS & NSL) & STlo & SThi & STb & MIk & PRES & IDSk & CHk & EXTk & FRk).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    assert (CFBk : crange (hcs asegs R HIA hk) FB 1024) by (exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))).
    assert (CSHD : forall c, FB <= c < FB + 1024 -> cshd R LBp LF' (arl_stklo R) (hstkhi asegs R HIA hk) c).
    { intros c Hc. right; right; left. exists (FB, 1024). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJS : forall a n, alloc_ceiling <= a -> disjoint_from WX a n).
    { intros a n A1. unfold WX. apply PkTmp.disjoint_from_app.
      - clear - HWX F1 A1. induction WXf as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWX as [|? ? Hw HWr]; subst.
        split; [| exact (IH HWr)]. destruct Hw as [[W1 W2]|(N & k & (_ & FC & _) & W1 & W2)]; cbn [fst snd] in *; lia.
      - clear - HWC A1. induction WXe as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWC as [|? ? Hw HWr]; subst. cbn [fst snd] in Hw.
        split; [lia| exact (IH HWr)]. }
    unfold EB.
    split; [exact HH2|].
    split; [split; [rewrite ET; exact ETk| split; [rewrite ES; exact ESk| rewrite EF; exact EFk]]|].
    split; [intros x Hx; apply HCS2, HCSk, Hx|].
    split; [split; [clear - HVk HV2; lia| clear - HFk HF2; lia]|].
    split. { dexists w0, w1, w2. eapply (presA_rw_cells asegs R); [exact HP| exact FHD| |].
             - eapply client_range_block; [apply in_app_iff; right; left; reflexivity| clear; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Z.min_l by (clear; lia); clear; lia].
             - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - HWH. induction WX as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWH as [|? ? Hw HWr]; subst. cbn [fst snd] in Hw. split; [lia| exact (IH HWr)]. }
    split. { split; [| exact NSH']. eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hk)); [exact CSOKk| | exact F8| clear - F0; lia| exact HP| exact FSH|].
             - rewrite NSH'. eapply crange_sub; [exact CFBk| clear; lia| clear; lia].
             - rewrite NSH'. intros c Hc. apply CSHD. clear - Hc. lia. }
    split. { replace (SHB + 80) with (Z.shiftr (FB + 640) 3 + al_sb AL) in * by (rewrite SH640; clear; lia).
             eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hk)); [exact CSOKk| | clear - F8; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP| exact FSHR|].
             - cbn [cells_size csize Nat.add]. eapply crange_sub; [exact CFBk| clear; lia| clear; lia].
             - cbn [cells_size csize Nat.add]. intros c Hc. apply CSHD. clear - Hc. lia. }
    split. { eapply (presA_rw_cells asegs R); [exact HP| exact SAVE| apply client_range_stack; clear - SP1; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split. { split; [| exact NSL]. eapply (presA_rw_cells asegs R); [exact HP| exact SLOTS| apply client_range_stack; clear; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split. { eapply (presA_stk asegs R); [exact HP| exact STlo| clear; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split. { eapply (presA_stk asegs R); [exact HP| exact SThi| clear; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split; [exact ST2|]. split; [exact MI2|].
    split. { eapply (presW_hmono R HIA hk h2); [| exact HCS2| exact ES].
             eapply eb_pres_step; [exact PRES| exact HP| exact SUB| clear - SP1; lia| exact HWX| exact HE1| exact HE2]. }
    split; [exact IDS2|].
    split. { rewrite Forall_forall in CHk, HCD |- *. intros ac Hac. ddestruct (CHk ac Hac) as (Hc & B1 & B2). split; [| split; [exact B1| exact B2]].
             eapply (presA_rw_cells asegs R); [exact HP| exact Hc| | exact (HCD ac Hac)].
             eapply client_range_block; [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| exact B1| clear - B2; lia]. }
    split; [exact EXT2| exact FR2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0>L12128799109.1L19777938910.7L2333536794.13L25158360165.5L31775376236.3L36359398762.5L4800287082.3 L58459207789.4L6203936179.1 L62253338345.3L66668349941.1L900258061.9  00000300F01201@01I01[01e02002502>02A02cS1fS2FB1A1n2A12A21a2HaS1R3HIA1h2sp2lo3LOS3TOP3sp13SP13lo'3LO'1a2HaS2FB1A1n2A12A2S2FB1A2A1S1R2lo3LOS3lo'3LO'S1R3HIA2hkS2FB1A1n2A2S3sp1S2FB1A2A1S1vS1R3HIA1h2sp3TOP3sp13SP13lo'5HTOP0". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG IDOK PKA LOS SLO TOP HH0 SP1 F64 FRSH C DSP DPI DPC"] Lemma eb_munch2 : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pm2,P,(4.&40.)(5.(4.&8.))PA,$6.Pn,$6.Plo',$6.P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(;.(<.(8.$6.$6.)(=.$6.$6.R4.(16.R4.R3.))(<.(8.$6.$6.)(=.$6.$6.R2.Vsp1,)(>.(8.$6.$6.))))R=.R5.)P,(?.Vlo,R3.)P,(?.(16.VFB,+20.)R6.)P,(?.(16.R7.R6.)(16.VFB,+3?8.))P,(36.=R7.)P,(10.$1.R12.R:.)P,(11.$1.R;.)P,(12.$1.R<.Vlo,Vsp1,)P,(52.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(30.(<.(8.$6.$6.)(=.$6.$6.R=.(16.R=.R<.))(>.(8.$6.$6.)))(4<.$6.(2.$7.)R1.)(74.(7>.(4=.$6.(2.$7.)R1.))))R10.)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R18.R17.R>.R15.R14.R13.R12.R11.R10.R?.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE m2 A n lo' EBk MU LO' A1 A2 N0 WM MI2 ST2 HCD.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA h _ _ _ HH0) as HTOP0.
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    assert (HH2 : HM asegs R HIA hk LBk LF' m2).
    { eapply (hm_munch asegs R HIA hk LBk LF' _ mk m2 HHk MU WM).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; intros a Ha; left.
      - right; right. exists (FB + 32, 984). split; [apply in_app_iff; right; exact INFD| cbn [fst snd]; clear - Ha A1 A2; lia].
      - left. rewrite ETk. clear - Ha LOS LO' TOP SP1. lia. }
    assert (HP : presA asegs R LBk LF' sp1 (arl_stklo R) (hstkhi asegs R HIA hk) ([(A, A + n)] ++ []) mk m2).
    { cbn [app]. eapply (presA_drop_below asegs R HIA hk LBk LF' [(A, A + n)] lo' sp1 mk mk m2 sp1 HHk); [| clear; lia| clear - LOS LO'; lia].
      eapply presA_weaken; [| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl|].
      - eapply (presA_of_munch asegs R LBk LF' _ _ _ _ mk m2 (hcs asegs R HIA hk) (hcs_ok asegs R HIA hk)); [| | exact MU| exact WM].
        + apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
          * eapply crange_sub; [exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))| clear - A1; lia| clear - A2; lia].
          * eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS LO'; lia| rewrite ESk; clear - HTOP0 TOP SP1; lia].
        + intros c0 Hc. eapply cshd_hcs; [exact HHk| apply Z.le_refl| exact Hc].
      - intros x Hx. cbn [outside] in Hx |- *. tauto. }
    pose proof (eb_step hk LBk mk v f SH SL CH T WE hk LBk m2 0 0 T LBk [(A, A + n)] [] WE EBk0 HH2 MI2 ST2 HP eq_refl eq_refl eq_refl
                  ltac:(intros x Hx; exact Hx) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb])
                  ltac:(apply Forall_cons; [left; cbn [fst snd]; clear - A1 A2; lia| apply Forall_nil]) ltac:(intros x _; exact I) ltac:(intros x Hx; exact Hx)
                  ltac:(apply Forall_nil) I I ltac:(apply Forall_cons; [right; cbn [fst snd]; clear - A1; lia| apply Forall_nil])
                  ltac:(rewrite app_nil_r; exact HCD) EXTk FRk) as E2.
    replace (v + 0) with v in E2 by (clear; lia). replace (f + 0) with f in E2 by (clear; lia). exact E2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis HGI : ecp_group_init_stmtA asegs R HIA A_MT A_ECP_GROUP_INIT.
  Hypothesis HIDL : ecp_grp_id_list_stmtA asegs AL A_ECP_GRP_ID_LIST IDONE IDS.

  (* [comment removed for export] *)
  Definition data_iv (w : ivl) : Prop := hl_data_lo L <= fst w /\ snd w <= hl_data_hi L.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54677079007.1000000MS1R1u1w1B1k3DI13DI23CIM2W12W2". (* [comment removed for export] *)
  #[using="DIMG"] Lemma data_iv_blk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))PW,(2.$9.)PB,$6.Pk,$6.P,(51.$1.VR,VHIA,R6.R5.(<.(8.$6.$6.)(=.$6.$6.VFB,+400.)VLF,)R4.)P,(22.(8.$6.$6.)(=.$6.$6.R3.R2.)R6.)P,(52.$9.$81.R5.)(30.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk W B k HH HIn HW. destruct DIMG as [DI1 DI2].
    destruct (hm_apart asegs R HIA hk _ _ _ HH) as [HBR _]. rewrite Forall_forall in HBR.
    destruct (HBR _ ltac:(apply in_app_iff; left; exact HIn)) as (_ & _ & _ & CIM). cbn [fst snd] in CIM.
    induction W as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? [W1 W2] HWr]; subst. cbn [fst snd] in *.
    split; [clear - CIM DI1 DI2 W1 W2; lia| exact (IH HWr)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18680896816.1100000MS1R2FB1u1w1a1n2A12A22F22W12W2". (* [comment removed for export] *)
  #[using="HIA IMG NEEDR h LB LF sp lo LOS SLO sp1 SP1 F64 FRSH"] Lemma data_iv_frame : forall W a n, Forall data_iv W -> FB <= a -> a + n <= FB + 1024 -> disjoint_from W a n.
  Proof.
    intros W a n HW A1 A2. dpose eb_frame_facts as (F0 & F1 & F2 & _).
    induction W as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? [W1 W2] HWr]; subst. cbn [fst snd] in *.
    split; [clear - F2 A1 A2 W1 W2; lia| exact (IH HWr)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L11707642223.7 L11709910993.6 L12128799109.1 L15721644686.6 L16242446612.6 L22221326366.3 L24471993009.3 L33408245636.8 L44789844162.3 L4800287082.3  L52792927696.8 L53558083909.7 L53560016891.6 L59264391236.3 L59570281806.11L66047912540.8 L66668349941.1 00000>00H00K00^00j01601@01\01f02002K02b03503?03e04A04DS1R3IDS2I33DHIS1R3IDS2I3S1fS1R5IDONE3IDS2I12I2S1R5IDONE2I1S5IDONE1x2HxS2FB2ac2B1S1R5IDONE3IDS2FB2F22I12I22I3S3IDS1x2HxS1R3HIA2hkS1R5IDONE3IDS2I12I22I31a2HaS1R5IDONE3IDS2I22I33DHIS1R5IDONE3IDS2I22I3S2FB2ac2B2S1R5IDONE3IDS2lo3LOS3sp13ALO2I22I33DHIS1R5IDONE3IDS2FB2F22I12I22I3S1v". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO SP1 F64 FRSH"] Lemma eb_ids_munch : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R:.R9.R8.R7.R6.R5.R4.R3.R2.(<.(8.$6.$6.)(=.$6.$6.VIDONE,(16.VIDONE,+1.))(<.(8.$6.$6.)(=.$6.$6.VIDS,(16.VIDS,+38.))(>.(8.$6.$6.)))))P,(;.(<.(8.$6.$6.)(=.$6.$6.VIDONE,(16.VIDONE,+1.))(<.(8.$6.$6.)(=.$6.$6.VIDS,(16.VIDS,+38.))(>.(8.$6.$6.))))R9.R2.)P,(10.$1.R:.R3.)P,(11.$1.R4.)P,(57.$1.VIDONE,VIDS,R5.)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R?.R>.R6.R<.R;.R:.R9.R8.R7.(<.(8.$6.$6.)(=.$6.$6.VIDONE,(16.VIDONE,+1.))(<.(8.$6.$6.)(=.$6.$6.VIDS,(16.VIDS,+38.))(>.(8.$6.$6.)))))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T m2 EBk MU WM MI2 IDS2.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    ddestruct IDOK as (I1 & I2 & I3 & I4 & _). pose proof (art_data_lo asegs R HIA) as DHI. cbn in DHI.
    assert (DIV : Forall data_iv W0).
    { apply Forall_cons; [split; cbn [fst snd]; clear - I1 I2 I3; lia| apply Forall_cons; [split; cbn [fst snd]; clear - I1 I2 I3; lia| apply Forall_nil]]. }
    assert (CST : forall a, IDONE <= a < IDONE + 1 \/ IDS <= a < IDS + 56 -> cstatic R a).
    { intros a Ha. split; [clear - Ha I1 I2 I3; lia| exact (I4 a Ha)]. }
    assert (HH2 : HM asegs R HIA hk LBk LF' m2).
    { eapply (hm_munch asegs R HIA hk LBk LF' _ mk m2 HHk MU WM).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; intros a Ha; left; right; left; apply CST; [left| right]; exact Ha. }
    assert (ST2 : stk asegs m2 lo sp1).
    { eapply stk_transport_disjoint; [exact STb| exact MU| exact WM|]. cbn [disjoint_from]. clear - I1 I2 I3 DHI ALO LOS. lia. }
    assert (HP : presA asegs R LBk LF' sp1 (arl_stklo R) (hstkhi asegs R HIA hk) ([] ++ W0) mk m2).
    { cbn [app]. eapply (presA_of_munch asegs R LBk LF' _ _ _ _ mk m2 (hcs asegs R HIA hk) (hcs_ok asegs R HIA hk)); [| | exact MU| exact WM].
      - apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; intros x Hx; apply (hcs_static asegs R HIA hk); apply CST; [left| right]; clear - Hx; lia.
      - intros c0 Hc. eapply cshd_hcs; [exact HHk| apply Z.le_refl| exact Hc]. }
    pose proof (eb_step_ids hk LBk mk v f SH SL CH T W0 hk LBk m2 0 0 T LBk [] W0 W0 EBk0 HH2 MI2 ST2 HP eq_refl eq_refl eq_refl
                  ltac:(intros x Hx; exact Hx) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb])
                  ltac:(apply Forall_nil) ltac:(intros x Hx; exact Hx) ltac:(intros x Hx; exact Hx)
                  ltac:(apply Forall_cons; [cbn [snd]; clear - I1 I2 I3 DHI; lia| apply Forall_cons; [cbn [snd]; clear - I1 I2 I3 DHI; lia| apply Forall_nil]])
                  IDS2
                  ltac:(cbn [app]; apply Forall_cons; [cbn [fst snd]; clear - F2 I1 I2 I3; lia| apply Forall_cons; [cbn [fst snd]; clear - F2 I1 I2 I3; lia| apply Forall_nil]])
                  ltac:(cbn [app]; rewrite Forall_forall in CHk |- *; intros ac Hac; ddestruct (CHk ac Hac) as (_ & B1 & B2); apply (data_iv_frame W0 _ _ DIV); [clear - B1; lia| clear - B2; lia])
                  EXTk FRk) as E2.
    replace (v + 0) with v in E2 by (clear; lia). replace (f + 0) with f in E2 by (clear; lia). exact E2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04=0@C53807985733.225D14735680649.274D21790401433.274D46719952988.216D46719952988.273D46719952988.274D50014262098.216D50014262098.273D50014262098.274D50244182904.274L10596430123.1  L11080239181.8  L11709910993.6  L12114880880.208L13062538913.0  L14077532924.266L14447004729.1  L14565380337.0  L15721644686.6  L16242446612.6  L16346890165.1  L1685717371.0   L17111567889.2  L17289268625.2  L1790642108.2   L18120891462.262L18120898828.265L18122958275.262L18140481520.266L18794210039.1  L19031033424.7  L19561236329.1  L1984726332.2   L19980016842.7  L20491039612.266L20650275440.266L21868500043.2  L22286006383.266L22409920380.266L22939159100.2  L24023900370.0  L24264274256.3  L26659094768.266L27886882754.0  L27958617797.14 L28632618922.2  L29108451424.222L30410547336.1  L31384711054.7  L32454903270.1  L35668120898.7  L35870121979.3  L38180633941.0  L38235734261.1  L38309573212.8  L38408712019.4  L39280637297.0  L40240748156.266L41418070141.266L41586653350.1  L42128420922.13 L42411609006.0  L4248698872.6   L44056310188.3  L44727859312.266L46204432317.2  L4681653737.1   L46883672865.0  L46966707113.2  L47513520362.222L47663688086.1  L48937103345.266L49379278409.0  L50388565080.1  L50616353679.266L50738124528.266L5116204071.3   L52149871223.1  L52719701141.1  L52736311528.1  L53246223740.266L53560016891.6  L54268397086.0  L54992078076.208L55715170945.263L56468645943.266L56763720560.266L57387013391.2  L57391149615.1  L57698627611.2  L57813718744.3  L57885184943.1  L59308628179.4  L59308630368.3  L60098763854.3  L60262731819.1  L6104554736.266 L62775046640.266L65096641020.266L66062374908.266L66151427842.16 L66742100260.4  L68429677231.1  L7735748552.2   L9404489852.266 P17096101078.274P17287434070.274P1784087931.216 P1784087931.274 P1990232059.216 P1990232059.274 P21870859916.216P21870859916.274P22945712379.216P22976122839.225P28627113325.274P46968017262.274P57713046236.274P7750690063.216 P7750690063.274 Q10160764996.274Q10592318618.220Q113250657.273  Q11579324185.219Q12051950040.273Q12636765557.274Q13257697385.219Q13396519709.212Q15004325700.219Q15103077986.273Q15457656009.219Q15521061624.270Q15677228903.270Q1792789496.270 Q18201203431.270Q18513787101.270Q19639559577.219Q19971695125.270Q2037562293.220 Q20377295057.222Q20459834793.219Q20580512354.216Q20580512354.273Q20580512354.274Q20612661376.212Q20851854948.219Q21694330087.270Q22444220057.219Q22712450012.216Q22712450012.273Q22712450012.274Q23628454911.267Q2390933737.219 Q24251258485.215Q24259883896.270Q24487240425.273Q25073716075.225Q25075822059.216Q25513505925.215Q25854312132.219Q2595979742.270 Q26295627581.270Q26307634249.219Q27730420327.270Q27851608849.270Q27853543318.269Q27853689897.267Q29648483289.219Q29745301161.213Q30225560386.270Q31337274133.219Q31358333560.270Q31716561380.219Q3203240366.213 Q3203240366.271 Q33310975513.219Q33749098471.270Q33947166577.217Q3421936230.273 Q34357517862.221Q34877581972.219Q34966529595.270Q3545121163.219 Q3551465399.219 Q35928394133.269Q3657071719.270 Q3763620088.270 Q38921014052.219Q40513117017.219Q40599399476.219Q40851215916.270Q4139618244.219 Q42566809956.219Q4323447160.270 Q44298944140.214Q44298944140.220Q44301027056.225Q45201877496.270Q45742289428.219Q4590925129.219 Q46358622841.219Q47228431932.225Q47801532788.219Q48119910507.225Q49698585326.214Q49698585326.272Q49785721508.219Q50734205856.218Q51379872473.219Q51449427892.219Q52389960886.216Q52389960886.273Q52389960886.274Q5265442331.272 Q52946523988.219Q53693185316.218Q54481541666.221Q54783724856.219Q54967541497.216Q54967541497.274Q55241230473.219Q55415036769.274Q55809854877.219Q5596578838.225 Q56592237972.219Q57225610745.219Q57656407986.273Q57897686558.220Q58668296436.219Q58768111688.216Q58768111688.274Q5941659220.219 Q59617553652.219Q59619599048.219Q59852654197.271Q60262496617.219Q60321780071.270Q60546513284.271Q60635707940.219Q61051761501.270Q63012415579.217Q63435846322.220Q63811190484.219Q64228675114.224Q64228946346.225Q64427786041.219Q65654860420.219Q65714787448.270Q6575031993.219 Q66108231689.219Q66901779611.220Q66942122546.214Q66954699982.216Q66954699982.274Q66956788302.225Q6733131066.270 Q68075597177.219Q68235297648.273Q68235297648.274Q6912043759.222 Q6912046254.216 Q6912046254.274 Q7785411076.219 Q798847092.219  Q8253422473.219 Q8945685151.267 Q9611917865.219 Q9674287591.270 Q9934975337.213 00000102<04T06f09>0;V0=[0?f0B10D<0D@0D`0Dj0F40F50G@0GE0GF0GY0Ge0Gj0Gk0Gl0Gm0Gn0IC0JX0Km0M80M<0MS0MW0MX0N00O;0PF0PG0QR0R]0R^0R_0Rk0T60T70T_0T`0Ta0Te0U:0U>0UU0U^0U_0Uc0VC0VR0VS0W^0Xi0Xn0YV0YW0Yl0Z60[A0[G0[K0[L0[M0]90]>0^I0^J0^O0_Z0`e0a00a40a90a=0bH0b[0b\0cf0e10f<0gG0gN0gR0gS0g^0gb0go0h30h=0hA0iL0jW0kb0lm0mO0mZ0m^0m_0nj10\12N14C16517j19\1;Q1=C1?81@R1BD1BE1C_1E<1FV1HK1I_1KL1LO1LP1NE1OH1Pi1Ql1S?1TB1UF1VJ1WN1XR1Y[1Zo1\31];1^O1_R1_S1_T1_U1`f1ai1bm1d01eM1fg1hA1iE1jH1l81m<1nO1om21E22e23h24l25l26o2832972:;2;?2<B2=E2>I2?L2@P2AS2Bb2Cn2E12F52Ge2IB2J\2K_2M=2N@2OC2PG2QK2RO2SR2TU2UX2UY2V\2W_2Xc2Yk2[32\M2]Q2^T2_W2`Z2b82c;2e12fA2gN2hQ2ie2jh2kk2mc2oX31M32Z33]35136Y37\3923:E3;H3<b3>63>73?:3@=3AP3Bd3Cg3E=3FP3GS3GT3GU3Ha3Id3Jh3L43M73N;3O]3O^3Pa3Rk3U;3V>3WA3XE3YH3ZK3[S3\[3^13_D3`^3al3bo3dB3eU3fi3h?3iR3jU3kX3l[3m[3n^3ob40eFS1R5NEEDR3IDS2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2v12v22v32v42v52v62v72v83v103v163v173v184IDLO2F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R3HIA5NEEDR3IDS1h2LF2sp3PKA2lo3SLO3TOP2FB3sp13SP13LFB3NZP2hk2v12v22v32v42v52v62v72v83v103v163v173v184IDLO2F04FBLO4SP1R3NER3ETk4NSH'3NSL2HB5Ha_st5Hl_stS1R3HIA5NEEDR1h2LF2sp3PKA2lo3SLO3TOP2FB3sp13SP13LFB3NZP2hk2v12v22v32v42v52v62v72v82v93v103v163v173v183ETk4NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS1R3HIA5NEEDR3IDS1h2LF2sp3PKA2lo3SLO3TOP2FB3sp13SP13LFB3NZP2hk2v12v22v32v42v52v62v72v83v103v163v173v184IDLO2F04FBLO4SP1R3NER3ETk4NSH'3NSL2HB5Ha_st5Hl_stS1R3HIA5NEEDR3IDS1h2LF2sp3PKA2lo3SLO3TOP2FB3sp13SP13LFB3NZP2hk2v12v22v32v42v52v62v72v83v103v163v173v184IDLO2F04FBLO4SP1R3NER3ETk4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS1R5NEEDR3IDS2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2v12v22v32v42v52v62v72v83v103v163v173v184IDLO2F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR3IDS2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2v12v22v32v42v52v62v72v83v103v163v173v184IDLO2F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR3IDS2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2v12v22v32v42v52v62v72v83v103v163v173v184IDLO2F04FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_stS2FBS1R5NEEDR2sp2lo3sp13SP14SLO13NERS1R3IDS2I3S2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLSS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3sp1SS1R5IDONE3IDS2I12I2S1R5IDONE2I1S3IDSSFFFS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184IDLO4IDHI4NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184IDLO4IDHI4NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184IDLO4IDHI4NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2FBS2lo2FB3sp14FBLO2d03XB2S2FBFS1R3HIA1h2sp3TOP3sp13SP1S3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLFS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLFSS2lo2FB4FBLOS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLSS1R5NEEDR2lo2FB3sp14FBLO4SLO13NER1a1n2A2FFS2FBS1R2lo3sp14SLO13NER1HS2FBS1R3HIA1h2sp2lo3TOP3HT0S1d1f3FB'SS2loS1R5NEEDR2sp2lo3sp13SP14SLO13NERS2sp2lo3sp13SP1SS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3sp1S1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2d03XB2SS1R2FB3APS2d03XB13XB2S3LEN1v2VBS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS1R2FBS2FBSFS1R2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS3sp1S3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLSS3sp1S3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2FB2d03XB1S2FBS3IDSS2FBS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS1R5IDONE3IDS2I22I3SS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2FB2F0S2FBFS2FB2d03XB2S2FBS3IDS4IDLO2K0S2KAS1R2lo3LOSS2FBS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2FB2r02F81q1r1H2H02q02H43sp14SP1MS2FB2d03XB1S2FBFS3IDS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184FBLO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184FBLO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184FBLO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184FBLO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184FBLO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184FBLO3NER4NSH'3NSL2HB5Ha_st5Hl_stFS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v183NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL3NERS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184IDLO4NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFS2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL4SP1R2HBS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184SP1R4NSH'3NSL2HBS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF2sp3PKA2lo2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v183NER4NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS3IDS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL3ALO2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184SP1R4NSH'3NSL2HBS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184SP1R4NSH'3NSL2HBS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS1R2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEst5CM8stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v83v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF HGL IDSN HGI HIDL"] Lemma idsearch_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_C ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$1=.PdP,$1=.PdA,$1=.PdB,$1=.PdX,$1=.PdY,$1=.PdZ,$1=.Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv8,(4.&40.)Pv9,(4.&40.)Pv10,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps3v,(4.&40.)Ps6v,(4.&40.)Ps10v,(4.&40.)Ps7v,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R31.R30.R2?.R2>.R2=.$82.(<.$7.(15.R20.)(<.$7.(15.R1?.)(<.$7.(15.R1>.)(<.$7.(15.R1=.)(<.$7.(15.R1<.)(<.$7.(15.R1;.)(<.$7.(15.R1:.)(<.$7.(15.R19.)(<.$7.(15.R18.)(<.$7.(15.R17.)(<.$7.(15.(14.&40.VPKA,))(<.$7.(15.(14.&40.(16.VFB,+198.)))(<.$7.(15.(14.&40.(16.VFB,+188.)))(<.$7.(15.(14.&40.(16.VFB,+270.)))(<.$7.(15.(14.&40.(16.VFB,+178.)))(<.$7.(15.R16.)(<.$7.(15.R15.)(<.$7.(15.R14.)(>.$7.)))))))))))))))))))(<.(8.$6.(2.$7.))(=.$6.(2.$7.)(16.VFB,+20.)(<.$7.(2<.#<0.R25.)(>.$7.)))(<.(8.$6.(2.$7.))(=.$6.(2.$7.)(16.VFB,+270.)(<.$7.(1:.R24.)(<.$7.(1:.R23.)(>.$7.))))(<.(8.$6.(2.$7.))(=.$6.(2.$7.)(16.VFB,+1>8.)(<.$7.(15.R22.)(<.$7.(15.R21.)(>.$7.))))(>.(8.$6.(2.$7.))))))(1<.(<.$1=.R2<.(<.$1=.R2;.(<.$1=.R2:.(<.$1=.R29.(<.$1=.R28.(<.$1=.R27.(<.$1=.R26.(>.$1=.)))))))))(<.(8.$6.$6.)(=.$6.$6.VIDONE,(16.VIDONE,+1.))(<.(8.$6.$6.)(=.$6.$6.VIDS,(16.VIDS,+38.))(>.(8.$6.$6.)))))P,(1?.$1.R30.R31.(16.VFB,+170.)+<0.(<.$1=.R2=.(<.$1=.R2<.(<.$1=.R2;.(<.$1=.R2:.(<.$1=.R29.(<.$1=.R28.(<.$1=.R27.(>.$1=.)))))))))P,(20.$6.(21.R2>.)(16.(16.VFB,+170.)+68.))P,(20.$6.(21.R2>.)(16.(16.VFB,+170.)+8.))P,(20.$6.(21.R2>.)(16.(16.VFB,+170.)+18.))P,(20.$6.(21.R2>.)(16.(16.VFB,+170.)+28.))P,(20.$6.(21.R2>.)(16.(16.VFB,+170.)+38.))P,(20.$6.(21.R2>.)(16.(16.VFB,+170.)+48.))P,(20.$6.(21.R2>.)(16.(16.VFB,+170.)+58.))P,(?.(2>.R39.)(16.(2>.VLB,)+5.))P,(?.(16.(16.(16.R38.(5>.+=.(16.$39.$48.)))$39.)$5<.)(3:.VLEN,))P,(?.(16.(16.(16.(16.R38.(5>.+=.(16.(3;.=)(49.=))))(3;.=))+15.)$5=.)(3<.Vd,))(3?.$1.(40.$1.VR,VHIA,R3=.Vmo0,)(41.$1.VR,VHIA,$25.$29.$2:.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(43.(44.R1?.(14.&40.Vsp1,)Vgp,Vtp,R1>.R1=.R1<.Vsp,(14.&40.Vsp1,)R1;.R1:.(14.&40.(16.VFB,+1=8.))R19.R18.R17.R16.R15.(14.&40.VFB,)R10.(14.&40.(16.(4>.VFB,+3.)(4?.(32.VR,))))(14.&40.(4?.(32.VR,)))R?.R=.(14.&40.(16.VFB,+1:8.))(14.&40.VFB,)R>.(14.&40.(16.VFB,+170.))R14.R13.R12.R11.)VF,(14.&40.+;0?00.)Vfc,(45.(4.&40.))R3;.(46.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s7v. intros EBk TOK EN EP EA EB' EX EY EZ C24k VB FB'.
    destruct (AImgGlobals.img_norz_sound _ _ IDSN) as (_ & IDLO & IDHI & _). unfold AImgGlobals.IMG_LO, AImgGlobals.IMG_HI in IDLO, IDHI.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl [(sp1 + 8, sp1 + 152); (SHB, SHB + 80)] mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB LBk LF mk FB 1024 FRSH HHk) as FRSHk.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hk) hk LBk LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    dpose (Forall_inv CHk) as (REFC & _ & _). dpose (Forall_inv (Forall_inv_tail CHk)) as (GID & _ & _).
    dpose (Forall_inv (Forall_inv_tail (Forall_inv_tail CHk))) as (PBN & _ & _). cbn [fst snd] in REFC, GID, PBN.
    pose proof (conj TOK (conj HHk (conj MIk (conj IDSk I)))) as BOX.
    unfold EP_SH_G in FSH.
    (* [comment removed for export] *)
    zstep. zstep. do 24 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH6 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ddestruct BOX as (TOK0 & HHk0 & MIk0 & IDSk0 & _).
    assert (OWN : Forall own_iv [(sp1 + 8, sp1 + 152); (SHB, SHB + 80)]).
    { apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]]. }
    assert (EB6 : EB hk LBk m6 v f EP_SH_GR
                    [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 (Z_to_bv 64 (FB + 472)); C8 v10; C8 (Z_to_bv 64 PKA); C8 (Z_to_bv 64 (FB + 408));
                     C8 (Z_to_bv 64 (FB + 392)); C8 (Z_to_bv 64 (FB + 624)); C8 (Z_to_bv 64 (FB + 376)); C8 v16; C8 v17; C8 v18]
                    [(FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])] (tmp_blocks (DS7 dN dP dA dB dX dY dZ)) W0).
    { unfold EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_GR; exact FSH6| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [exact (ids_state_own hk LBk mk m6 _ HHk0 OWN IDSk0 MU WM)|].
      split; [apply Forall_cons; [split; [exact GID| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| apply Forall_cons; [split; [exact PBN| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| apply Forall_nil]]|].
      split; [exact EXTk| exact FRk]. }
    assert (TOK6 : tmp_ok asegs m6 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_own hk LBk mk m6 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN).
      intros d0 Hd. ddestruct TOK0 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO SLO1 SP1 NER NEEDR; lia| split; [clear - XB1 XB2 APS; lia| exact I]]. }
    pose proof (ref_aobj _ _ _ _ _ _ _ _ _ EB6) as OREF.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof HGI as SP. unfold ecp_group_init_stmtA in SP.
      eapply SP with (h := hk) (LB := LBk) (LF := LF') (A := REF) (lo := lo) (LBg := LBk) (junk := jref); rewrite ?(unsigned_lit sp1) by exact SP1R; unfold ECP_GROUP_SIZE;
        first [ eassumption | exact OREF | reflexivity
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
    ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m7 & ridpad & rpP & rpA & rpB & rpX & rpY & rpZ & rpN & rhpad
                    & E & MU7 & WM7 & MI7 & HG7 & ST7 & HH7). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU7, ST7 by exact SP1R. unfold ECP_GROUP_SIZE in MU7.
    replace (ret_pc (Z_to_bv 64 0xb0f70)) with (Z_to_bv 64 0xb0f70 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (eb_munch2 hk LBk m6 v f _ _ _ _ _ m7 REF 192 lo EB6 MU7 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) WM7 MI7 ST7
                  ltac:(repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]; split; [clear; lia| exact I]|]); apply Forall_nil)) as EB7.
    assert (OWN7 : Forall own_iv [(REF, REF + 192); (lo, sp1)]).
    { apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1; lia| apply Forall_nil]]. }
    assert (TOK7 : tmp_ok asegs m7 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_own hk LBk m6 m7 _ _ ltac:(assumption) TOK6 MU7 WM7 ltac:(assumption) MI7 OWN7).
      intros d0 Hd. ddestruct TOK6 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2; lia| split; [clear - XB1 XB2 FBLO; lia| exact I]]. }
    clear EB6 TOK6 OREF OWN MU WM. clear HHk0 TOK0 MIk0 IDSk0.
    dpose EB7 as (HH7' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IDS7 & _).
    (* [comment removed for export] *)
    pose proof (munch_refl ([] : list ivl) m7) as MU. pose proof (wmono_refl asegs m7) as WM.
    zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof HIDL as SP. unfold ecp_grp_id_list_stmtA in SP.
      eapply SP with (CS := hcs asegs R HIA hk); [exact IDS7| exact MI7| reflexivity| exact (art_alwf asegs R HIA)| exact (hcs_ok asegs R HIA hk)]. }
    intros ms' PO. unfold ecp_grp_id_list_post in PO.
    ddestruct PO as (q0' & q1' & qa1' & qa2' & qa3' & qa4' & qa5' & qa6' & qa7' & m8 & bflag & E & MU8 & WM8 & MI8 & HF8 & BNZ & HIDS8). subst ms'.
    replace (ret_pc (Z_to_bv 64 0xb0f74)) with (Z_to_bv 64 0xb0f74 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (IDS8 : ecp_ids_state asegs IDONE IDS m8) by (exists bflag, ecp_ids_bytes; split; [exact HF8| split; [exact HIDS8| intros _; reflexivity]]).
    pose proof (eb_ids_munch hk LBk m7 v f _ _ _ _ m8 EB7 MU8 WM8 MI8 IDS8) as EB8.
    assert (DIV : Forall data_iv W0).
    { ddestruct IDOK as (I1 & I2 & I3 & _). apply Forall_cons; [split; cbn [fst snd]; clear - I1 I2 I3; lia| apply Forall_cons; [split; cbn [fst snd]; clear - I1 I2 I3; lia| apply Forall_nil]]. }
    assert (TOK8 : tmp_ok asegs m8 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_munchA asegs m7 m8 LBk G 192 _ _ TOK7 MU8 WM8 MI7 MI8); [apply (data_iv_frame W0 _ _ DIV); clear; lia|].
      intros d0 Hd O. pose proof (tmp_ok_in asegs _ _ _ _ _ _ TOK7 Hd) as MX. destruct (mpd_at_blk_in asegs m7 LBk d0 MX O) as (Ix & _).
      exact (data_iv_blk hk LBk m7 W0 _ _ HH7' Ix DIV). }
    assert (HG8 : ecp_group_at asegs A_MT m8 LBk REF (grp_init REF ridpad rpP rpA rpB rpX rpY rpZ rpN rhpad)).
    { eapply (ecp_group_at_munch asegs); [exact HG7| exact MU8| exact WM8| exact MI7| exact MI8| apply (data_iv_frame W0 _ _ DIV); clear; lia|].
      intros d0 Hd O. exfalso. rewrite (grp_init_noheap _ _ _ _ _ _ _ _ _ _ d0 Hd) in O. discriminate O. }
    clear EB7 TOK7 HG7 MU WM IDS7 HH7' MU7 WM7 MU8 WM8.
    clear HHk ETk ESk EFk HCSk HVk HFk FHD FSH6 NSH' FSHR SAVE SLOTS NSL STlo SThi STb PRES CHk EXTk FRk SCSk FRSHk CFBk INF INH IND AP SBND APS WLk REFC GID PBN EBk0. clear w0 w1 w2. try clear MIk. try clear IDSk. try clear TOK. try clear MI7.
    pose proof EB8 as EBk0. eb_open EB8.
    pose proof (munch_refl [(sp1, sp1 + 152)] m8) as MU. pose proof (wmono_refl asegs m8) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB LBk LF m8 FB 1024 FRSH HHk) as FRSHk.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hk) hk LBk LF m8 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (ids_aobj hk LBk LF' m8 HHk) as OIDS.
    dpose (Forall_inv CHk) as (GID & _ & _). dpose (Forall_inv (Forall_inv_tail CHk)) as (PBN & _ & _). cbn [fst snd] in GID, PBN.
    pose proof (conj TOK8 (conj HHk (conj MIk (conj IDSk (conj HG8 (conj HIDS8 I)))))) as BOX.
    unfold EP_SH_GR in FSH.
    (* [comment removed for export] *)
    pose proof IDOK as IDOK'. ddestruct IDOK' as (_ & _ & _ & _ & _ & _ & IDA).
    zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 IDLO IDHI; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    zstep.
    assert (IA3 : Z.land IDS 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact IDA).
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA IA3; rewrite ?IA3 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA.
    zstep. zstep.
    shadow_chk OIDS IDS 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs m8 IDS P_pk_ecparams_D.IDWS 0 (Z_to_bv 64 5) (wa IDS) (ids_bytes_at m8 HIDS8) eq_refl ltac:(clear; lia) ltac:(f_equal; clear; lia)) as RDJ.
    clear HIDS8.
    zstep. clear RDJ. rewrite (sx32_small_ep 5) by (clear; lia).
    zstep.
    (* [comment removed for export] *)
    destruct (stk_carve asegs m8 sp1 (sp1 + 8) 8 STlo ltac:(clear; lia)) as [STlo0 [j0 SL0]].
    replace (sp1 + 8 - Z.of_nat 8) with sp1 in STlo0, SL0 by (clear; lia). clear STlo.
    try cb8_to_c8 SL0 (@nil cell).
    do 21 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    ddestruct BOX as (TOK0 & HHk0 & MIk0 & IDSk0 & HG0 & HIDS0 & _).
    pose proof (stk_of_rw_cells asegs m9 sp1 _ SL0) as STlo. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in STlo.
    assert (OWN9 : Forall own_iv [(sp1, sp1 + 152)]).
    { apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_nil]. }
    assert (DJS : forall a n, FB <= a -> a + n <= FB + 1024 -> disjoint_from [(sp1, sp1 + 152)] a n).
    { intros a n A1 A2. cbn [disjoint_from]. split; [clear - A1 A2 FBLO SLO1 SP1 NER NEEDR; lia| exact I]. }
    assert (LI9 : LINV hk LBk m9 v f (grp_init REF ridpad rpP rpA rpB rpX rpY rpZ rpN rhpad) 0 MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb).
    { split.
      { unfold EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
        split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_GR; exact FSH| reflexivity]|]. split; [exact FSHR|].
        split; [exact SAVE|]. split; [split; [unfold SLL; exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
        split; [exact PRES|].
        split; [exact (ids_state_own hk LBk m8 m9 _ HHk0 OWN9 IDSk0 MU WM)|].
        split; [apply Forall_cons; [split; [exact GID| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| apply Forall_cons; [split; [exact PBN| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| apply Forall_nil]]|].
        change (grp_blocks (grp_init REF ridpad rpP rpA rpB rpX rpY rpZ rpN rhpad)) with (@nil blk). rewrite app_nil_r.
        split; [exact EXTk| exact FRk]. }
      split. { eapply (tmp_ok_own hk LBk m8 m9 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN9).
               intros d0 Hd. ddestruct TOK0 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). apply DJS; [clear - XB1; lia| clear - XB2; lia]. }
      split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [intros b Hb; change (grp_blocks (grp_init REF ridpad rpP rpA rpB rpX rpY rpZ rpN rhpad)) with (@nil blk) in Hb; destruct Hb|].
      split; [eapply (grp_at_own hk LBk m8 m9 REF _ _ HHk0 HG0 MU WM MIk0 ltac:(assumption) OWN9); apply DJS; clear; lia|].
      split; [intros d1 d2 H1 H2 NE O1 O2; exfalso; rewrite (grp_init_noheap _ _ _ _ _ _ _ _ _ _ d1 H1) in O1; discriminate O1|].
      split. { right; right; left. split; [reflexivity|]. split; [clear; lia|]. split; [reflexivity|]. dexists ridpad, rpP, rpA, rpB, rpX, rpY, rpZ, rpN, rhpad. split; [reflexivity| exact I]. }
      split; [eapply (rw_cells_transport asegs); [exact HIDS0| exact MU| exact WM| exact (own_iv_ids hk LBk m8 _ HHk0 OWN9)]| split; [exact C24k| exact SL0]]. }
    replace (Z_to_bv 64 IDS) with (Z_to_bv 64 (IDS + 4 * 0)) by (f_equal; clear; lia).
    eapply (loop_walk 13 0 hk LBk m9 v f _ 0 MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE dN dP dA dB dX dY dZ v16 v17 v18 gid gj' pb nb);
      [reflexivity| clear; lia| exact LI9| clear - VB; lia| clear - FB'; lia].
    all: match goal with |- ?g => idtac "ENTRY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkEP.
