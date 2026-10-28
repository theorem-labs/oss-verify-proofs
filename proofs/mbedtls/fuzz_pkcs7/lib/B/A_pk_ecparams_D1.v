(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_ecp_point_free P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_ecp_grp_id_list P_ecp_mul_mod P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_defs A_pk_defs A_mpi_free A_mpi_lset A_mpi_bitlen A_mpi_cmp_mpi A_asn1_get_tag_stmt A_asn1_get_int_loops A_asn1_get_mpi A_oid A_oid_ec_grp A_ecp_group_init A_ecp_group_free A_ecp_point_free A_ecp_grp_id_list A_pk_ecparams_aux A_free_seq A_pk_ecc_set_group A_pk_ecc_set_pubkey A_ecp_grp_facts A_pk_tmp A_pk_ecparams_stmt A_pk_ecparams_A A_pk_ecparams_B A_pk_ecparams_C A_mpi_read_binary_stmt_c24 A_asn1_get_mpi_c24.
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
Ltac2 gd_tbl_A_pk_ecparams_D1 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_B.EB"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_upd"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "WalkEP.Call.EP_SH_P"; "WalkEP.Call.SLP"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "WalkEP.Call.SPINV"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_FR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_FR"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_use_ecparams_postA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.nat"; "WalkEP.Call.sh_zero"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_FR"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_mpi.A_ASN1_GET_MPI"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_read_binary.chars_to_limbs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_lset.lset_R"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_tag_stmt.A_ASN1_GET_TAG"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.mpi_query_stmtA"; "WalkEP.Call.TAILV"; "WalkEP.Call.TAILF"].



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
  Variables (P BUF : Z) (bs : list byte).
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
  Hypothesis LEN0 : 0 <= LEN.
  Local Notation PEND := (P + LEN).
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma eb_ch_add : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pa,$6.Pcs,(2.$7.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(;.$1.R;.R3.R2.)P,(<.(=.VFB,+20.)R4.)P,(<.(=.R5.(>.(?.R4.)))(=.VFB,+3?8.))(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R10.R?.R>.R=.R<.R;.R:.(10.(8.$6.(2.$7.))(11.$6.(2.$7.)R6.R5.)R9.)R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE a cs EBk HC A1 A2. eb_open EBk.
    unfold A_pk_ecparams_B.EB. split; [exact HHk|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
    split; [dexists w0, w1, w2; exact FHD|]. split; [exact (conj FSH NSH')|]. split; [exact FSHR|].
    split; [exact SAVE|]. split; [exact (conj SLOTS NSL)|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [exact MIk|].
    split; [exact PRES|]. split; [exact IDSk|].
    split; [apply Forall_cons; [cbn [fst snd]; exact (conj HC (conj A1 A2))| exact CHk]|].
    split; [exact EXTk| exact FRk].
  Qed.

  #[using="Type"] Lemma eb_ch_get : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pa,$6.Pcs,(2.$7.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(12.(8.$6.(2.$7.))(11.$6.(2.$7.)R3.R2.)R6.)(;.$1.R<.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE a cs EBk HIn. eb_open EBk. rewrite Forall_forall in CHk. exact (proj1 (CHk _ HIn)).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L3771243718.6 L50790761713.800000I00dS5IDONE3IDS3BUF2bs3DBI2I2S1R5NEEDR2sp2lo3LOS3SLO3NER". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO SP1 F64 FRSH HBS0 CRB DSB DBI OBUF0"] Lemma eb_bytes : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R9.R8.R7.R6.R5.R4.R3.R2.R1.(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))(14.(15.$1.R8.VBUF,Vbs,)(14.(16.$1.(17.VR,)(18.$1.VR,VHIA,R:.)R8.VBUF,(>.(19.(4.&8.)Vbs,)))(1:.(1;.VR,)(1<.$3.R9.(1=.(10.(8.$6.$6.)(11.$6.$6.VFB,+400.)VLF,)))Vlo,VBUF,(>.(19.(4.&8.)Vbs,)))))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T EBk. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & _).
    ddestruct IDOK as (I1 & I2 & I3 & I4 & _).
    pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES) as HP.
    assert (SUBK : forall b, In b LB -> In b LBk) by (intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb]).
    assert (CRBs : client_range L (LB ++ fdata LF) (bv_unsigned sp) BUF (Z.of_nat (length bs))) by (eapply client_range_sep; [exact CRB| intros b Hb; exact Hb| exact DSB]).
    split. { eapply (presA_bytes_at asegs R _ _ _ _ _ _ m mk _ _ HP); [exact HBS0| exact CRBs|]. cbn [disjoint_from]. clear - DBI I2. lia. }
    split. { eapply aobj_cs_mono; [exact HCSk|].
             eapply (presA_aobj asegs R CS); [exact (hcs_ok asegs R HIA h)| exact HP| exact OBUF0| exact CRBs| clear - ALO LOS SLO NEEDR NER; lia| intros x Hx; rewrite ESk; eapply hcs_below_top; exact Hx]. }
    intros a Ha. destruct (CRB a Ha) as [K|[K|(b & Hb & Hr)]]; [left; exact K| right; left; exact K| right; right].
    exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0>L12128799109.1L18276469768.4L19778014479.6L2333536794.13L26317275145.3L29714913886.3L36359398762.5L4800287082.3 L6203936179.1 L66668349941.1L900258061.9  L9269646986.3 00000300?00P01<01E01N01`01j01o02202T02]S1fS2FB1w2W12W2S2FB1w1a2Ha2W12W2S1R3HIA1h2sp2lo3LOS3TOP3sp13SP13lo'3LO'1a2HaS2FB1w2W1S2FB1w2W1S1R2lo3LOS3lo'3LO'S1R3HIA2hkS3sp1S1vS1R3HIA1h2sp3TOP3sp13SP13lo'5HTOP0S2FB1w2W2". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 F64 FRSH"] Lemma eb_munchF : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pm2,P,(4.&40.)(5.(4.&8.))PWFr,(2.$9.)Plo',$6.P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(1>.(1<.$9.R3.(10.(8.$6.$6.)(11.$6.$6.R2.Vsp1,)(13.(8.$6.$6.))))R<.R4.)P,(<.Vlo,R3.)P,(1?.(8.$6.$6.)Lw,(8.$6.$6.)(14.(<.(=.VFB,+20.)(20.$6.$6.R1.))(<.(21.$6.$6.R1.)(=.VFB,+3?8.)))R5.)P,(22.$1.R?.R7.)P,(23.$1.R8.)P,(24.$1.R9.Vlo,Vsp1,)P,(1?.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(25.R:.(20.$6.(2.$7.)R1.)(>.(?.(21.$6.(2.$7.)R1.))))R=.)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R15.R14.R;.R12.R11.R10.R?.R>.R=.R<.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE m2 WFr lo' EBk MU LO' HWF WM MI2 ST2 HCD.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA h _ _ _ HH0) as HTOP0.
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    assert (HH2 : HM asegs R HIA hk LBk LF' m2).
    { eapply (hm_munch asegs R HIA hk LBk LF' _ mk m2 HHk MU WM).
      apply Forall_app. split.
      - rewrite Forall_forall in HWF |- *. intros w Hw a Ha. destruct (HWF w Hw) as [W1 W2]. left. right; right.
        exists (FB + 32, 984). split; [apply in_app_iff; right; exact INFD| cbn [fst snd]; clear - Ha W1 W2; lia].
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite ETk. clear - Ha LOS LO' TOP SP1. lia. }
    assert (HP : presA asegs R LBk LF' sp1 (arl_stklo R) (hstkhi asegs R HIA hk) (WFr ++ []) mk m2).
    { rewrite app_nil_r. eapply (presA_drop_below asegs R HIA hk LBk LF' WFr lo' sp1 mk mk m2 sp1 HHk); [| clear; lia| clear - LOS LO'; lia].
      eapply presA_weaken; [| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl|].
      - eapply (presA_of_munch asegs R LBk LF' _ _ _ _ mk m2 (hcs asegs R HIA hk) (hcs_ok asegs R HIA hk)); [| | exact MU| exact WM].
        + apply Forall_app. split.
          * rewrite Forall_forall in HWF |- *. intros w Hw. destruct (HWF w Hw) as [W1 W2].
            eapply crange_sub; [exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))| clear - W1; lia| clear - W2; lia].
          * apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
            eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS LO'; lia| rewrite ESk; clear - HTOP0 TOP SP1; lia].
        + intros c0 Hc. eapply cshd_hcs; [exact HHk| apply Z.le_refl| exact Hc].
      - intros x Hx. cbn [outside] in Hx. destruct Hx as [X1 X2]. apply outside_app. split; [exact X2| cbn [outside]; split; [exact X1| exact I]]. }
    pose proof (eb_step hk LBk mk v f SH SL CH T WE hk LBk m2 0 0 T LBk WFr [] WE EBk0 HH2 MI2 ST2 HP eq_refl eq_refl eq_refl
                  ltac:(intros x Hx; exact Hx) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb])
                  ltac:(rewrite Forall_forall in HWF |- *; intros w Hw; destruct (HWF w Hw) as [W1 W2]; left; clear - W1 W2; lia)
                  ltac:(intros x _; exact I) ltac:(intros x Hx; exact Hx)
                  ltac:(apply Forall_nil) I I
                  ltac:(rewrite app_nil_r; rewrite Forall_forall in HWF |- *; intros w Hw; destruct (HWF w Hw) as [W1 W2]; right; clear - W1; lia)
                  ltac:(rewrite app_nil_r; exact HCD) EXTk FRk) as E2.
    replace (v + 0) with v in E2 by (clear; lia). replace (f + 0) with f in E2 by (clear; lia). exact E2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L10383309542.1L11825717972.3L13551202163.1L18276469768.4L26317275145.3L38146834254.6L47010974703.2L52965510918.7L58213519427.4L59315284336.3L61923340120.1L6897470952.1 L9844399056.4 00000400?00C00O00X00e00j01901H01Q01T01X01bS2FBS2FB2d03DB1S2d0S2FB1w2W12W2S2FB1w2W1S2FB1w2W21B1QS1B1kS2FB1w2W11B1k1QS2FB2d03DB13DB2S2d'2N11QS1BS2FBS2FB1B1k1Q". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO SP1 F64 FRSH"] Lemma sp_mpi_step : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))Pds,(2.$26.)Pd0,$26.Pd',$26.Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))Pdv,$6.Pdf,$6.PWXc,(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R11.R10.R?.R>.R=.R<.R;.R:.(27.R9.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R10.R11.(=.VFB,+170.)+<0.R:.)P,(12.$26.R:.R;.)P,(29.$1.VR,VHIA,R9.R8.(10.(8.$6.$6.)(11.$6.$6.VFB,+400.)VLF,)R7.)P,(23.$1.R8.)P,(24.$1.R9.Vlo,Vsp1,)P,(2:.$1.VR,(2;.R16.R>.)(10.(8.$6.$6.)(11.$6.$6.VFB,+400.)VLF,)Vsp1,(2<.VR,)(2=.$1.VR,VHIA,R17.)(1<.$9.R7.(10.(8.$6.$6.)(11.$6.$6.(2>.R>.)(=.(2>.R>.)+10.))(13.(8.$6.$6.))))R15.R:.)P,(2?.$6.(30.$1.VR,VHIA,R=.)(30.$1.VR,VHIA,R18.))P,(2?.$6.(2=.$1.VR,VHIA,R>.)(2=.$1.VR,VHIA,R19.))P,(2?.$6.(31.$1.VR,VHIA,R?.)(31.$1.VR,VHIA,R1:.))P,Px,$6.P,(18.$1.VR,VHIA,R1<.R1.)(18.$1.VR,VHIA,R12.R2.)P,(<.(32.$1.VR,VHIA,R11.)(=.(32.$1.VR,VHIA,R1<.)R>.))P,(<.(33.$1.VR,VHIA,R12.)(=.(33.$1.VR,VHIA,R1=.)R>.))P,(34.$1.R11.R12.R14.)P,(35.R1>.R16.R13.R15.)P,Pb,$3.P,(12.$3.R1.(36.R17.))(37.(12.$3.R2.(36.R19.))(38.VR,(2;.R21.R19.)(10.(8.$6.$6.)(11.$6.$6.VFB,+400.)VLF,)(20.$6.$6.R2.)(21.$6.$6.R2.)))P,(1?.(8.$6.$6.)Lw,(8.$6.$6.)(14.(<.(=.VFB,+20.)(20.$6.$6.R1.))(14.(<.(21.$6.$6.R1.)(=.VFB,+3?8.))(37.(<.(21.$6.$6.R1.)(=.VFB,+170.))(<.(=.(=.VFB,+170.)+<0.)(20.$6.$6.R1.)))))R11.)P,(1?.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(25.(1<.$9.R13.(10.(8.$6.$6.)(11.$6.$6.(2>.R1:.)(=.(2>.R1:.)+10.))(13.(8.$6.$6.))))(20.$6.(2.$7.)R1.)(>.(?.(21.$6.(2.$7.)R1.))))R1;.)(14.(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R18.R17.R16.(=.R20.R15.)(=.R1?.R14.)R1>.R1=.R1<.(27.(39.R19.R1;.))(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))(14.(28.$1.R16.R17.(=.VFB,+170.)+<0.(39.R19.R1;.))(<.(3:.R17.)(=.(3:.R22.)(3:.(36.R19.))))))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH ds d0 d' h2 LB2 m2 dv df WXc EBk TOK Hd HH2 MI2 ST2 HP ET ES EF HCS2 HV2 HF2 MD2 OUT NEW HWC HCD.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    destruct (hm_apart asegs R HIA hk _ _ _ HHk) as [HBRk BAk]. pose proof (blocks_apart_app_l _ _ BAk) as BAk1.
    pose proof (HND _ _ _ _ HH2) as ND2. pose proof (HND _ _ _ _ HHk) as NDk.
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    dpose TOK as (T1 & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (DNS & DB1 & DB2).
    assert (SUBK : forall b, In b LB -> In b LBk) by (intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb]).
    assert (SUBp : forall b, In b LB -> In b (mpd_keep LBk d0)).
    { intros b Hb. apply In_mpd_keep_intro; [exact (SUBK b Hb)|]. intros Hc. apply (proj2 EXTk b); [| exact Hb]. apply in_tmp_blocks. exists d0. split; assumption. }
    assert (NEW' : forall b, In b (mpd_blk d') -> In b (mpd_blk d0) \/ ~ In b LBk).
    { intros b Hb. destruct (NEW b Hb) as [K|(G0 & G1 & G2 & G3)]; [left; exact K|].
      assert (DEC : forall x y : blk, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
      destruct (in_dec DEC b (mpd_blk d0)) as [K|K]; [left; exact K| right]. intros Hc.
      destruct (mpd_blk_in _ _ Hb) as [Od' ->]. cbn [fst snd] in *. pose proof MD2 as [(_ & _ & _ & _ & _ & OW) _]. rewrite Od' in OW. destruct OW as (N1 & _).
      destruct (G3 (md_p d') (4 * md_n d') ltac:(apply in_app_iff; left; apply In_mpd_keep_intro; [exact Hc| exact K])) as [Q|Q]; clear - Q N1; lia. }
    assert (WXO : Forall (wx_out LBk G 192 d0) (WXc ++ [(md_addr d0, md_addr d0 + 16)])).
    { apply Forall_app. split; [| apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]].
      rewrite Forall_forall in HWC |- *. intros w Hw. ddestruct (HWC w Hw) as (W1 & W2 & W3). right. split; [exact W3|].
      intros B k HIn _. destruct (eb_blk_apart hk LBk mk B k HHk HIn) as [Q|Q]; [right| left]; clear - Q W1 W2; lia. }
    destruct (tmp_updateA asegs L mk m2 LB [] LBk LB2 G 192 ds d0 d' sp1 _ (mpd_keep LBk d0 ++ fdata LF') BAk1 ND2
                ltac:(intros B k HIn K0; destruct (eb_blk_apart hk LBk mk B k HHk HIn) as [Q|Q]; clear - Q; lia)
                TOK ltac:(rewrite app_nil_r; exact EXTk) ltac:(intros b []) Hd MD2 OUT NEW'
                (presA_presx asegs R _ _ _ _ _ _ _ _ HP)
                ltac:(intros B k HIn NB; eapply client_range_block; [apply in_app_iff; left; apply In_mpd_keep_intro; [exact HIn| exact NB]| clear; lia| clear; lia])
                ltac:(eapply client_range_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia])
                WXO MIk MI2) as (TOK2 & EXT2 & _).
    rewrite app_nil_r in EXT2.
    assert (FR2 : forall b, In b (tmp_blocks (tmp_upd d' ds)) -> fresh_apart R LB LF (fst b) (snd b)).
    { intros b Hb. apply in_tmp_blocks in Hb. ddestruct Hb as (x & Hx & Hbx). apply in_tmp_upd in Hx.
      destruct Hx as [[-> _]|[Hx _]]; [| apply FRk; apply in_tmp_blocks; exists x; split; assumption].
      destruct (NEW b Hbx) as [K|(G0 & G1 & G2 & G3)]; [apply FRk; apply in_tmp_blocks; exists d0; split; assumption|].
      split; [exact G0|]. split; [exact G1|]. split; [exact G2|].
      intros B j Hj. apply G3. apply in_app_iff in Hj. apply in_app_iff. destruct Hj as [Hj|Hj]; [left; apply SUBp; exact Hj| right; eapply fdata_incl; [| exact Hj]; intros fb Hfb; right; exact Hfb]. }
    split; [| split; [exact TOK2| exact (mpd_out_cnt24 _ _ _ _ ND2 OUT)]].
    eapply (eb_step hk LBk mk v f SH SL CH _ W0 h2 LB2 m2 dv df _ (mpd_keep LBk d0) (WXc ++ [(md_addr d0, md_addr d0 + 16)]) [] W0);
      [exact EBk0| exact HH2| exact MI2| exact ST2| rewrite app_nil_r; exact HP| exact ET| exact ES| exact EF| exact HCS2| exact HV2| exact HF2| exact SUBp
      | | intros x _; exact I| intros x Hx; exact Hx| apply Forall_nil| exact I| exact I| | rewrite app_nil_r; exact HCD| exact EXT2| exact FR2].
    - apply Forall_app. split; [| apply Forall_cons; [left; cbn [fst snd]; clear - DB1 DB2; lia| apply Forall_nil]].
      rewrite Forall_forall in HWC |- *. intros w Hw. ddestruct (HWC w Hw) as (W1 & W2 & _). left. clear - W1 W2. lia.
    - rewrite app_nil_r. apply Forall_app. split; [| apply Forall_cons; [right; cbn [fst snd]; clear - DB1; lia| apply Forall_nil]].
      rewrite Forall_forall in HWC |- *. intros w Hw. destruct (HWC w Hw) as (W1 & _). right. clear - W1. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition EP_SH_P : list cell := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "(10.$7.(3;.(3<.&8.+?1.))(10.$7.(3;.(3<.&8.+?1.))(10.$7.(3;.(3<.&8.+?1.))(10.$7.(3;.(3<.&8.+?1.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?8.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+4.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.=))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+?2.))(10.$7.(3;.(3<.&8.+4.))(10.$7.(3;.(3<.&8.+?3.))(13.$7.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition SLP (v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 v16 v17 v18 : word) : list cell := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "(10.$7.(3=.O=.)(10.$7.(3=.O<.)(10.$7.(3=.O;.)(10.$7.(3=.O:.)(10.$7.(3=.O9.)(10.$7.(3=.O8.)(10.$7.(3=.O7.)(10.$7.(3=.O6.)(10.$7.(3=.O5.)(10.$7.(3=.(3<.&40.(=.VFB,+1:8.)))(10.$7.(3=.O4.)(10.$7.(3=.(3<.&40.(=.VFB,+198.)))(10.$7.(3=.(3<.&40.(=.VFB,+188.)))(10.$7.(3=.(3<.&40.(=.VFB,+270.)))(10.$7.(3=.(3<.&40.(=.VFB,+178.)))(10.$7.(3=.O3.)(10.$7.(3=.O2.)(10.$7.(3=.O1.)(13.$7.)))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition SPINV (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (v f : Z) (dN dP dA dB dX dY dZ : mpd)
      (p : Z) (lnw vw vw' : word) (jref : list byte) (gid gj' pb nb : word) (v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 v16 v17 v18 : word) (K : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "(14.(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,O23.O22.O21.O20.O1?.$3>.(3?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.)(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+120.)(10.$7.(3=.(3<.&40.O17.))(13.$7.)))(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+140.)(10.$7.(3=.O16.)(13.$7.)))(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+160.)(10.$7.(40.O15.)(10.$7.(40.O14.)(13.$7.))))(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+20.)(10.$7.(41.#<0.O13.)(13.$7.)))(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+270.)(10.$7.(40.O12.)(10.$7.(40.O11.)(13.$7.))))(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+1>8.)(10.$7.(3=.O10.)(10.$7.(3=.O?.)(13.$7.))))(13.(8.$6.(2.$7.)))))))))(27.(10.$26.O1>.(10.$26.O1=.(10.$26.O1<.(10.$26.O1;.(10.$26.O1:.(10.$26.O19.(10.$26.O18.(13.$26.)))))))))(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))(14.(28.$1.O21.O22.(=.VFB,+170.)+<0.(10.$26.O1>.(10.$26.O1=.(10.$26.O1<.(10.$26.O1;.(10.$26.O1:.(10.$26.O19.(10.$26.O18.(13.$26.)))))))))(14.(2?.$6.(2>.O1>.)(=.(=.VFB,+170.)+68.))(14.(2?.$6.(2>.O1=.)(=.(=.VFB,+170.)+8.))(14.(2?.$6.(2>.O1<.)(=.(=.VFB,+170.)+18.))(14.(2?.$6.(2>.O1;.)(=.(=.VFB,+170.)+28.))(14.(2?.$6.(2>.O1:.)(=.(=.VFB,+170.)+38.))(14.(2?.$6.(2>.O19.)(=.(=.VFB,+170.)+48.))(14.(2?.$6.(2>.O18.)(=.(=.VFB,+170.)+58.))(14.(14.(<.VP,O17.)(<.O17.(=.VP,VLEN,)))(<.(3:.O22.)(=.(3:.VLB,)O1.))))))))))))")
(* [comment removed for export] *).
  Definition SLPx (v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 s88 v16 v17 v18 : word) : list cell :=
    [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 s64; C8 s72; C8 s80; C8 s88; C8 (Z_to_bv 64 (FB + 408));
     C8 (Z_to_bv 64 (FB + 392)); C8 (Z_to_bv 64 (FB + 624)); C8 (Z_to_bv 64 (FB + 376)); C8 v16; C8 v17; C8 v18].
  Definition SPINVx (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (v f : Z) (dN dP dA dB dX dY dZ : mpd)
      (p : Z) (lnw vw vw' : word) (jref : list byte) (gid gj' pb nb : word) (v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 s88 v16 v17 v18 : word) (K : Z) : Prop :=
    EB hk LBk mk v f EP_SH_P (SLPx v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 s88 v16 v17 v18)
       [(FB + 288, [C8 (Z_to_bv 64 p)]); (FB + 320, [C8 lnw]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])]
       (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ]) W0 /\
    tmp_ok asegs mk LBk (FB + 368) 192 [dN; dP; dA; dB; dX; dY; dZ] /\
    md_addr dN = FB + 368 + 104 /\ md_addr dP = FB + 368 + 8 /\ md_addr dA = FB + 368 + 24 /\ md_addr dB = FB + 368 + 40 /\
    md_addr dX = FB + 368 + 56 /\ md_addr dY = FB + 368 + 72 /\ md_addr dZ = FB + 368 + 88 /\
    (P <= p <= P + LEN) /\ cnt24 LBk <= cnt24 LB + K.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0180@C53807985733.238C53807985733.239L12916956843.1  L15195629121.1  L1685717371.0   L22409920380.226L24023900370.0  L28948604668.226L29108451424.232L29108451424.233L32781806251.1  L32930889387.1  L35668120898.7  L42411609006.0  L4248698872.6   L46204432317.2  L47513520362.232L47513520362.233L49379278409.0  L51624893551.3  L60098763854.3  L9786907307.1   P22976122839.238P22976122839.239Q11799173861.238Q11799173861.239Q12820331109.233Q13919783118.233Q15221952244.233Q20377295060.235Q28072352329.233Q30225219578.233Q33947166577.233Q34347029405.234Q35334539030.233Q36253051258.233Q39125883166.234Q4355155300.229 Q44298944140.230Q44298944140.234Q44301027056.238Q44301027056.239Q47228431932.238Q47228431932.239Q48119910507.238Q48119910507.239Q53705517749.233Q54487832473.234Q55003624591.233Q55256112523.234Q5596578838.238 Q5596578838.239 Q59617553652.233Q59619599055.233Q61051420645.233Q63012415579.233Q63435846322.234Q64228675114.237Q64228675114.238Q64228946346.238Q64228946346.239Q64268197229.233Q66942122546.230Q66942122546.234Q66956788302.238Q66956788302.239Q67854022706.233Q67892150791.234Q6912043754.235 Q9933143375.233 Q9947771764.233 Q9947836772.229 00000100200600:00;01F01G02R02S02T02X02\03303403I03O05<06i06j07407>07B08]0:80;S0<n0>30>40?80@M0@N0AS0CD0D_0D`0Ee0Ef0Fj0H30I<0JW0L20MQ0O00Pg0R^0R_0TH0UL0UM0UN0UO0UP0UQ0VV0X90X:0ZE0\P0^a0a20a30b<0cE0d`0f;0f<0f=0gR0hV0iZ0j^FFS2FBS2FBSS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLSS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLFFS2FBS2FBS1R3HIA1h2sp2lo3TOP3HT0SS1R2FB3APS2d03XB13XB2S1R2FBS1R2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSS1R2FB3APSS1R2lo3LOSS2FBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF3PKA3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS1R2LF2sp3PKA2lo2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL3ALO2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_st5SAEstFS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLFFFFFS2LF3PKA3sp13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLS1R2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEst5CM8stS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEst5CM8stFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643s723v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE bs"] Lemma sp_err : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$26.PdP,$26.PdA,$26.PdB,$26.PdX,$26.PdY,$26.PdZ,$26.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Ps64,(4.&40.)Ps72,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pr,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps3v,(4.&40.)Ps6v,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)P,(42.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(3<.&40.VPKA,)R18.R17.R16.R15.)P,(14.(43.(44.(45.+2.+1?.))R15.)(<.R15.=))P,(46.(2?.$6.R16.=))P,(<.(=.R36.$47.)(48.VLEN,))P,(<.(=.(=.R36.+15.)$49.)(4:.Vd,))(4;.$1.(4<.$1.VR,VHIA,R3;.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.R18.(3<.&40.Vsp1,)Vgp,Vtp,R17.R16.R15.Vsp,(3<.&40.Vsp1,)R14.R13.(3<.&40.(=.VFB,+1=8.))R12.R11.R10.R?.R>.(3<.&40.VFB,)R9.(3<.&40.(=.(54.VFB,+3.)(55.(17.VR,))))(3<.&40.(55.(17.VR,)))R8.R7.R6.(3<.&40.VFB,)(3<.&40.R19.)(3<.&40.(=.VFB,+170.))R=.R<.R;.R:.)VF,(3<.&40.+;1188.)Vfc,(56.(4.&40.))R39.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s8v. (intros dd_H; ddestruct dd_H as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k); intros RR RNZ VB FB').
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
    pose proof (conj TOK (conj HHk (conj MIk (conj IDSk (conj CHk I))))) as BOX.
    unfold EP_SH_P in FSH. unfold SLP in SLOTS.
    (* [comment removed for export] *)
    do 6 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH6 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ddestruct BOX as (TOK0 & HHk0 & MIk0 & IDSk0 & CHk0 & _).
    assert (OWN : Forall own_iv [(SHB, SHB + 80)]) by (apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    assert (EB6 : EB hk LBk m6 v f EP_SH_G
                    [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 s64; C8 s72; C8 (Z_to_bv 64 (G + 56)); C8 (Z_to_bv 64 PKA); C8 (Z_to_bv 64 (G + 40));
                     C8 (Z_to_bv 64 (G + 24)); C8 (Z_to_bv 64 (FB + 624)); C8 (Z_to_bv 64 (G + 8)); C8 v16; C8 v17; C8 v18]
                    [(FB + 624, [C4 gid; C4 gj'])] (tmp_blocks (DS7 dN dP dA dB dX dY dZ)) W0).
    { replace (G + 56) with (FB + 424) by (clear; lia). replace (G + 40) with (FB + 408) by (clear; lia).
      replace (G + 24) with (FB + 392) by (clear; lia). replace (G + 8) with (FB + 376) by (clear; lia).
      unfold A_pk_ecparams_B.EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_G; cbn [repeat app]; exact FSH6| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [exact (ids_state_own hk LBk mk m6 _ HHk0 OWN IDSk0 MU WM)|].
      split; [eapply (ch_munch_sh mk m6 80); [apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk0)))))| apply Forall_nil]| exact MU| exact WM| clear - APS; lia]|].
      split; [exact EXTk| exact FRk]. }
    assert (TOK6 : tmp_ok asegs m6 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_own hk LBk mk m6 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN).
      intros d0 Hd. ddestruct TOK0 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2 APS; lia| exact I]. }
    replace (FB + 472) with (G + 104) by (clear; lia). replace (FB + 424) with (G + 56) by (clear; lia).
    rewrite <- (Z_to_bv_bv_unsigned gid) in EB6.
    eapply (ep_cleanup hk LBk m6 v f dN dP dA dB dX dY dZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r (bv_unsigned gid) gj');
      first [ exact EB6 | exact EN | exact EP | exact EA | exact EB' | exact EX | exact EY | exact EZ | exact RR | exact VB | exact FB' | exact TOK6
            | (intros R0; exfalso; exact (RNZ R0)) | idtac ].
    all: match goal with |- ?g => idtac "ERR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L35668120898.7  L36667852792.0  L54992078076.202L60098763854.3  Q13398370664.208Q20610286325.208Q28436691071.208Q43071304964.20800000G00H01O01Y03704E05N06]S1R3HIA1h2sp2lo3TOP3HT0SS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS1R2lo3LOSS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3NERS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4SP1RS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3SPR". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE bs"] Lemma sp_err94c : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$26.PdP,$26.PdA,$26.PdB,$26.PdX,$26.PdY,$26.PdZ,$26.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Ps64,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pr,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps3v,(4.&40.)Ps6v,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)P,(42.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(3<.&40.(=.VFB,+1=8.))(3<.&40.VPKA,)R19.R18.R17.R16.)P,(14.(43.(44.(45.+2.+1?.))R16.)(<.R16.=))P,(46.(2?.$6.R17.=))P,(<.(=.R36.$47.)(48.VLEN,))P,(<.(=.(=.R36.+15.)$49.)(4:.Vd,))(4;.$1.(4<.$1.VR,VHIA,R3;.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.R19.(3<.&40.Vsp1,)Vgp,Vtp,R18.R17.R16.Vsp,(3<.&40.Vsp1,)R15.R14.R13.R12.R11.R10.R?.R>.(3<.&40.VFB,)R9.(3<.&40.(=.(54.VFB,+3.)(55.(17.VR,))))(3<.&40.(55.(17.VR,)))R8.R7.R6.(3<.&40.VFB,)(3<.&40.R1:.)(3<.&40.(=.VFB,+170.))R=.R<.R;.R:.)VF,(3<.&40.+;1184.)Vfc,(56.(4.&40.))R39.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s8v. intros SI RR RNZ VB FB'.
    pose proof SI as (EBk & _). eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    unfold SLP in SLOTS.
    zstep.
    eapply (sp_err hk LBk mk v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 (Z_to_bv 64 (FB + 472)) v16 v17 v18 K r); [exact SI| exact RR| exact RNZ| exact VB| exact FB'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE bs"] Lemma sp_err948 : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$26.PdP,$26.PdA,$26.PdB,$26.PdX,$26.PdY,$26.PdZ,$26.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Ps64,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pr,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps3v,(4.&40.)Ps6v,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(42.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(3<.&40.(=.VFB,+1=8.))(3<.&40.VPKA,)R19.R18.R17.R16.)P,(14.(43.(44.(45.+2.+1?.))R16.)(<.R16.=))P,(46.(2?.$6.R17.=))P,(<.(=.R36.$47.)(48.VLEN,))P,(<.(=.(=.R36.+15.)$49.)(4:.Vd,))(4;.$1.(4<.$1.VR,VHIA,R3;.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.R19.(3<.&40.Vsp1,)Vgp,Vtp,R18.R17.R16.Vsp,(3<.&40.Vsp1,)(3<.&40.R1:.)R15.R14.R13.R12.R11.R10.R?.(3<.&40.VFB,)R:.(3<.&40.(=.(54.VFB,+3.)(55.(17.VR,))))(3<.&40.(55.(17.VR,)))R9.R8.R7.(3<.&40.VFB,)R6.(3<.&40.(=.VFB,+170.))R>.R=.R<.R;.)VF,(3<.&40.+;1180.)Vfc,(56.(4.&40.))R39.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI RR RNZ VB FB'.
    pose proof SI as (EBk & _). eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    zstep.
    eapply (sp_err94c hk LBk mk v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 v16 v17 v18 K r); [exact SI| exact RR| exact RNZ| exact VB| exact FB'].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L13201764833.112L18926748074.112L18932831555.112L27063921655.112L4499652908.112 L47555511156.112L5168204543.112 L66357445711.11200000Q00j01E01b02K02h03E03`S2LF2sp3PKA2FB3sp13LFB2bs1r2Hr2HnS2LF2sp3PKA2FB3sp13LFB2bsS2LF2sp3PKA2FB3sp13LFB2bs1rS2LF2sp3PKA2FB3sp13LFB2bs1r1cS2LF2sp3PKA2FB3sp13LFB3NZP2bs1r1c2Hr2Hc1ES2LF2sp3PKA2FB3sp13LFB2bs1r1cS2LF2sp3PKA2FB3sp13LFB2bs1r1cS2LF2sp3PKA2FB3sp13LFB2bs1r". (* [comment removed for export] *)
  #[using="LF sp PKA FB sp1 LFB NZP bs"] Lemma swrap32_errsum_ep : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Pr,$6.Pc,$6.P,(14.(43.-10000.R2.)(<.R2.=))P,(14.(<.(58.(45.+2.+40.)+10000.)R2.)(43.R2.(45.+2.+40.)))(2?.$6.(59.&20.(=.(5:.R4.+10000000000000000.)R3.))(=.R4.(58.R3.(45.+2.+40.))))")
(* [comment removed for export] *).
  Proof.
    intros r c Hr Hc. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296.
    change (4294967296 `div` 2) with 2147483648.
    assert (E : r mod 18446744073709551616 = r + 18446744073709551616 \/ r mod 18446744073709551616 = r).
    { destruct (Z.eq_dec r 0) as [->|Hn]; [right; reflexivity| left].
      rewrite <- (Z.mod_add r 1) by lia. rewrite Z.mod_small by lia. lia. }
    destruct E as [E|E]; rewrite E.
    - replace (r + 18446744073709551616 + c + 2147483648) with ((r + (c - 2^64) + 2147483648) + 8589934592 * 4294967296) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
    - replace (r + c + 2147483648) with ((r + (c - 2^64) + 2147483648) + 4294967296 * 4294967296) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma ep_signed64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
  Proof.
    intros z Hz. clear - Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    destruct (Z.lt_ge_cases z 0).
    - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia.
      destruct (Z.ltb_spec (z + 1 * 2^64) (2^63)); lia.
    - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
  Qed.
  Ltac ep_scheck H :=
    repeat match type of H with
    | context [bv_signed (Z_to_bv 64 ?z)] =>
        let E := fresh "ES" in
        first [ assert (E : bv_signed (Z_to_bv 64 z) = z) by (apply ep_signed64; lia)
              | (idtac "SIGNED-FAIL" z; fail 1) ];
        rewrite E in H; clear E
    end;
    first [ lia | Z.div_mod_to_equations; lia | (match type of H with ?T => idtac "SCHECK-LEFT" T end; fail) ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0190@C53807985733.236C53807985733.237L12916956843.1  L15195629121.1  L1685717371.0   L19246787633.2  L24023900370.0  L29008358026.219L29108451424.230L29108451424.231L32781806251.1  L32930889387.1  L35668120898.7  L42411609006.0  L4248698872.6   L42844608104.3  L43090215975.2  L45544150004.231L46204432317.2  L47513520362.230L47513520362.231L49379278409.0  L51624893551.3  L59308579414.10 L60098763854.3  L62165716363.2  L9786907307.1   P22976122839.236P22976122839.237Q11799173861.236Q11799173861.237Q13919783118.231Q15221952244.231Q20377295060.233Q28072352329.231Q33947166577.231Q34347029405.232Q35334539030.231Q39125883166.232Q4355155300.227 Q44298944140.228Q44298944140.232Q44301027056.236Q44301027056.237Q47228431932.236Q47228431932.237Q48119910507.236Q48119910507.237Q53705517749.231Q54487832473.232Q55003624591.231Q55256112523.232Q5596578838.236 Q5596578838.237 Q59617553652.231Q59619599055.231Q63012415579.231Q63435846322.232Q64228675114.235Q64228675114.236Q64228946346.236Q64228946346.237Q64268197229.231Q66942122546.228Q66942122546.232Q66956788302.236Q66956788302.237Q67854022706.231Q67892150791.232Q6912043754.233 Q9933143375.231 Q9947771764.231 Q9947836772.227 00000100200600:00;00<00=00>00?00@00D00H00_00`01501?01E01F01L03=04n04o05905I05S05Y05]07808S09n0;I0;J0<N0=c0=d0?U0A00A10A20B60C?0DH0Ec0G>0H]0J<0L30Mj0Mk0OT0PX0PY0PZ0P[0P\0P]0R@0RA0TP0V_0Y40[I0[J0\S0]\0_70`R0`S0`T0ai0bm0d10e5FFS2FBS2FBSSSFFFS2FBS2FBS1R3HIA1h2sp2lo3TOP3HT0SS1R2FB3APS2d03XB13XB2S3gid1r2RRS1r2RRFS1R2FBS1R2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSS1R2FB3APSS1r2RR2r02KZ1q1HS1R2lo3LOSS1r2RRS2FBS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS1R2LF2sp2lo2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3ALO2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_st5SAEstFS1R5NEEDR2LF2sp2lo3SLO2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3NER2HB5Ha_st5Hl_stS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLFFFFFS1R2LF2sp2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEst5CM8stS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2F02F84FBLO4SP1R3NER2HB5Ha_st5Hl_st5SAEst5CM8stFS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HBS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFS1R2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE bs"] Lemma sp_errtail : forall (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (v f : Z) (dN dP dA dB dX dY dZ : mpd) (p : Z) (lnw vw vw' : word) (jref : list byte) (gid gj' pb nb : word) (v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 v16 v17 v18 : word) (K rr : Z) (xra t0 t1 t2 a0v a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s6v s7v : word),
    SPINVx hk LBk mk v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 (Z_to_bv 64 PKA) v16 v17 v18 K ->
    -(2 ^ 31) < rr < 0 -> v + pk_set_group_PHI <= pk_ecparams_PHI LEN -> f + 21 + pk_set_group_FR <= pk_ecparams_FR d ->
    aevtA asegs (KF asegs R HIA hk mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1 (Z_to_bv 64 (FB + 472)) a3 a4 a5 a6 a7 (Z_to_bv 64 FB) s3v (Z_to_bv 64 SHB) (Z_to_bv 64 (al_sb AL)) s6v s7v
              (Z_to_bv 64 (FB + 424)) (Z_to_bv 64 FB) (Z_to_bv 64 rr) (Z_to_bv 64 G) t3 t4 t5 t6) F (Z_to_bv 64 0xb0eec) fc None mk (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until s7v. (intros dd_H; ddestruct dd_H as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k); intros RR VB FB').
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
    pose proof (conj TOK (conj HHk (conj MIk (conj IDSk (conj CHk I))))) as BOX.
    unfold EP_SH_P in FSH. unfold SLPx in SLOTS.
    (* [comment removed for export] *)
    do 4 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH6 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ddestruct BOX as (TOK0 & HHk0 & MIk0 & IDSk0 & CHk0 & _).
    assert (OWN : Forall own_iv [(SHB, SHB + 80)]) by (apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    assert (EB6 : EB hk LBk m6 v f EP_SH_G
                    [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 s64; C8 s72; C8 s80; C8 (Z_to_bv 64 PKA); C8 (Z_to_bv 64 (G + 40));
                     C8 (Z_to_bv 64 (G + 24)); C8 (Z_to_bv 64 (FB + 624)); C8 (Z_to_bv 64 (G + 8)); C8 v16; C8 v17; C8 v18]
                    [(FB + 624, [C4 gid; C4 gj'])] (tmp_blocks (DS7 dN dP dA dB dX dY dZ)) W0).
    { replace (G + 40) with (FB + 408) by (clear; lia).
      replace (G + 24) with (FB + 392) by (clear; lia). replace (G + 8) with (FB + 376) by (clear; lia).
      unfold A_pk_ecparams_B.EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_G; cbn [repeat app]; exact FSH6| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [exact (ids_state_own hk LBk mk m6 _ HHk0 OWN IDSk0 MU WM)|].
      split; [eapply (ch_munch_sh mk m6 80); [apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CHk0)))))| apply Forall_nil]| exact MU| exact WM| clear - APS; lia]|].
      split; [exact EXTk| exact FRk]. }
    assert (TOK6 : tmp_ok asegs m6 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_own hk LBk mk m6 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN).
      intros d0 Hd. ddestruct TOK0 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2 APS; lia| exact I]. }
    rewrite <- (Z_to_bv_bv_unsigned gid) in EB6.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    - replace (FB + 472) with (G + 104) by (clear; lia). replace (FB + 424) with (G + 56) by (clear; lia).
      eapply (ep_cleanup hk LBk m6 v f dN dP dA dB dX dY dZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned gid) gj');
        first [ exact EB6 | exact EN | exact EP | exact EA | exact EB' | exact EX | exact EY | exact EZ | exact VB | exact FB' | exact TOK6
              | (clear - RR; lia) | (intros R0; exfalso; clear - R0 RR; lia) | idtac ].
    - exfalso. clear - KZ RR. Z.div_mod_to_equations. lia.
    all: match goal with |- ?g => idtac "ERRTAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE bs"] Lemma sp_erradd : forall (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (v f : Z) (dN dP dA dB dX dY dZ : mpd) (p : Z) (lnw vw vw' : word) (jref : list byte) (gid gj' pb nb : word) (v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 v16 v17 v18 : word) (K r : Z) (xra t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s6v s7v s10v : word),
    SPINVx hk LBk mk v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 (Z_to_bv 64 PKA) v16 v17 v18 K ->
    -127 < r < 0 -> v + pk_set_group_PHI <= pk_ecparams_PHI LEN -> f + 21 + pk_set_group_FR <= pk_ecparams_FR d ->
    aevtA asegs (KF asegs R HIA hk mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 (Z_to_bv 64 (FB + 472)) a3 a4 a5 a6 a7 (Z_to_bv 64 FB) s3v (Z_to_bv 64 SHB) (Z_to_bv 64 (al_sb AL)) s6v s7v
              (Z_to_bv 64 (FB + 424)) (Z_to_bv 64 FB) s10v (Z_to_bv 64 G) t3 t4 t5 t6) F (Z_to_bv 64 0xb0edc) fc None mk (seg_rom asegs)).
  Proof.
    intros until s10v. intros SI RR VB FB'.
    pose proof SI as (EBk & _). eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    unfold SLPx in SLOTS.
    do 3 zstep. rewrite swrap32_errsum_ep by (clear - RR; lia).
    zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA RR; ep_scheck KA|]. clear KA.
    eapply (sp_errtail hk LBk mk v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 s72 s80 v16 v17 v18 K); [exact SI| clear - RR; lia| exact VB| exact FB'].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L22409920380.201L28948604668.201L35668120898.7  L36667852792.0  L54992078076.201L60098763854.3  Q10980424452.207Q13398370664.207Q15026967797.207Q20610286325.207Q28436691071.207Q35062870404.207Q41263643765.207Q43071304964.207Q4359140991.207 Q46474998015.207Q58021947240.207Q7379058664.207 00001702>02U02V03]03g05606T07b0900:90;H0<V0=e0>n0@70AU0C3S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS1R3HIA1h2sp2lo3TOP3HT0SS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS1R2lo3LOSS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3SPRS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3NERS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4SP1RS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3SPRS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3SPRS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4SP1RS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4SP1RS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3NERS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3NER". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE bs"] Lemma sp_errbac : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$26.PdP,$26.PdA,$26.PdB,$26.PdX,$26.PdY,$26.PdZ,$26.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Ps64,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pr,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps3v,(4.&40.)Ps6v,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(42.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(3<.&40.(=.VFB,+1=8.))(3<.&40.VPKA,)R19.R18.R17.R16.)P,(14.(43.-7?.R16.)(43.R16.=))P,(<.(=.R35.$47.)(48.VLEN,))P,(<.(=.(=.R35.+15.)$49.)(4:.Vd,))(4;.$1.(4<.$1.VR,VHIA,R3:.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.R18.(3<.&40.Vsp1,)Vgp,Vtp,R17.R16.R15.Vsp,(3<.&40.Vsp1,)(3<.&40.R19.)R14.R13.R12.R11.R10.R?.R>.(3<.&40.VFB,)R9.(3<.&40.(=.(54.VFB,+3.)(55.(17.VR,))))(3<.&40.(55.(17.VR,)))R8.R7.R6.(3<.&40.VFB,)R5.(3<.&40.(=.VFB,+170.))R=.R<.R;.R:.)VF,(3<.&40.+;13><.)Vfc,(56.(4.&40.))R38.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI RR VB FB'.
    pose proof SI as (EBk & _). eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    unfold SLP in SLOTS.
    do 3 zstep. rewrite swrap32_errsum_ep by (clear - RR; lia).
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB; [|exfalso; clear - KB RR; ep_scheck KB].
    eapply (sp_errtail hk LBk mk v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 (FB + 424)) v16 v17 v18 K); [exact SI| clear - RR; lia| exact VB| exact FB'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis HRB : mpi_read_binary_stmtA_c asegs R HIA A_MPI_READ_BINARY.
  Hypothesis HGM : asn1_get_mpi_stmtA_c asegs R HIA A_ASN1_GET_MPI A_MPI_READ_BINARY.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24705784626.8L66790382386.800000H00`S1R3HIA1h2hk1v2v'3HVk2V'S1R3HIA1h2hk1f2f'3HFk2F'". (* [comment removed for export] *)
  #[using="Type"] Lemma eb_budget_mono : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.Pv',$6.Pf',$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R<.R;.R:.R9.R8.R5.R4.R3.R2.R1.)P,(<.R:.R8.)P,(<.R:.R8.)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R?.R>.R=.R:.R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f v' f' SH SL CH T WE EBk V' F'. eb_open EBk.
    unfold A_pk_ecparams_B.EB. split; [exact HHk|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|].
    split; [split; [clear - HVk V'; lia| clear - HFk F'; lia]|].
    split; [dexists w0, w1, w2; exact FHD|]. split; [exact (conj FSH NSH')|]. split; [exact FSHR|].
    split; [exact SAVE|]. split; [exact (conj SLOTS NSL)|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [exact MIk|].
    split; [exact PRES|]. split; [exact IDSk|]. split; [exact CHk|]. split; [exact EXTk| exact FRk].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00h0>L10593307264.1L12194040960.1L13755912320.1L14149697408.1L14828576118.1L15707161472.1L16918517376.1L17312286080.1L1918640256.1 L19252913526.1L19263550592.1L20474891136.1L22426417792.1L2312458112.1 L23637758336.1L24031280256.1L25982791552.1L27194131072.1L28751611520.1L29919923574.1L30356736128.1L30752618368.1L323045750.1  L33190543734.1L33913126272.1L35470590336.1L35862277248.1L37434634368.1L40597239424.1L40991008128.1L42189846656.1L42581256064.1L44153613184.1L45352451712.1L47712132224.1L48908825472.1L5079410304.1 L51457380726.1L52071430528.1L54035458176.1L5475063168.1 L55625706112.1L57198063232.1L57593716096.1L59149312384.1L60756534144.1L62711960192.1L63917042048.1L64312956032.1L65874565248.1L66268333952.1L67475561088.1L7036934528.1 L711462272.1  L8637668224.1 L9940486518.1 00000400800900=00A00E00I00M00N00R00V00Z00^00b00f00j00n01201601:01;01?01C01G01K01O01S01T01X01\01]01a01e01i01m02102502902=02>02B02F02J02N02R02V02Z02^02b02c02g02k02o03303703;S2FBS2FBFS2FBS2FBS2FBS2FBS2FBFS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBFS2FBS2FBS2FBS2FBS2FBS2FBFS2FBS2FBFS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBFS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBFS2FBS2FBS2FBS2FBS2FBS2FB". (* [comment removed for export] *)
  #[using="Type"] Lemma tmp_upd7 : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Pd',$26.PdN,$26.PdP,$26.PdA,$26.PdB,$26.PdX,$26.PdY,$26.PdZ,$26.P,(2?.$6.(2>.R7.)(=.(=.VFB,+170.)+68.))P,(2?.$6.(2>.R7.)(=.(=.VFB,+170.)+8.))P,(2?.$6.(2>.R7.)(=.(=.VFB,+170.)+18.))P,(2?.$6.(2>.R7.)(=.(=.VFB,+170.)+28.))P,(2?.$6.(2>.R7.)(=.(=.VFB,+170.)+38.))P,(2?.$6.(2>.R7.)(=.(=.VFB,+170.)+48.))P,(2?.$6.(2>.R7.)(=.(=.VFB,+170.)+58.))(14.P,(2?.$6.(2>.R?.)(=.(=.VFB,+170.)+68.))(2?.(2.$26.)(39.R10.(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(10.$26.R10.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(14.P,(2?.$6.(2>.R?.)(=.(=.VFB,+170.)+8.))(2?.(2.$26.)(39.R10.(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(10.$26.R?.(10.$26.R10.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(14.P,(2?.$6.(2>.R?.)(=.(=.VFB,+170.)+18.))(2?.(2.$26.)(39.R10.(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(10.$26.R?.(10.$26.R>.(10.$26.R10.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(14.P,(2?.$6.(2>.R?.)(=.(=.VFB,+170.)+28.))(2?.(2.$26.)(39.R10.(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R10.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(14.P,(2?.$6.(2>.R?.)(=.(=.VFB,+170.)+38.))(2?.(2.$26.)(39.R10.(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R10.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(14.P,(2?.$6.(2>.R?.)(=.(=.VFB,+170.)+48.))(2?.(2.$26.)(39.R10.(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R10.(10.$26.R9.(13.$26.)))))))))P,(2?.$6.(2>.R?.)(=.(=.VFB,+170.)+58.))(2?.(2.$26.)(39.R10.(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R9.(13.$26.)))))))))(10.$26.R?.(10.$26.R>.(10.$26.R=.(10.$26.R<.(10.$26.R;.(10.$26.R:.(10.$26.R10.(13.$26.)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros d' dN dP dA dB dX dY dZ EN EP EA EB' EX EY EZ. unfold tmp_upd. cbn [map]. rewrite EN, EP, EA, EB', EX, EY, EZ.
    repeat split; intros E; rewrite E;
      repeat match goal with |- context [?u =? ?v] =>
        first [ rewrite (proj2 (Z.eqb_neq u v)) by (clear; lia) | replace (u =? v) with true by (symmetry; apply Z.eqb_eq; clear; lia) ] end; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition sh_zero (SH : list cell) (g0 n : nat) : Prop := forall i, (i < n)%nat -> cell_at SH (g0 + i) = Some (C1 (Z_to_bv 8 0)).

  #[using="IMG NEEDR LOS SLO SP1 F64 FRSH"] Lemma sh_zero_aobj : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pg0,$5;.Pn,$5;.P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(5<.R8.R3.R2.)P,(<.(5=.+8.(>.(5>.R4.R3.)))+400.)(16.$1.(17.VR,)(18.$1.VR,VHIA,R?.)R=.(=.VFB,(5=.+8.(>.R5.)))(5=.+8.(>.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE g0 n EBk HZ HB. ddestruct EBk as (HHq & _ & _ & _ & _ & (FSHq & _) & _).
    eapply (sh_aobj hk mk SH _ g0 n); [exact FSHq| exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHq ltac:(left; reflexivity))| reflexivity| exact HB| exact HZ].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308586248.2000006S1i2Hi". (* [comment removed for export] *)
  #[using="Type"] Lemma shp_grp : sh_zero EP_SH_P 46 24.
  Proof. intros i Hi. unfold EP_SH_P. do 24 (destruct i as [|i]; [reflexivity|]). exfalso. clear - Hi. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308586248.2000006S1i2Hi". (* [comment removed for export] *)
  #[using="Type"] Lemma shp_p : sh_zero EP_SH_P 36 1.
  Proof. intros i Hi. unfold EP_SH_P. do 1 (destruct i as [|i]; [reflexivity|]). exfalso. clear - Hi. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308586248.2000006S1i2Hi". (* [comment removed for export] *)
  #[using="Type"] Lemma shp_len : sh_zero EP_SH_P 40 1.
  Proof. intros i Hi. unfold EP_SH_P. do 1 (destruct i as [|i]; [reflexivity|]). exfalso. clear - Hi. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L16650455615.3L16856855592.5L39280637297.0L40560514702.6L5116269607.3 L56056173140.3L57813259992.3L59321168151.9L63667055128.000000;00L00M00b00m01801C01a01bS2FB2d03DB2S2FB2d03DB13DB21KSS1R2lo3LOS2d03ALO3PACS2FB2d03DB1S2FB2d03DB1S2FB2d03DB2S1R2FB2d02F23DB13DB21a2Ha4HdatS". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO SP1 F64 FRSH"] Lemma tmp_member : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pds,(2.$26.)Pd0,$26.P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R;.R:.R9.R8.R7.$3>.R6.R5.R4.R3.)P,(28.$1.R:.R;.(=.VFB,+170.)+<0.R3.)P,(12.$26.R3.R4.)(14.(34.$1.R<.R=.R4.)(14.(46.(2?.$5?.(60.R4.)$61.))(14.(62.(1;.VR,)(1<.$3.R=.(1=.(10.(8.$6.$6.)(11.$6.$6.VFB,+400.)VLF,)))Vsp1,(30.$1.VR,VHIA,R>.)R4.)(14.(16.$1.(17.VR,)(18.$1.VR,VHIA,R>.)R<.(2>.R4.)+10.)(14.(63.VR,(2>.R4.)+10.=)(14.(14.(<.(=.VFB,+170.)(2>.R4.))(<.(=.(2>.R4.)+10.)(=.(=.VFB,+170.)+<0.)))P,(2?.$5?.(60.R4.)$64.)(14.(12.(8.$6.$6.)(11.$6.$6.(65.R5.)(5=.+4.(66.R5.)))R>.)(14.(<.+1.(66.R5.))(14.(37.(<.(=.(65.R5.)(5=.+4.(66.R5.)))VFB,)(<.(=.VFB,+400.)(65.R5.)))(14.(<.(=.(65.R5.)(5=.+4.(66.R5.)))Vlo,)(43.=(65.R5.))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SL CH T WE ds d0 EBk TOK Hd.
    pose proof (sh_zero_aobj _ _ _ _ _ _ _ _ _ _ 46 24 EBk shp_grp ltac:(clear; lia)) as OGRP. change (FB + 8 * Z.of_nat 46) with G in OGRP. change (8 * Z.of_nat 24) with 192 in OGRP.
    pose proof EBk as (HHk & _).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    destruct (hm_apart asegs R HIA hk _ _ _ HHk) as [HBR _]. rewrite Forall_forall in HBR.
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    pose proof (tmp_ok_in asegs _ _ _ _ _ _ TOK Hd) as MD. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (DNS & DB1 & DB2).
    assert (HB : md_own d0 = LHeap -> In (md_p d0, 4 * md_n d0) LBk /\ 1 <= md_n d0 /\ (md_p d0 + 4 * md_n d0 <= FB \/ FB + 1024 <= md_p d0) /\ md_p d0 + 4 * md_n d0 <= lo /\ 0 < md_p d0).
    { intros O. destruct (mpd_at_blk_in asegs mk LBk d0 MD O) as (Ix & Nx). split; [exact Ix|]. split; [exact Nx|].
      split; [exact (eb_blk_apart hk LBk mk _ _ HHk Ix)|].
      destruct (HBR _ ltac:(apply in_app_iff; left; exact Ix)) as (P0 & _ & PAC & _). cbn [fst snd] in P0, PAC. split; [clear - PAC ALO LOS; lia| exact P0]. }
    split; [exact MD|]. split; [exact DNS|].
    split. { split; [eapply client_wrange_block; [apply in_app_iff; right; exact INFD| clear - DB1; lia| clear - DB2; lia]|].
             split; [intros a Ha Hdat; exfalso; clear - Ha Hdat DB1 DB2 F2; lia|].
             intros O. ddestruct (HB O) as (_ & _ & K & _). clear - K DB1 DB2. lia. }
    split; [eapply aobj_sub; [exact OGRP| exact DB1| exact DB2]|].
    split; [eapply (uw_obj_block asegs R HIA hk LBk LF' mk FB 1024); [exact HHk| apply in_app_iff; right; left; reflexivity| clear - DB1; lia| clear - DB2; lia| clear; lia]|].
    split; [exact (conj DB1 DB2)| exact HB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis BSNE : 0 < Z.of_nat (length bs).
  Variable slo : Z.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLOK : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  #[using="R"] Lemma aobj_sshad8 : forall (CS : Z -> Prop) mX lo' hi' B,
    cs_ok AL CS -> sshad asegs AL mX lo' hi' -> lo' <= B -> B + 8 <= hi' -> B mod 8 = 0 -> 0 <= B ->
    crange CS B 8 -> aobj asegs AL CS mX B 8.
  Proof.
    intros CS mX lo' hi' B OK SS H1 H2 HB H0 HC.
    pose proof (sshad_chunk asegs AL mX lo' hi' 0 B SS H1 ltac:(clear - H2; lia) HB) as SH.
    replace (shadow_of AL B) with (Z.shiftr B 3 + al_sb AL) in SH
      by (clear; unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
    change (aobj asegs AL CS mX B (8 * Z.of_nat 1)).
    apply (aobj_of_zero_shadow_sh asegs AL CS mX B (zcells 1) B 0 1 OK SH HC HB H0 ltac:(clear; lia)).
    intros i Hi. destruct i as [|i]; [reflexivity| clear - Hi; lia].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L15756354262.400000>S1R2lo3LOS3ALO". (* [comment removed for export] *)
  #[using="HIA lo LOS CRB BSNE"] Lemma buf_fresh_apart : forall N k, fresh_apart R LB LF N k -> 0 < k -> N + k <= BUF \/ BUF + Z.of_nat (length bs) <= N.
  Proof.
    intros N k FR K0. pose proof (art_lo asegs R HIA) as ALO.
    eapply (fresh_apart_client R LB LF lo BUF _ N k FR CRB BSNE K0). clear - ALO LOS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L11549122101.13L18269587311.9 L18901988838.1 L19980016842.7 L20055703022.6 L2220721423.2  L22252508346.1 L25585110647.5 L25897709499.9 L3106837867.7  L3125951147.1  L31556981372.12L36463969417.13L40907215636.6 L43163024723.1 L52392417244.13L52772242515.6 L55588686165.0 L58972524609.3 L63141559144.1 L63667055128.0 L65724588151.3 L66151427842.16L7333388441.13 L7391519012.13 L7889766813.2  00000?00_00c01;01P01W01[01k02H02b02f03L03f04904=04P04f04g05305705805A05c06106K06RS2FB3BUF2bs3BFAS1R3HIA3LEN2hk1p4END'2h23HV33PHMS2FBS1R3HIA1h2sp3TOP3sp13SP1S3LBk3LB22d'2C22CB2WRS2FB2F0S2FBS1P3BUF2BP1p3PP1S1R3HIA1h1d4BUDF2hk1f3HFk3FB'S3LEN1P3BUF2bs2PL4END'3PP3S2FBS1R3HIA1h3LEN3BUD2hk1v1p4END'3HVk2VB1HS2sp2lo3sp13SP13BUF2bs3DSBS1R2lo3sp14SLO13NERS2FBS2lo2FB3sp12bs4FBLOS3LEN1P1p4END'3PP13PP3SS3BUF2bs3B47S2FBSS2FB2d01KS2FB2r02F81q1r1H2H02q02H43sp14SP1MS2FB2bs2d03DB1S2FB3BUF2bs2d03DB13DB23BFAS2d02Nx". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO TOP TPV SP1 SP1M F64 FRSH BUD BUDF BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL HRB HGM BSNE slo SSH SLOK SLOL"] Lemma sp_getmpi : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCHr,(2.(8.$6.(2.$7.)))Pds,(2.$26.)Pd0,$26.Pp,$6.PEND',$6.PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R24.R23.R22.R21.R20.$3>.R1?.(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+120.)(10.$7.(3=.(3<.&40.R1;.))(13.$7.)))R1>.)(27.R1=.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R23.R24.(=.VFB,+170.)+<0.R1>.)P,(12.$26.R1>.R1?.)P,(<.VP,R1>.)P,(<.R1?.R1>.)P,(<.R1?.(=.VP,VLEN,))P,(1?.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(25.(10.(8.$6.$6.)(11.$6.$6.(=.VFB,+120.)(=.VFB,+128.))(10.(8.$6.$6.)(11.$6.$6.(2>.R23.)(=.(2>.R23.)+10.))(13.(8.$6.$6.))))(20.$6.(2.$7.)R1.)(>.(?.(21.$6.(2.$7.)R1.))))R24.)P,(<.(=.(3:.R2:.)+1.)$67.)P,(14.(<.=R21.)(43.R21.(45.+2.+40.)))P,(2?.$6.(5:.R22.+2.)=)P,(<.(=.R2;.(68.VLEN,))(48.VLEN,))P,(<.(=.R2;.(69.=))(4:.Vd,))P,Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))Pd',$26.Pr,$6.Pp',$6.Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R14.R13.R12.(=.R41.(68.VLEN,))(=.R40.(69.=))$3>.R3?.(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+120.)(10.$7.(3=.(3<.&40.R?.))(13.$7.)))R3>.)(27.(39.R11.R3=.))(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R13.R14.(=.VFB,+170.)+<0.(39.R12.R3>.))P,(2?.$6.(2>.R13.)(2>.R3>.))P,(<.(3:.R16.)(=.(3:.R46.)+1.))P,(14.(<.R3?.R13.)(<.R13.R3>.))P,(14.(43.-7?.R15.)(<.R15.=))P,P,(2?.$6.R16.=)(14.(<.(=.R42.+2.)R16.)(2?.$6.(6:.R18.)+1.))(4;.$1.(4<.$1.VR,VHIA,R1;.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R40.)(3<.&40.Vsp1,)Vgp,Vtp,R15.R14.R13.R3<.R3;.(3<.&40.R17.)R12.R11.R10.R?.R>.R=.R<.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R;.R:.R9.R8.)VF,(3<.&40.R40.)Vfc,(56.(4.&40.))R19.(57.$1.)))(4;.$1.(4<.$1.VR,VHIA,R31.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R26.)(3<.&40.Vsp1,)Vgp,Vtp,R25.R24.R23.R22.R21.(3<.&40.(=.VFB,+120.))(3<.&40.R27.)(3<.&40.(2>.R29.))R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)VF,(3<.&40.$6;.)Vfc,(56.(4.&40.))R2?.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EBk TOK Hd PP1 PP2 PP3 HCD C24k RETr RETe VB FB' CONT.
    destruct (tmp_member hk LBk mk v f SL _ _ _ ds d0 EBk TOK Hd) as (MD & DNS & MW & OX & UWX & (DB1 & DB2) & HBK).
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EBk) as (HBSk & OBUFk & CRBk).
    pose proof (sh_zero_aobj _ _ _ _ _ _ _ _ _ _ 36 1 EBk shp_p ltac:(clear; lia)) as OPP. change (FB + 8 * Z.of_nat 36) with (FB + 288) in OPP. change (8 * Z.of_nat 1) with 8 in OPP.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ CHr _ _ EBk ltac:(intros c Hc; right; exact Hc)) as EBr.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTOPk. rewrite ETk, ESk in HTOPk.
    pose proof (buf_fresh_apart FB 1024 FRSH ltac:(clear; lia)) as BFA.
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    assert (HBA : md_own d0 = LHeap -> BUF + Z.of_nat (length bs) <= md_p d0 \/ md_p d0 + 4 * md_n d0 <= BUF)
           by (intros O; ddestruct (HBK O) as (Ix & Nx & _); destruct (buf_fresh_apart (md_p d0) (4 * md_n d0)
                 ltac:(apply (FRk (md_p d0, 4 * md_n d0)); apply in_tmp_blocks; exists d0; split; [exact Hd| rewrite (mpd_blk_heap _ O); left; reflexivity]) ltac:(clear - Nx; lia)) as [Q|Q]; [right| left]; exact Q).
    assert (SSk : sshad asegs AL mk slo (bv_unsigned sp)).
    { eapply (presA_sshad asegs R); [exact (presW_presA asegs R HIA hk LB LF _ _ _ m mk PRES)| exact SSH| exact SLOK|].
      rewrite ESk. clear - HTOPk TOP. lia. }
    assert (SCS1 : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. clear - HTOPk TOP SP1. lia. }
    assert (OGM : aobj asegs AL (hcs asegs R HIA hk) mk (sp1 - 40) 8).
    { pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
      eapply (aobj_sshad8 _ mk slo (bv_unsigned sp)); [exact (hcs_ok asegs R HIA hk)| exact SSk| clear - SLOL SLO SP1 SLO1 NER NEEDR; lia| clear - SP1; lia
      | clear - SP1M; Z.div_mod_to_equations; lia| clear - ACP ALO LOS SLO SP1 SLO1 NER NEEDR; lia
      | eapply crange_sub; [exact SCS1| clear - SLO SP1 SLO1 NER NEEDR; lia| clear; lia]]. }
    pose proof (HGM HRB) as SG; unfold asn1_get_mpi_stmtA_c in SG.
    eapply aevtA_call;
      [ intros mo1 [HK1 MF1];
        eapply (SG hk LBk LF') with (PP := FB + 288) (P := p) (END := END') (BUF := BUF) (bs := bs) (dX := d0) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HK1 | exact HHk | exact PCELL | exact HBSk | exact MD | exact DNS | exact MW | exact STb | exact LOS | exact TPV | exact MIk | exact OPP | exact OX | exact OBUFk | exact OGM
              | exact UWX | exact B47 | exact BUF0 | exact HBA | exact CRBk | reflexivity
              | lazymatch goal with
                | |- BUF <= p => clear - BP PP1; lia
                | |- p <= END' => exact PP2
                | |- END' <= BUF + _ => clear - PP3 PL; lia
                | |- BUF + _ < 2^63 => clear - B47; lia
                | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia]
                | |- md_own d0 = LHeap -> _ => intros O; ddestruct (HBK O) as (_ & _ & K & _); clear - K; lia
                | |- _ mod 8 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < FB + 288 => clear - F0; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => pose proof (MPI_RB_PHI_mono (END' - p) LEN ltac:(clear - PP1 PP3; lia)); clear - BUD HVk VB H; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFk FB'; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_GET_MPI_c; exact C24k
                | |- _ \/ _ => clear - BFA DB1 DB2 FBLO DSB SP1; lia
                end
              | match goal with |- ?g => idtac "GM-PRE-LEFT:" g end ]
      | ].
    cbv beta; (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)); unfold asn1_get_mpi_postA_c in PO;
      ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & LB2 & d' & r & p' & E & PO);
      injection E as -> ->;
      ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & MD2 & OUT & PC2 & PB2 & RR2 & ROK & NEW & _);
      rewrite ?(unsigned_lit sp1) in ST2, PXl by exact SP1R;
      replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]);
      pose proof (MPI_RB_PHI_mono (END' - p) LEN ltac:(clear - PP1 PP3; lia)) as PHM;
      destruct (sp_mpi_step hk LBk mk v f _ _ CHr ds d0 d' h2 LB2 m2 (MPI_RB_PHI LEN) (MPI_RB_FR 0) [(FB + 288, FB + 288 + 8)] EBr TOK Hd HH2 MI2 ST2 PXl HT3 HS3 HF3 HCS3
                  ltac:(clear - HV3 PHM; lia) HFR3 MD2 OUT NEW
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil])
                  ltac:(replace (FB + 288 + 8) with (FB + 296) by (clear; lia); exact HCD)) as (EB2 & TOK2 & C2);
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2)));
      (eapply CONT; [| exact TOK2| exact (proj1 OUT)| | exact PB2| exact RR2| exact ROK]);
      [ eapply eb_ch_add; [exact EB2| exact PC2| clear; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]
      | pose proof (cnt24_mpd_blk d') as CB; pose proof (w24_range (4 * md_n d')) as WR; destruct (md_own d'); clear - C2 CB WR; lia ].
    all: match goal with |- ?g => idtac "GM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10426594609.9 L11423978205.12L1270244852.11 L12830807156.23L17651402493.23L17696793344.5 L17696793473.11L18269587311.8 L19980016842.7 L20055703022.6 L21204209940.6 L2425330274.11 L25897709499.9 L27627898957.11L27627898957.8 L39170172714.6 L55588686165.0 L55806790098.23L56206086928.6 L64002619400.13L66151427842.16L7889766813.2  00000L00o01P02@03003?03Q03l04D04Y04l05505R05j06B06V06W07607G07j08F08MS3LEN1P3BUF2bs3B472PL1q1n2Q2S3LEN1P3BUF2bs2BP2PL1q1n2Q12Q21a2HaS1R3HIA1h3LEN3BUD2hk1v1n3HVk2VB1HS2FB3LEN1P3BUF2bs2BP2PL2d01q1n2Q12Q23DB13DB23BFAS2sp2lo3sp13SP13LEN1P3BUF2bs3DSB2BP2PL1q1n2Q12Q2S1P3BUF2BP1q2Q1S1P3BUF2bs2BP1q2Q1S1R3HIA3LEN2hk1n2h23HV33PHMS1R3HIA1h2sp3TOP3sp13SP1S3LBk3LB22d'2C22CB2WRS1R2lo3sp14SLO13NERS2bs1n2N0S1R3HIA1h1d4BUDF2hk1f3HFk3FB'S3LEN1P3BUF2bs2PL1q1n2Q2S3LEN1P3BUF2bs2PL1q1n2Q2S1P3BUF4BUF02BP1q2Q1SS3LEN1P3BUF2bs3B472PL1q1n2N02Q2S3LEN1P1q1n2Q12Q2S3LEN1P3BUF2bs2BP2PL2d01q1n2Q12Q21KS3sp12r04SP1M1q1r1H2H02q02H4S2d02Nx". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO TOP TPV SP1 SP1M F64 FRSH BUD BUDF BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL HRB BSNE"] Lemma sp_readbin : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))Pds,(2.$26.)Pd0,$26.Pq,$6.Pn,$6.PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R24.R23.R22.R21.R20.$3>.R1?.R1>.(27.R1=.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R23.R24.(=.VFB,+170.)+<0.R1>.)P,(12.$26.R1>.R1?.)P,(<.VP,R1>.)P,(<.=R1>.)P,(<.(=.R20.R1?.)(=.VP,VLEN,))P,(1?.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(25.(10.(8.$6.$6.)(11.$6.$6.(2>.R23.)(=.(2>.R23.)+10.))(13.(8.$6.$6.)))(20.$6.(2.$7.)R1.)(>.(?.(21.$6.(2.$7.)R1.))))R24.)P,(<.(=.(3:.R2:.)+1.)$67.)P,(14.(<.=R21.)(43.R21.(45.+2.+40.)))P,(2?.$6.(5:.R22.+2.)=)P,(<.(=.R2;.(68.VLEN,))(48.VLEN,))P,(<.(=.R2;.(69.=))(4:.Vd,))P,Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))Pd',$26.Pr,$6.Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R13.R12.R11.(=.R40.(68.VLEN,))(=.R3?.(69.=))$3>.R3>.R3=.(27.(39.R10.R3<.))(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R12.R13.(=.VFB,+170.)+<0.(39.R11.R3=.))P,(2?.$6.(2>.R12.)(2>.R3=.))P,(<.(3:.R15.)(=.(3:.R45.)+1.))P,(37.(2?.$6.R13.=)(2?.$6.R13.$6<.))P,P,(2?.$6.R14.=)(14.(2?.$6.(6:.R16.)+1.)(2?.$6.(66.R16.)(6=.R3?.)))(4;.$1.(4<.$1.VR,VHIA,R19.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R3>.)(3<.&40.Vsp1,)Vgp,Vtp,R14.R13.R12.R3:.R39.(3<.&40.R15.)R11.R10.R?.R>.R=.R<.R;.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R:.R9.R8.R7.)VF,(3<.&40.R3>.)Vfc,(56.(4.&40.))R17.(57.$1.)))(4;.$1.(4<.$1.VR,VHIA,R31.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R26.)(3<.&40.Vsp1,)Vgp,Vtp,R25.R24.R23.R22.R21.(3<.&40.(2>.R29.))(3<.&40.R28.)(3<.&40.R27.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)VF,(3<.&40.$6>.)Vfc,(56.(4.&40.))R2?.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EBk TOK Hd Q1 N0 Q2 HCD C24k RETr RETe VB FB' CONT.
    destruct (tmp_member hk LBk mk v f SL _ _ _ ds d0 EBk TOK Hd) as (MD & DNS & MW & OX & UWX & (DB1 & DB2) & HBK).
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EBk) as (HBSk & OBUFk & CRBk).
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (buf_fresh_apart FB 1024 FRSH ltac:(clear; lia)) as BFA.
    assert (HBA : md_own d0 = LHeap -> BUF + Z.of_nat (length bs) <= md_p d0 \/ md_p d0 + 4 * md_n d0 <= BUF)
      by (intros O; ddestruct (HBK O) as (Ix & Nx & _); destruct (buf_fresh_apart (md_p d0) (4 * md_n d0)
            ltac:(apply (FRk (md_p d0, 4 * md_n d0)); apply in_tmp_blocks; exists d0; split; [exact Hd| rewrite (mpd_blk_heap _ O); left; reflexivity]) ltac:(clear - Nx; lia)) as [Q|Q]; [right| left]; exact Q).
    set (ibs := firstn (Z.to_nat n) (skipn (Z.to_nat (q - BUF)) bs)).
    assert (LENI : Z.of_nat (length ibs) = n) by (subst ibs; apply P_asn1_get_mpi.bytes_at_sub_length; clear - BP PL Q1 N0 Q2; lia).
    assert (HIB : bytes_at asegs mk q ibs) by (subst ibs; eapply P_asn1_get_mpi.bytes_at_sub; [exact HBSk| | |]; clear - BP PL Q1 N0 Q2; lia).
    pose proof HRB as SG. unfold mpi_read_binary_stmtA_c in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (SG hk LBk LF') with (dX := d0) (B := q) (ibs := ibs) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?LENI;
        first [ exact HK1 | exact HHk | exact HIB | exact MD | exact DNS | exact MW | exact STb | exact LOS | exact TPV | exact MIk | exact OX
              | exact UWX | reflexivity
              | lazymatch goal with
                | |- 0 < q => clear - BUF0 BP Q1; lia
                | |- q + _ < 2^63 => clear - B47 PL Q2; lia
                | |- client_range _ _ _ _ _ => intros a Ha; apply CRBk; clear - Ha BP PL Q1 Q2; lia
                | |- aobj _ _ _ _ q _ => eapply aobj_sub; [exact OBUFk| clear - BP Q1; lia| clear - PL Q2; lia]
                | |- md_own d0 = LHeap -> _ => intros O; pose proof (HBA O) as K; clear - K BP PL Q1 N0 Q2; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => rewrite unsigned_lit by exact RETr; exact RETe
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => pose proof (MPI_RB_PHI_mono n LEN ltac:(clear - Q1 Q2; lia)); clear - BUD HVk VB H; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFk FB'; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_RB_c; exact C24k
                | |- _ \/ _ => clear - BFA DB1 DB2 FBLO DSB SP1 BP PL Q1 N0 Q2 B47; lia
                end
              | match goal with |- ?g => idtac "RB-PRE-LEFT:" g end ]. }
    cbv beta; (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)); unfold mpi_read_binary_postA_c in PO.
    ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & LB2 & d' & r & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & MD2 & OUT & RR2 & ROK & NEW & _).
    rewrite ?(unsigned_lit sp1) in ST2, PXl by exact SP1R. rewrite LENI in HV3, ROK.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    pose proof (MPI_RB_PHI_mono n LEN ltac:(clear - Q1 Q2; lia)) as PHM.
    destruct (sp_mpi_step hk LBk mk v f _ _ CH ds d0 d' h2 LB2 m2 (MPI_RB_PHI LEN) (MPI_RB_FR 0) [] EBk0 TOK Hd HH2 MI2 ST2 PXl HT3 HS3 HF3 HCS3
                ltac:(clear - HV3 PHM; lia) HFR3 MD2 OUT NEW ltac:(apply Forall_nil) HCD) as (EB2 & TOK2 & C2).
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply CONT; [exact EB2| exact TOK2| exact (proj1 OUT)| | exact RR2| exact ROK].
    pose proof (cnt24_mpd_blk d') as CB; pose proof (w24_range (4 * md_n d')) as WR; destruct (md_own d'); clear - C2 CB WR; lia.
    all: match goal with |- ?g => idtac "RB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis UWC0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L26892418956.1 L28573888615.20L49799904432.3 L56658999053.1 L57628696595.20L62037160523.9 L66151427842.16L691677035.10  00000401801D01H02F02e03?03`S2spS1R3HIA5NEEDR5IDONE3IDS1h2sp2lo3LOS3SLO1C3ALO3NER3CAC2I22I33DHI1a2HaS2sp3sp13SP1S2spS1R3HIA5NEEDR5IDONE3IDS1h2sp2lo3LOS3SLO3ALO3NER2I22I33DHI1a2HaS1R5NEEDR2sp2lo3LOS3SLO3SPR3NERS2sp2r03SPA1q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3ALO3NER1H". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO SPA HH0 SP1 F64 FRSH INC D0 UWC0"] Lemma eb_uwc : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(37.(2?.(2.$9.)R2.(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))(2?.(2.$9.)R2.(10.(8.$6.$6.)(11.$6.$6.VC,(=.VC,+<0.))(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))))(6?.$1.R:.(2<.VR,)(2=.$1.VR,VHIA,R<.)(70.&40.Vsp,)Vsp1,(=.Vd,+1.))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE EBk WEC. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    dpose kp_block_facts as (C0 & CAC & CIM). ddestruct IDOK as (I1 & I2 & I3 & _). pose proof (art_data_lo asegs R HIA) as DHI. cbn in DHI.
    pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES) as HP. rewrite ESk in HP.
    assert (UW1 : uwc asegs mk (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP| exact UWC0| clear; lia| | clear - SPR ALO LOS SLO NEEDR NER; pose proof (alloc_ceiling_pos (L := arl_L R)); lia| apply hstkhi_le64; clear - SPR ALO LOS SLO NEEDR NER; lia].
      intros a Ha. destruct WEC as [-> | ->]; cbn [outside]; clear - Ha CAC I1 I2 I3 DHI ALO LOS SLO NEEDR NER; lia. }
    rewrite ESk.
    pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
    replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
    eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L19980016842.7 L23929269012.6 L4781719053.2  L50378799435.9 L5116269607.3  L57813259992.3 L59821159884.9 L66151427842.1600000H00[00a01>01I01T02102MS1R3HIA1h2sp3TOP3sp13SP1S1R2lo3sp14SLO13NERS1d2D0S1R3HIA1h1d4BUDF2hk1f3HFk3FB'S2FB2d03DB1S2FB2d03DB2S1R3HIA1h3LEN3BUD2hk1v3HVk2VBS3sp12r04SP1M1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO TOP SPA TPV HH0 SP1 SP1M F64 FRSH INC BUD BUDF D0 HLSET UWC0"] Lemma sp_lset : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))Pds,(2.$26.)Pd0,$26.Pz,$6.PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R23.R22.R21.R20.R1?.$3>.R1>.R1=.(27.R1<.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R22.R23.(=.VFB,+170.)+<0.R1=.)P,(12.$26.R1=.R1>.)P,(14.(<.(44.(45.+2.+1?.))R1=.)(43.R1=.(45.+2.+1?.)))P,(1?.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(25.(10.(8.$6.$6.)(11.$6.$6.(2>.R20.)(=.(2>.R20.)+10.))(13.(8.$6.$6.)))(20.$6.(2.$7.)R1.)(>.(?.(21.$6.(2.$7.)R1.))))R21.)P,(14.(<.=R1>.)(43.R1>.(45.+2.+40.)))P,(2?.$6.(5:.R1?.+2.)=)P,(<.(=.R27.(71.+1.))(48.VLEN,))P,(<.(=.R27.+3.)(4:.Vd,))P,Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))Pd',$26.Pr,$6.Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R13.R12.R11.(=.R3<.(71.+1.))(=.R3;.+3.)$3>.R3:.R39.(27.(39.R10.R38.))(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R12.R13.(=.VFB,+170.)+<0.(39.R11.R39.))P,(2?.$6.(2>.R12.)(2>.R39.))P,(<.(3:.R15.)(=.(3:.R41.)(3:.(36.R13.))))P,(72.R3:.R3;.R42.R13.R14.)(4;.$1.(4<.$1.VR,VHIA,R18.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R3:.)(3<.&40.Vsp1,)Vgp,Vtp,R13.R12.R11.Vsp,R36.(3<.&40.R14.)R10.R?.R>.R=.R<.R;.R:.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R9.R8.R7.R6.)VF,(3<.&40.R3:.)Vfc,(56.(4.&40.))R16.(57.$1.)))(4;.$1.(4<.$1.VR,VHIA,R2=.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R23.)(3<.&40.Vsp1,)Vgp,Vtp,R22.R21.R20.Vsp,R1?.(3<.&40.(2>.R25.))(3<.&40.R24.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)VF,(3<.&40.$73.)Vfc,(56.(4.&40.))R2;.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EBk TOK Hd ZB HCD RETr RETe VB FB' CONT.
    destruct (tmp_member hk LBk mk v f SL _ _ _ ds d0 EBk TOK Hd) as (MD & DNS & MW & OX & _ & (DB1 & DB2) & HBK).
    pose proof (eb_uwc _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as UWk.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof HLSET as SG. unfold mpi_lset_stmtA, mpi_xop_stmtA in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (SG hk LBk LF') with (dX := d0) (v := z) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HK1 | exact HHk | exact MD | exact DNS | exact ZB | exact STb | exact LOS | exact TPV | exact MIk | exact UWk | reflexivity
              | exact (mpd_writableA_of_P R _ _ _ _ _ MW)
              | lazymatch goal with
                | |- md_own d0 <> LNull -> _ => intros O; destruct (md_own d0) eqn:OO; [exfalso; apply O; reflexivity| ddestruct (HBK eq_refl) as (_ & _ & _ & K & _); left; exact K| exfalso; apply DNS; reflexivity]
                | |- mpd_aobjA _ _ _ _ _ => split; [exact OX| intros O; exfalso; exact (DNS O)]
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => rewrite unsigned_lit by exact RETr; exact RETe
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVk VB; lia
                | |- uw_obj _ _ _ _ => eapply (uw_obj_block asegs R HIA hk LBk LF' mk FB 1024); [exact HHk| apply in_app_iff; right; left; reflexivity| clear - DB1; lia| clear - DB2; lia| clear - D0; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => rewrite lset_FR_val; clear - BUDF HFk FB'; lia
                end
              | match goal with |- ?g => idtac "LS-PRE-LEFT:" g end ]. }
    cbv beta; (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)); unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & LB2 & d' & r & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & MD2 & OUT & NEW & RR2).
    rewrite ?(unsigned_lit sp1) in ST2, PXl by exact SP1R. rewrite lset_FR_val in HFR3.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    destruct (sp_mpi_step hk LBk mk v f _ _ CH ds d0 d' h2 LB2 m2 (grow_PHI 1) 3 [] EBk0 TOK Hd HH2 MI2 ST2 PXl HT3 HS3 HF3 HCS3
                HV3 HFR3 MD2 OUT NEW ltac:(apply Forall_nil) HCD) as (EB2 & TOK2 & C2).
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply CONT; [exact EB2| exact TOK2| exact (proj1 OUT)| exact C2| exact RR2].
    all: match goal with |- ?g => idtac "LS-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis HGT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L10550305273.8 L12207507179.1 L15362649509.3 L18901988838.1 L2220721423.2  L2225046107.11 L22252508346.1 L25585110647.5 L27940850327.6 L2950192944.14 L3106837867.7  L35248808226.14L35915898997.14L4185783531.1  L42989464550.1 L44139193149.14L46852734735.2 L51253953853.14L55588686165.0 L58972524609.3 L60098763854.3 L63667055128.0 L64385852090.1 L66151427842.16L66177879973.3 L66667331848.1 L67228227629.9 L8981313288.1  00000P00T00_00c00j01R01V01f02?02F02`03K03Z03^03b04F04M05105205>05H05I05M05o06:06>06]06aS1R5NEEDR2sp2lo3sp13SP14SLO13NERS2FBS2FB2d03XB1S2FBS2FB2F0S1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2d03XB2S2FBS1P3BUF2BP1p3PP1S1R5NEEDR2lo3sp14SLO13NERS2FB2bsS3LEN1P3BUF2bs2PL4END'3PP3S1R5NEEDR2sp2lo3sp13SP13BUF2bs3DSB4SLO13NERS2FB3BUF2bs3BFAS2FBS2FBS1R5NEEDR2lo2FB3sp12bs4FBLO4SLO13NERS2FB2F0S1R5NEEDR2lo2FB3sp12bs4FBLO4SLO13NERSS3BUF2bs3B47S1R2lo3LOSSS2FBS2FB2r02F81q1r1H2H02q02H43sp14SP1MS2FB2d03XB1S2FBS1R3HIA1h2sp2lo3TOP3sp13SP13HT0S2FB". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 SP1M F64 FRSH BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL BSNE HGT"] Lemma sp_gettag : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCHr,(2.(8.$6.(2.$7.)))Pds,(2.$26.)Pp,$6.PEND',$6.Ptag,$6.PRET,$6.Plnw,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R24.R23.R22.R21.R20.$3>.R1?.(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+120.)(10.$7.(3=.(3<.&40.R1<.))(13.$7.)))(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+140.)(10.$7.(3=.R18.)(13.$7.)))R1>.))(27.R1=.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R23.R24.(=.VFB,+170.)+<0.R1>.)P,(<.VP,R1>.)P,(<.R1?.R1>.)P,(<.R1?.(=.VP,VLEN,))P,(1?.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(25.(10.(8.$6.$6.)(11.$6.$6.(=.VFB,+120.)(=.(=.VFB,+120.)+8.))(10.(8.$6.$6.)(11.$6.$6.(=.VFB,+140.)(=.(=.VFB,+140.)+8.))(13.(8.$6.$6.))))(20.$6.(2.$7.)R1.)(>.(?.(21.$6.(2.$7.)R1.))))R23.)P,(14.(<.=R1?.)(43.R1?.(45.+2.+40.)))P,(2?.$6.(5:.R20.+2.)=)P,Pm2,P,(4.&40.)(5.(4.&8.))Pr,$6.Pp',$6.PL',(4.&40.)Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R3>.R3=.R12.R3;.R3:.$3>.R39.(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+120.)(10.$7.(3=.(3<.&40.R10.))(13.$7.)))(10.(8.$6.(2.$7.))(11.$6.(2.$7.)(=.VFB,+140.)(10.$7.(3=.R?.)(13.$7.)))R38.))(27.R37.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R13.R3>.(=.VFB,+170.)+<0.R38.)P,(14.(<.R38.R12.)(<.R12.R37.))P,(14.(43.-7?.R14.)(<.R14.=))P,P,(2?.$6.R15.=)(14.(<.(=.R3;.+2.)R15.)(<.(70.&40.R14.)(58.R3:.R15.)))(4;.$1.(4<.$1.VR,VHIA,R43.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R38.)(3<.&40.Vsp1,)Vgp,Vtp,R13.R12.R11.R33.R32.(3<.&40.R16.)R10.R?.R>.R=.R<.R;.R:.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R9.R8.R7.R6.)VF,(3<.&40.R38.)Vfc,(56.(4.&40.))R17.(57.$1.)))(4;.$1.(4<.$1.VR,VHIA,R2=.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R22.)(3<.&40.Vsp1,)Vgp,Vtp,R20.R1?.R1>.R1=.R1<.(3<.&40.(=.VFB,+120.))(3<.&40.R24.)(3<.&40.(=.VFB,+140.))(3<.&40.R23.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(3<.&40.$74.)Vfc,(56.(4.&40.))R2;.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EBk TOK PP1 PP2 PP3 HCD RETr RETe CONT.
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EBk) as (HBSk & OBUFk & CRBk).
    pose proof (sh_zero_aobj _ _ _ _ _ _ _ _ _ _ 36 1 EBk shp_p ltac:(clear; lia)) as OPP. change (FB + 8 * Z.of_nat 36) with (FB + 288) in OPP. change (8 * Z.of_nat 1) with 8 in OPP.
    pose proof (sh_zero_aobj _ _ _ _ _ _ _ _ _ _ 40 1 EBk shp_len ltac:(clear; lia)) as OLP. change (FB + 8 * Z.of_nat 40) with (FB + 320) in OLP. change (8 * Z.of_nat 1) with 8 in OLP.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_intror (or_introl eq_refl))) as LCELL.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ CHr _ _ EBk ltac:(intros c Hc; right; right; exact Hc)) as EBr.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (buf_fresh_apart FB 1024 FRSH ltac:(clear; lia)) as BFA.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP SP1. lia. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof HGT as SP. unfold asn1_get_tag_stmtA in SP.
      eapply SP with (CS := hcs asegs R HIA hk) (PP := FB + 288) (LENP := FB + 320) (P := p) (END := END') (BUF := BUF) (bs := bs) (lo := lo) (tag := tag);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact PCELL | exact LCELL | exact HBSk | exact MIk | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk)
              | exact (hm_abase asegs R HIA hk LBk LF' mk HHk) | exact OPP | exact OLP | exact OBUFk | exact STb | exact SCSk | exact BUF0 | reflexivity
              | lazymatch goal with
                | |- BUF <= p => clear - BP PP1; lia
                | |- p <= END' => exact PP2
                | |- END' <= BUF + _ => clear - PP3 PL; lia
                | |- BUF + _ < 2^63 => clear - B47; lia
                | |- _ mod 8 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < FB + _ => clear - F0; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ \/ _ => clear - BFA FBLO DSB SP1 SLO1 NER NEEDR; lia
                end
              | match goal with |- ?g => idtac "GT-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold asn1_get_tag_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & r & p' & L' & E & MU2 & WM2 & MI2 & EA0 & RR2 & PC2 & LC2 & PB2 & ROK & ST2). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R. subst y3.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    pose proof (eb_munchF hk LBk mk v f _ _ CHr _ _ m2 [(FB + 288, FB + 288 + 8); (FB + 320, FB + 320 + 8)] (sp1 - 16) EBr MU2 ltac:(clear - SLO1 NER NEEDR; lia)
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]]) WM2 MI2 ST2 HCD) as EB2.
    eapply CONT; [| | exact PB2| exact RR2| exact ROK].
    - eapply eb_ch_add; [eapply eb_ch_add; [exact EB2| exact LC2| clear; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]| exact PC2| clear; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia].
    - eapply (tmp_ok_own hk LBk mk m2 _ _ HHk TOK MU2 WM2 MIk MI2).
      + apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_cons; [right; right; cbn [fst snd]; clear - SLO1 NER NEEDR SP1; lia| apply Forall_nil]]].
      + intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
        cbn [disjoint_from app]. split; [clear - XB1; lia| split; [clear - XB1; lia| split; [clear - XB1 XB2 FBLO SLO1 NER NEEDR; lia| exact I]]].
    all: match goal with |- ?g => idtac "GT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L20412201782.7 L20416363692.8 L29432667347.5 L3482346814.8  L3486638756.6  L38235734261.1 L38408712019.4 L39846496343.5 L5196155000.7  L60098763854.3 L66151427842.16L67228227629.9 00000100U00e00f00g00k01:01M01c01m02I02hFS1R5NEEDR2lo3sp15STACK4HSTK4SLO13NERS1R2lo3LOS3ALO1HFFS2loS2sp2lo3sp13SP1S2lo2FB2d03DB24FBLOS2lo2FB3sp14FBLO1x3XB2S1R2lo3LOSS3sp12r04SP1M1q1r1H2H02q02H4S1R3HIA1h2sp2lo3TOP3sp13SP13HT0". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 SP1M F64 FRSH"] Lemma sp_query : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "PENTRY,$6.PSTACK,$6.PPRE,P,$26.P,$6.SpPRq,P,$26.P,$6.P,$6.SpP,(75.$1.(17.VR,)R4.R3.R2.R1.)P,(<.R4.+20.)Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))Pds,(2.$26.)Pd0,$26.PRET,$6.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs0,(4.&40.)Pxs1,(4.&40.)Pa1v,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs8,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R24.R23.R22.R21.R20.$3>.R1?.R1>.(27.R1=.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R23.R24.(=.VFB,+170.)+<0.R1>.)P,(12.$26.R1>.R1?.)P,A2.R2;.R1?.(70.&40.R18.)P,(14.(<.=R1?.)(43.R1?.(45.+2.+40.)))P,(2?.$6.(5:.R20.+2.)=)P,Pm2,P,(4.&40.)(5.(4.&8.))Pr,$6.Py0,(4.&40.)Py1,(4.&40.)Py2,(4.&40.)Py4,(4.&40.)Py5,(4.&40.)Py6,(4.&40.)Py7,(4.&40.)Py8,(4.&40.)Py9,(4.&40.)Py10,(4.&40.)Py11,(4.&40.)Py12,(4.&40.)Py13,(4.&40.)Py14,(4.&40.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R3:.R39.R10.R37.R36.$3>.R35.R34.(27.R33.)(10.(8.$6.$6.)(11.$6.$6.VIDONE,(=.VIDONE,+1.))(10.(8.$6.$6.)(11.$6.$6.VIDS,(=.VIDS,+38.))(13.(8.$6.$6.)))))P,(28.$1.R11.R3:.(=.VFB,+170.)+<0.R34.)P,A3.R3?.R34.(70.&40.R2=.)R11.(4;.$1.(4<.$1.VR,VHIA,R3=.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R34.)(3<.&40.Vsp1,)Vgp,Vtp,R11.R10.R?.R30.R2?.(3<.&40.R12.)R>.R=.R<.R;.R:.R9.R8.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R7.R6.R5.R4.)VF,(3<.&40.R34.)Vfc,(56.(4.&40.))R13.(57.$1.)))(4;.$1.(4<.$1.VR,VHIA,R2;.Vmo0,)(4=.$1.VR,VHIA,$4>.$4?.$50.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(52.(53.(3<.&40.R22.)(3<.&40.Vsp1,)Vgp,Vtp,R21.R20.R1?.R1>.R1=.(3<.&40.(2>.R23.))R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(3<.&40.R31.)Vfc,(56.(4.&40.))R29.(57.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros ENTRY STACK PRE Rq HQ HSTK. intros until t6. intros EBk TOK Hd HPRE RETr RETe CONT.
    destruct (tmp_member hk LBk mk v f SL _ _ _ ds d0 EBk TOK Hd) as (MD & DNS & MW & OX & _ & (DB1 & DB2) & HBK).
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    ddestruct (mpd_qpre hk LBk mk d0 HHk MD ltac:(intros O; exfalso; exact (DNS O))) as (Q1 & Q2 & Q3).
    assert (SCSk : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP SP1. lia. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { unfold mpi_query_stmtA in HQ.
      eapply HQ with (CS := hcs asegs R HIA hk) (LB := LBk) (dX := d0) (v := bv_unsigned a1v) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact MD | exact Q1 | exact MIk | exact HPRE | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk)
              | exact (hm_abase asegs R HIA hk LBk LF' mk HHk) | exact OX | exact Q2 | exact STb | exact SCSk | exact Q3 | reflexivity | (symmetry; apply Z_to_bv_bv_unsigned)
              | (left; clear - DB2 FBLO; lia)
              | (clear - ALO LOS; pose proof (alloc_ceiling_pos (L := arl_L R)); lia) | (clear - SLO1 NER NEEDR HSTK; lia) | (clear - SP1M; Z.div_mod_to_equations; lia)
              | match goal with |- ?g => idtac "Q-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_query_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & r & E & MU2 & WM2 & MI2 & ST2 & RR). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    eapply CONT; [exact (eb_scratch _ _ _ _ _ _ _ _ _ _ m2 lo EBk0 MU2 ltac:(clear; lia) WM2 MI2 ST2)| | exact RR].
    eapply (tmp_ok_own hk LBk mk m2 _ _ HHk TOK MU2 WM2 MIk MI2).
    - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1; lia| apply Forall_nil].
    - intros x Hx. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
      cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO; lia| exact I].
    all: match goal with |- ?g => idtac "Q-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 F64 FRSH"] Lemma eb_own : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pm2,P,(4.&40.)(5.(4.&8.))PWFr,(2.$9.)P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(1>.R2.R;.R3.)P,(1?.(8.$6.$6.)Lw,(8.$6.$6.)(14.(<.(=.VFB,+20.)(20.$6.$6.R1.))(<.(21.$6.$6.R1.)(=.VFB,+3?8.)))R3.)P,(22.$1.R=.R5.)P,(23.$1.R6.)P,(24.$1.R7.Vlo,Vsp1,)P,(1?.(8.$6.(2.$7.))Lac,(8.$6.(2.$7.))(25.R8.(20.$6.(2.$7.)R1.)(>.(?.(21.$6.(2.$7.)R1.))))R;.)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R13.R12.R9.R10.R?.R>.R=.R<.R;.R:.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE m2 WFr EBk MU HWF WM MI2 ST2 HCD.
    eapply (eb_munchF hk LBk mk v f SH SL CH T WE m2 WFr lo EBk); [| apply Z.le_refl| exact HWF| exact WM| exact MI2| exact ST2| exact HCD].
    intros x Hx. apply MU. apply outside_app in Hx. exact (proj1 Hx).
  Qed.

  (* [comment removed for export] *)
  Definition TAILV : Z := 13 * (GF_PHI + group_load_PHI) + GF_PHI + pk_set_group_PHI.
  Definition TAILF : Z := 13 * (GF_FR 0 + group_load_FRn 0) + GF_FR 0 + 21 + pk_set_group_FR.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L5558196365.200000:S3LEN4LEN0". (* [comment removed for export] *)
  #[using="LEN0"] Lemma tail_nonneg : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "(14.(<.=$76.)(14.(<.=$77.)(14.(<.$47.$76.)(14.(<.(=.+15.$49.)$77.)(14.(<.=(68.VLEN,))(14.(<.=(69.=))(<.=(71.+1.))))))))")
(* [comment removed for export] *).
  Proof.
    unfold TAILV, TAILF, pk_set_group_PHI, pk_set_group_FR, group_load_PHI, group_load_FRn, GF_PHI, GF_FR, MPI_RB_PHI, MPI_RB_FR, grow_PHI, calls_FR, fr_charge, AVOL_CALL.
    clear - LEN0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac ch_dj := clear; repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]; repeat split; lia|]); apply Forall_nil.


  Ltac inlist := cbn [In]; repeat (first [ left; reflexivity | right ]).

  #[using="Type"] Lemma w24_small : forall n, n < 5889 -> w24 n = 0.
  Proof. intros n H. unfold w24, win24. replace (5889 <=? n) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L2397676628.0 L29956516996.0L36705080954.2L61756540685.4L7669857218.4 00000100200900F00SSSS2d02N1S2d02d'2N'2N1S2d02d'2N'2N1". (* [comment removed for export] *)
  #[using="Type"] Lemma lset_cnt24 : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Pz,$6.Pd0,$26.PLBx,(2.$3.)Pr,$6.Pd',$26.P,(72.R5.R4.R3.R2.R1.)P,(<.(66.R5.)+1.)(14.(2?.$6.(3:.(36.R3.))=)(14.(<.(66.R3.)+1.)(14.(43.(44.(45.+2.+1?.))R4.)(<.R4.=))))")
(* [comment removed for export] *).
  Proof.
    (intros z d0 LBx r d' dd_H; ddestruct dd_H as ([(R0 & N' & _)|(RF & ->)] & _); intros N1); rewrite cnt24_mpd_blk.
    - split; [destruct (md_own d'); try reflexivity; apply w24_small; clear - N' N1; lia| split; [clear - N' N1; lia| subst r; clear; lia]].
    - split; [destruct (md_own d0); try reflexivity; apply w24_small; clear - N1; lia| split; [exact N1| subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L13679642378.8 L18814924225.1 L18884762225.10L20161731425.1 L2333536794.14 L27797056548.8 L31701524106.3 L37813904139.4 L38309573212.8 L49379278409.0 L53165354144.2 L55451675381.10L57866516861.10L59076925678.8 L59778638424.3 L66731276544.7 00000N00S01:01?02202S02_02k03K03L03T04=04f05G05S060S1R3HIA1h2sp3TOP3sp13SP15HTOP0S3sp1S1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2ac2B2S3sp1S1R3HIA5NEEDR1h2sp2lo3LOS3TOP3sp13SP14SLO13NER1a2HaS1R5NEEDR2lo3LOS3sp13ALO4SLO13NERS2sp3sp13SP1S3sp11a1n2HaS1R5NEEDR2sp2lo3sp13SP14SLO13NERSS2lo3sp1S1R5NEEDR2lo3LOS2FB3sp13ALO4SLO13NER4SBNDS1R5NEEDR2lo3LOS2FB3sp13ALO4SLO13NER4SBNDS1R5NEEDR2lo2FB3sp14FBLO4SLO13NERS2sp3sp13SP1S1R5NEEDR2lo3LOS3sp14SLO13NER". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO TOP HH0 SP1 F64 FRSH"] Lemma eb_slots : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D1 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PSH,(2.$7.)PSL,(2.$7.)PSL',(2.$7.)PCH,(2.(8.$6.(2.$7.)))PT,(2.$3.)PWE,(2.$9.)Pm2,P,(4.&40.)(5.(4.&8.))P,(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R<.R;.R:.R9.R8.R7.R6.R4.R3.R2.)P,(1>.(10.(8.$6.$6.)(11.$6.$6.(=.Vsp1,+8.)(=.Vsp1,+98.))(13.(8.$6.$6.)))R;.R2.)P,(22.$1.R<.R3.)P,(23.$1.R4.)P,(;.$1.R5.(=.Vsp1,+8.)R9.)P,(2?.$5;.(?.R:.)#90.)(:.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,R12.R11.R7.R?.R>.R=.R;.R:.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL SL' CH T WE m2 EBk MU WM MI2 SL2 NSL2.
    eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA h _ _ _ HH0) as HTOP0.
    pose proof (fresh_apart_relist_sg R HIA hk LB LBk LF mk FB 1024 FRSH HHk) as FRSHk.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hk) hk LBk LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & _ & _ & _ & _ & _ & _ & _ & SBND & _). change (1024 / 8) with 128 in SBND.
    assert (OWN : Forall own_iv [(sp1 + 8, sp1 + 152)]).
    { apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_nil]. }
    assert (DJ : forall a n, a + n <= sp1 + 8 \/ sp1 + 152 <= a -> disjoint_from [(sp1 + 8, sp1 + 152)] a n).
    { intros a n Ha. cbn [disjoint_from]. split; [clear - Ha; lia| exact I]. }
    unfold A_pk_ecparams_B.EB.
    split. { eapply (hm_munch asegs R HIA hk LBk LF' _ mk m2 HHk MU WM).
             apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite ETk. clear - Ha LOS SLO1 NER NEEDR TOP SP1. lia. }
    split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
    split; [dexists w0, w1, w2; eapply (rw_cells_transport asegs); [exact FHD| exact MU| exact WM| apply DJ; left; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FBLO SLO1 NER NEEDR; lia]|].
    split; [split; [eapply (rw_cells_transport asegs); [exact FSH| exact MU| exact WM| apply DJ; left; rewrite NSH'; clear - SBND ALO LOS SLO1 NER NEEDR; lia]| exact NSH']|].
    split; [eapply (rw_cells_transport asegs); [exact FSHR| exact MU| exact WM| apply DJ; left; cbn [cells_size csize Nat.add]; clear - SBND ALO LOS SLO1 NER NEEDR; lia]|].
    split; [eapply (rw_cells_transport asegs); [exact SAVE| exact MU| exact WM| apply DJ; right; clear - SP1; lia]|].
    split; [exact (conj SL2 NSL2)|].
    split; [eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM| apply DJ; left; clear; lia]|].
    split; [eapply stk_transport_disjoint; [exact SThi| exact MU| exact WM| apply DJ; right; clear; lia]|].
    split; [eapply stk_transport_disjoint; [exact STb| exact MU| exact WM| apply DJ; left; clear; lia]|].
    split; [exact MI2|].
    split. { eapply (presW_munch asegs R HIA hk LB LF _ _ _ m mk m2 _ PRES MU WM).
             - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
               eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS SLO1 NER NEEDR; lia| rewrite ESk; clear - HTOP0 TOP SP1; lia].
             - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
               apply (wcover_of_wlow R); [exact (hm_wlow asegs R HIA h _ _ _ HH0)| clear - ALO LOS SLO1 NER NEEDR; lia| clear - SP1; lia]. }
    split; [exact (ids_state_own hk LBk mk m2 _ HHk OWN IDSk MU WM)|].
    split. { rewrite Forall_forall in CHk |- *. intros ac Hac. ddestruct (CHk ac Hac) as (Hc & B1 & B2). split; [| exact (conj B1 B2)].
             eapply (rw_cells_transport asegs); [exact Hc| exact MU| exact WM| apply DJ; left; clear - B2 FBLO SLO1 NER NEEDR; lia]. }
    split; [exact EXTk| exact FRk].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis MCI : arl_memcmp_i R = 0x58704.
  Hypothesis SLOB : lo <= bv_unsigned sp - 336 - arl_need_bcmp R.
  Hypothesis NEEDB : 0 <= arl_need_bcmp R.

  (* [comment removed for export] *)
  Definition PRIME_FIELD_OID : list byte := Eval vm_compute in (match image_bytes asegs 0x265c0 7 with Some bs => bs | None => [] end).


  End Call.
End WalkEP.
