(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_ecp_point_free P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_ecp_grp_id_list P_ecp_mul_mod P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_D.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_defs A_pk_defs
     A_mpi_free A_mpi_lset A_mpi_bitlen A_mpi_cmp_mpi A_asn1_get_tag_stmt A_asn1_get_int_loops A_asn1_get_mpi A_oid A_oid_ec_grp
     A_ecp_group_init A_ecp_group_free A_ecp_point_free A_ecp_grp_id_list A_pk_ecparams_aux
     A_free_seq A_pk_ecc_set_group A_pk_ecc_set_pubkey A_ecp_grp_facts A_pk_tmp A_pk_ecparams_stmt A_pk_ecparams_A A_pk_ecparams_B A_pk_ecparams_C
     A_mpi_read_binary_stmt_c24 A_asn1_get_mpi_c24 A_pk_ecparams_D1.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_pk_ecparams_D2 () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.A.A_pk_ecparams_D1.SPINV"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.MPI_RB_PHI"; "OSSVerify.KrLib.A.A_pk_ecparams_D1.TAILV"; "OSSVerify.KrLib.A.A_pk_ecparams_stmt.pk_ecparams_PHI"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.MPI_RB_FR"; "OSSVerify.KrLib.A.A_pk_ecparams_D1.TAILF"; "OSSVerify.KrLib.A.A_pk_ecparams_stmt.pk_ecparams_FR"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "OSSVerify.KrLib.A.A_pk_ecparams_stmt.pk_use_ecparams_postA"; "OSSVerify.KrLib.A.A_ecp_defs.A_MT"; "OSSVerify.KrLib.A.A_ecp_defs.A_CA"; "OSSVerify.KrLib.A.A_ecp_defs.A_ONE"; "OSSVerify.KrLib.P.P_ecp_keypair_init.kp_init"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.A.A_mpi_stmtA.grow_PHI"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LNull"].



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
  Hypothesis SLO : lo <= bv_unsigned sp - 624 - arl_need_ecp R.
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
  Hypothesis SF5 : arl_setf5 R = 0x6adbc.
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

  Hypothesis HRB : mpi_read_binary_stmtA_c asegs R HIA A_MPI_READ_BINARY.
  Hypothesis HGM : asn1_get_mpi_stmtA_c asegs R HIA A_ASN1_GET_MPI A_MPI_READ_BINARY.
  Hypothesis BSNE : 0 < Z.of_nat (length bs).
  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis UWC0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis HGT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis MCI : arl_memcmp_i R = 0x58190.
  Hypothesis SLOB : lo <= bv_unsigned sp - 320 - arl_need_bcmp R.
  Hypothesis NEEDB : 0 <= arl_need_bcmp R.
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
  Local Notation eb_bytes := (A_pk_ecparams_D1.eb_bytes R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH BUF bs HBS0 CRB DSB DBI OBUF0).
  Local Notation eb_munchF := (A_pk_ecparams_D1.eb_munchF R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).
  Local Notation sp_mpi_step := (A_pk_ecparams_D1.sp_mpi_step R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO FB sp1 SP1 F64 FRSH).
  Local Notation SLP := (A_pk_ecparams_D1.SLP FB).
  Local Notation SPINV := (A_pk_ecparams_D1.SPINV R HIA IDONE IDS h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo FB sp1 LEN P).
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
  Local Notation buf_fresh_apart := (A_pk_ecparams_D1.buf_fresh_apart R HIA LB LF lo LOS BUF bs CRB BSNE).
  Local Notation sp_getmpi := (A_pk_ecparams_D1.sp_getmpi R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF P BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL HRB HGM BSNE).
  Local Notation sp_readbin := (A_pk_ecparams_D1.sp_readbin R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP TPV FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ BUD BUDF P BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL HRB BSNE).
  Local Notation eb_uwc := (A_pk_ecparams_D1.eb_uwc R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo d LOS SLO SPA HH0 FB sp1 SP1 F64 FRSH C INC D0 UWC0).
  Local Notation sp_lset := (A_pk_ecparams_D1.sp_lset R HIA IMG NEEDR HND IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP SPA TPV HH0 FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ INC BUD BUDF D0 HLSET UWC0).
  Local Notation sp_gettag := (A_pk_ecparams_D1.sp_gettag R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP HH0 FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ P BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL BSNE HGT).
  Local Notation sp_query := (A_pk_ecparams_D1.sp_query R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 PKA lo d LOS SLO TOP HH0 FB sp1 SP1 SP1M F64 FRSH info C LEN idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Local Notation eb_own := (A_pk_ecparams_D1.eb_own R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).
  Local Notation tail_nonneg := (A_pk_ecparams_D1.tail_nonneg LEN LEN0).
  Local Notation eb_slots := (A_pk_ecparams_D1.eb_slots R HIA IMG NEEDR IDONE IDS IDOK h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo LOS SLO TOP HH0 FB sp1 SP1 F64 FRSH).

  Ltac ch_dj := clear; repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]; repeat split; lia|]); apply Forall_nil.
  Ltac inlist := cbn [In]; repeat (first [ left; reflexivity | right ]).
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0350@C53807985733.309D16670306730.247D17209380499.247D31956866464.300D40016287967.247D40016287967.300D60175204683.300L12030387076.1  L12469921329.0  L14906048793.237L15195629121.1  L15374455067.303L1685717371.0   L17924243177.9  L1818808183.3   L18432251946.6  L18901988838.1  L18909959449.237L19561236329.1  L19711640196.1  L19767991565.1  L1986124813.1   L21516087713.9  L21866712442.1  L22252508346.1  L22409920380.296L22941438733.1  L24023900370.0  L24356290505.0  L25137631108.1  L28432818399.237L28948604668.296L29010569984.263L29022582655.2  L29252150116.1  L31573175913.9  L32713645262.289L33202183141.6  L35274486561.0  L35668120898.7  L35684885892.1  L35869826529.5  L35870121979.3  L36705801585.3  L36707279716.1  L39297207969.9  L39833374057.9  L42411609006.0  L4248698872.6   L43001578345.9  L44056310188.3  L46046848644.1  L46126591772.2  L46204432317.2  L46350850038.9  L46437661103.5  L46784238497.9  L4681653737.1   L47427904289.0  L47513520362.303L49379278409.0  L49738838761.1  L51163915460.6  L52220581018.289L52838613313.4  L53323719005.1  L54015471669.4  L54023799179.5  L54992078076.262L57885839492.1  L60098763854.3  L64224448909.5  L65105751913.9  L66151426447.10 L68697538081.9  L7283230113.9   L7462897247.3   L7738195705.2   L805459627.1    L9341288836.1   L9404489852.237 P22976122839.309P29008688568.248P29008688568.300P7750690063.248 P7750690063.300 Q10592318620.306Q10701806808.305Q11801279589.247Q12332606399.305Q1270901866.306 Q12820331109.303Q13400730472.269Q13779303417.303Q13919783118.303Q15221952244.303Q15224056021.244Q18668832038.305Q19089579269.303Q19401054440.244Q19639559579.305Q19682874911.305Q19828935533.305Q2037562293.304 Q20377295063.304Q20580512354.247Q20580512354.300Q20608450805.269Q24130586820.244Q25073716075.309Q25075822059.300Q28072352329.303Q29219344330.305Q30225219578.303Q30557275567.300Q31944295801.303Q32670200241.296Q33951481484.302Q34357517860.303Q35334539025.303Q3545121163.303 Q3551465399.303 Q36253051258.303Q39125883166.304Q39516934939.304Q40327015129.305Q41218494256.247Q41218494256.300Q41220736304.247Q41220736304.299Q42698228229.303Q4354927858.297 Q44298944140.298Q44298944140.304Q44301027056.309Q44708246993.306Q45437881016.306Q47228431932.309Q47409184484.247Q47411131620.247Q48117823211.247Q48117823211.300Q48119910507.309Q48228597444.244Q49698585326.246Q49698585326.298Q49933378966.247Q50721477213.301Q53697455321.301Q53705517746.303Q53881004917.244Q54087030033.299Q54088982289.300Q54389312920.306Q54481541664.303Q54967541497.248Q54967541497.300Q55003624584.303Q55256112523.304Q55809854879.305Q5596578838.309 Q56671730518.245Q57625797019.304Q57897686552.306Q58768111688.248Q58768111688.300Q58864946937.303Q59617553652.303Q59619599048.303Q60873713541.303Q61051420645.303Q63000015270.302Q63435846322.304Q6412966839.297 Q64228675114.308Q64228946346.309Q64268197229.303Q64814538957.306Q66901779611.304Q66942122546.298Q66942122546.304Q66954699982.248Q66954699982.300Q66956788302.309Q67854022709.303Q67892150791.304Q68379802528.296Q6912043753.304 Q6912046254.248 Q6912046254.300 Q7712614101.244 Q9077267670.305 Q9621591073.306 Q9735647057.306 Q9933143368.303 Q9947543794.297 Q9947771764.303 00000100201J02`04805N05O05S05T06W06[06\06]06a06l07A07E08H08L08P08T08X08\08`08d09g09k09l09m0:10;40<70<80<90<=0<A0=D0=Z0=[0>20>60>C0>L0>W0>[0>_0>c0>d0?90?=0?G0?K0?R0?X0@40@G0@K0@O0@P0B50B60B:0BQ0CT0Cb0Cf0D30DA0ED0EH0ER0Ec0Eg0F80F<0F@0FK0FL0FP0FT0GW0Hj0JX0LJ0N60O`0Pm0Pn0R?0SL0SM0TM0Ua0V]0V^0WZ0XV0XW0XX0Z20[?0[@0[A0[B0\O0\P0\Q0][0^W0_j0a;0a<0a=0b=0b>0b?0c;0d^0f10f20f30f40g40g50g60g70hH0iW0jh0l70m30mo0o010111D11E11F12]13n15?16n18[1:J1;F1<K1=P1=Q1>^1?k1?l1A61BE1CT1CU1E61FG1GV1HR1HS1I`1Ia1Jc1Jd1L11MB1NQ1NR1NS1NT1NU1OU1Q01Q11R31T61V?1V@1VA1WB1XC1YD1ZU1[d1]71]81]91^51_B1`S1ab1b^1ck1cl1cm1di1ee1faFFS2LF2sp3PKA2FB3sp13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stFS2FBFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBFSS2FBS2FB2d03XB1S3LEN1P1p3lnw3PB'3LNRS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS2FBS2FBS2FBS2FBS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBSSS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFFS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LB3LBk1K4C24k3LB22C2SS1R3HIA1h2sp2lo3TOP3HT0S2FBS1d1f3FB'3TF1S1d1f3FB'S2FB2d03XB3S2FBS2FBS2FBSS1R2FB3APS2d03XB13XB2S2FBS3LEN1v2VBS2FBS3LEN1PS1R2FBS3LEN1P1p3lnw3PB'3LNR2p23PB2S2LB1K2K43LB25C24k2S2FBS2FBSS1R2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSS2FBS2LB4C24H3LBk1K4C24k2K4S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS3LEN1v2VB3TV0S2FBS1d1f3FB'3TF0S3LEN1v2VB3TV1S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS1R2lo3LOSS3LEN1P1p3lnw3LNBS2FBS1r3RR22r02KR1q1HS2FBS2FBS1r3RR23RNZFS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4FBLO4SLO13NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184FBLO3NER3nbv4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184FBLO3NER3nbv4NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFFS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3NERS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stFFS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSL2HB5Ha_st5Hl_stS1R2LF2sp3PKA2lo2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFFS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFFFS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ALO4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ALO3NER3nbv4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_stFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183NER4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2F02HBFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stFFFFS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182F04NSH'3NSL2HBS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2bs2v12v22v32v42v52v62v73v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8stFFS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HBS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183nbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE"] Lemma stageN : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(9.&40.(:.VFB,+140.))(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R16.R15.R14.R13.)P,(;.(<.&40.R26.)(=.(:.VP,VLEN,)R27.))P,(;.R15.+4.)P,(;.(:.(:.R32.(>.VLEN,))$?.)(10.VLEN,))P,(;.(:.(:.R32.(11.=))$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R37.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R17.(9.&40.Vsp1,)Vgp,Vtp,R16.R15.R14.Vsp,(9.&40.Vsp1,)R13.R12.(9.&40.(:.VFB,+1=8.))R11.R10.R?.R>.R=.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))R8.R7.(9.&40.VFB,)R6.(9.&40.(:.VFB,+170.))R<.R;.R:.R9.)VF,(9.&40.+;00?<.)Vfc,(20.(4.&40.))R35.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. (intros dd_H; ddestruct dd_H as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k); intros LNB K4 VB FB').
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof (bv_unsigned_in_range 64 lnw) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 320, [C8 lnw]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])] _ _ EBk
                  ltac:(intros c Hc; right; exact Hc)) as EBr.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_intror (or_introl eq_refl))) as LCELL.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(FB + 288, FB + 296)] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (OWN1 : Forall own_iv [(FB + 288, FB + 296)]) by (apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    pose proof (eb_own hk LBk mk v f _ _ _ _ _ m1 [(FB + 288, FB + 296)] EBr MU ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) WM MIk STb ltac:(ch_dj)) as EB1r.
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB1r PCELL ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB1.
    assert (TOK1 : tmp_ok asegs m1 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk mk m1 _ _ HH0' TOK MU WM MI0' MIk OWN1).
      intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1; lia| exact I]. }
    (* [comment removed for export] *)
    do 3 zstep.
    replace (FB + 472) with (md_addr dN) by (rewrite EN; clear; lia).
    eapply (sp_getmpi hk LBk m1 v f _ _ (DS7 dN dP dA dB dX dY dZ) dN (p + bv_unsigned lnw) PEND 0xb011c);
      [exact EB1| exact TOK1| left; reflexivity| clear - PB' LNR; lia| clear - LNB; lia| clear; lia| rewrite EN; ch_dj
      | unfold C24_PK_USE_ECPARAMS, C24_ECP_GROUP_LOAD in C24H; clear - C24H C24k K4; lia| clear; lia| reflexivity| clear - VB TV0; lia| clear - FB' TF0; lia|].
    intros h2 LB2 m2 dN' r p2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB2 TOK2 EAD C2 PB2 RR2 ROK2.
    destruct (tmp_upd7 dN' dN dP dA dB dX dY dZ EN EP EA EB' EX EY EZ) as (UPD & _). rewrite (UPD ltac:(rewrite EAD; exact EN)) in EB2, TOK2. clear UPD.
    replace (md_addr dN) with (FB + 472) by (rewrite EN; clear; lia).
    assert (SI2 : SPINV h2 LB2 m2 (v + MPI_RB_PHI LEN) (f + MPI_RB_FR 0) dN' dP dA dB dX dY dZ p2 lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 (K + 1)).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [rewrite EAD; exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2 LNR LNB; lia| clear - C2 C24k; lia]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBr EB1r EB1 TOK1 PCELL LCELL OWN1.
    pose proof SI2 as (EBk & _).
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h2 LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h2) h2 _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h2 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h2) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { eapply (sp_errbac h2 LB2 m2 _ _ dN' dP dA dB dX dY dZ p2 lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 (K + 1) r);
        [exact SI2| | clear - VB TV0 TV1; lia| clear - FB' TF0 TF1; lia].
      assert (RNZ : r <> 0) by (intros ->; clear - KR; first [apply KR; reflexivity| (vm_compute in KR; congruence)]). clear - RR2 RNZ. lia. }
    assert (RZ : r = 0) by (clear - KR RR2; Z.div_mod_to_equations; lia). subst r. clear KR.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 3 zstep.
    replace (FB + 472) with (md_addr dN') by (rewrite EAD, EN; clear; lia).
    ddestruct SI2 as (EB2' & TOK2' & EN2 & _ & _ & _ & _ & _ & _ & PB2' & C24k2).
    eapply (sp_query A_MPI_BITLEN_Q _ _ _ (A_mpi_bitlen_spec AL IMG) ltac:(clear; lia) h2 LB2 m2 _ _ _ _ _ dN' 0xb012c);
      [exact EB2'| exact TOK2'| left; reflexivity| exact I| clear; lia| reflexivity|].
    intros m3 nbv z0 z1 z2 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB3 TOK3 RNB. cbv beta in RNB.
    replace (md_addr dN') with (FB + 472) by (rewrite EAD, EN; clear; lia).
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EB3 (or_intror (or_intror (or_intror (or_introl eq_refl))))) as REFC.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EB3 (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as GID.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EB3 (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as PBN.
    pose proof EB3 as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([(FB + 496, FB + 504); (SHB, SHB + 80)] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    assert (SCSk : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h2 LB _ LF m3 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h2) h2 _ LF m3 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h2 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h2) as CSOKk.
    pose proof (conj TOK3 (conj HHk (conj MIk (conj IDSk I)))) as BOX.
    unfold EP_SH_P in FSH. unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 9 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH6 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ddestruct BOX as (TOK0 & HHk0 & MIk0 & IDSk0 & _).
    assert (OWN : Forall own_iv [(FB + 496, FB + 504); (SHB, SHB + 80)]).
    { apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]]. }
    assert (EB6 : EB h2 LB2 m6 (v + MPI_RB_PHI LEN) (f + MPI_RB_FR 0) EP_SH_G
                    [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 (Z_to_bv 64 (FB + 320)); C8 (Z_to_bv 64 (FB + 472)); C8 (Z_to_bv 64 PKA);
                     C8 (Z_to_bv 64 (FB + 424)); C8 (Z_to_bv 64 (FB + 408)); C8 (Z_to_bv 64 (FB + 624)); C8 (Z_to_bv 64 (FB + 392)); C8 (Z_to_bv 64 (FB + 376)); C8 v16; C8 v17; C8 v18]
                    [(FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 (Z_to_bv 64 nbv)])] (tmp_blocks (DS7 dN' dP dA dB dX dY dZ)) W0).
    { unfold A_pk_ecparams_B.EB. split; [assumption|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH_G; cbn [repeat app]; exact FSH6| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [assumption|].
      split; [exact PRES|].
      split; [exact (ids_state_own h2 LB2 m3 m6 _ HHk0 OWN IDSk0 MU WM)|].
      split; [repeat (apply Forall_cons; [split; [first [exact REFC| exact GID| exact PBN]| cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]|]); apply Forall_nil|].
      split; [exact EXTk| exact FRk]. }
    assert (TOK6 : tmp_ok asegs m6 LB2 G 192 (DS7 dN' dP dA dB dX dY dZ)).
    { eapply (tmp_ok_own h2 LB2 m3 m6 _ _ HHk0 TOK0 MU WM MIk0 ltac:(assumption) OWN).
      intros d0 Hd. ddestruct TOK0 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2).
      assert (XB3 : md_addr d0 + 16 <= G + 120).
      { cbn [In] in Hd. decompose [or] Hd; try contradiction; subst d0; rewrite ?EN2, ?EP, ?EA, ?EB', ?EX, ?EY, ?EZ; clear; lia. }
      cbn [disjoint_from]. split; [clear - XB3; lia| split; [clear - XB1 XB2 APS; lia| exact I]]. }
    eapply (idsearch_walk h2 LB2 m6 _ _ dN' dP dA dB dX dY dZ jref gid gj' pb (Z_to_bv 64 nbv));
      [exact EB6| exact TOK6| exact EN2| exact EP| exact EA| exact EB'| exact EX| exact EY| exact EZ| clear - C24k2 K4; lia
      | unfold TAILV in VB; clear - VB; lia| unfold TAILF in FB'; clear - FB'; lia].
    all: match goal with |- ?g => idtac "N-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0110@L10470257411.298L12638774292.8  L14906048793.244L15451865249.10 L18457785511.0  L22717520555.1  L22767655841.10 L22966327585.10 L23160805025.10 L25141141322.3  L25142957688.7  L29010569984.273L29230279457.0  L29904362273.0  L30270422177.10 L30656207425.1  L31165787832.246L31166233296.243L34069150392.245L34204454049.10 L34541613483.247L34543839983.245L35668120898.7  L35869924834.6  L37483799694.8  L41203500611.3  L41799007210.2  L42987192166.257L4802675888.5   L48428923041.10 L48962193527.6  L48992829857.10 L49379278409.0  L50671553195.1  L51390623401.0  L52173625249.10 L52663760934.6  L52740280353.10 L54024012424.7  L54101625409.1  L54992078076.298L5558772641.10  L56103495585.10 L60098763854.3  L61707632420.11 L61900301956.0  L6668731487.5   Q13400730472.305Q15930096381.254Q20608450805.305Q22101451528.256Q22103975861.254Q24137124155.251Q25105683634.251Q25582878921.254Q25583013718.251Q25585075316.256Q39502765953.256Q39504763708.254Q4113544236.254 Q43608497032.251Q53622987766.254Q54487414257.256Q58126184374.254Q7706109738.251 00000100O01R01V01W01[01_01c01g02102C02D02E02F02J02N03V04^06X06\08V0:P0:g0;80;V0;_0;g0=00=A0=E0=[0=_0=`0=d0=e0=i0>;0>?0>U0>Y0?^0?b0?f0@00@W0@X0@i0B=0C90DC0DD0DE0EA0FP0G_0Hn0J=0J>0J?0K@0L<0M:0NI0OX0PTFS2LB3LBk1K4C24k3LB23dY'2C23CZ2S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBSS2FBS2FBS2FBS2FBS3LEN1v2VBS3LEN1v2VB3TV13RB0FSSS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2bs1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2PRS2LF2sp3PKA2FB3sp13LFB2bs1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2PRS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13LFB3LEN3NZP1P3BUF2bs2PL1p2v12v22v32v42v52v62v73v163v173v183PLT4NSH'3NSL2F04FBLO4SP1R3NERS2FBS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13LFB3LEN3NZP1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3PB'2F04FBLO4SP1R3NERS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13LFB3LEN3NZP1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3PB'2F04FBLO4SP1R3NERS1R3HIA1h2sp2lo3TOP3HT0S1d1f3FB'3TF13RF0S2LB1K3LB24C24k3LB33dZ'2C33CZ3S1d1f3FB'S2b03B0RS2LF2sp3PKA2FB3sp13LFB3BUF2bs1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1d1f3FB'3TF03RF0S2FBS3LEN1v2VB3TV03RB03GP0S2FBSS2FBSS2FBS3LEN1v2VB3TV03RB0S2FBS3LEN1v2VB3TV13RB03GP0S2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v181r4NSH'3NSLS2FBS2FBS1R2lo3LOSS3LEN1P3BUF2bs4BUF03B472BP2PL1p3PLT3PB'SS1d1f3FB'3TF03RF0S1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2PL1p2v12v22v32v42v52v62v73v163v173v183PLT4NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3PB'S2LF3PKA2FB3LFB3LEN1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3PB'S2LF3PKA2FB3LFB3LEN1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3PB'FFS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2PRS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2PL1p2v12v22v32v42v52v62v73v163v173v183PLT4NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2PL1p2v12v22v32v42v52v62v73v163v173v183PLT4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0"] Lemma stageYZ : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(9.&40.(:.VFB,+140.))(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R17.R16.R15.R14.)P,(;.(:.R28.+1.)(:.VP,VLEN,))P,(;.(<.&40.R28.)(=.(:.VP,VLEN,)R29.))P,(;.R17.+4.)P,(;.(22.R2=.)+1.)P,(;.(22.R2=.)+1.)P,(;.(:.(:.(:.R36.(23.+2.(24.+1.)))(>.VLEN,))$?.)(10.VLEN,))P,(;.(:.(:.(:.R36.+6.)(11.=))$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3;.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R1;.(9.&40.Vsp1,)Vgp,Vtp,R1:.R19.R18.Vsp,(9.&40.Vsp1,)R17.R16.R15.R14.R13.R12.R11.R10.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))R;.R:.(9.&40.VFB,)R9.(9.&40.(:.VFB,+170.))R?.R>.R=.R<.)VF,(9.&40.+;00;8.)Vfc,(20.(4.&40.))R39.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI PLT LNB K4 NY NZ VB FB'.
    dpose SI as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EBk) as (HBSk & OBUFk & CRBk).
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as PCELL.
    pose proof EBk as EBsave.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    assert (PR : 0 < p /\ p + 1 <= 2^63) by (clear - BUF0 BP PB' PLT PL B47; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    shadow_chk OBUFk p 1.
    (* [comment removed for export] *)
    get_byte bs (p - BUF) b0 NB0.
    read_at HBSk NB0 (p - BUF) RD0. zstep. clear RD0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (bv_unsigned_in_range 8 b0) as B0R. change (bv_modulus 8) with 256 in B0R.
    replace (FB + 440) with (md_addr dY) by (rewrite EY; clear; lia).
    eapply (sp_lset hk LBk mk v f _ _ (DS7 dN dP dA dB dX dY dZ) dY (bv_unsigned b0 + -2) 0xb00dc);
      [exact EBsave| exact TOK| inlist| clear - B0R; lia| rewrite EY; ch_dj| clear; lia| reflexivity| clear - VB TV0 RB0 GP0; lia| clear - FB' TF0 RF0; lia|].
    intros h2 LB2 m2 dY' r y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB2 TOK2 EAD C2 RL2.
    destruct (lset_cnt24 _ _ _ _ _ RL2 NY) as (CZ2 & NY' & RR2).
    ddestruct (tmp_upd7 dY' dN dP dA dB dX dY dZ EN EP EA EB' EX EY EZ) as (_ & _ & _ & _ & _ & UPD & _). rewrite (UPD ltac:(rewrite EAD; exact EY)) in EB2, TOK2. clear UPD.
    replace (md_addr dY) with (FB + 440) by (rewrite EY; clear; lia).
    assert (SI2 : SPINV h2 LB2 m2 (v + grow_PHI 1) (f + 3) dN dP dA dB dX dY' dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [rewrite EAD; exact EY|]. split; [exact EZ|].
      split; [exact PB'| clear - C2 CZ2 C24k; lia]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave PCELL HBSk OBUFk CRBk TOK C24k SI.
    dpose SI2 as (EBk & TOK & _ & _ & _ & _ & _ & EY2 & _ & _ & C24k). pose proof EBk as EBsave.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h2 LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h2) h2 _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h2 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h2) as CSOKk.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KR; zify_cond KR.
    { eapply (sp_err94c h2 LB2 m2 _ _ dN dP dA dB dX dY' dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K (-15616));
        [exact SI2| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (FB + 456) with (md_addr dZ) by (rewrite EZ; clear; lia).
    eapply (sp_lset h2 LB2 m2 _ _ _ _ (DS7 dN dP dA dB dX dY' dZ) dZ 1 0xb00f4);
      [exact EBsave| exact TOK| inlist| clear; lia| rewrite EZ; ch_dj| clear; lia| reflexivity| clear - VB TV0 RB0 GP0; lia| clear - FB' TF0 RF0; lia|].
    intros h3 LB3 m3 dZ' r3 z0 z1 z2 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB3 TOK3 EAD3 C3 RL3.
    destruct (lset_cnt24 _ _ _ _ _ RL3 NZ) as (CZ3 & NZ' & RR3).
    ddestruct (tmp_upd7 dZ' dN dP dA dB dX dY' dZ EN EP EA EB' EX EY2 EZ) as (_ & _ & _ & _ & _ & _ & UPD). rewrite (UPD ltac:(rewrite EAD3; exact EZ)) in EB3, TOK3. clear UPD.
    replace (md_addr dZ) with (FB + 456) by (rewrite EZ; clear; lia).
    assert (SI3 : SPINV h3 LB3 m3 (v + grow_PHI 1 + grow_PHI 1) (f + 3 + 3) dN dP dA dB dX dY' dZ' p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB3|]. split; [exact TOK3|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY2|]. split; [rewrite EAD3; exact EZ|].
      split; [exact PB'| clear - C3 CZ3 C24k; lia]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK C24k SI2.
    pose proof SI3 as (EBk & _).
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    assert (SCSk : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h3 LB _ LF m3 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 _ LF m3 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h3 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h3) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KR3; zify_cond KR3.
    { eapply (sp_err h3 LB3 m3 _ _ dN dP dA dB dX dY' dZ' p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ _ v16 v17 v18 K (-15616));
        [exact SI3| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    eapply (stageN h3 LB3 m3 _ _ dN dP dA dB dX dY' dZ' p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 K);
      [exact SI3| exact LNB| exact K4| clear - VB; lia| clear - FB'; lia].
    all: match goal with |- ?g => idtac "YZ-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01o0@L10739142159.2  L1107923688.291 L1108297344.288 L11511961495.8  L12386406295.6  L12782871409.10 L14334923850.290L14492240433.331L14906048793.264L14906048793.289L14906048793.311L14987706775.8  L15653086487.8  L16908924412.294L17075157494.302L18909959449.264L18909959449.294L18909959449.311L21876836729.2  L23116160671.5  L25141141322.3  L29010569984.261L29432667347.5  L30080938931.14 L32930889387.1  L34259272700.264L34259272700.311L34613667750.1  L35668120898.7  L35869924834.6  L36607162391.8  L37118870096.3  L38235734261.1  L38244991729.10 L38408712019.4  L39723389345.0  L40224675374.4  L41203500611.3  L42851534655.7  L44011663895.8  L44817448137.0  L45703525153.0  L46126591772.2  L46350850038.6  L4713006577.10  L47733298015.6  L48932718241.0  L49379278409.0  L49629343297.1  L50545063073.0  L51161687237.6  L51390623401.0  L51543886882.6  L5196155000.7   L52478885617.10 L52838367809.6  L54015504437.5  L54024012424.7  L54992078076.281L54992078076.311L55878914281.3  L56407690993.10 L57201169206.7  L58227785239.8  L58711294999.8  L59735358056.1  L60098763854.3  L61900301956.0  L63522661617.10 L66140579321.11 L66151426447.10 L66151427842.16 L67019580928.293L7293583127.8   L7462897247.3   L8465593249.290 L8467818725.292 L8848476737.1   L9080220944.4   L9404489852.238 L9404489852.264 L9404489852.294 L9404489852.311 Q13400612873.318Q13400730472.288Q1345456905.271 Q1345456905.318 Q15015151771.301Q15224234932.271Q15224234932.318Q15226282298.301Q15930096381.299Q19401054440.245Q19401233289.271Q19401233289.318Q19403280647.301Q20608450805.288Q20608699284.318Q24082542268.299Q24130372517.271Q24130372517.318Q24137124155.296Q2977307222.299 Q39035392148.271Q39035392148.318Q43608497032.296Q43709244743.299Q43710980602.301Q44241777630.301Q44243843324.296Q44243973987.299Q45989860231.301Q48222435115.301Q48228611493.271Q48228611493.318Q53878778522.301Q53880891412.271Q53880891412.318Q53881004917.245Q5868906982.299 Q66045133256.296Q67304708122.301Q7706109738.296 Q7712730548.271 Q7712730548.318 Q8818455171.301 Q8820127294.299 00000701@02I02M02f02j05805906<07?08E08I08M09P0:Z0;]0<`0=f0=l0>>0>H0>I0>Y0?=0?A0@D0AJ0AN0Ae0B60B:0BF0BJ0BN0B]0B^0Bl0C50CK0CO0CP0CQ0CX0Cl0D00DG0DH0DI0DM0DN0Df0Dg0E80EN0ER0Eh0F90FO0GR0HX0Hd0Hh0IB0IF0IJ0IN0IX0IY0I]0JI0JZ0K<0L?0LC0LN0NO0PP0PT0Pc0Qf0Ri0Sl0U20VI0W]0Y10ZH0[d0\`0]_0^[0_W0a10bE0c\0e00f:0gG0hc0i_0j^0kZ0l\0mf0o30oo10010111G12]14315G16C17?18>19H1:R1;_1<i1=h1?D1@N1AJ1BF1CE1CF1CGS2FB2F0S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182p24NSH'3NSL2PRS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182p24NSH'3NSL2PRS2FBS1R5NEEDR2lo3sp14SLO13NERS2FBS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3LEN3NZP1P3BUF2bs2PL2v12v22v32v42v52v62v73v163v173v182F02F84FBLO4SP1R3NER2p22L24LB2'3LNR4NSH'3NSL3LNZFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB3BUF2bs2v12v22v32v42v52v62v73v163v173v182p24NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1K2K3S3LEN1P2p22L24LB2'S3LEN1v2VBFS1R2lo3LOS3ALO1HS3LEN1P3BUF2bs4BUF03B472BP2PL2p23PB3S2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS1R3HIA1h2sp2lo3TOP3HT0S1d1f3FB'3TF13RF0S2FBS2lo2FB4FBLOS2loS2FBS2sp2lo3sp13SP1SS3LEN1P2p23PB3S1d1f3FB'S3LEN1v2VB3TV13RB03GP0S2FBSSS3LEN1PS3LEN1P1p3PB'2p23PB2S2FBS2LB3LBk1K5C24k33LB52C5SSS2FBSS2LB4C24H3LBk1K2K35C24k3SS1d1f3FB'3TF13RF0S2lo2FB3sp14FBLO1x3XB2S2FBS3LEN1v2VB3TV03RB03GP0S1d1f3FB'3TF03RF0S3LEN1v2VB3TV13RB03GP0S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2L23LNR3LNZS2FBS3LEN1P2p22L24LB2'3LNR3LNZS2FBS2FBS2FBS1R2lo3LOSSS2FBS1R5NEEDR2lo3LOS2FB3sp12F13ALO4SP1R4SLO13NERS1r3RR22r02KR1q1HS2FB2r02F81q1r1H2H02q02H43sp14SP1MS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS1r3RR23RNZS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13LFB3LEN3NZP1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v183PB'2F04FBLO4SP1R3NER2p23PG24NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13LFB3LEN3NZP1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v183PB'2F04FBLO4SP1R3NER2p23PG24NSH'3NSLS2FBS2sp2lo3sp13SP1S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2PL2v12v22v32v42v52v62v73v163v173v182p22L24LB2'3LNR4NSH'3NSL3LNZS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3NERS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2PL2v12v22v32v42v52v62v73v163v173v182p22L24LB2'3LNR4NSH'3NSL3LNZS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p24NSH'3NSL2PRS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFFS2LF3PKA2FB3LFB3LEN1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v183PB'2p23PG24NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v183PB'2p23PG24NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2BP1p2v12v22v32v42v52v62v73v163v173v183PB'2p23PG24NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p24NSH'3NSLS2LF3PKA2FB3LFB3LEN1P3BUF2bs2PL2v12v22v32v42v52v62v73v163v173v182p22L24LB2'3LNR4NSH'3NSL3LNZS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2dP2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFF". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0 HGT"] Lemma stagePT : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(9.&40.(:.VFB,+140.))(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R17.R16.R15.R14.)P,(;.R15.+3.)P,(25.$26.(27.R2<.)$28.)P,(;.(22.R2<.)+1.)P,(;.(22.R2<.)+1.)P,(;.(:.(:.(:.R35.(23.+2.(>.VLEN,)))(23.+2.(24.+1.)))$?.)(10.VLEN,))P,(;.(:.(:.(:.R35.(23.+2.(11.=)))+6.)$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3:.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R1:.(9.&40.Vsp1,)Vgp,Vtp,R19.R18.R17.Vsp,(9.&40.Vsp1,)R16.R15.R14.R13.R12.R11.R10.R?.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))R:.R9.(9.&40.VFB,)R8.(9.&40.(:.VFB,+170.))R>.R=.R<.R;.)VF,(9.&40.+:??;0.)Vfc,(20.(4.&40.))R38.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI K3 XNULL NY NZ VB FB'.
    dpose SI as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof EBk as EBsave.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 5 zstep.
    eapply (sp_gettag hk LBk mk v f _ _ (DS7 dN dP dA dB dX dY dZ) p PEND 4 0xaffc4 lnw);
      [exact EBsave| exact TOK| exact (proj1 PB')| exact (proj2 PB')| clear; lia| ch_dj| clear; lia| reflexivity|].
    intros m2 r p2 L2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB2 TOK2 PB2 RR2 ROK2.
    assert (SI2 : SPINV hk LBk m2 v f dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2; lia| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI.
    dpose SI2 as (EBk & TOK & _). pose proof EBk as EBsave.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { eapply (sp_errbac hk LBk m2 _ _ dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K r);
        [exact SI2| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      assert (RNZ : r <> 0) by (intros ->; clear - KR; first [apply KR; reflexivity| (vm_compute in KR; congruence)]). clear - RR2 RNZ. lia. }
    assert (RZ : r = 0) by (clear - KR RR2; Z.div_mod_to_equations; lia). subst r. clear KR. destruct (ROK2 eq_refl) as (PG2 & LB2'). clear ROK2.
    pose proof (bv_unsigned_in_range 64 L2) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 6 zstep.
    destruct (tmp_member hk LBk m2 v f _ _ _ _ _ dP EBsave TOK ltac:(inlist)) as (MDP & DNSP & _ & OXP & _ & _ & HBKP).
    destruct (tmp_member hk LBk m2 v f _ _ _ _ _ dX EBsave TOK ltac:(inlist)) as (MDX & _ & _ & OXX & _ & _ & _).
    ddestruct (mpd_qpre hk LBk m2 dP HHk MDP ltac:(intros O; exfalso; exact (DNSP O))) as (QP1 & QP2 & QP3).
    assert (CGX : rw_cells asegs m2 (G + 56) (mpi_cells 0 (Z_to_bv 64 (md_sg dX)) (md_n dX) (md_pad dX))).
    { pose proof MDX as [(CX & _ & _ & _ & _ & OW) _]. rewrite XNULL in OW. destruct OW as [P0 _]. rewrite P0, EX in CX. exact CX. }
    assert (OGX : aobj asegs AL (hcs asegs R HIA hk) m2 (G + 56) 8) by (eapply aobj_sub; [exact OXX| rewrite EX; clear; lia| rewrite EX; clear; lia]).
    assert (OGP : aobj asegs AL (hcs asegs R HIA hk) m2 (G + 8) 16) by (rewrite <- EP; exact OXP).
    assert (SCS1 : crange (hcs asegs R HIA hk) lo (sp1 - lo)).
    { eapply crange_sub; [exact SCSk| clear; lia| clear - SP1; lia]. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof (A_ecp_point_read_unset AL IMG) as SPU. unfold ecp_point_read_unset_stmtA in SPU.
      eapply SPU with (CS := hcs asegs R HIA hk) (LB := LBk) (G := G) (Q := FB + 424) (B := p2) (LEN := bv_unsigned L2) (lo := lo) (dP := dP);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact MDP | exact EP | exact QP1 | exact CGX | exact MIk | exact LNR | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk)
              | exact (hm_abase asegs R HIA hk LBk LF' m2 HHk) | exact QP2 | exact STb | exact SCS1 | exact QP3 | reflexivity | (symmetry; apply Z_to_bv_bv_unsigned)
              | exact OGX | exact OGP
              | lazymatch goal with
                | |- _ mod 8 = 0 => clear - F8; Z.div_mod_to_equations; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < _ => clear - F0; lia
                | |- 0 <= lo => clear - ALO LOS; pose proof (alloc_ceiling_pos (L := arl_L R)); lia
                | |- _ <= 2^64 => clear - F1 ALO LOS SLO1 SP1R NER NEEDR; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ \/ _ => left; clear - FBLO; lia
                end
              | match goal with |- ?g => idtac "PRU-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold pure_ret_postA in PO.
    ddestruct PO as (z0 & z1 & z2 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & E & MU3 & WM3 & MI3 & ST3). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU3, ST3 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xaffe0)) with (Z_to_bv 64 0xaffe0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (eb_scratch _ _ _ _ _ _ _ _ _ _ m3 lo EBsave MU3 ltac:(clear; lia) WM3 MI3 ST3) as EB3.
    assert (TOK3 : tmp_ok asegs m3 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { eapply (tmp_ok_own hk LBk m2 m3 _ _ HHk TOK MU3 WM3 MIk MI3).
      - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1; lia| apply Forall_nil].
      - intros x Hx. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
        cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO; lia| exact I]. }
    assert (SI3 : SPINV hk LBk m3 v f dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { ddestruct SI2 as (_ & _ & REST). exact (conj EB3 (conj TOK3 REST)). }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI2 PCELL LCELL MDP MDX OXP OXX OGX OGP QP1 QP2 QP3 CGX SCS1 MU3 WM3 EB2 TOK2.
    dpose SI3 as (EBk & TOK & _). pose proof EBk as EBsave.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m3 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m3 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    zstep. zstep.
    unfold ECP_BAD_INPUT_DATA_U, ECP_FEATURE_UNAVAILABLE_U.
    destruct (Z.eqb_spec (bv_unsigned L2) 0) as [LZ|LNZ]; fold_lit_if.
    { (* [comment removed for export] *)
      do 3 zstep. fold_lit_if. do 3 zstep.
      eapply (sp_err94c hk LBk m3 _ _ dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K (-15616));
        [exact SI3| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    (* [comment removed for export] *)
    do 3 zstep. fold_lit_if.
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EBsave) as (HBSk & OBUFk & CRBk).
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    ddestruct SI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PB3 & C24k3).
    assert (PR : 0 < p2 /\ p2 + 1 <= 2^63) by (clear - BUF0 BP PB3 LB2' LNZ LNR PL B47; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    shadow_chk OBUFk p2 1.
    (* [comment removed for export] *)
    get_byte bs (p2 - BUF) b0 NB0.
    read_at HBSk NB0 (p2 - BUF) RD0. zstep. clear RD0.
    do 5 zstep. if_cases KB; zify_cond KB.
    { eapply (sp_err94c hk LBk m3 _ _ dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K (-15616));
        [split; [exact EBsave| split; [exact TOK| split; [exact EN| split; [exact EP| split; [exact EA| split; [exact EB'| split; [exact EX| split; [exact EY| split; [exact EZ| split; [exact PB3| exact C24k3]]]]]]]]]]
        | clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    (* [comment removed for export] *)
    do 4 zstep.
    replace (FB + 376) with (md_addr dP) by (rewrite EP; clear; lia).
    eapply (sp_query A_MPI_SIZE_Q _ _ _ (A_mpi_size_spec AL IMG) ltac:(clear; lia) hk LBk m3 _ _ _ _ _ dP 0xb0030);
      [exact EBsave| exact TOK| inlist| exact I| clear; lia| reflexivity|].
    intros m4 szv q0 q1 q2 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 EB4 TOK4 RSZ. cbv beta in RSZ.
    assert (SI4 : SPINV hk LBk m4 v f dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB4|]. split; [exact TOK4|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|]. split; [exact PB3| exact C24k3]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK PCELL LCELL HBSk OBUFk CRBk.
    dpose SI4 as (EBk & TOK & _). pose proof EBk as EBsave.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m4 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m4 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 3 zstep. if_cases KS.
    { eapply (sp_err hk LBk m4 _ _ dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ _ v16 v17 v18 K (-15616));
        [exact SI4| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    clear KS.
    (* [comment removed for export] *)
    do 7 zstep.
    replace (FB + 424) with (md_addr dX) by (rewrite EX; clear; lia).
    eapply (sp_readbin hk LBk m4 v f _ _ (DS7 dN dP dA dB dX dY dZ) dX (p2 + 1) (bv_unsigned L2 + -1) 0xb0058);
      [exact EBsave| exact TOK| inlist| clear - PB3; lia| clear - LNZ LNR; lia| clear - LB2'; lia| rewrite EX; ch_dj
      | unfold C24_PK_USE_ECPARAMS, C24_ECP_GROUP_LOAD in C24H; clear - C24H C24k3 K3; lia| clear; lia| reflexivity| clear - VB TV0 RB0 GP0; lia| clear - FB' TF0 RF0; lia|].
    intros h5 LB5 m5 dX' r5 u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 EB5 TOK5 EAD5 C5 RR5 ROK5.
    ddestruct (tmp_upd7 dX' dN dP dA dB dX dY dZ EN EP EA EB' EX EY EZ) as (_ & _ & _ & _ & UPD & _). rewrite (UPD ltac:(rewrite EAD5; exact EX)) in EB5, TOK5. clear UPD.
    replace (md_addr dX) with (FB + 424) by (rewrite EX; clear; lia).
    assert (SI5 : SPINV h5 LB5 m5 (v + MPI_RB_PHI LEN) (f + MPI_RB_FR 0) dN dP dA dB dX' dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 (K + 1)).
    { split; [exact EB5|]. split; [exact TOK5|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [rewrite EAD5; exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact PB3| clear - C5 C24k3; lia]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK PCELL LCELL SI4.
    pose proof SI5 as (EBk & _).
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    assert (SCSk : crange (hcs asegs R HIA h5) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h5 LB _ LF m5 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h5) h5 _ LF m5 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h5 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h5) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR5; zify_cond KR5.
    - assert (RZ5 : r5 = 0) by (destruct RR5 as [-> | ->]; [reflexivity| exfalso; clear - KR5; vm_compute in KR5; congruence]).
      eapply (stageYZ h5 LB5 m5 _ _ dN dP dA dB dX' dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 (K + 1));
        [exact SI5| clear - LB2' LNZ LNR; lia| exact LB2'| clear - K3; lia| exact NY| exact NZ| clear - VB; lia| clear - FB'; lia].
    - (* [comment removed for export] *)
      do 3 zstep.
      eapply (sp_err94c h5 LB5 m5 _ _ dN dP dA dB dX' dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 (K + 1) (-15616));
        [exact SI5| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
    all: match goal with |- ?g => idtac "PT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L1229126065.241 L14906048793.241L16259683914.13 L19349569929.0  L31165788229.241L35668120898.7  L42851534655.7  L44768470194.4  L46369226564.0  L49379278409.0  L51543886882.6  L60098763854.3  Q24135026976.248Q7708206897.248 00001<02?02m02n04:04Q04g05005105205C05M06I07ES2LF2sp3PKA2FB3sp13LFB2bs1p2v12v22v32v42v52v62v73v163v173v182EC4NSH'3NSL3PRGS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS3LEN1P3BUF2bs4BUF03B472BP2PL1p2EC3ECL3ECB3PB'SS2LF2sp3PKA2FB3sp13LFB2bs1p2v12v22v32v42v52v62v73v163v173v182EC4NSH'3NSL3PRGS1R3HIA1h2sp2lo3TOP3HT0S3LEN1v2VB3TV13RB03GP0S1p2EC2KESSS1d1f3FB'3TF13RF0S1R2lo3LOSS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0 HGT"] Lemma seed_join : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.PEC,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(9.&40.(:.VFB,+140.))(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R17.R16.R15.R14.)P,(;.VP,R14.)P,(;.R15.(:.VP,VLEN,))P,(;.R17.+3.)P,(25.$26.(27.R2>.)$28.)P,(;.(22.R2>.)+1.)P,(;.(22.R2>.)+1.)P,(;.(:.(:.(:.R37.(23.+2.(>.VLEN,)))(23.+2.(24.+1.)))$?.)(10.VLEN,))P,(;.(:.(:.(:.R37.(23.+2.(11.=)))+6.)$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3<.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R1;.(9.&40.Vsp1,)Vgp,Vtp,R1:.R19.R18.Vsp,(9.&40.Vsp1,)R17.R16.R15.R14.R13.R12.R11.R10.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))(9.&40.R1<.)R;.(9.&40.VFB,)R:.(9.&40.(:.VFB,+170.))R?.R>.R=.R<.)VF,(9.&40.+:??:8.)Vfc,(20.(4.&40.))R3:.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI ECL ECB K3 XNULL NY NZ VB FB'.
    dpose SI as (EBk & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBk (or_introl eq_refl)) as PCELL.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    assert (PRG : 0 <= p < 2^63 /\ 0 <= EC < 2^63) by (clear - BUF0 BP PB' PL B47 ECB ECL; lia).
    (* [comment removed for export] *)
    zstep. zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *)
      do 3 zstep.
      eapply (sp_err94c hk LBk mk _ _ dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K (-15718));
        [exact SI| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    assert (PE : p = EC) by (clear - KE PRG; lia). subst p.
    eapply (stagePT hk LBk mk v f dN dP dA dB dX dY dZ EC lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 K);
      [exact SI| exact K3| exact XNULL| exact NY| exact NZ| exact VB| exact FB'].
    all: match goal with |- ?g => idtac "JOIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01T0@D16670306730.254D16670306730.279D17209380499.254D17209380499.279D40016287967.254D40016287967.279L11511961495.8  L12469921329.0  L14906048793.244L14906048793.269L14987706775.8  L15653086487.8  L16342831409.11 L16357579057.9  L1685717371.0   L17090287777.0  L17923741369.9  L17924243177.9  L1818808183.3   L18432251946.6  L18901988838.1  L18909959449.244L18909959449.269L19767991565.1  L21866712442.1  L22252508346.1  L22302152298.13 L23380989714.9  L28432818399.244L28432818399.269L29010569984.265L29022582655.2  L29252150116.1  L31572674105.9  L31573175913.9  L35668120898.7  L36607162391.8  L39833374057.9  L39833937209.9  L43001097017.9  L43001578345.9  L44011663895.8  L46350850038.10 L49379278409.0  L53323719005.1  L58227785239.8  L58711294999.8  L59612558537.4  L60098763854.3  L65105184569.9  L65105751913.9  L66151426447.10 L7293583127.8   L7738195705.2   L9404489852.244 L9404489852.269 P29008688568.255P29008688568.280P7750690063.255 P7750690063.280 Q11801279589.254Q11801279589.279Q15224056021.251Q15224056021.276Q19401054440.251Q19401054440.276Q20580512354.254Q20580512354.279Q24130586820.251Q24130586820.276Q41218494256.254Q41218494256.279Q41220736304.254Q41220736304.279Q47409184484.254Q47409184484.279Q47411131620.254Q47411131620.279Q48117823211.254Q48117823211.279Q48228597444.251Q48228597444.276Q49698585326.253Q49698585326.278Q49933378966.254Q49933378966.279Q53881004917.251Q53881004917.276Q54967541497.255Q54967541497.280Q56671730518.252Q56671730518.277Q58768111688.255Q58768111688.280Q66954699982.255Q66954699982.280Q6912046254.255 Q6912046254.280 Q7712614101.251 Q7712614101.276 00000100201J02b04:05R05V05W06Z07]07a07e08D08c08d08e08i08m09809M09Q0:T0;W0;[0;_0;c0<S0=30>60?90?:0?;0??0?C0?G0?^0?b0?f0?j0?n0@20@60@Y0@Z0@^0@b0@f0A40A>0AB0AF0AW0A[0A\0B_0Cb0EV0GJ0I60Jb0L30MD0N@0O<0PP0Qd0Qe0Qf0Rb0S^0To0V@0WQ0Xb0Z30[D0\U0]f0_U0aD0b@0c<0dA0eF0eG0eH0fR0g\0hm0j>0k@0lB0mS0nd10511F12W13h14d15`FFS2LF2sp3PKA2FB3sp13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2FBFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS2FBS3LEN1P1p3lnw2EC3PB'3LNR2p23PB2S3LEN1P1p3lnw2EC3PB'3LNR2p23PB2SSS2FBS2FBS2FB2d03XB1S3LEN1P1p3lnw3PB'3LNRS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS2FBS2FBS3LEN1P1p3lnw2EC3ECB3PB'3LNR2p22L23PB24LB2'4LNR2S3LEN1P1p3lnw2EC3LNB3ECB3PB'3LNRS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFFS2FBS2FBS2FBS1R3HIA1h2sp2lo3TOP3HT0S2FBS2FBS2FBS2FBS2FBS2FBS3LEN1P1p3lnw2EC3ECB3PB'3LNR2p23PB2SS2FBS2FBS2FBS1p3lnw2EC3LNBS1R2lo3LOSS2FBS2FBS1r3RR22r02KR1q1HS2FBFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184FBLO3NER2p22L24NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184FBLO3NER2p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4SLO13NERS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLFFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ALO3NER2p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_stFFS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2F02HBS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182F04NSH'3NSL2HBS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L24NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0 HGT"] Lemma stageSeed : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.PEC,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(9.&40.(:.VFB,+140.))(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R17.R16.R15.R14.)P,(;.(<.&40.R27.)(=.R14.R28.))P,(;.R15.(:.VP,VLEN,))P,(;.R17.+3.)P,(25.$26.(27.R2>.)$28.)P,(;.(22.R2>.)+1.)P,(;.(22.R2>.)+1.)P,(;.(:.(:.(:.R37.(23.+2.(>.VLEN,)))(23.+2.(24.+1.)))$?.)(10.VLEN,))P,(;.(:.(:.(:.R37.(23.+2.(11.=)))+6.)$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3<.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R1;.(9.&40.Vsp1,)Vgp,Vtp,R1:.R19.R18.Vsp,(9.&40.Vsp1,)R17.R16.R15.R14.R13.R12.R11.R10.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))(9.&40.R1<.)R;.(9.&40.VFB,)R:.(9.&40.(:.VFB,+170.))R?.R>.R=.R<.)VF,(9.&40.+:??6<.)Vfc,(20.(4.&40.))R3:.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI LNB ECB K3 XNULL NY NZ VB FB'.
    dpose SI as (EBsave & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof (bv_unsigned_in_range 64 lnw) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 320, [C8 lnw]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])] _ _ EBsave
                  ltac:(intros c Hc; right; exact Hc)) as EBr.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(FB + 288, FB + 296)] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    do 5 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (OWN1 : Forall own_iv [(FB + 288, FB + 296)]) by (apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    pose proof (eb_own hk LBk mk v f _ _ _ _ _ m1 [(FB + 288, FB + 296)] EBr MU ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) WM MIk STb ltac:(ch_dj)) as EB1r.
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB1r PCELL ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB1.
    assert (TOK1 : tmp_ok asegs m1 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk mk m1 _ _ HH0' TOK MU WM MI0' MIk OWN1).
      intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1; lia| exact I]. }
    assert (SI1 : SPINV hk LBk m1 v f dN dP dA dB dX dY dZ (p + bv_unsigned lnw) lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB1|]. split; [exact TOK1|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' LNR LNB ECB; lia| exact C24k]. }
    (* [comment removed for export] *)
    do 4 zstep.
    eapply (sp_gettag hk LBk m1 v f _ _ (DS7 dN dP dA dB dX dY dZ) (p + bv_unsigned lnw) EC 3 0xaff90 lnw);
      [exact EB1| exact TOK1| clear - PB' LNR; lia| clear - LNB; lia| exact ECB| ch_dj| clear; lia| reflexivity|].
    intros m2 r p2 L2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB2 TOK2 PB2 RR2 ROK2.
    assert (SI2 : SPINV hk LBk m2 v f dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2 LNR ECB; lia| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI SI1 EBr EB1r EB1 TOK1 PCELL LCELL OWN1.
    dpose SI2 as (EBsave & TOK & _). pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { eapply (seed_join hk LBk m2 v f dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 K EC);
        [exact SI2| clear - PB' PB2 LNR; lia| exact ECB| exact K3| exact XNULL| exact NY| exact NZ| exact VB| exact FB']. }
    assert (RZ : r = 0) by (clear - KR RR2; Z.div_mod_to_equations; lia). subst r. clear KR. destruct (ROK2 eq_refl) as (PG2 & LB2'). clear ROK2.
    pose proof (bv_unsigned_in_range 64 L2) as LNR2. change (bv_modulus 64) with (2^64) in LNR2.
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 320, [C8 L2]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])] _ _ EBsave
                  ltac:(intros c Hc; right; exact Hc)) as EBr.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(FB + 288, FB + 296)] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    do 5 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (OWN1 : Forall own_iv [(FB + 288, FB + 296)]) by (apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    pose proof (eb_own hk LBk m2 v f _ _ _ _ _ m3 [(FB + 288, FB + 296)] EBr MU ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) WM MIk STb ltac:(ch_dj)) as EB1r.
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB1r PCELL ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB1.
    assert (TOK1 : tmp_ok asegs m3 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk m2 m3 _ _ HH0' TOK MU WM MI0' MIk OWN1).
      intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1; lia| exact I]. }
    assert (SI3 : SPINV hk LBk m3 v f dN dP dA dB dX dY dZ (p2 + bv_unsigned L2) L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB1|]. split; [exact TOK1|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2 LNR LNR2 LB2' ECB; lia| exact C24k]. }
    eapply (seed_join hk LBk m3 v f dN dP dA dB dX dY dZ (p2 + bv_unsigned L2) L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 K EC);
      [exact SI3| clear - PB' PB2 LNR LNR2; lia| exact ECB| exact K3| exact XNULL| exact NY| exact NZ| exact VB| exact FB'].
    all: match goal with |- ?g => idtac "SEED-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01T0@D16670306730.254D17209380499.254D40016287967.254L10364399054.2  L1100163697.10  L11511961495.8  L12469921329.0  L14492240433.288L14906048793.244L14906048793.268L14987706775.8  L15653086487.8  L1685717371.0   L17924243177.9  L1818808183.3   L18432251946.6  L18901988838.1  L18909959449.244L18909959449.268L19767991565.1  L20765625018.9  L21866712442.1  L22252508346.1  L22638198257.10 L23380989714.9  L25141141322.3  L28432818399.244L28603631775.2  L29010569984.265L29022582655.2  L29252150116.1  L31573175913.9  L35668120898.7  L35869924834.6  L36607162391.8  L39833374057.9  L39953928681.7  L40800369137.10 L42851534655.7  L43001578345.9  L44011663895.8  L44741757425.10 L46350850038.10 L47733298015.6  L47915212785.10 L49379278409.0  L51159590045.6  L51543886882.6  L52838367809.6  L53323719005.1  L54015504437.5  L54024012424.7  L56174508785.10 L56494227009.1  L58227785239.8  L58573668988.268L58711294999.8  L59612558537.4  L60098763854.3  L63141123211.3  L65105751913.9  L66151426447.10 L66590572961.0  L7021056161.0   L7293583127.8   L7462897247.3   L7738195705.2   L79096076.0     L9404489852.244 L9404489852.268 P29008688568.255P7750690063.255 Q11801279589.254Q15224056021.251Q15224234932.275Q19401054440.251Q19401233289.275Q19998568980.275Q20580512354.254Q24130372517.275Q24130586820.251Q41218494256.254Q41220736304.254Q47409184484.254Q47411131620.254Q48117823211.254Q48228597444.251Q48228611493.275Q49698585326.253Q49933378966.254Q53880891412.275Q53881004917.251Q54967541497.255Q56671730518.252Q58768111688.255Q64039262601.275Q66954699982.255Q6912046254.255 Q7712614101.251 Q7712730548.275 00000101I02a02g02k02o03003104405705;05?05@05D05O05d05h06k07n08208Q08U08Y08]09=09G0:J0:S0:T0:U0:Y0:]0;40;E0;I0;M0;f0;j0<@0<D0<H0<L0<o0=E0=I0=J0=a0>20>H0>L0>]0?30?70?;0??0@B0@F0@T0@^0@g0@k0A<0A=0A>0AB0AM0AN0AO0BR0CU0EI0G50HF0IB0J>0KR0Lf0N00N10Nm0Oi0Q:0RK0S\0Tm0V\0WX0XT0YY0YZ0Zd0[n0]?0^A0_R0`f0b70cH0dD0e@FS2LF2sp3PKA2FB3sp13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1K2K2S2FBS2FBFFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS2FBSS2FBS2FB2d03XB1S3LEN1P1p3lnw3PB'3LNRS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS3LEN1P1p3lnw2EC3PB'3LNR2p23PB2S2FBS2FBS2FBS3LEN1P1p3lnw2EC3LNB3ECB3PB'3LNRS3LEN1v2VBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2L24LNR2FFS2FBS2FBS1R3HIA1h2sp2lo3TOP3HT0S1d1f3FB'3TF13RF0S2FBS2FBS3LEN1P2EC3ECB2p22L24LB2'S2FBS3LEN1v2VB3TV13RB03GP0S2FBS2FBS2FBS3LEN1P1p3lnw2EC3ECB3PB'3LNR2p23PB2S2LB3LBk1K4C24k3LB52C5S2FBSS2LB4C24H3LBk1K2K24C24kS1d1f3FB'3TF13RF0S3LEN1v2VB3TV03RB03GP0S2FBS1d1f3FB'3TF03RF0S3LEN1v2VB3TV13RB03GP0S2FBS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2FBS1p3lnw2EC3LNBS1R2lo3LOSS1d1f3FB'S2FBS1r3RR22r02KR1q1HSSS2FBS1r3RR23RNZFSS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4SLO13NERS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL3ALO3NER2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_stFS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2F02HBS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER4NSH'3NSLS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p3lnw2v12v22v32v42v52v62v73v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0 HGT"] Lemma stageB : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.PEC,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(9.&40.(:.VFB,+140.))(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R17.R16.R15.R14.)P,(;.(<.&40.R27.)(=.R14.R28.))P,(;.R15.(:.VP,VLEN,))P,(;.R17.+2.)P,(25.$26.(27.R2>.)$28.)P,(;.(22.R2>.)+1.)P,(;.(22.R2>.)+1.)P,(;.(:.(:.(:.R37.(23.+3.(>.VLEN,)))(23.+2.(24.+1.)))$?.)(10.VLEN,))P,(;.(:.(:.(:.R37.(23.+3.(11.=)))+6.)$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3<.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R1;.(9.&40.Vsp1,)Vgp,Vtp,R1:.R19.R18.Vsp,(9.&40.Vsp1,)R17.R16.R15.R14.R13.R12.R11.R10.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))(9.&40.R1<.)R;.(9.&40.VFB,)R:.(9.&40.(:.VFB,+170.))R?.R>.R=.R<.)VF,(9.&40.+:??2<.)Vfc,(20.(4.&40.))R3:.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI LNB ECB K2 XNULL NY NZ VB FB'.
    dpose SI as (EBsave & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof (bv_unsigned_in_range 64 lnw) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 320, [C8 lnw]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])] _ _ EBsave
                  ltac:(intros c Hc; right; exact Hc)) as EBr.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(FB + 288, FB + 296)] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    do 5 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (OWN1 : Forall own_iv [(FB + 288, FB + 296)]) by (apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    pose proof (eb_own hk LBk mk v f _ _ _ _ _ m1 [(FB + 288, FB + 296)] EBr MU ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) WM MIk STb ltac:(ch_dj)) as EB1r.
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB1r PCELL ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB1.
    assert (TOK1 : tmp_ok asegs m1 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk mk m1 _ _ HH0' TOK MU WM MI0' MIk OWN1).
      intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1; lia| exact I]. }
    assert (SI1 : SPINV hk LBk m1 v f dN dP dA dB dX dY dZ (p + bv_unsigned lnw) lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB1|]. split; [exact TOK1|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' LNR LNB ECB; lia| exact C24k]. }
    (* [comment removed for export] *)
    do 4 zstep.
    eapply (sp_gettag hk LBk m1 v f _ _ (DS7 dN dP dA dB dX dY dZ) (p + bv_unsigned lnw) EC 4 0xaff50 lnw);
      [exact EB1| exact TOK1| clear - PB' LNR; lia| clear - LNB; lia| exact ECB| ch_dj| clear; lia| reflexivity|].
    intros m2 r p2 L2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB2 TOK2 PB2 RR2 ROK2.
    assert (SI2 : SPINV hk LBk m2 v f dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2 LNR ECB; lia| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI SI1 EBr EB1r EB1 TOK1 PCELL LCELL OWN1.
    dpose SI2 as (EBsave & TOK & _). pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { eapply (sp_errbac hk LBk m2 _ _ dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K _);
        [exact SI2| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      assert (RNZ : r <> 0) by (intros ->; clear - KR; first [apply KR; reflexivity| (vm_compute in KR; congruence)]). clear - RR2 RNZ. lia. }
    assert (RZ : r = 0) by (clear - KR RR2; Z.div_mod_to_equations; lia). subst r. clear KR. destruct (ROK2 eq_refl) as (PG2 & LB2'). clear ROK2.
    pose proof (bv_unsigned_in_range 64 L2) as LNR2. change (bv_modulus 64) with (2^64) in LNR2.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 5 zstep.
    replace (FB + 408) with (md_addr dB) by (rewrite EB'; clear; lia).
    rewrite <- (Z_to_bv_bv_unsigned L2).
    eapply (sp_readbin hk LBk m2 v f _ _ (DS7 dN dP dA dB dX dY dZ) dB p2 (bv_unsigned L2) 0xaff68);
      [exact EBsave| exact TOK| inlist| clear - PB' PB2 LNR; lia| clear - LNR2; lia| clear - LB2' ECB; lia| rewrite EB'; ch_dj
      | unfold C24_PK_USE_ECPARAMS, C24_ECP_GROUP_LOAD in C24H; clear - C24H C24k K2; lia| clear; lia| reflexivity| clear - VB TV0 RB0 GP0; lia| clear - FB' TF0 RF0; lia|].
    intros h5 LB5 m5 dB' r5 u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 EB5 TOK5 EAD5 C5 RR5 ROK5.
    ddestruct (tmp_upd7 dB' dN dP dA dB dX dY dZ EN EP EA EB' EX EY EZ) as (_ & _ & _ & UPD & _). rewrite (UPD ltac:(rewrite EAD5; exact EB')) in EB5, TOK5. clear UPD.
    rewrite ?(Z_to_bv_bv_unsigned L2).
    assert (SI5 : SPINV h5 LB5 m5 (v + MPI_RB_PHI LEN) (f + MPI_RB_FR 0) dN dP dA dB' dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 (K + 1)).
    { split; [exact EB5|]. split; [exact TOK5|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [rewrite EAD5; exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2 LNR ECB; lia| clear - C5 C24k; lia]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK PCELL LCELL SI2.
    pose proof SI5 as (EBk & _).
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    assert (SCSk : crange (hcs asegs R HIA h5) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h5 LB _ LF m5 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h5) h5 _ LF m5 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h5 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h5) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR5; zify_cond KR5.
    { eapply (sp_errbac h5 LB5 m5 _ _ dN dP dA dB' dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 (K + 1) _);
        [exact SI5| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      destruct RR5 as [-> | ->]; [exfalso; apply KR5; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]. }
    eapply (stageSeed h5 LB5 m5 _ _ dN dP dA dB' dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 (K + 1) EC);
      [exact SI5| exact LB2'| exact ECB| clear - K2; lia| exact XNULL| exact NY| exact NZ| clear - VB; lia| clear - FB'; lia].
    all: match goal with |- ?g => idtac "B-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0130@L10470257411.287L10826632681.3  L11511961495.8  L14492240433.310L14906048793.264L14906048793.290L14987706775.8  L15318568095.2  L15653086487.8  L15793402742.10 L16507500205.11 L18909959449.264L18909959449.290L19722208118.10 L20765625018.6  L21444186492.290L2263936207.9   L22658091809.0  L23952587329.1  L25141141322.3  L27934866982.10 L29010569984.261L30561351161.2  L35668120898.7  L35869924834.6  L36607162391.8  L39953928681.5  L40871286518.10 L41068974454.10 L42851534655.7  L43100994499.3  L44011663895.8  L46126591772.2  L46350850038.6  L47733298015.6  L48834180257.0  L49379278409.0  L50165924257.0  L51159590045.6  L51543886882.6  L52838367809.6  L54015504437.5  L54024012424.7  L56442983542.10 L58227785239.8  L58711294999.8  L60098763854.3  L62586290822.10 L63141123211.3  L66151426447.10 L66338125686.10 L67576253535.2  L7293583127.8   L79096076.0     L9404489852.238 Q15224234932.271Q15224234932.297Q19401054440.245Q24130372517.271Q24130372517.297Q28089954068.297Q48228611493.271Q48228611493.297Q52019788937.297Q53881004917.245Q7712730548.271 Q7712730548.297 00000100=00A00B01E02Q02U02\02`02d03I04L05X05\06007<07[07\07`07j08K08L08U08l09=09A09S09W09[0:10:=0:A0:H0:\0;20;30;40;50;L0;]0<30<D0<Z0<^0<b0<f0=00=B0=K0=\0=`0=f0=j0=k0>n0?j0@o0BC0C?0DD0EW0FS0GX0I50J?0K;0L@FS2p22L24LNR2S2FBFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSLS2FBS1r3RR2S2FBS2FBS3LEN1P1p3PB'2p22L23PB22EC3ECB2p33PB3S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSLS2FBS3LEN1P1p3PB'2p23PB2S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSLS3LEN1P2p22L22EC3ECB2p32L34LB3'SS2FBS3LEN1v2VBS3LEN1P1p3PB'2p22L23PB22EC2p33PB3FS2L34LNR3S1R3HIA1h2sp2lo3TOP3HT0S1d1f3FB'3TF13RF0S2FBS3LEN1P2p22L24LB2'S2FBS2FBS3LEN1v2VB3TV13RB03GP0S2r33RR33RNZS2FBS3LEN1PS3LEN1P1p3PB'2p23PB2S2LB3LBk1K4C24k3LB52C5SSSS2LB4C24H3LBk1K2K14C24kS1d1f3FB'3TF13RF0S3LEN1v2VB3TV03RB03GP0S1d1f3FB'3TF03RF0S3LEN1v2VB3TV13RB03GP0S2FBS2FBS2FBS1R2lo3LOSS2r33RR31r3KR31q1HS1d1f3FB'S1r3RR22r02KR1q1HS2FBS1K2K1S2FBSS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSL4SLO13NERS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v184SLO13NER2p22L22EC4NSH'3NSLS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182p22L22EC4NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0 HGT"] Lemma stageA : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps7v,(4.&40.)Ps8v,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(9.&40.(:.VFB,+140.))(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R17.R16.R15.R14.)P,(;.R15.+1.)P,(25.$26.(27.R2<.)$28.)P,(;.(22.R2<.)+1.)P,(;.(22.R2<.)+1.)P,(;.(:.(:.(:.R35.(23.+4.(>.VLEN,)))(23.+2.(24.+1.)))$?.)(10.VLEN,))P,(;.(:.(:.(:.R35.(23.+4.(11.=)))+6.)$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3:.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R1:.(9.&40.Vsp1,)Vgp,Vtp,R19.R18.R17.Vsp,(9.&40.Vsp1,)R16.R15.R14.R13.R12.R11.R10.R?.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))R:.R9.(9.&40.VFB,)R8.(9.&40.(:.VFB,+170.))R>.R=.R<.R;.)VF,(9.&40.+:?>=8.)Vfc,(20.(4.&40.))R38.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI K1 XNULL NY NZ VB FB'.
    dpose SI as (EBsave & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 6 zstep.
    eapply (sp_gettag hk LBk mk v f _ _ (DS7 dN dP dA dB dX dY dZ) p PEND 48 0xafef0 lnw);
      [exact EBsave| exact TOK| exact (proj1 PB')| exact (proj2 PB')| clear; lia| ch_dj| clear; lia| reflexivity|].
    intros m2 r p2 L2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB2 TOK2 PB2 RR2 ROK2.
    assert (SI2 : SPINV hk LBk m2 v f dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2; lia| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI.
    dpose SI2 as (EBsave & TOK & _). pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { eapply (sp_err948 hk LBk m2 _ _ dN dP dA dB dX dY dZ p2 L2 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K r);
        [exact SI2| clear - RR2; lia| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      intros ->; clear - KR; first [apply KR; reflexivity| (vm_compute in KR; congruence)]. }
    assert (RZ : r = 0) by (clear - KR RR2; Z.div_mod_to_equations; lia). subst r. clear KR. destruct (ROK2 eq_refl) as (PG2 & LB2'). clear ROK2.
    pose proof (bv_unsigned_in_range 64 L2) as LNR2. change (bv_modulus 64) with (2^64) in LNR2.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    (* [comment removed for export] *)
    do 8 zstep.
    set (EC := p2 + bv_unsigned L2) in *.
    assert (ECB : EC <= PEND) by (unfold EC; clear - LB2'; lia).
    eapply (sp_gettag hk LBk m2 v f _ _ (DS7 dN dP dA dB dX dY dZ) p2 EC 4 0xaff14 L2);
      [exact EBsave| exact TOK| clear - PB' PB2; lia| unfold EC; clear - LNR2; lia| exact ECB| ch_dj| clear; lia| reflexivity|].
    intros m3 r3 p3 L3 z0 z1 z2 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB3 TOK3 PB3 RR3 ROK3.
    assert (SI3 : SPINV hk LBk m3 v f dN dP dA dB dX dY dZ p3 L3 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB3|]. split; [exact TOK3|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2 PB3 ECB; lia| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI2 PCELL LCELL.
    dpose SI3 as (EBsave & TOK & _). pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m3 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m3 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR3; zify_cond KR3.
    { eapply (sp_errbac hk LBk m3 _ _ dN dP dA dB dX dY dZ p3 L3 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K _);
        [exact SI3| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      assert (RNZ : r3 <> 0) by (intros ->; clear - KR3; first [apply KR3; reflexivity| (vm_compute in KR3; congruence)]). clear - RR3 RNZ. lia. }
    assert (RZ3 : r3 = 0) by (clear - KR3 RR3; Z.div_mod_to_equations; lia). subst r3. clear KR3. destruct (ROK3 eq_refl) as (PG3 & LB3'). clear ROK3.
    pose proof (bv_unsigned_in_range 64 L3) as LNR3. change (bv_modulus 64) with (2^64) in LNR3.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 4 zstep.
    replace (FB + 392) with (md_addr dA) by (rewrite EA; clear; lia).
    rewrite <- (Z_to_bv_bv_unsigned L3).
    eapply (sp_readbin hk LBk m3 v f _ _ (DS7 dN dP dA dB dX dY dZ) dA p3 (bv_unsigned L3) 0xaff28);
      [exact EBsave| exact TOK| inlist| clear - PB' PB2 PB3; lia| clear - LNR3; lia| clear - LB3' ECB; lia| rewrite EA; ch_dj
      | unfold C24_PK_USE_ECPARAMS, C24_ECP_GROUP_LOAD in C24H; clear - C24H C24k K1; lia| clear; lia| reflexivity| clear - VB TV0 RB0 GP0; lia| clear - FB' TF0 RF0; lia|].
    intros h5 LB5 m5 dA' r5 u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 EB5 TOK5 EAD5 C5 RR5 ROK5.
    ddestruct (tmp_upd7 dA' dN dP dA dB dX dY dZ EN EP EA EB' EX EY EZ) as (_ & _ & UPD & _). rewrite (UPD ltac:(rewrite EAD5; exact EA)) in EB5, TOK5. clear UPD.
    rewrite ?(Z_to_bv_bv_unsigned L3).
    assert (SI5 : SPINV h5 LB5 m5 (v + MPI_RB_PHI LEN) (f + MPI_RB_FR 0) dN dP dA' dB dX dY dZ p3 L3 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 (K + 1)).
    { split; [exact EB5|]. split; [exact TOK5|]. split; [exact EN|]. split; [exact EP|]. split; [rewrite EAD5; exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB2 PB3 ECB; lia| clear - C5 C24k; lia]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK PCELL LCELL SI3.
    pose proof SI5 as (EBk & _).
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    assert (SCSk : crange (hcs asegs R HIA h5) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h5 LB _ LF m5 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h5) h5 _ LF m5 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h5 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h5) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR5; zify_cond KR5.
    { eapply (sp_errbac h5 LB5 m5 _ _ dN dP dA' dB dX dY dZ p3 L3 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 (K + 1) _);
        [exact SI5| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      destruct RR5 as [-> | ->]; [exfalso; apply KR5; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]. }
    eapply (stageB h5 LB5 m5 _ _ dN dP dA' dB dX dY dZ p3 L3 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 (K + 1) EC);
      [exact SI5| exact LB3'| exact ECB| clear - K1; lia| exact XNULL| exact NY| exact NZ| clear - VB; lia| clear - FB'; lia].
    all: match goal with |- ?g => idtac "A-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02c0@D16670306730.278D17209380499.278D40016287967.278D40016287967.323D41162118442.323D46719952988.254D50014262098.254D5623640851.323 L10259629737.0  L12030387076.1  L12469921329.0  L13050815905.9  L14218035329.323L14492240433.294L14906048793.246L14906048793.268L14906048793.313L15493637052.8  L16798266401.9  L1685717371.0   L16908924412.272L17924243177.9  L18140481520.244L1818808183.3   L18430670468.0  L18515049316.1  L18901988838.1  L18909959449.243L19349569929.0  L19422852028.8  L19711640196.1  L19770819644.2  L19811942076.8  L19980016842.7  L21866712442.1  L21868500043.2  L22252508346.1  L24356290505.0  L25137631108.1  L25141141322.3  L25582828285.13 L25585108845.6  L26882835213.1  L26885151292.2  L28061483542.23 L28432818399.268L29022492404.13 L29022582655.2  L29252150116.1  L31573175913.9  L32365901494.23 L33976446175.313L35668120898.7  L35684885892.1  L35869924834.6  L37218691045.323L37251195161.313L37593808828.8  L38069802256.10 L38235734261.1  L38309573212.8  L38319490977.9  L38408712019.4  L38424225785.23 L39833374057.9  L41110932849.3  L41607260436.17 L41975692192.4  L42128420922.11 L42851534655.7  L43001578345.9  L43754759929.12 L43754759929.13 L45497087078.1  L45501773502.3  L45564688816.5  L46046848644.1  L46369226564.0  L46438723165.1  L47733298015.6  L49379278409.0  L49788159649.0  L51159590045.6  L51514702988.4  L51543886882.6  L5196155000.7   L52329398423.13 L52548154273.9  L52838367809.6  L53323719005.1  L53540680021.0  L54015504437.5  L54024012424.7  L54949972769.0  L54992078076.267L56055426732.2  L57885839492.1  L58283698316.0  L58744494047.8  L58800640149.6  L60098763854.3  L60690035770.1  L62865972668.8  L63141123211.3  L63980823713.9  L65105751913.9  L66212808353.0  L7735748552.2   L7738195705.2   L7813112924.10  L8848476737.1   L9080220944.4   L9341288836.1   L9404489852.244 L9786907307.1   P19772131067.254P21870859916.254P26886985979.254P29008688568.279P29008688568.324P7750690063.255 P7750690063.279 P7750690063.324 Q11801279589.254Q11801279589.278Q11801279589.323Q13400730472.274Q15224056021.250Q19403336892.251Q20580512354.254Q20580512354.278Q20580512354.323Q20608450805.274Q22712450012.254Q24130586820.320Q24132863642.253Q24136649662.275Q24251258485.254Q25513505925.254Q3203240366.252 Q33111571044.323Q33113550948.323Q41218494256.278Q41218494256.323Q41220736304.278Q41220736304.323Q42365632470.321Q46002230320.279Q47409184484.278Q47411131620.278Q48117823211.278Q48117823211.323Q48228597444.250Q49698585326.253Q49698585326.277Q49698585326.322Q49933378966.278Q50721622596.320Q52389960886.254Q53878789921.251Q54967541497.255Q54967541497.279Q54967541497.324Q56671730518.276Q5722487062.323 Q58768111688.255Q58768111688.279Q58768111688.324Q63197742677.320Q66954699982.255Q66954699982.279Q66954699982.324Q67300466605.279Q6912046254.255 Q6912046254.279 Q6912046254.324 Q7706420655.275 Q7710238859.253 Q7712614101.320 00000101I02a04;04<06K08M09g09h09l09m0:10;B0;C0<J0=Q0>X0>\0>`0>a0?h0?l0A30A>0A?0AC0AG0BN0BO0BS0BW0BX0B\0C40C80C90C=0C>0CB0CL0Cc0D70D;0D<0E:0FA0FB0FC0FG0FK0Fd0Gk0HB0HF0HW0Ih0Jo0K30KE0KI0Ki0Km0L<0Le0Li0M40Me0Mo0NW0Nm0O10OV0P;0P?0PG0PX0P\0P]0Pa0Q70Q80Q90QP0Q]0Qn0RD0RH0RL0Rb0Rf0Rg0S80SN0SO0TV0T\0T`0Ta0U<0UR0U\0U`0Ud0Um0V10V50V60V70V80VM0VQ0V`0Vd0Wk0Wo0Ya0[S0]E0_90`o0bI0d;0eo0gB0hS0if0kD0lD0m\0m]0m^0m_0nm10G11G12G13G14n16K17W18j1:=1;N1<a1>21?E1@K1Ai1C:1DK1F:1Gk1Hk1J81KA1LJ1LK1MK1O:1PH1Q[1Rl1T?1UE1UF1VY1Wj1Y=1Z=1[P1\a1^41_B1`U1af1c91d91e91f9FS2LF2sp3PKA2FB3sp13LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stFS1R3HIA5NEEDR1h2LF2sp3PKA2lo3SLO3TOP2FB3sp13SP13LFB3NZP2bs2hk2v12v22v32v42v52v62v73s643v163v173v183ETk4NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stSS2FBFS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182EF3ibs2p54NSH'3NSL3PRGFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2FBS2FBSS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2FB2d03XB1SS2FBS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLSS2FBS2FBFS2FBS1R3HIA1h2sp3TOP3sp13SP1S2FBFS2FBSS2FBS3LEN1v2VBS3LEN1P3BUF2bs2BP1p3PB'S3LEN1P3BUF2BP1p3PB'S2FBFS2sp2lo3sp13SP13LEN1P3BUF2bs3DSB2BP2PL1p3lnw2EF3LNB3EFB3PB'2L7S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLFFS2FBS2FBS1R2lo3LOS3sp12bs3ALO3ACVS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS1R3HIA1h2sp2lo3TOP3HT0S2FBS1d1f3FB'3TF13RF0S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182EF3ibs2p54NSH'3NSL3PRGS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2FBS2r53RR51r3KR51q1HS2loS1R5NEEDR2sp2lo3sp13SP14SLO13NERS2FBS2sp2lo3sp13SP1S3LEN1P3BUF2bs3B472PL1p3lnw2EF3LNB3EFB2L7S2FBS2FB2d03XB3S3LEN1P3BUF2bs4BUF03B472BP2PL1p2EF3EFB3PB'2p53PB5S2EF2p52KES1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2d03XB2S3LEN1v2VB3TV13RB03GP0S2FBS3LEN1P3BUF2bs2PL1p3lnw2EF3LNB3EFB2L7S3LEN1P3BUF2bs2PL1p3lnw2EF3LNB3EFB2L7S2FBS3lnw2KLS1p3lnw2EF3LNB2L7S2FBSS2FBS2LB3LBk1K4C24k3LB52C5SSS2LB4C24H3LBk1K2K04C24kS3LEN1P1p3PB'S1d1f3FB'3TF13RF0S2lo2FB3sp14FBLO1x3XB2S2bsS2FBS3LEN1v2VB3TV03RB03GP0S2FBSS1d1f3FB'3TF03RF0S3LEN1v2VB3TV13RB03GP0SS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS1K2K0S2FBSS3LEN1P1p2EF3EFB3PB'2p53PB5S1R2sp2lo3sp13SP14SLOBS1R2lo3LOSS2FBS2FBS1d1f3FB'S2FBS2FBSFFS2r53RR51r3KR51q1H2H0S2FBS2sp2lo3sp13SP1S2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2FBS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF3PKA2lo3LOS2FB3sp13LFB2bs1p2v12v22v32v42v52v62v73v163v173v182F13ALO4SLO13NER3ibs4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF3PKA2lo3LOS2FB3sp13LFB2bs2v12v22v32v42v52v62v73v163v173v182F13ALO4SLO13NER3ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v182F13ALO3NER3ibs4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182F13ALO3NER3ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v183NER3ibs4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4SLO13NERFFFS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4SLO13NER2HB5Ha_st5Hl_stS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL4SP1R2HBS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182F03ibs4NSH'3NSL2HBS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v183NER3ibs4NSH'3NSLS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ALO3NER3ibs4NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ALO3NER3ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_stFS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS1R5NEEDR2LF3PKA2lo3LOS2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL3ALO4SLO13NER2HB5Ha_st5Hl_stS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v182F03ibs4NSH'3NSL2HBFS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs1p2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs3pbv4NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73v163v173v183ibs4NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0 HGT MCI SLOB"] Lemma stageF2 : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Ps64,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.PEF,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(9.&40.(:.VFB,+1=8.))(9.&40.VPKA,)R16.R15.R14.R13.)P,(;.(<.&40.R27.)(=.R13.R28.))P,(;.R14.(:.VP,VLEN,))P,(;.R16.=)P,(25.$26.(27.R2>.)$28.)P,(;.(22.R2>.)+1.)P,(;.(22.R2>.)+1.)P,(;.(:.(:.(:.R37.(23.+5.(>.VLEN,)))(23.+2.(24.+1.)))$?.)(10.VLEN,))P,(;.(:.(:.(:.R37.(23.+5.(11.=)))+6.)$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3<.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R1:.(9.&40.Vsp1,)Vgp,Vtp,R19.R18.R17.Vsp,(9.&40.Vsp1,)R16.R15.R14.R13.R12.R11.R10.R?.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))(9.&40.R1;.)(9.&40.(:.VFB,+140.))(9.&40.VFB,)R:.(9.&40.(:.VFB,+170.))R>.R=.R<.R;.)VF,(9.&40.+:?>50.)Vfc,(20.(4.&40.))R3:.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI LNB EFB K0 XNULL NY NZ VB FB'.
    dpose SI as (EBsave & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof (bv_unsigned_in_range 64 lnw) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(sp1 + 8, sp1 + 152)] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    do 5 zstep. if_cases KL; zify_cond KL.
    { eapply (sp_err94c hk LBk mk _ _ dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K (-14720));
        [exact SI| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    assert (L7 : bv_unsigned lnw = 7) by (clear - KL LNR; lia). clear KL.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (eb_slots hk LBk mk v f _ _ _ _ _ _ m1 EBsave MU WM ltac:(assumption) SLOTS eq_refl) as EB1.
    assert (TOK1 : tmp_ok asegs m1 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk mk m1 _ _ HH0' TOK MU WM MI0' ltac:(assumption)).
      - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_nil].
      - intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO SLO1 NER NEEDR; lia| exact I]. }
    (* [comment removed for export] *)
    do 6 zstep.
    destruct (eb_bytes _ _ _ _ _ _ _ _ _ EB1) as (HBS1 & OBUF1 & CRB1).
    set (ibs := firstn (Z.to_nat 7) (skipn (Z.to_nat (p - BUF)) bs)).
    assert (LENI : Z.of_nat (length ibs) = 7) by (subst ibs; apply P_asn1_get_mpi.bytes_at_sub_length; clear - BP PL PB' LNB L7 EFB; lia).
    assert (HIB : bytes_at asegs m1 p ibs) by (subst ibs; eapply P_asn1_get_mpi.bytes_at_sub; [exact HBS1| | |]; clear - BP PL PB' LNB L7 EFB; lia).
    assert (RO : bytes_at asegs m1 0x26460 PRIME_FIELD_OID).
    { eapply (P_oid.ro_image_bytes_at asegs m1 0x26460 PRIME_FIELD_OID); [assumption| vm_compute; reflexivity| clear; lia| cbn; clear; lia]. }
    assert (ORO : aobj asegs AL (hcs asegs R HIA hk) m1 0x26460 7).
    { eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); destruct EB1 as (HH1 & _); exact HH1| vm_compute; reflexivity]. }
    pose proof (alloc_ceiling_val R) as ACV.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { pose proof (artA_bcmp asegs R HIA) as SPB. rewrite MCI in SPB.
      destruct EB1 as (HH1 & _).
      eapply SPB with (h := hk) (LB := LBk) (LF := LF') (P := p) (Q := 0x26460) (n := 7) (lo := lo) (ps := ibs) (qs := PRIME_FIELD_OID);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HH1 | exact HIB | exact RO | exact LENI | exact ORO | exact LOS | assumption | reflexivity
              | lazymatch goal with
                | |- aobj _ _ _ _ p 7 => eapply aobj_sub; [exact OBUF1| clear - BP PB'; lia| clear - PL PB' LNB L7 EFB; lia]
                | |- crange _ _ _ => eapply crange_sub; [exact SCSk| clear; lia| clear - SP1; lia]
                | |- lo <= _ => clear - SLOB SP1; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ < 2^40 => clear; lia
                | |- _ \/ _ => clear - DSB SP1 BP PL PB' LNB L7 EFB B47 ACV ALO LOS; lia
                end
              | match goal with |- ?g => idtac "BCMP-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold call_postA in PO.
    ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & E & MU2 & WM2 & MI2 & REQ & ST2 & HH2). subst ms'.
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xafe80)) with (Z_to_bv 64 0xafe80 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (eb_scratch _ _ _ _ _ _ _ _ _ _ m2 lo EB1 MU2 ltac:(clear; lia) WM2 MI2 ST2) as EB2.
    assert (TOK2 : tmp_ok asegs m2 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EB1 as (HH1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
      eapply (tmp_ok_own hk LBk m1 m2 _ _ HH1 TOK1 MU2 WM2 MI1 MI2).
      - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1; lia| apply Forall_nil].
      - intros x Hx. ddestruct TOK1 as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
        cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO; lia| exact I]. }
    assert (SI2 : SPINV hk LBk m2 v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact PB'| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI PCELL LCELL EB1 TOK1 HBS1 OBUF1 CRB1 HIB RO ORO MU2 WM2 HH2.
    dpose SI2 as (EBsave & TOK & _). pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m2 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m2 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KB.
    { eapply (sp_err hk LBk m2 _ _ dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ _ v16 v17 v18 K (-14720));
        [exact SI2| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    clear KB REQ.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 320, [C8 lnw]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 pb; C8 nb])] _ _ EBsave
                  ltac:(intros c Hc; right; exact Hc)) as EBr.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    clear MU. pose proof (munch_refl ([(FB + 288, FB + 296)] : list ivl) m2) as MU.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (OWN1 : Forall own_iv [(FB + 288, FB + 296)]) by (apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    pose proof (eb_own hk LBk m2 v f _ _ _ _ _ m3 [(FB + 288, FB + 296)] EBr MU ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) WM MIk STb ltac:(ch_dj)) as EB3r.
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB3r PCELL ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB3.
    assert (TOK3 : tmp_ok asegs m3 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk m2 m3 _ _ HH0' TOK MU WM MI0' MIk OWN1).
      intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1; lia| exact I]. }
    (* [comment removed for export] *)
    do 5 zstep.
    replace (FB + 376) with (md_addr dP) by (rewrite EP; clear; lia).
    eapply (sp_getmpi hk LBk m3 v f _ _ (DS7 dN dP dA dB dX dY dZ) dP (p + 7) EF 0xafea4);
      [exact EB3| exact TOK3| inlist| clear - PB'; lia| clear - LNB L7; lia| exact EFB| rewrite EP; ch_dj
      | unfold C24_PK_USE_ECPARAMS, C24_ECP_GROUP_LOAD in C24H; clear - C24H C24k K0; lia| clear; lia| reflexivity| clear - VB TV0 RB0 GP0; lia| clear - FB' TF0 RF0; lia|].
    intros h5 LB5 m5 dP' r5 p5 u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 EB5 TOK5 EAD5 C5 PB5 RR5 ROK5.
    ddestruct (tmp_upd7 dP' dN dP dA dB dX dY dZ EN EP EA EB' EX EY EZ) as (_ & UPD & _). rewrite (UPD ltac:(rewrite EAD5; exact EP)) in EB5, TOK5. clear UPD.
    replace (md_addr dP) with (FB + 376) by (rewrite EP; clear; lia).
    assert (SI5 : SPINV h5 LB5 m5 (v + MPI_RB_PHI LEN) (f + MPI_RB_FR 0) dN dP' dA dB dX dY dZ p5 lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 (K + 1)).
    { split; [exact EB5|]. split; [exact TOK5|]. split; [exact EN|]. split; [rewrite EAD5; exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB5 EFB; lia| clear - C5 C24k; lia]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI2 PCELL EBr EB3r EB3 TOK3 OWN1.
    dpose SI5 as (EBsave & TOK & _). pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    assert (SCSk : crange (hcs asegs R HIA h5) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h5 LB _ LF m5 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h5) h5 _ LF m5 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h5 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h5) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR5; zify_cond KR5; [| eapply (sp_errbac h5 LB5 m5 _ _ dN dP' dA dB dX dY dZ p5 lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 (K + 1) r5);
        [exact SI5| clear - KR5 RR5; Z.div_mod_to_equations; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]].
    assert (RZ5 : r5 = 0) by (clear - KR5 RR5; Z.div_mod_to_equations; lia). subst r5. clear KR5.
    (* [comment removed for export] *)
    do 2 zstep.
    replace (FB + 376) with (md_addr dP') by (rewrite EAD5, EP; clear; lia).
    eapply (sp_query A_MPI_BITLEN_Q _ _ _ (A_mpi_bitlen_spec AL IMG) ltac:(clear; lia) h5 LB5 m5 _ _ _ _ _ dP' 0xafec0);
      [exact EBsave| exact TOK| inlist| exact I| clear; lia| reflexivity|].
    intros m6 pbv z0 z1 z2 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB6 TOK6 RPB. cbv beta in RPB.
    replace (md_addr dP') with (FB + 376) by (rewrite EAD5, EP; clear; lia).
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 288, [C8 (Z_to_bv 64 p5)]); (FB + 320, [C8 lnw]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj'])] _ _ EB6
                  ltac:(intros c Hc; clear - Hc; cbn [In] in Hc |- *; tauto)) as EBr.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EB6 (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EB6 (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as PBN.
    pose proof EB6 as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl ([(FB + 488, FB + 496)] : list ivl) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    assert (SCSk : crange (hcs asegs R HIA h5) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h5 LB _ LF m6 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA h5) h5 _ LF m6 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h5 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h5) as CSOKk.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    assert (OWN7 : Forall own_iv [(FB + 488, FB + 496)]) by (apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]).
    pose proof (eb_own h5 LB5 m6 _ _ _ _ _ _ _ m7 [(FB + 488, FB + 496)] EBr MU ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) WM MIk STb ltac:(ch_dj)) as EB7r.
    pose proof (eb_ch_add _ _ _ _ _ _ _ _ _ _ _ _ EB7r PBN ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as EB7a.
    pose proof (eb_ch_incl _ _ _ _ _ _ _ _ [(FB + 288, [C8 (Z_to_bv 64 p5)]); (FB + 320, [C8 lnw]); (FB + 352, [C4 vw; C4 vw']); (FB + 32, [CB 192 jref]); (FB + 624, [C4 gid; C4 gj']); (FB + 488, [C8 (Z_to_bv 64 pbv); C8 nb])] _ _ EB7a
                  ltac:(intros c Hc; clear - Hc; cbn [In] in Hc |- *; tauto)) as EB7.
    assert (TOK7 : tmp_ok asegs m7 LB5 G 192 (DS7 dN dP' dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own h5 LB5 m6 m7 _ _ HH0' TOK6 MU WM MI0' MIk OWN7).
      intros d0 Hd.
      assert (XB3 : md_addr d0 + 16 <= G + 120).
      { cbn [In] in Hd. decompose [or] Hd; try contradiction; subst d0; rewrite ?EAD5, ?EN, ?EP, ?EA, ?EB', ?EX, ?EY, ?EZ; clear; lia. }
      cbn [disjoint_from]. split; [clear - XB3; lia| exact I]. }
    ddestruct SI5 as (_ & _ & EN5 & EP5 & _ & _ & _ & _ & _ & PB5' & C24k5).
    assert (SI7 : SPINV h5 LB5 m7 (v + MPI_RB_PHI LEN) (f + MPI_RB_FR 0) dN dP' dA dB dX dY dZ p5 lnw vw vw' jref gid gj' (Z_to_bv 64 pbv) nb v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 (FB + 320)) (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 (K + 1)).
    { split; [exact EB7|]. split; [exact TOK7|]. split; [exact EN|]. split; [exact EP5|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|]. split; [exact PB5'| exact C24k5]. }
    assert (PRG : 0 <= p5 < 2^63 /\ 0 <= EF < 2^63) by (clear - BUF0 BP PB' PB5 PL B47 EFB LNB LNR; lia).
    zstep. if_cases KE; zify_cond KE.
    - assert (PE : p5 = EF) by (clear - KE PRG; lia). subst p5.
      eapply (stageA h5 LB5 m7 _ _ dN dP' dA dB dX dY dZ EF lnw vw vw' jref gid gj' (Z_to_bv 64 pbv) nb v1 v2 v3 v4 v5 v6 v7 v16 v17 v18 (K + 1));
        [exact SI7| clear - K0; lia| exact XNULL| exact NY| exact NZ| clear - VB; lia| clear - FB'; lia].
    - (* [comment removed for export] *)
      do 3 zstep.
      eapply (sp_err94c h5 LB5 m7 _ _ dN dP' dA dB dX dY dZ p5 lnw vw vw' jref gid gj' (Z_to_bv 64 pbv) nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 (K + 1) (-15718));
        [exact SI7| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
    all: match goal with |- ?g => idtac "F2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01E0@D46719952988.249D46719952988.253D50014262098.249D50014262098.253L11511961495.8  L12114880880.242L12469921329.0  L14906048793.266L14987706775.8  L15318568088.2  L15653086487.8  L16507500205.6  L1685717371.0   L18909959449.266L21868500043.2  L22409920380.239L2263936207.5   L22775362903.3  L27934866982.6  L28877807824.11 L29010569984.263L29745045590.287L30195494665.2  L35668120898.7  L36607162391.8  L36650016793.10 L38309573212.8  L40065549985.0  L41976525601.0  L42128420922.11 L42851534655.7  L44011663895.8  L45042902588.2  L46126591772.2  L46441115929.242L49379278409.0  L51390623401.0  L51543886882.6  L54992078076.242L58227785239.8  L58711294999.8  L60098763854.3  L6104554736.239 L61900301956.0  L66151426447.10 L7293583127.8   L7735748552.2   P21870859916.249P21870859916.253P45032678651.249P45032678651.253P7750690063.250 P7750690063.253 Q11801279589.249Q11801279589.253Q13396272694.249Q15224234932.273Q20580512354.249Q20580512354.253Q20612386219.249Q22712450012.249Q22712450012.253Q24130372517.273Q24251258485.249Q24251258485.252Q25513505925.249Q25513505925.252Q3203240366.247 Q3203240366.250 Q3579455898.249 Q41266003573.246Q41833502603.249Q48228611493.273Q49698585326.248Q49698585326.251Q52389960886.249Q52389960886.253Q54967541497.250Q58768111688.250Q58768111688.253Q66954699982.250Q66954699982.253Q6912046254.250 Q7381417448.246 Q7712730548.273 00002G04^06h0920960:E0:F0;M0;Q0;X0;\0<00<10=80=90>H0>Z0>f0?:0?_0?`0?a0?i0@@0@D0@V0A60A70A80A`0B60B:0B;0BB0CQ0CR0CS0Cd0E30E70E;0EE0FT0FU0Ff0Fj0Fk0He0J[0LU0NK0Om0QK0Rf0T=0UY0VY0VZ0V[0Wm0YO0Zm0[m0]\0_G0`l0bM0c]0dm0f10gC0hG0iG0jX0ki0m`0oS10n12I13`15;16R17m19I1:IS1R3HIA5NEEDR1h2LF2sp3PKA2lo3SLO3TOP2FB3sp13SP13LFB3NZP2bs2hk2v12v22v32v42v52v62v73s643s723s803v163v173v183ETk4NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS1R3HIA5NEEDR1h2LF2sp3PKA2lo3SLO3TOP2FB3sp13SP13LFB3NZP2bs2hk2v12v22v32v42v52v62v73s643s723s803v163v173v183ETk4NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3sp13SP13LFB3NZP2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2F04FBLO4SP1R3NER2HB5Ha_st5Hl_stS2FBS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2FBS1r3RR3S2FBS3LEN1P1p3PB'2p33PB3SS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLFS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS3LEN1P2p32L34LB3'S2p32L34LNR3S3LEN1P1p3PB'2p33PB3S3LEN1P1p3PB'2p32L33PB32EF3EFB2p43PB4FFS2r43RR4S1R3HIA1h2sp2lo3TOP3HT0S2FBS2r43RR41r3KR41q1HS1R5NEEDR2sp2lo3sp13SP14SLO13NERSSS1R5NEEDR2lo2FB3sp14FBLO4SLO13NER2d03XB2S3LEN1v2VB3TV13RB03GP0S2FBFS3LEN1PS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLSSS1d1f3FB'3TF13RF0S2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS2FBS2FBS1R2lo3LOSS2LF2sp3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLSS1r3RR32r02KR1q1HS2FBFS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4FBLO3NER2HB5Ha_st5Hl_stS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4SLO13NERS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLFFS2LF2sp2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4SLO13NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4SLO13NER2HB5Ha_st5Hl_stS2LF2sp3PKA2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2sp2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4SP1R2HBS2LF2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4SP1R2HBS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS2LF2sp2lo2FB3sp13SP13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS2LF2FB3LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSLS2LF2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_stS2LF2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_stS1R5NEEDR2LF3PKA2lo3LOS2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3ALO4SLO13NER2HB5Ha_st5Hl_stS1R5NEEDR2LF2lo3LOS2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL3ALO4SLO13NER2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS1R5NEEDR2LF2lo2FB3sp13LFB2bs2v12v22v32v42v52v62v73s643s723s803v163v173v184NSH'3NSL4SLO13NERS2LF3PKA2FB3LFB2bs2v12v22v32v42v52v62v73s643v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE D0 PFREE HGF HGL IDSN HGI HIDL BUF bs HBS0 BUF0 B47 CRB DSB DBI OBUF0 BP PL LEN0 HRB HGM BSNE HLSET UWC0 HGT MCI SLOB"] Lemma stageF1 : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_D2 ()) "Phk,(0.$1.VR,VHIA,)PLBk,(2.$3.)Pmk,P,(4.&40.)(5.(4.&8.))Pv,$6.Pf,$6.PdN,$7.PdP,$7.PdA,$7.PdB,$7.PdX,$7.PdY,$7.PdZ,$7.Pp,$6.Plnw,(4.&40.)Pvw,(4.&40.)Pvw',(4.&40.)Pjref,(2.(4.&8.))Pgid,(4.&40.)Pgj',(4.&40.)Ppb,(4.&40.)Pnb,(4.&40.)Pv1,(4.&40.)Pv2,(4.&40.)Pv3,(4.&40.)Pv4,(4.&40.)Pv5,(4.&40.)Pv6,(4.&40.)Pv7,(4.&40.)Ps64,(4.&40.)Ps72,(4.&40.)Ps80,(4.&40.)Pv16,(4.&40.)Pv17,(4.&40.)Pv18,(4.&40.)PK,$6.Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0v,(4.&40.)Pa1,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ps10v,(4.&40.)P,(8.VR,VHIA,VIDONE,VIDS,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vlo,VFB,Vsp1,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)P,(;.R12.=)P,(25.$26.(27.R2<.)$28.)P,(;.(22.R2<.)+1.)P,(;.(22.R2<.)+1.)P,(;.(:.(:.(:.R35.(23.+5.(>.VLEN,)))(23.+2.(24.+1.)))$?.)(10.VLEN,))P,(;.(:.(:.(:.R35.(23.+5.(11.=)))+6.)$12.)(13.Vd,))(14.$1.(15.$1.VR,VHIA,R3:.Vmo0,)(16.$1.VR,VHIA,$17.$18.$19.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(1:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(1;.(1<.R17.(9.&40.Vsp1,)Vgp,Vtp,R16.R15.R14.Vsp,(9.&40.Vsp1,)R13.R12.(9.&40.(:.VFB,+1=8.))R11.R10.R?.R>.R=.(9.&40.VFB,)(9.&40.(:.VFB,+120.))(9.&40.(:.(1=.VFB,+3.)(1>.(1?.VR,))))(9.&40.(1>.(1?.VR,)))(9.&40.(:.VP,VLEN,))(9.&40.(:.VFB,+160.))(9.&40.VPKA,)(9.&40.VFB,)R8.(9.&40.(:.VFB,+170.))R<.R;.R:.R9.)VF,(9.&40.+:?;>0.)Vfc,(20.(4.&40.))R38.(21.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SI K0 XNULL NY NZ VB FB'.
    dpose SI as (EBsave & TOK & EN & EP & EA & EB' & EX & EY & EZ & PB' & C24k).
    dpose tail_nonneg as (TV0 & TF0 & TV1 & TF1 & RB0 & RF0 & GP0).
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_intror (or_introl eq_refl)))) as VCELL.
    pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([(sp1 + 8, sp1 + 152)] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF mk FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF mk FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    unfold A_pk_ecparams_D1.SLP in SLOTS.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (eb_slots hk LBk mk v f _ _ _ _ _ _ m1 EBsave MU WM ltac:(assumption) SLOTS eq_refl) as EB1.
    assert (TOK1 : tmp_ok asegs m1 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk mk m1 _ _ HH0' TOK MU WM MI0' ltac:(assumption)).
      - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_nil].
      - intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO SLO1 NER NEEDR; lia| exact I]. }
    assert (SI1 : SPINV hk LBk m1 v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 s72 (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB1|]. split; [exact TOK1|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact PB'| exact C24k]. }
    (* [comment removed for export] *)
    do 4 zstep. if_cases KV.
    2: { (* [comment removed for export] *)
      do 3 zstep.
      eapply (sp_err hk LBk m1 _ _ dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ _ v16 v17 v18 K (-15616));
        [exact SI1| clear; lia| clear; lia| clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia]. }
    clear KV.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    pose proof (eb_slots hk LBk mk v f _ _ _ _ _ _ m2 EBsave MU WM ltac:(assumption) SLOTS eq_refl) as EB2.
    assert (TOK2 : tmp_ok asegs m2 LBk G 192 (DS7 dN dP dA dB dX dY dZ)).
    { ddestruct EBk0 as (HH0' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0' & _).
      eapply (tmp_ok_own hk LBk mk m2 _ _ HH0' TOK MU WM MI0' ltac:(assumption)).
      - apply Forall_cons; [right; right; cbn [fst snd]; clear - SP1 SLO1 NER NEEDR; lia| apply Forall_nil].
      - intros d0 Hd. ddestruct TOK as (_ & T2 & _). pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & XB1 & XB2). cbn [disjoint_from]. split; [clear - XB1 XB2 FBLO SLO1 NER NEEDR; lia| exact I]. }
    assert (SI2 : SPINV hk LBk m2 v f dN dP dA dB dX dY dZ p lnw vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB2|]. split; [exact TOK2|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact PB'| exact C24k]. }
    (* [comment removed for export] *)
    do 6 zstep.
    eapply (sp_gettag hk LBk m2 v f _ _ (DS7 dN dP dA dB dX dY dZ) p PEND 48 0xafc1c lnw);
      [exact EB2| exact TOK2| exact (proj1 PB')| exact (proj2 PB')| clear; lia| ch_dj| clear; lia| reflexivity|].
    intros m3 r p3 L3 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB3 TOK3 PB3 RR3 ROK3.
    assert (SI3 : SPINV hk LBk m3 v f dN dP dA dB dX dY dZ p3 L3 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB3|]. split; [exact TOK3|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB3; lia| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI SI1 SI2 EB1 TOK1 EB2 TOK2 VCELL.
    dpose SI3 as (EBsave & TOK & _). pose proof EBsave as EBk.
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m3 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m3 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { eapply (sp_err948 hk LBk m3 _ _ dN dP dA dB dX dY dZ p3 L3 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K r);
        [exact SI3| clear - RR3; lia| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      intros ->; clear - KR; first [apply KR; reflexivity| (vm_compute in KR; congruence)]. }
    assert (RZ : r = 0) by (clear - KR RR3; Z.div_mod_to_equations; lia). subst r. clear KR. destruct (ROK3 eq_refl) as (PG3 & LB3'). clear ROK3.
    pose proof (bv_unsigned_in_range 64 L3) as LNR3. change (bv_modulus 64) with (2^64) in LNR3.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_introl eq_refl)) as PCELL.
    pose proof (eb_ch_get _ _ _ _ _ _ _ _ _ _ _ _ EBsave (or_intror (or_introl eq_refl))) as LCELL.
    (* [comment removed for export] *)
    do 8 zstep.
    set (EF := p3 + bv_unsigned L3) in *.
    assert (EFB : EF <= PEND) by (unfold EF; clear - LB3'; lia).
    eapply (sp_gettag hk LBk m3 v f _ _ (DS7 dN dP dA dB dX dY dZ) p3 EF 6 0xafc40 L3);
      [exact EBsave| exact TOK| clear - PB' PB3; lia| unfold EF; clear - LNR3; lia| exact EFB| ch_dj| clear; lia| reflexivity|].
    intros m4 r4 p4 L4 z0 z1 z2 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB4 TOK4 PB4 RR4 ROK4.
    assert (SI4 : SPINV hk LBk m4 v f dN dP dA dB dX dY dZ p4 L4 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 (Z_to_bv 64 (FB + 472)) (Z_to_bv 64 PKA) v16 v17 v18 K).
    { split; [exact EB4|]. split; [exact TOK4|]. split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [clear - PB' PB3 PB4 EFB; lia| exact C24k]. }
    try clear EBk0. try clear HHk. try clear ETk. try clear ESk. try clear EFk. try clear HCSk. try clear HVk. try clear HFk. try clear FHD. try clear FSH. try clear NSH'. try clear FSHR. try clear SAVE. try clear SLOTS. try clear NSL. try clear STlo. try clear SThi. try clear STb. try clear PRES. try clear CHk. try clear EXTk. try clear FRk. try clear LAWS. try clear KINV. try clear MU. try clear WM. try clear SCSk. try clear FRSHk. try clear CFBk. try clear INF. try clear INH. try clear IND. try clear AP. try clear SBND. try clear APS. try clear WLk. try clear CSOKk. try clear MIk. try clear IDSk. try clear w0 w1 w2.
    clear EBsave TOK SI3 PCELL LCELL.
    pose proof SI4 as (EBk & _).
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA hk LB _ LF m4 FB 1024 FRSH HHk) as FRSHk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk _ LF m4 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA hk _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    (* [comment removed for export] *)
    zstep. if_cases KR4; zify_cond KR4.
    - assert (RZ4 : r4 = 0) by (clear - KR4 RR4; Z.div_mod_to_equations; lia). subst r4. clear KR4. destruct (ROK4 eq_refl) as (PG4 & LB4').
      eapply (stageF2 hk LBk m4 _ _ dN dP dA dB dX dY dZ p4 L4 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 s64 v16 v17 v18 K EF);
        [exact SI4| exact LB4'| exact EFB| exact K0| exact XNULL| exact NY| exact NZ| exact VB| exact FB'].
    - eapply (sp_err948 hk LBk m4 _ _ dN dP dA dB dX dY dZ p4 L4 vw vw' jref gid gj' pb nb v1 v2 v3 v4 v5 v6 v7 _ v16 v17 v18 K r4);
        [exact SI4| clear - RR4; lia| | clear - VB TV0 TV1 RB0 GP0; lia| clear - FB' TF0 TF1 RF0; lia].
      intros ->; clear - KR4; first [apply KR4; reflexivity| (vm_compute in KR4; congruence)].
    all: match goal with |- ?g => idtac "F1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.
End WalkEP.
