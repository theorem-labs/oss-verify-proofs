(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_cmp P_mpi_shift_l.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_core_bitlen A_mpi_core_shift_l.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_shift_l.
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
Ltac2 gd_tbl_A_mpi_shift_l_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_c24.mpi_xop_stmtA_c"; "C24_SHIFT_L_c"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_l.shift_l_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_l.shift_l_FR"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_shift_l.shift_l_R"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_shift_l.shift_l_n"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SHIFT_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_l.A_WRAP_CALLOC_SL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_l.A_ASAN_MEMCPY_SL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_shift_l.A_ASAN_MEMSET_SL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "mpi_shift_l_stmtA_c"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_MEMSET_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"].



(* [comment removed for export] *)

Definition C24_SHIFT_L_c : Z := 1.
Definition mpi_shift_l_stmtA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "(0.O4.O3.O2.O1.+80.$1.Lc,$2.(3.(4.=R1.)(4.R1.(5.+2.+20.)))$6.L,$2.$7.LLB,(8.$9.)LdX,$:.Lc,$2.Lr,$2.LdX',$:.(;.R3.R4.R5.R2.R1.))")
(* [comment removed for export] *).


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_SL.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_SL.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_SL.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Hypothesis C24H : cnt24 LB + C24_SHIFT_L_c <= C24MAX.     (* [comment removed for export] *)
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sgX nX pX : Z) (xs : list word) (padX : word) (ownX : limb_own)
            (count lo : Z).
  Local Notation dX := (mkMPD X sgX nX pX xs padX ownX).
  Hypothesis MAX : mpd_at asegs m LB dX.
  Hypothesis NST : ownX <> LStatic.
  Hypothesis CNT : 0 <= count <= 2^32.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis DSP : ownX <> LNull -> pX + 4 * nX <= lo \/ bv_unsigned sp <= pX.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 128 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHX10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Notation FRAME := ([C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).   (* [comment removed for export] *)
  Notation POST mo := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                         (fun r dX' => shift_l_R count dX LB r dX') (shift_l_PHI dX count) shift_l_FR lo m mo).
  Notation bits := (core_bitlen xs nX).

  Ltac basic_facts hc LBc mm HH TOPc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0; pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L16569611521.6L45374877858.6L60457527992.6L61462073826.6L63306560470.2L63308723164.600000?00E00R00a00i016S1X2nX2xs2XB2BRS1X2XBS1X2nX3NRX2XBS1X2nX2xs2XB2BRS2nX3NRXS1X2nX3NRX2XB". (* [comment removed for export] *)
  #[using="LB m pX padX ownX MAX"] Lemma facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "(3.(<.$2.(=.VX,+8.)=)(3.(>.=VX,)(3.(<.$2.(?.(10.(11.&40.)Vxs,))VnX,)(3.(3.(4.=VnX,)(4.VnX,+2710.))(3.(12.(<.$2.VsgX,+1.)(<.$2.VsgX,-1.))(3.(4.(13.VX,+10.)(5.+2.+40.))(3.(4.=(14.Vxs,VnX,))(4.(14.Vxs,VnX,)(15.+20.VnX,)))))))))")
(* [comment removed for export] *).
  Proof.
    ddestruct MAX as [[CHX (XAL & X0 & LENX & NRX & _)] SGX]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold MPI_MAX_LIMBS in NRX.
    pose proof (rw_cells_bound _ _ _ _ CHX) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (core_bitlen_range xs nX ltac:(clear - NRX; lia)) as BR.
    repeat split; try assumption; clear - XB NRX BR; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L12283411672.100L14106684376.100L29428324939.5  L35653441506.7  L36423571333.99 L41288976216.100L44866992728.100L48429268312.100L49345641752.98 L5145216728.100 L60098763854.3  L67158371251.100L8722184664.100 Q15641568614.99 Q18364007270.99 Q21877861637.99 Q27904925317.99 Q31269115878.99 Q32653586022.99 Q33915848709.99 Q36423571333.99 Q3832210565.99  Q39941338501.99 Q41154176102.99 Q44650594790.99 Q51233520870.99 Q59840699110.99 Q66523986693.99 Q9840924165.99  00000700>00P00j01D01K01R01Y01`01g02102802?02F02M02`03303:03A03T03g04:04M04T04[04b04i05<05OS2ra2spS2ra2spS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS1R5NEEDR2ra2sp2lo3SLO3SPRS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1R2lo3LOSS2ra2spS2ra2spS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Phc,(16.$17.VR,VHIA,)PLBc,(8.$9.)Pmm,P,(11.&40.)(18.(11.&8.))Pr,$2.Pxra,(11.&40.)Pxs0,(11.&40.)Pxs1,(11.&40.)Pxs2,(11.&40.)Pxs3,(11.&40.)Pxs4,(11.&40.)Pxs5,(11.&40.)Pxs6,(11.&40.)Pxt0,(11.&40.)Pxt1,(11.&40.)Pxt2,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Pxt3,(11.&40.)Pxt4,(11.&40.)Pxt5,(11.&40.)Pxt6,(11.&40.)P,(19.$17.VR,VHIA,R1:.R19.VLF,R18.)P,(4.(1:.&40.Vsp,)(1;.$17.VR,VHIA,R1;.))P,(1<.$17.R1:.(13.(1:.&40.Vsp,)-40.)(1=.$1>.(1?.Vs6,)(1=.$1>.(1?.Vs5,)(1=.$1>.(1?.Vs4,)(1=.$1>.(1?.Vs3,)(1=.$1>.(1?.Vs2,)(1=.$1>.(1?.Vs1,)(1=.$1>.(1?.Vs0,)(1=.$1>.(1?.Vra,)(20.$1>.))))))))))P,(21.$17.R1;.Vlo,(13.(1:.&40.Vsp,)-40.))P,(22.$17.R1<.)(23.$17.(24.VR,)(25.$17.VR,VHIA,R1?.)Lms',$26.(27.(11.&40.)Lx5,(11.&40.)(27.(11.&40.)Lx6,(11.&40.)(27.(11.&40.)Lx7,(11.&40.)(27.(11.&40.)La1',(11.&40.)(27.(11.&40.)La2',(11.&40.)(27.(11.&40.)La3',(11.&40.)(27.(11.&40.)La4',(11.&40.)(27.(11.&40.)La5',(11.&40.)(27.(11.&40.)La6',(11.&40.)(27.(11.&40.)La7',(11.&40.)(27.(11.&40.)Lx28,(11.&40.)(27.(11.&40.)Lx29,(11.&40.)(27.(11.&40.)Lx30,(11.&40.)(27.(11.&40.)Lx31,(11.&40.)(3.(<.$26.R?.(28.(29.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(2:.&40.R2;.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(2;.Vra,)Vfc,(2<.(11.&40.))R2<.(2=.$17.)))(21.$17.R2<.Vlo,(1:.&40.Vsp,)))))))))))))))))(28.(29.R1;.(2:.&40.(13.(1:.&40.Vsp,)-40.))Vgp,Vtp,R13.R12.R11.R1:.R19.(2:.&40.R1<.)R10.R?.R>.R=.R<.R;.R:.R18.R17.R16.R15.R14.Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(2:.&40.+9=5;8.)Vfc,(2<.(11.&40.))R1=.(2=.$17.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc FR ST MI. basic_facts hc LBc mm HH TOPc.
    (* [comment removed for export] *)
    do 8 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308585216.3000008S1A1a2Ha". (* [comment removed for export] *)
  #[using="Type"] Lemma aobj_nil : forall (CSx : Z -> Prop) mm A, aobj asegs AL CSx mm A 0.
  Proof. intros. split; intros a Ha; exfalso; clear - Ha; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01_0@C17025492443.146C22016567563.147D38851507912.147D56475227919.147D5935508270.147 D60109446735.147K1153798179.146 K30786211471.147K36719207456.146K51736254456.147K61296927462.147L1147801049.4   L122502667.5    L122617647.6    L12283411672.143L124385309.5    L14106684376.143L18293330070.2  L23100341967.119L25567039905.0  L27157548066.7  L29428324939.5  L30801551019.3  L33087595724.2  L33421456805.5  L33421456805.6  L33422108226.6  L33424109123.9  L33424138608.7  L33434758949.5  L35653441506.7  L36438368167.147L36715738693.2  L39024900935.2  L39025161296.3  L39025341812.4  L39025375815.7  L39026979398.3  L41288976216.143L44866992728.143L46160487540.119L4786890204.6   L4786924271.9   L4787747164.5   L4787747164.6   L4789183214.5   L4793052101.6   L48107366172.3  L48429268312.143L49343544635.146L50498683023.7  L5145216728.143 L51731989917.3  L52320026445.3  L52324671757.4  L52326835775.2  L60098763854.3  L60237119186.4  L60237201398.2  L61291069212.3  L61929758668.2  L67158371251.143L8722184664.143 N6320619906.147 N8683170676.147 O17025492443.146O18850355132.147O22016567563.147O57399310481.147O67820358977.146P30786211471.147P36719207456.146Q12370813529.122Q15647485252.147Q17207350632.123Q18361764676.147Q21892392231.147Q26207421841.123Q26207721832.124Q26220303701.121Q27911362215.147Q30987168515.126Q31258976196.147Q31654082872.123Q32659531332.147Q33913831463.147Q36438368167.147Q37621080759.121Q38248387216.147Q3834391719.147 Q38851507912.147Q39212284437.124Q39935458727.147Q41139579972.147Q43879899724.147Q43925228937.124Q44652874180.147Q47243923986.122Q51223442628.147Q5473021098.121 Q5485174314.122 Q5485600919.123 Q5935508270.147 Q59830588100.147Q60511567613.124Q60697995187.124Q6143569392.122 Q66534617895.147Q8885007881.121 Q9534282490.121 Q9839205927.147 00000100200F00i01;01V02P02Q02R03M04U04V04W04X05:05;05]05d06606706H06Z06[06a06b06c06d06e06f07807R08Q08R08Z08[08\08]08^09@09b0::0:;0:<0:=0:>0:?0:O0:Z0;<0;^0<40<V0<W0<X0<Y0<_0<i0<j0=50=60=<0=^0>@0>T0>h0>i0>j0>k0>l0>m0>n0>o0?H0?^0?h0@>0@`0@j0A40A>0A`0BJ0B`0Bj0C@0Cb0DD0DN0DY0E;0EG0EQ0F30FI0FW0Fa0G70G80GN0GX0Gb0Gl0H60HL0HT0Ha0Hk0IM0IW0I_0JAFFS2ra2sp1X2xs1p1n3xs0S1R3HIA2ra2sp1X2xs2lo2hc1p3xs04TOPcS2ra2sp1X2xs1p3xs0S1R2ra2sp1X2xs2lo3LOS1p3xs0S1R3HIA2LF2sp2xs5count2lo2hc3LBc1p1n3xs03x144DSP'3x154POSTFFS1R3HIA2LF2sp1X2xs5count2lo2hc3LBc1p1n3xs03x143DSX3x154POSTS1R3HIA5NEEDR2LF2sp2xs5count2lo3CNT3SLO2hc3LBc1p1n3xs03x144DSP'3x154POSTFFFS2ra2sp1X2xs5count1p1n3xs03x153PC0FS2ra2sp1X2xs5count1p1n3xs03x153PC0S2sp2loS2ra2sp1X2xs1p3xs0SS1R2sp2lo3SLO3NRAS1R2lo3LOS3ALO3ACPFS1n2HnFFFFFS1R3HIA2sp2hc4TOPcS1R3HIA2sp2lo2hc4TOPc4HTOPS1R5NEEDR2ra2sp1X2xs5count2lo3CNT3SLO1p1n3xs02PB3SPR2X03x153PC0FS2sp3SPAFFFFS2ra2sp1X2xs5count1p1n3xs03x153PC0S2ra2sp1X2xs5count1p1n3xs03x153PC0S2ra2sp1X2xs1p3xs02X02XBFFFFFS2sp2lo1p1n4DSP'S1n3xs03LL0S2ra2sp1X2xs5count1p1n3xs03x153PC0S2ra2sp1X2xs5count1p1n3xs03x153PC0S2sp1X2lo1p1n4DXP'3DSXS2ra2sp1X2xs5count1p1n3xs03x153PC0FFFS1p2PBS1R2lo3LOSFS5count3CNTFS1n2HnS2ra2sp1X2xs5count1p1n3xs03x153PC0S2ra2sp1X2xs5count1p1n3xs03x153PC0S2sp2xs2lo3xs03x161CS2sp2xs2lo3xs03x161CFFFFFFFS2ra2sp1X2xs1p3xs03XAL2X0S2sp2xs2lo3xs03x153PC0S1X2xs3xs0S2sp2xs2lo3xs03x153PC0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0S1X2xs3xs0S1X2xs3xs0S1X2xs3xs0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0S1R5NEEDR2sp2xs2lo3LOS3SLO3xs03ALO3ACP3SPRS2sp2xs2lo3xs03x153PC0S1X2xs3xs0S2sp2xs2lo3xs03x153PC0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0S1X2xs3xs0S2xs2lo3xs0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0S2xs1p1n3xs0S1X2xs3xs0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0S2sp2xs2lo3xs03x153PC0S2sp2xs2lo3xs0S1X2xs3xs0S2sp2xs2lo3xs03x153PC0FS2sp2xs2lo3xs03x153PC0S1X2xs3xs0S1X2xs3xs0S1X2xs3xs0S2xs1p3xs0S2sp2xs2lo3xs03x153PC0S2xs3xs0S1X2xs3xs02X0S1X2xs3xs0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0S1X2xs3xs0S2xs3xs0S1R5NEEDR2sp2xs2lo3SLO3xs03x153PC0". (* [comment removed for export] *)
  #[using="IMG AMS NEEDR NEEDA LB m nX pX xs ownX MAX CNT LOS SLO SPA"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Phc,(16.$17.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(11.&40.)(18.(11.&8.))Pp,$2.Pn,$2.Pxs0,(8.(11.&40.))Pxra,(11.&40.)Pxt0,(11.&40.)Pxt1,(11.&40.)Pxt2,(11.&40.)Pxa0,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Pxs3,(11.&40.)Pxs4,(11.&40.)Pxt3,(11.&40.)Pxt4,(11.&40.)Pxt5,(11.&40.)Pxt6,(11.&40.)P,(19.$17.VR,VHIA,R18.R17.VLF,R16.)P,(<.$2.(1;.$17.VR,VHIA,R19.)(1;.$17.VR,VHIA,Vh,))P,(4.(1:.&40.Vsp,)(1;.$17.VR,VHIA,R1:.))P,(1<.$17.R19.VX,(2>.R18.(2:.&40.VsgX,)R17.VpadX,))P,(2?.$17.R1:.R19.R17.)P,(<.$2.(?.(10.(11.&40.)R18.))R19.)P,(3.(4.=R1:.)(4.R1:.+2710.))P,(<.$2.(=.R1<.+4.)=)P,(12.(<.$2.R1<.=)(>.=R1=.))P,(3.(4.=R1>.)(>.R1>.(5.+2.+40.)))P,(12.(4.(13.R1?.(15.+4.R1>.))Vlo,)(4.(1:.&40.Vsp,)R1?.))P,(30.(31.VR,)(32.$9.R22.(33.VLF,))(34.VR,)(1;.$17.VR,VHIA,R23.)R20.(15.+4.R1?.))P,(35.$17.(24.VR,)(25.$17.VR,VHIA,R24.)R22.VX,+10.)P,(35.$17.(24.VR,)(25.$17.VR,VHIA,R25.)R23.R22.(15.+4.R21.))P,(12.(4.(13.VX,+10.)R23.)(4.(13.R23.(15.+4.R22.))VX,))P,(12.(4.(13.VX,+10.)Vlo,)(4.(1:.&40.Vsp,)VX,))P,(1<.$17.R26.(13.(1:.&40.Vsp,)-40.)(1=.$1>.(1?.Vs6,)(1=.$1>.(1?.Vs5,)(1=.$1>.(1?.Vs4,)(1=.$1>.(1?.Vs3,)(1=.$1>.(1?.Vs2,)(1=.$1>.(1?.Vs1,)(1=.$1>.(1?.Vs0,)(1=.$1>.(1?.Vra,)(20.$1>.))))))))))P,(21.$17.R27.Vlo,(13.(1:.&40.Vsp,)-40.))P,(22.$17.R28.)(23.$17.(24.VR,)(25.$17.VR,VHIA,R2;.)Lms',$26.(27.(11.&40.)Lx5,(11.&40.)(27.(11.&40.)Lx6,(11.&40.)(27.(11.&40.)Lx7,(11.&40.)(27.(11.&40.)La1',(11.&40.)(27.(11.&40.)La2',(11.&40.)(27.(11.&40.)La3',(11.&40.)(27.(11.&40.)La4',(11.&40.)(27.(11.&40.)La5',(11.&40.)(27.(11.&40.)La6',(11.&40.)(27.(11.&40.)La7',(11.&40.)(27.(11.&40.)Lx28,(11.&40.)(27.(11.&40.)Lx29,(11.&40.)(27.(11.&40.)Lx30,(11.&40.)(27.(11.&40.)Lx31,(11.&40.)(27.P,(11.&40.)(18.(11.&8.))Lm',P,(11.&40.)(18.(11.&8.))(27.(8.(11.&40.))Lxs',(8.(11.&40.))(3.(<.$26.R11.(28.(29.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,(2:.&40.=)R=.R<.R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(2;.Vra,)Vfc,(2<.(11.&40.))R2.(2=.$17.)))(3.(36.(1=.(37.$2.$2.)(38.$2.$2.R39.(13.R39.(15.+4.R38.)))(1=.(37.$2.$2.)(38.$2.$2.Vlo,(1:.&40.Vsp,))(20.(37.$2.$2.))))R3:.R2.)(3.(39.$17.R3:.R2.)(3.(22.$17.R2.)(3.(2?.$17.R2.R39.R1.)(3.(<.$3:.(10.(11.&40.)R1.)(10.(11.&40.)R37.))(3.(<.$2.(3;.R1.R38.)(=.(15.(3;.R37.R38.)(5.+2.Vcount,))(5.+2.(15.+20.R38.))))(3.(1<.$17.R2.VX,(2>.R39.(2:.&40.VsgX,)R38.VpadX,))(3.(21.$17.R2.Vlo,(1:.&40.Vsp,))(19.$17.VR,VHIA,R3<.R3;.VLF,R2.))))))))))))))))))))))))))(28.(29.R25.(2:.&40.(13.(1:.&40.Vsp,)-40.))Vgp,Vtp,R24.R23.R22.(2:.&40.Vcount,)(2:.&40.VX,)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(2:.&40.(13.VX,+:.))R19.R18.(2:.&40.(13.(3<.VX,+3.)(3=.(24.VR,))))(2:.&40.(13.(3<.(13.VX,+:.)+3.)(3=.(24.VR,))))Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(2:.&40.+9=594.)Vfc,(2<.(11.&40.))R29.(2=.$17.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc HXS HXL LL0 Hn P4 NZP PB DSP' CWP OX OP DXP' DSX FR ST MI. basic_facts hc LBc mc HH TOPc.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & XB & BR).
    unfold mpi_cells in HXS.
    pose proof (munch_refl [(p, p + 4 * n); (lo, bv_unsigned sp)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj HXS I) as HXS0.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
      by (unfold zx16; rewrite !unsigned_lit by (clear - Hn; lia); rewrite Z.mod_small by (clear - Hn; lia); reflexivity).
    zstep. zstep.
    pose proof (munch_refl [(p, p + 4 * n); (lo, bv_unsigned sp)] mc) as MUX. pose proof (wmono_refl asegs mc) as WMX.
    pose proof (A_mpi_core_shift_l_spec R HIA IMG AMS NEEDA) as SPC. unfold mpi_core_shift_l_stmtA, A_MPI_CORE_SHIFT_L in SPC.
    callxA_sp (bv_unsigned sp + -64)
      (eapply SPC with (h := hc) (LB := LBc) (LF := LF) (X := p) (n := n) (cnt := count) (lo := lo) (xs := xs0);
       rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
       try eassumption; try reflexivity;
       first [ clear - LL0; lia
             | clear - CNT; lia
             | clear - PB; lia
             | unfold MPI_CORE_SHIFT_L_STACK_A; clear - LOS SLO NEEDR NRA; lia
             | clear - SPA; lia
             | rewrite LL0; clear - DSP' Hn; lia
             | clear - TOPc; lia
             | first [exact C24H | match goal with |- ?g => idtac "CSL-PRE-LEFT:" g end] ]).
    clear SPC.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CSL-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    destruct HXS0 as [HXS1 _].
    pose proof (rw_cells_transport asegs _ _ m5 _ _ HXS1 MUX WMX ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - DXP' DSX; lia)) as HXS5.
    (* [comment removed for export] *)
    zstep.
    do 8 zstep.
    zstep.
    release_frame FR ST5 (bv_unsigned sp).
    zstep.
    finish.
    all: try (unfold mpi_cells; exact HXS5).
    all: try eassumption.
    all: first [exact C24H | match goal with |- ?g => idtac "TW-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7864265218.1000004S2nX". (* [comment removed for export] *)
  #[using="NST"] Lemma post_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Pmo,$3>.Pmo',$3>.Ph',(16.$17.VR,VHIA,)Pm',P,(11.&40.)(18.(11.&8.))Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Px28,(11.&40.)Px29,(11.&40.)Px30,(11.&40.)Px31,(11.&40.)P,(22.$17.R?.)P,(21.$17.R10.Vlo,(1:.&40.Vsp,))P,(3?.R14.R13.)P,(40.$17.VR,(41.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(1:.&40.Vsp,)(34.VR,)(43.$17.VR,VHIA,Vh,)(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(20.(37.$2.$2.)))Vm,R12.)P,(<.$2.(1;.$17.VR,VHIA,R14.)(1;.$17.VR,VHIA,Vh,))P,(<.$2.(43.$17.VR,VHIA,R15.)(43.$17.VR,VHIA,Vh,))P,(<.$2.(44.$17.VR,VHIA,R16.)(44.$17.VR,VHIA,Vh,))P,(45.$17.VR,VHIA,R17.R18.)P,Px,$2.P,(25.$17.VR,VHIA,Vh,R1.)(25.$17.VR,VHIA,R1:.R2.)P,(4.(46.$17.VR,VHIA,R19.)(13.(46.$17.VR,VHIA,Vh,)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)))P,(4.(47.$17.VR,VHIA,R1:.)(13.(47.$17.VR,VHIA,Vh,)$7.))P,(19.$17.VR,VHIA,R1;.VLB,VLF,R1:.)P,(48.$17.R1;.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))(49.$17.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Lr,$2.LdX',$:.(;.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,R2.R1.)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)$7.Vlo,Vm,R1?.(4:.(28.(29.Vra,Vsp,Vgp,Vtp,R1;.R1:.R19.Vs0,Vs1,(2:.&40.$4;.)R18.R17.R16.R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(2;.Vra,)Vfc,(2<.(11.&40.))R1<.(2=.$17.))R1>.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH MA.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB, dX, MBEDTLS_ERR_MPI_ALLOC_FAILED.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [apply mpd_out_refl; cbn [md_own]; exact NST|].
    split; [intros b Hb; left; exact Hb|].
    unfold shift_l_R, binop_keep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk].
    split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros b Hb; left; exact Hb| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L32688684787.300000>S3sgX2xs5count". (* [comment removed for export] *)
  #[using="Type"] Lemma post_shift : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Pmo,$3>.Pmo',$3>.Ph',(16.$17.VR,VHIA,)Pm',P,(11.&40.)(18.(11.&8.))PLB',(8.$9.)Pn',$2.Pp',$2.Pxs',(8.(11.&40.))Pown',$4<.Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Px28,(11.&40.)Px29,(11.&40.)Px30,(11.&40.)Px31,(11.&40.)P,(<.$2.R12.(4=.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))P,(<.$2.(4>.R11.)(15.(4>.Vxs,)(5.+2.Vcount,)))P,(4.VnX,R14.)P,(4?.(<.$4<.R12.$50.))P,(22.$17.R18.)P,(21.$17.R19.Vlo,(1:.&40.Vsp,))P,(3?.R1=.R1<.)P,(40.$17.VR,(41.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(1:.&40.Vsp,)(34.VR,)(43.$17.VR,VHIA,Vh,)(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(20.(37.$2.$2.)))Vm,R1;.)P,(<.$2.(1;.$17.VR,VHIA,R1=.)(1;.$17.VR,VHIA,Vh,))P,(<.$2.(43.$17.VR,VHIA,R1>.)(43.$17.VR,VHIA,Vh,))P,(<.$2.(44.$17.VR,VHIA,R1?.)(44.$17.VR,VHIA,Vh,))P,(45.$17.VR,VHIA,R20.R21.)P,Px,$2.P,(25.$17.VR,VHIA,Vh,R1.)(25.$17.VR,VHIA,R23.R2.)P,(4.(46.$17.VR,VHIA,R22.)(13.(46.$17.VR,VHIA,Vh,)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)))P,(4.(47.$17.VR,VHIA,R23.)(13.(47.$17.VR,VHIA,Vh,)$7.))P,(19.$17.VR,VHIA,R24.R22.VLF,R23.)P,(48.$17.R24.R23.(42.VX,VsgX,R22.R21.R20.VpadX,R1?.))P,(51.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)R24.(42.VX,VsgX,R23.R22.R21.VpadX,R20.))P,Pb,$9.P,(52.$9.R1.(53.(42.VX,VsgX,R25.R24.R23.VpadX,R22.)))(12.(52.$9.R2.(53.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(54.VR,(41.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(55.$2.$2.R2.)(56.$2.$2.R2.)))P,Pb,$9.P,(52.$9.R1.(53.(42.VX,VsgX,R26.R25.R24.VpadX,R23.)))(12.(52.$9.R2.(53.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(4?.(52.$9.R2.VLB,)))(49.$17.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Lr,$2.LdX',$:.(;.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,R2.R1.)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)$7.Vlo,Vm,R2;.(4:.(28.(29.Vra,Vsp,Vgp,Vtp,R22.R21.R20.Vs0,Vs1,(2:.&40.=)R1?.R1>.R1=.R1<.R1;.R1:.R19.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R18.R17.R16.R15.)VF,(2;.Vra,)Vfc,(2<.(11.&40.))R28.(2=.$17.))R2:.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HN HV Hnn NS' MI ST MF HP HT HS HFL HK HCS HVOL HFR HH MA MO FRA FRB.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB', (mkMPD X sgX n' p' xs' padX own'), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HVOL|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|]. split; [exact MO|].
    split; [exact FRA|].
    unfold shift_l_R, binop_keep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_val].
    split; [left; split; [reflexivity| split; [unfold mpd_val; cbn [md_sg md_limbs]; rewrite HV; clear; lia| split; [reflexivity| exact HN]]]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FRB| exact Hnn].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00X0@D24976250634.119D52014138856.119D52014138856.120D62155808737.120K43355168775.119K43355168775.120L23100341967.115L29428324939.5  L35653441506.7  L43361613547.2  L46160487540.114L49578233423.115L50790580594.6  L60098763854.3  Q12370813529.117Q17207353341.116Q24974040330.118Q26207421841.115Q26207721832.116Q26207967338.113Q31654082872.115Q37625275423.116Q39212284437.116Q42081808994.116Q43925228937.116Q52016320488.118Q52016320488.119Q5485174314.117 Q5485603330.116 Q6027349519.119 Q6027349519.120 Q60511567613.116Q60697995187.116Q6143569392.117 Q62157788641.119Q62965564504.117Q62965564504.118Q7891539809.117 Q8880503606.113 Q9538787269.113 00000N00l01J01h02V03D03P03b04<04=04O04[05205<05O05U05m06306906?06E06K06Q06]06c07;07S07Y07_08708O08S08\08b09:09L09^09j0:00:4S2ra2sp1X2xs2nb2HB5Ha_st5Hl_stS2ra2sp1X2xs2nb2HB5Ha_st5Hl_stS2ra2sp1X2xs2pn2HB5Ha_st5Hl_stS2ra2sp1X2xs2pn2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs2lo3SLO2nb3DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs2lo3SLO2pn3DSX2HB5Ha_st5Hl_stS2ra2sp1X2xsS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPFS2ra2sp1X2xs2X02XBS2ra2sp1X2xsS1R5NEEDR2sp2lo3LOS3SLOS1R2lo3LOSS2ra2sp1X2xs3XAL2X0S1X2xsS1X2xs2nb2HB5Ha_st5Hl_stS1X2xsS1X2xsS1X2xsS1X2xsS1X2xsS1X2xsS1X2xs2X02HBS1X2xsS1X2xs2nb2HB5Ha_st5Hl_stS1X2xs2pn2HB5Ha_st5Hl_stS1X2xsS1X2xsS1X2xs2nb2HB5Ha_st5Hl_stS1X2xs2pn2HB5Ha_st5Hl_stS2xsS1X2xs2X0S1X2xsS1X2xs2pn2HB5Ha_st5Hl_stS1X2xs2XB2HB5Ha_stS1X2xs2XB2HB5Ha_stS1X2xs2X02HBS1X2xsS2xs". (* [comment removed for export] *)
  #[using="IMG NEEDR LB m nX pX xs ownX MAX LOS SLO"] Lemma store_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Phc,(16.$17.VR,VHIA,)PLBc,(8.$9.)Pmm,P,(11.&40.)(18.(11.&8.))Ppw,$2.Pnw,$2.Ppn,$2.Pnb,$2.Pxra,(11.&40.)Pxt0,(11.&40.)Pxt1,(11.&40.)Pxt2,(11.&40.)Pxa0,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Pxt3,(11.&40.)Pxt4,(11.&40.)Pxt5,(11.&40.)Pxt6,(11.&40.)P,(19.$17.VR,VHIA,R17.R16.VLF,R15.)P,(<.$2.(1;.$17.VR,VHIA,R18.)(1;.$17.VR,VHIA,Vh,))P,(4.(1:.&40.Vsp,)(1;.$17.VR,VHIA,R19.))P,(12.(4.(13.VX,+10.)Vlo,)(4.(1:.&40.Vsp,)VX,))P,(3.(4.=R16.)(>.R16.(5.+2.+40.)))P,(3.(4.=R16.)(>.R16.(5.+2.+40.)))P,(1<.$17.R1;.VX,(2>.R1:.(2:.&40.VsgX,)R19.VpadX,))P,(30.(31.VR,)(32.$9.R1=.(33.VLF,))(1:.&40.Vsp,)(1;.$17.VR,VHIA,Vh,)VX,+10.)P,(35.$17.(24.VR,)(25.$17.VR,VHIA,R1?.)R1=.VX,+10.)P,(1<.$17.R1>.(13.(1:.&40.Vsp,)-40.)(1=.$1>.(1?.Vs6,)(1=.$1>.(1?.Vs5,)(1=.$1>.(1?.Vs4,)(1=.$1>.(1?.Vs3,)(1=.$1>.(1?.Vs2,)(1=.$1>.(1?.Vs1,)(1=.$1>.(1?.Vs0,)(1=.$1>.(1?.Vra,)(20.$1>.))))))))))P,(21.$17.R1?.Vlo,(13.(1:.&40.Vsp,)-40.))P,(22.$17.R20.)(23.$17.(24.VR,)(25.$17.VR,VHIA,R23.)Lms',$26.(27.(11.&40.)Lya0,(11.&40.)(27.(11.&40.)Lya1,(11.&40.)(27.P,(11.&40.)(18.(11.&8.))Lm',P,(11.&40.)(18.(11.&8.))(3.(<.$26.R4.(28.(29.R20.(2:.&40.(13.(1:.&40.Vsp,)-40.))Vgp,Vtp,R1?.R1>.R1=.(2:.&40.Vcount,)(2:.&40.VX,)R3.R2.R1:.R19.R18.R17.R16.R15.(2:.&40.(13.VX,+:.))(2:.&40.R21.)(2:.&40.R22.)(2:.&40.(13.(3<.VX,+3.)(3=.(24.VR,))))(2:.&40.(13.(3<.(13.VX,+:.)+3.)(3=.(24.VR,))))Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(2:.&40.+9=594.)Vfc,(2<.(11.&40.))R1.(2=.$17.)))(3.(36.(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(20.(37.$2.$2.)))R25.R1.)(3.(39.$17.R25.R1.)(3.(22.$17.R1.)(3.(1<.$17.R1.VX,(2>.R22.(2:.&40.VsgX,)R21.VpadX,))(3.(1<.$17.R1.(13.(1:.&40.Vsp,)-40.)(1=.$1>.(1?.Vs6,)(1=.$1>.(1?.Vs5,)(1=.$1>.(1?.Vs4,)(1=.$1>.(1?.Vs3,)(1=.$1>.(1?.Vs2,)(1=.$1>.(1?.Vs1,)(1=.$1>.(1?.Vs0,)(1=.$1>.(1?.Vra,)(20.$1>.))))))))))(3.(21.$17.R1.Vlo,(13.(1:.&40.Vsp,)-40.))(19.$17.VR,VHIA,R27.R26.VLF,R1.)))))))))))(28.(29.R1<.(2:.&40.(13.(1:.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.(2:.&40.Vcount,)(2:.&40.VX,)R18.R17.R16.R15.R14.R13.R12.R11.(2:.&40.(13.VX,+:.))(2:.&40.R1=.)(2:.&40.R1>.)(2:.&40.(13.(3<.VX,+3.)(3=.(24.VR,))))(2:.&40.(13.(3<.(13.VX,+:.)+3.)(3=.(24.VR,))))Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(2:.&40.+9=57<.)Vfc,(2<.(11.&40.))R21.(2=.$17.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc DSX PNB NBB HX CWc OX FR ST MI. basic_facts hc LBc mm HH TOPc.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & XB & BR).
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(X, X + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    finish.
    all: first [exact C24H | match goal with |- ?g => idtac "SW-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@C17025492443.142C17025492443.143C31740276271.144C45137625611.127D10717101146.127D37703787028.146D50796826103.127D51156380339.127D5472627854.127 D56475227919.146D60109446735.146D62012212072.127D65953674461.146D65971393419.127K25314459433.126K25897202343.144K49983523542.127K53686521785.126K61093937827.142K61093937827.143K7077216994.145 K7077216994.146 L17122876980.3  L17122882543.10 L22975979955.1  L25301413196.3  L25895494275.3  L28812073500.11 L28814050656.3  L28814059707.9  L29428324939.5  L35653441506.7  L44698194513.4  L49994140762.2  L50683188306.3  L53672239005.3  L60098763854.3  L60447830869.2  L61097676998.2  L61931765936.11 L65370080834.12 L65370090393.5  L65372075237.11 L66151427842.16 L6992860188.3   L7064965255.2   O17025492443.142O17025492443.143O17223163713.126O17919651190.145O17919651190.146O24425325148.127O27154552881.126O31740276271.144O49587672251.142O49587672251.143O5812554222.145 O5812554222.146 P25897202343.144P44704452523.142P44704452523.143P61093937827.142P61093937827.143P6985681382.145 P6985681382.146 P7077216994.145 P7077216994.146 Q37703787028.146Q51156380339.127Q5472627854.127 Q65953674461.14600000100200300600700I01801J01\02?02Z02n03B03C03X03Y04:04P04Q04R04S04T04U04V04W04X04Y05=05>05?05Q05k05l05m05n05o06906?06@06F06G06H06V06o07007107207307407507607707807907:07;07<07=07>07S07h07i07j08K08l08m08n09809B09L09XFFFS1XFS2ra2sp1X2xs1A3xs0S1R5NEEDR2ra2sp1X2xs2lo3LOS3SLO1A3xs02A03SPR2X0S2ra2sp1X2xs1A3xs0S2ra2sp1X2xs1A3xs0S1R3HIA2ra2sp1X2xs2lo2hc1A3xs04TOPcS1R2ra2sp1X2xs2lo3LOS1A3xs0S1R2ra2sp1X2xs1A3xs0S2ra2sp1X2xs1A1n3xs0FS2sp1X2xs2lo3xs04DSX'FS1R5NEEDR2sp1X2xs2lo3SLO3xs04DSX'S1X2xs1A1n3xs03LL03DXAFFFFFFFFFS1R5NEEDR2sp2lo3SLO1A1n2Hn2A02AS3SPRFFS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPFFFFS1R2lo3LOSS1n2HnFS1n2HnFFS2sp2lo1A1n2ASS1A2r03A161q1r1H2H02q02H4FFFFFFFFFFFFFFFS2sp2xs2lo1A1n3xs02ASS2sp2xs2lo1A1n3xs02ASFFS1R5NEEDR2sp2xs2lo3SLO1A1n3xs02ASS1R5NEEDR2sp2xs2lo3SLO1A1n3xs02ASFFS2xs1A3xs0S1X2xs3xs0S1X2xs3xs0S2xs1A1n3xs0". (* [comment removed for export] *)
  #[using="IMG AMS NEEDR NEEDA LB m nX pX xs ownX MAX CNT LOS SLO SPA"] Lemma fin_tail : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Phc,(16.$17.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(11.&40.)(18.(11.&8.))Ppw,$2.Pnw,$2.PA,$2.Pn,$2.Pxs0,(8.(11.&40.))Pxra,(11.&40.)Pxt0,(11.&40.)Pxt1,(11.&40.)Pxt2,(11.&40.)Pxa0,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Pxt3,(11.&40.)Pxt4,(11.&40.)Pxt5,(11.&40.)Pxt6,(11.&40.)P,(19.$17.VR,VHIA,R18.R17.VLF,R16.)P,(<.$2.(1;.$17.VR,VHIA,R19.)(1;.$17.VR,VHIA,Vh,))P,(4.(1:.&40.Vsp,)(1;.$17.VR,VHIA,R1:.))P,(1<.$17.R19.VX,(2>.R18.(2:.&40.VsgX,)R17.VpadX,))P,(30.(31.VR,)(32.$9.R1;.(33.VLF,))(1:.&40.Vsp,)(1;.$17.VR,VHIA,Vh,)VX,+10.)P,(35.$17.(24.VR,)(25.$17.VR,VHIA,R1=.)R1;.VX,+10.)P,(2?.$17.R1<.R19.R17.)P,(<.$2.(?.(10.(11.&40.)R18.))R19.)P,(3.(>.=R1:.)(4.R1:.+2710.))P,(<.$2.(=.R1<.+10.)=)P,(>.=R1=.)P,(4.(13.R1>.(15.+4.R1=.))Vlo,)P,(30.(31.VR,)(32.$9.R23.(33.VLF,))(34.VR,)(1;.$17.VR,VHIA,R24.)R1?.(15.+4.R1>.))P,(35.$17.(24.VR,)(25.$17.VR,VHIA,R25.)R23.R20.(15.+4.R1?.))P,(12.(4.(13.VX,+10.)R21.)(4.(13.R21.(15.+4.R20.))VX,))P,(12.(4.(13.VX,+10.)Vlo,)(4.(1:.&40.Vsp,)VX,))P,(1<.$17.R26.(13.(1:.&40.Vsp,)-40.)(1=.$1>.(1?.Vs6,)(1=.$1>.(1?.Vs5,)(1=.$1>.(1?.Vs4,)(1=.$1>.(1?.Vs3,)(1=.$1>.(1?.Vs2,)(1=.$1>.(1?.Vs1,)(1=.$1>.(1?.Vs0,)(1=.$1>.(1?.Vra,)(20.$1>.))))))))))P,(21.$17.R27.Vlo,(13.(1:.&40.Vsp,)-40.))P,(22.$17.R28.)(23.$17.(24.VR,)(25.$17.VR,VHIA,R2;.)Lms',$26.(27.(11.&40.)Lx5,(11.&40.)(27.(11.&40.)Lx6,(11.&40.)(27.(11.&40.)Lx7,(11.&40.)(27.(11.&40.)La1',(11.&40.)(27.(11.&40.)La2',(11.&40.)(27.(11.&40.)La3',(11.&40.)(27.(11.&40.)La4',(11.&40.)(27.(11.&40.)La5',(11.&40.)(27.(11.&40.)La6',(11.&40.)(27.(11.&40.)La7',(11.&40.)(27.(11.&40.)Lx28,(11.&40.)(27.(11.&40.)Lx29,(11.&40.)(27.(11.&40.)Lx30,(11.&40.)(27.(11.&40.)Lx31,(11.&40.)(27.P,(11.&40.)(18.(11.&8.))Lm',P,(11.&40.)(18.(11.&8.))(27.(8.(11.&40.))Lxs',(8.(11.&40.))(3.(<.$26.R11.(28.(29.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,(2:.&40.=)R=.R<.R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(2;.Vra,)Vfc,(2<.(11.&40.))R2.(2=.$17.)))(3.(36.(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(1=.(37.$2.$2.)(38.$2.$2.R37.(13.R37.(15.+4.R36.)))(1=.(37.$2.$2.)(38.$2.$2.Vlo,(1:.&40.Vsp,))(20.(37.$2.$2.)))))R3:.R2.)(3.(39.$17.R3:.R2.)(3.(22.$17.R2.)(3.(2?.$17.R2.R37.R1.)(3.(<.$3:.(10.(11.&40.)R1.)(10.(11.&40.)R35.))(3.(<.$2.(3;.R1.R36.)(=.(15.(3;.R35.R36.)(5.+2.Vcount,))(5.+2.(15.+20.R36.))))(3.(1<.$17.R2.VX,(2>.R37.(2:.&40.VsgX,)R36.VpadX,))(3.(21.$17.R2.Vlo,(1:.&40.Vsp,))(19.$17.VR,VHIA,R3<.R3;.VLF,R2.))))))))))))))))))))))))))(28.(29.R23.(2:.&40.(13.(1:.&40.Vsp,)-40.))Vgp,Vtp,R22.R21.R20.(2:.&40.Vcount,)(2:.&40.VX,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(2:.&40.(13.VX,+:.))(2:.&40.R25.)(2:.&40.R26.)(2:.&40.(13.(3<.VX,+3.)(3=.(24.VR,))))(2:.&40.(13.(3<.(13.VX,+:.)+3.)(3=.(24.VR,))))Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(2:.&40.+9=57<.)Vfc,(2<.(11.&40.))R29.(2=.$17.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc HX CWX OX HA LL0 Hn A16 A0 AS CWA OA DXA DSX' FR ST MI. basic_facts hc LBc mc HH TOPc.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & XB & BR).
    pose proof (munch_refl [(X, X + 16); (A, A + 4 * n); (lo, bv_unsigned sp)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    callxA_sp (bv_unsigned sp + -64)
      (eapply store_walk with (hc := hc) (LBc := LBc) (pw := pw) (nw := nw) (pn := A) (nb := n); try eassumption;
       first [ clear - A0 AS SLO SPR Hn NEEDR; lia
             | clear - Hn; lia
             | first [exact C24H | match goal with |- ?g => idtac "SW-PRE-LEFT:" g end] ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-SW-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : HM asegs R HIA hc LBc LF m5 |- _ => rename H into HH5 end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
    match goal with H : rw_cells asegs m5 (bv_unsigned sp + -64) _ |- _ => rename H into FR5 end.
    match goal with H : rw_cells asegs m5 X _ |- _ => rename H into HX5 end.
    callxA_sp (bv_unsigned sp + -64)
      (eapply tail_walk with (hc := hc) (LBc := LBc) (p := A) (n := n) (xs0 := xs0); try eassumption;
       first [ clear - Hn; lia
             | clear - A16; Z.div_mod_to_equations; lia
             | right; exact A0
             | clear - A0 AS SLO SPR Hn NEEDR; lia
             | left; exact AS
             | first [exact C24H | match goal with |- ?g => idtac "TW-PRE-LEFT:" g end] ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-TW-SIDE:" g end.
    finish.
    all: try eassumption.
    all: first [exact C24H | match goal with |- ?g => idtac "FT-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L23905308515.5L31316198190.3L38189860086.1L39172636981.0L65397032456.100000C00N00R00S00WS3xs03xs'1n3LL03LENS3xs01n3LL0S2xsSS2xs". (* [comment removed for export] *)
  #[using="Type"] Lemma shifted_val : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Pxs0,(8.(11.&40.))Pxs',(8.(11.&40.))Pn,$2.P,(<.$2.(?.(10.(11.&40.)R3.))R1.)P,(<.$3:.(10.(11.&40.)R3.)(10.(11.&40.)R4.))P,(<.$2.(4>.R5.)(4>.Vxs,))P,(>.(15.(4>.Vxs,)(5.+2.Vcount,))(5.+2.(15.+20.R4.)))P,(<.$2.(3;.R6.R5.)(=.(15.(3;.R7.R5.)(5.+2.Vcount,))(5.+2.(15.+20.R5.))))(<.$2.(4>.R7.)(15.(4>.Vxs,)(5.+2.Vcount,)))")
(* [comment removed for export] *).
  Proof.
    intros xs0 xs' n LL0 LEN HV FITv LV.
    assert (E0 : lval xs0 n = limbs_val xs0) by (unfold lval; rewrite firstn_all2 by (clear - LL0; lia); reflexivity).
    assert (E1 : lval xs' n = limbs_val xs') by (unfold lval; rewrite firstn_all2 by (clear - LL0 LEN; lia); reflexivity).
    rewrite E1, E0, HV in LV. rewrite Z.mod_small in LV; [exact LV|].
    split; [| exact FITv].
    pose proof (lval_range xs (Z.of_nat (length xs)) ltac:(clear; lia)) as [G _]. unfold lval in G. rewrite firstn_all2 in G by (clear; lia).
    apply Z.mul_nonneg_nonneg; [exact G| apply Z.pow_nonneg; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L1160139931.136 L19947978140.136L23615739305.3  L26892418956.1  L28860517118.3  L29428324939.5  L29969586292.4  L35653441506.7  L37723235619.3  L40173403829.6  L40906110596.136L50790580594.6  L59314873579.6  L60098763854.3  L60445764899.4  L62018535662.1  L784449086.6    00000R01701A01E01N01`01n02H02R02d03F03]03o04904G04J04\S2ra2sp1X2nX2xs5count1A1n3xs'4LEN9S2ra2sp1X2nX2xs5count2lo1A1n3xs'4LEN9S1R3HIA2hcS2spS2nX1n2E2S1R2lo3LOS3ALO3ACPS2nX1n3LIM3NRXS1R3HIA2sp2lo2hc4TOPc4HTOPS2nX1n3LIMS2nX2xs1n3LIM4LENXS2ra2sp1X2nX2xs5count1A1n3xs'4LEN9S1R5NEEDR2sp2lo3LOS3SLOS2nX1A1n3LIM3NRX1HS1R2lo3LOSS2nX1n3LIM3NRXS1RS2nX2xs1n3LIM4LENX". (* [comment removed for export] *)
  #[using="IMG NEEDR MAX NST XW DSP LOS SLO TOP"] Lemma post_fin : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Pmo,$3>.Pmo9,$3>.Phc,(16.$17.VR,VHIA,)PLBr,(8.$9.)Pmc,P,(11.&40.)(18.(11.&8.))Pm9,P,(11.&40.)(18.(11.&8.))PA,$2.Pn,$2.Pxs',(8.(11.&40.))PPHI,$2.PFR,$2.Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Px28,(11.&40.)Px29,(11.&40.)Px30,(11.&40.)Px31,(11.&40.)P,(<.$2.R12.(4=.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))P,(3.(>.VnX,R13.)(4.R13.+2710.))P,(>.(15.(4>.Vxs,)(5.+2.Vcount,))(5.+2.(15.+20.R14.)))P,(19.$17.VR,VHIA,R1:.(1=.(37.$2.$2.)(38.$2.$2.R16.(15.+4.R15.))R19.)VLF,R18.)P,(<.$2.(1;.$17.VR,VHIA,R1;.)(1;.$17.VR,VHIA,Vh,))P,(<.$2.(43.$17.VR,VHIA,R1<.)(43.$17.VR,VHIA,Vh,))P,(<.$2.(44.$17.VR,VHIA,R1=.)(44.$17.VR,VHIA,Vh,))P,Px,$2.P,(25.$17.VR,VHIA,Vh,R1.)(25.$17.VR,VHIA,R20.R2.)P,(4.(46.$17.VR,VHIA,R1?.)(13.(46.$17.VR,VHIA,Vh,)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)))P,(4.(47.$17.VR,VHIA,R20.)(13.(47.$17.VR,VHIA,Vh,)$7.))P,(40.$17.VR,(41.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(1:.&40.Vsp,)(34.VR,)(43.$17.VR,VHIA,Vh,)(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(20.(37.$2.$2.)))Vm,R1?.)P,(35.$17.(24.VR,)(25.$17.VR,VHIA,R22.)R20.VX,+10.)P,(35.$17.(24.VR,)(25.$17.VR,VHIA,R23.)R21.R1?.(15.+4.R1>.))P,(54.VR,VLB,VLF,R20.(15.+4.R1?.))P,(<.$2.(=.R21.+10.)=)P,Pb,$9.P,(52.$9.R1.(41.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(52.$9.R2.R27.)P,Pb,$9.P,(52.$9.R1.R27.)(52.$9.R2.VLB,)P,Pb,$9.P,(52.$9.R1.VLB,)P,(4?.(52.$9.R2.(53.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))))(52.$9.R3.R2:.)P,Pb,$9.P,(52.$9.R1.(53.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(4?.(52.$9.R2.R2:.))P,(36.(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(1=.(37.$2.$2.)(38.$2.$2.R26.(13.R26.(15.+4.R25.)))(1=.(37.$2.$2.)(38.$2.$2.Vlo,(1:.&40.Vsp,))(20.(37.$2.$2.)))))R28.R27.)P,(39.$17.R29.R28.)P,(22.$17.R29.)P,(2?.$17.R2:.R29.R27.)P,(<.$3:.(10.(11.&40.)R28.)(10.(11.&40.)(32.(11.&40.)Vxs,(57.(11.&40.)(2:.&40.=)(58.(59.R29.VnX,))))))P,(<.$2.(3;.R29.R2:.)(=.(15.(3;.(32.(11.&40.)Vxs,(57.(11.&40.)(2:.&40.=)(58.(59.R2:.VnX,))))R2:.)(5.+2.Vcount,))(5.+2.(15.+20.R2:.))))P,(1<.$17.R2=.VX,(2>.R2<.(2:.&40.VsgX,)R2;.VpadX,))P,(21.$17.R2>.Vlo,(1:.&40.Vsp,))P,(19.$17.VR,VHIA,R32.(1=.(37.$2.$2.)(38.$2.$2.R2>.(15.+4.R2=.))R31.)VLF,R2?.)P,(3?.R35.R34.)P,(45.$17.VR,VHIA,R34.R35.)(49.$17.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Lr,$2.LdX',$:.(;.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,R2.R1.)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)$7.Vlo,Vm,R37.(4:.(28.(29.Vra,Vsp,Vgp,Vtp,R2<.R2;.R2:.Vs0,Vs1,(2:.&40.=)R29.R28.R27.R26.R25.R24.R23.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R22.R21.R20.R1?.)VF,(2;.Vra,)Vfc,(2<.(11.&40.))R32.(2=.$17.))R36.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HN LIM FITv HHc HT HS HFL HCS HV HFR HPc OXc OAc HFRA A16 KEEPR RIN ROUT RX MU9 WM9 MI9 HA9 LEN9 LV9 HX9 ST9 HH9 MF9 HK9.
    assert (TOPc : bv_unsigned sp <= htop asegs R HIA hc) by (rewrite HT; exact TOP).
    basic_facts hc ((A, 4 * n) :: LBr) mc HHc TOPc.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & XB & BR).
    dpose HFRA as (A0 & AC & AD & HAP).
    assert (NIA : ~ In (A, 4 * n) LB).
    { intros Hin. destruct (HAP A (4 * n) ltac:(apply in_app_iff; left; exact Hin)); clear - H LIM NRX; lia. }
    eapply (post_shift mo mo9 hc m9 ((A, 4 * n) :: LBr) n A xs' LHeap); try eassumption.
    - eapply (shifted_val (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (n - nX))) xs' n); try eassumption.
      + rewrite length_app, repeat_length. clear - LENX LIM NRX; lia.
      + apply P_mpi_add_abs_W.limbs_val_app_zeros.
    - clear - LIM; lia.
    - discriminate.
    - (* [comment removed for export] *)
      eapply presA_trans; [exact HPc|]. rewrite <- HS.
      eapply (presA_drop_fresh asegs R HIA hc (mpd_keep LB dX) LF [(X, X + 16)] A (4 * n) mc m9 (bv_unsigned sp));
        [| apply fresh_apart_keep; exact HFRA| clear - LOS SLO NEEDR; lia].
      eapply (presA_weaken asegs R ((A, 4 * n) :: LBr) (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                (hstkhi asegs R HIA hc) (hstkhi asegs R HIA hc) [(A, A + 4 * n); (X, X + 16)]);
        [| intros b Hb; right; apply KEEPR; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
      eapply (presA_drop_below asegs R HIA hc ((A, 4 * n) :: LBr) LF _ lo (bv_unsigned sp) _ mc m9); [exact HHc| | clear; lia| exact LOS].
      eapply (presA_of_munch asegs R ((A, 4 * n) :: LBr) LF _ _ _ _ mc m9 (hcs asegs R HIA hc) CSOK);
        [| intros c0 Hc; eapply cshd_hcs; [exact HHc| | exact Hc]; clear; lia | | exact WM9].
      + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (A + 4 * n - A) with (4 * n) by lia; eapply aobj_crange; exact OAc|].
        apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OXc|]. apply Forall_nil.
      + eapply munch_weaken; [| exact MU9]. clear. intros y Hy. cbn [outside fst snd] in *. tauto.
    - (* [comment removed for export] *)
      eapply mpd_at_rebuild; [discriminate| exact HX9| exact XAL| exact X0| | unfold MPI_MAX_LIMBS; clear - LIM NRX; lia| exact SGX| intros E; discriminate E|].
      + rewrite <- (Nat2Z.id (length xs')), LEN9, length_app, repeat_length. clear - LENX LIM NRX; lia.
      + intros _. split; [clear - LIM NRX; lia|]. split; [left; reflexivity|]. split; [exact A16| exact HA9].
    - (* [comment removed for export] *)
      unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n].
      split; [reflexivity|]. split; [discriminate|].
      split; [intros b [Hb|Hb]; [right; left; exact Hb| left; apply RIN; exact Hb]|].
      split; [intros b Hb Hn; right; exact (ROUT b Hb Hn)|].
      intros b Hb [E|Hin]; [| exfalso; exact (RX b Hb Hin)].
      exfalso. subst b. unfold mpd_blk in Hb. cbn [md_own md_p md_n] in Hb.
      destruct ownX; [destruct Hb| | destruct Hb]. destruct Hb as [E|[]]. injection E as E1 E2.
      dpose MAX as [[_ (_ & _ & _ & _ & OWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OWN.
      ddestruct OWN as (N1 & HIN & _). apply NIA. rewrite <- E1. replace (4 * n) with (4 * nX) by (clear - E2; lia). exact HIN.
    - cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. cbn [fst snd]. apply fresh_apart_keep. exact HFRA.
    - cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. exact NIA.
    all: first [exact C24H | match goal with |- ?g => idtac "PF-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Grow.
    Variables (mo : Model) (m1 : mem) (limbs : Z).
    Hypothesis HH1 : HM asegs R HIA h LB LF m1.
    Hypothesis HXS1 : rw_cells asegs m1 X [C8 (Z_to_bv 64 pX); C2 (Z_to_bv 64 sgX); C2 (Z_to_bv 64 nX); C4 padX].
    Hypothesis PCH1 : ownX = LHeap -> rw_cells asegs m1 pX [CB (4 * length xs)%nat (u32s xs)].
    Hypothesis OX1 : aobj asegs AL CS m1 X 16.
    Hypothesis FR1 : rw_cells asegs m1 (bv_unsigned sp + -64) FRAME.
    Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -64).
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis HP1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "(40.$17.VR,(41.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(1:.&40.Vsp,)(34.VR,)(43.$17.VR,VHIA,Vh,)(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(20.(37.$2.$2.)))Vm,Vm1,)")
(* [comment removed for export] *).
    Hypothesis BUD : havol asegs R HIA h + shift_l_PHI dX count <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + shift_l_FR <= FR_MAX.
    Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.
    Hypothesis DXP : ownX = LHeap -> X + 16 <= pX \/ pX + 4 * nX <= X.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16.
    Hypothesis P0 : 0 <= pX.
    Hypothesis PC : pX + 4 * nX <= alloc_ceiling.
    Hypothesis PHEAP : ownX = LHeap -> 0 < pX /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ 1 <= nX.
    Hypothesis PNULL : ownX = LNull -> pX = 0 /\ nX = 0.
    Hypothesis LIM : nX < limbs <= 10000.
    Hypothesis HN : limbs = shift_l_n count dX.
    Hypothesis FIT : limbs_val xs * 2 ^ count < 2 ^ (32 * limbs).

    Local Ltac2 Set LiaOrc.tbl := fun () => "03H0@C17025492443.201C31740276271.202D10111111973.229D10557048349.229D16049893661.203D34611504346.229D37703914153.228D37703914153.229D38983586459.229D40600806371.228D50796826103.203D52756908355.228D52756908355.229D59428651230.155D59429060293.229D63595235433.203D64336185449.203K1227220751.202 K25897202343.202K36719207456.201K4540635128.202 K51736254456.202K61205767951.202L11144442263.154L11404239431.12 L11414166579.16 L11414166579.22 L11583759780.10 L1160155683.259 L1233234968.4   L12694533441.2  L12750819336.13 L12755534717.11 L13375081314.4  L13870505274.6  L14350476896.7  L1546386346.16  L15500908608.22 L15506042591.7  L16256253080.5  L1649577667.2   L1728360839.7   L17377090088.20 L17585880332.15 L18293330070.2  L18513325338.7  L19061415402.1  L19947928356.259L20857671769.14 L21570111356.22 L23036393198.8  L23100341967.163L23100341967.192L2414589328.20  L24391384886.2  L25033921014.12 L25280789856.10 L25436154562.16 L25560229662.259L25890634160.3  L26892418956.1  L27711224602.12 L28348757579.20 L28553555646.2  L28814040852.163L29428324939.5  L30661063921.14 L32250862063.4  L33658417335.20 L33669001629.16 L33811788193.0  L34171955900.7  L34413141779.22 L35653441506.7  L36440793763.3  L36715738693.2  L37714553091.1  L38948636245.0  L39025375836.20 L39039630198.22 L39172636981.0  L39187934475.6  L39280637297.0  L39359458311.17 L39621323139.1  L40281191306.3  L40590202953.5  L40803681500.7  L40823280838.20 L41858767142.4  L43168300488.10 L43168300488.4  L43168300488.5  L44397119898.2  L44586766814.7  L44697879740.4  L4494212682.4   L45026238780.2  L4536894877.4   L45818796787.5  L46160487540.171L46160803852.3  L46948705943.22 L47107138245.3  L47858894730.7  L47860712607.10 L47955344026.2  L47955441591.191L47956781558.170L48132467214.7  L49309103263.20 L49659282750.4  L50790809970.7  L51043066701.10 L51622416288.7  L51731989917.3  L51878091212.7  L51943510129.10 L52037294262.234L52476066706.163L52752331497.8  L54271395752.2  L5479049730.1   L57836289759.20 L59308632307.1  L59308633593.3  L59308661072.8  L59308668813.4  L59308742867.3  L59321342699.2  L60047848958.4  L60047848958.6  L60098763854.3  L60419394486.11 L60549562490.3  L60684097692.2  L61211782168.3  L62018535662.1  L62624471726.40 L62624471726.41 L62627242265.40 L62627242265.41 L63799194974.11 L64372451842.1  L64966926188.10 L64968776825.7  L656136024.1    L66610753222.9  L67996112456.1  L6992249585.3   L8800769400.4   L9596616833.4   L9799018071.4   N12401863469.202N14951461807.202N20716133971.202N31170017719.202N32071669760.202O17025492443.201O17919651190.202O26871806789.202O31740276271.202O39322336069.202O48499521681.202O49587672251.201O57399310481.202O65674534437.202P25897202343.202P36719207456.201P44704452523.201P45829525988.202P6985681382.202 P8434753010.228 P8434753010.229 P8435147753.154 P8435147753.155 Q12370813529.168Q12370813529.200Q17205254096.199Q17207204208.167Q20190308418.203Q26207421841.178Q26207721832.179Q26209819600.199Q26220304629.176Q30985055127.141Q30985055127.223Q30987168515.183Q30987329587.205Q30987329589.123Q31651620729.199Q31654082872.178Q37623180338.199Q37625422482.167Q37703787028.203Q37940043306.200Q38248387216.203Q39212284437.179Q43879899724.203Q43925228937.179Q44728669274.155Q44729068097.229Q48514199408.228Q48514322795.154Q5483504175.199 Q5485174314.168 Q5485174314.200 Q5485489295.167 Q60511567613.179Q60697995187.179Q6143569392.168 Q6143569392.200 Q65983947055.168Q65983947055.200Q8885009321.176 Q9534281562.176 00000100200l00m00n02<02\03<04704W05X05Y05Z06806X06Y06Z07H07I07J08<08X09C09a0:70:I0:[0:\0;H0;I0;J0;K0;L0;^0<40<J0<`0==0=>0=O0=W0=X0=n0=o0>60>O0>S0?B0?C0?\0?]0@=0@]0@n0@o0AF0AG0A\0BH0BI0BM0BN0Bc0Bj0D40DF0DG0DV0Dk0E@0EA0EZ0Eg0FG0FS0FT0FW0FX0Fd0G00G10GG0GH0GI0GP0GY0Gb0H=0HA0HO0HP0HQ0HR0HZ0H[0H\0Hn0I70I80I90I_0Ih0JI0JU0JV0Jf0Jn0KU0L<0LW0M00M>0MU0MV0Mo0N00N10N20NR0O`0Oa0Oh0Ok0P;0P?0PH0Pd0Q20Q<0Q=0QM0Q`0Qj0Qk0R70R80R90R<0R=0R>0R?0R@0R]0Ra0S:0S;0S>0ST0SX0SY0Sj0T80TJ0UC0UD0U`0V<0V=0V>0V?0V@0VA0VB0VC0VD0VE0VF0VG0VH0Vn0W^0XX0Xm0YB0Y]0Z80Z_0[F0[X0\00\P0\b0]40]F0]X0^T0_J0`@0a60b20bD0bV0bh0c@0cR0cS0cf0d80dN0d`0da0db0eL0f<0fN0ff0g80gP0g`0h50hM0h_0h`0ha0i30iCFFS2ra2sp1X2nX2pX2xs5count3CNT5limbs2P03LIM3SPR2X04LENX1A2A0FFS2ra2sp1X3sgX2nX2pX2xs4padX4ownX5count3CNT5limbs2P03LIM2HN3SPR2X04LENX2BR1A2A0S2ra2sp1X2pX2xs5count5limbs2P01AS2ra2sp1X2pX2xs5count5limbs2P01AS2ra2sp1X2nX2pX2xs5count3CNT5limbs2P03LIM3SPR2X02BR1A2A02N1S2ra2sp1X2pX2xs5count5limbs2P01AS1R5NEEDR2ra2sp1X2pX2xs5count2lo3CNT3LOS3SLO5limbs2P03SPR2X01A2A0FFS2ra2sp1X2pX2xs5count5limbs2P0S2ra2sp1X2pX2xs5count5limbs2P01AFFS2nX2pX2xs5count3CNT5limbs2P03LIM4LENX1A2KP2PAFFS1R2sp2nX2pX2xs5count2lo3CNT3LOS5limbs2PC3ALO4LENXS2sp1X2xs5count2lo5limbs3DSXS1X2nX2pX2xs5count3CNT5limbs2P03LIM1A2XA2KPS2ra2sp1X2pX2xs5count5limbs2P0S2nX2lo5limbs3LIM1A2ASS1R3HIA2sp2h24TOP2S1R3HIA2sp2h24TOP2FS2ra2sp1X2nX2pX2xs5count5limbs2P01A3xs'4LEN9FFFFS2nX5limbs3LIM3NRXS2nX2xs5limbs3LIM4LENXS2nX2pX5limbs3LIM1A2PAS1X2r03XAL1q1r1H2q02H4S1R3HIA1h2sp4BUDF3SPR2h24HFR2FS1R3HIA1h2h24HFR2S2nX3NRXFS1R3HIA1h2sp5limbs3BUDFS2sp2loS1R2lo3LOS5limbs3ALO1A2ACS2nXS2ra2sp1X2nX2pX2xs5count2lo5limbs2P01A3xs'4LEN9FS2sp2nX5limbs3LIM3SPR3NRXFS2ra2sp1X2pX2xs5count5limbs2P01AS2ra2sp1X2pX2xs5count5limbs2P01AS1R3HIA1h2sp4BUDFFS1R2nX2pX2lo3LOS2PC3ALOFS2sp2nX5limbs3LIM3SPRS2ra2sp1X2nX2pX2xs5count5limbs2P01A3xs'4LEN9FS2spFS2sp2nX5limbs3LIM3SPRS2nX2pXS1R5NEEDR2ra2sp1X2nX2pX2xs5count2lo3CNT3SLO5limbs2P03LIM3SPR2X02BR1A2A02ASS1R2lo3LOS3ALO3ACPFS2nX2pX2xs4LENXS1R2sp2lo3SLO3NRM3SPRS1R2sp2lo3SLO3NRA3SPRSS1R3HIA1h2h24HFR22h44HFR4S1R2sp2lo3SLOS1R3HIA1h2sp2lo3TOP4HTOP2h24TOP2S2nX2xs4LENXFS1ASS2sp3SPA3SPRS2sp3SPA3SPRSS2nX2xs5limbs3LIM4LENXSFS5limbsS1R3HIA1hS5limbs1AS1R5NEEDR2sp2lo3LOS3SLO3ALOS2spS2nX2xs4LENX1AFFFS2nX3NRXFFS2nX5limbs3LIM3NRXS2LB4C24HFFS2ra2sp1X2pX2xs5count5limbs2P02X02XB1AS1X2X02XBS1R3HIA1h2sp5limbs3BUD3SPR2h23HV2S2nX2xs4LENXFS1R2nX2pX2PC3ACVS2nX3NRXS2ra2sp1X2nX2pX2xs5count5limbs2P03NRX1AS2ra2sp1X2nX2pX2xs5count5limbs2P03NRX1AS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp2nX5limbs3LIM3SPR3NRXS2nX5limbs3LIMS1R5NEEDR2sp2lo3LOS3SLOFS2nX2pX5limbs3LIM1A2N12PAFFFS2ra2sp1X2pX2xs5count5limbs2P01AS1R5NEEDR2ra2sp1X2nX2pX2xs5count2lo3CNT3LOS3SLO5limbs2P02PC3ALO3SPR2X02BR1A2A0FS2nX2pXS1XS1R3HIA1h2sp3TOPS2KPS1A2A02KZS2nX2pX5limbs3LIM1A2N12PA2E1S2nX1l4LENX2EnS2pX2KP2B0FS2nX5limbs3LIM1AS2nX2xs5limbs3LIM1AS1R2lo3LOSFS2nX5limbs1AFFS1RFFFFS1R3HIA1h5limbs2h23HV22h43HV4S2pXS1R2nX5limbs3LIM1A2AC3ACVFS1XS1R3HIA1h5limbs2h23HV2S2spFS2nX5limbs3LIM2N1S2nX2xs4LENX1AS2nX5limbs3LIM3NRXS1R2sp2nX2xs5count2lo3CNT3LOS5limbs3LIM3ALO2BR1A2AC3x291CFS2sp2xs5count2lo5limbs3x291CS2sp2xs5count2lo5limbs3x291CFFFFFFFFFFFFS2sp2nX2xs5count2lo3CNT5limbs3LIM1A2ASS1R2sp2nX2xs5count2lo3CNT3LOS5limbs3LIM3ALO1A2ACS1R5NEEDR2sp2nX2xs5count2lo3CNT3LOS3SLO5limbs3LIM3ALO1A2ACS2sp1X2xs5count5limbsS2sp1X2xs5count5limbsS2sp1X2pX2xs5count5limbs2P0S2sp1X2pX2xs5count5limbs2P0S2ra2sp1X2pX2xs5count5limbs2P03XAL2X01AS2ra2sp1X2pX2xs5count5limbs2P03XAL2X01AS1X2xs5count5limbsS1X2pX2xs5count5limbs2P0S2nX2xs5count3CNT5limbs3LIM2BR1AS1X2xs5count5limbsS1X2xs5count5limbsS1X2xs5count5limbsS1X2xs5count5limbsS1R5NEEDR2sp2pX2xs5count2lo3CNT3LOS3SLO5limbs2P03ALO3ACP3SPRS1R5NEEDR2sp2xs5count2lo3CNT3LOS3SLO5limbs3ALO3ACP3SPRS1R5NEEDR2sp2xs5count2lo3CNT3LOS3SLO5limbs3ALO3ACP3SPRS1R5NEEDR2sp2xs5count2lo3CNT3LOS3SLO5limbs3ALO3ACP3SPRS1R5NEEDR2sp2pX2xs5count2lo3CNT3LOS3SLO5limbs2P03ALO3ACP3SPRS1X2xs5count5limbsS1X2xs5count5limbsS1X2xs5count5limbsS1X2pX2xs5count5limbs2P0S2xs5count5limbs1AFS2xs5count2lo5limbsS1X2xs5count5limbsS2sp2xs5count2lo5limbsS1X2xs5count5limbsFFS1R5NEEDR2sp2xs5count2lo3CNT3LOS3SLO5limbsS1R5NEEDR2sp2pX2xs5count2lo3CNT3LOS3SLO5limbs2P0S1X2xs5count5limbsS1X2pX2xs5count5limbs2P0S1X2xs5count5limbsS1X2pX2xs5count5limbs2P0S2xs5count5limbsS1X2xs5count5limbs2X0S1X2pX2xs5count5limbs2P0S1X2xs5count5limbsFFS1X2xs5count5limbsS2xs5count5limbs". (* [comment removed for export] *)
    #[using="IMG ZF CALLOC AMC AMS NEEDR NEEDA HND DIMG C24H MAX NST CNT XW DSP LOS SLO TOP SPA TPV HH1 HXS1 PCH1 OX1 FR1 ST1 MI1 HP1 BUD BUDF DSX DXP CW P0 PC PHEAP PNULL LIM HN FIT"] Lemma grow_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Pxra,(11.&40.)Pxt0,(11.&40.)Pxt1,(11.&40.)Pxt2,(11.&40.)Pxa0,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Pxs4,(11.&40.)Pxt3,(11.&40.)Pxt4,(11.&40.)Pxt5,(11.&40.)Pxt6,(11.&40.)(5:.$17.(5;.$17.VR,VHIA,Vh,Vmo,)(49.$17.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Lr,$2.LdX',$:.(;.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,R2.R1.)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)$7.Vlo,Vm,Vmo,)(28.(29.R11.(2:.&40.(13.(1:.&40.Vsp,)-40.))Vgp,Vtp,R10.R?.R>.(2:.&40.Vcount,)(2:.&40.VX,)R=.R<.R;.R:.R9.R8.R7.R6.(2:.&40.(13.VX,+:.))(2:.&40.Vlimbs,)R5.(2:.&40.(13.(3<.VX,+3.)(3=.(24.VR,))))(2:.&40.(13.(3<.(13.VX,+:.)+3.)(3=.(24.VR,))))Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(2:.&40.+9=518.)Vfc,(2<.(11.&40.))Vm1,(2=.$17.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. basic_facts h LB m1 HH1 TOP.
      dpose facts as (XAL & X0 & LENX & NRX & SGX & XB & BR).
      pose proof (HND _ _ _ _ HH1) as ND.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      unfold shift_l_PHI, grow_PHI in BUD. cbn [md_n md_limbs] in BUD. rewrite <- HN in BUD. unfold shift_l_FR in BUDF.
      assert (MA1 : mpd_at asegs m1 LB dX).
      { eapply mpd_at_rebuild; [exact NST| unfold mpi_cells; exact HXS1| exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGX| exact PNULL|].
        intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
        eapply (u32arr_of_cells asegs); [exact (PCH1 E)| reflexivity]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := limbs) (sz := 4) (lo := lo) (d := 0);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; try eassumption; try reflexivity.
        all: try ((intros _; first [ clear - C24H; unfold C24_SHIFT_L_c in C24H; lia | match goal with HS : forall b, In b ?L -> In b LB, HHr : HM _ _ _ _ ?L _ _ |- _ => let NDq := fresh "NDq" in let CI := fresh "CI" in pose proof (HND _ _ _ _ HHr) as NDq; apply NoDup_map_inv in NDq; pose proof (cnt24_incl _ _ NDq HS) as CI; clear - CI C24H; unfold C24_SHIFT_L_c in C24H; lia end ])).   (* [comment removed for export] *)
        all: try (apply uwc_data; [clear; lia| rewrite unsigned_lit by (clear - CNT; lia); pose proof (alloc_ceiling_val R) as ACV; clear - CNT ALO ACV; lia]).   (* [comment removed for export] *)
        all: clear - CNT LIM NRX LOS SLO NEEDR NRM TOP SPA SPR BUD BUDF; try (unfold AMAX); try (unfold AVOL_CALL in * ); try (unfold fr_charge in * ); try lia.
        all: first [exact C24H | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end]. }
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by qlia.
      ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      (* [comment removed for export] *)
      assert (PCH2 : ownX = LHeap -> rw_cells asegs m2 pX [CB (4 * length xs)%nat (u32s xs)]).
      { intros E. ddestruct (PHEAP E) as (B0 & HIN & _). eapply (presA_rw_cells asegs R); [exact HP2| exact (PCH1 E)| | cbn; clear; tauto].
        simpl_sizes. eapply client_range_block; [apply in_app_iff; left; exact HIN| clear; lia| clear - LENX; lia]. }
      presA_transport HP2.
      assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|].
        eapply presA_weaken; [exact HP2| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
      clear HP2.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX1) as OX2.
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      clear CSOK SB64 SCS0 SCS HTOP.
      pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
      (* [comment removed for export] *)
      zstep. zstep.
      destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
      - (* [comment removed for export] *)
        pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
        assert (MA2 : mpd_at asegs m2 LB dX).
        { eapply mpd_at_rebuild; [exact NST| unfold mpi_cells; match goal with H : rw_cells asegs m2 X _ |- _ => exact H end| exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGX| exact PNULL|].
          intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
          eapply (u32arr_of_cells asegs); [exact (PCH2 E)| reflexivity]. }
        zstep.
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply epi_walk with (hc := h2) (LBc := LB) (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); try eassumption
          | intros y Hy; exact Hy | ].
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFAIL-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. destruct PO as [E ST9]. subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply post_keep; try eassumption.
        all: first [exact C24H | match goal with |- ?g => idtac "GFAIL-LEFT:" g end].
        { unfold shift_l_PHI, grow_PHI; cbn [md_n md_limbs]; rewrite <- HN. unfold AVOL_CALL in *. clear - HV2 LIM NRX; lia. }
        { unfold shift_l_FR, fr_charge in *. clear - HFR2. lia. }
      - (* [comment removed for export] *)
        replace (limbs * 4) with (4 * limbs) in HFRA, HAS, HH2, HNEW by (clear; lia).
        pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP.
        assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP; lia]).
        dpose HFRA as (A0 & AC & AD & HAP).
        pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * limbs) :: LB) LF m2 A (4 * limbs) HH2 (or_introl eq_refl)) as OA.
        assert (HINA : In (A, 4 * limbs) (((A, 4 * limbs) :: LB) ++ fdata LF)) by (left; reflexivity).
        assert (XA : X + 16 <= A \/ A + 4 * limbs <= X).
        { destruct (fresh_apart_client R LB LF (bv_unsigned sp) X 16 A (4 * limbs) HFRA); [| clear; lia| clear - LIM NRX; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
          eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
        assert (AS : A + 4 * limbs <= lo) by (clear - AC ALO LOS; lia).
        (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - A0 AC H; lia); clear - KZ A0; lia|]. clear KZ.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. if_cases KP; zify_cond KP.
        + (* [comment removed for export] *)
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          assert (EO : ownX = LNull) by (destruct ownX; [reflexivity| exfalso; destruct (PHEAP eq_refl) as [B0 _]; clear - B0 KP; lia| exfalso; exact (NST eq_refl)]).
          destruct (PNULL EO) as [EP En]. clear PHEAP PCH2.
          assert (xs = []) as EL by (destruct xs; [reflexivity| exfalso; cbn in LENX; clear - LENX En; lia]).
          assert (CW3 : client_wrange L (((A, 4 * limbs) :: LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CW|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
          assert (HA2 : u32arr asegs m2 A (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (limbs - nX)))).
          { rewrite EL, En. cbn [app]. rewrite Z.sub_0_r.
            replace (Z.to_nat (4 * limbs)) with (4 * Z.to_nat limbs)%nat in HNEW by (clear - LIM NRX; lia).
            eapply (u32arr_of_cells asegs); [exact HNEW| symmetry; apply u32s_repeat0]. }
          eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
            [ eapply (fin_tail h2 ((A, 4 * limbs) :: LB) m2 pX nX A limbs (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (limbs - nX)))); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (rewrite length_app, repeat_length; clear - LENX LIM NRX; lia).
          all: try (clear - LIM NRX; lia).
          all: try (eapply client_wrange_block; [exact HINA| clear; lia| clear - LIM NRX; lia]).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN0-PRE-LEFT:" g end.
          intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & xs' & E9 & MU9 & WM9 & MI9 & HA9 & LEN9 & LV9 & HX9 & ST9 & HH9). subst ms'.
          apply aevtA_done. intros mo9 [HK9 MF9].
          eapply (post_fin mo mo9 h2 LB m2 m9 A limbs xs'); try eassumption.
          all: try (clear - LIM; lia).
          all: first [exact C24H | match goal with |- ?g => idtac "GFIN0-LEFT:" g end].
          { unfold shift_l_PHI, grow_PHI; cbn [md_n md_limbs]; rewrite <- HN. unfold AVOL_CALL in *. clear - HV2 LIM NRX; lia. }
          { unfold shift_l_FR, fr_charge in *. clear - HFR2. lia. }
          { intros b Hb. eapply In_mpd_keep. exact Hb. }
          { intros b Hb. exact Hb. }
          { intros b Hb _. exact Hb. }
          { unfold mpd_blk. cbn [md_own md_p md_n]. rewrite EO. intros b []. }
        + (* [comment removed for export] *)
          assert (EO : ownX = LHeap).
          { destruct ownX; [| reflexivity| exfalso; exact (NST eq_refl)]. exfalso. rewrite (proj1 (PNULL eq_refl)) in KP.
            rewrite ?unsigned_lit in KP by (clear; lia). clear - KP. lia. }
          ddestruct (PHEAP EO) as (B0 & HIN & HP16 & N1). pose proof (PCH2 EO) as PCH. clear PHEAP PCH2 PNULL.
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          pose proof (DXP EO) as DXP'. pose proof (DSP ltac:(rewrite EO; discriminate)) as DSP'.
          pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * limbs) :: LB) LF m2 pX (4 * nX) HH2 (or_intror HIN)) as OP.
          assert (PA : A + 4 * limbs <= pX \/ pX + 4 * nX <= A) by (apply HAP; apply in_app_iff; left; exact HIN).
          assert (HINP : In (pX, 4 * nX) (((A, 4 * limbs) :: LB) ++ fdata LF)) by (right; apply in_app_iff; left; exact HIN).
          (* [comment removed for export] *)
          assert (LQ : Z.land (Z.lor pX A) 3 = 0).
          { rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2). rewrite !Z.land_ones by lia. change (2 ^ 2) with 4.
            replace (pX mod 4) with 0 by (clear - HP16; Z.div_mod_to_equations; lia).
            replace (A mod 4) with 0 by (clear - A16; Z.div_mod_to_equations; lia). reflexivity. }
          zstep. zstep. zstep. if_cases KQ; zify_cond KQ; [exfalso; clear - KQ LQ; rewrite ?LQ in KQ; rewrite ?Zmod_0_l in KQ; lia|].
          shadow_chk OX2 (X + 10) 2.
          zstep.
          replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
            by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
          zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
          zstep. zstep.
          (* [comment removed for export] *)
          assert (HN2 : rw_cells asegs m2 A ([CB (4 * length xs)%nat (repeat (Z_to_bv 8 0) (4 * length xs))]
                                              ++ [CB (Z.to_nat (4 * (limbs - nX))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (limbs - nX))))])).
          { eapply rw_cells_reshape; [exact HNEW| |].
            - cbn. rewrite !repeat_length; repeat split; reflexivity.
            - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. clear - LENX LIM NRX; lia. }
          apply rw_cells_app in HN2. destruct HN2 as [HNA HNB]. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
          replace (A + Z.of_nat (4 * length xs + 0)) with (A + nX * 4) in HNB by (clear - LENX; lia).
          apply (u8arr_of_rw_cells asegs) in HNA.
          pose proof (proj1 (u32arr_of_cells asegs m2 pX _ _ xs PCH eq_refl)) as PBA.
          pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + nX * 4); (X, X + 16)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2'.
          pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_SL) as SPC. unfold A_ASAN_MEMCPY_SL in SPC.
          acallxA_sp (bv_unsigned sp + -64)
            (eapply SPC with (h := h2) (LB := (A, 4 * limbs) :: LB) (LF := LF) (DST := A) (SRC := pX) (n := nX * 4) (lo := lo)
                              (ds := repeat (Z_to_bv 8 0) (4 * length xs)) (ss := u32s xs);
             rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
             try eassumption; try reflexivity;
             first [ left; rewrite AMC; reflexivity
                   | rewrite repeat_length; clear - LENX; lia
                   | rewrite u32s_length; clear - LENX; lia
                   | eapply aobj_sub; [exact OA| clear; lia| clear - LIM LENX; lia]
                   | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
                   | right; clear - PA LIM N1; lia
                   | left; clear - AS PC ALO LOS LIM N1; lia
                   | right; pose proof (alloc_ceiling_val R) as ACV; clear - AC PC LIM N1 ACV; lia
                   | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP; lia]
                   | eapply client_wrange_block; [exact HINA| clear; lia| clear - LIM; lia]
                   | clear - NRX LIM LOS SLO NEEDR NRA TOP2 SPA SPR; lia
                   | first [exact C24H | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end] ]).
          clear SPC.
          all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
          match goal with H : u8arr asegs m3 A (u32s xs) |- _ => rename H into HPA end.
          match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
          match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
          match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
          (* [comment removed for export] *)
          zstep. zstep. zstep.
          replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
            by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
          zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
          zstep.
          replace (4 * length xs)%nat with (Z.to_nat (nX * 4)) in PCH by (clear - LENX; lia).
          assert (HINA4 : In (A, 4 * limbs) (((A, 4 * limbs) :: lb_remove pX LB) ++ fdata LF)) by (left; reflexivity).
          assert (CW4 : client_wrange L (((A, 4 * limbs) :: lb_remove pX LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
            destruct Hb as [Hb|Hb]; [left; right; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb] | right; exact Hb]. }
          pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
          eapply aevtA_call.
          { intros mo3 [HK3 MF3].
            eapply SPZ with (h := h2) (LB := (A, 4 * limbs) :: LB) (LF := LF) (buf := pX) (len := nX * 4) (lo := lo) (d := 0) (junk := u32s xs);
              rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; try eassumption; try reflexivity.
            all: try (right; split; [right; replace (nX * 4) with (4 * nX) by (clear; lia); exact HIN | exact PCH]).
            all: try (apply uwc_data; [clear; lia| rewrite unsigned_lit by (clear - CNT; lia); pose proof (alloc_ceiling_val R) as ACV; clear - CNT ALO ACV; lia]).   (* [comment removed for export] *)
            all: clear - CNT LIM NRX LOS SLO NEEDR TOP2 SPA SPR BUD BUDF HV2 HFR2; try (unfold AVOL_CALL in * ); try (unfold fr_charge in * ); try lia.
            all: first [exact C24H | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end]. }
          clear SPZ.
          (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
          destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by qlia.
          ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
            replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
          match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
          rewrite (lb_remove_cons_other A (4 * limbs) pX LB) in HP4, HH4 by (clear - PA LIM N1; lia).
          (* [comment removed for export] *)
          assert (HP4' : presA asegs R ((A, 4 * limbs) :: lb_remove pX LB) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA h2) [] m3 m4).
          { eapply (presA_drop_freed asegs R HIA h2 ((A, 4 * limbs) :: LB) LF _ [] pX (4 * nX) m3 m3 m4);
              [exact HH3| right; exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
              | replace (pX + 4 * nX) with (pX + nX * 4) by (clear; lia); exact HP4].
            intros b xb [Hb|Hb] Hr.
            - subst b. split; [left; reflexivity|]. intros E. injection E as E1 E2. clear - E1 PA LIM N1. lia.
            - split; [right; eapply In_lb_remove; exact Hb|]. intros E. subst b. exact (lb_remove_notin LB pX (4 * nX) ND Hb). }
          clear HP4 PCH PBA OP HINP HINA.
          apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
          presA_transport HP4'.
          apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
          clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
          pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OX2) as OX4.
          assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
          (* [comment removed for export] *)
          assert (HA4 : u32arr asegs m4 A (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (limbs - nX)))).
          { apply u32arr_app. split.
            - eapply (u32arr_of_cells asegs); [| reflexivity]. exact HPA.
            - replace (A + 4 * Z.of_nat (length xs)) with (A + nX * 4) by (clear - LENX; lia).
              replace (Z.to_nat (4 * (limbs - nX))) with (4 * Z.to_nat (limbs - nX))%nat in HNB by (clear - LIM NRX; lia).
              eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
              match goal with H : rw_cells asegs m4 (A + nX * 4) _ |- _ => exact H | |- ?g => idtac "HNB-LOST" end. }
          pose proof (hm_aobj_block asegs R HIA h4 ((A, 4 * limbs) :: lb_remove pX LB) LF m4 A (4 * limbs) HH4 (or_introl eq_refl)) as OA4.
          eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
            [ eapply (fin_tail h4 ((A, 4 * limbs) :: lb_remove pX LB) m4 pX nX A limbs (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (limbs - nX)))); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (rewrite HT4; exact HT2).
          all: try (rewrite length_app, repeat_length; clear - LENX LIM NRX; lia).
          all: try (clear - LIM NRX; lia).
          all: try (eapply client_wrange_block; [exact HINA4| clear; lia| clear - LIM NRX; lia]).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN1-PRE-LEFT:" g end.
          intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & xs' & E9 & MU9 & WM9 & MI9 & HA9 & LEN9 & LV9 & HX9 & ST9 & HH9). subst ms'.
          apply aevtA_done. intros mo9 [HK9 MF9].
          eapply (post_fin mo mo9 h4 (lb_remove pX LB) m4 m9 A limbs xs'); try eassumption.
          all: try (clear - LIM; lia).
          all: first [exact C24H | match goal with |- ?g => idtac "GFIN1-LEFT:" g end].
          { rewrite HT4; exact HT2. }
          { rewrite HS4; exact HS2. }
          { rewrite HF4; exact HF2. }
          { intros y Hy; apply HCS4, HCS2, Hy. }
          { unfold shift_l_PHI, grow_PHI; cbn [md_n md_limbs]; rewrite <- HN. unfold AVOL_CALL in *. clear - HV2 HV4 LIM NRX; lia. }
          { unfold shift_l_FR, fr_charge in *. clear - HFR2 HFR4. lia. }
          { (* [comment removed for export] *)
            eapply presA_trans; [exact HPX2|]. eapply presA_trans.
            - eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                        (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
                [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
              eapply (presA_drop_fresh asegs R HIA h LB LF [(X, X + 16)] A (nX * 4) m2 m3 (bv_unsigned sp));
                [| eapply fresh_apart_sub; [exact HFRA| clear - LIM N1; lia] | clear - ALO LOS SLO NEEDR; lia].
              eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m2 m3); [exact HH1| | clear; lia| exact LOS].
              eapply (presA_of_munch asegs R LB LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK); [| | exact MU2 | exact WM2'].
              + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
                apply Forall_cons; [cbn [fst snd]; replace (A + nX * 4 - A) with (nX * 4) by lia; eapply aobj_crange; eapply aobj_sub; [exact OA| clear; lia| clear - LIM; lia]|].
                apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX2|]. apply Forall_nil.
              + intros c0 Hc. eapply cshd_hcs; [exact HH3| | rewrite HS2; eapply cshd_mono_lb; [exact Hc| intros b Hb; right; exact Hb]]. clear; lia.
            - eapply presA_weaken; [exact HP4'| | intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia| intros y _; exact I].
              intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb]. }
          { intros b Hb; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb]. }
          { intros b Hb; eapply In_lb_remove; exact Hb. }
          { intros [B k] Hb Hn. apply In_lb_remove_keep; [exact Hb|]. apply (nodup_fst_neq LB pX (4 * nX) B k ND HIN Hb).
            intros E. apply Hn. unfold mpd_blk; cbn [md_own md_p md_n]; rewrite EO. left. symmetry. exact E. }
          { unfold mpd_blk; cbn [md_own md_p md_n]; rewrite EO. intros b [<-|[]]. exact (lb_remove_notin LB pX (4 * nX) ND). }
      all: first [exact C24H | match goal with |- ?g => idtac "GROW-LEFT:" g end].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Grow.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L1649577667.2   L19933184425.115L19945959281.114L22700019210.2  L26892418956.1  L29428324939.5  L35653441506.7  L38727942924.3  L40281191306.3  L4235704438.5   L48132467214.7  L59308585216.2  L60098763854.3  L62018535662.1  L68289945359.11500000800\01=01@01D01V01n02702@02P02k03103;03>03_S2nX3NRXS2ra2sp1X2nX2pX2xs5count2lo3xs'4LEN9S2ra2sp1X2nX2xs5count2lo3xs'4LEN9S1yS2spS1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1hS1R3HIA1hS1R3HIA1h2nX3NRXS1R5NEEDR2sp2lo3LOS3SLO3ALOS1a2HaS1R2lo3LOSS1RS2ra2sp1X2nX2pX2xs5count3xs'4LEN9". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG MAX NST XW DSP LOS SLO TOP"] Lemma post_tail0 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Pmo,$3>.Pmo9,$3>.Pm1,P,(11.&40.)(18.(11.&8.))Pm9,P,(11.&40.)(18.(11.&8.))Pxs',(8.(11.&40.))Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Pxa3,(11.&40.)Pxa4,(11.&40.)Pxa5,(11.&40.)Pxa6,(11.&40.)Pxa7,(11.&40.)Px28,(11.&40.)Px29,(11.&40.)Px30,(11.&40.)Px31,(11.&40.)P,(<.$2.VnX,(4=.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))P,(>.(15.(4>.Vxs,)(5.+2.Vcount,))(5.+2.(15.+20.VnX,)))P,(40.$17.VR,(41.VLB,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(1:.&40.Vsp,)(34.VR,)(43.$17.VR,VHIA,Vh,)(1=.(37.$2.$2.)(38.$2.$2.VX,(13.VX,+10.))(20.(37.$2.$2.)))Vm,R13.)P,(19.$17.VR,VHIA,Vh,VLB,VLF,R14.)P,(35.$17.(24.VR,)(25.$17.VR,VHIA,Vh,)R15.VX,+10.)P,(36.(1=.(37.$2.$2.)(38.$2.$2.VpX,(13.VpX,(15.+4.VnX,)))(1=.(37.$2.$2.)(38.$2.$2.Vlo,(1:.&40.Vsp,))(20.(37.$2.$2.))))R16.R15.)P,(39.$17.R17.R16.)P,(22.$17.R17.)P,(2?.$17.R18.VpX,R17.)P,(<.$3:.(10.(11.&40.)R18.)(10.(11.&40.)Vxs,))P,(<.$2.(3;.R19.VnX,)(=.(15.(3;.Vxs,VnX,)(5.+2.Vcount,))(5.+2.(15.+20.VnX,))))P,(1<.$17.R1;.VX,(2>.VpX,(2:.&40.VsgX,)VnX,VpadX,))P,(21.$17.R1<.Vlo,(1:.&40.Vsp,))P,(19.$17.VR,VHIA,Vh,VLB,VLF,R1=.)P,(3?.R21.R20.)P,(45.$17.VR,VHIA,Vh,R21.)(49.$17.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Lr,$2.LdX',$:.(;.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,R2.R1.)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)$7.Vlo,Vm,R23.(4:.(28.(29.Vra,Vsp,Vgp,Vtp,R1>.R1=.R1<.Vs0,Vs1,(2:.&40.=)R1;.R1:.R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(2;.Vra,)Vfc,(2<.(11.&40.))R20.(2=.$17.))R22.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HN FITv HP1 HH1 OX1 MU9 WM9 MI9 HA9 LEN9 LV9 HX9 ST9 HH9 MF9 HK9.
    basic_facts h LB m9 HH9 TOP.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & XB & BR).
    dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN.
    assert (CASES : ownX = LNull \/ ownX = LHeap) by (destruct ownX; [left; reflexivity| right; reflexivity| exfalso; exact (NST eq_refl)]).
    assert (HP9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
    { eapply presA_trans; [exact HP1|].
      destruct CASES as [EO|EO]; pose proof HOWN as HOWN'; rewrite EO in HOWN'.
      + (* [comment removed for export] *)
        destruct HOWN' as [EP En].
        eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                  (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(pX, pX + 4 * nX)]);
          [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside fst snd]; rewrite EP, En; clear; intros y _; lia].
        eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m1 m9); [exact HH9| | clear; lia| exact LOS].
        eapply (presA_weaken asegs R LB LB LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                  (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(pX, pX + 4 * nX); (lo, bv_unsigned sp)]);
          [| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside fst snd]; clear; intros y Hy; tauto].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m1 m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH9| | exact Hc]; clear; lia | exact MU9 | exact WM9].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; rewrite EP, En; intros a Ha; exfalso; clear - Ha; lia|].
        apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|]. apply Forall_nil.
      + ddestruct HOWN' as (N1 & HIN & HP16 & _).
        eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] pX (4 * nX) m1 m1 m9);
          [exact HH1| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
        * intros b xb Hb Hr. unfold mpd_keep in Hb. cbn [md_own md_p md_n] in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
          split; [exact Hb|]. intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
        * eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16); (pX, pX + 4 * nX)]);
            [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside fst snd]; clear; intros y Hy; tauto].
          eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m1 m9); [exact HH9| | clear; lia| exact LOS].
          eapply (presA_weaken asegs R LB LB LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(pX, pX + 4 * nX); (lo, bv_unsigned sp)]);
            [| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside fst snd]; clear; intros y Hy; tauto].
          eapply (presA_of_munch asegs R LB LF _ _ _ _ m1 m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH9| | exact Hc]; clear; lia | exact MU9 | exact WM9].
          unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (pX + 4 * nX - pX) with (4 * nX) by lia; eapply hcs_block; [exact HH9| exact HIN]|].
          apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|]. apply Forall_nil. }
    assert (MA9 : mpd_at asegs m9 LB (mkMPD X sgX nX pX xs' padX ownX)).
    { eapply mpd_at_rebuild; [exact NST| exact HX9| exact XAL| exact X0| rewrite LEN9; exact LENX
                             | unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGX| |].
      + intros E. rewrite E in HOWN. exact HOWN.
      + intros E. rewrite E in HOWN. ddestruct HOWN as (N1 & HIN & HP16 & _). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16| exact HA9]. }
    eapply (post_shift mo mo9 h m9 LB nX pX xs' ownX); try eassumption; try reflexivity.
    all: first [ lazymatch goal with
                 | |- limbs_val _ = _ => eapply (shifted_val xs xs' nX); try eassumption; reflexivity
                 | |- nX <= nX => clear; lia
                 | |- forall x, _ -> _ => first [ intros y Hy; exact Hy | intros y Hy; left; exact Hy ]
                 | |- havol _ _ _ _ <= _ => unfold shift_l_PHI; rewrite <- HN; unfold grow_PHI, AVOL_CALL; clear - NRX; lia
                 | |- hfr _ _ _ _ <= _ => unfold shift_l_FR, fr_charge; clear; lia
                 | |- mpd_out _ _ _ _ => unfold mpd_out; cbn [md_addr md_own md_p md_n mpd_blk]; split; [reflexivity|]; split; [exact NST|];
                                         split; [intros b Hb; left; exact Hb|]; split; [intros b Hb _; exact Hb| intros b _ _; reflexivity]
                 end
               | idtac ].
    all: first [exact C24H | match goal with |- ?g => idtac "PT0-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0390@D13554616751.120D13554616751.121D21524471097.140D30841324822.121D35881667587.120D35881667587.121D65415345542.140K335357944.140  K42587433812.120K42587433812.121K43080499426.140L11808292612.147L11808292741.146L12068146560.5  L12283411672.115L12751102156.11 L12757393009.8  L13301871092.115L14106684376.114L1649577667.2   L1685717371.0   L17646078182.116L19892441013.1  L22706556426.7  L23100341967.119L24579960702.2  L25070343932.10 L25377982725.5  L29428324939.5  L30240581978.4  L31955952619.5  L32027975233.0  L32426051249.2  L331342290.2    L34462250985.2  L34716616382.0  L34994544387.115L35049057794.11 L35055341759.15 L35653441506.7  L36484385790.139L37032017814.2  L37034127760.5  L37786237729.0  L38727942924.3  L38948636245.0  L39025343476.8  L39029471052.15 L39172636981.0  L39280637297.0  L39284637285.0  L39841478693.15 L39843563160.11 L39845737629.8  L39887139444.115L40834179097.119L41288976216.115L41415922540.5  L41417986918.2  L41418169706.2  L4233574524.8   L42594106808.2  L4296336400.15  L4302625453.11  L43061363337.114L43082027553.2  L43681423538.139L44397119898.2  L44866992728.115L45611961194.12 L45614069207.9  L45898055924.115L46160487540.119L46160487540.139L46165130557.116L47416350744.6  L47954684338.138L47955344026.2  L47957478064.147L48317505440.2  L48429268312.115L50666159343.12 L5145216728.115 L51925114228.115L52474017674.7  L52476102967.9  L5255722929.116 L53016254335.11 L53022550466.15 L53516993810.8  L53519152530.139L5697346430.3   L57933933556.115L58402729315.3  L59025125053.10 L59027214336.14 L59308517357.5  L59308518135.5  L59308585216.33 L59308628433.6  L59308668813.4  L59308696420.5  L59335885566.2  L60098763854.3  L61462073826.5  L62624422312.34 L62624996514.50 L62627095698.39 L63306560470.2  L63962036340.114L64194470200.2  L64372451842.1  L64425109425.6  L65381926838.5  L66151427842.16 L66151427842.17 L67041875997.11 L67158371251.115L67353064626.139L7274816372.115 L774765788.5    L8722184664.115 N14106276406.141N29298589664.141O2464015924.140 O3346460878.140 P43080499426.140Q12370813529.120Q15457446739.117Q15457446739.118Q15643324129.116Q17207350632.121Q18365925601.117Q18694146040.121Q19120365881.120Q21798041355.121Q21879645826.117Q25157988860.121Q25513505925.119Q25513505925.120Q25662358575.121Q26207421841.121Q26207721832.122Q26207721832.142Q26209519061.141Q26209818583.139Q26220436438.119Q27907200258.117Q30972598960.126Q30985071382.125Q30987168052.142Q31228709292.121Q31271525473.117Q31394594844.121Q31651985788.141Q31654082872.121Q31836793127.140Q32655500769.117Q33918256002.117Q35014437530.121Q35717497884.121Q36425882626.117Q37620952116.119Q3830427394.117 Q39212284437.122Q39212284437.142Q39845525023.140Q39939554818.117Q41152393185.117Q4143427880.121 Q43925228937.122Q43925228937.142Q43928033258.118Q44648843873.117Q49698585326.118Q49698585326.119Q50800894295.140Q51235796833.117Q53969758199.121Q5472625193.119 Q5485174314.120 Q5485600919.121 Q59843137889.117Q60511567613.122Q60511567613.142Q60697995187.122Q60697995187.142Q6143569392.120 Q61802139820.121Q6416456232.121 Q64255486968.121Q66522067074.117Q67528989526.120Q67528989526.121Q7377275490.119 Q7377275490.120 Q8882910347.139 Q8884615306.119 Q9534674041.119 Q9540573304.139 Q9843367298.116 00000e01l02D03<03c04_05E05g06[07a07b08C09609L09X09Y09Z09f0:20::0:;0:G0:K0:c0:o0;60;70;K0;]0;m0;n0;o0<70<80<90<:0<F0<G0<Z0=20=O0=Z0=e0=f0=o0>00>O0?10?20?30?40?N0?O0?f0@20@@0@L0@_0@`0@a0A?0A@0AA0AB0Ad0Ae0BO0BW0Bc0Bd0Be0C10CC0CU0Cg0D@0DS0D[0E:0E@0EL0En0F:0FF0F[0F\0Fn0Fo0GV0GZ0Gf0Gg0H30H?0H@0HA0HS0Hf0Hg0I@0IN0Ia0Ih0J20J<0J=0J>0J?0JG0JS0JZ0J^0J_0K60KQ0KR0L50LA0LM0LY0Ll0M80MS0M_0M`0Ma0Mb0N50N?0NI0NS0NY0Nc0Nn0OV0OW0Om0P80PT0QB0QC0QI0QO0QU0Q[0Qa0Qg0R=0Rc0SI0So0T;0TE0TI0TO0TU0T_0Ti0U?0UK0UL0Ub0Uh0V>0VD0VJ0V`0W60W@0WA0WG0WM0WW0Wa0X50XI0XP0XZ0Xf0Xl0Y20Y80YB0YF0YJ0YS0Y\0Yb0Yc0Yn0Yo0ZE0Zm0[g0\O0]F0]L0]R0]V0]Z0^0S1R5NEEDR2ra2sp1X2xs2lo3LOS3SLO3SPR2X02HB5Ha_st5Hl_stS1R5NEEDR2ra2sp2s01X2xs2lo3LOS3SLO3SPR2X02HB5Ha_st5Hl_st2s12s22s32s42s5S1R3HIA1h2ra2sp1X2xs3TOPS1R5NEEDR2ra2sp2s61X2xs2lo3LOS3SLO3SPR2X02HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X2xs3TOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X2xs3TOP2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5NEEDR2ra2sp1X2xs2lo3LOS3SLO3SPR2X0S1R5NEEDR2sp1X2pX2xs2lo3SLO2P03DSXS1R5NEEDR2ra2sp1X2pX2xs2lo3SLO2P03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X2pX2xs2lo3SLO2P03DSX2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS2ra2sp1X2nX2xs5count5limbs2LR2K1S2ra2sp1X2nX2pX2xs5count3CNT3SPR2X03NRX2BR5limbs2LRS2nX2xs5count5limbs2LRS2ra2sp1X2xsFFS2ra2sp1X2xsS2ra2sp1X2xsS2nX3NRXSS2ra2sp1X2xsS2spS1R5NEEDR2sp2lo3SLO1y2HyS2ra2sp1X2xsS2nX2pXFS2nX2xs5count3CNT2BRS1R2lo3LOS3ALO3ACPS2nX2xs5count2K0FSS2nX3NRXFFSS2ra2sp1X2xsFS2sp2nX2xs3SPR4LENXS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X2nX2xs3SPR2X03NRX2BRS5count3CNTS5count3CNTSS1R3HIA1hSS1R5NEEDR2sp2lo3SLO3SPA3SPR3LO0S1R5NEEDR2sp2xs2lo3SLO3SPA3SPR3LO0SSSS1R5NEEDR2sp2xs2lo3SLO3SPRFS1R5NEEDR2sp2lo3SLO3SPRS2ra2sp1X2xsS1R2ra2sp1X2xsS2ra2sp1X2xsS2nX2xs5count5limbsSSS1R3HIA1h2nX2xs5count5limbs2LRFFFS1R5NEEDR2ra2sp1X2xs2lo3SLO3SPR2X0FS2ra2sp1X2nX2xs5count3CNT3SPR2X03NRX2BR2K0S2nX3NRXS2ra2sp1X2xsFFS2ra2sp1X2xsS2ra2sp1X2xs2X02XBS2ra2sp1X2xs2X02XBS2ra2sp1X2xs2X02XBS2nX2xs5count5limbs2LR2K1S2ra2sp1X2nX2xs3NRXS2nX3NRXS2ra2sp1X2nX2xs5count3NRX5limbsS1X2X0S2ra2sp1X2xsS1R2sp2nX2pX2xs2lo3LOS3ALO4LENX2PCS2ra2sp1X2xsS2ra2sp1X2xsS1R2nX2pX3NRX2PC2B01HFS2ra2sp1X2xs2X02XBFS1R5NEEDR2sp2nX2pX2xs2lo3SLO3SPR4LENX1HS2spS2ra2sp1X2xsFS2ra2sp1X2xsS2nX2xs4LENXFFS2nX2xs5count1p2LNS2nX2xs5count2K02LTFS2nX2xs5count5limbs2LR2K2S2nX1l4LENX2EnS2nX2xs5count2K02GES2pX2B0S1R2lo3LOSS2nX2xs2BRFFFS2nX3NRXS2ra2sp1X2xsS1R3ACPS2pXFS2nX2xs5count5limbs3LGES2pX2r04HP161q1r1H2H02q02H4FS1R5NEEDR2sp2nX2pX2xs2lo3SLO4LENX1DS2ra2sp1X2xsS2ra2sp1X2xsS2ra2sp1X2xsS1R5NEEDR2sp2lo3SLOS2ra2sp1X2xsS1R5NEEDR2sp2xs2lo3SLO2x21CS2sp2xs2x21CFFFS2ra2sp1X2xs3XAL2X0S2sp2xs2HBS2sp2xs2HBS2sp2xs2loS1X2xsS2sp2xs2loS1R2xs4IMG'S1R5NEEDR2sp2s62xs2lo3SLO2HB5Ha_st5Hl_stFS1R5NEEDR2sp2xs2lo3SLOS1R2xs4IMG'S2ra2sp2xs2lo2HB5Ha_st5Hl_stS2sp2s02xs2lo2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS1X2xsS1X2xsS1X2xsS1X2xsS1X2xsS1X2xsS1R5NEEDR2sp2xs2lo3SLOS1R5NEEDR2sp2xs2lo3LOS3SLO3ALO3ACP3SPRS1R5NEEDR2sp2xs2lo3LOS3SLO3ALO3ACP3SPRS1R5NEEDR2sp2xs2lo3LOS3SLO3ALO3ACP3SPRS1R2xs5ALWF'S2sp2xs2loS2xsS1X2xsS1X2xsS2sp2xs2loS2sp2xs2loS1R5NEEDR2sp2xs2lo3SLOS1R2xs5ALWF'FS1R5NEEDR2sp2xs2lo3SLOS1X2xsS1R5NEEDR2sp2xs2lo3SLOS1X2xsS1X2xsS1R5NEEDR2sp2xs2lo3SLOS1R5NEEDR2sp2xs2lo3SLOS2sp2xs2loFS1X2xsS1X2xsS2sp2xs2HBS2sp2xs2loS2sp2xs3SPR2HB5Ha_stS2sp2xs3SPR2HB5Ha_stS2sp2xsS2sp2xs2loS1R2xs5ALWF'S1X2xsS1X2xsS1X2xsS2sp2xs2loS2xsS2xsS1X2xs2X0S1X2xs2X0S1X2xsFS1R2xs4IMG'FS1R5NEEDR2sp2xs2lo3SLOS1R5NEEDR2ra2sp2xs2lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2sp2s02xs2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5NEEDR2ra2sp2xs2lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2sp2s02xs2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S1X2xsS1X2xsS2xsS2xsS1R5NEEDR2sp2xs2lo3SLO". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC AMS NEEDR NEEDA HND DIMG C24H MAX NST CNT XW DSP LOS SLO TOP SPA TPV"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "Pmo,$3>.Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)P,(19.$17.VR,VHIA,Vh,VLB,VLF,Vm,)P,(45.$17.VR,VHIA,Vh,R?.)P,(21.$17.Vm,Vlo,(1:.&40.Vsp,))P,(22.$17.Vm,)P,(35.$17.(24.VR,)(25.$17.VR,VHIA,Vh,)Vm,VX,+10.)P,(4.(13.(46.$17.VR,VHIA,Vh,)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,))$5<.)P,(4.(13.(47.$17.VR,VHIA,Vh,)$7.)$5=.)(5>.$17.(49.$17.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Lr,$2.LdX',$:.(;.Vcount,(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,R2.R1.)(6.(42.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)Vcount,)$7.Vlo,Vm,R15.)(4:.(28.(29.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(2:.&40.VX,)(2:.&40.Vcount,)R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(2:.&40.$5?.)Vfc,(2<.(11.&40.))Vm,(2=.$17.))R15.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo ST MI OX BUD BUDF. unfold A_MPI_SHIFT_L. basic_facts h LB m HH TOP.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & XB & BR).
    pose proof (HND _ _ _ _ HH) as ND.
    dpose MAX as [[HXS (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, HOWN.
    destruct XW as [CW DXP]. cbn [md_addr md_own md_p md_n] in CW, DXP.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF BA]. rewrite Forall_forall in HF.
    (* [comment removed for export] *)
    assert (PB : 0 <= pX /\ pX + 4 * nX <= alloc_ceiling
                 /\ (ownX = LHeap -> 0 < pX /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ u32arr asegs m pX xs /\ 1 <= nX)
                 /\ (ownX = LNull -> pX = 0 /\ nX = 0)).
    { destruct ownX; [| | exfalso; exact (NST eq_refl)].
      - destruct HOWN as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
        split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
      - ddestruct HOWN as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        split; [clear - B0; lia|]. split; [exact BC|].
        split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| split; [exact HXL| exact N1]]]]| intros E; discriminate E]. }
    ddestruct PB as (P0 & PC & PHEAP & PNULL).
    assert (CASES : (ownX = LNull /\ pX = 0 /\ nX = 0 /\ xs = []) \/ (ownX = LHeap /\ 1 <= nX)).
    { destruct ownX; [left| right| exfalso; exact (NST eq_refl)].
      - destruct (PNULL eq_refl) as [EP En]. split; [reflexivity|]. split; [exact EP|]. split; [exact En|].
        destruct xs; [reflexivity| exfalso; cbn in LENX; clear - LENX En; lia].
      - split; [reflexivity| exact (proj2 (proj2 (proj2 (proj2 (PHEAP eq_refl)))))]. }
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 9 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { apply presA_nil_any. eapply (presA_tail0 asegs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact MU0| exact WM0]. }
    assert (PCH1 : ownX = LHeap -> rw_cells asegs m1 pX [CB (4 * length xs)%nat (u32s xs)]).
    { intros E. ddestruct (PHEAP E) as (B0 & _ & _ & HXL & _). apply u32arr_cells.
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PC ALO LOS SLO NEEDR LENX; lia]. }
    (* [comment removed for export] *)
    assert (XL7 : Z.land X 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact XAL | clear - XAL; Z.div_mod_to_equations; lia]).
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ X0 XB; rewrite ?Z.mod_small in KZ by lia; lia|].
    zstep. zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA XL7; rewrite ?XL7 in KA; rewrite ?Zmod_0_l in KA; lia|].
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _
              (mpi_core_bitlen_postA asegs (Z_to_bv 64 0x9d4dc) SP' gp tp (Z_to_bv 64 count) (Z_to_bv 64 X) (Z_to_bv 64 (X + 10))
                 s3 s4 SHX SHX10 s7 s8 s9 s10 s11 F fc xs nX lo m1) _ _ KINV);
      [ | intros y Hy; exact Hy | ].
    { destruct CASES as [(EO & EP & En & EL)|(EO & N1)].
      - rewrite EP, En, EL.
        pose proof (A_mpi_core_bitlen_z_spec AL IMG) as SP. unfold mpi_core_bitlen_z_stmtA, MPI_CORE_BITLEN_STACK_A, A_MPI_CORE_BITLEN in SP.
        eapply SP with (A := 0) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; try eassumption; try reflexivity.
        all: try (pose proof (art_alwf asegs R HIA); assumption).
        all: try (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
        all: clear - SLO SPA SPR LO0 NEEDR; try lia.
        all: first [exact C24H | match goal with |- ?g => idtac "BL0-PRE-LEFT:" g end].
      - pose proof (A_mpi_core_bitlen_spec AL IMG) as SP. unfold mpi_core_bitlen_stmtA, MPI_CORE_BITLEN_STACK_A, A_MPI_CORE_BITLEN in SP.
        ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & _).
        eapply SP with (A := pX) (n := nX) (xs := xs) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; try eassumption; try reflexivity.
        all: try (pose proof (art_alwf asegs R HIA); assumption).
        all: try (eapply (proj1 (u32arr_of_cells asegs m1 pX _ _ xs (PCH1 EO) eq_refl))).
        all: try (eapply hm_aobj_block; [exact HH| exact HIN]).
        all: try (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
        all: try (clear - HP16; Z.div_mod_to_equations; lia).
        all: try (destruct (DSP ltac:(rewrite EO; discriminate)); clear - NRX LENX N1 LO0 SLO SPA SPR NEEDR H; lia).
        all: clear - NRX LENX B0 N1 LO0 SLO SPA SPR NEEDR; try lia.
        all: first [exact C24H | match goal with |- ?g => idtac "BL1-PRE-LEFT:" g end]. }
    cbv beta. intros ms' PO. unfold mpi_core_bitlen_postA, MPI_CORE_BITLEN_STACK_A in PO.
    destruct_exs PO. ddestruct PO as (E & MU1 & WM1 & MI2 & EA0 & ST2). subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MU1, ST2 by qlia.
    replace (ret_pc (Z_to_bv 64 0x9d4dc)) with (Z_to_bv 64 0x9d4dc) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match type of EA0 with ?a = _ => subst a end.
    transport_after_callA asegs m1 m2 MU1. transport_after_call asegs m1 m2 MU1 WM1.
    assert (HP2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
    { eapply presA_trans; [exact HP1|]. apply presA_nil_any.
      eapply (presA_tail0 asegs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| | exact WM1].
      eapply munch_weaken; [| exact MU1]. intros y Hy. cbn [outside fst snd] in *. clear - SLO NEEDR Hy. lia. }
    rename MU1 into MUb. rename WM1 into WMb. try clear MI. rename MI2 into MI.
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. zstep. rewrite ?Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (HN : nX = shift_l_n count dX).
      { unfold shift_l_n; cbn [md_n md_limbs]. destruct (Z.ltb_spec (nX * 32) (bits + count)) as [LT|GE]; [exfalso; clear - LT K0; lia| reflexivity]. }
      assert (FIT : limbs_val xs * 2 ^ count < 2 ^ (32 * nX)).
      { pose proof (core_bitlen_val xs nX ltac:(clear - NRX; lia)) as BV.
        assert (LVX : limbs_val xs = lval xs nX) by (unfold lval; rewrite firstn_all2 by (clear - LENX; lia); reflexivity). rewrite LVX.
        destruct BV as [[B0 L0]|[B1 [L1 L2]]].
        - rewrite L0. rewrite Z.mul_0_l. apply Z.pow_pos_nonneg; clear - NRX; lia.
        - apply (Z.lt_le_trans _ (2 ^ bits * 2 ^ count)); [apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; clear - CNT; lia| exact L2]|].
          rewrite <- Z.pow_add_r by (clear - BR CNT; lia). apply Z.pow_le_mono_r; [clear; lia| clear - K0; lia]. }
      destruct CASES as [(EO & EP & En & EL)|(EO & N1)].
      - (* [comment removed for export] *)
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply (tail_walk h LB m2 pX nX xs); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
        all: try (unfold mpi_cells; exact HXS).
        all: try (rewrite EP, EL; apply u32arr_nil).
        all: try (rewrite EP; reflexivity).
        all: try (left; exact En).
        all: try (rewrite EP; clear; lia).
        all: try (rewrite EP, En; left; exact LO0).
        all: try (rewrite En; replace (4 * 0) with 0 by (clear; lia); first [apply aobj_nil | intros a Ha; exfalso; clear - Ha; lia]).
        all: try (right; rewrite EP, En; clear - X0; lia).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "T0-PRE-LEFT:" g end.
        intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & xs' & E9 & MU9 & WM9 & MI9 & HA9 & LEN9 & LV9 & HX9 & ST9 & HH9). subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply (post_tail0 mo mo9 m2 m9 xs'); try eassumption.
        all: first [exact C24H | match goal with |- ?g => idtac "T0-LEFT:" g end].
      - (* [comment removed for export] *)
        ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & _).
        pose proof (PCH1 EO) as PCH.
        eapply (rw_cells_transport asegs _ m1 m2) in PCH; [| exact MUb| exact WMb
          | cbn [disjoint_from cells_size csize Nat.add]; pose proof (DSP ltac:(rewrite EO; discriminate)) as D; clear - D LENX SLO NEEDR NRX; lia].
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply (tail_walk h LB m2 pX nX xs); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
        all: try (unfold mpi_cells; exact HXS).
        all: try (eapply (u32arr_of_cells asegs); [exact PCH| reflexivity]).
        all: try (clear - HP16; Z.div_mod_to_equations; lia).
        all: try (right; exact B0).
        all: try (pose proof (alloc_ceiling_val R); clear - B0 PC NRX H; lia).
        all: try (exact (DSP ltac:(rewrite EO; discriminate))).
        all: try (eapply client_wrange_block; [apply in_app_iff; left; exact HIN| clear; lia| clear; lia]).
        all: try (eapply hm_aobj_block; [exact HH| exact HIN]).
        all: try (exact (DXP EO)).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "T1-PRE-LEFT:" g end.
        intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & xs' & E9 & MU9 & WM9 & MI9 & HA9 & LEN9 & LV9 & HX9 & ST9 & HH9). subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply (post_tail0 mo mo9 m2 m9 xs'); try eassumption.
        all: first [exact C24H | match goal with |- ?g => idtac "T1-LEFT:" g end]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (bits_to_limbs_ge (bits + count) ltac:(clear - BR CNT; lia)) as LGE.
    replace (Z.b2z (0 <? Z.land (bits + count) 31)) with (if Z.land (bits + count) 31 =? 0 then 0 else 1)
      by (pose proof (Z.land_nonneg (bits + count) 31) as LN; destruct (Z.land (bits + count) 31); [reflexivity| reflexivity| exfalso; clear - LN; lia]).
    set (limbs := (bits + count) ≫ 5 + (if Z.land (bits + count) 31 =? 0 then 0 else 1)) in *.
    assert (LD : limbs = limbs_of_bits (bits + count)).
    { subst limbs. unfold limbs_of_bits. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 5) with 32. change 31 with (Z.ones 5). rewrite Z.land_ones by (clear; lia). reflexivity. }
    assert (LR : nX < limbs /\ 1 <= limbs <= (bits + count) / 32 + 1).
    { rewrite LD in *. unfold limbs_of_bits in *.
      destruct ((bits + count) mod 32 =? 0); clear - K0 LGE BR CNT NRX; Z.div_mod_to_equations; nia. }
    assert (HN : limbs = shift_l_n count dX).
    { unfold shift_l_n; cbn [md_n md_limbs]. destruct (Z.ltb_spec (nX * 32) (bits + count)) as [LT|GE]; [exact LD| exfalso; clear - GE K0; lia]. }
    assert (FIT : limbs_val xs * 2 ^ count < 2 ^ (32 * limbs)).
    { pose proof (core_bitlen_val xs nX ltac:(clear - NRX; lia)) as BV.
      assert (LVX : limbs_val xs = lval xs nX) by (unfold lval; rewrite firstn_all2 by (clear - LENX; lia); reflexivity). rewrite LVX.
      destruct BV as [[B0 L0]|[B1 [L1 L2]]].
      - rewrite L0. rewrite Z.mul_0_l. apply Z.pow_pos_nonneg; clear - LR; lia.
      - apply (Z.lt_le_trans _ (2 ^ bits * 2 ^ count)); [apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; clear - CNT; lia| exact L2]|].
        rewrite <- Z.pow_add_r by (clear - BR CNT; lia). apply Z.pow_le_mono_r; [clear; lia| clear - LGE; lia]. }
    clearbody limbs. clear LD LGE.
    assert (PCH2 : ownX = LHeap -> rw_cells asegs m2 pX [CB (4 * length xs)%nat (u32s xs)]).
    { intros EO. pose proof (PCH1 EO) as PCH.
      eapply (rw_cells_transport asegs _ m1 m2) in PCH; [exact PCH| exact MUb| exact WMb
        | cbn [disjoint_from cells_size csize Nat.add]; pose proof (DSP ltac:(rewrite EO; discriminate)) as D; clear - D LENX SLO NEEDR NRX; lia]. }
    assert (PHEAP' : ownX = LHeap -> 0 < pX /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ 1 <= nX).
    { intros EO. ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1). split; [exact B0|]. split; [exact HIN|]. split; [exact HP16| exact N1]. }
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      rewrite ?Z.mod_small in K1 by (clear - LR BR CNT NRX; Z.div_mod_to_equations; lia).
      assert (MA2 : mpd_at asegs m2 LB dX).
      { eapply mpd_at_rebuild; [exact NST| unfold mpi_cells; exact HXS| exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGX| exact PNULL|].
        intros E. ddestruct (PHEAP' E) as (B0 & HIN & HP16 & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
        eapply (u32arr_of_cells asegs); [exact (PCH2 E)| reflexivity]. }
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply epi_walk with (hc := h) (LBc := LB) (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); try eassumption
        | intros y Hy; exact Hy | ].
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "E1-PRE-LEFT:" g end.
      intros ms' PO. destruct_exs PO. destruct PO as [E ST9]. subst ms'.
      apply aevtA_done. intros mo9 [HK9 MF9].
      eapply post_keep; try eassumption; try reflexivity.
      all: try (intros y Hy; exact Hy).
      all: try (unfold shift_l_PHI; rewrite <- HN; unfold grow_PHI, AVOL_CALL; clear - LR; lia).
      all: try (unfold shift_l_FR, fr_charge; clear; lia).
      all: first [exact C24H | match goal with |- ?g => idtac "E1-LEFT:" g end]. }
    rewrite ?Z.mod_small in K1 by (clear - LR BR CNT NRX; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?Z.mod_small in K2 by (clear - LR K1 NRX; lia); clear - K2 LR; lia|].
    eapply (grow_walk mo m2 limbs); try eassumption.
    all: try (clear - LR K1; lia).
    all: first [exact C24H | match goal with |- ?g => idtac "MW-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_mpi_shift_l_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "PR,$60.PHIA,(61.$17.R1.)P,(62.(24.R2.))P,(63.$17.R3.R2.$64.)P,(<.$2.(65.R4.)$66.)P,(<.$2.(67.R5.)$68.)P,(<.$2.(69.R6.)$6:.)P,(4.=(6;.R7.))P,(4.=(6<.R8.))P,Ph,(16.$17.R9.R8.)PLB,(8.$9.)PLF,(8.$9.)Pm,P,(11.&40.)(18.(11.&8.))P,(19.$17.R=.R<.R4.R3.R2.R1.)(6=.$2.(6>.(37.$2.$2.)$2.(55.$2.$2.)R4.))P,(3.(4.(6?.(31.R:.))(70.(31.R:.)))(4.(71.(31.R:.))(72.(31.R:.))))(73.$17.R;.R:.$5?.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMC AMS NEEDR NEEDA HND DIMG. unfold mpi_shift_l_stmtA_c, mpi_xop_stmtA_c.
  intros until d. intros HH HK MX HNS CNT XW DSP ST LOS SLO TOP SPA TPV MI RA2 OXA BUD UW XUW BUDF C24H -> ->.
  destruct dX as [X sg n P limbs pad own].
  eapply main_walk; try eassumption. exact (proj1 OXA).
Qed.

(* [comment removed for export] *)
Lemma A_mpi_shift_l_spec_closed_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_l_c24 ()) "PR,$60.PHIA,(61.$17.R1.)P,(62.(24.R2.))P,(<.$2.(74.R3.)$75.)P,(<.$2.(76.R4.)$77.)P,(<.$2.(65.R5.)$66.)P,(<.$2.(67.R6.)$68.)P,(<.$2.(69.R7.)$6:.)P,Pm,P,(11.&40.)(18.(11.&8.))P,(78.R9.R1.)(79.R2.)P,(4.=(6<.R9.))P,(4.=(7:.R:.))P,(4.=(6;.R;.))P,Ph,(16.$17.R<.R;.)PLB,(8.$9.)PLF,(8.$9.)Pm,P,(11.&40.)(18.(11.&8.))P,(19.$17.R10.R?.R4.R3.R2.R1.)(6=.$2.(6>.(37.$2.$2.)$2.(55.$2.$2.)R4.))P,(3.(4.(6?.(31.R=.))(70.(31.R=.)))(4.(71.(31.R=.))(72.(31.R=.))))(73.$17.R>.R=.$5?.)")
(* [comment removed for export] *).
Proof.
  intros. eapply A_mpi_shift_l_spec_c; eauto. eapply A_zeroize_and_free_spec; eauto.
Qed.
