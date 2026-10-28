(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_mpi_resize_clear.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_resize_clear.
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
Ltac2 gd_tbl_A_mpi_resize_clear_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_c24.mpi_xop_stmtA_c"; "C24_RESIZE_CLEAR_c"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear.resize_clear_FR"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_resize_clear.resize_clear_R"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_RESIZE_CLEAR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear.A_WRAP_CALLOC_RC"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear.A_ASAN_MEMSET_RC"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "mpi_resize_clear_stmtA_c"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_MEMSET_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "mpi_resize_clear_coreA_c"; "mpi_resize_clear_coreA_r_c"].



Definition C24_RESIZE_CLEAR_c : Z := 1.
Definition mpi_resize_clear_stmtA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "(0.O4.O3.O2.O1.+60.$1.Lnl,$2.(3.(4.=R1.)(5.R1.(6.+2.+40.)))L,$7.Lnl,$2.(8.R1.)$9.LLB,(:.$;.)LdX,$7.Lnl,$2.Lr,$2.LdX',$7.(<.R3.R4.R5.R2.R1.))")
(* [comment removed for export] *).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09d20c]).
Local Ltac zchk_new ::= constr:([0x09cff4; 0x09cff8; 0x09d010; 0x09d014; 0x09d01c; 0x09d028; 0x09d030; 0x09d034; 0x09d038; 0x09d03c; 0x09d048; 0x09d080; 0x09d084; 0x09d188; 0x09d18c; 0x09d190; 0x09d1cc; 0x09d1d0; 0x09d1d4; 0x09d200; 0x09d230; 0x09d248]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_RC.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_RC.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Hypothesis C24H : cnt24 LB + C24_RESIZE_CLEAR_c <= C24MAX.     (* [comment removed for export] *)
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sg n P : Z) (limbs : list word) (pad : word) (own : limb_own) (nl lo d : Z).
  Local Notation dX := (mkMPD X sg n P limbs pad own).
  Hypothesis HNS : own <> LStatic.
  Hypothesis NL : 0 <= nl < 2^64.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis DSP : own <> LNull -> P + 4 * n <= lo \/ bv_unsigned sp <= P.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 96 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis XUW : uw_obj R X 16 d.

  Ltac rt_facts hh :=
    pose proof (hcs_ok asegs R HIA hh) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hh) as SCS0;
    pose proof (arl_need_rt_free R) as NRF; pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ hh ?LBx LF ?mx, TOPx : bv_unsigned sp <= htop _ _ _ hh |- _ =>
      pose proof (hm_top asegs R HIA hh LBx LF mx HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange (hcs asegs R HIA hh) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPx HTOP; lia])
    end.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHX10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Notation FRAME := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)
  Notation POST := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                      (fun r dX' => resize_clear_R nl dX LB r dX') (grow_PHI nl) (resize_clear_FR d) lo).

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L12283411672.98L14106684376.98L29428324939.5 L35653441506.7 L36423571333.97L41288976216.98L44866992728.98L48429268312.98L49345641752.96L5145216728.98 L60098763854.3 L8722184664.98 Q15641568614.97Q18364007270.97Q21877861637.97Q27904925317.97Q32653586022.97Q33915848709.97Q3832210565.97 Q39941338501.97Q41154176102.97Q44650594790.97Q51233520870.97Q59840699110.97Q66523986693.97Q9840924165.97 00000400800J00d01;01?01C01G01K01O01Y01]01d01k02>02Q02X02k03>03Q03X03_03f03m04@04SS2spS2spS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS1R5NEEDR2sp2lo3SLO3SPRS2spS2spS2spS2spS2spS1R2lo3LOSS2spS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Phc,(=.$>.VR,VHIA,)PLBc,(:.$;.)Pmm,P,(?.&40.)(10.(?.&8.))Pr,$2.Pxra,(?.&40.)Pxs0,(?.&40.)Pxs1,(?.&40.)Pxs2,(?.&40.)Pxs3,(?.&40.)Pxs4,(?.&40.)Pxs5,(?.&40.)Pxs6,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,R1:.R19.VLF,R18.)P,(4.(12.&40.Vsp,)(13.$>.VR,VHIA,R1;.))P,(14.$>.R1:.(15.(12.&40.Vsp,)-40.)(16.$17.(19.Vs6,)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R1;.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R1<.)(1=.$>.(1>.VR,)(1?.$>.VR,VHIA,R1?.)Lms',$20.(21.(?.&40.)Lx5,(?.&40.)(21.(?.&40.)Lx6,(?.&40.)(21.(?.&40.)Lx7,(?.&40.)(21.(?.&40.)La1',(?.&40.)(21.(?.&40.)La2',(?.&40.)(21.(?.&40.)La3',(?.&40.)(21.(?.&40.)La4',(?.&40.)(21.(?.&40.)La5',(?.&40.)(21.(?.&40.)La6',(?.&40.)(21.(?.&40.)La7',(?.&40.)(21.(?.&40.)Lx28,(?.&40.)(21.(?.&40.)Lx29,(?.&40.)(21.(?.&40.)Lx30,(?.&40.)(21.(?.&40.)Lx31,(?.&40.)(3.(22.$20.R?.(23.(24.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(25.&40.R2;.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(26.Vra,)Vfc,(27.(?.&40.))R2<.(28.$>.)))(1;.$>.R2<.Vlo,(12.&40.Vsp,)))))))))))))))))(23.(24.R1;.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R13.R12.R11.R1:.R19.(25.&40.R1<.)R10.R?.R>.R=.R<.R;.R:.R18.R17.R16.R15.R14.Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(25.&40.+9=1>4.)Vfc,(27.(?.&40.))R1=.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc FR ST MI. basic_facts hc LBc mm HH TOPc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: first [exact C24H | match goal with |- ?g => idtac "EPI-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@D24976250634.113D24976250634.116D52014138856.113D52014138856.116D62155808737.116K43355168775.113K43355168775.116L12283411672.112L14106684376.112L23100341967.112L29074096193.106L29074168500.109L29428324939.5  L35653441506.7  L36425783560.112L41288976216.112L43361613547.2  L44866992728.112L46160487540.112L46160540950.109L48429268312.112L49345641752.111L49578233423.112L50790580594.6  L5145216728.112 L60098763854.3  L8722184664.112 Q12370813529.113Q15643290603.112Q17207353341.112Q18365959659.112Q20414272036.113Q20414272036.116Q21879808904.112Q22285631880.110Q22285648010.107Q22286196081.109Q24974040330.112Q24974040330.115Q26207720445.110Q26207721832.113Q26209519061.112Q27907166216.112Q31651985788.112Q32655335659.112Q33918027400.112Q37625275423.112Q3830196744.112 Q39212284437.110Q39212284437.113Q39939652360.112Q41152162539.112Q42081808994.110Q42081808994.113Q43925228937.113Q44648681323.112Q4926406185.110 Q51236024939.112Q52016320488.112Q52016320488.115Q54253886744.109Q5485174314.113 Q5485603330.112 Q56761401107.110Q59843171435.112Q60511567613.110Q60511567613.113Q60697995187.113Q6143569392.113 Q62157788641.115Q62965564504.111Q62965564504.114Q63231501142.107Q66522035592.112Q7891539809.113 Q8880812193.110 Q9538477138.110 Q9538787269.107 Q9843398792.112 00000H00`01801P01h02S03>03G03P03Y03b03k04=04W05305<05=05F05O05X05a05j06306J06S06]06f07407@07F07R07m08H08`08f08l09209G09\09b09h09n0:F0:L0:X0;00;60;N0;T0;Z0<20<>0<G0<P0<V0<b0<h0=40=I0=^0=d0=j0>00>60>B0>H0>N0>T0>Z0>o0?>0?M0?S0?k0@40@:0@@0@F0@^S2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO3DSX2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO3DSX2XB2HB5Ha_st5Hl_stS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS1R5NEEDR2sp1X2lo3SLO3SPR2XBS2sp1X2XBFS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R5NEEDR2sp2lo3LOS3SLOS2sp1X2XBS1R2lo3LOSS2sp1X2XBS2sp1X4ALX82XBS2sp1X2lo2XBS1X2XBS2sp1X2lo2XBS2sp1X2lo2XB2HB5Ha_st5Hl_stS2sp1X2lo2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1X2XBS1X2XBS1X2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS2sp1X2lo2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS2sp1X2lo2XBS1X2XB2HBS1X2XB2HBS1X2XBS2sp1X2lo2XBS1X2XBS2sp1X2lo2XBS1X2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS1X2XBS2sp1X2lo2XBS1X2XBS1X2XBS1X2XBS1X2XBS1X2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_stS1X2XB2HB5Ha_stS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XB2HBS1X2XBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma finA_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Phc,(=.$>.VR,VHIA,)PLBc,(:.$;.)Pmm,P,(?.&40.)(10.(?.&8.))Ppw,$2.Psw,(?.&40.)Pnw,$2.Pxra,(?.&40.)Pxs2,(?.&40.)Pxs3,(?.&40.)Pxs4,(?.&40.)Pxs5,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa0,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,R1:.R19.VLF,R18.)P,(22.$2.(13.$>.VR,VHIA,R1;.)(13.$>.VR,VHIA,Vh,))P,(4.(12.&40.Vsp,)(13.$>.VR,VHIA,R1<.))P,(22.$2.(29.VX,+8.)=)P,(2:.(4.(15.VX,+10.)Vlo,)(4.(12.&40.Vsp,)VX,))P,(14.$>.R1=.VX,(2;.R1<.R1;.R1:.Vpad,))P,(2<.(2=.VR,)(2>.$;.R1?.(2?.VLF,))(12.&40.Vsp,)(13.$>.VR,VHIA,Vh,)VX,+10.)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,R21.)R1?.VX,+10.)P,(14.$>.R20.(15.(12.&40.Vsp,)-40.)(16.$17.(19.Vs6,)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R21.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R22.)(1=.$>.(1>.VR,)(1?.$>.VR,VHIA,R25.)Lms',$20.(21.(?.&40.)Lx5,(?.&40.)(21.(?.&40.)Lx6,(?.&40.)(21.(?.&40.)Lx7,(?.&40.)(21.(?.&40.)La1',(?.&40.)(21.(?.&40.)La2',(?.&40.)(21.(?.&40.)La3',(?.&40.)(21.(?.&40.)La4',(?.&40.)(21.(?.&40.)La5',(?.&40.)(21.(?.&40.)La6',(?.&40.)(21.(?.&40.)La7',(?.&40.)(21.(?.&40.)Lx28,(?.&40.)(21.(?.&40.)Lx29,(?.&40.)(21.(?.&40.)Lx30,(?.&40.)(21.(?.&40.)Lx31,(?.&40.)(21.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(3.(22.$20.R10.(23.(24.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(26.Vra,)Vfc,(27.(?.&40.))R1.(28.$>.)))(3.(31.(16.(32.$2.$2.)(33.$2.$2.Vlo,(12.&40.Vsp,))(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.))))R33.R1.)(3.(34.$>.R33.R1.)(3.(1<.$>.R1.)(3.(14.$>.R1.VX,(2;.=(25.&40.+1.)=Vpad,))(3.(1;.$>.R1.Vlo,(12.&40.Vsp,))(11.$>.VR,VHIA,R35.R34.VLF,R1.))))))))))))))))))))))(23.(24.R1?.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R1:.R19.R18.(25.&40.VX,)(25.&40.(15.(35.VX,+3.)(36.(1>.VR,))))R17.R16.R15.R14.R13.R12.R11.R10.R1>.R1=.R1<.R1;.(25.&40.(36.(1>.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(25.&40.+9=0<0.)Vfc,(27.(?.&40.))R23.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc ALX8 DSX HX CWc OX FR ST MI. basic_facts hc LBc mm HH TOPc.
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: first [exact C24H | match goal with |- ?g => idtac "FINA-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01X0@C12806640203.127C17025492443.126D23181406632.127D24976250634.128D47198685102.127D52014138856.128D60109446735.127D61783585890.127D64311484648.127K14164087439.127K32320886220.128K36719207456.126K43355168775.128K51736254456.127K55237452495.127L12283411672.123L13062538913.0  L13604058994.4  L14106684376.123L14161137646.3  L14369733550.2  L18134777442.3  L18293330070.2  L19052617798.4  L1938956572.14  L2340205082.8   L24483526758.2  L24695322772.2  L2684524054.7   L29061434714.120L29074168500.123L29428324939.5  L32327419688.3  L33658630589.14 L35653441506.7  L36425783560.124L36715738693.2  L39172636981.0  L40108680262.4  L41288976216.123L43361613547.2  L44866992728.123L47209170218.1  L48429268312.123L49343544635.123L50790580594.6  L5145216728.123 L51731989917.3  L54897920813.3  L55243743307.3  L57018340393.14 L57835847637.14 L60098763854.3  L61929606957.104L8722184664.123 N14223628126.127N21806751459.127N22834764276.127N37104593031.127N45847573372.127O12806640203.127O17025492443.126O25425648043.127O27559730561.126O3791992892.127 O57399310481.127P14164087439.127P18124291302.127P19047445027.126P36719207456.126Q15643290603.124Q18365959659.124Q21879808904.124Q22285631880.125Q22286196081.124Q22289960337.122Q23181406632.127Q24974040330.127Q27907166216.124Q30987168521.107Q32655335659.124Q33918027400.124Q38248387216.127Q3830196744.124 Q38476389417.128Q39212284437.125Q39939652360.124Q41152162539.124Q42081808994.125Q43879899724.127Q44648681323.124Q47198685102.127Q4926406185.125 Q51236024939.124Q52016320488.127Q54253886744.124Q56761401107.125Q59843171435.124Q60511567613.125Q62965564504.126Q63219035725.122Q66522035592.124Q9534675678.122 Q9843398792.124 00000100200E00c01401R01j01k02I02J03003103b04804L04[04\04]04l04m04n04o05605705D05E05J05P05e06406C06U06V06k07C07e07f07g08208A08B08Q08T08c09209I09X09Y09e09f09j0::0:D0:X0:g0;=0;U0;V0;n0<Z0<[0<\0<]0<^0<_0<`0<a0=N0=g0=h0>:0>L0>j0?60?B0?N0?^0@90@W0AE0AW0B50BD0Bb0CG0CS0D10DC0DR0Dd0E60ED0EP0Eb0F=0FI0FU0Fg0G30GH0GT0H20H>0H\FFS2sp1X1n1P5limbs2XBS2sp1X5limbs2XB2HB5Ha_st5Hl_stS2sp1X1P5limbs2XBS2sp1X5limbs2XB2HB5Ha_st5Hl_stS1R2sp1X5limbs2lo3LOS2XBFS1R3HIA1h2sp1X5limbs2lo3TOP2XBFS1X1n1P5limbs2NR3DXP2XB2HB5Ha_st5Hl_stFS1R5NEEDR2sp1X5limbs2lo3SLO3DSX2XB2HB5Ha_st5Hl_stS2sp1X5limbs2lo3DSX2XBS1X1n1P5limbs3DXP2XBS2sp1X5limbs2XBSFS2sp1X5limbs2XBFFFS2sp2loFS2sp1n2NR3SPRFS1n1PS1n2NRS1R1n1P2lo3LOS2PC3ALOS2sp1X5limbs2XBS2sp1X5limbs2XBS1R2lo3LOS3ALO3ACPFS1R2sp2lo3SLO3NRA3SPRS1R3HIA1h2sp2lo3TOP4HTOPS1R5NEEDR2sp1X5limbs2lo3SLO3SPR2XBFSS1n1P2lo2PSS2sp1X5limbs2XBFS2sp1X5limbs2XBS1PS2sp1X5limbs2XBS2sp1X5limbs2XBS1R5NEEDR2sp2lo3LOS3SLOS2sp1X5limbs2XBFS1n5limbs2LLFS2spS1R3HIA1h2sp3TOPS1R2lo3LOSS2sp1X1n5limbs2NR2XBS2sp1X5limbs2XBS1X1n1P5limbs2XB3x151CS2sp1X5limbs2lo2XB3x151CFS2sp1X5limbs2lo2XB3x151CS1X1n1P5limbs2XB3x151C1R2sp2lo3LOS2NR2PC3ALOFFFFFFFS1R5NEEDR2sp1X1n1P5limbs2lo3LOS3SLO2PC3ALO2XBS2sp1X1n1P5limbs2lo2XB2PSFS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X1n1P5limbs2XBS1X5limbs2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS2sp1X1n1P5limbs2lo2XB2HB5Ha_st5Hl_stS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS2sp1X5limbs2lo2XBS1X5limbs2XB2HBS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1X1P5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1X5limbs2XB2HB5Ha_st5Hl_stS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XB2HB5Ha_stS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG AMS NEEDR LOS SLO TOP"] Lemma finB_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Pmm,P,(?.&40.)(10.(?.&8.))Pxra,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,Vh,VLB,VLF,R?.)P,(22.$2.(29.VX,+8.)=)P,(2:.(4.(15.VX,+10.)Vlo,)(4.(12.&40.Vsp,)VX,))P,(3.(4.+1.Vn,)(4.Vn,$37.))P,(38.(32.$2.$2.)(33.$2.$2.VP,(39.+4.Vn,))VLB,)P,(4.(15.VP,(39.+4.Vn,))(3:.(2=.VR,)))P,(2:.(4.(15.VX,+10.)VP,)(4.(15.VP,(39.+4.Vn,))VX,))P,(14.$>.R16.VX,(2;.VP,(25.&40.Vsg,)Vn,Vpad,))P,(3;.$>.R17.VP,Vlimbs,)P,(22.$2.(3<.(3=.(?.&40.)Vlimbs,))Vn,)P,(2<.(2=.VR,)(2>.$;.VLB,(2?.VLF,))(12.&40.Vsp,)(13.$>.VR,VHIA,Vh,)VX,+10.)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,Vh,)R1:.VX,+10.)P,(14.$>.R1;.(15.(12.&40.Vsp,)-40.)(16.$17.(19.Vs6,)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R1<.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R1=.)(1=.$>.(1>.VR,)(1?.$>.VR,VHIA,Vh,)Lms',$20.(21.(?.&40.)Lx5,(?.&40.)(21.(?.&40.)Lx6,(?.&40.)(21.(?.&40.)Lx7,(?.&40.)(21.(?.&40.)La1',(?.&40.)(21.(?.&40.)La2',(?.&40.)(21.(?.&40.)La3',(?.&40.)(21.(?.&40.)La4',(?.&40.)(21.(?.&40.)La5',(?.&40.)(21.(?.&40.)La6',(?.&40.)(21.(?.&40.)La7',(?.&40.)(21.(?.&40.)Lx28,(?.&40.)(21.(?.&40.)Lx29,(?.&40.)(21.(?.&40.)Lx30,(?.&40.)(21.(?.&40.)Lx31,(?.&40.)(21.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(3.(22.$20.R10.(23.(24.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(26.Vra,)Vfc,(27.(?.&40.))R1.(28.$>.)))(3.(31.(16.(32.$2.$2.)(33.$2.$2.Vlo,(12.&40.Vsp,))(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(16.(32.$2.$2.)(33.$2.$2.VP,(15.VP,(39.+4.Vn,)))(1:.(32.$2.$2.)))))R2>.R1.)(3.(34.$>.R2>.R1.)(3.(1<.$>.R1.)(3.(14.$>.R1.VX,(2;.VP,(25.&40.+1.)Vn,Vpad,))(3.(3;.$>.R1.VP,(3>.(?.&40.)(25.&40.=)(3?.Vn,)))(3.(1;.$>.R1.Vlo,(12.&40.Vsp,))(11.$>.VR,VHIA,Vh,VLB,VLF,R1.)))))))))))))))))))))))(23.(24.R1=.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R1<.R1;.R1:.(25.&40.VX,)(25.&40.Vn,)(25.&40.VP,)(25.&40.Vn,)R19.R18.R17.R16.R15.R14.(25.&40.(15.VX,+:.))(25.&40.(15.VX,+8.))(25.&40.(15.(35.(15.VX,+:.)+3.)(36.(1>.VR,))))(25.&40.(15.(35.VX,+3.)(36.(1>.VR,))))(25.&40.(36.(1>.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(25.&40.+9=050.)Vfc,(27.(?.&40.))R1>.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH ALX8 DSX NR HIN PC DXP HX HPL LL CWc OX FR ST MI. basic_facts h LB mm HH TOP.
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    unfold MPI_MAX_LIMBS in NR.
    assert (CWs : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X 16) by (eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    destruct (hm_apart asegs R HIA h LB LF mm HH) as [HF _]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & _ & _). cbn in B0.
    pose proof (hm_aobj_block asegs R HIA h LB LF mm P (4 * n) HH HIN) as OP.
    assert (HINF : In (P, 4 * n) (LB ++ fdata LF)) by (apply in_app_iff; left; exact HIN).
    assert (PS : P + 4 * n <= lo) by (clear - PC ALO LOS; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16); (P, P + 4 * n)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply u32arr_cells in HPL. apply (u8arr_of_rw_cells asegs) in HPL.
    (* [comment removed for export] *)
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_RC) as SPM. unfold A_ASAN_MEMSET_RC in SPM.
    callxA_sp (bv_unsigned sp + -64)
      (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := P) (v := 0) (n := n * 4) (lo := lo) (ds := u32s limbs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | rewrite u32s_length; clear - LL; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
             | left; clear - PS; lia                                                          (* [comment removed for export] *)
             | eapply (blk_top47_sub asegs R HIA h LB LF); [exact HH| exact HIN| clear; lia]     (* [comment removed for export] *)
             | eapply client_wrange_block; [exact HINF| clear; lia| clear; lia]
             | clear - NR LOS SLO NEEDR NRA TOP SPA SPR; lia
             | first [exact C24H | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end] ]).
    clear SPM.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 P _ |- _ => rename H into HPZ end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : ?x = Z_to_bv 64 P |- _ => subst x end.
    apply (rw_cells_of_u8arr asegs) in HPZ. rewrite repeat_length in HPZ.
    replace (Z.to_nat (n * 4)) with (4 * Z.to_nat n)%nat in HPZ by (clear - NR; lia).
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OX (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST5 (bv_unsigned sp).
    zstep.
    finish.
    all: try (eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]).
    all: first [exact C24H | match goal with |- ?g => idtac "FINB-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@D24976250634.110D24976250634.113D52014138856.110D52014138856.113D62155808737.113K43355168775.110K43355168775.113L23100341967.109L29074096193.103L29074168500.106L29428324939.5  L35653441506.7  L43361613547.2  L46160487540.109L49578233423.109L50790580594.6  L60098763854.3  Q12370813529.110Q17207353341.109Q22285631880.107Q22285648010.104Q22286196081.106Q24974040330.109Q24974040330.112Q26207720445.107Q26207721832.110Q26209519061.109Q31651985788.109Q37625275423.109Q39212284437.107Q39212284437.110Q42081808994.107Q42081808994.110Q43925228937.110Q4926406185.107 Q52016320488.109Q52016320488.112Q54253886744.106Q5485174314.110 Q5485603330.109 Q56761401107.107Q6027349519.110 Q6027349519.113 Q60511567613.107Q60511567613.110Q60697995187.110Q6143569392.110 Q62157788641.112Q62965564504.108Q62965564504.111Q63231501142.104Q7891539809.110 Q8880812193.107 Q9538477138.107 Q9538787269.104 00000H00`01801P01h02S03>03G03P03Y03k04E04F04O04X04o05905G05M05S05Y05_06406I06O06U06[06a06g06m07307<07E07K07Q07f08;08A08G08M08S08h09=09C09I09O09U09j0:90:H0:N0:W0:]0:c0:iS2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS2sp1X2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO3DSX2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO3DSX2XB2HB5Ha_st5Hl_stS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPFS2sp1X2XBS2sp1X2XBS1R5NEEDR2sp2lo3LOS3SLOS1R2lo3LOSS2sp1X4ALX82XBS1X2XBS1X2XBS1X2XBS1X2XBS1X2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS1X2XBS1X2XBS1X2XBS1X2XBS1X2XB2HBS1X2XB2HBS1X2XBS1X2XBS1X2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS1X2XBS1X2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS1X2XBS1X2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_stS1X2XB2HB5Ha_stS1X2XBS1X2XB2HBS1X2XBS1X2XBS1X2XB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma mid_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Phc,(=.$>.VR,VHIA,)PLBc,(:.$;.)Pmm,P,(?.&40.)(10.(?.&8.))Ppw,$2.Psw,(?.&40.)Pnw,$2.Pxra,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa0,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,R16.R15.VLF,R14.)P,(22.$2.(13.$>.VR,VHIA,R17.)(13.$>.VR,VHIA,Vh,))P,(4.(12.&40.Vsp,)(13.$>.VR,VHIA,R18.))P,(22.$2.(29.VX,+8.)=)P,(2:.(4.(15.VX,+10.)Vlo,)(4.(12.&40.Vsp,)VX,))P,(14.$>.R19.VX,(2;.R18.R17.R16.Vpad,))P,(2<.(2=.VR,)(2>.$;.R1;.(2?.VLF,))(12.&40.Vsp,)(13.$>.VR,VHIA,Vh,)VX,+10.)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,R1=.)R1;.VX,+10.)P,(14.$>.R1<.(15.(12.&40.Vsp,)-40.)(16.$17.(19.Vs6,)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R1=.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R1>.)(1=.$>.(1>.VR,)(1?.$>.VR,VHIA,R21.)Lms',$20.(21.(?.&40.)La0',(?.&40.)(21.(?.&40.)La1',(?.&40.)(21.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(3.(22.$20.R4.(23.(24.R1?.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R1>.R1=.R1<.(25.&40.VX,)(25.&40.Vnl,)R3.R2.R19.R18.R17.R16.R15.R14.(25.&40.(15.VX,+:.))(25.&40.(15.VX,+8.))(25.&40.(15.(35.(15.VX,+:.)+3.)(36.(1>.VR,))))(25.&40.(15.(35.VX,+3.)(36.(1>.VR,))))(25.&40.(36.(1>.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(25.&40.+9=140.)Vfc,(27.(?.&40.))R1.(28.$>.)))(3.(31.(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.)))R23.R1.)(3.(34.$>.R23.R1.)(3.(1<.$>.R1.)(3.(14.$>.R1.VX,(2;.=(25.&40.+1.)=Vpad,))(3.(14.$>.R1.(15.(12.&40.Vsp,)-40.)(16.$17.(19.Vs6,)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))(3.(1;.$>.R1.Vlo,(15.(12.&40.Vsp,)-40.))(11.$>.VR,VHIA,R25.R24.VLF,R1.)))))))))))(23.(24.R1;.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R1:.R19.R18.(25.&40.VX,)(25.&40.Vnl,)R17.R16.R15.R14.R13.R12.R11.R10.(25.&40.(15.VX,+:.))(25.&40.(15.VX,+8.))(25.&40.(15.(35.(15.VX,+:.)+3.)(36.(1>.VR,))))(25.&40.(15.(35.VX,+3.)(36.(1>.VR,))))(25.&40.(36.(1>.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(25.&40.+9=110.)Vfc,(27.(?.&40.))R1?.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc ALX8 DSX HX CWc OX FR ST MI. basic_facts hc LBc mm HH TOPc.
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(X, X + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OX (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    finish.
    all: first [exact C24H | match goal with |- ?g => idtac "MID-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@D24976250634.112D52014138856.112D52014138856.113D62155808737.113K43355168775.112K43355168775.113L12283411672.109L14106684376.109L23100341967.109L29428324939.5  L35653441506.7  L36425783560.109L41288976216.109L43361613547.2  L44866992728.109L46160487540.108L48429268312.109L49345641752.108L49578233423.109L50790580594.6  L5145216728.109 L60098763854.3  L8722184664.109 Q12370813529.110Q15643290603.109Q17207353341.109Q18365959659.109Q20414272036.112Q20414272036.113Q21879808904.109Q24974040330.111Q26207421841.108Q26207721832.109Q26207967338.106Q27907166216.109Q31654082872.108Q32655335659.109Q33918027400.109Q37625275423.109Q3830196744.109 Q39212284437.109Q39939652360.109Q41152162539.109Q42081808994.109Q43925228937.109Q44648681323.109Q51236024939.109Q52016320488.111Q52016320488.112Q5485174314.110 Q5485603330.109 Q59843171435.109Q60511567613.109Q60697995187.109Q6143569392.110 Q62157788641.112Q62965564504.110Q62965564504.111Q66522035592.109Q7891539809.110 Q8880503606.106 Q9538787269.106 Q9843398792.109 00000K00f01A01\02J03803A03J03S03e04?04[04d04e04n05705@05I05R05i06206<06E06S06_06e07107O07m08E08]08c08i08o09G09M09Y0:10:70:O0:U0:m0;90;B0;H0;T0;`0<80<P0<V0<\0<h0<n0=40=:0=R0=a0>00>H0>Q0>W0>]0?5S2sp1X2nl2XB2HB5Ha_st5Hl_stS2sp1X2nl2XB2HB5Ha_st5Hl_stS2sp1X2pn2XB2HB5Ha_st5Hl_stS2sp1X2pn2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2nl2lo3SLO3DSX2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO2pn3DSX2XB2HB5Ha_st5Hl_stS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS1R5NEEDR2sp1X2lo3SLO3SPR2XBS2sp1X2XBFS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R5NEEDR2sp2lo3LOS3SLOS2sp1X2XBS1R2lo3LOSS2sp1X2XBS2sp1X4ALX82XBS2sp1X2lo2XBS1X2XBS2sp1X2lo2XBS2sp1X2nl2lo2XB2HB5Ha_st5Hl_stS2sp1X2lo2pn2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO2XBS1X2nl2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS2sp1X2lo2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS2sp1X2lo2XBS1X2XB2HBS1X2XBS2sp1X2lo2XBS2sp1X2lo2XBS1X2nl2XB2HB5Ha_st5Hl_stS1X2pn2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS2sp1X2lo2XBS1X2XBS1X2XBS1X2XBS1X2pn2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_stS1X2XB2HB5Ha_stS1R5NEEDR2sp1X2lo3SLO2XBS1X2XB2HBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma finC_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Phc,(=.$>.VR,VHIA,)PLBc,(:.$;.)Pmm,P,(?.&40.)(10.(?.&8.))Ppw,$2.Psw,(?.&40.)Pnw,$2.Ppn,$2.Pxra,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa0,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,R17.R16.VLF,R15.)P,(22.$2.(13.$>.VR,VHIA,R18.)(13.$>.VR,VHIA,Vh,))P,(4.(12.&40.Vsp,)(13.$>.VR,VHIA,R19.))P,(22.$2.(29.VX,+8.)=)P,(2:.(4.(15.VX,+10.)Vlo,)(4.(12.&40.Vsp,)VX,))P,(3.(4.=R16.)(5.R16.(6.+2.+40.)))P,(14.$>.R1;.VX,(2;.R1:.R19.R18.Vpad,))P,(2<.(2=.VR,)(2>.$;.R1=.(2?.VLF,))(12.&40.Vsp,)(13.$>.VR,VHIA,Vh,)VX,+10.)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,R1?.)R1=.VX,+10.)P,(14.$>.R1>.(15.(12.&40.Vsp,)-40.)(16.$17.(19.Vs6,)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R1?.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R20.)(1=.$>.(1>.VR,)(1?.$>.VR,VHIA,R23.)Lms',$20.(21.(?.&40.)Lx5,(?.&40.)(21.(?.&40.)Lx6,(?.&40.)(21.(?.&40.)Lx7,(?.&40.)(21.(?.&40.)La1',(?.&40.)(21.(?.&40.)La2',(?.&40.)(21.(?.&40.)La3',(?.&40.)(21.(?.&40.)La4',(?.&40.)(21.(?.&40.)La5',(?.&40.)(21.(?.&40.)La6',(?.&40.)(21.(?.&40.)La7',(?.&40.)(21.(?.&40.)Lx28,(?.&40.)(21.(?.&40.)Lx29,(?.&40.)(21.(?.&40.)Lx30,(?.&40.)(21.(?.&40.)Lx31,(?.&40.)(21.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(3.(22.$20.R10.(23.(24.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(26.Vra,)Vfc,(27.(?.&40.))R1.(28.$>.)))(3.(31.(16.(32.$2.$2.)(33.$2.$2.Vlo,(12.&40.Vsp,))(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.))))R31.R1.)(3.(34.$>.R31.R1.)(3.(1<.$>.R1.)(3.(14.$>.R1.VX,(2;.R2=.R2?.Vnl,Vpad,))(3.(1;.$>.R1.Vlo,(12.&40.Vsp,))(11.$>.VR,VHIA,R33.R32.VLF,R1.))))))))))))))))))))))(23.(24.R1<.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.(25.&40.VX,)(25.&40.Vnl,)R18.R17.R16.R15.R14.R13.R12.R11.(25.&40.(15.VX,+:.))(25.&40.R1=.)(25.&40.(15.(35.(15.VX,+:.)+3.)(36.(1>.VR,))))(25.&40.(15.(35.VX,+3.)(36.(1>.VR,))))(25.&40.(36.(1>.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(25.&40.+9=1<4.)Vfc,(27.(?.&40.))R21.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc ALX8 DSX PNB HX CWc OX FR ST MI. basic_facts hc LBc mm HH TOPc.
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: first [exact C24H | match goal with |- ?g => idtac "FINC-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30741553502.0000001S". (* [comment removed for export] *)
  #[using="Type"] Lemma post_empty : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "PLBr,(:.$;.)Pmo,$40.Pmo',$40.Ph',(=.$>.VR,VHIA,)Pm',P,(?.&40.)(10.(?.&8.))Pr,$2.Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(1<.$>.R10.)P,(1;.$>.R11.Vlo,(12.&40.Vsp,))P,(41.R15.R14.)P,(42.$>.VR,(43.VLB,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(12.&40.Vsp,)(45.VR,)(46.$>.VR,VHIA,Vh,)(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.)))Vm,R13.)P,(22.$2.(13.$>.VR,VHIA,R15.)(13.$>.VR,VHIA,Vh,))P,(22.$2.(46.$>.VR,VHIA,R16.)(46.$>.VR,VHIA,Vh,))P,(22.$2.(47.$>.VR,VHIA,R17.)(47.$>.VR,VHIA,Vh,))P,(48.$>.VR,VHIA,R18.R19.)P,Px,$2.P,(1?.$>.VR,VHIA,Vh,R1.)(1?.$>.VR,VHIA,R1;.R2.)P,(4.(49.$>.VR,VHIA,R1:.)(15.(49.$>.VR,VHIA,Vh,)(8.Vnl,)))P,(4.(4:.$>.VR,VHIA,R1;.)(15.(4:.$>.VR,VHIA,Vh,)(9.Vd,)))P,(11.$>.VR,VHIA,R1<.R1?.VLF,R1;.)P,(14.$>.R1<.VX,(2;.=(25.&40.+1.)=Vpad,))P,(22.$2.(29.VX,+8.)=)P,(5.=VX,)P,Pb,$;.P,(38.$;.R1.R24.)(38.$;.R2.VLB,)P,Pb,$;.P,(38.$;.R1.VLB,)P,(4;.(38.$;.R2.(4<.(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))))(38.$;.R3.R27.)P,Pb,$;.P,(38.$;.R1.(4<.(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(4;.(38.$;.R2.R27.))P,(2:.(3.(22.$2.R21.=)(22.$2.Vnl,=))(22.$2.R21.$4=.))(4>.$>.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$2.LdX',$7.(<.Vnl,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(8.Vnl,)(9.Vd,)Vlo,Vm,R26.(4?.(23.(24.Vra,Vsp,Vgp,Vtp,R21.R20.R1?.Vs0,Vs1,(25.&40.R22.)R1>.R1=.R1<.R1;.R1:.R19.R18.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(26.Vra,)Vfc,(27.(?.&40.))R23.(28.$>.))R25.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH HX ALX X0 HI1 HI2 HI3 Hr.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LBr, (mkMPD X 1 0 0 [] pad LNull), r.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|].
    split. { split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact HX|]. split; [exact ALX|]. split; [exact X0|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia|]. split; reflexivity. }
    split. { unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split; [intros b Hb; left; apply HI1, Hb|]. split; [exact HI2|]. intros b Hb1 Hb2. exfalso. exact (HI3 b Hb1 Hb2). }
    split; [cbn [mpd_blk md_own]; intros b []|].
    unfold resize_clear_R. cbn [md_sg md_n md_limbs md_own md_addr mpd_blk md_p]. split; [| split; [reflexivity| intros b []]].
    destruct Hr as [[-> Hnl]| ->]; [left| right; repeat split; reflexivity].
    rewrite Hnl. cbn [Z.to_nat repeat]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; intros _; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L29971683454.2L38725398356.5L4233607010.5 L51857265384.2L54007989351.2L59308660947.500000600D00S00Y00_00nS1n2NRS1R3HIA1h1d2D0S1R3HIA1h2nl2NLS1n2NRS1n2NRS1n2nl2NR2En2E0". (* [comment removed for export] *)
  #[using="NL"] Lemma post_same : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Pmo,$40.Pmo',$40.Pm',P,(?.&40.)(10.(?.&8.))Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(1<.$>.R?.)P,(1;.$>.R10.Vlo,(12.&40.Vsp,))P,(41.R13.R12.)P,(42.$>.VR,(43.VLB,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(12.&40.Vsp,)(45.VR,)(46.$>.VR,VHIA,Vh,)(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.)))Vm,R12.)P,(48.$>.VR,VHIA,Vh,R14.)P,(11.$>.VR,VHIA,Vh,VLB,VLF,R14.)P,(14.$>.R15.VX,(2;.VP,(25.&40.+1.)Vn,Vpad,))P,(3;.$>.R16.VP,(3>.(?.&40.)(25.&40.=)(3?.Vn,)))P,(22.$50.Vown,$51.)P,(38.(32.$2.$2.)(33.$2.$2.VP,(39.+4.Vn,))VLB,)P,(22.$2.(29.VP,+10.)=)P,(3.(4.+1.Vn,)(4.Vn,$37.))P,(22.$2.Vn,Vnl,)P,(22.$2.(29.VX,+8.)=)P,(5.=VX,)P,(4.=Vd,)(4>.$>.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$2.LdX',$7.(<.Vnl,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(8.Vnl,)(9.Vd,)Vlo,Vm,R21.(4?.(23.(24.Vra,Vsp,Vgp,Vtp,R1>.R1=.R1<.Vs0,Vs1,(25.&40.=)R1;.R1:.R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(26.Vra,)Vfc,(27.(?.&40.))R1?.(28.$>.))R20.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HK HH HX HPZ EO HIN HP16 NR En ALX X0 D0.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h, LB, (mkMPD X 1 n P (repeat (Z_to_bv 64 0) (Z.to_nat n)) pad LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK|]. split; [intros y Hy; exact Hy|].
    split; [unfold grow_PHI, AVOL_CALL; clear - NL; lia|]. split; [rewrite resize_clear_FR_val; clear - D0; lia|]. split; [exact HH|].
    split. { split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact HX|]. split; [exact ALX|]. split; [exact X0|]. split; [rewrite repeat_length; clear - NR; lia|]. split; [clear - NR; lia|].
      split; [clear - NR; lia|]. split; [exact HIN|]. split; [exact HP16| exact HPZ]. }
    split. { apply mpd_out_same_blocks; cbn [md_addr md_own mpd_blk md_p md_n]; [reflexivity| discriminate| rewrite EO; reflexivity]. }
    split; [cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b Hb; left; exact Hb|].
    unfold resize_clear_R. cbn [md_sg md_n md_limbs md_own md_addr mpd_blk md_p]. rewrite EO. split; [| split; [reflexivity| intros b Hb; left; exact Hb]].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [exact En|]. split; [rewrite En; reflexivity|].
    split; [intros E0; exfalso; clear - E0 En NR; lia| intros E0; discriminate E0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L17344167783.2L34147935404.2L45233861524.2L59308660947.300000700>00E00OS2nl2NRS2nl2NRS2nl2NRS2nl2NR2E0". (* [comment removed for export] *)
  #[using="Type"] Lemma post_new : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "PLBr,(:.$;.)Pmo,$40.Pmo',$40.Ph',(=.$>.VR,VHIA,)Pm',P,(?.&40.)(10.(?.&8.))PA,$2.Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(1<.$>.R10.)P,(1;.$>.R11.Vlo,(12.&40.Vsp,))P,(41.R15.R14.)P,(42.$>.VR,(43.VLB,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(12.&40.Vsp,)(45.VR,)(46.$>.VR,VHIA,Vh,)(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.)))Vm,R13.)P,(22.$2.(13.$>.VR,VHIA,R15.)(13.$>.VR,VHIA,Vh,))P,(22.$2.(46.$>.VR,VHIA,R16.)(46.$>.VR,VHIA,Vh,))P,(22.$2.(47.$>.VR,VHIA,R17.)(47.$>.VR,VHIA,Vh,))P,(48.$>.VR,VHIA,R18.R19.)P,Px,$2.P,(1?.$>.VR,VHIA,Vh,R1.)(1?.$>.VR,VHIA,R1;.R2.)P,(4.(49.$>.VR,VHIA,R1:.)(15.(49.$>.VR,VHIA,Vh,)(8.Vnl,)))P,(4.(4:.$>.VR,VHIA,R1;.)(15.(4:.$>.VR,VHIA,Vh,)(9.Vd,)))P,(11.$>.VR,VHIA,R1<.(16.(32.$2.$2.)(33.$2.$2.R1:.(39.+4.Vnl,))R1?.)VLF,R1;.)P,(14.$>.R1<.VX,(2;.R1;.(25.&40.+1.)Vnl,Vpad,))P,(3;.$>.R1=.R1<.(3>.(?.&40.)(25.&40.=)(3?.Vnl,)))P,(22.$2.(29.R1=.+10.)=)P,(52.VR,R23.VLF,R1>.(39.+4.Vnl,))P,(3.(4.+1.Vnl,)(4.Vnl,$37.))P,(22.$2.(29.VX,+8.)=)P,(5.=VX,)P,Pb,$;.P,(38.$;.R1.R28.)(38.$;.R2.VLB,)P,Pb,$;.P,(38.$;.R1.VLB,)P,(4;.(38.$;.R2.(4<.(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))))(38.$;.R3.R2;.)P,Pb,$;.P,(38.$;.R1.(4<.(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(4;.(38.$;.R2.(16.(32.$2.$2.)(33.$2.$2.R26.(39.+4.Vnl,))R2;.)))P,Pb,$;.P,(38.$;.R1.(43.VLB,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(38.$;.R2.R2<.)P,(4;.(38.(32.$2.$2.)(33.$2.$2.R26.(39.+4.Vnl,))VLB,))(4>.$>.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$2.LdX',$7.(<.Vnl,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(8.Vnl,)(9.Vd,)Vlo,Vm,R2;.(4?.(23.(24.Vra,Vsp,Vgp,Vtp,R26.R25.R24.Vs0,Vs1,(25.&40.=)R23.R22.R21.R20.R1?.R1>.R1=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(26.Vra,)Vfc,(27.(?.&40.))R28.(28.$>.))R2:.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH HX HA A16 HFRA NR ALX X0 HI1 HI2 HI3 HI4 HNI.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', ((A, 4 * nl) :: LBr), (mkMPD X 1 nl A (repeat (Z_to_bv 64 0) (Z.to_nat nl)) pad LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|].
    split. { split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact HX|]. split; [exact ALX|]. split; [exact X0|]. split; [rewrite repeat_length; clear - NR; lia|]. split; [clear - NR; lia|].
      split; [clear - NR; lia|]. split; [left; reflexivity|]. split; [exact A16| exact HA]. }
    split. { unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split; [intros b [Hb|Hb]; [right; left; exact Hb| left; apply HI1, Hb]|].
      split; [intros b Hb Hn; right; exact (HI2 b Hb Hn)|].
      intros b Hb1 Hb2. exfalso. exact (HI3 b Hb1 Hb2). }
    split; [cbn [mpd_blk md_own md_p md_n]; intros b [<-|[]]; right; cbn [fst snd]; eapply fresh_apart_blocks_mono; [exact HFRA| exact HI4]|].
    unfold resize_clear_R. cbn [md_sg md_n md_limbs md_own md_addr mpd_blk md_p]. split; [| split; [reflexivity| intros b [<-|[]]; right; exact HNI]].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [intros E0; exfalso; clear - E0 NR; lia| intros E0; discriminate E0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac epi_return hh LBx rr FRC FR LAWS KINV :=
    eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
      [ eapply epi_walk with (hc := hh) (LBc := LBx) (r := rr); try eassumption; subst FRC; exact FR
      | intros y Hy; exact Hy | ];
    let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; destruct_exs PO;
    let E := fresh "E" in let ST9 := fresh "ST9" in
    destruct PO as [E ST9]; subst ms';
    apply aevtA_done;
    let mo9 := fresh "mo9" in let HK9 := fresh "HK9" in let MF9 := fresh "MF9" in
    intros mo9 [HK9 MF9].

  (* [comment removed for export] *)
  Ltac post_side :=
    first [ eassumption
          | reflexivity
          | match goal with |- mo_frame _ _ => eapply mo_frame_trans; [| eassumption]; eapply mo_frame_trans; eassumption end
          | match goal with H : ?f asegs R HIA ?h2 = ?f asegs R HIA ?hc, H' : ?f asegs R HIA ?hc = ?f asegs R HIA h |- ?f asegs R HIA ?h2 = ?f asegs R HIA h => rewrite H; exact H' end
          | match goal with |- forall x, hcs _ _ _ _ x -> hcs _ _ _ _ x => let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; repeat match goal with H : forall x, hcs _ _ _ ?a x -> hcs _ _ _ ?b x |- hcs _ _ _ ?b y => apply H end; exact Hy end
          | match goal with |- havol _ _ _ _ <= _ => unfold grow_PHI, AVOL_CALL in *; repeat match goal with H : havol _ _ _ _ <= _ |- _ => revert H end; generalize NL; clear; intros; lia end
          | match goal with |- hfr _ _ _ _ <= _ => rewrite ?resize_clear_FR_val in *; unfold fr_charge in *; repeat match goal with H : hfr _ _ _ _ <= _ |- _ => revert H end; generalize (uw_obj_nonneg _ _ _ _ XUW); clear; intros; lia end
          | match goal with H : rw_cells asegs ?mx X _ |- rw_cells asegs ?mx X _ => unfold mpi_cells; exact H end
          | right; reflexivity
          | left; split; [reflexivity| assumption]
          | match goal with |- _ <= _ <= MPI_MAX_LIMBS => unfold MPI_MAX_LIMBS; lia end
          | first [exact C24H | match goal with |- ?g => idtac "POST-SIDE-LEFT:" g end] ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0130@D59426836089.157L12049405014.1  L13963285677.7  L16256253080.9  L16840298758.2  L17422679242.7  L23100341967.162L23268831852.193L23615739305.3  L24613785634.7  L25425969574.8  L28813938827.13 L28814040852.162L29428324939.5  L33421926002.23 L33656389789.23 L35170884280.23 L35653441506.7  L36977326574.23 L38948636245.0  L39027378806.23 L40290687782.1  L40825300204.23 L41075549270.3  L41077498031.4  L46160487540.123L48132467214.7  L5479049730.1   L58095162391.157L59308628566.3  L59308633593.3  L59308661201.4  L59308762472.4  L59314873579.4  L59321342699.2  L60098763854.3  L61566975277.23 L62018535662.1  L62625145375.47 L656136024.1    L66610753222.9  L67996112456.1  L7431626507.23  L8697919885.2   P8437034318.156 P8437034318.157 Q12370813529.166Q17205141328.165Q26207421841.123Q26207721832.124Q26207774423.121Q30985055127.144Q30987329589.126Q31654082872.123Q37623358642.165Q39212284437.124Q43925228937.124Q44731046653.157Q48511918028.156Q5262061745.126 Q5483358895.165 Q5485174314.166 Q60511567613.124Q60697995187.124Q6143569392.166 Q8880817547.121 Q9538464120.121 00000900=00S00n01501J01U01i02302I02`03M04:04L04^05305=05W05e05f06206506906:06J06V07107407=07G07P07]07^07i07j08408R08U08V08Y09309709V09]09f09o0:A0:G0:M0:S0:Y0;A0;i0;o0<50<;0<A0<B0<^0<g0<m0=30=90=B0=H0=N0=TS2sp1X2XBS2nlS1R2nl2lo3LOS3ALO1A2ACS1R3HIA1h1d2hc2h24HFRc4HFR2S2nl2K0S1R3HIA1h1d2hc1H4HFRcS2sp1X2XB1AS2sp1X2nl2K02XB2K21AS1R3HIA2hcS1R3HIA1h2nl2hc2NL3HVcS2sp1X2nl2lo2K01A2AS2XAS1R5NEEDR2sp2nl2lo2NL3LOS3SLO3ALO3SPR1A2A02ACS1R5NEEDR2sp1X2nl2lo3SLO2X02K03SPR2XB1A2A02ASS1R2lo3LOS3ALO3ACPS1R3HIA2sp2hc4TOPcS1R2sp2lo3SLO3NRM3SPRS2sp2nl2NLS1R3HIA2sp2lo2hc4TOPc4HTOPS2sp2nl3SPR2K2SS2sp3SPA3SPRS1XS2spFS2LB4C24H3LBr2CIS2sp1X2X02XBS1R5NEEDR2sp2lo3LOS3SLO3ALOS1XS2sp1X2XBS2nl2K02K3S1A2A02KZS1n2nl3NEQ2E2FS2nl2K01A1HFS1R2lo3LOSS1R3HIA1h2sp2nl2hc3HVc3BUD3SPRS1RFS1XS1R3HIA1h2nl2hc2h23HVc3HV2S2spS1R3HIA1h2sp1d2hc4HFRc4BUDF3SPRS2nl2K0S2sp1X2XBS2sp1X2XBS2sp1X3ALX2X02XB1AS1X2XBS1X2XBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X2lo3LOS3SLO3ALO3ACP3SPR2XBS1X2XBS1X2XBS1X2XBS1X2XBFS1R5NEEDR2sp1X2lo3LOS3SLO2XBS1X2X02XBS1X2XBS1X2XBS1X2XBS1X2X02XBS1X2XBS1X2XBS1X2XB". (* [comment removed for export] *)
  #[using="IMG CALLOC NEEDR HND C24H NL LOS SLO TOP SPA TPV XUW"] Lemma grow_part : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Phc,(=.$>.VR,VHIA,)PLBr,(:.$;.)Pmo,$40.Pmm,P,(?.&40.)(10.(?.&8.))Pxra,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa0,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,R14.R13.VLF,R11.)P,(22.$2.(13.$>.VR,VHIA,R15.)(13.$>.VR,VHIA,Vh,))P,(22.$2.(46.$>.VR,VHIA,R16.)(46.$>.VR,VHIA,Vh,))P,(22.$2.(47.$>.VR,VHIA,R17.)(47.$>.VR,VHIA,Vh,))P,Px,$2.P,(1?.$>.VR,VHIA,Vh,R1.)(1?.$>.VR,VHIA,R1:.R2.)P,(4.(49.$>.VR,VHIA,R19.)(15.(49.$>.VR,VHIA,Vh,)$53.))P,(4.(4:.$>.VR,VHIA,R1:.)(15.(4:.$>.VR,VHIA,Vh,)(54.Vd,)))P,(42.$>.VR,(43.VLB,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(12.&40.Vsp,)(45.VR,)(46.$>.VR,VHIA,Vh,)(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.)))Vm,R18.)P,Pb,$;.P,(38.$;.R1.R1<.)(38.$;.R2.VLB,)P,Pb,$;.P,(38.$;.R1.VLB,)P,(4;.(38.$;.R2.(4<.(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))))(38.$;.R3.R1?.)P,Pb,$;.P,(38.$;.R1.(4<.(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(4;.(38.$;.R2.R1?.))P,Pb,$;.P,(38.$;.R1.(43.VLB,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(38.$;.R2.R20.)P,Pb,$;.P,(38.$;.R1.(4<.(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(3.(22.$;.R2.(33.$2.$2.VP,(39.+4.Vn,)))(3.(38.(32.$2.$2.)(33.$2.$2.VP,(39.+4.Vn,))VLB,)(4.+1.Vn,)))P,(4;.(22.$2.Vn,Vnl,))P,(14.$>.R1?.VX,(2;.=(25.&40.+1.)=Vpad,))P,(22.$2.(29.VX,+8.)=)P,(5.=VX,)P,(2:.(4.(15.VX,+10.)Vlo,)(4.(12.&40.Vsp,)VX,))P,(2<.(2=.VR,)(2>.$;.R25.(2?.VLF,))(12.&40.Vsp,)(13.$>.VR,VHIA,Vh,)VX,+10.)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,R27.)R24.VX,+10.)P,(14.$>.R25.(15.(12.&40.Vsp,)-40.)(16.$17.(19.Vs6,)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R26.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R27.)P,(4.+1.Vnl,)P,(4.(15.(49.$>.VR,VHIA,Vh,)(8.Vnl,))$55.)P,(4.(15.(4:.$>.VR,VHIA,Vh,)(9.Vd,))$56.)(57.$>.(58.$>.VR,VHIA,R2>.R2<.)(4>.$>.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$2.LdX',$7.(<.Vnl,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(8.Vnl,)(9.Vd,)Vlo,Vm,R2<.)(23.(24.R2:.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R29.R28.R27.(25.&40.VX,)(25.&40.Vnl,)R26.R25.R24.R23.R22.R21.R20.R1?.(25.&40.(15.VX,+:.))(25.&40.(15.VX,+8.))(25.&40.(15.(35.(15.VX,+:.)+3.)(36.(1>.VR,))))(25.&40.(15.(35.VX,+3.)(36.(1>.VR,))))(25.&40.(36.(1>.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R1>.R1=.R1<.R1;.)VF,(25.&40.+9=140.)Vfc,(27.(?.&40.))R2;.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT HS HFL HCSc HVc HFRc HPX HI1 HI2 HI3 HI4 HBLK NEQ HXS ALX X0 DSX CWr OX FR ST MI K0 BUD BUDF.
    assert (TOPc : bv_unsigned sp <= htop asegs R HIA hc) by (rewrite HT; exact TOP).
    basic_facts hc LBr mm HH TOPc.
    rewrite resize_clear_FR_val in BUDF. unfold grow_PHI in BUD. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
    pose proof (HND _ _ _ _ HH) as NDr.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    lazymatch type of FR with rw_cells _ _ _ ?cs => set (FRC := cs) in FR end.
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    unfold mpi_cells in HXS.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      epi_return hc LBr MBEDTLS_ERR_MPI_ALLOC_FAILED FRC FR LAWS KINV.
      eapply (post_empty LBr mo _ hc); post_side. }
    rewrite ?unsigned_lit in K2 by (clear - NL; lia).
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. try (replace (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by (clear - NL; lia); clear - K3 K0; lia|]. clear K3.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBr) (LF := LF) (cnt := nl) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity.
      all: try ((intros _; first [ clear - C24H; unfold C24_RESIZE_CLEAR_c in C24H; lia | match goal with HS : forall b, In b ?L -> In b LB, HHr : HM _ _ _ _ ?L _ _ |- _ => let NDq := fresh "NDq" in let CI := fresh "CI" in pose proof (HND _ _ _ _ HHr) as NDq; apply NoDup_map_inv in NDq; pose proof (cnt24_incl _ _ NDq HS) as CI; clear - CI C24H; unfold C24_RESIZE_CLEAR_c in C24H; lia end ])).   (* [comment removed for export] *)
      all: try (eapply uw_obj_uwc; [exact XUW | clear; lia]).
      all: clear - NL K0 K2 LOS SLO NEEDR NRM TOPc SPA SPR BUD BUDF HVc HFRc D0; try (unfold AMAX); try (unfold AVOL_CALL in * ); try (unfold fr_charge in * ); try lia.
      all: first [exact C24H | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2.
    assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
    { eapply presA_trans; [exact HPX|]. rewrite <- HS.
      eapply presA_weaken; [exact HP2| exact HI4| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
    clear HPX HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in OX.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOPc).
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    (* [comment removed for export] *)
    zstep. zstep.
    destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
    - (* [comment removed for export] *)
      pose proof (hm_top asegs R HIA h2 LBr LF m2 HH2) as HTOP.
      zstep.
      epi_return h2 LBr MBEDTLS_ERR_MPI_ALLOC_FAILED FRC FR LAWS KINV.
      eapply (post_empty LBr mo _ h2); post_side.
    - (* [comment removed for export] *)
      replace (nl * 4) with (4 * nl) in HFRA, HAS, HH2, HNEW by (clear; lia).
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP.
      dpose HFRA as (A0 & AC & AD & HAP).
      assert (AS : A + 4 * nl <= lo) by (clear - AC ALO LOS; lia).
      assert (XA : X + 16 <= A \/ A + 4 * nl <= X).
      { destruct (fresh_apart_client R LBr LF (bv_unsigned sp) X 16 A (4 * nl) HFRA); [| clear; lia| clear - K0; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
        eapply client_range_inside; [exact CWr| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (CW3 : client_wrange L (((A, 4 * nl) :: LBr) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
      { eapply client_wrange_mono; [exact CWr|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - A0 AC H; lia); clear - KZ A0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply finC_walk with (hc := h2) (LBc := (A, 4 * nl) :: LBr); try eassumption; try reflexivity
        | intros y Hy; exact Hy | ].
      all: try (rewrite HT2; exact HT).
      all: try (unfold mpi_cells; exact HXS).
      all: try (subst FRC; exact FR).
      all: try (clear - A0 AC ALO LOS SLO SPR NEEDR NL; lia).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "FINC-PRE-LEFT:" g end.
      intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      assert (HA9 : u32arr asegs m9 A (repeat (Z_to_bv 64 0) (Z.to_nat nl))).
      { replace (Z.to_nat (4 * nl)) with (4 * Z.to_nat nl)%nat in HNEW by (clear - K0; lia).
        eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
        eapply (rw_cells_transport asegs _ m2 m9); [exact HNEW| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - XA AS K0; lia]. }
      (* [comment removed for export] *)
      assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
      { eapply presA_trans; [exact HPX2|]. rewrite <- HS, <- HS2.
        eapply (presA_tail asegs R HIA h2 ((A, 4 * nl) :: LBr)); [exact HH2| intros b Hb; right; apply HI4, Hb| exact LOS| exact TOP2| exact OX| exact MU| exact WM]. }
      (* [comment removed for export] *)
      assert (HI3' : forall b, In b (mpd_blk dX) -> ~ In b ((A, 4 * nl) :: LBr)).
      { intros b Hb [E|Hin]; [| exact (HI3 b Hb Hin)]. ddestruct (HBLK b Hb) as (Eb & _ & _). rewrite Eb in E. injection E as E1 E2.
        clear - E2 NEQ. lia. }
      assert (HNI : ~ In (A, 4 * nl) LB).
      { intros Hin. assert (Hr : In (A, 4 * nl) LBr).
        { apply HI2; [exact Hin|]. intros Hb. destruct (HBLK _ Hb) as (Eb & _ & _). injection Eb as E1 E2. clear - E2 NEQ; lia. }
        destruct (HAP A (4 * nl) ltac:(apply in_app_iff; left; exact Hr)); clear - H K0; lia. }
      eapply (post_new LBr mo _ h2); post_side.
    all: first [exact C24H | match goal with |- ?g => idtac "GROW-PART-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac free_limbs_call HH HIN PCHx :=
    let SPZ := fresh "SPZ" in
    pose proof ZF as SPZ; unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ;
    eapply aevtA_call;
    [ let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
      intros mo1 [HK1 MF1];
      eapply SPZ with (buf := P) (len := n * 4) (lo := lo) (d := d) (junk := u32s limbs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity;
      first [ right; split; [replace (n * 4) with (4 * n) by (clear; lia); exact HIN | exact PCHx]
            | eapply uw_obj_uwc; [exact XUW | clear; lia]
            | unfold AVOL_CALL, fr_charge in *; rewrite ?resize_clear_FR_val in *;
              repeat match goal with H : _ <= _ |- _ => revert H | H : _ < _ |- _ => revert H | H : _ <= _ < _ |- _ => revert H | H : _ <= _ <= _ |- _ => revert H end;
              generalize (uw_obj_nonneg _ _ _ _ XUW); generalize SPA; clear; intros; lia
            | first [exact C24H | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end] ]
    | clear SPZ ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "02c0@D13554616751.118D13554616751.119D35881667587.118D35881667587.119D59429060037.160D59429060037.161K42587433812.118K42587433812.119L11468776467.3  L1160155683.153 L1164172544.1   L11668949970.118L11668949970.121L12283411672.115L13301871092.115L14106684376.114L1458502320.162 L16256253080.7  L1685717371.0   L17646078182.114L1954497222.2   L19947928356.153L20456930578.2  L20457280334.4  L20457362125.3  L20457362254.4  L21704522672.163L23100341967.118L23100341967.120L24912882372.1  L26892418956.1  L28762391469.4  L29428324939.5  L29767916836.3  L29772212396.154L33087634096.2  L34148013454.3  L34148095374.3  L34148465618.1  L34425302674.41 L34838900123.41 L35653441506.7  L38438489981.3  L38727422828.5  L38948636245.0  L39027460855.41 L39172636981.0  L39280637297.0  L39416313820.41 L39887139444.115L40281191306.3  L40290687782.1  L40803681500.7  L40834179097.117L41288976216.115L4233607010.5   L42594106808.2  L43061363337.112L44866992728.115L45898055924.115L46122776823.12 L46160478526.117L46160487540.120L46160487540.125L46164737795.122L48132467214.7  L48429268312.115L49346446901.41 L5145216728.115 L51925114228.115L5259987890.117 L5260001178.118 L5260339702.119 L57344136272.153L57838374516.41 L57933933556.115L59308546259.5  L59308632307.1  L59308633339.3  L59308742867.3  L60098763854.3  L60418807424.5  L61929067222.124L61929718192.2  L61929812241.120L61933948591.125L62018535662.1  L62369652128.2  L62624897321.38 L63962036340.114L64194470200.2  L64630569949.3  L66610753222.7  L67996112456.1  L7274816372.115 L774765788.5    L8722184664.115 P8434753266.159 P8434753266.160 P8434753266.161 Q12370813529.119Q12370813529.121Q15457446739.115Q15457446739.116Q15643324129.114Q17207372757.118Q17207970193.120Q18365925601.115Q18694146040.117Q21798041355.117Q21879645826.115Q25157988860.117Q25513505925.117Q25513505925.118Q25662358575.117Q26207421841.120Q26207421841.127Q26207721832.121Q26207721832.128Q26207774677.118Q26220304872.125Q27907200258.115Q30985055127.151Q30985055127.152Q30987329589.133Q30987329589.134Q31228709292.117Q31394594844.117Q31654082872.120Q31654082872.127Q32655500769.115Q33918256002.115Q35014437530.117Q35717497884.117Q37625319479.118Q37625770611.120Q3830427394.115 Q39212284437.121Q39212284437.128Q39939554818.115Q41152393185.115Q4143427880.117 Q43925228937.121Q43925228937.128Q44648843873.115Q44729067841.160Q44729067841.161Q48514198640.159Q48514198640.160Q49698585326.116Q49698585326.117Q51235796833.115Q5262061745.133 Q5262061745.134 Q53969758199.117Q5485174314.119 Q5485174314.121 Q5485583914.118 Q5485640814.120 Q59843137889.115Q60511567613.121Q60511567613.128Q60697995187.121Q60697995187.128Q6143569392.119 Q6143569392.121 Q61802139820.117Q6416456232.117 Q64255486968.117Q66522067074.115Q67528989526.118Q67528989526.119Q7377275490.117 Q7377275490.118 Q8880817289.118 Q8885009076.125 Q9534281287.125 Q9538463866.118 Q9843367298.114 00000k02502b03^04204F05?06G06S06g06j07d08^08m09<09K09_0:40:50:D0:J0:a0:b0:c0:l0:m0;A0;P0;_0;b0;f0;g0<90<B0<^0<d0<n0<o0=00=B0=b0>:0>C0>P0>Q0?=0?>0??0?^0?m0@60@90@T0@e0A40AC0AD0Ai0B80BG0Bh0C:0CL0Cc0D:0DU0Dd0E90EH0EW0Ei0F;0FM0Fc0G80GG0GV0GZ0Gc0Gl0H60HD0H]0Hc0I70IP0IS0IX0IY0Ih0Io0J80JN0JR0Ja0K40KC0KR0Ka0L00LF0L\0Ln0M@0MR0M^0Mj0N<0NO0NP0Nn0OA0Oe0PX0PY0Pe0Q10Q=0QI0QU0Qa0R?0Rm0S[0TI0U70UK0UW0Uc0Uo0VA0V_0W30W40W@0WL0Wj0X60XB0X`0Y20Y30Y?0YK0Y]0Y^0Y_0ZA0Zc0[?0[[0[m0\<0\K0\_0\k0]70]C0]O0]a0]m0^90^H0^W0^c0^o0_00_C0_D0_b0`R0aQ0bA0c@0cL0cX0cd0d00dNS1R5NEEDR2ra2sp1X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S1R3HIA1h2ra2sp1X5limbs3TOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01X5limbs3TOP2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp1X1P5limbs2XB2P0S2sp1X1P5limbs2XB2P0S1R5NEEDR2ra2sp1X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_st2s12s22s32s42s5S1n5limbs2LLS2sp1X1P5limbs2XB2P0S1XS1R5NEEDR2sp1X1n1P5limbs2lo3LOS3SLO2X02LL3ALO3SPR2XB2P02PCS1R5NEEDR2sp1X1n1P5limbs2lo3LOS3SLO2X02LL3ALO3SPR2XB2P02PCS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X1P5limbs2XB2P0S1R3HIA1h1d2h21H4HFR2SS2sp1X5limbs2XBS1P2B0S2sp1X1P5limbs2lo2XB2P0FFS1n2nl2K1FS2sp1X1P5limbs2XB2P0S2sp1X5limbs2XBS2sp1X5limbs2XBS1nS2spFS1R2lo3LOS3ALO3ACPS1n2NR2N1S2sp1X1n1P5limbs2NR2XB2P02N1S1n2NRS2nl2NL2K0FFS1R2sp1X2lo2XB3SLOS1R3HIA1h2sp1X1d2XB3SPR5BUDF02D0S1R3HIA1h2sp2lo3TOP4HTOPS1n2nl2K1S1R3HIA1h1d1HSS1R2sp1X2lo3SPA2XB3SPR3ACP5NEEDR3LOS3SLO3ALOSSS1R3HIA1h2sp1X2nl2XB2NL3SPR3BUDS2sp1X5limbs2XBS1R3HIA1hS1XS1R5NEEDR2sp2lo3LOS3SLO3ALOS1R2sp1X5limbs2XBS2sp1X5limbs2XBS1R3HIA1h2nl2NLFS1R5NEEDR2sp1X5limbs2lo3SLO2X03SPR2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS1R2sp1n1P5limbs2lo3LOS2LL3ALO2PCS2sp1X5limbs2X02XBS2sp1X5limbs2X02XBS2sp1X1P5limbs2X02XB2P0S2sp1X1P5limbs2X02XB2P0S1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1X5limbs2XBS2sp1X1n2NR2XB3SPR2N1S2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2X02XBS2sp1X5limbs2X02XBS2sp1X5limbs2X02XBS2sp1X1n1P5limbs2XB2P0S1R3HIA1h2sp1X2XB3TOPS2sp1X5limbs2XBS1n2nl2K02En2N0S2KPS1X2X02KXS1P2KP2B0S1R2lo3LOSS1R3HIA1h1d2D0S2sp1X1n1P5limbs2NR2XB2P0S1n2NRS2sp1X1n5limbs2NR2XBS2sp1X1n1P5limbs2NR2XB2P0S1RS1n1PFS2sp1X5limbs2XBS1R3ACPS1R3HIA1hS1R3HIA1h2nl2h22NL3HV2S2spS2sp1X5limbs2XBS1R5NEEDR2sp2lo3SLOS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs3ALX2X02XBS2sp1X5limbs3ALX2X02XBS2sp1X5limbs2XB2HBS2sp1X5limbs2XB2HBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1R1X5limbs4IMG'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs4IMG'2XBS2ra2sp1X5limbs2lo2XB2HB5Ha_st5Hl_stS2sp2s01X5limbs2lo2XB2HB5Ha_st5Hl_st2s12s22s32s42s5FS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R1X5limbs5ALWF'2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs5ALWF'2XBFS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS2sp1X5limbs2lo2XBFS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBFFS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2XBS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs2lo2XBS1X5limbs2X02XBS1X5limbs2X02XBS1R1X5limbs5ALWF'2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2X02XBS1X5limbs2X02XBS1X5limbs2XBS1X5limbs2XBFS1R1X5limbs4IMG'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMS NEEDR HND DIMG C24H HNS NL XW DSP LOS SLO TOP SPA TPV XUW"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Pmo,$40.Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)P,(11.$>.VR,VHIA,Vh,VLB,VLF,Vm,)P,(48.$>.VR,VHIA,Vh,R?.)P,(59.$>.Vm,VLB,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(1;.$>.Vm,Vlo,(12.&40.Vsp,))P,(1<.$>.Vm,)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,Vh,)Vm,VX,+10.)P,(4.(15.(49.$>.VR,VHIA,Vh,)(8.Vnl,))$55.)P,(4.(15.(4:.$>.VR,VHIA,Vh,)(9.Vd,))$56.)(5:.$>.(4>.$>.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$2.LdX',$7.(<.Vnl,(44.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(8.Vnl,)(9.Vd,)Vlo,Vm,R16.)(4?.(23.(24.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(25.&40.VX,)(25.&40.Vnl,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.$5;.)Vfc,(27.(?.&40.))Vm,(28.$>.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo MX ST MI OX BUD BUDF. unfold A_MPI_RESIZE_CLEAR. rt_facts h.
    pose proof BUDF as BUDF0. rewrite resize_clear_FR_val in BUDF. pose proof BUD as BUD0. unfold grow_PHI in BUD.
    pose proof (HND _ _ _ _ HH) as ND. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
    ddestruct MX as (HXS & ALX & X0 & LL & NR & HOWN). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, ALX, X0, LL, NR, HOWN.
    destruct XW as [CW DXP]. cbn [md_addr md_own md_p md_n] in CW, DXP.
    pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF BA]. rewrite Forall_forall in HF.
    unfold MPI_MAX_LIMBS in NR.
    (* [comment removed for export] *)
    assert (PB : 0 <= P /\ P + 4 * n <= alloc_ceiling
                 /\ (own = LHeap -> 0 < P /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr asegs m P limbs /\ 1 <= n)
                 /\ (own = LNull -> P = 0 /\ n = 0)).
    { destruct own; [| | exfalso; exact (HNS eq_refl)].
      - destruct HOWN as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
        split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
      - ddestruct HOWN as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        split; [clear - B0; lia|]. split; [exact BC|].
        split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| split; [exact HXL| exact N1]]]]| intros E; discriminate E]. }
    ddestruct PB as (P0 & PC & PHEAP & PNULL). clear HOWN.
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 8 zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB AB. zstep.
    lazymatch type of FR with rw_cells _ _ _ ?cs => set (FRC := cs) in FR end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { apply presA_nil_any. eapply (presA_tail0 asegs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact MU0| exact WM0]. }
    assert (PCH1 : own = LHeap -> u32arr asegs m1 P limbs).
    { intros E. ddestruct (PHEAP E) as (_ & _ & _ & HXL & _).
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PC ALO LOS SLO NEEDR LL; lia]. }
    clear MU0 WM0.
    (* [comment removed for export] *)
    assert (KEEPH : own = LHeap -> (forall b, In b (lb_remove P LB) -> In b LB) /\ (forall b, In b LB -> ~ In b (mpd_blk dX) -> In b (lb_remove P LB))
                    /\ (forall b, In b (mpd_blk dX) -> ~ In b (lb_remove P LB)) /\ (forall b, In b (mpd_keep LB dX) -> In b (lb_remove P LB))
                    /\ (forall b, In b (mpd_blk dX) -> b = (P, 4 * n) /\ In (P, 4 * n) LB /\ 1 <= n)).
    { intros EO. ddestruct (PHEAP EO) as (_ & HIN & _ & _ & N1). cbn [mpd_blk md_own md_p md_n]. rewrite EO.
      split; [intros b Hb; eapply In_lb_remove; exact Hb|].
      split; [intros [B k] Hb Hn; apply In_lb_remove_keep; [exact Hb|]; apply (nodup_fst_neq LB P (4 * n) B k ND HIN Hb); intros E; apply Hn; left; symmetry; exact E|].
      split; [intros b [<-|[]] Hin; exact (lb_remove_notin LB P (4 * n) ND Hin)|].
      split; [intros b Hb; eapply (in_keep_remove LB (mkMPD X sg n P limbs pad LHeap)); [exact ND| reflexivity| exact HIN| exact Hb]|].
      intros b [<-|[]]. split; [reflexivity|]. split; [exact HIN| exact N1]. }
    assert (KEEPN : own = LNull -> (forall b, In b LB -> In b LB) /\ (forall b, In b LB -> ~ In b (mpd_blk dX) -> In b LB)
                    /\ (forall b, In b (mpd_blk dX) -> ~ In b LB) /\ (forall b, In b (mpd_keep LB dX) -> In b LB)
                    /\ (forall b, In b (mpd_blk dX) -> b = (P, 4 * n) /\ In (P, 4 * n) LB /\ 1 <= n)).
    { intros EO. cbn [mpd_blk md_own md_p md_n]. rewrite EO.
      split; [intros b Hb; exact Hb|]. split; [intros b Hb _; exact Hb|]. split; [intros b []|].
      split; [intros b Hb; eapply In_mpd_keep; exact Hb|]. intros b []. }
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K0 by (clear - NL; lia).
      (* [comment removed for export] *)
      zstep. if_cases KX; zify_cond KX; [exfalso; rewrite ?unsigned_lit in KX by (clear - XB; lia); clear - KX X0; lia|]. clear KX.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
        assert (EO : own = LNull) by (destruct own; [reflexivity| exfalso; destruct (PHEAP eq_refl) as [B0 _]; clear - B0 KP; lia| exfalso; exact (HNS eq_refl)]).
        ddestruct (KEEPN EO) as (HI1 & HI2 & HI3 & HI4 & HBLK).
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply finA_walk with (hc := h) (LBc := LB); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
        all: try (unfold mpi_cells; exact HXS).
        all: try (subst FRC; exact FR).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "FINA0-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        apply aevtA_done. intros mo9 [HK9 MF9].
        assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
        { eapply presA_trans; [exact HP1|]. eapply (presA_tail asegs R HIA h LB); [exact HH| exact HI4| exact LOS| exact TOP| exact OX| exact MU| exact WM]. }
        eapply (post_empty LB mo _ h); post_side.
      + (* [comment removed for export] *)
        assert (EO : own = LHeap).
        { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. rewrite (proj1 (PNULL eq_refl)) in KP.
          rewrite ?unsigned_lit in KP by (clear; lia). clear - KP. lia. }
        ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1). pose proof (PCH1 EO) as HXL1. clear PHEAP PCH1 PNULL KEEPN.
        ddestruct (KEEPH EO) as (HI1 & HI2 & HI3 & HI4 & HBLK). clear KEEPH.
        rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
        specialize (DXP EO). specialize (DSP ltac:(rewrite EO; discriminate)).
        (* [comment removed for export] *)
        zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
        (* [comment removed for export] *)
        zstep.
        replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
        pose proof (u32arr_cells asegs _ _ _ HXL1) as PCH. replace (4 * length limbs)%nat with (Z.to_nat (n * 4)) in PCH by (clear - LL; lia).
        assert (CWr : client_wrange L (lb_remove P LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
        { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HI4, Hb| right; exact Hb]. }
        free_limbs_call HH HIN PCH.
        (intros ms' mo2' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
        destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo2'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by qlia.
        ddestruct PO as (MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
        match type of HH2 with HM _ _ _ ?hh _ _ _ => rename hh into h2 end.
        assert (HP2' : presA asegs R (lb_remove P LB) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA h) [] m1 m2).
        { eapply (presA_drop_freed asegs R HIA h LB LF _ [] P (4 * n) m1 m1 m2);
            [exact HH| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
            | replace (P + 4 * n) with (P + n * 4) by (clear; lia); exact HP2].
          intros b xb Hb Hr. split; [apply HI1, Hb|]. intros E. subst b. exact (lb_remove_notin LB P (4 * n) ND Hb). }
        clear HP2 PCH HXL1.
        presA_transport HP2'.
        assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
        { eapply presA_trans; [exact HP1|]. eapply presA_weaken; [exact HP2'| exact HI4| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
        apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
        pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX) as OX2.
        assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply finA_walk with (hc := h2) (LBc := lb_remove P LB); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
        all: try (unfold mpi_cells; exact HXS).
        all: try (subst FRC; exact FR).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "FINA1-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        apply aevtA_done. intros mo9 [HK9 MF9].
        assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
        { eapply presA_trans; [exact HPX2|]. rewrite <- HS2. eapply (presA_tail asegs R HIA h2 (lb_remove P LB)); [exact HH2| exact HI4| exact LOS| exact TOP2| exact OX2| exact MU| exact WM]. }
        eapply (post_empty (lb_remove P LB) mo _ h2); post_side.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K0 by (clear - NL; lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
      zstep.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in K1 by (clear - NL NR; lia).
        (* [comment removed for export] *)
        zstep. if_cases KP; zify_cond KP.
        * (* [comment removed for export] *)
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          assert (EO : own = LNull) by (destruct own; [reflexivity| exfalso; destruct (PHEAP eq_refl) as [B0 _]; clear - B0 KP; lia| exfalso; exact (HNS eq_refl)]).
          ddestruct (KEEPN EO) as (HI1 & HI2 & HI3 & HI4 & HBLK). destruct (PNULL EO) as [EP En].
          eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
            [ eapply mid_walk with (hc := h) (LBc := LB); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
          all: try (unfold mpi_cells; exact HXS).
          all: try (subst FRC; exact FR).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "MID0-PRE-LEFT:" g end.
          intros ms' PO. ddestruct PO as (a0' & a1' & m3 & E & MU & WM & MI3 & HX3 & FR3 & ST3 & HH3). subst ms'.
          pose proof (aobj_munch asegs AL CS CSOK [(X, X + 16)] m1 m3 X 16 ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX| apply Forall_nil]) MU OX) as OX3.
          assert (HPX3 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m3).
          { eapply presA_trans; [exact HP1|]. eapply (presA_tail asegs R HIA h LB); [exact HH| exact HI4| exact LOS| exact TOP| exact OX| | exact WM].
            eapply munch_weaken; [| exact MU]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
          eapply grow_part with (LBr := LB); try eassumption; try reflexivity.
          all: try (intros y Hy; exact Hy).
          all: try (subst FRC; exact FR3).
          all: try (unfold AVOL_CALL; clear; lia).
          all: try (unfold fr_charge; clear - D0; lia).
          all: try (clear - K0 NL; lia).
          all: try (clear - K1; lia).
          all: first [exact C24H | match goal with |- ?g => idtac "GP0-PRE-LEFT:" g end].
        * (* [comment removed for export] *)
          assert (EO : own = LHeap).
          { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. rewrite (proj1 (PNULL eq_refl)) in KP.
            rewrite ?unsigned_lit in KP by (clear; lia). clear - KP. lia. }
          ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1). pose proof (PCH1 EO) as HXL1. clear PHEAP PCH1 PNULL KEEPN.
          ddestruct (KEEPH EO) as (HI1 & HI2 & HI3 & HI4 & HBLK). clear KEEPH.
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          specialize (DXP EO). specialize (DSP ltac:(rewrite EO; discriminate)).
          (* [comment removed for export] *)
          zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
          pose proof (u32arr_cells asegs _ _ _ HXL1) as PCH. replace (4 * length limbs)%nat with (Z.to_nat (n * 4)) in PCH by (clear - LL; lia).
          assert (CWr : client_wrange L (lb_remove P LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HI4, Hb| right; exact Hb]. }
          free_limbs_call HH HIN PCH.
          (intros ms' mo2' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
          destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo2'.
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by qlia.
          ddestruct PO as (MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
            replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
          match type of HH2 with HM _ _ _ ?hh _ _ _ => rename hh into h2 end.
          assert (HP2' : presA asegs R (lb_remove P LB) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA h) [] m1 m2).
          { eapply (presA_drop_freed asegs R HIA h LB LF _ [] P (4 * n) m1 m1 m2);
              [exact HH| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
              | replace (P + 4 * n) with (P + n * 4) by (clear; lia); exact HP2].
            intros b xb Hb Hr. split; [apply HI1, Hb|]. intros E. subst b. exact (lb_remove_notin LB P (4 * n) ND Hb). }
          clear HP2 PCH HXL1.
          presA_transport HP2'.
          assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
          { eapply presA_trans; [exact HP1|]. eapply presA_weaken; [exact HP2'| exact HI4| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
          apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
          clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
          pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX) as OX2.
          assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
          (* [comment removed for export] *)
          
          eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
            [ eapply mid_walk with (hc := h2) (LBc := lb_remove P LB); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
          all: try (unfold mpi_cells; exact HXS).
          all: try (subst FRC; exact FR).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "MID1-PRE-LEFT:" g end.
          intros ms' PO. ddestruct PO as (a0' & a1' & m3 & E & MU & WM & MI3 & HX3 & FR3 & ST3 & HH3). subst ms'.
          pose proof (hcs_ok asegs R HIA h2) as CSOK2.
          pose proof (aobj_munch asegs AL _ CSOK2 [(X, X + 16)] m2 m3 X 16 ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX2| apply Forall_nil]) MU OX2) as OX3.
          assert (HPX3 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m3).
          { eapply presA_trans; [exact HPX2|]. rewrite <- HS2. eapply (presA_tail asegs R HIA h2 (lb_remove P LB)); [exact HH2| exact HI4| exact LOS| exact TOP2| exact OX2| | exact WM].
            eapply munch_weaken; [| exact MU]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
          eapply grow_part with (LBr := lb_remove P LB); try eassumption; try reflexivity.
          all: try (subst FRC; exact FR3).
          all: try (clear - K0 NL; lia).
          all: try (clear - K1; lia).
          all: first [exact C24H | match goal with |- ?g => idtac "GP1-PRE-LEFT:" g end].
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in K1 by (clear - NL NR; lia).
        assert (En : n = nl) by (clear - K1; lia).
        assert (EO : own = LHeap).
        { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. destruct (PNULL eq_refl) as [_ N0]. clear - N0 En K0. lia. }
        ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1). pose proof (PCH1 EO) as HXL1. clear PHEAP PCH1 PNULL KEEPN.
        ddestruct (KEEPH EO) as (HI1 & HI2 & HI3 & HI4 & HBLK). clear KEEPH.
        specialize (DXP EO).
        replace (Z_to_bv 64 nl) with (Z_to_bv 64 n) by (rewrite En; reflexivity).
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply finB_walk; try eassumption; try reflexivity | intros y Hy; exact Hy | ].
        all: try (unfold mpi_cells; exact HXS).
        all: try (subst FRC; exact FR).
        all: try (unfold MPI_MAX_LIMBS; clear - NR N1; lia).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "FINB-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & HPZ9 & ST9 & HH9). subst ms'.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        apply aevtA_done. intros mo9 [HK9 MF9].
        assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
        { eapply presA_trans; [exact HP1|].
          (* [comment removed for export] *)
          eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] P (4 * n) m1 m1 m9);
            [exact HH| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
          - intros b xb Hb Hr. unfold mpd_keep in Hb. cbn [md_own md_p md_n] in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
            split; [exact Hb|]. intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
          - eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                      (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16); (P, P + 4 * n)]);
              [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside]; clear; intros y Hy; tauto].
            eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m1 m9); [exact HH| | clear; lia| exact LOS].
            eapply (presA_of_munch asegs R LB LF _ _ _ _ m1 m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU | exact WM].
            unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
            apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|].
            apply Forall_cons; [cbn [fst snd]; replace (P + 4 * n - P) with (4 * n) by lia; eapply hcs_block; [exact HH| exact HIN]|]. apply Forall_nil. }
        eapply (post_same mo); post_side.
    all: first [exact C24H | match goal with |- ?g => idtac "MAIN-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_mpi_resize_clear_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "PR,$5<.PHIA,(5=.$>.R1.)P,(5>.(1>.R2.))P,(5?.$>.R3.R2.$60.)P,(22.$2.(61.R4.)$62.)P,(22.$2.(63.R5.)$64.)P,(4.=(65.R6.))P,Ph,(=.$>.R7.R6.)PLB,(:.$;.)PLF,(:.$;.)Pm,P,(?.&40.)(10.(?.&8.))P,(11.$>.R;.R:.R4.R3.R2.R1.)(66.$2.(67.(32.$2.$2.)$2.(68.$2.$2.)R4.))P,(3.(4.(69.(2=.R8.))(6:.(2=.R8.)))(4.(6;.(2=.R8.))(6<.(2=.R8.))))(6=.$>.R9.R8.$5;.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMS NEEDR HND DIMG. unfold mpi_resize_clear_stmtA_c, mpi_xop_stmtA_c.
  intros until d. intros HH HK MX HNS NLv XW DSP ST LOS SLO TOP SPA TPV MI RA2 OXA BUD UW XUW BUDF C24H -> ->.
  destruct dX as [X sg n P limbs pad own].
  eapply main_walk; try eassumption; [exact (proj1 MX)| exact (proj1 OXA)].
Qed.

(* [comment removed for export] *)
Lemma A_mpi_resize_clear_spec_closed_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "PR,$5<.PHIA,(5=.$>.R1.)P,(5>.(1>.R2.))P,(22.$2.(6>.R3.)$6?.)P,(22.$2.(70.R4.)$71.)P,(22.$2.(61.R5.)$62.)P,(22.$2.(63.R6.)$64.)P,Pm,P,(?.&40.)(10.(?.&8.))P,(72.R8.R1.)(73.R2.)P,(4.=(74.R8.))P,(4.=(75.R9.))P,(4.=(65.R:.))P,Ph,(=.$>.R;.R:.)PLB,(:.$;.)PLF,(:.$;.)Pm,P,(?.&40.)(10.(?.&8.))P,(11.$>.R?.R>.R4.R3.R2.R1.)(66.$2.(67.(32.$2.$2.)$2.(68.$2.$2.)R4.))P,(3.(4.(69.(2=.R<.))(6:.(2=.R<.)))(4.(6;.(2=.R<.))(6<.(2=.R<.))))(6=.$>.R=.R<.$5;.)")
(* [comment removed for export] *).
Proof.
  intros. eapply A_mpi_resize_clear_spec_c; eauto. eapply A_zeroize_and_free_spec; eauto.
Qed.

(* [comment removed for export] *)
Definition mpi_resize_clear_coreA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Ph,(=.O4.O3.O2.)PLB,(:.$;.)PLF,(:.$;.)Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(76.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pmo,$40.PdX,$7.Pnl,$2.Plo,$2.Pd,$2.P,(11.O4.O3.O2.R2:.R29.R28.R6.)P,(48.O4.O3.O2.R2;.R6.)P,(77.O4.R8.R2;.R6.)P,(4;.(22.$50.(78.R7.)$79.))P,(3.(4.=R7.)(5.R7.(6.+2.+40.)))P,(7:.O3.R2>.R2=.(12.&40.R2;.)(13.O4.O3.O2.R2?.)R9.)P,P,(4;.(22.$50.(78.R:.)$7;.))(2:.(4.(15.(7<.R;.)(39.+4.(7=.R;.)))R9.)(4.(12.&40.R2=.)(7<.R;.)))P,(1;.O4.R=.R9.(12.&40.R2=.))P,(4.(45.O3.)R:.)P,(4.R;.(7>.(7>.(12.&40.R2?.)+60.)(65.O3.)))P,(4.(12.&40.R30.)(13.O4.O3.O2.R34.))P,(22.$2.(29.(12.&40.R31.)+10.)=)P,(22.(?.&40.)R30.(25.&40.(7?.O3.)))P,(1<.O4.R13.)P,(30.O4.(1>.O3.)(1?.O4.O3.O2.R38.)R14.(80.R12.)+10.)P,(4.(15.(49.O4.O3.O2.R39.)(8.R12.))$55.)P,(81.O3.(80.R14.)+10.R11.)P,(4.(15.(4:.O4.O3.O2.R3;.)(9.R12.))$56.)P,(4.(15.(82.R3;.)$1.)$83.)P,(22.(?.&40.)R31.(25.&40.(80.R17.)))P,(22.(?.&40.)R31.(25.&40.R17.))(5:.O4.(4>.O4.O3.O2.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R3?.R3>.R3=.R19.Lr,$2.LdX',$7.(<.R1:.R1;.R40.R2.R1.)(8.R18.)(9.R16.)R17.R1;.R1:.)(4?.(23.(24.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(25.&40.O1.)R1<.(27.(?.&40.))R1;.(28.O4.))R1:.))")
(* [comment removed for export] *).

Lemma A_mpi_resize_clear_core_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "PR,$5<.PHIA,(5=.$>.R1.)P,(5>.(1>.R2.))P,(5?.$>.R3.R2.$60.)P,(22.$2.(61.R4.)$62.)P,(22.$2.(63.R5.)$64.)P,(4.=(65.R6.))P,Ph,(=.$>.R7.R6.)PLB,(:.$;.)PLF,(:.$;.)Pm,P,(?.&40.)(10.(?.&8.))P,(11.$>.R;.R:.R4.R3.R2.R1.)(66.$2.(67.(32.$2.$2.)$2.(68.$2.$2.)R4.))P,(3.(4.(69.(2=.R8.))(6:.(2=.R8.)))(4.(6;.(2=.R8.))(6<.(2=.R8.))))(84.$>.R9.R8.$5;.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMS NEEDR HND DIMG. unfold mpi_resize_clear_coreA_c.
  intros until d. intros HH HK MX HNS NLv XW DSP ST LOS SLO TOP SPA TPV MI OX BUD XUW BUDF C24H -> ->.
  destruct dX as [X sg n P limbs pad own].
  eapply main_walk; try eassumption. exact (proj1 MX).
Qed.

(* [comment removed for export] *)
Definition mpi_resize_clear_coreA_r_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "Ph,(=.O4.O3.O2.)PLB,(:.$;.)PLF,(:.$;.)Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(76.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pmo,$40.PdX,$7.Pnl,$2.Plo,$2.Pd,$2.P,(11.O4.O3.O2.R2:.R29.R28.R6.)P,(48.O4.O3.O2.R2;.R6.)P,(59.O4.R8.R2;.R6.)P,(4;.(22.$50.(78.R7.)$79.))P,(3.(4.=R7.)(5.R7.(6.+2.+40.)))P,(7:.O3.R2>.R2=.(12.&40.R2;.)(13.O4.O3.O2.R2?.)R9.)P,P,(4;.(22.$50.(78.R:.)$7;.))(2:.(4.(15.(7<.R;.)(39.+4.(7=.R;.)))R9.)(4.(12.&40.R2=.)(7<.R;.)))P,(1;.O4.R=.R9.(12.&40.R2=.))P,(4.(45.O3.)R:.)P,(4.R;.(7>.(7>.(12.&40.R2?.)+60.)(65.O3.)))P,(4.(12.&40.R30.)(13.O4.O3.O2.R34.))P,(22.$2.(29.(12.&40.R31.)+10.)=)P,(22.(?.&40.)R30.(25.&40.(7?.O3.)))P,(1<.O4.R13.)P,(30.O4.(1>.O3.)(1?.O4.O3.O2.R38.)R14.(80.R12.)+10.)P,(4.(15.(49.O4.O3.O2.R39.)(8.R12.))$55.)P,(81.O3.(80.R14.)+10.R11.)P,(4.(15.(4:.O4.O3.O2.R3;.)(9.R12.))$56.)P,(4.(15.(82.R3;.)$1.)$83.)P,(22.(?.&40.)R31.(25.&40.(80.R17.)))P,(22.(?.&40.)R31.(25.&40.R17.))(5:.O4.(4>.O4.O3.O2.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R3?.R3>.R3=.R19.Lr,$2.LdX',$7.(<.R1:.R1;.R40.R2.R1.)(8.R18.)(9.R16.)R17.R1;.R1:.)(4?.(23.(24.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(25.&40.O1.)R1<.(27.(?.&40.))R1;.(28.O4.))R1:.))")
(* [comment removed for export] *).

Lemma A_mpi_resize_clear_core_r_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear_c24 ()) "PR,$5<.PHIA,(5=.$>.R1.)P,(5>.(1>.R2.))P,(5?.$>.R3.R2.$60.)P,(22.$2.(61.R4.)$62.)P,(22.$2.(63.R5.)$64.)P,(4.=(65.R6.))P,Ph,(=.$>.R7.R6.)PLB,(:.$;.)PLF,(:.$;.)Pm,P,(?.&40.)(10.(?.&8.))P,(11.$>.R;.R:.R4.R3.R2.R1.)(66.$2.(67.(32.$2.$2.)$2.(68.$2.$2.)R4.))P,(3.(4.(69.(2=.R8.))(6:.(2=.R8.)))(4.(6;.(2=.R8.))(6<.(2=.R8.))))(85.$>.R9.R8.$5;.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMS NEEDR HND DIMG. unfold mpi_resize_clear_coreA_r_c.
  intros until d. intros HH HK MX HNS NLv XW DSP ST LOS SLO TOP SPA TPV MI OX BUD XUW BUDF C24H -> ->.
  destruct dX as [X sg n P limbs pad own].
  eapply main_walk; try eassumption.
Qed.
