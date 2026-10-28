(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_grow.
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
Ltac2 gd_tbl_A_mpi_grow_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_c24.mpi_xop_stmtA_c"; "C24_GROW_c"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow.grow_FR"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_grow.grow_R"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_GROW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow.A_WRAP_CALLOC_GR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow.A_ASAN_MEMCPY_GR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "mpi_grow_stmtA_c"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_MEMSET_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"].



Definition C24_GROW_c : Z := 1.
Definition mpi_grow_stmtA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_c24 ()) "(0.O4.O3.O2.O1.+60.$1.Lnb,$2.(3.(4.=R1.)(5.R1.(6.+2.+40.)))L,$7.Lnb,$2.(8.R1.)$9.LLB,(:.$;.)LdX,$7.Lnb,$2.Lr,$2.LdX',$7.(<.R3.R4.R5.R2.R1.))")
(* [comment removed for export] *).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09b4f8]).
Local Ltac zchk_new ::= constr:([0x09b414; 0x09b418; 0x09b41c; 0x09b478; 0x09b47c; 0x09b480]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_GR.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_GR.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Hypothesis C24H : cnt24 LB + C24_GROW_c <= C24MAX.     (* [comment removed for export] *)
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sg n P : Z) (limbs : list word) (pad : word) (own : limb_own) (nb lo d : Z).
  Local Notation dX := (mkMPD X sg n P limbs pad own).
  Hypothesis HNS : own <> LStatic.
  Hypothesis NB : 0 <= nb < 2^64.
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
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHX10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Notation FRAME := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)
  Notation POST := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                      (fun r dX' => grow_R nb dX LB r dX') (grow_PHI nb) (grow_FR d) lo).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L12283411672.95L14106684376.95L29428324939.5 L35653441506.7 L36423571333.94L41288976216.95L44866992728.95L48429268312.95L49345641752.93L5145216728.95 L60098763854.3 L8722184664.95 Q15641568614.94Q18364007270.94Q21877861637.94Q27904925317.94Q32653586022.94Q33915848709.94Q3832210565.94 Q39941338501.94Q41154176102.94Q44650594790.94Q51233520870.94Q59840699110.94Q66523986693.94Q9840924165.94 00000400800J00d01;01?01C01G01K01O01Y01]01d01k02>02Q02X02k03>03Q03X03_03f03m04@04SS2spS2spS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS1R5NEEDR2sp2lo3SLO3SPRS2spS2spS2spS2spS2spS1R2lo3LOSS2spS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_c24 ()) "Phc,(=.$>.VR,VHIA,)PLBc,(:.$;.)Pmm,P,(?.&40.)(10.(?.&8.))Pr,$2.Pjk,(:.(?.&8.))Pxra,(?.&40.)Pxs0,(?.&40.)Pxs1,(?.&40.)Pxs2,(?.&40.)Pxs3,(?.&40.)Pxs4,(?.&40.)Pxs5,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,R1:.R19.VLF,R18.)P,(4.(12.&40.Vsp,)(13.$>.VR,VHIA,R1;.))P,(14.$>.R1:.(15.(12.&40.Vsp,)-40.)(16.$17.(18.#8.R18.)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R1;.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R1<.)(1=.$>.(1>.VR,)(1?.$>.VR,VHIA,R1?.)Lms',$20.(21.(?.&40.)Lx5,(?.&40.)(21.(?.&40.)Lx6,(?.&40.)(21.(?.&40.)Lx7,(?.&40.)(21.(?.&40.)La1',(?.&40.)(21.(?.&40.)La2',(?.&40.)(21.(?.&40.)La3',(?.&40.)(21.(?.&40.)La4',(?.&40.)(21.(?.&40.)La5',(?.&40.)(21.(?.&40.)La6',(?.&40.)(21.(?.&40.)La7',(?.&40.)(21.(?.&40.)Lx28,(?.&40.)(21.(?.&40.)Lx29,(?.&40.)(21.(?.&40.)Lx30,(?.&40.)(21.(?.&40.)Lx31,(?.&40.)(3.(22.$20.R?.(23.(24.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(25.&40.R2;.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(26.Vra,)Vfc,(27.(?.&40.))R2<.(28.$>.)))(1;.$>.R2<.Vlo,(12.&40.Vsp,)))))))))))))))))(23.(24.R1:.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R13.R12.R11.R19.R18.(25.&40.R1<.)R10.R?.R>.R=.R<.R;.R:.R17.R16.R15.R14.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(25.&40.+9;4=4.)Vfc,(27.(?.&40.))R1=.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc FR ST MI.
    pose proof (hcs_ok asegs R HIA hc) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@D24976250634.108D52014138856.108D52014138856.109D62155808737.109K43355168775.108K43355168775.109L12283411672.105L14106684376.105L23100341967.105L29428324939.5  L35653441506.7  L36425783560.105L41288976216.105L43361613547.2  L44866992728.105L46160487540.104L48429268312.105L49345641752.104L49578233423.105L50790580594.6  L5145216728.105 L60098763854.3  L8722184664.105 Q12370813529.106Q15643290603.105Q17207353341.105Q18365959659.105Q20414272036.108Q20414272036.109Q21879808904.105Q24974040330.107Q26207421841.104Q26207721832.105Q26207967338.102Q27907166216.105Q31654082872.104Q32655335659.105Q33918027400.105Q37625275423.105Q3830196744.105 Q39212284437.105Q39939652360.105Q41152162539.105Q42081808994.105Q43925228937.105Q44648681323.105Q51236024939.105Q52016320488.107Q52016320488.108Q5485174314.106 Q5485603330.105 Q59843171435.105Q60511567613.105Q60697995187.105Q6143569392.106 Q62157788641.108Q62965564504.106Q62965564504.107Q66522035592.105Q7891539809.106 Q8880503606.102 Q9538787269.102 Q9843398792.105 00000K00f01A01\02J03803A03J03S03e04?04[04d04e04n05705@05I05R05i06206<06E06S06_06e07107O07m08E08]08c08i08o09G09M09Y0:10:70:O0:U0:m0;90;B0;H0;T0;`0<80<P0<V0<\0<h0<n0=40=:0=R0=a0>00>H0>Q0>W0>]0?5S2sp1X2nb2XB2HB5Ha_st5Hl_stS2sp1X2nb2XB2HB5Ha_st5Hl_stS2sp1X2pn2XB2HB5Ha_st5Hl_stS2sp1X2pn2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2nb2lo3SLO3DSX2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO2pn3DSX2XB2HB5Ha_st5Hl_stS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS1R5NEEDR2sp1X2lo3SLO3SPR2XBS2sp1X2XBFS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R5NEEDR2sp2lo3LOS3SLOS2sp1X2XBS1R2lo3LOSS2sp1X2XBS2sp1X4ALX82XBS2sp1X2lo2XBS1X2XBS2sp1X2lo2XBS2sp1X2nb2lo2XB2HB5Ha_st5Hl_stS2sp1X2lo2pn2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO2XBS1X2nb2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS2sp1X2lo2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS2sp1X2lo2XBS1X2XB2HBS1X2XBS2sp1X2lo2XBS2sp1X2lo2XBS1X2nb2XB2HB5Ha_st5Hl_stS1X2pn2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS2sp1X2lo2XBS1X2XBS1X2XBS1X2XBS1X2pn2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_stS1X2XB2HB5Ha_stS1R5NEEDR2sp1X2lo3SLO2XBS1X2XB2HBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma fin_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_c24 ()) "Phc,(=.$>.VR,VHIA,)PLBc,(:.$;.)Pmm,P,(?.&40.)(10.(?.&8.))Ppw,$2.Pnw,$2.Ppn,$2.Pjk,(:.(?.&8.))Pxra,(?.&40.)Pxt0,(?.&40.)Pxt1,(?.&40.)Pxt2,(?.&40.)Pxa0,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Pxt3,(?.&40.)Pxt4,(?.&40.)Pxt5,(?.&40.)Pxt6,(?.&40.)P,(11.$>.VR,VHIA,R17.R16.VLF,R15.)P,(22.$2.(13.$>.VR,VHIA,R18.)(13.$>.VR,VHIA,Vh,))P,(4.(12.&40.Vsp,)(13.$>.VR,VHIA,R19.))P,(22.$2.(29.VX,+8.)=)P,(2:.(4.(15.VX,+10.)Vlo,)(4.(12.&40.Vsp,)VX,))P,(3.(4.=R17.)(5.R17.(6.+2.+40.)))P,(14.$>.R1;.VX,(2;.R1:.(25.&40.Vsg,)R19.Vpad,))P,(2<.(2=.VR,)(2>.$;.R1=.(2?.VLF,))(12.&40.Vsp,)(13.$>.VR,VHIA,Vh,)VX,+10.)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,R1?.)R1=.VX,+10.)P,(14.$>.R1>.(15.(12.&40.Vsp,)-40.)(16.$17.(18.#8.R1:.)(16.$17.(19.Vs5,)(16.$17.(19.Vs4,)(16.$17.(19.Vs3,)(16.$17.(19.Vs2,)(16.$17.(19.Vs1,)(16.$17.(19.Vs0,)(16.$17.(19.Vra,)(1:.$17.))))))))))P,(1;.$>.R1?.Vlo,(15.(12.&40.Vsp,)-40.))P,(1<.$>.R20.)(1=.$>.(1>.VR,)(1?.$>.VR,VHIA,R23.)Lms',$20.(21.(?.&40.)Lx5,(?.&40.)(21.(?.&40.)Lx6,(?.&40.)(21.(?.&40.)Lx7,(?.&40.)(21.(?.&40.)La1',(?.&40.)(21.(?.&40.)La2',(?.&40.)(21.(?.&40.)La3',(?.&40.)(21.(?.&40.)La4',(?.&40.)(21.(?.&40.)La5',(?.&40.)(21.(?.&40.)La6',(?.&40.)(21.(?.&40.)La7',(?.&40.)(21.(?.&40.)Lx28,(?.&40.)(21.(?.&40.)Lx29,(?.&40.)(21.(?.&40.)Lx30,(?.&40.)(21.(?.&40.)Lx31,(?.&40.)(21.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(3.(22.$20.R10.(23.(24.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(26.Vra,)Vfc,(27.(?.&40.))R1.(28.$>.)))(3.(31.(16.(32.$2.$2.)(33.$2.$2.Vlo,(12.&40.Vsp,))(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.))))R31.R1.)(3.(34.$>.R31.R1.)(3.(1<.$>.R1.)(3.(14.$>.R1.VX,(2;.R2>.(25.&40.Vsg,)Vnb,Vpad,))(3.(1;.$>.R1.Vlo,(12.&40.Vsp,))(11.$>.VR,VHIA,R33.R32.VLF,R1.))))))))))))))))))))))(23.(24.R1<.(25.&40.(15.(12.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.(25.&40.VX,)(25.&40.Vnb,)R18.R17.R16.R15.R14.R13.R12.R11.(25.&40.(15.VX,+:.))(25.&40.R1>.)(25.&40.(15.(35.(15.VX,+:.)+3.)(36.(1>.VR,))))(25.&40.(15.(35.VX,+3.)(36.(1>.VR,))))Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(25.&40.+9;4;4.)Vfc,(27.(?.&40.))R21.(28.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc ALX8 DSX PNB HX CWc OX FR ST MI.
    pose proof (hcs_ok asegs R HIA hc) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: first [exact C24H | match goal with |- ?g => idtac "FIN-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39010053918.3L67805705926.300000:00DS1n2nb3HleS1n2nb3Hle". (* [comment removed for export] *)
  #[using="HNS"] Lemma post_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_c24 ()) "Pmo,$37.Pmo',$37.Ph',(=.$>.VR,VHIA,)Pm',P,(?.&40.)(10.(?.&8.))Pr,$2.Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Pxa1,(?.&40.)Pxa2,(?.&40.)Pxa3,(?.&40.)Pxa4,(?.&40.)Pxa5,(?.&40.)Pxa6,(?.&40.)Pxa7,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(1<.$>.R10.)P,(1;.$>.R11.Vlo,(12.&40.Vsp,))P,(38.R15.R14.)P,(39.$>.VR,(3:.VLB,(3;.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(12.&40.Vsp,)(3<.VR,)(3=.$>.VR,VHIA,Vh,)(16.(32.$2.$2.)(33.$2.$2.VX,(15.VX,+10.))(1:.(32.$2.$2.)))Vm,R13.)P,(22.$2.(13.$>.VR,VHIA,R15.)(13.$>.VR,VHIA,Vh,))P,(22.$2.(3=.$>.VR,VHIA,R16.)(3=.$>.VR,VHIA,Vh,))P,(22.$2.(3>.$>.VR,VHIA,R17.)(3>.$>.VR,VHIA,Vh,))P,(3?.$>.VR,VHIA,R18.R19.)P,Px,$2.P,(1?.$>.VR,VHIA,Vh,R1.)(1?.$>.VR,VHIA,R1;.R2.)P,(4.(40.$>.VR,VHIA,R1:.)(15.(40.$>.VR,VHIA,Vh,)(8.Vnb,)))P,(4.(41.$>.VR,VHIA,R1;.)(15.(41.$>.VR,VHIA,Vh,)(9.Vd,)))P,(11.$>.VR,VHIA,R1<.VLB,VLF,R1;.)P,(42.$>.R1<.VLB,(3;.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(2:.(22.$2.R1<.$43.)(3.(22.$2.R1<.=)(4.Vnb,Vn,)))(44.$>.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3;.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$2.LdX',$7.(<.Vnb,(3;.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(8.Vnb,)(9.Vd,)Vlo,Vm,R21.(45.(23.(24.Vra,Vsp,Vgp,Vtp,R1<.R1;.R1:.Vs0,Vs1,(25.&40.R1=.)R19.R18.R17.R16.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(26.Vra,)Vfc,(27.(?.&40.))R1>.(28.$>.))R20.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH MA Hr.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB, dX, r.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [apply mpd_out_refl; cbn [md_own]; exact HNS|].
    split; [intros b Hb; left; exact Hb|].
    split; [| intros b Hb; left; exact Hb].
    destruct Hr as [->|[-> Hle]]; [right; split; reflexivity| left].
    cbn [md_sg md_n md_pad md_limbs]. replace (Z.to_nat (nb - n)) with 0%nat by (clear - Hle; lia). cbn [repeat]. rewrite app_nil_r.
    split; [reflexivity|]. split; [reflexivity|]. split; [clear - Hle; lia|]. split; [reflexivity|]. split; [reflexivity|]. intros _; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac keep_return hh LBx rr FRC FR LAWS KINV :=
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "04[0@C17025492443.194C31740276271.195D13554616751.117D13554616751.118D13589037945.222D16049893661.196D17815656873.221D20501856385.196D30461620607.222D33379250345.222D34779215654.222D35881667587.117D35881667587.118D37703914153.221D37703914153.222D50796826103.196D52756908355.221D52756908355.222D59428651230.152D59429060293.222D63595235433.196K25897202343.195K36659004088.195K36719207456.194K42587433812.117K42587433812.118K51736254456.195K53933808495.195K61205767951.195L11412023960.5  L11414166579.17 L11414166579.24 L11468776467.3  L1157912586.115 L1160237219.191 L1160237219.247 L11668949970.158L1172642220.248 L11946965170.10 L12283411672.113L12694533441.2  L12750819336.13 L12755534717.11 L13301871092.113L13603882068.12 L14106684376.112L14369733550.2  L15089701933.3  L16256253080.7  L1685717371.0   L17379109507.22 L17585880332.15 L17646078182.113L18294800738.11 L19130496105.22 L1936974140.17  L1954497222.2   L19935441067.248L19946008845.115L19947878820.191L19947878820.247L21369350046.3  L22601415187.4  L23100341967.158L23100341967.185L23298740641.0  L24483526758.2  L24912882372.1  L24914258088.247L25426381488.10 L25426381488.12 L25890634160.3  L26707095699.5  L26798959255.4  L26798959255.6  L26892418956.1  L28813938827.13 L28814040852.158L28943460204.4  L29428324939.5  L32693198944.7  L3278082148.2   L32987209960.7  L33087634096.2  L33656389660.22 L33669001629.17 L34171955900.9  L34413141779.24 L34838818203.22 L35561496115.4  L35653441506.7  L36671000797.4  L36715738693.2  L3722508646.8   L37334827261.4  L37714553091.1  L38314509377.12 L38725398356.5  L38948636245.0  L39027378935.22 L39039630198.24 L39172636981.0  L39280637297.0  L39887139444.113L40108971872.12 L40281191306.3  L40290687782.1  L40369445627.7  L40803681500.7  L40825300077.22 L40834179097.118L41288976216.113L4233605228.5   L42594106808.2  L43061363337.111L44697879740.4  L44866992728.113L45026238780.2  L45388968343.153L45771419496.4  L45818796787.5  L45898055924.113L46122776823.12 L46160478526.114L46160487540.117L46160487540.164L46702865590.227L46948705943.24 L47209170218.1  L48132467214.7  L48429268312.113L49350293428.24 L49578891104.24 L49657279893.4  L50790809970.7  L5145216728.113 L51632320110.3  L51731989917.3  L51879758738.7  L51881576583.10 L51925114228.113L5260163351.157 L52752331497.8  L53923074168.4  L547707976.3    L5479049730.1   L54897920813.3  L57402658371.4  L57838325364.22 L57933933556.113L58804912007.12 L59308632307.1  L59308633593.3  L59308661072.8  L59308668813.4  L59308742867.3  L59310683780.4  L59314873579.6  L59321342699.2  L60098763854.3  L60447862057.2  L60549562490.3  L61211782168.3  L61929718192.2  L61929812241.117L61931164306.163L61931850903.184L62018535662.1  L62369652128.2  L62624471726.46 L62625145375.46 L63799194974.9  L6386878927.22  L63962036340.112L64194470200.2  L64966926188.10 L64968776825.7  L656136024.1    L66610753222.7  L67996112456.1  L68108785696.1  L6992249585.12  L7273050298.6   L7274816372.113 L774765788.5    L8722184664.113 L8810490561.4   N12401863469.195N20716133971.195N31170017719.195N32071669760.195N53807417181.195O17025492443.194O17919651190.195O29478932113.195O31740276271.195O39322336069.195O47259422021.195O49587672251.194O57399310481.195O65674534437.195P25897202343.195P36719207456.194P44704452523.194P45829525988.195P6985681382.195 P8434753010.221 P8434753010.222 P8435147753.151 P8435147753.152 Q11523265569.196Q12370813529.163Q12370813529.193Q15457446739.114Q15457446739.115Q15643324129.113Q17205254096.192Q17207204208.162Q18365925601.114Q18694146040.119Q21798041355.119Q21879645826.114Q25157988860.119Q25513505925.116Q25513505925.117Q25662358575.119Q26207421841.118Q26207721832.119Q26207721832.172Q26207774677.116Q26209519061.171Q26209819600.192Q26220304629.169Q27907200258.114Q29651637810.193Q30985055127.140Q30985055127.216Q30987168515.176Q30987329587.198Q30987329589.122Q31228709292.119Q31394594844.119Q31651620729.192Q31651985788.171Q31654082872.118Q32655500769.114Q33918256002.114Q35014437530.119Q35717497884.119Q37623180338.192Q37625422482.162Q37703787028.196Q38248387216.196Q3830427394.114 Q39212284437.119Q39212284437.172Q39939554818.114Q41152393185.114Q4143427880.119 Q43879899724.196Q43925228937.119Q43925228937.172Q44648843873.114Q44728669274.152Q44729068097.222Q48514199408.221Q48514322795.151Q49698585326.115Q49698585326.116Q51235796833.114Q5262061745.122 Q5262061751.198 Q53969758199.119Q5483504175.192 Q5485174314.163 Q5485174314.193 Q5485489295.162 Q59843137889.114Q60511567613.119Q60511567613.172Q60697995187.119Q60697995187.172Q6143569392.163 Q6143569392.193 Q61802139820.119Q6416456232.119 Q64255486968.119Q65983947055.163Q65983947055.193Q66522067074.114Q67528989526.117Q67528989526.118Q7377275490.116 Q7377275490.117 Q8880817289.116 Q8885009321.169 Q9534281562.169 Q9538463866.116 Q9843367298.113 00000100200m02702\02]03603703803c04N05;06706M06c07V07W07X07g08=08>08?08e08f09_0:g0;=0;a0<B0<Q0<c0=50=A0=P0=a0>70?60?L0?k0@:0@;0@<0@=0@L0@M0@\0@]0@f0A<0A=0AP0AQ0A`0Ak0B90BL0BR0Bk0C=0CQ0Cj0D30D?0DP0Df0Dg0Dl0Do0EG0Ec0FE0FF0FX0Fc0G40G80Ge0H]0Hi0I;0IK0IL0I_0Ie0J:0JO0Jj0K70KQ0K]0L=0L>0L?0L@0LD0LG0LX0Lf0Lg0M30M?0M@0MA0MP0Me0Mn0N10NG0Nb0Nf0O70OF0OU0OV0P;0P<0PK0PT0Pc0Q10Q20QA0Qb0R40RF0R_0S50SS0SV0T10T@0TV0U50U>0UU0Ud0Un0Uo0V00V>0VM0Va0Vb0Vc0Vm0W00W<0WJ0WZ0Wi0XK0XO0XX0Xn0Y90YB0YO0Y_0Y`0Yj0Z00Z80Z90Z?0ZS0Zn0[I0[L0[Q0[R0[S0[m0\70\F0\M0\a0\b0\e0]80]<0]@0]A0]S0]b0^50^D0^R0_D0_\0`40`50`60`70`80`90`:0`;0`<0`=0`>0`?0`@0`A0``0aI0b@0bO0b^0bm0c<0cR0cj0dG0dY0dk0e=0eI0eU0eg0f:0f;0fY0fl0gP0hC0hD0hP0h\0hh0i40i@0iL0iX0j60j70je0kS0lA0lo0m]0n10n=0nI0nU0na0o30oQ0oe0of10210>10L10[11911E11Q11o12A12B12T12`12l13>13?13@13b14D14`15<15N15]15l16@16L16X16d17017B17N17Z17i18818D18P18Q18d18e18f18g19E1:51;41;d1<c1<o1=;1=G1=S1>1FFS1R5NEEDR2ra2sp1X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp1X1n1P5limbs2X03SPR2XB2P01A2A02N1FS2sp1X1P5limbs2nb2XB2P01AFFS2sp1X1n1P5limbs2nb2X02LL3SPR2XB2P02K11A2A0S2sp1X1n1P5limbs2nb2X02LL3SPR2XB2P02K11A2A0S1R3HIA1h2ra2sp1X5limbs3TOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01X5limbs3TOP2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp1X1P5limbs2XB2P01AS2sp1X1P5limbs2XB2P01AS1R5NEEDR2sp1X1P5limbs2lo3LOS3SLO2X03SPR2XB2P01A2A0FFS2sp1X5limbs2XBS2sp1X1P5limbs2XB2P01AFFS1R2sp1X1n1P5limbs2lo3LOS2LL3ALO2XB2PCFS1R5NEEDR2ra2sp1X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp1X5limbs2lo2XB3DSXS1X1n1P5limbs2nb2LL2XB2P02K11A2KP2PAS1X1n1P5limbs2nb2XB2P02K11A2XA2KPS1n2nb2NR2K02K1S1R3HIA2sp2h24TOP2S1R3HIA2sp2h24TOP2S1n5limbs2LLS2sp1X5limbs2XBS2sp1X5limbs2XB1AS2sp1X1P5limbs2XB2P01AS1R5NEEDR2sp1X1n1P5limbs2lo3LOS3SLO2X02LL3ALO3SPR2XB2P02PC1A2A0S2sp1X1P5limbs2XB2P01AS1X2sg1n1P5limbs3pad2nb2K11A2E2S2sp1X5limbs2XBFFFS2sp1X5limbs2XBFS2sp1X5limbs2XBFS1n2nb2K1S1R3HIA1h1d2h22D04HFR2SS1R3HIA1h2sp2nb3BUDFS2sp1X5limbs2XBS2sp2lo3FRCS2sp2nb3SPR2K0S2sp1n2nb3SPR2K02K1S1P2B0S2sp1X1P5limbs2lo2XB2P01AS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XB1AS2sp1X1P5limbs2lo2XB2P01AS1n2nb2K1S1n2nb2NR2K1S2sp1X5limbs2XB1AS2sp1X1P5limbs2XB2P01ASS1n1PS1nS2sp1X1n1P5limbs2XB2P01AS2sp1X1n2nb2lo2NR2K11A2XA2ASS2sp1X1n5limbs2nb2lo2LL2K11A2XA2ASFS1n5limbs2nb2LL2K1S1n2nb2K11AS1n5limbs2nb2K11AS2spS1R5NEEDR2sp2nb2lo2NB3LOS3SLO3ALO3SPR1A2A02ACS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2X02LL3SPR2XB2K11A2A02ASS1n2nb2NR2K1S1R2lo3LOS3ALO3ACPS1n1P2nb2K11A2PAFS1n1P2nb2K11A2N12PAS1n2NRS1R2sp2lo3SLO3NRM3SPRS1R2sp2lo3SLO3NRA3SPRS1R3HIA1h1d2h24HFR22h44HFR4S1R2sp2lo3SLOS1R3HIA1h2sp1d4BUDF3SPR2D0S1n2nb2K12N1S1R3HIA1h2sp2lo3TOP4HTOP2h24TOP2FFFS2nbS1AS1n2nb2lo2K11A2ASS1R3HIA1h1d2D0SS2sp3SPA3SPRS2sp3SPA3SPRSSS2sp1X5limbs2XBS1R1n1P2lo3LOS3ALO2PCS1R3HIA1hS1XS1R2nb2lo3LOS3ALO1A2ACS1R5NEEDR2sp2lo3LOS3SLO3ALOS2spS1R2sp1X5limbs2XBS2sp1X5limbs2XBS1R3HIA1h2nb2NBFS1R5NEEDR2sp1X5limbs2lo3SLO2X03SPR2XBFS2sp1X5limbs2XBS2LB4C24HS2sp1X5limbs2XBS1n5limbs2LL1AFS2sp1X5limbs2XBS1R2sp1n1P5limbs2lo3LOS2LL3ALO2PCS2sp1X5limbs2X02XBS2sp1X5limbs2X02XBS2sp1X1P5limbs2X02XB2P01AS2sp1X1P5limbs2XB2P01AS1R3HIA1h2sp2nb2h23BUD3SPR3HV2S1PS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1X5limbs2XBS2sp1n2nb2NR3SPR2K02K1S1R3HIA1h2sp1d2h24BUDF3SPR4HFR2S1n2nb2K1S1R5NEEDR2sp2lo3LOS3SLOS2sp1X5limbs2XBS1R3HIA2h4FFS1R1n1P2PC3ACVS2sp1X5limbs2XBS2sp1X5limbs2X02XB1AFFS1R3HIA2h2S1XS1n5limbs2LLS1n5limbs2LL1AS1R3HIA1h2sp3TOPS2sp1X5limbs2XBS2sp1X1n5limbs2nb2lo2LL2K11A2XA2ASS2KPS1A2A02KZS1n1P2nb2K11A2N12PA2E1S1n1l2LL2EnS1P2KP2B0S1n2nb2K13HleS1n2nb2NR2K11A1HFS1R2lo3LOSS1n2NRS1n2nb1AFS1n2NRS2sp1X1n5limbs2NR2XBS2sp1X1n1P5limbs2NR2XB2P01AS2sp1X1n1P5limbs2NR2XB2P01AS1RS1n1PFFS1R3HIA1h2nb2h23HV22h43HV4S2sp2nb2NBS2sp1X5limbs2XBS1R3ACPS1R1n2nb2K11A2AC3ACVFS1XS1R3HIA1h2nb2h23HV2S2spS2nbFS1n5limbs2nb2LL2K1S2sp1X5limbs2XBS1R5NEEDR2sp2lo3SLOS2sp1X5limbs2XBS1n1P5limbs2LLS1R2sp1X1n5limbs2nb2lo3LOS3ALO2XB2K11A2AC2N13x291CS2sp1X5limbs2lo2XB3x291CS2sp1X5limbs2lo2XB3x291CFFFFFFFFFFFFFS2sp1X1n5limbs2nb2lo2XB2K11A2ASS1R2sp1X1n5limbs2nb2lo3LOS3ALO2XB2K11A2ACS1R5NEEDR2sp1X1n5limbs2nb2lo3LOS3SLO3ALO2XB3FRC2K11A2ACS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS1X1n5limbs2nb2XB2K11AS2sp1X5limbs3ALX2X02XB1AS2sp1X1P5limbs3ALX2X02XB2P01AS2sp1X5limbs2XB2HBS2sp1X5limbs2XB2HBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1R1X5limbs4IMG'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs4IMG'2XBS2ra2sp1X5limbs2lo2XB2HB5Ha_st5Hl_stS2sp2s01X5limbs2lo2XB2HB5Ha_st5Hl_st2s12s22s32s42s5FS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBFS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R1X5limbs5ALWF'2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs5ALWF'2XBFS1X5limbs2XBS1X5limbs2XBS1X5limbs2XB1AS1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS2sp1X5limbs2lo2XBFS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBFFS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2XBS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs2lo2XBS1X5limbs2X02XBS1X5limbs2X02XBS1R1X5limbs5ALWF'2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2X02XBS1X5limbs2X02XBS1X5limbs2XBS1X5limbs2XBFS1R1X5limbs4IMG'2XBFFFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s5S1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG ZF CALLOC AMC NEEDR HND DIMG C24H HNS NB XW DSP LOS SLO TOP SPA TPV XUW"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_c24 ()) "Pmo,$37.Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)P,(11.$>.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3?.$>.VR,VHIA,Vh,R?.)P,(42.$>.Vm,VLB,(3;.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(1;.$>.Vm,Vlo,(12.&40.Vsp,))P,(1<.$>.Vm,)P,(30.$>.(1>.VR,)(1?.$>.VR,VHIA,Vh,)Vm,VX,+10.)P,(4.(15.(40.$>.VR,VHIA,Vh,)(8.Vnb,))$46.)P,(4.(15.(41.$>.VR,VHIA,Vh,)(9.Vd,))$47.)(48.$>.(44.$>.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3;.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$2.LdX',$7.(<.Vnb,(3;.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(8.Vnb,)(9.Vd,)Vlo,Vm,R16.)(45.(23.(24.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(25.&40.VX,)(25.&40.Vnb,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.$49.)Vfc,(27.(?.&40.))Vm,(28.$>.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo MX ST MI OX BUD BUDF. unfold A_MPI_GROW. rt_facts h.
    rewrite grow_FR_val in BUDF. unfold grow_PHI in BUD. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
    pose proof (HND _ _ _ _ HH) as ND.
    destruct MX as [(HXS & ALX & X0 & LL & NR & HOWN) SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, ALX, X0, LL, NR, HOWN, SG.
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
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ ?cs => set (FRC := cs) in FR end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
        [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
      eapply (presA_drop_below asegs R HIA h LB LF [(X, X + 16)] lo (bv_unsigned sp) _ m m1); [exact HH| | clear; lia| exact LOS].
      eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | exact WM0].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|]. apply Forall_nil.
      - eapply munch_weaken; [| exact MU0]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
    assert (PCH1 : own = LHeap -> rw_cells asegs m1 P [CB (4 * length limbs)%nat (u32s limbs)]).
    { intros E. ddestruct (PHEAP E) as (B0 & _ & _ & HXL & _). apply u32arr_cells.
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PC ALO LOS SLO NEEDR LL; lia]. }
    assert (MA1 : mpd_at asegs m1 LB dX).
    { eapply mpd_at_rebuild; [exact HNS| unfold mpi_cells; exact HXS| exact ALX| exact X0| exact LL| unfold MPI_MAX_LIMBS; clear - NR; lia| exact SG| exact PNULL|].
      intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & HXL & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
      eapply (u32arr_of_cells asegs); [exact (PCH1 E)| reflexivity]. }
    clear MU0 WM0.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      keep_return h LB MBEDTLS_ERR_MPI_ALLOC_FAILED FRC FR LAWS KINV.
      eapply post_keep; try eassumption; try reflexivity.
      - intros y Hy; exact Hy.
      - unfold grow_PHI, AVOL_CALL. clear - NB; lia.
      - rewrite grow_FR_val. clear - D0; lia.
      - left; reflexivity.
      all: first [exact C24H | match goal with |- ?g => idtac "E1-LEFT:" g end]. }
    rewrite ?unsigned_lit in K0 by (clear - NB; lia).
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB AB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      rewrite ?unsigned_lit in K1 by (clear - NB NR; lia).
      zstep.
      keep_return h LB 0 FRC FR LAWS KINV.
      eapply post_keep; try eassumption; try reflexivity.
      - intros y Hy; exact Hy.
      - unfold grow_PHI, AVOL_CALL. clear - NB; lia.
      - rewrite grow_FR_val. clear - D0; lia.
      - right. split; [reflexivity| clear - K1; lia].
      all: first [exact C24H | match goal with |- ?g => idtac "E2-LEFT:" g end]. }
    rewrite ?unsigned_lit in K1 by (clear - NB NR; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := nb) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity.
      all: try ((intros _; first [ clear - C24H; unfold C24_GROW_c in C24H; lia | match goal with HS : forall b, In b ?L -> In b LB, HHr : HM _ _ _ _ ?L _ _ |- _ => let NDq := fresh "NDq" in let CI := fresh "CI" in pose proof (HND _ _ _ _ HHr) as NDq; apply NoDup_map_inv in NDq; pose proof (cnt24_incl _ _ NDq HS) as CI; clear - CI C24H; unfold C24_GROW_c in C24H; lia end ])).   (* [comment removed for export] *)
      all: try (eapply uw_obj_uwc; [exact XUW | clear; lia]).
      all: clear - NB K0 K1 NR LOS SLO NEEDR NRM TOP SPA SPR BUD BUDF D0; try (unfold AMAX); try (unfold AVOL_CALL in * ); try (unfold fr_charge in * ); try lia.
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
    assert (PCH2 : own = LHeap -> rw_cells asegs m2 P [CB (4 * length limbs)%nat (u32s limbs)]).
    { intros E. ddestruct (PHEAP E) as (B0 & HIN & _). eapply (presA_rw_cells asegs R); [exact HP2| exact (PCH1 E)| | cbn; clear; tauto].
      simpl_sizes. eapply client_range_block; [apply in_app_iff; left; exact HIN| clear; lia| clear - LL; lia]. }
    clear PCH1 MA1.
    presA_transport HP2.
    assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
    { eapply presA_trans; [exact HP1|].
      eapply presA_weaken; [exact HP2| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
    clear HP1 HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in OX.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    (* [comment removed for export] *)
    zstep. zstep.
    destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
    - (* [comment removed for export] *)
      pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
      assert (MA2 : mpd_at asegs m2 LB dX).
      { eapply mpd_at_rebuild; [exact HNS| unfold mpi_cells; exact HXS| exact ALX| exact X0| exact LL| unfold MPI_MAX_LIMBS; clear - NR; lia| exact SG| exact PNULL|].
        intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & HXL & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
        eapply (u32arr_of_cells asegs); [exact (PCH2 E)| reflexivity]. }
      zstep.
      keep_return h2 LB MBEDTLS_ERR_MPI_ALLOC_FAILED FRC FR LAWS KINV.
      eapply post_keep; try eassumption; try reflexivity.
      + unfold grow_PHI, AVOL_CALL in *. clear - NB HV2; lia.
      + rewrite grow_FR_val. unfold fr_charge in HFR2. clear - HFR2 D0; lia.
      + left; reflexivity.
      all: first [exact C24H | match goal with |- ?g => idtac "E3-LEFT:" g end].
    - (* [comment removed for export] *)
      replace (nb * 4) with (4 * nb) in HFRA, HAS, HH2, HNEW by (clear; lia).
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP; lia]).
      dpose HFRA as (A0 & AC & AD & HAP).
      pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * nb) :: LB) LF m2 A (4 * nb) HH2 (or_introl eq_refl)) as OA.
      assert (HINA : In (A, 4 * nb) (((A, 4 * nb) :: LB) ++ fdata LF)) by (left; reflexivity).
      assert (XA : X + 16 <= A \/ A + 4 * nb <= X).
      { destruct (fresh_apart_client R LB LF (bv_unsigned sp) X 16 A (4 * nb) HFRA); [| clear; lia| clear - K1 NR; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
        eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (AS : A + 4 * nb <= lo) by (clear - AC ALO LOS; lia).
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - A0 AC H; lia); clear - KZ A0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
        assert (EO : own = LNull) by (destruct own; [reflexivity| exfalso; destruct (PHEAP eq_refl) as [B0 _]; clear - B0 KP; lia| exfalso; exact (HNS eq_refl)]).
        destruct (PNULL EO) as [EP En]. clear PHEAP PCH2.
        assert (limbs = []) as EL by (destruct limbs; [reflexivity| exfalso; cbn in LL; clear - LL En; lia]).
        assert (CW3 : client_wrange L (((A, 4 * nb) :: LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
        { eapply client_wrange_mono; [exact CW|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply fin_walk with (hc := h2) (LBc := (A, 4 * nb) :: LB); try eassumption; try reflexivity
          | intros y Hy; exact Hy | ].
        all: try (unfold mpi_cells; exact HXS).
        all: try (subst FRC; exact FR).
        all: try (clear - A0 AC ALO LOS SLO SPR NEEDR NB; lia).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "FIN0-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        apply aevtA_done. intros mo9 [HK9 MF9].
        (* [comment removed for export] *)
        assert (HA9 : u32arr asegs m9 A (limbs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nb - n)))).
        { rewrite EL, En. cbn [app]. rewrite Z.sub_0_r.
          replace (Z.to_nat (4 * nb)) with (4 * Z.to_nat nb)%nat in HNEW by (clear - K1 NR; lia).
          eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
          eapply (rw_cells_transport asegs _ m2 m9); [exact HNEW| exact MU| exact WM|].
          cbn [disjoint_from cells_size csize Nat.add]. clear - XA AS K1 NR; lia. }
        unfold mpi_binop_postA. deexists 14.
        dexists m9, mo9, h2, ((A, 4 * nb) :: LB), (mkMPD X sg nb A (limbs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nb - n))) pad LHeap), 0.
        split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
        split.
        { eapply presA_trans; [exact HPX2|]. rewrite <- HS2.
          eapply (presA_weaken asegs R ((A, 4 * nb) :: LB) (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2) [(X, X + 16)]);
            [| intros b Hb; right; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
          eapply (presA_drop_below asegs R HIA h2 ((A, 4 * nb) :: LB) LF [(X, X + 16)] lo (bv_unsigned sp) _ m2 m9); [exact HH2| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R ((A, 4 * nb) :: LB) LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
            [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | exact MU | exact WM].
          unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|]. apply Forall_nil. }
        split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
        split; [exact HCS2|].
        split; [unfold grow_PHI, AVOL_CALL in *; clear - NB HV2; lia|].
        split; [rewrite grow_FR_val; unfold fr_charge in HFR2; clear - HFR2 D0; lia|].
        split; [exact HH9|].
        split.
        { eapply mpd_at_rebuild; [discriminate| exact HX9| exact ALX| exact X0| rewrite length_app, repeat_length; clear - LL K1 NR; lia
                                 | unfold MPI_MAX_LIMBS; clear - K0 K1 NR; lia| exact SG| intros E; discriminate E|].
          intros _. split; [clear - K1 NR; lia|]. split; [left; reflexivity|]. split; [exact A16| exact HA9]. }
        split.
        { unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
          split; [reflexivity|]. split; [discriminate|].
          split; [intros b [Hb|Hb]; [right; left; exact Hb| left; exact Hb]|].
          split; [intros b Hb _; right; exact Hb|].
          intros b []. }
        split.
        { cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. cbn [fst snd]. apply fresh_apart_keep. exact HFRA. }
        unfold grow_R. cbn [md_sg md_n md_pad md_limbs mpd_blk md_own md_p]. split.
        { left. split; [reflexivity|]. split; [reflexivity|]. split; [clear - K1; lia|]. split; [reflexivity|]. split; [reflexivity|].
          intros Hle. exfalso. clear - Hle K1. lia. }
        intros b [<-|[]]. right. intros Hin. destruct (HAP A (4 * nb) ltac:(apply in_app_iff; left; exact Hin)); clear - H K1 NR; lia.
      + (* [comment removed for export] *)
        assert (EO : own = LHeap).
        { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. rewrite (proj1 (PNULL eq_refl)) in KP.
          rewrite ?unsigned_lit in KP by (clear; lia). clear - KP. lia. }
        ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1). pose proof (PCH2 EO) as PCH. clear PHEAP PCH2 PNULL.
        rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
        specialize (DXP EO). specialize (DSP ltac:(rewrite EO; discriminate)).
        pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * nb) :: LB) LF m2 P (4 * n) HH2 (or_intror HIN)) as OP.
        assert (PA : A + 4 * nb <= P \/ P + 4 * n <= A) by (apply HAP; apply in_app_iff; left; exact HIN).
        assert (HINP : In (P, 4 * n) (((A, 4 * nb) :: LB) ++ fdata LF)) by (right; apply in_app_iff; left; exact HIN).
        (* [comment removed for export] *)
        shadow_chk OX (X + 10) 2.
        zstep.
        replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
        zstep. zstep.
        (* [comment removed for export] *)
        assert (HN2 : rw_cells asegs m2 A ([CB (4 * length limbs)%nat (repeat (Z_to_bv 8 0) (4 * length limbs))]
                                            ++ [CB (Z.to_nat (4 * (nb - n))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (nb - n))))])).
        { eapply rw_cells_reshape; [exact HNEW| |].
          - cbn. rewrite !repeat_length; repeat split; reflexivity.
          - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. clear - LL K1; lia. }
        apply rw_cells_app in HN2. destruct HN2 as [HNA HNB]. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
        replace (A + Z.of_nat (4 * length limbs + 0)) with (A + n * 4) in HNB by (clear - LL; lia).
        apply (u8arr_of_rw_cells asegs) in HNA.
        pose proof (proj1 (u32arr_of_cells asegs m2 P _ _ limbs PCH eq_refl)) as PBA.
        pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + n * 4); (X, X + 16)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2'.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_GR) as SPC. unfold A_ASAN_MEMCPY_GR in SPC.
        acallxA_sp (bv_unsigned sp + -64)
          (eapply SPC with (h := h2) (LB := (A, 4 * nb) :: LB) (LF := LF) (DST := A) (SRC := P) (n := n * 4) (lo := lo)
                            (ds := repeat (Z_to_bv 8 0) (4 * length limbs)) (ss := u32s limbs);
           rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
           try eassumption; try reflexivity;
           first [ left; rewrite AMC; reflexivity
                 | rewrite repeat_length; clear - LL; lia
                 | rewrite u32s_length; clear - LL; lia
                 | eapply aobj_sub; [exact OA| clear; lia| clear - K1 LL; lia]
                 | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
                 | right; clear - PA K1 N1; lia
                 | left; clear - AS PC ALO LOS K1 N1; lia                                            (* [comment removed for export] *)
                 | right; pose proof (alloc_ceiling_val R) as ACV; clear - AC PC K1 N1 ACV; lia          (* [comment removed for export] *)
                 | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP; lia]
                 | eapply client_wrange_block; [exact HINA| clear; lia| clear - K1; lia]
                 | clear - NR K0 K1 LOS SLO NEEDR NRA TOP2 SPA SPR; lia
                 | first [exact C24H | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end] ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 A (u32s limbs) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
        zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
        zstep.
        replace (4 * length limbs)%nat with (Z.to_nat (n * 4)) in PCH by (clear - LL; lia).
        assert (CW4 : client_wrange L (((A, 4 * nb) :: lb_remove P LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
        { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
          destruct Hb as [Hb|Hb]; [left; right; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb] | right; exact Hb]. }
        assert (HINA4 : In (A, 4 * nb) (((A, 4 * nb) :: lb_remove P LB) ++ fdata LF)) by (left; reflexivity).
        pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
        eapply aevtA_call.
        { intros mo3 [HK3 MF3].
          eapply SPZ with (h := h2) (LB := (A, 4 * nb) :: LB) (LF := LF) (buf := P) (len := n * 4) (lo := lo) (d := d) (junk := u32s limbs);
            rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity.
          all: try (right; split; [right; replace (n * 4) with (4 * n) by (clear; lia); exact HIN | exact PCH]).
          all: try (eapply uw_obj_uwc; [exact XUW | clear; lia]).
          all: clear - NB K0 K1 NR LOS SLO NEEDR TOP2 SPA SPR BUD BUDF HV2 HFR2 D0; try (unfold AVOL_CALL in * ); try (unfold fr_charge in * ); try lia.
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
        rewrite (lb_remove_cons_other A (4 * nb) P LB) in HP4, HH4 by (clear - PA K1 N1; lia).
        (* [comment removed for export] *)
        assert (HP4' : presA asegs R ((A, 4 * nb) :: lb_remove P LB) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA h2) [] m3 m4).
        { eapply (presA_drop_freed asegs R HIA h2 ((A, 4 * nb) :: LB) LF _ [] P (4 * n) m3 m3 m4);
            [exact HH3| right; exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
            | replace (P + 4 * n) with (P + n * 4) by (clear; lia); exact HP4].
          intros b xb [Hb|Hb] Hr.
          - subst b. split; [left; reflexivity|]. intros E. injection E as E1 E2. clear - E1 PA K1 N1. lia.
          - split; [right; eapply In_lb_remove; exact Hb|]. intros E. subst b. exact (lb_remove_notin LB P (4 * n) ND Hb). }
        clear HP4 PCH PBA OP HINP HINA.
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        presA_transport HP4'.
        apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
        pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OX) as OX4.
        assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
        (* [comment removed for export] *)
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply fin_walk with (hc := h4) (LBc := (A, 4 * nb) :: lb_remove P LB); try eassumption; try reflexivity
          | intros y Hy; exact Hy | ].
        all: try (rewrite HT4; exact HT2).
        all: try (unfold mpi_cells; exact HXS).
        all: try (subst FRC; exact FR).
        all: try (clear - A0 AC ALO LOS SLO SPR NEEDR NB; lia).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "FIN1-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        apply aevtA_done. intros mo9 [HK9 MF9].
        (* [comment removed for export] *)
        assert (HA9 : u32arr asegs m9 A (limbs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nb - n)))).
        { apply u32arr_app. split.
          - eapply (u32arr_of_cells asegs); [| reflexivity].
            eapply (rw_cells_transport asegs _ m4 m9); [exact HPA| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - XA AS K1 NR LL; lia].
          - replace (A + 4 * Z.of_nat (length limbs)) with (A + n * 4) by (clear - LL; lia).
            replace (Z.to_nat (4 * (nb - n))) with (4 * Z.to_nat (nb - n))%nat in HNB by (clear - K1 NR; lia).
            eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
            eapply (rw_cells_transport asegs _ m4 m9); [exact HNB| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - XA AS K1 NR LL; lia]. }
        unfold mpi_binop_postA. deexists 14.
        dexists m9, mo9, h4, ((A, 4 * nb) :: lb_remove P LB), (mkMPD X sg nb A (limbs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nb - n))) pad LHeap), 0.
        split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
        split.
        { (* [comment removed for export] *)
          eapply presA_trans; [exact HPX2|]. eapply presA_trans; [| eapply presA_trans].
          - (* [comment removed for export] *)
            eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                      (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
              [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
            eapply (presA_drop_fresh asegs R HIA h LB LF [(X, X + 16)] A (n * 4) m2 m3 (bv_unsigned sp));
              [| eapply fresh_apart_sub; [exact HFRA| clear - K1 N1; lia] | clear - ALO LOS SLO NEEDR; lia].
            eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m2 m3); [exact HH| | clear; lia| exact LOS].
            eapply (presA_of_munch asegs R LB LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK); [| | exact MU2 | exact WM2'].
            + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
              apply Forall_cons; [cbn [fst snd]; replace (A + n * 4 - A) with (n * 4) by lia; eapply aobj_crange; eapply aobj_sub; [exact OA| clear; lia| clear - K1; lia]|].
              apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|]. apply Forall_nil.
            + intros c0 Hc. eapply cshd_hcs; [exact HH3| | rewrite HS2; eapply cshd_mono_lb; [exact Hc| intros b Hb; right; exact Hb]]. clear; lia.
          - (* [comment removed for export] *)
            eapply presA_weaken; [exact HP4'| | intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia| intros y _; exact I].
            intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb].
          - (* [comment removed for export] *)
            rewrite <- HS2, <- HS4. pose proof (hcs_ok asegs R HIA h4) as CSOK4.
            eapply (presA_weaken asegs R ((A, 4 * nb) :: lb_remove P LB) (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                      (hstkhi asegs R HIA h4) (hstkhi asegs R HIA h4) [(X, X + 16)]);
              [| intros b Hb; right; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb]| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
            eapply (presA_drop_below asegs R HIA h4 ((A, 4 * nb) :: lb_remove P LB) LF [(X, X + 16)] lo (bv_unsigned sp) _ m4 m9); [exact HH4| | clear; lia| exact LOS].
            eapply (presA_of_munch asegs R ((A, 4 * nb) :: lb_remove P LB) LF _ _ _ _ m4 m9 (hcs asegs R HIA h4) CSOK4);
              [| intros c0 Hc; eapply cshd_hcs; [exact HH4| | exact Hc]; clear; lia | exact MU | exact WM].
            unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; eapply crange_mono; [exact HCS4| exact SCS]|].
            apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX4|]. apply Forall_nil. }
        split; [rewrite HT4; exact HT2|]. split; [rewrite HS4; exact HS2|]. split; [rewrite HF4; exact HF2|]. split; [exact HK9|].
        split; [intros y Hy; apply HCS4, HCS2, Hy|].
        split; [unfold grow_PHI, AVOL_CALL in *; clear - NB HV2 HV4; lia|].
        split; [rewrite grow_FR_val; unfold fr_charge in HFR2, HFR4; clear - HFR2 HFR4 D0; lia|].
        split; [exact HH9|].
        split.
        { eapply mpd_at_rebuild; [discriminate| exact HX9| exact ALX| exact X0| rewrite length_app, repeat_length; clear - LL K1 NR; lia
                                 | unfold MPI_MAX_LIMBS; clear - K0 K1 NR; lia| exact SG| intros E; discriminate E|].
          intros _. split; [clear - K1 NR; lia|]. split; [left; reflexivity|]. split; [exact A16| exact HA9]. }
        split.
        { unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
          split; [reflexivity|]. split; [discriminate|].
          split; [intros b [Hb|Hb]; [right; left; exact Hb| left; eapply In_lb_remove; exact Hb]|].
          split. { intros [B k] Hb Hn. right. apply In_lb_remove_keep; [exact Hb|].
                   apply (nodup_fst_neq LB P (4 * n) B k ND HIN Hb). intros E. apply Hn. left. symmetry. exact E. }
          intros b [<-|[]] [E|Hin]; [injection E as E1 E2; clear - E2 K1; lia| exfalso; exact (lb_remove_notin LB P (4 * n) ND Hin)]. }
        split.
        { cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. cbn [fst snd]. apply fresh_apart_keep. exact HFRA. }
        unfold grow_R. cbn [md_sg md_n md_pad md_limbs mpd_blk md_own md_p]. rewrite EO. split.
        { left. split; [reflexivity|]. split; [reflexivity|]. split; [clear - K1; lia|]. split; [reflexivity|]. split; [reflexivity|].
          intros Hle. exfalso. clear - Hle K1. lia. }
        intros b [<-|[]]. right. intros Hin. destruct (HAP A (4 * nb) ltac:(apply in_app_iff; left; exact Hin)); clear - H K1 NR; lia.
    all: first [exact C24H | match goal with |- ?g => idtac "MAIN-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_mpi_grow_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_c24 ()) "PR,$4:.PHIA,(4;.$>.R1.)P,(4<.(1>.R2.))P,(4=.$>.R3.R2.$4>.)P,(22.$2.(4?.R4.)$50.)P,(22.$2.(51.R5.)$52.)P,(4.=(53.R6.))P,Ph,(=.$>.R7.R6.)PLB,(:.$;.)PLF,(:.$;.)Pm,P,(?.&40.)(10.(?.&8.))P,(11.$>.R;.R:.R4.R3.R2.R1.)(54.$2.(55.(32.$2.$2.)$2.(56.$2.$2.)R4.))P,(3.(4.(57.(2=.R8.))(58.(2=.R8.)))(4.(59.(2=.R8.))(5:.(2=.R8.))))(5;.$>.R9.R8.$49.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMC NEEDR HND DIMG. unfold mpi_grow_stmtA_c, mpi_xop_stmtA_c.
  intros until d. intros HH HK MX HNS NBv XW DSP ST LOS SLO TOP SPA TPV MI RA2 OXA BUD UW XUW BUDF C24H -> ->.
  destruct dX as [X sg n P limbs pad own].
  eapply main_walk; try eassumption. exact (proj1 OXA).
Qed.

(* [comment removed for export] *)
Lemma A_mpi_grow_spec_closed_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_c24 ()) "PR,$4:.PHIA,(4;.$>.R1.)P,(4<.(1>.R2.))P,(22.$2.(5<.R3.)$5=.)P,(22.$2.(5>.R4.)$5?.)P,(22.$2.(4?.R5.)$50.)P,(22.$2.(51.R6.)$52.)P,Pm,P,(?.&40.)(10.(?.&8.))P,(60.R8.R1.)(61.R2.)P,(4.=(62.R8.))P,(4.=(63.R9.))P,(4.=(53.R:.))P,Ph,(=.$>.R;.R:.)PLB,(:.$;.)PLF,(:.$;.)Pm,P,(?.&40.)(10.(?.&8.))P,(11.$>.R?.R>.R4.R3.R2.R1.)(54.$2.(55.(32.$2.$2.)$2.(56.$2.$2.)R4.))P,(3.(4.(57.(2=.R<.))(58.(2=.R<.)))(4.(59.(2=.R<.))(5:.(2=.R<.))))(5;.$>.R=.R<.$49.)")
(* [comment removed for export] *).
Proof.
  intros. eapply A_mpi_grow_spec_c; eauto. eapply A_zeroize_and_free_spec; eauto.
Qed.

