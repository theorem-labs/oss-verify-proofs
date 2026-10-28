(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_mpi_resize_clear.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
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
Ltac2 gd_tbl_A_mpi_resize_clear () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_xop_stmtA"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "resize_clear_FR"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_resize_clear.resize_clear_R"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_RESIZE_CLEAR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"].


Definition A_WRAP_CALLOC_RC : Z := 0x69484.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMSET_RC : Z := 0x68258.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition resize_clear_FR (d : Z) : Z := calls_FR 2 d.
Lemma resize_clear_FR_val : forall d, resize_clear_FR d = 2 * (d + 3).
Proof. intros. unfold resize_clear_FR, calls_FR, fr_charge. lia. Qed.

Definition mpi_resize_clear_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "(0.O4.O3.O2.O1.+60.Lnl,$1.(2.(3.=R1.)(4.R1.(5.+2.+40.)))L,$6.Lnl,$1.(7.R1.)$8.LLB,(9.$:.)LdX,$6.Lnl,$1.Lr,$1.LdX',$6.(;.R3.R4.R5.R2.R1.))")
(* [comment removed for export] *).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09d20c]).
Local Ltac zchk_new ::= constr:([0x09cff4; 0x09cff8; 0x09d010; 0x09d014; 0x09d01c; 0x09d028; 0x09d030; 0x09d034; 0x09d038; 0x09d03c; 0x09d048; 0x09d080; 0x09d084; 0x09d188; 0x09d18c; 0x09d190; 0x09d1cc; 0x09d1d0; 0x09d1d4; 0x09d200; 0x09d230; 0x09d248]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Hypothesis C24T : c24_transition.   (* [comment removed for export] *)
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
  #[using="IMG NEEDR LOS SLO"] Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Phc,(<.$=.VR,VHIA,)PLBc,(9.$:.)Pmm,P,(>.&40.)(?.(>.&8.))Pr,$1.Pxra,(>.&40.)Pxs0,(>.&40.)Pxs1,(>.&40.)Pxs2,(>.&40.)Pxs3,(>.&40.)Pxs4,(>.&40.)Pxs5,(>.&40.)Pxs6,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,R1:.R19.VLF,R18.)P,(3.(11.&40.Vsp,)(12.$=.VR,VHIA,R1;.))P,(13.$=.R1:.(14.(11.&40.Vsp,)-40.)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))P,(1:.$=.R1;.Vlo,(14.(11.&40.Vsp,)-40.))P,(1;.$=.R1<.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,R1?.)Lms',$1?.(20.(>.&40.)Lx5,(>.&40.)(20.(>.&40.)Lx6,(>.&40.)(20.(>.&40.)Lx7,(>.&40.)(20.(>.&40.)La1',(>.&40.)(20.(>.&40.)La2',(>.&40.)(20.(>.&40.)La3',(>.&40.)(20.(>.&40.)La4',(>.&40.)(20.(>.&40.)La5',(>.&40.)(20.(>.&40.)La6',(>.&40.)(20.(>.&40.)La7',(>.&40.)(20.(>.&40.)Lx28,(>.&40.)(20.(>.&40.)Lx29,(>.&40.)(20.(>.&40.)Lx30,(>.&40.)(20.(>.&40.)Lx31,(>.&40.)(2.(21.$1?.R?.(22.(23.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(24.&40.R2;.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(25.Vra,)Vfc,(26.(>.&40.))R2<.(27.$=.)))(1:.$=.R2<.Vlo,(11.&40.Vsp,)))))))))))))))))(22.(23.R1;.(24.&40.(14.(11.&40.Vsp,)-40.))Vgp,Vtp,R13.R12.R11.R1:.R19.(24.&40.R1<.)R10.R?.R>.R=.R<.R;.R:.R18.R17.R16.R15.R14.Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(24.&40.+9=1>4.)Vfc,(26.(>.&40.))R1=.(27.$=.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc FR ST MI. basic_facts hc LBc mm HH TOPc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma finA_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Phc,(<.$=.VR,VHIA,)PLBc,(9.$:.)Pmm,P,(>.&40.)(?.(>.&8.))Ppw,$1.Psw,(>.&40.)Pnw,$1.Pxra,(>.&40.)Pxs2,(>.&40.)Pxs3,(>.&40.)Pxs4,(>.&40.)Pxs5,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,R1:.R19.VLF,R18.)P,(21.$1.(12.$=.VR,VHIA,R1;.)(12.$=.VR,VHIA,Vh,))P,(3.(11.&40.Vsp,)(12.$=.VR,VHIA,R1<.))P,(21.$1.(28.VX,+8.)=)P,(29.(3.(14.VX,+10.)Vlo,)(3.(11.&40.Vsp,)VX,))P,(13.$=.R1=.VX,(2:.R1<.R1;.R1:.Vpad,))P,(2;.(2<.VR,)(2=.$:.R1?.(2>.VLF,))(11.&40.Vsp,)(12.$=.VR,VHIA,Vh,)VX,+10.)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,R21.)R1?.VX,+10.)P,(13.$=.R20.(14.(11.&40.Vsp,)-40.)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))P,(1:.$=.R21.Vlo,(14.(11.&40.Vsp,)-40.))P,(1;.$=.R22.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,R25.)Lms',$1?.(20.(>.&40.)Lx5,(>.&40.)(20.(>.&40.)Lx6,(>.&40.)(20.(>.&40.)Lx7,(>.&40.)(20.(>.&40.)La1',(>.&40.)(20.(>.&40.)La2',(>.&40.)(20.(>.&40.)La3',(>.&40.)(20.(>.&40.)La4',(>.&40.)(20.(>.&40.)La5',(>.&40.)(20.(>.&40.)La6',(>.&40.)(20.(>.&40.)La7',(>.&40.)(20.(>.&40.)Lx28,(>.&40.)(20.(>.&40.)Lx29,(>.&40.)(20.(>.&40.)Lx30,(>.&40.)(20.(>.&40.)Lx31,(>.&40.)(20.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(2.(21.$1?.R10.(22.(23.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(24.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(25.Vra,)Vfc,(26.(>.&40.))R1.(27.$=.)))(2.(30.(15.(31.$1.$1.)(32.$1.$1.Vlo,(11.&40.Vsp,))(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.))))R33.R1.)(2.(33.$=.R33.R1.)(2.(1;.$=.R1.)(2.(13.$=.R1.VX,(2:.=(24.&40.+1.)=Vpad,))(2.(1:.$=.R1.Vlo,(11.&40.Vsp,))(10.$=.VR,VHIA,R35.R34.VLF,R1.))))))))))))))))))))))(22.(23.R1?.(24.&40.(14.(11.&40.Vsp,)-40.))Vgp,Vtp,R1:.R19.R18.(24.&40.VX,)(24.&40.(14.(34.VX,+3.)(35.(1=.VR,))))R17.R16.R15.R14.R13.R12.R11.R10.R1>.R1=.R1<.R1;.(24.&40.(35.(1=.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(24.&40.+9=0<0.)Vfc,(26.(>.&40.))R23.(27.$=.)))")
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
    all: match goal with |- ?g => idtac "FINA-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG AMS NEEDR LOS SLO TOP"] Lemma finB_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Pmm,P,(>.&40.)(?.(>.&8.))Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,Vh,VLB,VLF,R?.)P,(21.$1.(28.VX,+8.)=)P,(29.(3.(14.VX,+10.)Vlo,)(3.(11.&40.Vsp,)VX,))P,(2.(3.+1.Vn,)(3.Vn,$36.))P,(37.(31.$1.$1.)(32.$1.$1.VP,(38.+4.Vn,))VLB,)P,(3.(14.VP,(38.+4.Vn,))(39.(2<.VR,)))P,(29.(3.(14.VX,+10.)VP,)(3.(14.VP,(38.+4.Vn,))VX,))P,(13.$=.R16.VX,(2:.VP,(24.&40.Vsg,)Vn,Vpad,))P,(3:.$=.R17.VP,Vlimbs,)P,(21.$1.(3;.(3<.(>.&40.)Vlimbs,))Vn,)P,(2;.(2<.VR,)(2=.$:.VLB,(2>.VLF,))(11.&40.Vsp,)(12.$=.VR,VHIA,Vh,)VX,+10.)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,Vh,)R1:.VX,+10.)P,(13.$=.R1;.(14.(11.&40.Vsp,)-40.)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))P,(1:.$=.R1<.Vlo,(14.(11.&40.Vsp,)-40.))P,(1;.$=.R1=.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,Vh,)Lms',$1?.(20.(>.&40.)Lx5,(>.&40.)(20.(>.&40.)Lx6,(>.&40.)(20.(>.&40.)Lx7,(>.&40.)(20.(>.&40.)La1',(>.&40.)(20.(>.&40.)La2',(>.&40.)(20.(>.&40.)La3',(>.&40.)(20.(>.&40.)La4',(>.&40.)(20.(>.&40.)La5',(>.&40.)(20.(>.&40.)La6',(>.&40.)(20.(>.&40.)La7',(>.&40.)(20.(>.&40.)Lx28,(>.&40.)(20.(>.&40.)Lx29,(>.&40.)(20.(>.&40.)Lx30,(>.&40.)(20.(>.&40.)Lx31,(>.&40.)(20.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(2.(21.$1?.R10.(22.(23.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(24.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(25.Vra,)Vfc,(26.(>.&40.))R1.(27.$=.)))(2.(30.(15.(31.$1.$1.)(32.$1.$1.Vlo,(11.&40.Vsp,))(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(15.(31.$1.$1.)(32.$1.$1.VP,(14.VP,(38.+4.Vn,)))(19.(31.$1.$1.)))))R2>.R1.)(2.(33.$=.R2>.R1.)(2.(1;.$=.R1.)(2.(13.$=.R1.VX,(2:.VP,(24.&40.+1.)Vn,Vpad,))(2.(3:.$=.R1.VP,(3=.(>.&40.)(24.&40.=)(3>.Vn,)))(2.(1:.$=.R1.Vlo,(11.&40.Vsp,))(10.$=.VR,VHIA,Vh,VLB,VLF,R1.)))))))))))))))))))))))(22.(23.R1=.(24.&40.(14.(11.&40.Vsp,)-40.))Vgp,Vtp,R1<.R1;.R1:.(24.&40.VX,)(24.&40.Vn,)(24.&40.VP,)(24.&40.Vn,)R19.R18.R17.R16.R15.R14.(24.&40.(14.VX,+:.))(24.&40.(14.VX,+8.))(24.&40.(14.(34.(14.VX,+:.)+3.)(35.(1=.VR,))))(24.&40.(14.(34.VX,+3.)(35.(1=.VR,))))(24.&40.(35.(1=.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(24.&40.+9=050.)Vfc,(26.(>.&40.))R1>.(27.$=.)))")
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
             | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
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
    all: match goal with |- ?g => idtac "FINB-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma mid_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Phc,(<.$=.VR,VHIA,)PLBc,(9.$:.)Pmm,P,(>.&40.)(?.(>.&8.))Ppw,$1.Psw,(>.&40.)Pnw,$1.Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,R16.R15.VLF,R14.)P,(21.$1.(12.$=.VR,VHIA,R17.)(12.$=.VR,VHIA,Vh,))P,(3.(11.&40.Vsp,)(12.$=.VR,VHIA,R18.))P,(21.$1.(28.VX,+8.)=)P,(29.(3.(14.VX,+10.)Vlo,)(3.(11.&40.Vsp,)VX,))P,(13.$=.R19.VX,(2:.R18.R17.R16.Vpad,))P,(2;.(2<.VR,)(2=.$:.R1;.(2>.VLF,))(11.&40.Vsp,)(12.$=.VR,VHIA,Vh,)VX,+10.)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,R1=.)R1;.VX,+10.)P,(13.$=.R1<.(14.(11.&40.Vsp,)-40.)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))P,(1:.$=.R1=.Vlo,(14.(11.&40.Vsp,)-40.))P,(1;.$=.R1>.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,R21.)Lms',$1?.(20.(>.&40.)La0',(>.&40.)(20.(>.&40.)La1',(>.&40.)(20.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(2.(21.$1?.R4.(22.(23.R1?.(24.&40.(14.(11.&40.Vsp,)-40.))Vgp,Vtp,R1>.R1=.R1<.(24.&40.VX,)(24.&40.Vnl,)R3.R2.R19.R18.R17.R16.R15.R14.(24.&40.(14.VX,+:.))(24.&40.(14.VX,+8.))(24.&40.(14.(34.(14.VX,+:.)+3.)(35.(1=.VR,))))(24.&40.(14.(34.VX,+3.)(35.(1=.VR,))))(24.&40.(35.(1=.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(24.&40.+9=140.)Vfc,(26.(>.&40.))R1.(27.$=.)))(2.(30.(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))R23.R1.)(2.(33.$=.R23.R1.)(2.(1;.$=.R1.)(2.(13.$=.R1.VX,(2:.=(24.&40.+1.)=Vpad,))(2.(13.$=.R1.(14.(11.&40.Vsp,)-40.)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))(2.(1:.$=.R1.Vlo,(14.(11.&40.Vsp,)-40.))(10.$=.VR,VHIA,R25.R24.VLF,R1.)))))))))))(22.(23.R1;.(24.&40.(14.(11.&40.Vsp,)-40.))Vgp,Vtp,R1:.R19.R18.(24.&40.VX,)(24.&40.Vnl,)R17.R16.R15.R14.R13.R12.R11.R10.(24.&40.(14.VX,+:.))(24.&40.(14.VX,+8.))(24.&40.(14.(34.(14.VX,+:.)+3.)(35.(1=.VR,))))(24.&40.(14.(34.VX,+3.)(35.(1=.VR,))))(24.&40.(35.(1=.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(24.&40.+9=110.)Vfc,(26.(>.&40.))R1?.(27.$=.)))")
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
    all: match goal with |- ?g => idtac "MID-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma finC_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Phc,(<.$=.VR,VHIA,)PLBc,(9.$:.)Pmm,P,(>.&40.)(?.(>.&8.))Ppw,$1.Psw,(>.&40.)Pnw,$1.Ppn,$1.Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,R17.R16.VLF,R15.)P,(21.$1.(12.$=.VR,VHIA,R18.)(12.$=.VR,VHIA,Vh,))P,(3.(11.&40.Vsp,)(12.$=.VR,VHIA,R19.))P,(21.$1.(28.VX,+8.)=)P,(29.(3.(14.VX,+10.)Vlo,)(3.(11.&40.Vsp,)VX,))P,(2.(3.=R16.)(4.R16.(5.+2.+40.)))P,(13.$=.R1;.VX,(2:.R1:.R19.R18.Vpad,))P,(2;.(2<.VR,)(2=.$:.R1=.(2>.VLF,))(11.&40.Vsp,)(12.$=.VR,VHIA,Vh,)VX,+10.)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,R1?.)R1=.VX,+10.)P,(13.$=.R1>.(14.(11.&40.Vsp,)-40.)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))P,(1:.$=.R1?.Vlo,(14.(11.&40.Vsp,)-40.))P,(1;.$=.R20.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,R23.)Lms',$1?.(20.(>.&40.)Lx5,(>.&40.)(20.(>.&40.)Lx6,(>.&40.)(20.(>.&40.)Lx7,(>.&40.)(20.(>.&40.)La1',(>.&40.)(20.(>.&40.)La2',(>.&40.)(20.(>.&40.)La3',(>.&40.)(20.(>.&40.)La4',(>.&40.)(20.(>.&40.)La5',(>.&40.)(20.(>.&40.)La6',(>.&40.)(20.(>.&40.)La7',(>.&40.)(20.(>.&40.)Lx28,(>.&40.)(20.(>.&40.)Lx29,(>.&40.)(20.(>.&40.)Lx30,(>.&40.)(20.(>.&40.)Lx31,(>.&40.)(20.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(2.(21.$1?.R10.(22.(23.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(24.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(25.Vra,)Vfc,(26.(>.&40.))R1.(27.$=.)))(2.(30.(15.(31.$1.$1.)(32.$1.$1.Vlo,(11.&40.Vsp,))(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.))))R31.R1.)(2.(33.$=.R31.R1.)(2.(1;.$=.R1.)(2.(13.$=.R1.VX,(2:.R2=.R2?.Vnl,Vpad,))(2.(1:.$=.R1.Vlo,(11.&40.Vsp,))(10.$=.VR,VHIA,R33.R32.VLF,R1.))))))))))))))))))))))(22.(23.R1<.(24.&40.(14.(11.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.(24.&40.VX,)(24.&40.Vnl,)R18.R17.R16.R15.R14.R13.R12.R11.(24.&40.(14.VX,+:.))(24.&40.R1=.)(24.&40.(14.(34.(14.VX,+:.)+3.)(35.(1=.VR,))))(24.&40.(14.(34.VX,+3.)(35.(1=.VR,))))(24.&40.(35.(1=.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(24.&40.+9=1<4.)Vfc,(26.(>.&40.))R21.(27.$=.)))")
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
    all: match goal with |- ?g => idtac "FINC-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma post_empty : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "PLBr,(9.$:.)Pmo,$3?.Pmo',$3?.Ph',(<.$=.VR,VHIA,)Pm',P,(>.&40.)(?.(>.&8.))Pr,$1.Px5,(>.&40.)Px6,(>.&40.)Px7,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Px28,(>.&40.)Px29,(>.&40.)Px30,(>.&40.)Px31,(>.&40.)P,(1;.$=.R10.)P,(1:.$=.R11.Vlo,(11.&40.Vsp,))P,(40.R15.R14.)P,(41.$=.VR,(42.VLB,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(11.&40.Vsp,)(44.VR,)(45.$=.VR,VHIA,Vh,)(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))Vm,R13.)P,(21.$1.(12.$=.VR,VHIA,R15.)(12.$=.VR,VHIA,Vh,))P,(21.$1.(45.$=.VR,VHIA,R16.)(45.$=.VR,VHIA,Vh,))P,(21.$1.(46.$=.VR,VHIA,R17.)(46.$=.VR,VHIA,Vh,))P,(47.$=.VR,VHIA,R18.R19.)P,Px,$1.P,(1>.$=.VR,VHIA,Vh,R1.)(1>.$=.VR,VHIA,R1;.R2.)P,(3.(48.$=.VR,VHIA,R1:.)(14.(48.$=.VR,VHIA,Vh,)(7.Vnl,)))P,(3.(49.$=.VR,VHIA,R1;.)(14.(49.$=.VR,VHIA,Vh,)(8.Vd,)))P,(10.$=.VR,VHIA,R1<.R1?.VLF,R1;.)P,(13.$=.R1<.VX,(2:.=(24.&40.+1.)=Vpad,))P,(21.$1.(28.VX,+8.)=)P,(4.=VX,)P,Pb,$:.P,(37.$:.R1.R24.)(37.$:.R2.VLB,)P,Pb,$:.P,(37.$:.R1.VLB,)P,(4:.(37.$:.R2.(4;.(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))))(37.$:.R3.R27.)P,Pb,$:.P,(37.$:.R1.(4;.(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(4:.(37.$:.R2.R27.))P,(29.(2.(21.$1.R21.=)(21.$1.Vnl,=))(21.$1.R21.$4<.))(4=.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$6.(;.Vnl,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(7.Vnl,)(8.Vd,)Vlo,Vm,R26.(4>.(22.(23.Vra,Vsp,Vgp,Vtp,R21.R20.R1?.Vs0,Vs1,(24.&40.R22.)R1>.R1=.R1<.R1;.R1:.R19.R18.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(25.Vra,)Vfc,(26.(>.&40.))R23.(27.$=.))R25.))")
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

  (* [comment removed for export] *)
  #[using="NL"] Lemma post_same : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Pmo,$3?.Pmo',$3?.Pm',P,(>.&40.)(?.(>.&8.))Px5,(>.&40.)Px6,(>.&40.)Px7,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Px28,(>.&40.)Px29,(>.&40.)Px30,(>.&40.)Px31,(>.&40.)P,(1;.$=.R?.)P,(1:.$=.R10.Vlo,(11.&40.Vsp,))P,(40.R13.R12.)P,(41.$=.VR,(42.VLB,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(11.&40.Vsp,)(44.VR,)(45.$=.VR,VHIA,Vh,)(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))Vm,R12.)P,(47.$=.VR,VHIA,Vh,R14.)P,(10.$=.VR,VHIA,Vh,VLB,VLF,R14.)P,(13.$=.R15.VX,(2:.VP,(24.&40.+1.)Vn,Vpad,))P,(3:.$=.R16.VP,(3=.(>.&40.)(24.&40.=)(3>.Vn,)))P,(21.$4?.Vown,$50.)P,(37.(31.$1.$1.)(32.$1.$1.VP,(38.+4.Vn,))VLB,)P,(21.$1.(28.VP,+10.)=)P,(2.(3.+1.Vn,)(3.Vn,$36.))P,(21.$1.Vn,Vnl,)P,(21.$1.(28.VX,+8.)=)P,(4.=VX,)P,(3.=Vd,)(4=.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$6.(;.Vnl,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(7.Vnl,)(8.Vd,)Vlo,Vm,R21.(4>.(22.(23.Vra,Vsp,Vgp,Vtp,R1>.R1=.R1<.Vs0,Vs1,(24.&40.=)R1;.R1:.R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(25.Vra,)Vfc,(26.(>.&40.))R1?.(27.$=.))R20.))")
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

  (* [comment removed for export] *)
  #[using="Type"] Lemma post_new : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "PLBr,(9.$:.)Pmo,$3?.Pmo',$3?.Ph',(<.$=.VR,VHIA,)Pm',P,(>.&40.)(?.(>.&8.))PA,$1.Px5,(>.&40.)Px6,(>.&40.)Px7,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Px28,(>.&40.)Px29,(>.&40.)Px30,(>.&40.)Px31,(>.&40.)P,(1;.$=.R10.)P,(1:.$=.R11.Vlo,(11.&40.Vsp,))P,(40.R15.R14.)P,(41.$=.VR,(42.VLB,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(11.&40.Vsp,)(44.VR,)(45.$=.VR,VHIA,Vh,)(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))Vm,R13.)P,(21.$1.(12.$=.VR,VHIA,R15.)(12.$=.VR,VHIA,Vh,))P,(21.$1.(45.$=.VR,VHIA,R16.)(45.$=.VR,VHIA,Vh,))P,(21.$1.(46.$=.VR,VHIA,R17.)(46.$=.VR,VHIA,Vh,))P,(47.$=.VR,VHIA,R18.R19.)P,Px,$1.P,(1>.$=.VR,VHIA,Vh,R1.)(1>.$=.VR,VHIA,R1;.R2.)P,(3.(48.$=.VR,VHIA,R1:.)(14.(48.$=.VR,VHIA,Vh,)(7.Vnl,)))P,(3.(49.$=.VR,VHIA,R1;.)(14.(49.$=.VR,VHIA,Vh,)(8.Vd,)))P,(10.$=.VR,VHIA,R1<.(15.(31.$1.$1.)(32.$1.$1.R1:.(38.+4.Vnl,))R1?.)VLF,R1;.)P,(13.$=.R1<.VX,(2:.R1;.(24.&40.+1.)Vnl,Vpad,))P,(3:.$=.R1=.R1<.(3=.(>.&40.)(24.&40.=)(3>.Vnl,)))P,(21.$1.(28.R1=.+10.)=)P,(51.VR,R23.VLF,R1>.(38.+4.Vnl,))P,(2.(3.+1.Vnl,)(3.Vnl,$36.))P,(21.$1.(28.VX,+8.)=)P,(4.=VX,)P,Pb,$:.P,(37.$:.R1.R28.)(37.$:.R2.VLB,)P,Pb,$:.P,(37.$:.R1.VLB,)P,(4:.(37.$:.R2.(4;.(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))))(37.$:.R3.R2;.)P,Pb,$:.P,(37.$:.R1.(4;.(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(4:.(37.$:.R2.(15.(31.$1.$1.)(32.$1.$1.R26.(38.+4.Vnl,))R2;.)))P,Pb,$:.P,(37.$:.R1.(42.VLB,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(37.$:.R2.R2<.)P,(4:.(37.(31.$1.$1.)(32.$1.$1.R26.(38.+4.Vnl,))VLB,))(4=.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$6.(;.Vnl,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(7.Vnl,)(8.Vd,)Vlo,Vm,R2;.(4>.(22.(23.Vra,Vsp,Vgp,Vtp,R26.R25.R24.Vs0,Vs1,(24.&40.=)R23.R22.R21.R20.R1?.R1>.R1=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(25.Vra,)Vfc,(26.(>.&40.))R28.(27.$=.))R2:.))")
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
          | match goal with |- ?g => idtac "POST-SIDE-LEFT:" g end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="C24T IMG CALLOC NEEDR HND NL LOS SLO TOP SPA TPV XUW"] Lemma grow_part : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Phc,(<.$=.VR,VHIA,)PLBr,(9.$:.)Pmo,$3?.Pmm,P,(>.&40.)(?.(>.&8.))Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,R14.R13.VLF,R11.)P,(21.$1.(12.$=.VR,VHIA,R15.)(12.$=.VR,VHIA,Vh,))P,(21.$1.(45.$=.VR,VHIA,R16.)(45.$=.VR,VHIA,Vh,))P,(21.$1.(46.$=.VR,VHIA,R17.)(46.$=.VR,VHIA,Vh,))P,Px,$1.P,(1>.$=.VR,VHIA,Vh,R1.)(1>.$=.VR,VHIA,R1:.R2.)P,(3.(48.$=.VR,VHIA,R19.)(14.(48.$=.VR,VHIA,Vh,)$52.))P,(3.(49.$=.VR,VHIA,R1:.)(14.(49.$=.VR,VHIA,Vh,)(53.Vd,)))P,(41.$=.VR,(42.VLB,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(11.&40.Vsp,)(44.VR,)(45.$=.VR,VHIA,Vh,)(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))Vm,R18.)P,Pb,$:.P,(37.$:.R1.R1<.)(37.$:.R2.VLB,)P,Pb,$:.P,(37.$:.R1.VLB,)P,(4:.(37.$:.R2.(4;.(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))))(37.$:.R3.R1?.)P,Pb,$:.P,(37.$:.R1.(4;.(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(4:.(37.$:.R2.R1?.))P,Pb,$:.P,(37.$:.R1.(42.VLB,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(37.$:.R2.R20.)P,Pb,$:.P,(37.$:.R1.(4;.(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(2.(21.$:.R2.(32.$1.$1.VP,(38.+4.Vn,)))(2.(37.(31.$1.$1.)(32.$1.$1.VP,(38.+4.Vn,))VLB,)(3.+1.Vn,)))P,(4:.(21.$1.Vn,Vnl,))P,(13.$=.R1?.VX,(2:.=(24.&40.+1.)=Vpad,))P,(21.$1.(28.VX,+8.)=)P,(4.=VX,)P,(29.(3.(14.VX,+10.)Vlo,)(3.(11.&40.Vsp,)VX,))P,(2;.(2<.VR,)(2=.$:.R25.(2>.VLF,))(11.&40.Vsp,)(12.$=.VR,VHIA,Vh,)VX,+10.)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,R27.)R24.VX,+10.)P,(13.$=.R25.(14.(11.&40.Vsp,)-40.)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))P,(1:.$=.R26.Vlo,(14.(11.&40.Vsp,)-40.))P,(1;.$=.R27.)P,(3.+1.Vnl,)P,(3.(14.(48.$=.VR,VHIA,Vh,)(7.Vnl,))$54.)P,(3.(14.(49.$=.VR,VHIA,Vh,)(8.Vd,))$55.)(56.$=.(57.$=.VR,VHIA,R2>.R2<.)(4=.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$6.(;.Vnl,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(7.Vnl,)(8.Vd,)Vlo,Vm,R2<.)(22.(23.R2:.(24.&40.(14.(11.&40.Vsp,)-40.))Vgp,Vtp,R29.R28.R27.(24.&40.VX,)(24.&40.Vnl,)R26.R25.R24.R23.R22.R21.R20.R1?.(24.&40.(14.VX,+:.))(24.&40.(14.VX,+8.))(24.&40.(14.(34.(14.VX,+:.)+3.)(35.(1=.VR,))))(24.&40.(14.(34.VX,+3.)(35.(1=.VR,))))(24.&40.(35.(1=.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R1>.R1=.R1<.R1;.)VF,(24.&40.+9=140.)Vfc,(26.(>.&40.))R2;.(27.$=.)))")
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
      all: try (apply c24_of_transition; exact C24T).   (* [comment removed for export] *)
      all: try (eapply uw_obj_uwc; [exact XUW | clear; lia]).
      all: clear - NL K0 K2 LOS SLO NEEDR NRM TOPc SPA SPR BUD BUDF HVc HFRc D0; try (unfold AMAX); try (unfold AVOL_CALL in * ); try (unfold fr_charge in * ); try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
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
    all: match goal with |- ?g => idtac "GROW-PART-LEFT:" g end.
  Qed.

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
            | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end ]
    | clear SPZ ].

  #[using="C24T IMG ZF CALLOC AMS NEEDR HND DIMG HNS NL XW DSP LOS SLO TOP SPA TPV XUW"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Pmo,$3?.Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)P,(10.$=.VR,VHIA,Vh,VLB,VLF,Vm,)P,(47.$=.VR,VHIA,Vh,R?.)P,(58.$=.Vm,VLB,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(1:.$=.Vm,Vlo,(11.&40.Vsp,))P,(1;.$=.Vm,)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,Vh,)Vm,VX,+10.)P,(3.(14.(48.$=.VR,VHIA,Vh,)(7.Vnl,))$54.)P,(3.(14.(49.$=.VR,VHIA,Vh,)(8.Vd,))$55.)(59.$=.(4=.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$6.(;.Vnl,(43.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(7.Vnl,)(8.Vd,)Vlo,Vm,R16.)(4>.(22.(23.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(24.&40.VX,)(24.&40.Vnl,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(24.&40.$5:.)Vfc,(26.(>.&40.))Vm,(27.$=.))R16.))")
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
          all: match goal with |- ?g => idtac "GP0-PRE-LEFT:" g end.
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
          all: match goal with |- ?g => idtac "GP1-PRE-LEFT:" g end.
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
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.

End Walk.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mpi_resize_clear_coreA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Ph,(<.O4.O3.O2.)PLB,(9.$:.)PLF,(9.$:.)Pra,(>.&40.)Psp,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Pa0,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)PF,(5;.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))Pmo,$3?.PdX,$6.Pnl,$1.Plo,$1.Pd,$1.P,(10.O4.O3.O2.R2:.R29.R28.R6.)P,(47.O4.O3.O2.R2;.R6.)P,(5<.O4.R8.R2;.R6.)P,(4:.(21.$4?.(5=.R7.)$5>.))P,(2.(3.=R7.)(4.R7.(5.+2.+40.)))P,(5?.O3.R2>.R2=.(11.&40.R2;.)(12.O4.O3.O2.R2?.)R9.)P,P,(4:.(21.$4?.(5=.R:.)$60.))(29.(3.(14.(61.R;.)(38.+4.(62.R;.)))R9.)(3.(11.&40.R2=.)(61.R;.)))P,(1:.O4.R=.R9.(11.&40.R2=.))P,(3.(44.O3.)R:.)P,(3.R;.(63.(63.(11.&40.R2?.)+60.)(64.O3.)))P,(3.(11.&40.R30.)(12.O4.O3.O2.R34.))P,(21.$1.(28.(11.&40.R31.)+10.)=)P,(21.(>.&40.)R30.(24.&40.(65.O3.)))P,(1;.O4.R13.)P,(2?.O4.(1=.O3.)(1>.O4.O3.O2.R38.)R14.(66.R12.)+10.)P,(3.(14.(48.O4.O3.O2.R39.)(7.R12.))$54.)P,(67.O3.(66.R14.)+10.R11.)P,(3.(14.(49.O4.O3.O2.R3;.)(8.R12.))$55.)P,(21.(>.&40.)R30.(24.&40.(66.R16.)))P,(21.(>.&40.)R30.(24.&40.R16.))(59.O4.(4=.O4.O3.O2.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.R3>.R3=.R3<.R18.Lr,$1.LdX',$6.(;.R19.R1:.R3?.R2.R1.)(7.R17.)(8.R15.)R16.R1:.R19.)(4>.(22.(23.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R1<.(24.&40.O1.)R1;.(26.(>.&40.))R1:.(27.O4.))R19.))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Definition mpi_resize_clear_coreA_r (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_resize_clear ()) "Ph,(<.O4.O3.O2.)PLB,(9.$:.)PLF,(9.$:.)Pra,(>.&40.)Psp,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Pa0,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)PF,(5;.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))Pmo,$3?.PdX,$6.Pnl,$1.Plo,$1.Pd,$1.P,(10.O4.O3.O2.R2:.R29.R28.R6.)P,(47.O4.O3.O2.R2;.R6.)P,(58.O4.R8.R2;.R6.)P,(4:.(21.$4?.(5=.R7.)$5>.))P,(2.(3.=R7.)(4.R7.(5.+2.+40.)))P,(5?.O3.R2>.R2=.(11.&40.R2;.)(12.O4.O3.O2.R2?.)R9.)P,P,(4:.(21.$4?.(5=.R:.)$60.))(29.(3.(14.(61.R;.)(38.+4.(62.R;.)))R9.)(3.(11.&40.R2=.)(61.R;.)))P,(1:.O4.R=.R9.(11.&40.R2=.))P,(3.(44.O3.)R:.)P,(3.R;.(63.(63.(11.&40.R2?.)+60.)(64.O3.)))P,(3.(11.&40.R30.)(12.O4.O3.O2.R34.))P,(21.$1.(28.(11.&40.R31.)+10.)=)P,(21.(>.&40.)R30.(24.&40.(65.O3.)))P,(1;.O4.R13.)P,(2?.O4.(1=.O3.)(1>.O4.O3.O2.R38.)R14.(66.R12.)+10.)P,(3.(14.(48.O4.O3.O2.R39.)(7.R12.))$54.)P,(67.O3.(66.R14.)+10.R11.)P,(3.(14.(49.O4.O3.O2.R3;.)(8.R12.))$55.)P,(21.(>.&40.)R30.(24.&40.(66.R16.)))P,(21.(>.&40.)R30.(24.&40.R16.))(59.O4.(4=.O4.O3.O2.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.R3>.R3=.R3<.R18.Lr,$1.LdX',$6.(;.R19.R1:.R3?.R2.R1.)(7.R17.)(8.R15.)R16.R1:.R19.)(4>.(22.(23.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R1<.(24.&40.O1.)R1;.(26.(>.&40.))R1:.(27.O4.))R19.))")
(* [comment removed for export] *).

