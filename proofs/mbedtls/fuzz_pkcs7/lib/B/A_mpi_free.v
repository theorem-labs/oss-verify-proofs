(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
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
Ltac2 gd_tbl_A_mpi_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_free.mpi_free_LB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_free.mpi_free_X"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_at"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "mpi_free_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_MEMSET_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"].


Definition mpi_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X P n : Z) (pad : word) (own : limb_own) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O21.O20.O1?.)Lh',(5.O21.O20.O1?.)(6.(7.$0.R13.(8.(9.(:.O1;.O1:.O19.O18.R12.R11.R10.O17.O16.R?.R>.R=.R<.R;.R:.R9.R8.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R7.R6.R5.R4.)O;.(;.O1;.)O:.(<.(2.&40.))R3.(=.O21.))R2.))(6.(>.O21.R3.)(6.(?.O21.R3.O4.(10.&40.O1:.))(6.(11.O1.R2.)(6.(12.O21.O20.(13.O5.O8.O7.O1=.)O1<.(10.&40.O1:.)(14.O20.)(15.O21.O20.O1?.O1>.)(16.(17.$18.$18.)(19.$18.$18.O9.(1:.O9.+10.))(1;.O5.O8.O7.))O2.R3.)(6.(7.$18.(1<.O21.O20.O1?.R1.)(1<.O21.O20.O1?.O1>.))(6.(7.$18.(15.O21.O20.O1?.R1.)(15.O21.O20.O1?.O1>.))(6.(7.$18.(1=.O21.O20.O1?.R1.)(1=.O21.O20.O1?.O1>.))(6.(1>.O21.O20.O1?.R1.R2.)(6.Px,$18.P,(1?.O21.O20.O1?.O1>.R1.)(1?.O21.O20.O1?.R3.R2.)(6.(20.(21.O21.O20.O1?.R1.)(1:.(21.O21.O20.O1?.O1>.)$22.))(6.(20.(23.O21.O20.O1?.R1.)(1:.(23.O21.O20.O1?.O1>.)(24.O3.)))(6.(25.O21.O20.O1?.R1.(13.O5.O8.O7.O1=.)O1<.R3.)(26.O21.R3.O9.(27.=(28.&40.+1.)=O6.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_free_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_free ()) "Ph,(5.O4.O3.O2.)PLB,(29.$2:.)PLF,(29.$2:.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PX,$18.Psw,(2.&40.)Pn,$18.PP,$18.Plimbs,(29.(2.&40.))Ppad,(2.&40.)Pown,$2<.Plo,$18.Pd,$18.P,(25.O4.O3.O2.R2?.R2>.R2=.R;.)P,(1>.O4.O3.O2.R30.R;.)P,(2=.O4.R=.R30.R;.R:.R9.R8.R7.R6.R5.)P,(2>.(7.$2<.R6.$2?.))P,(30.(31.O3.)(32.$2:.(13.R7.R:.R;.R32.)(33.R31.))(10.&40.R2?.)(1<.O4.O3.O2.R33.)R=.+10.)P,P,(7.$2<.R8.$34.)(35.(20.(1:.R?.+10.)R<.)(20.(1:.R<.(36.+4.R=.))R?.))P,(?.O4.R11.R8.(10.&40.R31.))P,(20.(14.O3.)R9.)P,(20.R:.(37.(37.(10.&40.R33.)+40.)(38.O3.)))P,(20.(10.&40.R34.)(1<.O4.O3.O2.R38.))P,(7.$18.(39.(10.&40.R35.)+10.)=)P,(7.(2.&40.)R34.(28.&40.(3:.O3.)))P,(>.O4.R17.)P,(3;.O4.(3<.O3.)(1?.O4.O3.O2.R3<.)R18.R16.+10.)P,(20.(1:.(21.O4.O3.O2.R3=.)$22.)$3=.)P,(3>.O3.R18.+10.R10.)P,(20.(1:.(23.O4.O3.O2.R3?.)(24.R11.))$3?.)P,(7.(2.&40.)R34.(28.&40.R1:.))(40.O4.(41.O4.O3.O2.R41.R40.R3?.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1;.R18.R19.R16.R15.R14.R13.R1=.R1<.)(8.(9.(:.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(28.&40.O1.)R1>.(<.(2.&40.))R1=.(=.O4.))R1<.))")
(* [comment removed for export] *).

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09bb28]).
Local Ltac zchk_new ::= constr:([0x09ba84; 0x09ba88]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X : Z) (sw : word) (n P : Z) (limbs : list word) (pad : word) (own : limb_own) (lo d : Z).
  Hypothesis HNS : own <> LStatic.
  Hypothesis CW : client_wrange L (mpi_free_LB own P n LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16.
  Hypothesis DXP : own = LHeap -> X + 16 <= P \/ P + 4 * n <= X.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 64 - arl_need_rt R.
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
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ hh ?LBx LF ?mx, TOPx : bv_unsigned sp <= htop _ _ _ hh |- _ =>
      pose proof (hm_top asegs R HIA hh LBx LF mx HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange (hcs asegs R HIA hh) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPx HTOP; lia])
    end.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation FRAME := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation POST := (mpi_free_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X P n pad own lo d).

  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma fin_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_free ()) "Phc,(5.$42.VR,VHIA,)PLBc,(29.$2:.)Pmm,P,(2.&40.)(3.(2.&8.))Ppw,$18.Pjk,(29.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(25.$42.VR,VHIA,R15.R14.VLF,R13.)P,(7.$18.(1<.$42.VR,VHIA,R16.)(1<.$42.VR,VHIA,Vh,))P,(20.(10.&40.Vsp,)(1<.$42.VR,VHIA,R17.))P,Px,$18.P,(1?.$42.VR,VHIA,Vh,R1.)(1?.$42.VR,VHIA,R1:.R2.)P,(7.$18.(39.VX,+8.)=)P,(35.(20.(1:.VX,+10.)Vlo,)(20.(10.&40.Vsp,)VX,))P,(26.$42.R19.VX,(27.R18.Vsw,Vn,Vpad,))P,(30.(31.VR,)(32.$2:.R1;.(33.VLF,))(10.&40.Vsp,)(1<.$42.VR,VHIA,Vh,)VX,+10.)P,(3;.$42.(3<.VR,)(1?.$42.VR,VHIA,R1=.)R1;.VX,+10.)P,(26.$42.R1<.(1:.(10.&40.Vsp,)-30.)(16.$43.(44.#8.R1:.)(16.$43.(45.Vs3,)(16.$43.(45.Vs2,)(16.$43.(45.Vs1,)(16.$43.(45.Vs0,)(16.$43.(45.Vra,)(46.$43.))))))))P,(?.$42.R1=.Vlo,(1:.(10.&40.Vsp,)-30.))P,(>.$42.R1>.)(47.$42.(3<.VR,)(1?.$42.VR,VHIA,R21.)Lms',$48.(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3',(2.&40.)(1.(2.&40.)La4',(2.&40.)(1.(2.&40.)La5',(2.&40.)(1.(2.&40.)La6',(2.&40.)(1.(2.&40.)La7',(2.&40.)(1.(2.&40.)Lx28,(2.&40.)(1.(2.&40.)Lx29,(2.&40.)(1.(2.&40.)Lx30,(2.&40.)(1.(2.&40.)Lx31,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(6.(7.$48.R11.(9.(:.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,R=.R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(;.Vra,)Vfc,(<.(2.&40.))R1.(=.$42.)))(6.(49.(16.(17.$18.$18.)(19.$18.$18.Vlo,(10.&40.Vsp,))(16.(17.$18.$18.)(19.$18.$18.VX,(1:.VX,+10.))(46.(17.$18.$18.))))R30.R1.)(6.(4:.$42.R30.R1.)(6.(>.$42.R1.)(6.(26.$42.R1.VX,(27.=(28.&40.+1.)=Vpad,))(6.(?.$42.R1.Vlo,(10.&40.Vsp,))(25.$42.VR,VHIA,R32.R31.VLF,R1.)))))))))))))))))))))))(9.(:.R1<.(28.&40.(1:.(10.&40.Vsp,)-30.))Vgp,Vtp,R1;.R1:.R19.(28.&40.VX,)(28.&40.(1:.VX,+:.))R18.R17.R16.R15.R14.R13.R12.R11.(28.&40.(1:.(4;.VX,+3.)(4<.(3<.VR,))))(28.&40.(4<.(3<.VR,)))Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(28.&40.+9;:=0.)Vfc,(<.(2.&40.))R1?.(=.$42.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc HCSc ALX8 DSX HX CWc OX FR ST MI.
    pose proof (hcs_ok asegs R HIA hc) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.

  #[using="IMG ZF NEEDR HNS CW DXP LOS SLO TOP SPA TPV XUW"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_free ()) "Pmo,$4.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(25.$42.VR,VHIA,Vh,VLB,VLF,Vm,)P,(1>.$42.VR,VHIA,Vh,R10.)P,(2=.$42.Vm,VLB,VX,Vsw,Vn,VP,Vlimbs,Vpad,Vown,)P,(?.$42.Vm,Vlo,(10.&40.Vsp,))P,(>.$42.Vm,)P,(3;.$42.(3<.VR,)(1?.$42.VR,VHIA,Vh,)Vm,VX,+10.)P,(20.(1:.(21.$42.VR,VHIA,Vh,)$22.)$3=.)P,(20.(1:.(23.$42.VR,VHIA,Vh,)(24.Vd,))$3?.)(40.$42.(41.$42.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,VP,Vn,Vpad,Vown,Vlo,Vd,Vm,R17.)(8.(9.(:.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(28.&40.VX,)R13.R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(28.&40.$4=.)Vfc,(<.(2.&40.))Vm,(=.$42.))R17.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo MX ST MI OX BUD BUDF. unfold A_MPI_FREE. rt_facts h.
    pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
    ddestruct MX as (HXS & ALX & X0 & LL & NB & HOWN).
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF _]. rewrite Forall_forall in HF.
    (* [comment removed for export] *)
    assert (PB : 0 <= P /\ P + 4 * n <= alloc_ceiling /\ (own = LHeap -> 0 < P /\ In (P, 4 * n) LB /\ u32arr asegs m P limbs) /\ (own = LNull -> P = 0)).
    { destruct own; [| | exfalso; exact (HNS eq_refl)].
      - destruct HOWN as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|]. split; [intros E; discriminate E| intros _; exact E0].
      - ddestruct HOWN as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        split; [clear - B0; lia|]. split; [exact BC|]. split; [intros _; split; [exact B0| split; [exact HIN| exact HXL]]| intros E; discriminate E]. }
    ddestruct PB as (P0 & PC & PHEAP & PNULL). clear HOWN.
    (* [comment removed for export] *)
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| | exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia].
      intros b Hb. unfold mpi_free_LB in Hb. destruct own; [exact Hb| eapply In_lb_remove; exact Hb| exact Hb]. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - XB; lia); clear - K0 X0; lia|]. clear K0.
    (* [comment removed for export] *)
    zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ ?cs => set (FRC := cs) in FR end.
    (* [comment removed for export] *)
    zstep. if_cases KP; zify_cond KP.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KP by (clear - P0 PC; pose proof (alloc_ceiling_val R); lia).
      assert (EO : own = LNull) by (destruct own; [reflexivity| exfalso; destruct (PHEAP eq_refl) as [B0 _]; clear - B0 KP; lia| exfalso; exact (HNS eq_refl)]).
      subst own. cbn [mpi_free_LB mpi_free_X] in *.
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply fin_walk with (hc := h) (LBc := LB); try eassumption; try reflexivity; try (intros y Hy; exact Hy)
        | intros y Hy; exact Hy | ].
      all: try (unfold mpi_cells; exact HXS).
      all: try (subst FRC; exact FR).
      intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      unfold mpi_free_postA. deexists 16. dexists mo9, h. split; [reflexivity|].
      split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
      split.
      { cbn [mpi_free_LB mpi_free_X].
        eapply (presA_drop_below asegs R HIA h LB LF [(X, X + 16)] lo (bv_unsigned sp) _ m m9); [exact HH| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | eapply wmono_trans; [exact WM0| exact WM]].
        - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|]. apply Forall_nil.
        - eapply munch_trans; [eapply munch_weaken; [| exact MU0]; clear; intros y Hy; clear - Hy; cbn [outside] in *; tauto (* [comment removed for export] *) | exact MU]. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|].
      split; [intros y Hy; exact Hy|].
      split; [unfold AVOL_CALL; clear; lia|]. split; [unfold fr_charge; clear - D0; lia|].
      split; [exact HH9| exact HX9].
    - (* [comment removed for export] *)
      assert (EO : own = LHeap).
      { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. rewrite (PNULL eq_refl) in KP.
        rewrite ?unsigned_lit in KP by (clear; lia). clear - KP. lia. }
      subst own. cbn [mpi_free_LB mpi_free_X] in *. ddestruct (PHEAP eq_refl) as (B0 & HIN & HXL).
      rewrite ?unsigned_lit in KP by (clear - P0 PC NB; pose proof (alloc_ceiling_val R); lia).
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OX (X + 10) 2.
      zstep.
      unfold MPI_MAX_LIMBS in NB.
      replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NB; lia); rewrite Z.mod_small by (clear - NB; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. zstep.
      (* [comment removed for export] *)
      pose proof (u32arr_transport asegs _ m m1 _ _ HXL MU0 WM0 ltac:(cbn [disjoint_from]; clear - B0 PC NB LL ALO LOS SLO NEEDR; lia)) as HPL.
      apply u32arr_cells in HPL.
      replace (4 * length limbs)%nat with (Z.to_nat (n * 4)) in HPL by (clear - LL; lia).
      pose proof ZF as SP. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SP.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply SP with (h := h) (LB := LB) (LF := LF) (buf := P) (len := n * 4) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity.
        all: try (right; split; [replace (n * 4) with (4 * n) by (clear; lia); exact HIN | exact HPL]).
        all: try (eapply uw_obj_uwc; [exact XUW | clear; lia]).
        all: clear - NB B0 P0 PC LOS SLO NEEDR TOP SPA SPR BUD BUDF; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SP.
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by qlia.
      ddestruct PO as (MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      match type of HH2 with HM _ _ _ ?hh _ _ _ => rename hh into h2 end.
      replace (n * 4) with (4 * n) in HP2, HH2 by (clear; lia).
      (* [comment removed for export] *)
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) FRC)
        by (eapply (presA_rw_cells asegs R); [exact HP2| exact FR| apply client_range_stack; subst FRC; simpl_sizes; clear; lia| subst FRC; cbn; clear - B0 PC ALO LOS SLO NEEDR; lia]).
      assert (HXS2 : rw_cells asegs m2 X [C8 (Z_to_bv 64 P); C2 sw; C2 (Z_to_bv 64 n); C4 pad]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HXS| | cbn; specialize (DXP eq_refl); clear - DXP; lia].
        simpl_sizes. eapply client_range_sp_mono; [| eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]]. clear; lia. }
      assert (OX2 : aobj asegs AL CS m2 X 16).
      { eapply (presA_aobj asegs R CS); [exact CSOK| exact HP2| exact OX| | clear - LOS SLO NEEDR; lia| intros y Hy; eapply hcs_below_top; exact Hy].
        eapply client_range_sp_mono; [| eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]]. clear; lia. }
      clear HXS FR OX.
      (* [comment removed for export] *)
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX2) as OX3.
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply fin_walk with (hc := h2) (LBc := lb_remove P LB); try eassumption; try reflexivity
        | intros y Hy; exact Hy | ].
      all: try (unfold mpi_cells; exact HXS2).
      all: try exact HCS2.
      all: try (subst FRC; exact FR2).
      intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      unfold mpi_free_postA. deexists 16. dexists mo9, h2. split; [reflexivity|].
      split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
      split.
      { (* [comment removed for export] *)
        assert (CXP : crange CS P (4 * n)) by (eapply hcs_block; [exact HH| exact HIN]).
        eapply presA_trans; [eapply presA_trans|].
        - (* [comment removed for export] *)
          eapply (presA_weaken asegs R LB (lb_remove P LB) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16); (P, P + 4 * n)]);
            [| intros b Hb; eapply In_lb_remove; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
          eapply (presA_drop_below asegs R HIA h LB LF [(X, X + 16); (P, P + 4 * n)] lo (bv_unsigned sp) _ m m1); [exact HH| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | exact WM0].
          + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
            apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX2|].
            apply Forall_cons; [cbn [fst snd]; replace (P + 4 * n - P) with (4 * n) by lia; exact CXP|]. apply Forall_nil.
          + eapply munch_weaken; [| exact MU0]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *).
        - (* [comment removed for export] *)
          eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
          cbn [outside]. clear. (intros y dd_H; ddestruct dd_H as (A1 & A2 & _)). split; [clear - A2; lia| exact I].
        - (* [comment removed for export] *)
          rewrite <- HS2. pose proof (hcs_ok asegs R HIA h2) as CSOK2.
          eapply (presA_drop_below asegs R HIA h2 (lb_remove P LB) LF [(X, X + 16); (P, P + 4 * n)] lo (bv_unsigned sp) _ m2 m9); [exact HH2| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R (lb_remove P LB) LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK2);
            [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | | exact WM].
          + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; eapply crange_mono; [exact HCS2| exact SCS]|].
            apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX3|].
            apply Forall_cons; [cbn [fst snd]; replace (P + 4 * n - P) with (4 * n) by lia; eapply crange_mono; [exact HCS2| exact CXP]|]. apply Forall_nil.
          + eapply munch_weaken; [| exact MU]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [exact HV2|]. split; [exact HFR2|].
      split; [exact HH9| exact HX9].
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
End Walk.

Lemma A_mpi_free_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_free ()) "PR,$4>.PHIA,(4?.$42.R1.)P,(50.(3<.R2.))P,(51.$42.R3.R2.$52.)P,(20.=(38.R4.))(53.$42.R5.R4.$4=.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF NEEDR. unfold mpi_free_stmtA.
  intros until d. intros HH HK MX HNS CW DXP ST LOS SLO TOP SPA TPV MI OX BUD XUW BUDF ->.
  eapply main_walk; eassumption.
Qed.

(* [comment removed for export] *)
Lemma A_mpi_free_spec_closed : ltac2:(CDefT.buildp (gd_tbl_A_mpi_free ()) "PR,$4>.PHIA,(4?.$42.R1.)P,(50.(3<.R2.))P,(7.$18.(54.R3.)$55.)P,(7.$18.(56.R4.)$57.)P,Pm,P,(2.&40.)(3.(2.&8.))P,(58.R6.R1.)(59.R2.)P,(20.=(5:.R6.))P,(20.=(5;.R7.))P,(20.=(38.R8.))(53.$42.R9.R8.$4=.)")
(* [comment removed for export] *).
Proof.
  intros. eapply A_mpi_free_spec; eauto. eapply A_zeroize_and_free_spec; eauto.
Qed.
