(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA.
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
Ltac2 gd_tbl_A_mpi_zeroize_and_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "zeroize_and_free_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "A_WRAP_MEMSET_ZF"; "A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "zeroize_and_free_stmtA"].


Definition A_MEMSET_FUNC_ZF : Z := 0x0f1540.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_WRAP_MEMSET_ZF : Z := 0x67db4.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_WRAP_FREE_ZF : Z := 0x6947c.      (* [comment removed for export] *) (* [comment removed for export] *)

Definition zeroize_and_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (buf len lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_zeroize_and_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1>.O1=.O1<.)Lh',(5.O1>.O1=.O1<.)(6.(7.$0.R13.(8.(9.(:.O18.O17.O16.O15.R12.R11.R10.O14.O13.R?.R>.R=.R<.R;.R:.R9.R8.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R7.R6.R5.R4.)O8.(;.O18.)O7.(<.(2.&40.))R3.(=.O1>.))R2.))(6.(>.O1>.R3.)(6.(?.O1>.R3.O4.(10.&40.O17.))(6.(11.O1.R2.)(6.(12.O1>.O1=.(13.O6.O1:.)O19.(10.&40.O17.)(14.O1=.)(15.O1>.O1=.O1<.O1;.)(16.(17.$18.$18.)(19.$18.$18.O6.(1:.O6.O5.))(1;.(17.$18.$18.)))O2.R3.)(6.(7.$18.(1<.O1>.O1=.O1<.R1.)(1<.O1>.O1=.O1<.O1;.))(6.(7.$18.(15.O1>.O1=.O1<.R1.)(15.O1>.O1=.O1<.O1;.))(6.(7.$18.(1=.O1>.O1=.O1<.R1.)(1=.O1>.O1=.O1<.O1;.))(6.(1>.O1>.O1=.O1<.R1.R2.)(6.Px,$18.P,(1?.O1>.O1=.O1<.O1;.R1.)(1?.O1>.O1=.O1<.R3.R2.)(6.(20.(21.O1>.O1=.O1<.R1.)(1:.(21.O1>.O1=.O1<.O1;.)$22.))(6.(20.(23.O1>.O1=.O1<.R1.)(1:.(23.O1>.O1=.O1<.O1;.)(24.O3.)))(25.O1>.O1=.O1<.R1.(13.O6.O1:.)O19.R3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition zeroize_and_free_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_zeroize_and_free ()) "Ph,(5.O4.O3.O2.)PLB,(26.$27.)PLF,(26.$27.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(28.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pbuf,$18.Plen,$18.Plo,$18.Pd,$18.Pjunk,(26.(2.&8.))P,(25.O4.O3.O2.R2;.R2:.R29.R7.)P,(1>.O4.O3.O2.R2<.R7.)P,(29.(6.(7.$18.R7.=)(7.$18.R6.=))(6.(2:.(17.$18.$18.)(19.$18.$18.R7.R6.)R2<.)(2;.O4.R9.R7.(16.$2<.(2=.(2>.R6.)R3.)(1;.$2<.)))))P,(6.(20.=R7.)(2?.R7.(30.+2.+28.)))P,(?.O4.R;.R7.(10.&40.R2;.))P,(20.(14.O3.)R8.)P,(20.R9.(31.(31.(10.&40.R2=.)+10.)(32.O3.)))P,(20.(10.&40.R2>.)(1<.O4.O3.O2.R32.))P,(7.$18.(33.(10.&40.R2?.)+10.)=)P,(7.(2.&40.)R2>.(34.&40.(35.O3.)))P,(>.O4.R11.)P,(20.(1:.(21.O4.O3.O2.R36.)$22.)$36.)P,(37.O4.R13.(14.O3.)(15.O4.O3.O2.R37.)(10.&40.R2=.)(10.&40.R33.)R>.)P,(20.(1:.(23.O4.O3.O2.R38.)(24.R?.))$38.)P,(7.(2.&40.)R2=.(34.&40.R13.))P,(7.(2.&40.)R2=.(34.&40.R13.))(39.O4.(3:.O4.O3.O2.R3;.R3:.R39.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.R15.R14.R13.R12.R17.R16.)(8.(9.(:.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(34.&40.O1.)R18.(<.(2.&40.))R17.(=.O4.))R16.))")
(* [comment removed for export] *).

Lemma lb_remove_none : forall A (LB : list blk), (forall b, In b LB -> fst b <> A) -> lb_remove A LB = LB.
Proof.
  intros A LB. induction LB as [|b r IH]; cbn; intros H; [reflexivity|].
  destruct (Z.eqb_spec (fst b) A) as [E|NE]; [exfalso; apply (H b); [left; reflexivity| exact E]|].
  f_equal. apply IH. intros b' Hb'. apply H. right. exact Hb'.
Qed.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis MSI : arl_memset_i R = A_WRAP_MEMSET_ZF.
  Hypothesis FREE : arl_free R = A_WRAP_FREE_ZF.
  Hypothesis RTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis NEEDF : 0 <= arl_need_free R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (buf len lo : Z) (junk : list byte).
  Hypothesis HB : (buf = 0 /\ len = 0) \/ (In (buf, len) LB /\ rw_cells asegs m buf [CB (Z.to_nat len) junk]).
  Hypothesis Hn : 0 <= len < 2^40.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts hh :=
    pose proof (hcs_ok asegs R HIA hh) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hh) as SCS0;
    pose proof (arl_need_rt_free R) as NRF; pose proof (arl_need_rt_amem R) as NRA;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ hh LB LF ?mx |- _ =>
      pose proof (hm_top asegs R HIA hh LB LF mx HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange (hcs asegs R HIA hh) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

  (* [comment removed for export] *)
  #[using="IMG MSI FREE RTC NEEDA NEEDF junk HB Hn LOS SLO TOP"] Lemma front_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_zeroize_and_free ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(25.$3;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(?.$3;.Vm,Vlo,(10.&40.Vsp,))P,(>.$3;.Vm,)(3<.$3;.(3=.VR,)(1?.$3;.VR,VHIA,Vh,)Lms',$3>.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3',(2.&40.)(1.(2.&40.)La4',(2.&40.)(1.(2.&40.)La5',(2.&40.)(1.(2.&40.)La6',(2.&40.)(1.(2.&40.)La7',(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(6.(7.$3>.R10.(9.(:.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(34.&40.Vbuf,)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(34.&40.(3?.VR,))Vfc,(<.(2.&40.))R1.(=.$3;.)))(6.(40.(16.(17.$18.$18.)(19.$18.$18.Vbuf,(1:.Vbuf,Vlen,))(16.(17.$18.$18.)(19.$18.$18.Vlo,(10.&40.Vsp,))(1;.(17.$18.$18.))))Vm,R1.)(6.(41.$3;.Vm,R1.)(6.(>.$3;.R1.)(6.(?.$3;.R1.Vlo,(10.&40.Vsp,))(25.$3;.VR,VHIA,Vh,VLB,VLF,R1.)))))))))))))))))))))(9.(:.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,(34.&40.Vbuf,)(34.&40.Vlen,)R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(34.&40.$42.)Vfc,(<.(2.&40.))Vm,(=.$3;.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH ST MI. unfold A_ZEROIZE_AND_FREE. rt_facts h.
    unfold A_WRAP_FREE_ZF in FREE.
    pose proof (munch_refl [(buf, buf + len); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct HB as [[E0 EL] | [HIN HBC]].
    { (* [comment removed for export] *)
      subst buf len. carve_frame 16%nat ST.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
      rewrite <- FREE. apply evtA_done. deexists 15. split; [reflexivity|].
      repeat (split; [assumption|]). assumption. }
    (* [comment removed for export] *)
    pose proof (rw_cells_bound _ _ _ _ HBC) as BB. cbn [cells_size csize Nat.add] in BB.
    assert (JL : length junk = Z.to_nat len).
    { destruct HBC as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF. }
    assert (BB' : 0 < buf /\ buf + len <= alloc_ceiling).
    { destruct (hm_apart asegs R HIA h LB LF _ HH) as [HF _]. rewrite Forall_forall in HF.
      ddestruct (HF (buf, len) ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear - B0 BC. lia. }
    clear BB.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by (clear - BB' ACP; lia); clear - KB BB'; lia|].
    (* [comment removed for export] *)
    zstep. zstep. if_cases KL; zify_cond KL.
  - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by (clear - Hn; lia).
      zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
      rewrite <- FREE. apply evtA_done. deexists 15. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
  - rewrite ?unsigned_lit in KL by (clear - Hn; lia).
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with H : HM _ _ _ _ _ _ mx |- _ => pose proof (asan_rtc_memset_func mx (RTC mx (hm_rtc asegs R HIA h LB LF mx H))) as MSF end end.
      zstep. clear MSF.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      apply (u8arr_of_rw_cells asegs) in HBC.
      pose proof (hm_aobj_block asegs R HIA h LB LF _ buf len ltac:(eassumption) HIN) as OB.
      assert (HINF : In (buf, len) (LB ++ fdata LF)) by (apply in_app_iff; left; exact HIN).
      pose proof (artA_amemset asegs R HIA A_WRAP_MEMSET_ZF) as SPM. rewrite <- MSI in SPM. unfold A_WRAP_MEMSET_ZF in MSI. rewrite MSI in SPM.
      callxA_sp (bv_unsigned sp + -16)
        (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := buf) (v := 0) (n := len) (lo := lo) (ds := junk);
         rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia;
         try eassumption; try reflexivity; try lia;
         try (right; reflexivity);
         try (rewrite JL; lia);
         try (eapply crange_sub; [exact SCS0| lia| lia]);
         try (eapply (blk_top47_sub asegs R HIA h LB LF); [eassumption| exact HIN| clear; lia]);   (* [comment removed for export] *)
         try (eapply client_wrange_block; [exact HINF| lia| lia])).
      clear SPM.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "ZF-MEMSET-LEFT:" g end.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : stk _ m5 lo _ |- _ => rename H into ST5 end.
      match goal with H : ?x = Z_to_bv 64 buf |- _ => subst x end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. release_frame FR ST5 (bv_unsigned sp). zstep.
      rewrite <- FREE. apply evtA_done. deexists 15. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    all: match goal with |- ?g => idtac "FRONT-LEFT:" g end.
  Qed.

  #[using="IMG MSI FREE RTC NEEDA NEEDF junk HB Hn LOS SLO TOP SPA TPV"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_zeroize_and_free ()) "Pmo,$4.Pd,$18.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(25.$3;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(1>.$3;.VR,VHIA,Vh,R10.)P,(?.$3;.Vm,Vlo,(10.&40.Vsp,))P,(>.$3;.Vm,)P,(20.(1:.(21.$3;.VR,VHIA,Vh,)$22.)$36.)P,(37.$3;.Vm,(14.VR,)(15.$3;.VR,VHIA,Vh,)(10.&40.Vs0,)(10.&40.Vsp,)R13.)P,(20.(1:.(23.$3;.VR,VHIA,Vh,)(24.R14.))$38.)(39.$3;.(3:.$3;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vbuf,Vlen,Vlo,R15.Vm,R16.)(8.(9.(:.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(34.&40.Vbuf,)(34.&40.Vlen,)R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(34.&40.$42.)Vfc,(<.(2.&40.))Vm,(=.$3;.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros mo d t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HKmo ST MI BUD UW BUDF. rt_facts h.
    pose proof (fr_charge_nonneg _ _ _ _ _ _ _ UW) as FRC0.
    pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SLO SPR NEEDF NRF; lia)) as TOP64.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV); [eapply front_walk; eassumption | intros y Hy; exact Hy |].
    intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI2 & ST2 & HH2). subst ms'.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    (* [comment removed for export] *)
    assert (UW2 : uwc asegs m2 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_callW asegs _ m m2); [exact UW| exact MU| | clear; lia| clear - SPR; lia| exact TOP64].
      intros a Ha. cbn [outside]. destruct HB as [[E0 EL]|[HIN _]].
      - subst buf len. clear - Ha Hn LOS SLO SPR NEEDF NRF. lia.
      - destruct (hm_apart asegs R HIA h LB LF _ HH) as [HF _]. rewrite Forall_forall in HF.
        ddestruct (HF (buf, len) ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        clear - Ha B0 BC ALO LOS SLO SPR NEEDF NRF. lia. }
    (* [comment removed for export] *)
    intros mo1 [HK1 MF1].
    destruct HB as [[E0 EL] | [HIN HBC]].
    - (* [comment removed for export] *)
      subst buf len.
      assert (ELB : lb_remove 0 LB = LB).
      { apply lb_remove_none. intros b Hb. destruct (hm_apart asegs R HIA h LB LF _ HH) as [HF _]. rewrite Forall_forall in HF.
        destruct (HF b ltac:(apply in_app_iff; left; exact Hb)) as (B0 & _). clear - B0. lia. }
      eapply aevtS_mono.
      { apply aevtS_of_aevt. eapply (evtA_aevt asegs AL (AIh asegs R HIA h) (AIh_laws asegs R HIA h)); [exact (conj HK1 (fun x Hx => Hx))|].
        eapply (heapA_free_null asegs R HIA) with (lo := lo); try eassumption; try reflexivity.
        all: clear - LOS SLO NEEDF NRF TOP SPA; try lia.
        all: match goal with |- ?g => idtac "FREE0-PRE-LEFT:" g end. }
      intros c Q9. destruct c as [ms9 mo9]. cbv beta in Q9. cbn [cfg_ms cfg_model] in Q9. ddestruct Q9 as (PC & AI9 & MM9).
      unfold call_postA in PC. destruct_exs PC. ddestruct PC as (E & MI9 & ST9 & WM9 & HP9 & h9 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKiff & HH9). subst ms9.
      unfold zeroize_and_free_postA. deexists 16. dexists mo9, h9. split; [reflexivity|].
      split; [exact MI9|]. split; [exact ST9|].
      split; [eapply mo_frame_trans; [exact MF1| apply mo_mat_frame; exact MM9]|].
      split.
      { rewrite ELB. eapply presA_trans; [| eapply presA_weaken; [exact HP9| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]].
        (* [comment removed for export] *)
        eapply (presA_drop_below asegs R HIA h LB LF [(0, 0 + 0)] lo (bv_unsigned sp) m m m2); [exact HH| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m2 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | exact WM].
        - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
          apply Forall_cons; [cbn [fst snd]; intros xq Hxq; exfalso; clear - Hxq; lia|]. apply Forall_nil.
        - eapply munch_weaken; [| exact MU]. clear. intros x Hx; clear - Hx; cbn [outside] in *. tauto (* [comment removed for export] *). }
      split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|].
      split; [apply (proj2 (HKiff mo9)); exact (proj1 AI9)|].
      split; [intros y Hy; rewrite Ehcs; exact Hy|].
      split; [rewrite Evol; unfold AVOL_CALL; clear; lia|].
      split; [rewrite Efr; clear - FRC0; lia|].
      rewrite ELB. exact HH9.
    - (* [comment removed for export] *)
      eapply aevtS_mono.
      { eapply (heapA_free asegs R HIA) with (h := h) (LB := LB) (LF := LF) (A := buf) (n := len) (lo := lo) (d := d);
          try eassumption; try reflexivity.
        all: clear - LOS SLO NEEDF NRF TOP SPA BUD BUDF; try lia.
        all: match goal with |- ?g => idtac "FREE-PRE-LEFT:" g end. }
      intros c Q9. cbv beta in Q9. ddestruct Q9 as (ms9 & mo9 & E & PC). subst c.
      unfold call_postA in PC. destruct_exs PC. ddestruct PC as (E & MI9 & ST9 & MF9 & HP9 & h9 & Ehtop & Estk & Eflag & HK9 & HCS9 & HV9 & HFR9 & HH9). subst ms9.
      unfold zeroize_and_free_postA. deexists 16. dexists mo9, h9. split; [reflexivity|].
      split; [exact MI9|]. split; [exact ST9|].
      split; [eapply mo_frame_trans; [exact MF1| exact MF9]|].
      split.
      { eapply presA_trans; [| eapply presA_weaken; [exact HP9| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]].
        eapply (presA_weaken asegs R LB (lb_remove buf LB) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(buf, buf + len)]);
          [| intros b Hb; eapply In_lb_remove; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below asegs R HIA h LB LF [(buf, buf + len)] lo (bv_unsigned sp) m m m2); [exact HH| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m2 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | exact WM].
        - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (buf + len - buf) with len by lia; eapply hcs_block; [exact HH| exact HIN]|]. apply Forall_nil.
        - eapply munch_weaken; [| exact MU]. clear. intros x Hx; clear - Hx; cbn [outside] in *. tauto (* [comment removed for export] *). }
      split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact HK9|].
      split; [exact HCS9|]. split; [exact HV9|]. split; [exact HFR9|]. exact HH9.
    all: match goal with |- ?g => idtac "ZF-LEFT:" g end.
  Qed.
End Walk.

Lemma A_zeroize_and_free_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_zeroize_and_free ()) "PR,$43.PHIA,(44.$3;.R1.)P,(45.(3=.R2.))P,(7.$18.(46.R3.)$47.)P,(7.$18.(3?.R4.)$48.)P,Pm,P,(2.&40.)(3.(2.&8.))P,(49.R6.R1.)(4:.R2.)P,(20.=(4;.R6.))P,(20.=(4<.R7.))(4=.$3;.R8.R7.$42.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG MSI FREE RTC NA NF. unfold zeroize_and_free_stmtA.
  intros until junk. intros HH HK HB Hn ST LOS SLO TOP SPA TPV MI BUD UW BUDF -> ->.
  eapply main_walk; eassumption.
Qed.
