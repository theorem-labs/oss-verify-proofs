(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_platform_zeroize.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Ltac2 gd_tbl_A_platform_zeroize () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "platform_zeroize_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "A_WRAP_MEMSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "platform_zeroize_stmtA"; "A_PLATFORM_ZEROIZE"].


Definition A_PLATFORM_ZEROIZE : Z := 0x0a7edc.
Definition A_MEMSET_FUNC : Z := 0x0f1540.     (* [comment removed for export] *)
Definition A_WRAP_MEMSET : Z := 0x67db4.      (* [comment removed for export] *)

(* [comment removed for export] *)
Notation PLATFORM_ZEROIZE_STACK_A := 16 (only parsing).

Definition platform_zeroize_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_platform_zeroize ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O16.O15.O14.O13.R10.R?.R>.O12.O11.R=.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(8.O16.)O5.(9.(2.&40.))R1.(:.O1<.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.O4.(10.O4.O3.))(<.(=.$>.$>.)(?.$>.$>.O2.(11.&40.O15.))(12.(=.$>.$>.))))O1.R1.)(4.(13.O1<.O1.R1.)(4.(14.O1<.R1.)(4.(15.O1<.R1.O4.(<.$16.(17.(18.O3.)(19.(2.&8.)(1:.&8.=)(18.O3.)))(12.$16.)))(4.(1;.O1<.R1.O2.(11.&40.O15.))(1<.O1<.O1;.O1:.O19.O18.O17.R1.)))))))))))))))))))))))")
(* [comment removed for export] *).

Definition platform_zeroize_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_platform_zeroize ()) "Ph,(1=.O4.O3.O2.)PLB,(1>.$1?.)PLF,(1>.$1?.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Pn,$>.Plo,$>.Pjunk,(1>.(2.&8.))P,(1<.O4.O3.O2.R29.R28.R27.R5.)P,(15.O4.R6.R5.(<.$16.(17.(18.R4.)R2.)(12.$16.)))P,(21.=R5.)P,(22.=R7.)P,(1;.O4.R9.R6.(11.&40.R29.))P,(21.(23.O3.)R7.)P,(21.R8.(24.(24.(11.&40.R2;.)+10.)(25.O3.)))P,(21.(11.&40.R2<.)(26.O4.O3.O2.R30.))P,(5.$>.(27.(11.&40.R2=.)+10.)=)P,(28.(21.(10.R=.R<.)R;.)(21.(11.&40.R2>.)R=.))P,(14.O4.R?.)P,(29.O4.(2:.O3.)(2;.O4.O3.O2.R34.)R10.R?.R>.)P,(22.R?.(2<.+2.+28.))P,(2=.(2>.O3.)(2?.$1?.R35.(30.R34.))(23.O3.)(26.O4.O3.O2.R36.)R11.R10.)P,(5.(2.&40.)R2;.(1:.&40.R12.))P,(5.(2.&40.)R2;.(1:.&40.R12.))(31.O4.(2:.O3.)(2;.O4.O3.O2.R39.)(32.O4.O3.O2.R39.R38.R37.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R14.R13.R12.R15.)(6.(7.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(1:.&40.O1.)R16.(9.(2.&40.))R15.(:.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  (* [comment removed for export] *)
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis MSI : arl_memset_i R = A_WRAP_MEMSET.
  Hypothesis RTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis NEED0 : 0 <= arl_need_amem R.

  #[using="IMG MSI RTC NEED0"] Lemma A_platform_zeroize_walk : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Proof.
    unfold platform_zeroize_stmtA, A_PLATFORM_ZEROIZE.
    intros until junk. intros HH HB Hn HA ST LOS SLO TOP SPA DS MI OA N40 CWA -> ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by lia.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)).
    { eapply crange_sub; [exact SCS0| lia| lia]. }
    pose proof (rw_cells_bound _ _ _ _ HB) as AB. cbn [cells_size csize Nat.add] in AB.
    assert (JL : length junk = Z.to_nat n).
    { destruct HB as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF. }
    assert (AB' : 0 <= A /\ A + n <= 2^64) by lia. clear AB. rename AB' into AB.
    pose proof (munch_refl [(A, A + n); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      rewrite ?unsigned_lit in K0 by lia.
      zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      finish; try eassumption; try lia.
      subst n. cbn [Z.to_nat repeat] in *. destruct junk; [exact HB | cbn in JL; lia]. }
    rewrite ?unsigned_lit in K0 by lia.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with H : HM _ _ _ _ _ _ mx |- _ => pose proof (asan_rtc_memset_func mx (RTC mx (hm_rtc asegs R HIA h LB LF mx H))) as MSF end end.
    (* [comment removed for export] *)
    zstep. clear MSF. zstep. zstep. zstep.
    apply (u8arr_of_rw_cells asegs) in HB.
    pose proof (artA_amemset asegs R HIA A_WRAP_MEMSET) as SPM. rewrite <- MSI in SPM. unfold A_WRAP_MEMSET in MSI. rewrite MSI in SPM.
    callxA_sp (bv_unsigned sp + -16)
      (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := A) (v := 0) (n := n) (lo := lo) (ds := junk);
       rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia;
       try eassumption; try reflexivity; try lia;
       try (right; reflexivity);
       try (rewrite JL; lia);
       try (eapply crange_sub; [exact SCS0| lia| lia]);
       try (eapply (cw_top47_or asegs R HIA h LB LF); [eassumption| exact CWA| lia]);   (* [comment removed for export] *)
       try solve_client_wrange).
    clear SPM.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "PZ-CALL-LEFT:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr _ m5 A _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; rename H into HZ end.
    match goal with H : stk _ m5 lo _ |- _ => rename H into ST end.
    match goal with H : ?x = Z_to_bv 64 A |- _ => subst x end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish; try eassumption; try lia.
    all: match goal with |- ?g => idtac "PZ-LEFT2:" g end.
  Qed.
End Walk.

Lemma A_platform_zeroize_spec : ltac2:(CDefT.buildp (gd_tbl_A_platform_zeroize ()) "PR,$33.PHIA,(34.$35.R1.)P,(36.(2:.R2.))P,(5.$>.(37.R3.)$38.)P,Pm,P,(2.&40.)(3.(2.&8.))P,(39.R5.R1.)(3:.R2.)P,(21.=(25.R5.))(3;.$35.R6.R5.$3<.)")
(* [comment removed for export] *).
Proof. intros. eapply A_platform_zeroize_walk; eauto. Qed.
