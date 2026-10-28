(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow NodesA SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_unreg_globals A_tailkit_defs A_oomtail A_refused.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance Lib.PropExec.fx0.
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
Ltac2 gd_tbl_A_main_tails () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.tail_memA"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_oom"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].


Section Tails.
  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis GSB : al_gsb AL = 0x1099f8%Z.
  Hypothesis IMGCS : A_unreg_globals.img_cs AL CS.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_main_tails ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VKI,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VKI,R1.(<.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_main_tails ()) "Pmo,$0.Pmo',$0.P,A1.VKI,R2.P,(8.$=.(>.R2.)(>.R3.))P,(8.(1.(2.(3.&40.)(3.&40.)))(?.R3.)(?.R4.))P,(8.(1.(3.&40.))(10.R4.)(10.R5.))P,(8.(9.(3.&40.))(11.R5.)(11.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Variable sp : word.
  Hypothesis SPlo : (0x7fff7f000000 + 4096 <= bv_unsigned sp)%Z.
  Hypothesis SPhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis WCS : crange CS (bv_unsigned sp - 4096) 4096.
  Hypothesis ICS : forall a n, 0x10000 <= a -> a + n <= 0x0f1000 -> crange CS a n.   (* [comment removed for export] *)

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rtc_stderr_cells : ltac2:(CDefT.buildp (gd_tbl_A_main_tails ()) "Pm,P,(3.&40.)(9.(3.&8.))P,(12.R1.)(7.(13.$14.R2.+?6:;0.(15.$16.(17.(18.&40.+?5=48.))(19.$16.)))(13.$14.R2.+?5=48.(15.$16.(17.(18.&40.+?:488.))(19.$16.))))")
(* [comment removed for export] *).
  Proof.
    intros m RTC. split.
    - exact (asan_rtc_cell m 0x0f6ab0 8%nat 0x0f5d48 RTC ltac:(unfold rtc_cells; cbn [In]; repeat (first [left; reflexivity | right]))).
    - exact (asan_rtc_cell m 0x0f5d48 8%nat 0x0fa488 RTC ltac:(unfold rtc_cells; cbn [In]; repeat (first [left; reflexivity | right]))).
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma oom1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_tails ()) "Pra,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Pm,P,(3.&40.)(9.(3.&8.))P,(12.R1.)(1:.$14.VAL,VCS,Lms',$1;.(8.$1;.R1.(1<.(1=.(18.&40.+97368.)Vsp,R20.R1?.R1>.R1=.R1<.R1;.R1:.(18.&40.+156>6.)(18.&40.+13.)(18.&40.+1.)(18.&40.+?:488.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(1>.&5.(3.&40.))(18.&40.+58714.)(18.&20.=)(1?.(3.&40.))R3.(20.$14.)))(1<.(1=.R20.Vsp,R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(1>.&5.(3.&40.))(18.&40.+97388.)(18.&20.=)(1?.(3.&40.))R2.(20.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros * RTC. al_facts. destruct (rtc_stderr_cells m RTC) as [G1 G2].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtA_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma oom2_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_tails ()) "Pra,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Pm,P,(3.&40.)(9.(3.&8.))P,(12.R1.)(1:.$14.VAL,VCS,Lms',$1;.(8.$1;.R1.(1<.(1=.(18.&40.+97368.)Vsp,R20.R1?.R1>.R1=.R1<.R1;.R1:.(18.&40.+156>6.)(18.&40.+13.)(18.&40.+1.)(18.&40.+?:488.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(1>.&5.(3.&40.))(18.&40.+58714.)(18.&20.=)(1?.(3.&40.))R3.(20.$14.)))(1<.(1=.R20.Vsp,R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(1>.&5.(3.&40.))(18.&40.+97348.)(18.&20.=)(1?.(3.&40.))R2.(20.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros * RTC. al_facts. destruct (rtc_stderr_cells m RTC) as [G1 G2].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtA_done. reflexivity.
  Qed.

  Variables (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).

  #[using="AL CS IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly SPlo SPhi SPal WCS ICS"] Theorem oom_glueA : ltac2:(CDefT.buildp (gd_tbl_A_main_tails ()) "Ppc,$21.Pra,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PM,P,(3.&40.)(9.(3.&8.))Pmo,$0.P,(22.(8.$21.R1?.+97388.)(8.$21.R1?.+97348.))P,(23.Vsp,R3.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,A1.VKI,R3.P,(8.(9.$24.)(25.(26.R4.)(18.&40.+2.))(;.$24.(27.(18.&40.+2.))))(28.$14.(29.(1<.(1=.R22.Vsp,(18.&40.+10800.)(18.&40.+63<:90.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)(1>.&5.(3.&40.))(18.&40.R23.)(18.&20.=)(1?.(3.&40.))R6.(20.$14.))R5.)(2:.$2;.(2<.R5.)))")
(* [comment removed for export] *).
  Proof.
    intros * Hpc TM HKI FD2. pose proof (tm_rtc _ _ _ _ _ _ _ _ TM) as RTC.
    eapply (rz_evtA_K asegs AL CS KI K_halted K_mat); [exact HKI | |].
    { destruct Hpc as [-> | ->]; [apply oom1_steps | apply oom2_steps]; exact RTC. }
    cbn beta. intros ms2 mo2 -> HKI2 MM2.
    change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
    rewrite <- (mo_mat_fs _ _ MM2).
    eapply (oom_tailA AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly sp mo2 SPlo SPhi SPal HKI2);
      [ unfold m_fds in *; destruct MM2 as (E1 & _); rewrite E1; exact FD2
      | exact WCS
      | apply ICS; lia
      | reflexivity .. | apply (tail_oom _ _ _ _ _ _ _ _ TM) ].
  Qed.
End Tails.
