(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_SetShadow () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.SetShadow.setsh_post"; "ARUN_1.setsh_entry"].

Section ARUN_1. Context {hAR : arun}.
Definition A_SETSH_00 : Z := 0x6b228.   (* [comment removed for export] *)
Definition A_SETSH_F5 : Z := 0x6b330.   (* [comment removed for export] *)
Definition A_SETSH_F8 : Z := 0x6b348.   (* [comment removed for export] *)

Definition setsh_entry (xx : Z) : Z := if Z.eqb xx 0 then A_SETSH_00 else if Z.eqb xx 0xf5 then A_SETSH_F5 else A_SETSH_F8.

Section SetShadow.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Definition setsh_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s n xx : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SetShadow ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O16.O15.O14.O13.R?.R>.R=.O12.O11.(8.&40.O4.)R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(9.O16.)O5.(:.(2.&40.))R1.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.O4.(12.O4.O3.))(13.(?.$10.$10.)))O1.R1.)(4.(14.$<.O1.R1.)(4.(15.$<.R1.)(4.(16.$<.R1.O4.(>.$17.(18.(19.O3.)(1:.(2.&8.)(8.&8.O2.)(19.O3.)))(13.$17.)))(1;.R1.)))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF"] Lemma setsh_spec : ltac2:(CDefT.buildp (gd_tbl_AW_SetShadow ()) "Pxx,$10.Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps,$10.Pn,$10.PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pold,(1=.$17.)P,(1>.(5.$10.R24.=)(1>.(5.$10.R24.+?5.)(5.$10.R24.+?8.)))P,(16.$<.R3.R7.R2.)P,(5.$10.(1?.(20.R3.))R7.)P,(21.=R8.)P,Px,$10.P,(4.(22.R;.R1.)(21.R1.(12.R;.R:.)))(23.VAL,VCS,R2.)P,(22.+7???8000.R;.)P,(21.(12.R<.R;.)(24.+2.+2?.))P,(1;.R9.)P,(15.$<.R:.)(25.$<.VAL,VCS,(26.R2<.R2;.R2:.R29.R25.R24.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R=.R<.R?.R>.R2=.R;.)(6.(7.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.(8.&40.R?.)(8.&40.R>.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R=.(8.&40.(27.R2=.))R<.(:.(2.&40.))R;.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros xx ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s n F fc m old
      XX OLD SZ NPOS AOK SLO SHI PS MI.
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    dpose PS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GRM & RM & _). unfold A_GOT_RMEMSET, A_RMEMSET, A_MUSL_MEMSET in GRM, RM.
    (* [comment removed for export] *)
    assert (SH : rw_cells asegs m s [CB (Z.to_nat n) (cells_bytes old)]).
    { eapply rw_cells_reshape; [exact OLD| | cbn; rewrite app_nil_r; reflexivity]. cbn. split; [| exact I].
      rewrite cells_bytes_length by (exact (proj1 (proj1 OLD))). clear -SZ. lia. }
    assert (CALL : forall (x6 : word),
      evtA asegs AL CS (setsh_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s n xx m)
        (MS (mkR ra sp gp tp t0 x6 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 xx) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x0eadc4) fc None m (seg_rom asegs))).
    { intros x6. eapply evtA_mono.
      - eapply (A_memset_evtA_aok AL CS IMG) with (S := s) (k := n) (v := xx);
          [exact SH| exact MI| exact AOK| clear -SLO; lia| clear -NPOS; lia| clear -SHI; lia| clear -XX; lia| reflexivity| reflexivity| reflexivity].
      - cbv beta. (intros ms' dd_H; ddestruct dd_H as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m' & -> & MU & WM & MI' & SH')).
        unfold setsh_post. deexists 15. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact SH'|].
        eapply (poison_statics_transport _ _ _ PS MU). intros A' n' H. cbn. clear -H SLO. lia. }
    unfold setsh_entry, A_SETSH_00, A_SETSH_F5, A_SETSH_F8.
    destruct XX as [-> | [-> | ->]]; cbn [Z.eqb Pos.eqb].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. apply CALL.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. apply CALL.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. apply CALL.
  Qed.
End SetShadow.

End ARUN_1.
