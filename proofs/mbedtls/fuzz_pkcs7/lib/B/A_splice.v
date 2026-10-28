(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb StoreOk ShapeX MemSplit
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg ARestrict A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_splice () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.ARestrict.AIMG_HI"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.sr_vars_lt"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.kn_vars_lt"; "Stdlib.Lists.List.In"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.junk_vals"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.sr_after_call_j"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ridx"; "RocqVerifyHarness.AgentSubmission.BB.LibKnowFrame.kn_frame"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "Stdlib.ZArith.BinInt.Z.lt"].


Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [O|NO]; [|right; intros [_ O]; exact (NO O)].
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_le_dec x hi); first [right; intros [N _]; apply N; lia | left; split; [lia | exact O]].
Qed.

(* [comment removed for export] *)
Lemma grows_of_munch_high : ltac2:(CDefT.buildp (gd_tbl_A_splice ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))P,(4.R3.R2.R1.)P,(5.$6.R3.R2.)P,Px,$7.P,(8.(9.R6.R1.))(:.$;.R2.)(<.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' MU WM HI x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR.
  destruct (outside_dec W (bv_unsigned x)) as [O|NO].
  - rewrite (MU x O). exact Hx.
  - specialize (HI _ NO).
    assert (WV : wview asegs m x <> None). { unfold wview. destruct (m x); [discriminate | exfalso; apply Hx; reflexivity]. }
    specialize (WM x WV). unfold wview in WM. destruct (m' x) eqn:Mx; [discriminate|].
    exfalso. change (Z.of_N 1) with 1 in WM.
    destruct (find_segment asegs (bv_unsigned x) 1) as [seg|] eqn:FS; [|apply WM; reflexivity].
    pose proof (find_segment_cov asegs asegs (bv_unsigned x) 1 seg FS ltac:(auto) 0 ltac:(lia)) as C.
    rewrite Z.add_0_r in C. apply asegs_segcov in C. lia.
Qed.

Section WithK.
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable K : Model -> Prop.
  Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_splice ()) "Pmo,$=.Pacc,(0.(>.(2.&40.)$?.))P,A1.VK,R2.P,(10.VAL,VCS,R2.)(11.$=.Lmo',$=.(12.(13.(3.$=.)(14.R5.R4.)(15.$=.R1.))(12.A1.VK,R1.(16.R5.R1.))))")
(* [comment removed for export] *).

  #[using="K_halted K_mat"] Theorem splice_evtA : ltac2:(CDefT.buildp (gd_tbl_A_splice ()) "Pvals,(0.(2.&40.))Pebs,P,$?.(0.(2.&8.))Psr,(0.$17.)Pkn,(0.$18.)PR,(19.&5.(2.&40.))PM,P,(2.&40.)(3.(2.&8.))Pmo,$=.Pkept,(0.(2.&5.))Pk0,$7.Plo,$7.PQ,P,(19.&5.(2.&40.))P,P,(2.&40.)(3.(2.&8.))SpPpc,$7.Ppc',$7.PT,$1:.ZE,$1;.(1<.(1=.R>.)R=.)Zsp0,$7.(1>.&40.(1=.R?.#0.))P,(1?.R2.R>.R<.)P,(20.$6.R3.R<.R>.)P,A1.VK,R<.P,(13.$21.(22.(23.(2.&40.)R13.)R11.)$24.)P,(13.$21.(25.(23.(2.&40.)R14.)R11.)$24.)P,(8.(26.(2.&5.)(27.&5.=$28.)R>.))P,(:.(29.$;.+800000.)R7.)P,(:.(29.R8.R?.)(2:.+2.+40.))P,(:.-800000.R10.)P,(:.(2;.R:.+800000.)R10.)P,(2<.$6.VAL,VCS,Lms',$2=.(11.(19.&5.(2.&40.))LR',(19.&5.(2.&40.))(11.P,(2.&40.)(3.(2.&8.))LM',P,(2.&40.)(3.(2.&8.))(12.(13.$2=.R3.(2>.R2.(2?.&5.(2.&40.))(30.&40.R11.)(30.&20.=)(31.(2.&40.))R1.(32.$6.)))(12.Pr,(2.&5.)P,(26.(2.&5.)R1.R17.)(13.(2.&40.)(33.R4.R2.)(33.R1;.R2.))(12.(4.(34.(>.$7.$7.)(35.$7.$7.R14.(29.R>.R15.))(36.(>.$7.$7.)))R18.R1.)(12.(5.$6.R18.R1.)A2.R13.R2.R1.))))))(2>.R16.(2?.&5.(2.&40.))(30.&40.R?.)(30.&20.=)(31.(2.&40.))R15.(32.$6.)))P,PR',(19.&5.(2.&40.))PM',P,(2.&40.)(3.(2.&8.))Pmo',$=.P,A2.R14.R3.R2.P,(4.(34.(>.$7.$7.)(35.$7.$7.R16.(29.R10.R17.))(36.(>.$7.$7.)))R1:.R3.)P,(5.$6.R1;.R4.)P,(1?.(1<.(1=.(37.(2.&40.)R21.(38.R6.)))R20.)(39.R1?.(3:.(2.&5.)$?.$3;.R1:.)(23.(2.&40.)R21.))R6.)P,(20.$6.(1<.(1=.(37.(2.&40.)R22.(38.R7.)))R21.)R6.(3<.R1?.(3=.#0.)-800000.(29.+800000.R1:.)))P,A1.VK,R6.P,(16.R1>.R7.)(3>.$6.(3?.(40.$41.R:.(30.&40.R19.)R9.(32.$6.))R8.)R18.)(3>.$6.(3?.(40.$41.R18.(30.&40.R11.)R17.(32.$6.))R16.)R?.)")
(* [comment removed for export] *).
  Proof.
    intros vals ebs sr kn R M mo kept k0 lo Q pc pc' T E sp0 HR HK HKmo Hsv Hkv H0 SPlo SPhi K0 LO EV HC.
    pose proof (bv_unsigned_in_range 64 (vals_ev vals 0)) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR. subst sp0.
    change (mkst R (Z_to_bv 64 pc) M (seg_rom asegs)) with (MS R bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None M (seg_rom asegs)).
    eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HKmo | exact EV |].
    cbn beta. (intros ms' mo' dd_H; ddestruct dd_H as (R' & M' & -> & KEPT & MU & WM & HQ); intros HK' MM').
    change (MS R' bvmap_empty (Z_to_bv 64 pc') (Z_to_bv 32 0) None M' (seg_rom asegs)) with (mkst R' (Z_to_bv 64 pc') M' (seg_rom asegs)).
    apply HC; [exact HQ | exact MU | exact WM | | | exact HK' | exact MM'].
    - apply (regs_after_keeps vals ebs sr R R' kept Hsv HR KEPT H0).
    - set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
      assert (HKe : know_ok asegs E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (E0 : bv_unsigned (edenot E' (EVar 0)) = bv_unsigned (vals_ev vals 0)).
      { subst E'. cbn [edenot ev]. unfold vals_ev. destruct vals as [|v0 vs]; [vm_compute; reflexivity|reflexivity]. }
      eapply know_ok_frame; [exact HKe | | | ].
      + unfold flat, estart. cbn [a_base a_off]. rewrite E0. unfold AIMG_HI in SPlo. lia.
      + intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite E0 in Hx. apply MU. cbn [outside]. split; [lia | exact I].
      + eapply grows_of_munch_high; [exact MU | exact WM |]. cbn [outside]. intros x Hx. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem splice_rzJ : ltac2:(CDefT.buildp (gd_tbl_A_splice ()) "Pvals,(0.(2.&40.))Pebs,P,$?.(0.(2.&8.))Psr,(0.$17.)Pkn,(0.$18.)PR,(19.&5.(2.&40.))PM,P,(2.&40.)(3.(2.&8.))Pmo,$=.Pkept,(0.(2.&5.))Pk0,$7.Plo,$7.PQ,P,(19.&5.(2.&40.))P,P,(2.&40.)(3.(2.&8.))P,$=.SpPpc,$7.Ppc',$7.PT,$1:.ZE,$1;.(1<.(1=.R>.)R=.)Zsp0,$7.(1>.&40.(1=.R?.#0.))P,(1?.R2.R>.R<.)P,(20.$6.R3.R<.R>.)P,(13.$21.(22.(23.(2.&40.)R12.)R10.)$24.)P,(13.$21.(25.(23.(2.&40.)R13.)R10.)$24.)P,(8.(26.(2.&5.)(27.&5.=$28.)R=.))P,(:.(29.$;.+800000.)R6.)P,(:.(29.R7.R>.)(2:.+2.+40.))P,(:.-800000.R?.)P,(:.(2;.R9.+800000.)R?.)P,P,PR',(19.&5.(2.&40.))PM',P,(2.&40.)(3.(2.&8.))Pmo',$=.P,A3.R12.R3.R2.R1.P,Pr,(2.&5.)P,(26.(2.&5.)R1.R17.)(13.(2.&40.)(33.R6.R2.)(33.R1;.R2.))P,(4.(34.(>.$7.$7.)(35.$7.$7.R15.(29.R?.R16.))(36.(>.$7.$7.)))R19.R4.)P,(5.$6.R1:.R5.)(3>.$6.(3?.(2>.R7.(2?.&5.(2.&40.))(30.&40.R14.)(30.&20.=)(31.(2.&40.))R6.(32.$6.))R5.)R13.)(3>.$6.(3?.(2>.R16.(2?.&5.(2.&40.))(30.&40.R?.)(30.&20.=)(31.(2.&40.))R15.(32.$6.))R14.)R=.)P,PR',(19.&5.(2.&40.))PM',P,(2.&40.)(3.(2.&8.))Pmo',$=.P,A3.R13.R3.R2.R1.P,(4.(34.(>.$7.$7.)(35.$7.$7.R15.(29.R?.R16.))(36.(>.$7.$7.)))R19.R3.)P,(5.$6.R1:.R4.)P,(1?.(1<.(1=.(37.(2.&40.)R20.(38.R6.)))R1?.)(39.R1>.(3:.(2.&5.)$?.$3;.R19.)(23.(2.&40.)R20.))R6.)P,(20.$6.(1<.(1=.(37.(2.&40.)R21.(38.R7.)))R20.)R6.(3<.R1>.(3=.#0.)-800000.(29.+800000.R19.)))(3>.$6.(3?.(40.$41.R8.(30.&40.R16.)R7.(32.$6.))R6.)R15.)(3>.$6.(3?.(40.$41.R17.(30.&40.R10.)R16.(32.$6.))R15.)R>.)")
(* [comment removed for export] *).
  Proof.
    intros vals ebs sr kn R M mo kept k0 lo Q pc pc' T E sp0 HR HK Hsv Hkv H0 SPlo SPhi K0 LO CALL HC.
    pose proof (bv_unsigned_in_range 64 (vals_ev vals 0)) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR. subst sp0.
    change (mkst R (Z_to_bv 64 pc) M (seg_rom asegs)) with (MS R bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None M (seg_rom asegs)).
    apply CALL. intros R' M' mo' HQ KEPT MU WM.
    change (MS R' bvmap_empty (Z_to_bv 64 pc') (Z_to_bv 32 0) None M' (seg_rom asegs)) with (mkst R' (Z_to_bv 64 pc') M' (seg_rom asegs)).
    apply HC; [exact HQ | exact MU | exact WM | |].
    - apply (regs_after_keeps vals ebs sr R R' kept Hsv HR KEPT H0).
    - set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
      assert (HKe : know_ok asegs E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (E0 : bv_unsigned (edenot E' (EVar 0)) = bv_unsigned (vals_ev vals 0)).
      { subst E'. cbn [edenot ev]. unfold vals_ev. destruct vals as [|v0 vs]; [vm_compute; reflexivity|reflexivity]. }
      eapply know_ok_frame; [exact HKe | | | ].
      + unfold flat, estart. cbn [a_base a_off]. rewrite E0. unfold AIMG_HI in SPlo. lia.
      + intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite E0 in Hx. apply MU. cbn [outside]. split; [lia | exact I].
      + eapply grows_of_munch_high; [exact MU | exact WM |]. cbn [outside]. intros x Hx. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="K_halted K_mat"] Theorem splice_evtA2 : ltac2:(CDefT.buildp (gd_tbl_A_splice ()) "Pvals,(0.(2.&40.))Pebs,P,$?.(0.(2.&8.))Psr,(0.$17.)Pkn,(0.$18.)PR,(19.&5.(2.&40.))PM,P,(2.&40.)(3.(2.&8.))Pmo,$=.Pkept,(0.(2.&5.))Pk0,$7.Puk,$7.Pun,$7.Plo,$7.PQ,P,(19.&5.(2.&40.))P,P,(2.&40.)(3.(2.&8.))SpPpc,$7.Ppc',$7.PT,$1:.ZE,$1;.(1<.(1=.R10.)R?.)Zsp0,$7.(1>.&40.(1=.R11.#0.))P,(1?.R2.R10.R>.)P,(20.$6.R3.R>.R10.)P,A1.VK,R>.P,(13.$21.(22.(23.(2.&40.)R15.)R13.)$24.)P,(13.$21.(25.(23.(2.&40.)R16.)R13.)$24.)P,(8.(26.(2.&5.)(27.&5.=$28.)R10.))P,(:.(29.$;.+800000.)R7.)P,(:.(29.R8.R11.)(2:.+2.+40.))P,(:.-800000.R12.)P,(:.R13.R12.)P,(:.=R12.)P,(42.(29.(29.R<.R14.)R13.)(2:.+2.+40.))P,(:.(2;.R=.+800000.)R13.)P,(2<.$6.VAL,VCS,Lms',$2=.(11.(19.&5.(2.&40.))LR',(19.&5.(2.&40.))(11.P,(2.&40.)(3.(2.&8.))LM',P,(2.&40.)(3.(2.&8.))(12.(13.$2=.R3.(2>.R2.(2?.&5.(2.&40.))(30.&40.R14.)(30.&20.=)(31.(2.&40.))R1.(32.$6.)))(12.Pr,(2.&5.)P,(26.(2.&5.)R1.R1<.)(13.(2.&40.)(33.R4.R2.)(33.R20.R2.))(12.(4.(34.(>.$7.$7.)(35.$7.$7.(29.R11.R19.)(29.(29.R11.R19.)R18.))(34.(>.$7.$7.)(35.$7.$7.R17.(29.R11.R1:.))(36.(>.$7.$7.))))R1=.R1.)(12.(5.$6.R1=.R1.)A2.R16.R2.R1.))))))(2>.R1;.(2?.&5.(2.&40.))(30.&40.R12.)(30.&20.=)(31.(2.&40.))R1:.(32.$6.)))P,PR',(19.&5.(2.&40.))PM',P,(2.&40.)(3.(2.&8.))Pmo',$=.P,A2.R17.R3.R2.P,(4.(34.(>.$7.$7.)(35.$7.$7.(29.R13.R1;.)(29.(29.R13.R1;.)R1:.))(34.(>.$7.$7.)(35.$7.$7.R19.(29.R13.R1<.))(36.(>.$7.$7.))))R1?.R3.)P,(5.$6.R20.R4.)P,(1?.(1<.(1=.(37.(2.&40.)R26.(38.R6.)))R25.)(39.R24.(3:.(2.&5.)$?.$3;.R1?.)(23.(2.&40.)R26.))R6.)P,(20.$6.(1<.(1=.(37.(2.&40.)R27.(38.R7.)))R26.)R6.(3<.(3<.R24.(3=.#0.)R1>.R1=.)(3=.#0.)-800000.(29.+800000.R1?.)))P,A1.VK,R6.P,(16.R23.R7.)(3>.$6.(3?.(40.$41.R:.(30.&40.R1<.)R9.(32.$6.))R8.)R1;.)(3>.$6.(3?.(40.$41.R1=.(30.&40.R14.)R1<.(32.$6.))R1;.)R12.)")
(* [comment removed for export] *).
  Proof.
    intros vals ebs sr kn R M mo kept k0 uk un lo Q pc pc' T E sp0 HR HK HKmo Hsv Hkv H0 SPlo SPhi K0 UK UN UH LO EV HC.
    pose proof (bv_unsigned_in_range 64 (vals_ev vals 0)) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR. subst sp0.
    change (mkst R (Z_to_bv 64 pc) M (seg_rom asegs)) with (MS R bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None M (seg_rom asegs)).
    eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HKmo | exact EV |].
    cbn beta. (intros ms' mo' dd_H; ddestruct dd_H as (R' & M' & -> & KEPT & MU & WM & HQ); intros HK' MM').
    change (MS R' bvmap_empty (Z_to_bv 64 pc') (Z_to_bv 32 0) None M' (seg_rom asegs)) with (mkst R' (Z_to_bv 64 pc') M' (seg_rom asegs)).
    apply HC; [exact HQ | exact MU | exact WM | | | exact HK' | exact MM'].
    - apply (regs_after_keeps vals ebs sr R R' kept Hsv HR KEPT H0).
    - set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
      set (b0 := bv_unsigned (vals_ev vals 0)) in *.
      assert (HKe : know_ok asegs E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (E0 : bv_unsigned (edenot E' (EVar 0)) = b0).
      { subst E' b0. cbn [edenot ev]. unfold vals_ev. destruct vals as [|v0 vs]; [vm_compute; reflexivity|reflexivity]. }
      assert (GR : mem_grows M M').
      { eapply grows_of_munch_high; [exact MU | exact WM |]. cbn [outside]. intros x Hx. lia. }
      (* [comment removed for export] *)
      set (M1 := fun x : word => if ((b0 + uk <=? bv_unsigned x) && (bv_unsigned x <? b0 + uk + un))%bool then M' x else M x).
      assert (HK1 : know_ok asegs E' M1 (kn_frame kn (EVar 0) uk un)).
      { eapply know_ok_frame; [exact HKe | | |].
        - unfold flat, estart. cbn [a_base a_off]. rewrite E0. unfold AIMG_HI in SPlo. lia.
        - intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite E0 in Hx. subst M1. cbn beta.
          destruct (Z.leb_spec0 (b0 + uk) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (b0 + uk + un)); cbn [andb]; first [lia | reflexivity].
        - intros x Hx. subst M1. cbn beta. destruct (_ && _)%bool; [apply GR; exact Hx | exact Hx]. }
      eapply know_ok_frame; [exact HK1 | | |].
      + unfold flat, estart. cbn [a_base a_off]. rewrite E0. unfold AIMG_HI in SPlo. lia.
      + intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite E0 in Hx. subst M1. cbn beta.
        destruct (Z.leb_spec0 (b0 + uk) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (b0 + uk + un)); cbn [andb]; try reflexivity.
        all: apply MU; cbn [outside]; repeat split; lia.
      + intros x Hx. subst M1. cbn beta in Hx. destruct (_ && _)%bool; [exact Hx | apply GR; exact Hx].
  Qed.
End WithK.
