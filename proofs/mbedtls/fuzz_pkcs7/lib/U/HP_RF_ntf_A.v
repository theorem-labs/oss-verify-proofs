(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocModel_B F_ntf_A F_ntf_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_ntf_A () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "rntf_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.ivs_covered"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rntf_ret_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.MallocModel_B.aor_st"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Heap.F_ntf_B.fm_facts"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.fm_st"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
  [CB 48 junk; C8 (wz rp_canary); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)

(* [comment removed for export] *)
End RP_1.
Ltac rmeta_open cq MUq WMq :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
    pose proof (wmono_refl rsegs mX) as WMq end.

(* [comment removed for export] *)
Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
    clear MUq WMq CH end.

(* [comment removed for export] *)
Ltac rmeta_chunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
  rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

(* [comment removed for export] *)
Section RP_2. Context {hRP : run_params}.
#[using="Type"] Lemma rntf_ret : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_A ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))PW,(3.(4.$5.$5.))Pjunk,(3.(0.&8.))Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Pst,$6.Pst',$6.Plo,$5.P,(7.VhRP,R2.R;.)P,(8.$9.R<.)P,(:.(0.&40.)R27.(;.&40.$<.))P,(=.$9.R>.(>.(?.&40.R2?.)-60.)(10.VhRP,R<.R7.R8.R9.R:.R;.))P,(11.$9.R?.R5.(>.(?.&40.R30.)-60.))P,(12.(13.VhRP,)R6.)P,(12.R7.(14.(?.&40.R32.)+60.))P,(15.(16.(4.$5.$5.)(17.$5.$5.(14.(?.&40.R33.)+60.)(?.&40.R33.))R11.)R13.R12.)P,(18.$9.R14.R13.)P,(19.(1:.R<.R:.(?.&40.R35.))R13.)(1;.$9.(1<.VhRP,R12.R36.R35.R34.R11.R10.R?.R>.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R;.R=.R16.R<.R2<.R2=.)(1=.(1>.R37.(;.&40.(>.(?.&40.R36.)-60.))R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(;.&40.+40260.)R17.(1?.(0.&40.))R15.(20.$9.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  rceilb; unfold RSSP_GUARD, rntf_frame in *. subst s1.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  clear MR' MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
  finish.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rntf_aor : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_A ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Pst,$6.Pg,$21.Pi,$5.Plo,$5.P,(7.VhRP,R4.R;.)P,(8.$9.R<.)P,(22.R6.R5.)P,(:.(0.&40.)R24.(23.(24.(25.+2.R5.))))P,(26.(12.=R6.)(27.R6.+20.))P,(:.(0.&40.)R28.(;.&40.$<.))P,(26.(12.=(28.(29.R:.R9.)))(27.(28.(29.R:.R9.))(25.+2.+20.)))P,(=.$9.R12.(>.(?.&40.R31.)-60.)(10.VhRP,R11.R<.R=.R>.R?.R10.))P,(11.$9.R13.R9.(>.(?.&40.R32.)-60.))P,(12.(13.VhRP,)R:.)P,(12.R;.(14.(?.&40.R34.)+60.))(1;.$9.(1<.VhRP,R14.R35.R34.R33.R13.R12.R11.R10.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R<.R?.R16.(2:.R?.R>.R=.)(23.=)(23.=))(1=.(1>.R36.(;.&40.(>.(?.&40.R35.)-60.))R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.(;.&40.(>.(2;.R?.R>.)+1<.))R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(;.&40.+40238.)R17.(1?.(0.&40.))R16.(20.$9.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
  pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & _). pose proof MSL as MS0. ddestruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
  ddestruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
  assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
  rceilb; unfold NSLOTS in *.
  assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
  set (mr := get_meta_rec st g) in *.
  pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
  { apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. lia. }
  subst a1.
  st1. rewrite sx32_wz_sxv by lia. st1.
  amo_step AMO. rewrite ?sx32_wz_sxv by lia.
  st1. if_false.
  amo_step AMO.
  st1. if_false.
  st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (MR' : rmrep (aor_st st g i) mX) end.
  { unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
    eapply rw_cells_congr; [ | | | exact MM].
    - unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
      rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
      rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
      split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
    - reflexivity.
    - cbn. tauto. }
  clear MUg MM.
  (* [comment removed for export] *)
  st1. st1.
  eapply rntf_ret; [exact MR' | assumption | exact S1 | exact FR | exact ST | rceilb; lia | lia | exact MU | exact WM |].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [exact MR | exact MSL | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rntf_frame_remerge : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_A ()) "Pm,P,(0.&40.)(2.(0.&8.))PA,$5.Pj0,(3.(0.&8.))Pz1,(0.&40.)Pz2,(0.&40.)Pz3,(0.&40.)Pz4,(0.&40.)Pz5,(0.&40.)Prest,(3.$2<.)P,(=.$9.R9.R8.(16.$2<.(2=.#8.R7.)(16.$2<.(2>.R6.)(16.$2<.(2>.R5.)(16.$2<.(2>.R4.)(16.$2<.(2>.R3.)(16.$2<.(2>.R2.)R1.)))))))(=.$9.R:.R9.(16.$2<.(2=.#30.(2?.(0.&8.)R8.(2?.(0.&8.)(30.R7.)(2?.(0.&8.)(30.R6.)(2?.(0.&8.)(30.R5.)(2?.(0.&8.)(30.R4.)(30.R3.)))))))R2.))")
(* [comment removed for export] *).
Proof.
  intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
  eapply rw_cells_congr; [| | | exact H].
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
  - reflexivity.
  - split; [| ddestruct WFr as (_ & _ & _ & _ & _ & X); exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rntf_fm : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_A ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Pst,$6.Pg,$21.Plo,$5.P,(7.VhRP,R3.R:.)P,(8.$9.R;.)P,(22.R5.R4.)P,(31.R6.R5.)P,(:.(0.&40.)R25.(;.&40.$<.))P,(=.$9.R?.(>.(?.&40.R2=.)-60.)(10.VhRP,R>.R9.R:.R;.R<.R=.))P,(11.$9.R10.R7.(>.(?.&40.R2>.)-60.))P,(12.(13.VhRP,)R8.)P,(12.R9.(14.(?.&40.R30.)+60.))(1;.$9.(1<.VhRP,R11.R31.R30.R2?.R10.R?.R>.R=.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R:.R<.R13.(32.R<.R;.)R28.R29.)(1=.(1>.R32.(;.&40.(>.(?.&40.R31.)-60.))R30.R2?.R2>.R2=.R2<.R2;.R2:.(;.&40.(2;.R<.R;.))R29.R28.R27.R26.R25.R24.R23.(;.&40.$33.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(;.&40.+4019<.)R14.(1?.(0.&40.))R13.(20.$9.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros MR MI MSL FMF S1 FR ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  dpose FR as [[[LJ _] _] _]. cbn in LJ.
  rceilb; unfold RCTX, rntf_frame in *.
  rmeta_chunk MR MSL CH.
  (* [comment removed for export] *)
  dpose MR as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRf : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  clear MUs.
  (* [comment removed for export] *)
  rmeta_open (conc st g) MUg WMg.
  st1. st1. (* [comment removed for export] *)
  st1. st1. (* [comment removed for export] *)
  st1. st1. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
    assert (CH' : rw_cells rsegs mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
      by (eapply rw_cells_congr; [ | | | exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; tauto]);
    clear CH; rename CH' into CH
  end end.
  st1. st1. (* [comment removed for export] *)
  st1. st1. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
    assert (CH' : rw_cells rsegs mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
      by (eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
    clear CH; rename CH' into CH
  end end.
  rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
  set (st0 := put_meta g meta0 st) in MR0.
  assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; exact MSL).
  (* [comment removed for export] *)
  rmeta_chunk MR0 MSL0 CH0.
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  clear CH0 K1 K2.
  (* [comment removed for export] *)
  st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
  - (* [comment removed for export] *)
    ddestruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
    pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
    unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    (* [comment removed for export] *)
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR0 MSL0 CH.
    st1.
    rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
    set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
    assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
    assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
    assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
    (* [comment removed for export] *)
    rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by exact NEh.
    unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
    st1.
    clear CHh.
    (* [comment removed for export] *)
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MRa MSga CH.
    st1.
    rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
    unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
    set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
    assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
    assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
    assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
    (* [comment removed for export] *)
    munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
    st1.
    rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
    set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
    assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
    (* [comment removed for export] *)
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st head) MUh WMh.
    rmeta_chunk MR2 MSh2 CH.
    st1.
    rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
    assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
    { unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
      rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
      rewrite get_meta_rec_put_same.
      rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
      reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
    eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | rceilb; lia | lia | exact MU | exact WM |].
    cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
    + eapply rfree_fp_meta; [exact MR | exact MSh | lia].
    + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
    + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
    + apply rfree_fp_ctx. unfold RCTX. lia.
  - (* [comment removed for export] *)
    unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR0 MSL0 CH.
    st1. st1.
    rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
    set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.
    (* [comment removed for export] *)
    clear C1. dpose MRb as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1. rewrite FMH in C1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
    { eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        unfold pw at 4. cbn [oconc]. unfold wz at 4. exact C1.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
    { unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
    eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | rceilb; lia | lia | exact MU | exact WM |].
    cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
    + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
    + apply rfree_fp_ctx. unfold RCTX. lia.
Qed.

End RP_2.
