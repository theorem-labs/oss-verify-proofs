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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_free_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_get_meta.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_free_B () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.bit"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_last_idx"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mask_upto"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rftriv_post"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "Corelib.Init.Logic.or"].


Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rfree_fp_meta0 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_B ()) "Pst,$0.Pst0,$0.Pm,P,(1.&40.)(2.(1.&8.))Plo,$3.Psp,$3.Pq,$4.Pa,$3.P,(5.VhRP,R7.R5.)P,(6.R8.R3.)P,(7.(8.$9.$:.$;.$<.)(=.R8.)(=.R9.))P,(>.(?.(10.R:.R5.)R4.)(11.R4.(12.(10.R:.R5.)+28.)))(13.R:.R8.R7.R5.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros st st0 m lo sp q a MR dd_H; ddestruct dd_H as (ar & arr & k & Har & Hk & Eq); intros ER Ha). pose proof MR as (WF & _).
  ddestruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed.

(* [comment removed for export] *)
Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_B ()) "Lms',$14.(15.(1.&40.)Lt0,(1.&40.)(15.(1.&40.)Lt1,(1.&40.)(15.(1.&40.)Lt2,(1.&40.)(15.(1.&40.)La0,(1.&40.)(15.(1.&40.)La1,(1.&40.)(15.(1.&40.)La2,(1.&40.)(15.(1.&40.)La3,(1.&40.)(15.(1.&40.)La4,(1.&40.)(15.(1.&40.)La5,(1.&40.)(15.(1.&40.)La6,(1.&40.)(15.(1.&40.)La7,(1.&40.)(15.(1.&40.)Lt3,(1.&40.)(15.(1.&40.)Lt4,(1.&40.)(15.(1.&40.)Lt5,(1.&40.)(15.(1.&40.)Lt6,(1.&40.)(15.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(>.(7.$14.R11.(16.(17.O16.O15.O14.O13.R10.R?.R>.O12.O11.R=.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(18.O16.)O5.(19.(1.&40.))R1.(1:.$1;.)))(>.(1<.O3.O2.R1.)(>.(1=.$1;.O2.R1.)(>.(1>.$1;.R1.)(>.(1?.$1;.R1.O4.(20.&40.O15.))(5.VhRP,O1.R1.))))))))))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rfree_triv : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_B ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Px1,(1.&40.)PF,(21.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Pjunk,(22.(1.&8.))Plo,$3.Pst0,$0.Pst,$0.Pg,$4.Pidx,$3.Zmr,$23.(24.R3.R2.)Zst',$0.(25.R3.(26.(12.(27.R1.)(28.R2.)))R4.)P,(5.VhRP,R5.R9.)P,(1>.$1;.R:.)P,(6.R7.R6.)P,(7.(8.$9.$:.$;.$<.)(=.R8.)(=.R9.))P,(7.(8.$4.(29.$9.$:.$3.$2:.)(2;.$9.$:.$;.$3.$2:.$2<.)$2=.)(2>.R9.)(2>.R:.))P,(>.(?.=(27.R7.))(11.(27.R7.)(2?.+2.+20.)))P,(>.(?.=(30.R8.))(11.(30.R8.)(2?.+2.+20.)))P,(>.(?.=(31.R9.))(11.(31.R9.)+20.))P,(>.(?.=R;.)(?.R;.(31.R:.)))P,(7.$32.(33.(27.R;.)R<.)$34.)P,(7.$32.(33.(30.R<.)R=.)$34.)P,(35.(7.$3.(27.R=.)=))P,(35.(7.$3.(12.(36.(27.R>.)(30.R>.))(28.R?.))(37.(31.R>.))))P,(38.$1;.R16.(12.(20.&40.R33.)-30.)(39.$3:.(3;.#8.R15.)(39.$3:.(3<.R26.)(39.$3:.(3<.R27.)(39.$3:.(3<.R2<.)(39.$3:.(3<.R2=.)(39.$3:.(3<.R34.)(3=.$3:.))))))))P,(1?.$1;.R17.R15.(12.(20.&40.R34.)-30.))P,(?.(3>.VhRP,)R16.)P,(?.R17.(3?.(20.&40.R36.)+30.))(40.$1;.(41.R38.R37.R36.R35.R31.R30.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1<.R1;.R18.(13.R17.R18.(20.&40.R37.))R1:.R12.)(16.(17.R1=.(42.&40.(12.(20.&40.R37.)-30.))R36.R35.R34.R33.R32.(42.&40.R14.)R2?.(43.(10.R16.R15.))(42.&40.(12.(10.R16.R15.)+1<.))(43.(44.(2?.+2.R14.)))(43.(44.(3?.(2?.+2.(12.(31.R13.)+1.))+1.)))(42.&40.+7<<=<.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1<.(42.&40.+3?<>0.)R1;.(19.(1.&40.))R1:.(1:.$1;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
  pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  clearbody gw.
  dpose MR as (WF & CX & GL & AR & GR & SH). ddestruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  rceilb; unfold RNEED_LOCKS in *.
  (* [comment removed for export] *)
  step. step. rewrite !sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
  (* [comment removed for export] *)
  step. if_true.
  (* [comment removed for export] *)
  st1.
  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2.
  { exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
  clear K2.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
  pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
  step. if_cases K3; zify_cond K3.
  { exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
  clear K3 RSUM.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
  rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
  step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
  clear K4 RL.
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (MR' : rmrep st' mX) end.
  { unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
    rewrite HG in MM.
    eapply rw_cells_congr; [ | | | exact MM].
    - unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
      unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
    - reflexivity.
    - cbn. tauto. }
  clear MUg MM.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
    pose proof (wmono_refl rsegs mX) as WMs end.
  step. step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  clear MR' MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply rfree_fp_stack. lia.
      - intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
  finish.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rfree_tocall : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_B ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Px1,(1.&40.)PF,(21.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Pst,$0.Pg,$4.Pidx,$3.Zmr,$23.(24.R3.R2.)P,(5.VhRP,R4.R5.)P,(1>.$1;.R6.)P,(6.R6.R5.)P,(>.(?.=(27.R4.))(11.(27.R4.)(2?.+2.+20.)))P,(>.(?.=(30.R5.))(11.(30.R5.)(2?.+2.+20.)))P,(>.(?.=(31.R6.))(11.(31.R6.)+20.))P,(>.(?.=R8.)(?.R8.(31.R7.)))P,(7.$32.(33.(27.R8.)R9.)$34.)P,(7.$32.(33.(30.R9.)R:.)$34.)P,(45.(7.$3.(27.R:.)=)(7.$3.(12.(36.(27.R:.)(30.R:.))(28.R;.))(37.(31.R:.))))(40.$1;.Lms',$14.(15.(1.&40.)Lx2,(1.&40.)(15.(1.&40.)Lx3,(1.&40.)(15.(1.&40.)Lx4,(1.&40.)(15.(1.&40.)Lx5,(1.&40.)(15.(1.&40.)Lx6,(1.&40.)(15.(1.&40.)Lx7,(1.&40.)(7.$14.R7.(16.(17.(42.&40.+3?=50.)(42.&40.(12.(20.&40.R33.)-30.))R32.R31.R30.R2?.R2>.(42.&40.R13.)R2;.(42.&40.(10.R15.R14.))(42.&40.R13.)R6.R5.R4.R3.R2.R1.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R18.(42.&40.+3?>;8.)R17.(19.(1.&40.))R16.(1:.$1;.)))))))))(16.(17.R12.(42.&40.(12.(20.&40.R2<.)-30.))R2;.R2:.R29.R28.R27.(42.&40.R<.)R24.(43.(10.R>.R=.))(42.&40.(12.(10.R>.R=.)+1<.))(43.(44.(2?.+2.R<.)))(43.(44.(3?.(2?.+2.(12.(31.R;.)+1.))+1.)))(42.&40.+7<<=<.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R11.(42.&40.+3?<>0.)R10.(19.(1.&40.))R?.(1:.$1;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  clearbody gw.
  dpose MR as (WF & CX & GL & AR & GR & SH). ddestruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  rceilb; unfold RNEED_LOCKS in *.
  (* [comment removed for export] *)
  step. step. rewrite !sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
  (* [comment removed for export] *)
  step. if_true. st1.
  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
    st1. st1.
    apply evt_done. deexists 6. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
    rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
    rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
    pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
    step. if_cases K3; zify_cond K3.
    + st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
      st1. st1.
      apply evt_done. deexists 6. reflexivity.
    + exfalso. destruct HNT as [Hz|Hall].
      * apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
      * apply K3. rewrite ?wz_unsigned by apply sxv_range.
        apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
        unfold bit, mask_upto in Hall. exact Hall.
Qed.

End RP_1.
