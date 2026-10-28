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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B F_ntf_C MallocKit_B MallocKit_B3 F_am_A F_am_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_ntf_A HP_RF_ntf_C HP_RF_am_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
  cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
       c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_am_D () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_free_meta_head"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_next"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_prev"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_ret_post"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.dequeue"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.LFree"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_count"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_A.am_took"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma ram_deq : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_D ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Ps4o,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Plo,$4.Pst,$5.Ph,$6.Pnx,$6.Ppv,$6.P,(7.VhRP,R4.R7.)P,(8.$9.R8.)P,(:.$;.(<.(=.R6.))(>.$6.R5.))P,(?.R7.R6.)P,(:.$;.(10.(11.R8.R7.))(>.$6.R6.))P,(:.$;.(12.(11.R9.R8.))(>.$6.R6.))P,(?.R:.R8.)P,(?.R;.R8.)P,(13.(:.$6.R:.R;.)(:.$6.R9.R;.))P,(14.$9.R10.(15.(16.&40.R35.)-40.)(17.VhRP,R?.R13.R14.R15.R16.R17.R18.))P,(18.$9.R11.R?.(15.(16.&40.R36.)-40.))P,(19.(1:.VhRP,)R10.)P,(19.R11.(1;.(16.&40.R38.)+40.))(1<.$9.(1=.VhRP,R1<.R39.R38.R37.R1;.R1:.R19.R18.R17.R28.R27.R26.R25.R24.R23.R22.R16.R15.R12.R11.R14.(1>.$1?.R10.R11.)(20.&40.(21.R11.R10.)))(22.(23.R1=.(20.&40.(15.(16.&40.R39.)-40.))R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.(20.&40.$24.)(20.&40.$25.)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R16.(20.&40.+40344.)R15.(26.(0.&40.))R14.(27.$9.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _).
  dpose (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _).
  dpose (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _).
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH in C1.
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (512968, 512968 + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
  st1. clear CH.
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (Enx : nx = h).
    { rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
    { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells rsegs ?mX 512968 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 512816) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
        [exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | rceilb; lia | lia].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    deexists 15. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
  - (* [comment removed for export] *)
    assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
    assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).
    (* [comment removed for export] *)
    rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR MSp CH.
    st1.
    rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
    set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
    (* [comment removed for export] *)
    rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st nx) MUn WMn.
    rmeta_chunk MR1 MSn1 CH.
    st1.
    rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
    set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    (* [comment removed for export] *)
    st1. st1.
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    (* [comment removed for export] *)
    rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    clear C1. dpose MR2 as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
    replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
    { eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
        unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells rsegs ?mX 512968 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    (* [comment removed for export] *)
    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
      rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 512816) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
        [exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | rceilb; lia | lia].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    deexists 15. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_take_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_D ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Ps4o,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Plo,$4.Pst,$5.Pq,$6.P,(7.VhRP,R2.R5.)P,(8.$9.R6.)P,(:.$;.(<.(=.R4.))(26.$6.))P,(28.(:.$4.(29.(=.R5.))=))P,(2:.(19.=(29.(=.R6.)))(2;.(29.(=.R6.))(2<.+2.+40.)))P,(:.$;.(2=.(=.R7.))(>.$6.R6.))P,(?.R8.R7.)P,(14.$9.R<.(15.(16.&40.R31.)-40.)(17.VhRP,R;.R?.R10.R11.R12.R13.R14.))P,(18.$9.R=.R;.(15.(16.&40.R32.)-40.))P,(19.(1:.VhRP,)R<.)P,(19.R=.(1;.(16.&40.R34.)+40.))(1<.$9.(1=.VhRP,R18.R35.R34.R33.R17.R16.R15.R14.R13.R24.R23.R22.R21.R20.R1?.R1>.R12.R11.R>.R=.R10.(2>.R=.R<.(1;.(29.(=.R=.))+1.))(20.&40.(21.R=.R<.)))(22.(23.R19.(20.&40.(15.(16.&40.R35.)-40.))R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.(20.&40.$24.)(20.&40.$25.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R12.(20.&40.+40344.)R11.(26.(0.&40.))R10.(27.$9.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _).
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, AVM in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1.
  rewrite bv_eqb_refl. cbv iota.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
  rewrite CF; clear CF.
  st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
  replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
  change (Z_to_bv 64 512816) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 512960) with (Z_to_bv 64 RMLOCK).
  eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
    [exact MR | exact MI | exact MSq | lia | exact FR | exact ST | rceilb; lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_disp0 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_D ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pst,$5.P,(7.VhRP,R1.R2.)P,(:.$;.(<.(=.R2.))(26.$6.))P,(:.$4.(29.(=.R3.))=)(1<.$9.Lms',$2?.(:.$2?.R1.(22.(23.R9.R26.R25.R24.R23.R22.R21.R20.R1?.(20.&40.=)(20.&40.=)R1<.R1;.R1:.R19.R18.R17.R16.(20.&40.$25.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R8.(20.&40.+40398.)R7.(26.(0.&40.))R6.(27.$9.)))(22.(23.R8.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(20.&40.$25.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R7.(20.&40.+40344.)R6.(26.(0.&40.))R5.(27.$9.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until st. intros MR FMH CNT.
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, CNT in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

End RP_1.
