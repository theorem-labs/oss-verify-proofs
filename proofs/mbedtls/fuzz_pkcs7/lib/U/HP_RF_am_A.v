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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_ntf_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_am_A () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RP_1.ram_fp"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rregions_wf"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RP_1.ram_frame"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.ram_ret_post"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.MallocModel_B.clr_links"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_A.am_took"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"].


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "(0.(1.(2.O3.O1.)(3.O1.O2.))(0.(1.(2.$4.O1.)(3.O1.(5.$4.+3:0.)))(6.$7.Lrid,$7.(6.$8.Lr,$8.(1.(9.(:.$8.)(;.$7.$8.(<.$7.$=.$>.$8.)(?.$7.$=.$>.$8.)R2.(10.O4.))(11.$8.R1.))(1.(12.(9.$13.(14.R1.)$15.))(1.(2.(16.R1.)O1.)(3.O1.(5.(17.R1.)(18.(19.R1.)))))))))))")
(* [comment removed for export] *).

#[using="hRP"] Lemma ram_fp_alloc_fp st lo sp a : ram_fp st lo sp a -> ralloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. rceilb. unfold ram_fp, ralloc_fp. tauto. Qed.
#[using="hRP"] Lemma ram_fp_stack st lo sp a : lo <= a < sp -> ram_fp st lo sp a.
Proof. rceilb. intros; left; assumption. Qed.
#[using="hRP"] Lemma ram_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> ram_fp st lo sp a.
Proof. rceilb. intros; right; left; assumption. Qed.
#[using="hRP"] Lemma ram_fp_region st lo sp a rid r : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "P,(9.(:.$8.)(;.$7.$8.(<.$7.$=.$>.$8.)(?.$7.$=.$>.$8.)O2.(10.O6.))(11.$8.O1.))P,(12.(9.$13.(14.O1.)$15.))P,(1.(2.(16.O1.)O3.)(3.O3.(5.(17.O1.)(18.(19.O1.)))))(1:.O6.O5.O4.O3.)")
(* [comment removed for export] *).
Proof. rceilb. intros; right; right. dexists rid, r. auto. Qed.
#[using="Type"] Lemma ram_fp_not_errno st lo sp a : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "P,(1:.O4.O3.O2.O1.)P,(1;.VhRP,O4.)P,(2.(1<.VhRP,)O3.)(12.(1.(2.(5.(1=.&40.(1>.&40.+5=0<8.))-:4.)O1.)(3.O1.(5.(5.(1=.&40.(1>.&40.+5=0<8.))-:4.)+4.))))")
(* [comment removed for export] *).
Proof. rceilb.
  (intros [H|[H|(rid & r & Hr & _ & H)]] dd_H; ddestruct dd_H as (_ & WR & _); intros LO); rceilb; unfold RCTX in *; rewrite ?unsigned_lit by lia; try lia.
  destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2).
  pose proof (lr_lo_ge r). rceilb. lia.
Qed.
#[using="Type"] Lemma ram_fp_meta : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "Pst,$1?.Pm,P,(20.&40.)(:.(20.&8.))Plo,$21.Psp,$21.Pq,$22.Pa,$21.P,(23.VhRP,R6.R5.)P,(24.R7.R3.)P,(1.(2.(25.R8.R4.)R3.)(3.R3.(5.(25.R8.R4.)+28.)))(1:.R9.R7.R6.R4.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros st m lo sp q a MR dd_H; ddestruct dd_H as (ar & arr & k & Har & Hk & Eq); intros Ha). pose proof MR as (WF & _).
  ddestruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ram_fp_area : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "Pst,$1?.Pm,P,(20.&40.)(:.(20.&8.))Plo,$21.Psp,$21.Pak,$22.Par,$26.Pa,$21.P,(23.VhRP,R7.R6.)P,(9.(:.$26.)(;.$22.$26.(<.$22.(27.$7.$=.$21.$28.)(29.$7.$=.$>.$21.$28.$2:.)$26.)(?.$22.(27.$7.$=.$21.$28.)(29.$7.$=.$>.$21.$28.$2:.)$26.)R4.(2;.R8.))(11.$26.R3.))P,(1.(2.(25.R9.R5.)R3.)(3.R3.(5.(25.R9.R5.)+1000.)))(1:.R:.R8.R7.R4.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
  ddestruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
  eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
#[using="hRP"] Lemma ram_fp_same st st' lo sp a : s_regions st' = s_regions st -> ram_fp st' lo sp a <-> ram_fp st lo sp a.
Proof. rceilb. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.

(* [comment removed for export] *)
Definition ram_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "Lms',$2<.(6.(20.&40.)Lt0,(20.&40.)(6.(20.&40.)Lt1,(20.&40.)(6.(20.&40.)Lt2,(20.&40.)(6.(20.&40.)La1,(20.&40.)(6.(20.&40.)La2,(20.&40.)(6.(20.&40.)La3,(20.&40.)(6.(20.&40.)La4,(20.&40.)(6.(20.&40.)La5,(20.&40.)(6.(20.&40.)La6,(20.&40.)(6.(20.&40.)La7,(20.&40.)(6.(20.&40.)Lt3,(20.&40.)(6.(20.&40.)Lt4,(20.&40.)(6.(20.&40.)Lt5,(20.&40.)(6.(20.&40.)Lt6,(20.&40.)(6.P,(20.&40.)(:.(20.&8.))Lm',P,(20.&40.)(:.(20.&8.))(1.(9.$2<.R10.(2=.(2>.O17.O16.O15.O14.R?.R>.R=.O13.O12.O1.R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(2?.O17.)O6.(30.(20.&40.))R1.(31.$32.)))(1.(33.(1:.O4.O5.(1=.&40.O16.))O3.R1.)(1.(34.$32.O3.R1.)(1.(35.$32.R1.)(1.(36.$32.R1.O5.(1=.&40.O16.))(23.VhRP,O2.R1.)))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 junk; C8 (wz rp_canary); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_tail : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "Psp,(20.&40.)Pgp,(20.&40.)Ptp,(20.&40.)Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Ps0,(20.&40.)Ps1,(20.&40.)Pa1,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Ps3,(20.&40.)Ps4,(20.&40.)Ps5,(20.&40.)Ps6,(20.&40.)Ps7,(20.&40.)Ps8,(20.&40.)Ps9,(20.&40.)Ps10,(20.&40.)Ps11,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)Px1,(20.&40.)Praw,(20.&40.)Ps0o,(20.&40.)Ps1o,(20.&40.)Ps2o,(20.&40.)Ps3o,(20.&40.)Ps4o,(20.&40.)PF,(37.&5.(20.&40.))Pfc,(20.&20.)Pm,P,(20.&40.)(:.(20.&8.))Pjunk,(38.(20.&8.))Plo,$21.Pst,$1?.Pq,$22.P,(23.VhRP,R2.R5.)P,(35.$32.R6.)P,(24.R4.R3.)P,(39.$32.R8.(5.(1=.&40.R2=.)-40.)(3:.R7.R;.R<.R=.R>.R?.R10.))P,(36.$32.R9.R7.(5.(1=.&40.R2>.)-40.))P,(2.(1<.VhRP,)R8.)P,(2.R9.(3;.(1=.&40.R30.)+40.))(3<.$32.(3=.R14.R31.R30.R2?.R13.R12.R11.R10.R?.R20.R1?.R1>.R1=.R1<.R1;.R1:.R>.R=.R:.R9.R<.(3>.R8.$3?.R9.)(1>.&40.(25.R9.R8.)))(2=.(2>.R15.(1>.&40.(5.(1=.&40.R31.)-40.))R30.R2?.R2>.R2=.R2<.R2;.R2:.(1>.&40.(25.R9.R8.))R29.R28.R27.R26.R25.R24.R23.(1>.&40.$40.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R>.(1>.&40.+40504.)R=.(30.(20.&40.))R<.(31.$32.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until q. intros MR MI MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  dpose MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  rmeta_chunk MR MSq CH.
  rceilb; unfold RSSP_GUARD, ram_frame in *.
  rmeta_open (conc st q) MUq WMq.
  (* [comment removed for export] *)
  st1. st1.
  rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
  rewrite <- upd_meta_put in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl rsegs mX) as WMs end.
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : rmrep (upd_meta q clr_links st) mX)
      by (eapply rmrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply ram_fp_stack. lia.
      - intros x Hx. eapply ram_fp_meta; [exact MR | exact MSq | lia]. }
  apply evt_done. unfold ram_ret_post. deexists 15.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_b0 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_A ()) "Psp,(20.&40.)Pgp,(20.&40.)Ptp,(20.&40.)Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Ps0,(20.&40.)Ps1,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Ps4,(20.&40.)Ps5,(20.&40.)Ps6,(20.&40.)Ps7,(20.&40.)Ps8,(20.&40.)Ps9,(20.&40.)Ps10,(20.&40.)Ps11,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)Px1,(20.&40.)Praw,(20.&40.)Ps0o,(20.&40.)Ps1o,(20.&40.)Ps2o,(20.&40.)Ps3o,(20.&40.)Ps4o,(20.&40.)PF,(37.&5.(20.&40.))Pfc,(20.&20.)Pm,P,(20.&40.)(:.(20.&8.))Pjunk,(38.(20.&8.))Plo,$21.Pcnt,$21.Pst,$1?.Pq,$22.P,(23.VhRP,R2.R6.)P,(35.$32.R7.)P,(24.R4.R3.)P,(1.(2.=R6.)(3.R6.(41.+2.+40.)))P,(39.$32.R:.(5.(1=.&40.R2=.)-40.)(3:.R9.R=.R>.R?.R10.R11.R12.))P,(36.$32.R;.R9.(5.(1=.&40.R2>.)-40.))P,(2.(1<.VhRP,)R:.)P,(2.R;.(3;.(1=.&40.R30.)+40.))(3<.$32.(3=.R16.R31.R30.R2?.R15.R14.R13.R12.R11.R22.R21.R20.R1?.R1>.R1=.R1<.R10.R?.R<.R:.R>.(42.R:.R9.R;.)(1>.&40.(25.R:.R9.)))(2=.(2>.R17.(1>.&40.(5.(1=.&40.R31.)-40.))R30.R2?.R2>.R2=.R2<.R2;.R2:.(1>.&40.(25.R:.R9.))(1>.&40.R;.)R29.R28.R27.R26.R25.R24.(1>.&40.$40.)(1>.&40.$43.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R10.(1>.&40.+404?8.)R?.(30.(20.&40.))R>.(31.$32.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until q. intros MR MI MSq HC FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1.
  rceilb; unfold RCTX, RMLOCK in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 24, RCTX + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
  { eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
      rewrite (conc_aadd st q META_SIZE) by (ddestruct MSq as (a & ar & k & Ha & Hk & ->); cbn; pose proof MR as (WF' & _);
          ddestruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
      unfold META_SIZE, wz. exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
  clear MUc WMc C1.
  change (conc st q) with (conc st1 q).
  eapply evt_mono.
  { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
      [exact MR1 | assumption | exact MSq | exact FR | exact ST | rceilb; lia | lia]. }
  intros ms' RP. unfold ram_ret_post in RP |- *.
  ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
  deexists 15. split; [reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|exact I]].
      + intros x Hx. apply ram_fp_stack. lia.
      + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

End RP_1.
