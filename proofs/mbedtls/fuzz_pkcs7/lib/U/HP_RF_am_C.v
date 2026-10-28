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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_ntf_A HP_RF_am_A HP_RF_am_K.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_am_C () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "stdpp.base.lookup"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_C.pgal"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.NSLOTS"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.AREA_HDR"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.META_SIZE"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_metas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_secret"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.zeros"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_fp"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_meta_area_tail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_areas"; "stdpp.base.insert"; "stdpp.fin_maps.map_insert"; "stdpp.gmap.gmap_partial_alter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mkArea"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_ret_post"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_A.am_took"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_meta_area_tail"; "stdpp.base.is_Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_area_count"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_K.carve_st"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma ram_carve2 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_C ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Ps4o,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Plo,$4.Pst0,$5.Pst,$5.Pp,$6.Pr,$7.P,(8.VhRP,R3.R7.)P,(9.$:.R8.)P,(;.(<.$=.$>.$?.$7.)(10.R5.)(10.R6.))P,(;.(2.$7.)(11.$=.$7.(<.$=.$>.$?.$7.)(12.$=.$>.$?.$7.)(13.$=.$4.R5.)(10.R6.))(14.$7.R4.))P,(15.(;.$16.(17.R5.)$18.))P,(19.=(1:.$=.$4.R7.))P,(19.(1;.(1:.$=.$4.R8.)+1000.)(1<.(1=.R7.)))P,(1>.(1:.$=.$4.R9.))P,(19.(1?.R9.)(1;.(20.R9.)(1:.$=.$4.R:.)))P,(;.(2.$21.)(11.$6.$21.(<.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)(12.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)R;.(26.R<.))(27.$21.))P,Pk,$4.P,(28.(19.=R1.)(29.R1.$2:.))(;.(2.$2;.)(11.$6.$2;.(<.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$2;.)(12.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$2;.)(2<.R>.(1;.$2=.(2>.$2?.R2.)))(30.R?.))(27.$2;.))P,(28.(19.=(31.(32.R>.)))(29.(31.(32.R>.))(33.+2.+40.)))P,(34.$:.R13.(35.R?.R>.)(36.$37.(38.(39.=))(36.$37.(38.(39.=))(36.$37.(3:.(39.=))(36.$37.(3:.(39.=))(3;.$37.))))))P,(34.$:.R14.(1;.(35.R10.R?.)+18.)(36.$37.(3<.#?>8.(3=.#?>8.))(3;.$37.)))P,(3>.(3?.R12.R13.(40.&40.R3:.))R16.R15.)P,(41.$:.R17.R16.)P,(34.$:.R17.(1;.(40.&40.R3<.)-40.)(42.VhRP,R16.R1;.R1<.R1=.R1>.R1?.R20.))P,(43.$:.R18.R16.(1;.(40.&40.R3=.)-40.))P,(19.(44.VhRP,)R17.)P,(19.R18.(45.(40.&40.R3?.)+40.))ZstC,$5.(46.(47.(14.$6.R16.))R17.)ZstD,$5.(48.(49.$6.$21.(<.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)(4:.$6.$21.(<.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)(4;.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.))R17.(4<.(31.(32.R18.))(27.$6.)$2:.)(26.R1.))R1.)(4=.$:.(4>.VhRP,R26.R42.R41.R40.R25.R24.R23.R22.R21.R32.R31.R30.R2?.R2>.R2=.R2<.R20.R1?.R1;.R1:.R1>.(4?.R1.(2<.R18.$2=.)+64.)(50.&40.(1;.(35.R19.R18.)+18.)))(51.(52.R27.(50.&40.(1;.(40.&40.R42.)-40.))R41.R40.R3?.R3>.R3=.R3<.(50.&40.(35.R19.R18.))R3;.R3:.R39.R38.R37.R36.R35.R34.(50.&40.$53.)(50.&40.$54.)R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R20.(50.&40.+404=4.)R1?.(27.(0.&40.))R1=.(55.$:.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until r. intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose MR as (WF & (C1 & _) & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). rceilb.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold ctx_head_cells in C1.
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  assert (PD : conc st p + 4096 <= 0x48000 \/ 0x7e000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 64, RCTX + 72)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
  { eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl rsegs mX) as WMp end.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
  { eapply rmrep_transport_unowned; [exact MRC | exact MUp | exact WMp |].
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
  clear MUp WMp MRC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
  { unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [exact MRC3 | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | idtac].
    - exact SAL.
    - change (conc stC p) with (conc st p). exact HDR0.
    - intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
      destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [exact B| exact W| cbn; tauto| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
    - change (conc stC p) with (conc st p).
      destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [exact B| exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
  clear MRC3 HDR0 REST.
  assert (MSq : meta_slot stD (aadd p AREA_HDR)).
  { dexists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
    unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
  assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
  { change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
  rewrite CQ. change (Z_to_bv 64 512816) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 512960) with (Z_to_bv 64 RMLOCK).
  eapply evt_mono.
  { eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
      [exact MRD | assumption | exact MSq | lia | | | rceilb; lia | lia].
    - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
    - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
  intros ms' RP. unfold ram_ret_post in RP |- *.
  ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
  deexists 15. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha.
      apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
      + intros x Hx. apply ram_fp_stack. lia.
      + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
      + intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; exact Hr| exact NK|].
        pose proof (lr_lo_ge r). lia. }
  (* [comment removed for export] *)
  split; [eapply wmono_trans; [exact WM0| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ram_carve_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_C ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Ps4o,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Plo,$4.Pst,$5.Pp,$6.Pr,$7.P,(8.VhRP,R3.R6.)P,(9.$:.R7.)P,(;.(2.$7.)(11.$=.$7.(<.$=.$>.$?.$7.)(12.$=.$>.$?.$7.)(13.$=.$4.R4.)(10.R5.))(14.$7.R3.))P,(15.(;.$16.(17.R4.)$18.))P,(19.=(1:.$=.$4.R6.))P,(19.(1;.(1:.$=.$4.R7.)+1000.)(1<.(1=.R6.)))P,(1>.(1:.$=.$4.R8.))P,(19.(1?.R8.)(1;.(20.R8.)(1:.$=.$4.R9.)))P,(;.(2.$21.)(11.$6.$21.(<.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)(12.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)R:.(26.R;.))(27.$21.))P,Pk,$4.P,(28.(19.=R1.)(29.R1.$2:.))(;.(2.$2;.)(11.$6.$2;.(<.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$2;.)(12.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$2;.)(2<.R=.(1;.$2=.(2>.$2?.R2.)))(30.R>.))(27.$2;.))P,Ptl,$6.P,(;.$56.(57.(32.R>.))(14.$6.R1.))(58.$21.(11.$6.$21.(<.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)(12.$6.(22.$=.$>.$4.$23.)(24.$=.$>.$?.$4.$23.$25.)$21.)R2.(26.R?.)))P,(28.(19.+1.(59.(32.R>.)))(29.(59.(32.R>.))(33.+2.+40.)))P,(28.(19.=(31.(32.R?.)))(29.(31.(32.R?.))(33.+2.+40.)))P,(5:.$:.R13.(35.R10.R?.)(3=.#1000.))P,(5;.$:.R14.(35.R11.R10.)+1000.)P,(34.$:.R15.(1;.(40.&40.R39.)-40.)(42.VhRP,R14.R18.R19.R1:.R1;.R1<.R1=.))P,(43.$:.R16.R14.(1;.(40.&40.R3:.)-40.))P,(19.(44.VhRP,)R15.)P,(19.R16.(45.(40.&40.R3<.)+40.))(4=.$:.(4>.VhRP,R21.R3=.R3<.R3;.R20.R1?.R1>.R1=.R1<.R2=.R2<.R2;.R2:.R29.R28.R27.R1;.R1:.R17.(5<.R16.R15.)R19.(4?.(5<.R16.R15.)(2<.R15.$2=.)+64.)(50.&40.(1;.(35.R16.R15.)+18.)))(51.(52.R22.(50.&40.(1;.(40.&40.R3=.)-40.))R3<.R3;.R3:.R39.R38.R37.(50.&40.(35.R16.R15.))R36.R35.R34.R33.R32.R31.R30.R2?.(50.&40.$53.)(50.&40.$54.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R1;.(50.&40.+404:8.)R1:.(27.(0.&40.))R19.(55.$:.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until r. intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC ZB ZW FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose MR as (WF & (C1 & _) & _ & AR & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). rceilb.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold ctx_head_cells in C1.
  (* [comment removed for export] *)
  assert (HDR0 : rw_cells rsegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [exact ZB| exact ZW| cbn; tauto| reflexivity| lia| cbn; lia]. }
  assert (REST : rw_cells rsegs m (conc st p + 24) [CB 4072 (zeros 4072)]).
  { eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [exact ZB| exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| cbn; lia]. }
  clear ZB ZW.
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD in *.
  assert (PD : conc st p + 4096 <= 0x48000 \/ 0x7e000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RF DR1 DR23 DR2 RU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0. unfold RCTX in MU0.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
  { eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
      rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
      lazymatch goal with H : rw_cells rsegs ?mX 512968 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1.
  destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
  - (* [comment removed for export] *)
    destruct (TL tl eq_refl) as [ar Har].
    ddestruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). rceilb.
    pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
    destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
    assert (TD : conc st tl + 4096 <= 0x48000 \/ 0x7e000 <= conc st tl) by lia.
    assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
    assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
    { destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
      - rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
        assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
        unfold pgal in SAL. clear - Ct Cp NEo SAL StL E. Z.div_mod_to_equations. lia.
      - destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
    clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
    unfold pw. cbn [oconc]. unfold wz.
    assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    rewrite CF. clear CF.
    dpose MR1 as (_ & _ & _ & AR1 & _). ddestruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
    change (conc st1 tl) with (conc st tl) in ARh.
    apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl rsegs mX) as WMa end.
    (* [comment removed for export] *)
    st1. st1.
    set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| exact MUa| exact WMa|].
      change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. exact ARh. }
    clear MUa WMa ARh MR1.
    rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 512816) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 512960) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact FRESH | exact SEC | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. eapply ram_fp_area; [exact MR| exact Har| lia].
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
      - rceilb; lia.
      - lia. }
    intros ms' RP. exact RP.
  - (* [comment removed for export] *)
    unfold pw. cbn [oconc]. unfold wz.
    change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 56, RCTX + 64)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    (* [comment removed for export] *)
    st1.
    set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
        rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
        lazymatch goal with H : rw_cells rsegs ?mX 512968 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MR1.
    rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 512816) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 512960) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact SEC | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
      - rceilb; lia.
      - lia. }
    intros ms' RP. exact RP.
Qed.

End RP_1.
