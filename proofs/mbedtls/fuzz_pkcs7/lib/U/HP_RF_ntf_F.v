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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F MallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_free_A HP_RF_ntf_A HP_RF_ntf_E.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_ntf_F () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B3.mw_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.F_ntf_B.fm_facts"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_shadow"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_ntf_A.rntf_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rntf_ret_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.fm_st"; "RocqVerifyHarness.AgentSubmission.Heap.F_ntf_F.seq_st"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_maplen"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.zeros"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_seq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.record_seq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.step_seq"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_word"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "00O0@L1281580983.75  L14223199850.82 L16073429832.87 L16073429832.88 L17147286273.80 L18600826357.82 L20554796889.79 L22374889542.108L23319027747.87 L23378378850.81 L25069450385.75 L25069450385.82 L26892269087.108L2994607484.74  L2994607485.81  L3226138248.108 L40111354639.87 L42439018439.75 L46486781711.80 L46488991252.82 L49702840724.82 L54996280770.75 L56040388152.78 L56040616754.77 L56916068920.87 L59314955108.78 L62132358640.87 L63578605179.77 L6918902905.108 L8832910886.108 L9788380166.80  00000=00Q00c01501E01o02A02O02P02\02l03C03O03^03m03n04A04d05005@05T05a06:06S06a07107E07F07G07`080S4junk2LJ3LENS4junk2sc2LJ3SR'3LENS4junk2st1g3MWR2LJS4junk2st1g3MWR2LJS4junk2sc2LJ3SR'S3hRP3RCB2sp4junk2sc2lo2LO4LOLE2LJ3SR'3LENS4junk2sc2LJ2Sa2SbS4junk2LJ1x2HxFS4junk2sc2LJS2sp4junk2LJ3LENS2sp4junk2sc2LJ3SR'3LENS2sp4junk2LJS4junk2ns2NS2LJS4junk2ns2NS2LJFS3hRP4junk2lo2LO2LJS3hRP3RCB2sp4junk2lo2LO4LOLE2LJ3LENS4junk2sc2LJS4junk2sc2LJ3LENS4junk2sc2LJ3SR'3LENS4junk2LJ3LENS4junk2st1g2sc3HSC3SCR2LJS4junk2st1g2sc3HSC3SCR2LJS4junk2st1g2LJS4junk2sc2LJ1K1ES2sp4junk2lo4LOLE2LJFFS2sp4junk2lo4LOLE2LJ1x2HxS4junk2sc2LJ3SR'". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_seq : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_F ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Pst0,$4.Pst,$4.Pg,$5.Pp,$5.Psc,$6.Pns,$6.Plo,$6.Zmr,$7.(8.R6.R5.)P,(9.VhRP,R7.R?.)P,(:.$;.R10.)P,(<.R9.R8.)P,(=.R4.)P,(>.$6.R8.(?.R5.))P,(>.$10.(11.R6.)(12.$5.R:.))P,(13.(14.=R9.)(15.R9.+100.))P,(16.R>.R=.)P,(>.(0.&40.)R2=.(17.&40.$18.))P,(>.(19.$1:.$1;.$1<.$1=.)(1>.R10.)(1>.R11.))P,(>.(19.$1:.$1;.$1<.$1?.)(20.R11.)(20.R12.))P,(>.(19.$5.(21.$1:.$1;.$6.$22.)(23.$1:.$1;.$1<.$6.$22.$24.)$25.)(26.R12.)(26.R13.))P,(27.(28.(29.$6.$6.)(2:.$6.$6.(2;.(2<.&40.R38.)+60.)(2<.&40.R38.))(28.(29.$6.$6.)(2:.$6.$6.$2=.(2>.$2=.+3:0.))(2?.(29.$6.$6.))))R1<.R1;.)P,(30.$;.R1=.R1<.)P,(31.$;.R1=.(2>.(2<.&40.R3:.)-60.)(32.VhRP,R1<.R17.R18.R19.R1:.R1;.))P,(33.$;.R1>.R11.(2>.(2<.&40.R3;.)-60.))P,(14.(34.VhRP,)R12.)P,(14.R13.(2;.(2<.&40.R3=.)+60.))(35.$;.(36.VhRP,R1?.R3>.R3=.R3<.R1>.R1=.R1<.R1;.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R24.R23.R14.R1:.R22.(37.(38.R15.R16.R19.)R18.)(17.&40.(39.R19.R17.))(17.&40.(3:.(3;.R13.)+1000.)))(3<.(3=.R3?.(17.&40.(2>.(2<.&40.R3>.)-60.))R3=.R3<.R3;.R3:.R39.R38.R37.(17.&40.(39.R19.R18.))(17.&40.R16.)(17.&40.R15.)R36.R35.R34.R33.R32.(17.&40.$2=.)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R24.(17.&40.+40174.)R23.(3>.(0.&40.))R21.(3?.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (meta_word_range _ MW) as MWR. dpose MW as (LI & FB & SCR & ML).
  dpose FR as [[[LJ _] _] _]. cbn in LJ.
  rceilb; unfold RCTX, rntf_frame in *.
  (* [comment removed for export] *)
  st1. rewrite ?(unsigned_lit sc) by lia. st1.
  (* [comment removed for export] *)
  dpose MR as (_ & (_ & _ & _ & _ & _ & C6) & _).
  pose proof (rw_cells_store_ok_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (512968 + 912)) C6 eq_refl eq_refl
                ltac:(unfold wa; f_equal; lia)) as SOK.
  clear C6.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish (512968 + 912) [b8 ns] FR ST MU WM SOK.
  set (st1 := upd_ctx (set_seq ns) st) in MR1.
  (* [comment removed for export] *)
  st1.
  assert (JOIN : forall m2 (a1' : word),
    rmrep (seq_st ns sc st) m2 -> mem_inv rsegs m2 ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (512968, 512968 + 928)] m0 m2 -> wmono rsegs m0 m2 ->
    stk rsegs m2 lo (bv_unsigned sp + -96) -> rw_cells rsegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 (wz rp_canary); C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
    evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
                 (fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 512968) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x4018c) fc None m2 (seg_rom rsegs))).
  { intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
    assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
    rmeta_chunk MR2 MS2 CH.
    assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
    rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.
    (* [comment removed for export] *)
    st1. st1. st1. st1. clear CH.
    rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
    replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
    eapply evt_mono.
    { eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
        first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | rceilb; lia | lia | idtac].
      unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
    intros ms' PO. unfold rntf_ret_post in PO |- *.
    ddestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
    deexists 14. split; [reflexivity|].
    split.
    { eapply rpres_except_trans.
      - apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
        cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
      - eapply rpres_except_mono; [exact PE|]. intros a Ha.
        eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try lia;
          unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
    split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
    eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
  - assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    (* [comment removed for export] *)
    st1.
    dpose MR1 as (_ & (_ & _ & _ & US & _) & _).
    pose proof (u8arr_store_ok rsegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (512968 + (sc + -7) + 848)) US
                  ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    clear US.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish (512968 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
    eapply JOIN; try eassumption.
    unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
    match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
    unfold upd_ctx. cbn. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="hRP"] Lemma zeros32_cells : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_F ()) "(>.(3.(0.&8.))(40.(28.$41.(42.(17.&40.=))(28.$41.(42.(17.&40.=))(28.$41.(42.(17.&40.=))(28.$41.(42.(17.&40.=))(2?.$41.))))))(43.#20.))")
(* [comment removed for export] *).
Proof. rceilb. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L10312655142.74L11674666328.76L11954261848.76L16075460336.73L16077671799.74L26637834840.76L40107142448.74L47283939617.80L53146345158.74L54102219671.80L54102219671.81L5636801488.80 L59314923118.74L60783005528.76L61672509099.74L62128149455.74L68179570553.76L9962406557.76 00000@00I00R00d01901B01U01^02902g03U03g04>04G04^05205;05DS4junk2st3SEQ2LJS4junk2LJS4junk2LJS4junk2st1g3MWR2LJS4junk2st1g2ML2LJ3SEQS4junk2LJS3hRP4junk2lo2LO2LJS4junk2LJS4junk2st1g3HML3SEQ2ML2LJ1KS3hRP3RCB2sp4junk2lo2LO4LOLE2LJ2HB5Ha_st5Hl_stS3hRP3RCB2sp4junk2lo2LO4LOLE2LJ2HB5Ha_st5Hl_stS4junk2st3SEQ2LJ1KS4junk2st1g3HML2ML2LJ1KS4junk2LJS4junk2st1g3HML2ML2LJ1KS2sp4junk2lo4LOLE2LJS4junk2LJS4junk2LJ". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_top : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_F ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(3.(0.&8.))Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Pst0,$4.Pst,$4.Pg,$5.Pp,$5.Psc,$6.Plo,$6.Zmr,$7.(8.R5.R4.)P,(9.VhRP,R6.R>.)P,(:.$;.R?.)P,(<.R8.R7.)P,(=.R4.)P,(>.$6.R7.(?.R5.))P,(>.$10.(11.R6.)(12.$5.R9.))P,(44.(>.$6.(3;.R7.)=))P,(13.(14.=(45.(46.R=.)))(15.(45.(46.R=.))+100.))P,(16.R>.R=.)P,(>.(0.&40.)R2>.(17.&40.$18.))P,(>.(19.$1:.$1;.$1<.$1=.)(1>.R10.)(1>.R11.))P,(>.(19.$1:.$1;.$1<.$1?.)(20.R11.)(20.R12.))P,(>.(19.$5.(21.$1:.$1;.$6.$22.)(23.$1:.$1;.$1<.$6.$22.$24.)$25.)(26.R12.)(26.R13.))P,(27.(28.(29.$6.$6.)(2:.$6.$6.(2;.(2<.&40.R39.)+60.)(2<.&40.R39.))(28.(29.$6.$6.)(2:.$6.$6.$2=.(2>.$2=.+3:0.))(2?.(29.$6.$6.))))R1<.R1;.)P,(30.$;.R1=.R1<.)P,(31.$;.R1=.(2>.(2<.&40.R3;.)-60.)(32.VhRP,R1<.R17.R18.R19.R1:.R1;.))P,(33.$;.R1>.R12.(2>.(2<.&40.R3<.)-60.))P,(14.(34.VhRP,)R13.)P,(14.R14.(2;.(2<.&40.R3>.)+60.))(35.$;.(36.VhRP,R1?.R3?.R3>.R3=.R1>.R1=.R1<.R1;.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R24.R23.R15.R1:.R22.(37.(47.R16.(48.R19.))R18.)(17.&40.(39.R19.R17.))(17.&40.(3:.(3;.R14.)+1000.)))(3<.(3=.R40.(17.&40.(2>.(2<.&40.R3?.)-60.))R3>.R3=.R3<.R3;.R3:.R39.R38.(17.&40.(39.R19.R18.))(17.&40.R16.)(49.(4:.R14.))R36.R35.R34.R33.R32.(17.&40.$2=.)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R24.(17.&40.+40114.)R23.(3>.(0.&40.))R21.(3?.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. dpose MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  dpose FR as [[[LJ _] _] _]. cbn in LJ.
  rceilb; unfold RCTX, rntf_frame in *.
  (* [comment removed for export] *)
  st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.
  (* [comment removed for export] *)
  pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
  st1. clear RDS. st1.
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  - (* [comment removed for export] *)
    st1.
    replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
    2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
      first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | rceilb; lia].
  - (* [comment removed for export] *)
    dpose MR as (_ & (_ & _ & _ & US & _) & _).
    pose proof (rw_cells_of_u8arr rsegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
    replace (512968 + 848) with 513816 in UB by reflexivity.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(512968 + 848, 512968 + 880)]%Z mX) as MUz; pose proof (wmono_refl rsegs mX) as WMz end.
    st1. st1. st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (UA' : u8arr rsegs mX (RCTX + 848) (zeros 32))
        by (apply (u8arr_of_rw_cells rsegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tauto]) end.
    clear UB.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
    { eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
        unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }
    (* [comment removed for export] *)
    st1. st1.
    replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
    2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
    replace (conc st p) with (conc stz p) by reflexivity.
    change (get_meta_rec st g) with (get_meta_rec stz g).
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
      first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | rceilb; lia
            | apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
