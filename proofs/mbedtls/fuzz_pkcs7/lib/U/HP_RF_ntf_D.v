(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_D MallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_ntf_A HP_RF_ntf_E.
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
Ltac2 gd_tbl_HP_RF_ntf_D () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.land"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B3.mw_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.usage"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rfg_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocModel_B.fg_usage_st"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_word"].



(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26983581294.9L4366122214.10L8734630769.9 00000;00J00RS1a1n2Ha2NES1a1n2Hn1k2Hk1HS1a1n2Ha". (* [comment removed for export] *)
#[using="hRP"] Lemma testbit_false_ge a n : 0 <= a < 2^n -> 0 <= n -> forall k, n <= k -> Z.testbit a k = false.
Proof. rceilb.
  intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L14349313109.9L25831690560.9L35495402263.9L56759190151.9L58937931451.9L9277398327.9 00000500:00;00A00G00OS1n1GS1n1GSS1a2HaS1b2HbS1n2Hn1L". (* [comment removed for export] *)
#[using="hRP"] Lemma lor_lxor_ones64 a b : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_D ()) "P,(0.(1.=O2.)(2.O2.(3.+2.+40.)))P,(0.(1.=O1.)(2.O1.(3.+2.+40.)))(4.$5.(6.(7.O2.+????????????????.)(7.O1.+????????????????.))(7.(8.O2.O1.)+????????????????.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
  destruct (Z.lt_ge_cases n 64) as [L|G].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L11601621875.8L14822106158.7L29317575382.7L34241555761.8L36476774354.7L44015166854.7L5231142375.6 L5231146246.7 L58028792219.6L65275802054.8L67353100442.700000100400500:00@00A00G00M00S00Y00ZSS1wSS1u1wS1w2HXSS1w2HwS1w2HwS1w2HwS1w2HLS". (* [comment removed for export] *)
#[using="hRP"] Lemma usage_sub_word u w : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_D ()) "P,(0.(1.=O2.)(2.O2.(3.+2.+40.)))P,(0.(1.=O1.)(2.O1.(3.+2.+40.)))(4.(9.&40.)(:.&40.(;.O2.(6.(<.&40.(:.&40.(7.O1.+????????????????.)))+??????????????>0.)))(=.(>.O2.(;.(8.O1.+1?.)+1.))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros Hu Hw.
  assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
  rewrite unsigned_lit by lia.
  change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
  rewrite lor_lxor_ones64 by lia.
  assert (HL : 0 <= Z.land w 31 < 32).
  { split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite zb_lxor_ones by lia. unfold wz.
  rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
  replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_D ()) "Lms',$?.(10.(9.&40.)La3,(9.&40.)(10.(9.&40.)La4,(9.&40.)(10.P,(9.&40.)(11.(9.&8.))Lm',P,(9.&40.)(11.(9.&8.))(0.(4.$?.R4.(12.(13.O23.(:.&40.(;.(<.&40.O22.)-60.))O21.O20.O14.O13.O12.O1?.O1>.(:.&40.(14.O7.O4.))(:.&40.O3.)(=.O2.)R3.R2.O11.O10.O?.(:.&40.$15.)O1=.O1<.O1;.O1:.O19.O18.O17.O16.O15.O>.O=.O<.O;.)O:.(:.&40.+40114.)O9.(16.(9.&40.))R1.(17.$18.)))(0.(19.(1:.O7.O8.(<.&40.O22.))O6.R1.)(0.(1;.$18.O6.R1.)(0.(1<.$18.R1.)(0.(1=.$18.R1.O8.(;.(<.&40.O22.)-60.))(0.(1>.$18.R1.(;.(<.&40.O22.)-60.)O1.)(1?.VhRP,O5.R1.))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00O0?L11425559571.58L11603785325.58L11887039770.63L11889072664.65L18600826357.66L20391564489.63L22067087340.58L22374889542.66L25069450385.66L25755212519.64L29786659065.64L30832843899.66L33379325362.58L36030178447.64L36032323863.63L36032520848.60L36034748437.61L39912510457.65L45083181516.58L49702840724.66L49731370611.61L50827569594.60L50993530517.60L5631454109.63 L56864992525.58L63350722656.58L8495637125.66 L8495997724.64 L8496049026.64 L8832910886.66 L8927180544.58 00000?00K00`01501`02502A02R03A03V03b04904H04[04n05A05T05c05o06D06U06V06g06h07407I07\07k08:08V08oS2fr2mr3FRL3LFRS2fr3FRL3LFRS2fr2mr3FRL3SCR3LFR1KS2fr2mr3FRL3SCR3LFR1KS3hRP3RCB2sp2fr2lo2mr3FRL2LO4LOLE3LFR1K3LENS2fr2st2mr2UR3FRL3LFRS2fr3FRL3LFRS2fr3FRL3LFR1x2HxS3hRP3RCB2sp2fr2lo2mr3FRL2LO4LOLE3SCR3LFR1K3LENS2fr2mr3FRL3SCR3LFR1KS2fr3FRL3LFRS2fr2mr3FRL3SCR3LFR3LENS2fr2mr3FRL3LFRS2fr2mr3FRL3SCR3LFRS2fr2mr3FRL3MWR3LFRS2fr2mr3FRL3MWR3LFRS2fr2mr3FRL3SCR3LFRS2fr2mr3FRL3LFRS2fr3FRL3LFRS2fr2mr3FRL3LFR1K3LENS2fr2mr3FRL3LFR1KFS2fr2mr3FRL3LFR1KFS2fr3FRL3LFRS2fr2mr3FRL2LI2FB3LFRS2fr2mr3FRL3LFR3LENS2fr2mr3FRL3LFRS2fr2mr3FRL3LFRS2sp2fr2lo3FRL4LOLE3LFR1x2HxS2fr2mr3FRL2LI2FB3SCR3LFR". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_fg : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_D ()) "Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(20.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(11.(9.&8.))Pfr,(21.$22.)Pst,$23.Pg,$24.Plo,$5.Zmr,$25.(26.R3.R2.)P,(1?.VhRP,R4.R6.)P,(1<.$18.R7.)P,(27.R6.R5.)P,(28.R4.)P,P,(2.(29.R5.)+30.)(0.(1.=(2:.R9.(29.R6.)))(2.(2:.R9.(29.R6.))(3.+2.+40.)))P,(1>.$18.R;.(;.(<.&40.R29.)-60.)R:.)P,(4.$2;.(2<.R;.)#60.)P,(1=.$18.R=.R9.(;.(<.&40.R2;.)-60.))P,(1.(2=.VhRP,)R:.)P,(1.R;.(>.(<.&40.R2=.)+60.))(2>.$18.(2?.R2?.R2>.R2=.R2<.R28.R27.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R2;.R2:.R29.R22.R21.R20.R16.R15.R14.R13.R12.R11.R<.R>.R10.(30.R>.R=.)R=.(29.R;.)(31.R;.)R?.)(12.(13.R2?.(:.&40.(;.(<.&40.R2>.)-60.))R2=.R2<.R2;.R2:.R29.R28.R27.(:.&40.(14.R>.R=.))R26.R25.R24.R23.R22.R21.R20.(:.&40.$15.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(:.&40.+400>0.)R11.(16.(9.&40.))R10.(17.$18.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (meta_word_range mr MW) as MWR.
  dpose MW as (LI & FB & SCR & ML).
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  rceilb; unfold RCTX in *.
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
      with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rmeta_chunk MR MSL CH. fold mr in CH.
  st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    clear CH.
    unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. unfold rfg_post. deexists 3. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR].
  - unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    specialize (UR ltac:(lia)).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (512968, 512968 + 928)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa (RCTX + 464 + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    st1.
    replace (wa (512968 + 464 + 8 * m_sizeclass mr)) with (Z_to_bv 64 (512968 + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    (* [comment removed for export] *)
    st1. st1. st1.
    rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
    (* [comment removed for export] *)
    dpose MR as (_ & (_ & _ & USG & _) & _).
    pose proof (u64arr_store_ok rsegs _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 (512968 + m_sizeclass mr * 8 + 464)) USG
                  ltac:(rewrite usages_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    clear USG.
    rraw_store_finish (512968 + 464 + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (CH' : rw_cells rsegs mX (conc st g) (meta_cells st mr)) end.
    { pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
      rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
      replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [exact X|].
      unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
    clear CH. unfold meta_cells in CH'.
    st1. clear CH'.
    apply evt_done. unfold rfg_post. deexists 3. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
