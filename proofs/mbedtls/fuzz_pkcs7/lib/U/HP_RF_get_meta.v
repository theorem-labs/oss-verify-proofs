(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_get_meta () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rget_meta_post"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le2"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.UNIT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Known"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.g_meta"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area_of"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_check"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_secret"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_last_idx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freeable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_maplen"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rget_meta_entry"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RP_1.runlock_post"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.runlock_entry"].



Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma land_pow2_testbit a i : 0 <= a -> 0 <= i -> Z.land a (2 ^ i) = 0 <-> Z.testbit a i = false.
Proof.
  intros Ha Hi. split.
  - intros H. destruct (Z.testbit a i) eqn:E; [|reflexivity]. exfalso.
    assert (T : Z.testbit (Z.land a (2 ^ i)) i = true) by (rewrite Z.land_spec, E, Z.pow2_bits_true by lia; reflexivity).
    rewrite H, Z.bits_0 in T. discriminate.
  - intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec n i) as [->|NE]; [rewrite H; reflexivity|].
    rewrite (Z.pow2_bits_false i n) by lia. apply andb_false_r.
Qed.

#[using="Type"] Lemma sllw1_word' i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_get_meta ()) "Lms',$0.(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(3.$0.R5.(4.(5.O1>.O1=.O1<.O1;.O1:.O19.O18.O17.O16.O5.(6.O4.)R4.R3.R2.R1.O7.O6.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.)O3.(7.O1>.)O2.(8.(2.&40.))O1.(9.$:.)))))))")
(* [comment removed for export] *).


#[using="Type"] Lemma rget_meta_tail : ltac2:(CDefT.buildp (gd_tbl_HP_RF_get_meta ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pgw,(2.&40.)PF,(;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(<.(2.&8.))Poff16,$=.Pmword,$=.Pmaplen,$=.P,(>.(?.=R3.)(10.R3.+10000.))P,(>.(?.=R3.)(10.R3.(11.+2.+40.)))P,(>.(?.=R3.)(10.R3.(11.+2.+28.)))P,(3.$=.(12.R5.+<.)R4.)P,P,(13.(3.$=.R5.=))(?.R8.(14.(15.R6.+100.)+1.))(16.$:.(17.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R1<.R1;.R<.R8.R;.R:.R9.)(4.(5.R28.R27.R26.R25.R24.R23.R22.R21.R20.R<.(6.R8.)(6.R7.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R;.(18.&40.+3?>9<.)R:.(8.(2.&40.))R9.(9.$:.)))")
(* [comment removed for export] *).
Proof.
  intros until maplen. intros O16 MW ML MW4 Hml.
  st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  - st1. unfold rget_meta_post. finish.
  - st1. st1. st1. if_cases K2; zify_cond K2.
    + st1. unfold rget_meta_post. finish.
    + exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. rewrite ?wz_unsigned in K2 by lia.
      first [ rewrite Z.mod_small in K2 by lia
            | change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia; rewrite Z.mod_small in K2 by lia
            | idtac ]. lia.
Qed.

#[using="Type"] Lemma rget_meta_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_get_meta ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(<.(2.&8.))PP,$=.PG,$=.PB,$=.PA,$=.Pb3,$=.Poff16,$=.Pavail,$=.Pfreed,$=.Plast_idx,$=.Pfreeable,$=.Psc,$=.Pmaplen,$=.Psecret,$=.Pprev,(2.&40.)Pnext,(2.&40.)Zidx,$=.(19.R;.+1?.)Zmword,$=.(1:.(1:.(1:.R8.(15.+20.R7.))(15.+40.R6.))(15.+1000.R5.))P,(3.$=.(1;.&40.R2:.)R11.)P,(3.$=.(1<.R12.+10.)=)P,(?.(1:.(15.+10.R>.)+10.)R13.)P,(?.(1:.R14.+10.)(11.+2.+40.))P,(3.$=.R13.(14.(14.R15.(15.+10.R10.))+10.))P,(3.$=.R13.(14.R15.(1<.R15.+1000.)))P,(?.=R16.)P,(?.(1:.R17.+28.)(11.+2.+40.))P,(3.(<.(1=.(2.&8.)))(1>.$:.R1:.(1?.(14.R19.+4.))#1.)(20.(1=.(2.&8.))(21.(2.&8.)(22.=)(23.(2.&8.)))))P,(3.(<.(1=.(2.&8.)))(1>.$:.R1;.(1?.(14.R1:.+3.))#1.)(20.(1=.(2.&8.))(21.(2.&8.)(22.R16.)(23.(2.&8.)))))P,(3.(<.(1=.(2.&8.)))(1>.$:.R1<.(1?.(14.R1;.+2.))#2.)(20.(1=.(2.&8.))(24.(6.R16.))))P,(3.(<.(1=.(2.&8.)))(1>.$:.R1=.(1?.R1:.)#8.)(20.(1=.(2.&8.))(25.(6.R1;.))))P,(26.$:.R1>.R1<.(21.$27.(28.R10.)(21.$27.(28.R?.)(21.$27.(28.(6.R1;.))(21.$27.(29.(6.R17.))(21.$27.(29.(6.R16.))(21.$27.(28.(6.R=.))(23.$27.))))))))P,(3.(<.(1=.(2.&8.)))(1>.$:.R1?.(1?.R1;.)#8.)(20.(1=.(2.&8.))(25.(6.R12.))))P,(3.(<.(1=.(2.&8.)))(1>.$:.R20.(1?.$2:.)#8.)(20.(1=.(2.&8.))(25.(6.R13.))))P,P,(10.R16.+30.)(3.(<.(1=.(2.&8.)))(1>.$:.R22.(1?.(1:.$2;.(15.+2.R17.)))#2.)(20.(1=.(2.&8.))(24.(6.(2<.R17.)))))P,(>.(?.=R1=.)(10.R1=.+100.))P,(>.(?.=R1=.)(10.R1=.+10000.))P,(>.(?.=R1=.)(10.R1=.(11.+2.+20.)))P,(>.(?.=R1=.)(10.R1=.(11.+2.+20.)))P,(>.(?.=R19.)(10.R19.(11.+2.+40.)))P,(>.(?.=R1>.)(10.R1>.+20.))P,(>.(?.=R1>.)(10.R1>.+2.))P,(>.(?.=R1>.)(10.R1>.+40.))P,(>.(?.=R1>.)(10.R1>.(11.+2.+28.)))P,(?.R1;.R22.)P,(3.$2=.(2>.R25.R1<.)$2?.)P,(3.$2=.(2>.R25.R1=.)$2?.)P,P,(10.R23.+30.)(>.(?.(15.(2<.R24.)R1?.)R29.)(10.R29.(15.(2<.R24.)(1:.R1?.+1.))))P,P,(?.+30.R24.)(3.$=.R25.+3?.)P,P,(13.(3.$=.R24.=))(?.R2;.(14.(15.R25.+100.)+1.))(16.$:.(17.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R43.R42.(6.R2?.)R2;.R33.R32.R31.)(4.(5.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(18.&40.+3?=:8.)R32.(8.(2.&40.))R31.(9.$:.)))")
(* [comment removed for export] *).
Proof.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  (* [comment removed for export] *)
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
    rewrite GW. eapply rget_meta_tail; eauto.
    subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia.
  - specialize (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
    st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (94460 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (94460 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite GW. eapply rget_meta_tail; eauto.
    subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rget_meta_spec : ltac2:(CDefT.buildp (gd_tbl_HP_RF_get_meta ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(<.(2.&8.))Pst,$30.Pp,$31.Pr,$32.Pg,$31.Pgh,$33.Par,$34.Pb3,$=.Plo,$=.Phi,$=.Zsh,$35.(36.R9.(37.$38.$=.R8.))Zpo,$=.(39.$38.$=.R9.)Zoff16,$=.(1:.R4.(15.+100.R3.))Zidx,$=.(19.R6.+1?.)Zbase,$31.(3:.R<.(14.(3;.(15.$3<.R2.))$3<.))Zmr,$3=.(3>.R>.R;.)P,(3?.VhRP,R?.R10.)P,(40.$:.R11.)P,(3.(<.$32.)(41.$38.$32.(42.$38.$43.$44.$32.)(45.$38.$43.$44.$32.)(37.$38.$=.R10.)(46.R11.))(20.$32.R?.))P,(3.$47.(48.R10.)$49.)P,(3.$=.(1;.&40.R2<.)(1:.(4:.R11.)R9.))P,(3.$=.(1<.R:.+10.)=)P,(?.+10.R;.)P,(?.(1:.(15.+10.R;.)+10.)R<.)P,(?.(1:.R=.+10.)(4;.(4<.R15.)))P,(3.$4=.(4>.R?.(14.R>.+4.))(4?.=))P,(3.$4=.(4>.R10.(14.R?.+3.))(4?.R13.))P,(3.$4=.(4>.R11.(14.R10.+2.))(4?.R13.))P,(3.$4=.(4>.R12.(14.R11.+1.))(4?.R13.))P,(3.(<.$33.)(41.$31.$33.(42.$31.(50.$38.$43.$=.$51.)(52.$38.$43.$44.$=.$51.$53.)$33.)(45.$31.(50.$38.$43.$=.$51.)(52.$38.$43.$44.$=.$51.$53.)$33.)R?.(54.R1<.))(20.$33.R18.))P,(3.$55.(56.R19.)(20.$31.R1:.))P,(57.R1>.R1;.)P,(?.=(39.$38.$=.R1<.))P,(3.$55.(58.R12.)(20.$31.R13.))P,(3.(<.$34.)(41.$31.$34.(42.$31.(50.$38.$43.$=.$51.)(52.$38.$43.$44.$=.$51.$53.)$34.)(45.$31.(50.$38.$43.$=.$51.)(52.$38.$43.$44.$=.$51.$53.)$34.)(59.R1>.)(5:.R21.))(20.$34.R1<.))P,(3.$=.(5;.R1=.)(5<.(5=.R22.)))P,(>.(?.=(5>.R15.))(10.(5>.R15.)(11.+2.+20.)))P,(>.(?.=(5?.R16.))(10.(5?.R16.)(11.+2.+20.)))P,(>.(?.=(5<.(5=.R25.)))(10.(5<.(5=.R25.))(11.+2.+40.)))P,(>.(?.=(60.R18.))(10.(60.R18.)+20.))P,(>.(?.=(61.R19.))(10.(61.R19.)+2.))P,(>.(?.=(62.R1:.))(10.(62.R1:.)+40.))P,(>.(?.=(63.R1;.))(10.(63.R1;.)(11.+2.+28.)))P,(?.R1>.(60.R1<.))P,(3.$2=.(2>.(5>.R1=.)R1?.)$2?.)P,(3.$2=.(2>.(5?.R1>.)R20.)$2?.)P,P,(10.(62.R1?.)+30.)(>.(?.(15.(2<.(62.R20.))R22.)R23.)(10.R23.(15.(2<.(62.R20.))(1:.R22.+1.))))P,P,(?.+30.(62.R20.))(3.$=.(62.R21.)+3?.)P,P,(13.(3.$=.(63.R21.)=))(?.R25.(14.(15.(63.R22.)+100.)+1.))(16.$:.(17.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R43.R42.(6.(64.R30.R2=.))R25.R33.R32.R31.)(4.(5.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(18.&40.$65.)R32.(8.(2.&40.))R31.(9.$:.)))")
(* [comment removed for export] *).
Proof.
  intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
  dpose MR as (WF & CX & GL & AR & GR & SH).
  ddestruct WF as ((Hres & RPHres) & WR & DISJ & WA & WG).
  ddestruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). rceilb.
  (* [comment removed for export] *)
  destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  ddestruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia.
  (* [comment removed for export] *)
  destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  (* [comment removed for export] *)
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  (* [comment removed for export] *)
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC.
  (* [comment removed for export] *)
  ddestruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  ddestruct MS as (a & ara & k & Ha & Hkk & Eg).
  ddestruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  ddestruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). rceilb.
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
  { unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
    replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  unfold rget_meta_entry.
  eapply (rget_meta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_get_meta ()) "Lms',$0.(3.$0.R1.(4.(5.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.(6.=)O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(7.O21.)O2.(8.(2.&40.))O1.(9.$:.)))")
(* [comment removed for export] *).

#[using="Type"] Lemma runlock_spec : ltac2:(CDefT.buildp (gd_tbl_HP_RF_get_meta ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(<.(2.&8.))P,(3.$=.(1;.&40.R19.)$66.)P,(26.$:.R2.(1;.&40.R1:.)(21.$27.(29.(6.=))(23.$27.)))(16.$:.(67.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(4.(5.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(18.&40.$68.)R4.(8.(2.&40.))R3.(9.$:.)))")
(* [comment removed for export] *).
Proof.
  intros until m. intros HA LK. unfold runlock_entry.
  step. rewrite sx32_wz by lia. step. if_cases K; zify_cond K.
  { exfalso. rewrite wz_unsigned in K by lia. lia. }
  step. apply evt_done. reflexivity.
Qed.

End RP_1.
