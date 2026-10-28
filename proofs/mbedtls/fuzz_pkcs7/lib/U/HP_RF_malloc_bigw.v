(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_bigw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMalloc_fp HP_RF_enframe HP_RMallocKit_A2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_malloc_bigw () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.zeros"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_word"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_bigw.big_meta"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmunmap_entry"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_meta_entry"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_seq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RP_1.rseq_post"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.step_seq"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_bigw.big_st"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.u32"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"].


Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L22362493461.8 L33234766905.10L55686273877.11L56087383078.8 00000800@00H00PS1x1k2XKS1k1i2HiS1k1i2HiS1x1k2X0". (* [comment removed for export] *)
#[using="hRP"] Lemma rzeros_bytes_at : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "Pm,P,(0.&40.)(1.(0.&8.))Px,$2.Pk,$3.P,(4.=R2.)P,(4.(5.R3.(6.R2.))(7.+2.+40.))P,Po,$2.P,(8.(4.=R1.)(9.R1.(6.R4.)))(:.$;.R7.(5.R6.R2.)(<.(0.&8.)(=.=)(>.(0.&8.))))(:.$;.R6.R5.(?.R4.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
  intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  ddestruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
  rewrite Z.add_0_r in HB. exact HB.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L16131084811.12L17210504373.6 L24928565326.10L29317573413.6 L35497642613.6 L6160747397.6  L64522633523.1200000;00<00J00K00L00M00XS1x1i2H12H3SS1i2H12H22Hi1HSSSS1x1i2H12H2". (* [comment removed for export] *)
#[using="hRP"] Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof. rceilb.
  intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
  change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
  assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
  { change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
  rewrite T4064.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
    rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L27293495702.8 L33581900583.5 L35298690951.14L36644237772.5 L44687353605.13L52952359618.5 L55269914620.5 L63681228783.8 L8850913373.8  00000100400=00C00L00R00X00]00bSS1nS1n1q1r1HS1n2HnS1n1r1q1HS1n2HnS1n2HnS1i1HS1i1H". (* [comment removed for export] *)
#[using="hRP"] Lemma rbig_word_eq rid n : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "P,(8.(4.=O1.)(9.O1.(7.+2.+20.)))(10.$2.(11.(12.(5.(5.O1.+?>0.)+33.)+?????????????800.)+?>0.)(13.(14.O2.O1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
  unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  replace (n + 4064 + 51) with (n + 4115) by lia.
  assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
    destruct (Z.lt_ge_cases i 12).
    - rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L11447730091.39L29010614439.1100000f00lS2c01q1r2r21H2H02q02r02r12H42H52q12H92q22r33H142q33H19S1r2H0". (* [comment removed for export] *)
#[using="hRP"] Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof. rceilb.
  intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L27900861085.46L51711223320.4500000:00>S2sp2lo2LOS2sp". (* [comment removed for export] *)
#[using="hRP"] Lemma rbig_fail1_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pra',(0.&40.)Pnw,(0.&40.)Prav,(0.&40.)Ps0v,(0.&40.)Ps1v,(0.&40.)Ps2v,(0.&40.)Ps3v,(0.&40.)Ps4v,(0.&40.)PF,(15.&5.(0.&40.))Pfc,(0.&20.)Pm,$16.Plo,$2.P,(17.$;.R2.(5.(18.&40.R26.)-30.)(<.$19.(1:.R5.)(<.$19.(1:.R6.)(<.$19.(1:.R7.)(<.$19.(1:.R8.)(<.$19.(1:.R9.)(<.$19.(1:.R:.)(>.$19.))))))))P,(1;.$;.R3.R2.(5.(18.&40.R27.)-30.))P,(4.R3.(1<.(18.&40.R28.)+30.))P,(4.+30.(18.&40.R29.))(1=.$;.Lms',$1>.(8.(10.$1>.R1.(1?.(20.R?.R2;.R2:.R29.R28.R27.R26.R>.R=.(21.=)R25.R24.R23.R22.R21.R20.R1?.R<.R;.R:.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R9.(22.R?.)R8.(23.(0.&40.))R7.(24.$;.)))(1;.$;.R7.R6.(18.&40.R2;.)))(1?.(20.R10.(25.&40.(5.(18.&40.R2:.)-30.))R29.R28.R27.R26.R25.R?.(25.&40.$26.)(25.&40.-1.)R24.R23.R22.R21.R20.R1?.R1>.(25.&40.-1.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R8.(25.&40.+40600.)R7.(23.(0.&40.))R6.(24.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L27904922626.48L51711223320.4700000:00>S2sp2lo2LOS2sp". (* [comment removed for export] *)
#[using="hRP"] Lemma rbig_fail2b_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pra',(0.&40.)Pnw,(0.&40.)Ps1w,(0.&40.)Prav,(0.&40.)Ps0v,(0.&40.)Ps1v,(0.&40.)Ps2v,(0.&40.)Ps3v,(0.&40.)Ps4v,(0.&40.)PF,(15.&5.(0.&40.))Pfc,(0.&20.)Pm,$16.Plo,$2.P,(17.$;.R2.(5.(18.&40.R29.)-30.)(<.$19.(1:.R5.)(<.$19.(1:.R6.)(<.$19.(1:.R7.)(<.$19.(1:.R8.)(<.$19.(1:.R9.)(<.$19.(1:.R:.)(>.$19.))))))))P,(1;.$;.R3.R2.(5.(18.&40.R2:.)-30.))P,(4.R3.(1<.(18.&40.R2;.)+30.))P,(4.+30.(18.&40.R2<.))(1=.$;.Lms',$1>.(8.(10.$1>.R1.(1?.(20.R?.R2>.R2=.R2<.R2;.R2:.R29.R>.R=.(21.=)R27.R26.R25.R24.R23.R22.R21.R<.R;.R:.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R9.(22.R?.)R8.(23.(0.&40.))R7.(24.$;.)))(1;.$;.R7.R6.(18.&40.R2>.)))(1?.(20.R11.(25.&40.(5.(18.&40.R2=.)-30.))R2<.R2;.R2:.R29.R28.R10.R?.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R8.(25.&40.+407<<.)R7.(23.(0.&40.))R6.(24.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L14475535759.36L2389669903.36 000001002SS". (* [comment removed for export] *)
#[using="hRP"] Lemma rbig_fail2a_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pra',(0.&40.)Pnw,(0.&40.)Pxw,(0.&40.)Pndw,(0.&40.)PF,(15.&5.(0.&40.))Pfc,(0.&20.)Pm,$16.P,(17.$;.R1.$26.(<.$19.(27.(21.=))(>.$19.)))(1=.$;.Lms',$1>.(10.$1>.R1.(1?.(20.(25.&40.+407<<.)(25.&40.(5.(18.&40.R22.)-30.))R21.R20.R1?.R1>.R1=.R8.(25.&40.$26.)R7.R6.R1;.R1:.R19.R18.R17.R16.R15.R6.R7.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R5.(25.&40.$28.)R4.(23.(0.&40.))R3.(24.$;.)))(1?.(20.R8.(25.&40.(5.(18.&40.R21.)-30.))R20.R1?.R1>.R1=.R1<.R7.(25.&40.$26.)(21.=)R1;.R1:.R19.R18.R17.R16.R15.R14.R5.R6.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R4.(25.&40.+406?4.)R3.(23.(0.&40.))R2.(24.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until m. intros LK. unfold RMLOCK in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step.
  eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x407c0)) with (Z_to_bv 64 0x407c0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "Lms',$1>.(29.(0.&40.)La0,(0.&40.)(29.(0.&40.)La1,(0.&40.)(29.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(8.(10.$1>.R4.(1?.(20.(25.&40.+406?4.)(25.&40.(5.(18.&40.O25.)-30.))O24.O23.O1;.O1:.O19.O>.(25.&40.$26.)R3.R2.O18.O17.O16.O15.O14.O13.(25.&40.-1.)(25.&40.(5.O1.+14.))O=.O22.O21.O20.O1?.O1>.O1=.O1<.O12.O11.O10.O?.)O6.(25.&40.$2:.)O5.(23.(0.&40.))R1.(24.$;.)))(8.(2;.(<.(2<.$2.$2.)(2=.$2.$2.(5.$2>.+350.)(5.$2>.+370.))(<.(2<.$2.$2.)(2=.$2.$2.(5.$2>.+390.)(5.$2>.+391.))(>.(2<.$2.$2.))))O2.R1.)(8.(2?.$;.O2.R1.)(8.(30.$;.R1.)(8.(1;.$;.R1.O4.(5.(18.&40.O25.)-30.))(8.(17.$;.R1.(5.(18.&40.O25.)-30.)(<.$19.(1:.O7.)(<.$19.(1:.O8.)(<.$19.(1:.O9.)(<.$19.(1:.O:.)(<.$19.(1:.O;.)(<.$19.(1:.O<.)(>.$19.))))))))(31.VhRP,O3.R1.))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10310309893.56L11674666328.61L11954261848.61L1281580983.71 L14195568791.61L14195568791.62L16075584200.58L21432414376.61L25069450385.71L2994607484.70 L45997765831.71L47283939617.61L47584419917.61L53144248697.58L54996280770.71L55085309993.61L5634884155.63 L56906373800.61L57020095031.57L58113841832.61L59308628304.58L60783005528.61L61665771703.60L68179570553.61L9962406557.61 00000800900:00?00d01I01Q01R01W01^02802902:02O02T02U02`02a02b02c02g02h03903:03;S2st3SEQSSS3LENS3hRP3RCB2sp2lo2LO3ILO2HB5Ha_st5Hl_stS3hRP3RCB2sp2lo2LO3ILO2HB5Ha_st5Hl_stS2st3SEQSS3LENS2ns2NSS3hRP3RCB2sp2lo2LO3ILO3LENSSS2xw2st3SEQ3XNE2XR2K2S3LENSS2st3SEQ2K2SSSS2K1SS2xw2st3XNE2XR2K2SS". (* [comment removed for export] *)
#[using="Type"] Lemma rbig_seq_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pra',(0.&40.)Pnw,(0.&40.)Pxw,(0.&40.)Prav,(0.&40.)Ps0v,(0.&40.)Ps1v,(0.&40.)Ps2v,(0.&40.)Ps3v,(0.&40.)Ps4v,(0.&40.)PF,(15.&5.(0.&40.))Pfc,(0.&20.)Pm,$16.Plo,$2.Pn,$2.Pst,$32.P,(31.VhRP,R1.R4.)P,(8.(4.=(33.(34.R2.)))(9.(33.(34.R2.))+100.))P,(35.(10.$2.(18.&40.R?.)(1<.(7.+2.+40.)+1.)))P,(17.$;.R7.(5.(18.&40.R2;.)-30.)(<.$19.(1:.R:.)(<.$19.(1:.R;.)(<.$19.(1:.R<.)(<.$19.(1:.R=.)(<.$19.(1:.R>.)(<.$19.(1:.R?.)(>.$19.))))))))P,(1;.$;.R8.R7.(5.(18.&40.R2<.)-30.))P,(4.R8.(1<.(18.&40.R2=.)+30.))P,(4.(36.VhRP,)R9.)P,(30.$;.R;.)(1=.$;.(37.R30.R2?.R2>.R22.R21.R20.R1?.R1>.R1=.R1<.R2=.R2<.R2;.R29.R28.R27.R26.R25.R24.R1;.R1:.R19.R18.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R;.(38.R9.)R<.R:.)(1?.(20.R17.(25.&40.(5.(18.&40.R30.)-30.))R2?.R2>.R2=.R2<.R2;.R16.(25.&40.$26.)R15.R2:.R29.R28.R27.R26.R25.R24.(25.&40.-1.)(25.&40.(5.R:.+14.))R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R>.(25.&40.+40600.)R=.(23.(0.&40.))R<.(24.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until st. intros MR SEQ XNE FR ST LO ILO MI.
  pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
  dpose MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
  rceilb; unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry in *. unfold ctx_tail_cells in C6.
  replace (512968 + 912) with 513880 in C6 by reflexivity. replace (512968 + 848) with 513816 in US by reflexivity.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.
  (* [comment removed for export] *)
  step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.
  (* [comment removed for export] *)
  step. rewrite ?zxb_b8 by lia. step.
  (* [comment removed for export] *)
  assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
    rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk rsegs mj lo (bv_unsigned sp + -48) -> mem_inv rsegs mj ->
    munch [(512968 + 848, 512968 + 880); (512968 + 912, 512968 + 913)]%Z m mj -> wmono rsegs m mj ->
    evt rsegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 512960)
               (Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x406ec) fc None mj (seg_rom rsegs))).
  { intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
    dpose MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (512968 + 912) with 513880 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 513880) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    raw_store_finishR (512968 + 912) [b8 ns] FRj STj MUj WMj SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. deexists 3. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
    eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    assert (UZ : u8arr rsegs m1 513816 (zeros 32)).
    { apply (u8arr_of_rw_cells rsegs m1 513816 32). apply (rw_cells_congr rsegs m1 513816 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
    clear USC.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with MUc : munch _ m m1, WMc : wmono rsegs m m1 |- _ =>
    assert (MRz : rmrep stz m1);
    [ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold RCTX; replace (512968 + 912) with 513880 by reflexivity;
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX, FRc : rw_cells rsegs ?mX (bv_unsigned sp + -48) _, STc : stk rsegs ?mX _ _, MIc : mem_inv rsegs ?mX |- _ =>
      eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : rceil <= lo.

Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@L11899637627.113L12352870321.99 L12701517829.105L12701517829.114L12701517829.115L12701536187.116L13568959351.116L13628143591.110L15032598273.109L15468669819.113L18926678684.109L21473875220.107L21473875220.116L21473875220.117L21908342439.121L2383826871.99  L24689431572.107L24689431572.116L24689431572.117L26392564056.99 L26439369980.110L26824225136.119L30652567469.109L32391122337.109L35214505915.110L36644302768.110L38297493895.116L39651076098.116L46177259928.101L47443082127.107L47443082127.116L47443082127.117L47803475360.110L49234157850.105L49234157850.114L49234157850.115L55347981555.113L55850107689.110L56093935916.99 L56338360900.109L57271765628.109L58288111936.95 L59309005136.115L59309005265.115L59309005398.115L59309005527.115L59309005652.115L59309005781.115L59314923118.102L59314938599.124L59314938599.12700000=00P00c01601I01W01c02\02d02e02m03k04m05k06@06^07^08b09b09l0:`0:o0;@0;M0<M0<Z0=;0=G0=]0>P0?G0@80@H0@Y0@j0A;0AH0AR0A_0Al0B60BG0C10C[0DE0Do0EY0FC0FX0G:0H;S2st1g1c1G2CRS2st1g1x1n1G2NR3XRUS2st1g1x1G2gw2HG2HBS2st1g1x1G2gw2HG2HBS2st1g1x1G2gw2HG2HBS2st1g1x1G3LENS2st1g1G3LENS3hRP2st1g1x1n2lo1G2NR3CLO2sp2gw2LO2XC3XRU2HB5Ha_st5Hl_stS2st1g1GFS2st1g1GS2st1g1x1n1G2NR2gw2HG3GI13GI22X03XRU3XI13XI22GX2HB5Ha_st5Hl_stS2st1g3rid1x1n1G2NR2gw2HG3GI13GI22X03XRU3XI13XI22GX2HB5Ha_st5Hl_stS2st1g1x1n1G2NR2gw2HG3GI13GI22X03XRU3XI13XI22GX2HB5Ha_st5Hl_stS2st1g1G3GI13GI21r2H0S3hRP2st1g1x1n1G2NR3RCB2XC3XRUS2st1g1x1n1G2NR2gw2HG4Gpos3GI13GI23XRU3XI13XI22GX2HB5Ha_st5Hl_stS2st1g3rid1x1n1G2NR2gw2HG4Gpos3GI13GI23XRU3XI13XI22GX2HB5Ha_st5Hl_stS2st1g1x1n1G2NR2gw2HG4Gpos3GI13GI23XRU3XI13XI22GX2HB5Ha_st5Hl_stS2st1g1x1GS2st1g1x1n1G2NR2gw3GI13GI23XRU3XI22GX2HB5Ha_st5Hl_stS2st1g1x1G1a2HaS2st1g1n1G2NR3XRUS2st1g1n1G2NRS2st1g1x1n1G2NR2gw2HG4Gpos3GI13GI23XRU3XI13XI22GX2HB5Ha_st5Hl_stS2st1g1n1G2NRS3hRP2st1g2lo1G3CLO3RCB2sp2LO3LENS2st1g1G3LENS2st1g1n1G2NR3XRU1o2HoS3hRP2st1g1x2lo1G3CLO2sp2gw2HG2LO2GC2HB5Ha_st5Hl_stS3hRP2st1g3rid1n2lo1G3CLO2sp2gw2HG2LO2GC2HB5Ha_st5Hl_stS3hRP2st1g2lo1G3CLO2sp2gw2HG2LO2GC2HB5Ha_st5Hl_stS2st1g1n1G2NR2LRS2st1g1G2gw2HG2HBS2st1g1G2gw2HG2HBS2st1g1G2gw2HG2HBS2st1g1c1G2CRS2st1g1n1GS2st1g1x1G2X0S2st1g1n1G2NRS2st1g1n1GS2st1g1n1G2NR3XRUS2st1g1x1n1G2NR3GI13GI23XRU3XI22GX1a2Ha2R1S2st1g1x1n1G2NR3GI13GI23XRU3XI22GX1a2Ha2R2S2st1g1x1n1G2NR3GI13GI23XRU3XI22GX1a2Ha2R3S2st1g1x1n1G2NR3GI13GI23XRU3XI22GX1a2Ha2R4S2st1g1x1n1G2NR3GI13GI23XRU3XI22GX1a2Ha2R5S2st1g1x1n1G2NR3GI13GI23XRU3XI22GX1a2Ha2R6S2st1g1G2gw2HG4Gpos1KS2st1g1x1G1a2Ha2rq2Rq1D1n2NR3XRU1HS2st1g1x1G1a2Ha2ak3Rak3rga2Ca3Sa11D1n2NR3XRU1H1b2Rb2rb2Cb3Sb13Sb0". (* [comment removed for export] *)
#[using="MR TK G0 MSL RR GN AN SHN HC CR NR CLO"] Lemma rbig_succ_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_bigw ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pra',(0.&40.)Pgw,(0.&40.)Ps0v,(0.&40.)Ps1v,(0.&40.)Ps2v,(0.&40.)Ps3v,(0.&40.)Ps4v,(0.&40.)Prav,(0.&40.)PF,(15.&5.(0.&40.))Pfc,(0.&20.)P,(10.$2.(18.&40.R9.)VG,)P,(17.$;.Vm,(5.(18.&40.R24.)-30.)(<.$19.(1:.R5.)(<.$19.(1:.R6.)(<.$19.(1:.R7.)(<.$19.(1:.R8.)(<.$19.(1:.R9.)(<.$19.(1:.R4.)(>.$19.))))))))P,(1;.$;.Vm,Vlo,(5.(18.&40.R25.)-30.))P,(4.Vlo,(1<.(18.&40.R26.)+30.))P,(30.$;.Vm,)(1=.$;.Lms',$1>.(29.(0.&40.)La0',(0.&40.)(29.(0.&40.)La1',(0.&40.)(29.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(8.(10.$1>.R4.(1?.(20.R13.(25.&40.(5.(18.&40.R2<.)-30.))R2;.R2:.R29.R28.R27.(25.&40.Vn,)(25.&40.$26.)R3.R2.R25.R24.R23.R22.R21.R20.R12.(21.=)(21.Vx,)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R;.(25.&40.+4088<.)R:.(23.(0.&40.))R1.(24.$;.)))(8.(2;.(<.(2<.$2.$2.)(2=.$2.$2.VG,(5.VG,+28.))(<.(2<.$2.$2.)(2=.$2.$2.Vx,(5.Vx,+8.))(<.(2<.$2.$2.)(2=.$2.$2.(5.$2>.+<.)(5.$2>.+10.))(>.(2<.$2.$2.)))))Vm,R1.)(8.(2?.$;.Vm,R1.)(8.(30.$;.R1.)(8.(1;.$;.R1.Vlo,(5.(18.&40.R2<.)-30.))(8.(17.$;.R1.(5.(18.&40.R2<.)-30.)(<.$19.(1:.R=.)(<.$19.(1:.R>.)(<.$19.(1:.R?.)(<.$19.(1:.R10.)(<.$19.(1:.R11.)(<.$19.(1:.R<.)(>.$19.))))))))(8.(31.VhRP,(39.Vst,Vg,Vrid,Vn,(3:.(5.Vc,+1.)))R1.)(3;.(39.Vst,Vg,Vrid,Vn,(3:.(5.Vc,+1.))))))))))))))(1?.(20.R?.(25.&40.(5.(18.&40.R28.)-30.))R27.R26.R25.R24.R23.(25.&40.Vn,)(25.&40.$26.)R>.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.(25.&40.(5.Vn,+14.))(21.Vx,)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R7.(25.&40.+406?4.)R6.(23.(0.&40.))Vm,(24.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
  set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
  pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose MR as (WF & (CX1 & _) & _ & AR & GRP & SH). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  dpose (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
  fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
  change (meta_word meta0) with 0 in CH.
  ddestruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
  pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
  destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].
  (* [comment removed for export] *)
  destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
  assert (HDR : rw_cells rsegs m x [C8 (wz 0); C1 (b8 0)]).
  { apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
    - cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
      apply rzeros_bytes_at; [lia| cbn; rceilb; lia|].
      intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
      unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
    - cbn. eapply wr_at_sub; [exact XW| lia| lia]. }
  (* [comment removed for export] *)
  pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
  rewrite <- HG in CH.
  rceilb; unfold RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  unfold ctx_head_cells in CX1. rewrite HC in CX1.
  pose proof (rw_cells_prefix rsegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
  assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl rsegs m) as WMa.
  step.
  assert (PWX : pw st (Some (rid, 0)) = wz x).
  { unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHA : rw_cells rsegs mX (conc st g) (meta_cells st (big_metaA rid)));
    [ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
      change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
    | pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
  clear MUa WMa CHA.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
  cbv delta [wz]. step.
  set (stA := put_meta g (big_metaA rid) st) in MRA.
  destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
  { eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
      ddestruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
      ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
      pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      + rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
        destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
        cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - unfold RGOT_SSP in R5. lia.
    - unfold RSSP_GUARD in R6. lia. }
  clear MRB0 MUb WMb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
  { eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
    change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
    unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
  clear MRB1.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
  rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
  replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
  pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
  step. step. step.
  set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
  lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHC : rw_cells rsegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
    [ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
      change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
    | pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
  clear MUc WMc CHC MRB.
  (* [comment removed for export] *)
  step. rewrite (sx32_wz_sxv c) by lia. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX 512968 _ |- _ =>
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 512980) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
    clear H end.
  st1. rewrite le4_swrap_succ by lia.
  set (stC := put_meta g (big_meta rid n) stB) in MRC.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
  clear MRC.
  raw_store_finishR (512968 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. deexists 3. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact MRD| exact TKB].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SUCC.

End RP_1.
