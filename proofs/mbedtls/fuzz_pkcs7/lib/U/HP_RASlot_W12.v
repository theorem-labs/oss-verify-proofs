(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W12.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RF_malloc_entry HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RASlot_W2 HP_RASlot_W4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W12 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_W4.rt1_regs"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_meta_entry"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_slot_entry"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L2157636948.35 L42794413067.35L6753472924.34 L7442835684.34 00000400<00=00DS2scS2sc3SZRSS2sc2SC". (* [comment removed for export] *)
#[using="SC"] Lemma rag_entry_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W12 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))P,(3.$4.R1.)(5.$4.Lms',$6.(7.$6.R1.(8.(9.Vsc,(:.&40.+40:=0.)R1>.R1=.R1<.R1;.R1:.R19.R18.(:.&40.(;.$<.(=.Vsc,+2.)))R16.R15.R14.R13.R12.R11.R10.R?.(:.&40.(=.Vsc,+2.))(>.(?.Vsc,))(:.&40.$<.)R;.R:.R9.R8.R7.R6.)R5.(:.&40.$10.)R4.(11.(0.&40.))R3.(12.$4.)))(8.(9.Vsc,R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(:.&40.+40:;8.)R3.(11.(0.&40.))R2.(12.$4.)))")
(* [comment removed for export] *).
Proof.
  intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *.
  pose proof (size_class_range sc SC) as SZR.
  step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
  pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (94460 + 2 * sc) with (94460 + sc * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  step. apply evt_done. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End AG1.

(* [comment removed for export] *)
#[using="Type"] Lemma rag_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
  0 <= gm < 2^64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if gm =? 0 then 0x41138 else 0x40adc)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40ad0) fc None m (seg_rom rsegs)).
Proof.
  intros until gm. intros GR MI.
  step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
  - replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

#[using="SZC CR SMALL"] Lemma rstc_q_eq : j = stc_q (szc * cnt).
Proof.
  unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "01T0?L10022931269.63L10023289312.64L11028254010.69L12076517061.66L12712880528.59L1482069293.72 L16075583823.66L16916892674.59L18179265889.53L18179724641.55L18181367782.52L18395536607.49L18468417428.60L22796385821.57L23235732884.71L24140338504.74L25109010663.71L26454810024.61L27316758952.49L27648159986.69L27688007078.63L27690091296.62L28155396397.61L30261996870.66L31323011143.72L31464074128.71L31464074129.64L31799012504.72L32185887926.71L32509216314.69L35516470224.66L35842097472.70L35842273781.71L36759189123.65L36761272705.66L37991463626.66L40823607660.62L40829623250.46L41415828429.53L41416053612.60L41417920842.52L41417920844.59L41418040267.74L41652169568.60L42704510862.46L43071640411.60L43073741533.57L43393816798.72L4351261724.71 L4353507130.72 L4353685161.72 L43901314518.69L45615793312.59L46778126076.54L48775325161.64L49098857183.70L49099320514.48L50998141849.60L51185923522.64L51792457914.74L52488874831.62L52514079877.72L52514229526.72L53279723706.69L53517140246.69L53519091638.72L53519207973.72L55899452735.47L56775177115.66L56777654300.71L5687589883.74 L5690084950.56 L5690538106.67 L5690538235.64 L5690538876.61 L5690555260.58 L57394758142.71L5742896305.57 L5742896310.52 L5744989872.54 L59251176999.59L59251192621.60L59603018663.64L63370523563.65L65199789371.66L66468437330.63L67482146131.60L67507599744.65L6753458106.52 L6753458109.57 L6753473980.71 L6753473981.64 L67961326483.66L679672258.69  L7178147913.66 L7620900481.57 L7620900486.52 L8396965519.62 L9540561407.74 L9627047418.69 00000G00^01?01`02<02U02m03B03W03o04D04]05305L05e06L06l07I07^08C08b09A09W09n0:O0:f0;=0;^0<D0<e0=90=R0=k0>M0>o0?F0?a0@10@C0@U0@g0A?0Ab0B80BQ0Bl0CD0C]0D60DO0Dh0EM0Ei0F>0FU0GA0GZ0H00HD0Hk0IC0IU0Ig0JL0Jm0K?0KQ0Kj0L20LG0Lj0M?0M`0N>0NY0O10OF0O^0P30PH0P^0Q40QH0Qf0RF0Rd0S?0SW0Si0T>0TP0Tb0U60U[0V;0VS0Vh0W@0Wc0XHS3szc3cnt2n'1j1q1k1i2IRS3szc3cnt2n'1j1q1k1i2IRS3szc3cnt2n'1j1q1x2v12v22w22w32w4S3szc3cnt2n'1j1q1x2v12v22w22w32R5S3szc3cnt2n'1j1q1x2v12v23RV2S3szc3cnt2n'1j1q1k2i13SR2S3szc3cnt2n'1j1q1k1i3SR1S3szc3cnt2n'1j1q1k2P2S3szc3cnt2n'1j1q1x2XRS3szc3cnt2n'1j1q1x2XR2v1S3szc3cnt2n'1j1q1x2XRS3szc3cnt2n'1j2PR1q3Q101xS3szc3cnt2n'1j1q1k3K13S3szc3cnt2n'1j1q1x2v13RV1S3szc3cnt2n'1j1q1k2i13SR2S3szc3cnt2n'1j1q1x1k2v12v22w22w32w43K13S3szc3cnt2n'1j1q1k3K131i2i11c2HcS3szc3cnt2n'1j1q1x1k3K132EK1iS3szc3cnt2n'1j1q4SCRjS3szc3cnt2n'1j1q1x2v12v22w22w32w43RW4S3szc3cnt2n'1j1q1x2v12v22w23RW2S3szc3cnt2n'1j1q1x2v12v22w23RW2S3szc3cnt2n'1j1q1k3K13S3szc3cnt2n'1j1q1k1i2IRS3szc3cnt2n'1j1q1x1k3K132EX2i12LTS3szc3cnt2n'1j1q1k1i2IRS3szc3cnt2n'1j1q1k1i2IRS3szc3cnt2n'1j1q1x1k3K132EX2i12GES3szc3cnt2n'1j1q3Q102v12v22w22w32w42LGS3szc3cnt2n'1j1q1x2v12v22w22w32w4S3szc3cnt2n'1j1q1k1iS3szc3cnt2n'1j1q1k2i13I1RS3szc3cnt2n'1j1q1k2i13I1RS3szc3cnt2n'1j1q1x2v12v22w22w33RW3S3szc3cnt2n'1j1q1x2v12v22w22w33RW3S3szc3cnt2n'1j1q1k1i2IRS3szc3cnt2n'1j1q1x2v12v22w2S3szc3cnt2n'1j1qS3szc3cnt2n'1j1q1xS3szc3cnt2n'1j1q1kS3szc3cnt2n'1j1q1xS3szc3cnt2n'1j1q1x2v12v2S3szc3cnt2n'1j1q1x1k2v12v22w22w32w4S3szc3cnt2n'1j1q1k3K13S3szc3cnt5SMALL2n'1j2PR1qS3szc3cnt2n'1j1q1x2R12v12v2S3szc3cnt2n'1j1q1x2R12v1S3szc3cnt2n'1j1q1k2i13I1RS3szc3cnt2n'1j1q1k2i13I1RS3szc3cnt2n'1j1q1k2i13I1RS3szc3cnt2n'1j1q1k2i13I1RS3szc3cnt2n'1j1q1x2v12v22w22w32w43RW4S3szc3cnt2n'1j1q1x2v12v23RV2S3szc3cnt2n'1j1q1x2R2S3szc3cnt2n'1j1q1k1i2IRS3szc3cnt5SMALL2n'1j2PR1q1x1k2v12v22w22w32w4S3szc3cnt5SMALL2n'1j2PR1qS3szc3cnt2n'1j1q1k3K13S3szc3cnt2n'1j1q1k1iS3szc3cnt2n'1j1q1x1k2v12v22w22w32w43K13S3szc3cnt2n'1j1q3Q101k1iS3szc3cnt2n'1j1q1kS3szc3cnt2n'1j1q1kS3szc3cnt2n'1j1q1x2v12v22w22w32w43RW4S3szc3cnt2n'1j1q1x2v12v22w22w32w4S3szc3cnt2n'1j1q1kS3szc3cnt2n'1j1q1kS3szc3cnt5SMALL2n'1j2PR1qS1q2QR1kS3szc3cnt2n'1j1q2QR1kS3szc3cnt2n'1j1q1x1k2v12v22w22w32w4S3szc3cnt2n'1j1q1x2v1S3szc3cnt2n'1j1q1x2v12v22w22w32w4S3szc3cnt2n'1j1q1x2v12v22w22w3S3szc3cnt2n'1j1q1x2v12v22w2S3szc3cnt2n'1j1q1x2v12v2S3szc3cnt2n'1j1q1k2i1S3szc3cnt2n'1j1q1x2XR2v1S3szc3cnt2n'1j1q1x2XRS3szc3cnt2n'1j1q1x2XRS3szc3cnt2n'1j1q1k3K13S3szc3cnt2n'1j1q1k3K13S3szc3cnt2n'1j1q1k1iS3szc3cnt2n'1j1q1x2v12v22w22w3S3szc3cnt2n'1j1q1x1k3K132EX1i2K3S3szc3cnt2n'1j1q1x2v12v22w22R4S3szc3cnt2n'1j1q1x2v12v22R3S3szc3cnt2n'1j1q1k1i3SR1S3szc3cnt2n'1j1q1xS3szc3cnt2n'1j1q1x2v1S3szc3cnt2n'1j1q1kS3szc3cnt2n'1j1q1kS3szc3cnt2n'1j1q1k1iS3szc3cnt2n'1j1q1x2v12v22w22w32w43RW4S3szc3cnt2n'1j1q1x1k3K132EX1i2K3S3szc3cnt2n'1j1q1x2XR2v1S3szc3cnt2n'1j1q1x2XRS3szc3cnt2n'1j1q1k3K131iS3szc3cnt2n'1j1q1x1k2v12v22w22w32w4S3szc3cnt2n'1j1q1x2v12v22w22w32w43RW4". (* [comment removed for export] *)
#[using="SZC CR SMALL"] Lemma rnest_call_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W12 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))P,(3.$4.R1.)(5.$4.Lms',$6.(13.(0.&40.)La2',(0.&40.)(13.(0.&40.)La3',(0.&40.)(13.(0.&40.)La4',(0.&40.)(7.$6.R4.(8.(14.(:.&40.+40<;8.)R24.R23.R22.R21.R20.R1?.R1>.R1=.(:.&40.Vj,)(>.Vn',)R3.R2.R1.R18.R17.R16.(:.&40.Vj,)R14.R13.R12.R11.R10.R?.(:.&40.$<.)R>.R=.R<.R;.R:.R9.)R8.(:.&40.$15.)R7.(11.(0.&40.))R6.(12.$4.))))))(8.(14.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(>.(=.(=.Vszc,+10.)Vcnt,))R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.(:.&40.$<.)R:.R9.R8.R7.R6.R5.)R4.(:.&40.+40;>8.)R3.(11.(0.&40.))R2.(12.$4.)))")
(* [comment removed for export] *).
Proof.
  intros until m. intros MI.
  assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
  set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
  pose proof rstc_q_eq as STC. fold q in STC.
  unfold RSIZE_CLASSES, ralloc_slot_entry in *.
  (* [comment removed for export] *)
  assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
    evt rsegs (fun ms' => exists a2'' a3'' a4'',
      ms' = MS (mkR (Z_to_bv 64 0x40cb8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 94460) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 264408) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 94460) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40cac) fc None m (seg_rom rsegs))).
  { intros a0' a2' a3' jv ->.
    pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
    step. rewrite SysStep.sextw_small by lia. step. step.
    apply evt_done. deexists 3. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
  step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
  - (* [comment removed for export] *)
    apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (unfold n' in K; nia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    dpose (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
    assert (K13 : 3 <= k <= 12).
    { unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (94460 + (i + 1) * 2) with (94460 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt rsegs (fun ms' => exists a2'' a3'' a4'',
        ms' = MS (mkR (Z_to_bv 64 0x40cb8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 94460) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 264408) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 68135) (Z_to_bv 64 q) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 94460) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x40c90) fc None m (seg_rom rsegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (94460 + i1 * 2) with (94460 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End STC.
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L35497614361.39L49712512005.39L49718884623.38L59308548964.39L59314923118.3700000100<00=00G00JSS3idx2IR2NEFS3idx2IR1KS1K". (* [comment removed for export] *)
#[using="Type"] Lemma rnest_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
  -1 <= idx < 32 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if idx =? -1 then 0x40d30 else 0x40cbc)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40cb8) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros IR MI.
  step. if_cases K; zify_cond K.
  - replace (idx =? -1) with true.
    2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
        change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
    apply evt_done. reflexivity.
  - replace (idx =? -1) with false.
    2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
    apply evt_done. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
