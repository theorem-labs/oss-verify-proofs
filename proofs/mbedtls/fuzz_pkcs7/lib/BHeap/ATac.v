(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export StepA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Export AImg.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac addr_diff E A ::=
  let k := addr_diff_raw E A in
  lazymatch eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 8192)) with true => k end.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ATac () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "LinuxProcessSemantics.Riscv.Sem.reg_get"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.ones"; "Stdlib.ZArith.BinInt.Z.lnot"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma land_m1_64 : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_accesses_ecall : ltac2:(CDefT.buildp (gd_tbl_ATac ()) "Psegs,(0.$1.)PR,(2.&5.(3.&40.))PF,(2.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(4.(3.&40.))Pm,P,(3.&40.)(4.(3.&8.))Pro,P,(3.&40.)(4.(3.&8.))Pw,(3.&20.)P,(5.(4.(3.&20.))(6.R9.R6.)(7.(3.&20.)R1.))P,(5.$8.(9.R2.)$:.)(5.(;.(<.$=.))(>.R;.(?.R:.R9.R8.R7.R6.R5.R4.))(10.(<.$=.)(11.$=.(12.R:.R9.R8.(13.R:.(14.&5.+11.$15.))R7.R6.R5.R4.)(16.$17.))))")
(* [comment removed for export] *).
Proof.
  intros segs R F pc fc rv m ro w Hf He.
  unfold step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.

#[using="Type"] Lemma evtA_ecall : ltac2:(CDefT.buildp (gd_tbl_ATac ()) "Psegs,(0.$1.)PL,$18.PCS,P,$19.SpPQ,P,$=.SpPR,(2.&5.(3.&40.))PF,(2.&5.(3.&40.))Ppc,$19.Pfc,(3.&20.)Prv,(4.(3.&40.))Pm,P,(3.&40.)(4.(3.&8.))Pw,(3.&20.)P,(5.(4.(3.&20.))(6.R;.(1:.&40.R5.))(7.(3.&20.)R1.))P,(5.$8.(9.R2.)$:.)P,A1.R:.(12.R9.R8.(1:.&40.R7.)(13.R9.(14.&5.+11.$15.))R6.R5.R4.(1;.R=.))(1<.R>.R=.R<.R;.(?.R:.R9.(1:.&40.R8.)R7.R6.R5.(1;.R>.)))")
(* [comment removed for export] *).
Proof.
  intros segs L CS Q R F pc fc rv m w Hf He HQ.
  eapply evtA_step; [| apply acc_ok_nil | apply evtA_done; exact HQ].
  split; [reflexivity|]. apply (step_accesses_ecall segs R F (Z_to_bv 64 pc) fc rv m (seg_rom segs) w Hf He).
Qed.

(* [comment removed for export] *)
End ARUN_1.
Ltac stepA_ecall :=
  lazymatch goal with
  | |- evtA ?segs ?L ?CS ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w => apply (evtA_ecall segs L CS Q R F pc fc rv m w); [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.

(* [comment removed for export] *)
Section ARUN_2. Context {hAR : arun}.
#[using="Type"] Lemma land_clear_low : ltac2:(CDefT.buildp (gd_tbl_ATac ()) "Px,$19.Pk,$19.P,(1=.(1>.=R2.)(1?.R2.(20.+2.+40.)))P,(1=.(1>.=R2.)(1>.R2.+40.))(5.$19.(21.R4.(21.(22.+40.)(23.(22.R3.))))(24.(25.R4.(20.+2.R3.))(20.+2.R3.)))")
(* [comment removed for export] *).
Proof.
  intros x k Hx Hk.
  rewrite Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_align12 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx. change 18446744073709547520 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 12))).
  rewrite land_clear_low by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_align4 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551600 = x / 16 * 16.
Proof.
  intros x Hx. change 18446744073709551600 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 4))).
  rewrite land_clear_low by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_align3 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx. change 18446744073709551608 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 3))).
  rewrite land_clear_low by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sx32_small : forall v, 0 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Lemma swrap32_small : forall v, 0 <= v < 2^31 -> bv_swrap 32 v = v.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Lemma wrap32_small : forall v, 0 <= v < 2^32 -> bv_wrap 32 v = v.
Proof. intros v Hv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. apply Z.mod_small. lia. Qed.

End ARUN_2.
