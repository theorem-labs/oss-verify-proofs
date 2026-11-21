(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflRod6 InflCtx6 InflLoop6 Callee6i
     InflA_LIT InflA_Term InflA_Type2 InflA_Copy InflA_Stored InflA_Head3 InflA_Check3 InflA_Dict2 InflA_Length
     InflA_Match5 InflA_Distext3 InflA_Dist7 InflA_Lenext3 InflA_Len7 InffastSafe IfSpec IfSpec6 InflA_LenF.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Cl2 InflA_Cl3 InflA_Ll.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma zrange32 : forall (P : Z -> Prop) (lo : Z),
  (forall i : nat, (i < 32)%nat -> P (lo + Z.of_nat i)) -> forall m, lo <= m <= lo + 31 -> P m.
Proof.
  intros P lo H m Hm. replace m with (lo + Z.of_nat (Z.to_nat (m - lo))) by lia. apply H. lia.
Qed.

Section Arms.
  Hypothesis MEMCPY : memcpy_run6.
  Variable ROM : (word -> option byte) -> Prop.
  Hypothesis ROMok : forall M, rod6_clear M -> ROM M.
  Hypothesis ADLER : adler32_run6 ROM.
  Hypothesis ITABLE : itable_run6.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.
  Hypothesis CLPINV : InflA_Cl1.InflA_Codelens5.cl_pinv_stmt.

  Theorem arms6 : forall m, HEAD <= m <= SYNC -> arm_stmt m.
  Proof.
    apply (zrange32 arm_stmt HEAD). intros i Hi.
    do 32 (destruct i as [|i];
      [ first [ exact arm_HEAD_sim
              | apply arm_dead_sim; unfold HEAD, FLAGS, HCRC, SYNC; cbn; lia
              | exact arm_DICTID_sim | exact arm_DICT_sim | exact arm_TYPE_sim | exact arm_TYPEDO_sim
              | exact (arm_STORED_sim MEMCPY) | exact (arm_COPY__sim MEMCPY) | exact (arm_COPY_sim MEMCPY)
              | exact (arm_TABLE_sim (lenlens_core_ok ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV)) | exact (arm_LENLENS_sim ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV) | exact (arm_CODELENS_sim ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV)
              | exact (arm_LEN__sim IFAST FFOK FASTOK GFOB FFRAME) | exact (arm_LEN_sim IFAST FFOK FASTOK GFOB FFRAME) | exact arm_LENEXT_sim | exact arm_DIST_sim | exact arm_DISTEXT_sim
              | exact arm_MATCH_sim | exact arm_LIT_sim | exact (arm_CHECK_sim ROM ROMok ADLER) | exact arm_LENGTH_sim
              | exact arm_DONE_sim | exact arm_BAD_sim | exact arm_MEM_sim ]
      |]).
    cbn in Hi. lia.
  Qed.

  Theorem loop6 : loop_stmt.
  Proof. exact (inf_loop_sim arms6). Qed.
End Arms.
End FXG.
