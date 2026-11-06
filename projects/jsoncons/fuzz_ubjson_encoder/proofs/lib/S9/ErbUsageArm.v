(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec ShapeAlg SpinAlg Spec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 LibIface LibIfaceAB
  DrvKitA As0DrvKitA Eb0DrvEntry Eb0Drv_defs Eb0DrvLib Eb0DrvStdio Eb0DrvA ErbDrvE2 ErbMainPhaseA ErbDrvMain ErbDiagArmRefuse ErbDiagStrK ErbDiagArmOpen ErbDiagArmUsage ErbUsageEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Theorem dg_usage_ok : forall scfg L C IL, dg_usage_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & HDGS & _) Hsp Hal DL _] a0s fs0 p0 can cr0 A0 [PLO STR NONUL PLEN PDEF] SAH.
  unfold usage_kA. intros vals R M model HL P0 P1 P3 HR HK DI F1 F2.
  destruct usage_itinerary_okA as (_ & _ & FRB & OKb).
  set (E := ENVA [] vals) in *.
  assert (FR : forall off v, existsb (kentry_eqb (KWord (SA (EVar 0) off) 8 v)) knU = true ->
               rdn ASEGS (mrestrict (ahid A0 model) M) (Z_to_bv 64 (bv_unsigned sp0 + off)) 8 = Some (word_to_le_bytes 8 (edenot E v))).
  { intros off v Hb. exact (kword_sp sp0 vals _ _ knU off 8 v HK Hb P0). }
  apply (dg_usage_site scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG HDGS M0 [] PropExec.fx0 vals knU R M model [] [] cr0 A0 fs0 p0 a0s
           (fun k => if Z.eqb k 64 then edenot E (EAlu ALU_ADD (EVar 0) (ELit 8)) else if Z.eqb k 72 then edenot E (EVar 2) else if Z.eqb k 80 then edenot E (ELit 691376)
                     else if Z.eqb k 88 then edenot E (EVar 25) else Z_to_bv 64 0) HK OKb P0).
  - regv HR (1%bv : reg). reflexivity.
  - regv HR (2%bv : reg). cbn [edenot ev ENVA E]. rewrite P0. apply alu_add_w_litA.
  - regv HR (4%bv : reg). reflexivity.
  - regv HR (8%bv : reg). reflexivity.
  - regv HR (10%bv : reg). reflexivity.
  - regv HR (11%bv : reg). reflexivity.
  - regv HR (12%bv : reg). cbn [edenot ev ENVA E]. exact P1.
  - exact DI.
  - exact F2.
  - rewrite F1. vm_compute. reflexivity.
  - exact (STR_ATA ar sp0 M0 A0 p0 a0s PLO STR NONUL PLEN PDEF SAH).
  - replace (bv_unsigned sp0 - 56) with (bv_unsigned sp0 + -56) by ring. exact (FR (-56) (ELit 1172444) eq_refl).
  - intros k Hk. cbn [In] in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [Z.eqb Pos.eqb].
    + replace (bv_unsigned sp0 - 64) with (bv_unsigned sp0 + -64) by ring. exact (FR (-64) (EAlu ALU_ADD (EVar 0) (ELit 8)) eq_refl).
    + replace (bv_unsigned sp0 - 72) with (bv_unsigned sp0 + -72) by ring. exact (FR (-72) (EVar 2) eq_refl).
    + replace (bv_unsigned sp0 - 80) with (bv_unsigned sp0 + -80) by ring. exact (FR (-80) (ELit 691376) eq_refl).
    + replace (bv_unsigned sp0 - 88) with (bv_unsigned sp0 + -88) by ring. exact (FR (-88) (EVar 25) eq_refl).
    + replace (bv_unsigned sp0 - 96) with (bv_unsigned sp0 + -96) by ring. exact (FR (-96) (ELit 0) eq_refl).
    + replace (bv_unsigned sp0 - 104) with (bv_unsigned sp0 + -104) by ring. exact (FR (-104) (ELit 0) eq_refl).
    + replace (bv_unsigned sp0 - 112) with (bv_unsigned sp0 + -112) by ring. exact (FR (-112) (ELit 0) eq_refl).
    + replace (bv_unsigned sp0 - 120) with (bv_unsigned sp0 + -120) by ring. exact (FR (-120) (ELit 0) eq_refl).
Qed.

Theorem as0_usage_closed : forall scfg (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (BUDGET : Z),
  2 ^ 40 + 2 ^ 20 + EbrInv.PRIMCAP <= BUDGET -> BUDGET <= 2 ^ 41 ->
  inst_ok_stmt scfg L C BUDGET -> free_null_stmt scfg L BUDGET -> h4e_stmt BUDGET -> icpt_ok_stmt scfg L IL BUDGET -> dla_ok_stmt scfg L C IL -> drv_consts_stmt L C IL ->
  usage_stmt scfg.
Proof.
  intros scfg L C IL BUDGET B1 B2 INST FN H4 ICPT DLA CONSTS.
  exact (as0_usage scfg L C IL BUDGET B1 B2 INST FN H4 ICPT DLA CONSTS (dg_usage_ok scfg L C IL)).
Qed.
