(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmParSpecs PmLayout PnLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PnSpecsAa
     PmModelFactsA PnStepA PmStep PgSrc PgV8 PgSrcA PnLayout PnModel PnModelFacts PnStatics PnStaticsA PnRunA PnRunAa PnASrcKit PmAUarK PmAUar
     PnDecFacts PnSpecsAXD PnADec128Defs PnADec128K PnADec128S PnADec128F.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADM.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Definition mid_run : Prop :=
  forall (E : dve), dkc L ar HI E ->
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (sigma : Z),
    dmem E M -> L5KA.zeros_at M (vF E + 32) 144 -> 0 <= sigma <= 1 ->
    PNADD.stJ (vR E) (vsp E) (vF E) (vfirst E) sigma (vvp E) R ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (pc' : Z),
      msteps RSEGS (st fx R 0xb2964 M) (st fx' R' pc' M') /\ mem_grows M M' /\ PNADD.agree_but (Wmid E) M M'
      /\ ( (pc' = 0xb2b04 /\ exists e z sd, PNADD.stP (vR E) (vsp E) (vF E) (vfirst E) sigma e z sd R' /\ PNADD.sdigs (vF E) M' z sd
                                          /\ 0 <= e <= 16383 /\ 0 <= z /\ 1 <= sd /\ z + sd <= 36)
           \/ (pc' = 0xb3100 /\ exists hi lo, PNADD.stX (vR E) (vsp E) (vF E) (vfirst E) sigma hi lo R' /\ 0 <= hi < 2 ^ 64 /\ 0 <= lo < 2 ^ 64
                                          /\ PNADD.vp_at M' (vvp E) lo hi) ).

(* [comment removed for export] *)
Definition special_stmt : Prop :=
  forall (E : dve), dkc L ar HI E ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) (sigma hi lo : Z),
    dst L ar HI E Mc modelc LKc Ac -> 0 <= sigma <= 1 -> 0 <= hi < 2 ^ 64 -> 0 <= lo < 2 ^ 64 ->
    PNADD.vp_at (mrestrict (ahid Ac modelc) Mc) (vvp E) lo hi ->
    PNADD.stX (vR E) (vsp E) (vF E) (vfirst E) sigma hi lo Rc ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb3100 Mc modelc) (vK E).

(* [comment removed for export] *)
Lemma out_to_end (E : dve) (X : dkc L ar HI E) (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (ptr ec : Z) :
  dst L ar HI E M' model' LK' A' ->
  PNADD.out_post (vR E) (vsp E) (vF E) (vfl E) (vfirst E) (vr E) ptr ec R' (mrestrict (ahid A' model') M') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb2fa4 M' model') (vK E).
Proof.
  intros ST (SE & _ & Hp & Hec). apply (PNADF.epilogue L ar C HI LY HIok E X fx' R' M' model' LK' A' ptr ec ST SE Hp).
  destruct Hec as [-> | ->]; clear; lia.
Qed.

Theorem signj_of : mid_run -> out_stmt L ar HI -> special_stmt -> PNADS.at_signj L ar HI.
Proof.
  intros MID OUT SPC E X fx Rc Mc modelc LKc Ac sigma ST ZS Hs RJ.
  pose proof (dmem_of L ar C HI LY HIok E X Mc modelc LKc Ac ST) as DM.
  destruct (MID E X fx Rc _ sigma DM ZS Hs RJ) as (fx' & R' & M' & pc' & MS & MG & FRZ & [(-> & e & z & sd & SP & SD & He & Hz & Hsd & Hzs)|(-> & hi & lo & SX & Hhi & Hlo & VP)]).
  - apply (dk_piece L ar C HI LY HIok E X fx fx' Rc R' 0xb2964 0xb2b04 Mc modelc LKc Ac M' (Wmid E) ST MS MG FRZ (fun a Wa => Wa)).
    intros M3 model3 ST3 HID3 VIS3.
    pose proof (dmem_of L ar C HI LY HIok E X M3 model3 LKc Ac ST3) as (MIA3 & _). rewrite HID3, VIS3 in MIA3.
    apply (OUT E X fx' R' M3 model3 LKc Ac sigma e z sd ST3).
    + rewrite HID3, VIS3. unfold PNADD.out_pre. split; [exact SP|]. split; [exact MIA3|]. split; [exact SD|]. split; [exact Hs|]. split; [exact He|]. split; [exact Hz|]. split; [exact Hsd| exact Hzs].
    + intros fx9 R9 M9 model9 LK9 A9 ptr ec ST9 OP9. exact (out_to_end E X fx9 R9 M9 model9 LK9 A9 ptr ec ST9 OP9).
  - apply (dk_piece L ar C HI LY HIok E X fx fx' Rc R' 0xb2964 0xb3100 Mc modelc LKc Ac M' (Wmid E) ST MS MG FRZ (fun a Wa => Wa)).
    intros M3 model3 ST3 HID3 VIS3.
    apply (SPC E X fx' R' M3 model3 LKc Ac sigma hi lo ST3 Hs Hhi Hlo); [| exact SX]. rewrite HID3, VIS3. exact VP.
Qed.

End WithHeap.
End SCFG_1.
End PNADM.
