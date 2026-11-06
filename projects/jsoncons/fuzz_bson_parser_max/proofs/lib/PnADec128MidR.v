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
     PnDecFacts PnMemW PnSpecsAXD PnADec128Defs PnADec128K PnADec128S PnADec128F PnADec128M PnADec128Rnd3 PnADec128Mid.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADMR.
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

Theorem mid_run_ok : PNADM.mid_run L ar HI.
Proof.
  intros E X fx R M sigma DM ZS Hs SJ.
  dgeom L ar HI E X.
  pose proof DM as DM'. unfold dmem, PNADD.MIA in DM'.
  destruct DM' as ((MWS & MWF & MFW & MFSW & MFLW & MIMGC & MCSB & MCUAR & MOWN & MC128 & MFLC & MZF6 & MZSIG) & (lo & hi & Hlo & Hhi & VP) & MIMG0 & _).
  set (V := (hi mod 2 ^ 49) * 2 ^ 64 + lo). set (E1 := hi / 4294967296 / 131072).
  assert (FV : 0 <= V < 2 ^ 113).
  { subst V. pose proof (Z.mod_pos_bound hi (2 ^ 49) ltac:(clear; lia)) as B. clear - B Hlo. lia. }
  assert (FE1 : 0 <= E1 < 2 ^ 64).
  { subst E1. split; [apply Z.div_pos; [apply Z.div_pos|]; clear - Hhi; lia|]. apply Z.div_lt_upper_bound; [clear; lia|]. apply Z.div_lt_upper_bound; clear - Hhi; lia. }
  assert (ZR : PNADD.zers (vF E) M 4).
  { intros i Hi. unfold PNADD.cell. apply (PNMW.u32_of_zeros RSEGS M (vF E + 32) 144 (vF E + 32 + 4 * i)); [exact ZS| clear - Hi; lia| clear - Hi; lia| clear - GFF1; lia| clear - GFF1; lia]. }
  pose proof (PNADMID.middle (vR E) (vsp E) (vF E) (vfirst E) sigma E1) as MID.
  L5SAR.feed MID ltac:(first [ assumption | lia ]).
  specialize (MID V FV (vvp E) hi lo).
  L5SAR.feed MID ltac:(first [ assumption | reflexivity | lia ]).
  destruct (MID fx R M SJ MWS MFW MIMG0 MZSIG ZR VP) as (fx' & R' & M' & pc' & MS & MG & FZ & [(-> & SX & EQM) | (-> & z & sd & SP & Hz & Hsd & Hzs & SD)]).
  - assert (EM : M' = M) by (apply functional_extensionality; exact EQM). subst M'.
    exists fx', R', M, 0xb3100. split; [exact MS|]. split; [exact MG|].
    split; [intros a Ha Hn; reflexivity|].
    right. split; [reflexivity|]. exists hi, lo. split; [exact SX|]. split; [exact Hhi|]. split; [exact Hlo| exact VP].
  - exists fx', R', M', 0xb2b04. split; [exact MS|]. split; [exact MG|].
    split. { intros a Ha Hn. apply (FZ a Ha). intros W. apply Hn. unfold Wmid. unfold PNADRN3.Wrnd in W. clear - W. lia. }
    left. split; [reflexivity|]. exists (Z.land E1 16383), z, sd. split; [exact SP|]. split; [exact SD|].
    split; [exact (PNADMID.e14_range E1)|]. split; [exact Hz|]. split; [exact Hsd| exact Hzs].
Qed.

(* [comment removed for export] *)
Theorem signj_of2 : out_stmt L ar HI -> PNADM.special_stmt L ar HI -> PNADS.at_signj L ar HI.
Proof. intros OUT SPC. exact (PNADM.signj_of L ar C HI LY HIok mid_run_ok OUT SPC). Qed.

End WithHeap.
End SCFG_1.
End PNADMR.
