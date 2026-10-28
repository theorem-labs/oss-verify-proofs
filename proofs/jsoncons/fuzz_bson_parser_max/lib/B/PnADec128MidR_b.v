(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts PnMemW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128S_b PnADec128F_b PnADec128M_b PnADec128Rnd3_b PnADec128Mid_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADMR.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Theorem mid_run_ok : PNADM.mid_run L ar HI.
Proof.
  intros E X fx R M modelc LKc Ac sigma ST ZS Hs SJ KP KX.
  dgeom L ar HI E X.
  pose proof (dmem_of L ar C HI LY HIok E X M modelc LKc Ac ST) as DM. unfold dmem, PNADD.MIA in DM.
  destruct DM as ((MWS & MWF & MFW & _ & _ & _ & _ & _ & _ & _ & _ & _ & MZSIG) & (lo & hi & Hlo & Hhi & VP) & MIMG0 & _).
  set (V := (hi mod 2 ^ 49) * 2 ^ 64 + lo). set (E1 := hi / 4294967296 / 131072).
  assert (FV : 0 <= V < 2 ^ 113).
  { subst V. pose proof (Z.mod_pos_bound hi (2 ^ 49) ltac:(clear; lia)) as B. clear - B Hlo. lia. }
  assert (FE1 : 0 <= E1 < 2 ^ 64).
  { subst E1. split; [apply Z.div_pos; [apply Z.div_pos|]; clear - Hhi; lia|]. apply Z.div_lt_upper_bound; [clear; lia|]. apply Z.div_lt_upper_bound; clear - Hhi; lia. }
  assert (ZR : PNADD.zers (vF E) (mrestrict (ahid Ac modelc) M) 4).
  { intros i Hi. unfold PNADD.cell. apply (PNMW.u32_of_zeros RSEGS (mrestrict (ahid Ac modelc) M) (vF E + 32) 144 (vF E + 32 + 4 * i)); [exact ZS| clear - Hi; lia| clear - Hi; lia| clear - GFF1; lia| clear - GFF1; lia]. }
  pose proof (PNADMID.decode (vR E) (vsp E) (vF E) (vfirst E) sigma E1) as DEC.
  L5SAR.feed DEC ltac:(first [ assumption | lia ]).
  specialize (DEC V FV (vvp E) hi lo).
  L5SAR.feed DEC ltac:(first [ assumption | reflexivity | lia ]).
  destruct (DEC fx R _ SJ MWS MIMG0 ZR VP) as (fx1 & R1 & M1 & MG1 & FZ1 & [ (MS1 & SX) | [ (MS1 & SZ & Z17) | (MS1 & HD1 & FC1 & Vp) ] ]); clear DEC.
  -
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx fx1 R R1 0xb406c 0xb4994 M modelc LKc Ac M1 (PNADMID.Wdec (vsp E)) ST MS1 MG1 FZ1).
    { intros a Wa. unfold PNADMID.Wdec, Wmid in *. clear - Wa. lia. }
    intros M3 model3 ST3 HID3 VIS3. apply (KX fx1 R1 M3 model3 LKc Ac hi lo ST3 SX Hhi Hlo).
    rewrite HID3, VIS3. destruct VP as (V0 & V8 & VZ). unfold PNADD.SH, PNADD.SBv in VZ |- *.
    split; [| split].
    + apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelc) M) M1); [| clear - GV1; lia| clear - GV1; lia| exact V0].
      intros i Hi. apply FZ1; [clear - Hi GV1; lia| unfold PNADMID.Wdec; clear - Hi GVS; lia].
    + apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelc) M) M1); [| clear - GV1; lia| clear - GV1; lia| exact V8].
      intros i Hi. apply FZ1; [clear - Hi GV1; lia| unfold PNADMID.Wdec; clear - Hi GVS; lia].
    + apply (L5KA.zeros_at_agree1 (mrestrict (ahid Ac modelc) M) M1); [| exact VZ].
      intros i Hi. unfold PNADD.SH, PNADD.SBv in Hi. apply FZ1; [clear - Hi GV1; lia| unfold PNADMID.Wdec; clear - Hi GV1 GS1; lia].
  -
    pose proof (L5.writable_grows RSEGS _ _ _ _ MG1 MWS) as WS1. pose proof (L5.writable_grows RSEGS _ _ _ _ MG1 MFW) as WF1.
    pose proof (PNADMID.iszero (vR E) (vsp E) (vF E) (vfirst E) sigma E1) as IZ. L5SAR.feed IZ ltac:(first [ assumption | lia ]).
    specialize (IZ V FV). destruct (IZ fx1 R1 M1 _ SZ Z17 WS1 WF1) as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SP2 & C0); clear IZ.
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx fx2 R R2 0xb406c 0xb4294 M modelc LKc Ac M2 (fun a => PNADMID.Wdec (vsp E) a \/ vF E + 32 <= a < vF E + 36) ST
             (msteps_trans _ _ _ _ MS1 MS2) (mem_grows_trans _ _ _ MG1 MG2)).
    { intros a Ha Hn. rewrite (FZ2 a Ha ltac:(intro; apply Hn; right; assumption)). apply FZ1; [exact Ha| intro; apply Hn; left; assumption]. }
    { intros a [Wa|Wa]; unfold PNADMID.Wdec, Wmid in *; clear - Wa; lia. }
    intros M3 model3 ST3 HID3 VIS3.
    apply (KP fx2 R2 M3 model3 LKc Ac _ 0 1 ST3 SP2); [| exact (PNADMID.e14_range E1) | clear; lia | clear; lia | clear; lia].
    rewrite HID3, VIS3. intros i Hi. exists 0. split; [replace i with 0 by (clear - Hi; lia); exact C0| clear; lia].
  -
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx fx1 R R1 0xb406c 0xb4164 M modelc LKc Ac M1 (PNADMID.Wdec (vsp E)) ST MS1 MG1 FZ1).
    { intros a Wa. unfold PNADMID.Wdec, Wmid in *. clear - Wa. lia. }
    intros M3 model3 ST3 HID3 VIS3.
    apply (PNADRN3.rounds L ar C HI LY HIok E X V fx1 R1 M3 model3 LKc Ac FV ST3); [rewrite HID3, VIS3; exact HD1|].
    intros fx4 R4 M4 model4 ST4 KEEP RO4 DG4. rewrite HID3, VIS3 in KEEP.
    pose proof (dmem_of L ar C HI LY HIok E X M4 model4 LKc Ac ST4) as DM4. unfold dmem, PNADD.MIA in DM4.
    destruct DM4 as ((NWS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NZSIG) & _).
    pose proof (gmem_of L ar C HI LY HIok E X _ _ _ _ _ (dsg_of_dst L ar HI E _ _ _ _ ST4)) as (GM4 & _). unfold gmem in GM4.
    destruct GM4 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N176 & _) & _).
    assert (TR : forall k v, 168 <= k <= 240 -> L5.u64_at RSEGS M1 (vsp E - k) v -> L5.u64_at RSEGS (mrestrict (ahid Ac model4) M4) (vsp E - k) v).
    { intros k v Hk Cv. apply (L5C.u64_at_agree RSEGS M1); [| clear - Hk GS1; lia| clear - Hk GS1; lia| exact Cv].
      intros i Hi. apply KEEP. unfold PNADRN3.Wkeep, PNADRN3.Wrnd. split; [left; clear - Hi Hk; lia| intros [W|W]; clear - W Hi Hk GFFS GS1; lia]. }
    destruct FC1 as (K240 & K232 & K224 & K216 & K208 & K200 & K192 & K184). destruct HD1 as (_ & _ & _ & K168 & _ & _).
    destruct RO4 as (O2 & O3 & O4 & O8 & O9 & O18).
    pose proof (PNADMID.scan (vR E) (vsp E) (vF E) (vfirst E) sigma E1) as SC. L5SAR.feed SC ltac:(first [ assumption | lia ]).
    specialize (SC V FV Vp).
    destruct (SC fx4 R4 _ O2 O3 O4 O8 O9 O18 (TR 240 _ ltac:(clear; lia) K240) (TR 232 _ ltac:(clear; lia) K232) (TR 224 _ ltac:(clear; lia) K224)
                (TR 216 _ ltac:(clear; lia) K216) (TR 208 _ ltac:(clear; lia) K208) (TR 200 _ ltac:(clear; lia) K200) (TR 192 _ ltac:(clear; lia) K192)
                (TR 184 _ ltac:(clear; lia) K184) N176 (TR 168 _ ltac:(clear; lia) K168) DG4 NWS NZSIG) as (fx5 & R5 & z & MS5 & SP5 & Hz5); clear SC.
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx4 fx5 R4 R5 0xb4268 0xb4294 M4 model4 LKc Ac _ (fun _ => False) ST4 MS5 (mem_grows_refl _) (fun a _ _ => eq_refl) (fun a Wa => False_ind _ Wa)).
    intros M6 model6 ST6 HID6 VIS6.
    apply (KP fx5 R5 M6 model6 LKc Ac _ z (36 - z) ST6 SP5); [| exact (PNADMID.e14_range E1) | clear - Hz5; lia | clear - Hz5; lia | clear - Hz5; lia].
    rewrite HID6, VIS6. intros i Hi. exists (PNDF.dg V i). split; [exact (DG4 i ltac:(clear - Hi Hz5; lia))| exact (PNDF.dg_range V i)].
Qed.

(* [comment removed for export] *)
Theorem signj_of2 : out_stmt L ar HI -> PNADM.special_stmt L ar HI -> PNADS.at_signj L ar HI.
Proof. intros OUT SPC. exact (PNADM.signj_of L ar C HI LY HIok mid_run_ok OUT SPC). Qed.

End WithHeap.
End SCFG_1.
End PNADMR.
