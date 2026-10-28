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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADRNC.
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
Let LYa := PMA.ly_as0 L C LY.

Lemma dg_memcall_fr E (X : dkc L ar HI E) axc Mc modelc LKc Ac (M1 : mem) model1 (D : Z -> Prop) :
  dsg L ar HI E axc Mc modelc LKc Ac ->
  ri_inv HI (vLB E) (PNADK.FF' E) LKc (vcr E) Ac M1 (vml_of model1) -> L5CA.amodel_ok Ac model1 -> model_rt modelc model1 ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (PNADK.FF' E) (vsp E - 256) 2560 a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, vsp E - 256 - 2560 <= a < vsp E - 256 -> M1 (Z_to_bv 64 a) <> None) ->
  (forall a, D a -> M1 (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  (forall a, D a -> vsp E - 136 <= a < vsp E - 120) ->
  dsg L ar HI E axc M1 model1 LKc Ac /\ (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at M1 (PNADD.SH (vF E) + 4) 18).
Proof.
  intros ST HH1 AM1 RT1 PRES SDEF DDEF DDEC DIN.
  pose proof ST as (BI & DF & AF & DV & AV & BASE & ERR & C128 & C176).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). cbn [app] in B1.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. unfold SCR in *.
  pose proof (c_GEOM L ar HI E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GFA8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  destruct (c_BLK L ar HI E X) as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  destruct (WB _ HB) as ((BB0 & _ & _ & _ & BBC & _) & _). cbn [fst snd] in BB0, BBC.
  pose proof (geom_rng L ar HI E X) as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12' & R13' & R14').
  pose proof (Wg_facts L ar HI E X) as WGF.
  assert (DW : forall a, D a -> Wg E a) by (intros a Da; pose proof (DIN a Da) as Y; right; right; left; clear - Y; lia).
  (* [comment removed for export] *)
  assert (AGST : forall a, 0 <= a < 2 ^ 64 -> ahl_ceil ar <= a < 2 ^ 47 -> ~ (vsp E - 256 - 2560 <= a < vsp E - 256) -> ~ (vsp E - 136 <= a < vsp E - 120) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hs Hns Hnd. apply PRES; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
    intros Da. exact (Hnd (DIN a Da)). }
  assert (AGW : forall a, 0 <= a < 2 ^ 64 -> ahl_ceil ar <= a < 2 ^ 47 -> ~ (vsp E - 120 - 2696 <= a < vsp E - 120) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hs Hn. apply AGST; [exact Ha| exact Hs| clear - Hn; lia| clear - Hn; lia]. }
  assert (SDW : forall a, vsp E - 120 - 2696 <= a < vsp E - 120 -> M1 (Z_to_bv 64 a) <> None).
  { intros a Ha. destruct (L5SAR.rng_dec a (vsp E - 256 - 2560) (vsp E - 256)) as [I|O]; [exact (SDEF a I)|].
    destruct (DDEC a) as [Da|ND]; [exact (DDEF a Da)|].
    pose proof B6 as (_ & _ & _ & _ & DSCR & _). unfold L5.defined in DSCR.
    rewrite (PRES a); [| clear - Ha O R1' R2'; lia| apply L5SAR.stack_client; [clear - Ha O GSLO R2'; lia| exact O]| exact ND].
    lazymatch type of DSCR with forall i, 0 <= i < ?s -> _ =>
      pose proof (DSCR (a - (vsp E - s))) as DX; replace (vsp E - s + (a - (vsp E - s))) with a in DX by (clear; lia) end.
    exact (DX ltac:(clear - Ha O; lia)). }
  assert (PRESF : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (vFF E) (vsp E - 256) 2560 a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc ND. apply PRES; [exact Ha| apply L5SAR.aclient_cons; exact Hc| exact ND]. }
  set (WD := [(vsp E - 136, 16)] : list L5.range).
  assert (EKD : L5SAR.ek L ar (vLB E) (PNADK.FF' E) (vsp E - 256) 2560 WD Mc M1).
  { intros a (Ha & Hc & Ho). apply PRES; [exact Ha| exact Hc|]. intros Da. pose proof (DIN a Da) as Y.
    apply (Ho (vsp E - 136, 16)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  assert (OUTI : forall a, 65536 <= a < 6905856 -> L5.outside WD a).
  { intros a Ha rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Ha Hr GS1; lia. }
  split; [| intros ZS; apply (zeros_agree Mc M1 _ _); [| exact ZS]; intros i Hi; apply PRES; [clear - Hi R9' R10'; lia| |]].
  2:{ apply (L5SAR.fframe_shadow_client L ar _ (PNADK.FF' E) (vsp E - 256) 2560 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). unfold PNADD.SH, PNADD.SBv, SB in *. clear - Hi; lia. }
  2:{ intros Da. pose proof (DIN i Da) as Y; unfold PNADD.SH, PNADD.SBv in *.
      assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). clear - Y Hi GS1 E0. lia. }
  unfold dsg. split.
  { unfold PMAUK.binv. cbn [app]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact RT1]|]. split; [exact B4|]. split; [exact B5|].
    split. { apply (L5SAR.astk_after_eq L ar C HI HIok (vLB E) (PNADK.FF' E) LKc (vcr E) Ac Mc Mc M1 _ (vsp E) _ (vsp E - 120) 2696 B1 B6 (mem_grows_refl Mc) AGW SDW); clear; lia. }
    split. { eapply L5SAR.ek_trans; [exact B7|]. apply (L5SAR.ek_mem L ar (vLB E) (vFF E) (vsp E) 18432 (vsp E - 256) 2560 D (W E) Mc M1 PRESF); [clear; lia| clear; lia|].
             intros a Hc Ho Da. pose proof (DIN a Da) as Y.
             apply (GNCS a); [clear - Y; lia| exact Hc]. }
    split. { eapply L5SAR.dk_trans; [exact B8|]. apply (L5SAR.dk_mem L ar (vLB E) (vFF E) (vsp E) 18432 (vsp E - 256) 2560 D Mc M1 PRESF SDEF DDEF DDEC); clear; lia. }
    split. { apply (GOWN Mc M1 B9). intros a Ha. pose proof (GOCR a Ha) as OC. apply AGST; [clear - OC R1' R2'; lia| clear - OC GSLO GSPT R2'; lia| clear - OC; lia| clear - OC; lia]. }
    intros i Hi. rewrite PRES; [apply B10; exact Hi| | |]; change (ff_bytes 3) with 512 in Hi; change (512 / 8) with 64 in Hi.
    - clear - Hi R9' R10'; unfold PNADD.SH, PNADD.SBv, SB in *; lia.
    - apply (L5SAR.fframe_shadow_client L ar _ (PNADK.FF' E) (vsp E - 256) 2560 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). clear - Hi; lia.
    - intros Da. assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      pose proof (DIN _ Da) as Y; unfold SB in *; clear - Y Hi GS1 E0; lia. }
  split.
  { intros i Hi. destruct (DDEC (vfirst E + i)) as [Da|ND]; [exact (DDEF _ Da)|]. rewrite PRES; [exact (DF i Hi)| clear - Hi R3' R4'; lia| | exact ND].
    apply (L5SAR.block_client L ar _ (PNADK.FF' E) _ _ Bq Bm); [exact HB| clear - Hi HB1 HB2; lia]. }
  split.
  { apply (aacc_agree Mc M1 _ _); [| exact AF]. intros a Ha. pose proof (S_rng (vfirst E) 48 a GFA8 ltac:(clear; lia) Ha) as SR. change ((48 + 7) / 8) with 6 in SR.
    apply PRES; [clear - SR R11' R12'; unfold PNADD.SH, PNADD.SBv in *; lia| |].
    - unfold aclient, aclient_g. do 6 right. exists (Bq, Bm). split; [exact HB|]. cbn [fst snd]. unfold in_shadow_of.
      pose proof (sh6_in_blk (vfirst E) Bq Bm (S a - (vfirst E / 8 + 2147450880)) GFA8 ltac:(clear - BB0; lia) HB1 HB2 ltac:(clear - SR; lia)) as Y. unfold S, SB in *. clear - Y. lia.
    - intros Da. pose proof (WGF _ (DW _ Da)) as (_ & _ & N & _). apply N. unfold PNADD.SH, PNADD.SBv. clear - SR; lia. }
  destruct (c_VST L ar HI E X) as (VST1 & VST2).
  assert (VCL : forall i, 0 <= i < 16 -> aclient L ar (vLB E) (PNADK.FF' E) (vsp E - 256) 2560 (vvp E + i)).
  { intros i Hi. apply (L5SAR.stack_client L ar (vLB E) (PNADK.FF' E) (vsp E - 256) 2560 (vvp E + i)); [clear - Hi VST1 VST2 GSLO GSPT; lia| clear - Hi VST1; lia]. }
  assert (VSCL : forall i, 0 <= i < 16 / 8 -> aclient L ar (vLB E) (PNADK.FF' E) (vsp E - 256) 2560 (vvp E / 8 + SB + i)).
  { change (16 / 8) with 2. intros i Hi. apply (L5SAR.stk_shadow_client L ar (vLB E) (PNADK.FF' E) (vsp E - 256) 2560 (vvp E / 8 + SB + i)); [| clear - GSPT; lia].
    revert i Hi. intros i Hi. unfold in_shadow_of, S. pose proof (Z.div_le_mono (ahl_ceil ar) (vvp E) 8 ltac:(clear; lia) ltac:(clear - VST1 GSLO; lia)) as Q1.
    pose proof (Z.div_le_mono (vvp E + 8) (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) 8 ltac:(clear; lia) ltac:(clear - VST2; lia)) as Q2.
    replace (vvp E + 8) with (vvp E + 1 * 8) in Q2 by (clear; lia). rewrite Z.div_add in Q2 by (clear; lia). clear - Hi Q1 Q2. lia. }
  change (16 / 8) with 2 in VSCL.
  split.
  { intros i Hi. rewrite PRES; [exact (DV i Hi)| clear - Hi R5' R6'; lia| exact (VCL i Hi)|].
    intros Da. pose proof (WGF _ (DW _ Da)) as (_ & _ & _ & _ & _ & _ & N & _). apply N. clear - Hi; lia. }
  split.
  { apply (aacc_agree Mc M1 _ _); [| exact AV]. intros a Ha. pose proof (S_rng (vvp E) 16 a GV8 ltac:(clear; lia) Ha) as SR. change ((16 + 7) / 8) with 2 in SR.
    apply PRES; [clear - SR R13' R14'; unfold PNADD.SH, PNADD.SBv in *; lia| |].
    - replace (S a) with (vvp E / 8 + SB + (S a - (vvp E / 8 + SB))) by (clear; lia). apply VSCL. unfold SB. clear - SR. lia.
    - intros Da. pose proof (WGF _ (DW _ Da)) as (_ & _ & _ & N & _). apply N. unfold PNADD.SH, PNADD.SBv. clear - SR; lia. }
  split; [apply (PMASK.base_keep L ar C LY (vLB E) (PNADK.FF' E) (vsp E - 256) 2560 WD Mc M1 EKD); [intros a Ha; apply OUTI; clear - Ha; lia| exact BASE]|].
  split.
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B Mc M1); [| exact ERR].
    intros a Ha Dp. apply EKD. split; [exact Ha|]. pose proof (depA_img a Dp) as DI. split; [| apply OUTI; exact DI].
    unfold aclient, aclient_g. right; right; left.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia| exact (PMA.ly_static L C LY a Dp)]. }
  split; [apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C128]| apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C176]]; intros i Hi.
  all: apply AGST; [clear - Hi R1' R2'; lia| clear - Hi GSLO GSPT R2'; lia| clear - Hi; lia| clear - Hi; lia].
Qed.

End WithHeap.
End SCFG_1.
End PNADRNC.
