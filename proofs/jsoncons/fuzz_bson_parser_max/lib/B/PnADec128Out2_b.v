(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128OP1_b PnADec128OP2_b PnADec128OP3_b PnADec128S_b PnADec128Out1_b PnASrcReadK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADO2.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
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

(* [comment removed for export] *)

Lemma dg_call E (X : dkc L ar HI E) (scrc : Z) axc Mc modelc LKc Ac (M1 : mem) model1 LK1 A1 (D : Z -> Prop) :
  0 <= scrc -> 256 + scrc <= 18432 ->
  dsg L ar HI E axc Mc modelc LKc Ac ->
  ri_inv HI (vLB E) (FF' E) LK1 (vcr E) A1 M1 (vml_of model1) -> L5CA.amodel_ok A1 model1 -> model_rt modelc model1 ->
  incl Ac A1 -> incl LK1 LKc ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) scrc a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, vsp E - 256 - scrc <= a < vsp E - 256 -> M1 (Z_to_bv 64 a) <> None) ->
  (forall a, D a -> M1 (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  (forall a, D a -> (vF E + 32 <= a < vF E + 504) \/ (vfirst E <= a < vfirst E + 42)) ->
  dsg L ar HI E axc M1 model1 LK1 A1 /\ (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at M1 (PNADD.SH (vF E) + 4) 18).
Proof.
  intros HS0 HS1 ST HH1 AM1 RT1 IA1 ILK1 PRES SDEF DDEF DDEC DIN.
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
  assert (DW : forall a, D a -> Wg E a) by (intros a Da; destruct (DIN a Da) as [Y|Y]; [right; right; right; left; exact Y| right; right; right; right; right; exact Y]).
  (* [comment removed for export] *)
  assert (AGST : forall a, 0 <= a < 2 ^ 64 -> ahl_ceil ar <= a < 2 ^ 47 -> ~ (vsp E - 256 - scrc <= a < vsp E - 256) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hs Hns. apply PRES; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
    intros Da. destruct (DIN a Da) as [Y|Y]; [clear - Y Hs GFCEIL; lia| clear - Y Hs HB2 BBC; lia]. }
  assert (PRESF : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (vFF E) (vsp E - 256) scrc a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc ND. apply PRES; [exact Ha| apply L5SAR.aclient_cons; exact Hc| exact ND]. }
  set (WD := [(vF E + 32, 472); (vfirst E, 42)] : list L5.range).
  assert (EKD : L5SAR.ek L ar (vLB E) (FF' E) (vsp E - 256) scrc WD Mc M1).
  { intros a (Ha & Hc & Ho). apply PRES; [exact Ha| exact Hc|]. intros Da. destruct (DIN a Da) as [Y|Y].
    - apply (Ho (vF E + 32, 472)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia].
    - apply (Ho (vfirst E, 42)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  assert (OUTI : forall a, 65536 <= a < 6905856 -> L5.outside WD a).
  { intros a Ha rr [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; [clear - Ha Hr GFFI; lia| clear - Ha Hr GFI; lia]. }
  split; [| intros ZS; apply (zeros_agree Mc M1 _ _); [| exact ZS]; intros i Hi; apply PRES; [clear - Hi R9' R10'; lia| |]].
  2:{ apply (L5SAR.fframe_shadow_client L ar _ (FF' E) (vsp E - 256) scrc (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). unfold PNADD.SH, PNADD.SBv, SB in *. clear - Hi; lia. }
  2:{ intros Da. destruct (DIN i Da) as [Y|Y]; unfold PNADD.SH, PNADD.SBv in *.
      - assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). clear - Y Hi GFFSH E0. lia.
      - assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). clear - Y Hi GFSH E0. lia. }
  unfold dsg. split.
  { unfold PMAUK.binv. cbn [app]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact RT1]|]. split; [intros x Hx; apply IA1; apply B4; exact Hx|]. split; [intros x Hx; apply B5; apply ILK1; exact Hx|].
    split. { apply (L5SAR.astk_after_eq L ar C HI HIok (vLB E) (FF' E) LKc (vcr E) Ac Mc Mc M1 _ (vsp E) _ (vsp E - 256) scrc B1 B6 (mem_grows_refl Mc) AGST SDEF); clear - HS0 HS1; lia. }
    split. { eapply L5SAR.ek_trans; [exact B7|]. apply (L5SAR.ek_mem L ar (vLB E) (vFF E) (vsp E) 18432 (vsp E - 256) scrc D (W E) Mc M1 PRESF); [clear - HS0 HS1; lia| clear - HS0 HS1; lia|].
             intros a Hc Ho Da. destruct (DIN a Da) as [Y|Y].
             - apply (GNCF a); [left; clear - Y; lia| exact Hc].
             - apply (Ho (vfirst E, 42)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
    split. { eapply L5SAR.dk_trans; [exact B8|]. apply (L5SAR.dk_mem L ar (vLB E) (vFF E) (vsp E) 18432 (vsp E - 256) scrc D Mc M1 PRESF SDEF DDEF DDEC); clear - HS0 HS1; lia. }
    split. { apply (GOWN Mc M1 B9). intros a Ha. pose proof (GOCR a Ha) as OC. apply AGST; [clear - OC R1' R2'; lia| clear - OC GSLO GSPT R2'; lia| clear - OC; lia]. }
    intros i Hi. rewrite PRES; [apply B10; exact Hi| | |]; change (ff_bytes 3) with 512 in Hi; change (512 / 8) with 64 in Hi.
    - clear - Hi R9' R10'; unfold PNADD.SH, PNADD.SBv, SB in *; lia.
    - apply (L5SAR.fframe_shadow_client L ar _ (FF' E) (vsp E - 256) scrc (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). clear - Hi; lia.
    - intros Da. assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      destruct (DIN _ Da) as [Y|Y]; unfold SB in *; [clear - Y Hi GFFSH E0; lia| clear - Y Hi GFSH E0; lia]. }
  split.
  { intros i Hi. destruct (DDEC (vfirst E + i)) as [Da|ND]; [exact (DDEF _ Da)|]. rewrite PRES; [exact (DF i Hi)| clear - Hi R3' R4'; lia| | exact ND].
    apply (L5SAR.block_client L ar _ (FF' E) _ _ Bq Bm); [exact HB| clear - Hi HB1 HB2; lia]. }
  split.
  { apply (aacc_agree Mc M1 _ _); [| exact AF]. intros a Ha. pose proof (S_rng (vfirst E) 48 a GFA8 ltac:(clear; lia) Ha) as SR. change ((48 + 7) / 8) with 6 in SR.
    apply PRES; [clear - SR R11' R12'; unfold PNADD.SH, PNADD.SBv in *; lia| |].
    - unfold aclient, aclient_g. do 6 right. exists (Bq, Bm). split; [exact HB|]. cbn [fst snd]. unfold in_shadow_of.
      pose proof (sh6_in_blk (vfirst E) Bq Bm (S a - (vfirst E / 8 + 2147450880)) GFA8 ltac:(clear - BB0; lia) HB1 HB2 ltac:(clear - SR; lia)) as Y. unfold S, SB in *. clear - Y. lia.
    - intros Da. pose proof (WGF _ (DW _ Da)) as (_ & _ & N & _). apply N. unfold PNADD.SH, PNADD.SBv. clear - SR; lia. }
  destruct (c_VST L ar HI E X) as (VST1 & VST2).
  assert (VCL : forall i, 0 <= i < 16 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) scrc (vvp E + i)).
  { intros i Hi. apply (L5SAR.stack_client L ar (vLB E) (FF' E) (vsp E - 256) scrc (vvp E + i)); [clear - Hi VST1 VST2 GSLO GSPT; lia| clear - Hi VST1; lia]. }
  assert (VSCL : forall i, 0 <= i < 16 / 8 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) scrc (vvp E / 8 + SB + i)).
  { change (16 / 8) with 2. intros i Hi. apply (L5SAR.stk_shadow_client L ar (vLB E) (FF' E) (vsp E - 256) scrc (vvp E / 8 + SB + i)); [| clear - GSPT; lia].
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
  split; [apply (PMASK.base_keep L ar C LY (vLB E) (FF' E) (vsp E - 256) scrc WD Mc M1 EKD); [intros a Ha; apply OUTI; clear - Ha; lia| exact BASE]|].
  split.
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B Mc M1); [| exact ERR].
    intros a Ha Dp. apply EKD. split; [exact Ha|]. pose proof (depA_img a Dp) as DI. split; [| apply OUTI; exact DI].
    unfold aclient, aclient_g. right; right; left.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia| exact (PMA.ly_static L C LY a Dp)]. }
  split.
  { apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C128]. intros i Hi.
    apply AGST; [clear - Hi R1' R2'; lia| clear - Hi GSLO GSPT R2'; lia| clear - Hi; lia]. }
  apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C176]. intros i Hi.
  apply AGST; [clear - Hi R1' R2'; lia| clear - Hi GSLO GSPT R2'; lia| clear - Hi; lia].
Qed.

Abbreviation view Ac modelc Mc := (mrestrict (ahid Ac modelc) Mc).

(* [comment removed for export] *)
Lemma E_FHI E (X : dkc L ar HI E) : vfirst E + 48 <= vsp E - 256.
Proof.
  pose proof (c_HH L ar HI E X) as HH.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  destruct (c_BLK L ar HI E X) as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB _ HB) as ((BB0 & _ & _ & _ & BBC & _) & _). cbn [fst snd] in BB0, BBC.
  unfold PNADK.SCR in *. clear - HB2 BBC GSLO. lia.
Qed.

(* [comment removed for export] *)
Lemma E_MIA E (X : dkc L ar HI E) Mc modelc LKc Ac : dst L ar HI E Mc modelc LKc Ac ->
  PNADD.MIA (vR E) (vsp E) (vfirst E) (vr E) (vF E) (vfl E) (view Ac modelc Mc).
Proof. intros ST. exact (proj1 (dmem_of L ar C HI LY HIok E X _ _ _ _ ST)). Qed.

Lemma E_C176 E (X : dkc L ar HI E) Mc modelc LKc Ac : dst L ar HI E Mc modelc LKc Ac ->
  L5.u64_at RSEGS (view Ac modelc Mc) (vsp E - 176) (vfirst E + 42).
Proof.
  intros ST. pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & C176 & _).
  pose proof (sp_rng L ar HI E X) as SR.
  pose proof (proj2 (gmem_of L ar C HI LY HIok E X _ _ _ _ _ (dsg_of_dst L ar HI E _ _ _ _ ST))) as (VS & _).
  exact (proj2 (L5A.u64_at_vis (ahid Ac modelc) Mc (vsp E - 176) (vfirst E + 42) (L5A.avis_sub _ _ _ (vsp E - 176) 8 VS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - SR; lia) ltac:(clear - SR; lia)) C176).
Qed.

Lemma Wout_mid E a : PNADO1.Wout (vfirst E) (vF E) a -> Wmid E a.
Proof.
  unfold PNADO1.Wout, Wmid, PNADD.SH, PNADD.SBv. intros [Y|[Y|Y]]; [right; right; right; right; right; exact Y| right; right; right; left; clear - Y; lia| right; right; right; right; left; clear - Y; lia].
Qed.

(* [comment removed for export] *)
Lemma vpiece E (X : dkc L ar HI E) (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) Mc modelc LKc Ac (M2v : mem) :
  dst L ar HI E Mc modelc LKc Ac ->
  msteps RSEGS (L5SAR.st fx1 R1 pc1 (view Ac modelc Mc)) (L5SAR.st fx2 R2 pc2 M2v) ->
  PNADO1.vout (vfirst E) (vF E) (view Ac modelc Mc) M2v ->
  (forall (M3 : mem) model3,
      dst L ar HI E M3 model3 LKc Ac -> view Ac model3 M3 = M2v ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 pc2 M3 model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 Mc modelc) (vK E).
Proof.
  intros ST MS (MG & AG) KR.
  apply (dk_piece L ar C HI LY HIok E X fx1 fx2 R1 R2 pc1 pc2 Mc modelc LKc Ac M2v (PNADO1.Wout (vfirst E) (vF E)) ST MS MG).
  - exact AG.
  - intros a Wa. exact (Wout_mid E a Wa).
  - intros M3 model3 ST3 HID3 VIS3. apply (KR M3 model3 ST3). rewrite HID3. exact VIS3.
Qed.

(* [comment removed for export] *)
Lemma dgo_memset_buf E (X : dkc L ar HI E) axc (fx : FPState) Ra Mc modelc LKc Ac (d c n ra : Z) :
  dsg L ar HI E axc Mc modelc LKc Ac -> vfirst E <= d -> d + n <= vfirst E + 42 -> 0 < n <= 2 ^ 27 ->
  getr Ra (reg 10) = Z_to_bv 64 d -> getr Ra (reg 11) = Z_to_bv 64 c -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  (forall Rb Mb modelb, regs_preserved Ra Rb -> dsg L ar HI E axc Mb modelb LKc Ac ->
     (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at Mb (PNADD.SH (vF E) + 4) 18) ->
     (forall a, vF E + 32 <= a < vF E + 504 -> Mb (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra 0x78130 Mc modelc) (vK E).
Proof.
  intros ST Hd1 Hd2 Hn Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 KC.
  pose proof ST as (BI & DF & AF & _). pose proof BI as (HHc & AMc & _ & _ & _ & ASTKc & _). cbn [app] in HHc.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. unfold PNADK.SCR in *.
  dgeom L ar HI E X.
  destruct (c_BLK L ar HI E X) as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MS.
  assert (U2 : bv_unsigned (getr Ra 2%bv) = vsp E - 256) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; clear - SR; lia).
  unfold PMSPA.cfg. apply (MS fx Ra Mc modelc (vLB E) (PNADK.FF' E) LKc (vcr E) Ac d c n (vK E)); clear MS.
  - split; [exact HHc|]. split; [exact (proj1 AMc)|]. split; [exact (proj2 AMc)|].
    split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [clear - Hn; lia|].
    split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by exact Hra'; exact Hra|].
    split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Mc Mc (vsp E) 18432 256 2560 ASTKc (fun x Hx => Hx)); [clear; lia| clear; lia| clear; lia|].
             replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. clear - GS32.
             pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
    split; [intros a Ha; apply AF; clear - Ha Hd1 Hd2; lia|].
    split. { intros i Hi. rewrite U2. apply (L5SAR.block_client L ar _ (PNADK.FF' E) _ _ Bq Bm); [exact HB|]. clear - Hi Hd1 Hd2 HB1 HB2; lia. }
    split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Mc (vfirst E) 42 DF ltac:(clear - GF1; lia) ltac:(clear - GF1; lia)) as WR.
             replace (d + i) with (vfirst E + (d - vfirst E + i)) by (clear; lia). apply WR; clear - Hi Hm Hd1 Hd2; lia. }
    split; [exact (c_K0 L ar HI E X)|]. apply (L5SAR.app_rng_block L ar C HI HIok _ _ _ _ _ _ _ Bq Bm d n HHc HB); [clear - Hd1 HB1; lia| clear - Hd2 HB2; lia].
  - rewrite L5K.rl11. exact Ra11.
  - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
    assert (AMb : L5CA.amodel_ok Ac modelb) by (split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMc)| exact MIb]).
    destruct (PNADK.dg_memcall L ar C HI LY HIok E X axc Mc modelc LKc Ac Mb modelb (fun a => d <= a < d + n) ST HHb AMb RTb PRES SDEFb) as (STb & ZSb).
    + intros a Ha. destruct (BYTES (a - d) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (d + (a - d)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    + intros a. destruct (L5SAR.rng_dec a d (d + n)) as [Y|Y]; [left; exact Y| right; exact Y].
    + intros a Ha. right. clear - Ha Hd1 Hd2; lia.
    + apply (KC Rb Mb modelb RPb STb ZSb). intros a Ha. apply PRES; [clear - Ha GFF1; lia| |].
      * apply (L5SAR.fframe_client L ar _ (PNADK.FF' E) _ _ (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Ha; lia.
      * clear - Ha Hd1 Hd2 GFFf. lia.
Qed.

(* [comment removed for export] *)
Definition okont (E : dve) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (ptr ec : Z),
    dst L ar HI E M' model' LK' A' ->
    PNADD.out_post (vR E) (vsp E) (vF E) (vfl E) (vfirst E) (vr E) ptr ec R' (view A' model' M') ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb46b0 M' model') (vK E).

(* [comment removed for export] *)
Lemma to_retp E (X : dkc L ar HI E) (fx1 fx2 : FPState) R1 R2 (pc1 : Z) Mc modelc LKc Ac (M2v : mem) ptr ec :
  dst L ar HI E Mc modelc LKc Ac ->
  msteps RSEGS (L5SAR.st fx1 R1 pc1 (view Ac modelc Mc)) (L5SAR.st fx2 R2 0xb46b0 M2v) ->
  PNADO1.vout (vfirst E) (vF E) (view Ac modelc Mc) M2v ->
  PNADD.stE (vR E) (vsp E) (vF E) ptr ec R2 -> vfirst E <= ptr <= vfirst E + 42 -> (ec = 0 \/ ec = 75) ->
  okont E ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 Mc modelc) (vK E).
Proof.
  intros ST MS VO SE Hp Hec KONT.
  apply (vpiece E X fx1 fx2 R1 R2 pc1 0xb46b0 Mc modelc LKc Ac M2v ST MS VO).
  intros M3 model3 ST3 V3. apply (KONT fx2 R2 M3 model3 LKc Ac ptr ec ST3).
  unfold PNADD.out_post. split; [exact SE|]. split; [| split; [exact Hp| exact Hec]].
  rewrite V3. exact (PNADO1.MIA_out _ _ _ _ _ _ _ (c_GEOM L ar HI E X) _ _ (E_MIA E X _ _ _ _ ST) VO).
Qed.

(* [comment removed for export] *)
Lemma arm_regular E (X : dkc L ar HI E) sigma z sd (fx : FPState) R Mc modelc LKc Ac :
  0 <= sigma <= 1 -> 0 <= z -> 1 <= sd -> z + sd <= 36 ->
  dst L ar HI E Mc modelc LKc Ac -> PNADD.sdigs (vF E) (view Ac modelc Mc) z sd ->
  PNADO1.RLO (vR E) (vsp E) (vfirst E) (vF E) sigma z sd R -> okont E ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb42cc Mc modelc) (vK E).
Proof.
  intros Hsig Hz Hsd Hzs ST SD (RLR & G30 & G18 & G13) KONT.
  pose proof (c_GEOM L ar HI E X) as GEOM. pose proof (sp_rng L ar HI E X) as SR. pose proof (E_FHI E X) as FHI. pose proof (E_MIA E X _ _ _ _ ST) as MI.
  destruct (PNADO1.regular _ _ _ _ _ _ _ GEOM _ sigma z sd MI SD Hsig Hz Hsd Hzs SR FHI fx R _ RLR G30 G18 G13 (PNADO1.vout_refl _ _ _))
    as (fx2 & R2 & M2 & cnt & MS & VO & SE & Hc).
  apply (to_retp E X fx fx2 R R2 0xb42cc Mc modelc LKc Ac M2 (vfirst E + sigma + cnt) 0 ST MS VO SE); [clear - Hc Hsig Hzs Hz; lia| left; reflexivity| exact KONT].
Qed.

(* [comment removed for export] *)
Lemma sdigs_xfer E (X : dkc L ar HI E) axc axb Mc modelc LKc Ac Mb modelb LKb Ab z sd :
  dsg L ar HI E axc Mc modelc LKc Ac -> dsg L ar HI E axb Mb modelb LKb Ab -> 0 <= z -> z + sd <= 36 ->
  (forall a, vF E + 32 <= a < vF E + 504 -> Mb (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  PNADD.sdigs (vF E) (view Ac modelc Mc) z sd -> PNADD.sdigs (vF E) (view Ab modelb Mb) z sd.
Proof.
  intros STc STb Hz Hzs FK SD i Hi. destruct (SD i Hi) as (v & CV & Hv). exists v. split; [| exact Hv].
  pose proof (proj2 (gmem_of L ar C HI LY HIok E X _ _ _ _ _ STc)) as (_ & _ & VFc & _).
  pose proof (proj2 (gmem_of L ar C HI LY HIok E X _ _ _ _ _ STb)) as (_ & _ & VFb & _).
  pose proof (c_GEOM L ar HI E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold PNADD.cell in *.
  assert (R1 : 0 <= vF E + 32 + 4 * i) by (clear - Hi Hz GFF1; lia). assert (R2 : vF E + 32 + 4 * i + 4 <= 2 ^ 64) by (clear - Hi Hz Hzs GFF1; lia).
  apply (proj2 (L5A.u32_at_vis (ahid Ab modelb) Mb _ v (L5A.avis_sub (ahid Ab modelb) (vF E) 512 (vF E + 32 + 4 * i) 4 VFb ltac:(clear - Hi Hz; lia) ltac:(clear - Hi Hz Hzs; lia)) R1 R2)).
  apply (PMF.u32_at_agree RSEGS Mc Mb); [| exact R1| exact R2|].
  - intros j Hj. apply FK. clear - Hj Hi Hz Hzs. lia.
  - exact (proj1 (L5A.u32_at_vis (ahid Ac modelc) Mc _ v (L5A.avis_sub (ahid Ac modelc) (vF E) 512 (vF E + 32 + 4 * i) 4 VFc ltac:(clear - Hi Hz; lia) ltac:(clear - Hi Hz Hzs; lia)) R1 R2) CV).
Qed.

(* [comment removed for export] *)
Lemma arm_radix E (X : dkc L ar HI E) sigma z sd e (fx : FPState) R Mc modelc LKc Ac :
  0 <= sigma <= 1 -> 0 <= z -> 1 <= sd -> z + sd <= 36 -> 0 <= e <= 6175 -> -6 <= sd + e - 6177 ->
  dst L ar HI E Mc modelc LKc Ac -> PNADD.sdigs (vF E) (view Ac modelc Mc) z sd ->
  PNADO1.RLO (vR E) (vsp E) (vfirst E) (vF E) sigma z sd R ->
  getr R (reg 14) = Z_to_bv 64 (e - 6176) -> okont E ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb44ac Mc modelc) (vK E).
Proof.
  intros Hsig Hz Hsd Hzs He Hlo ST SD RLO G14 KONT.
  pose proof (c_GEOM L ar HI E X) as GEOM. pose proof (sp_rng L ar HI E X) as SR. pose proof (E_FHI E X) as FHI. pose proof (E_MIA E X _ _ _ _ ST) as MI.
  destruct (PNADO1.radix _ _ _ _ _ _ _ GEOM _ sigma z sd MI SD Hsig Hz Hsd Hzs SR (E_C176 E X _ _ _ _ ST) fx R _ e He Hlo RLO G14 (PNADO1.vout_refl _ _ _))
    as (fx2 & R2 & M2 & ptr & MS & VO & SE & Hp).
  exact (to_retp E X fx fx2 R R2 0xb44ac Mc modelc LKc Ac M2 ptr 0 ST MS VO SE Hp (or_introl eq_refl) KONT).
Qed.

(* [comment removed for export] *)
Lemma dgo_memset_F E (X : dkc L ar HI E) axc (fx : FPState) Ra Mc modelc LKc Ac (d c n ra : Z) :
  dsg L ar HI E axc Mc modelc LKc Ac -> vF E + 32 <= d -> d + n <= vF E + 504 -> 0 < n <= 2 ^ 27 -> PMSPA.accA Mc d n ->
  getr Ra (reg 10) = Z_to_bv 64 d -> getr Ra (reg 11) = Z_to_bv 64 c -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  (forall Rb Mb modelb, regs_preserved Ra Rb -> dsg L ar HI E axc Mb modelb LKc Ac ->
     (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at Mb (PNADD.SH (vF E) + 4) 18) ->
     (forall i, 0 <= i < n -> Mb (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 (c mod 256))) ->
     (forall a, (vF E + 32 <= a < vF E + 504 /\ ~ (d <= a < d + n)) \/ (PNADD.SH (vF E) <= a < PNADD.SH (vF E) + 64) -> Mb (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra 0x78130 Mc modelc) (vK E).
Proof.
  intros ST Hd1 Hd2 Hn ACC Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 KC.
  pose proof ST as (BI & _). pose proof BI as (HHc & AMc & _ & _ & _ & ASTKc & _). cbn [app] in HHc.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. unfold PNADK.SCR in *.
  dgeom L ar HI E X.
  pose proof (geom_rng L ar HI E X) as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12' & R13' & R14').
  pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MS.
  assert (U2 : bv_unsigned (getr Ra 2%bv) = vsp E - 256) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; clear - SR; lia).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (_ & WF & _).
  destruct (WF (vF E, 3, vsp E - 256 + 32) ltac:(left; reflexivity)) as (_ & _ & _ & _ & FDEF & _). cbn [ff_addr ff_class fst snd] in FDEF. change (ff_bytes 3) with 512 in FDEF.
  unfold PMSPA.cfg. apply (MS fx Ra Mc modelc (vLB E) (PNADK.FF' E) LKc (vcr E) Ac d c n (vK E)); clear MS.
  - split; [exact HHc|]. split; [exact (proj1 AMc)|]. split; [exact (proj2 AMc)|].
    split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [clear - Hn; lia|].
    split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by exact Hra'; exact Hra|].
    split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Mc Mc (vsp E) 18432 256 2560 ASTKc (fun x Hx => Hx)); [clear; lia| clear; lia| clear; lia|].
             replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. clear - GS32.
             pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
    split; [exact ACC|].
    split. { intros i Hi. rewrite U2. apply (L5SAR.fframe_client L ar _ (PNADK.FF' E) _ _ (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Hi Hd1 Hd2; lia. }
    split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Mc (vF E) 512 FDEF ltac:(clear - GFF1; lia) ltac:(clear - GFF1; lia)) as WR.
             replace (d + i) with (vF E + (d - vF E + i)) by (clear; lia). apply WR; clear - Hi Hm Hd1 Hd2; lia. }
    split; [exact (c_K0 L ar HI E X)|]. apply (L5SAR.app_rng_fs L ar C HI HIok _ _ _ _ _ _ _ d n HHc); [clear - GFS1 Hd1; lia| clear - GFS2 Hd2; lia].
  - rewrite L5K.rl11. exact Ra11.
  - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
    assert (AMb : L5CA.amodel_ok Ac modelb) by (split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMc)| exact MIb]).
    assert (BY : forall i, 0 <= i < n -> Mb (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 (c mod 256))).
    { intros i Hi. destruct (BYTES i Hi) as (v & Ev & Bv). unfold byte_at in Bv. rewrite Bv. subst v. reflexivity. }
    destruct (PNADK.dg_memcall L ar C HI LY HIok E X axc Mc modelc LKc Ac Mb modelb (fun a => d <= a < d + n) ST HHb AMb RTb PRES SDEFb) as (STb & ZSb).
    + intros a Ha. replace a with (d + (a - d)) by (clear; lia). rewrite BY by (clear - Ha; lia). discriminate.
    + intros a. destruct (L5SAR.rng_dec a d (d + n)) as [Y|Y]; [left; exact Y| right; exact Y].
    + intros a Ha. left. clear - Ha Hd1 Hd2; lia.
    + apply (KC Rb Mb modelb RPb STb ZSb BY). intros a [(Ha & ND)|Ha].
      * apply PRES; [clear - Ha GFF1; lia| | exact ND].
        apply (L5SAR.fframe_client L ar _ (PNADK.FF' E) _ _ (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Ha; lia.
      * apply PRES; [clear - Ha R9' R10'; lia| |].
        -- apply (L5SAR.fframe_shadow_client L ar _ (PNADK.FF' E) (vsp E - 256) 2560 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
           rewrite (proj1 (proj2 GF8)). unfold PNADD.SH, PNADD.SBv, SB in *. clear - Ha; lia.
        -- unfold PNADD.SH, PNADD.SBv in *.
           assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). clear - Ha Hd1 Hd2 GFFSH E0. lia.
Qed.

(* [comment removed for export] *)
Lemma wapp_W E (X : dkc L ar HI E) : PMKA.wapp (W E).
Proof.
  pose proof (c_GEOM L ar HI E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & _).
  unfold W. intros rr [<-|Hr]; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - GFSH; lia|].
  destruct (PNST.bax_dec (vax E)); [destruct Hr|].
  revert rr Hr. unfold PNST.dec_W. cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
  intros rr Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; left; clear; lia|]). destruct Hr.
Qed.

Lemma tu_entry E (X : dkc L ar HI E) axc Mc modelc LKc Ac (Ra : bvmap 5 word) (ra h : Z) :
  dsg L ar HI E axc Mc modelc LKc Ac -> 1 <= h <= 2 ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  getr Ra (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  PMSPA.entryA PMA.AD L ar Ra Mc (vsp E - 256) ra h /\ PGSA.ffroomB PNRA.FCB h (FF' E) LKc /\ PMSPA.ffrsA (FF' E) (vsp E - 256)
  /\ PMSPA.aobjA (FF' E) (vF E + 240) 24 /\ (vsp E - 256) mod 32 = 0 /\ (vF E + 240) mod 8 = 0.
Proof.
  intros ST Hh R1 RAok R2 R3 R4.
  pose proof ST as (BI & _). pose proof BI as (HHc & AMc & MRT & INCA & INCL & ASTKc & EKc & DKc & OWNc & DSHc). cbn [app] in HHc.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. unfold PNADK.SCR in *.
  dgeom L ar HI E X.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF1 & _).
  pose proof (c_ASTK L ar HI E X) as ASTK0. unfold PNADK.SCR in ASTK0. pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (c_STKSH L ar HI E X) as STKSH0. unfold PNADK.SCR in STKSH0. change (18432 / 8) with 2304 in STKSH0.
  assert (SCRH : PMSPA.pm_scr h = 14336 \/ PMSPA.pm_scr h = 16384) by (destruct (Z.eq_dec h 1) as [->|N]; [left; reflexivity| right; replace h with 2 by (clear - Hh N; lia); reflexivity]).
  assert (SCR8 : PMSPA.pm_scr h mod 8 = 0 /\ 0 <= PMSPA.pm_scr h <= 16384) by (destruct SCRH as [-> | ->]; split; first [reflexivity | clear; lia]).
  split.
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact R1|]. split; [exact RAok|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
    split.
    - apply (L5SAR.astk_sub ar Mc Mc (vsp E) 18432 256 (PMSPA.pm_scr h) ASTKc (mem_grows_refl Mc)); [clear; lia| clear - SCR8; lia| clear - SCR8; lia|].
      replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact (proj1 ASTKc).
    - pose proof (PMKA.stksh_keepA L ar (vLB E) (vFF E) (vsp E) 18432 (W E) (vM E) Mc EKc (wapp_W E X) (vsp E - 18432) 2304) as SZ.
      change (18432 / 8) with 2304 in *.
      assert (SZc : shadow_zero Mc (vsp E - 18432) 2304).
      { apply SZ; [clear - SR; lia| clear - SLO; lia| clear - SR; lia| | clear; lia| exact STKSH0].
        apply PMKA.mod16_8'. replace (vsp E - 18432) with (vsp E + (-1152) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
      apply (PMKA.shadow_zero_sub Mc (vsp E - 18432) 2304); [| | | | | exact SZc].
      + apply PMKA.mod16_8'. replace (vsp E - 18432) with (vsp E + (-1152) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
      + destruct SCRH as [-> | ->]; apply PMKA.mod16_8'; [replace (vsp E - 256 - 14336) with (vsp E + (-912) * 16) by (clear; lia)| replace (vsp E - 256 - 16384) with (vsp E + (-1040) * 16) by (clear; lia)]; rewrite Z_mod_plus_full; exact A16.
      + clear - SCR8; lia.
      + destruct SCRH as [-> | ->]; [change (14336 / 8) with 1792| change (16384 / 8) with 2048]; clear; lia.
      + destruct SCRH as [-> | ->]; [change (14336 / 8) with 1792| change (16384 / 8) with 2048]; clear; lia. }
  split. { apply (PMAUAR.ffroomB_push PNRA.FCB 3 h (vFF E) (vLK E) LKc _ (c_FRM L ar HI E X) INCL); [exact NDF1| clear - Hh; lia]. }
  split. { apply (PMAUAR.ffrsA_push (vFF E) (vsp E) (vsp E - 256) (vF E) 3 (vsp E - 256 + 32) (c_FRS L ar HI E X)); clear; lia. }
  split. { exists (vF E, 3, vsp E - 256 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 3) with 512. clear; lia. }
  split. { replace (vsp E - 256) with (vsp E + (-8) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact GS32. }
  pose proof (Z.div_mod (vF E) 32 ltac:(clear; lia)) as D. rewrite GFF32, Z.add_0_r in D. rewrite D. replace (32 * (vF E / 32) + 240) with ((4 * (vF E / 32) + 30) * 8) by (clear; lia). apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma tu_after E (X : dkc L ar HI E) (h : Z) Mc modelc LKc Ac (Mb : mem) modelb LKb Ab :
  1 <= h <= 2 ->
  dst L ar HI E Mc modelc LKc Ac ->
  L5CA.ahpres L ar (vLB E) (FF' E) (vsp E - 256) (PMSPA.pm_scr h) [(vF E + 240, 24)] Mc Mb ->
  L5.defined Mb (vF E + 240) 24 ->
  model_rt modelc modelb -> incl LKb LKc -> incl Ac Ab -> L5CA.amodel_ok Ab modelb ->
  ri_inv HI (vLB E) (FF' E) LKb (vcr E) Ab Mb (vml_of modelb) ->
  dst L ar HI E Mb modelb LKb Ab.
Proof.
  intros Hh ST (AH1 & AH2 & AH3) DS RTb ILK IAW AMb HHb.
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ZS).
  assert (SCRH : PMSPA.pm_scr h = 14336 \/ PMSPA.pm_scr h = 16384) by (destruct (Z.eq_dec h 1) as [->|N]; [left; reflexivity| right; replace h with 2 by (clear - Hh N; lia); reflexivity]).
  destruct (dg_call E X (PMSPA.pm_scr h) _ Mc modelc LKc Ac Mb modelb LKb Ab (fun a => vF E + 240 <= a < vF E + 240 + 24)
              ltac:(destruct SCRH as [-> | ->]; clear; lia) ltac:(destruct SCRH as [-> | ->]; clear; lia)
              (dsg_of_dst L ar HI E _ _ _ _ ST) HHb AMb RTb IAW ILK) as (STb & ZSb).
  - intros a Ha Hc ND. apply AH1. split; [exact Ha|]. split; [exact Hc|].
    intros rr [<-|[]] Hr. apply ND. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. exact Hr.
  - intros a Ha. replace a with (vsp E - 256 - PMSPA.pm_scr h + (a - (vsp E - 256 - PMSPA.pm_scr h))) by (clear; lia). apply AH2. clear - Ha. lia.
  - intros a Ha. replace a with (vF E + 240 + (a - (vF E + 240))) by (clear; lia). apply DS. clear - Ha. lia.
  - intros a. destruct (L5SAR.rng_dec a (vF E + 240) (vF E + 240 + 24)) as [Y|Y]; [left; exact Y| right; exact Y].
  - intros a Ha. left. clear - Ha. lia.
  - exact (dst_of_dsg L ar HI E _ _ _ _ STb (ZSb ZS)).
Qed.

(* [comment removed for export] *)
Lemma dgo_fi E (X : dkc L ar HI E) (fx : FPState) Ra Mc modelc LKc Ac (v n ra : Z) :
  PNRAa.from_int_spec L ar HI ->
  dst L ar HI E Mc modelc LKc Ac -> PM.vstr_at RSEGS PMSPA.accA Mc (vF E + 240) (PM.VShort n) -> 0 <= n <= 11 -> - 2 ^ 31 <= v < 2 ^ 31 ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  getr Ra (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 10) = Z_to_bv 64 v -> getr Ra (reg 11) = Z_to_bv 64 (vF E + 240) ->
  (forall (fx' : FPState) Rb (Mb : mem) modelb LKb Ab n',
      regs_preserved Ra Rb -> dst L ar HI E Mb modelb LKb Ab -> PM.vstr_at RSEGS PMSPA.accA Mb (vF E + 240) (PM.VShort n') -> n + 1 <= n' <= n + 11 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra (PNL.pn_from_int PMA.AN) Mc modelc) (vK E).
Proof.
  intros FI ST VS Hn Hv R1 RAok R2 R3 R4 R10 R11 KC.
  pose proof ST as (BI & _). pose proof BI as (HHc & AMc & _). cbn [app] in HHc.
  destruct (tu_entry E X _ Mc modelc LKc Ac Ra ra 2 (dsg_of_dst L ar HI E _ _ _ _ ST) ltac:(clear; lia) R1 RAok R2 R3 R4) as (ENT & FRM & FRS & AOB & S32 & O8).
  unfold PNRAa.from_int_spec, PNRA.from_int_spec in FI.
  apply (FI fx Ra Mc modelc (vK E) (vLB E) (FF' E) LKc Ac (vcr E) (vF E + 240) v (vsp E - 256) ra n HHc AMc (c_K0 L ar HI E X) ENT FRM FRS S32).
  - rewrite L5K.rl10. exact R10.
  - exact Hv.
  - rewrite L5K.rl11. exact R11.
  - exact AOB.
  - exact O8.
  - exact VS.
  - exact Hn.
  - intros fx' R' M' model' LK' Aw' n' RP VS' Hn' AH RT' ILK IAW AM' HH'.
    apply (KC fx' R' M' model' LK' Aw' n' RP); [| exact VS'| exact Hn'].
    exact (tu_after E X 2 Mc modelc LKc Ac M' model' LK' Aw' ltac:(clear; lia) ST AH (proj1 VS') RT' ILK IAW AM' HH').
Qed.

(* [comment removed for export] *)
Lemma dgo_pbs E (X : dkc L ar HI E) (fx : FPState) Ra Mc modelc LKc Ac (n ra : Z) :
  PNRAa.str_push_back_short_spec L ar HI ->
  dst L ar HI E Mc modelc LKc Ac -> PM.vstr_at RSEGS PMSPA.accA Mc (vF E + 240) (PM.VShort n) -> n <= 21 ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  getr Ra (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 10) = Z_to_bv 64 (vF E + 240) ->
  (forall (fx' : FPState) Rb (Mb : mem) modelb LKb Ab,
      regs_preserved Ra Rb -> dst L ar HI E Mb modelb LKb Ab -> PM.vstr_at RSEGS PMSPA.accA Mb (vF E + 240) (PM.VShort (n + 1)) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra (PNL.pn_str_push_back PMA.AN) Mc modelc) (vK E).
Proof.
  intros PBS ST VS Hn R1 RAok R2 R3 R4 R10 KC.
  pose proof ST as (BI & _). pose proof BI as (HHc & AMc & _). cbn [app] in HHc.
  destruct (tu_entry E X _ Mc modelc LKc Ac Ra ra 1 (dsg_of_dst L ar HI E _ _ _ _ ST) ltac:(clear; lia) R1 RAok R2 R3 R4) as (ENT & FRM & FRS & AOB & S32 & O8).
  unfold PNRAa.str_push_back_short_spec, PNRA.str_push_back_short_spec in PBS.
  apply (PBS fx Ra Mc modelc (vK E) (vLB E) (FF' E) LKc Ac (vcr E) (vF E + 240) (vsp E - 256) ra n HHc AMc (c_K0 L ar HI E X) ENT FRM FRS).
  - rewrite L5K.rl10. exact R10.
  - exact AOB.
  - exact O8.
  - exact VS.
  - exact Hn.
  - intros fx' R' M' model' LK' Aw' RP VS' AH RT' ILK IAW AM' HH'.
    apply (KC fx' R' M' model' LK' Aw' RP); [| exact VS'].
    exact (tu_after E X 1 Mc modelc LKc Ac M' model' LK' Aw' ltac:(clear; lia) ST AH (proj1 VS') RT' ILK IAW AM' HH').
Qed.


(* [comment removed for export] *)
Lemma dgo_memcpy E (X : dkc L ar HI E) axc (fx : FPState) Ra Mc modelc LKc Ac (d src n ra : Z) :
  dsg L ar HI E axc Mc modelc LKc Ac -> vfirst E <= d -> d + n <= vfirst E + 42 -> 0 < n <= 2 ^ 27 ->
  vF E + 32 <= src -> src + n <= vF E + 504 -> L5.defined Mc src n -> PMSPA.accA Mc src n ->
  getr Ra (reg 10) = Z_to_bv 64 d -> getr Ra (reg 11) = Z_to_bv 64 src -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  (forall Rb Mb modelb, regs_preserved Ra Rb -> dsg L ar HI E axc Mb modelb LKc Ac ->
     (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at Mb (PNADD.SH (vF E) + 4) 18) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra 0x77c94 Mc modelc) (vK E).
Proof.
  intros ST Hd1 Hd2 Hn Hs1 Hs2 SDEF SACC Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 KC.
  pose proof ST as (BI & DF & AF & _). pose proof BI as (HHc & AMc & _ & _ & _ & ASTKc & _). cbn [app] in HHc.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. unfold PNADK.SCR in *.
  dgeom L ar HI E X.
  destruct (c_BLK L ar HI E X) as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as MS. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MS.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memcpy L C LYa), (L5A.aly_scr_mem L C LYa), (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in MS.
  assert (U2 : bv_unsigned (getr Ra 2%bv) = vsp E - 256) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; clear - SR; lia).
  destruct (PMASRK.rdn_of_defR Mc (Z.to_nat n) src ltac:(clear - Hs1 GFF1; lia) ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - Hs2 GFF1; lia)) as (bs & RDN).
  { intros i Hi. rewrite Z2Nat.id in Hi by (clear - Hn; lia). apply SDEF. exact Hi. }
  unfold PMSPA.cfg. apply (MS fx Ra Mc modelc (vLB E) (PNADK.FF' E) LKc (vcr E) Ac d src n bs (vK E)); clear MS.
  - split; [exact HHc|]. split; [exact (proj1 AMc)|]. split; [exact (proj2 AMc)|].
    split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [clear - Hn; lia|].
    split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by exact Hra'; exact Hra|].
    split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Mc Mc (vsp E) 18432 256 2560 ASTKc (fun x Hx => Hx)); [clear; lia| clear; lia| clear; lia|].
             replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. clear - GS32.
             pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
    split; [intros a Ha; apply AF; clear - Ha Hd1 Hd2; lia|].
    split. { intros i Hi. rewrite U2. apply (L5SAR.block_client L ar _ (PNADK.FF' E) _ _ Bq Bm); [exact HB|]. clear - Hi Hd1 Hd2 HB1 HB2; lia. }
    split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Mc (vfirst E) 42 DF ltac:(clear - GF1; lia) ltac:(clear - GF1; lia)) as WR.
             replace (d + i) with (vfirst E + (d - vfirst E + i)) by (clear; lia). apply WR; clear - Hi Hm Hd1 Hd2; lia. }
    split; [exact (c_K0 L ar HI E X)|]. apply (L5SAR.app_rng_block L ar C HI HIok _ _ _ _ _ _ _ Bq Bm d n HHc HB); [clear - Hd1 HB1; lia| clear - Hd2 HB2; lia].
  - rewrite L5K.rl11. exact Ra11.
  - exact SACC.
  - clear - Hs1 Hs2 GFF1; lia.
  - apply (L5SAR.app_rng_fs L ar C HI HIok _ _ _ _ _ _ _ src n HHc); [clear - GFS1 Hs1; lia| clear - GFS2 Hs2; lia].
  - intros i Hi. right. rewrite U2. apply (L5SAR.fframe_client L ar _ (PNADK.FF' E) _ _ (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Hi Hs1 Hs2; lia.
  - exact RDN.
  - intros _. destruct GFFf as [Y|Y]; [left; clear - Y Hs1 Hd2; lia| right; clear - Y Hs2 Hd1; lia].
  - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
    assert (AMb : L5CA.amodel_ok Ac modelb) by (split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMc)| exact MIb]).
    destruct (PNADK.dg_memcall L ar C HI LY HIok E X axc Mc modelc LKc Ac Mb modelb (fun a => d <= a < d + n) ST HHb AMb RTb PRES SDEFb) as (STb & ZSb).
    + intros a Ha. destruct (BYTES (a - d) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (d + (a - d)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    + intros a. destruct (L5SAR.rng_dec a d (d + n)) as [Y|Y]; [left; exact Y| right; exact Y].
    + intros a Ha. right. clear - Ha Hd1 Hd2; lia.
    + exact (KC Rb Mb modelb RPb STb ZSb).
Qed.

(* [comment removed for export] *)
Lemma view_F E (X : dkc L ar HI E) axc Mc modelc LKc Ac axb Mb modelb LKb Ab a :
  dsg L ar HI E axc Mc modelc LKc Ac -> dsg L ar HI E axb Mb modelb LKb Ab -> view Ab modelb Mb = view Ac modelc Mc ->
  (vF E <= a < vF E + 512 \/ PNADD.SH (vF E) <= a < PNADD.SH (vF E) + 64 \/ vfirst E <= a < vfirst E + 42) ->
  Mb (Z_to_bv 64 a) = Mc (Z_to_bv 64 a).
Proof.
  intros STc STb V Ha.
  pose proof (proj2 (gmem_of L ar C HI LY HIok E X _ _ _ _ _ STc)) as (_ & VFc & VFFc & VSHc & _).
  pose proof (proj2 (gmem_of L ar C HI LY HIok E X _ _ _ _ _ STb)) as (_ & VFb & VFFb & VSHb & _).
  assert (Hc : ahid Ac modelc (Z_to_bv 64 a) = false).
  { destruct Ha as [Y|[Y|Y]];
      [replace a with (vF E + (a - vF E)) by (clear; lia); apply VFFc; clear - Y; lia
      | replace a with (PNADD.SH (vF E) + (a - PNADD.SH (vF E))) by (clear; lia); apply VSHc; clear - Y; lia
      | replace a with (vfirst E + (a - vfirst E)) by (clear; lia); apply VFc; clear - Y; lia]. }
  assert (Hb : ahid Ab modelb (Z_to_bv 64 a) = false).
  { destruct Ha as [Y|[Y|Y]];
      [replace a with (vF E + (a - vF E)) by (clear; lia); apply VFFb; clear - Y; lia
      | replace a with (PNADD.SH (vF E) + (a - PNADD.SH (vF E))) by (clear; lia); apply VSHb; clear - Y; lia
      | replace a with (vfirst E + (a - vfirst E)) by (clear; lia); apply VFb; clear - Y; lia]. }
  pose proof (f_equal (fun f => f (Z_to_bv 64 a)) V) as Q. cbv beta in Q. unfold mrestrict in Q. rewrite Hc, Hb in Q. exact Q.
Qed.

(* [comment removed for export] *)
Lemma vstr_xfer E (X : dkc L ar HI E) (Mc Mb : mem) s :
  (forall a, (vF E <= a < vF E + 512 \/ PNADD.SH (vF E) <= a < PNADD.SH (vF E) + 64 \/ vfirst E <= a < vfirst E + 42) -> Mb (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  PM.vstr_at RSEGS PMSPA.accA Mc (vF E + 240) (PM.VShort s) -> PM.vstr_at RSEGS PMSPA.accA Mb (vF E + 240) (PM.VShort s).
Proof.
  intros AG (SDEF & SACC & Hs & SB0).
  pose proof (c_GEOM L ar HI E X) as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  assert (F8 : (vF E + 240) mod 8 = 0).
  { replace (vF E + 240) with (vF E + 30 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (Z.div_mod (vF E) 32 ltac:(clear; lia)) as D. rewrite GFF32, Z.add_0_r in D. rewrite D.
    replace (32 * (vF E / 32)) with ((4 * (vF E / 32)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (Q8 : (vF E + 240) / 8 = vF E / 8 + 30).
  { replace (vF E + 240) with (vF E + 30 * 8) by (clear; lia). apply Z_div_plus. clear; lia. }
  split; [| split; [| split; [exact Hs|]]].
  - intros i Hi. rewrite AG by (left; clear - Hi; lia). apply SDEF. exact Hi.
  - apply (aacc_agree Mc Mb _ _); [| exact SACC]. intros a Ha. pose proof (S_rng (vF E + 240) 24 a F8 ltac:(clear; lia) Ha) as SR. change ((24 + 7) / 8) with 3 in SR. rewrite Q8 in SR.
    apply AG. right; left. unfold PNADD.SH, PNADD.SBv. clear - SR. lia.
  - apply (L5C.u8_at_agree RSEGS Mc Mb); [intros i Hi; apply AG; left; clear - Hi; lia| clear - GFF1; lia| clear - GFF1; lia| exact SB0].
Qed.

Lemma ec_eval (p q : Z) : 0 <= p < 2 ^ 64 -> 0 <= q -> q + 42 < 2 ^ 64 ->
  alu64 Instr.ALU_AND (alu64 Instr.ALU_ADD (alu64 Instr.ALU_SLTU (Z_to_bv 64 p) (alu64 Instr.ALU_ADD (Z_to_bv 64 q) (Z_to_bv 64 42))) (Z_to_bv 64 (-1))) (Z_to_bv 64 75)
  = Z_to_bv 64 (if p <? q + 42 then 0 else 75).
Proof.
  intros Hp Hq Hq'.
  assert (AQ : alu64 Instr.ALU_ADD (Z_to_bv 64 q) (Z_to_bv 64 42) = Z_to_bv 64 (q + 42)).
  { rewrite alu_add. unfold v_add. rewrite !L5.unsigned_lit by (clear - Hq Hq'; lia). reflexivity. }
  rewrite AQ, alu_sltu. unfold v_sltu, PropExec.c_ltu, bv_ltu.
  rewrite (L5.unsigned_lit p), (L5.unsigned_lit (q + 42)) by (clear - Hp Hq Hq'; lia).
  destruct (p <? q + 42); apply bv_eq; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sci_copy E (X : dkc L ar HI E) (fx : FPState) R Mc modelc LKc Ac k n :
  dst L ar HI E Mc modelc LKc Ac -> PM.vstr_at RSEGS PMSPA.accA Mc (vF E + 240) (PM.VShort n) -> 1 <= n <= 22 -> 1 <= k <= 36 ->
  PNADO1.RL (vR E) (vsp E) (vfirst E) (vF E) R -> getr R (reg 21) = Z_to_bv 64 (vF E + 240) -> getr R (reg 25) = Z_to_bv 64 (vfirst E + k) ->
  okont E ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb460c Mc modelc) (vK E).
Proof.
  intros ST VS Hn Hk RLR G21 G25 KONT.
  pose proof (c_GEOM L ar HI E X) as GEOM. pose proof (sp_rng L ar HI E X) as SR. pose proof (E_FHI E X) as FHI. pose proof (E_MIA E X _ _ _ _ ST) as MI.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof GEOM as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof MI as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  pose proof (proj2 (gmem_of L ar C HI LY HIok E X _ _ _ _ _ (dsg_of_dst L ar HI E _ _ _ _ ST))) as (VSK & VFI & VFF & VSH & VSHF & VIMG).
  pose proof VS as (SDEF & SACC & _ & SB0).
  assert (B0 : L5.u8_at RSEGS (view Ac modelc Mc) (vF E + 240) (2 * n)).
  { apply (proj2 (L5A.u8_at_vis (ahid Ac modelc) Mc _ _ (L5A.avis_sub _ (vF E) 512 (vF E + 240) 1 VFF ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFF1; lia) ltac:(clear - GFF1; lia))). exact SB0. }
  assert (X1 : 0 <= vsp E < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= vfirst E < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= vF E < 2 ^ 64) by (clear - GFF1; lia).
  assert (X4 : 0 <= vfirst E + k < 2 ^ 64) by (clear - GF1 Hk; lia). assert (X5 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
  assert (Y1 : 0 <= 2 * n <= 255) by (clear - Hn; lia). assert (Y2 : 1 <= vfirst E + k - vfirst E <= 37) by (clear - Hk; lia).
  assert (Y4 : vsp E mod 32 = 0) by exact GS32. assert (Y5 : vF E mod 32 = 0) by exact GFF32. assert (Y6 : 4096 <= vfirst E <= 140737488355280) by exact GF1.
  pose proof (PNADO1.geomF _ _ _ _ _ GEOM) as (E0 & SHlo & SHhi). unfold PNADD.SH, PNADD.SBv in SHlo, SHhi, W4.
  assert (Y7 : 65536 + 6840320 <= vF E / 8 + 2147450880 \/ vF E / 8 + 2147450880 + 64 <= 65536) by (left; clear - SHlo; lia).
  assert (Y9 : 18446603336221196297 <= ((((18446744073709551615 * (vfirst E + k)) mod 2 ^ 64) + 18446744073709551614) mod 2 ^ 64) <= 18446744073709547517).
  { rewrite Z.add_mod_idemp_l by (clear; lia).
    match goal with |- _ <= ?a mod 2 ^ 64 <= _ => rewrite <- (Z.mod_unique a (2 ^ 64) (vfirst E + k) (2 ^ 64 - (vfirst E + k) - 2)) end;
      clear - GF1 Hk; lia. }
  pose proof (E_C176 E X _ _ _ _ ST) as C176.
  LeanFeed.pfeed P (PNADOP2.adoI5_conc fx R (view Ac modelc Mc) (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 50%nat => vF E
      | 83%nat => vfirst E + k | 84%nat => 2 * n | _ => 0 end)) ltac:(PNADK.dsc).

  assert (N2 : 2 * n / 2 = n) by (rewrite Z.mul_comm; apply Z_div_mult; clear; Lia.lia).
  assert (L0 : Z.land (2 * n) 1 = 0) by (change 1 with (Z.ones 1); rewrite Z.land_ones by (clear; Lia.lia); change (2 ^ 1) with 2; rewrite Z.mul_comm; apply Z_mod_mult).
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ZS).
  assert (WS3 : forall a, vF E / 8 + 2147450880 + 30 <= a < vF E / 8 + 2147450880 + 30 + 3 -> PNADO1.Wout (vfirst E) (vF E) a)
    by (intros a Ha; right; right; unfold PNADD.SH, PNADD.SBv; clear - Ha; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A1 & A10 & A11 & A12 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & HX1 & HX2)
    | [ (MS1 & KS1 & A10 & A11 & A12 & A18 & A19 & A20 & A21 & A23 & A24 & HX1 & HX2) | (MS1 & KS1 & A10 & A12 & A19 & A21 & A24 & HX) ]]);
    (assert (EM : M1 = view Ac modelc Mc) by (apply functional_extensionality; exact FW1)); subst M1; rewrite ?N2 in *.
  - (* [comment removed for export] *)
    rewrite !Z.mod_small in HX1 by (clear - GF1 Hk Hn; lia).
    apply (vpiece E X fx fx1 R R1 0xb460c 0x77c94 Mc modelc LKc Ac (view Ac modelc Mc) ST MS1 (PNADO1.vout_refl _ _ _)).
    intros M3 model3 ST3 V3.
    pose proof (view_F E X (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac (PNST.bax_add_dec (vax E)) M3 model3 LKc Ac) as AG3.
    assert (AG3' : forall a, vF E <= a < vF E + 512 \/ PNADD.SH (vF E) <= a < PNADD.SH (vF E) + 64 \/ vfirst E <= a < vfirst E + 42 -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
      by (intros a Ha; exact (AG3 a (dsg_of_dst L ar HI E _ _ _ _ ST) (dsg_of_dst L ar HI E _ _ _ _ ST3) V3 Ha)).
    clear AG3.
    destruct (vstr_xfer E X Mc M3 n AG3' VS) as (SDEF3 & SACC3 & _ & SB3).
    pose proof ST3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ZS3).
    apply (dgo_memcpy E X _ fx1 R1 M3 model3 LKc Ac (vfirst E + k + 1) (vF E + 241) n 0xb4654 (dsg_of_dst L ar HI E _ _ _ _ ST3));
      [clear - Hk; lia| clear - HX1; lia| clear - Hn; lia| clear; lia| clear - Hn; lia
      | intros i Hi; replace (vF E + 241 + i) with (vF E + 240 + (1 + i)) by (clear; lia); apply SDEF3; clear - Hi Hn; lia
      | intros a Ha; apply SACC3; clear - Ha Hn; lia
      | exact A10| exact A11| exact A12| rewrite (KS1 _) by inl; rewrite Q4; exact (c_Rtp L ar HI E X)| exact A1| reflexivity| clear; lia| rewrite (KS1 _) by inl; exact Q2|].
    intros Rb Mb modelb RPb STb ZSb.
    pose proof (dst_of_dsg L ar HI E _ _ _ _ STb (ZSb ZS3)) as STb'.
    pose proof (E_MIA E X _ _ _ _ STb') as MIb.
    destruct MIb as (W1b & W2b & W3b & W4b & W5b & ICb & CSBb & CUARb & SVb & C128b & FLCb & ZF6b & ZSIGb). unfold PNADD.SH, PNADD.SBv in W4b.
    assert (KB : forall j, In j L5K.CS -> getr Rb (reg j) = getr R1 (reg j)) by (intros j Hj; exact (L5K.regs_preserved_index R1 Rb j RPb Hj)).
    assert (B2 : getr Rb (reg 2) = Z_to_bv 64 (vsp E - 256)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; exact Q2).
    assert (B8 : getr Rb (reg 8) = Z_to_bv 64 (vsp E)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; exact Q8).
    assert (B9 : getr Rb (reg 9) = Z_to_bv 64 (vsp E - 256)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; exact Q9).
    assert (B18 : getr Rb (reg 18) = Z_to_bv 64 (vfirst E + k + n + 1)) by (rewrite (KB _) by inl; exact A18).
    pose proof A19 as B19. rewrite <- (KB 19%nat ltac:(inl)) in B19.
    pose proof A20 as B20. rewrite <- (KB 20%nat ltac:(inl)) in B20.
    assert (B22 : getr Rb (reg 22) = Z_to_bv 64 (2 * n / 2)) by (rewrite (KB _) by inl; rewrite N2; exact A22).
    pose proof A23 as B23. rewrite <- (KB 23%nat ltac:(inl)) in B23.
    assert (B27 : getr Rb (reg 27) = getr R (reg 27)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; reflexivity). rewrite Q27 in B27.
    assert (X6 : 0 <= vfirst E + k + n + 1 < 2 ^ 64) by (clear - GF1 Hk Hn; lia).
    pose proof (E_C176 E X _ _ _ _ STb') as Cb.
    LeanFeed.pfeed P6 (PNADOP2.adoI6_conc fx1 Rb (view Ac modelb Mb) (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 50%nat => vF E
      | 83%nat => vfirst E + k | 84%nat => 2 * n | 85%nat => vfirst E + k + n + 1 | _ => 0 end)) ltac:(PNADK.dsc).
    destruct P6 as (fx2 & R2 & M2 & MG2 & _ & FZ2 & MS2 & KS2 & C10 & C11 & C21 & C24 & C25 & _).
    assert (E24 : getr R2 (reg 24) = Z_to_bv 64 (vfirst E + k + n + 1)).
    { rewrite C24. rewrite (KB _) by inl. rewrite A24. rewrite L5.unsigned_lit by (clear - GF1 Hk; lia). rewrite N2. f_equal. clear; lia. }
    assert (E25 : getr R2 (reg 25) = Z_to_bv 64 0).
    { rewrite C25. cbn [AX2.edenot AX2.ev]. rewrite ec_eval by (clear - GF1 Hk Hn; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (clear - HX1; lia). reflexivity. }
    apply (to_retp E X fx1 fx2 Rb R2 0xb4654 Mb modelb LKc Ac M2 (vfirst E + k + n + 1) 0 STb' MS2).
    + exact (PNADO1.vout_step _ _ _ _ _ _ (PNADO1.vout_refl _ _ _) MG2 FZ2 WS3).
    + unfold PNADD.stE, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [exact E24 | exact E25 | (rewrite (KS2 _) by inl; first [assumption | (rewrite (KB _) by inl; rewrite (KS1 _) by inl; assumption)])].
    + clear - HX1 Hk Hn. lia.
    + left. reflexivity.
    + exact KONT.
  - (* [comment removed for export] *)
    idtac.
    assert (B2 : getr R1 (reg 2) = Z_to_bv 64 (vsp E - 256)) by (rewrite (KS1 _) by inl; exact Q2).
    assert (B8 : getr R1 (reg 8) = Z_to_bv 64 (vsp E)) by (rewrite (KS1 _) by inl; exact Q8).
    assert (B9 : getr R1 (reg 9) = Z_to_bv 64 (vsp E - 256)) by (rewrite (KS1 _) by inl; exact Q9).
    assert (B27 : getr R1 (reg 27) = getr R (reg 27)) by (rewrite (KS1 _) by inl; reflexivity). rewrite Q27 in B27.
    clear Q2 Q8 Q9 Q23 Q19 Q20 Q27.
    rewrite !Z.mod_small in HX1 by (clear - GF1 Hk Hn; lia).
    LeanFeed.pfeed P6 (PNADOP2.adoI5n_conc fx1 R1 (view Ac modelc Mc) (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 50%nat => vF E | 84%nat => 2 * n | _ => 0 end)) ltac:(PNADK.dsc).
    destruct P6 as (fx2 & R2 & M2 & MG2 & _ & FZ2 & MS2 & KS2 & C10 & C11 & C24 & C25 & _).
    assert (E25 : getr R2 (reg 25) = Z_to_bv 64 75).
    { rewrite C25. cbn [AX2.edenot AX2.ev]. rewrite A18. rewrite ec_eval by (clear - GF1 Hk Hn; lia). rewrite (proj2 (Z.ltb_ge _ _)) by (clear - HX1; lia). reflexivity. }
    apply (to_retp E X fx fx2 R R2 0xb460c Mc modelc LKc Ac M2 (vfirst E + k + 1) 75 ST (msteps_trans _ _ _ _ MS1 MS2)).
    + exact (PNADO1.vout_step _ _ _ _ _ _ (PNADO1.vout_refl _ _ _) MG2 FZ2 WS3).
    + unfold PNADD.stE, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [(rewrite C24; exact A24) | exact E25 | (rewrite (KS2 _) by inl; first [assumption | (rewrite (KS1 _) by inl; assumption)])].
    + clear - Hk. lia.
    + right. reflexivity.
    + exact KONT.
  - (* [comment removed for export] *)
    exfalso. rewrite L0 in HX. clear - HX. change ((0 - 0) mod 2 ^ 64) with 0 in HX. Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma sci_fi E (X : dkc L ar HI E) (fx : FPState) Ra Mc modelc LKc Ac k n scw :
  PNRAa.from_int_spec L ar HI ->
  dst L ar HI E Mc modelc LKc Ac -> PM.vstr_at RSEGS PMSPA.accA Mc (vF E + 240) (PM.VShort n) -> 0 <= n <= 1 -> - 2 ^ 31 <= scw < 2 ^ 31 -> 1 <= k <= 36 ->
  PNADO1.RL (vR E) (vsp E) (vfirst E) (vF E) Ra -> getr Ra (reg 21) = Z_to_bv 64 (vF E + 240) -> getr Ra (reg 25) = Z_to_bv 64 (vfirst E + k) ->
  getr Ra (reg 1) = Z_to_bv 64 0xb460c -> getr Ra (reg 10) = Z_to_bv 64 scw -> getr Ra (reg 11) = Z_to_bv 64 (vF E + 240) ->
  okont E ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra 0xb6200 Mc modelc) (vK E).
Proof.
  intros FI ST VS Hn Hs Hk RLR G21 G25 G1 G10 G11 KONT.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20).
  apply (dgo_fi E X fx Ra Mc modelc LKc Ac scw n 0xb460c FI ST VS ltac:(clear - Hn; lia) Hs G1 ltac:(split; [clear; lia| reflexivity]) Q2
           ltac:(rewrite Q3; exact (c_Rgp L ar HI E X)) ltac:(rewrite Q4; exact (c_Rtp L ar HI E X)) G10 G11).
  intros fx' Rb Mb modelb LKb Ab n' RPb STb VSb Hn'.
  assert (KB : forall j, In j L5K.CS -> getr Rb (reg j) = getr Ra (reg j)) by (intros j Hj; exact (L5K.regs_preserved_index Ra Rb j RPb Hj)).
  apply (sci_copy E X fx' Rb Mb modelb LKb Ab k n' STb VSb ltac:(clear - Hn Hn'; lia) Hk).
  - unfold PNADO1.RL, PNADD.RBA. repeat apply conj; (rewrite (KB _) by inl; assumption).
  - rewrite (KB _) by inl. exact G21.
  - rewrite (KB _) by inl. exact G25.
  - exact KONT.
Qed.

(* [comment removed for export] *)
Lemma sci_sign E (X : dkc L ar HI E) (fx : FPState) R Mc modelc LKc Ac k scw :
  PNRAa.str_push_back_short_spec L ar HI -> PNRAa.from_int_spec L ar HI ->
  dst L ar HI E Mc modelc LKc Ac -> PM.vstr_at RSEGS PMSPA.accA Mc (vF E + 240) (PM.VShort 0) -> - 2 ^ 31 <= scw < 2 ^ 31 -> 1 <= k <= 36 ->
  PNADO1.RL (vR E) (vsp E) (vfirst E) (vF E) R -> getr R (reg 21) = Z_to_bv 64 (vF E + 240) -> getr R (reg 24) = Z_to_bv 64 scw ->
  getr R (reg 25) = Z_to_bv 64 (vfirst E + k) -> okont E ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb45f0 Mc modelc) (vK E).
Proof.
  intros PBS FI ST VS Hs Hk RLR G21 G24 G25 KONT.
  pose proof (c_GEOM L ar HI E X) as GEOM. pose proof (sp_rng L ar HI E X) as SR. pose proof (E_MIA E X _ _ _ _ ST) as MI.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof GEOM as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof MI as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  set (w := scw mod 2 ^ 64).
  assert (X7 : 0 <= w < 2 ^ 64) by (apply Z.mod_pos_bound; clear; Lia.lia).
  assert (EW : Z_to_bv 64 w = Z_to_bv 64 scw) by (apply PNADO1.to_bv_eqm; unfold w; rewrite Z.mod_mod by (clear; Lia.lia); reflexivity).
  assert (G24' : getr R (reg 24) = Z_to_bv 64 w) by (rewrite EW; exact G24).
  assert (X1 : 0 <= vsp E < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= vfirst E < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= vF E < 2 ^ 64) by (clear - GFF1; lia).
  assert (Y4 : vsp E mod 32 = 0) by exact GS32.
  LeanFeed.pfeed P (PNADOP2.adoI3b_conc fx R (view Ac modelc Mc) (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 50%nat => vF E | 81%nat => w | _ => 0 end)) ltac:(PNADK.dsc).
  assert (RAOK : forall ra, ra = 0xb460c \/ ra = 0xb4600 -> L5.ra_ok ra) by (intros ra [-> | ->]; (split; [clear; lia| reflexivity])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A1 & A10 & A11 & HX) | (MS1 & KS1 & A1 & A10 & A11 & HX) ]);
    (assert (EM : M1 = view Ac modelc Mc) by (apply functional_extensionality; exact FW1)); subst M1; clear HX;
    apply (vpiece E X fx fx1 R R1 0xb45f0 _ Mc modelc LKc Ac (view Ac modelc Mc) ST MS1 (PNADO1.vout_refl _ _ _));
    intros M3 model3 ST3 V3;
    pose proof (view_F E X (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac (PNST.bax_add_dec (vax E)) M3 model3 LKc Ac) as AG3;
    (assert (AG3' : forall a, vF E <= a < vF E + 512 \/ PNADD.SH (vF E) <= a < PNADD.SH (vF E) + 64 \/ vfirst E <= a < vfirst E + 42 -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
      by (intros a Ha; exact (AG3 a (dsg_of_dst L ar HI E _ _ _ _ ST) (dsg_of_dst L ar HI E _ _ _ _ ST3) V3 Ha)));
    clear AG3; pose proof (vstr_xfer E X Mc M3 0 AG3' VS) as VS3.
  - (* [comment removed for export] *)
    apply (sci_fi E X fx1 R1 M3 model3 LKc Ac k 0 scw FI ST3 VS3 ltac:(clear; lia) Hs Hk).
    + unfold PNADO1.RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; (rewrite (KS1 _) by inl; assumption).
    + rewrite (KS1 _) by inl. exact G21.
    + rewrite (KS1 _) by inl. exact G25.
    + exact A1.
    + rewrite A10. exact EW.
    + exact A11.
    + exact KONT.
  - (* [comment removed for export] *)
    apply (dgo_pbs E X fx1 R1 M3 model3 LKc Ac 0 0xb4600 PBS ST3 VS3 ltac:(clear; lia) A1 (RAOK _ (or_intror eq_refl)) ltac:(rewrite (KS1 _) by inl; exact Q2)
             ltac:(rewrite (KS1 _) by inl; rewrite Q3; exact (c_Rgp L ar HI E X)) ltac:(rewrite (KS1 _) by inl; rewrite Q4; exact (c_Rtp L ar HI E X)) A10).
    intros fx' Rb Mb modelb LKb Ab RPb STb VSb. change (0 + 1) with 1 in VSb.
    assert (KB : forall j, In j L5K.CS -> getr Rb (reg j) = getr R1 (reg j)) by (intros j Hj; exact (L5K.regs_preserved_index R1 Rb j RPb Hj)).
    pose proof (E_MIA E X _ _ _ _ STb) as MIb.
    destruct MIb as (W1b & W2b & W3b & W4b & W5b & ICb & CSBb & CUARb & SVb & C128b & FLCb & ZF6b & ZSIGb).
    assert (B2 : getr Rb (reg 2) = Z_to_bv 64 (vsp E - 256)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; exact Q2).
    assert (B8 : getr Rb (reg 8) = Z_to_bv 64 (vsp E)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; exact Q8).
    assert (B9 : getr Rb (reg 9) = Z_to_bv 64 (vsp E - 256)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; exact Q9).
    assert (B19 : getr Rb (reg 19) = getr R (reg 19)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; reflexivity). rewrite Q19 in B19.
    assert (B20 : getr Rb (reg 20) = getr R (reg 20)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; reflexivity). rewrite Q20 in B20.
    assert (B21 : getr Rb (reg 21) = getr R (reg 21)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; reflexivity). rewrite G21 in B21.
    assert (B23 : getr Rb (reg 23) = getr R (reg 23)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; reflexivity). rewrite Q23 in B23.
    assert (B24 : getr Rb (reg 24) = Z_to_bv 64 w) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; exact G24').
    assert (B27 : getr Rb (reg 27) = getr R (reg 27)) by (rewrite (KB _) by inl; rewrite (KS1 _) by inl; reflexivity). rewrite Q27 in B27.
    LeanFeed.pfeed P4 (PNADOP2.adoI4_conc fx' Rb (view Ab modelb Mb) (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 50%nat => vF E | 81%nat => w | _ => 0 end)) ltac:(PNADK.dsc).
    destruct P4 as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & MS2 & KS2 & C1 & C10 & C11).
    assert (EM : M2 = view Ab modelb Mb) by (apply functional_extensionality; exact FW2). subst M2.
    apply (vpiece E X fx' fx2 Rb R2 0xb4600 _ Mb modelb LKb Ab (view Ab modelb Mb) STb MS2 (PNADO1.vout_refl _ _ _)).
    intros M5 model5 ST5 V5.
    pose proof (view_F E X (PNST.bax_add_dec (vax E)) Mb modelb LKb Ab (PNST.bax_add_dec (vax E)) M5 model5 LKb Ab) as AG5.
    assert (AG5' : forall a, vF E <= a < vF E + 512 \/ PNADD.SH (vF E) <= a < PNADD.SH (vF E) + 64 \/ vfirst E <= a < vfirst E + 42 -> M5 (Z_to_bv 64 a) = Mb (Z_to_bv 64 a))
      by (intros a Ha; exact (AG5 a (dsg_of_dst L ar HI E _ _ _ _ STb) (dsg_of_dst L ar HI E _ _ _ _ ST5) V5 Ha)).
    clear AG5. pose proof (vstr_xfer E X Mb M5 1 AG5' VSb) as VS5.
    apply (sci_fi E X fx2 R2 M5 model5 LKb Ab k 1 scw FI ST5 VS5 ltac:(clear; lia) Hs Hk).
    + unfold PNADO1.RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; (rewrite (KS2 _) by inl; first [assumption | (rewrite (KB _) by inl; rewrite (KS1 _) by inl; assumption)]).
    + rewrite (KS2 _) by inl. exact B21.
    + rewrite (KS2 _) by inl. rewrite (KB _) by inl. rewrite (KS1 _) by inl. exact G25.
    + exact C1.
    + rewrite C10. exact EW.
    + exact C11.
    + exact KONT.
Qed.

(* [comment removed for export] *)
Lemma arm_sci E (X : dkc L ar HI E) sigma z sd scw (fx : FPState) R Mc modelc LKc Ac :
  PNRAa.str_push_back_short_spec L ar HI -> PNRAa.from_int_spec L ar HI ->
  0 <= sigma <= 1 -> 0 <= z -> 1 <= sd -> z + sd <= 36 -> - 2 ^ 31 <= scw < 2 ^ 31 ->
  dst L ar HI E Mc modelc LKc Ac -> PNADD.sdigs (vF E) (view Ac modelc Mc) z sd ->
  PNADO1.RLO (vR E) (vsp E) (vfirst E) (vF E) sigma z sd R ->
  getr R (reg 10) = Z_to_bv 64 (sd - 1) -> getr R (reg 24) = Z_to_bv 64 scw -> okont E ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb4388 Mc modelc) (vK E).
Proof.
  intros PBS FI Hsig Hz Hsd Hzs Hs ST SD RLO G10 G24 KONT.
  pose proof (c_GEOM L ar HI E X) as GEOM. pose proof (sp_rng L ar HI E X) as SR. pose proof (E_FHI E X) as FHI. pose proof (E_MIA E X _ _ _ _ ST) as MI.
  destruct (PNADO1.sci_head _ _ _ _ _ _ _ GEOM _ sigma z sd MI SD Hsig Hz Hsd Hzs SR scw fx R _ RLO G10 G24 (PNADO1.vout_refl _ _ _))
    as (fx1 & R1 & M1 & k & MS1 & VO1 & RL1 & C24 & C25 & Hk & Hk36).
  pose proof RL1 as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof GEOM as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (PNADO1.MIA_out _ _ _ _ _ _ _ GEOM _ _ MI VO1) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (PNADO1.dst_facts _ _ _ _ _ _ _ GEOM _ M1 k MI VO1 ltac:(clear - Hk Hk36 Hsig; lia)) as (TR & TZ & TW & TSH & TS & TI & TD).
  pose proof (PNADO1.geomF _ _ _ _ _ GEOM) as (E0 & SHlo & SHhi). unfold PNADD.SH, PNADD.SBv in SHlo, SHhi, W4.
  assert (X1 : 0 <= vsp E < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= vfirst E < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= vF E < 2 ^ 64) by (clear - GFF1; lia).
  assert (X4 : 0 <= vfirst E + k < 2 ^ 64) by (clear - TR; lia).
  assert (Y4 : vsp E mod 32 = 0) by exact GS32. assert (Y5 : vF E mod 32 = 0) by exact GFF32.
  assert (Y7 : 65536 + 6840320 <= vF E / 8 + 2147450880 \/ vF E / 8 + 2147450880 + 64 <= 65536) by (left; clear - SHlo; lia).
  assert (Y8 : vfirst E + k + 1 <= vF E / 8 + 2147450880 \/ vF E / 8 + 2147450880 + 64 <= vfirst E + k) by (clear - TSH SHlo SHhi; lia).
  LeanFeed.pfeed P (PNADOP2.adoI3_conc fx1 R1 M1 (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 50%nat => vF E | 83%nat => vfirst E + k | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx2 & R2 & M2 & MG2 & _ & FZ2 & MS2 & KS2 & A1 & A10 & A11 & A12 & A21 & A22 & U32 & U31 & U30 & UE).
  assert (VO2 : PNADO1.vout (vfirst E) (vF E) (view Ac modelc Mc) M2).
  { apply (PNADO1.vout_step _ _ _ _ _ (fun i => (vfirst E + k + 0 <= i < vfirst E + k + 0 + 1) \/ (vF E / 8 + 2147450880 + 30 <= i < vF E / 8 + 2147450880 + 30 + 3)) VO1 MG2).
    - intros i Hi HN. apply FZ2; [exact Hi| intros Y; apply HN; left; exact Y| intros Y; apply HN; right; exact Y].
    - intros a [Y|Y]; [left; clear - Y Hk Hk36 Hsig; lia| right; right; unfold PNADD.SH, PNADD.SBv; clear - Y; lia]. }
  apply (vpiece E X fx fx2 R R2 0xb4388 0x78130 Mc modelc LKc Ac M2 ST (msteps_trans _ _ _ _ MS1 MS2) VO2).
  intros M3 model3 ST3 V3.
  pose proof (proj2 (gmem_of L ar C HI LY HIok E X _ _ _ _ _ (dsg_of_dst L ar HI E _ _ _ _ ST3))) as (VSK & VFI & VFF & VSH & VSHF & VIMG).
  assert (ZS30v : L5KA.zeros_at M2 (vF E / 8 + 2147450880 + 30) 3).
  { intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2) by (clear - Hi; lia).
    destruct Hc as [-> | [-> | ->]];
      [ replace (vF E / 8 + 2147450880 + 30 + 0) with (vF E / 8 + 2147450910) by (clear; lia); apply (L5ADHR.byte_of_u8 M2 _ 0 U30); [right; clear - SHlo; lia| clear - SHlo SHhi; lia]
      | replace (vF E / 8 + 2147450880 + 30 + 1) with (vF E / 8 + 2147450911) by (clear; lia); apply (L5ADHR.byte_of_u8 M2 _ 0 U31); [right; clear - SHlo; lia| clear - SHlo SHhi; lia]
      | replace (vF E / 8 + 2147450880 + 30 + 2) with (vF E / 8 + 2147450912) by (clear; lia); apply (L5ADHR.byte_of_u8 M2 _ 0 U32); [right; clear - SHlo; lia| clear - SHlo SHhi; lia] ]. }
  assert (ZS30 : L5KA.zeros_at M3 (vF E / 8 + 2147450880 + 30) 3).
  { apply (proj1 (L5A.zeros_at_vis (ahid Ac model3) M3 _ 3 (L5A.avis_sub _ _ _ (vF E / 8 + 2147450880 + 30) 3 VSH ltac:(unfold PNADD.SH, PNADD.SBv; clear; lia) ltac:(unfold PNADD.SH, PNADD.SBv; clear; lia)))).
    rewrite V3. exact ZS30v. }
  assert (F8 : (vF E + 240) mod 8 = 0).
  { replace (vF E + 240) with (vF E + 30 * 8) by (clear; lia). rewrite Z_mod_plus_full. pose proof (Z.div_mod (vF E) 32 ltac:(clear; lia)) as D. rewrite GFF32, Z.add_0_r in D. rewrite D.
    replace (32 * (vF E / 32)) with ((4 * (vF E / 32)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (Q8' : (vF E + 240) / 8 = vF E / 8 + 30).
  { replace (vF E + 240) with (vF E + 30 * 8) by (clear; lia). apply Z_div_plus. clear; lia. }
  assert (ACC3 : PMSPA.accA M3 (vF E + 240) 24).
  { apply PNADS.aacc_of_zeros; [exact F8| clear; lia|]. change ((24 + 7) / 8) with 3. rewrite Q8'. replace (vF E / 8 + 30 + 2147450880) with (vF E / 8 + 2147450880 + 30) by (clear; lia). exact ZS30. }
  pose proof ST3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ZS3).
  apply (dgo_memset_F E X _ fx2 R2 M3 model3 LKc Ac (vF E + 240) 0 24 0xb45f0 (dsg_of_dst L ar HI E _ _ _ _ ST3));
    [clear; lia| clear; lia| clear; lia| exact ACC3| exact A10| exact A11| exact A12| rewrite (KS2 _) by inl; rewrite Q4; exact (c_Rtp L ar HI E X)| exact A1| reflexivity| clear; lia
    | rewrite (KS2 _) by inl; exact Q2|].
  intros Rb Mb modelb RPb STb ZSb BYTES FK.
  pose proof (dst_of_dsg L ar HI E _ _ _ _ STb (ZSb ZS3)) as STb'.
  assert (KB : forall j, In j L5K.CS -> getr Rb (reg j) = getr R2 (reg j)) by (intros j Hj; exact (L5K.regs_preserved_index R2 Rb j RPb Hj)).
  assert (VSb : PM.vstr_at RSEGS PMSPA.accA Mb (vF E + 240) (PM.VShort 0)).
  { split; [| split; [| split; [clear; lia|]]].
    - intros i Hi. rewrite (BYTES i Hi). discriminate.
    - apply (aacc_agree M3 Mb _ _); [| exact ACC3]. intros a Ha. pose proof (S_rng (vF E + 240) 24 a F8 ltac:(clear; lia) Ha) as SRa. change ((24 + 7) / 8) with 3 in SRa. rewrite Q8' in SRa.
      apply FK. right. unfold PNADD.SH, PNADD.SBv. clear - SRa. lia.
    - change (2 * 0) with 0. pose proof (BYTES 0 ltac:(clear; lia)) as B0. rewrite Z.add_0_r in B0. unfold L5.u8_at. cbn [rdn]. rewrite B0. reflexivity. }
  apply (sci_sign E X fx2 Rb Mb modelb LKc Ac k scw PBS FI STb' VSb Hs ltac:(clear - Hk Hk36 Hsig; lia)).
  - unfold PNADO1.RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; (rewrite (KB _) by inl; rewrite (KS2 _) by inl; assumption).
  - rewrite (KB _) by inl. exact A21.
  - rewrite (KB _) by inl. rewrite (KS2 _) by inl. exact C24.
  - rewrite (KB _) by inl. rewrite (KS2 _) by inl. exact C25.
  - exact KONT.
Qed.

(* [comment removed for export] *)
Theorem out_ok : PNRAa.str_push_back_short_spec L ar HI -> PNRAa.from_int_spec L ar HI -> PNADK.out_stmt L ar HI.
Proof.
  intros PBS FI E X fx Rc Mc modelc LKc Ac sigma e z sd ST (SP & MI & SD & Hsig & He & Hz & Hsd & Hzs) KONT.
  pose proof (c_GEOM L ar HI E X) as GEOM. pose proof (sp_rng L ar HI E X) as SR.
  assert (XF : forall (M3 : mem) model3, dst L ar HI E M3 model3 LKc Ac -> view Ac model3 M3 = view Ac modelc Mc -> PNADD.sdigs (vF E) (view Ac model3 M3) z sd)
    by (intros M3 model3 _ V3; rewrite V3; exact SD).
  destruct (PNADO1.fork _ _ _ _ _ _ _ GEOM _ sigma z sd MI Hz Hsd Hzs SR fx Rc _ e SP He (PNADO1.vout_refl _ _ _))
    as (fx1 & R1 & [ (MS & RLO1 & G10 & G24 & Hc) | [ (MS & RLO1 & G14 & He2 & Hlo) | (MS & RLO1 & He6) ]]).
  - apply (vpiece E X fx fx1 Rc R1 0xb4294 0xb4388 Mc modelc LKc Ac (view Ac modelc Mc) ST MS (PNADO1.vout_refl _ _ _)).
    intros M3 model3 ST3 V3.
    exact (arm_sci E X sigma z sd (sd + e - 6177) fx1 R1 M3 model3 LKc Ac PBS FI Hsig Hz Hsd Hzs ltac:(clear - He Hsd Hzs Hz; lia) ST3 (XF M3 model3 ST3 V3) RLO1 G10 G24 KONT).
  - apply (vpiece E X fx fx1 Rc R1 0xb4294 0xb44ac Mc modelc LKc Ac (view Ac modelc Mc) ST MS (PNADO1.vout_refl _ _ _)).
    intros M3 model3 ST3 V3.
    exact (arm_radix E X sigma z sd e fx1 R1 M3 model3 LKc Ac Hsig Hz Hsd Hzs ltac:(clear - He He2; lia) Hlo ST3 (XF M3 model3 ST3 V3) RLO1 G14 KONT).
  - apply (vpiece E X fx fx1 Rc R1 0xb4294 0xb42cc Mc modelc LKc Ac (view Ac modelc Mc) ST MS (PNADO1.vout_refl _ _ _)).
    intros M3 model3 ST3 V3.
    exact (arm_regular E X sigma z sd fx1 R1 M3 model3 LKc Ac Hsig Hz Hsd Hzs ST3 (XF M3 model3 ST3 V3) RLO1 KONT).
Qed.

End WithHeap.
End SCFG_1.
End PNADO2.
