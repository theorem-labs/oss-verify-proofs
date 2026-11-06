(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIfaceAEx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmAUarK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
Local Ltac lia := L5FastLia.plia.

Module PMAUKS.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR. Import L5CBR. Import L5ADHR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Section CTX.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (sp SCR : Z) (spc olo ohi : Z) (ocell : Z -> Prop) (own : (word -> option byte) -> Prop)
          (F fl : Z) (k : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit) (BX0 : list (Z * Z)).
Local Notation B := (ff_bytes k).
Local Notation FF' := ((F, k, spc + 32) :: FF).
Local Notation gctx := (PMAUK.gctx L ar HI LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0).
Local Notation binv := (PMAUK.binv L ar HI M model LB FF LK A sp SCR spc own F k).
Local Notation Wret := (PMAUK.Wret F fl k).

(* [comment removed for export] *)
Lemma binv_pieceS (G : gctx) W BX Mc modelc LKc crc Ac M1 model1 (Wp Wy : Z -> Prop) :
  binv W BX Mc modelc LKc crc Ac ->
  ri_inv HI (BX ++ LB) FF' LKc crc Ac M1 (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 -> mem_grows Mc M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, Wy a -> ~ aclient L ar LB FF sp SCR a /\ ~ ocell a) ->
  (forall a, Wp a -> Wy a \/ (~ ocell a /\ ((spc <= a < sp) \/ F <= a < F + B \/ F / 8 + SB <= a < F / 8 + SB + B / 8 \/ ~ L5.outside W a))) ->
  binv W BX M1 model1 LKc crc Ac.
Proof.
destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 MG FRM NCY WP.
unfold PMAUK.binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
split. eapply astk_grows. exact B6. exact MG.
split. { eapply ek_trans. exact B7. intros a (Ha & Hc & Ho). apply FRM. exact Ha. intros X. destruct (WP a X) as [Y|(_ & [Y|[Y|[Y|Y]]])].
- exact (proj1 (NCY a Y) Hc).
- apply (NCS a). exact Y. exact Hc.
- apply (NCF a). left; exact Y. exact Hc.
- apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - Y. unfold SB in Y |- *. lia. exact Hc.
- exact (Y Ho). }
split. { eapply dk_trans. exact B8. apply dk_grows. exact MG. }
split. { apply (OWNAG Mc M1 B9). intros a Ha. apply FRM. pose proof (OCR a Ha). clear - H SPC SLO. lia.
intros X. destruct (WP a X) as [Y|Y]; [exact (proj2 (NCY a Y) Ha)| exact (proj1 Y Ha)]. }
eapply L5.defined_grows. exact MG. exact B10.
Qed.

(* [comment removed for export] *)
Definition WretY (Wx Wy : Z -> Prop) (a : Z) : Prop := Wret a \/ Wx a \/ Wy a.
Lemma retire_coreS (G : gctx) W BX Mc modelc LKc crc Ac (Wx Wy : Z -> Prop) (fx fx9 : FPState) Rc (pc : Z) R9 (r : Z) M9v (K : TSet) :
  binv W BX Mc modelc LKc crc Ac ->
  (forall a, Wx a -> aclientw L ar (BX ++ LB) FF' 0 0 a /\ ~ L5.outside W a) -> (forall a, Wx a \/ ~ Wx a) ->
  (forall a, Wy a -> sp - SCR <= a < sp /\ ~ aclient L ar LB FF sp SCR a) -> (forall a, Wy a \/ ~ Wy a) ->
  msteps RSEGS (st fx Rc pc (mrestrict (ahid Ac modelc) Mc)) (st fx9 R9 r M9v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ WretY Wx Wy a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 ->
  (forall (Mf : word -> option byte) (modelf : Model),
      (forall a, 0 <= a < 2 ^ 64 -> ~ WretY Wx Wy a -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      mem_grows Mc Mf -> mrestrict (ahid Ac modelc) Mf = M9v ->
      ahpres L ar LB FF sp SCR W M Mf ->
      model_rt model modelf -> amodel_ok Ac modelf ->
      ri_inv HI (BX ++ LB) FF LKc crc Ac Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fx9) R9 r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof. 
intros BI WX WXD WY WYD wMS MG9 wFZ wFL0 KF.
destruct (PMAUK.vis_facts L ar C HI LY HIok M model LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 G W BX Mc modelc LKc crc Ac BI)
as (_ & _ & _ & (FLC8 & FLV8 & _)).
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
assert (FLNC8 : ~ aclient L ar (BX ++ LB) FF' 0 0 fl).
{ apply (not_client_bx L ar FF' fl BX LB). apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LB B1 eq_refl). exact FLP. exact FLBIG. exact FLNC. }
apply (apiece_retire L ar C HI LY HIok (BX ++ LB) FF LKc crc Ac Mc modelc fx fx9 Rc pc R9 r M9v (WretY Wx Wy) F k (spc + 32) fl K B1 B2).
{ exact FLC8. }
{ exact FLNC8. }
{ exact FLV8. }
{ clear - FLR; lia. }
{ exact wMS. }
{ exact MG9. }
{ exact wFZ. }
{ intros a Ha Wa. unfold WretY, PMAUK.Wret in Wa. destruct Wa as [[[Wa|Wa]|Wa]|[Wa|Wa]].
- right. apply (fframe_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity. clear - Wa FR; lia.
- right. apply (fframe_shadow_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity.
unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Wa. unfold SB in *. lia.
- left; exact Wa.
- right. exact (proj1 (WX a Wa)).
- right. destruct (WY a Wa) as (Y1 & _). unfold aclientw, aclient_g. right; left. split; [clear - Y1 SLO SPC; lia| intros Z; clear - Z; lia]. }
{ intros a. unfold WretY, PMAUK.Wret. destruct (WXD a) as [X|X]; [left; right; left; exact X|]. destruct (WYD a) as [Y|Y]; [left; right; right; exact Y|].
destruct (rng_dec a F (F + 8)); [left; left; left; left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + ff_bytes k / 8)); [left; left; left; right; tauto|].
destruct (Z.eq_dec a fl); [left; left; right; exact e|]. right. intros [[[Z|Z]|Z]|[Z|Z]]; tauto. }
{ exact wFL0. }
intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
assert (ASTK9 : astk ar M9 sp SCR). { eapply astk_grows. exact B6. exact MGM9. }
apply (KF M9 model9).
- exact FRM9.
- exact MGM9.
- exact VIS9.
- apply ahpres_of.
+ eapply ek_trans. exact B7.
intros a (Ha & Hc & Ho). apply FRM9. exact Ha. unfold WretY, PMAUK.Wret. intros [[[X|X]|X]|[X|X]].
* apply (NCF a). left; clear - X FR; lia. exact Hc.
* apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - X. unfold SB in X |- *. lia. exact Hc.
* subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
* exact (proj2 (WX a X) Ho).
* exact (proj2 (WY a X) Hc).
+ eapply astk_defined. exact ASTK9. clear - SPC; lia. clear; lia.
+ eapply dk_trans. exact B8. apply dk_grows. exact MGM9.
- eapply L5LZ.model_rt_trans. exact B3. exact RT9.
- exact AM9.
- exact HH9.
Qed.
End CTX.
End WithIface.
End SCFG_1.
End PMAUKS.
