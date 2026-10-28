(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AFKR.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR. Import L5CBR. Import L5ADHR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Local Abbreviation statics_vis := (L5ADHR.statics_vis L ar C HI LY HIok).

Section CTX.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (sp SCR : Z)                       (* [comment removed for export] *)
          (spc olo ohi : Z)                  (* [comment removed for export] *)
          (ocell : Z -> Prop) (own : (word -> option byte) -> Prop)
          (F fl : Z) (k : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation B := (ff_bytes k).
Local Notation FF' := ((F, k, spc + 32) :: FF).

Record gctx : Prop := GCTX {
  g_k : In k [0; 1; 2; 3; 4; 5];
  g_SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47;
  g_SLO : ahl_ceil ar + 4096 + SCR <= sp;
  g_SHI : sp <= ar_sptop ar;
  g_SPC : 0 <= spc /\ sp - SCR <= spc /\ spc <= olo /\ olo <= ohi /\ ohi <= sp /\ 0 <= SCR /\ sp <= 2 ^ 47;
  g_OCR : forall a, ocell a -> olo <= a < ohi;
  g_OWN : forall M1 M1', own M1 -> (forall a, ocell a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own M1';
  g_FS1 : ar_fs ar <= F;
  g_FS2 : F + B <= ar_fs ar + FS_BYTES;
  g_FCEIL : F + B <= ahl_ceil ar;
  g_LKI2 : incl LK2 LK;
  g_FLP : ar_fs ar <= fl < ar_fs ar + FS_BYTES;
  g_FLNC : ~ aclient L ar LB FF' 0 0 fl;
  g_HH2 : ri_inv HI LB FF' LK2 cr2 A M2 (vml_of model2);
  g_FLC : cell_is RSEGS M2 (F + B - 8) 8 fl;
  g_FR : 4096 <= F /\ F + B <= 2 ^ 47 /\ 6905856 <= F /\ 64 <= B <= 2048;
  g_F8 : F / 8 * 8 = F /\ (F + B - 1) / 8 = F / 8 + B / 8 - 1 /\ B / 8 * 8 = B;
  g_FBIG : 2147446784 + 17592186048512 <= F \/ F + B <= 2147446784;
  g_F32 : F mod 32 = 0;
  g_FLA : F + B <= fl \/ fl + 1 <= F;
  g_FLR : 4096 <= fl /\ fl + 1 <= 2 ^ 47 /\ 6905856 <= fl /\ fl + 1 <= ahl_ceil ar;
  g_FLBIG : 2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784;
  g_NCF : forall a : Z, F <= a < F + B \/ S F <= a <= S (F + B - 1) -> ~ aclient L ar LB FF sp SCR a;
  g_NCS : forall a : Z, spc <= a < sp -> ~ aclient L ar LB FF sp SCR a
}.
Ltac open_gctx G :=
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].

Definition binv (W : list L5.range) (BX : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
  ri_inv HI (BX ++ LB) FF' LKc crc Ac Mc (vml_of modelc) /\ amodel_ok Ac modelc /\ model_rt model modelc /\ incl A Ac /\ incl LKc LK /\
  astk ar Mc sp SCR /\ ek L ar LB FF sp SCR W M Mc /\ dk L ar LB FF sp SCR M Mc /\ own Mc /\ L5.defined Mc (F / 8 + SB) (B / 8).

Lemma binv_model W BX Mc modelc LKc crc Ac model1 :
  binv W BX Mc modelc LKc crc Ac -> ri_inv HI (BX ++ LB) FF' LKc crc Ac Mc (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 ->
  binv W BX Mc model1 LKc crc Ac.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1. unfold binv.
  split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5. split. exact B6. split. exact B7. split. exact B8. split. exact B9. exact B10.
Qed.

(* [comment removed for export] *)
Lemma binv_piece (G : gctx) W BX Mc modelc LKc crc Ac M1 model1 (Wp : Z -> Prop) :
  binv W BX Mc modelc LKc crc Ac ->
  ri_inv HI (BX ++ LB) FF' LKc crc Ac M1 (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 -> mem_grows Mc M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (spc <= a < sp /\ ~ ocell a) \/ F <= a < F + B \/ F / 8 + SB <= a < F / 8 + SB + B / 8) ->
  binv W BX M1 model1 LKc crc Ac.
Proof.
  open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 MG FRM WP.
  unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
  split. eapply astk_grows. exact B6. exact MG.
  split. { eapply ek_trans. exact B7. apply (ek_piece L ar LB FF sp SCR W Mc M1 Wp FRM). intros a Ha Hc _ X. destruct (WP a X) as [Y|[Y|Y]].
           - apply (NCS a). exact (proj1 Y). exact Hc.
           - apply (NCF a). left; exact Y. exact Hc.
           - apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - Y. unfold SB in Y |- *. lia. exact Hc. }
  split. { eapply dk_trans. exact B8. apply dk_grows. exact MG. }
  split. { apply (OWNAG Mc M1 B9). intros a Ha. apply FRM. pose proof (OCR a Ha). clear - H SPC SLO. lia.
           intros X. destruct (WP a X) as [Y|[Y|Y]]. exact (proj2 Y Ha). pose proof (OCR a Ha). clear - H Y SPC SLO FCEIL. lia.
           pose proof (OCR a Ha). clear - H Y SPC SLO SPT FR F8. unfold SB in Y. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia. }
  eapply L5.defined_grows. exact MG. exact B10.
Qed.

(* [comment removed for export] *)
Lemma binv_mem (G : gctx) W BX Mc modelc LKc crc Ac M1 model1 (D : Z -> Prop) scr :
  binv W BX Mc modelc LKc crc Ac ->
  ri_inv HI (BX ++ LB) FF' LKc crc Ac M1 (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BX ++ LB) FF' spc scr a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, spc - scr <= a < spc -> M1 (Z_to_bv 64 a) <> None) ->
  (forall a, D a -> M1 (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  (forall a, D a -> F + 32 <= a < F + B - 8) -> sp - SCR <= spc - scr -> 0 <= scr ->
  binv W BX M1 model1 LKc crc Ac.
Proof.
  open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 PRES SDEF DDEF DDEC DIN HS HS0.
  assert (PRES' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF spc scr a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc ND. apply PRES. exact Ha. apply aclient_cons. apply aclient_appb. exact Hc. exact ND. }
  unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
  split. { apply (astk_after_eq L ar C HI HIok (BX ++ LB) FF' LKc crc Ac Mc Mc M1 _ sp _ spc scr B1 B6 (mem_grows_refl Mc)).
           - intros a Ha Hs Hns. apply PRES. exact Ha. apply stack_client. exact Hs. exact Hns. intros X. apply DIN in X. clear - X Hs FR FCEIL; lia.
           - exact SDEF.
           - exact HS.
           - clear - SPC; lia.
           - clear - SPC; lia. }
  split. { eapply ek_trans. exact B7. apply (ek_mem L ar LB FF sp SCR spc scr D W Mc M1 PRES').
           - exact HS.
           - clear - SPC; lia.
           - intros a Hc _ X. apply DIN in X. apply (NCF a). left; clear - X FR; lia. exact Hc. }
  split. { eapply dk_trans. exact B8. apply (dk_mem L ar LB FF sp SCR spc scr D Mc M1 PRES' SDEF DDEF DDEC).
           - exact HS.
           - clear - SPC; lia. }
  split. { apply (OWNAG Mc M1 B9). intros a Ha. pose proof (OCR a Ha) as OC. apply PRES. clear - OC SPC SLO; lia. apply stack_client. clear - OC SPC SLO SHI SPT; lia. clear - OC SPC HS0; lia.
           intros X. apply DIN in X. clear - X OC SPC SLO FCEIL. lia. }
  intros i Hi. rewrite PRES. apply B10. exact Hi.
  - clear - Hi FR F8. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
  - apply (fframe_shadow_client L ar (BX ++ LB) FF' spc scr F k (spc + 32)). left; reflexivity. unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Hi. lia.
  - intros Y. apply DIN in Y. clear - Y Hi FR F8 FBIG. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
Qed.

(* [comment removed for export] *)
Lemma binv_callee (G : gctx) W W1 BX BXa BX1 Mc modelc LKc crc Ac M1 model1 LK1 cr1 A1 SCRc (Wc : list L5.range) :
  binv W BX Mc modelc LKc crc Ac ->
  ahpres L ar (BXa ++ LB) FF' spc SCRc Wc Mc M1 ->
  ri_inv HI (BX1 ++ LB) FF' LK1 cr1 A1 M1 (vml_of model1) -> amodel_ok A1 model1 -> model_rt modelc model1 -> incl Ac A1 -> incl LK1 LKc ->
  0 <= SCRc -> sp - SCR <= spc - SCRc ->
  (forall rr a, In rr Wc -> L5.in_rng rr a -> ~ ocell a /\ ~ (F / 8 + SB <= a < F / 8 + SB + B / 8)) ->
  (forall a, aclient L ar LB FF sp SCR a -> L5.outside W1 a -> L5.outside Wc a) ->
  (forall a, L5.outside W1 a -> L5.outside W a) ->
  binv W1 BX1 M1 model1 LK1 cr1 A1.
Proof.
  open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) AH HH1 AM1 RT1 IA1 ILK1 HS0 HS WAV WOUT WW.
  unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1.
  split. { intros x Hx. apply IA1. apply B4. exact Hx. } split. { intros x Hx. apply B5. apply ILK1. exact Hx. }
  split. { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ (BXa ++ LB) FF' Mc Mc M1 sp SCR spc SCRc Wc B1 B6 (mem_grows_refl Mc) AH).
           - exact HS.
           - clear - SPC; lia.
           - clear - SPC; lia. }
  split. { eapply ek_trans. { apply (ek_W L ar LB FF sp SCR W1 W M Mc B7). exact WW. }
           apply (ek_callee L ar LB BXa FF [(F, k, spc + 32)] sp SCR spc SCRc W1 Wc Mc M1 AH).
           - exact HS.
           - clear - SPC; lia.
           - exact WOUT. }
  split. { eapply dk_trans. exact B8. apply (dk_callee L ar LB BXa FF [(F, k, spc + 32)] sp SCR spc SCRc Wc Mc M1 AH).
           - exact HS.
           - clear - SPC; lia. }
  split. { apply (OWNAG Mc M1 B9). intros a Ha. pose proof (OCR a Ha) as OC. apply (proj1 AH). split. clear - OC SPC SLO; lia.
           split. apply stack_client. clear - OC SPC SLO SHI SPT; lia. clear - OC SPC HS0; lia.
           intros rr Hr X. exact (proj1 (WAV rr a Hr X) Ha). }
  intros i Hi. apply (proj2 (proj2 AH)).
  - clear - Hi FR F8. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
  - apply (fframe_shadow_client L ar (BXa ++ LB) FF' spc SCRc F k (spc + 32)). left; reflexivity. unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Hi. lia.
  - apply B10. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma vis_facts (G : gctx) W BX Mc modelc LKc crc Ac :
  binv W BX Mc modelc LKc crc Ac ->
  (L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) spc (sp - spc) /\ L5.img_clear (mrestrict (ahid Ac modelc) Mc) 1249280 1282048 /\
   L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) 1309752 2147450880 /\ L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) 1309760 1 /\
   L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) 1283280 1219844) /\
  own (mrestrict (ahid Ac modelc) Mc) /\
  (L5.defined (mrestrict (ahid Ac modelc) Mc) F B /\ L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) F B /\
   L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) (F / 8 + SB) (B / 8) /\ L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (F + B - 8) fl /\
   L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) fl 1) /\
  (cell_is RSEGS Mc (F + B - 8) 8 fl /\ avis (ahid Ac modelc) fl 1 /\ avis (ahid Ac modelc) F B /\ avis (ahid Ac modelc) spc (sp - spc) /\ avis (ahid Ac modelc) (F / 8 + SB) (B / 8)).
Proof.
  open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS8 & VIMG8 & VFS8 & _ & _ & VFSSH8 & _).
  pose proof (statics_vis (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (IMGC8 & CSB8 & CUAR8).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C Mc LY ST) as (_ & _ & _ & RMS & _).
  set (H8 := ahid Ac modelc) in *. set (MV8 := mrestrict H8 Mc) in *.
  assert (SV8 : avis H8 spc (sp - spc)). { apply (VIS8 spc (sp - spc)). clear - SPC SLO; lia. clear - SPC; lia. }
  assert (FV8 : avis H8 F B) by (apply (VFS8 F B FS1 FS2)).
  assert (SHV8 : avis H8 (F / 8 + SB) (B / 8)).
  { apply (VFSSH8 (F / 8 + SB) (B / 8)). intros i Hi. unfold in_shadow_of, S.
    pose proof (Z.div_le_mono (ar_fs ar) F 8 ltac:(clear; lia) FS1) as X1. pose proof (Z.div_le_mono (F + B - 1) (ar_fs ar + FS_BYTES - 1) 8 ltac:(clear; lia) ltac:(clear - FS2; lia)) as X2.
    destruct F8 as (_ & X3 & _). clear - Hi X1 X2 X3. lia. }
  assert (WSv : L5.writable RSEGS MV8 spc (sp - spc)).
  { apply (proj2 (writable_vis H8 Mc spc (sp - spc) SV8 ltac:(clear - SPC; lia) ltac:(clear - SPC; lia))).
    eapply (astk_writable ar Mc sp). exact B6. clear - SPC; lia. clear; lia. clear - SPC; lia. }
  assert (OWN8v : own MV8). { apply (OWNAG Mc MV8 B9). intros a Ha. pose proof (OCR a Ha) as OC. apply mrestrict_visible. replace a with (spc + (a - spc)) by (clear; lia). apply SV8. clear - OC SPC; lia. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & WF8 & _).
  assert (FDEF8 : L5.defined MV8 F B). { apply (proj2 (defined_vis H8 Mc F B FV8)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF8 _ (or_introl eq_refl))))))). }
  assert (FW8 : L5.writable RSEGS MV8 F B). { apply (L5C.writable_of_defined RSEGS). exact FDEF8. clear - FR; lia. clear - FR; lia. }
  assert (FSHW8 : L5.writable RSEGS MV8 (F / 8 + SB) (B / 8)).
  { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H8 Mc _ _ SHV8)). exact B10.
    clear - FR. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
    clear - FR F8. unfold SB. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H. lia. }
  pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ modelc F k _ _ fl HH2 B1 (or_introl eq_refl) (or_introl eq_refl) Hk FLC) as [FLC8 FL8].
  pose proof (fl_writable L ar C HI LY HIok _ FF' LKc _ Ac Mc _ fl B1 FLP) as [FLD8 FLW8].
  pose proof (fl_vis L ar C HI LY HIok _ FF' LKc _ Ac Mc modelc fl B1 FLP) as FLV8.
  assert (FLW8v : L5.writable RSEGS MV8 fl 1). { apply (proj2 (writable_vis H8 Mc fl 1 FLV8 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW8. }
  assert (RMSv : L5.u64_at RSEGS MV8 1283280 1219844). { apply (proj2 (u64_at_vis H8 Mc 1283280 1219844 (VIMG8 1283280 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))). exact RMS. }
  split. { split. exact WSv. split. exact IMGC8. split. exact CSB8. split. exact CUAR8. exact RMSv. }
  split. exact OWN8v.
  split. { split. exact FDEF8. split. exact FW8. split. exact FSHW8. split. exact FL8. exact FLW8v. }
  split. exact FLC8. split. exact FLV8. split. exact FV8. split. exact SV8. exact SHV8.
Qed.

(* [comment removed for export] *)
Definition Wret (a : Z) : Prop := (F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + B / 8) \/ a = fl.

Lemma retire_core (G : gctx) W BX Mc modelc LKc crc Ac (fx fx9 : FPState) Rc (pc : Z) R9 (r : Z) M9v (K : TSet) :
  binv W BX Mc modelc LKc crc Ac ->
  msteps RSEGS (st fx Rc pc (mrestrict (ahid Ac modelc) Mc)) (st fx9 R9 r M9v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wret a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 ->
  (forall (Mf : word -> option byte) (modelf : Model),
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wret a -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      ahpres L ar LB FF sp SCR W M Mf ->
      model_rt model modelf -> amodel_ok Ac modelf ->
      ri_inv HI (BX ++ LB) FF LKc crc Ac Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fx9) R9 r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros BI wMS MG9 wFZ wFL0 KF.
  destruct (vis_facts G W BX Mc modelc LKc crc Ac BI) as (_ & _ & _ & (FLC8 & FLV8 & _)).
  pose proof G as G'. open_gctx G'. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (FLNC8 : ~ aclient L ar (BX ++ LB) FF' 0 0 fl).
  { apply (not_client_bx L ar FF' fl BX LB). apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LB B1 eq_refl). exact FLP. exact FLBIG. exact FLNC. }
  apply (apiece_retire L ar C HI LY HIok (BX ++ LB) FF LKc crc Ac Mc modelc fx fx9 Rc pc R9 r M9v Wret F k (spc + 32) fl K B1 B2).
  { exact FLC8. }
  { exact FLNC8. }
  { exact FLV8. }
  { clear - FLR; lia. }
  { exact wMS. }
  { exact MG9. }
  { exact wFZ. }
  { intros a Ha Wa. unfold Wret in Wa. destruct Wa as [[Wa|Wa]|Wa].
    - right. apply (fframe_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity. clear - Wa FR; lia.
    - right. apply (fframe_shadow_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Wa. unfold SB in *. lia.
    - left; exact Wa. }
  { intros a. unfold Wret. repeat match goal with X : _ |- _ => clear X end.
    destruct (rng_dec a F (F + 8)); [left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + ff_bytes k / 8)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto. }
  { exact wFL0. }
  intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
  assert (ASTK9 : astk ar M9 sp SCR). { eapply astk_grows. exact B6. exact MGM9. }
  apply (KF M9 model9).
  - exact FRM9.
  - apply ahpres_of.
    + eapply ek_trans. exact B7.
      intros a (Ha & Hc & Ho). apply FRM9. exact Ha. unfold Wret. intros [[X|X]|X].
      * apply (NCF a). left; clear - X FR; lia. exact Hc.
      * apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - X. unfold SB in X |- *. lia. exact Hc.
      * subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
    + eapply astk_defined. exact ASTK9. clear - SPC; lia. clear; lia.
    + eapply dk_trans. exact B8. apply dk_grows. exact MGM9.
  - eapply L5LZ.model_rt_trans. exact B3. exact RT9.
  - exact AM9.
  - exact HH9.
Qed.
End CTX.
End WithIface.
End SCFG_1.
End L5AFKR.
