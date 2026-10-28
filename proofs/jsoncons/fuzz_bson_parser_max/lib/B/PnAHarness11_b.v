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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAHarnessKit3_b PnAHarnessP4_b Ba0_code_a83e4_a83e8_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA11.
Import L5A. Import L5CA. Import L5SAR. Import PNHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
          (V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
(* [comment removed for export] *)
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis RA : L5.ra_ok (U R 1).
Hypothesis G2R : getr R (reg 2) = Z_to_bv 64 (V2 + cls).
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PNHAK2.wapart_nil | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil])]])
  | (apply PNHAK2.wapart_nil) | lia ].

(* [comment removed for export] *)
Lemma harness_tail (SF : HAJ.astack_free_spec L ar SCFG HI 0x5e2e8 16 5) (fx : FPState) Rc Mc modelc BX LKc crc Ac (K : TSet) (g : PNST.st) :
  Bv W BX Mc modelc LKc crc Ac -> rinvH R Rc V2 cls F -> K [] -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g Mc ->
  getr Rc (reg 21) = Z_to_bv 64 18446744073709551608 -> getr Rc (reg 22) = Z_to_bv 64 1266024 ->
  getr Rc (reg 23) = Z_to_bv 64 (F + 1024) -> getr Rc (reg 26) = Z_to_bv 64 18446744073709551608 ->
  (forall (fxf : FPState) Rf Mf modelf,
      regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g Mf ->
      ahpres L ar LB FF (V2 + cls) 36864 W M Mf ->
      model_rt model modelf -> amodel_ok Ac modelf ->
      ri_inv HI (BX ++ LB) FF LKc crc Ac Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (@L5A.cfg fxf Rf (U R 1) Mf modelf) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx Rc 0xa8778 Mc modelc) K.
Proof.
  intros BI RI K0 LS X21 X22 X23 X26 KF.
  pose proof G as G'. destruct G' as [HkG SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  destruct (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W BX Mc modelc LKc crc Ac BI)
    as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & (FLC8 & FLV8 & FV8 & SPV8 & FSV8)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *. replace (F + 2048 - 8) with (F + 2040) in FLCv by lia.
  set (H := ahid Ac modelc) in *. set (MV := mrestrict H Mc) in *.
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV (V2 - 128) 128) by (eapply L5.writable_sub; [exact WSv| clear; lia| clear - CLS; lia]).
  unfold HeapIfaceA.SB in FSHWv.
  assert (SHW : BIGSHADOW_HI <= V2 + cls - 36864) by (unfold BIGSHADOW_HI; clear - V2R CLS; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  LeanFeed.pfeed P (PNAHP4.bhaO_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact FDEFv | exact FWv | exact FSHWv | exact FLWv | exact Q5 | exact FLCv | (unfold PNAHP4.aligned; exact V2A) ]).
  destruct P as (fx1 & R1 & M1v & MG1 & oFR & oFZ & (oMS & oKS & oR1 & oR10 & oR11 & oQ)). clear oQ.
  set (WO := fun a => F <= a < F + 8 \/ F / 8 + 2147450884 <= a < F / 8 + 2147450884 + 3).
  apply (apiece L ar C HI LYa HIok _ FF' LKc crc Ac Mc modelc fx fx1 Rc 0xa8778 R1 0x5e2e8 M1v WO K B1 B2 oMS MG1).
  { intros a Ha Hna. apply oFZ; [exact Ha|..]; intros X0; apply Hna; subst WO; cbn beta; clear - X0; lia. }
  { intros a Ha Wa. subst WO; cbn beta in Wa. split.
    - destruct Wa as [Wa|Wa].
      + apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      + apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
        unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (BI1 : Bv W BX M1 model1 LKc crc Ac).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W BX Mc modelc LKc crc Ac M1 model1 WO BI HH1 AM1 MRT1 MGM1 FR1).
    intros a Wa. subst WO; cbn beta in Wa. right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
  pose proof BI1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (RI1 : rinvH R R1 V2 cls F) by (apply (rinvH_ks R Rc R1 V2 cls F PNAHP4.KS_bhaO RI oKS); vm_compute; reflexivity).
  pose proof RI1 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (LS1 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M1).
  { apply (PNHAK.ls_piece _ Mc M1 WO FR1); [| exact LS]. intros a Wa. subst WO; cbn beta in Wa. unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  (* [comment removed for export] *)
  assert (U2 : bv_unsigned (getr R1 2%bv) = V2 - 128). { rewrite L5K.rl2, Y2. apply L5.unsigned_lit. clear - V2R; lia. }
  unfold HAJ.astack_free_spec in SF. rewrite (aly_segs L C LYa) in SF.
  apply (SF fx1 R1 M1 model1 (BX ++ LB) FF' LKc crc Ac K F (V2 - 128 + 32) C1 (proj1 C2) (proj2 C2)); clear SF.
  { left; reflexivity. }
  { rewrite L5K.rl10. exact oR10. }
  { rewrite L5K.rl4, Y4. exact TP. }
  { rewrite L5K.rl1, oR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
  { rewrite U2. replace (V2 - 128) with (V2 + cls - (cls + 128)) by (clear; lia).
    apply (astack_ok_of_astk L ar C LYa Mc M1 (V2 + cls) 36864 (cls + 128) 16 B6 MGM1); [clear - CLS; lia| clear; lia| clear - CLS; lia|].
    replace (V2 + cls - (cls + 128)) with (V2 - 128) by (clear; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  { exact K0. }
  intros R' M' model' RP' _ AG' SDEF' MRT' MI' HH'.
  rewrite U2 in AG', SDEF'. rewrite L5K.rl1, oR1.
  cbn [ff_remove ff_addr fst snd] in HH'. rewrite Z.eqb_refl in HH'.
  change (ff_bytes 5) with 2048 in AG'.
  change (srealizes RSEGS SCFG (@L5A.cfg fx1 R' 0xa87a0 M' model') K).
  assert (AM' : amodel_ok Ac model'). { split; [| exact MI']. rewrite (L5LZ.model_rt_halted _ _ MRT'). exact (proj1 C2). }
  (* [comment removed for export] *)
  assert (NSH : forall a, V2 + cls - 36864 <= a -> ~ in_shadow_of F 2048 a).
  { intros a Ha X. unfold in_shadow_of in X. pose proof (PMKA.S_in_shadow (F + 2048 - 1) ltac:(clear - FR; lia)) as SX. clear - Ha X SX SHW. lia. }
  (* [comment removed for export] *)
  assert (ACL : forall a, aclient L ar LB FF (V2 + cls) 36864 a -> aclient L ar (BX ++ LB) FF' (V2 - 128) 16 a).
  { intros a Hc. apply aclient_appb. apply aclient_cons. apply (aclient_mono L ar LB FF (V2 + cls) 36864 (V2 - 128) 16 a Hc). clear - CLS; lia. }
  assert (AGc : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (V2 + cls) 36864 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (AG' a Ha (ACL a Hc)). intros X. apply (NCF a); [| exact Hc]. right. unfold in_shadow_of in X. exact X. }
  assert (AGstk : forall a, V2 - 128 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply AG'; [clear - Ha V2R; lia| apply stack_client; [clear - Ha SLO SPT CLS; lia| clear - Ha; lia]| apply NSH; clear - Ha CLS; lia]. }
  assert (ASTK' : astk ar M' (V2 + cls) 36864).
  { destruct C6 as (A16 & SLO1 & SHI1 & SPT1 & DSCR & DUP).
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
    assert (D : forall x, (V2 + cls - 36864 <= x < V2 + cls \/ V2 + cls <= x < ar_stack_top ar) -> M' (Z_to_bv 64 x) <> None).
    { intros x Hx. destruct (rng_dec x (V2 - 128 - 16) (V2 - 128)) as [I|O].
      - apply SDEF'. exact I.
      - rewrite AG'; [| clear - Hx TOP V2R V2S CLS; lia| apply stack_client; [clear - Hx SLO1 TOP V2S CLS; lia| exact O]| apply NSH; clear - Hx; lia].
        destruct (Z_lt_le_dec x (V2 + cls)).
        + replace x with (V2 + cls - 36864 + (x - (V2 + cls - 36864))) by (clear; lia). apply DSCR. clear - Hx l; lia.
        + replace x with (V2 + cls + (x - (V2 + cls))) by (clear; lia). apply DUP. clear - Hx l; lia. }
    split. exact A16. split. exact SLO1. split. exact SHI1. split. exact SPT1. split.
    - intros j Hj. apply D. clear - Hj; lia.
    - intros j Hj. apply D. clear - Hj; lia. }
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M').
  { apply (PNHAK.ls_agree g M1 M'); [| exact LS1]. intros a Ha X. apply (AG' a Ha).
    - exact (PNHAK.stat_client L C LY ar (BX ++ LB) FF' (V2 - 128) 16 a (fun x X0 => X0) X).
    - intros Y. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in Y. pose proof (PNHAK.statc_range a X) as SR. clear - Y SR FR. lia. }
  pose proof (vis_pack L ar C HI LYa HIok _ _ LKc crc Ac M' model' HH') as (HOFF' & VIS' & _).
  set (H' := ahid Ac model') in *. set (MV' := mrestrict H' M') in *.
  assert (SV' : avis H' (V2 - 128) (128 + cls)). { apply (VIS' (V2 - 128) (128 + cls)). clear - SLO CLS; lia. clear - V2R V2S CLS; lia. }
  assert (AGv : forall a, V2 - 128 <= a < V2 + cls -> MV' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. unfold MV'. rewrite (mrestrict_visible H' M'). 2:{ replace a with ((V2 - 128) + (a - (V2 - 128))) by (clear; lia). apply SV'. clear - Ha; lia. }
    apply AGstk. clear - Ha V2S; lia. }
  assert (OWN' : tfrk (V2 + cls) R MV').
  { apply (tfrk_agree (V2 + cls) R M1 MV'); [clear - V2R CLS; lia| clear - V2S; lia| exact C9|]. intros a Ha. unfold tocell in Ha. apply AGv. clear - Ha CLS; lia. }
  pose proof OWN' as (T1 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26).
  assert (WS' : L5.writable RSEGS MV' (V2 - 128) (128 + cls)).
  { apply (proj2 (writable_vis H' M' (V2 - 128) (128 + cls) SV' ltac:(clear - V2R; lia) ltac:(clear - V2R V2S CLS; lia))).
    apply (astk_writable ar M' (V2 + cls) 36864); [exact ASTK'| clear - CLS; lia| clear; lia| clear - CLS; lia]. }
  (* [comment removed for export] *)
  assert (Z2 : getr R' (reg 2) = Z_to_bv 64 (V2 - 128)) by (rewrite (cs_of_preserved R1 R' 2 RP') by inl; exact Y2).
  assert (Z8 : getr R' (reg 8) = Z_to_bv 64 (V2 + cls)) by (rewrite (cs_of_preserved R1 R' 8 RP') by inl; exact Y8).
  assert (Z9 : getr R' (reg 9) = Z_to_bv 64 (V2 - 128)) by (rewrite (cs_of_preserved R1 R' 9 RP') by inl; exact Y9).
  assert (Z18 : getr R' (reg 18) = Z_to_bv 64 F) by (rewrite (cs_of_preserved R1 R' 18 RP') by inl; exact Y18).
  assert (Z19 : getr R' (reg 19) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (cs_of_preserved R1 R' 19 RP') by inl; exact Y19).
  assert (Z20 : getr R' (reg 20) = Z_to_bv 64 (F + 32)) by (rewrite (cs_of_preserved R1 R' 20 RP') by inl; exact Y20).
  assert (Z21 : getr R' (reg 21) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R1 R' 21 RP') by inl; rewrite (oKS 21%nat) by inl; exact X21).
  assert (Z22 : getr R' (reg 22) = Z_to_bv 64 1266024) by (rewrite (cs_of_preserved R1 R' 22 RP') by inl; rewrite (oKS 22%nat) by inl; exact X22).
  assert (Z23 : getr R' (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R1 R' 23 RP') by inl; rewrite (oKS 23%nat) by inl; exact X23).
  assert (Z24 : getr R' (reg 24) = Z_to_bv 64 F) by (rewrite (cs_of_preserved R1 R' 24 RP') by inl; exact Y24).
  assert (Z25 : getr R' (reg 25) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R1 R' 25 RP') by inl; exact Y25).
  assert (Z26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R1 R' 26 RP') by inl; rewrite (oKS 26%nat) by inl; exact X26).
  assert (Z3 : getr R' (reg 3) = getr R (reg 3)) by (rewrite (cs_of_preserved R1 R' 3 RP') by inl; exact Y3).
  assert (Z4 : getr R' (reg 4) = getr R (reg 4)) by (rewrite (cs_of_preserved R1 R' 4 RP') by inl; exact Y4).
  assert (Z27 : getr R' (reg 27) = getr R (reg 27)) by (rewrite (cs_of_preserved R1 R' 27 RP') by inl; exact Y27).
  (* [comment removed for export] *)
  assert (V0R : forall k, 0 <= U R k < 2 ^ 64) by (intros k; apply UR).
  assert (EPI : exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx1 R' 0xa87a0 MV') (st fx9 R9 (U R 1) M9v) /\ mem_grows MV' M9v
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ False -> M9v (Z_to_bv 64 a) = MV' (Z_to_bv 64 a))
      /\ getr R9 (reg 2) = Z_to_bv 64 (V2 + cls) /\ getr R9 (reg 10) = Z_to_bv 64 0
      /\ (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R9 (reg k) = Z_to_bv 64 (U R k))
      /\ (forall k, In k [3; 4; 27]%nat -> getr R9 (reg k) = getr R' (reg k))).
  { destruct CLS as [E0|E0].
    - idtac. rewrite E0, Z.add_0_r in Z8, WS'. rewrite E0, Z.add_0_r in T1, T8, T9, T18, T19, T20, T21, T22, T23, T24, T25, T26.
      LeanFeed.pfeed P (PNAHP4.bhaR0_conc fx1 R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl
                    | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                    | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | exact WS' | (unfold PNAHP4.aligned; exact V2A)
                         | (match goal with Hx : L5.u64_at RSEGS MV' ?a ?v |- L5.u64_at RSEGS MV' ?b ?v => replace b with a by (clear; lia); exact Hx end) ]).
      destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26)).
      exists fx9, R9, M9v. split.
      { eapply msteps_trans; [exact eMS|]. apply (ret_to fx9 R9 M9v 0xa87ec W_a83e4 (U R 1) F_a83e4 eq_refl D_a83e4 eR1 (proj1 RA) (proj2 RA)). }
      split; [exact MG9|]. split; [intros a Ha _; apply eFZ; exact Ha|]. split; [rewrite E0, Z.add_0_r; exact eR2|]. split; [exact eR10|]. split.
      + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
      + intros k Hk. apply eKS. revert k Hk. apply (L5K.incl_b [3; 4; 27]%nat PNAHP4.KS_bhaR0). vm_compute; reflexivity.
    - idtac. rewrite E0 in Z8, WS'. rewrite E0 in T1, T8, T9, T18, T19, T20, T21, T22, T23, T24, T25, T26.
      LeanFeed.pfeed P (PNAHP4.bhaR16_conc fx1 R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl
                    | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                    | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - V2R V2S E0; lia) | (clear - FR; lia) | exact WS' | (unfold PNAHP4.aligned; exact V2A)
                         | (match goal with Hx : L5.u64_at RSEGS MV' ?a ?v |- L5.u64_at RSEGS MV' ?b ?v => replace b with a by (clear; lia); exact Hx end) ]).
      destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26)).
      exists fx9, R9, M9v. split.
      { eapply msteps_trans; [exact eMS|]. apply (ret_to fx9 R9 M9v 0xa87ec W_a83e4 (U R 1) F_a83e4 eq_refl D_a83e4 eR1 (proj1 RA) (proj2 RA)). }
      split; [exact MG9|]. split; [intros a Ha _; apply eFZ; exact Ha|]. split; [rewrite E0; exact eR2|]. split; [exact eR10|]. split.
      + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
      + intros k Hk. apply eKS. revert k Hk. apply (L5K.incl_b [3; 4; 27]%nat PNAHP4.KS_bhaR16). vm_compute; reflexivity. }
  destruct EPI as (fx9 & R9 & M9v & eMS & MG9 & eFZ & eR2 & eR10 & eRS & eRK).
  apply (apiece L ar C HI LYa HIok _ FF LKc crc Ac M' model' fx1 fx9 R' 0xa87a0 R9 (U R 1) M9v (fun _ => False) K HH' AM' eMS MG9).
  { exact eFZ. }
  { intros a Ha []. }
  intros Mf modelf HHf AMf MRTf HIDf VISf MGMf FRf VVf.
  assert (EQf : forall a, 0 <= a < 2 ^ 64 -> Mf (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) by (intros a Ha; apply FRf; [exact Ha| intros []]).
  apply (KF fx9 R9 Mf modelf).
  - apply preserved_by_index. intros j Hj. unfold cs_all in Hj. cbn [In] in Hj.
    destruct Hj as [<-|Hj]. { rewrite eR2. symmetry. exact G2R. }
    destruct Hj as [<-|Hj]. { rewrite (eRK 3%nat) by inl. exact Z3. }
    destruct Hj as [<-|Hj]. { rewrite (eRK 4%nat) by inl. exact Z4. }
    do 11 (destruct Hj as [<-|Hj]; [rewrite eRS by inl; symmetry; apply U_to|]).
    destruct Hj as [<-|[]]. rewrite (eRK 27%nat) by inl. exact Z27.
  - exact eR10.
  - apply (PNHAK.ls_agree g M' Mf); [| exact LS']. intros a Ha _. apply EQf. exact Ha.
  - apply ahpres_of.
    + eapply ek_trans. exact B7. eapply ek_trans.
      { apply (ek_piece L ar LB FF (V2 + cls) 36864 W Mc M1 WO FR1). intros a Ha Hc _ X0. subst WO; cbn beta in X0. destruct X0 as [X0|X0].
        * apply (NCF a). left; clear - X0; lia. exact Hc.
        * apply (NCF a). right. unfold HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB in X0 |- *. clear - X0. lia. exact Hc. }
      eapply ek_trans.
      { intros a (Ha & Hc & _). apply AGc. exact Ha. exact Hc. }
      intros a (Ha & _ & _). apply EQf. exact Ha.
    + apply (astk_defined ar Mf (V2 + cls) 36864); [| clear; lia| clear; lia]. eapply astk_grows. exact ASTK'. exact MGMf.
    + eapply dk_trans. exact B8. eapply dk_trans. apply dk_grows. exact MGM1. eapply dk_trans; [| apply dk_grows; exact MGMf].
      intros a Ha Hc D. rewrite AGc. exact D. exact Ha. exact Hc.
  - eapply L5LZ.model_rt_trans. exact B3. eapply L5LZ.model_rt_trans. exact MRT1. eapply L5LZ.model_rt_trans. exact MRT'. exact MRTf.
  - exact AMf.
  - exact HHf.
Qed.
End Stage.
End SCFG_1.
End PNHA11.
