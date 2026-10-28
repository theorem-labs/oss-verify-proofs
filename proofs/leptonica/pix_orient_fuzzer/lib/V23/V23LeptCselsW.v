(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptExecB LeptRecs LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptCloseSpec V23LeptCloseIface V23LeptCselsSpec V23LeptCselsA V23LeptCselsC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCloseIface O23LeptCselsSpec O23LeptCselsA.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CselsWrap.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma csels_finish : forall (fr : bvmap 5 word) C A m md regs (s size dir : Z) (ret : word) (S : TSet) (kR bR : Z)
    (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (sel1 arr1 sel2 arr2 : Z) (rows1 rows2 : list Z) (tab1 tab2 : list (list Z))
    (sy1 sx1 cy1 cx1 sy2 sx2 cy2 cx2 : Z),
  Cok C ->
  (forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (sel1 sel2 : Z) (sv1 sv2 : selv) (c1 c2 : Z -> Z -> Z),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10%bv = Z_to_bv 64 0 ->
     sub_live A A' -> POSTM C A (s + 48) m m' ->
     rdn SEGS m' (Z_to_bv 64 (s + O23LeptCselsSpec.csels_k1 size)) 8 = Some (Z_to_le_bytes 8 sel1) ->
     rdn SEGS m' (Z_to_bv 64 (s + O23LeptCselsSpec.csels_k2 size)) 8 = Some (Z_to_le_bytes 8 sel2) ->
     (forall a : word, s <= u a < s + 48 -> ~ (s + O23LeptCselsSpec.csels_k1 size <= u a < s + O23LeptCselsSpec.csels_k1 size + 8) ->
                       ~ (s + O23LeptCselsSpec.csels_k2 size <= u a < s + O23LeptCselsSpec.csels_k2 size + 8) -> m' a = m a) ->
     sel_at (alloc_top (c_vm C)) A' m' sel1 sv1 -> sel_at (alloc_top (c_vm C)) A' m' sel2 sv2 ->
     sel_cont m' sv1 c1 -> sel_cont m' sv2 c2 -> v_name sv1 = 0 -> v_name sv2 = 0 -> O23LeptCloseIface.csels_shape size dir sv1 sv2 ->
     (forall p, sel_blk sel1 sv1 p \/ sel_blk sel2 sv2 p -> live A (Z_to_bv 64 p) = None /\ live (c_A0 C) (Z_to_bv 64 p) = None) ->
     (forall p q, sel_blk sel1 sv1 p -> sel_blk sel2 sv2 q -> p <> q) ->
     (forall q : word, (forall p, sel_blk sel1 sv1 p \/ sel_blk sel2 sv2 p -> q <> Z_to_bv 64 p) -> live A' q = live A q) ->
     aroom A' vm' (kR - O23LeptCloseIface.csels_K size) (bR - O23LeptCloseIface.csels_K size * 2 ^ 17) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
  W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10%bv = Z_to_bv 64 0 ->
  sub_live A A' -> POSTM C A (s + 48) m m' -> O23LeptCselsA.cs_fra (s + 48) (O23LeptCselsSpec.csels_k1 size - 48) (O23LeptCselsSpec.csels_k2 size - 48) m m' ->
  aroom A' vm' (kR - O23LeptCloseIface.csels_K size) (bR - O23LeptCloseIface.csels_K size * 2 ^ 17) ->
  cs_cell m' (s + 48 + (O23LeptCselsSpec.csels_k1 size - 48), 8%nat, sel1) -> cs_cell m' (s + 48 + (O23LeptCselsSpec.csels_k2 size - 48), 8%nat, sel2) ->
  cs_sel_facts C A A' m' sel1 arr1 sy1 sx1 cy1 cx1 rows1 tab1 ->
  cs_sel_facts C A A' m' sel2 arr2 sy2 sx2 cy2 cx2 rows2 tab2 ->
  List.NoDup (O23LeptCselsA.cs_words sel1 arr1 rows1 ++ O23LeptCselsA.cs_words sel2 arr2 rows2) ->
  (forall q : word, ~ In q (O23LeptCselsA.cs_words sel1 arr1 rows1 ++ O23LeptCselsA.cs_words sel2 arr2 rows2) -> live A' q = live A q) ->
  Z.of_nat (length rows1) = sy1 -> 1 <= sy1 <= 10000 -> 1 <= sx1 <= 10000 -> 0 <= cy1 < 2 ^ 32 -> 0 <= cx1 < 2 ^ 32 -> O23LeptCselsA.cs_tab_ok sx1 tab1 = true ->
  Z.of_nat (length rows2) = sy2 -> 1 <= sy2 <= 10000 -> 1 <= sx2 <= 10000 -> 0 <= cy2 < 2 ^ 32 -> 0 <= cx2 < 2 ^ 32 -> O23LeptCselsA.cs_tab_ok sx2 tab2 = true ->
  O23LeptCloseIface.csels_shape size dir (O23LeptCselsA.cs_sv sy1 sx1 cy1 cx1 arr1 rows1) (O23LeptCselsA.cs_sv sy2 sx2 cy2 cx2 arr2 rows2) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S.
Proof.
  intros fr C A m md regs s size dir ret S kR bR fr' cs' A' m' vm' regs' sel1 arr1 sel2 arr2 rows1 rows2 tab1 tab2
    sy1 sx1 cy1 cx1 sy2 sx2 cy2 cx2 HC HK Hz Hfs HW Hkept H10 Hsub Hpost Hfra Hroom C1 C2 F1 F2 ND Hlive
    Hl1 Hsy1 Hsx1 Hcy1 Hcx1 Ht1 Hl2 Hsy2 Hsx2 Hcy2 Hcx2 Ht2 Hshape.
  pose proof (mkFP fr' cs') as fxl.
  pose proof (O23LeptCselsA.cs_nodup_app_l _ _ _ ND) as ND1. pose proof (O23LeptCselsA.cs_nodup_app_r _ _ _ ND) as ND2.
  destruct (cs_sel_of C A A' m' (with_vmmaps vm' md) sel1 arr1 sy1 sx1 cy1 cx1 rows1 tab1 HC HW F1 ND1 Hl1 Hsy1 Hsx1 Hcy1 Hcx1 Ht1)
    as (SA1 & SC1 & SB1 & SQ1).
  destruct (cs_sel_of C A A' m' (with_vmmaps vm' md) sel2 arr2 sy2 sx2 cy2 cx2 rows2 tab2 HC HW F2 ND2 Hl2 Hsy2 Hsx2 Hcy2 Hcx2 Ht2)
    as (SA2 & SC2 & SB2 & SQ2).
  unfold cs_cell in C1, C2. cbn [fst snd] in C1, C2.
  apply (HK fr' cs' A' m' vm' regs' sel1 sel2 (O23LeptCselsA.cs_sv sy1 sx1 cy1 cx1 arr1 rows1) (O23LeptCselsA.cs_sv sy2 sx2 cy2 cx2 arr2 rows2)
           (O23LeptCselsA.cs_tab tab1) (O23LeptCselsA.cs_tab tab2) Hz Hfs HW Hkept H10 Hsub Hpost).
  - replace (s + O23LeptCselsSpec.csels_k1 size) with (s + 48 + (O23LeptCselsSpec.csels_k1 size - 48)) by lia. exact C1.
  - replace (s + O23LeptCselsSpec.csels_k2 size) with (s + 48 + (O23LeptCselsSpec.csels_k2 size - 48)) by lia. exact C2.
  - intros a Ha N1 N2. unfold O23LeptCselsA.cs_fra in Hfra.
    apply Hfra; [lia | intros X; apply N1; lia | intros X; apply N2; lia].
  - exact SA1.
  - exact SA2.
  - exact SC1.
  - exact SC2.
  - reflexivity.
  - reflexivity.
  - exact Hshape.
  - intros p [Hp | Hp].
    + destruct (SB1 p Hp) as (_ & L1 & L2). split; assumption.
    + destruct (SB2 p Hp) as (_ & L1 & L2). split; assumption.
  - intros p q Hp Hq E. subst q.
    destruct (SB1 p Hp) as (I1 & _). destruct (SB2 p Hq) as (I2 & _).
    exact (O23LeptCselsA.cs_nodup_app_disj _ _ _ _ ND I1 I2).
  - intros q Hq. apply Hlive. intros Hin. apply in_app_or in Hin as [Hin | Hin].
    + destruct (SQ1 q Hin) as (p & Hp & ->). exact (Hq p (or_introl Hp) eq_refl).
    + destruct (SQ2 q Hin) as (p & Hp & ->). exact (Hq p (or_intror Hp) eq_refl).
  - exact Hroom.
Qed.

Theorem selectComposableSels_lit_W : selectComposableSels_lit_contract.
Proof.
  unfold selectComposableSels_lit_contract.
  intros fr cs C A m md regs s size dir ret S HC HW Hz Hsp Hal Hlo Hhi Hra Hret Htp H10 H11 H12 H13 Hcase kR bR Hroom HkR HbR HK.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    let n := eval vm_compute in (bv_unsigned pc) in
    replace pc with (Z_to_bv 64 n) by (apply bv_eq; reflexivity) end.
  assert (Hal' : (s + 48) mod 16 = 0) by (replace (s + 48) with (s + 3 * 16) by lia; rewrite Z_mod_plus_full; exact Hal).
  assert (Hwin : c_top C - LSTK + CSELS_WIN <= s + 48) by (unfold CSELS_WIN; unfold CSELS_STACK in Hlo; lia).
  destruct Hcase as [[-> ->] | [-> ->]].
  - change (O23LeptCselsSpec.csels_k1 8) with 16 in H12. change (O23LeptCselsSpec.csels_k2 8) with 8 in H13.
    change (O23LeptCloseIface.csels_K 8) with 16 in HkR, HbR.
    assert (Hsp' : getr regs 2 = Z_to_bv 64 (s + 48 + -48)) by (rewrite Hsp; f_equal; lia).
    assert (H12' : getr regs 12 = Z_to_bv 64 (s + 48 + -32)) by (rewrite H12; f_equal; lia).
    assert (H13' : getr regs 13 = Z_to_bv 64 (s + 48 + -40)) by (rewrite H13; f_equal; lia).
    apply (csels_chain8 (mkFP fr cs) C A m md regs (s + 48) ret S HC HW Hz Hsp' Hal' Hwin Hhi Hra Hret Htp H10 H11 H12' H13'
             kR bR Hroom HkR HbR).
    intros fr' cs' A' m' vm' regs' sel1 arr1 r1_0 r1_1 r1_2 r1_3 sel2 arr2 r2_0 r2_1 r2_2 r2_3 r2_4 r2_5 r2_6 r2_7
      Kz Kfs KW Kk K10 Ksub Kpost Kfra Kroom Kc1 Kc2 KF1 KF2 KND Klive.
    apply (csels_finish fr C A m md regs s 8 2 ret S kR bR fr' cs' A' m' vm' regs' sel1 arr1 sel2 arr2 _ _ _ _ 4 1 2 0 8 1 4 0
             HC HK Kz Kfs KW Kk K10 Ksub Kpost Kfra Kroom Kc1 Kc2 KF1 KF2 KND Klive);
      [reflexivity | lia | lia | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | reflexivity |].
    unfold O23LeptCloseIface.csels_shape. left. unfold O23LeptCselsA.cs_sv. cbn [v_sy v_sx v_cy v_cx]. repeat split.
  - change (O23LeptCselsSpec.csels_k1 30) with 32 in H12. change (O23LeptCselsSpec.csels_k2 30) with 24 in H13.
    change (O23LeptCloseIface.csels_K 30) with 6 in HkR, HbR.
    assert (Hsp' : getr regs 2 = Z_to_bv 64 (s + 48 + -48)) by (rewrite Hsp; f_equal; lia).
    assert (H12' : getr regs 12 = Z_to_bv 64 (s + 48 + -16)) by (rewrite H12; f_equal; lia).
    assert (H13' : getr regs 13 = Z_to_bv 64 (s + 48 + -24)) by (rewrite H13; f_equal; lia).
    apply (csels_chain30 (mkFP fr cs) C A m md regs (s + 48) ret S HC HW Hz Hsp' Hal' Hwin Hhi Hra Hret Htp H10 H11 H12' H13'
             kR bR Hroom HkR HbR).
    intros fr' cs' A' m' vm' regs' sel1 arr1 r1_0 sel2 arr2 r2_0
      Kz Kfs KW Kk K10 Ksub Kpost Kfra Kroom Kc1 Kc2 KF1 KF2 KND Klive.
    apply (csels_finish fr C A m md regs s 30 1 ret S kR bR fr' cs' A' m' vm' regs' sel1 arr1 sel2 arr2 _ _ _ _ 1 6 0 3 1 30 0 15
             HC HK Kz Kfs KW Kk K10 Ksub Kpost Kfra Kroom Kc1 Kc2 KF1 KF2 KND Klive);
      [reflexivity | lia | lia | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | reflexivity |].
    unfold O23LeptCloseIface.csels_shape. right. unfold O23LeptCselsA.cs_sv. cbn [v_sy v_sx v_cy v_cx]. repeat split.
Qed.

End CselsWrap.
