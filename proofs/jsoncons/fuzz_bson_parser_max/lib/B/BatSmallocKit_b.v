(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b
     BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatWrapC_b BatWrapVis_b BatWrapC2_b BatIfaceFrame_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_rdn_none_img : forall (M : word -> option byte) a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, a <= U x < a + Z.of_nat n -> M x = None) -> rdn ASEGS M (Z_to_bv 64 a) n = rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros M a n Ha Hn N. destruct n as [|n]; [reflexivity|]. apply rdn_ext.
  - rewrite art_u_lit by lia. lia.
  - intros x Hx. rewrite art_u_lit in Hx by lia. apply N. exact Hx.
Qed.
Lemma art_desc_md : rdn ASEGS (fun _ => None) (Z_to_bv 64 0x1382b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)).
Proof. vm_compute. first [reflexivity | f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity]. Qed.
Lemma art_desc_off : rdn ASEGS (fun _ => None) (Z_to_bv 64 (0x1382b8 + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 64 - 2048))).
Proof. vm_compute. first [reflexivity | f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity]. Qed.

Section Kit.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).

#[using="Type"] Lemma art_zone_off_fs_shadow : forall (G : art_gs art_fsg) LB A (M Mr : word -> option byte) model x,
  art_alloc_rep art_fsg rn G LB Mr -> art_kn_ok MAPS0 RESV0 rn -> BI (g_log art_fsg G) A M model -> art_alloc_zone art_fsg rn G x ->
  ~ (HeapIfaceA.S (ar_fs (rn_ar rn)) <= x < HeapIfaceA.S (ar_fs (rn_ar rn) + FS_BYTES)).
Proof.
  intros G LB A M Mr model x REP KN B0 Z X. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  destruct Fapp as (Fa0 & Fap & Fa47). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
  assert (SR : 0x7fff8000 <= x < 0x10007fff8000).
  { pose proof (art_S_lo (ar_fs (rn_ar rn)) Fa0). assert ((ar_fs (rn_ar rn) + FS_BYTES) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - X H H0. lia. }
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. unfold apart, FS_BYTES in *.
  destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
  - unfold art_zone_statics in Z. clear - Z SR. lia.
  - unfold art_zone_thread in Z. clear - Z SR G10. lia.
  - clear - Z SR G16. lia.
  - unfold art_zone_kspace in Z. clear - Z SR Khi. lia.
  - destruct Z as [Z | (p & Hp & Z)]; [clear - Z SR Papp; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & _). clear - Z SR L4. lia.
  - unfold art_zone_depot, dprivD in Z. clear - Z SR Al2s Abs. lia.
  - destruct Z as [Z | (p & Hp & Z)].
    + destruct Afkb as [AF | AF].
      * pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
      * pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
    + destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & L5).
      specialize (L5 (ar_fs (rn_ar rn), 11571200) ltac:(unfold art_objs; do 6 right; left; reflexivity)). unfold apart in L5. cbn [fst snd] in L5.
      destruct L5 as [AF | AF].
      * pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
      * pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
  - clear - Z SR. lia.
  - clear - Z SR G20. lia.
  - clear - Z SR G22 Hkey. lia.
  - clear - Z SR. lia.
  - clear - Z SR. lia.
Qed.
End Kit.
