(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5 PmRefRead_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopKitX_u5 ChunkKit_u5.
Import ListNotations. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TKW.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w_add1 : forall a, 0 <= a -> a + 1 < 2 ^ 64 -> (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a H0 H1. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (bv_unsigned (1%bv : bv 64)) with 1 by reflexivity. rewrite (Z.mod_small a) by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rdn_bytes_at : forall (M : mem) (t : list Z) a, L5.bytes_at RSEGS M a t -> 0 <= a -> a + Z.of_nat (length t) < 2 ^ 63 ->
  rdn RSEGS M (Z_to_bv 64 a) (length t) = Some (map (Z_to_bv 8) t).
Proof.
  intros M t. induction t as [|v r IH]; intros a B Ha Hn; [reflexivity|].
  cbn [length] in Hn. cbn [length map]. rewrite (TKX.rdn_S M _ (length r)).
  pose proof (B 0%nat ltac:(cbn; lia)) as B0. cbn [nth] in B0. rewrite Z.add_0_r in B0. unfold L5.u8_at in B0. rewrite (TKX.rdn_S M _ 0) in B0.
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|]; [|discriminate B0].
  cbn [rdn] in B0. injection B0 as ->. rewrite (w_add1 a) by lia. rewrite (IH (a + 1)); [reflexivity | | lia | lia].
  intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact (B (S i) ltac:(cbn; lia)).
Qed.
(* [comment removed for export] *)
Lemma bytes_at_slice : forall (M : mem) (s : list Z) D a (k : nat), L5.bytes_at RSEGS M D s -> D <= a -> a - D + Z.of_nat k <= Z.of_nat (length s) ->
  L5.bytes_at RSEGS M a (firstn k (skipn (Z.to_nat (a - D)) s)).
Proof.
  intros M s D a k B HD Hk i Hi. rewrite length_firstn, length_skipn in Hi.
  rewrite nth_firstn. destruct (Nat.ltb_spec i k); [|lia]. rewrite nth_skipn.
  replace (a + Z.of_nat i) with (D + Z.of_nat (Z.to_nat (a - D) + i)) by lia. apply B. lia.
Qed.
Lemma length_slice : forall {A} (s : list A) o (k : nat), (o + k <= length s)%nat -> length (firstn k (skipn o s)) = k.
Proof. intros A s o k H. rewrite length_firstn, length_skipn. lia. Qed.
(* [comment removed for export] *)
Lemma bytes_at_wbytes : forall (M : mem) dst (bs : list byte), 0 <= dst -> dst + Z.of_nat (length bs) < 2 ^ 63 ->
  L5.bytes_at RSEGS (wbytes M (Z_to_bv 64 dst) bs) dst (map bv_unsigned bs).
Proof.
  intros M dst bs Hd Hn i Hi. rewrite length_map in Hi. unfold L5.u8_at. rewrite (TKX.rdn_S _ _ 0).
  pose proof (wbytes_nth bs M (Z_to_bv 64 dst) i) as W. rewrite Z_to_bv_unsigned in W. unfold bv_wrap in W. change (bv_modulus 64) with (2 ^ 64) in W.
  rewrite (Z.mod_small dst) in W by lia. rewrite W by lia. cbn [rdn]. f_equal. f_equal.
  rewrite (@nth_indep _ (map bv_unsigned bs) i 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hi). rewrite map_nth. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma map_unsigned_of_Z8 : forall (t : list Z), Forall (fun b => 0 <= b <= 255) t -> map bv_unsigned (map (Z_to_bv 8) t) = t.
Proof.
  intros t H. induction H as [|v r Hv _ IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rm_match_x : forall (KK : Z -> Prop) (M M' : mem) c P ps, TK.samem KK M M' -> 0 <= P -> P + 272 < 2 ^ 63 -> (forall i, P + 148 <= i < P + 224 -> KK i) ->
  PMR.rm_match c M P ps -> PMR.rm_match c M' P ps.
Proof.
  intros KK M M' c P ps AG HP HP2 HK (CORE & STR & NUM). split; [exact CORE|]. split; [|exact NUM].
  intros Hs. destruct (STR Hs) as (A1 & A2 & A3 & A4 & A5 & (t & A6 & A7)). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [intros H; apply (TK.u32_samem KK M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact (A4 H)]|].
  split; [intros H; apply (TK.u32_samem KK M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact (A5 H)]|].
  exists t. split; [apply (TK.u8_samem KK M M' _ _ AG); [lia | apply HK; lia | exact A6] | exact A7].
Qed.
(* [comment removed for export] *)
Lemma win_bytes_x : forall (KK : Z -> Prop) (M M' : mem) ps w, TK.samem KK M M' ->
  (forall p e, PML.ps_win ps = Some (p, e) -> 0 <= p /\ e < 2 ^ 63 /\ forall i, p <= i < e -> KK i) ->
  PMW.win_bytes M ps w -> PMW.win_bytes M' ps w.
Proof.
  intros KK M M' ps w AG HK WB. unfold PMW.win_bytes in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact WB].
  destruct WB as (B & L & F). destruct (HK p e eq_refl) as (Hp & He & HKi). split; [|split; [exact L | exact F]].
  apply (TK.bytes_samem KK M M' p w AG); [lia | lia | intros i Hi; apply HKi; lia | exact B].
Qed.
Lemma win_bytes_setwin : forall (M : mem) ps p e w, L5.bytes_at RSEGS M p w -> Z.of_nat (length w) = e - p -> Forall (fun b => 0 <= b <= 255) w ->
  PMW.win_bytes M (PML.ps_set_win ps (Some (p, e))) w.
Proof. intros M [] p e w B L F. unfold PMW.win_bytes. cbn. split; [exact B | split; [exact L | exact F]]. Qed.
Lemma win_bytes_nil : forall (M M' : mem) ps w, PMS.win_exhausted ps -> PMW.win_bytes M ps w -> w = [] /\ PMW.win_bytes M' ps w.
Proof.
  intros M M' ps w EX WB. unfold PMW.win_bytes, PMS.win_exhausted, PML.winlen in *. destruct (PML.ps_win ps) as [[p e]|].
  - destruct WB as (B & L & F). assert (w = []) by (destruct w; [reflexivity | cbn [length] in L; lia]). subst w. split; [reflexivity|].
    split; [intros i Hi; cbn in Hi; lia | split; [exact L | constructor]].
  - split; [exact WB | exact WB].
Qed.
End TKW.
