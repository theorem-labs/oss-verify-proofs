(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7z8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M.
Import ListNotations.
Open Scope Z_scope.

Definition avoid_J (pres parr : Z) (objs : list (Z * Z)) (bl : Z) : list (Z * Z) :=
[(pres, pres + kPrimResLen); (parr, parr + kPtrArrLen)] ++ objs ++ [(0x10000, 0x645000); (0x7fff7000, 0x10007fff8000); (bl, 2^64)].
Definition LA_J (sb pres parr : Z) (objs : list (Z * Z)) (bl : Z) : ALay := mkALay sb parr (avoid_J pres parr objs bl).

Definition TMAX_J : Z := 17740000000000.
Definition NMAX_J : Z := 128.

Lemma L_main_jo6_alloc_ok : forall atop, lv_alloc_ok (L_main_jo6 atop).
Proof.
intros atop. split; [reflexivity|]. split.
- intros x Hx. cbn in Hx. unfold kLowEnd, kHighMemBeg.
destruct Hx as [<-|[<-|[<-|[]]]]; cbn; lia.
- intros y Hy. unfold L_main_jo6, Qsn5.in_zivs, Qsn5.zin. cbn [lv_excl existsb fst snd].
unfold kLowEnd, kHighMemBeg in Hy.
destruct (Z.lt_ge_cases y 0x8fff7000) as [H1|H1]; [apply orb_true_iff; left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia|].
destruct (Z.lt_ge_cases y 0x2008fff7000) as [H2|H2];
[apply orb_true_iff; right; apply orb_true_iff; left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia|].
apply orb_true_iff; right; apply orb_true_iff; right; apply orb_true_iff; left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma ll_ok_J LV sb pres parr objs bl :
lv_alloc_ok LV -> main_addrs_ok sb pres parr -> objs_ok objs ->
In (0x10000, 0x645000) (lv_base LV) -> In (bl, 2^47) (lv_base LV) -> bl < 2^47 ->
ll_ok (LA_J sb pres parr objs bl) LV 0 (PERM_main pres parr objs) TMAX_J NMAX_J.
Proof.
intros HLV [P0 P1 P2 S1 S2 S3 Q0 Q1 Q2 Q3] HO Hhull Hband Hbl. pose proof HLV as (Hsh & Hex & Hcov).
unfold objs_ok in HO. rewrite Forall_forall in HO.
unfold lowhigh, kHighMemBeg, kPrimResLen, kPtrArrLen, CEIL, kLowEnd in *. cbn [fst snd] in P0, Q0.
assert (Hceil : kCeil = 0x7fffff800000) by apply kCeil_val.
constructor; unfold PERM_main, avoid_J, LA_J, band_hi, band_lo, band_gap, kPrimResLen, kPtrArrLen, KHI, kHighMemBeg in *;
cbn [al_space_beg al_ptrarr al_avoid fst snd] in *; unfold avoid_J, kPrimResLen, kPtrArrLen, kHighMemBeg in *.
- constructor; cbn [al_space_beg al_ptrarr]; unfold kPage; lia.
- exact Hsh.
- intros r Hr. rewrite Hceil. apply in_app_iff in Hr as [[<-|[<-|[<-|[<-|[<-|[]]]]]]|Hr]; cbn [fst snd]; try lia.
pose proof (HO r Hr). lia.
-
intros iv Hiv. apply in_app_iff in Hiv as [[<-|[<-|[]]]|Hiv]; cbn [fst snd]; (split; [try lia|intros y Hy; cbn [fst snd] in Hy]).
+ left. exists (pres, pres + 0x2000011000). split; [apply in_app_iff; left; left; reflexivity| cbn [fst snd]; lia].
+ left. exists (parr, parr + 0x800000). split; [apply in_app_iff; left; right; left; reflexivity| cbn [fst snd]; lia].
+ apply in_app_iff in Hiv as [Hiv|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; [pose proof (HO iv Hiv); lia| lia| lia| lia].
+ apply in_app_iff in Hiv as [Hiv|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hy.
* left. exists iv. split; [apply in_app_iff; right; exact Hiv| lia].
* right; left. exists (0x10000, 0x645000). split; [exact Hhull| cbn [fst snd]; lia].
* left. destruct (Z.lt_ge_cases y 0x8fff7000).
{ exists (0x7fff7000, 0x8fff7000). split; [apply in_app_iff; left; right; right; right; left; reflexivity| cbn [fst snd]; lia]. }
destruct (Z.lt_ge_cases y 0x2008fff7000).
{ exists (0x8fff7000, 0x2008fff7000). split; [apply in_app_iff; left; right; right; right; right; left; reflexivity| cbn [fst snd]; lia]. }
exists (0x2008fff7000, 0x10007fff8000). split; [apply in_app_iff; left; right; right; left; reflexivity| cbn [fst snd]; lia].
* destruct (Z.lt_ge_cases y (2^47)).
{ right; left. exists (bl, 2^47). split; [exact Hband| cbn [fst snd]; lia]. }
right; right. rewrite Hceil. lia.
- exists (pres, pres + 0x2000011000). split; [apply in_app_iff; left; left; reflexivity|]. split; [| cbn [fst snd]; lia].
apply excl_entry_lowhigh; [exact HLV|]. unfold z2w. cbn [fst snd]. rewrite !u_w64 by lia. unfold kLowEnd, kHighMemBeg. lia.
- exists (parr, parr + 0x800000). split; [apply in_app_iff; left; right; left; reflexivity|]. split; [| cbn [fst snd]; lia].
apply excl_entry_lowhigh; [exact HLV|]. unfold z2w. cbn [fst snd]. rewrite !u_w64 by lia. unfold kLowEnd, kHighMemBeg. lia.
- exists (0x2008fff7000, 0x10007fff8000). split; [apply in_app_iff; left; right; right; left; reflexivity|]. unfold kShadowOffset. cbn [fst snd]. rewrite Hceil.
change (17594333495296 / 8) with 2199291686912. change (140737479966720 / 8) with 17592184995840. lia.
- exists (0x7fff7000, 0x8fff7000). split; [apply in_app_iff; left; right; right; right; left; reflexivity|]. unfold kShadowOffset, kLowEnd. cbn [fst snd].
change (2147446784 / 8) with 268430848. lia.
- intros y Hy. unfold kLowEnd in Hy.
destruct (Z.lt_ge_cases y 0x8fff7000).
+ exists (0x7fff7000, 0x8fff7000). split; [apply in_app_iff; left; right; right; right; left; reflexivity| cbn; lia].
+ destruct (Z.lt_ge_cases y 0x2008fff7000).
* exists (0x8fff7000, 0x2008fff7000). split; [apply in_app_iff; left; right; right; right; right; left; reflexivity| cbn; lia].
* exists (0x2008fff7000, 0x10007fff8000). split; [apply in_app_iff; left; right; right; left; reflexivity| cbn; lia].
- intros y Hy. apply Hcov. unfold kLowEnd, kHighMemBeg in *. lia.
- lia.
- unfold TMAX_J, NMAX_J, kMaxCnt, kMaxChunk, QybZ.Mq0.alloc_ceiling, page_size. lia.
Qed.
