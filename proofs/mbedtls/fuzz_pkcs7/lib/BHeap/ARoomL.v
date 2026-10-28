(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ahx.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_ARoomL () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "Stdlib.ZArith.BinInt.Z.mul"; "ARUN_1.SEC_MIN_COST"; "RocqVerifyHarness.AgentSubmission.AHeap.AFreeSlot.zsum"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec_cost_live"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec_cost_ghost"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPrimHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.bwf"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.cb_of"; "ARUN_1.STAT"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Stdlib.ZArith.BinInt.Z.ltb"; "ARUN_1.WINDOW"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.HKv"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vranges_ok"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_eb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vnb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.VLIMIT"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition SEC_MIN_COST : Z := 77824.   (* [comment removed for export] *)

#[using="Type"] Lemma zsum_nonneg' : forall {A} (f : A -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= zsum f l.
Proof. intros A f l H. induction l as [|x r IH]; cbn; [lia|]. pose proof (H x ltac:(now left)). specialize (IH ltac:(intros; apply H; now right)). lia. Qed.

#[using="Type"] Lemma zsum_div_le : forall {A} (f : A -> Z) l S, 0 < S -> (forall x, In x l -> 0 <= f x) -> zsum (fun x => f x / S) l <= zsum f l / S.
Proof.
  intros A f l S HS POS. induction l as [|x r IH]; cbn; [rewrite Z.div_0_l by lia; lia|].
  pose proof (POS x ltac:(now left)) as Px. specialize (IH ltac:(intros; apply POS; now right)).
  pose proof (zsum_nonneg' f r ltac:(intros; apply POS; now right)) as Pr.
  assert (f x / S + zsum f r / S <= (f x + zsum f r) / S).
  { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (f x) S ltac:(lia)). pose proof (Z.mod_pos_bound (f x) S ltac:(lia)).
    pose proof (Z.div_mod (zsum f r) S ltac:(lia)). pose proof (Z.mod_pos_bound (zsum f r) S ltac:(lia)). lia. }
  lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_live_bound : ltac2:(CDefT.buildp (gd_tbl_ARoomL ()) "Pl,(0.$1.)PS,$2.P,(3.=R1.)P,(4.$1.Lsh,$1.(5.(6.+2.+10.)(7.R1.))R3.)(5.(8.$9.(:.$1.Lsh,$1.(;.(<.(7.R1.)R4.)+2.)R4.))(;.(8.$9.(<.(:.$1.$7.R4.)R3.))(8.+2.(:.$1.$=.R4.))))")
(* [comment removed for export] *).
Proof.
  intros l S HS B.
  assert (POS : forall x, In x l -> 0 <= s_map_size x) by (intros x Hx; pose proof (proj1 (Forall_forall _ _) B x Hx) as X; cbn beta in X; lia).
  pose proof (zsum_div_le s_map_size l S HS POS) as D.
  assert (C : SEC_MIN_COST * zsum (fun _ : shdr => 2) l <= 2 * zsum sec_cost_live l).
  { clear D. induction l as [|x r IH]; cbn; [lia|]. inversion B; subst. specialize (IH ltac:(assumption) ltac:(intros; apply POS; now right)).
    unfold sec_cost_live at 1. unfold npg_shadow, SEC_MIN_COST in *. pose proof (Z.div_pos (s_map_size x) 32768 ltac:(lia) ltac:(lia)). lia. }
  replace (zsum (fun sh : shdr => s_map_size sh / S + 2) l) with (zsum (fun sh => s_map_size sh / S) l + zsum (fun _ : shdr => 2) l) by (rewrite <- zsum_add; reflexivity).
  unfold SEC_MIN_COST in *. lia.
Qed.

#[using="Type"] Lemma sec_ghost_bound : ltac2:(CDefT.buildp (gd_tbl_ARoomL ()) "Pl,(0.(>.$2.$2.))PS,$2.P,(3.=R1.)P,(4.(>.$2.$2.)Lg,(>.$2.$2.)(5.(6.+2.+10.)(?.$2.$2.R1.))R3.)(5.(8.$9.(:.(>.$2.$2.)Lg,(>.$2.$2.)(;.(<.(?.$2.$2.R1.)R4.)+2.)R4.))(;.(8.$9.(<.(:.(>.$2.$2.)(?.$2.$2.)R4.)R3.))(8.+2.(:.(>.$2.$2.)$10.R4.))))")
(* [comment removed for export] *).
Proof.
  intros l S HS B.
  assert (POS : forall x, In x l -> 0 <= snd x) by (intros x Hx; pose proof (proj1 (Forall_forall _ _) B x Hx) as X; cbn beta in X; lia).
  pose proof (zsum_div_le snd l S HS POS) as D.
  assert (C : SEC_MIN_COST * zsum (fun _ : Z * Z => 2) l <= 2 * zsum sec_cost_ghost l).
  { clear D. induction l as [|x r IH]; cbn; [lia|]. inversion B; subst. specialize (IH ltac:(assumption) ltac:(intros; apply POS; now right)).
    unfold sec_cost_ghost at 1. unfold npg_shadow, SEC_MIN_COST in *. pose proof (Z.div_pos (snd x) 32768 ltac:(lia) ltac:(lia)). lia. }
  replace (zsum (fun g : Z * Z => snd g / S + 2) l) with (zsum (fun g : Z * Z => snd g / S) l + zsum (fun _ : Z * Z => 2) l) by (rewrite <- zsum_add; reflexivity).
  unfold SEC_MIN_COST in *. lia.
Qed.

(* [comment removed for export] *)
Definition STAT (S ctx : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_ARoomL ()) "(;.(;.(;.(;.(;.(;.(;.(;.(;.(;.(;.(<.$11.O2.)(<.$12.O2.))(<.+1000.O2.))(<.O1.O2.))(<.$13.O2.))(<.+1000.O2.))+<.)(8.+10.(;.(<.(6.+2.+18.)O2.)+2.)))(;.(;.(;.(<.+10000000.O2.)(<.+20000000000.O2.))(<.+=???0001000.O2.))+6.))(8.(;.(<.(6.+2.+14.)O2.)+2.)+8000.))(8.(;.(<.(6.+2.+17.)O2.)+2.)+1000.))(;.(<.(6.+2.+10.)O2.)+2.))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma vst_cb_gen : ltac2:(CDefT.buildp (gd_tbl_ARoomL ()) "Ph,$14.PS,$2.PH,$2.P,(15.VhAR,R3.)P,(5.(16.R4.)R2.)P,(5.(6.+2.+10.)R4.)(5.(8.$9.(17.R5.R6.))(;.(8.$9.(;.(18.R5.(19.(1:.R6.)))(<.R4.R5.)))(8.+2.R4.)))")
(* [comment removed for export] *).
Proof.
  (intros h S H dd_H; ddestruct dd_H as ([WL WLS] & WR & WS & WD & WB & (BS & BG & XL & XF)); intros HV HS).
  assert (S0 : 0 < S) by lia.
  unfold cb_of, cover_of, hulls_of, fixed_of. rewrite !map_app. cbn [map app].
  rewrite ?zsum_app. cbn [zsum fst snd]. rewrite ?zsum_app. cbn [zsum fst snd t_lo t_len]. rewrite !zsum_map. cbn [fst snd t_len].
  dpose WD as (_ & _ & _ & _ & _ & _ & LNB & LBL). dpose WB as (GWF & HV0 & SECB).
  assert (SECB' : zsum sec_cost_live (s_chunks (h_sec h)) + zsum sec_cost_ghost (a_sech (h_acct h)) <= h_havol h)
    by (unfold SECC in SECB; rewrite !sum_zsum, !zsum_map in SECB; exact SECB). clear SECB. rename SECB' into SECB.
  assert (G1 : 0 <= zsum sec_cost_live (s_chunks (h_sec h))).
  { apply zsum_nonneg'. intros x Hx. unfold sec_cost_live, npg_shadow. pose proof (proj1 (Forall_forall _ _) BS x Hx) as X. cbn beta in X. assert (0 <= s_map_size x / 32768) by (apply Z.div_pos; clear - X; lia). clear - H0 X. lia. }
  assert (G2 : 0 <= zsum sec_cost_ghost (a_sech (h_acct h))).
  { apply zsum_nonneg'. intros x Hx. unfold sec_cost_ghost, npg_shadow. pose proof (proj1 (Forall_forall _ _) BG x Hx) as X. cbn beta in X. assert (0 <= snd x / 32768) by (apply Z.div_pos; clear - X; lia). clear - H0 X. lia. }
  pose proof (sec_live_bound (s_chunks (h_sec h)) S S0 BS) as XS.
  pose proof (sec_ghost_bound (a_sech (h_acct h)) S S0 BG) as XG.
  assert (LS : zsum s_map_size (s_chunks (h_sec h)) <= zsum sec_cost_live (s_chunks (h_sec h))).
  { apply zsum_le. intros x Hx. unfold sec_cost_live, npg_shadow. pose proof (proj1 (Forall_forall _ _) BS x Hx) as X. cbn beta in X. assert (0 <= s_map_size x / 32768) by (apply Z.div_pos; clear - X; lia). lia. }
  assert (LG : zsum snd (a_sech (h_acct h)) <= zsum sec_cost_ghost (a_sech (h_acct h))).
  { apply zsum_le. intros x Hx. unfold sec_cost_ghost, npg_shadow. pose proof (proj1 (Forall_forall _ _) BG x Hx) as X. cbn beta in X. assert (0 <= snd x / 32768) by (apply Z.div_pos; clear - X; lia). lia. }
  assert (D1 : zsum s_map_size (s_chunks (h_sec h)) / S + zsum snd (a_sech (h_acct h)) / S <= H / S).
  { assert (A0 : 0 <= zsum s_map_size (s_chunks (h_sec h))) by (apply zsum_nonneg'; intros x Hx; pose proof (proj1 (Forall_forall _ _) BS x Hx) as X; cbn beta in X; lia).
    assert (B0 : 0 <= zsum snd (a_sech (h_acct h))) by (apply zsum_nonneg'; intros x Hx; pose proof (proj1 (Forall_forall _ _) BG x Hx) as X; cbn beta in X; lia).
    apply Z.le_trans with (m := (zsum s_map_size (s_chunks (h_sec h)) + zsum snd (a_sech (h_acct h))) / S).
    - apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (zsum s_map_size (s_chunks (h_sec h))) S ltac:(lia)). pose proof (Z.mod_pos_bound (zsum s_map_size (s_chunks (h_sec h))) S ltac:(lia)).
      pose proof (Z.div_mod (zsum snd (a_sech (h_acct h))) S ltac:(lia)). pose proof (Z.mod_pos_bound (zsum snd (a_sech (h_acct h))) S ltac:(lia)). lia.
    - apply Z.div_le_mono; [lia|]. clear - LS LG SECB HV G1 G2. lia. }
  assert (XE : zsum (fun x : Z * Z => snd x / S + 2) (l_extra (h_L h)) <= 16 * (2^24 / S + 2)).
  { apply Z.le_trans with (m := zsum (fun _ => 2^24 / S + 2) (l_extra (h_L h))).
    - apply zsum_le. intros x Hx. pose proof (proj1 (Forall_forall _ _) XF x Hx) as X. cbn beta in X. assert (snd x / S <= 2^24 / S) by (apply Z.div_le_mono; lia). lia.
    - rewrite zsum_const. assert (P0 : 0 <= 2^24 / S + 2) by (pose proof (Z.div_pos (2^24) S); lia). clear - P0 XL. nia. }
  assert (XN : zsum (fun _ : Z => 2^20 / S + 2) (d_nb (h_dep h)) <= (2^20 / S + 2) * 32768).
  { rewrite zsum_const. assert (P0 : 0 <= 2^20 / S + 2) by (pose proof (Z.div_pos (2^20) S); lia). clear - P0 LNB. nia. }
  assert (XB : zsum (fun _ : Z => 2^23 / S + 2) (d_bl (h_dep h)) <= (2^23 / S + 2) * 4096).
  { rewrite zsum_const. assert (P0 : 0 <= 2^23 / S + 2) by (pose proof (Z.div_pos (2^23) S); lia). clear - P0 LBL. nia. }
  assert (XM : zsum (fun x : trange => t_len x / S + 2) (emb_tr h) <= 2^16 / S + 2).
  { unfold emb_tr. destruct (a_emb (h_acct h) =? 0); cbn [zsum t_len].
    - pose proof (Z.div_pos (2^16) S ltac:(lia) S0) as P0. lia.
    - change kEmbBytes with (2^16). lia. }
  unfold STAT. unfold SEC_MIN_COST in *. clear - XS XG D1 XE XN XB XM SECB HV G1 G2. lia.
Qed.

(* [comment removed for export] *)
Definition WINDOW : Z := 93822836363264.   (* [comment removed for export] *)
#[using="Type"] Lemma WINDOW_ok : WINDOW = ACEIL_MIN - bottomup_floor. Proof. reflexivity. Qed.
Definition room_ok_b (k : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_ARoomL ()) "ZS,$2.(8.+1000.O1.)(1;.(;.(8.$9.(;.(18.R1.+10000.)(<.(6.+2.+20.)R1.)))(8.+2.(6.+2.+20.)))(8.$9.(<.$1<.R1.)))")
(* [comment removed for export] *).
#[using="Type"] Lemma room_ok_all : forall k, 16 <= k <= 65540 -> room_ok_b k = true.
Proof.
  intros k Hk. apply (zall_spec room_ok_b (Z.to_nat 65525) 16); [| lia].
  first [let g := lazymatch goal with |- ?g0 => eval hnf in g0 end in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end | vm_compute; reflexivity]. (* [comment removed for export] *)
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma room_ok_b_eq : forall k,
  room_ok_b k = (let S := 4096 * k in SEC_MIN_COST * (STAT S 65536 + 2^32 / S) + 2 * 2^32 <? SEC_MIN_COST * (WINDOW / S)).
Proof. intros k. exact (@eq_refl bool (let S := 4096 * k in SEC_MIN_COST * (STAT S 65536 + 2^32 / S) + 2 * 2^32 <? SEC_MIN_COST * (WINDOW / S))). Qed.

#[using="Type"] Theorem HKv_room_large : ltac2:(CDefT.buildp (gd_tbl_ARoomL ()) "PAL,$1=.Ph,$14.Pmo,$1>.PS,$2.P,(15.VhAR,R3.)P,(1?.VhAR,R5.(20.R4.)R3.)P,(21.R6.(20.R5.))P,(5.(16.R6.)(6.+2.+20.))P,(22.(5.(6.+2.+10.)R5.)(5.R5.(;.(6.+2.+1<.)+4000.)))P,(23.$2.(24.R6.+1000.)=)P,(5.(;.(;.(25.(20.R9.))(8.+1000.(26.(20.R9.))))R7.)$27.)(28.(29.&40.)La,(29.&40.)(2:.VhAR,+22.R9.R:.R1.))")
(* [comment removed for export] *).
Proof.
  intros AL h mo S A K VR HV HS SAL EBUD.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & TBL & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  pose proof A as B. pose proof A as ([WL _] & _). unfold wf_L in WL.
  assert (E : l_ctxlen (h_L h) = 65536) by (decompose [and] WL; assumption).
  pose proof (Z.div_mod S 4096 ltac:(lia)) as DS. rewrite SAL, Z.add_0_r in DS.
  set (JZ := WINDOW / S).
  assert (J0 : 0 <= JZ) by (subst JZ; apply Z.div_pos; unfold WINDOW; lia).
  apply (room_gen AL (vst_of h) mo S JZ 0x22 K); [lia| exact SAL| exact J0| | |].
  - subst JZ. pose proof (Z.mul_div_le WINDOW S ltac:(lia)) as MD. pose proof WINDOW_ok as WE. clear - MD WE. lia.
  - eapply Z.le_lt_trans; [apply (cb_of_ok S h); [lia| exact CE2]|].
    pose proof (vst_cb_gen h S (2^32) B HV ltac:(lia)) as X. rewrite E in X.
    pose proof (room_ok_all (S / 4096) ltac:(lia)) as R. rewrite (room_ok_b_eq (S / 4096)) in R. apply Z.ltb_lt in R. (* [comment removed for export] *)
    replace (4096 * (S / 4096)) with S in R by lia. subst JZ. unfold SEC_MIN_COST in *. clear - X R. lia.
  - intros _. pose proof (HKv_mat_le AL (vst_of h) mo VR K). lia.
Qed.

End ARUN_1.
