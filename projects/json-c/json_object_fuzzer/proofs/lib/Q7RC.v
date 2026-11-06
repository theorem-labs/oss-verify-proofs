(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPWv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPWv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlOh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlOh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcV4.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SLOT.
Variable T : Type.
Variable Post : mled -> T -> Prop.

#[using="Type"] Theorem alloc_slot_ft (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
49 - sc <= Z.of_nat f ->
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
(forall st1 idx L1 LS1, SLOT_POST idle sc req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
ftree L (alloc_slot full_lay f st sc req k bail) Post.
Proof.
induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit HK.
{ exfalso. cbn in Hf. lia. }
change (alloc_slot full_lay (S f) st sc req k bail) with
(try_avail sc st (fun st1 first =>
if negb (first =? 0) then k st1 (ctz32 first)
else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
match go with
| None => k st2 (-1)
| Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
queue (LActive sc) g st3 (fun st4 => k st4 0) bail
end) bail) bail).
destruct (try_avail_ok T (X_as idle) L BL sc
(fun st1 first =>
if negb (first =? 0) then k st1 (ctz32 first)
else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
match go with
| None => k st2 (-1)
| Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
queue (LActive sc) g st3 (fun st4 => k st4 0) bail
end) bail) bail eq_refl eq_refl Hsc st LS INV) as (st1 & first & LS1 & E & TAF & RES).
rewrite E. cbn beta.
assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
{ intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).
destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1)].
-
change (negb (0 =? 0)) with false. cbn iota.
assert (REC : REC_OK T (alloc_slot full_lay f) sc Post).
{ intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' Hreq' Hfit' HK'.
apply (IH j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
apply (alloc_group_ft T (alloc_slot full_lay f) sc Post REC idle st1 L BL LS1 req _ bail INV1 TF1 ND Hsc Hreq Hfit HA).
intros st2 go L2 LS2 (ACT2 & LIVE2 & GP2 & RES2). destruct go as [g|].
+ destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2' & AZ2).
cbn zeta.
destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4 & ID4).
rewrite EQ. eapply HK. split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4| exact ID4]]]|].
right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
split; [exact INV4|]. split; [exact TF4|].

intros U o Ho. unfold get_shadow. rewrite SH4. unfold undersized in U. rewrite SC4, STR4 in U.
assert (SCg2 : m_sizeclass (MR st2 g) = sc) by (rewrite Em; reflexivity).
apply AZ2; [| exact Ho]. unfold undersized. rewrite SCg2. exact U.
+ destruct RES2 as [INV2 TF2']. eapply HK. split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| exact GP2]|].
left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
-
replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
cbn iota. rewrite Eidx. eapply HK.
split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. right.
pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. split; [apply TF0_TF2; exact TF1|].

intros U. exfalso. unfold undersized in U. rewrite SC in U. destruct U as [U|U]; lia.
Qed.
End SLOT.

End RC__1.
