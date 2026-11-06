(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: W_shadow_pin.v's shp_ashp and W_shadow_pin_fr.v's ashp_str2_1_fr over a generic ARx
   (W_contract_x.v ashp_x).  The AR proof reads two conjuncts of AR's invariant: am_const (every const cell of
   as_const B ly holds its value) and am_zshadow (every range of zero_shadow_ranges B ly reads 0).  Over ARx they are
   the AR_laws_x fields alx_const_cells (YCbqG.v ARx_const_cells_law) and alx_zshadow (ARx_zshadow_law), with the same
   texts; nothing else of AR is read.  The literal's check is W_shadow_pin_fr.v's, decided by vm_compute over the
   start-up instance's tables (AF0m.Tfib_const_shadow, AF0m.Tfib_zero_shadow) for every B with AF0m.TfibSyms B.
     .str.2   ""   0x20ee0, 1 byte, granule 0x20ee0, shadow 0x7fffc1dc = 1 (W_shadow_pin_fr.v:8)
   - ashp_str2_1_fr_x: for every ARx with AR_laws_x and every B with TfibSyms B.
   - ashp_str2_1_fr_cf: at the cf instance of top_x (B := TfibB, ARx := ARcf (cp := CfParams_reply) segs TfibB /\
     Hp = [], laws by AR_laws_x_and_hp over AR_laws_x_cf, as top_x's ARX_laws), so top_x's ARX discharges
     remove_x's HSTR2S by `exact ashp_str2_1_fr_cf` (ARX unfolds to that relation). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_kit W_img W_contract W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0l AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

Section b.
Variable cs : list acell.
Variable zs : list (Z * Z).
Hypothesis HCS : forall ly c, In c cs -> In c (as_const B ly).
Hypothesis HZS : forall r, In r zs -> In r (as_zero_shadow B).

(* W_shadow_pin.v:111 shp_val_ok, over ARx: am_const -> alx_const_cells, am_zshadow -> alx_zshadow *)
Lemma shp_val_ok_x : forall ly S Hp (W : world SEGS) mem md s v, ARx ly S Hp W mem md -> shp_val cs zs s = Some v ->
aview SEGS (w_H W) mem s = Some v.
Proof.
intros ly S Hp W mem md s v HAR H. unfold shp_val in H.
destruct (shp_cells_at s cs) as [u|] eqn:Ec.
- injection H as <-. apply shp_cells_at_ok in Ec as (c & Hc & Hu).
  pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) c (HCS ly c Hc)) as Hh.
  exact (shp_cell_at_ok B s c u ly _ Hu Hh).
- destruct (shp_zs_at s zs) eqn:Ez; [|discriminate H]. injection H as <-.
  unfold shp_zs_at in Ez. apply existsb_exists in Ez as (r & Hr & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  assert (Hin : In r (YG0n.zero_shadow_ranges B ly)) by (right; exact (HZS r Hr)).
  pose proof (alx_zshadow _ _ _ LAWS ly S Hp W mem md r HAR Hin) as Hzr. red in Hzr.
  specialize (Hzr (s - (SHADOW_OFF + fst r / 8)) ltac:(lia)). unfold YG0v.shadow_of_addr in Hzr.
  replace (SHADOW_OFF + fst r / 8 + (s - (SHADOW_OFF + fst r / 8))) with s in Hzr by lia. exact Hzr.
Qed.

(* W_shadow_pin.v:129 shp_ashp, over ARx *)
Theorem shp_ashp_x : forall a n, shp_check cs zs a n = true -> ashp_x ARx a n.
Proof.
intros a n Hc ly S Hp W mem md HAR. unfold shp_check in Hc. apply andb_true_iff in Hc as [Hr Hh]. split.
- intros x Hx. rewrite forallb_forall in Hr. specialize (Hr x (shp_zseq_in a n x Hx)). cbv beta in Hr.
  destruct (shp_val cs zs (shadow_of_addr SHADOW_OFF x)) as [s|] eqn:Ev; [|discriminate Hr].
  exists s. split; [exact (shp_val_ok_x ly S Hp W mem md _ s HAR Ev)|].
  unfold shp_saddrb in Hr. unfold saddr_ok. apply orb_true_iff in Hr as [Hr|Hr]; [left; apply Z.eqb_eq; exact Hr|right].
  apply andb_true_iff in Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. split; assumption.
- intros Hn s Hs. apply orb_true_iff in Hh as [Hh|Hh]; [apply Z.leb_le in Hh; lia|].
  rewrite forallb_forall in Hh.
  assert (Hin : In s (shp_zseq (shadow_addr a / 8 * 8)
    (shadow_addr (a + n - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8))) by (apply shp_zseq_in; lia).
  specialize (Hh s Hin). cbv beta in Hh.
  destruct (shp_val cs zs s) as [v|] eqn:Ev; [|discriminate Hh].
  rewrite (shp_val_ok_x ly S Hp W mem md s v HAR Ev). discriminate.
Qed.
End b.
End a.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis HT : AF0m.TfibSyms B.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.

(* W_shadow_pin_fr.v:34 tfib_shp, over ARx *)
Lemma tfib_shp_x : forall a n, shp_check AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow a n = true -> ashp_x ARx a n.
Proof.
intros a n H. apply (shp_ashp_x B ARx LAWS AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow); [| | exact H].
- intros ly c Hc. rewrite (AF0m.ts_const _ HT ly). unfold AF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right. exact Hc.
- intros r Hr. rewrite (AF0m.ts_zsh _ HT). exact Hr.
Qed.

(* W_shadow_pin_fr.v:44 ashp_str2_1_fr, over ARx: .str.2 "" (check_shape_ends' prefix, PF), 0x20ee0, 1 byte;
   0x7fffc1dc = 1 *)
Lemma ashp_str2_1_fr_x : ashp_x ARx (VAL (A_OBJ 28)) 1.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* W_shadow_pin_fr.v:47-69, the other literals, over ARx (the same decision by vm_compute over the start-up tables) *)
(* .str.4 " end" (check_shape_ends' loop 3 bcmp operand), 0x20f00, 4 bytes; 0x7fffc1e0 = 5 *)
Lemma ashp_end5_4_fr_x : ashp_x ARx (VAL A_lit_end5) 4.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* .str.4 " end\0", 0x20f00, 5 bytes *)
Lemma ashp_end5_5_fr_x : ashp_x ARx (VAL A_lit_end5) 5.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* .str.5 "param_gesture", 0x20f20, 13 bytes; 0x7fffc1e4 = 0 (zero shadow), 0x7fffc1e5 = 6 *)
Lemma ashp_gesture_13_fr_x : ashp_x ARx (VAL A_lit_gesture) 13.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* .str.5 "param_gesture\0", 0x20f20, 14 bytes *)
Lemma ashp_gesture_14_fr_x : ashp_x ARx (VAL A_lit_gesture) 14.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* .str.6 "begin", 0x20f40, 5 bytes; 0x7fffc1e8 = 6 *)
Lemma ashp_begin_5_fr_x : ashp_x ARx (VAL A_lit_begin) 5.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* .str.6 "begin\0", 0x20f40, 6 bytes *)
Lemma ashp_begin_6_fr_x : ashp_x ARx (VAL A_lit_begin) 6.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* .str.7 "end", 0x20f60, 3 bytes; 0x7fffc1ec = 4 *)
Lemma ashp_end_3_fr_x : ashp_x ARx (VAL A_lit_end) 3.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
(* .str.7 "end\0", 0x20f60, 4 bytes *)
Lemma ashp_end_4_fr_x : ashp_x ARx (VAL A_lit_end) 4.
Proof. apply tfib_shp_x. vm_compute. reflexivity. Qed.
End f.

(* ------------------------------------------------------------------ at the cf instance of top_x *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* top_x's ARX (W_LLVMFuzzerTestOneInput_top_x.v Definition ARX), and its laws as top_x's ARX_laws proves them *)
Lemma ashp_str2_1_fr_cf :
  ashp_x (fun ly S Hp (W : world segs) mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [])
    (VAL (A_OBJ 28)) 1.
Proof.
  apply (ashp_str2_1_fr_x TfibB TfibB_syms _ (hl := @cf_head CfParams_reply)).
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.
End cf.
