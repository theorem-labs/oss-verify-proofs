(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 60 of its 91 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntRec.v, with its module paths changed; 102 of its 135 lines of code are new or changed and 58 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonC2Mod.v, with its module paths and module names changed; 81 of its 208 lines of code are new or changed and 8 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonC2Defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_text disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb slot_ser_Pq.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma set_nth_length : forall (k : nat) (o : jobj) (t : tokv), length (set_nth k o t) = length o.
Proof.
  intros k o. revert k. induction o as [|x o IH]; intros k t; destruct k as [|k]; cbn [set_nth length];
    try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma slot_of_lt : forall (Bz : list Z) (t : tokv) (k : nat), slot_of Bz t = Some k -> (k < 6)%nat.
Proof.
  intros Bz t k H. unfold slot_of, keys in H. cbn [slot_from] in H.
  repeat (match type of H with context [if ?c then _ else _] => destruct c end;
    [injection H as <-; lia|]). discriminate H.
Qed.

Lemma c2m_set_nth_id : forall (k : nat) (o : jobj) (d : tokv), set_nth k o (nth k o d) = o.
Proof.
  intros k o. revert k. induction o as [|x o IH]; intros k d; destruct k as [|k]; cbn [set_nth nth];
    try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma c2m_objs_snoc : forall (buf : Z) (vpad : list byte) (acc : list jobj) (o : jobj),
  slot_ser_defs.objs_bytes buf vpad (acc ++ [o]) =
  slot_ser_defs.objs_bytes buf vpad acc ++ slot_ser_defs.obj_bytes buf vpad o.
Proof.
  intros buf vpad acc o. unfold slot_ser_defs.objs_bytes. rewrite map_app, concat_app.
  cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma c2m_obj_len : forall (buf : Z) (vpad : list byte) (o : jobj),
  length vpad = 4%nat -> length o = 6%nat -> length (slot_ser_defs.obj_bytes buf vpad o) = 144%nat.
Proof.
  intros buf vpad o L Ho.
  pose proof (slot_ser_Pq.objs_len buf vpad [o] L ltac:(constructor; [exact Ho | constructor])) as H.
  unfold slot_ser_defs.objs_bytes in H. cbn [map concat] in H. rewrite app_nil_r in H.
  cbn [length] in H. lia.
Qed.

Lemma c2m_obj_in : forall (buf : Z) (vpad : list byte) (o : jobj) (k : nat) (t : tokv) (j : nat) (d : byte),
  length vpad = 4%nat -> (k < length o)%nat -> (24 * k <= j < 24 * k + 24)%nat ->
  nth j (slot_ser_defs.obj_bytes buf vpad (set_nth k o t)) d =
  nth (j - 24 * k)%nat (slot_ser_defs.slot24 buf vpad t) d.
Proof.
  intros buf vpad o. unfold slot_ser_defs.obj_bytes.
  induction o as [|x o IH]; intros k t j d L Hk Hj; cbn [length] in Hk; [lia|].
  destruct k as [|k]; cbn [set_nth map concat].
  - rewrite app_nth1 by (rewrite slot_ser_Pq.slot24_len by exact L; lia).
    replace (j - 24 * 0)%nat with j by lia. reflexivity.
  - rewrite app_nth2 by (rewrite slot_ser_Pq.slot24_len by exact L; lia).
    rewrite slot_ser_Pq.slot24_len by exact L.
    rewrite IH by (first [exact L | lia]).
    replace (j - 24 - 24 * k)%nat with (j - 24 * S k)%nat by lia. reflexivity.
Qed.

Lemma c2m_obj_out : forall (buf : Z) (vpad : list byte) (o : jobj) (k : nat) (t : tokv) (j : nat) (d : byte),
  length vpad = 4%nat -> ~ (24 * k <= j < 24 * k + 24)%nat ->
  nth j (slot_ser_defs.obj_bytes buf vpad (set_nth k o t)) d =
  nth j (slot_ser_defs.obj_bytes buf vpad o) d.
Proof.
  intros buf vpad o. unfold slot_ser_defs.obj_bytes.
  induction o as [|x o IH]; intros k t j d L Hj; [destruct k; reflexivity|].
  destruct k as [|k]; cbn [set_nth map concat].
  - rewrite !app_nth2 by (rewrite slot_ser_Pq.slot24_len by exact L; lia).
    rewrite !slot_ser_Pq.slot24_len by exact L. reflexivity.
  - destruct (Nat.lt_ge_cases j 24) as [Hj2|Hj2].
    + rewrite !app_nth1 by (rewrite slot_ser_Pq.slot24_len by exact L; lia). reflexivity.
    + rewrite !app_nth2 by (rewrite slot_ser_Pq.slot24_len by exact L; lia).
      rewrite !slot_ser_Pq.slot24_len by exact L.
      apply IH; [exact L | lia].
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma jc2_ws : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> json_ws (p_B P) (p_j2 P) = p_j2 P.
Proof.
  intros P W m (HF & Hip & _). apply json_ws_id; [exact (proj1 (proj2 (proj2 HF))) | lia].
Qed.

Lemma jc2_acc6 : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> Forall (fun o : jobj => length o = 6%nat) (p_acc P).
Proof.
  intros P W m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & HL) & _).
  exact (proj1 (proj1 (Forall_app _ _ _) HL)).
Qed.

Lemma jc2_count : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> 0 <= p_count P <= 7.
Proof.
  intros P W m (HF & _ & Hc & _ & _ & _ & _ & HJ & _).
  pose proof (proj1 (proj2 HF)) as Hfin.
  destruct (jpairs_cont_step (p_B P) (p_fin P) _ _ _ _ HJ) as [(_ & HP) | (_ & _ & HA)].
  - pose proof (jpairs_from_count (p_B P) (p_fin P) _ _ _ _ HP). lia.
  - pose proof (jobjs_after_count (p_B P) (p_fin P) _ _ _ _ HA). lia.
Qed.

Lemma jc2_c2_ok : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> length (p_c2 P) = 6%nat /\ Forall (slot_ser_tokb.tok_inb (p_B P)) (p_c2 P).
Proof.
  intros P W m (_ & _ & _ & _ & _ & _ & HU & _ & HL & HA & _ & HV & _).
  unfold jslot_upd in HU. destruct (slot_of (p_B P) (p_kt P)) as [k|] eqn:ES.
  - destruct (tv_kind (nth k (p_cur P) tok_none) =? 0); [|discriminate HU].
    injection HU as <-. rewrite set_nth_length. split; [exact HL|].
    apply slot_ser_tokb.set_nth_forall; [exact HA | exact HV].
  - injection HU as <-. split; [exact HL | exact HA].
Qed.

Lemma jc2_none : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> slot_of (p_B P) (p_kt P) = None -> p_c2 P = p_cur P.
Proof.
  intros P W m (_ & _ & _ & _ & _ & _ & HU & _) HS. unfold jslot_upd in HU. rewrite HS in HU.
  injection HU as <-. reflexivity.
Qed.

Lemma jc2_some : forall (P : jc2p) (W : world SEGS) (m : word -> option byte) (k : nat),
  jc2_x P W m -> slot_of (p_B P) (p_kt P) = Some k ->
  tv_kind (nth k (p_cur P) tok_none) = 0 /\ p_c2 P = set_nth k (p_cur P) (p_vt P).
Proof.
  intros P W m k (_ & _ & _ & _ & _ & _ & HU & _) HS. unfold jslot_upd in HU. rewrite HS in HU.
  destruct (tv_kind (nth k (p_cur P) tok_none) =? 0) eqn:EK; [|discriminate HU].
  injection HU as <-. split; [apply Z.eqb_eq; exact EK | reflexivity].
Qed.

Lemma jc2_kb0 : forall P, jc2_kb P 0.
Proof. intros P. split; [lia | reflexivity]. Qed.

Lemma jc2_kb_step : forall (P : jc2p) (kb : nat), (kb < 6)%nat ->
  jc2_kb P kb -> jtok_is (p_B P) (p_kt P) 1 (nth kb keys []) = false -> jc2_kb P (S kb).
Proof.
  intros P kb Hk (_ & HE) HF. split; [lia|]. rewrite HE.
  replace (skipn kb keys) with (nth kb keys [] :: skipn (S kb) keys).
  - cbn [slot_from]. rewrite HF. reflexivity.
  - unfold keys in *. do 6 (destruct kb as [|kb]; [reflexivity|]). lia.
Qed.

Lemma jc2_kb_hit : forall (P : jc2p) (kb : nat), (kb < 6)%nat ->
  jc2_kb P kb -> jtok_is (p_B P) (p_kt P) 1 (nth kb keys []) = true ->
  slot_of (p_B P) (p_kt P) = Some kb.
Proof.
  intros P kb Hk (_ & HE) HT. rewrite HE.
  replace (skipn kb keys) with (nth kb keys [] :: skipn (S kb) keys).
  - cbn [slot_from]. rewrite HT. reflexivity.
  - unfold keys in *. do 6 (destruct kb as [|kb]; [reflexivity|]). lia.
Qed.

Lemma jc2_kb_end : forall (P : jc2p), jc2_kb P 6 -> slot_of (p_B P) (p_kt P) = None.
Proof. intros P (_ & HE). rewrite HE. reflexivity. Qed.

Theorem jc2_obj : jc2_obj_stmt.
Proof.
  intros buf vpad acc cur k t HA Hc Hk Ht L.
  rewrite !c2m_objs_snoc.
  pose proof (slot_ser_Pq.objs_len buf vpad acc L HA) as HLa.
  change (@length (list tokv) acc) with (@length jobj acc) in HLa.
  split.
  - rewrite !length_app.
    rewrite (c2m_obj_len buf vpad (set_nth k cur t) L) by (rewrite set_nth_length; exact Hc).
    rewrite (c2m_obj_len buf vpad cur L Hc). reflexivity.
  - intros j Hj. rewrite length_app, HLa, (c2m_obj_len buf vpad cur L Hc) in Hj.
    destruct (Nat.lt_ge_cases j (144 * length acc)) as [H1|H1].
    + rewrite !app_nth1 by lia.
      replace ((144 * length acc + 24 * k <=? j)%nat) with false by (symmetry; apply Nat.leb_gt; lia).
      reflexivity.
    + rewrite !app_nth2 by lia. rewrite HLa.
      destruct (Nat.lt_ge_cases j (144 * length acc + 24 * k)) as [H2|H2].
      * replace ((144 * length acc + 24 * k <=? j)%nat) with false by (symmetry; apply Nat.leb_gt; lia).
        apply c2m_obj_out; [exact L | lia].
      * replace ((144 * length acc + 24 * k <=? j)%nat) with true by (symmetry; apply Nat.leb_le; lia).
        destruct (Nat.lt_ge_cases j (144 * length acc + 24 * k + 24)) as [H3|H3].
        -- replace ((j <? 144 * length acc + 24 * k + 24)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           rewrite c2m_obj_in by (first [exact L | lia]).
           replace (j - 144 * length acc - 24 * k)%nat with (j - (144 * length acc + 24 * k))%nat by lia.
           reflexivity.
        -- replace ((j <? 144 * length acc + 24 * k + 24)%nat) with false
             by (symmetry; apply Nat.ltb_ge; lia).
           apply c2m_obj_out; [exact L | lia].
Qed.

Theorem jc2_zero : jc2_zero_stmt.
Proof.
  intros buf vpad acc cur k HA Hc Hk L Hz j Hj.
  rewrite c2m_objs_snoc.
  pose proof (slot_ser_Pq.objs_len buf vpad acc L HA) as HLa.
  change (@length (list tokv) acc) with (@length jobj acc) in HLa.
  rewrite app_nth2 by lia. rewrite HLa.
  pose proof (c2m_obj_in buf vpad cur k (nth k cur tok_none) (j - 144 * length acc) (Z_to_bv 8 0) L
    ltac:(lia) ltac:(lia)) as E.
  rewrite c2m_set_nth_id in E. rewrite E.
  unfold slot_ser_defs.slot24. rewrite Hz, Z.eqb_refl. apply nth_repeat.
Qed.

End h.
End f.
End d.
