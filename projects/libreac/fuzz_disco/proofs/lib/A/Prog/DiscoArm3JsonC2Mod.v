(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 60 of its 91 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntRec.v, with its module paths changed; 102 of its 135 lines of code are new or changed and 58 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonC2Defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_text disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb slot_ser_Pq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

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

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

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
