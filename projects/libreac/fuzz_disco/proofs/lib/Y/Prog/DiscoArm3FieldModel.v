(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 163 of its 193 lines of code are new or changed and 515 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/TjLoopCuts.v, with its module paths and module names changed; 218 of its 249 lines of code are new or changed and 162 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProSeat.v, with its module names changed; 312 of its 350 lines of code are new or changed and 211 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldCut.v; 68 of its 105 lines of code are new or changed and 313 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoArm3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma a3f_count : forall (T : list byte) now count os,
  length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (a3_text T now) 9 = Some (count, os) ->
  count = disco_table_c.n_of T /\ 0 <= count <= 8 /\ length os = Z.to_nat count /\
  Forall (fun o => length o = 6%nat) os /\
  Forall (Forall (slot_ser_tokb.tok_inb (a3_text T now))) os /\
  Forall (fun c => 33 <= c <= 255) (a3_text T now) /\ (length (a3_text T now) <= 969)%nat.
Proof.
  intros T now count os LT TOK Hnow JR.
  pose proof (slot_ser_pure.ser_tj_ok T LT TOK) as [TOK' WF].
  destruct (disco_json_lemmas.F1_2_json_read_table reac_disco_table_json_c.box_tok
              (reac_disco_table_json_c.tj_entries T) now slot_ser_pure.ser_tok_ok TOK' WF Hnow) as (os' & JR' & F2).
  change (disco_json_text.table_json_text reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now)
    with (a3_text T now) in JR'.
  rewrite JR in JR'. injection JR' as Ec Eo. subst os'.
  pose proof (slot_ser_pure.ser_tj_len T) as LE. pose proof TOK as (T1 & _). unfold disco_table_c.tbl_T1 in T1.
  pose proof (Forall2_length F2) as LF.
  split; [rewrite Ec, LE; lia|]. split; [rewrite Ec; destruct TOK' as (TL & _); lia|].
  split; [rewrite <- LF, Ec; lia|]. split.
  { clear -F2. induction F2 as [|e o E O V F IH]; constructor; [|exact IH].
    apply (f_equal (@length _)) in V. unfold disco_json_lemmas.obj_view in V. rewrite length_map in V. exact V. }
  split; [exact (slot_ser_tokb.json_read_inb _ _ _ _ JR)|]. split.
  { exact (slot_ser_pure.ser_text_g33 reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now
             slot_ser_pure.ser_tok_ok WF Hnow). }
  exact (disco_json_lemmas.C7_text_bound reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now
           slot_ser_pure.ser_tok_ok TOK' WF Hnow).
Qed.

Lemma a3f_tj_nth : forall T k, 0 <= k < disco_table_c.n_of T ->
  nth_error (reac_disco_table_json_c.tj_entries T) (Z.to_nat k) = Some (reac_disco_table_json_c.tj_entry T k).
Proof.
  intros T k Hk. unfold reac_disco_table_json_c.tj_entries. rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 (Z.to_nat (disco_table_c.n_of T))) 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn [option_map]. f_equal. f_equal. lia.
Qed.

Lemma a3f_obj : forall (T : list byte) now count os k,
  length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (a3_text T now) 9 = Some (count, os) -> 0 <= k < count ->
  let X := a3_text T now in let o := nth (Z.to_nat k) os [] in let e := reac_disco_table_json_c.tj_entry T k in
  (forall j, 0 <= j < count ->
     disco_json_reader_model.jtok_is X (nth 0 o disco_json_reader_model.tok_none) 1
       (disco_json_text.mac_text (disco_json_text.e_mac (reac_disco_table_json_c.tj_entry T j))) = (j =? k)) /\
  disco_json_reader_model.jtok_is X (nth 1 o disco_json_reader_model.tok_none) 1
    (disco_json_text.rolename (disco_json_text.e_role e)) = true /\
  disco_json_reader_model.jtok_is X (nth 2 o disco_json_reader_model.tok_none) 1
    (fst (disco_json_text.model_of reac_disco_table_json_c.box_tok e)) = true /\
  disco_json_reader_model.jtok_is X (nth 3 o disco_json_reader_model.tok_none) 1
    (snd (disco_json_text.model_of reac_disco_table_json_c.box_tok e)) = true /\
  disco_json_reader_model.jtok_is X (nth 4 o disco_json_reader_model.tok_none) 3 (disco_json_text.owned_text e) = true /\
  disco_json_reader_model.jtok_is X (nth 5 o disco_json_reader_model.tok_none) 2
    (disco_json_text.dec (disco_json_text.age_of now (disco_json_text.e_last_seen e))) = true.
Proof.
  intros T now count os k LT TOK Hnow JR Hk X o e.
  destruct (a3f_count T now count os LT TOK Hnow JR) as (Ec & Hc & Los & _).
  pose proof (slot_ser_pure.ser_tj_ok T LT TOK) as [TOK' WF].
  assert (JR' : disco_json_reader_model.json_read
                  (disco_json_text.table_json_text reac_disco_table_json_c.box_tok
                     (reac_disco_table_json_c.tj_entries T) now) 9 =
                Some (Z.of_nat (length (reac_disco_table_json_c.tj_entries T)), os)).
  { rewrite slot_ser_pure.ser_tj_len, Z2Nat.id by lia. rewrite <- Ec. exact JR. }
  assert (Eo : nth_error os (Z.to_nat k) = Some o) by (apply nth_error_nth'; lia).
  pose proof (a3f_tj_nth T k ltac:(lia)) as Ek.
  destruct (disco_json_lemmas.F1_3_serialise_finds reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T)
              now os slot_ser_pure.ser_tok_ok TOK' WF Hnow JR' (Z.to_nat k) _ _ Eo Ek)
    as (M & R & Mo & Wd & O & A).
  split; [|exact (conj R (conj Mo (conj Wd (conj O A))))].
  intros j Hj. specialize (M (Z.to_nat j) (reac_disco_table_json_c.tj_entry T j) (a3f_tj_nth T j ltac:(lia))).
  destruct (Z.eqb_spec j k) as [->|N]; [apply M; reflexivity|].
  apply not_true_is_false. intros E. apply M in E. lia.
Qed.

Lemma a3f_quot : forall x, 0 <= x < 2 ^ 64 -> x * a3f_KDV / 2 ^ 64 / 2 ^ 18 = x / 1000000.
Proof.
  intros x Hx. rewrite Z.div_div by lia. unfold a3f_KDV.
  pose proof (Z.div_mod x 1000000 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 1000000 ltac:(lia)) as M.
  set (q := x / 1000000) in *. set (r := x mod 1000000) in *.
  symmetry. apply Z.div_unique with (r := x * 4835703278458516699 - q * 4835703278458516698824704); [left|ring].
  split; lia.
Qed.

Lemma a3f_count_y : a3f_count_stmt.
Proof. exact a3f_count. Qed.
