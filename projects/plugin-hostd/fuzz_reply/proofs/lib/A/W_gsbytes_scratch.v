(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the GS-FREE arm of segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x83940 .. 0x839b8, gesture_seen's "an END line whose key is held at slot n",
   relay.c:116-119 inlined).  The statement is lib/A/W_drain_gs.v's gs_free_stmt, proved here; the Section
   header below is lib/A/W_drain_cx.v's, verbatim.

   GF (0x83940) -> DLN (S q) (0x836f4), one call and two stores:
     0x83940  lbu a0, 0(s3)   the shadow byte of &s->held[n]; the report arm 0x83d14 is NOT taken
     0x83948  ld  a0, 0(s10)  a0 = s->held[n], the held key's text
     0x8394c  jal free        CALL free #2, through AFREE (afree_cf_rule) on the inner journal
     0x83950  the shadow bytes of &s->held (8(sp)) and &s->nheld (72(sp)); both report arms NOT taken
     0x83974  a3 = s->nheld;  0x83980  sw: s->nheld = nheld - 1
     0x83984  a0 = &s->held[nheld - 1], a1 = &s->held[n], both shadow-checked
     0x839b0  ld; 0x839b4 sd: s->held[n] = s->held[nheld - 1]
     0x839b8  j 0x836f4 = DLN (S q).
   The model step is drain_b_c.seen_tr's GEnd/Some branch: the request RFree (|key| + 1), the held keys
   swap_remove'd at n, the array size unchanged (W_drain_gs.v gs_seen_end_old). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_gsfree_scratch.v; 85 of its 240 lines of code are new or changed and 3225 lines of the source are left out. *)
(* scratch, owned by DrGs' byte-image hand. DELETE BEFORE COMMIT.
   The byte-image readers and writers of drain's GS segment (lib/A/W_drain_gs.v): the two cells of the relay
   entry that gesture_seen writes (s->held at SA + 40, 8 bytes; s->nheld at SA + 48, 4 bytes) and the held
   array's slots (lib/Prog/gestures_end_b_c.v key_ptrs, 8 bytes per key).  All of it is byte algebra over
   lib/Reusable/YI00.v garr8, lib/Reusable/YI04.v val_mem / le_byte and lib/Prog/RelayRep.v entry_bytes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx W_drain_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).

Definition gs_k0 : Z * list byte * list byte := (0, [], []).

(* ---------------------------------------------------------------------------------------------------------
   helpers: byte lists, their lengths, and the garr8 frame
   --------------------------------------------------------------------------------------------------------- *)

Lemma gs_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma gs_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma gs_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.

Lemma gs_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

(* the k-th byte of an n-byte little-endian image of v is le_byte v n k (val_mem's le_byte, YO0f's) *)
Lemma gs_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, gs_nth_zle by exact Hk. rewrite gs_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma gs_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.

Lemma gs_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.

(* a byte run whose ASan view is unchanged keeps its image *)
Lemma gs_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (1) a little-endian field: val_mem from garr8 of its bytes, and back
   --------------------------------------------------------------------------------------------------------- *)

Lemma gs_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite gs_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite gs_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma gs_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite gs_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite gs_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite gs_le_byte1 by exact Hr. reflexivity.
Qed.

Lemma gs_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Lemma gs_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac gs_len := rewrite ?length_app, ?gs_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].
Ltac gs_len_in H := rewrite ?length_app, ?gs_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes in H;
  cbn [length] in H.

(* ---------------------------------------------------------------------------------------------------------
   (2) the two cells of the relay entry that gesture_seen writes
   RelayRep.v:21 entry_bytes e = le4 fd ++ le4 eof ++ le4 skip ++ pad1 ++ le8 buf ++ le8 used ++ le8 cap
                                 ++ le8 hp ++ le4 nheld ++ pad2, so s->held is at + 40 and s->nheld at + 48.
   --------------------------------------------------------------------------------------------------------- */ *)

Lemma gs_entry_hp : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_hp e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 40) 8 (re_hp e).
Proof.
intros W m SA e Hp1 Hhp H.
unfold entry_bytes in H. rewrite !gs_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gs_le8_bytes (re_hp e) Hhp) in H.
apply (gs_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hhp|].
apply (gs_garr8_at _ _ _ _ H). gs_len. lia.
Qed.

Lemma gs_entry_nheld : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_nheld e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 48) 4 (re_nheld e).
Proof.
intros W m SA e Hp1 Hnh H.
unfold entry_bytes in H. rewrite !gs_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gs_le4_bytes (re_nheld e) Hnh) in H.
apply (gs_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hnh|].
apply (gs_garr8_at _ _ _ _ H). gs_len. lia.
Qed.

(* the entry after the two stores: every other byte of the 56 is unchanged *)
Lemma gs_entry_store : forall (W : world SEGS) m (W' : world SEGS) m' SA e e',
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
re_fd e' = re_fd e -> re_eof e' = re_eof e -> re_skip e' = re_skip e -> re_pad1 e' = re_pad1 e ->
re_buf e' = re_buf e -> re_used e' = re_used e -> re_cap e' = re_cap e -> re_pad2 e' = re_pad2 e ->
0 <= re_hp e' < 2 ^ 64 -> 0 <= re_nheld e' < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W' m') (SA + 40) 8 (re_hp e') ->
val_mem SEGS (arm W' m') (SA + 48) 4 (re_nheld e') ->
(forall x, SA <= x < SA + 40 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 52 <= x < SA + 56 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') SA (bzs (entry_bytes e')).

Proof.
intros W m W' m' SA e e' Hp1 Hp2 Efd Eeof Eskip Ep1 Ebuf Eused Ecap Ep2 Hhp Hnh H Vhp Vnh K1 K2.
unfold entry_bytes in H |- *. rewrite Efd, Eeof, Eskip, Ep1, Ebuf, Eused, Ecap, Ep2.
rewrite !gs_bzs_app, !app_assoc in H |- *.
apply garr8_app in H as [H HP2]. apply garr8_app in H as [H _]. apply garr8_app in H as [HZ _].
rewrite (gs_le8_bytes (re_hp e') Hhp), (gs_le4_bytes (re_nheld e') Hnh).
apply garr8_app. split; [apply garr8_app; split; [apply garr8_app; split|]|].
- apply (gs_garr8_kept W m); [exact HZ|]. intros x Hx. apply K1. gs_len_in Hx. lia.
- apply (gs_garr8_at _ (SA + 40)); [|gs_len; lia].
  apply gs_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hhp | exact Vhp].
- apply (gs_garr8_at _ (SA + 48)); [|gs_len; lia].
  apply gs_garr8_of_val; [change (8 * Z.of_nat 4) with 32; exact Hnh | exact Vnh].
- apply (gs_garr8_at _ (SA + 52)); [|gs_len; lia].
  apply (gs_garr8_kept W m).
  + apply (gs_garr8_at _ _ _ _ HP2). gs_len. lia.
  + intros x Hx. apply K2. gs_len_in Hx. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (3) the held array: one 8-byte slot per key (gestures_end_b_c.v:29 key_ptrs)
   --------------------------------------------------------------------------------------------------------- *)

Lemma gs_ptrs_nil : key_ptrs [] = [].
Proof. reflexivity. Qed.

Lemma gs_ptrs_cons : forall k ks, key_ptrs (k :: ks) = Mem.le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs ks.
Proof. reflexivity. Qed.

Lemma gs_ptrs_split : forall a b, key_ptrs (a ++ b) = key_ptrs a ++ key_ptrs b.
Proof. intros a b. unfold key_ptrs. rewrite map_app, concat_app. reflexivity. Qed.

(* the slot of key x, between the slots of the keys before it and after it *)
Lemma gs_ptrs_mid : forall a x b,
key_ptrs (a ++ x :: b) = key_ptrs a ++ Mem.le8 (Z_to_bv 64 (key_addr x)) ++ key_ptrs b.
Proof. intros a x b. rewrite gs_ptrs_split, gs_ptrs_cons. reflexivity. Qed.

(* the slot count, for the array's size bookkeeping *)
Lemma gs_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
rewrite gs_ptrs_cons, length_app, Mem.length_le8, IH. cbn [length]. lia.
Qed.

Lemma gs_nth_last : forall (l : list (Z * list byte * list byte)) z d, nth (length (l ++ [z]) - 1) (l ++ [z]) d = z.
Proof.
intros l z d. rewrite length_app. cbn [length]. replace (length l + 1 - 1)%nat with (length l) by lia. apply nth_middle.
Qed.

Lemma gs_ptrs_slot : forall (W : world SEGS) m hp ks i,
(i < length ks)%nat -> 0 <= key_addr (nth i ks gs_k0) < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W m) (hp + 8 * Z.of_nat i) 8 (key_addr (nth i ks gs_k0)).
Proof.
intros W m hp ks i Hi Hv H.
destruct (nth_split ks gs_k0 Hi) as (l1 & l2 & E & L).
rewrite E, gs_ptrs_mid, !gs_bzs_app in H.
apply garr8_app in H as [_ H]. apply garr8_app in H as [H _].
rewrite (gs_le8_bytes _ Hv) in H.
apply (gs_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (gs_garr8_at _ _ _ _ H). rewrite gs_bzs_len, gs_ptrs_len, L. lia.
Qed.

(* a begin not held: the new key's pointer is appended at slot |ks| *)
Lemma gs_ptrs_app : forall (W : world SEGS) m (W' : world SEGS) m' hp ks k,
0 <= key_addr k < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W' m') (hp + 8 * Z.of_nat (length ks)) 8 (key_addr k) ->
(forall x, hp <= x < hp + 8 * Z.of_nat (length ks) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') hp (bzs (key_ptrs (ks ++ [k]))).
Proof.
intros W m W' m' hp ks k Hk H V K.
rewrite gs_ptrs_split, gs_ptrs_cons, gs_ptrs_nil, app_nil_r, gs_bzs_app.
apply garr8_app. split.
- apply (gs_garr8_kept W m); [exact H|]. intros x Hx. apply K. rewrite gs_bzs_len, gs_ptrs_len in Hx. lia.
- apply (gs_garr8_at _ (hp + 8 * Z.of_nat (length ks))); [|rewrite gs_bzs_len, gs_ptrs_len; lia].
  rewrite (gs_le8_bytes _ Hk). apply gs_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hk | exact V].
Qed.

(* an end held at slot n: the last slot's pointer is written into slot n and the array is one slot shorter *)
Lemma gs_ptrs_swap : forall (W : world SEGS) m (W' : world SEGS) m' hp ks n,
(n < length ks)%nat -> 0 <= key_addr (nth (length ks - 1) ks gs_k0) < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W' m') (hp + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks gs_k0)) ->
(forall x, hp <= x < hp + 8 * Z.of_nat (length ks) ->
   ~ (hp + 8 * Z.of_nat n <= x < hp + 8 * Z.of_nat n + 8) ->
   aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') hp (bzs (key_ptrs (swap_remove gs_k0 n ks))).
Proof.
intros W m W' m' hp ks n Hn Hv H V K.
destruct (nth_split ks gs_k0 Hn) as (a & b & E & L).
set (x := nth n ks gs_k0) in E. clearbody x. subst ks n.
induction b as [|z b' _] using rev_ind.
- (* the held key is the last: the array just loses its last slot *)
  rewrite swap_remove_last.
  rewrite gs_ptrs_split, gs_bzs_app in H. apply garr8_app in H as [H _].
  apply (gs_garr8_kept W m); [exact H|]. intros y Hy. rewrite gs_bzs_len, gs_ptrs_len in Hy.
  apply K; rewrite ?length_app; cbn [length]; lia.
- (* the last key z moves into slot |a| *)
  assert (Ez : nth (length (a ++ x :: b' ++ [z]) - 1) (a ++ x :: b' ++ [z]) gs_k0 = z).
  { replace (a ++ x :: b' ++ [z]) with ((a ++ x :: b') ++ [z]) by (rewrite <- app_assoc; reflexivity).
    apply gs_nth_last. }
  rewrite Ez in Hv, V.
  rewrite swap_remove_mid, gs_ptrs_mid, !gs_bzs_app.
  rewrite gs_ptrs_mid, !gs_bzs_app in H. apply garr8_app in H as [Ha H]. apply garr8_app in H as [_ H].
  rewrite gs_ptrs_split, gs_bzs_app in H. apply garr8_app in H as [Hb _].
  apply garr8_app. split; [|apply garr8_app; split].
  + apply (gs_garr8_kept W m); [exact Ha|]. intros y Hy. rewrite gs_bzs_len, gs_ptrs_len in Hy.
    apply K; rewrite ?length_app; cbn [length]; rewrite ?length_app; cbn [length]; lia.
  + apply (gs_garr8_at _ (hp + 8 * Z.of_nat (length a))); [|rewrite gs_bzs_len, gs_ptrs_len; lia].
    rewrite (gs_le8_bytes _ Hv). apply gs_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hv | exact V].
  + apply (gs_garr8_at _ (hp + 8 * Z.of_nat (length a) + 8)); [|rewrite !gs_bzs_len, gs_ptrs_len, Mem.length_le8; lia].
    apply (gs_garr8_kept W m).
    * apply (gs_garr8_at _ _ _ _ Hb). rewrite !gs_bzs_len, gs_ptrs_len, Mem.length_le8. lia.
    * intros y Hy. rewrite gs_bzs_len, gs_ptrs_len in Hy.
      apply K; rewrite ?length_app; cbn [length]; rewrite ?length_app; cbn [length]; lia.
Qed.

End b.
End a.
