(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: loop 2 of the image-B (fuzz_reply.asan-ubsan) walk of check_shape_ends (0x85770),
   the `g_gone <> 0` loop from its head 0x858ac (W_cshe_epi.v cshe_l2_in) to the epilogue's entry 0x8592c
   (W_cshe_epi.v cshe_out_B).  A segment lemma of BCheckShapeEvent's pb_check_shape_ends.  A NEW walk over
   lib/B/W_listing.v: B's loop is not A's (B reads the vector again in every turn, has four UBSan trap edges on the
   record's address, and CALLS list_drop at 0x85924 where A inlines free + __asan_memmove).  Structure after
   lib/A/W_cshe_l2w.v (a working branch d6e8218b728: the invariant l2_mem / l2_inv, the record fields, the source
   kept across a call) and lib/A/W_cshe_l2.v (a working branch 4bd30a14d29: the filter lemmas). *)
(* One turn, m + 1 records not yet examined (s3 = m + 1), the record v[m]:
     0x858ac  lbu (s2) (the shadow byte of &held.v), ld a1,0(s1) (v), addiw s3,s3,-1, a0 = v + 16 m   (l2_head)
     0x858c4  the traps bltu a0,a1 (refuted by trap_ptr_wrap_atom), snez/seqz/xor/beqz, beqz a1, andi a0,7
              (decided from the seat's facts), the shadow checks of v[m]'s two words, a0 = v[m].s,
              a1 = v[m].n, a2 = PF, has_prefix (HP)                                                   (l2_ent)
     0x85918  beqz a0: no match -> 0x85928; a match: list_drop(&held, m) (LDROP at the list head's own globals
              [(HA + 80, 16)], lifted to G by ajournal_gx_G_mono)
     0x85928  bgtz s3: back to the head while records are left, else the epilogue's entry 0x8592c        (l2_tail)
   The invariant (l2_mem m) after the turn of index m: the held list is the first m records of the entry's list
   followed by the records past them without the prefix; the dropped records are those with it, and their
   blocks left ablocks (one per list_drop); the journal, the rest of the source, the meter, the frame, and errno's
   view (cshe_out_B's last conjunct). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_frame_b W_shadow_pin W_traps W_cshe_epi.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel.
(* The sink-instance guard, after every import (MERGE.md (sha256 0694aca87ccd; internal record) item 3) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the model's side (CheckRep) *)
Lemma l2_kp_cons : forall (P : list byte) (r : Z * list byte) (l : list (Z * list byte)),
filter (fun x => negb (CheckRep.prefixb P (snd x))) (r :: l) =
if CheckRep.prefixb P (snd r) then filter (fun x => negb (CheckRep.prefixb P (snd x))) l
else r :: filter (fun x => negb (CheckRep.prefixb P (snd x))) l.
Proof.
intros P r l. rewrite list_basics.list.filter_cons.
destruct (CheckRep.prefixb P (snd r)) eqn:E; match goal with |- context [decide ?X] => destruct (decide X) as [D|D] end;
  cbn in D |- *; first [reflexivity | (exfalso; apply D; rewrite E; exact I) | (rewrite E in D; contradiction)
  | contradiction].
Qed.
Lemma l2_ds_cons : forall (P : list byte) (r : Z * list byte) (l : list (Z * list byte)),
filter (fun x => CheckRep.prefixb P (snd x)) (r :: l) =
if CheckRep.prefixb P (snd r) then r :: filter (fun x => CheckRep.prefixb P (snd x)) l
else filter (fun x => CheckRep.prefixb P (snd x)) l.
Proof.
intros P r l. rewrite list_basics.list.filter_cons.
destruct (CheckRep.prefixb P (snd r)) eqn:E; match goal with |- context [decide ?X] => destruct (decide X) as [D|D] end;
  cbn in D |- *; first [reflexivity | (exfalso; apply D; rewrite E; exact I) | (rewrite E in D; contradiction)
  | contradiction].
Qed.
Lemma l2_filter_len : forall (f : Z * list byte -> bool) l, (length (filter (fun x => f x) l) <= length l)%nat.
Proof.
intros f l. induction l as [|r l IH]; [cbn; lia|]. rewrite list_basics.list.filter_cons.
destruct (decide _); cbn [length]; lia.
Qed.
Lemma l2_in_filter : forall (f : Z * list byte -> bool) l x, In x (filter (fun y => f y) l) -> In x l.
Proof.
intros f l x. induction l as [|r l IH]; cbn [In]; [intros H; exact H|].
rewrite list_basics.list.filter_cons. destruct (decide _) as [D|D].
- cbn [In]. intros [H|H]; [left; exact H | right; exact (IH H)].
- intros H. right. exact (IH H).
Qed.
Lemma l2_nodup_filter : forall (Y : Type) (g : Z * list byte -> Y) (f : Z * list byte -> bool) l,
List.NoDup (map g l) -> List.NoDup (map g (filter (fun r => f r) l)).
Proof.
intros Y g f l. induction l as [|r l IH]; [intros _; rewrite list_basics.list.filter_nil; constructor|].
intros ND. rewrite list_basics.list.filter_cons. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
destruct (decide _) as [D|D]; [|exact (IH ND)].
cbn [map]. apply List.NoDup_cons_iff. split; [|exact (IH ND)].
intros Hin. apply NI. apply in_map_iff in Hin as (x & Ex & Hx). rewrite <- Ex. apply in_map.
exact (l2_in_filter f l x Hx).
Qed.
Lemma l2_skipn_nth : forall (l : list (Z * list byte)) (k : nat), (k < length l)%nat ->
skipn k l = nth k l (0, []) :: skipn (S k) l.
Proof.
intros l. induction l as [|x l IH]; intros [|k] Hk; cbn [length] in Hk; try lia; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.
Lemma l2_firstn_nth : forall (l : list (Z * list byte)) (k : nat), (k < length l)%nat ->
firstn (S k) l = firstn k l ++ [nth k l (0, [])].
Proof.
intros l. induction l as [|x l IH]; intros [|k] Hk; cbn [length] in Hk; try lia; [reflexivity|].
cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
Lemma l2_drop_split : forall {X : Type} (A Bs : list X) x,
firstn (length A) (A ++ x :: Bs) ++ skipn (S (length A)) (A ++ x :: Bs) = A ++ Bs.
Proof. intros X A. induction A as [|a A IH]; intros Bs x; cbn; [reflexivity | f_equal; apply IH]. Qed.
(* one record further down the list: a miss keeps it, a hit drops it *)
Lemma l2_kp_miss : forall (P : list byte) (R : list (Z * list byte)) m, (m < length R)%nat ->
CheckRep.prefixb P (snd (nth m R (0, []))) = false ->
firstn (S m) R ++ filter (fun x => negb (CheckRep.prefixb P (snd x))) (skipn (S m) R) =
firstn m R ++ filter (fun x => negb (CheckRep.prefixb P (snd x))) (skipn m R).
Proof.
intros P R m Hm E. rewrite (l2_firstn_nth R m Hm), (l2_skipn_nth R m Hm), l2_kp_cons, E, <- app_assoc. reflexivity.
Qed.
Lemma l2_ds_miss : forall (P : list byte) (R : list (Z * list byte)) m, (m < length R)%nat ->
CheckRep.prefixb P (snd (nth m R (0, []))) = false ->
filter (fun x => CheckRep.prefixb P (snd x)) (skipn m R) = filter (fun x => CheckRep.prefixb P (snd x)) (skipn (S m) R).
Proof. intros P R m Hm E. rewrite (l2_skipn_nth R m Hm), l2_ds_cons, E. reflexivity. Qed.
Lemma l2_kp_hit : forall (P : list byte) (R : list (Z * list byte)) m, (m < length R)%nat ->
CheckRep.prefixb P (snd (nth m R (0, []))) = true ->
filter (fun x => negb (CheckRep.prefixb P (snd x))) (skipn m R) =
filter (fun x => negb (CheckRep.prefixb P (snd x))) (skipn (S m) R).
Proof. intros P R m Hm E. rewrite (l2_skipn_nth R m Hm), l2_kp_cons, E. reflexivity. Qed.
Lemma l2_ds_hit : forall (P : list byte) (R : list (Z * list byte)) m, (m < length R)%nat ->
CheckRep.prefixb P (snd (nth m R (0, []))) = true ->
filter (fun x => CheckRep.prefixb P (snd x)) (skipn m R) =
nth m R (0, []) :: filter (fun x => CheckRep.prefixb P (snd x)) (skipn (S m) R).
Proof. intros P R m Hm E. rewrite (l2_skipn_nth R m Hm), l2_ds_cons, E. reflexivity. Qed.
(* the held list after list_drop of record m (ldrop_list, W_contract.v) *)
Lemma l2_ldrop_recs : forall (H1 : hlist) (R K : list (Z * list byte)) m, (S m <= length R)%nat ->
hl_recs H1 = firstn (S m) R ++ K -> hl_recs (ldrop_list H1 m) = firstn m R ++ K.
Proof.
intros H1 R K m Hm E. unfold ldrop_list. cbn [HarnessRep.hl_recs]. rewrite E.
assert (HL : length (firstn (S m) R) = S m) by (rewrite length_firstn; lia).
rewrite firstn_app, skipn_app, HL, firstn_firstn.
replace (Nat.min m (S m)) with m by lia. replace (m - S m)%nat with 0%nat by lia.
replace (S m - S m)%nat with 0%nat by lia. rewrite (skipn_all2 (firstn (S m) R)) by lia. cbn [firstn skipn app].
rewrite app_nil_r. reflexivity.
Qed.
Lemma l2_nodup_mid4 : forall (L1 L2 L3 L4 Ma Mb : list Z) x,
List.NoDup (L1 ++ L2 ++ L3 ++ L4 ++ Ma ++ x :: Mb) -> List.NoDup (L1 ++ L2 ++ L3 ++ L4 ++ Ma ++ Mb).
Proof.
intros L1 L2 L3 L4 Ma Mb x H.
replace (L1 ++ L2 ++ L3 ++ L4 ++ Ma ++ Mb) with ((L1 ++ L2 ++ L3 ++ L4 ++ Ma) ++ Mb) by (rewrite <- !app_assoc; reflexivity).
apply (List.NoDup_remove_1 _ _ x). rewrite <- !app_assoc. exact H.
Qed.
Lemma l2_lb_drop : forall (l : hlist) i x A Bs, hl_recs l = A ++ x :: Bs -> length A = i -> 0 < hl_cap l ->
list_blocks l = [hl_v l] ++ map fst A ++ fst x :: map fst Bs /\ list_blocks (ldrop_list l i) = [hl_v l] ++ map fst A ++ map fst Bs.
Proof.
intros l i x A Bs E HA Hc. assert (Ec : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
unfold list_blocks, ldrop_list. cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs]. rewrite Ec, E, <- HA, l2_drop_split.
rewrite !map_app. cbn [map]. split; reflexivity.
Qed.
Lemma l2_nodup_hs_drop : forall (h0 : hsrc) i, (i < length (hl_recs (hs_held h0)))%nat -> 0 < hl_cap (hs_held h0) ->
NoDup (hs_blocks h0) -> NoDup (hs_blocks (CheckRep.set_held h0 (ldrop_list (hs_held h0) i))).
Proof.
intros h0 i Hi Hc ND. apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup.
destruct (nth_split (hl_recs (hs_held h0)) (0, []) Hi) as (A & Bs & Hsp & HlA).
set (x := nth i (hl_recs (hs_held h0)) (0, [])) in Hsp. clearbody x.
destruct (l2_lb_drop (hs_held h0) i x A Bs Hsp HlA Hc) as [E1 E2].
unfold hs_blocks in *. cbn [CheckRep.set_held hs_pending hs_partial hs_expected hs_held].
rewrite E2. rewrite E1 in ND. exact (l2_nodup_mid4 _ _ _ _ _ _ (fst x) ND).
Qed.
Lemma l2_set_held_twice : forall (h0 : hsrc) (H1 H2 : hlist),
CheckRep.set_held (CheckRep.set_held h0 H1) H2 = CheckRep.set_held h0 H2.
Proof. intros h0 H1 H2. reflexivity. Qed.
(* a byte string as the walk reads it (lib/A/W_check_shape_ends.v cshe_bytes, a working branch d6e8218b728) *)
Lemma l2_u8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma l2_nth_bzs : forall (l : list byte) (j : nat), nth j (HarnessRep.bzs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j. unfold HarnessRep.bzs, HarnessRep.bz. rewrite <- (map_nth bv_unsigned l (Z_to_bv 8 0) j). reflexivity.
Qed.
Lemma l2_bzs_inj : forall l1 l2 : list byte, HarnessRep.bzs l1 = HarnessRep.bzs l2 -> l1 = l2.
Proof.
induction l1 as [|a l1 IH]; intros [|b l2] H; unfold HarnessRep.bzs in H; cbn [map] in H;
  try discriminate H; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma l2_leqb : forall a b : list Z, RelayModel.list_eqb a b = true <-> a = b.
Proof.
intros a b. unfold RelayModel.list_eqb. destruct (list_eq_dec Z.eq_dec a b) as [E|E].
- split; [intros _; exact E | intros _; reflexivity].
- split; [intros Hc; discriminate Hc | intros Hc; exfalso; exact (E Hc)].
Qed.
Lemma l2_text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Definition l2_bytes (W : world SEGS) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
forall t, 0 <= t < Z.of_nat (length l) ->
aview SEGS (w_H W) mem (a + t) = Some (bv_unsigned (nth (Z.to_nat t) l (Z_to_bv 8 0))).
Lemma l2_bytes_of_garr8 : forall (W : world SEGS) mem a (l : list byte),
garr8 SEGS (mrestrict (w_H W) mem) a (HarnessRep.bzs l) -> l2_bytes W mem a l.
Proof.
intros W mem a l Hg t Ht.
assert (HL : length (HarnessRep.bzs l) = length l) by (unfold HarnessRep.bzs; apply length_map).
assert (Hj : (Z.to_nat t < length (HarnessRep.bzs l))%nat) by lia.
unfold aview. replace (a + t) with (a + Z.of_nat (Z.to_nat t)) by lia.
rewrite (garr8_mbyte SEGS _ a _ (Z.to_nat t) Hg Hj). cbn [option_map].
destruct (Hg (Z.to_nat t) Hj) as (_ & Hr). rewrite (l2_u8 _ Hr). f_equal. apply l2_nth_bzs.
Qed.
(* has_prefix's answer on a record's text is exactly the plain model's prefixb (W_check_shape_ends.v cshe_prefixb_iff) *)
Lemma l2_prefixb_iff : forall (W : world SEGS) mem (q PF : Z) (x P : list byte),
l2_bytes W mem q (x ++ [Z_to_bv 8 0]) -> l2_bytes W mem PF (P ++ [Z_to_bv 8 0]) ->
((Z.of_nat (length P) <= Z.of_nat (length x) /\ hp_prefix_of W mem q PF (Z.of_nat (length P))) <->
 CheckRep.prefixb P x = true).
Proof.
intros W mem q PF x P Hx HP.
assert (LX : forall t, 0 <= t < Z.of_nat (length x) ->
  aview SEGS (w_H W) mem (q + t) = Some (bv_unsigned (nth (Z.to_nat t) x (Z_to_bv 8 0)))).
{ intros t Ht. rewrite (Hx t ltac:(rewrite length_app; cbn [length]; lia)).
  do 2 f_equal. apply app_nth1. lia. }
assert (LP : forall t, 0 <= t < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + t) = Some (bv_unsigned (nth (Z.to_nat t) P (Z_to_bv 8 0)))).
{ intros t Ht. rewrite (HP t ltac:(rewrite length_app; cbn [length]; lia)).
  do 2 f_equal. apply app_nth1. lia. }
unfold CheckRep.prefixb. split.
- intros (Hle & Hpre). apply andb_true_iff. split; [apply Nat.leb_le; lia|].
  apply l2_leqb. f_equal.
  assert (LF : length (firstn (length P) x) = length P) by (rewrite length_firstn; lia).
  assert (NX : forall t, (t < length P)%nat -> nth t x (Z_to_bv 8 0) = nth t (firstn (length P) x) (Z_to_bv 8 0)).
  { intros t Ht. transitivity (nth t (firstn (length P) x ++ skipn (length P) x) (Z_to_bv 8 0));
    [rewrite firstn_skipn; reflexivity | apply app_nth1; lia]. }
  apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [exact LF|].
  intros t Ht. rewrite LF in Ht. rewrite <- (NX t Ht).
  specialize (Hpre (Z.of_nat t) ltac:(lia)).
  rewrite (LX (Z.of_nat t) ltac:(lia)), (LP (Z.of_nat t) ltac:(lia)) in Hpre.
  injection Hpre as Hpre. rewrite !Nat2Z.id in Hpre. apply bv_eq. exact Hpre.
- intros Hb. apply andb_true_iff in Hb as [Hb1 Hb2]. apply Nat.leb_le in Hb1. apply l2_leqb in Hb2.
  apply l2_bzs_inj in Hb2.
  assert (NX : forall t, (t < length P)%nat -> nth t x (Z_to_bv 8 0) = nth t (firstn (length P) x) (Z_to_bv 8 0)).
  { intros t Ht. transitivity (nth t (firstn (length P) x ++ skipn (length P) x) (Z_to_bv 8 0));
    [rewrite firstn_skipn; reflexivity | apply app_nth1; rewrite length_firstn; lia]. }
  split; [lia|]. intros t Ht.
  rewrite (LX t ltac:(lia)), (LP t ltac:(lia)). do 2 f_equal.
  rewrite (NX (Z.to_nat t) ltac:(lia)), Hb2. reflexivity.
Qed.
(* the vector's records as 8-byte cells (W_cshe_l2w.v l2_rec_fields) *)
Lemma l2_garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
garr8 SEGS m a (HarnessRep.bzs (word_to_le_bytes 8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hl : length (HarnessRep.bzs (word_to_le_bytes 8 w)) = 8%nat)
by (unfold HarnessRep.bzs; rewrite length_map; apply length_N_to_le_bytes).
rewrite (garr8_mbyte SEGS m a _ k H ltac:(lia)). f_equal.
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned w) k Hk (bv_unsigned_in_range 64 w)) as Hn.
rewrite Z_to_bv_bv_unsigned in Hn.
unfold HarnessRep.bzs.
replace (nth k (map HarnessRep.bz (word_to_le_bytes 8 w)) 0)
with (HarnessRep.bz (nth k (word_to_le_bytes 8 w) (Z_to_bv 8 0))).
2: { rewrite <- (map_nth HarnessRep.bz). apply nth_indep. rewrite length_map, length_N_to_le_bytes. exact Hk. }
rewrite (nth_error_nth _ _ _ Hn). unfold HarnessRep.bz. apply Z_to_bv_bv_unsigned.
Qed.
Lemma l2_rec_fields : forall B ly S W mem LA l lines j,
alist_at B ly S W mem LA l lines -> (j < length (HarnessRep.hl_recs l))%nat ->
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j) 8
  (fst (nth j (HarnessRep.hl_recs l) (0, [])) mod 2 ^ 64) /\
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) 8
  (Z.of_nat (length (snd (nth j (HarnessRep.hl_recs l) (0, [])))) mod 2 ^ 64).
Proof.
intros B ly S W mem LA l lines j HA Hj.
destruct HA as (_ & _ & _ & _ & Hcap & Hv & _).
destruct Hv as [(Hc0 & _) | (_ & _ & _ & Hg)].
{ unfold HarnessRep.hl_n in Hcap. lia. }
destruct (nth_split (HarnessRep.hl_recs l) (0, []) Hj) as (l1 & l2 & Hsp & Hl1).
set (r := nth j (HarnessRep.hl_recs l) (0, [])) in *.
rewrite Hsp in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold HarnessRep.bzs in Hg. rewrite !map_app in Hg. rewrite <- !app_assoc in Hg.
apply garr8_app in Hg as [_ Hg]. rewrite length_map, l2_text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 Hg]. apply garr8_app in Hg as [H2 _].
rewrite length_map, length_N_to_le_bytes in H2.
apply l2_garr8_val_mem8 in H1. apply l2_garr8_val_mem8 in H2.
rewrite Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1, H2 by lia.
split; [exact H1|]. replace (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) with (HarnessRep.hl_v l + 16 * Z.of_nat j + Z.of_nat 8) by lia.
exact H2.
Qed.
(* writability across a step that keeps presence (W_cshe_l2w.v l2_writable_kept_w) *)
Lemma l2_writable_kept_w : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m' ) a.
Proof.
intros W W' m m' a Hp Hh Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
- rewrite (Hh _ EH') in Hw. exact Hw.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma l2_vm_keep : forall (W W' : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v.
Proof.
intros W W' m m' a n v Hk Hv i Hi. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat i) (Hk (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.
Lemma l2_g8_keep : forall (W W' : world SEGS) m m' a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W m) a l -> garr8 SEGS (arm W' m') a l.
Proof.
intros W W' m m' a l Hk Hg. apply (garr8_frame SEGS (arm W m) (arm W' m') a l Hg).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (Hk x Hx).
Qed.
Lemma l2_shv_sub : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma l2_amem_of_app : forall p n, in_app p n -> amem_range p n.
Proof.
intros p n (H1 & H2). pose proof ASAN_CEIL_range as AC.
unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
(* the token engine's shadow address of atom m + c, with the shadow base in atom 21 (s5) *)
Lemma l2_U_sh : forall E m c x, ew E m = Z_to_bv 64 x -> ew E 21 = Z_to_bv 64 SB -> 0 <= x < 2 ^ 47 -> x + c < 2 ^ 47 -> 0 <= x + c ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0)) = (x + c) / 8 + SB.
Proof.
intros E m c x Hm H21 Hx Hc Hc0.
rewrite !U_SAlu, (U_atom_off E m x c Hm) by lia. rewrite (U_atom E 21 SB H21) by (unfold SB; lia). rewrite U_lit by lia.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
assert (D : 0 <= (x + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. unfold SB. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma l2_wrap_add : forall x c y, x + c = y -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 y.
Proof.
intros x c y <-. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* the address the head computes: a0 = ((s3 << 4) - 16) + v with s3 = m + 1, and s3 - 1 *)
Lemma l2_addr_val : forall v m, 0 <= m < 2 ^ 26 -> 0 <= v < 2 ^ 47 ->
alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_SLL (Z_to_bv 64 (m + 1)) (Z_to_bv 64 4)) (Z_to_bv 64 (-16))) (Z_to_bv 64 v) =
Z_to_bv 64 (v + 16 * m).
Proof.
intros v m Hm Hv. rewrite !zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
change (4 mod 2 ^ 64) with 4. change (Z.land 4 63) with 4. change (-16 mod 2 ^ 64) with (2 ^ 64 - 16).
rewrite ?(Z.mod_small 4 (2 ^ 64)) by lia.
rewrite (Z.mod_small (m + 1)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite !(Z.mod_small ((m + 1) * 16)) by lia. rewrite !(Z.mod_small v) by lia.
rewrite !Z.mod_mod by lia. rewrite Zplus_mod_idemp_l.
replace ((m + 1) * 16 + (2 ^ 64 - 16) + v) with (v + 16 * m + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
apply Z.mod_small. lia.
Qed.
Lemma l2_dec_val : forall m, 0 <= m < 2 ^ 26 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (m + 1)) + -1) = Z_to_bv 64 m.
Proof. intros m Hm. rewrite unsigned_lit_small by lia. f_equal. lia. Qed.

(* ------------------------------------------------------------------ the symbolic states *)
(* The token engine's shadow form: the shadow base SB is in s5 (x21, atom 21). *)
Definition l2_Bx : sv := SOff 21 0.
Definition l2_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the two inner cut points: 0x858c4 (a0 = &v[m], a1 = v, s3 = m) and 0x85928 (bgtz s3) *)
Definition A_l2e : Z := AF_fr_check_shape_ends + 0x154.
Definition A_l2t : Z := AF_fr_check_shape_ends + 0x1b8.
(* The head 0x858ac: s2 (x18) pinned to the shadow byte of s1 = &held.v (atom 9), the list head's first word v
   (atom 32), s3 = m + 1 (atom 19); the shadow check of &held.v is covered by (9, 0, 16) (azs of HA + 64 .. HA + 96). *)
Definition l2_shv : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 21 0).
Definition l2_hd : YP09.region := YP09.mkRegion (Some 9%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition l2h_sr : list sv := sr_set sr_atoms 18%bv l2_shv.
Definition l2h_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 4096 0x7fff8000 3); (21%nat, mkAF SB SB 0);
(19%nat, mkAF 1 (2 ^ 26) 0); (32%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition ss_l2h : sstate := mkSS A_csheB_l2 l2h_sr [ l2_hd ] None l2h_facts.
Definition l2_SHh : list shent := [ mkSHE 9 0 16 ].
Definition l2_xh (v : Z) : list word := map (Z_to_bv 64) [v].
(* 0x858c4: a0 = &v[m] (atom 10), a1 = v (atom 11), s3 = m (atom 19); the record's two words s (atom 32) and n
   (atom 33); its shadow checks are covered by (10, 0, 16) (the vector's block).  The trap bltu a0,a1 is the one
   edge the runner cannot decide (W_traps.v R5); the null-consistency, non-null and alignment traps are decided from
   atoms 10 and 11's facts (R1). *)
Definition l2_rec : YP09.region := YP09.mkRegion (Some 10%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition l2e_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 4);
(21%nat, mkAF SB SB 0); (19%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_l2e : sstate := mkSS A_l2e sr_atoms [ l2_rec ] None l2e_facts.
Definition l2_SHe : list shent := [ mkSHE 10 0 16 ].
Definition l2_xe (s len : Z) : list word := map (Z_to_bv 64) [s; len].
(* 0x85928: only s3 = m (atom 19) *)
Definition l2t_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (19%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_l2t : sstate := mkSS A_l2t sr_atoms [] None l2t_facts.
Definition l2_SHt : list shent := [].

Lemma l2h_state : forall (W : world SEGS) regs mem SP HA v m,
getr regs 2 = w64 SP -> getr regs 9 = w64 (HA + 80) -> getr regs 18 = w64 ((HA + 80) / 8 + SB) ->
getr regs 19 = w64 m -> getr regs 21 = w64 SB ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 1 <= m <= 2 ^ 26 ->
val_mem SEGS (arm W mem) (HA + 80) 8 v ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (HA + 80) 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (l2_xh v))) ss_l2h
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_csheB_l2)) mem (seg_rom SEGS))) /\
sh_ok SEGS l2_Bx l2_SHh (Eimg (Ereg regs (l2_xh v))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP HA v m H2 H9 H18 H19 H21 HSP HSPa HA8 HAlo HAhi Hv Hv16 Hm Mv HRA.
pose proof pa_B_ok as HBASE.
assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := Eimg (Ereg regs (l2_xh v))).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 m) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (V9 : base_val E (Some 9%nat) = HA + 80) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_l2h. apply pa_entry_st_ok_full.
  + unfold l2h_sr. apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H18. unfold w64, l2_shv. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 21 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 21 0))).
         rewrite (l2_U_sh E 9 0 (HA + 80) E9 E21) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold l2_hd. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (HA + 80) 0 8 (SOff 32 0) v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Mv.
  + apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [l2h_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E21, E19, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, l2_SHh. constructor; [|constructor].
  eapply shent_ok_of_range.
  + exact HRA.
  + unfold l2_Bx. rewrite (U_atom E 21 SB E21) by (unfold SB; lia). reflexivity.
  + rewrite (U_atom E 9 (HA + 80) E9) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
Lemma l2e_state : forall (W : world SEGS) regs mem SP RA v m s len,
getr regs 2 = w64 SP -> getr regs 10 = w64 RA -> getr regs 11 = w64 v -> getr regs 19 = w64 m ->
getr regs 21 = w64 SB ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 ->
4096 <= RA <= 140737479966720 -> RA mod 16 = 0 -> 4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 0 <= m <= 2 ^ 26 ->
in_app RA 16 -> 0 <= s < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
val_mem SEGS (arm W mem) RA 8 s -> val_mem SEGS (arm W mem) (RA + 8) 8 len ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF RA 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (l2_xe s len))) ss_l2e
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_l2e)) mem (seg_rom SEGS))) /\
sh_ok SEGS l2_Bx l2_SHe (Eimg (Ereg regs (l2_xe s len))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP RA v m s len H2 H10 H11 H19 H21 HSP HSPa HR HR16 Hv Hv16 Hm HRapp Hs Hl Ms Ml HRR.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs (l2_xe s len))).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (l2_xe s len) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E10 : ew E 10 = Z_to_bv 64 RA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E19 : ew E 19 = Z_to_bv 64 m) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E32 : ew E 32 = Z_to_bv 64 s) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 len) by exact (EX 1%nat ltac:(lia)).
assert (V10 : base_val E (Some 10%nat) = RA) by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_l2e. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold l2_rec. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite V10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ RA 0 8 (SOff 32 0) s);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Ms.
    * apply (chunk_ok_val SEGS E _ RA 8 8 (SOff 33 0) len);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Ml].
  + apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [l2e_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E10, E11, E21, E19, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, l2_SHe. constructor; [|constructor].
  eapply shent_ok_of_range.
  + exact HRR.
  + unfold l2_Bx. rewrite (U_atom E 21 SB E21) by (unfold SB; lia). reflexivity.
  + rewrite (U_atom E 10 RA E10) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. cbn in Hx. destruct HRapp as [_ [HH | [HH _]]];
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

Section c.
Variable B : asyms.
(* ARx conversion (route (b); A's lib/A/W_check_shape_ends.v Section c on a working branch 4f281bf9308): the
   generic allocator relation ARx with its laws, the placement PST, the room record RP; HP0 (every ghost list is []),
   IMGC (the image's cover) and BLKN (a block's size is >= 0) as W_check_no_loss.v's Section c takes them *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the agreed Section hypotheses (W_cshe_epi.v's list); LDROP is list_drop's contract at any G' with gx_ok / gx_rt /
   ROMS, which B's pb_list_drop (lib/B/W_list_drop.v Section d) gives: at the caller's G the drop keeps no byte of G,
   and cshe_spec puts HA + 64 .. HA + 96 in G, so the walk takes it at the list head's own [(HA + 80, 16)] *)
(* W_frame_x.v Section q's FRMF (the fake frames' alignment: the generic counterpart of YG0s.v frame_facts; at ARi0:
   W_frame_x.FRMF_AR) *)
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
(* the image is off the placement PST: the generic journal's image clause keeps a byte only outside PST *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis LDROP : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_x B PST ARx MT RP G' (BASE + AF_fr_list_drop).
Hypothesis HP : hp_spec_x B PST ARx (BASE + AF_fr_has_prefix).
Hypothesis TL : PALib B.
Hypothesis HGR : gx_ok SEGS B cshe_ro_B.
Hypothesis HGRR : gx_rt B cshe_ro_B.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HGS : forall a, VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Let BR := paj_branch (PI := PI).
(* ---- the walk at the empty ghost list (HP0: every ARx state's ghost list is []): AR0 / AJ0 / AJi0 / AFP0 are cgif's
   AR / journal / inner journal / afn_pre at Hp = [], and each kit lemma the AR walk cites is its _x twin at [] ---- *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x SEGS B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFP0 STK ly S W regs mem md ch := (afn_pre_x SEGS B ARx STK ly S [] W regs mem md ch).
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H;
  hp0a H; clear H.
Local Notation ajournal_gx_AR0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_G_mono0 G0 G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_x SEGS B PST ARx G0 G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_sub0 Hs G0 STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k
    STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1 :=
  (ajournal_gx_sub_x SEGS B PST ARx LAWS Hs G0 STK sp0 XO0 OUT0 FP ly S [] W mem md own lyc Sc [] Wc memc mdc k
     STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 [] W2 mem2 md2 k1).
Local Notation ajournal_gx_init0 G0 XO OUT STK FP ly S W regs mem md ch :=
  (ajournal_gx_init_x SEGS B PST ARx G0 XO OUT STK FP ly S [] W regs mem md ch).
Local Notation afn_pre_at0 STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 :=
  (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k regsc STK1 o ch1).
Local Notation aj_bcmp_gx_at0 pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw :=
  (aj_bcmp_gx_at_x B PST ARx LAWS pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S [] W0 mem md own lyc Sc [] mdc k x y n o
     raw).
Local Notation range_addressable_of_block0 ly S W mem md :=
  (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation shadow_hull_vis_of_block0 ly S W mem md :=
  (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation sep_blocks0 ly S W mem md := (sep_blocks_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation sep_block_frame0 ly S W mem md := (sep_block_frame_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation blk_img0 ly S W mem md := (blk_img_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation frm_img0 ly S W mem md := (frm_img_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation frames_bounds0 ly S W mem md := (frames_bounds_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation amem_range_of_block0 ly S W mem md := (amem_range_of_block_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation rom_pinned_view0 ly S W mem md := (rom_pinned_view_x SEGS B ARx LAWS ly S [] W mem md).
(* cgif's al_blocks at AR0: ARx_blocks_law's six conjuncts and BLKN's size *)
Lemma al0_blocks : forall ly S (W : world SEGS) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* W_kit_x.blk_off_imgP_x's proof, at this file's off_img (lib/B/YCbq.v: IMG_TOP_B = 0x5fc000) *)
Lemma cshe_blk_off_img : forall ly S (W : world SEGS) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) -> off_img p (req_size n).
Proof.
  intros ly S W mem md p n HAR Hin. unfold off_img.
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  pose proof (req_size_pos n (BLKN ly S [] W mem md p n HAR Hin)) as [Q _].
  destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 p) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S [] W mem md (Z.max p 0x10000) HAR _)).
    left. exists p, n. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.
(* W_frame.v's frame_al64 / shadow_hull_vis_of_frame at AR0: W_frame_x's twins over FRMF *)
Lemma frame_al640 : forall ly S (W : world SEGS) mem md cid pos, AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof. intros ly S W mem md cid pos HAR Hin. eapply frame_al64_x; eassumption. Qed.
Lemma shadow_hull_vis_of_frame0 : forall ly S (W : world SEGS) mem md cid pos d n,
  AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= d -> d + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) d n.
Proof. intros ly S W mem md cid pos d n HAR Hin H1 H2 H3. eapply shadow_hull_vis_of_frame_x; eassumption. Qed.
(* W_frame_b.v frm_off_imgB (a fake frame lies off image B's own image [0x10000, 0x5fc000)) at AR0: its proof, with
   IMGC for the image's cover and FRMF for the frame's size *)
Lemma cshe_frm_off_img : forall ly S (W : world SEGS) mem md cid pos, AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos HAR Hin.
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  destruct (FRMF ly S [] W mem md cid pos HAR Hin) as (_ & _ & F64 & _).
  destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max (frame_addr ly cid pos) 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S [] W mem md (Z.max (frame_addr ly cid pos) 0x10000) HAR _)).
    right. left. exists cid, pos. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.
(* errno is an image cell below the allocator's ceiling (PALib's api_env), so no frame of this walk holds it *)
Lemma l2_errno_low : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd.
Proof. exact (proj1 (pal_env B TL)). Qed.

(* ------------------------------------------------------------------ keeping the source (W_cshe_l2w.v) *)
Lemma l2_list_kept : forall ly1 S1 (W1 W2 : world SEGS) m1 m2 LA l lines,
alist_at B ly1 S1 W1 m1 LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (ablocks B ly1 S1) -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly1 S1)).
Proof.
intros ly1 S1 W1 W2 m1 m2 LA l lines HL KH KB. destruct HL as (_ & _ & _ & _ & (Hn & Hc) & Hv & _ & _ & HF).
rewrite Forall_forall in HF. split.
- intros rr Hr a Ha. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [apply KH; exact Ha|].
  apply in_app_or in Hr as [Hr | Hr].
  + destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    destruct Hv as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
    apply (KB _ _ a Hin). unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, l2_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul in Ha.
    change (Z.of_nat 16) with 16 in Ha. unfold hl_n in Hj. unfold req_size, AREC in *.
    destruct (16 * hl_cap l =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
  + apply in_map_iff in Hr as (x & <- & Hx). destruct (HF x Hx) as (Hin & _).
    apply (KB _ _ a Hin). unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha.
    unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
- intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
  + destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
    destruct Hv as [(Hc0 & _) | (_ & Hin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hin].
  + apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (HF x Hx)).
Qed.
Lemma l2_src_kept : forall ly1 S1 (W1 W2 : world SEGS) m1 m2 HA1 h1,
asrc_at B ly1 S1 W1 m1 HA1 h1 ->
(forall a, HA1 <= a < HA1 + ASRC -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (ablocks B ly1 S1) -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
asrc_at B ly1 S1 W2 m2 HA1 h1.
Proof.
intros ly1 S1 W1 W2 m1 m2 HA1 h1 HS KH KB.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPd & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpl & _ & _ & HE & HH & _).
destruct (l2_list_kept _ _ _ _ _ _ (HA1 + 16) _ _ HPd ltac:(intros a Ha; apply KH; unfold ASRC; lia) KB) as [K1 B1].
destruct (l2_list_kept _ _ _ _ _ _ (HA1 + 64) _ _ HE ltac:(intros a Ha; apply KH; unfold ASRC; lia) KB) as [K2 B2].
destruct (l2_list_kept _ _ _ _ _ _ (HA1 + 80) _ _ HH ltac:(intros a Ha; apply KH; unfold ASRC; lia) KB) as [K3 B3].
apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W2 m2 HA1 h1 HS).
- intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  + apply KH. exact Ha.
  + apply (KB _ _ a Hpin). unfold gfp, bzs in Ha. rewrite length_map in Ha. cbn [fst snd] in Ha.
    unfold req_size, APARTIAL in *. cbn. lia.
  + apply in_app_or in Hr as [Hr|Hr]; [exact (K1 r Hr a Ha)|].
    apply in_app_or in Hr as [Hr|Hr]; [exact (K2 r Hr a Ha) | exact (K3 r Hr a Ha)].
- intros b Hb. unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb|Hb]; [exact (B1 b Hb)|].
  apply in_app_or in Hb as [Hb|Hb]; [exact (B2 b Hb) | exact (B3 b Hb)].
Qed.
(* a step that keeps every byte below the allocator's ceiling (it writes only above lo) and presence keeps the
   source *)
Lemma l2_src_step : forall ly1 S1 md1 (W1 W2 : world SEGS) m1 m2 HA1 h1 lo hi,
AR0 ly1 S1 W1 m1 md1 -> asrc_at B ly1 S1 W1 m1 HA1 h1 ->
(forall a, HA1 <= a < HA1 + ASRC -> in_img SEGS a) -> alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> wle W1 W2 ->
asrc_at B ly1 S1 W2 m2 HA1 h1.
Proof.
intros ly1 S1 md1 W1 W2 m1 m2 HA1 h1 lo hi HAR HS Himg Hlo HK Hp Hw.
pose proof (asan_consts) as (C1 & _).
apply (l2_src_kept ly1 S1 W1 W2 m1 m2 HA1 h1 HS).
- intros a Ha. split; [|intros Hwr; exact (l2_writable_kept_w W1 W2 m1 m2 a (Hp a) Hw Hwr)].
  pose proof (pa_img_range a (Himg a Ha)) as HI. apply HK; lia.
- intros b n a Hin Ha. split; [|intros Hwr; exact (l2_writable_kept_w W1 W2 m1 m2 a (Hp a) Hw Hwr)].
  destruct (al0_blocks ly1 S1 W1 m1 md1 b n HAR Hin) as (_ & B4096 & Bceil & _).
  apply HK; lia.
Qed.
Lemma l2_saved_kept : forall (W1 W2 : world SEGS) m1 m2 sp rs,
(forall a, sp - 96 <= a < sp -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
cshe_saved_B W1 m1 sp rs -> cshe_saved_B W2 m2 sp rs.
Proof.
intros W1 W2 m1 m2 sp rs HK HS. unfold cshe_saved_B in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; (apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [intros k Hk; apply HK; cbn in Hk; lia | assumption]).
Qed.
(* the source with its held list replaced: every other byte and block kept (W_cshe_l2w.v l2_src_swap) *)
Lemma l2_src_swap : forall ly1 S1 (W1 : world SEGS) m1 ly2 S2 (W2 : world SEGS) m2 HA0 (h0 : hsrc) (H' : hlist),
asrc_at B ly1 S1 W1 m1 HA0 h0 ->
(forall a, HA0 <= a < HA0 + 80 -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (gfp (hs_partial h0) (bzs (hs_pjunk h0)) :: alist_fp (HA0 + 16) (hs_pending h0) ++ alist_fp (HA0 + 64) (hs_expected h0)) ->
(forall b, In b ((hs_partial h0, APARTIAL) :: alist_blks (hs_pending h0) ++ alist_blks (hs_expected h0)) -> In b (ablocks B ly2 S2)) ->
alist_at B ly2 S2 W2 m2 (HA0 + 80) H' true ->
NoDup (hs_blocks (CheckRep.set_held h0 H')) ->
asrc_at B ly2 S2 W2 m2 HA0 (CheckRep.set_held h0 H').
Proof.
intros ly1 S1 W1 m1 ly2 S2 W2 m2 HA0 h0 H'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
   H21 & H22 & H23 & H24) HK HF HB HL HND.
assert (Hvm : forall a n v, HA0 <= a -> a + Z.of_nat n <= HA0 + 80 ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v)
  by (intros a n v Ha Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply HK; lia | exact Hv]).
split; [apply Hvm; [lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | exact H3]|].
split; [apply Hvm; [lia | cbn; lia | exact H4]|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i 80) as [Hi8 | Hi8]; [apply (proj2 (HK (HA0 + i) ltac:(lia))); exact (H5 i Hi)|].
  pose proof HL as (_ & _ & _ & HW & _). replace (HA0 + i) with (HA0 + 80 + (i - 80)) by lia. apply HW. unfold ASRC in Hi. lia. }
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H10
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; left; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; left; exact Hb]|].
split; [apply Hvm; [lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|].
split; [apply HB; left; reflexivity|].
split; [exact H19|].
split; [apply (akept_garr8 W1 m1); [intros x Hx; apply (HF (gfp (hs_partial h0) (bzs (hs_pjunk h0))));
  [left; reflexivity | exact Hx] | exact H20]|].
split; [exact H21|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H22
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; right; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; right; exact Hb]|].
split; [exact HL | exact HND].
Qed.
(* what a callee's journal at its own globals G' says of the bytes off G' (ajournal_gx_inner) *)
Lemma l2_callee_keeps : forall G' STK1 sp1 FP1 ly1 S1 (W1 : world SEGS) m1 md1 ly2 S2 (W2 : world SEGS) m2 md2 k,
AJ0 G' 0 [] STK1 sp1 FP1 ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ inG G' a -> alloc_ceiling <= a -> ~ (sp1 - STK1 <= a < sp1) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ inG G' a -> in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP1 a ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
(forall p n i, 0 <= p + i < 2 ^ 64 -> ~ inG G' (p + i) -> In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) ->
  0 <= i < req_size n -> ~ inFP FP1 (p + i) -> aview SEGS (w_H W2) m2 (p + i) = aview SEGS (w_H W1) m1 (p + i)) /\
wle W1 W2 /\ frames S2 = frames S1 /\ AR0 ly2 S2 W2 m2 md2.
Proof.
intros G' STK1 sp1 FP1 ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k HJ.
destruct (ajournal_gx_inner0 G' 0 [] STK1 sp1 FP1 ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 k HJ) as (memS & HJi & Hag).
rewrite !Z.add_0_r in HJi.
destruct HJi as (HAR & _ & _ & Hwle & _ & Hfrs & _ & _ & F1 & F2 & F3 & _).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G' a -> aview SEGS (w_H W1) memS a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hn. apply Hag. rewrite unsigned_lit_small by lia. exact Hn. }
split; [intros a Ha Hn Hc Hs; rewrite (F1 a ltac:(lia) Hs); exact (AG a Ha Hn)|].
split; [intros a Ha Hn Hi Ho He Hf; rewrite (F3 a Hi Ho He (HPST a Hi) Hf); exact (AG a Ha Hn)|].
split; [intros p n i Ha Hn Hin1 Hin2 Hi Hf; rewrite (F2 p n i Hin1 Hin2 Hi Hf); exact (AG (p + i) Ha Hn)|].
split; [exact Hwle|]. split; [rewrite Hfrs; reflexivity | exact HAR].
Qed.
(* L2CHECK4 *)

(* a run whose regions have no write window keeps every byte *)
Ltac l2_nowin Hf :=
lazymatch type of Hf with frame_of ?Ev ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) =>
  apply (aview_kept_out Ev rs H m0 m1 Hf); [lia|];
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros (rg & Hin & Hrg);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; lia|]);
  destruct Hin
end.
(* back along the runs since a memory m: each frame_of with no write window keeps every byte *)
Ltac l2_back :=
match goal with
| |- aview _ ?H ?m ?a = aview _ ?H ?m ?a => reflexivity
| Hf : frame_of _ _ (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- aview _ ?H ?m1 ?a = _ =>
    transitivity (aview SEGS H m0 a); [l2_nowin Hf | l2_back]
end.
(* presence, back along the runs' mem_grows to a fact Hq about the memory they started from *)
Ltac l2_pres_back Hq :=
first [ exact Hq
      | lazymatch goal with Hg : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- apresent ?H ?m1 ?a =>
          apply (apresent_grows H m0 m1 a Hg); l2_pres_back Hq end ].
(* a register the run did not change: the same symbolic value in the state HS0 the run started from *)
Ltac l2_keepreg HS0 HS r :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq; rewrite Bq, <- A; clear A Bq.
Ltac l2_keepreg2 HS0 HS r OLD :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq;
repeat (rewrite OLD in Bq by lia); rewrite Bq, <- A; clear A Bq.

(* ------------------------------------------------------------------ the loop *)
Section loop.
(* the entry of check_shape_ends (cshe_spec's names), and what the loop keeps needing of it *)
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 gone : Z) (j : nat) (h : hsrc) (P ob : list byte).
(* the room round: the caller's room budget past the call (cshe_post_x's kr) *)
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation R0 := (hl_recs (hs_held h)).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_out_B B PST ARx G MT RP regs0 ly S W mem md XO AT HA A0 gone h P ob kr).
Local Notation PLEN := (Z.of_nat (length P)).
(* the records past the first m: those dropped (they have the prefix), those kept *)
Local Notation DS m := (filter (fun r => CheckRep.prefixb P (snd r)) (skipn m (hl_recs (hs_held h)))).
Local Notation KP m := (filter (fun r => negb (CheckRep.prefixb P (snd r))) (skipn m (hl_recs (hs_held h)))).
Hypothesis HPRE : AFP0 CSHE_STK_B ly S W regs0 mem md ch.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 4096 <= HA.
Hypothesis HAhi : HA + ASRC <= kLowMemEnd.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis HAj : HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j.
Hypothesis Hj4 : (j < 4)%nat.
Hypothesis HND0 : NoDup (CheckRep.texts (hs_held h)).
Hypothesis Hn26 : hl_n (hs_held h) < 2 ^ 26.
Hypothesis HPz : ~ In (Z_to_bv 8 0) P.
Hypothesis HPl : PLEN + 1 < 2 ^ 32.
Hypothesis HPF0 : 0 < PF.
Hypothesis HPFh : PF + PLEN + 8 <= 2 ^ 63.
Hypothesis HPB : forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0))).
Hypothesis HPN : aview SEGS (w_H W) mem (PF + PLEN) = Some 0.
Hypothesis HPV : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (sp0 - CSHE_STK_B <= a < sp0 + XO).
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
Hypothesis HPRA0 : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
(* where P lives (cshe_spec's one premise, W3Checks-2's ruling at a working branch fb87b19890f): a read-only literal,
   or a buffer inside one of the entry's fake frames (ARM_gone's prefix[48]) *)
Hypothesis HPLOC : ((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1)) \/
  (exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))).
Hypothesis HROM0 : rom_view SEGS W mem.
Hypothesis HSRC0 : asrc_at B ly S W mem HA h.

(* the source g_s[j]: image bytes the allocator does not own, not errno, not read-only, apart from g_gone *)
Lemma l2_HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a /\ ~ (VAL A_g_gone <= a < VAL A_g_gone + 1).
Proof.
intros a Ha. unfold ASRC in *.
assert (Hs : VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384) by (rewrite HAj in Ha; lia).
destruct (HGS a Hs) as (Hi & Hr & Hg & _).
assert (Hg' : inG cshe_ro_B a).
{ unfold inG, cshe_ro_B. apply Exists_exists. exists (VAL (A_OBJ 19), 384). split; [right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
destruct (HGR a Hg') as (_ & Ho & _). pose proof (proj1 (HGRR a Hg')) as He.
split; [exact Hi|]. split; [exact Ho|]. split; [exact He|]. split; [exact Hr | exact Hg].
Qed.
(* g_gone: an image byte the allocator does not own, not errno (cshe_ro_B) *)
Lemma l2_gone_img : in_img SEGS (VAL A_g_gone) /\ ~ Exists (in_zr (VAL A_g_gone)) (as_owned_static B) /\
  ~ (as_errno B <= VAL A_g_gone < as_errno B + 4).
Proof.
assert (Hg' : inG cshe_ro_B (VAL A_g_gone)).
{ unfold inG, cshe_ro_B. apply Exists_exists. exists (VAL A_g_gone, 1). split; [left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
destruct (HGR _ Hg') as (Hi & Ho & _). pose proof (proj1 (HGRR _ Hg')) as He.
split; [exact Hi|]. split; [exact Ho | exact He].
Qed.

(* the invariant at the head, m records not yet examined *)
Definition l2_regs (regs1 : bvmap 5 word) (m : nat) : Prop :=
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 27 = getr regs0 27 /\
getr regs1 8 = w64 PF /\ getr regs1 9 = w64 (HA + 80) /\ getr regs1 18 = w64 ((HA + 80) / 8 + SB) /\
getr regs1 19 = w64 (Z.of_nat m) /\ getr regs1 21 = w64 SB.
Definition l2_mem (m : nat) (ly1 : alayout) (S1 : astate) (kk : Z) (H1 : hlist) (W1 : world SEGS)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v (hs_held h) /\ hl_cap H1 = hl_cap (hs_held h) /\
hl_recs H1 = firstn m (hl_recs (hs_held h)) ++ KP m /\
(forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (DS m) ++ rest) ->
  Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length (DS m)) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat m * mo_free MT) /\
rom_view SEGS W1 mem1 /\ cshe_saved_B W1 mem1 sp0 regs0 /\
val_mem SEGS (arm W1 mem1) AT 8 A0 /\ val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)) /\
(* the room round: one free's room (MT_rk's mo_free) per record still to examine, past the caller's kr; the live
   counts stay under the bounds (cshe_pk = ldrop_pk = 0: the drops only remove blocks) *)
rp_RM RP S1 (Z.to_nat (Z.of_nat m * mo_free MT_rk) + kr) /\ cnt_ok RP (ablocks B ly1 S1).
(* MT_rk's free costs 1: the budget for m records is m *)
Lemma l2_rk : forall m, Z.to_nat (Z.of_nat m * mo_free MT_rk) = m.
Proof. intros m. change (mo_free MT_rk) with 1. rewrite Z.mul_1_r. apply Nat2Z.id. Qed.
Definition l2_inv (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_mem m ly1 S1 kk H1 W1 mem1 md1 /\ l2_regs regs1 m.
(* 0x858c4: s3 = m, a0 = &v[m], a1 = v; the record v[m] not examined yet *)
Definition l2_mid (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_mem (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 /\ l2_regs regs1 m /\
getr regs1 10 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m) /\ getr regs1 11 = w64 (hl_v (hs_held h)).

Lemma l2_regs_eq : forall regs1 regs2 m, (forall r, getr regs2 r = getr regs1 r) -> l2_regs regs1 m -> l2_regs regs2 m.
Proof. intros regs1 regs2 m E X. unfold l2_regs in *. rewrite !E. exact X. Qed.

(* the memory side of the invariant moves across a step that writes only [lo, hi), above the allocator's ceiling
   and below the frame, and keeps presence *)
Lemma l2_mem_keep : forall m ly1 S1 kk H1 (W1 W2 : world SEGS) m1 m2 md1 md2 lo hi,
l2_mem m ly1 S1 kk H1 W1 m1 md1 ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 m2 md2 kk ->
alloc_ceiling <= lo -> hi <= sp0 - 112 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> wle W1 W2 ->
l2_mem m ly1 S1 kk H1 W2 m2 md2.
Proof.
intros m ly1 S1 kk H1 W1 W2 m1 m2 md1 md2 lo hi
  (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & MAT & MG & MER & HRMk & HCNk) HJ2 Hlo Hhi HK HPs Hw.
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 m1 md1 kk HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
split; [exact HJ2|].
split.
{ apply (l2_src_step ly1 S1 md1 W1 W2 m1 m2 HA _ lo hi HAR1 HSRC); [| exact Hlo | exact HK | exact HPs | exact Hw].
  intros a Ha. exact (proj1 (l2_HAimg a Ha)). }
split; [exact HV|]. split; [exact HC|]. split; [exact HREC|]. split; [exact HPERM|].
split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split.
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi) as HI. rewrite HK by lia. exact (HROM a Hr). }
split.
{ apply (l2_saved_kept W1 W2 m1 m2 sp0 regs0); [|exact HSAV]. intros a Ha. apply HK; lia. }
split; [apply (l2_vm_keep W1 W2 m1 m2); [intros x Hx; cbn in Hx; apply HK; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W2 m1 m2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
  pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR. apply HK; lia. }
split; [intros i Hi; destruct l2_errno_low as [E0 E1]; rewrite HK by lia; exact (MER i Hi)|].
exact (conj HRMk HCNk).
Qed.

(* a record without the prefix: the head moves one record down, nothing else changes *)
Lemma l2_mem_miss : forall m ly1 S1 kk H1 W1 mem1 md1, (Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = false ->
l2_mem (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 -> l2_mem m ly1 S1 kk H1 W1 mem1 md1.
Proof.
intros m ly1 S1 kk H1 W1 mem1 md1 Hm E (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & MAT & MG & MER & HRMk & HCNk).
pose proof (mo_free_nonneg MT ML) as Hf.
split; [exact HJ|]. split; [exact HSRC|]. split; [exact HV|]. split; [exact HC|].
split; [rewrite HREC; apply l2_kp_miss; [lia | exact E]|].
rewrite (l2_ds_miss P (hl_recs (hs_held h)) m ltac:(lia) E).
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|].
split.
{ apply (mok_station MT S1 S1 (Z.of_nat (Datatypes.S m) * mo_free MT) 0 (Z.of_nat m * mo_free MT) ML HMOK
    (mle_start MT S1 ML)); [apply Z.mul_nonneg_nonneg; lia | rewrite Nat2Z.inj_succ; nia]. }
split; [exact HROM|]. split; [exact HSAV|]. split; [exact MAT|]. split; [exact MG|]. split; [exact MER|].
(* the room round: the record is kept, its free's room stays unspent *)
split; [|exact HCNk]. rewrite l2_rk. rewrite l2_rk in HRMk. exact (RMM_of RP S1 (m + kr) (Datatypes.S m + kr) ltac:(lia) HRMk).
Qed.
(* L2CHECK5 *)

(* the stack and frame numbers every piece needs *)
Lemma l2_sp_facts : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47 /\ (sp0 - 112) mod 16 = 0 /\ alloc_ceiling + CSHE_STK_B <= sp0 /\
  sp0 + XO <= 2 ^ 47 /\ 0 <= XO.
Proof.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HXO : 0 <= XO) by lia.
split; [rewrite WS in Hslo; lia|]. split; [rewrite Zminus_mod, Hal16; reflexivity|]. lia.
Qed.

(* ---- 0x858ac .. 0x858c4: the shadow check of &held.v, a1 = v, s3 = m, a0 = v + 16 m ---- *)
Lemma l2_head : forall m W1 regs1 mem1 md1, l2_inv (Datatypes.S m) W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_mid m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_l2e)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR) HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
pose proof HM as (HJ & HSRC & HV & HC & HREC & _).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & _).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (al0_blocks ly1 S1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
assert (HSm : 1 <= Z.of_nat (Datatypes.S m) <= 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (l2h_state W1 regs1 mem1 (sp0 - 112) HA (hl_v H1) (Z.of_nat (Datatypes.S m)) R2 R9 R18 R19 R21 HSPb HSPa HA8 HAlo HAhi'
  HvR V16 HSm MvH ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (l2_xh (hl_v H1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat m + 1))
  by (rewrite (EEo 19%nat 19%bv eq_refl), R19; unfold w64; f_equal; lia).
pose proof HS as HS0.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ SHOK l2_Bspan A_l2e.
{ apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_hd] in Ha; lia | apply awr_ok_x_nil]. }
pmkst HS.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_nowin HFr).
assert (PRES : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (19%bv : bv 5) T19.
rewrite E19, E32 in T10. rewrite (l2_addr_val (hl_v H1) (Z.of_nat m) ltac:(unfold hl_n in Hn26; lia) ltac:(lia)) in T10.
rewrite E32 in T11. rewrite E19, (l2_dec_val (Z.of_nat m) ltac:(unfold hl_n in Hn26; lia)) in T19.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  replace (BASE + k) with (BASE + A_l2e) by (unfold A_l2e, AF_fr_check_shape_ends; lia) end.
apply HKont. split; [lia|].
exists ly1, S1, kk, H1. split; [|split; [|split]].
- apply (l2_mem_keep (Datatypes.S m) ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 _ (sp0 - 112) (sp0 - 112) HM HJ);
  [lia | lia | intros a Ha _; exact (KEEP a Ha) | exact PRES | apply wle_refl].
- unfold l2_regs.
  split; [l2_keepreg HS0 HS (2%bv : bv 5); exact R2|].
  split; [l2_keepreg HS0 HS (3%bv : bv 5); exact R3|].
  split; [l2_keepreg HS0 HS (4%bv : bv 5); exact R4|].
  split; [l2_keepreg HS0 HS (27%bv : bv 5); exact R27|].
  split; [l2_keepreg HS0 HS (8%bv : bv 5); exact R8|].
  split; [l2_keepreg HS0 HS (9%bv : bv 5); exact R9|].
  split; [l2_keepreg HS0 HS (18%bv : bv 5); exact R18|].
  split; [exact T19|].
  l2_keepreg HS0 HS (21%bv : bv 5); exact R21.
- rewrite T10, HV. unfold w64, AREC. f_equal.
- rewrite T11, HV. reflexivity.
Qed.
(* L2CHECK6 *)

Lemma l2t_state : forall (W1 : world SEGS) regs mem1 SP m,
getr regs 2 = w64 SP -> getr regs 19 = w64 m -> 2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> 0 <= m <= 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_l2t
(restrict (w_H W1) (mkst regs (Z_to_bv 64 (BASE + A_l2t)) mem1 (seg_rom SEGS))) /\
sh_ok SEGS l2_Bx l2_SHt (Eimg (Ereg regs [])) (mrestrict (w_H W1) mem1).
Proof.
intros W1 regs mem1 SP m H2 H19 HSP HSPa Hm.
set (E := Eimg (Ereg regs [])).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E19 : ew E 19 = Z_to_bv 64 m) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
split.
- rewrite restrict_mkst_fx. unfold ss_l2t. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor.
  + apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [l2t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E19, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, l2_SHt. constructor.
Qed.

(* ---- 0x85928: bgtz s3, back to the head while records are left; else on to the epilogue's entry 0x8592c, where
   m = 0: the held list is the records of the entry's list without the prefix ---- *)
Lemma l2_tail : forall m W1 regs1 mem1 md1, l2_inv m W1 regs1 mem1 md1 -> gone <> 0 ->
(forall W2 regs2 mem2 md2, (0 < m)%nat -> l2_inv m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_csheB_l2)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_l2t)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR) Hgone HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
pose proof HM as (HJ & _).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
destruct (l2t_state W1 regs1 mem1 (sp0 - 112) (Z.of_nat m) R2 R19 HSPb HSPa ltac:(unfold hl_n in Hn26; lia)) as [HS SHOK].
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat m))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl); exact R19).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose proof HS as HS0.
psrr_branch_tok RUNx BR HS SHOK l2_Bspan.
- (* bgtz taken: records are left, back to the head *)
  rewrite trap_br_lt, S_SLit, S_SOff, E19, unsigned_lit_small, Z.add_0_r, !swrap64_id in Hc
    by (unfold half64, hl_n in *; lia).
  apply Z.ltb_lt in Hc.
  paj_run_to_tok_x RUNTOx HS HJ SHOK l2_Bspan A_csheB_l2. { cbn [ss_mem add_cond ss_l2t]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms) rr = getr regs1 rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS0) as X0.
    cbn [ms_regs restrict mkst] in X0. rewrite X1, X0. reflexivity. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_nowin HFr).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_mem m ly1 S1 kk H1 W1 (ms_mem ms) mdd).
  { apply (l2_mem_keep m ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 mdd (sp0 - 112) (sp0 - 112) HM HJ);
    [lia | lia | intros a Ha _; exact (KEEP a Ha) | intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp) | apply wle_refl]. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_csheB_l2) by (unfold A_csheB_l2, AF_fr_check_shape_ends; lia) end.
  apply HKont; [lia|]. split; [exact Hle|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
  exact (l2_regs_eq regs1 (ms_regs ms) m RG HR).
- (* bgtz not taken: that was the last record, the epilogue's entry *)
  rewrite trap_br_lt, S_SLit, S_SOff, E19, unsigned_lit_small, Z.add_0_r, !swrap64_id in Hc
    by (unfold half64, hl_n in *; lia).
  apply Z.ltb_ge in Hc. assert (Hm0 : m = 0%nat) by lia. subst m.
  paj_run_to_tok_x RUNTOx HS HJ SHOK l2_Bspan A_csheB_ret. { cbn [ss_mem add_cond ss_l2t]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms) rr = getr regs1 rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS0) as X0.
    cbn [ms_regs restrict mkst] in X0. rewrite X1, X0. reflexivity. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_nowin HFr).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_mem 0 ly1 S1 kk H1 W1 (ms_mem ms) mdd).
  { apply (l2_mem_keep 0 ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 mdd (sp0 - 112) (sp0 - 112) HM HJ);
    [lia | lia | intros a Ha _; exact (KEEP a Ha) | intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp) | apply wle_refl]. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_csheB_ret) by (unfold A_csheB_ret, AF_fr_check_shape_ends; lia) end.
  apply SRr_ret. unfold cshe_out_B.
  pose proof MEMF as (HJm & HSRCm & HVm & HCm & HRECm & HPERMm & HFRSm & HMLEm & HMOKm & HROMm & HSAVm & MATm & MGm & MERm & HRMm & HCNm).
  exists ly1, S1, (ms_regs ms), (ms_mem ms), mdd, kk, H1,
    (filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h))), 0.
  split; [reflexivity|]. split; [exact HJm|].
  split; [rewrite RG; exact R2|]. split; [rewrite RG; exact R3|]. split; [rewrite RG; exact R4|].
  split; [rewrite RG; exact R27|].
  split; [exact HSAVm|]. split; [exact HSRCm|]. split; [exact HVm|]. split; [exact HCm|].
  split.
  { unfold CheckRep.texts. rewrite HRECm. cbn [firstn app skipn].
    try apply NoDup_ListNoDup. apply l2_nodup_filter. try apply NoDup_ListNoDup. exact HND0. }
  split; [left; split; [exact Hgone|]; split; [rewrite HRECm; reflexivity | split; reflexivity]|].
  split; [lia|]. split; [rewrite Z.add_0_r; exact MATm|]. split; [exact MGm|].
  split; [exact HPERMm|]. split; [exact HFRSm|].
  split; [|split; [exact MERm|]; rewrite l2_rk in HRMm; exact HRMm].
  apply (mo_le_mono MT ML _ _ _ _ HMLEm).
  pose proof (mo_free_nonneg MT ML) as Hf.
  assert (HL : (length (filter (fun r => CheckRep.prefixb P (snd r)) (skipn 0 (hl_recs (hs_held h)))) <=
    length (hl_recs (hs_held h)))%nat).
  { pose proof (l2_filter_len (fun r => CheckRep.prefixb P (snd r)) (skipn 0 (hl_recs (hs_held h)))) as X.
    rewrite length_skipn in X. cbn beta in X. lia. }
  unfold hl_n. apply Z.mul_le_mono_nonneg_r; [exact Hf | lia].
Qed.

(* ------------------------------------------------------------------ the drop of record m *)
Lemma l2_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & H1 & H2) Ha Hn. exists r. split; [exact Hin|]. split; [exact H8|]. lia. Qed.
Lemma l2_nodup_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
cbn [app] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
destruct H1 as [<- | H1]; [apply NI; apply in_or_app; right; exact H2 | exact (IH l2 x ND H1 H2)].
Qed.
Lemma l2_blks_blocks : forall (l : hlist) b n, In (b, n) (alist_blks l) -> In b (list_blocks l).
Proof.
intros l b n Hb. unfold alist_blks, list_blocks in *. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app.
- left. destruct (hl_cap l =? 0); [destruct Hb|]. destruct Hb as [E | []]. injection E as <- _. left. reflexivity.
- right. apply in_map_iff in Hb as (x & Ex & Hx). injection Ex as <- _. apply in_map. exact Hx.
Qed.
Lemma l2_alist_blks_in : forall ly0 S0 W0 m0 LA l lines, alist_at B ly0 S0 W0 m0 LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 LA l lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
  destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. exact (proj1 (HF x Hx)).
Qed.
(* the list's bytes are kept when its head and the bytes of its own blocks are *)
Lemma l2_list_kept2 : forall ly1 S1 (W1 W2 : world SEGS) m1 m2 LA l lines,
alist_at B ly1 S1 W1 m1 LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (alist_blks l) -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (alist_fp LA l).
Proof.
intros ly1 S1 W1 W2 m1 m2 LA l lines HL KH KB. destruct HL as (_ & _ & _ & _ & (Hn & Hc) & Hv & _ & _ & HF).
rewrite Forall_forall in HF.
intros rr Hr a Ha. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [apply KH; exact Ha|].
apply in_app_or in Hr as [Hr | Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
  destruct Hv as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  apply (KB (hl_v l) (AREC * hl_cap l) a); [unfold alist_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app, l2_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul in Ha.
  change (Z.of_nat 16) with 16 in Ha. unfold hl_n in Hj. unfold req_size, AREC in *.
  destruct (16 * hl_cap l =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
- apply in_map_iff in Hr as (x & <- & Hx).
  apply (KB (fst x) (Z.of_nat (length (snd x)) + 1) a).
  + unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha.
    unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
Qed.
(* FP1 (the vector and the dropped text) never holds address 0: list_drop does not open the sink *)
Lemma l2_fp_spares : forall v cv q nq a, 4096 <= v -> 4096 <= q ->
fp_spares [(v, v + cv); (q, q + nq)] a.
Proof.
intros v cv q nq a Hv Hq (rr & Hin & Hr). exfalso. cbn [In] in Hin.
destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia.
Qed.

(* ---- P's facts at a later state of the walk.  P is a read-only literal (its bytes kept by rom_view, its shadow by
   ashp in any AR state) or a buffer inside one of the entry's fake frames: there the journal's frame clause keeps
   P's bytes and their shadow bytes (a fake frame is off image B, so off G, and off every heap block, so off FPc), and
   its 8-aligned shadow hull is visible in any AR state (W_frame.v shadow_hull_vis_of_frame). ---- *)
Lemma l2_frame_keep : forall ly1 S1 (W1 : world SEGS) mem1 md1 kk cid pos a,
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk ->
In (cid, pos) (frames S) ->
in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
~ inFP FPc a -> ~ inG G a -> 0 <= a < 2 ^ 64 ->
aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a.
Proof.
intros ly1 S1 W1 mem1 md1 kk cid pos a HJ1 Hin Hr Hnf HnG Ha.
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ1)
  as (memS & HJi & Hag).
destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
rewrite (F4 cid pos a Hin Hr Hnf). apply Hag. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* a byte of FPc (the held list's blocks) lies in a block of the entry *)
Lemma l2_FPc_blk : forall y, inFP FPc y -> exists b n, In (b, n) (ablocks B ly S) /\ b <= y < b + req_size n.
Proof.
intros y (rr & Hin & Hr). unfold blk_FP in Hin. apply in_map_iff in Hin as ([b n] & <- & Hbn). cbn [fst snd] in Hr.
exists b, n. split; [|exact Hr].
pose proof HSRC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
exact (l2_alist_blks_in ly S W mem (HA + 80) (hs_held h) true HAH (b, n) Hbn).
Qed.
Lemma l2_pfx_keep : forall ly1 S1 (W1 : world SEGS) mem1 md1 kk,
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk ->
rom_view SEGS W1 mem1 ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1) /\
shadow_hull_vis (aview SEGS (w_H W1) mem1) PF (PLEN + 1).
Proof.
intros ly1 S1 W1 mem1 md1 kk HJ1 HRV1.
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ1) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPLOC as [(HPROM & HPS) | (cid & pos & HinF & HPfr)].
- (* a read-only literal *)
  assert (PK : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a)
    by (intros a Ha; rewrite (HRV1 a (HPROM a Ha)); symmetry; exact (HROM0 a (HPROM a Ha))).
  destruct (HPS ly1 S1 [] W1 mem1 md1 HAR1) as [HRA HHV].
  split; [exact PK|]. split; [exact HRA | apply HHV; lia].
- (* a buffer in a fake frame of the entry *)
  pose proof HPRE as (HAR0 & _).
  destruct (frame_al640 ly S W mem md cid pos HAR0 HinF) as (Hal & Hbal & Hb64).
  destruct (frames_bounds0 ly S W mem md cid pos HAR0 HinF) as (F4096 & Fceil & Fapp).
  pose proof (cshe_frm_off_img ly S W mem md cid pos HAR0 HinF) as Foff.
  assert (HPfr' : forall a, PF <= a < PF + PLEN + 8 ->
    frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid)
    by (intros a Ha; pose proof (HPfr a Ha) as X; unfold in_zr, frame_rng in X; cbn [fst snd] in X; exact X).
  assert (HFw : frame_addr ly cid pos <= PF /\ PF + PLEN + 8 <= frame_addr ly cid pos + fs_frame_bytes cid).
  { pose proof (HPfr' PF ltac:(lia)). pose proof (HPfr' (PF + PLEN + 7) ltac:(lia)). lia. }
  assert (NG : forall y, y < 65536 \/ 6275072 <= y -> ~ inG G y).
  { intros y Hy HGy. pose proof (pa_img_range y (proj1 (HG y HGy))). lia. }
  assert (NFf : forall y, frame_addr ly cid pos <= y < frame_addr ly cid pos + fs_frame_bytes cid -> ~ inFP FPc y).
  { intros y Hy Hf. destruct (l2_FPc_blk y Hf) as (b & n & Hbn & Hb).
    pose proof (sep_block_frame0 ly S W mem md b n cid pos HAR0 Hbn HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (NFs : forall y, kLowShadowBeg <= y < kHighMemBeg -> ~ inFP FPc y).
  { intros y Hy Hf. destruct (l2_FPc_blk y Hf) as (b & n & Hbn & Hb).
    destruct (al0_blocks ly S W mem md b n HAR0 Hbn) as (_ & _ & _ & (Ha1 & Ha2) & _).
    destruct Ha2 as [Ha2 | [Ha2 _]]; lia. }
  assert (PK : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a).
  { intros a Ha. pose proof (HPfr' a Ha) as Hfa.
    apply (l2_frame_keep ly1 S1 W1 mem1 md1 kk cid pos a HJ1 HinF);
      [left; exact (HPfr a Ha) | exact (NFf a Hfa) | apply NG; destruct Foff; [left | right]; lia | lia]. }
  split; [exact PK|]. split.
  + (* the shadow bytes of P are frame shadow bytes: kept from the entry *)
    pose proof (Z.div_mod (frame_addr ly cid pos) 64 ltac:(lia)) as D1. rewrite Hal, Z.add_0_r in D1.
    pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D2. rewrite Hbal, Z.add_0_r in D2.
    assert (Ef8 : frame_addr ly cid pos / 8 = 8 * (frame_addr ly cid pos / 64)).
    { rewrite D1 at 1. replace (64 * (frame_addr ly cid pos / 64)) with ((8 * (frame_addr ly cid pos / 64)) * 8) by ring.
      apply Z_div_mult. lia. }
    assert (Eb8 : fs_frame_bytes cid / 8 = 8 * (fs_frame_bytes cid / 64)).
    { rewrite D2 at 1. replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by ring.
      apply Z_div_mult. lia. }
    intros x Hx. destruct (HPRA0 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok]. rewrite <- Hsv.
    unfold shadow_of_addr. pose proof (HPfr' x ltac:(lia)) as Hfx.
    assert (Hlo : 8 * (frame_addr ly cid pos / 64) <= x / 8) by (apply Z.div_le_lower_bound; lia).
    assert (Hhi : x / 8 < 8 * (frame_addr ly cid pos / 64) + 8 * (fs_frame_bytes cid / 64))
      by (apply Z.div_lt_upper_bound; lia).
    assert (Hx0 : 0 <= x / 8) by (apply Z.div_pos; lia).
    assert (Hxc : x / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
    apply (l2_frame_keep ly1 S1 W1 mem1 md1 kk cid pos (SHADOW_OFF + x / 8) HJ1 HinF).
    * right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Ef8, Eb8. lia.
    * apply NFs. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
    * apply NG. right. unfold SHADOW_OFF. lia.
    * unfold SHADOW_OFF. lia.
  + (* the hull: visible in any AR state with the frame live; frames and the frame base are the entry's *)
    destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ1)
      as (memS & HJi & _).
    destruct HJi as (_ & Hly & _ & _ & _ & Hfrs & _).
    assert (Efr : frame_addr ly1 cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    assert (HinF1 : In (cid, pos) (frames S1)) by (rewrite Hfrs; exact HinF).
    apply (shadow_hull_vis_of_frame0 ly1 S1 W1 mem1 md1 cid pos PF (PLEN + 1) HAR1 HinF1); rewrite ?Efr; lia.
Qed.
(* P lies below the allocator's ceiling in both of its places (the image, a fake frame), so s0 = PF ends the frame
   chain at each call *)
Lemma l2_PF_low : PF + PLEN + 8 <= alloc_ceiling.
Proof.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPLOC as [(HPROM & _) | (cid & pos & HinF & HPfr)].
- pose proof (HPROM (PF + PLEN + 7) ltac:(lia)) as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range (PF + PLEN + 7) ltac:(exists sg; split; [exact Hsg | exact Hra])). lia.
- pose proof HPRE as (HAR0 & _).
  destruct (frames_bounds0 ly S W mem md cid pos HAR0 HinF) as (_ & Fceil & _).
  pose proof (HPfr (PF + PLEN + 7) ltac:(lia)) as X. unfold in_zr, frame_rng in X. cbn [fst snd] in X. lia.
Qed.

Lemma l2_drop : forall m ly1 S1 kk H1 W1 regsT memT mdc,
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = true ->
l2_mem (Datatypes.S m) ly1 S1 kk H1 W1 memT mdc -> l2_regs regsT m ->
getr regsT 10 = w64 (HA + 80) -> getr regsT 11 = w64 (Z.of_nat m) -> getr regsT 1 = Z_to_bv 64 (BASE + A_l2t) ->
(forall W2 regs2 mem2 md2, l2_inv m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_l2t)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_fr_list_drop)) memT (seg_rom SEGS)) mdc) Post.
Proof.
intros m ly1 S1 kk H1 W1 regsT memT mdc Hle HPT HM HR T10 T11 T1 Kont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
assert (WL : LDROP_STK = 16448) by reflexivity.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & MAT & MG & MER & HRMk & HCNk).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 memT mdc kk HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPEND & _ & _ & _ & _ & _ & _ & _ & HPART & _ & _ & _ & HEXP & HAH0 & HNDB).
assert (HAH : alist_at B ly1 S1 W1 memT (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (al0_blocks ly1 S1 W1 memT mdc _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
set (r := nth m (hl_recs (hs_held h)) (0, [])) in *.
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
assert (HRIN0 : In r (hl_recs (hs_held h))) by (unfold r; apply nth_In; lia).
pose proof HFallH as HFallH'. rewrite Forall_forall in HFallH'. destruct (HFallH' r HRIN) as (HrB & HrG & HrL & _).
destruct (al0_blocks ly1 S1 W1 memT mdc _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
rewrite HreqR in Hrceil.
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
pose proof l2_PF_low as HPlow.
(* list_drop's globals: the held list head *)
set (G' := [(HA + 80, 16)]).
assert (HG'G : forall a, inG G' a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)]. unfold in_zr in Ha. cbn [fst snd] in Ha.
  apply HGa. lia. }
assert (HG'r : forall a, inG G' a -> HA + 80 <= a < HA + 96).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)]. unfold in_zr in Ha. cbn [fst snd] in Ha. lia. }
assert (HG' : gx_ok SEGS B G') by exact (gx_ok_sub SEGS B G' G HG'G HG).
assert (HGRT' : gx_rt B G').
{ apply (gx_rt_sub B G' cshe_ro_B); [|exact HGRR]. intros a Ha. pose proof (HG'r a Ha) as Hr.
  unfold inG, cshe_ro_B. apply Exists_exists. exists (VAL (A_OBJ 19), 384). split; [right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. rewrite HAj in Hr. unfold ASRC in Hr. lia. }
assert (HROMS' : forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a).
{ intros a Hr. destruct (ROMNS a Hr) as [He Hp]. split; [exact Hp|]. split; [exact He|].
  intros Ha. pose proof (HG'r a Ha) as Hra. destruct (l2_HAimg a ltac:(unfold ASRC; lia)) as (_ & _ & _ & Hnr & _).
  exact (Hnr Hr). }
pose proof (LDROP G' HG' HGRT' HROMS') as LD.
(* list_drop's entry: afn_pre from this function's journal *)
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 memT mdc kk HJ)
  as (memS & HJi & HgS).
assert (UspT : spZ regsT = sp0 - 112)
  by (change (spZ regsT) with (bv_unsigned (getr regsT 2)); rewrite R2; apply unsigned_lit_small; lia).
assert (HPREd : AFP0 LDROP_STK ly1 S1 W1 regsT memT mdc []).
{ eapply (afn_pre_at0 (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 memT mdc kk
    regsT LDROP_STK (- 112 - XO) [] HJi).
  - rewrite UspT. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - rewrite WL. lia.
  - rewrite WL, WS. lia.
  - rewrite T1. apply ret_ok_codeptr_v; [unfold A_l2t, AF_fr_check_shape_ends; lia | reflexivity].
  - unfold raZ. rewrite T1. rewrite unsigned_lit_small by (unfold A_l2t, AF_fr_check_shape_ends; lia).
    unfold A_l2t, AF_fr_check_shape_ends. lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite R8. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ refine (LD W1 ly1 S1 [] regsT memT mdc [] (HA + 80) H1 true m HPREd T10 T11 HAH _ _ _ _ _ _ _ _
    (Z.to_nat (Z.of_nat m * mo_free MT_rk) + kr)%nat _ _ _).
  - lia.
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold AREC, hl_n in *. lia.
  - apply (l2_azs_sub (HA + 64) 32); [exact Hzs | lia | lia].
  - intros a Ha. split; [apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia|]. rewrite UspT, WL. lia.
  - intros a Ha. rewrite UspT, WL. lia.
  - apply (mo_ok_le MT ML S1 (mo_free MT) (Z.of_nat (Datatypes.S m) * mo_free MT) HMOK).
    pose proof (mo_free_nonneg MT ML). nia.
  - (* the room round: record m's free is spent from the budget, the rest's stays *)
    rewrite l2_rk. rewrite l2_rk in HRMk. change (Z.to_nat (mo_free MT_rk)) with 1%nat. exact HRMk.
  - (* list_drop's count premise (ldrop_pk = 0): the invariant's *)
    exact HCNk.
  - exact HROM. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hpD & regs2 & mem2 & md2 & -> & HJd & HP2 & HAPK & HERR & HAL2 & (b1 & b2 & Eb1 & Eb2) & Hmle & HRMd).
hp0g HJd.
rewrite ENTH in HJd, Eb1.
set (FP1 := [(hl_v H1, hl_v H1 + AREC * hl_cap H1);
  (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1))]) in HJd.
destruct (l2_callee_keeps G' LDROP_STK (spZ regsT) FP1 ly1 S1 W1 memT mdc ly2 S2 W2 mem2 md2 1 HJd)
  as (K1 & K2 & K3 & Hwle12 & Hfrs12 & HAR2).
rewrite UspT in K1.
assert (HFPS : forall a, fp_spares FP1 a) by (intros a; apply l2_fp_spares; lia).
(* the journal of check_shape_ends after the drop *)
assert (HFP1 : forall a, inFP FP1 a -> (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  Reusable.YCbq.in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hin & Hr). left. cbn [FP1 In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr.
  - split.
    + exists (hl_v (hs_held h), hl_v (hs_held h) + req_size (AREC * hl_cap (hs_held h))). split.
      * unfold blk_FP, list_blks. apply in_map_iff. exists (hl_v (hs_held h), AREC * hl_cap (hs_held h)). split; [reflexivity|].
        apply in_or_app. left. destruct (hl_cap (hs_held h) =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia | left; reflexivity].
      * cbn [fst snd]. rewrite <- HV, <- HC, HreqV. lia.
    + exists (hl_v H1), (AREC * hl_cap H1). split; [exact HvinH|]. rewrite HreqV. lia.
  - rewrite HreqR in Hr. split.
    + exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split.
      * unfold blk_FP, list_blks. apply in_map_iff. exists (fst r, Z.of_nat (length (snd r)) + 1). split; [reflexivity|].
        apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). exact HRIN0.
      * cbn [fst snd]. rewrite HreqR. lia.
    + exists (fst r), (Z.of_nat (length (snd r)) + 1). split; [exact HrB|]. rewrite HreqR. lia. }
pose proof (ajournal_gx_G_mono0 G' G 0 [] LDROP_STK (spZ regsT) FP1 ly1 S1 W1 memT mdc [] ly2 S2 W2 mem2 md2 1 HG'G HJd)
  as HJdG.
pose proof (ajournal_gx_sub0 Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 memT mdc kk
  LDROP_STK (spZ regsT) 0 [] FP1 [] ly2 S2 W2 mem2 md2 1 HJ HJdG
  ltac:(rewrite UspT, WL, WS; lia) ltac:(rewrite UspT; lia) ltac:(rewrite UspT; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ3.
cbn [app] in HJ3.
(* the blocks the drop keeps: every block of the source but the vector and the dropped text *)
assert (NDB : List.NoDup (hs_blocks (CheckRep.set_held h H1))) by (apply NoDup_ListNoDup; exact HNDB).
assert (HVB : In (hl_v H1) (list_blocks H1))
  by (unfold list_blocks; destruct (hl_cap H1 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia | apply in_or_app; left; left; reflexivity]).
assert (HRB : In (fst r) (list_blocks H1)) by (unfold list_blocks; apply in_or_app; right; apply in_map; exact HRIN).
assert (HOTH : forall b, In b (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
  b <> hl_v H1 /\ b <> fst r).
{ intros b Hb. unfold hs_blocks in NDB. cbn [CheckRep.set_held hs_pending hs_partial hs_expected hs_held] in NDB.
  rewrite !app_assoc in NDB. rewrite !app_assoc in Hb.
  split; intros ->; [exact (l2_nodup_disj _ _ _ NDB Hb HVB) | exact (l2_nodup_disj _ _ _ NDB Hb HRB)]. }
assert (KIN : forall b n, In (b, n) (ablocks B ly1 S1) -> b <> fst r -> In (b, n) (ablocks B ly2 S2)).
{ intros b n Hin Hb. rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hin | [E | Hin]]; apply in_or_app;
  [left; exact Hin | injection E as E _; exfalso; exact (Hb (eq_sym E)) | right; exact Hin]. }
assert (KB : forall b n a, In (b, n) (ablocks B ly1 S1) -> b <> hl_v H1 -> b <> fst r -> b <= a < b + req_size n ->
  abyte_kept W1 memT W2 mem2 a).
{ intros b n a Hin Hb1 Hb2 Ha.
  pose proof (KIN b n Hin Hb2) as Hin2.
  destruct (al0_blocks ly1 S1 W1 memT mdc b n HAR1 Hin) as (B16 & B4096 & Bceil & Bapp & _).
  destruct (al0_blocks ly2 S2 W2 mem2 md2 b n HAR2 Hin2) as (_ & _ & _ & _ & Bp2 & _).
  split.
  - replace a with (b + (a - b)) by lia. apply (K3 b n (a - b)); [lia | | exact Hin | exact Hin2 | lia |].
    + intros HGa'. pose proof (HG'r _ HGa') as Hr'. destruct (l2_HAimg (b + (a - b)) ltac:(unfold ASRC; lia)) as (Hi & _).
      exact (blk_img0 ly1 S1 W1 memT mdc b n (b + (a - b)) HAR1 Hin ltac:(lia) Hi).
    + intros (rr & Hrr & Hrr2). cbn [FP1 In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Hrr2.
      * assert (Hne : (hl_v H1, AREC * hl_cap H1) <> (b, n)) by (intros E; injection E as E _; exact (Hb1 (eq_sym E))).
        pose proof (sep_blocks0 ly1 S1 W1 memT mdc _ _ _ _ HAR1 HvinH Hin Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
      * assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (b, n)) by (intros E; injection E as E _; exact (Hb2 (eq_sym E))).
        pose proof (sep_blocks0 ly1 S1 W1 memT mdc _ _ _ _ HAR1 HrB Hin Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqR in Hd, Hrr2. lia.
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Bp2 a Ha)). }
(* the image bytes the drop keeps: off its own globals, not the allocator's, not errno *)
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ inG G' a -> abyte_kept W1 memT W2 mem2 a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as HI. split.
  - apply K2; [lia | exact Hn | exact Hi | exact Ho | exact He | apply HFPS].
  - intros Hw. apply (l2_writable_kept_w W1 W2 memT mem2 a); [exact (HAPK a Hi Ho He) | exact Hwle12 | exact Hw]. }
assert (KH : forall a, HA <= a < HA + 80 -> abyte_kept W1 memT W2 mem2 a).
{ intros a Ha. destruct (l2_HAimg a ltac:(unfold ASRC; lia)) as (Hi & Ho & He & _).
  apply KI; [exact Hi | exact Ho | exact He | intros X; pose proof (HG'r a X); lia]. }
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
assert (SRC2 : asrc_at B ly2 S2 W2 mem2 HA (CheckRep.set_held h (ldrop_list H1 m))).
{ rewrite <- (l2_set_held_twice h H1 (ldrop_list H1 m)).
  apply (l2_src_swap ly1 S1 W1 memT ly2 S2 W2 mem2 HA (CheckRep.set_held h H1) (ldrop_list H1 m) HSRC KH).
  - intros rr Hrr a Ha. cbn [CheckRep.set_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr, HPJ, HPART.
    destruct Hrr as [<- | Hrr].
    + destruct (HOTH (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as [Hb1 Hb2].
      apply (KB (hs_partial h) APARTIAL a HPART Hb1 Hb2).
      unfold gfp, bzs in Ha. rewrite length_map in Ha. cbn [fst snd] in Ha. rewrite HPJ in Ha.
      unfold req_size, APARTIAL in *. cbn. lia.
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * refine (l2_list_kept2 ly1 S1 W1 W2 memT mem2 (HA + 16) (hs_pending h) false HPEND _ _ rr Hrr a Ha).
        -- intros x Hx. apply KH. lia.
        -- intros b n x Hbn Hx. destruct (HOTH b ltac:(apply in_or_app; left; exact (l2_blks_blocks _ _ _ Hbn))) as [Hb1 Hb2].
           exact (KB b n x (l2_alist_blks_in _ _ _ _ _ _ _ HPEND _ Hbn) Hb1 Hb2 Hx).
      * refine (l2_list_kept2 ly1 S1 W1 W2 memT mem2 (HA + 64) (hs_expected h) true HEXP _ _ rr Hrr a Ha).
        -- intros x Hx. apply KH. lia.
        -- intros b n x Hbn Hx.
           destruct (HOTH b ltac:(apply in_or_app; right; apply in_or_app; right; exact (l2_blks_blocks _ _ _ Hbn))) as [Hb1 Hb2].
           exact (KB b n x (l2_alist_blks_in _ _ _ _ _ _ _ HEXP _ Hbn) Hb1 Hb2 Hx).
  - intros [b n] Hbb. cbn [CheckRep.set_held hs_partial hs_pending hs_expected] in Hbb, HPART. destruct Hbb as [Hbb | Hbb].
    + injection Hbb as <- <-. apply KIN; [exact HPART|].
      exact (proj2 (HOTH (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity))).
    + apply in_app_or in Hbb as [Hbb | Hbb].
      * apply KIN; [exact (l2_alist_blks_in _ _ _ _ _ _ _ HPEND _ Hbb)|].
        exact (proj2 (HOTH b ltac:(apply in_or_app; left; exact (l2_blks_blocks _ _ _ Hbb)))).
      * apply KIN; [exact (l2_alist_blks_in _ _ _ _ _ _ _ HEXP _ Hbb)|].
        exact (proj2 (HOTH b ltac:(apply in_or_app; right; apply in_or_app; right; exact (l2_blks_blocks _ _ _ Hbb)))).
  - exact HAL2.
  - exact (l2_nodup_hs_drop (CheckRep.set_held h H1) m ltac:(cbn [CheckRep.set_held hs_held]; lia)
      ltac:(cbn [CheckRep.set_held hs_held]; lia) HNDB). }
assert (MEM2 : l2_mem m ly2 S2 (kk + 1) (ldrop_list H1 m) W2 mem2 md2).
{ split; [exact HJ3|]. split; [exact SRC2|].
  split; [unfold ldrop_list; cbn [HarnessRep.hl_v]; exact HV|].
  split; [unfold ldrop_list; cbn [HarnessRep.hl_cap]; exact HC|].
  split; [rewrite (l2_ldrop_recs H1 _ _ m Hle HREC); f_equal; symmetry; apply l2_kp_hit; [lia | exact HPT]|].
  split.
  { intros rest Hp. rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT) in Hp. cbn [map] in Hp.
    assert (Hp' : Permutation (ablocks B ly S)
      (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (filter (fun r => CheckRep.prefixb P (snd r))
        (skipn (Datatypes.S m) (hl_recs (hs_held h)))) ++ (fst r, Z.of_nat (length (snd r)) + 1) :: rest))
      by (eapply Permutation_trans; [exact Hp | apply Permutation_middle]).
    pose proof (HPERM _ Hp') as Hp1. rewrite Eb1 in Hp1. rewrite Eb2.
    apply (Permutation_cons_inv (a := (fst r, Z.of_nat (length (snd r)) + 1))).
    eapply Permutation_trans; [apply Permutation_middle | exact Hp1]. }
  split; [rewrite Hfrs12; exact HFRS|].
  split.
  { rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT). cbn [length]. rewrite Nat2Z.inj_succ.
    match goal with |- mo_le _ _ _ (Z.succ ?x * _) =>
      replace (Z.succ x * mo_free MT) with (x * mo_free MT + mo_free MT) by ring end.
    exact (mo_le_trans MT ML _ _ _ _ _ HMLE Hmle). }
  split.
  { apply (mo_ok_step MT ML S1 S2 (mo_free MT) (Z.of_nat m * mo_free MT)); [|exact Hmle].
    replace (mo_free MT + Z.of_nat m * mo_free MT) with (Z.of_nat (Datatypes.S m) * mo_free MT) by (rewrite Nat2Z.inj_succ; ring).
    exact HMOK. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as (Hne & Hpin).
    assert (Hd : forall rr, {in_zr a rr} + {~ in_zr a rr}).
    { intros rr. unfold in_zr. destruct (Z_le_gt_dec (fst rr) a); destruct (Z_lt_ge_dec a (fst rr + snd rr));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Hno].
    - exact (rom_pinned_view0 ly2 S2 W2 mem2 md2 a HAR2 (Hpin Hown)).
    - assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
      rewrite (proj1 (KI a Hi Hno Hne (proj2 (proj2 (HROMS' a Hr))))). exact (HROM a Hr). }
  split.
  { apply (l2_saved_kept W1 W2 memT mem2 sp0 regs0); [|exact HSAV]. intros a Ha.
    apply K1; [lia | intros X; pose proof (HG'r a X); lia | lia | rewrite WL; lia]. }
  split.
  { apply (l2_vm_keep W1 W2 memT mem2); [|exact MAT]. intros x Hx. cbn in Hx.
    apply K1; [lia | intros X; pose proof (HG'r x X); lia | lia | rewrite WL; lia]. }
  split.
  { apply (l2_vm_keep W1 W2 memT mem2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
    assert (Ex : x = VAL A_g_gone) by lia. subst x. destruct l2_gone_img as (Hi & Ho & He).
    apply (proj1 (KI _ Hi Ho He ltac:(intros X; pose proof (HG'r _ X) as Hx';
      destruct (l2_HAimg (VAL A_g_gone) ltac:(unfold ASRC; lia)) as (_ & _ & _ & _ & Hg); apply Hg; lia))). }
  (* errno: ldrop_post keeps its view (the conjunct after apres_kept) *)
  split; [intros i Hi; rewrite (HERR i Hi); exact (MER i Hi)|].
  (* the room round: list_drop's post room is the rest's budget; the counts fell by record m's block *)
  split; [exact HRMd|].
  rewrite Eb2. rewrite Eb1 in HCNk. refine (cnt_ok_pk_mono RP _ _ _ _ _ HCNk).
  intros P0. pose proof (ReplyCnt.acnt_del_le P0 b1 b2 (fst r, Z.of_nat (length (snd r)) + 1)). lia. }
assert (REGS2 : l2_regs regs2 m).
{ assert (P2 : getr regs2 2 = getr regsT 2) by (apply (HP2 2); unfold acallee_saved; lia).
  assert (P3 : getr regs2 3 = getr regsT 3) by (apply (HP2 3); unfold acallee_saved; lia).
  assert (P4 : getr regs2 4 = getr regsT 4) by (apply (HP2 4); unfold acallee_saved; lia).
  assert (P27 : getr regs2 27 = getr regsT 27) by (apply (HP2 27); unfold acallee_saved; lia).
  assert (P8 : getr regs2 8 = getr regsT 8) by (apply (HP2 8); unfold acallee_saved; lia).
  assert (P9 : getr regs2 9 = getr regsT 9) by (apply (HP2 9); unfold acallee_saved; lia).
  assert (P18 : getr regs2 18 = getr regsT 18) by (apply (HP2 18); unfold acallee_saved; lia).
  assert (P19 : getr regs2 19 = getr regsT 19) by (apply (HP2 19); unfold acallee_saved; lia).
  assert (P21 : getr regs2 21 = getr regsT 21) by (apply (HP2 21); unfold acallee_saved; lia).
  unfold l2_regs. rewrite P2, P3, P4, P27, P8, P9, P18, P19, P21. exact HR. }
rewrite T1. apply Kont. split; [lia|]. exists ly2, S2, (kk + 1), (ldrop_list H1 m). split; [exact MEM2 | exact REGS2].
Qed.

(* ---- 0x858c4 .. 0x85918: the record's traps (bltu refuted by trap_ptr_wrap_atom; the rest decided), the shadow
   checks of v[m]'s two words, has_prefix(v[m].s, v[m].n, PF); beqz a0: no match -> 0x85928, a match -> list_drop
   (l2_drop) ---- *)
Lemma l2_ent : forall m W1 regs1 mem1 md1, l2_mid m W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_inv m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_l2t)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_l2e)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR & R10 & R11) Kont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof HM as (HJ & HSRC & HV & HC & HREC & _ & _ & _ & _ & HROM & _).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (al0_blocks ly1 S1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (unfold AREC in Vceil; lia).
(* the record v[m] *)
set (r := nth m (hl_recs (hs_held h)) (0, [])).
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
rewrite Forall_forall in HFallH. destruct (HFallH r HRIN) as (HrB & HrG & HrL & _).
destruct (HrL eq_refl) as (HrNZ & HrLEN). unfold APARTIAL in HrLEN.
destruct (al0_blocks ly1 S1 W1 mem1 md1 _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
rewrite HreqR in Hrceil, Hrapp.
destruct (l2_rec_fields B ly1 S1 W1 mem1 (HA + 80) H1 true m HAH ltac:(lia)) as (Ms0 & Ml0).
rewrite ENTH, HV in Ms0, Ml0. rewrite Z.mod_small in Ms0, Ml0 by lia.
set (RA := hl_v (hs_held h) + AREC * Z.of_nat m) in *.
assert (HRA : 4096 <= RA /\ hl_v H1 <= RA /\ RA + 16 <= hl_v H1 + AREC * hl_cap H1 /\ RA mod 16 = 0).
{ unfold RA, AREC. rewrite <- HV. unfold hl_n in *. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Zplus_mod, V16. replace (16 * Z.of_nat m) with (Z.of_nat m * 16) by lia. rewrite Z_mod_mult. reflexivity. }
assert (HRapp : in_app RA 16) by (apply (in_app_sub (hl_v H1) (AREC * hl_cap H1)); [exact Vapp | lia | lia | lia]).
pose proof (range_addressable_of_block0 ly1 S1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR1 HvinH
  ltac:(lia) ltac:(rewrite HreqV; lia)) as HRAR.
assert (Ms1 : val_mem SEGS (arm W1 mem1) RA 8 (fst r)) by (unfold RA, AREC; exact Ms0).
assert (Ml1 : val_mem SEGS (arm W1 mem1) (RA + 8) 8 (Z.of_nat (length (snd r)))) by (unfold RA, AREC; exact Ml0).
destruct (l2e_state W1 regs1 mem1 (sp0 - 112) RA (hl_v (hs_held h)) (Z.of_nat m) (fst r) (Z.of_nat (length (snd r)))
  R2 R10 R11 R19 R21 HSPb HSPa ltac:(lia) ltac:(lia) ltac:(rewrite <- HV; lia) ltac:(rewrite <- HV; exact V16)
  ltac:(unfold hl_n in Hn26; lia) HRapp ltac:(lia) ltac:(lia) Ms1 Ml1 HRAR) as [HS SHOK].
pose proof alloc_ceiling_val as ACV.
remember (Eimg (Ereg regs1 (l2_xe (fst r) (Z.of_nat (length (snd r)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j0, (j0 < 2)%nat -> ew E (32 + j0) = nth j0 (l2_xe (fst r) (Z.of_nat (length (snd r)))) (Z_to_bv 64 0)).
{ intros j0 Hj0. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 (fst r)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 1%nat ltac:(lia)).
clear EX.
assert (E10 : ew E 10 = Z_to_bv 64 (hl_v (hs_held h) + AREC * Z.of_nat m)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (hl_v (hs_held h))) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EEo 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = RA) by (rewrite E10; apply unsigned_lit_small; lia).
pose proof HS as HS0.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ SHOK l2_Bspan AF_fr_has_prefix.
{ apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_rec] in Ha; lia | apply awr_ok_x_nil]. }
psrr_branch_tok RUNTOx BR HS SHOK l2_Bspan.
{ (* bltu a0,a1 taken: &v[m] = v + 16 m does not wrap *)
  exfalso. rewrite (trap_ptr_wrap_atom E 10 11 (hl_v (hs_held h)) (AREC * Z.of_nat m) E10 E11) in Hc
    by (unfold AREC, hl_n in *; lia). discriminate Hc. }
clear Hc.
paj_run_to_tok_x RUNTOx HS HJ SHOK l2_Bspan AF_fr_has_prefix.
{ cbn [ss_mem add_cond].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_rec] in Ha; lia | apply awr_ok_x_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_back).
assert (PRESr : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; l2_pres_back Hp).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 _ _ kk HJ)
  as (memS & HJi & HgS).
assert (HAR3 : AR0 ly1 S1 W1 (ms_mem ms0) mdc) by exact (proj1 HJi).
assert (Usp1 : spZ (ms_regs ms0) = sp0 - 112) by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite Q2; exact Usp).
pose proof l2_PF_low as HPlow.
assert (HPREh : AFP0 HP_STK ly1 S1 W1 (ms_regs ms0) (ms_mem ms0) mdc []).
{ eapply (afn_pre_at0 (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms0) mdc kk
    (ms_regs ms0) HP_STK (- 112 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - rewrite WS. unfold HP_STK, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, (EEo 8%nat 8%bv eq_refl), R8. rewrite unsigned_lit_small by lia. lia. }
(* the prefix's bytes are read-only, so they are the entry's *)
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi). rewrite KEEPr by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
assert (RV0 : rom_view SEGS W1 (ms_mem ms0)) by (intros a Hr; rewrite ROMK by exact Hr; exact (HROM0 a Hr)).
destruct (l2_pfx_keep ly1 S1 W1 (ms_mem ms0) mdc kk HJ RV0) as (PK & HRAP & HHVP0).
assert (HHVP : 0 < PLEN + 1 -> shadow_hull_vis (aview SEGS (w_H W1) (ms_mem ms0)) PF (PLEN + 1)) by (intros _; exact HHVP0).
assert (TXT : l2_bytes W1 (ms_mem ms0) (fst r) (snd r ++ [Z_to_bv 8 0])).
{ apply l2_bytes_of_garr8. apply (l2_g8_keep W1 W1 mem1 (ms_mem ms0)); [|exact HrG].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. apply KEEPr. lia. }
assert (PTXT : l2_bytes W1 (ms_mem ms0) PF (P ++ [Z_to_bv 8 0])).
{ intros t Ht. rewrite length_app in Ht. cbn [length] in Ht. rewrite PK by lia.
  destruct (Z_lt_ge_dec t PLEN) as [Hlt | Hge].
  - rewrite app_nth1 by lia. exact (HPB t ltac:(lia)).
  - assert (Ht' : t = PLEN) by lia. rewrite Ht'. rewrite app_nth2 by lia.
    replace (Z.to_nat PLEN - length P)%nat with 0%nat by lia. cbn [nth]. rewrite HPN. reflexivity. }
eapply SRr_bind.
{ apply (HP W1 ly1 S1 [] (ms_regs ms0) (ms_mem ms0) mdc [] (fst r) (Z.of_nat (length (snd r))) PF PLEN HPREh).
  - rewrite Q10, E32. reflexivity.
  - rewrite Q11, E33. reflexivity.
  - rewrite Q12, (EEo 8%nat 8%bv eq_refl), R8. reflexivity.
  - lia.
  - lia.
  - exact HPl.
  - exact HPF0.
  - lia.
  - lia.
  - lia.
  - split; [lia|]. split.
    + intros k Hk. exists (bv_unsigned (nth (Z.to_nat k) P (Z_to_bv 8 0))). split.
      * rewrite PK by lia. exact (HPB k Hk).
      * intros H0z. apply HPz. assert (Hn0 : nth (Z.to_nat k) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite H0z; reflexivity).
        rewrite <- Hn0. apply nth_In. lia.
    + intros _. rewrite PK by lia. exact HPN.
  - intros a Ha. rewrite PK by lia. exact (proj1 (HPV a ltac:(lia))).
  - unfold hp_off. rewrite Usp1. intros a Ha. destruct (HPV a ltac:(lia)) as [_ Hn]. unfold HP_STK, ESTACK. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact (HHVP ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). rewrite PK by lia.
    exact (proj1 (HPV a ltac:(lia))).
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle2. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (fst r + (a - fst r)) by lia.
      rewrite (TXT (a - fst r) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + unfold hp_off. rewrite Usp1. intros a Ha. unfold HP_STK, ESTACK in *. lia.
    + apply l2_amem_of_app. apply (in_app_sub (fst r) (Z.of_nat (length (snd r)) + 1)); [exact Hrapp | lia | lia | lia].
    + eapply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms0) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms0) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (l2_shv_sub _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) (HHVP ltac:(lia))). }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HFRc & HRES).
rewrite Usp1 in HJc, HFRc.
assert (HB : exists b, (b = 0 \/ b = 1) /\ getr regs2 10 = w64 b /\ (b = 1 <-> CheckRep.prefixb P (snd r) = true)).
{ destruct HRES as [(Hle2 & Hpre & Hr10) | (Hnp & Hr10)].
  - exists 1. split; [right; reflexivity|]. split; [exact Hr10|]. split; [intros _|intros _; reflexivity].
    apply (proj1 (l2_prefixb_iff W1 (ms_mem ms0) (fst r) PF (snd r) P TXT PTXT)). split; assumption.
  - exists 0. split; [left; reflexivity|]. split; [exact Hr10|]. split; [intros Hc; discriminate Hc|].
    intros Hp. exfalso. destruct (proj2 (l2_prefixb_iff W1 (ms_mem ms0) (fst r) PF (snd r) P TXT PTXT) Hp) as (Hl3 & Hpr).
    exact (Hnp Hl3 Hpr). }
destruct HB as (b & Hb01 & Hb10 & HbP).
assert (HJc' : AJ0 G 0 [] HP_STK (sp0 - 112) [] ly1 S1 W1 (ms_mem ms0) mdc [] ly1 S1 W2 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|].
  apply ajournal_gx_nil_x. exact HJc. }
pose proof (ajournal_gx_sub0 Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W1 (ms_mem ms0) mdc kk HP_STK (sp0 - 112) 0 [] [] [] ly1 S1 W2 mem2 md2 0 HJ HJc'
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U10.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRc; [lia|]. unfold HP_STK, ESTACK. lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (F40 : ew Ea 40 = w64 b) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hb10).
clear HEa.
assert (F10 : ew Ea 10 = Z_to_bv 64 RA) by (rewrite OLDa by lia; exact E10).
assert (F21 : ew Ea 21 = Z_to_bv 64 SB) by (rewrite OLDa by lia; rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (HAR2 : AR0 ly1 S1 W2 mem2 md2)
  by exact (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 mem2 md2 kk HJ2).
assert (SHOK2 : sh_ok SEGS l2_Bx l2_SHe Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, l2_SHe. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (range_addressable_of_block0 ly1 S1 W2 mem2 md2 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR2 HvinH
      ltac:(lia) ltac:(rewrite HreqV; lia)).
  - unfold l2_Bx. rewrite (U_atom Ea 21 SB F21) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 10 RA F10) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. destruct HRapp as [_ [HH | [HH _]]];
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) by (intros a Ha Hs; rewrite HFRc by assumption; apply KEEPr; exact Ha).
assert (PRES2 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) by (intros a Hp; exact (HPR2 a (PRESr a Hp))).
rewrite Q1.
paj_run_tok_x RUNx HS HJ2 SHOK2 l2_Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
psrr_branch_tok RUNx BR HS SHOK2 l2_Bspan.
- (* beqz taken: no match, on to 0x85928 *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb0 : b = 0) by (apply Z.eqb_eq in Hc; exact Hc).
  assert (HPF : CheckRep.prefixb P (snd r) = false)
    by (destruct (CheckRep.prefixb P (snd r)) eqn:Eq; [exfalso; pose proof (proj2 HbP eq_refl); lia | reflexivity]).
  paj_run_to_tok_x RUNTOx HS HJ2 SHOK2 l2_Bspan A_l2t.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_mem (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms2) mdb).
  { apply (l2_mem_keep (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms2) md1 mdb (sp0 - 112 - HP_STK) (sp0 - 112) HM HJ2);
    [unfold HP_STK, ESTACK; lia | lia | | | exact Hwle2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  pose proof (l2_mem_miss m ly1 S1 kk H1 W2 (ms_mem ms2) mdb Hle HPF MEM1) as MEM0.
  assert (REGS1 : l2_regs (ms_regs ms2) m).
  { unfold l2_regs.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [l2_keepreg2 HS0 HS (19%bv : bv 5) OLDa; exact R19|].
    l2_keepreg2 HS0 HS (21%bv : bv 5) OLDa; exact R21. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_l2t) by (unfold A_l2t, AF_fr_check_shape_ends; lia) end.
  apply Kont. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEM0 | exact REGS1].
- (* beqz not taken: a match, list_drop(&held, m) *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb1 : b = 1) by (destruct Hb01 as [-> | ->]; [discriminate Hc | reflexivity]).
  assert (HPT : CheckRep.prefixb P (snd r) = true) by (apply HbP; exact Hb1).
  paj_run_to_tok_x RUNTOx HS HJ2 SHOK2 l2_Bspan AF_fr_list_drop.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_mem (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms2) mdb).
  { apply (l2_mem_keep (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms2) md1 mdb (sp0 - 112 - HP_STK) (sp0 - 112) HM HJ2);
    [unfold HP_STK, ESTACK; lia | lia | | | exact Hwle2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  assert (REGS1 : l2_regs (ms_regs ms2) m).
  { unfold l2_regs.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [l2_keepreg2 HS0 HS (19%bv : bv 5) OLDa; exact R19|].
    l2_keepreg2 HS0 HS (21%bv : bv 5) OLDa; exact R21. }
  prreg HS (1%bv : bv 5) T1. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
  repeat (rewrite OLDa in T10 by lia). repeat (rewrite OLDa in T11 by lia).
  rewrite (EEo 9%nat 9%bv eq_refl), R9 in T10. rewrite (EEo 19%nat 19%bv eq_refl), R19 in T11.
  assert (T1' : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + A_l2t))
    by (rewrite T1; f_equal; unfold A_l2t, AF_fr_check_shape_ends; lia).
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + AF_fr_list_drop) by (unfold AF_fr_list_drop; lia) end.
  exact (l2_drop m ly1 S1 kk H1 W2 (ms_regs ms2) (ms_mem ms2) mdb Hle HPT MEM1 REGS1 T10 T11 T1' Kont).
Qed.

(* ---- the loop: by induction on the records left, from a fresh symbolic state at the head each turn ---- *)
Lemma l2_loop : forall m W1 regs1 mem1 md1, gone <> 0 -> l2_inv (Datatypes.S m) W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction m as [|m IH]; intros W1 regs1 mem1 md1 Hg Hinv;
  (apply (l2_head _ W1 regs1 mem1 md1 Hinv); intros W2 regs2 mem2 md2 Hmid;
   apply (l2_ent _ W2 regs2 mem2 md2 Hmid); intros W3 regs3 mem3 md3 Hinv3;
   apply (l2_tail _ W3 regs3 mem3 md3 Hinv3 Hg); intros W4 regs4 mem4 md4 Hm Hinv4).
- lia.
- exact (IH W4 regs4 mem4 md4 Hg Hinv4).
Qed.
Lemma l2_set_held_id : forall ly0 S0 (W0 : world SEGS) m0 HA0 (h0 : hsrc),
asrc_at B ly0 S0 W0 m0 HA0 h0 -> asrc_at B ly0 S0 W0 m0 HA0 (CheckRep.set_held h0 (hs_held h0)).
Proof. intros ly0 S0 W0 m0 HA0 h0 H. exact H. Qed.
(* loop 2's first entry (W_cshe_epi.v cshe_l2_in) is the invariant at n = hl_n (hs_held h) records *)
Lemma l2_run : val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> mo_ok MT S (cshe_cost MT (hs_held h)) ->
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) -> cnt_ok_pk RP cshe_pk (ablocks B ly S) ->
forall W1 c1, cshe_l2_in B PST ARx G regs0 ly S W mem md XO AT HA PF gone h W1 c1 -> SRr SEGS W1 c1 Post.
Proof.
intros HAT0 HGN HMO HRM0 HCN0 W1 c1 (regs1 & mem1 & md1 & -> & HJ1 & Q2 & Q3 & Q4 & Q27 & Q8 & Q9 & Q18 & Q19 & Q21 & HSAV1 & HKEEP1 & HPRES1 &
  Hgone & Hn0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
assert (Hlen : exists n', length (hl_recs (hs_held h)) = Datatypes.S n').
{ destruct (length (hl_recs (hs_held h))) as [|n] eqn:E; [unfold hl_n in Hn0; rewrite E in Hn0; lia | exists n; reflexivity]. }
destruct Hlen as (n' & En).
pose proof HJ1 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & Hwle01 & _).
apply (l2_loop n' W1 regs1 mem1 md1 Hgone).
split; [rewrite En; lia|].
exists ly, S, 0, (hs_held h). split.
- split; [exact HJ1|].
  split.
  { apply l2_set_held_id.
    apply (l2_src_step ly S md W W1 mem mem1 HA h (sp0 - CSHE_STK_B) sp0 HAR0 HSRC0); [| lia | | exact HPRES1 | exact Hwle01].
    - intros a Ha. exact (proj1 (l2_HAimg a Ha)).
    - intros a Ha Hno. exact (HKEEP1 a Ha Hno). }
  split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite <- En, firstn_all, skipn_all, list_basics.list.filter_nil, app_nil_r; reflexivity|].
  split; [rewrite <- En, skipn_all, list_basics.list.filter_nil; cbn [map app]; intros rest Hp; exact Hp|].
  split; [reflexivity|].
  split; [rewrite <- En, skipn_all, list_basics.list.filter_nil; cbn [length Z.of_nat]; rewrite Z.mul_0_l;
          exact (mle_start MT S ML)|].
  split; [unfold cshe_cost, hl_n in HMO; rewrite En in HMO; exact HMO|].
  split.
  { intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
    pose proof (pa_img_range a Hi) as HI. rewrite HKEEP1 by (rewrite ?WS; lia). exact (HROM0 a Hr). }
  split; [exact HSAV1|].
  split; [apply (l2_vm_keep W W1 mem mem1); [intros x Hx; cbn in Hx; apply HKEEP1; lia | exact HAT0]|].
  split.
  { apply (l2_vm_keep W W1 mem mem1); [|exact HGN]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
    pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR. apply HKEEP1; rewrite ?WS; lia. }
  (* errno: an image cell, outside [sp0 - CSHE_STK_B, sp0), so cshe_l2_in's kept-view clause gives it *)
  split; [intros i Hi; destruct l2_errno_low as [E0 E1]; apply HKEEP1; rewrite ?WS; lia|].
  (* the room round: cshe_cost MT_rk is one free per record, the loop's budget at n records; the counts are the
     entry's (cshe_pk = 0) *)
  split; [|exact HCN0]. unfold cshe_cost, hl_n in HRM0. rewrite En in HRM0. exact HRM0.
- unfold l2_regs. unfold hl_n in Q19. rewrite En in Q19.
  split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q27|]. split; [exact Q8|].
  split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19 | exact Q21].
Qed.
End loop.

(* ------------------------------------------------------------------ the segment lemma *)
(* Loop 2 of check_shape_ends on image B, from its first entry 0x858ac (cshe_l2_in) to the epilogue's entry 0x8592c
   (cshe_out_B, the gone <> 0 disjunct).  Its premises are cshe_spec's own (lib/B/W_contract.v Section w3e, CSHE_STK
   read as CSHE_STK_B; P's location as W3Checks-2's one disjunctive premise, a working branch fb87b19890f), so the
   composition gives each by assumption. *)
Lemma cshe_l2_B : forall W ly S regs mem md ch XO AT HA (j : nat) PF h P A0 gone (O OUT : Z) (ob : list byte),
AFP0 CSHE_STK_B ly S W regs mem md ch ->
XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j -> (j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK_B <= a < spZ regs + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
((forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (Z.of_nat (length P) + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\
   forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
mo_ok MT S (cshe_cost MT (hs_held h)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) -> cnt_ok_pk RP cshe_pk (ablocks B ly S) ->
forall W1 c1, cshe_l2_in B PST ARx G regs ly S W mem md XO AT HA PF gone h W1 c1 ->
SRr SEGS W1 c1 (cshe_out_B B PST ARx G MT RP regs ly S W mem md XO AT HA A0 gone h P ob kr).
Proof.
intros W ly S regs mem md ch XO AT HA j PF h P A0 gone O OUT ob HPRE HX16 HXtop HSRC HA8 HAlo HAhi HGa Hzs HAj Hj4
  HND0 Hn26 HATl HATh HAT0 HPz HPl HPF0 HPFh HPB HPN HPV HPM1 HPM8 HPRA0 HPLOC HROM0 HGN HMO kr HRM0 HCN0 W1 c1 HIN.
eapply l2_run; eassumption.
Qed.
(* the closure, printed into every build log: Section variables (B, MT, G and the hypotheses LAWS ML HG LDROP HP TL
   HGR HGRR ROMNS HGS, and the contexts) and the axioms, to be checked against toolchain/allowed-axioms.txt *)
Print Assumptions cshe_l2_B.

(* ---- route R: loop 2 at a world relation R, for W_check_shape_ends.v pb_check_shape_ends_xR.  Each X_xR below is the
   strict X above with the journal ajournal_gx_x SEGS B PST ARx -> ajournal_gx_xR SEGS B PST ARx R (AJ0R), SRr SEGS ->
   SRrG SEGS R, and cshe_l2_in / cshe_out_B -> W_cshe_epi.v's cshe_l2_in_xR / cshe_out_B_xR.  The runs are the G runs
   (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, with W_kit_x.v paj_run_tok_xR / paj_run_to_tok_xR), the branch is
   paj_branch_xR, the binds SRrG_bind (R_trans).  has_prefix stays strict (HP): its SRr fact is lifted by SRr_SRrG
   (WLE_R).  list_drop is LDROP_R (W_contract_xR_g3.v ldrop_spec_xR), in place of LDROP.  A call's world step is R, not
   wle, so writability across it comes from presence alone (l2_writable_kept_w_xR).  Section loop's journal-free helpers
   whose closed forms take Section loop's hypotheses (their proofs' lia) are restated in loopR (l2_HAimg_xR, l2t_state_xR,
   ..); l2_regs, l2_regs_eq, l2_rk, l2_set_held_id, l2_nodup_disj and l2_blks_blocks are used as they are.  The strict
   texts above are unchanged. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis LDROP_R : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_xR B PST ARx R MT RP G' (BASE + AF_fr_list_drop).
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* the walk at the empty ghost list over the R journal: AJ0R / AJi0R, and the kit's R lemmas at [] *)
Local Notation AJ0R G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR SEGS B PST ARx R G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR SEGS B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
Local Notation ajournal_gx_AR0R G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_xR SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0R G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_xR SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_G_mono0R G0 G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_xR SEGS B PST ARx G0 G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_sub0R Hs G0 STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k
    STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1 :=
  (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hs R_trans G0 STK sp0 XO0 OUT0 FP ly S [] W mem md own lyc Sc [] Wc memc mdc k
     STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 [] W2 mem2 md2 k1).
Local Notation ajournal_gx_init0R G0 XO OUT STK FP ly S W regs mem md ch :=
  (ajournal_gx_init_xR SEGS B PST ARx R_refl G0 XO OUT STK FP ly S [] W regs mem md ch).
Local Notation afn_pre_at0R STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 :=
  (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k regsc STK1 o ch1).
Local Notation aj_bcmp_gx_at0R pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw :=
  (aj_bcmp_gx_at_xR B PST ARx LAWS R_trans WLE_R pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S [] W0 mem md own lyc Sc [] mdc
     k x y n o raw).

(* l2_writable_kept_w without wle: writability across a step that keeps presence, at any world relation (where the byte
   is hidden or absent, its writability is the segment's) *)
Lemma l2_writable_kept_w_xR : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof.
intros W W' m m' a Hp Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EHb.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [Hh _]. rewrite EHb in Hh. discriminate.
- destruct (m' (Z_to_bv 64 a)) as [b2|] eqn:Emb; [discriminate|].
  destruct (w_H W (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [_ [b3 Hb3]]. rewrite Emb in Hb3. discriminate.
Qed.
(* l2_src_step across a step at R (writability from presence alone) *)
Lemma l2_src_step_xR : forall ly1 S1 md1 (W1 W2 : world SEGS) m1 m2 HA1 h1 lo hi,
AR0 ly1 S1 W1 m1 md1 -> asrc_at B ly1 S1 W1 m1 HA1 h1 ->
(forall a, HA1 <= a < HA1 + ASRC -> in_img SEGS a) -> alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> R W1 W2 ->
asrc_at B ly1 S1 W2 m2 HA1 h1.
Proof.
intros ly1 S1 md1 W1 W2 m1 m2 HA1 h1 lo hi HAR HS Himg Hlo HK Hp Hw.
pose proof (asan_consts) as (C1 & _).
apply (l2_src_kept ly1 S1 W1 W2 m1 m2 HA1 h1 HS).
- intros a Ha. split; [|intros Hwr; exact (l2_writable_kept_w_xR W1 W2 m1 m2 a (Hp a) Hwr)].
  pose proof (pa_img_range a (Himg a Ha)) as HI. apply HK; lia.
- intros b n a Hin Ha. split; [|intros Hwr; exact (l2_writable_kept_w_xR W1 W2 m1 m2 a (Hp a) Hwr)].
  destruct (al0_blocks ly1 S1 W1 m1 md1 b n HAR Hin) as (_ & B4096 & Bceil & _).
  apply HK; lia.
Qed.
(* l2_callee_keeps over the R journal: the callee's world step is R *)
Lemma l2_callee_keeps_xR : forall G' STK1 sp1 FP1 ly1 S1 (W1 : world SEGS) m1 md1 ly2 S2 (W2 : world SEGS) m2 md2 k,
AJ0R G' 0 [] STK1 sp1 FP1 ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ inG G' a -> alloc_ceiling <= a -> ~ (sp1 - STK1 <= a < sp1) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ inG G' a -> in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP1 a ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
(forall p n i, 0 <= p + i < 2 ^ 64 -> ~ inG G' (p + i) -> In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) ->
  0 <= i < req_size n -> ~ inFP FP1 (p + i) -> aview SEGS (w_H W2) m2 (p + i) = aview SEGS (w_H W1) m1 (p + i)) /\
R W1 W2 /\ frames S2 = frames S1 /\ AR0 ly2 S2 W2 m2 md2.
Proof.
intros G' STK1 sp1 FP1 ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k HJ.
destruct (ajournal_gx_inner0R G' 0 [] STK1 sp1 FP1 ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 k HJ) as (memS & HJi & Hag).
rewrite !Z.add_0_r in HJi.
destruct HJi as (HAR & _ & _ & Rw & _ & Hfrs & _ & _ & F1 & F2 & F3 & _).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G' a -> aview SEGS (w_H W1) memS a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hn. apply Hag. rewrite unsigned_lit_small by lia. exact Hn. }
split; [intros a Ha Hn Hc Hs; rewrite (F1 a ltac:(lia) Hs); exact (AG a Ha Hn)|].
split; [intros a Ha Hn Hi Ho He Hf; rewrite (F3 a Hi Ho He (HPST a Hi) Hf); exact (AG a Ha Hn)|].
split; [intros p n i Ha Hn Hin1 Hin2 Hi Hf; rewrite (F2 p n i Hin1 Hin2 Hi Hf); exact (AG (p + i) Ha Hn)|].
split; [exact Rw|]. split; [rewrite Hfrs; reflexivity | exact HAR].
Qed.

(* ------------------------------------------------------------------ the loop at R *)
Section loopR.
(* Section loop's variables, notations and hypotheses, verbatim, with Post at cshe_out_B_xR .. R .. *)
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 gone : Z) (j : nat) (h : hsrc) (P ob : list byte).
(* the room round: the caller's room budget past the call (cshe_post_x's kr) *)
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation R0 := (hl_recs (hs_held h)).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_out_B_xR B PST ARx G R MT RP regs0 ly S W mem md XO AT HA A0 gone h P ob kr).
Local Notation PLEN := (Z.of_nat (length P)).
(* the records past the first m: those dropped (they have the prefix), those kept *)
Local Notation DS m := (filter (fun r => CheckRep.prefixb P (snd r)) (skipn m (hl_recs (hs_held h)))).
Local Notation KP m := (filter (fun r => negb (CheckRep.prefixb P (snd r))) (skipn m (hl_recs (hs_held h)))).
Hypothesis HPRE : AFP0 CSHE_STK_B ly S W regs0 mem md ch.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 4096 <= HA.
Hypothesis HAhi : HA + ASRC <= kLowMemEnd.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis HAj : HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j.
Hypothesis Hj4 : (j < 4)%nat.
Hypothesis HND0 : NoDup (CheckRep.texts (hs_held h)).
Hypothesis Hn26 : hl_n (hs_held h) < 2 ^ 26.
Hypothesis HPz : ~ In (Z_to_bv 8 0) P.
Hypothesis HPl : PLEN + 1 < 2 ^ 32.
Hypothesis HPF0 : 0 < PF.
Hypothesis HPFh : PF + PLEN + 8 <= 2 ^ 63.
Hypothesis HPB : forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0))).
Hypothesis HPN : aview SEGS (w_H W) mem (PF + PLEN) = Some 0.
Hypothesis HPV : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (sp0 - CSHE_STK_B <= a < sp0 + XO).
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
Hypothesis HPRA0 : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
(* where P lives (cshe_spec's one premise): a read-only literal, or a buffer inside one of the entry's fake frames *)
Hypothesis HPLOC : ((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1)) \/
  (exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))).
Hypothesis HROM0 : rom_view SEGS W mem.
Hypothesis HSRC0 : asrc_at B ly S W mem HA h.

(* l2_HAimg / l2_gone_img at loopR's variables *)
Lemma l2_HAimg_xR : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a /\ ~ (VAL A_g_gone <= a < VAL A_g_gone + 1).
Proof.
intros a Ha. unfold ASRC in *.
assert (Hs : VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384) by (rewrite HAj in Ha; lia).
destruct (HGS a Hs) as (Hi & Hr & Hg & _).
assert (Hg' : inG cshe_ro_B a).
{ unfold inG, cshe_ro_B. apply Exists_exists. exists (VAL (A_OBJ 19), 384). split; [right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
destruct (HGR a Hg') as (_ & Ho & _). pose proof (proj1 (HGRR a Hg')) as He.
split; [exact Hi|]. split; [exact Ho|]. split; [exact He|]. split; [exact Hr | exact Hg].
Qed.
Lemma l2_gone_img_xR : in_img SEGS (VAL A_g_gone) /\ ~ Exists (in_zr (VAL A_g_gone)) (as_owned_static B) /\
  ~ (as_errno B <= VAL A_g_gone < as_errno B + 4).
Proof.
assert (Hg' : inG cshe_ro_B (VAL A_g_gone)).
{ unfold inG, cshe_ro_B. apply Exists_exists. exists (VAL A_g_gone, 1). split; [left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
destruct (HGR _ Hg') as (Hi & Ho & _). pose proof (proj1 (HGRR _ Hg')) as He.
split; [exact Hi|]. split; [exact Ho | exact He].
Qed.
(* l2_azs_sub, l2_alist_blks_in, l2_list_kept2, l2_fp_spares and l2t_state at loopR's variables *)
Lemma l2_azs_sub_xR : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & H1 & H2) Ha Hn. exists r. split; [exact Hin|]. split; [exact H8|]. lia. Qed.
Lemma l2_alist_blks_in_xR : forall ly0 S0 W0 m0 LA l lines, alist_at B ly0 S0 W0 m0 LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 LA l lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
  destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. exact (proj1 (HF x Hx)).
Qed.
Lemma l2_list_kept2_xR : forall ly1 S1 (W1 W2 : world SEGS) m1 m2 LA l lines,
alist_at B ly1 S1 W1 m1 LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (alist_blks l) -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (alist_fp LA l).
Proof.
intros ly1 S1 W1 W2 m1 m2 LA l lines HL KH KB. destruct HL as (_ & _ & _ & _ & (Hn & Hc) & Hv & _ & _ & HF).
rewrite Forall_forall in HF.
intros rr Hr a Ha. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [apply KH; exact Ha|].
apply in_app_or in Hr as [Hr | Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
  destruct Hv as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  apply (KB (hl_v l) (AREC * hl_cap l) a); [unfold alist_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app, l2_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul in Ha.
  change (Z.of_nat 16) with 16 in Ha. unfold hl_n in Hj. unfold req_size, AREC in *.
  destruct (16 * hl_cap l =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
- apply in_map_iff in Hr as (x & <- & Hx).
  apply (KB (fst x) (Z.of_nat (length (snd x)) + 1) a).
  + unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha.
    unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
Qed.
Lemma l2_fp_spares_xR : forall v cv q nq a, 4096 <= v -> 4096 <= q ->
fp_spares [(v, v + cv); (q, q + nq)] a.
Proof.
intros v cv q nq a Hv Hq (rr & Hin & Hr). exfalso. cbn [In] in Hin.
destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma l2t_state_xR : forall (W1 : world SEGS) regs mem1 SP m,
getr regs 2 = w64 SP -> getr regs 19 = w64 m -> 2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> 0 <= m <= 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_l2t
(restrict (w_H W1) (mkst regs (Z_to_bv 64 (BASE + A_l2t)) mem1 (seg_rom SEGS))) /\
sh_ok SEGS l2_Bx l2_SHt (Eimg (Ereg regs [])) (mrestrict (w_H W1) mem1).
Proof.
intros W1 regs mem1 SP m H2 H19 HSP HSPa Hm.
set (E := Eimg (Ereg regs [])).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E19 : ew E 19 = Z_to_bv 64 m) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
split.
- rewrite restrict_mkst_fx. unfold ss_l2t. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor.
  + apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [l2t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E19, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, l2_SHt. constructor.
Qed.

(* the invariant over the R journal (l2_regs reads no journal: the strict one, at regs0 HA PF) *)
Definition l2_mem_xR (m : nat) (ly1 : alayout) (S1 : astate) (kk : Z) (H1 : hlist) (W1 : world SEGS)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v (hs_held h) /\ hl_cap H1 = hl_cap (hs_held h) /\
hl_recs H1 = firstn m (hl_recs (hs_held h)) ++ KP m /\
(forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (DS m) ++ rest) ->
  Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length (DS m)) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat m * mo_free MT) /\
rom_view SEGS W1 mem1 /\ cshe_saved_B W1 mem1 sp0 regs0 /\
val_mem SEGS (arm W1 mem1) AT 8 A0 /\ val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)) /\
rp_RM RP S1 (Z.to_nat (Z.of_nat m * mo_free MT_rk) + kr) /\ cnt_ok RP (ablocks B ly1 S1).
Definition l2_inv_xR (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_mem_xR m ly1 S1 kk H1 W1 mem1 md1 /\ l2_regs regs0 HA PF regs1 m.
Definition l2_mid_xR (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_mem_xR (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 /\ l2_regs regs0 HA PF regs1 m /\
getr regs1 10 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m) /\ getr regs1 11 = w64 (hl_v (hs_held h)).

(* the memory side of the invariant moves across a step that writes only [lo, hi), above the allocator's ceiling
   and below the frame, and keeps presence *)
Lemma l2_mem_keep_xR : forall m ly1 S1 kk H1 (W1 W2 : world SEGS) m1 m2 md1 md2 lo hi,
l2_mem_xR m ly1 S1 kk H1 W1 m1 md1 ->
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 m2 md2 kk ->
alloc_ceiling <= lo -> hi <= sp0 - 112 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> R W1 W2 ->
l2_mem_xR m ly1 S1 kk H1 W2 m2 md2.
Proof.
intros m ly1 S1 kk H1 W1 W2 m1 m2 md1 md2 lo hi
  (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & MAT & MG & MER & HRMk & HCNk) HJ2 Hlo Hhi HK HPs Hw.
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 m1 md1 kk HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
split; [exact HJ2|].
split.
{ apply (l2_src_step_xR ly1 S1 md1 W1 W2 m1 m2 HA _ lo hi HAR1 HSRC); [| exact Hlo | exact HK | exact HPs | exact Hw].
  intros a Ha. exact (proj1 (l2_HAimg_xR a Ha)). }
split; [exact HV|]. split; [exact HC|]. split; [exact HREC|]. split; [exact HPERM|].
split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split.
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi) as HI. rewrite HK by lia. exact (HROM a Hr). }
split.
{ apply (l2_saved_kept W1 W2 m1 m2 sp0 regs0); [|exact HSAV]. intros a Ha. apply HK; lia. }
split; [apply (l2_vm_keep W1 W2 m1 m2); [intros x Hx; cbn in Hx; apply HK; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W2 m1 m2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
  pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR. apply HK; lia. }
split; [intros i Hi; destruct l2_errno_low as [E0 E1]; rewrite HK by lia; exact (MER i Hi)|].
exact (conj HRMk HCNk).
Qed.

(* a record without the prefix: the head moves one record down, nothing else changes *)
Lemma l2_mem_miss_xR : forall m ly1 S1 kk H1 W1 mem1 md1, (Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = false ->
l2_mem_xR (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 -> l2_mem_xR m ly1 S1 kk H1 W1 mem1 md1.
Proof.
intros m ly1 S1 kk H1 W1 mem1 md1 Hm E (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & MAT & MG & MER & HRMk & HCNk).
pose proof (mo_free_nonneg MT ML) as Hf.
split; [exact HJ|]. split; [exact HSRC|]. split; [exact HV|]. split; [exact HC|].
split; [rewrite HREC; apply l2_kp_miss; [lia | exact E]|].
rewrite (l2_ds_miss P (hl_recs (hs_held h)) m ltac:(lia) E).
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|].
split.
{ apply (mok_station MT S1 S1 (Z.of_nat (Datatypes.S m) * mo_free MT) 0 (Z.of_nat m * mo_free MT) ML HMOK
    (mle_start MT S1 ML)); [apply Z.mul_nonneg_nonneg; lia | rewrite Nat2Z.inj_succ; nia]. }
split; [exact HROM|]. split; [exact HSAV|]. split; [exact MAT|]. split; [exact MG|]. split; [exact MER|].
(* the room round: the record is kept, its free's room stays unspent *)
split; [|exact HCNk]. rewrite l2_rk. rewrite l2_rk in HRMk. exact (RMM_of RP S1 (m + kr) (Datatypes.S m + kr) ltac:(lia) HRMk).
Qed.

(* the stack and frame numbers every piece needs (l2_sp_facts at loopR's variables) *)
Lemma l2_sp_facts_xR : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47 /\ (sp0 - 112) mod 16 = 0 /\ alloc_ceiling + CSHE_STK_B <= sp0 /\
  sp0 + XO <= 2 ^ 47 /\ 0 <= XO.
Proof.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HXO : 0 <= XO) by lia.
split; [rewrite WS in Hslo; lia|]. split; [rewrite Zminus_mod, Hal16; reflexivity|]. lia.
Qed.

(* ---- 0x858ac .. 0x858c4 at R ---- *)
Lemma l2_head_xR : forall m W1 regs1 mem1 md1, l2_inv_xR (Datatypes.S m) W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_mid_xR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_l2e)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR) HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts_xR as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
pose proof HM as (HJ & HSRC & HV & HC & HREC & _).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & _).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (al0_blocks ly1 S1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
assert (HSm : 1 <= Z.of_nat (Datatypes.S m) <= 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (l2h_state W1 regs1 mem1 (sp0 - 112) HA (hl_v H1) (Z.of_nat (Datatypes.S m)) R2 R9 R18 R19 R21 HSPb HSPa HA8 HAlo HAhi'
  HvR V16 HSm MvH ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (l2_xh (hl_v H1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat m + 1))
  by (rewrite (EEo 19%nat 19%bv eq_refl), R19; unfold w64; f_equal; lia).
pose proof HS as HS0.
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOx HS HJ SHOK l2_Bspan A_l2e.
{ apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_hd] in Ha; lia | apply awr_ok_x_nil]. }
pmkst HS.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_nowin HFr).
assert (PRES : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (19%bv : bv 5) T19.
rewrite E19, E32 in T10. rewrite (l2_addr_val (hl_v H1) (Z.of_nat m) ltac:(unfold hl_n in Hn26; lia) ltac:(lia)) in T10.
rewrite E32 in T11. rewrite E19, (l2_dec_val (Z.of_nat m) ltac:(unfold hl_n in Hn26; lia)) in T19.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  replace (BASE + k) with (BASE + A_l2e) by (unfold A_l2e, AF_fr_check_shape_ends; lia) end.
apply HKont. split; [lia|].
exists ly1, S1, kk, H1. split; [|split; [|split]].
- apply (l2_mem_keep_xR (Datatypes.S m) ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 _ (sp0 - 112) (sp0 - 112) HM HJ);
  [lia | lia | intros a Ha _; exact (KEEP a Ha) | exact PRES | apply R_refl].
- unfold l2_regs.
  split; [l2_keepreg HS0 HS (2%bv : bv 5); exact R2|].
  split; [l2_keepreg HS0 HS (3%bv : bv 5); exact R3|].
  split; [l2_keepreg HS0 HS (4%bv : bv 5); exact R4|].
  split; [l2_keepreg HS0 HS (27%bv : bv 5); exact R27|].
  split; [l2_keepreg HS0 HS (8%bv : bv 5); exact R8|].
  split; [l2_keepreg HS0 HS (9%bv : bv 5); exact R9|].
  split; [l2_keepreg HS0 HS (18%bv : bv 5); exact R18|].
  split; [exact T19|].
  l2_keepreg HS0 HS (21%bv : bv 5); exact R21.
- rewrite T10, HV. unfold w64, AREC. f_equal.
- rewrite T11, HV. reflexivity.
Qed.

(* ---- 0x85928 at R: bgtz s3, back to the head, else the epilogue's entry 0x8592c ---- *)
Lemma l2_tail_xR : forall m W1 regs1 mem1 md1, l2_inv_xR m W1 regs1 mem1 md1 -> gone <> 0 ->
(forall W2 regs2 mem2 md2, (0 < m)%nat -> l2_inv_xR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_csheB_l2)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_l2t)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR) Hgone HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts_xR as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
pose proof HM as (HJ & _).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
destruct (l2t_state_xR W1 regs1 mem1 (sp0 - 112) (Z.of_nat m) R2 R19 HSPb HSPa ltac:(unfold hl_n in Hn26; lia)) as [HS SHOK].
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat m))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl); exact R19).
pose (RUNx := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose proof HS as HS0.
psrr_branch_tok RUNx BRR HS SHOK l2_Bspan.
- (* bgtz taken: records are left, back to the head *)
  rewrite trap_br_lt, S_SLit, S_SOff, E19, unsigned_lit_small, Z.add_0_r, !swrap64_id in Hc
    by (unfold half64, hl_n in *; lia).
  apply Z.ltb_lt in Hc.
  paj_run_to_tok_xR RUNTOx HS HJ SHOK l2_Bspan A_csheB_l2. { cbn [ss_mem add_cond ss_l2t]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms) rr = getr regs1 rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS0) as X0.
    cbn [ms_regs restrict mkst] in X0. rewrite X1, X0. reflexivity. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_nowin HFr).
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_mem_xR m ly1 S1 kk H1 W1 (ms_mem ms) mdd).
  { apply (l2_mem_keep_xR m ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 mdd (sp0 - 112) (sp0 - 112) HM HJ);
    [lia | lia | intros a Ha _; exact (KEEP a Ha) | intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp) | apply R_refl]. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_csheB_l2) by (unfold A_csheB_l2, AF_fr_check_shape_ends; lia) end.
  apply HKont; [lia|]. split; [exact Hle|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
  exact (l2_regs_eq regs0 HA PF regs1 (ms_regs ms) m RG HR).
- (* bgtz not taken: that was the last record, the epilogue's entry *)
  rewrite trap_br_lt, S_SLit, S_SOff, E19, unsigned_lit_small, Z.add_0_r, !swrap64_id in Hc
    by (unfold half64, hl_n in *; lia).
  apply Z.ltb_ge in Hc. assert (Hm0 : m = 0%nat) by lia. subst m.
  paj_run_to_tok_xR RUNTOx HS HJ SHOK l2_Bspan A_csheB_ret. { cbn [ss_mem add_cond ss_l2t]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms) rr = getr regs1 rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS0) as X0.
    cbn [ms_regs restrict mkst] in X0. rewrite X1, X0. reflexivity. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_nowin HFr).
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_mem_xR 0 ly1 S1 kk H1 W1 (ms_mem ms) mdd).
  { apply (l2_mem_keep_xR 0 ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 mdd (sp0 - 112) (sp0 - 112) HM HJ);
    [lia | lia | intros a Ha _; exact (KEEP a Ha) | intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp) | apply R_refl]. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_csheB_ret) by (unfold A_csheB_ret, AF_fr_check_shape_ends; lia) end.
  apply (SRrG_ret SEGS R R_refl). unfold cshe_out_B_xR.
  pose proof MEMF as (HJm & HSRCm & HVm & HCm & HRECm & HPERMm & HFRSm & HMLEm & HMOKm & HROMm & HSAVm & MATm & MGm & MERm & HRMm & HCNm).
  exists ly1, S1, (ms_regs ms), (ms_mem ms), mdd, kk, H1,
    (filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h))), 0.
  split; [reflexivity|]. split; [exact HJm|].
  split; [rewrite RG; exact R2|]. split; [rewrite RG; exact R3|]. split; [rewrite RG; exact R4|].
  split; [rewrite RG; exact R27|].
  split; [exact HSAVm|]. split; [exact HSRCm|]. split; [exact HVm|]. split; [exact HCm|].
  split.
  { unfold CheckRep.texts. rewrite HRECm. cbn [firstn app skipn].
    try apply NoDup_ListNoDup. apply l2_nodup_filter. try apply NoDup_ListNoDup. exact HND0. }
  split; [left; split; [exact Hgone|]; split; [rewrite HRECm; reflexivity | split; reflexivity]|].
  split; [lia|]. split; [rewrite Z.add_0_r; exact MATm|]. split; [exact MGm|].
  split; [exact HPERMm|]. split; [exact HFRSm|].
  split; [|split; [exact MERm|]; rewrite l2_rk in HRMm; exact HRMm].
  apply (mo_le_mono MT ML _ _ _ _ HMLEm).
  pose proof (mo_free_nonneg MT ML) as Hf.
  assert (HL : (length (filter (fun r => CheckRep.prefixb P (snd r)) (skipn 0 (hl_recs (hs_held h)))) <=
    length (hl_recs (hs_held h)))%nat).
  { pose proof (l2_filter_len (fun r => CheckRep.prefixb P (snd r)) (skipn 0 (hl_recs (hs_held h)))) as X.
    rewrite length_skipn in X. cbn beta in X. lia. }
  unfold hl_n. apply Z.mul_le_mono_nonneg_r; [exact Hf | lia].
Qed.

(* ---- P's facts at a later state of the walk, over the R journal (l2_frame_keep / l2_pfx_keep's proofs) ---- *)
Lemma l2_frame_keep_xR : forall ly1 S1 (W1 : world SEGS) mem1 md1 kk cid pos a,
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk ->
In (cid, pos) (frames S) ->
in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
~ inFP FPc a -> ~ inG G a -> 0 <= a < 2 ^ 64 ->
aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a.
Proof.
intros ly1 S1 W1 mem1 md1 kk cid pos a HJ1 Hin Hr Hnf HnG Ha.
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ1)
  as (memS & HJi & Hag).
destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
rewrite (F4 cid pos a Hin Hr Hnf). apply Hag. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* a byte of FPc (the held list's blocks) lies in a block of the entry (l2_FPc_blk at loopR's variables) *)
Lemma l2_FPc_blk_xR : forall y, inFP FPc y -> exists b n, In (b, n) (ablocks B ly S) /\ b <= y < b + req_size n.
Proof.
intros y (rr & Hin & Hr). unfold blk_FP in Hin. apply in_map_iff in Hin as ([b n] & <- & Hbn). cbn [fst snd] in Hr.
exists b, n. split; [|exact Hr].
pose proof HSRC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
exact (l2_alist_blks_in_xR ly S W mem (HA + 80) (hs_held h) true HAH (b, n) Hbn).
Qed.
Lemma l2_pfx_keep_xR : forall ly1 S1 (W1 : world SEGS) mem1 md1 kk,
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk ->
rom_view SEGS W1 mem1 ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1) /\
shadow_hull_vis (aview SEGS (w_H W1) mem1) PF (PLEN + 1).
Proof.
intros ly1 S1 W1 mem1 md1 kk HJ1 HRV1.
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ1) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPLOC as [(HPROM & HPS) | (cid & pos & HinF & HPfr)].
- (* a read-only literal *)
  assert (PK : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a)
    by (intros a Ha; rewrite (HRV1 a (HPROM a Ha)); symmetry; exact (HROM0 a (HPROM a Ha))).
  destruct (HPS ly1 S1 [] W1 mem1 md1 HAR1) as [HRA HHV].
  split; [exact PK|]. split; [exact HRA | apply HHV; lia].
- (* a buffer in a fake frame of the entry *)
  pose proof HPRE as (HAR0 & _).
  destruct (frame_al640 ly S W mem md cid pos HAR0 HinF) as (Hal & Hbal & Hb64).
  destruct (frames_bounds0 ly S W mem md cid pos HAR0 HinF) as (F4096 & Fceil & Fapp).
  pose proof (cshe_frm_off_img ly S W mem md cid pos HAR0 HinF) as Foff.
  assert (HPfr' : forall a, PF <= a < PF + PLEN + 8 ->
    frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid)
    by (intros a Ha; pose proof (HPfr a Ha) as X; unfold in_zr, frame_rng in X; cbn [fst snd] in X; exact X).
  assert (HFw : frame_addr ly cid pos <= PF /\ PF + PLEN + 8 <= frame_addr ly cid pos + fs_frame_bytes cid).
  { pose proof (HPfr' PF ltac:(lia)). pose proof (HPfr' (PF + PLEN + 7) ltac:(lia)). lia. }
  assert (NG : forall y, y < 65536 \/ 6275072 <= y -> ~ inG G y).
  { intros y Hy HGy. pose proof (pa_img_range y (proj1 (HG y HGy))). lia. }
  assert (NFf : forall y, frame_addr ly cid pos <= y < frame_addr ly cid pos + fs_frame_bytes cid -> ~ inFP FPc y).
  { intros y Hy Hf. destruct (l2_FPc_blk_xR y Hf) as (b & n & Hbn & Hb).
    pose proof (sep_block_frame0 ly S W mem md b n cid pos HAR0 Hbn HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (NFs : forall y, kLowShadowBeg <= y < kHighMemBeg -> ~ inFP FPc y).
  { intros y Hy Hf. destruct (l2_FPc_blk_xR y Hf) as (b & n & Hbn & Hb).
    destruct (al0_blocks ly S W mem md b n HAR0 Hbn) as (_ & _ & _ & (Ha1 & Ha2) & _).
    destruct Ha2 as [Ha2 | [Ha2 _]]; lia. }
  assert (PK : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a).
  { intros a Ha. pose proof (HPfr' a Ha) as Hfa.
    apply (l2_frame_keep_xR ly1 S1 W1 mem1 md1 kk cid pos a HJ1 HinF);
      [left; exact (HPfr a Ha) | exact (NFf a Hfa) | apply NG; destruct Foff; [left | right]; lia | lia]. }
  split; [exact PK|]. split.
  + (* the shadow bytes of P are frame shadow bytes: kept from the entry *)
    pose proof (Z.div_mod (frame_addr ly cid pos) 64 ltac:(lia)) as D1. rewrite Hal, Z.add_0_r in D1.
    pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D2. rewrite Hbal, Z.add_0_r in D2.
    assert (Ef8 : frame_addr ly cid pos / 8 = 8 * (frame_addr ly cid pos / 64)).
    { rewrite D1 at 1. replace (64 * (frame_addr ly cid pos / 64)) with ((8 * (frame_addr ly cid pos / 64)) * 8) by ring.
      apply Z_div_mult. lia. }
    assert (Eb8 : fs_frame_bytes cid / 8 = 8 * (fs_frame_bytes cid / 64)).
    { rewrite D2 at 1. replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by ring.
      apply Z_div_mult. lia. }
    intros x Hx. destruct (HPRA0 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok]. rewrite <- Hsv.
    unfold shadow_of_addr. pose proof (HPfr' x ltac:(lia)) as Hfx.
    assert (Hlo : 8 * (frame_addr ly cid pos / 64) <= x / 8) by (apply Z.div_le_lower_bound; lia).
    assert (Hhi : x / 8 < 8 * (frame_addr ly cid pos / 64) + 8 * (fs_frame_bytes cid / 64))
      by (apply Z.div_lt_upper_bound; lia).
    assert (Hx0 : 0 <= x / 8) by (apply Z.div_pos; lia).
    assert (Hxc : x / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
    apply (l2_frame_keep_xR ly1 S1 W1 mem1 md1 kk cid pos (SHADOW_OFF + x / 8) HJ1 HinF).
    * right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Ef8, Eb8. lia.
    * apply NFs. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
    * apply NG. right. unfold SHADOW_OFF. lia.
    * unfold SHADOW_OFF. lia.
  + (* the hull: visible in any AR state with the frame live; frames and the frame base are the entry's *)
    destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ1)
      as (memS & HJi & _).
    destruct HJi as (_ & Hly & _ & _ & _ & Hfrs & _).
    assert (Efr : frame_addr ly1 cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    assert (HinF1 : In (cid, pos) (frames S1)) by (rewrite Hfrs; exact HinF).
    apply (shadow_hull_vis_of_frame0 ly1 S1 W1 mem1 md1 cid pos PF (PLEN + 1) HAR1 HinF1); rewrite ?Efr; lia.
Qed.
(* l2_PF_low at loopR's variables *)
Lemma l2_PF_low_xR : PF + PLEN + 8 <= alloc_ceiling.
Proof.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPLOC as [(HPROM & _) | (cid & pos & HinF & HPfr)].
- pose proof (HPROM (PF + PLEN + 7) ltac:(lia)) as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range (PF + PLEN + 7) ltac:(exists sg; split; [exact Hsg | exact Hra])). lia.
- pose proof HPRE as (HAR0 & _).
  destruct (frames_bounds0 ly S W mem md cid pos HAR0 HinF) as (_ & Fceil & _).
  pose proof (HPfr (PF + PLEN + 7) ltac:(lia)) as X. unfold in_zr, frame_rng in X. cbn [fst snd] in X. lia.
Qed.

(* ---- the drop of record m at R: list_drop by LDROP_R; writability across its step from presence (HAPK) ---- *)
Lemma l2_drop_xR : forall m ly1 S1 kk H1 W1 regsT memT mdc,
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = true ->
l2_mem_xR (Datatypes.S m) ly1 S1 kk H1 W1 memT mdc -> l2_regs regs0 HA PF regsT m ->
getr regsT 10 = w64 (HA + 80) -> getr regsT 11 = w64 (Z.of_nat m) -> getr regsT 1 = Z_to_bv 64 (BASE + A_l2t) ->
(forall W2 regs2 mem2 md2, l2_inv_xR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_l2t)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_fr_list_drop)) memT (seg_rom SEGS)) mdc) Post.
Proof.
intros m ly1 S1 kk H1 W1 regsT memT mdc Hle HPT HM HR T10 T11 T1 Kont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts_xR as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
assert (WL : LDROP_STK = 16448) by reflexivity.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & MAT & MG & MER & HRMk & HCNk).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 memT mdc kk HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPEND & _ & _ & _ & _ & _ & _ & _ & HPART & _ & _ & _ & HEXP & HAH0 & HNDB).
assert (HAH : alist_at B ly1 S1 W1 memT (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (al0_blocks ly1 S1 W1 memT mdc _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
set (r := nth m (hl_recs (hs_held h)) (0, [])) in *.
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
assert (HRIN0 : In r (hl_recs (hs_held h))) by (unfold r; apply nth_In; lia).
pose proof HFallH as HFallH'. rewrite Forall_forall in HFallH'. destruct (HFallH' r HRIN) as (HrB & HrG & HrL & _).
destruct (al0_blocks ly1 S1 W1 memT mdc _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
rewrite HreqR in Hrceil.
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
pose proof l2_PF_low_xR as HPlow.
(* list_drop's globals: the held list head *)
set (G' := [(HA + 80, 16)]).
assert (HG'G : forall a, inG G' a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)]. unfold in_zr in Ha. cbn [fst snd] in Ha.
  apply HGa. lia. }
assert (HG'r : forall a, inG G' a -> HA + 80 <= a < HA + 96).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)]. unfold in_zr in Ha. cbn [fst snd] in Ha. lia. }
assert (HG' : gx_ok SEGS B G') by exact (gx_ok_sub SEGS B G' G HG'G HG).
assert (HGRT' : gx_rt B G').
{ apply (gx_rt_sub B G' cshe_ro_B); [|exact HGRR]. intros a Ha. pose proof (HG'r a Ha) as Hr.
  unfold inG, cshe_ro_B. apply Exists_exists. exists (VAL (A_OBJ 19), 384). split; [right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. rewrite HAj in Hr. unfold ASRC in Hr. lia. }
assert (HROMS' : forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a).
{ intros a Hr. destruct (ROMNS a Hr) as [He Hp]. split; [exact Hp|]. split; [exact He|].
  intros Ha. pose proof (HG'r a Ha) as Hra. destruct (l2_HAimg_xR a ltac:(unfold ASRC; lia)) as (_ & _ & _ & Hnr & _).
  exact (Hnr Hr). }
pose proof (LDROP_R G' HG' HGRT' HROMS') as LD.
(* list_drop's entry: afn_pre from this function's journal *)
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 memT mdc kk HJ)
  as (memS & HJi & HgS).
assert (UspT : spZ regsT = sp0 - 112)
  by (change (spZ regsT) with (bv_unsigned (getr regsT 2)); rewrite R2; apply unsigned_lit_small; lia).
assert (HPREd : AFP0 LDROP_STK ly1 S1 W1 regsT memT mdc []).
{ eapply (afn_pre_at0R (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 memT mdc kk
    regsT LDROP_STK (- 112 - XO) [] HJi).
  - rewrite UspT. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - rewrite WL. lia.
  - rewrite WL, WS. lia.
  - rewrite T1. apply ret_ok_codeptr_v; [unfold A_l2t, AF_fr_check_shape_ends; lia | reflexivity].
  - unfold raZ. rewrite T1. rewrite unsigned_lit_small by (unfold A_l2t, AF_fr_check_shape_ends; lia).
    unfold A_l2t, AF_fr_check_shape_ends. lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite R8. rewrite unsigned_lit_small by lia. lia. }
eapply (SRrG_bind SEGS R R_trans).
{ refine (LD W1 ly1 S1 [] regsT memT mdc [] (HA + 80) H1 true m HPREd T10 T11 HAH _ _ _ _ _ _ _ _
    (Z.to_nat (Z.of_nat m * mo_free MT_rk) + kr)%nat _ _ _).
  - lia.
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold AREC, hl_n in *. lia.
  - apply (l2_azs_sub_xR (HA + 64) 32); [exact Hzs | lia | lia].
  - intros a Ha. split; [apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia|]. rewrite UspT, WL. lia.
  - intros a Ha. rewrite UspT, WL. lia.
  - apply (mo_ok_le MT ML S1 (mo_free MT) (Z.of_nat (Datatypes.S m) * mo_free MT) HMOK).
    pose proof (mo_free_nonneg MT ML). nia.
  - (* the room round: record m's free is spent from the budget, the rest's stays *)
    rewrite l2_rk. rewrite l2_rk in HRMk. change (Z.to_nat (mo_free MT_rk)) with 1%nat. exact HRMk.
  - (* list_drop's count premise (ldrop_pk = 0): the invariant's *)
    exact HCNk.
  - exact HROM. }
cbv beta. intros W2 c2 Rw2 (ly2 & S2 & hpD & regs2 & mem2 & md2 & -> & HJd & HP2 & HAPK & HERR & HAL2 & (b1 & b2 & Eb1 & Eb2) & Hmle & HRMd).
hp0gR HJd.
rewrite ENTH in HJd, Eb1.
set (FP1 := [(hl_v H1, hl_v H1 + AREC * hl_cap H1);
  (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1))]) in HJd.
destruct (l2_callee_keeps_xR G' LDROP_STK (spZ regsT) FP1 ly1 S1 W1 memT mdc ly2 S2 W2 mem2 md2 1 HJd)
  as (K1 & K2 & K3 & Rw12 & Hfrs12 & HAR2).
rewrite UspT in K1.
assert (HFPS : forall a, fp_spares FP1 a) by (intros a; apply l2_fp_spares_xR; lia).
(* the journal of check_shape_ends after the drop *)
assert (HFP1 : forall a, inFP FP1 a -> (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  Reusable.YCbq.in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hin & Hr). left. cbn [FP1 In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr.
  - split.
    + exists (hl_v (hs_held h), hl_v (hs_held h) + req_size (AREC * hl_cap (hs_held h))). split.
      * unfold blk_FP, list_blks. apply in_map_iff. exists (hl_v (hs_held h), AREC * hl_cap (hs_held h)). split; [reflexivity|].
        apply in_or_app. left. destruct (hl_cap (hs_held h) =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia | left; reflexivity].
      * cbn [fst snd]. rewrite <- HV, <- HC, HreqV. lia.
    + exists (hl_v H1), (AREC * hl_cap H1). split; [exact HvinH|]. rewrite HreqV. lia.
  - rewrite HreqR in Hr. split.
    + exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split.
      * unfold blk_FP, list_blks. apply in_map_iff. exists (fst r, Z.of_nat (length (snd r)) + 1). split; [reflexivity|].
        apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). exact HRIN0.
      * cbn [fst snd]. rewrite HreqR. lia.
    + exists (fst r), (Z.of_nat (length (snd r)) + 1). split; [exact HrB|]. rewrite HreqR. lia. }
pose proof (ajournal_gx_G_mono0R G' G 0 [] LDROP_STK (spZ regsT) FP1 ly1 S1 W1 memT mdc [] ly2 S2 W2 mem2 md2 1 HG'G HJd)
  as HJdG.
pose proof (ajournal_gx_sub0R Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 memT mdc kk
  LDROP_STK (spZ regsT) 0 [] FP1 [] ly2 S2 W2 mem2 md2 1 HJ HJdG
  ltac:(rewrite UspT, WL, WS; lia) ltac:(rewrite UspT; lia) ltac:(rewrite UspT; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ3.
cbn [app] in HJ3.
(* the blocks the drop keeps: every block of the source but the vector and the dropped text *)
assert (NDB : List.NoDup (hs_blocks (CheckRep.set_held h H1))) by (apply NoDup_ListNoDup; exact HNDB).
assert (HVB : In (hl_v H1) (list_blocks H1))
  by (unfold list_blocks; destruct (hl_cap H1 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia | apply in_or_app; left; left; reflexivity]).
assert (HRB : In (fst r) (list_blocks H1)) by (unfold list_blocks; apply in_or_app; right; apply in_map; exact HRIN).
assert (HOTH : forall b, In b (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
  b <> hl_v H1 /\ b <> fst r).
{ intros b Hb. unfold hs_blocks in NDB. cbn [CheckRep.set_held hs_pending hs_partial hs_expected hs_held] in NDB.
  rewrite !app_assoc in NDB. rewrite !app_assoc in Hb.
  split; intros ->; [exact (l2_nodup_disj _ _ _ NDB Hb HVB) | exact (l2_nodup_disj _ _ _ NDB Hb HRB)]. }
assert (KIN : forall b n, In (b, n) (ablocks B ly1 S1) -> b <> fst r -> In (b, n) (ablocks B ly2 S2)).
{ intros b n Hin Hb. rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hin | [E | Hin]]; apply in_or_app;
  [left; exact Hin | injection E as E _; exfalso; exact (Hb (eq_sym E)) | right; exact Hin]. }
assert (KB : forall b n a, In (b, n) (ablocks B ly1 S1) -> b <> hl_v H1 -> b <> fst r -> b <= a < b + req_size n ->
  abyte_kept W1 memT W2 mem2 a).
{ intros b n a Hin Hb1 Hb2 Ha.
  pose proof (KIN b n Hin Hb2) as Hin2.
  destruct (al0_blocks ly1 S1 W1 memT mdc b n HAR1 Hin) as (B16 & B4096 & Bceil & Bapp & _).
  destruct (al0_blocks ly2 S2 W2 mem2 md2 b n HAR2 Hin2) as (_ & _ & _ & _ & Bp2 & _).
  split.
  - replace a with (b + (a - b)) by lia. apply (K3 b n (a - b)); [lia | | exact Hin | exact Hin2 | lia |].
    + intros HGa'. pose proof (HG'r _ HGa') as Hr'. destruct (l2_HAimg_xR (b + (a - b)) ltac:(unfold ASRC; lia)) as (Hi & _).
      exact (blk_img0 ly1 S1 W1 memT mdc b n (b + (a - b)) HAR1 Hin ltac:(lia) Hi).
    + intros (rr & Hrr & Hrr2). cbn [FP1 In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Hrr2.
      * assert (Hne : (hl_v H1, AREC * hl_cap H1) <> (b, n)) by (intros E; injection E as E _; exact (Hb1 (eq_sym E))).
        pose proof (sep_blocks0 ly1 S1 W1 memT mdc _ _ _ _ HAR1 HvinH Hin Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
      * assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (b, n)) by (intros E; injection E as E _; exact (Hb2 (eq_sym E))).
        pose proof (sep_blocks0 ly1 S1 W1 memT mdc _ _ _ _ HAR1 HrB Hin Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqR in Hd, Hrr2. lia.
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Bp2 a Ha)). }
(* the image bytes the drop keeps: off its own globals, not the allocator's, not errno; writability from presence *)
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ inG G' a -> abyte_kept W1 memT W2 mem2 a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as HI. split.
  - apply K2; [lia | exact Hn | exact Hi | exact Ho | exact He | apply HFPS].
  - intros Hw. apply (l2_writable_kept_w_xR W1 W2 memT mem2 a); [exact (HAPK a Hi Ho He) | exact Hw]. }
assert (KH : forall a, HA <= a < HA + 80 -> abyte_kept W1 memT W2 mem2 a).
{ intros a Ha. destruct (l2_HAimg_xR a ltac:(unfold ASRC; lia)) as (Hi & Ho & He & _).
  apply KI; [exact Hi | exact Ho | exact He | intros X; pose proof (HG'r a X); lia]. }
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
assert (SRC2 : asrc_at B ly2 S2 W2 mem2 HA (CheckRep.set_held h (ldrop_list H1 m))).
{ rewrite <- (l2_set_held_twice h H1 (ldrop_list H1 m)).
  apply (l2_src_swap ly1 S1 W1 memT ly2 S2 W2 mem2 HA (CheckRep.set_held h H1) (ldrop_list H1 m) HSRC KH).
  - intros rr Hrr a Ha. cbn [CheckRep.set_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr, HPJ, HPART.
    destruct Hrr as [<- | Hrr].
    + destruct (HOTH (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as [Hb1 Hb2].
      apply (KB (hs_partial h) APARTIAL a HPART Hb1 Hb2).
      unfold gfp, bzs in Ha. rewrite length_map in Ha. cbn [fst snd] in Ha. rewrite HPJ in Ha.
      unfold req_size, APARTIAL in *. cbn. lia.
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * refine (l2_list_kept2_xR ly1 S1 W1 W2 memT mem2 (HA + 16) (hs_pending h) false HPEND _ _ rr Hrr a Ha).
        -- intros x Hx. apply KH. lia.
        -- intros b n x Hbn Hx. destruct (HOTH b ltac:(apply in_or_app; left; exact (l2_blks_blocks _ _ _ Hbn))) as [Hb1 Hb2].
           exact (KB b n x (l2_alist_blks_in_xR _ _ _ _ _ _ _ HPEND _ Hbn) Hb1 Hb2 Hx).
      * refine (l2_list_kept2_xR ly1 S1 W1 W2 memT mem2 (HA + 64) (hs_expected h) true HEXP _ _ rr Hrr a Ha).
        -- intros x Hx. apply KH. lia.
        -- intros b n x Hbn Hx.
           destruct (HOTH b ltac:(apply in_or_app; right; apply in_or_app; right; exact (l2_blks_blocks _ _ _ Hbn))) as [Hb1 Hb2].
           exact (KB b n x (l2_alist_blks_in_xR _ _ _ _ _ _ _ HEXP _ Hbn) Hb1 Hb2 Hx).
  - intros [b n] Hbb. cbn [CheckRep.set_held hs_partial hs_pending hs_expected] in Hbb, HPART. destruct Hbb as [Hbb | Hbb].
    + injection Hbb as <- <-. apply KIN; [exact HPART|].
      exact (proj2 (HOTH (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity))).
    + apply in_app_or in Hbb as [Hbb | Hbb].
      * apply KIN; [exact (l2_alist_blks_in_xR _ _ _ _ _ _ _ HPEND _ Hbb)|].
        exact (proj2 (HOTH b ltac:(apply in_or_app; left; exact (l2_blks_blocks _ _ _ Hbb)))).
      * apply KIN; [exact (l2_alist_blks_in_xR _ _ _ _ _ _ _ HEXP _ Hbb)|].
        exact (proj2 (HOTH b ltac:(apply in_or_app; right; apply in_or_app; right; exact (l2_blks_blocks _ _ _ Hbb)))).
  - exact HAL2.
  - exact (l2_nodup_hs_drop (CheckRep.set_held h H1) m ltac:(cbn [CheckRep.set_held hs_held]; lia)
      ltac:(cbn [CheckRep.set_held hs_held]; lia) HNDB). }
assert (MEM2 : l2_mem_xR m ly2 S2 (kk + 1) (ldrop_list H1 m) W2 mem2 md2).
{ split; [exact HJ3|]. split; [exact SRC2|].
  split; [unfold ldrop_list; cbn [HarnessRep.hl_v]; exact HV|].
  split; [unfold ldrop_list; cbn [HarnessRep.hl_cap]; exact HC|].
  split; [rewrite (l2_ldrop_recs H1 _ _ m Hle HREC); f_equal; symmetry; apply l2_kp_hit; [lia | exact HPT]|].
  split.
  { intros rest Hp. rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT) in Hp. cbn [map] in Hp.
    assert (Hp' : Permutation (ablocks B ly S)
      (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (filter (fun r => CheckRep.prefixb P (snd r))
        (skipn (Datatypes.S m) (hl_recs (hs_held h)))) ++ (fst r, Z.of_nat (length (snd r)) + 1) :: rest))
      by (eapply Permutation_trans; [exact Hp | apply Permutation_middle]).
    pose proof (HPERM _ Hp') as Hp1. rewrite Eb1 in Hp1. rewrite Eb2.
    apply (Permutation_cons_inv (a := (fst r, Z.of_nat (length (snd r)) + 1))).
    eapply Permutation_trans; [apply Permutation_middle | exact Hp1]. }
  split; [rewrite Hfrs12; exact HFRS|].
  split.
  { rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT). cbn [length]. rewrite Nat2Z.inj_succ.
    match goal with |- mo_le _ _ _ (Z.succ ?x * _) =>
      replace (Z.succ x * mo_free MT) with (x * mo_free MT + mo_free MT) by ring end.
    exact (mo_le_trans MT ML _ _ _ _ _ HMLE Hmle). }
  split.
  { apply (mo_ok_step MT ML S1 S2 (mo_free MT) (Z.of_nat m * mo_free MT)); [|exact Hmle].
    replace (mo_free MT + Z.of_nat m * mo_free MT) with (Z.of_nat (Datatypes.S m) * mo_free MT) by (rewrite Nat2Z.inj_succ; ring).
    exact HMOK. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as (Hne & Hpin).
    assert (Hd : forall rr, {in_zr a rr} + {~ in_zr a rr}).
    { intros rr. unfold in_zr. destruct (Z_le_gt_dec (fst rr) a); destruct (Z_lt_ge_dec a (fst rr + snd rr));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Hno].
    - exact (rom_pinned_view0 ly2 S2 W2 mem2 md2 a HAR2 (Hpin Hown)).
    - assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
      rewrite (proj1 (KI a Hi Hno Hne (proj2 (proj2 (HROMS' a Hr))))). exact (HROM a Hr). }
  split.
  { apply (l2_saved_kept W1 W2 memT mem2 sp0 regs0); [|exact HSAV]. intros a Ha.
    apply K1; [lia | intros X; pose proof (HG'r a X); lia | lia | rewrite WL; lia]. }
  split.
  { apply (l2_vm_keep W1 W2 memT mem2); [|exact MAT]. intros x Hx. cbn in Hx.
    apply K1; [lia | intros X; pose proof (HG'r x X); lia | lia | rewrite WL; lia]. }
  split.
  { apply (l2_vm_keep W1 W2 memT mem2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
    assert (Ex : x = VAL A_g_gone) by lia. subst x. destruct l2_gone_img_xR as (Hi & Ho & He).
    apply (proj1 (KI _ Hi Ho He ltac:(intros X; pose proof (HG'r _ X) as Hx';
      destruct (l2_HAimg_xR (VAL A_g_gone) ltac:(unfold ASRC; lia)) as (_ & _ & _ & _ & Hg); apply Hg; lia))). }
  (* errno: ldrop_post keeps its view (the conjunct after apres_kept) *)
  split; [intros i Hi; rewrite (HERR i Hi); exact (MER i Hi)|].
  (* the room round: list_drop's post room is the rest's budget; the counts fell by record m's block *)
  split; [exact HRMd|].
  rewrite Eb2. rewrite Eb1 in HCNk. refine (cnt_ok_pk_mono RP _ _ _ _ _ HCNk).
  intros P0. pose proof (ReplyCnt.acnt_del_le P0 b1 b2 (fst r, Z.of_nat (length (snd r)) + 1)). lia. }
assert (REGS2 : l2_regs regs0 HA PF regs2 m).
{ assert (P2 : getr regs2 2 = getr regsT 2) by (apply (HP2 2); unfold acallee_saved; lia).
  assert (P3 : getr regs2 3 = getr regsT 3) by (apply (HP2 3); unfold acallee_saved; lia).
  assert (P4 : getr regs2 4 = getr regsT 4) by (apply (HP2 4); unfold acallee_saved; lia).
  assert (P27 : getr regs2 27 = getr regsT 27) by (apply (HP2 27); unfold acallee_saved; lia).
  assert (P8 : getr regs2 8 = getr regsT 8) by (apply (HP2 8); unfold acallee_saved; lia).
  assert (P9 : getr regs2 9 = getr regsT 9) by (apply (HP2 9); unfold acallee_saved; lia).
  assert (P18 : getr regs2 18 = getr regsT 18) by (apply (HP2 18); unfold acallee_saved; lia).
  assert (P19 : getr regs2 19 = getr regsT 19) by (apply (HP2 19); unfold acallee_saved; lia).
  assert (P21 : getr regs2 21 = getr regsT 21) by (apply (HP2 21); unfold acallee_saved; lia).
  unfold l2_regs. rewrite P2, P3, P4, P27, P8, P9, P18, P19, P21. exact HR. }
rewrite T1. apply Kont. split; [lia|]. exists ly2, S2, (kk + 1), (ldrop_list H1 m). split; [exact MEM2 | exact REGS2].
Qed.

(* ---- 0x858c4 .. 0x85918 at R: the record's traps, has_prefix (HP, strict, lifted by SRr_SRrG), beqz a0: no match ->
   0x85928, a match -> list_drop (l2_drop_xR) ---- *)
Lemma l2_ent_xR : forall m W1 regs1 mem1 md1, l2_mid_xR m W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_inv_xR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_l2t)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_l2e)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR & R10 & R11) Kont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts_xR as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity. rewrite WS in HSTKc.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof HM as (HJ & HSRC & HV & HC & HREC & _ & _ & _ & _ & HROM & _).
pose proof HR as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21).
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (al0_blocks ly1 S1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (unfold AREC in Vceil; lia).
(* the record v[m] *)
set (r := nth m (hl_recs (hs_held h)) (0, [])).
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
rewrite Forall_forall in HFallH. destruct (HFallH r HRIN) as (HrB & HrG & HrL & _).
destruct (HrL eq_refl) as (HrNZ & HrLEN). unfold APARTIAL in HrLEN.
destruct (al0_blocks ly1 S1 W1 mem1 md1 _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
rewrite HreqR in Hrceil, Hrapp.
destruct (l2_rec_fields B ly1 S1 W1 mem1 (HA + 80) H1 true m HAH ltac:(lia)) as (Ms0 & Ml0).
rewrite ENTH, HV in Ms0, Ml0. rewrite Z.mod_small in Ms0, Ml0 by lia.
set (RA := hl_v (hs_held h) + AREC * Z.of_nat m) in *.
assert (HRA : 4096 <= RA /\ hl_v H1 <= RA /\ RA + 16 <= hl_v H1 + AREC * hl_cap H1 /\ RA mod 16 = 0).
{ unfold RA, AREC. rewrite <- HV. unfold hl_n in *. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Zplus_mod, V16. replace (16 * Z.of_nat m) with (Z.of_nat m * 16) by lia. rewrite Z_mod_mult. reflexivity. }
assert (HRapp : in_app RA 16) by (apply (in_app_sub (hl_v H1) (AREC * hl_cap H1)); [exact Vapp | lia | lia | lia]).
pose proof (range_addressable_of_block0 ly1 S1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR1 HvinH
  ltac:(lia) ltac:(rewrite HreqV; lia)) as HRAR.
assert (Ms1 : val_mem SEGS (arm W1 mem1) RA 8 (fst r)) by (unfold RA, AREC; exact Ms0).
assert (Ml1 : val_mem SEGS (arm W1 mem1) (RA + 8) 8 (Z.of_nat (length (snd r)))) by (unfold RA, AREC; exact Ml0).
destruct (l2e_state W1 regs1 mem1 (sp0 - 112) RA (hl_v (hs_held h)) (Z.of_nat m) (fst r) (Z.of_nat (length (snd r)))
  R2 R10 R11 R19 R21 HSPb HSPa ltac:(lia) ltac:(lia) ltac:(rewrite <- HV; lia) ltac:(rewrite <- HV; exact V16)
  ltac:(unfold hl_n in Hn26; lia) HRapp ltac:(lia) ltac:(lia) Ms1 Ml1 HRAR) as [HS SHOK].
pose proof alloc_ceiling_val as ACV.
remember (Eimg (Ereg regs1 (l2_xe (fst r) (Z.of_nat (length (snd r)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j0, (j0 < 2)%nat -> ew E (32 + j0) = nth j0 (l2_xe (fst r) (Z.of_nat (length (snd r)))) (Z_to_bv 64 0)).
{ intros j0 Hj0. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 (fst r)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 1%nat ltac:(lia)).
clear EX.
assert (E10 : ew E 10 = Z_to_bv 64 (hl_v (hs_held h) + AREC * Z.of_nat m)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (hl_v (hs_held h))) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EEo 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = RA) by (rewrite E10; apply unsigned_lit_small; lia).
pose proof HS as HS0.
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOx HS HJ SHOK l2_Bspan AF_fr_has_prefix.
{ apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_rec] in Ha; lia | apply awr_ok_x_nil]. }
psrr_branch_tok RUNTOx BRR HS SHOK l2_Bspan.
{ (* bltu a0,a1 taken: &v[m] = v + 16 m does not wrap *)
  exfalso. rewrite (trap_ptr_wrap_atom E 10 11 (hl_v (hs_held h)) (AREC * Z.of_nat m) E10 E11) in Hc
    by (unfold AREC, hl_n in *; lia). discriminate Hc. }
clear Hc.
paj_run_to_tok_xR RUNTOx HS HJ SHOK l2_Bspan AF_fr_has_prefix.
{ cbn [ss_mem add_cond].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_rec] in Ha; lia | apply awr_ok_x_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_back).
assert (PRESr : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; l2_pres_back Hp).
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 _ _ kk HJ)
  as (memS & HJi & HgS).
assert (HAR3 : AR0 ly1 S1 W1 (ms_mem ms0) mdc) by exact (proj1 HJi).
assert (Usp1 : spZ (ms_regs ms0) = sp0 - 112) by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite Q2; exact Usp).
pose proof l2_PF_low_xR as HPlow.
assert (HPREh : AFP0 HP_STK ly1 S1 W1 (ms_regs ms0) (ms_mem ms0) mdc []).
{ eapply (afn_pre_at0R (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms0) mdc kk
    (ms_regs ms0) HP_STK (- 112 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - rewrite WS. unfold HP_STK, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, (EEo 8%nat 8%bv eq_refl), R8. rewrite unsigned_lit_small by lia. lia. }
(* the prefix's bytes are read-only, so they are the entry's *)
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi). rewrite KEEPr by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
assert (RV0 : rom_view SEGS W1 (ms_mem ms0)) by (intros a Hr; rewrite ROMK by exact Hr; exact (HROM0 a Hr)).
destruct (l2_pfx_keep_xR ly1 S1 W1 (ms_mem ms0) mdc kk HJ RV0) as (PK & HRAP & HHVP0).
assert (HHVP : 0 < PLEN + 1 -> shadow_hull_vis (aview SEGS (w_H W1) (ms_mem ms0)) PF (PLEN + 1)) by (intros _; exact HHVP0).
assert (TXT : l2_bytes W1 (ms_mem ms0) (fst r) (snd r ++ [Z_to_bv 8 0])).
{ apply l2_bytes_of_garr8. apply (l2_g8_keep W1 W1 mem1 (ms_mem ms0)); [|exact HrG].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. apply KEEPr. lia. }
assert (PTXT : l2_bytes W1 (ms_mem ms0) PF (P ++ [Z_to_bv 8 0])).
{ intros t Ht. rewrite length_app in Ht. cbn [length] in Ht. rewrite PK by lia.
  destruct (Z_lt_ge_dec t PLEN) as [Hlt | Hge].
  - rewrite app_nth1 by lia. exact (HPB t ltac:(lia)).
  - assert (Ht' : t = PLEN) by lia. rewrite Ht'. rewrite app_nth2 by lia.
    replace (Z.to_nat PLEN - length P)%nat with 0%nat by lia. cbn [nth]. rewrite HPN. reflexivity. }
eapply (SRrG_bind SEGS R R_trans).
{ apply (SRr_SRrG SEGS R WLE_R).
  apply (HP W1 ly1 S1 [] (ms_regs ms0) (ms_mem ms0) mdc [] (fst r) (Z.of_nat (length (snd r))) PF PLEN HPREh).
  - rewrite Q10, E32. reflexivity.
  - rewrite Q11, E33. reflexivity.
  - rewrite Q12, (EEo 8%nat 8%bv eq_refl), R8. reflexivity.
  - lia.
  - lia.
  - exact HPl.
  - exact HPF0.
  - lia.
  - lia.
  - lia.
  - split; [lia|]. split.
    + intros k Hk. exists (bv_unsigned (nth (Z.to_nat k) P (Z_to_bv 8 0))). split.
      * rewrite PK by lia. exact (HPB k Hk).
      * intros H0z. apply HPz. assert (Hn0 : nth (Z.to_nat k) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite H0z; reflexivity).
        rewrite <- Hn0. apply nth_In. lia.
    + intros _. rewrite PK by lia. exact HPN.
  - intros a Ha. rewrite PK by lia. exact (proj1 (HPV a ltac:(lia))).
  - unfold hp_off. rewrite Usp1. intros a Ha. destruct (HPV a ltac:(lia)) as [_ Hn]. unfold HP_STK, ESTACK. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact (HHVP ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). rewrite PK by lia.
    exact (proj1 (HPV a ltac:(lia))).
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle2. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (fst r + (a - fst r)) by lia.
      rewrite (TXT (a - fst r) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + unfold hp_off. rewrite Usp1. intros a Ha. unfold HP_STK, ESTACK in *. lia.
    + apply l2_amem_of_app. apply (in_app_sub (fst r) (Z.of_nat (length (snd r)) + 1)); [exact Hrapp | lia | lia | lia].
    + eapply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms0) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms0) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (l2_shv_sub _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) (HHVP ltac:(lia))). }
cbv beta. intros W2 c2 Rw2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HFRc & HRES).
rewrite Usp1 in HJc, HFRc.
assert (HB : exists b, (b = 0 \/ b = 1) /\ getr regs2 10 = w64 b /\ (b = 1 <-> CheckRep.prefixb P (snd r) = true)).
{ destruct HRES as [(Hle2 & Hpre & Hr10) | (Hnp & Hr10)].
  - exists 1. split; [right; reflexivity|]. split; [exact Hr10|]. split; [intros _|intros _; reflexivity].
    apply (proj1 (l2_prefixb_iff W1 (ms_mem ms0) (fst r) PF (snd r) P TXT PTXT)). split; assumption.
  - exists 0. split; [left; reflexivity|]. split; [exact Hr10|]. split; [intros Hc; discriminate Hc|].
    intros Hp. exfalso. destruct (proj2 (l2_prefixb_iff W1 (ms_mem ms0) (fst r) PF (snd r) P TXT PTXT) Hp) as (Hl3 & Hpr).
    exact (Hnp Hl3 Hpr). }
destruct HB as (b & Hb01 & Hb10 & HbP).
(* has_prefix's strict inner journal is one at R (WLE_R), then a gx journal at [] lifted to G *)
assert (HJc' : AJ0R G 0 [] HP_STK (sp0 - 112) [] ly1 S1 W1 (ms_mem ms0) mdc [] ly1 S1 W2 mem2 md2 0).
{ apply (ajournal_gx_G_mono_xR SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|].
  apply ajournal_gx_nil_xR. eapply ajournal_xR_mono; [exact WLE_R|].
  exact HJc. }
pose proof (ajournal_gx_sub0R Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W1 (ms_mem ms0) mdc kk HP_STK (sp0 - 112) 0 [] [] [] ly1 S1 W2 mem2 md2 0 HJ HJc'
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U10.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRc; [lia|]. unfold HP_STK, ESTACK. lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (F40 : ew Ea 40 = w64 b) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hb10).
clear HEa.
assert (F10 : ew Ea 10 = Z_to_bv 64 RA) by (rewrite OLDa by lia; exact E10).
assert (F21 : ew Ea 21 = Z_to_bv 64 SB) by (rewrite OLDa by lia; rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (HAR2 : AR0 ly1 S1 W2 mem2 md2)
  by exact (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 mem2 md2 kk HJ2).
assert (SHOK2 : sh_ok SEGS l2_Bx l2_SHe Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, l2_SHe. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (range_addressable_of_block0 ly1 S1 W2 mem2 md2 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR2 HvinH
      ltac:(lia) ltac:(rewrite HreqV; lia)).
  - unfold l2_Bx. rewrite (U_atom Ea 21 SB F21) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 10 RA F10) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. destruct HRapp as [_ [HH | [HH _]]];
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) by (intros a Ha Hs; rewrite HFRc by assumption; apply KEEPr; exact Ha).
assert (PRES2 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) by (intros a Hp; exact (HPR2 a (PRESr a Hp))).
rewrite Q1.
paj_run_tok_xR RUNx HS HJ2 SHOK2 l2_Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
psrr_branch_tok RUNx BRR HS SHOK2 l2_Bspan.
- (* beqz taken: no match, on to 0x85928 *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb0 : b = 0) by (apply Z.eqb_eq in Hc; exact Hc).
  assert (HPF : CheckRep.prefixb P (snd r) = false)
    by (destruct (CheckRep.prefixb P (snd r)) eqn:Eq; [exfalso; pose proof (proj2 HbP eq_refl); lia | reflexivity]).
  paj_run_to_tok_xR RUNTOx HS HJ2 SHOK2 l2_Bspan A_l2t.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_mem_xR (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms2) mdb).
  { apply (l2_mem_keep_xR (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms2) md1 mdb (sp0 - 112 - HP_STK) (sp0 - 112) HM HJ2);
    [unfold HP_STK, ESTACK; lia | lia | | | exact Rw2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  pose proof (l2_mem_miss_xR m ly1 S1 kk H1 W2 (ms_mem ms2) mdb Hle HPF MEM1) as MEM0.
  assert (REGS1 : l2_regs regs0 HA PF (ms_regs ms2) m).
  { unfold l2_regs.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [l2_keepreg2 HS0 HS (19%bv : bv 5) OLDa; exact R19|].
    l2_keepreg2 HS0 HS (21%bv : bv 5) OLDa; exact R21. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_l2t) by (unfold A_l2t, AF_fr_check_shape_ends; lia) end.
  apply Kont. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEM0 | exact REGS1].
- (* beqz not taken: a match, list_drop(&held, m) *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb1 : b = 1) by (destruct Hb01 as [-> | ->]; [discriminate Hc | reflexivity]).
  assert (HPT : CheckRep.prefixb P (snd r) = true) by (apply HbP; exact Hb1).
  paj_run_to_tok_xR RUNTOx HS HJ2 SHOK2 l2_Bspan AF_fr_list_drop.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_mem_xR (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms2) mdb).
  { apply (l2_mem_keep_xR (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms2) md1 mdb (sp0 - 112 - HP_STK) (sp0 - 112) HM HJ2);
    [unfold HP_STK, ESTACK; lia | lia | | | exact Rw2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  assert (REGS1 : l2_regs regs0 HA PF (ms_regs ms2) m).
  { unfold l2_regs.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [l2_keepreg2 HS0 HS (19%bv : bv 5) OLDa; exact R19|].
    l2_keepreg2 HS0 HS (21%bv : bv 5) OLDa; exact R21. }
  prreg HS (1%bv : bv 5) T1. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
  repeat (rewrite OLDa in T10 by lia). repeat (rewrite OLDa in T11 by lia).
  rewrite (EEo 9%nat 9%bv eq_refl), R9 in T10. rewrite (EEo 19%nat 19%bv eq_refl), R19 in T11.
  assert (T1' : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + A_l2t))
    by (rewrite T1; f_equal; unfold A_l2t, AF_fr_check_shape_ends; lia).
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + AF_fr_list_drop) by (unfold AF_fr_list_drop; lia) end.
  exact (l2_drop_xR m ly1 S1 kk H1 W2 (ms_regs ms2) (ms_mem ms2) mdb Hle HPT MEM1 REGS1 T10 T11 T1' Kont).
Qed.

(* ---- the loop at R: by induction on the records left ---- *)
Lemma l2_loop_xR : forall m W1 regs1 mem1 md1, gone <> 0 -> l2_inv_xR (Datatypes.S m) W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction m as [|m IH]; intros W1 regs1 mem1 md1 Hg Hinv;
  (apply (l2_head_xR _ W1 regs1 mem1 md1 Hinv); intros W2 regs2 mem2 md2 Hmid;
   apply (l2_ent_xR _ W2 regs2 mem2 md2 Hmid); intros W3 regs3 mem3 md3 Hinv3;
   apply (l2_tail_xR _ W3 regs3 mem3 md3 Hinv3 Hg); intros W4 regs4 mem4 md4 Hm Hinv4).
- lia.
- exact (IH W4 regs4 mem4 md4 Hg Hinv4).
Qed.
(* loop 2's first entry at R (W_cshe_epi.v cshe_l2_in_xR) is the invariant at n = hl_n (hs_held h) records; the entry's
   world step is R, so the source is kept by l2_src_step_xR *)
Lemma l2_run_xR : val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> mo_ok MT S (cshe_cost MT (hs_held h)) ->
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) -> cnt_ok_pk RP cshe_pk (ablocks B ly S) ->
forall W1 c1, cshe_l2_in_xR B PST ARx G R regs0 ly S W mem md XO AT HA PF gone h W1 c1 -> SRrG SEGS R W1 c1 Post.
Proof.
intros HAT0 HGN HMO HRM0 HCN0 W1 c1 (regs1 & mem1 & md1 & -> & HJ1 & Q2 & Q3 & Q4 & Q27 & Q8 & Q9 & Q18 & Q19 & Q21 & HSAV1 & HKEEP1 & HPRES1 &
  Hgone & Hn0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct l2_sp_facts_xR as (HSPb & HSPa & HSTKc & HX47 & HXO).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
assert (Hlen : exists n', length (hl_recs (hs_held h)) = Datatypes.S n').
{ destruct (length (hl_recs (hs_held h))) as [|n] eqn:E; [unfold hl_n in Hn0; rewrite E in Hn0; lia | exists n; reflexivity]. }
destruct Hlen as (n' & En).
pose proof HJ1 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & Rw01 & _).
apply (l2_loop_xR n' W1 regs1 mem1 md1 Hgone).
split; [rewrite En; lia|].
exists ly, S, 0, (hs_held h). split.
- split; [exact HJ1|].
  split.
  { apply l2_set_held_id.
    apply (l2_src_step_xR ly S md W W1 mem mem1 HA h (sp0 - CSHE_STK_B) sp0 HAR0 HSRC0); [| lia | | exact HPRES1 | exact Rw01].
    - intros a Ha. exact (proj1 (l2_HAimg_xR a Ha)).
    - intros a Ha Hno. exact (HKEEP1 a Ha Hno). }
  split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite <- En, firstn_all, skipn_all, list_basics.list.filter_nil, app_nil_r; reflexivity|].
  split; [rewrite <- En, skipn_all, list_basics.list.filter_nil; cbn [map app]; intros rest Hp; exact Hp|].
  split; [reflexivity|].
  split; [rewrite <- En, skipn_all, list_basics.list.filter_nil; cbn [length Z.of_nat]; rewrite Z.mul_0_l;
          exact (mle_start MT S ML)|].
  split; [unfold cshe_cost, hl_n in HMO; rewrite En in HMO; exact HMO|].
  split.
  { intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
    pose proof (pa_img_range a Hi) as HI. rewrite HKEEP1 by (rewrite ?WS; lia). exact (HROM0 a Hr). }
  split; [exact HSAV1|].
  split; [apply (l2_vm_keep W W1 mem mem1); [intros x Hx; cbn in Hx; apply HKEEP1; lia | exact HAT0]|].
  split.
  { apply (l2_vm_keep W W1 mem mem1); [|exact HGN]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
    pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR. apply HKEEP1; rewrite ?WS; lia. }
  (* errno: an image cell, outside [sp0 - CSHE_STK_B, sp0), so cshe_l2_in_xR's kept-view clause gives it *)
  split; [intros i Hi; destruct l2_errno_low as [E0 E1]; apply HKEEP1; rewrite ?WS; lia|].
  (* the room round: cshe_cost MT_rk is one free per record, the loop's budget at n records; the counts are the
     entry's (cshe_pk = 0) *)
  split; [|exact HCN0]. unfold cshe_cost, hl_n in HRM0. rewrite En in HRM0. exact HRM0.
- unfold l2_regs. unfold hl_n in Q19. rewrite En in Q19.
  split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q27|]. split; [exact Q8|].
  split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19 | exact Q21].
Qed.
End loopR.

(* ------------------------------------------------------------------ the segment lemma at R *)
(* cshe_l2_B at a world relation R: cshe_l2_B's premises verbatim; the entry cshe_l2_in_xR, the step relation
   SRrG SEGS R and the exit cshe_out_B_xR (W_cshe_epi.v Section wR).  list_drop's contract is LDROP_R, not LDROP. *)
Lemma cshe_l2_B_xR : forall W ly S regs mem md ch XO AT HA (j : nat) PF h P A0 gone (O OUT : Z) (ob : list byte),
AFP0 CSHE_STK_B ly S W regs mem md ch ->
XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j -> (j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK_B <= a < spZ regs + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
((forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (Z.of_nat (length P) + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\
   forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
mo_ok MT S (cshe_cost MT (hs_held h)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) -> cnt_ok_pk RP cshe_pk (ablocks B ly S) ->
forall W1 c1, cshe_l2_in_xR B PST ARx G R regs ly S W mem md XO AT HA PF gone h W1 c1 ->
SRrG SEGS R W1 c1 (cshe_out_B_xR B PST ARx G R MT RP regs ly S W mem md XO AT HA A0 gone h P ob kr).
Proof.
intros W ly S regs mem md ch XO AT HA j PF h P A0 gone O OUT ob HPRE HX16 HXtop HSRC HA8 HAlo HAhi HGa Hzs HAj Hj4
  HND0 Hn26 HATl HATh HAT0 HPz HPl HPF0 HPFh HPB HPN HPV HPM1 HPM8 HPRA0 HPLOC HROM0 HGN HMO kr HRM0 HCN0 W1 c1 HIN.
eapply l2_run_xR; eassumption.
Qed.
(* the closure, printed into the build log: Section variables (R and its laws, LDROP_R; B, MT, G and Section c's
   hypotheses but LDROP; the contexts) and the axioms *)
Print Assumptions cshe_l2_B_xR.
End wR.
End c.
End b.
End a.
