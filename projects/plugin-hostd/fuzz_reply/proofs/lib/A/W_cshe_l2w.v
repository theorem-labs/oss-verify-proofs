(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: loop 2 of the ASan walk of fuzz_reply's check_shape_ends (0x853b0), the
   `g_gone <> 0` loop from its head 0x854c4 to the epilogue 0x85690, over W_check_shape_ends.v's interface
   (cshe_post_x, cshe_epi_x, the Section hypotheses).  A segment lemma for W3's pb_check_shape_ends_x.
   THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record), on the check_bounded template
   a working branch, lib/A/W_check_bounded.v): cshe_l2_run_x is stated over any allocator relation ARx with its
   laws, as W_contract_x.cshe_post_x's g_gone <> 0 disjunct.  The Section hypotheses are W_check_shape_ends.v's generic
   ones (same names, same order): PST / ARx / hl / LAWS, HP0 (no hidden head in any ARx state: the heap-block shadow
   facts are W_journal_x's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x, and every ghost list the
   walk meets is []), IMGC / BLKN (W_kit_x.v blk_off_imgP_x), FRMF (W_frame_x.v's fake-frame alignment, for
   cshe_P_at_x); the calls are the kit's: free through AFREE (W_journal_x.v afree_cf_rule_c_x, the caller-context form
   at CTX_AFREE, with this loop's site fact HCTX_cshe_l2: its free returns to 0x8551c), __asan_memmove through AMOVE
   (W_sites_x.v amemmove_realizes_x, entered by aj_gx_entry_at_x), has_prefix through W_has_prefix.pb_has_prefix_x;
   P's facts are W_check_shape_ends.v's cshe_P_at_x, the epilogue its cshe_epi_x.  The AR statement is re-derived at
   ARi0 in W_cshe_top.v. *)
(* One turn at index i = m - 1 (m the records not yet examined, counting down from n):
     0x854c4  the shadow check of l->v, s3 = l->v + 16 i                       (l2_A, state ss_l2a)
     0x854d4  the two shadow checks of v[i], has_prefix(v[i].s, v[i].n, PF)  (l2_B, state ss_l2b)
     0x85508  beqz a0: no match -> 0x85558;
     0x8550c  match: the shadow check of v[i], free(v[i].s), the shadow checks of l->v and l->n (a partial
              granule check that is not taken: l->n's shadow is zero), __asan_memmove(&v[i], &v[i + 1],
              16 (n - i - 1)), l->n = n - 1                                       (l2_C, state ss_l2c)
     0x85558  s4--, s5++, s7 -= 16;  bltu s6, s4 -> 0x854c4 else j 0x85690.
   The invariant (l2_inv m) says: the held list is the first m records of the entry's list followed by the
   records past them that do not have the prefix, the dropped ones are those that do, with the journal, the
   source, the meter, the blocks and the frame of the entry.  At m = 0 the epilogue cshe_epi_x gives cshe_post_x's
   gone <> 0 disjunct. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YO0c YN2e YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_check_shape_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_has_prefix.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the model's side (CheckRep) *)
Lemma l2_filter_cons : forall (f : Z * list byte -> bool) r l,
filter (fun x => f x) (r :: l) = if f r then r :: filter (fun x => f x) l else filter (fun x => f x) l.
Proof.
intros f r l. rewrite list_basics.list.filter_cons.
destruct (f r) eqn:E; match goal with |- context [decide ?X] => destruct (decide X) as [D|D] end;
  cbn in D |- *; first [reflexivity | (exfalso; apply D; rewrite E; exact I) | (rewrite E in D; contradiction)
  | contradiction].
Qed.
Lemma l2_filter_app : forall (f : Z * list byte -> bool) a b,
filter (fun x => f x) (a ++ b) = filter (fun x => f x) a ++ filter (fun x => f x) b.
Proof. intros f a b. apply list_basics.list.filter_app. Qed.
Lemma l2_filter_len : forall (f : Z * list byte -> bool) l, (length (filter (fun x => f x) l) <= length l)%nat.
Proof.
intros f l. induction l as [|r l IH]; [cbn; lia|]. rewrite l2_filter_cons. destruct (f r); cbn [length]; lia.
Qed.
Lemma l2_in_filter : forall (f : Z * list byte -> bool) l x, In x (filter (fun y => f y) l) -> In x l.
Proof.
intros f l x. induction l as [|r l IH]; [cbn; tauto|]. rewrite l2_filter_cons. intros Hx.
destruct (f r); [destruct Hx as [<- | Hx]; [left; reflexivity | right; exact (IH Hx)] | right; exact (IH Hx)].
Qed.
Lemma l2_nodup_filter : forall (Y : Type) (g : Z * list byte -> Y) (f : Z * list byte -> bool) l,
List.NoDup (map g l) -> List.NoDup (map g (filter (fun r => f r) l)).
Proof.
intros Y g f l. induction l as [|r l IH]; [intros _; rewrite list_basics.list.filter_nil; constructor|].
intros ND. rewrite l2_filter_cons. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
destruct (f r); [|exact (IH ND)].
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
Lemma l2_set_held2 : forall h0 a b, CheckRep.set_held (CheckRep.set_held h0 a) b = CheckRep.set_held h0 b.
Proof. intros [] a b. reflexivity. Qed.
(* the kept and the dropped records, one record further down the list *)
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
(* the held list after the inlined list_drop of record m *)
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

(* ------------------------------------------------------------------ the walk's Section, as W_check_shape_ends.v's *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* the two inner states of a turn: 0x854d4 (s3 = &v[i]) and 0x8550c (after has_prefix matched) *)
Definition A_cshe_l2b : Z := AF_fr_check_shape_ends + 0x124.
Definition A_cshe_l2h : Z := AF_fr_check_shape_ends + 0x15c.

(* The vector's records as 8-byte cells (check_no_loss's cnl_rec_fields, W_check_no_loss.v:148-194). *)
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
Lemma l2_text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
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
(* writability across a step that keeps presence (W1's W_list_drop.v writable_kept_w) *)
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
Lemma l2_aview_of_val_mem2 : forall H H' (m m' : word -> option byte) a n v k,
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H' m' (a + k) = aview SEGS H m (a + k).
Proof.
intros H H' m m' a n v k H1 H2 Hk. unfold aview.
rewrite (val_mem_agree SEGS _ _ a n v H1 H2 k Hk). reflexivity.
Qed.
Lemma l2_vm_keep : forall (W W' : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v.
Proof.
intros W W' m m' a n v Hk Hv i Hi. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat i) (Hk (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.
Lemma l2_val_mem_of_chunk4 : forall E (m : word -> option byte) base off e v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 4%N e)) -> U E e = v -> 0 <= v < 2 ^ 32 ->
val_mem SEGS m (base + off) 4 v.
Proof.
intros E m base off e v Hc Hv Hr k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb. injection Hb as <-. cbn [YP09.c_off] in Hm.
rewrite Hm. f_equal. unfold byte_of_word, YO0f.le_byte.
change (bv_unsigned (sv_denot E e)) with (U E e). rewrite Hv.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma l2_shv_sub : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma l2_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma l2_mod64_32 : forall a, a mod 2 ^ 64 mod 2 ^ 32 = a mod 2 ^ 32.
Proof.
intros a. replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. rewrite Z.rem_mul_r by lia.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
(* the memmove's byte count at 0x85548: (n + s5) << 4 with s5 = -k, as the walk's addw / slli leave it *)
Lemma l2_count_eq : forall k n, 0 <= k <= n -> n < 2 ^ 30 ->
alu64 ALU_SLL (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 (- k))) (low32 (Z_to_bv 64 n)))) (Z_to_bv 64 4) =
Z_to_bv 64 (16 * (n - k)).
Proof.
intros k n Hk Hn.
assert (RA : bv_unsigned (alu32 ALU_ADD (low32 (Z_to_bv 64 (- k))) (low32 (Z_to_bv 64 n))) = n - k).
{ rewrite YO0c.alu32_add_unsigned, !YO0c.low32_unsigned, !Z_to_bv_unsigned. unfold lo32, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite !l2_mod64_32. rewrite <- Zplus_mod.
  replace (- k + n) with (n - k) by lia. apply Z.mod_small. lia. }
apply bv_eq. rewrite YO0c.alu64_sll, YO0c.sext64_alu32, RA.
rewrite sx32_small by lia. rewrite (unsigned_lit_small 4) by lia.
replace (4 mod 64) with 4 by reflexivity.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite Z.mod_small by lia. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma l2_nodup_disj : forall (l1 l2 : list Z) x y, List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
induction l1 as [|z l1 IH]; intros l2 x y ND H1 H2; [destruct H1|]. cbn [app] in ND.
apply List.NoDup_cons_iff in ND as [Hn ND]. destruct H1 as [<- | H1].
- intros <-. apply Hn. apply in_or_app. right. exact H2.
- exact (IH l2 x y ND H1 H2).
Qed.
Lemma l2_soff : forall E n x c, ew E n = Z_to_bv 64 x -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n x c H. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
rewrite U_SOff, H. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma l2_U_sh : forall E m c x, ew E m = Z_to_bv 64 x -> ew E 25 = Z_to_bv 64 SB -> 0 <= x < 2 ^ 47 -> x + c < 2 ^ 47 -> 0 <= x + c ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 25 0)) = (x + c) / 8 + SB.
Proof.
intros E m c x Hm H25 Hx Hc Hc0.
rewrite !U_SAlu, (U_atom_off E m x c Hm) by lia. rewrite (U_atom E 25 SB H25) by (unfold SB; lia). rewrite U_lit by lia.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
assert (D : 0 <= (x + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. unfold SB. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ the three symbolic states *)
(* s0 (x8) is pinned to s2 + 8 = &l->n, s10 (x26) to the shadow byte of l->v (the token engine's shadow form, Bx1 =
   s9), and at 0x8550c s8 (x24) to the shadow byte of v[i]; the shadow checks of l->v and l->n are covered by the
   entry (18, 0, 16) (azs of HA + 64 .. HA + 96), those of v[i] by (19, 0, 16) (the vector's block). *)
Definition l2_shv : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0).
Definition l2_shn : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0).
Definition l2_shr : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 25 0).
Definition l2_hd0 : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition l2_hdw : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 8 12
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition l2_fr : YP09.region := YP09.mkRegion (Some 2%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 l2_shn)].
Definition l2_rec : YP09.region := YP09.mkRegion (Some 19%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
Definition l2_sr : list sv := sr_set (sr_set sr_atoms 8%bv (SOff 18 8)) 26%bv l2_shv.
Definition l2c_sr : list sv := sr_set l2_sr 24%bv l2_shr.
(* atoms 32 the vector v, 33 the count n, 34 v[i].s, 35 v[i].n *)
Definition l2_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (18%nat, mkAF 4096 0x7fff8000 3); (25%nat, mkAF SB SB 0);
(32%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 1 (2 ^ 26) 0) ] [] [].
Definition l2b_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (18%nat, mkAF 4096 0x7fff8000 3); (25%nat, mkAF SB SB 0);
(32%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 1 (2 ^ 26) 0); (19%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition ss_l2a : sstate := mkSS A_cshe_l2 l2_sr [ l2_hd0 ] None l2_facts.
Definition ss_l2b : sstate := mkSS A_cshe_l2b l2_sr [ l2_hd0; l2_rec ] None l2b_facts.
Definition ss_l2c : sstate := mkSS A_cshe_l2h l2c_sr [ l2_fr; l2_hdw; l2_rec ] None l2b_facts.
(* 0x85558, where both paths of a turn meet before the counters: no region, the registers as atoms *)
Definition A_cshe_l2t : Z := AF_fr_check_shape_ends + 0x1a8.
Definition l2t_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (18%nat, mkAF 4096 0x7fff8000 3); (25%nat, mkAF SB SB 0) ] [] [].
Definition ss_l2t : sstate := mkSS A_cshe_l2t sr_atoms [] None l2t_facts.
Definition l2_SHa : list shent := [ mkSHE 18 0 16 ].
Definition l2_SHb : list shent := [ mkSHE 18 0 16; mkSHE 19 0 16 ].
Definition l2_xa (v n : Z) : list word := map (Z_to_bv 64) [v; n].
Definition l2_xb (v n s len : Z) : list word := map (Z_to_bv 64) [v; n; s; len].

Lemma l2a_state : forall (W : world SEGS) regs mem SP HA v n,
getr regs 2 = w64 SP -> getr regs 8 = w64 (HA + 88) -> getr regs 18 = w64 (HA + 80) ->
getr regs 25 = w64 SB -> getr regs 26 = w64 ((HA + 80) / 8 + SB) ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 1 <= n <= 2 ^ 26 ->
val_mem SEGS (arm W mem) (HA + 80) 8 v -> val_mem SEGS (arm W mem) (HA + 88) 4 n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (HA + 80) 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (l2_xa v n))) ss_l2a
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l2)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx1 l2_SHa (Eimg (Ereg regs (l2_xa v n))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP HA v n H2 H8 H18 H25 H26 HSP HSPa HA8 HAlo HAhi Hv Hv16 Hn Mv Mn HRA.
pose proof pa_B_ok as HBASE.
assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := Eimg (Ereg regs (l2_xa v n))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (l2_xa v n) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E18 : ew E 18 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 v) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; rewrite E18; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_l2a. apply pa_entry_st_ok_full.
  + unfold l2_sr.
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H26. unfold w64, l2_shv. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
         rewrite (l2_U_sh E 18 0 (HA + 80) E18 E25) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H8. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SOff 18 8))) with (U E (SOff 18 8)).
         rewrite (U_atom_off E 18 (HA + 80) 8 E18) by lia. replace (HA + 80 + 8) with (HA + 88) by lia.
         apply unsigned_lit_small. lia. }
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold l2_hd0. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite V18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (HA + 80) 0 8 (SOff 32 0) v);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mv.
    * apply (chunk_ok_val SEGS E _ (HA + 80) 8 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      replace (HA + 80 + 8) with (HA + 88) by lia. exact Mn.
  + apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [l2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E18, E25, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, l2_SHa. constructor; [|constructor].
  eapply shent_ok_of_range.
  + exact HRA.
  + unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
  + rewrite (U_atom E 18 (HA + 80) E18) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

Lemma l2b_state : forall (W : world SEGS) regs mem SP HA v n R s len,
getr regs 2 = w64 SP -> getr regs 8 = w64 (HA + 88) -> getr regs 18 = w64 (HA + 80) -> getr regs 19 = w64 R ->
getr regs 25 = w64 SB -> getr regs 26 = w64 ((HA + 80) / 8 + SB) ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 1 <= n <= 2 ^ 26 ->
4096 <= R <= 140737479966720 -> R mod 16 = 0 -> (HA + 96 <= R \/ R + 16 <= HA + 80) -> in_app R 16 ->
0 <= s < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
val_mem SEGS (arm W mem) (HA + 80) 8 v -> val_mem SEGS (arm W mem) (HA + 88) 4 n ->
val_mem SEGS (arm W mem) R 8 s -> val_mem SEGS (arm W mem) (R + 8) 8 len ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (HA + 80) 16 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF R 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (l2_xb v n s len))) ss_l2b
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l2b)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx1 l2_SHb (Eimg (Ereg regs (l2_xb v n s len))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP HA v n R s len H2 H8 H18 H19 H25 H26 HSP HSPa HA8 HAlo HAhi Hv Hv16 Hn HR HR16 HRd HRapp Hs Hl
  Mv Mn Ms Ml HRA HRR.
pose proof pa_B_ok as HBASE.
assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := Eimg (Ereg regs (l2_xb v n s len))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (l2_xb v n s len) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E18 : ew E 18 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 R) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 v) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 s) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; rewrite E18; apply unsigned_lit_small; lia).
assert (V19 : base_val E (Some 19%nat) = R) by (cbn [base_val]; rewrite E19; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_l2b. apply pa_entry_st_ok_full.
  + unfold l2_sr.
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H26. unfold w64, l2_shv. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
         rewrite (l2_U_sh E 18 0 (HA + 80) E18 E25) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H8. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SOff 18 8))) with (U E (SOff 18 8)).
         rewrite (U_atom_off E 18 (HA + 80) 8 E18) by lia. replace (HA + 80 + 8) with (HA + 88) by lia.
         apply unsigned_lit_small. lia. }
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold l2_hd0, l2_rec. constructor; [|constructor; [|constructor]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite V18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 0 8 (SOff 32 0) v);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mv.
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 8 4 (SOff 33 0) n);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (HA + 80 + 8) with (HA + 88) by lia. exact Mn.
    * rewrite V19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ R 0 8 (SOff 34 0) s);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Ms.
      -- apply (chunk_ok_val SEGS E _ R 8 8 (SOff 35 0) len);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Ml].
  + apply pairwise_disjoint_of_extents. unfold l2_hd0, l2_rec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V18, V19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. destruct HRd; repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [l2b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E18, E25, E32, E33, E19, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, l2_SHb. constructor; [|constructor; [|constructor]].
  + eapply shent_ok_of_range.
    * exact HRA.
    * unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom E 18 (HA + 80) E18) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold SHADOW_OFF in *. lia.
  + eapply shent_ok_of_range.
    * exact HRR.
    * unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom E 19 R E19) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. cbn in Hx. destruct HRapp as [_ [HH | [HH _]]];
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

Lemma l2_amem_of_app : forall p n, in_app p n -> amem_range p n.
Proof.
intros p n (H1 & H2). pose proof ASAN_CEIL_range as AC.
unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
Lemma l2_g8_keep : forall (W W' : world SEGS) m m' a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W m) a l -> garr8 SEGS (arm W' m') a l.
Proof.
intros W W' m m' a l Hk Hg. apply (garr8_frame SEGS (arm W m) (arm W' m') a l Hg).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (Hk x Hx).
Qed.

Lemma l2c_state : forall (W : world SEGS) regs mem SP HA v n R s len,
getr regs 2 = w64 SP -> getr regs 8 = w64 (HA + 88) -> getr regs 18 = w64 (HA + 80) -> getr regs 19 = w64 R ->
getr regs 24 = w64 (R / 8 + SB) -> getr regs 25 = w64 SB -> getr regs 26 = w64 ((HA + 80) / 8 + SB) ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 1 <= n <= 2 ^ 26 ->
4096 <= R <= 140737479966720 -> R mod 16 = 0 -> (HA + 96 <= R \/ R + 16 <= HA + 80) -> in_app R 16 -> R + 16 <= SP ->
0 <= s < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
val_mem SEGS (arm W mem) (SP + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W mem) (HA + 80) 8 v -> val_mem SEGS (arm W mem) (HA + 88) 4 n -> awr W mem (HA + 88) 4 ->
val_mem SEGS (arm W mem) R 8 s -> val_mem SEGS (arm W mem) (R + 8) 8 len ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (HA + 80) 16 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF R 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (l2_xb v n s len))) ss_l2c
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l2h)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx1 l2_SHb (Eimg (Ereg regs (l2_xb v n s len))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP HA v n R s len H2 H8 H18 H19 H24 H25 H26 HSP HSPa HA8 HAlo HAhi Hv Hv16 Hn HR HR16 HRd HRapp HRS Hs Hl
  M16 Mv Mn Hwn Ms Ml HRA HRR.
pose proof pa_B_ok as HBASE.
assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HD88 : 0 <= (HA + 88) / 8 <= HA + 88) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HDR : 0 <= R / 8 <= R) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := Eimg (Ereg regs (l2_xb v n s len))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (l2_xb v n s len) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E18 : ew E 18 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 R) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 v) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 s) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (V2 : base_val E (Some 2%nat) = SP) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; rewrite E18; apply unsigned_lit_small; lia).
assert (V19 : base_val E (Some 19%nat) = R) by (cbn [base_val]; rewrite E19; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_l2c. apply pa_entry_st_ok_full.
  + unfold l2c_sr, l2_sr.
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H24. unfold w64, l2_shr. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 25 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 25 0))).
         rewrite (l2_U_sh E 19 0 R E19 E25) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H26. unfold w64, l2_shv. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
         rewrite (l2_U_sh E 18 0 (HA + 80) E18 E25) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H8. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SOff 18 8))) with (U E (SOff 18 8)).
         rewrite (U_atom_off E 18 (HA + 80) 8 E18) by lia. replace (HA + 80 + 8) with (HA + 88) by lia.
         apply unsigned_lit_small. lia. }
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold l2_fr, l2_hdw, l2_rec. constructor; [|constructor; [|constructor; [|constructor]]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite V2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ SP 16 8 l2_shn ((HA + 88) / 8 + SB));
      [| unfold SB; zside | zside | exact M16].
      unfold l2_shn. apply bv_eq.
      change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))))
        with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))).
      rewrite (l2_U_sh E 18 8 (HA + 80) E18 E25) by lia.
      replace (HA + 80 + 8) with (HA + 88) by lia. rewrite unsigned_lit_small; [reflexivity|].
      unfold SB. lia.
    * rewrite V18. split; [lia|]. split; [lia|]. split.
      { intros o Ho. unfold awr, arm in Hwn. replace (HA + 80 + o) with (HA + 88 + (o - 8)) by lia. exact (Hwn (o - 8) ltac:(lia)). }
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 0 8 (SOff 32 0) v);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mv.
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 8 4 (SOff 33 0) n);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (HA + 80 + 8) with (HA + 88) by lia. exact Mn.
    * rewrite V19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ R 0 8 (SOff 34 0) s);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Ms.
      -- apply (chunk_ok_val SEGS E _ R 8 8 (SOff 35 0) len);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Ml].
  + apply pairwise_disjoint_of_extents. unfold l2_fr, l2_hdw, l2_rec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V2, V18, V19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. destruct HRd; repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [l2b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E18, E25, E32, E33, E19, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, l2_SHb. constructor; [|constructor; [|constructor]].
  + eapply shent_ok_of_range.
    * exact HRA.
    * unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom E 18 (HA + 80) E18) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold SHADOW_OFF in *. lia.
  + eapply shent_ok_of_range.
    * exact HRR.
    * unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom E 19 R E19) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. cbn in Hx. destruct HRapp as [_ [HH | [HH _]]];
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

Lemma l2t_state : forall (W : world SEGS) regs mem SP HA,
getr regs 2 = w64 SP -> getr regs 18 = w64 (HA + 80) -> getr regs 25 = w64 SB ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs ([] : list word))) ss_l2t
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l2t)) mem (seg_rom SEGS))).
Proof.
intros W regs mem SP HA H2 H18 H25 HSP HSPa HA8 HAlo HAhi.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs ([] : list word))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E18 : ew E 18 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
rewrite restrict_mkst_fx. unfold ss_l2t. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
  cbn [l2t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E18, E25, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
  unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): W_check_shape_ends.v's room record *)
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
(* the Section hypotheses of W_check_shape_ends.v's generic walk, verbatim and in its order *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
(* the free rule in its caller-context form (W_journal_x Section hc), one CTX for the allocator's free entry; the loop's
   one free call hands the rule the chain [] (s0 holds &held.n, an image address), so its trace is the singleton
   [its return address]: free at 0x85518 returns to 0x8551c = check_shape_ends + 0x16c *)
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis HCTX_cshe_l2 : In [BASE + AF_fr_check_shape_ends + 0x16c] CTX_AFREE.
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis ALDROP : forall ly S W mem ly' S' W' mem' LA l lines i,
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
   Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) ->
(forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
awr W' mem' LA 16 ->
val_mem SEGS (arm W' mem') (LA + 8) 4 (HarnessRep.hl_n l - 1) ->
(forall k, 0 <= k < AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (HarnessRep.hl_v l + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) mem (HarnessRep.hl_v l + AREC * Z.of_nat i + AREC + k)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * Z.of_nat i \/
 HarnessRep.hl_v l + AREC * (HarnessRep.hl_n l - 1) <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall r, In r (HarnessRep.hl_recs (ldrop_list l i)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines.
Hypothesis PLACEG0 : VAL A_g_gone + 1 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL A_g_gone.
Hypothesis PLACEG32 : VAL A_g_gone + 1 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL A_g_gone.
Hypothesis HGR : gx_ok SEGS B cshe_ro.
Hypothesis HGRR : gx_rt B cshe_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let BR := paj_branch (PI := PI).
(* every ghost list a journal of this walk reaches is [] (HP0 at the state the journal ends in) *)
Lemma l2_ar {G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k} :
ajournal_gx_x SEGS B PST ARx G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k ->
ARx ly1 S1 hp1 W1 mem1 md1.
Proof. intros HJ. eapply ajournal_gx_AR_x. exact HJ. Qed.
Lemma l2_hp0 {G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k} :
ajournal_gx_x SEGS B PST ARx G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k -> hp1 = [].
Proof. intros HJ. exact (HP0 _ _ _ _ _ _ (l2_ar HJ)). Qed.

(* ------------------------------------------------------------------ keeping the source *)
(* the bytes asrc_at reads (its own 96 bytes, and its lists' blocks) carry it to a later memory (W_cshe_l3.v
   l3_list_kept / l3_src_kept) *)
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
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpl & _ & _ & HE & HH & _).
destruct (l2_list_kept _ _ _ _ _ _ (HA1 + 16) _ _ HP ltac:(intros a Ha; apply KH; unfold ASRC; lia) KB) as [K1 B1].
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
Lemma l2_src_step : forall ly1 S1 hp1 md1 (W1 W2 : world SEGS) m1 m2 HA1 h1 lo hi,
ARx ly1 S1 hp1 W1 m1 md1 -> asrc_at B ly1 S1 W1 m1 HA1 h1 ->
(forall a, HA1 <= a < HA1 + ASRC -> in_img SEGS a) -> alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> wle W1 W2 ->
asrc_at B ly1 S1 W2 m2 HA1 h1.
Proof.
intros ly1 S1 hp1 md1 W1 W2 m1 m2 HA1 h1 lo hi HAR HS Himg Hlo HK Hp Hw.
pose proof (asan_consts) as (C1 & _).
apply (l2_src_kept ly1 S1 W1 W2 m1 m2 HA1 h1 HS).
- intros a Ha. split; [|intros Hwr; exact (l2_writable_kept_w W1 W2 m1 m2 a (Hp a) Hw Hwr)].
  pose proof (pa_img_range a (Himg a Ha)) as HI. apply HK; lia.
- intros b n a Hin Ha. split; [|intros Hwr; exact (l2_writable_kept_w W1 W2 m1 m2 a (Hp a) Hw Hwr)].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 m1 md1 b n HAR Hin) as (_ & B4096 & Bceil & _).
  apply HK; lia.
Qed.
Lemma l2_saved_kept : forall (W1 W2 : world SEGS) m1 m2 sp rs,
(forall a, sp - 104 <= a < sp -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
cshe_saved W1 m1 sp rs -> cshe_saved W2 m2 sp rs.
Proof.
intros W1 W2 m1 m2 sp rs HK HS. unfold cshe_saved in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; (apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [intros k Hk; apply HK; cbn in Hk; lia | assumption]).
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
(* the bytes a list's predicate reads are kept when its head is and every block of it (each satisfying P0) is
   (W_check_no_loss.v cnl_list_kept) *)
Lemma l2_list_kept_P : forall ly1 S1 hp1 W1 m1 md1 W2 m2 LA l lines (P0 : Z -> Prop),
ARx ly1 S1 hp1 W1 m1 md1 -> alist_at B ly1 S1 W1 m1 LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (ablocks B ly1 S1) -> P0 b -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
(forall b, In b (list_blocks l) -> P0 b) ->
akept W1 m1 W2 m2 (alist_fp LA l).
Proof.
intros ly1 S1 hp1 W1 m1 md1 W2 m2 LA l lines P0 HAR HL KH KB HP rr Hr a Ha.
assert (Hrq : forall n, 0 <= n -> n <= req_size n)
  by (intros n Hn; unfold req_size; destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E|]; lia).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [apply KH; exact Ha|].
apply in_app_or in Hr as [Hr | Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
  destruct HL as (_ & _ & _ & _ & (Hn & _) & [(Hc & _) | (Hc & Hin & Hj & _)] & _); [apply Z.eqb_neq in Ec; lia|].
  apply (KB _ _ a Hin).
  + apply HP. unfold list_blocks. rewrite Ec. left. reflexivity.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, l2_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul in Ha.
    change (Z.of_nat 16) with 16 in Ha. unfold hl_n in Hj. pose proof (Hrq (AREC * hl_cap l) ltac:(unfold AREC; lia)).
    unfold AREC in *. lia.
- apply in_map_iff in Hr as (x & <- & Hx).
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF x Hx) as (Hin & _).
  apply (KB _ _ a Hin).
  + apply HP. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hx.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha.
    pose proof (Hrq (Z.of_nat (length (snd x)) + 1) ltac:(lia)). lia.
Qed.
Lemma l2_alist_blks_fst : forall (l : hlist) b, In b (alist_blks l) -> In (fst b) (list_blocks l).
Proof.
intros l b Hb. unfold alist_blks, list_blocks in Hb |- *. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app.
- left. destruct (hl_cap l =? 0); [destruct Hb|]. destruct Hb as [<- | []]. cbn [fst]. left. reflexivity.
- right. apply in_map_iff in Hb as (x & <- & Hx). cbn [fst]. apply in_map. exact Hx.
Qed.
(* the source with its held list replaced: every other byte and block kept (W_check_no_loss.v nls_src_swap) *)
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
(* the room round: a free keeps the live counts under their bounds (one block fewer, ReplyCnt.acnt_del_le), as
   W_list_free.v lf_cnt_del *)
Lemma l2_cnt_del : forall RP0 l1 (x : Z * Z) l2, cnt_ok RP0 (l1 ++ x :: l2) -> cnt_ok RP0 (l1 ++ l2).
Proof.
intros RP0 l1 x l2 H. unfold cnt_ok in *.
apply (cnt_ok_pk_mono RP0 (fun _ => 0%nat) (fun _ => 0%nat) (l1 ++ x :: l2) (l1 ++ l2)); [|exact H].
intros P0. cbv beta. rewrite !Nat.add_0_r. apply ReplyCnt.acnt_del_le.
Qed.
(* the free of a block, lifted from the allocator parameter's rule to the walk's journal at any out-parameter window
   (W_check_no_loss.v cnl_free_gx) *)
Lemma l2_free_gx : forall XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb (o : Z) raw ch
  (kr : nat),
ajournal_gx_x SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own lyc Sc hpc W memT mdc k -> XO1 mod 16 = 0 ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
(* the room round: the rule's room (one free) and the live counts at the call *)
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
(In (pa, nb) (ablocks B ly S) -> forall i, 0 <= i < req_size nb -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 hp2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) /\
 aregs_preserved regsT regs2 /\
 (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, nb) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
 frames S2 = frames Sc /\
 acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size nb) /\
 mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
 (forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (pa <= a < pa + req_size nb) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).
Proof.
intros XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb o raw ch kr
HJ HX Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hch Hctx HRM HCNT Hfp Hmo.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
assert (Hal' : (o - XO1) mod 16 = 0) by (rewrite Zminus_mod, Hal, HX; reflexivity).
eapply SRr_mono.
{ exact (AFREE W regsT memT (STK + XO1) (sp0 + XO1) FP ly S hp W0 memS md own lyc Sc hpc mdc k pa nb (o - XO1) raw ch kr
  HJi Hin Ha0 ltac:(lia) Hal' ltac:(lia) ltac:(lia)
  (* the stack room below the call (a Theorem Labs lane's ACALL_PREFIX), from the journal's astk_ok *)
  (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o - XO1) regsT HJi ltac:(lia) ltac:(lia))
  Hgp Htp Hra Hraw Hch Hctx HRM HCNT Hfp Hmo). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs & HK & Hle & HRM2 & Herr & Hpr).
replace (sp0 + XO1 + (o - XO1) - ASTACK) with (sp0 + o - ASTACK) in HK by lia.
replace (sp0 + XO1 + (o - XO1)) with (sp0 + o) in HK by lia.
exists ly2, S2, hp2, regs2, mem2, md2. split; [reflexivity|].
split; [|split; [exact HP2 | split; [exact Hbl | split; [exact Hfrs | split; [exact HK |
  split; [exact Hle | split; [exact HRM2 | split; [exact Herr | exact Hpr]]]]]]]].
apply (ajournal_gx_pack_x SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply (proj1 HK); lia.
Qed.

(* ------------------------------------------------------------------ the loop *)
Section loop.
(* the entry of check_shape_ends (cshe_spec's names), and what the loop keeps needing of it *)
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 gone : Z) (j : nat) (h : hsrc) (P ob : list byte).
(* the room round: the caller's room budget past this call (cshe_post_x's kr) *)
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation R0 := (hl_recs (hs_held h)).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_post_x B PST ARx MT RP G regs0 ly S hp W mem md XO AT HA h P A0 gone ob kr).
Local Notation PLEN := (Z.of_nat (length P)).
(* the records past the first m: those dropped (they have the prefix), those kept *)
Local Notation DS m := (filter (fun r => CheckRep.prefixb P (snd r)) (skipn m (hl_recs (hs_held h)))).
Local Notation KP m := (filter (fun r => negb (CheckRep.prefixb P (snd r))) (skipn m (hl_recs (hs_held h)))).
Hypothesis HPRE : afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs0 mem md ch.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HSRC0 : asrc_at B ly S W mem HA h.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 4096 <= HA.
Hypothesis HAhi : HA + ASRC <= kLowMemEnd.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis HAj : HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j.
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
  ~ (sp0 - CSHE_STK <= a < sp0 + XO).
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
Hypothesis HPRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
(* where P lives: a read-only literal, or a local of one of S's fake frames (cshe_spec's disjunction) *)
Hypothesis HPHOME : (forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
  exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos)).
Hypothesis HROM0 : rom_view SEGS W mem.
Hypothesis Hgone : gone <> 0.
Hypothesis HMO : mo_ok MT S (cshe_cost MT (hs_held h)).

(* the source g_s[j]: image bytes the allocator does not own, not errno, not read-only, apart from g_gone *)
Lemma l2_HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a /\ ~ (VAL A_g_gone <= a < VAL A_g_gone + 1).
Proof.
intros a Ha. unfold ASRC in *.
assert (Hs : VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384) by (rewrite HAj in Ha; lia).
destruct (HGS a Hs) as (Hi & Hr & Hg & _).
assert (Hg' : inG cshe_ro a).
{ unfold inG, cshe_ro. apply Exists_exists. exists (VAL (A_OBJ 22), 384). split; [right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
destruct (HGR a Hg') as (_ & Ho & _). pose proof (proj1 (HGRR a Hg')) as He.
split; [exact Hi|]. split; [exact Ho|]. split; [exact He|]. split; [exact Hr | exact Hg].
Qed.
(* errno's four bytes are image bytes (the runtime's api_env) *)
Lemma l2_errno_img : forall q, 0 <= q < 4 -> in_img SEGS (as_errno B + q).
Proof. intros q Hq. pose proof (pal_env B TL) as (_ & HeImg & _). apply HeImg. lia. Qed.
(* and none of them is a byte of g_s[j] *)
Lemma l2_errno_off : forall q, 0 <= q < 4 -> ~ (HA <= as_errno B + q < HA + ASRC).
Proof.
intros q Hq Hc. destruct (l2_HAimg (as_errno B + q) Hc) as (_ & _ & He & _). lia.
Qed.

(* the invariant at the head, m records not yet examined (the Kind-B proof's cse_inv at i = m - 1,
   lib/A/Prog/check_shape_ends.v:503-521 on a working branch, over this walk's journal) *)
Definition l2_regs (regs1 : bvmap 5 word) (m : nat) : Prop :=
getr regs1 2 = w64 (sp0 - 144) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 8 = w64 (HA + 88) /\ getr regs1 9 = w64 PF /\ getr regs1 18 = w64 (HA + 80) /\
getr regs1 20 = w64 (Z.of_nat m + 1) /\ getr regs1 21 = w64 (- Z.of_nat m) /\ getr regs1 22 = w64 1 /\
getr regs1 23 = w64 (AREC * (Z.of_nat m - 1)) /\ getr regs1 25 = w64 SB /\
getr regs1 26 = w64 ((HA + 80) / 8 + SB) /\ getr regs1 27 = w64 3.
Definition l2_mem (m : nat) (ly1 : alayout) (S1 : astate) (kk : Z) (H1 : hlist) (W1 : world SEGS)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v (hs_held h) /\ hl_cap H1 = hl_cap (hs_held h) /\
hl_recs H1 = firstn m (hl_recs (hs_held h)) ++ KP m /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks (DS m) ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length (DS m)) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat m * mo_free MT) /\
rom_view SEGS W1 mem1 /\ cshe_saved W1 mem1 sp0 regs0 /\
val_mem SEGS (arm W1 mem1) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
val_mem SEGS (arm W1 mem1) AT 8 A0 /\ val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone /\
(* errno's view is the entry's (cshe_post_x's conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
(* the room round: the room budget (one free per record not yet examined) and the live counts, which only fall *)
rp_RM RP S1 (m + kr) /\ cnt_ok RP (ablocks B ly1 S1).
Definition l2_inv (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_mem m ly1 S1 kk H1 W1 mem1 md1 /\ l2_regs regs1 m.
(* 0x854d4: s3 = &v[m] *)
Definition l2_mid (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_mem (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 /\ l2_regs regs1 (Datatypes.S m) /\
getr regs1 19 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m).
(* 0x8550c: has_prefix said v[m] has the prefix; s8 = the shadow byte of &v[m] *)
Definition l2_hit (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat /\ CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = true /\
exists ly1 S1 kk H1, l2_mem (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 /\ l2_regs regs1 (Datatypes.S m) /\
getr regs1 19 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m) /\
getr regs1 24 = w64 ((hl_v (hs_held h) + AREC * Z.of_nat m) / 8 + SB).
(* where a turn ends: the head while records are left, else the epilogue *)
Definition l2_pc (m : nat) : Z := match m with O => BASE + A_cshe_ret | Datatypes.S _ => BASE + A_cshe_l2 end.

Lemma l2_regs_eq : forall regs1 regs2 m, (forall r, getr regs2 r = getr regs1 r) -> l2_regs regs1 m -> l2_regs regs2 m.
Proof. intros regs1 regs2 m E X. unfold l2_regs in *. rewrite !E. exact X. Qed.

(* the memory side of the invariant moves across a step that writes only [lo, hi), above the allocator's ceiling
   and below the frame, and keeps presence *)
Lemma l2_mem_keep : forall m ly1 S1 kk H1 (W1 W2 : world SEGS) m1 m2 md1 md2 lo hi,
l2_mem m ly1 S1 kk H1 W1 m1 md1 ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] W2 m2 md2 kk ->
alloc_ceiling <= lo -> hi <= sp0 - 144 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> wle W1 W2 ->
l2_mem m ly1 S1 kk H1 W2 m2 md2.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 W2 m1 m2 md1 md2 lo hi
  (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT)
  HJ2 Hlo Hhi HK HP Hw.
pose proof (l2_ar HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
split; [exact HJ2|].
split.
{ apply (l2_src_step ly1 S1 [] md1 W1 W2 m1 m2 HA _ lo hi HAR1 HSRC); [| exact Hlo | exact HK | exact HP | exact Hw].
  intros a Ha. exact (proj1 (l2_HAimg a Ha)). }
split; [exact HV|]. split; [exact HC|]. split; [exact HREC|]. split; [exact HPERM|].
split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split.
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi) as HI. rewrite HK by lia. exact (HROM a Hr). }
split.
{ apply (l2_saved_kept W1 W2 m1 m2 sp0 regs0); [|exact HSAV]. intros a Ha. apply HK; lia. }
split; [apply (l2_vm_keep W1 W2 m1 m2); [intros x Hx; cbn in Hx; apply HK; lia | exact M16]|].
split; [apply (l2_vm_keep W1 W2 m1 m2); [intros x Hx; cbn in Hx; apply HK; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W2 m1 m2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
  pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR. apply HK; lia. }
split; [intros q Hq; pose proof (pa_img_range _ (l2_errno_img q Hq)) as HeR; rewrite HK by lia; exact (MERR q Hq)|].
exact (conj MRM MCNT).
Qed.

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
(* a register the run did not change: the same symbolic value in the state HS0 the run started from *)
Ltac l2_keepreg HS0 HS r :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq; rewrite Bq, <- A; clear A Bq.

(* ---- 0x854c4 .. 0x854d4: the shadow check of l->v, s3 = l->v + 16 i ---- *)
Lemma l2_A : forall m W1 regs1 mem1 md1, l2_inv (Datatypes.S m) W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_mid m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l2b)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR) HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof (l2_ar HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & _).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
destruct (l2a_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) R2 R8 R18 R25 R26 HSPb HSPa HA8 HAlo HAhi'
  HvR V16 Hn1 MvH ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (l2_xa (hl_v H1) (hl_n H1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
pose proof HS as HS0.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan A_cshe_l2b.
{ apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_hd0] in Ha; lia | apply awr_ok_x_nil]. }
pmkst HS.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_nowin HFr).
assert (PRES : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
assert (T19' : getr (ms_regs ms) 19 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m)).
{ prreg HS (19%bv : bv 5) T19. rewrite T19, (EEo 23%nat 23%bv eq_refl), R23, E32, HV. unfold w64.
  rewrite YI08.alu64_add_lit. f_equal. unfold AREC. lia. }
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  replace (BASE + k) with (BASE + A_cshe_l2b) by (unfold A_cshe_l2b, AF_fr_check_shape_ends; lia) end.
apply HKont. split; [lia|].
exists ly1, S1, kk, H1. split; [|split; [|exact T19']].
- apply (l2_mem_keep (Datatypes.S m) ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 _ (sp0 - 144) (sp0 - 144) HM HJ);
  [lia | lia | intros a Ha _; exact (KEEP a Ha) | exact PRES | apply wle_refl].
- unfold l2_regs.
  split; [l2_keepreg HS0 HS (2%bv : bv 5); exact R2|].
  split; [l2_keepreg HS0 HS (3%bv : bv 5); exact R3|].
  split; [l2_keepreg HS0 HS (4%bv : bv 5); exact R4|].
  split; [l2_keepreg HS0 HS (8%bv : bv 5); exact R8|].
  split; [l2_keepreg HS0 HS (9%bv : bv 5); exact R9|].
  split; [l2_keepreg HS0 HS (18%bv : bv 5); exact R18|].
  split; [l2_keepreg HS0 HS (20%bv : bv 5); exact R20|].
  split; [l2_keepreg HS0 HS (21%bv : bv 5); exact R21|].
  split; [l2_keepreg HS0 HS (22%bv : bv 5); exact R22|].
  split; [l2_keepreg HS0 HS (23%bv : bv 5); exact R23|].
  split; [l2_keepreg HS0 HS (25%bv : bv 5); exact R25|].
  split; [l2_keepreg HS0 HS (26%bv : bv 5); exact R26|].
  l2_keepreg HS0 HS (27%bv : bv 5); exact R27.
Qed.

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
(* a register no run and no call changed, read in the state HS0 the walk started from (env OLD-related) *)
Ltac l2_keepreg2 HS0 HS r OLD :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq;
repeat (rewrite OLD in Bq by lia); rewrite Bq, <- A; clear A Bq.

Lemma l2_wrap_add : forall x c y, x + c = y -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 y.
Proof.
intros x c y <-. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* a record without the prefix: the head moves one record down, nothing else changes *)
Lemma l2_mem_miss : forall m ly1 S1 kk H1 W1 mem1 md1, (Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = false ->
l2_mem (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 -> l2_mem m ly1 S1 kk H1 W1 mem1 md1.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 mem1 md1 Hm E (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HRST).
pose proof (mo_free_nonneg MT ML) as Hf.
split; [exact HJ|]. split; [exact HSRC|]. split; [exact HV|]. split; [exact HC|].
split; [rewrite HREC; apply l2_kp_miss; [lia | exact E]|].
rewrite (l2_ds_miss P (hl_recs (hs_held h)) m ltac:(lia) E).
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|].
destruct HRST as (HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
split.
{ apply (mok_station MT S1 S1 (Z.of_nat (Datatypes.S m) * mo_free MT) 0 (Z.of_nat m * mo_free MT) ML HMOK
    (mle_start MT S1 ML)); [apply Z.mul_nonneg_nonneg; lia | rewrite Nat2Z.inj_succ; nia]. }
split; [exact HROM|]. split; [exact HSAV|]. split; [exact M16|]. split; [exact MAT|]. split; [exact MG|].
split; [exact MERR|]. split; [|exact MCNT].
(* a record without the prefix is not freed: the budget past it is smaller *)
exact (RMM_of RP S1 (m + kr) (Datatypes.S m + kr) ltac:(lia) MRM).
Qed.

(* ---- 0x854d4 .. 0x85508: the shadow checks of v[i], has_prefix(v[i].s, v[i].n, PF), beqz a0;
   no match: 0x85558 .. 0x85564, the counters and bltu, to the head or (last record) the epilogue ---- *)
Lemma l2_B : forall m W1 regs1 mem1 md1, l2_mid m W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_inv m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (l2_pc m)) mem2 (seg_rom SEGS)) md2) Post) ->
(forall W2 regs2 mem2 md2, l2_hit m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l2h)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2b)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
pose proof (cshe_P_at_x B PST ARx G LAWS FRMF HG XO [(AT, AT + 8)] CSHE_STK sp0 ly S hp W mem md HA h PF PLEN (proj1 HPRE) HSRC0
  ltac:(lia) HPRA HPHOME) as LPA. clear HPHOME.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR & R19) Kloop Khit.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & _ & _ & _ & _ & HROM & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof (l2_ar HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (unfold AREC in Vceil; lia).
(* the record v[m] *)
set (r := nth m (hl_recs (hs_held h)) (0, [])).
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
rewrite Forall_forall in HFallH. destruct (HFallH r HRIN) as (HrB & HrG & HrL & _).
destruct (HrL eq_refl) as (HrNZ & HrLEN). unfold APARTIAL in HrLEN.
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
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
assert (HRimg : HA + 96 <= RA \/ RA + 16 <= HA + 80).
{ pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as Hoff. rewrite HreqV in Hoff.
  pose proof (pa_img_range HA (proj1 (l2_HAimg HA ltac:(unfold ASRC; lia)))) as HI1.
  pose proof (pa_img_range (HA + 95) (proj1 (l2_HAimg (HA + 95) ltac:(unfold ASRC; lia)))) as HI2.
  unfold off_img in Hoff. destruct Hoff; [right | left]; lia. }
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR1 HvinH
  ltac:(lia) ltac:(rewrite HreqV; lia)) as HRAR.
destruct (l2b_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) RA (fst r) (Z.of_nat (length (snd r)))
  R2 R8 R18 R19 R25 R26 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1 ltac:(lia) ltac:(lia) HRimg HRapp ltac:(lia) ltac:(lia)
  MvH ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH) Ms0 Ml0
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia]) HRAR) as [HS SHOK].
pose proof alloc_ceiling_val as ACV.
assert (HXO0 : 0 <= XO) by (pose proof HJ as (_ & HX & _); exact HX).
remember (Eimg (Ereg regs1 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j0, (j0 < 4)%nat -> ew E (32 + j0) =
  nth j0 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))) (Z_to_bv 64 0)).
{ intros j0 Hj0. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E34 : ew E 34 = Z_to_bv 64 (fst r)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 3%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (EEo 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite (EEo 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = RA) by (rewrite (EEo 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
pose proof HS as HS0.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan AF_fr_has_prefix.
{ cbv [ss_mem ss_l2b l2_hd0 l2_rec].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_nowin HFr).
assert (PRESr : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] W1 _ _ kk HJ)
  as (memS & HJi & HgS).
assert (HAR3 : ARx ly1 S1 [] W1 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (Usp1 : spZ (ms_regs ms) = sp0 - 144) by (unfold spZ; rewrite Q2; exact Usp).
assert (HPREh : afn_pre_x SEGS B ARx HP_STK ly1 S1 [] W1 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_x_at SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 [] W1 (ms_mem ms) mdc kk
    (ms_regs ms) HP_STK (- 144 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia. }
(* read-only bytes are the entry's *)
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi). rewrite KEEPr by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
(* P's bytes and its shadow, wherever P lives (W_check_shape_ends.v cshe_P_at_x) *)
destruct (LPA ly1 S1 [] W1 (ms_mem ms) mdc kk HJ ROMK) as (PK & HRAP & HHVP & _).
assert (TXT : cshe_bytes W1 (ms_mem ms) (fst r) (snd r ++ [Z_to_bv 8 0])).
{ apply cshe_bytes_of_garr8. apply (l2_g8_keep W1 W1 mem1 (ms_mem ms)); [|exact HrG].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. apply KEEPr. lia. }
assert (PTXT : cshe_bytes W1 (ms_mem ms) PF (P ++ [Z_to_bv 8 0])).
{ intros t Ht. rewrite length_app in Ht. cbn [length] in Ht. rewrite PK by lia.
  destruct (Z_lt_ge_dec t PLEN) as [Hlt | Hge].
  - rewrite app_nth1 by lia. exact (HPB t ltac:(lia)).
  - assert (Ht' : t = PLEN) by lia. rewrite Ht'. rewrite app_nth2 by lia.
    replace (Z.to_nat PLEN - length P)%nat with 0%nat by lia. cbn [nth]. rewrite HPN. reflexivity. }
eapply SRr_bind.
{ apply (W_has_prefix.pb_has_prefix_x B PST ARx LAWS ASTRLEN ABCMP W1 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdc []
    (fst r) (Z.of_nat (length (snd r))) PF PLEN HPREh).
  - rewrite Q10, E34. reflexivity.
  - rewrite Q11, E35. reflexivity.
  - rewrite Q12, (EEo 9%nat 9%bv eq_refl), R9. reflexivity.
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
  - unfold hp_off. rewrite Usp1. intros a Ha. pose proof (proj2 (HPV a ltac:(lia))) as Hno. rewrite WS in Hno.
    unfold HP_STK, ESTACK. clear - Hno HXO0. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact HHVP.
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). rewrite PK by lia.
    exact (proj1 (HPV a ltac:(lia))).
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle2. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (fst r + (a - fst r)) by lia.
      rewrite (TXT (a - fst r) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + unfold hp_off. rewrite Usp1. intros a Ha. unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *. lia.
    + apply l2_amem_of_app. apply (in_app_sub (fst r) (Z.of_nat (length (snd r)) + 1)); [exact Hrapp | lia | lia | lia].
    + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 (ms_mem ms) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 (ms_mem ms) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (l2_shv_sub _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) HHVP). }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HFRc & HRES).
rewrite Usp1 in HJc, HFRc.
assert (HB : exists b, (b = 0 \/ b = 1) /\ getr regs2 10 = w64 b /\ (b = 1 <-> CheckRep.prefixb P (snd r) = true)).
{ destruct HRES as [(Hle2 & Hpre & Hr10) | (Hnp & Hr10)].
  - exists 1. split; [right; reflexivity|]. split; [exact Hr10|]. split; [intros _|intros _; reflexivity].
    apply (proj1 (cshe_prefixb_iff W1 (ms_mem ms) (fst r) PF (snd r) P TXT PTXT)). split; assumption.
  - exists 0. split; [left; reflexivity|]. split; [exact Hr10|]. split; [intros Hc; discriminate Hc|].
    intros Hp. exfalso. destruct (proj2 (cshe_prefixb_iff W1 (ms_mem ms) (fst r) PF (snd r) P TXT PTXT) Hp) as (Hl3 & Hpr).
    exact (Hnp Hl3 Hpr). }
destruct HB as (b & Hb01 & Hb10 & HbP).
assert (HJc' : ajournal_gx_x SEGS B PST ARx G 0 [] HP_STK (sp0 - 144) [] ly1 S1 [] W1 (ms_mem ms) mdc [] ly1 S1 [] W2 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|].
  apply ajournal_gx_nil_x. exact HJc. }
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 [] W1 (ms_mem ms) mdc kk HP_STK (sp0 - 144) 0 [] [] [] ly1 S1 [] W2 mem2 md2 0 HJ HJc'
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18, ?U19.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRc; [lia|]. unfold HP_STK, ESTACK. lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRc; [lia|]. unfold HP_STK, ESTACK. lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (F40 : ew Ea 40 = w64 b) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hb10).
clear HEa.
assert (F18 : ew Ea 18 = Z_to_bv 64 (HA + 80)) by (rewrite OLDa by lia; rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (F19 : ew Ea 19 = Z_to_bv 64 RA) by (rewrite OLDa by lia; rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (F25 : ew Ea 25 = Z_to_bv 64 SB) by (rewrite OLDa by lia; rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (HAR2 : ARx ly1 S1 [] W2 mem2 md2)
  by exact (l2_ar HJ2).
assert (SHOK2 : sh_ok SEGS Bx1 l2_SHb Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, l2_SHb. constructor; [|constructor; [|constructor]].
  - eapply shent_ok_of_range.
    + exact (azs_range_addressable_x B ARx LAWS ly1 S1 [] W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
    + unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
    + rewrite (U_atom Ea 18 (HA + 80) F18) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold SHADOW_OFF in *. lia.
  - eapply shent_ok_of_range.
    + exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W2 mem2 md2 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR2 HvinH
        ltac:(lia) ltac:(rewrite HreqV; lia)).
    + unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
    + rewrite (U_atom Ea 19 RA F19) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. cbn in Hx. destruct HRapp as [_ [HH | [HH _]]];
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* what the turn kept so far, from the head's memory *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) by (intros a Ha Hs; rewrite HFRc by assumption; apply KEEPr; exact Ha).
assert (PRES2 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) by (intros a Hp; exact (HPR2 a (PRESr a Hp))).
rewrite Q1.
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNx BR HS SHOK2 Bspan.
- (* beqz taken: no match *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb0 : b = 0) by (apply Z.eqb_eq in Hc; exact Hc).
  assert (HPF : CheckRep.prefixb P (snd r) = false)
    by (destruct (CheckRep.prefixb P (snd r)) eqn:Eq; [exfalso; pose proof (proj2 HbP eq_refl); lia | reflexivity]).
  paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_nil. }
  prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_mem (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms1) mdb).
  { apply (l2_mem_keep (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms1) md1 mdb (sp0 - 144 - HP_STK) (sp0 - 144) HM HJ2);
    [unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *; lia | lia | | | exact Hwle2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  pose proof (l2_mem_miss m ly1 S1 kk H1 W2 (ms_mem ms1) mdb Hle HPF MEM1) as MEM0.
  assert (REGS1 : l2_regs (ms_regs ms1) m).
  { unfold l2_regs.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [rewrite T20, (OLDa 20%nat) by lia; rewrite (EEo 20%nat 20%bv eq_refl), R20; unfold w64; apply l2_wrap_add; lia|].
    split; [rewrite T21, (OLDa 21%nat) by lia; rewrite (EEo 21%nat 21%bv eq_refl), R21; unfold w64; apply l2_wrap_add; lia|].
    split; [l2_keepreg2 HS0 HS (22%bv : bv 5) OLDa; exact R22|].
    split; [rewrite T23, (OLDa 23%nat) by lia; rewrite (EEo 23%nat 23%bv eq_refl), R23; unfold w64; apply l2_wrap_add;
            unfold AREC; lia|].
    split; [l2_keepreg2 HS0 HS (25%bv : bv 5) OLDa; exact R25|].
    split; [l2_keepreg2 HS0 HS (26%bv : bv 5) OLDa; exact R26|].
    l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27. }
  assert (F20 : ew Ea 20 = Z_to_bv 64 (Z.of_nat (Datatypes.S m) + 1))
    by (rewrite OLDa by lia; rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (F22 : ew Ea 22 = Z_to_bv 64 1) by (rewrite OLDa by lia; rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  clear T20 T21 T23.
  pose proof HS as HSt.
  psrr_branch_tok RUNx BR HS SHOK2 Bspan.
  + (* bltu taken: records are left, back to the head *)
    rewrite branch_ltu_U, (U_atom Ea 22 1 F22), (U_atom_off Ea 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc0 by (unfold hl_n in Hn26; lia).
    destruct m as [|m']; [exfalso; apply Z.ltb_lt in Hc0; lia|].
    paj_run_to_tok_x RUNTOx HS HJ2 SHOK2 Bspan A_cshe_l2.
    { cbn [ss_mem add_cond].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    pmkst HS.
    assert (RG : forall rr, getr (ms_regs ms2) rr = getr (ms_regs ms1) rr).
    { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
      rewrite X1, X0. reflexivity. }
    assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a)
      by (intros a Ha; l2_back).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
    assert (MEMF : l2_mem (Datatypes.S m') ly1 S1 kk H1 W2 (ms_mem ms2) mdd).
    { apply (l2_mem_keep (Datatypes.S m') ly1 S1 kk H1 W2 W2 (ms_mem ms1) (ms_mem ms2) mdb mdd (sp0 - 144) (sp0 - 144) MEM0 HJ2);
      [lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply wle_refl].
      intros a Hp. l2_pres_back Hp. }
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
      replace (BASE + k) with (l2_pc (Datatypes.S m')) by (cbn [l2_pc]; unfold A_cshe_l2, AF_fr_check_shape_ends; lia) end.
    apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
    exact (l2_regs_eq (ms_regs ms1) (ms_regs ms2) (Datatypes.S m') RG REGS1).
  + (* bltu not taken: that was the last record, on to the epilogue *)
    rewrite branch_ltu_U, (U_atom Ea 22 1 F22), (U_atom_off Ea 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc0 by (unfold hl_n in Hn26; lia).
    assert (Hm0 : m = 0%nat) by (apply Z.ltb_ge in Hc0; lia). subst m.
    paj_run_to_tok_x RUNTOx HS HJ2 SHOK2 Bspan A_cshe_ret.
    { cbn [ss_mem add_cond].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    pmkst HS.
    assert (RG : forall rr, getr (ms_regs ms2) rr = getr (ms_regs ms1) rr).
    { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
      rewrite X1, X0. reflexivity. }
    assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a)
      by (intros a Ha; l2_back).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
    assert (MEMF : l2_mem 0 ly1 S1 kk H1 W2 (ms_mem ms2) mdd).
    { apply (l2_mem_keep 0 ly1 S1 kk H1 W2 W2 (ms_mem ms1) (ms_mem ms2) mdb mdd (sp0 - 144) (sp0 - 144) MEM0 HJ2);
      [lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply wle_refl].
      intros a Hp. l2_pres_back Hp. }
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
      replace (BASE + k) with (l2_pc 0) by (cbn [l2_pc]; unfold A_cshe_ret, AF_fr_check_shape_ends; lia) end.
    apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
    exact (l2_regs_eq (ms_regs ms1) (ms_regs ms2) 0 RG REGS1).
- (* beqz not taken: a match *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb1 : b = 1) by (destruct Hb01 as [-> | ->]; [discriminate Hc | reflexivity]).
  assert (HPT : CheckRep.prefixb P (snd r) = true) by (apply HbP; exact Hb1).
  paj_run_to_tok_x RUNTOx HS HJ2 SHOK2 Bspan A_cshe_l2h.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_mem (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms1) mdb).
  { apply (l2_mem_keep (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms1) md1 mdb (sp0 - 144 - HP_STK) (sp0 - 144) HM HJ2);
    [unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *; lia | lia | | | exact Hwle2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  prreg HS (24%bv : bv 5) T24.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_cshe_l2h) by (unfold A_cshe_l2h, AF_fr_check_shape_ends; lia) end.
  apply Khit. split; [exact Hle|]. split; [exact HPT|].
  exists ly1, S1, kk, H1. split; [exact MEM1|]. split.
  { unfold l2_regs.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [l2_keepreg2 HS0 HS (20%bv : bv 5) OLDa; exact R20|].
    split; [l2_keepreg2 HS0 HS (21%bv : bv 5) OLDa; exact R21|].
    split; [l2_keepreg2 HS0 HS (22%bv : bv 5) OLDa; exact R22|].
    split; [l2_keepreg2 HS0 HS (23%bv : bv 5) OLDa; exact R23|].
    split; [l2_keepreg2 HS0 HS (25%bv : bv 5) OLDa; exact R25|].
    split; [l2_keepreg2 HS0 HS (26%bv : bv 5) OLDa; exact R26|].
    l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27. }
  split; [l2_keepreg2 HS0 HS (19%bv : bv 5) OLDa; exact R19|].
  rewrite T24, F19, F25. unfold w64. rewrite l2_srl3 by lia. rewrite YI08.alu64_add_lit. reflexivity.
Qed.

(* ---- 0x85558 .. 0x85568: s4--, s5++, s7 -= 16, bltu s6, s4 -> the head, else j 0x85690 ---- *)
Lemma l2_D : forall m ly1 S1 kk H1 W1 regs1 mem1 md1, (Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
l2_mem m ly1 S1 kk H1 W1 mem1 md1 -> l2_regs regs1 (Datatypes.S m) ->
(forall W2 regs2 mem2 md2, l2_inv m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (l2_pc m)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2t)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 regs1 mem1 md1 Hle HM HR Kloop.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
pose proof (l2t_state W1 regs1 mem1 (sp0 - 144) HA R2 R18 R25 HSPb HSPa HA8 HAlo HAhi') as HS.
remember (Eimg (Ereg regs1 ([] : list word))) as E eqn:HE.
assert (SHOK : sh_ok SEGS Bx1 [] E (mrestrict (w_H W1) mem1)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (F20 : ew E 20 = Z_to_bv 64 (Z.of_nat (Datatypes.S m) + 1)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (F22 : ew E 22 = Z_to_bv 64 1) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
pose proof HS as HS0.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ SHOK Bspan.
{ cbv [ss_mem ss_l2t]. apply awr_ok_x_nil. }
prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23.
assert (REGS1 : l2_regs (ms_regs ms) m).
{ unfold l2_regs.
  split; [l2_keepreg HS0 HS (2%bv : bv 5); exact R2|].
  split; [l2_keepreg HS0 HS (3%bv : bv 5); exact R3|].
  split; [l2_keepreg HS0 HS (4%bv : bv 5); exact R4|].
  split; [l2_keepreg HS0 HS (8%bv : bv 5); exact R8|].
  split; [l2_keepreg HS0 HS (9%bv : bv 5); exact R9|].
  split; [l2_keepreg HS0 HS (18%bv : bv 5); exact R18|].
  split; [rewrite T20, (EEo 20%nat 20%bv eq_refl), R20; unfold w64; apply l2_wrap_add; lia|].
  split; [rewrite T21, (EEo 21%nat 21%bv eq_refl), R21; unfold w64; apply l2_wrap_add; lia|].
  split; [l2_keepreg HS0 HS (22%bv : bv 5); exact R22|].
  split; [rewrite T23, (EEo 23%nat 23%bv eq_refl), R23; unfold w64; apply l2_wrap_add; unfold AREC; lia|].
  split; [l2_keepreg HS0 HS (25%bv : bv 5); exact R25|].
  split; [l2_keepreg HS0 HS (26%bv : bv 5); exact R26|].
  l2_keepreg HS0 HS (27%bv : bv 5); exact R27. }
clear T20 T21 T23.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
pose proof HS as HSt.
psrr_branch_tok RUNx BR HS SHOK Bspan.
- (* bltu taken: records are left, back to the head *)
  rewrite branch_ltu_U, (U_atom E 22 1 F22), (U_atom_off E 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc
    by (unfold hl_n in Hn26; lia).
  destruct m as [|m']; [exfalso; apply Z.ltb_lt in Hc; lia|].
  paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan A_cshe_l2.
  { cbv [ss_mem add_cond]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms0) rr = getr (ms_regs ms) rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
    rewrite X1, X0. reflexivity. }
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_back).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_mem (Datatypes.S m') ly1 S1 kk H1 W1 (ms_mem ms0) mdd).
  { apply (l2_mem_keep (Datatypes.S m') ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms0) md1 mdd (sp0 - 144) (sp0 - 144) HM HJ);
    [rewrite WS in *; lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply wle_refl].
    intros a Hp. l2_pres_back Hp. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (l2_pc (Datatypes.S m')) by (cbn [l2_pc]; unfold A_cshe_l2, AF_fr_check_shape_ends; lia) end.
  apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
  exact (l2_regs_eq (ms_regs ms) (ms_regs ms0) (Datatypes.S m') RG REGS1).
- (* bltu not taken: that was the last record, on to the epilogue *)
  rewrite branch_ltu_U, (U_atom E 22 1 F22), (U_atom_off E 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc
    by (unfold hl_n in Hn26; lia).
  assert (Hm0 : m = 0%nat) by (apply Z.ltb_ge in Hc; lia). subst m.
  paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan A_cshe_ret.
  { cbv [ss_mem add_cond]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms0) rr = getr (ms_regs ms) rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
    rewrite X1, X0. reflexivity. }
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_back).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_mem 0 ly1 S1 kk H1 W1 (ms_mem ms0) mdd).
  { apply (l2_mem_keep 0 ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms0) md1 mdd (sp0 - 144) (sp0 - 144) HM HJ);
    [rewrite WS in *; lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply wle_refl].
    intros a Hp. l2_pres_back Hp. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (l2_pc 0) by (cbn [l2_pc]; unfold A_cshe_ret, AF_fr_check_shape_ends; lia) end.
  apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
  exact (l2_regs_eq (ms_regs ms) (ms_regs ms0) 0 RG REGS1).
Qed.

(* the memory side of a drop: from the invariant before the turn (m + 1 records to examine, v[m] has the prefix), the
   free of v[m].s, the memmove and the store of n - 1 give the invariant with m records to examine; every fact the
   walk proves about the memory after the turn is a premise *)
Lemma l2_mem_drop : forall m ly1 S1 kk H1 W1 mem1 md1 ly2 S2 W2 mem2 md2,
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = true ->
l2_mem (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 [] W2 mem2 md2 (kk + 1) ->
wle W1 W2 ->
(exists l1 l2, ablocks B ly1 S1 = l1 ++ (fst (nth m (hl_recs (hs_held h)) (0, [])),
   Z.of_nat (length (snd (nth m (hl_recs (hs_held h)) (0, [])))) + 1) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
frames S2 = frames S1 ->
mo_le MT S1 S2 (mo_free MT) ->
rom_view SEGS W2 mem2 ->
val_mem SEGS (arm W2 mem2) (HA + 88) 4 (hl_n H1 - 1) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 88 <= a < HA + 92) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 144 - ASTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
  ~ (fst (nth m (hl_recs (hs_held h)) (0, [])) <= a <
     fst (nth m (hl_recs (hs_held h)) (0, [])) + Z.of_nat (length (snd (nth m (hl_recs (hs_held h)) (0, [])))) + 1) ->
  ~ (hl_v (hs_held h) + AREC * Z.of_nat m <= a <
     hl_v (hs_held h) + AREC * Z.of_nat m + AREC * (hl_n H1 - 1 - Z.of_nat m)) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall k, 0 <= k < AREC * (hl_n H1 - 1 - Z.of_nat m) ->
  aview SEGS (w_H W2) mem2 (hl_v (hs_held h) + AREC * Z.of_nat m + k) =
  aview SEGS (w_H W1) mem1 (hl_v (hs_held h) + AREC * Z.of_nat m + AREC + k)) ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W1) mem1 (as_errno B + j)) ->
(* the room round: the free's post room (its rule's kr is the m + kr left) *)
rp_RM RP S2 (m + kr) ->
l2_mem m ly2 S2 (kk + 1) (ldrop_list H1 m) W2 mem2 md2.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 mem1 md1 ly2 S2 W2 mem2 md2 Hle HPT HM HJ2 Hwle Hbl Hfrs2 Hle2 ROMF MnF KIMG KPRES KHI KBLK KMOV
  KERR HRMd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as ACV.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (EAS : ESTACK = 4096 /\ ASTACK = 16384) by (split; reflexivity).
pose proof (mo_free_nonneg MT ML) as Hf0.
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
pose proof (l2_ar HJ) as HAR1.
pose proof (l2_ar HJ2)
  as HAR2.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPD & _ & _ & _ & _ & _ & _ & _ & HPIN & HPJLEN & _ & _ & HED & HAH0 & HNDS).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected] in HPD, HPIN, HPJLEN, HED.
pose proof HNDS as HNDS0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil.
set (r := nth m (hl_recs (hs_held h)) (0, [])) in *.
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
pose proof HFallH as HFallH'. rewrite Forall_forall in HFallH'. destruct (HFallH' r HRIN) as (HrB & _).
assert (HreqT : forall x : Z * list byte, req_size (Z.of_nat (length (snd x)) + 1) = Z.of_nat (length (snd x)) + 1).
{ intros x. unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq;
  [apply Z.eqb_eq in Eq; pose proof (Nat2Z.is_nonneg (length (snd x))); lia | reflexivity]. }
assert (VNE : hl_v H1 <> fst r) by (intros Heq; apply HninH; rewrite Heq; apply in_map; exact HRIN).
assert (Ecap : (hl_cap H1 =? 0) = false) by (apply Z.eqb_neq; lia).
(* the head bytes of the source *)
assert (GH : forall a, HA <= a < HA + 96 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (l2_HAimg a ltac:(unfold ASRC; lia)) as (Hi & Ho & He & _). split; [exact Hi|]. split; [exact Ho | exact He]. }
assert (KHD : forall a, HA <= a < HA + 96 -> ~ (HA + 88 <= a < HA + 92) -> abyte_kept W1 mem1 W2 mem2 a).
{ intros a Ha Hw. destruct (GH a Ha) as (Hi & Ho & He). split; [exact (KIMG a Hi Ho He Hw)|].
  intros Hwr. apply (l2_writable_kept_w W1 W2 mem1 mem2 a); [intros Hp; exact (KPRES a Hi Ho He Hp) | exact Hwle | exact Hwr]. }
(* the blocks other than the freed text and the vector keep their bytes and their writability *)
assert (KOFF : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + Z.of_nat (length (snd r)) + 1)).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 p n (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 Hin HrB
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite (HreqT r) in DJx. lia. }
assert (KOFV : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> hl_v H1 -> p <= a < p + req_size n ->
  ~ (hl_v H1 <= a < hl_v H1 + AREC * hl_cap H1)).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 p n (hl_v H1) (AREC * hl_cap H1) HAR1 Hin HvinH
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite HreqV in DJx. lia. }
assert (BLK2 : forall p n, In (p, n) (ablocks B ly1 S1) -> (p, n) <> (fst r, Z.of_nat (length (snd r)) + 1) ->
  In (p, n) (ablocks B ly2 S2)).
{ intros p n Hin Hne2. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | exfalso; exact (Hne2 (eq_sym Hx)) | right; exact Hx]. }
assert (KBK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <> hl_v H1 -> p <= a < p + req_size n ->
  abyte_kept W1 mem1 W2 mem2 a).
{ intros p n a Hin Hp1 Hp2 Ha. split.
  - apply (KBLK p n a Hin Ha (KOFF p n a Hin Hp1 Ha)). intros Hc. apply (KOFV p n a Hin Hp2 Ha). rewrite HV.
    unfold hl_n in *. unfold AREC in *. lia.
  - intros Hw.
    destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 mem2 md2 p n HAR2
      (BLK2 p n Hin ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq)))) as (_ & _ & _ & _ & Hpres & _).
    exact (apresent_writable SEGS _ _ _ (proj1 (Hpres a Ha))). }
(* the held list, one record shorter *)
assert (HE2 : alist_at B ly2 S2 W2 mem2 (HA + 80) (ldrop_list H1 m) true).
{ apply (ALDROP ly1 S1 W1 mem1 ly2 S2 W2 mem2 (HA + 80) H1 true m HAH).
  - lia.
  - rewrite ENTH. exact Hbl.
  - intros a Ha. exact (proj1 (KHD a ltac:(lia) ltac:(lia))).
  - intros i Hi. destruct (GH (HA + 80 + i) ltac:(lia)) as (Hi1 & Ho1 & He1).
    apply (l2_writable_kept_w W1 W2 mem1 mem2 (HA + 80 + i));
    [intros Hp; exact (KPRES _ Hi1 Ho1 He1 Hp) | exact Hwle | exact (MwH i Hi)].
  - replace (HA + 80 + 8) with (HA + 88) by lia. exact MnF.
  - intros k Hk. rewrite HV. exact (KMOV k Hk).
  - intros a Ha.
    apply (KBLK (hl_v H1) (AREC * hl_cap H1) a HvinH).
    + rewrite HreqV. unfold hl_n in *. unfold AREC in *. lia.
    + apply (KOFF (hl_v H1) (AREC * hl_cap H1) a HvinH VNE). rewrite HreqV. unfold hl_n in *. unfold AREC in *. lia.
    + rewrite <- HV. unfold hl_n in *. unfold AREC in *. lia.
  - intros r' Hr' a Ha.
    destruct (nth_split (hl_recs H1) (0, []) (proj2 HLR : (m < length (hl_recs H1))%nat)) as (A & Bs & Hsp & HlA).
    rewrite ENTH in Hsp.
    unfold ldrop_list in Hr'. cbn [HarnessRep.hl_recs] in Hr'. rewrite Hsp, <- HlA, l2_drop_split in Hr'.
    assert (Hin' : In r' (hl_recs H1)).
    { rewrite Hsp. apply in_app_or in Hr' as [Hx | Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
    assert (Hne1 : fst r' <> fst r).
    { intros Heq. pose proof HNDvH as ND1. apply NoDup_ListNoDup in ND1. rewrite Hsp, map_app in ND1. cbn [map] in ND1.
      apply List.NoDup_remove_2 in ND1. apply ND1. rewrite <- Heq, <- map_app. apply in_map. exact Hr'. }
    assert (Hne2 : fst r' <> hl_v H1) by (intros Heq; apply HninH; rewrite <- Heq; apply in_map; exact Hin').
    destruct (HFallH' r' Hin') as (HrB' & _).
    exact (proj1 (KBK (fst r') (Z.of_nat (length (snd r')) + 1) a HrB' Hne1 Hne2 ltac:(rewrite (HreqT r'); lia))). }
(* the other lists of the source and their blocks *)
apply NoDup_ListNoDup in HNDS. unfold hs_blocks in HNDS.
cbn [CheckRep.set_held hs_pending hs_partial hs_expected hs_held] in HNDS.
assert (NDX : forall b, In b (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
  b <> fst r /\ b <> hl_v H1).
{ intros b Hb.
  assert (HN2 : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks H1))
    by (rewrite <- !app_assoc; exact HNDS).
  split.
  - apply (l2_nodup_disj _ _ b (fst r) HN2 Hb). unfold list_blocks. apply in_or_app. right. apply in_map. exact HRIN.
  - apply (l2_nodup_disj _ _ b (hl_v H1) HN2 Hb). unfold list_blocks. apply in_or_app. left. rewrite Ecap. left. reflexivity. }
assert (HreqP : req_size APARTIAL = APARTIAL)
  by (unfold req_size, APARTIAL; destruct (6000 =? 0) eqn:Ez; [discriminate | reflexivity]).
assert (SFP : akept W1 mem1 W2 mem2
  (gfp (hs_partial (CheckRep.set_held h H1)) (bzs (hs_pjunk (CheckRep.set_held h H1))) ::
   alist_fp (HA + 16) (hs_pending (CheckRep.set_held h H1)) ++ alist_fp (HA + 64) (hs_expected (CheckRep.set_held h H1)))).
{ cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected].
  intros rr Hrr a Ha. cbn [In] in Hrr. destruct Hrr as [<- | Hrr].
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, HPJLEN in Ha.
    destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (Hp1 & Hp2).
    exact (KBK (hs_partial h) APARTIAL a HPIN Hp1 Hp2 ltac:(rewrite HreqP; unfold APARTIAL in *; lia)).
  - apply in_app_or in Hrr as [Hrr | Hrr]; revert rr Hrr a Ha.
    + apply (l2_list_kept_P ly1 S1 [] W1 mem1 md1 W2 mem2 (HA + 16) (hs_pending h) _
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HPD).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. exact (NDX b ltac:(apply in_or_app; left; exact Hb)).
    + apply (l2_list_kept_P ly1 S1 [] W1 mem1 md1 W2 mem2 (HA + 64) (hs_expected h) _
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HED).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. exact (NDX b ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb)). }
assert (SBLK : forall b, In b ((hs_partial (CheckRep.set_held h H1), APARTIAL) ::
  alist_blks (hs_pending (CheckRep.set_held h H1)) ++ alist_blks (hs_expected (CheckRep.set_held h H1))) ->
  In b (ablocks B ly2 S2)).
{ cbn [CheckRep.set_held hs_pending hs_partial hs_expected].
  intros b Hb. destruct Hb as [<- | Hb].
  - destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (Hp1 & _).
    exact (BLK2 (hs_partial h) APARTIAL HPIN ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))).
  - apply in_app_or in Hb as [Hb | Hb]; destruct b as [p n].
    + pose proof (l2_alist_blks_in ly1 S1 W1 mem1 (HA + 16) (hs_pending h) _ HPD (p, n) Hb) as Hin1.
      destruct (NDX p ltac:(apply in_or_app; left; exact (l2_alist_blks_fst _ (p, n) Hb))) as (Hp1 & _).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))).
    + pose proof (l2_alist_blks_in ly1 S1 W1 mem1 (HA + 64) (hs_expected h) _ HED (p, n) Hb) as Hin1.
      destruct (NDX p ltac:(apply in_or_app; right; apply in_or_app; right; exact (l2_alist_blks_fst _ (p, n) Hb)))
        as (Hp1 & _).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))). }
pose proof (l2_nodup_hs_drop (CheckRep.set_held h H1) m ltac:(cbn [CheckRep.set_held hs_held]; lia)
  ltac:(cbn [CheckRep.set_held hs_held]; lia) HNDS0) as NDnew.
pose proof (l2_src_swap ly1 S1 W1 mem1 ly2 S2 W2 mem2 HA (CheckRep.set_held h H1) (ldrop_list H1 m) HSRC
  ltac:(intros a Ha; apply KHD; lia) SFP SBLK HE2 NDnew) as SRC2.
rewrite l2_set_held2 in SRC2.
(* the invariant with m records to examine *)
split; [exact HJ2|]. split; [exact SRC2|].
split; [unfold ldrop_list; cbn [HarnessRep.hl_v]; exact HV|].
split; [unfold ldrop_list; cbn [HarnessRep.hl_cap]; exact HC|].
split; [rewrite (l2_ldrop_recs H1 _ _ m Hle HREC), (l2_kp_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT); reflexivity|].
split.
{ intros rest Hp. rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT) in Hp. fold r in Hp.
  unfold cshe_ds_blks in Hp, HPERM. cbn [map] in Hp.
  pose proof (HPERM ((fst r, Z.of_nat (length (snd r)) + 1) :: rest)
    ltac:(eapply Permutation_trans; [exact Hp | apply Permutation_middle])) as HP1.
  destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb1 in HP1. rewrite Eb2.
  apply (Permutation_cons_inv (a := (fst r, Z.of_nat (length (snd r)) + 1))).
  eapply Permutation_trans; [apply Permutation_middle | exact HP1]. }
split; [rewrite Hfrs2; exact HFRS|].
split.
{ apply (mle_weaken MT S S2 _ _ ML (mle_station MT S S1 S2 _ _ ML HMLE Hle2)).
  rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT). cbn [length]. rewrite Nat2Z.inj_succ, Z.mul_succ_l. lia. }
split.
{ apply (mok_station MT S1 S2 (Z.of_nat (Datatypes.S m) * mo_free MT) (mo_free MT) (Z.of_nat m * mo_free MT) ML HMOK Hle2).
  - apply Z.mul_nonneg_nonneg; lia.
  - rewrite Nat2Z.inj_succ, Z.mul_succ_l. lia. }
split; [exact ROMF|].
split; [apply (l2_saved_kept W1 W2 mem1 mem2 sp0 regs0); [intros a Ha; apply KHI; rewrite WS in *; lia | exact HSAV]|].
split; [apply (l2_vm_keep W1 W2 mem1 mem2); [intros x Hx; cbn in Hx; apply KHI; rewrite WS in *; lia | exact M16]|].
split; [apply (l2_vm_keep W1 W2 mem1 mem2); [intros x Hx; cbn in Hx; apply KHI; rewrite WS in *; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W2 mem1 mem2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
  assert (Hg : inG cshe_ro x).
  { unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1). split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. lia. }
  destruct (HGR x Hg) as (Hi & Ho & _). pose proof (proj1 (HGRR x Hg)) as He.
  apply (KIMG x Hi Ho He). intros Hc. destruct (l2_HAimg x ltac:(unfold ASRC; lia)) as (_ & _ & _ & _ & Hng). lia. }
split; [intros q Hq; rewrite (KERR q Hq); exact (MERR q Hq)|].
split; [exact HRMd|].
(* the free dropped one block: the live counts only fell *)
destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in MCNT. exact (l2_cnt_del RP l1 _ l2 MCNT).
Qed.

(* a run whose regions' one write window is l->n, [HA + 88, HA + 92): every byte off it is kept; U18 is the env's
   value of atom 18 (HA + 80) *)
Ltac l2_wkeep Hf U18 :=
lazymatch type of Hf with frame_of ?Ev ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) =>
  apply (aview_kept_out Ev rs H m0 m1 Hf); [lia|];
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros (rg & Hin & Hrg);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?U18 in Hrg; lia|]);
  destruct Hin
end.

(* l2_wkeep on the run's frame from m0 to m1 *)
Ltac l2_wkeep_m m0 m1 U18 :=
lazymatch goal with Hf : frame_of _ _ (mrestrict _ m0) (mrestrict _ m1) |- _ => l2_wkeep Hf U18 end.
(* a register two calls and the runs around them did not change *)
Ltac l2_keepreg3 HS0 HS r OLDa OLDb :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq;
repeat (rewrite OLDb in Bq by lia); repeat (rewrite OLDa in Bq by lia); rewrite Bq, <- A; clear A Bq.

(* ---- 0x8550c .. 0x85564: v[i] has the prefix.  The shadow check of v[i], free(v[i].s), the shadow checks of l->v
   and l->n (l->n's shadow byte is zero, so the partial-granule check 0x8556c is not reached),
   __asan_memmove(&v[i], &v[i + 1], 16 (n - i - 1)), l->n = n - 1, the counters and bltu ---- *)
Lemma l2_C : forall m W1 regs1 mem1 md1, l2_hit m W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_inv m W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (l2_pc m)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2h)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros m W1 regs1 mem1 md1 (Hle & HPT & ly1 & S1 & kk & H1 & HM & HR & R19 & R24) Kloop.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof (l2_ar HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (unfold AREC in Vceil; lia).
set (r := nth m (hl_recs (hs_held h)) (0, [])) in *.
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
pose proof HFallH as HFallH'. rewrite Forall_forall in HFallH'. destruct (HFallH' r HRIN) as (HrB & HrG & HrL & _).
destruct (HrL eq_refl) as (HrNZ & HrLEN). unfold APARTIAL in HrLEN.
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
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
assert (HRimg : HA + 96 <= RA \/ RA + 16 <= HA + 80).
{ pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as Hoff. rewrite HreqV in Hoff.
  pose proof (pa_img_range HA (proj1 (l2_HAimg HA ltac:(unfold ASRC; lia)))) as HI1.
  pose proof (pa_img_range (HA + 95) (proj1 (l2_HAimg (HA + 95) ltac:(unfold ASRC; lia)))) as HI2.
  unfold off_img in Hoff. destruct Hoff; [right | left]; lia. }
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR1 HvinH
  ltac:(lia) ltac:(rewrite HreqV; lia)) as HRAR.
pose proof alloc_ceiling_val as ACV.
assert (HXO0 : 0 <= XO) by (pose proof HJ as (_ & HX & _); exact HX).
assert (HAWn : awr W1 mem1 (HA + 88) 4)
  by (intros i Hi; replace (HA + 88 + i) with (HA + 80 + (8 + i)) by lia; apply MwH; lia).
destruct (l2c_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) RA (fst r) (Z.of_nat (length (snd r)))
  R2 R8 R18 R19 R24 R25 R26 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1 ltac:(lia) ltac:(lia) HRimg HRapp
  ltac:(unfold AREC, CSHE_STK, CSHE_FRAME, ASTACK in *; lia) ltac:(lia) ltac:(lia)
  M16 MvH ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH) HAWn Ms0 Ml0
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia]) HRAR) as [HS SHOK].
clear HRimg.
remember (Eimg (Ereg regs1 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j0, (j0 < 4)%nat -> ew E (32 + j0) =
  nth j0 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))) (Z_to_bv 64 0)).
{ intros j0 Hj0. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (fst r)) by exact (EX 2%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (EEo 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite (EEo 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18).
pose proof HS as HS0.
pose proof (pal_free B TL) as HBfree.
pose proof HG as HGok.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
(* ---- 0x8550c .. 0x85518: the shadow check of v[i], a0 = v[i].s, jal free ---- *)
paj_run_tok_x RUNx HS HJ SHOK Bspan.
{ cbv [ss_mem ss_l2c l2_fr l2_hdw l2_rec].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite HBfree.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HAR1m : ARx ly1 S1 [] W1 (ms_mem ms) mdc) by (eapply ajournal_gx_AR_x; exact HJ).
assert (Usp2 : spZ (ms_regs ms) = sp0 + -144)
  by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite Q2, Usp; lia).
assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a) by (intros a Ha Hno; l2_wkeep HFr U18).
(* ---- free(v[i].s), returning to 0x8551c ---- *)
eapply SRr_bind.
{ apply (l2_free_gx XO [(AT, AT + 8)] W1 (ms_regs ms) (ms_mem ms) CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] _ kk
    (fst r) (Z.of_nat (length (snd r)) + 1) (-144) (getr (ms_regs ms) 1) [] (m + kr) HJ HX16 HrB).
  - rewrite Q10, E34. reflexivity.
  - exact Usp2.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ASTACK. lia.
  - rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly1 _ (spZ (ms_regs ms)) (HA + 88) [] (ms_regs ms)).
    + apply achain_low. lia.
    + rewrite Usp2. lia.
    + unfold s0Z. rewrite Q8, U18, unsigned_lit_small by lia. lia.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_check_shape_ends + 0x16c); [exact HCTX_cshe_l2|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_check_shape_ends in *; lia].
  - (* the free's room: S m + kr = 1 + (m + kr) by conversion *)
    exact MRM.
  - exact MCNT.
  - intros _ i Hi. exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; lia].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r, Z.of_nat (length (snd r)) + 1)).
    unfold list_blks. apply in_or_app. right.
    apply (in_map (fun rr => (fst rr, Z.of_nat (length (snd rr)) + 1))). unfold r. apply nth_In. lia.
  - pose proof (mo_free_nonneg MT ML) as Hf.
    apply (mok_station MT S1 S1 (Z.of_nat (Datatypes.S m) * mo_free MT) 0 (mo_free MT) ML HMOK (mle_start MT S1 ML));
    [lia | rewrite Nat2Z.inj_succ; nia]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs2 & HK & Hle2 & HRM2 & Herr2 & Hpres2).
pose proof (l2_hp0 HJ2) as Ehp2. subst hp2.
assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
assert (GH : forall a, HA <= a < HA + 96 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (l2_HAimg a ltac:(unfold ASRC; lia)) as (Hi & Ho & He & _). split; [exact Hi|]. split; [exact Ho | exact He]. }
assert (IMGK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a /\
  (apresent (w_H W1) (ms_mem ms) a -> apresent (w_H W2) mem2 a)).
{ intros a Hi Ho He. split; [exact (proj1 (proj2 (proj2 HK)) a Hi Ho He)|].
  apply (Hpres2 a Hi).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly1 S1 [] W1 (ms_mem ms) _ a HAR1m Hi) Hw)).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 [] W2 mem2 md2 a HAR2 Hi) Hw)).
  - exact He.
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 (ms_mem ms) _ (fst r) _ a HAR1m HrB Hr Hi). }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK); lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GH a ltac:(lia)) as (Hi & Ho & He). exact (proj1 (IMGK a Hi Ho He)).
  - intros a Ha Hw. destruct (GH a ltac:(lia)) as (Hi & Ho & He).
    apply (l2_writable_kept_w W1 W2 (ms_mem ms) mem2 a); [exact (proj2 (IMGK a Hi Ho He)) | exact Hwle2 | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
clear HEa.
assert (F18 : ew Ea 18 = Z_to_bv 64 (HA + 80)) by (rewrite OLDa by lia; rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (F25 : ew Ea 25 = Z_to_bv 64 SB) by (rewrite OLDa by lia; rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18a).
assert (SHOK2 : sh_ok SEGS Bx1 l2_SHa Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, l2_SHa. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 [] W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80) F18) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x8551c .. 0x85548: the shadow checks of l->v and l->n, a0 = &v[i], a1 = &v[i + 1], a2 = 16 (n - i - 1) ---- *)
rewrite Q1.
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (EAS : ESTACK = 4096 /\ ASTACK = 16384) by (split; reflexivity).
pose proof (l2_ar HJ2)
  as HAR3.
assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a) by (intros a Ha Hno; l2_wkeep_m mem2 (ms_mem ms0) U18a).
(* the vector is still live after the free (it is not v[m].s's block) *)
assert (VNE : hl_v H1 <> fst r) by (intros Heq; apply HninH; rewrite Heq; apply in_map; exact HRIN).
assert (Hvin2 : In (hl_v H1, AREC * hl_cap H1) (ablocks B ly2 S2)).
{ pose proof Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. pose proof HvinH as Hv1. rewrite Eb1 in Hv1.
  apply in_app_or in Hv1 as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. exact (VNE (eq_sym Ex)). }
destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 (ms_mem ms0) _ _ _ HAR3 Hvin2) as (_ & _ & _ & _ & Vpres & _).
rewrite HreqV in Vpres.
set (CNT := AREC * (hl_n H1 - 1 - Z.of_nat m)).
assert (HCNTk : CNT = 16 * (hl_n H1 - 1 - Z.of_nat m)) by reflexivity.
assert (HCNT : 0 <= CNT /\ RA + 16 + CNT <= hl_v H1 + AREC * hl_cap H1).
{ rewrite HCNTk. unfold RA, AREC. rewrite <- HV. unfold hl_n in *. split; lia. }
assert (Uspa : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (Uspm : spZ (ms_regs ms0) = sp0 + -144)
  by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite P2, Uspa; lia).
assert (R10 : getr (ms_regs ms0) 10 = w64 RA).
{ rewrite P10, (OLDa 23%nat), (OLDa 32%nat) by lia. rewrite (EEo 23%nat 23%bv eq_refl), R23, E32, HV. unfold w64, RA.
  rewrite YI08.alu64_add_lit. f_equal. unfold AREC. lia. }
assert (R11 : getr (ms_regs ms0) 11 = w64 (RA + 16)).
{ rewrite P11, (OLDa 23%nat), (OLDa 32%nat) by lia. rewrite (EEo 23%nat 23%bv eq_refl), R23, E32, HV. unfold w64, RA.
  rewrite unsigned_lit_small by (unfold AREC, hl_n in *; lia). rewrite YI08.alu64_add_lit. f_equal. unfold AREC. lia. }
assert (R12 : getr (ms_regs ms0) 12 = w64 CNT).
{ rewrite P12, (OLDa 21%nat), (OLDa 33%nat) by lia. rewrite (EEo 21%nat 21%bv eq_refl), R21, E33. unfold w64.
  rewrite (l2_count_eq (Z.of_nat (Datatypes.S m)) (hl_n H1)) by (unfold hl_n in *; lia). rewrite HCNTk. f_equal. lia. }
assert (Ecap : (hl_cap (hs_held h) =? 0) = false) by (apply Z.eqb_neq; rewrite <- HC; lia).
assert (HvFP : forall a, hl_v H1 <= a < hl_v H1 + AREC * hl_cap H1 -> inFP FPc a).
{ intros a Ha. exists (hl_v (hs_held h), hl_v (hs_held h) + req_size (AREC * hl_cap (hs_held h))).
  split; [|cbn [fst snd]; rewrite <- HV, <- HC, HreqV; lia].
  unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v (hs_held h), AREC * hl_cap (hs_held h))).
  unfold list_blks. apply in_or_app. left. rewrite Ecap. left. reflexivity. }
(* rom_view at the memmove: the runs wrote only l->n (no rom byte of g_s), the free keeps a rom byte either because the
   runtime owns it and it is pinned, or because it is an image byte it did not touch (W_journal.v acall_kept_rom_view) *)
assert (ROMIMG : forall a, in_rom SEGS a -> in_img SEGS a)
  by (intros a (sg & Hsg & _ & Hra); exists sg; split; assumption).
assert (ROMW : forall a, in_rom SEGS a -> ~ (HA + 88 <= a < HA + 92)).
{ intros a Hr Hc. destruct (l2_HAimg a ltac:(unfold ASRC; lia)) as (_ & _ & _ & Hnr & _). exact (Hnr Hr). }
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)). rewrite (KEEPa a ltac:(lia) (ROMW a Hrom)). exact (HROM a Hrom). }
assert (ROM2 : rom_view SEGS W2 mem2) by (eapply (acall_kept_rom_view_x SEGS B ARx LAWS); [exact HAR2 | exact HK | exact ROMNS | exact ROM1]).
assert (ROMK : rom_view SEGS W2 (ms_mem ms0)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)). rewrite (KEEPb a ltac:(lia) (ROMW a Hrom)). exact (ROM2 a Hrom). }
(* ---- __asan_memmove(&v[m], &v[m + 1], 16 (n - m - 1)), 0x85548 ---- *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS G XO [(AT, AT + 8)] ESTACK (SIGMA WS_asan_memmove)
  (fun a => RA <= a < RA + CNT) _
  W2 (ms_regs ms0) (ms_mem ms0) CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 [] _ (kk + 1)
  (-144) (getr (ms_regs ms0) 1) HGok HX16 HJ2).
- exact Uspm.
- reflexivity.
- lia.
- lia.
- rewrite WS. lia.
- rewrite P3, (OLDa 3%nat) by lia. rewrite (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
- rewrite P4, (OLDa 4%nat) by lia. rewrite (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
- reflexivity.
- rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a. destruct (Z_le_gt_dec RA a) as [Hd1|Hd1]; [|right; lia].
  destruct (Z_lt_ge_dec a (RA + CNT)) as [Hd2|Hd2]; [left; lia | right; lia].
- intros a Ha HGb. cbv beta in Ha. exfalso.
  apply (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; lia | exact (proj1 (HGok a HGb))].
- intros a Ha HnG. cbv beta in Ha. split; [|rewrite WS in *; lia].
  right. left. split; [apply HvFP; lia|].
  exists (hl_v H1), (AREC * hl_cap H1). split; [exact Hvin2 | rewrite HreqV; lia].
- intros HPRE2 HSC.
  (* the destination is a heap block, so no byte of it is an image byte (W_list_drop.v:961-963 on a working branch) *)
  assert (MNIMG : forall a, RA <= a < RA + CNT -> ~ in_img SEGS a).
  { intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2).
    rewrite HreqV. lia. }
  apply (AMOVE ly2 S2 [] W2 (ms_regs ms0) (ms_mem ms0) _ RA (RA + 16) CNT HPRE2 R10 R11 R12).
  + rewrite HCNTk. unfold hl_n in *. lia.
  + lia.
  + lia.
  + intros a Ha. split; [|split].
    * apply (apresent_writable SEGS). exact (proj1 (Vpres a ltac:(lia))).
    * exact (proj2 (Vpres a ltac:(lia))).
    * rewrite Uspm. rewrite WS in *. lia.
  + apply l2_amem_of_app. apply (in_app_sub (hl_v H1) (AREC * hl_cap H1)); [exact Vapp | lia | lia | lia].
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia | exact Hpos].
  + lia.
  + lia.
  + intros a Ha. split.
    * destruct (proj1 (Vpres a ltac:(lia))) as [Hh [b Hb]].
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
    * rewrite Uspm. rewrite WS in *. lia.
  + apply l2_amem_of_app. apply (in_app_sub (hl_v H1) (AREC * hl_cap H1)); [exact Vapp | lia | lia | lia].
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia | exact Hpos].
  + exact ROMK.
  + intros Hpos. split; apply l2_amem_of_app; apply (in_app_sub (hl_v H1) (AREC * hl_cap H1));
    first [exact Vapp | lia].
  + exact MNIMG. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hres3 & Hmov) & Hfr3 & Hpres3).
pose proof (l2_ar HJ3) as HAR4.
assert (MOFF : forall a, in_img SEGS a -> ~ (RA <= a < RA + CNT)).
{ intros a Hi Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; lia | exact Hi]. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Uspa, ?U18a).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; [lia | cbv beta; lia | rewrite WS in *; lia].
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GH a ltac:(lia)) as (Hi & _ & _). pose proof (pa_img_range a Hi).
    apply Hfr3; [lia | exact (MOFF a Hi) | rewrite WS in *; lia].
  - intros a Ha Hw. apply (l2_writable_kept_w W2 W2 (ms_mem ms0) mem3 a); [intros Hp; exact (Hpres3 a Hp) | apply wle_refl | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m0, (m0 < 52)%nat -> ew Eb m0 = ew Ea m0) by (intros m0 Hm0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm0).
clear HEb.
assert (K18 : ew Eb 18 = Z_to_bv 64 (HA + 80)) by (rewrite OLDb by lia; exact F18).
assert (K25 : ew Eb 25 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact F25).
assert (K33 : ew Eb 33 = Z_to_bv 64 (hl_n H1)) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E33).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
assert (SHOK3 : sh_ok SEGS Bx1 l2_SHa Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, l2_SHa. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 [] W2 mem3 md3 (HA + 64) 32 HAR4 Hzs).
  - unfold Bx1. rewrite (U_atom Eb 25 SB K25) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Eb 18 (HA + 80) K18) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x8554c .. 0x85558: l->n = n - 1 ---- *)
rewrite P1.
paj_run_to_tok_x RUNTOx HS HJ3 SHOK3 Bspan A_cshe_l2t.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdF := mdq) in * end.
assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem3 a) by (intros a Ha Hno; l2_wkeep_m mem3 (ms_mem ms1) U18b).
(* l->n after the store *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok _ ltac:(cbn [ss_mem]; right; left; reflexivity)) as (_ & _ & _ & Hchs).
pose proof (proj1 (Forall_forall _ _) Hchs (YP09.mkChunk 8 (CVal 4%N (SOff 33 (-1))))
  ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch8.
assert (MnF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 88) 4 (hl_n H1 - 1)).
{ replace (HA + 88) with (base_val Eb (Some 18%nat) + 8) by (rewrite V18b; lia).
  apply (l2_val_mem_of_chunk4 Eb _ _ 8 (SOff 33 (-1)) (hl_n H1 - 1) Hch8); [|lia].
  rewrite (U_atom_off Eb 33 (hl_n H1) (-1) K33) by lia. lia. }
(* ---- what the free, the memmove and the three runs kept, from (W1, mem1) to (W2, ms_mem ms1) ---- *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 88 <= a < HA + 92) -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hi Ho He Hw. pose proof (pa_img_range a Hi) as Har.
  rewrite (KEEPc a ltac:(lia) Hw).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; exact (MOFF a Hi)) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb a ltac:(lia) Hw).
  rewrite (proj1 (proj2 (proj2 HK)) a Hi Ho He).
  exact (KEEPa a ltac:(lia) Hw). }
assert (KPRES : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) (ms_mem ms1) a).
{ intros a Hi Ho He Hp.
  assert (Q1p : apresent (w_H W1) (ms_mem ms) a) by l2_pres_back Hp.
  pose proof (proj2 (IMGK a Hi Ho He) Q1p) as Q2p.
  assert (Q3p : apresent (w_H W2) (ms_mem ms0) a) by l2_pres_back Q2p.
  pose proof (Hpres3 a Q3p) as Q4p.
  l2_pres_back Q4p. }
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 144 - ASTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hs. assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by lia.
  rewrite (KEEPc a ltac:(lia) Hnw).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; lia) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb a ltac:(lia) Hnw).
  rewrite (proj1 HK a Ha ltac:(lia)).
  exact (KEEPa a ltac:(lia) Hnw). }
assert (KBLK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + Z.of_nat (length (snd r)) + 1) -> ~ (RA <= a < RA + CNT) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros p n a Hin Ha Hnr Hnm.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 Hin) as (_ & Hp4096 & Hpc & _).
  assert (Hni : ~ in_img SEGS a) by exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 p n a HAR1 Hin Ha).
  assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by (intros Hc; apply Hni; exact (proj1 (GH a ltac:(lia)))).
  rewrite (KEEPc a ltac:(lia) Hnw).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; exact Hnm) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb a ltac:(lia) Hnw).
  replace a with (p + (a - p)) by lia.
  rewrite (proj1 (proj2 HK) p n (a - p) Hin ltac:(lia) ltac:(cbv beta; rewrite HreqR; lia)).
  replace (p + (a - p)) with a by lia.
  exact (KEEPa a ltac:(lia) Hnw). }
assert (KMOV : forall k, 0 <= k < CNT -> aview SEGS (w_H W2) (ms_mem ms1) (RA + k) = aview SEGS (w_H W1) mem1 (RA + AREC + k)).
{ intros k Hk.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) (fst r)
    (Z.of_nat (length (snd r)) + 1) HAR1 HvinH HrB
    ltac:(intros Heq; injection Heq as Heq _; exact (VNE Heq))) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite HreqV, HreqR in DJ.
  assert (Hni1 : ~ in_img SEGS (RA + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hni2 : ~ in_img SEGS (RA + 16 + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hnw1 : ~ (HA + 88 <= RA + k < HA + 92)) by (intros Hc; apply Hni1; exact (proj1 (GH (RA + k) ltac:(lia)))).
  assert (Hnw2 : ~ (HA + 88 <= RA + 16 + k < HA + 92)) by (intros Hc; apply Hni2; exact (proj1 (GH (RA + 16 + k) ltac:(lia)))).
  rewrite (KEEPc (RA + k) ltac:(lia) Hnw1).
  rewrite (Hmov k Hk).
  rewrite (KEEPb (RA + 16 + k) ltac:(lia) Hnw2).
  replace (RA + 16 + k) with (hl_v H1 + (RA + 16 + k - hl_v H1)) by lia.
  rewrite (proj1 (proj2 HK) (hl_v H1) (AREC * hl_cap H1) (RA + 16 + k - hl_v H1) HvinH
    ltac:(rewrite HreqV; lia) ltac:(cbv beta; rewrite HreqR; lia)).
  replace (hl_v H1 + (RA + 16 + k - hl_v H1)) with (RA + AREC + k) by (unfold AREC; lia).
  exact (KEEPa (RA + AREC + k) ltac:(unfold AREC; lia) ltac:(unfold AREC; exact Hnw2)). }
assert (ROMF : rom_view SEGS W2 (ms_mem ms1)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  rewrite (KEEPc a ltac:(lia) (ROMW a Hrom)).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; exact (MOFF a Hi)) ltac:(rewrite WS in *; lia)).
  exact (ROMK a Hrom). }
(* errno's four bytes: the runs write only l->n (a byte of g_s, not errno), the memmove only its heap destination,
   and the free keeps errno's view *)
assert (KERR : forall j, 0 <= j < 4 ->
  aview SEGS (w_H W2) (ms_mem ms1) (as_errno B + j) = aview SEGS (w_H W1) mem1 (as_errno B + j)).
{ intros q Hq. pose proof (l2_errno_img q Hq) as Hi. pose proof (pa_img_range _ Hi) as Har.
  assert (Hw : ~ (HA + 88 <= as_errno B + q < HA + 92))
    by (intros Hc; apply (l2_errno_off q Hq); unfold ASRC; lia).
  rewrite (KEEPc (as_errno B + q) ltac:(lia) Hw).
  rewrite (Hfr3 (as_errno B + q) ltac:(lia) ltac:(cbv beta; exact (MOFF _ Hi)) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb (as_errno B + q) ltac:(lia) Hw).
  rewrite (Herr2 q Hq).
  exact (KEEPa (as_errno B + q) ltac:(lia) Hw). }
pose proof (l2_mem_drop m ly1 S1 kk H1 W1 mem1 md1 ly2 S2 W2 (ms_mem ms1) mdF Hle HPT HM HJ3 Hwle2 Hbl Hfrs2 Hle2
  ROMF MnF KIMG KPRES KHI KBLK KMOV KERR HRM2) as MEMF.
assert (REGSF : l2_regs (ms_regs ms1) (Datatypes.S m)).
{ unfold l2_regs.
  split; [l2_keepreg3 HS0 HS (2%bv : bv 5) OLDa OLDb; exact R2|].
  split; [l2_keepreg3 HS0 HS (3%bv : bv 5) OLDa OLDb; exact R3|].
  split; [l2_keepreg3 HS0 HS (4%bv : bv 5) OLDa OLDb; exact R4|].
  split; [l2_keepreg3 HS0 HS (8%bv : bv 5) OLDa OLDb; exact R8|].
  split; [l2_keepreg3 HS0 HS (9%bv : bv 5) OLDa OLDb; exact R9|].
  split; [l2_keepreg3 HS0 HS (18%bv : bv 5) OLDa OLDb; exact R18|].
  split; [l2_keepreg3 HS0 HS (20%bv : bv 5) OLDa OLDb; exact R20|].
  split; [l2_keepreg3 HS0 HS (21%bv : bv 5) OLDa OLDb; exact R21|].
  split; [l2_keepreg3 HS0 HS (22%bv : bv 5) OLDa OLDb; exact R22|].
  split; [l2_keepreg3 HS0 HS (23%bv : bv 5) OLDa OLDb; exact R23|].
  split; [l2_keepreg3 HS0 HS (25%bv : bv 5) OLDa OLDb; exact R25|].
  split; [l2_keepreg3 HS0 HS (26%bv : bv 5) OLDa OLDb; exact R26|].
  l2_keepreg3 HS0 HS (27%bv : bv 5) OLDa OLDb; exact R27. }
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  replace (BASE + k) with (BASE + A_cshe_l2t) by (unfold A_cshe_l2t, AF_fr_check_shape_ends; lia) end.
exact (l2_D m ly2 S2 (kk + 1) (ldrop_list H1 m) W2 (ms_regs ms1) (ms_mem ms1) mdF Hle MEMF REGSF Kloop).
Qed.

(* ---- 0x85690: the epilogue, from the invariant with no record left to cshe_post_x's g_gone <> 0 case ---- *)
Lemma l2_epi : forall W1 regs1 mem1 md1, l2_inv 0 W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_ret)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros W1 regs1 mem1 md1 (_ & ly1 & S1 & kk & H1 & HM & HR).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
pose proof HR as (R2 & R3 & R4 & _).
pose proof (l2_ar HJ) as HAR1.
assert (WS : CSHE_STK = 16528) by reflexivity.
change (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_ret)) mem1 (seg_rom SEGS)) md1)
  with (cfg_at SEGS (BASE + A_cshe_ret) regs1 mem1 md1).
apply (cshe_epi_x B PST ARx G LAWS HG W ly S hp mem md XO [(AT, AT + 8)] FPc ly1 S1 [] W1 regs0 regs1 mem1 md1 kk Post HJ);
  [exact Hra0 | exact Hal16 | rewrite WS in *; lia | lia | exact R2 | exact R3 | exact R4 | exact HSAV |].
intros regs' mem' md' HPRES HMEQ HPR HJ'.
unfold cshe_post_x.
exists ly1, S1, [], regs', mem', md', kk, H1, (filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h))), 0.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPRES|].
split.
{ intros q Hq. pose proof (pa_img_range _ (l2_errno_img q Hq)) as HeR.
  rewrite (HMEQ (as_errno B + q)) by lia. exact (MERR q Hq). }
split.
{ apply (l2_src_step ly1 S1 [] md1 W1 W1 mem1 mem' HA _ sp0 sp0 HAR1 HSRC); [| rewrite WS in *; lia | | exact HPR | apply wle_refl].
  - intros a Ha. exact (proj1 (l2_HAimg a Ha)).
  - intros a Ha _. exact (HMEQ a Ha). }
split; [exact HV|]. split; [exact HC|].
assert (HR0 : hl_recs H1 = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs (hs_held h)))
  by (rewrite HREC; reflexivity).
split.
{ unfold CheckRep.texts. rewrite HR0. apply NoDup_ListNoDup. apply l2_nodup_filter.
  apply NoDup_ListNoDup. exact HND0. }
split; [left; split; [exact Hgone|]; split; [exact HR0|]; split; reflexivity|].
split; [lia|].
split; [rewrite Z.add_0_r; apply (l2_vm_keep W1 W1 mem1 mem'); [intros x Hx; apply HMEQ; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W1 mem1 mem'); [|exact MG]. intros x Hx.
  pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR. apply HMEQ. lia. }
split; [exact HPERM|]. split; [exact HFRS|].
split; [|exact MRM].
apply (mle_weaken MT S S1 _ _ ML HMLE). unfold cshe_cost, hl_n.
apply Z.mul_le_mono_nonneg_r; [exact (mo_free_nonneg MT ML)|]. apply Nat2Z.inj_le.
exact (l2_filter_len (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h))).
Qed.

(* the loop: from the head with m records not yet examined, by induction on m *)
Lemma l2_loop : forall m W1 regs1 mem1 md1, l2_inv m W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (l2_pc m)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction m as [|m IH]; intros W1 regs1 mem1 md1 HI.
- exact (l2_epi W1 regs1 mem1 md1 HI).
- cbn [l2_pc]. apply (l2_A m W1 regs1 mem1 md1 HI). intros W2 regs2 mem2 md2 HM.
  apply (l2_B m W2 regs2 mem2 md2 HM).
  + intros W3 regs3 mem3 md3 HI3. exact (IH W3 regs3 mem3 md3 HI3).
  + intros W3 regs3 mem3 md3 HH. apply (l2_C m W3 regs3 mem3 md3 HH).
    intros W4 regs4 mem4 md4 HI4. exact (IH W4 regs4 mem4 md4 HI4).
Qed.

Lemma l2_set_held_id : forall h0, CheckRep.set_held h0 (hs_held h0) = h0.
Proof. intros []. reflexivity. Qed.

(* Loop 2 in full: from the state cshe_gone_l2_x leaves at the head 0x854c4 (the registers it names, and the frame,
   the journal, the source and the cells of the entry as loop 1 and the g_gone test left them) to cshe_post_x's
   g_gone <> 0 disjunct, through the epilogue cshe_epi_x.  The journal's ghost list at the head is any hp1 (HP0 makes
   it []). *)
Lemma cshe_l2_run_x : forall W1 hp1 regs1 mem1 md1 kk,
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly S hp1 W1 mem1 md1 kk ->
asrc_at B ly S W1 mem1 HA h -> rom_view SEGS W1 mem1 -> cshe_saved W1 mem1 sp0 regs0 ->
val_mem SEGS (arm W1 mem1) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W1 mem1) AT 8 A0 -> val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
0 < hl_n (hs_held h) ->
getr regs1 2 = w64 (sp0 - 144) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = w64 (HA + 88) -> getr regs1 9 = w64 PF -> getr regs1 18 = w64 (HA + 80) ->
getr regs1 20 = w64 (hl_n (hs_held h) + 1) -> getr regs1 21 = w64 (- hl_n (hs_held h)) -> getr regs1 22 = w64 1 ->
getr regs1 23 = w64 (AREC * (hl_n (hs_held h) - 1)) -> getr regs1 25 = w64 SB ->
getr regs1 26 = w64 ((HA + 80) / 8 + SB) -> getr regs1 27 = w64 3 ->
(* the room round: one free per held record past the caller's kr, and the live counts at the loop's head *)
rp_RM RP S (length (hl_recs (hs_held h)) + kr) -> cnt_ok RP (ablocks B ly S) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros W1 hp1 regs1 mem1 md1 kk HJ HSRC HROM HSAV M16 MAT MG MERR0 Hn0 R2 R3 R4 R8 R9 R18 R20 R21 R22 R23 R25 R26 R27
  HRM0 HCNT0.
pose proof (l2_hp0 HJ) as Ehp1. subst hp1.
destruct (hl_recs (hs_held h)) as [|r0 rs0] eqn:ER; [unfold hl_n in Hn0; rewrite ER in Hn0; cbn in Hn0; lia|].
replace (BASE + A_cshe_l2) with (l2_pc (length (hl_recs (hs_held h)))) by (rewrite ER; reflexivity).
apply l2_loop. split; [lia|]. exists ly, S, kk, (hs_held h).
assert (EN : hl_n (hs_held h) = Z.of_nat (length (hl_recs (hs_held h)))) by reflexivity.
split.
- split; [exact HJ|]. split; [rewrite l2_set_held_id; exact HSRC|].
  split; [reflexivity|]. split; [reflexivity|].
  rewrite firstn_all, skipn_all. rewrite list_basics.list.filter_nil, list_basics.list.filter_nil, app_nil_r.
  split; [reflexivity|]. split; [intros rest Hp; exact Hp|]. split; [reflexivity|].
  split; [cbn [length Z.of_nat]; rewrite Z.mul_0_l; exact (mle_start MT S ML)|].
  split; [rewrite <- EN; exact HMO|].
  split; [exact HROM|]. split; [exact HSAV|]. split; [exact M16|]. split; [exact MAT|]. split; [exact MG|].
  split; [exact MERR0|]. split; [first [exact HRM0 | rewrite ER; exact HRM0] | exact HCNT0].
- unfold l2_regs. rewrite <- EN.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split; [exact R18|]. split; [exact R20|]. split; [exact R21|]. split; [exact R22|]. split; [exact R23|].
  split; [exact R25|]. split; [exact R26 | exact R27].
Qed.

End loop.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): loop 2 at a world relation R, for a Theorem Labs lane's pb_check_shape_ends_xR
   (lib/A/W_cshe_top.v Section wR, hypothesis L2R).  Each <name>R below is the strict <name> above with the journal
   ajournal_gx_x SEGS B PST ARx -> ajournal_gx_xR SEGS B PST ARx R, SRr SEGS -> SRrG SEGS R and cshe_post_x ->
   cshe_post_xR (W_contract_xR_g6.v); the strict texts above are unchanged.  The runs are the G runs (paj_run_x_xG /
   paj_run_to_x_xG, W_journal_x.v Section g) driven by paj_run_tok_xR / paj_run_to_tok_xR (W_kit_x.v), the branch is
   paj_branch_xR.  The three calls: has_prefix stays strict, lifted by SRr_SRrG (WLE_R) and bound by SRrG_bind
   (R_trans); the free is AFREE_R (afree_cf_rule_c_xR), whose call-boundary premise (RO at the call memory; part 3c
   removed its memnorm premise) comes from ARx at the call state (RO_ARx, as W_list_drop.v Section wR); the memmove is
   aj_gx_entry_at_xR.  A world step at R may hide more than wle allows, so writability across it is taken from presence
   alone (l2_writable_kept_pR).  W_check_shape_ends.v's cshe_P_at_x and its epilogue cshe_epi_m_x / cshe_epi_x read a
   strict journal; l2_P_atR, l2_epi_mR and l2_epi_xR are their texts over the R journal, with their proofs. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* writability across a step that keeps presence, at any world relation: where the byte is hidden or absent its
   writability is the segment's (W_LLVMFuzzerTestOneInput_remove.v cn_awr_kept); l2_writable_kept_w without wle *)
Lemma l2_writable_kept_pR : forall (W W' : world SEGS) (m m' : word -> option byte) a,
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
(* l2_ar / l2_hp0 over the R journal *)
Lemma l2_arR {G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k} :
ajournal_gx_xR SEGS B PST ARx R G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k ->
ARx ly1 S1 hp1 W1 mem1 md1.
Proof. intros HJ. eapply ajournal_gx_AR_xR. exact HJ. Qed.
Lemma l2_hp0R {G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k} :
ajournal_gx_xR SEGS B PST ARx R G' XO' OUT STK sp' FP ly0 S0 hp0 W0 mem0 md0 own ly1 S1 hp1 W1 mem1 md1 k -> hp1 = [].
Proof. intros HJ. exact (HP0 _ _ _ _ _ _ (l2_arR HJ)). Qed.
(* l2_src_step across a step at R (writability from presence alone) *)
Lemma l2_src_stepR : forall ly1 S1 hp1 md1 (W1 W2 : world SEGS) m1 m2 HA1 h1 lo hi,
ARx ly1 S1 hp1 W1 m1 md1 -> asrc_at B ly1 S1 W1 m1 HA1 h1 ->
(forall a, HA1 <= a < HA1 + ASRC -> in_img SEGS a) -> alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> R W1 W2 ->
asrc_at B ly1 S1 W2 m2 HA1 h1.
Proof.
intros ly1 S1 hp1 md1 W1 W2 m1 m2 HA1 h1 lo hi HAR HS Himg Hlo HK Hp Hw.
pose proof (asan_consts) as (C1 & _).
apply (l2_src_kept ly1 S1 W1 W2 m1 m2 HA1 h1 HS).
- intros a Ha. split; [|intros Hwr; exact (l2_writable_kept_pR W1 W2 m1 m2 a (Hp a) Hwr)].
  pose proof (pa_img_range a (Himg a Ha)) as HI. apply HK; lia.
- intros b n a Hin Ha. split; [|intros Hwr; exact (l2_writable_kept_pR W1 W2 m1 m2 a (Hp a) Hwr)].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 m1 md1 b n HAR Hin) as (_ & B4096 & Bceil & _).
  apply HK; lia.
Qed.
(* l2_free_gx at R: the free rule AFREE_R *)
Lemma l2_free_gxR : forall XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb (o : Z) raw ch
  (kr : nat),
ajournal_gx_xR SEGS B PST ARx R G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own lyc Sc hpc W memT mdc k -> XO1 mod 16 = 0 ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
(* the room round: the rule's room (one free) and the live counts at the call *)
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
(In (pa, nb) (ablocks B ly S) -> forall i, 0 <= i < req_size nb -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 hp2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) /\
 aregs_preserved regsT regs2 /\
 (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, nb) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
 frames S2 = frames Sc /\
 acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size nb) /\
 mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
 (forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (pa <= a < pa + req_size nb) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).
Proof.
intros XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb o raw ch kr
HJ HX Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hch Hctx HRM HCNT Hfp Hmo.
(* the call memory's RO, from ARx at the call state (W_list_drop.v aj_free_gx_xR) *)
pose proof HJ as HARc. apply ajournal_gx_AR_xR in HARc.
pose proof (RO_ARx _ _ _ _ _ _ HARc) as HRO.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
assert (Hal' : (o - XO1) mod 16 = 0) by (rewrite Zminus_mod, Hal, HX; reflexivity).
eapply (SRrG_mono SEGS R).
{ exact (AFREE_R W regsT memT (STK + XO1) (sp0 + XO1) FP ly S hp W0 memS md own lyc Sc hpc mdc k pa nb (o - XO1) raw ch kr
  HJi Hin Ha0 ltac:(lia) Hal' ltac:(lia) ltac:(lia)
  (* the stack room below the call (a Theorem Labs lane's ACALL_PREFIX), from the journal's astk_ok *)
  (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o - XO1) regsT HJi ltac:(lia) ltac:(lia))
  Hgp Htp Hra Hraw Hch HRO Hctx HRM HCNT Hfp Hmo). }
cbv beta. intros W2 c2 HR2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs & HK & Hle & HRM2 & Herr & Hpr).
replace (sp0 + XO1 + (o - XO1) - ASTACK) with (sp0 + o - ASTACK) in HK by lia.
replace (sp0 + XO1 + (o - XO1)) with (sp0 + o) in HK by lia.
exists ly2, S2, hp2, regs2, mem2, md2. split; [reflexivity|].
split; [|split; [exact HP2 | split; [exact Hbl | split; [exact Hfrs | split; [exact HK |
  split; [exact Hle | split; [exact HRM2 | split; [exact Herr | exact Hpr]]]]]]]].
apply (ajournal_gx_pack_xR SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply (proj1 HK); lia.
Qed.

(* W_check_shape_ends.v cshe_P_at_x over the R journal (its proof, at the journal lemmas' R twins) *)
Lemma l2_P_atR : forall XO OUT STK sp0 ly S hp W mem md HA h PF PLEN,
ARx ly S hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= PLEN ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
forall ly1 S1 hp1 W1 mem1 md1 kk,
ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 (blk_FP (list_blks (hs_held h))) ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk ->
(forall a, in_rom SEGS a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1) /\
shadow_hull_vis (aview SEGS (w_H W1) mem1) PF (PLEN + 1) /\
(forall a, PF <= a < PF + PLEN + 8 -> 4096 <= a < alloc_ceiling).
Proof.
intros XO OUT STK sp0 ly S hp W mem md HA h PF PLEN HAR0 HSRC HPL HRA HOME ly1 S1 hp1 W1 mem1 md1 kk HJ ROMK.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO OUT STK sp0 _ ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HOME as [(HR & HS) | (cid & pos & Hin & Hfr)].
- (* a read-only literal *)
  destruct (HS ly1 S1 hp1 W1 mem1 md1 HAR1) as [HRAP HHVP].
  split; [intros a Ha; exact (ROMK a (HR a Ha))|].
  split; [exact HRAP|]. split; [exact (HHVP ltac:(lia))|].
  intros a Ha. destruct (HR a Ha) as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])). lia.
- (* a local of one of the entry's fake frames *)
  assert (HBS : forall b, In b (list_blks (hs_held h)) -> In b (ablocks B ly S)).
  { intros b Hb. apply (cshe_src_blks B ly S W mem HA h HSRC b). unfold asrc_blks.
    right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO OUT STK sp0 _ ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ)
    as (memS & HJi & Hag).
  pose proof HJi as (_ & Hlay & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
  destruct (frames_bounds_x SEGS B ARx LAWS ly S hp W mem md cid pos HAR0 Hin) as (Hf0 & Hfc & _).
  destruct (W_frame_x.frame_al64_x SEGS ARx FRMF ly S hp W mem md cid pos HAR0 Hin) as (Hal & Hbal & _).
  assert (HPin : frame_addr ly cid pos <= PF /\ PF + PLEN + 8 <= frame_addr ly cid pos + fs_frame_bytes cid).
  { pose proof (Hfr PF ltac:(lia)) as H1. pose proof (Hfr (PF + PLEN + 7) ltac:(lia)) as H2.
    unfold in_zr, frame_rng in H1, H2. cbn [fst snd] in H1, H2. lia. }
  (* no frame byte and no shadow byte of the frame is in the free footprint, nor in G *)
  assert (NFP : forall x, inFP (blk_FP (list_blks (hs_held h))) x ->
    x < frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= x).
  { intros x (r & Hr & Hrr). unfold blk_FP in Hr. apply in_map_iff in Hr as ((p & k) & <- & Hpk). cbn [fst snd] in Hrr.
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly S hp W mem md p k cid pos HAR0 (HBS _ Hpk) Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (NFPs : forall x, inFP (blk_FP (list_blks (hs_held h))) x -> x < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= x).
  { intros x (r & Hr & Hrr). unfold blk_FP in Hr. apply in_map_iff in Hr as ((p & k) & <- & Hpk). cbn [fst snd] in Hrr.
    destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p k HAR0 (HBS _ Hpk)) as (_ & _ & _ & Happ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia. }
  split.
  { intros a Ha. rewrite (F4 cid pos a Hin).
    - apply Hag. rewrite unsigned_lit_small by lia. intros Hg.
      exact (frm_img_x SEGS B ARx LAWS ly S hp W mem md cid pos a HAR0 Hin ltac:(lia) (proj1 (HG a Hg))).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - intros HF. pose proof (NFP a HF). lia. }
  split.
  { apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1));
      [|exact HRA].
    intros x Hx.
    pose proof (cshe_shadow_in_frame (frame_addr ly cid pos) (fs_frame_bytes cid) x Hal Hbal ltac:(lia)) as Hsx.
    unfold shadow_addr in Hsx. unfold shadow_of_addr.
    assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite (F4 cid pos _ Hin).
    - apply Hag. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). intros Hg.
      pose proof (pa_img_range _ (proj1 (HG _ Hg))). unfold SHADOW_OFF in *. lia.
    - right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
    - intros HF. pose proof (NFPs _ HF). lia. }
  split.
  { assert (EF : frame_addr ly1 cid pos = frame_addr ly cid pos).
    { destruct Hlay as (_ & _ & _ & _ & _ & HF & _). unfold frame_addr. rewrite HF. reflexivity. }
    apply (W_frame_x.shadow_hull_vis_of_frame_x SEGS B ARx LAWS FRMF ly1 S1 hp1 W1 mem1 md1 cid pos PF (PLEN + 1) HAR1);
      [rewrite Hfrs; exact Hin | rewrite EF; lia | rewrite EF; lia | lia]. }
  intros a Ha. lia.
Qed.

(* W_check_shape_ends.v cshe_v64 (a section-local tactic there) *)
Ltac l2_v64 w :=
let H := fresh "Hbr" in pose proof (bv_unsigned_in_range 64 w) as H;
change (bv_modulus 64) with (2 ^ 64) in H; zside.
(* W_check_shape_ends.v cshe_epi_m_x / cshe_epi_x over the R journal: the epilogue moves no world, so its strict walk
   over the R journal (paj_run_x_xR) is lifted by SRr_SRrG *)
Lemma l2_epi_mR : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall x : word, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR HQ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSHE_STK = 16528) by reflexivity. rewrite WS in Hceil. pose proof alloc_ceiling_val as ACV.
destruct HFR as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
assert (Hspv : spZ regs = spZ regs0 - 144).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. unfold spZ in Hceil, H47. lia. }
remember (Eimg (Ereg regs (cshe_svextra regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E32 : ew E 32 = getr regs0 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs0 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs0 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs0 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs0 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs0 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs0 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs0 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = getr regs0 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = getr regs0 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 144) by (rewrite E2; exact Hspv).
assert (N1 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 136) 8 (bv_unsigned (getr regs0 1)))
  by (replace (spZ regs0 - 144 + 136) with (spZ regs0 - 8) by lia; exact M1).
assert (N8 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 128) 8 (bv_unsigned (getr regs0 8)))
  by (replace (spZ regs0 - 144 + 128) with (spZ regs0 - 16) by lia; exact M8).
assert (N9 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 120) 8 (bv_unsigned (getr regs0 9)))
  by (replace (spZ regs0 - 144 + 120) with (spZ regs0 - 24) by lia; exact M9).
assert (N18 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 112) 8 (bv_unsigned (getr regs0 18)))
  by (replace (spZ regs0 - 144 + 112) with (spZ regs0 - 32) by lia; exact M18).
assert (N19 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 104) 8 (bv_unsigned (getr regs0 19)))
  by (replace (spZ regs0 - 144 + 104) with (spZ regs0 - 40) by lia; exact M19).
assert (N20 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 96) 8 (bv_unsigned (getr regs0 20)))
  by (replace (spZ regs0 - 144 + 96) with (spZ regs0 - 48) by lia; exact M20).
assert (N21 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 88) 8 (bv_unsigned (getr regs0 21)))
  by (replace (spZ regs0 - 144 + 88) with (spZ regs0 - 56) by lia; exact M21).
assert (N22 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 80) 8 (bv_unsigned (getr regs0 22)))
  by (replace (spZ regs0 - 144 + 80) with (spZ regs0 - 64) by lia; exact M22).
assert (N23 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 72) 8 (bv_unsigned (getr regs0 23)))
  by (replace (spZ regs0 - 144 + 72) with (spZ regs0 - 72) by lia; exact M23).
assert (N24 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 64) 8 (bv_unsigned (getr regs0 24)))
  by (replace (spZ regs0 - 144 + 64) with (spZ regs0 - 80) by lia; exact M24).
assert (N25 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 56) 8 (bv_unsigned (getr regs0 25)))
  by (replace (spZ regs0 - 144 + 56) with (spZ regs0 - 88) by lia; exact M25).
assert (N26 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 48) 8 (bv_unsigned (getr regs0 26)))
  by (replace (spZ regs0 - 144 + 48) with (spZ regs0 - 96) by lia; exact M26).
assert (N27 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 40) 8 (bv_unsigned (getr regs0 27)))
  by (replace (spZ regs0 - 144 + 40) with (spZ regs0 - 104) by lia; exact M27).
assert (HS : st_ok_pi SEGS VAL E ss_cshe_ret
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_ret)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cshe_ret. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, cshe_frmR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
    cbn [base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons); try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 40 8 (SOff 45 0) (bv_unsigned (getr regs0 27)));
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 27) | zside | exact N27].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 48 8 (SOff 44 0) (bv_unsigned (getr regs0 26)));
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 26) | zside | exact N26].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 56 8 (SOff 43 0) (bv_unsigned (getr regs0 25)));
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 25) | zside | exact N25].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 64 8 (SOff 42 0) (bv_unsigned (getr regs0 24)));
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 24) | zside | exact N24].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 72 8 (SOff 41 0) (bv_unsigned (getr regs0 23)));
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 23) | zside | exact N23].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 80 8 (SOff 40 0) (bv_unsigned (getr regs0 22)));
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 22) | zside | exact N22].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 88 8 (SOff 39 0) (bv_unsigned (getr regs0 21)));
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 21) | zside | exact N21].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 96 8 (SOff 38 0) (bv_unsigned (getr regs0 20)));
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 20) | zside | exact N20].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 104 8 (SOff 37 0) (bv_unsigned (getr regs0 19)));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 19) | zside | exact N19].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 112 8 (SOff 36 0) (bv_unsigned (getr regs0 18)));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 18) | zside | exact N18].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 120 8 (SOff 35 0) (bv_unsigned (getr regs0 9)));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 9) | zside | exact N9].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 128 8 (SOff 34 0) (bv_unsigned (getr regs0 8)));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 8) | zside | exact N8].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 136 8 (SOff 32 0) (bv_unsigned (getr regs0 1)));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l2_v64 (getr regs0 1) | zside | exact N1].
  - apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [cshe_efacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hceil H47 Hal16 C1 C3 WS ACV. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|].
    apply Z.divide_sub_r; [exact Hal16 | exists 9; reflexivity]. }
assert (SHOK : sh_ok SEGS Bx [] E (mrestrict (w_H W) mem)) by constructor.
pose (RUNx := paj_run_x_xR B PST ARx LAWS R G HG XO OUT).
unfold cfg_at. change (w64 (BASE + A_cshe_ret)) with (Z_to_bv 64 (BASE + A_cshe_ret)).
paj_run_tok_x RUNx HS HJ SHOK Bspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold cshe_frmR. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (paj_ret_at (PL := PL_fr) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (HR1 : getr (ms_regs ms) 1 = getr regs0 1) by (rewrite R1; exact E32).
assert (ZB : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r)
  by (intros z r <-; apply Z_to_bv_bv_unsigned).
assert (HPRES : aregs_preserved regs0 (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite (ZB 2 (2%bv : bv 5) eq_refl), R2, Usp.
    replace (spZ regs0 - 144 + 144) with (spZ regs0) by lia.
    unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (ZB 3 (3%bv : bv 5) eq_refl), R3, E3. exact H3.
  - rewrite (ZB 4 (4%bv : bv 5) eq_refl), R4, E4. exact H4.
  - rewrite (ZB 8 (8%bv : bv 5) eq_refl), R8. exact E34.
  - rewrite (ZB 9 (9%bv : bv 5) eq_refl), R9. exact E35.
  - assert (Hr18 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr18 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + rewrite (ZB 18 (18%bv : bv 5) eq_refl), R18. exact E36.
    + rewrite (ZB 19 (19%bv : bv 5) eq_refl), R19. exact E37.
    + rewrite (ZB 20 (20%bv : bv 5) eq_refl), R20. exact E38.
    + rewrite (ZB 21 (21%bv : bv 5) eq_refl), R21. exact E39.
    + rewrite (ZB 22 (22%bv : bv 5) eq_refl), R22. exact E40.
    + rewrite (ZB 23 (23%bv : bv 5) eq_refl), R23. exact E41.
    + rewrite (ZB 24 (24%bv : bv 5) eq_refl), R24. exact E42.
    + rewrite (ZB 25 (25%bv : bv 5) eq_refl), R25. exact E43.
    + rewrite (ZB 26 (26%bv : bv 5) eq_refl), R26. exact E44.
    + rewrite (ZB 27 (27%bv : bv 5) eq_refl), R27. exact E45. }
assert (HKEEP : forall x : word, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (HFr x) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cshe_ret In] in Hin. unfold cshe_frmR in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
cbn [ms_regs ms_mem]. rewrite HR1, Hra.
apply (HQ (ms_regs ms) (ms_mem ms) _ HPRES HKEEP).
apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
Lemma l2_epi_xR : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR HQ.
apply (SRr_SRrG SEGS R WLE_R).
apply (l2_epi_mR W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR).
intros regs' mem' md' HPRES HMEQ HJ'. apply (HQ regs' mem' md' HPRES); [| |exact HJ'].
- intros a Ha. apply (aview_eq_of SEGS). apply HMEQ.
- intros a Hp. exact (cshe_apres_meq W mem mem' a (HMEQ _) Hp).
Qed.

(* ------------------------------------------------------------------ the loop at R *)
Section loopR.
(* Section loop's variables, notations and hypotheses, verbatim, with Post at cshe_post_xR .. R .. *)
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 gone : Z) (j : nat) (h : hsrc) (P ob : list byte).
(* the room round: the caller's room budget past this call (cshe_post_x's kr) *)
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation R0 := (hl_recs (hs_held h)).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_post_xR B PST ARx R MT RP G regs0 ly S hp W mem md XO AT HA h P A0 gone ob kr).
Local Notation PLEN := (Z.of_nat (length P)).
(* the records past the first m: those dropped (they have the prefix), those kept *)
Local Notation DS m := (filter (fun r => CheckRep.prefixb P (snd r)) (skipn m (hl_recs (hs_held h)))).
Local Notation KP m := (filter (fun r => negb (CheckRep.prefixb P (snd r))) (skipn m (hl_recs (hs_held h)))).
Hypothesis HPRE : afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs0 mem md ch.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HSRC0 : asrc_at B ly S W mem HA h.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 4096 <= HA.
Hypothesis HAhi : HA + ASRC <= kLowMemEnd.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis HAj : HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j.
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
  ~ (sp0 - CSHE_STK <= a < sp0 + XO).
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
Hypothesis HPRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
(* where P lives: a read-only literal, or a local of one of S's fake frames (cshe_spec's disjunction) *)
Hypothesis HPHOME : (forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
  exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos)).
Hypothesis HROM0 : rom_view SEGS W mem.
Hypothesis Hgone : gone <> 0.
Hypothesis HMO : mo_ok MT S (cshe_cost MT (hs_held h)).

(* the source g_s[j]: image bytes the allocator does not own, not errno, not read-only, apart from g_gone *)
Lemma l2_HAimgR : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a /\ ~ (VAL A_g_gone <= a < VAL A_g_gone + 1).
Proof.
intros a Ha. unfold ASRC in *.
assert (Hs : VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384) by (rewrite HAj in Ha; lia).
destruct (HGS a Hs) as (Hi & Hr & Hg & _).
assert (Hg' : inG cshe_ro a).
{ unfold inG, cshe_ro. apply Exists_exists. exists (VAL (A_OBJ 22), 384). split; [right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
destruct (HGR a Hg') as (_ & Ho & _). pose proof (proj1 (HGRR a Hg')) as He.
split; [exact Hi|]. split; [exact Ho|]. split; [exact He|]. split; [exact Hr | exact Hg].
Qed.
(* errno's four bytes are image bytes (l2_errno_img, restated: its lia closes over the loop's hypotheses) *)
Lemma l2_errno_imgR : forall q, 0 <= q < 4 -> in_img SEGS (as_errno B + q).
Proof. intros q Hq. pose proof (pal_env B TL) as (_ & HeImg & _). apply HeImg. lia. Qed.
(* and none of them is a byte of g_s[j] *)
Lemma l2_errno_offR : forall q, 0 <= q < 4 -> ~ (HA <= as_errno B + q < HA + ASRC).
Proof.
intros q Hq Hc. destruct (l2_HAimgR (as_errno B + q) Hc) as (_ & _ & He & _). lia.
Qed.

(* the invariant at the head, m records not yet examined (the Kind-B proof's cse_inv at i = m - 1,
   lib/A/Prog/check_shape_ends.v:503-521 on a working branch, over this walk's journal) *)
Definition l2_regsR (regs1 : bvmap 5 word) (m : nat) : Prop :=
getr regs1 2 = w64 (sp0 - 144) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 8 = w64 (HA + 88) /\ getr regs1 9 = w64 PF /\ getr regs1 18 = w64 (HA + 80) /\
getr regs1 20 = w64 (Z.of_nat m + 1) /\ getr regs1 21 = w64 (- Z.of_nat m) /\ getr regs1 22 = w64 1 /\
getr regs1 23 = w64 (AREC * (Z.of_nat m - 1)) /\ getr regs1 25 = w64 SB /\
getr regs1 26 = w64 ((HA + 80) / 8 + SB) /\ getr regs1 27 = w64 3.
Definition l2_memR (m : nat) (ly1 : alayout) (S1 : astate) (kk : Z) (H1 : hlist) (W1 : world SEGS)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v (hs_held h) /\ hl_cap H1 = hl_cap (hs_held h) /\
hl_recs H1 = firstn m (hl_recs (hs_held h)) ++ KP m /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks (DS m) ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length (DS m)) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat m * mo_free MT) /\
rom_view SEGS W1 mem1 /\ cshe_saved W1 mem1 sp0 regs0 /\
val_mem SEGS (arm W1 mem1) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
val_mem SEGS (arm W1 mem1) AT 8 A0 /\ val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone /\
(* errno's view is the entry's (cshe_post_x's conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
(* the room round: the room budget (one free per record not yet examined) and the live counts, which only fall *)
rp_RM RP S1 (m + kr) /\ cnt_ok RP (ablocks B ly1 S1).
Definition l2_invR (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_memR m ly1 S1 kk H1 W1 mem1 md1 /\ l2_regsR regs1 m.
(* 0x854d4: s3 = &v[m] *)
Definition l2_midR (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat /\
exists ly1 S1 kk H1, l2_memR (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 /\ l2_regsR regs1 (Datatypes.S m) /\
getr regs1 19 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m).
(* 0x8550c: has_prefix said v[m] has the prefix; s8 = the shadow byte of &v[m] *)
Definition l2_hitR (m : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat /\ CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = true /\
exists ly1 S1 kk H1, l2_memR (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 /\ l2_regsR regs1 (Datatypes.S m) /\
getr regs1 19 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m) /\
getr regs1 24 = w64 ((hl_v (hs_held h) + AREC * Z.of_nat m) / 8 + SB).

Lemma l2_regs_eqR : forall regs1 regs2 m, (forall r, getr regs2 r = getr regs1 r) -> l2_regsR regs1 m -> l2_regsR regs2 m.
Proof. intros regs1 regs2 m E X. unfold l2_regsR in *. rewrite !E. exact X. Qed.

(* the memory side of the invariant moves across a step that writes only [lo, hi), above the allocator's ceiling
   and below the frame, and keeps presence *)
Lemma l2_mem_keepR : forall m ly1 S1 kk H1 (W1 W2 : world SEGS) m1 m2 md1 md2 lo hi,
l2_memR m ly1 S1 kk H1 W1 m1 md1 ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] W2 m2 md2 kk ->
alloc_ceiling <= lo -> hi <= sp0 - 144 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> R W1 W2 ->
l2_memR m ly1 S1 kk H1 W2 m2 md2.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 W2 m1 m2 md1 md2 lo hi
  (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT)
  HJ2 Hlo Hhi HK HP Hw.
pose proof (l2_arR HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
split; [exact HJ2|].
split.
{ apply (l2_src_stepR ly1 S1 [] md1 W1 W2 m1 m2 HA _ lo hi HAR1 HSRC); [| exact Hlo | exact HK | exact HP | exact Hw].
  intros a Ha. exact (proj1 (l2_HAimgR a Ha)). }
split; [exact HV|]. split; [exact HC|]. split; [exact HREC|]. split; [exact HPERM|].
split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split.
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi) as HI. rewrite HK by lia. exact (HROM a Hr). }
split.
{ apply (l2_saved_kept W1 W2 m1 m2 sp0 regs0); [|exact HSAV]. intros a Ha. apply HK; lia. }
split; [apply (l2_vm_keep W1 W2 m1 m2); [intros x Hx; cbn in Hx; apply HK; lia | exact M16]|].
split; [apply (l2_vm_keep W1 W2 m1 m2); [intros x Hx; cbn in Hx; apply HK; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W2 m1 m2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
  pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR. apply HK; lia. }
split; [intros q Hq; pose proof (pa_img_range _ (l2_errno_imgR q Hq)) as HeR; rewrite HK by lia; exact (MERR q Hq)|].
exact (conj MRM MCNT).
Qed.

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
(* a register the run did not change: the same symbolic value in the state HS0 the run started from *)
Ltac l2_keepreg HS0 HS r :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq; rewrite Bq, <- A; clear A Bq.

(* ---- 0x854c4 .. 0x854d4: the shadow check of l->v, s3 = l->v + 16 i ---- *)
Lemma l2_AR : forall m W1 regs1 mem1 md1, l2_invR (Datatypes.S m) W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_midR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l2b)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR) HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof (l2_arR HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & _).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
destruct (l2a_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) R2 R8 R18 R25 R26 HSPb HSPa HA8 HAlo HAhi'
  HvR V16 Hn1 MvH ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (l2_xa (hl_v H1) (hl_n H1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
pose proof HS as HS0.
pose (RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_cshe_l2b.
{ apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi l2_hd0] in Ha; lia | apply awr_ok_x_nil]. }
pmkst HS.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_nowin HFr).
assert (PRES : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
assert (T19' : getr (ms_regs ms) 19 = w64 (hl_v (hs_held h) + AREC * Z.of_nat m)).
{ prreg HS (19%bv : bv 5) T19. rewrite T19, (EEo 23%nat 23%bv eq_refl), R23, E32, HV. unfold w64.
  rewrite YI08.alu64_add_lit. f_equal. unfold AREC. lia. }
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  replace (BASE + k) with (BASE + A_cshe_l2b) by (unfold A_cshe_l2b, AF_fr_check_shape_ends; lia) end.
apply HKont. split; [lia|].
exists ly1, S1, kk, H1. split; [|split; [|exact T19']].
- apply (l2_mem_keepR (Datatypes.S m) ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms) md1 _ (sp0 - 144) (sp0 - 144) HM HJ);
  [lia | lia | intros a Ha _; exact (KEEP a Ha) | exact PRES | apply R_refl].
- unfold l2_regsR.
  split; [l2_keepreg HS0 HS (2%bv : bv 5); exact R2|].
  split; [l2_keepreg HS0 HS (3%bv : bv 5); exact R3|].
  split; [l2_keepreg HS0 HS (4%bv : bv 5); exact R4|].
  split; [l2_keepreg HS0 HS (8%bv : bv 5); exact R8|].
  split; [l2_keepreg HS0 HS (9%bv : bv 5); exact R9|].
  split; [l2_keepreg HS0 HS (18%bv : bv 5); exact R18|].
  split; [l2_keepreg HS0 HS (20%bv : bv 5); exact R20|].
  split; [l2_keepreg HS0 HS (21%bv : bv 5); exact R21|].
  split; [l2_keepreg HS0 HS (22%bv : bv 5); exact R22|].
  split; [l2_keepreg HS0 HS (23%bv : bv 5); exact R23|].
  split; [l2_keepreg HS0 HS (25%bv : bv 5); exact R25|].
  split; [l2_keepreg HS0 HS (26%bv : bv 5); exact R26|].
  l2_keepreg HS0 HS (27%bv : bv 5); exact R27.
Qed.

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
(* a register no run and no call changed, read in the state HS0 the walk started from (env OLD-related) *)
Ltac l2_keepreg2 HS0 HS r OLD :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq;
repeat (rewrite OLD in Bq by lia); rewrite Bq, <- A; clear A Bq.

(* a record without the prefix: the head moves one record down, nothing else changes *)
Lemma l2_mem_missR : forall m ly1 S1 kk H1 W1 mem1 md1, (Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = false ->
l2_memR (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 -> l2_memR m ly1 S1 kk H1 W1 mem1 md1.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 mem1 md1 Hm E (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HRST).
pose proof (mo_free_nonneg MT ML) as Hf.
split; [exact HJ|]. split; [exact HSRC|]. split; [exact HV|]. split; [exact HC|].
split; [rewrite HREC; apply l2_kp_miss; [lia | exact E]|].
rewrite (l2_ds_miss P (hl_recs (hs_held h)) m ltac:(lia) E).
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|].
destruct HRST as (HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
split.
{ apply (mok_station MT S1 S1 (Z.of_nat (Datatypes.S m) * mo_free MT) 0 (Z.of_nat m * mo_free MT) ML HMOK
    (mle_start MT S1 ML)); [apply Z.mul_nonneg_nonneg; lia | rewrite Nat2Z.inj_succ; nia]. }
split; [exact HROM|]. split; [exact HSAV|]. split; [exact M16|]. split; [exact MAT|]. split; [exact MG|].
split; [exact MERR|]. split; [|exact MCNT].
(* a record without the prefix is not freed: the budget past it is smaller *)
exact (RMM_of RP S1 (m + kr) (Datatypes.S m + kr) ltac:(lia) MRM).
Qed.

(* ---- 0x854d4 .. 0x85508: the shadow checks of v[i], has_prefix(v[i].s, v[i].n, PF), beqz a0;
   no match: 0x85558 .. 0x85564, the counters and bltu, to the head or (last record) the epilogue ---- *)
Lemma l2_BR : forall m W1 regs1 mem1 md1, l2_midR m W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_invR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (l2_pc m)) mem2 (seg_rom SEGS)) md2) Post) ->
(forall W2 regs2 mem2 md2, l2_hitR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l2h)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2b)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
pose proof (l2_P_atR XO [(AT, AT + 8)] CSHE_STK sp0 ly S hp W mem md HA h PF PLEN (proj1 HPRE) HSRC0
  ltac:(lia) HPRA HPHOME) as LPA. clear HPHOME.
intros m W1 regs1 mem1 md1 (Hle & ly1 & S1 & kk & H1 & HM & HR & R19) Kloop Khit.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & _ & _ & _ & _ & HROM & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof (l2_arR HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & _ & _ & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (unfold AREC in Vceil; lia).
(* the record v[m] *)
set (r := nth m (hl_recs (hs_held h)) (0, [])).
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
rewrite Forall_forall in HFallH. destruct (HFallH r HRIN) as (HrB & HrG & HrL & _).
destruct (HrL eq_refl) as (HrNZ & HrLEN). unfold APARTIAL in HrLEN.
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
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
assert (HRimg : HA + 96 <= RA \/ RA + 16 <= HA + 80).
{ pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as Hoff. rewrite HreqV in Hoff.
  pose proof (pa_img_range HA (proj1 (l2_HAimgR HA ltac:(unfold ASRC; lia)))) as HI1.
  pose proof (pa_img_range (HA + 95) (proj1 (l2_HAimgR (HA + 95) ltac:(unfold ASRC; lia)))) as HI2.
  unfold off_img in Hoff. destruct Hoff; [right | left]; lia. }
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR1 HvinH
  ltac:(lia) ltac:(rewrite HreqV; lia)) as HRAR.
destruct (l2b_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) RA (fst r) (Z.of_nat (length (snd r)))
  R2 R8 R18 R19 R25 R26 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1 ltac:(lia) ltac:(lia) HRimg HRapp ltac:(lia) ltac:(lia)
  MvH ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH) Ms0 Ml0
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia]) HRAR) as [HS SHOK].
pose proof alloc_ceiling_val as ACV.
assert (HXO0 : 0 <= XO) by (pose proof HJ as (_ & HX & _); exact HX).
remember (Eimg (Ereg regs1 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j0, (j0 < 4)%nat -> ew E (32 + j0) =
  nth j0 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))) (Z_to_bv 64 0)).
{ intros j0 Hj0. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E34 : ew E 34 = Z_to_bv 64 (fst r)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 3%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (EEo 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite (EEo 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = RA) by (rewrite (EEo 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
pose proof HS as HS0.
pose (RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNG := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan AF_fr_has_prefix.
{ cbv [ss_mem ss_l2b l2_hd0 l2_rec].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; l2_nowin HFr).
assert (PRESr : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] W1 _ _ kk HJ)
  as (memS & HJi & HgS).
assert (HAR3 : ARx ly1 S1 [] W1 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (Usp1 : spZ (ms_regs ms) = sp0 - 144) by (unfold spZ; rewrite Q2; exact Usp).
assert (HPREh : afn_pre_x SEGS B ARx HP_STK ly1 S1 [] W1 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_x_atR SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 [] W1 (ms_mem ms) mdc kk
    (ms_regs ms) HP_STK (- 144 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia. }
(* read-only bytes are the entry's *)
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Hr. assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; assumption).
  pose proof (pa_img_range a Hi). rewrite KEEPr by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
(* P's bytes and its shadow, wherever P lives (W_check_shape_ends.v cshe_P_at_x) *)
destruct (LPA ly1 S1 [] W1 (ms_mem ms) mdc kk HJ ROMK) as (PK & HRAP & HHVP & _).
assert (TXT : cshe_bytes W1 (ms_mem ms) (fst r) (snd r ++ [Z_to_bv 8 0])).
{ apply cshe_bytes_of_garr8. apply (l2_g8_keep W1 W1 mem1 (ms_mem ms)); [|exact HrG].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. apply KEEPr. lia. }
assert (PTXT : cshe_bytes W1 (ms_mem ms) PF (P ++ [Z_to_bv 8 0])).
{ intros t Ht. rewrite length_app in Ht. cbn [length] in Ht. rewrite PK by lia.
  destruct (Z_lt_ge_dec t PLEN) as [Hlt | Hge].
  - rewrite app_nth1 by lia. exact (HPB t ltac:(lia)).
  - assert (Ht' : t = PLEN) by lia. rewrite Ht'. rewrite app_nth2 by lia.
    replace (Z.to_nat PLEN - length P)%nat with 0%nat by lia. cbn [nth]. rewrite HPN. reflexivity. }
eapply (SRrG_bind SEGS R R_trans).
{ apply (SRr_SRrG SEGS R WLE_R).
  apply (W_has_prefix.pb_has_prefix_x B PST ARx LAWS ASTRLEN ABCMP W1 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdc []
    (fst r) (Z.of_nat (length (snd r))) PF PLEN HPREh).
  - rewrite Q10, E34. reflexivity.
  - rewrite Q11, E35. reflexivity.
  - rewrite Q12, (EEo 9%nat 9%bv eq_refl), R9. reflexivity.
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
  - unfold hp_off. rewrite Usp1. intros a Ha. pose proof (proj2 (HPV a ltac:(lia))) as Hno. rewrite WS in Hno.
    unfold HP_STK, ESTACK. clear - Hno HXO0. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact HHVP.
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). rewrite PK by lia.
    exact (proj1 (HPV a ltac:(lia))).
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle2. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (fst r + (a - fst r)) by lia.
      rewrite (TXT (a - fst r) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + unfold hp_off. rewrite Usp1. intros a Ha. unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *. lia.
    + apply l2_amem_of_app. apply (in_app_sub (fst r) (Z.of_nat (length (snd r)) + 1)); [exact Hrapp | lia | lia | lia].
    + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 (ms_mem ms) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 (ms_mem ms) _ (fst r) (Z.of_nat (length (snd r)) + 1));
      [exact HAR3 | exact HrB | lia | rewrite HreqR; lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (l2_shv_sub _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) HHVP). }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HFRc & HRES).
rewrite Usp1 in HJc, HFRc.
assert (HB : exists b, (b = 0 \/ b = 1) /\ getr regs2 10 = w64 b /\ (b = 1 <-> CheckRep.prefixb P (snd r) = true)).
{ destruct HRES as [(Hle2 & Hpre & Hr10) | (Hnp & Hr10)].
  - exists 1. split; [right; reflexivity|]. split; [exact Hr10|]. split; [intros _|intros _; reflexivity].
    apply (proj1 (cshe_prefixb_iff W1 (ms_mem ms) (fst r) PF (snd r) P TXT PTXT)). split; assumption.
  - exists 0. split; [left; reflexivity|]. split; [exact Hr10|]. split; [intros Hc; discriminate Hc|].
    intros Hp. exfalso. destruct (proj2 (cshe_prefixb_iff W1 (ms_mem ms) (fst r) PF (snd r) P TXT PTXT) Hp) as (Hl3 & Hpr).
    exact (Hnp Hl3 Hpr). }
destruct HB as (b & Hb01 & Hb10 & HbP).
assert (HJc' : ajournal_gx_xR SEGS B PST ARx R G 0 [] HP_STK (sp0 - 144) [] ly1 S1 [] W1 (ms_mem ms) mdc [] ly1 S1 [] W2 mem2 md2 0).
{ apply (ajournal_gx_G_mono_xR SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|].
  apply ajournal_gx_nil_xR. eapply ajournal_xR_mono; [exact WLE_R|].
  first [exact HJc | rewrite ajournal_x_wle in HJc; exact HJc]. }
pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 [] W1 (ms_mem ms) mdc kk HP_STK (sp0 - 144) 0 [] [] [] ly1 S1 [] W2 mem2 md2 0 HJ HJc'
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18, ?U19.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRc; [lia|]. unfold HP_STK, ESTACK. lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRc; [lia|]. unfold HP_STK, ESTACK. lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (F40 : ew Ea 40 = w64 b) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hb10).
clear HEa.
assert (F18 : ew Ea 18 = Z_to_bv 64 (HA + 80)) by (rewrite OLDa by lia; rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (F19 : ew Ea 19 = Z_to_bv 64 RA) by (rewrite OLDa by lia; rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (F25 : ew Ea 25 = Z_to_bv 64 SB) by (rewrite OLDa by lia; rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (HAR2 : ARx ly1 S1 [] W2 mem2 md2)
  by exact (l2_arR HJ2).
assert (SHOK2 : sh_ok SEGS Bx1 l2_SHb Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, l2_SHb. constructor; [|constructor; [|constructor]].
  - eapply shent_ok_of_range.
    + exact (azs_range_addressable_x B ARx LAWS ly1 S1 [] W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
    + unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
    + rewrite (U_atom Ea 18 (HA + 80) F18) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold SHADOW_OFF in *. lia.
  - eapply shent_ok_of_range.
    + exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W2 mem2 md2 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR2 HvinH
        ltac:(lia) ltac:(rewrite HreqV; lia)).
    + unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
    + rewrite (U_atom Ea 19 RA F19) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. cbn in Hx. destruct HRapp as [_ [HH | [HH _]]];
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* what the turn kept so far, from the head's memory *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) by (intros a Ha Hs; rewrite HFRc by assumption; apply KEEPr; exact Ha).
assert (PRES2 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) by (intros a Hp; exact (HPR2 a (PRESr a Hp))).
rewrite Q1.
paj_run_tok_xR RUNG HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNG BRR HS SHOK2 Bspan.
- (* beqz taken: no match *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb0 : b = 0) by (apply Z.eqb_eq in Hc; exact Hc).
  assert (HPF : CheckRep.prefixb P (snd r) = false)
    by (destruct (CheckRep.prefixb P (snd r)) eqn:Eq; [exfalso; pose proof (proj2 HbP eq_refl); lia | reflexivity]).
  paj_run_tok_xR RUNG HS HJ2 SHOK2 Bspan.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_nil. }
  prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_memR (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms1) mdb).
  { apply (l2_mem_keepR (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms1) md1 mdb (sp0 - 144 - HP_STK) (sp0 - 144) HM HJ2);
    [unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *; lia | lia | | | exact Hwle2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  pose proof (l2_mem_missR m ly1 S1 kk H1 W2 (ms_mem ms1) mdb Hle HPF MEM1) as MEM0.
  assert (REGS1 : l2_regsR (ms_regs ms1) m).
  { unfold l2_regsR.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [rewrite T20, (OLDa 20%nat) by lia; rewrite (EEo 20%nat 20%bv eq_refl), R20; unfold w64; apply l2_wrap_add; lia|].
    split; [rewrite T21, (OLDa 21%nat) by lia; rewrite (EEo 21%nat 21%bv eq_refl), R21; unfold w64; apply l2_wrap_add; lia|].
    split; [l2_keepreg2 HS0 HS (22%bv : bv 5) OLDa; exact R22|].
    split; [rewrite T23, (OLDa 23%nat) by lia; rewrite (EEo 23%nat 23%bv eq_refl), R23; unfold w64; apply l2_wrap_add;
            unfold AREC; lia|].
    split; [l2_keepreg2 HS0 HS (25%bv : bv 5) OLDa; exact R25|].
    split; [l2_keepreg2 HS0 HS (26%bv : bv 5) OLDa; exact R26|].
    l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27. }
  assert (F20 : ew Ea 20 = Z_to_bv 64 (Z.of_nat (Datatypes.S m) + 1))
    by (rewrite OLDa by lia; rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (F22 : ew Ea 22 = Z_to_bv 64 1) by (rewrite OLDa by lia; rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  clear T20 T21 T23.
  pose proof HS as HSt.
  psrr_branch_tok RUNG BRR HS SHOK2 Bspan.
  + (* bltu taken: records are left, back to the head *)
    rewrite branch_ltu_U, (U_atom Ea 22 1 F22), (U_atom_off Ea 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc0 by (unfold hl_n in Hn26; lia).
    destruct m as [|m']; [exfalso; apply Z.ltb_lt in Hc0; lia|].
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 Bspan A_cshe_l2.
    { cbn [ss_mem add_cond].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    pmkst HS.
    assert (RG : forall rr, getr (ms_regs ms2) rr = getr (ms_regs ms1) rr).
    { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
      rewrite X1, X0. reflexivity. }
    assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a)
      by (intros a Ha; l2_back).
    lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
    assert (MEMF : l2_memR (Datatypes.S m') ly1 S1 kk H1 W2 (ms_mem ms2) mdd).
    { apply (l2_mem_keepR (Datatypes.S m') ly1 S1 kk H1 W2 W2 (ms_mem ms1) (ms_mem ms2) mdb mdd (sp0 - 144) (sp0 - 144) MEM0 HJ2);
      [lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply R_refl].
      intros a Hp. l2_pres_back Hp. }
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
      replace (BASE + k) with (l2_pc (Datatypes.S m')) by (cbn [l2_pc]; unfold A_cshe_l2, AF_fr_check_shape_ends; lia) end.
    apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
    exact (l2_regs_eqR (ms_regs ms1) (ms_regs ms2) (Datatypes.S m') RG REGS1).
  + (* bltu not taken: that was the last record, on to the epilogue *)
    rewrite branch_ltu_U, (U_atom Ea 22 1 F22), (U_atom_off Ea 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc0 by (unfold hl_n in Hn26; lia).
    assert (Hm0 : m = 0%nat) by (apply Z.ltb_ge in Hc0; lia). subst m.
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 Bspan A_cshe_ret.
    { cbn [ss_mem add_cond].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    pmkst HS.
    assert (RG : forall rr, getr (ms_regs ms2) rr = getr (ms_regs ms1) rr).
    { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
      rewrite X1, X0. reflexivity. }
    assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a)
      by (intros a Ha; l2_back).
    lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
    assert (MEMF : l2_memR 0 ly1 S1 kk H1 W2 (ms_mem ms2) mdd).
    { apply (l2_mem_keepR 0 ly1 S1 kk H1 W2 W2 (ms_mem ms1) (ms_mem ms2) mdb mdd (sp0 - 144) (sp0 - 144) MEM0 HJ2);
      [lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply R_refl].
      intros a Hp. l2_pres_back Hp. }
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
      replace (BASE + k) with (l2_pc 0) by (cbn [l2_pc]; unfold A_cshe_ret, AF_fr_check_shape_ends; lia) end.
    apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
    exact (l2_regs_eqR (ms_regs ms1) (ms_regs ms2) 0 RG REGS1).
- (* beqz not taken: a match *)
  rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc by (destruct Hb01; lia).
  assert (Hb1 : b = 1) by (destruct Hb01 as [-> | ->]; [discriminate Hc | reflexivity]).
  assert (HPT : CheckRep.prefixb P (snd r) = true) by (apply HbP; exact Hb1).
  paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 Bspan A_cshe_l2h.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_nil. }
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; l2_back).
  assert (MEM1 : l2_memR (Datatypes.S m) ly1 S1 kk H1 W2 (ms_mem ms1) mdb).
  { apply (l2_mem_keepR (Datatypes.S m) ly1 S1 kk H1 W1 W2 mem1 (ms_mem ms1) md1 mdb (sp0 - 144 - HP_STK) (sp0 - 144) HM HJ2);
    [unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *; lia | lia | | | exact Hwle2].
    - intros a Ha Hs. rewrite KEEP3 by exact Ha. exact (KEEP2 a Ha Hs).
    - intros a Hp. pose proof (PRES2 a Hp) as Hq. l2_pres_back Hq. }
  prreg HS (24%bv : bv 5) T24.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (BASE + A_cshe_l2h) by (unfold A_cshe_l2h, AF_fr_check_shape_ends; lia) end.
  apply Khit. split; [exact Hle|]. split; [exact HPT|].
  exists ly1, S1, kk, H1. split; [exact MEM1|]. split.
  { unfold l2_regsR.
    split; [l2_keepreg2 HS0 HS (2%bv : bv 5) OLDa; exact R2|].
    split; [l2_keepreg2 HS0 HS (3%bv : bv 5) OLDa; exact R3|].
    split; [l2_keepreg2 HS0 HS (4%bv : bv 5) OLDa; exact R4|].
    split; [l2_keepreg2 HS0 HS (8%bv : bv 5) OLDa; exact R8|].
    split; [l2_keepreg2 HS0 HS (9%bv : bv 5) OLDa; exact R9|].
    split; [l2_keepreg2 HS0 HS (18%bv : bv 5) OLDa; exact R18|].
    split; [l2_keepreg2 HS0 HS (20%bv : bv 5) OLDa; exact R20|].
    split; [l2_keepreg2 HS0 HS (21%bv : bv 5) OLDa; exact R21|].
    split; [l2_keepreg2 HS0 HS (22%bv : bv 5) OLDa; exact R22|].
    split; [l2_keepreg2 HS0 HS (23%bv : bv 5) OLDa; exact R23|].
    split; [l2_keepreg2 HS0 HS (25%bv : bv 5) OLDa; exact R25|].
    split; [l2_keepreg2 HS0 HS (26%bv : bv 5) OLDa; exact R26|].
    l2_keepreg2 HS0 HS (27%bv : bv 5) OLDa; exact R27. }
  split; [l2_keepreg2 HS0 HS (19%bv : bv 5) OLDa; exact R19|].
  rewrite T24, F19, F25. unfold w64. rewrite l2_srl3 by lia. rewrite YI08.alu64_add_lit. reflexivity.
Qed.

(* ---- 0x85558 .. 0x85568: s4--, s5++, s7 -= 16, bltu s6, s4 -> the head, else j 0x85690 ---- *)
Lemma l2_DR : forall m ly1 S1 kk H1 W1 regs1 mem1 md1, (Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
l2_memR m ly1 S1 kk H1 W1 mem1 md1 -> l2_regsR regs1 (Datatypes.S m) ->
(forall W2 regs2 mem2 md2, l2_invR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (l2_pc m)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2t)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 regs1 mem1 md1 Hle HM HR Kloop.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
pose proof (l2t_state W1 regs1 mem1 (sp0 - 144) HA R2 R18 R25 HSPb HSPa HA8 HAlo HAhi') as HS.
remember (Eimg (Ereg regs1 ([] : list word))) as E eqn:HE.
assert (SHOK : sh_ok SEGS Bx1 [] E (mrestrict (w_H W1) mem1)) by (unfold sh_ok; constructor).
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (F20 : ew E 20 = Z_to_bv 64 (Z.of_nat (Datatypes.S m) + 1)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (F22 : ew E 22 = Z_to_bv 64 1) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
pose proof HS as HS0.
pose (RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNG := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ cbv [ss_mem ss_l2t]. apply awr_ok_x_nil. }
prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23.
assert (REGS1 : l2_regsR (ms_regs ms) m).
{ unfold l2_regsR.
  split; [l2_keepreg HS0 HS (2%bv : bv 5); exact R2|].
  split; [l2_keepreg HS0 HS (3%bv : bv 5); exact R3|].
  split; [l2_keepreg HS0 HS (4%bv : bv 5); exact R4|].
  split; [l2_keepreg HS0 HS (8%bv : bv 5); exact R8|].
  split; [l2_keepreg HS0 HS (9%bv : bv 5); exact R9|].
  split; [l2_keepreg HS0 HS (18%bv : bv 5); exact R18|].
  split; [rewrite T20, (EEo 20%nat 20%bv eq_refl), R20; unfold w64; apply l2_wrap_add; lia|].
  split; [rewrite T21, (EEo 21%nat 21%bv eq_refl), R21; unfold w64; apply l2_wrap_add; lia|].
  split; [l2_keepreg HS0 HS (22%bv : bv 5); exact R22|].
  split; [rewrite T23, (EEo 23%nat 23%bv eq_refl), R23; unfold w64; apply l2_wrap_add; unfold AREC; lia|].
  split; [l2_keepreg HS0 HS (25%bv : bv 5); exact R25|].
  split; [l2_keepreg HS0 HS (26%bv : bv 5); exact R26|].
  l2_keepreg HS0 HS (27%bv : bv 5); exact R27. }
clear T20 T21 T23.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdb := mdq) in * end.
pose proof HS as HSt.
psrr_branch_tok RUNG BRR HS SHOK Bspan.
- (* bltu taken: records are left, back to the head *)
  rewrite branch_ltu_U, (U_atom E 22 1 F22), (U_atom_off E 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc
    by (unfold hl_n in Hn26; lia).
  destruct m as [|m']; [exfalso; apply Z.ltb_lt in Hc; lia|].
  paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_cshe_l2.
  { cbv [ss_mem add_cond]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms0) rr = getr (ms_regs ms) rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
    rewrite X1, X0. reflexivity. }
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_back).
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_memR (Datatypes.S m') ly1 S1 kk H1 W1 (ms_mem ms0) mdd).
  { apply (l2_mem_keepR (Datatypes.S m') ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms0) md1 mdd (sp0 - 144) (sp0 - 144) HM HJ);
    [rewrite WS in *; lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply R_refl].
    intros a Hp. l2_pres_back Hp. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (l2_pc (Datatypes.S m')) by (cbn [l2_pc]; unfold A_cshe_l2, AF_fr_check_shape_ends; lia) end.
  apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
  exact (l2_regs_eqR (ms_regs ms) (ms_regs ms0) (Datatypes.S m') RG REGS1).
- (* bltu not taken: that was the last record, on to the epilogue *)
  rewrite branch_ltu_U, (U_atom E 22 1 F22), (U_atom_off E 20 (Z.of_nat (Datatypes.S m) + 1) (-1) F20) in Hc
    by (unfold hl_n in Hn26; lia).
  assert (Hm0 : m = 0%nat) by (apply Z.ltb_ge in Hc; lia). subst m.
  paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_cshe_ret.
  { cbv [ss_mem add_cond]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (RG : forall rr, getr (ms_regs ms0) rr = getr (ms_regs ms) rr).
  { intros rr. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ rr HSt) as X0.
    rewrite X1, X0. reflexivity. }
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; l2_back).
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdd := mdq) in * end.
  assert (MEMF : l2_memR 0 ly1 S1 kk H1 W1 (ms_mem ms0) mdd).
  { apply (l2_mem_keepR 0 ly1 S1 kk H1 W1 W1 mem1 (ms_mem ms0) md1 mdd (sp0 - 144) (sp0 - 144) HM HJ);
    [rewrite WS in *; lia | lia | intros a Ha _; exact (KEEP4 a Ha) | | apply R_refl].
    intros a Hp. l2_pres_back Hp. }
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    replace (BASE + k) with (l2_pc 0) by (cbn [l2_pc]; unfold A_cshe_ret, AF_fr_check_shape_ends; lia) end.
  apply Kloop. split; [lia|]. exists ly1, S1, kk, H1. split; [exact MEMF|].
  exact (l2_regs_eqR (ms_regs ms) (ms_regs ms0) 0 RG REGS1).
Qed.

(* the memory side of a drop: from the invariant before the turn (m + 1 records to examine, v[m] has the prefix), the
   free of v[m].s, the memmove and the store of n - 1 give the invariant with m records to examine; every fact the
   walk proves about the memory after the turn is a premise *)
Lemma l2_mem_dropR : forall m ly1 S1 kk H1 W1 mem1 md1 ly2 S2 W2 mem2 md2,
(Datatypes.S m <= length (hl_recs (hs_held h)))%nat ->
CheckRep.prefixb P (snd (nth m (hl_recs (hs_held h)) (0, []))) = true ->
l2_memR (Datatypes.S m) ly1 S1 kk H1 W1 mem1 md1 ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 [] W2 mem2 md2 (kk + 1) ->
R W1 W2 ->
(exists l1 l2, ablocks B ly1 S1 = l1 ++ (fst (nth m (hl_recs (hs_held h)) (0, [])),
   Z.of_nat (length (snd (nth m (hl_recs (hs_held h)) (0, [])))) + 1) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
frames S2 = frames S1 ->
mo_le MT S1 S2 (mo_free MT) ->
rom_view SEGS W2 mem2 ->
val_mem SEGS (arm W2 mem2) (HA + 88) 4 (hl_n H1 - 1) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 88 <= a < HA + 92) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 144 - ASTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
  ~ (fst (nth m (hl_recs (hs_held h)) (0, [])) <= a <
     fst (nth m (hl_recs (hs_held h)) (0, [])) + Z.of_nat (length (snd (nth m (hl_recs (hs_held h)) (0, [])))) + 1) ->
  ~ (hl_v (hs_held h) + AREC * Z.of_nat m <= a <
     hl_v (hs_held h) + AREC * Z.of_nat m + AREC * (hl_n H1 - 1 - Z.of_nat m)) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall k, 0 <= k < AREC * (hl_n H1 - 1 - Z.of_nat m) ->
  aview SEGS (w_H W2) mem2 (hl_v (hs_held h) + AREC * Z.of_nat m + k) =
  aview SEGS (w_H W1) mem1 (hl_v (hs_held h) + AREC * Z.of_nat m + AREC + k)) ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W1) mem1 (as_errno B + j)) ->
(* the room round: the free's post room (its rule's kr is the m + kr left) *)
rp_RM RP S2 (m + kr) ->
l2_memR m ly2 S2 (kk + 1) (ldrop_list H1 m) W2 mem2 md2.
Proof.
clear HPHOME.
intros m ly1 S1 kk H1 W1 mem1 md1 ly2 S2 W2 mem2 md2 Hle HPT HM HJ2 Hwle Hbl Hfrs2 Hle2 ROMF MnF KIMG KPRES KHI KBLK KMOV
  KERR HRMd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as ACV.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (EAS : ESTACK = 4096 /\ ASTACK = 16384) by (split; reflexivity).
pose proof (mo_free_nonneg MT ML) as Hf0.
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
pose proof (l2_arR HJ) as HAR1.
pose proof (l2_arR HJ2)
  as HAR2.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPD & _ & _ & _ & _ & _ & _ & _ & HPIN & HPJLEN & _ & _ & HED & HAH0 & HNDS).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected] in HPD, HPIN, HPJLEN, HED.
pose proof HNDS as HNDS0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & _ & _)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil.
set (r := nth m (hl_recs (hs_held h)) (0, [])) in *.
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
pose proof HFallH as HFallH'. rewrite Forall_forall in HFallH'. destruct (HFallH' r HRIN) as (HrB & _).
assert (HreqT : forall x : Z * list byte, req_size (Z.of_nat (length (snd x)) + 1) = Z.of_nat (length (snd x)) + 1).
{ intros x. unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq;
  [apply Z.eqb_eq in Eq; pose proof (Nat2Z.is_nonneg (length (snd x))); lia | reflexivity]. }
assert (VNE : hl_v H1 <> fst r) by (intros Heq; apply HninH; rewrite Heq; apply in_map; exact HRIN).
assert (Ecap : (hl_cap H1 =? 0) = false) by (apply Z.eqb_neq; lia).
(* the head bytes of the source *)
assert (GH : forall a, HA <= a < HA + 96 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (l2_HAimgR a ltac:(unfold ASRC; lia)) as (Hi & Ho & He & _). split; [exact Hi|]. split; [exact Ho | exact He]. }
assert (KHD : forall a, HA <= a < HA + 96 -> ~ (HA + 88 <= a < HA + 92) -> abyte_kept W1 mem1 W2 mem2 a).
{ intros a Ha Hw. destruct (GH a Ha) as (Hi & Ho & He). split; [exact (KIMG a Hi Ho He Hw)|].
  intros Hwr. apply (l2_writable_kept_pR W1 W2 mem1 mem2 a); [intros Hp; exact (KPRES a Hi Ho He Hp) | exact Hwr]. }
(* the blocks other than the freed text and the vector keep their bytes and their writability *)
assert (KOFF : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + Z.of_nat (length (snd r)) + 1)).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 p n (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 Hin HrB
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite (HreqT r) in DJx. lia. }
assert (KOFV : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> hl_v H1 -> p <= a < p + req_size n ->
  ~ (hl_v H1 <= a < hl_v H1 + AREC * hl_cap H1)).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 p n (hl_v H1) (AREC * hl_cap H1) HAR1 Hin HvinH
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite HreqV in DJx. lia. }
assert (BLK2 : forall p n, In (p, n) (ablocks B ly1 S1) -> (p, n) <> (fst r, Z.of_nat (length (snd r)) + 1) ->
  In (p, n) (ablocks B ly2 S2)).
{ intros p n Hin Hne2. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | exfalso; exact (Hne2 (eq_sym Hx)) | right; exact Hx]. }
assert (KBK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <> hl_v H1 -> p <= a < p + req_size n ->
  abyte_kept W1 mem1 W2 mem2 a).
{ intros p n a Hin Hp1 Hp2 Ha. split.
  - apply (KBLK p n a Hin Ha (KOFF p n a Hin Hp1 Ha)). intros Hc. apply (KOFV p n a Hin Hp2 Ha). rewrite HV.
    unfold hl_n in *. unfold AREC in *. lia.
  - intros Hw.
    destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 mem2 md2 p n HAR2
      (BLK2 p n Hin ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq)))) as (_ & _ & _ & _ & Hpres & _).
    exact (apresent_writable SEGS _ _ _ (proj1 (Hpres a Ha))). }
(* the held list, one record shorter *)
assert (HE2 : alist_at B ly2 S2 W2 mem2 (HA + 80) (ldrop_list H1 m) true).
{ apply (ALDROP ly1 S1 W1 mem1 ly2 S2 W2 mem2 (HA + 80) H1 true m HAH).
  - lia.
  - rewrite ENTH. exact Hbl.
  - intros a Ha. exact (proj1 (KHD a ltac:(lia) ltac:(lia))).
  - intros i Hi. destruct (GH (HA + 80 + i) ltac:(lia)) as (Hi1 & Ho1 & He1).
    apply (l2_writable_kept_pR W1 W2 mem1 mem2 (HA + 80 + i));
    [intros Hp; exact (KPRES _ Hi1 Ho1 He1 Hp) | exact (MwH i Hi)].
  - replace (HA + 80 + 8) with (HA + 88) by lia. exact MnF.
  - intros k Hk. rewrite HV. exact (KMOV k Hk).
  - intros a Ha.
    apply (KBLK (hl_v H1) (AREC * hl_cap H1) a HvinH).
    + rewrite HreqV. unfold hl_n in *. unfold AREC in *. lia.
    + apply (KOFF (hl_v H1) (AREC * hl_cap H1) a HvinH VNE). rewrite HreqV. unfold hl_n in *. unfold AREC in *. lia.
    + rewrite <- HV. unfold hl_n in *. unfold AREC in *. lia.
  - intros r' Hr' a Ha.
    destruct (nth_split (hl_recs H1) (0, []) (proj2 HLR : (m < length (hl_recs H1))%nat)) as (A & Bs & Hsp & HlA).
    rewrite ENTH in Hsp.
    unfold ldrop_list in Hr'. cbn [HarnessRep.hl_recs] in Hr'. rewrite Hsp, <- HlA, l2_drop_split in Hr'.
    assert (Hin' : In r' (hl_recs H1)).
    { rewrite Hsp. apply in_app_or in Hr' as [Hx | Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
    assert (Hne1 : fst r' <> fst r).
    { intros Heq. pose proof HNDvH as ND1. apply NoDup_ListNoDup in ND1. rewrite Hsp, map_app in ND1. cbn [map] in ND1.
      apply List.NoDup_remove_2 in ND1. apply ND1. rewrite <- Heq, <- map_app. apply in_map. exact Hr'. }
    assert (Hne2 : fst r' <> hl_v H1) by (intros Heq; apply HninH; rewrite <- Heq; apply in_map; exact Hin').
    destruct (HFallH' r' Hin') as (HrB' & _).
    exact (proj1 (KBK (fst r') (Z.of_nat (length (snd r')) + 1) a HrB' Hne1 Hne2 ltac:(rewrite (HreqT r'); lia))). }
(* the other lists of the source and their blocks *)
apply NoDup_ListNoDup in HNDS. unfold hs_blocks in HNDS.
cbn [CheckRep.set_held hs_pending hs_partial hs_expected hs_held] in HNDS.
assert (NDX : forall b, In b (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
  b <> fst r /\ b <> hl_v H1).
{ intros b Hb.
  assert (HN2 : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks H1))
    by (rewrite <- !app_assoc; exact HNDS).
  split.
  - apply (l2_nodup_disj _ _ b (fst r) HN2 Hb). unfold list_blocks. apply in_or_app. right. apply in_map. exact HRIN.
  - apply (l2_nodup_disj _ _ b (hl_v H1) HN2 Hb). unfold list_blocks. apply in_or_app. left. rewrite Ecap. left. reflexivity. }
assert (HreqP : req_size APARTIAL = APARTIAL)
  by (unfold req_size, APARTIAL; destruct (6000 =? 0) eqn:Ez; [discriminate | reflexivity]).
assert (SFP : akept W1 mem1 W2 mem2
  (gfp (hs_partial (CheckRep.set_held h H1)) (bzs (hs_pjunk (CheckRep.set_held h H1))) ::
   alist_fp (HA + 16) (hs_pending (CheckRep.set_held h H1)) ++ alist_fp (HA + 64) (hs_expected (CheckRep.set_held h H1)))).
{ cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected].
  intros rr Hrr a Ha. cbn [In] in Hrr. destruct Hrr as [<- | Hrr].
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, HPJLEN in Ha.
    destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (Hp1 & Hp2).
    exact (KBK (hs_partial h) APARTIAL a HPIN Hp1 Hp2 ltac:(rewrite HreqP; unfold APARTIAL in *; lia)).
  - apply in_app_or in Hrr as [Hrr | Hrr]; revert rr Hrr a Ha.
    + apply (l2_list_kept_P ly1 S1 [] W1 mem1 md1 W2 mem2 (HA + 16) (hs_pending h) _
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HPD).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. exact (NDX b ltac:(apply in_or_app; left; exact Hb)).
    + apply (l2_list_kept_P ly1 S1 [] W1 mem1 md1 W2 mem2 (HA + 64) (hs_expected h) _
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HED).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. exact (NDX b ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb)). }
assert (SBLK : forall b, In b ((hs_partial (CheckRep.set_held h H1), APARTIAL) ::
  alist_blks (hs_pending (CheckRep.set_held h H1)) ++ alist_blks (hs_expected (CheckRep.set_held h H1))) ->
  In b (ablocks B ly2 S2)).
{ cbn [CheckRep.set_held hs_pending hs_partial hs_expected].
  intros b Hb. destruct Hb as [<- | Hb].
  - destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (Hp1 & _).
    exact (BLK2 (hs_partial h) APARTIAL HPIN ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))).
  - apply in_app_or in Hb as [Hb | Hb]; destruct b as [p n].
    + pose proof (l2_alist_blks_in ly1 S1 W1 mem1 (HA + 16) (hs_pending h) _ HPD (p, n) Hb) as Hin1.
      destruct (NDX p ltac:(apply in_or_app; left; exact (l2_alist_blks_fst _ (p, n) Hb))) as (Hp1 & _).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))).
    + pose proof (l2_alist_blks_in ly1 S1 W1 mem1 (HA + 64) (hs_expected h) _ HED (p, n) Hb) as Hin1.
      destruct (NDX p ltac:(apply in_or_app; right; apply in_or_app; right; exact (l2_alist_blks_fst _ (p, n) Hb)))
        as (Hp1 & _).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))). }
pose proof (l2_nodup_hs_drop (CheckRep.set_held h H1) m ltac:(cbn [CheckRep.set_held hs_held]; lia)
  ltac:(cbn [CheckRep.set_held hs_held]; lia) HNDS0) as NDnew.
pose proof (l2_src_swap ly1 S1 W1 mem1 ly2 S2 W2 mem2 HA (CheckRep.set_held h H1) (ldrop_list H1 m) HSRC
  ltac:(intros a Ha; apply KHD; lia) SFP SBLK HE2 NDnew) as SRC2.
rewrite l2_set_held2 in SRC2.
(* the invariant with m records to examine *)
split; [exact HJ2|]. split; [exact SRC2|].
split; [unfold ldrop_list; cbn [HarnessRep.hl_v]; exact HV|].
split; [unfold ldrop_list; cbn [HarnessRep.hl_cap]; exact HC|].
split; [rewrite (l2_ldrop_recs H1 _ _ m Hle HREC), (l2_kp_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT); reflexivity|].
split.
{ intros rest Hp. rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT) in Hp. fold r in Hp.
  unfold cshe_ds_blks in Hp, HPERM. cbn [map] in Hp.
  pose proof (HPERM ((fst r, Z.of_nat (length (snd r)) + 1) :: rest)
    ltac:(eapply Permutation_trans; [exact Hp | apply Permutation_middle])) as HP1.
  destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb1 in HP1. rewrite Eb2.
  apply (Permutation_cons_inv (a := (fst r, Z.of_nat (length (snd r)) + 1))).
  eapply Permutation_trans; [apply Permutation_middle | exact HP1]. }
split; [rewrite Hfrs2; exact HFRS|].
split.
{ apply (mle_weaken MT S S2 _ _ ML (mle_station MT S S1 S2 _ _ ML HMLE Hle2)).
  rewrite (l2_ds_hit P (hl_recs (hs_held h)) m ltac:(lia) HPT). cbn [length]. rewrite Nat2Z.inj_succ, Z.mul_succ_l. lia. }
split.
{ apply (mok_station MT S1 S2 (Z.of_nat (Datatypes.S m) * mo_free MT) (mo_free MT) (Z.of_nat m * mo_free MT) ML HMOK Hle2).
  - apply Z.mul_nonneg_nonneg; lia.
  - rewrite Nat2Z.inj_succ, Z.mul_succ_l. lia. }
split; [exact ROMF|].
split; [apply (l2_saved_kept W1 W2 mem1 mem2 sp0 regs0); [intros a Ha; apply KHI; rewrite WS in *; lia | exact HSAV]|].
split; [apply (l2_vm_keep W1 W2 mem1 mem2); [intros x Hx; cbn in Hx; apply KHI; rewrite WS in *; lia | exact M16]|].
split; [apply (l2_vm_keep W1 W2 mem1 mem2); [intros x Hx; cbn in Hx; apply KHI; rewrite WS in *; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W2 mem1 mem2); [|exact MG]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
  assert (Hg : inG cshe_ro x).
  { unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1). split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. lia. }
  destruct (HGR x Hg) as (Hi & Ho & _). pose proof (proj1 (HGRR x Hg)) as He.
  apply (KIMG x Hi Ho He). intros Hc. destruct (l2_HAimgR x ltac:(unfold ASRC; lia)) as (_ & _ & _ & _ & Hng). lia. }
split; [intros q Hq; rewrite (KERR q Hq); exact (MERR q Hq)|].
split; [exact HRMd|].
(* the free dropped one block: the live counts only fell *)
destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in MCNT. exact (l2_cnt_del RP l1 _ l2 MCNT).
Qed.

(* a run whose regions' one write window is l->n, [HA + 88, HA + 92): every byte off it is kept; U18 is the env's
   value of atom 18 (HA + 80) *)
Ltac l2_wkeep Hf U18 :=
lazymatch type of Hf with frame_of ?Ev ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) =>
  apply (aview_kept_out Ev rs H m0 m1 Hf); [lia|];
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros (rg & Hin & Hrg);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?U18 in Hrg; lia|]);
  destruct Hin
end.

(* l2_wkeep on the run's frame from m0 to m1 *)
Ltac l2_wkeep_m m0 m1 U18 :=
lazymatch goal with Hf : frame_of _ _ (mrestrict _ m0) (mrestrict _ m1) |- _ => l2_wkeep Hf U18 end.
(* a register two calls and the runs around them did not change *)
Ltac l2_keepreg3 HS0 HS r OLDa OLDb :=
let A := fresh "A" in let Bq := fresh "Bq" in prreg HS0 r A; prreg HS r Bq;
repeat (rewrite OLDb in Bq by lia); repeat (rewrite OLDa in Bq by lia); rewrite Bq, <- A; clear A Bq.

(* ---- 0x8550c .. 0x85564: v[i] has the prefix.  The shadow check of v[i], free(v[i].s), the shadow checks of l->v
   and l->n (l->n's shadow byte is zero, so the partial-granule check 0x8556c is not reached),
   __asan_memmove(&v[i], &v[i + 1], 16 (n - i - 1)), l->n = n - 1, the counters and bltu ---- *)
Lemma l2_CR : forall m W1 regs1 mem1 md1, l2_hitR m W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2, l2_invR m W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (l2_pc m)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2h)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros m W1 regs1 mem1 md1 (Hle & HPT & ly1 & S1 & kk & H1 & HM & HR & R19 & R24) Kloop.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof (l2_arR HJ) as HAR1.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0. clear HAH0.
pose proof HAH as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (HLR : (length (hl_recs H1) <= length (hl_recs (hs_held h)))%nat /\ (Datatypes.S m <= length (hl_recs H1))%nat).
{ rewrite HREC, length_app, length_firstn.
  pose proof (l2_filter_len (fun r => negb (CheckRep.prefixb P (snd r))) (skipn (Datatypes.S m) (hl_recs (hs_held h)))) as Hf.
  rewrite length_skipn in Hf. lia. }
assert (Hn1 : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
destruct HvvH as [(Hc0 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [unfold hl_n in *; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
rewrite HreqV in Vceil, Vapp.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (unfold AREC in Vceil; lia).
set (r := nth m (hl_recs (hs_held h)) (0, [])) in *.
assert (ENTH : nth m (hl_recs H1) (0, []) = r).
{ unfold r. rewrite HREC, app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (m <? Datatypes.S m)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
assert (HRIN : In r (hl_recs H1)) by (rewrite <- ENTH; apply nth_In; lia).
pose proof HFallH as HFallH'. rewrite Forall_forall in HFallH'. destruct (HFallH' r HRIN) as (HrB & HrG & HrL & _).
destruct (HrL eq_refl) as (HrNZ & HrLEN). unfold APARTIAL in HrLEN.
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 HrB) as (Hr16 & Hr4096 & Hrceil & Hrapp & _).
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
assert (HRimg : HA + 96 <= RA \/ RA + 16 <= HA + 80).
{ pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly1 S1 [] W1 mem1 md1 _ _ HAR1 HvinH) as Hoff. rewrite HreqV in Hoff.
  pose proof (pa_img_range HA (proj1 (l2_HAimgR HA ltac:(unfold ASRC; lia)))) as HI1.
  pose proof (pa_img_range (HA + 95) (proj1 (l2_HAimgR (HA + 95) ltac:(unfold ASRC; lia)))) as HI2.
  unfold off_img in Hoff. destruct Hoff; [right | left]; lia. }
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) RA 16 HAR1 HvinH
  ltac:(lia) ltac:(rewrite HreqV; lia)) as HRAR.
pose proof alloc_ceiling_val as ACV.
assert (HXO0 : 0 <= XO) by (pose proof HJ as (_ & HX & _); exact HX).
assert (HAWn : awr W1 mem1 (HA + 88) 4)
  by (intros i Hi; replace (HA + 88 + i) with (HA + 80 + (8 + i)) by lia; apply MwH; lia).
destruct (l2c_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) RA (fst r) (Z.of_nat (length (snd r)))
  R2 R8 R18 R19 R24 R25 R26 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1 ltac:(lia) ltac:(lia) HRimg HRapp
  ltac:(unfold AREC, CSHE_STK, CSHE_FRAME, ASTACK in *; lia) ltac:(lia) ltac:(lia)
  M16 MvH ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH) HAWn Ms0 Ml0
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia]) HRAR) as [HS SHOK].
clear HRimg.
remember (Eimg (Ereg regs1 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs1 rr).
{ intros m0 rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j0, (j0 < 4)%nat -> ew E (32 + j0) =
  nth j0 (l2_xb (hl_v H1) (hl_n H1) (fst r) (Z.of_nat (length (snd r)))) (Z_to_bv 64 0)).
{ intros j0 Hj0. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (fst r)) by exact (EX 2%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (EEo 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite (EEo 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18).
pose proof HS as HS0.
pose proof (pal_free B TL) as HBfree.
pose proof HG as HGok.
pose (RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNG := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
(* ---- 0x8550c .. 0x85518: the shadow check of v[i], a0 = v[i].s, jal free ---- *)
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ cbv [ss_mem ss_l2c l2_fr l2_hdw l2_rec].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite HBfree.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HAR1m : ARx ly1 S1 [] W1 (ms_mem ms) mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (Usp2 : spZ (ms_regs ms) = sp0 + -144)
  by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite Q2, Usp; lia).
assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a) by (intros a Ha Hno; l2_wkeep HFr U18).
(* ---- free(v[i].s), returning to 0x8551c ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ apply (l2_free_gxR XO [(AT, AT + 8)] W1 (ms_regs ms) (ms_mem ms) CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 [] _ kk
    (fst r) (Z.of_nat (length (snd r)) + 1) (-144) (getr (ms_regs ms) 1) [] (m + kr) HJ HX16 HrB).
  - rewrite Q10, E34. reflexivity.
  - exact Usp2.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ASTACK. lia.
  - rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly1 _ (spZ (ms_regs ms)) (HA + 88) [] (ms_regs ms)).
    + apply achain_low. lia.
    + rewrite Usp2. lia.
    + unfold s0Z. rewrite Q8, U18, unsigned_lit_small by lia. lia.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_check_shape_ends + 0x16c); [exact HCTX_cshe_l2|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_check_shape_ends in *; lia].
  - (* the free's room: S m + kr = 1 + (m + kr) by conversion *)
    exact MRM.
  - exact MCNT.
  - intros _ i Hi. exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; lia].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r, Z.of_nat (length (snd r)) + 1)).
    unfold list_blks. apply in_or_app. right.
    apply (in_map (fun rr => (fst rr, Z.of_nat (length (snd rr)) + 1))). unfold r. apply nth_In. lia.
  - pose proof (mo_free_nonneg MT ML) as Hf.
    apply (mok_station MT S1 S1 (Z.of_nat (Datatypes.S m) * mo_free MT) 0 (mo_free MT) ML HMOK (mle_start MT S1 ML));
    [lia | rewrite Nat2Z.inj_succ; nia]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs2 & HK & Hle2 & HRM2 & Herr2 & Hpres2).
pose proof (l2_hp0R HJ2) as Ehp2. subst hp2.
assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
assert (GH : forall a, HA <= a < HA + 96 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (l2_HAimgR a ltac:(unfold ASRC; lia)) as (Hi & Ho & He & _). split; [exact Hi|]. split; [exact Ho | exact He]. }
assert (IMGK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a /\
  (apresent (w_H W1) (ms_mem ms) a -> apresent (w_H W2) mem2 a)).
{ intros a Hi Ho He. split; [exact (proj1 (proj2 (proj2 HK)) a Hi Ho He)|].
  apply (Hpres2 a Hi).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly1 S1 [] W1 (ms_mem ms) _ a HAR1m Hi) Hw)).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 [] W2 mem2 md2 a HAR2 Hi) Hw)).
  - exact He.
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 (ms_mem ms) _ (fst r) _ a HAR1m HrB Hr Hi). }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK); lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GH a ltac:(lia)) as (Hi & Ho & He). exact (proj1 (IMGK a Hi Ho He)).
  - intros a Ha Hw. destruct (GH a ltac:(lia)) as (Hi & Ho & He).
    apply (l2_writable_kept_pR W1 W2 (ms_mem ms) mem2 a); [exact (proj2 (IMGK a Hi Ho He)) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
clear HEa.
assert (F18 : ew Ea 18 = Z_to_bv 64 (HA + 80)) by (rewrite OLDa by lia; rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (F25 : ew Ea 25 = Z_to_bv 64 SB) by (rewrite OLDa by lia; rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18a).
assert (SHOK2 : sh_ok SEGS Bx1 l2_SHa Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, l2_SHa. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 [] W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80) F18) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x8551c .. 0x85548: the shadow checks of l->v and l->n, a0 = &v[i], a1 = &v[i + 1], a2 = 16 (n - i - 1) ---- *)
rewrite Q1.
paj_run_tok_xR RUNG HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (EAS : ESTACK = 4096 /\ ASTACK = 16384) by (split; reflexivity).
pose proof (l2_arR HJ2)
  as HAR3.
assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a) by (intros a Ha Hno; l2_wkeep_m mem2 (ms_mem ms0) U18a).
(* the vector is still live after the free (it is not v[m].s's block) *)
assert (VNE : hl_v H1 <> fst r) by (intros Heq; apply HninH; rewrite Heq; apply in_map; exact HRIN).
assert (Hvin2 : In (hl_v H1, AREC * hl_cap H1) (ablocks B ly2 S2)).
{ pose proof Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. pose proof HvinH as Hv1. rewrite Eb1 in Hv1.
  apply in_app_or in Hv1 as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. exact (VNE (eq_sym Ex)). }
destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 (ms_mem ms0) _ _ _ HAR3 Hvin2) as (_ & _ & _ & _ & Vpres & _).
rewrite HreqV in Vpres.
set (CNT := AREC * (hl_n H1 - 1 - Z.of_nat m)).
assert (HCNTk : CNT = 16 * (hl_n H1 - 1 - Z.of_nat m)) by reflexivity.
assert (HCNT : 0 <= CNT /\ RA + 16 + CNT <= hl_v H1 + AREC * hl_cap H1).
{ rewrite HCNTk. unfold RA, AREC. rewrite <- HV. unfold hl_n in *. split; lia. }
assert (Uspa : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (Uspm : spZ (ms_regs ms0) = sp0 + -144)
  by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite P2, Uspa; lia).
assert (R10 : getr (ms_regs ms0) 10 = w64 RA).
{ rewrite P10, (OLDa 23%nat), (OLDa 32%nat) by lia. rewrite (EEo 23%nat 23%bv eq_refl), R23, E32, HV. unfold w64, RA.
  rewrite YI08.alu64_add_lit. f_equal. unfold AREC. lia. }
assert (R11 : getr (ms_regs ms0) 11 = w64 (RA + 16)).
{ rewrite P11, (OLDa 23%nat), (OLDa 32%nat) by lia. rewrite (EEo 23%nat 23%bv eq_refl), R23, E32, HV. unfold w64, RA.
  rewrite unsigned_lit_small by (unfold AREC, hl_n in *; lia). rewrite YI08.alu64_add_lit. f_equal. unfold AREC. lia. }
assert (R12 : getr (ms_regs ms0) 12 = w64 CNT).
{ rewrite P12, (OLDa 21%nat), (OLDa 33%nat) by lia. rewrite (EEo 21%nat 21%bv eq_refl), R21, E33. unfold w64.
  rewrite (l2_count_eq (Z.of_nat (Datatypes.S m)) (hl_n H1)) by (unfold hl_n in *; lia). rewrite HCNTk. f_equal. lia. }
assert (Ecap : (hl_cap (hs_held h) =? 0) = false) by (apply Z.eqb_neq; rewrite <- HC; lia).
assert (HvFP : forall a, hl_v H1 <= a < hl_v H1 + AREC * hl_cap H1 -> inFP FPc a).
{ intros a Ha. exists (hl_v (hs_held h), hl_v (hs_held h) + req_size (AREC * hl_cap (hs_held h))).
  split; [|cbn [fst snd]; rewrite <- HV, <- HC, HreqV; lia].
  unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v (hs_held h), AREC * hl_cap (hs_held h))).
  unfold list_blks. apply in_or_app. left. rewrite Ecap. left. reflexivity. }
(* rom_view at the memmove: the runs wrote only l->n (no rom byte of g_s), the free keeps a rom byte either because the
   runtime owns it and it is pinned, or because it is an image byte it did not touch (W_journal.v acall_kept_rom_view) *)
assert (ROMIMG : forall a, in_rom SEGS a -> in_img SEGS a)
  by (intros a (sg & Hsg & _ & Hra); exists sg; split; assumption).
assert (ROMW : forall a, in_rom SEGS a -> ~ (HA + 88 <= a < HA + 92)).
{ intros a Hr Hc. destruct (l2_HAimgR a ltac:(unfold ASRC; lia)) as (_ & _ & _ & Hnr & _). exact (Hnr Hr). }
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)). rewrite (KEEPa a ltac:(lia) (ROMW a Hrom)). exact (HROM a Hrom). }
assert (ROM2 : rom_view SEGS W2 mem2) by (eapply (acall_kept_rom_view_x SEGS B ARx LAWS); [exact HAR2 | exact HK | exact ROMNS | exact ROM1]).
assert (ROMK : rom_view SEGS W2 (ms_mem ms0)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)). rewrite (KEEPb a ltac:(lia) (ROMW a Hrom)). exact (ROM2 a Hrom). }
(* ---- __asan_memmove(&v[m], &v[m + 1], 16 (n - m - 1)), 0x85548 ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G XO [(AT, AT + 8)] ESTACK (SIGMA WS_asan_memmove)
  (fun a => RA <= a < RA + CNT) _
  W2 (ms_regs ms0) (ms_mem ms0) CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 [] _ (kk + 1)
  (-144) (getr (ms_regs ms0) 1) HGok HX16 HJ2).
- exact Uspm.
- reflexivity.
- lia.
- lia.
- rewrite WS. lia.
- rewrite P3, (OLDa 3%nat) by lia. rewrite (EEo 3%nat 3%bv eq_refl), R3. exact Hgp0.
- rewrite P4, (OLDa 4%nat) by lia. rewrite (EEo 4%nat 4%bv eq_refl), R4. exact Htp0.
- reflexivity.
- rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a. destruct (Z_le_gt_dec RA a) as [Hd1|Hd1]; [|right; lia].
  destruct (Z_lt_ge_dec a (RA + CNT)) as [Hd2|Hd2]; [left; lia | right; lia].
- intros a Ha HGb. cbv beta in Ha. exfalso.
  apply (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; lia | exact (proj1 (HGok a HGb))].
- intros a Ha HnG. cbv beta in Ha. split; [|rewrite WS in *; lia].
  right. left. split; [apply HvFP; lia|].
  exists (hl_v H1), (AREC * hl_cap H1). split; [exact Hvin2 | rewrite HreqV; lia].
- intros HPRE2 HSC.
  (* the destination is a heap block, so no byte of it is an image byte (W_list_drop.v:961-963 on a working branch) *)
  assert (MNIMG : forall a, RA <= a < RA + CNT -> ~ in_img SEGS a).
  { intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2).
    rewrite HreqV. lia. }
  apply (AMOVE ly2 S2 [] W2 (ms_regs ms0) (ms_mem ms0) _ RA (RA + 16) CNT HPRE2 R10 R11 R12).
  + rewrite HCNTk. unfold hl_n in *. lia.
  + lia.
  + lia.
  + intros a Ha. split; [|split].
    * apply (apresent_writable SEGS). exact (proj1 (Vpres a ltac:(lia))).
    * exact (proj2 (Vpres a ltac:(lia))).
    * rewrite Uspm. rewrite WS in *. lia.
  + apply l2_amem_of_app. apply (in_app_sub (hl_v H1) (AREC * hl_cap H1)); [exact Vapp | lia | lia | lia].
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia | exact Hpos].
  + lia.
  + lia.
  + intros a Ha. split.
    * destruct (proj1 (Vpres a ltac:(lia))) as [Hh [b Hb]].
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
    * rewrite Uspm. rewrite WS in *. lia.
  + apply l2_amem_of_app. apply (in_app_sub (hl_v H1) (AREC * hl_cap H1)); [exact Vapp | lia | lia | lia].
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; lia | exact Hpos].
  + exact ROMK.
  + intros Hpos. split; apply l2_amem_of_app; apply (in_app_sub (hl_v H1) (AREC * hl_cap H1));
    first [exact Vapp | lia].
  + exact MNIMG. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hres3 & Hmov) & Hfr3 & Hpres3).
pose proof (l2_arR HJ3) as HAR4.
assert (MOFF : forall a, in_img SEGS a -> ~ (RA <= a < RA + CNT)).
{ intros a Hi Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; lia | exact Hi]. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Uspa, ?U18a).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; [lia | cbv beta; lia | rewrite WS in *; lia].
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GH a ltac:(lia)) as (Hi & _ & _). pose proof (pa_img_range a Hi).
    apply Hfr3; [lia | exact (MOFF a Hi) | rewrite WS in *; lia].
  - intros a Ha Hw. apply (l2_writable_kept_w W2 W2 (ms_mem ms0) mem3 a); [intros Hp; exact (Hpres3 a Hp) | apply wle_refl | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m0, (m0 < 52)%nat -> ew Eb m0 = ew Ea m0) by (intros m0 Hm0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm0).
clear HEb.
assert (K18 : ew Eb 18 = Z_to_bv 64 (HA + 80)) by (rewrite OLDb by lia; exact F18).
assert (K25 : ew Eb 25 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact F25).
assert (K33 : ew Eb 33 = Z_to_bv 64 (hl_n H1)) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E33).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
assert (SHOK3 : sh_ok SEGS Bx1 l2_SHa Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, l2_SHa. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 [] W2 mem3 md3 (HA + 64) 32 HAR4 Hzs).
  - unfold Bx1. rewrite (U_atom Eb 25 SB K25) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Eb 18 (HA + 80) K18) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x8554c .. 0x85558: l->n = n - 1 ---- *)
rewrite P1.
paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 Bspan A_cshe_l2t.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdF := mdq) in * end.
assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem3 a) by (intros a Ha Hno; l2_wkeep_m mem3 (ms_mem ms1) U18b).
(* l->n after the store *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok _ ltac:(cbn [ss_mem]; right; left; reflexivity)) as (_ & _ & _ & Hchs).
pose proof (proj1 (Forall_forall _ _) Hchs (YP09.mkChunk 8 (CVal 4%N (SOff 33 (-1))))
  ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch8.
assert (MnF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 88) 4 (hl_n H1 - 1)).
{ replace (HA + 88) with (base_val Eb (Some 18%nat) + 8) by (rewrite V18b; lia).
  apply (l2_val_mem_of_chunk4 Eb _ _ 8 (SOff 33 (-1)) (hl_n H1 - 1) Hch8); [|lia].
  rewrite (U_atom_off Eb 33 (hl_n H1) (-1) K33) by lia. lia. }
(* ---- what the free, the memmove and the three runs kept, from (W1, mem1) to (W2, ms_mem ms1) ---- *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 88 <= a < HA + 92) -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hi Ho He Hw. pose proof (pa_img_range a Hi) as Har.
  rewrite (KEEPc a ltac:(lia) Hw).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; exact (MOFF a Hi)) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb a ltac:(lia) Hw).
  rewrite (proj1 (proj2 (proj2 HK)) a Hi Ho He).
  exact (KEEPa a ltac:(lia) Hw). }
assert (KPRES : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) (ms_mem ms1) a).
{ intros a Hi Ho He Hp.
  assert (Q1p : apresent (w_H W1) (ms_mem ms) a) by l2_pres_back Hp.
  pose proof (proj2 (IMGK a Hi Ho He) Q1p) as Q2p.
  assert (Q3p : apresent (w_H W2) (ms_mem ms0) a) by l2_pres_back Q2p.
  pose proof (Hpres3 a Q3p) as Q4p.
  l2_pres_back Q4p. }
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 144 - ASTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hs. assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by lia.
  rewrite (KEEPc a ltac:(lia) Hnw).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; lia) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb a ltac:(lia) Hnw).
  rewrite (proj1 HK a Ha ltac:(lia)).
  exact (KEEPa a ltac:(lia) Hnw). }
assert (KBLK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + Z.of_nat (length (snd r)) + 1) -> ~ (RA <= a < RA + CNT) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros p n a Hin Ha Hnr Hnm.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 mem1 md1 _ _ HAR1 Hin) as (_ & Hp4096 & Hpc & _).
  assert (Hni : ~ in_img SEGS a) by exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 p n a HAR1 Hin Ha).
  assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by (intros Hc; apply Hni; exact (proj1 (GH a ltac:(lia)))).
  rewrite (KEEPc a ltac:(lia) Hnw).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; exact Hnm) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb a ltac:(lia) Hnw).
  replace a with (p + (a - p)) by lia.
  rewrite (proj1 (proj2 HK) p n (a - p) Hin ltac:(lia) ltac:(cbv beta; rewrite HreqR; lia)).
  replace (p + (a - p)) with a by lia.
  exact (KEEPa a ltac:(lia) Hnw). }
assert (KMOV : forall k, 0 <= k < CNT -> aview SEGS (w_H W2) (ms_mem ms1) (RA + k) = aview SEGS (w_H W1) mem1 (RA + AREC + k)).
{ intros k Hk.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) (fst r)
    (Z.of_nat (length (snd r)) + 1) HAR1 HvinH HrB
    ltac:(intros Heq; injection Heq as Heq _; exact (VNE Heq))) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite HreqV, HreqR in DJ.
  assert (Hni1 : ~ in_img SEGS (RA + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hni2 : ~ in_img SEGS (RA + 16 + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hnw1 : ~ (HA + 88 <= RA + k < HA + 92)) by (intros Hc; apply Hni1; exact (proj1 (GH (RA + k) ltac:(lia)))).
  assert (Hnw2 : ~ (HA + 88 <= RA + 16 + k < HA + 92)) by (intros Hc; apply Hni2; exact (proj1 (GH (RA + 16 + k) ltac:(lia)))).
  rewrite (KEEPc (RA + k) ltac:(lia) Hnw1).
  rewrite (Hmov k Hk).
  rewrite (KEEPb (RA + 16 + k) ltac:(lia) Hnw2).
  replace (RA + 16 + k) with (hl_v H1 + (RA + 16 + k - hl_v H1)) by lia.
  rewrite (proj1 (proj2 HK) (hl_v H1) (AREC * hl_cap H1) (RA + 16 + k - hl_v H1) HvinH
    ltac:(rewrite HreqV; lia) ltac:(cbv beta; rewrite HreqR; lia)).
  replace (hl_v H1 + (RA + 16 + k - hl_v H1)) with (RA + AREC + k) by (unfold AREC; lia).
  exact (KEEPa (RA + AREC + k) ltac:(unfold AREC; lia) ltac:(unfold AREC; exact Hnw2)). }
assert (ROMF : rom_view SEGS W2 (ms_mem ms1)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  rewrite (KEEPc a ltac:(lia) (ROMW a Hrom)).
  rewrite (Hfr3 a ltac:(lia) ltac:(cbv beta; exact (MOFF a Hi)) ltac:(rewrite WS in *; lia)).
  exact (ROMK a Hrom). }
(* errno's four bytes: the runs write only l->n (a byte of g_s, not errno), the memmove only its heap destination,
   and the free keeps errno's view *)
assert (KERR : forall j, 0 <= j < 4 ->
  aview SEGS (w_H W2) (ms_mem ms1) (as_errno B + j) = aview SEGS (w_H W1) mem1 (as_errno B + j)).
{ intros q Hq. pose proof (l2_errno_imgR q Hq) as Hi. pose proof (pa_img_range _ Hi) as Har.
  assert (Hw : ~ (HA + 88 <= as_errno B + q < HA + 92))
    by (intros Hc; apply (l2_errno_offR q Hq); unfold ASRC; lia).
  rewrite (KEEPc (as_errno B + q) ltac:(lia) Hw).
  rewrite (Hfr3 (as_errno B + q) ltac:(lia) ltac:(cbv beta; exact (MOFF _ Hi)) ltac:(rewrite WS in *; lia)).
  rewrite (KEEPb (as_errno B + q) ltac:(lia) Hw).
  rewrite (Herr2 q Hq).
  exact (KEEPa (as_errno B + q) ltac:(lia) Hw). }
pose proof (l2_mem_dropR m ly1 S1 kk H1 W1 mem1 md1 ly2 S2 W2 (ms_mem ms1) mdF Hle HPT HM HJ3 Hwle2 Hbl Hfrs2 Hle2
  ROMF MnF KIMG KPRES KHI KBLK KMOV KERR HRM2) as MEMF.
assert (REGSF : l2_regsR (ms_regs ms1) (Datatypes.S m)).
{ unfold l2_regsR.
  split; [l2_keepreg3 HS0 HS (2%bv : bv 5) OLDa OLDb; exact R2|].
  split; [l2_keepreg3 HS0 HS (3%bv : bv 5) OLDa OLDb; exact R3|].
  split; [l2_keepreg3 HS0 HS (4%bv : bv 5) OLDa OLDb; exact R4|].
  split; [l2_keepreg3 HS0 HS (8%bv : bv 5) OLDa OLDb; exact R8|].
  split; [l2_keepreg3 HS0 HS (9%bv : bv 5) OLDa OLDb; exact R9|].
  split; [l2_keepreg3 HS0 HS (18%bv : bv 5) OLDa OLDb; exact R18|].
  split; [l2_keepreg3 HS0 HS (20%bv : bv 5) OLDa OLDb; exact R20|].
  split; [l2_keepreg3 HS0 HS (21%bv : bv 5) OLDa OLDb; exact R21|].
  split; [l2_keepreg3 HS0 HS (22%bv : bv 5) OLDa OLDb; exact R22|].
  split; [l2_keepreg3 HS0 HS (23%bv : bv 5) OLDa OLDb; exact R23|].
  split; [l2_keepreg3 HS0 HS (25%bv : bv 5) OLDa OLDb; exact R25|].
  split; [l2_keepreg3 HS0 HS (26%bv : bv 5) OLDa OLDb; exact R26|].
  l2_keepreg3 HS0 HS (27%bv : bv 5) OLDa OLDb; exact R27. }
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  replace (BASE + k) with (BASE + A_cshe_l2t) by (unfold A_cshe_l2t, AF_fr_check_shape_ends; lia) end.
exact (l2_DR m ly2 S2 (kk + 1) (ldrop_list H1 m) W2 (ms_regs ms1) (ms_mem ms1) mdF Hle MEMF REGSF Kloop).
Qed.

(* ---- 0x85690: the epilogue, from the invariant with no record left to cshe_post_x's g_gone <> 0 case ---- *)
Lemma l2_epiR : forall W1 regs1 mem1 md1, l2_invR 0 W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_ret)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
clear HPHOME.
intros W1 regs1 mem1 md1 (_ & ly1 & S1 & kk & H1 & HM & HR).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HM as (HJ & HSRC & HV & HC & HREC & HPERM & HFRS & HMLE & HMOK & HROM & HSAV & M16 & MAT & MG & MERR & MRM & MCNT).
pose proof HR as (R2 & R3 & R4 & _).
pose proof (l2_arR HJ) as HAR1.
assert (WS : CSHE_STK = 16528) by reflexivity.
change (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_ret)) mem1 (seg_rom SEGS)) md1)
  with (cfg_at SEGS (BASE + A_cshe_ret) regs1 mem1 md1).
apply (l2_epi_xR W ly S hp mem md XO [(AT, AT + 8)] FPc ly1 S1 [] W1 regs0 regs1 mem1 md1 kk Post HJ);
  [exact Hra0 | exact Hal16 | rewrite WS in *; lia | lia | exact R2 | exact R3 | exact R4 | exact HSAV |].
intros regs' mem' md' HPRES HMEQ HPR HJ'.
unfold cshe_post_xR.
exists ly1, S1, [], regs', mem', md', kk, H1, (filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h))), 0.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPRES|].
split.
{ intros q Hq. pose proof (pa_img_range _ (l2_errno_imgR q Hq)) as HeR.
  rewrite (HMEQ (as_errno B + q)) by lia. exact (MERR q Hq). }
split.
{ apply (l2_src_step ly1 S1 [] md1 W1 W1 mem1 mem' HA _ sp0 sp0 HAR1 HSRC); [| rewrite WS in *; lia | | exact HPR | apply wle_refl].
  - intros a Ha. exact (proj1 (l2_HAimgR a Ha)).
  - intros a Ha _. exact (HMEQ a Ha). }
split; [exact HV|]. split; [exact HC|].
assert (HR0 : hl_recs H1 = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs (hs_held h)))
  by (rewrite HREC; reflexivity).
split.
{ unfold CheckRep.texts. rewrite HR0. apply NoDup_ListNoDup. apply l2_nodup_filter.
  apply NoDup_ListNoDup. exact HND0. }
split; [left; split; [exact Hgone|]; split; [exact HR0|]; split; reflexivity|].
split; [lia|].
split; [rewrite Z.add_0_r; apply (l2_vm_keep W1 W1 mem1 mem'); [intros x Hx; apply HMEQ; lia | exact MAT]|].
split.
{ apply (l2_vm_keep W1 W1 mem1 mem'); [|exact MG]. intros x Hx.
  pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR. apply HMEQ. lia. }
split; [exact HPERM|]. split; [exact HFRS|].
split; [|exact MRM].
apply (mle_weaken MT S S1 _ _ ML HMLE). unfold cshe_cost, hl_n.
apply Z.mul_le_mono_nonneg_r; [exact (mo_free_nonneg MT ML)|]. apply Nat2Z.inj_le.
exact (l2_filter_len (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h))).
Qed.

(* the loop: from the head with m records not yet examined, by induction on m *)
Lemma l2_loopR : forall m W1 regs1 mem1 md1, l2_invR m W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (l2_pc m)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction m as [|m IH]; intros W1 regs1 mem1 md1 HI.
- exact (l2_epiR W1 regs1 mem1 md1 HI).
- cbn [l2_pc]. apply (l2_AR m W1 regs1 mem1 md1 HI). intros W2 regs2 mem2 md2 HM.
  apply (l2_BR m W2 regs2 mem2 md2 HM).
  + intros W3 regs3 mem3 md3 HI3. exact (IH W3 regs3 mem3 md3 HI3).
  + intros W3 regs3 mem3 md3 HH. apply (l2_CR m W3 regs3 mem3 md3 HH).
    intros W4 regs4 mem4 md4 HI4. exact (IH W4 regs4 mem4 md4 HI4).
Qed.

(* Loop 2 in full: from the state cshe_gone_l2_x leaves at the head 0x854c4 (the registers it names, and the frame,
   the journal, the source and the cells of the entry as loop 1 and the g_gone test left them) to cshe_post_x's
   g_gone <> 0 disjunct, through the epilogue cshe_epi_x.  The journal's ghost list at the head is any hp1 (HP0 makes
   it []). *)
Lemma cshe_l2_run_xR : forall W1 hp1 regs1 mem1 md1 kk,
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly S hp1 W1 mem1 md1 kk ->
asrc_at B ly S W1 mem1 HA h -> rom_view SEGS W1 mem1 -> cshe_saved W1 mem1 sp0 regs0 ->
val_mem SEGS (arm W1 mem1) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W1 mem1) AT 8 A0 -> val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
0 < hl_n (hs_held h) ->
getr regs1 2 = w64 (sp0 - 144) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = w64 (HA + 88) -> getr regs1 9 = w64 PF -> getr regs1 18 = w64 (HA + 80) ->
getr regs1 20 = w64 (hl_n (hs_held h) + 1) -> getr regs1 21 = w64 (- hl_n (hs_held h)) -> getr regs1 22 = w64 1 ->
getr regs1 23 = w64 (AREC * (hl_n (hs_held h) - 1)) -> getr regs1 25 = w64 SB ->
getr regs1 26 = w64 ((HA + 80) / 8 + SB) -> getr regs1 27 = w64 3 ->
(* the room round: one free per held record past the caller's kr, and the live counts at the loop's head *)
rp_RM RP S (length (hl_recs (hs_held h)) + kr) -> cnt_ok RP (ablocks B ly S) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2)) mem1 (seg_rom SEGS)) md1) Post.
Proof using All - AFREE.
intros W1 hp1 regs1 mem1 md1 kk HJ HSRC HROM HSAV M16 MAT MG MERR0 Hn0 R2 R3 R4 R8 R9 R18 R20 R21 R22 R23 R25 R26 R27
  HRM0 HCNT0.
pose proof (l2_hp0R HJ) as Ehp1. subst hp1.
destruct (hl_recs (hs_held h)) as [|r0 rs0] eqn:ER; [unfold hl_n in Hn0; rewrite ER in Hn0; cbn in Hn0; lia|].
replace (BASE + A_cshe_l2) with (l2_pc (length (hl_recs (hs_held h)))) by (rewrite ER; reflexivity).
apply l2_loopR. split; [lia|]. exists ly, S, kk, (hs_held h).
assert (EN : hl_n (hs_held h) = Z.of_nat (length (hl_recs (hs_held h)))) by reflexivity.
split.
- split; [exact HJ|]. split; [rewrite l2_set_held_id; exact HSRC|].
  split; [reflexivity|]. split; [reflexivity|].
  rewrite firstn_all, skipn_all. rewrite list_basics.list.filter_nil, list_basics.list.filter_nil, app_nil_r.
  split; [reflexivity|]. split; [intros rest Hp; exact Hp|]. split; [reflexivity|].
  split; [cbn [length Z.of_nat]; rewrite Z.mul_0_l; exact (mle_start MT S ML)|].
  split; [rewrite <- EN; exact HMO|].
  split; [exact HROM|]. split; [exact HSAV|]. split; [exact M16|]. split; [exact MAT|]. split; [exact MG|].
  split; [exact MERR0|]. split; [first [exact HRM0 | rewrite ER; exact HRM0] | exact HCNT0].
- unfold l2_regsR. rewrite <- EN.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split; [exact R18|]. split; [exact R20|]. split; [exact R21|]. split; [exact R22|]. split; [exact R23|].
  split; [exact R25|]. split; [exact R26 | exact R27].
Qed.

End loopR.
End wR.
End c.
End b.
End a.
