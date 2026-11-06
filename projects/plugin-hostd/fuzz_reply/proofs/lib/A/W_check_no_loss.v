(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's check_no_loss, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/AC8b.v (a loop from its head), lib/A/ACh2.v
   (internal calls) and lib/A/ACbk.v (entry and return). *)
(* check_no_loss(s, at) at 0x85958 (fuzz_reply.c:405-432) checks, for each line the source s still expects, that the
   controller saw it, and feeds it to the reference model: while s->expected.n > 0 it takes the first expected text;
   when g_gone is clear it reads the stream's next line with next_line (an internal call; cells at, &line, &len) and
   aborts unless it is that text (same length, same bytes by bcmp); then gesture_model(s, text) (an internal call);
   then the inlined list_drop(&s->expected, 0): free the text, memmove the records after it down, n - 1.
   Plain contract re-expressed: lib/Prog/check_no_loss_c.v:26-88 (expected emptied with its vector kept, held texts
   = upds (texts H) (texts E), NoDup, *at advanced by |bstream E| when the controller did not go), without the plain
   side's runtime-resource terms; the meter MT (Reusable/YC5d.v) and the room predicate cnl_room take their place.
   THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record), on the check_bounded template
   a working branch, lib/A/W_check_bounded.v): pb_check_no_loss_x proves W_contract_x.cnl_spec_x over any
   allocator relation ARx with its laws (Section c).  Its Section hypotheses (what other lanes owe):
    PST / ARx / hl / LAWS (the generic relation and its laws AR_laws_x), HP0 (no hidden heads in any ARx state:
     a Theorem Labs lane's ruling, for the heap-block shadow facts), IMGC / BLKN (W_kit_x.v Section g, for blk_off_imgP_x),
     HPST (no image byte lies in PST; true at PST = []),
     TL (W_kit.v PALib), ML (the meter laws, ameter_laws MT), HG (gx_ok
     of the caller's G; no gx_rt of it: a caller's G holds errno), CNLAP (the image objects the walk reads are
     apart: placement, vm_compute at PB_fr), HGR / HGRR (gx_ok / gx_rt of cnl_ro, the image objects the walk keeps:
     instance), ROMNS (a rom byte is not errno and is rom_pinned when owned: instance),
     NL (next_line, W_contract_x.v nl_spec_x, lane W1), GM (gesture_model, gm_spec_g_x at any G, lane W4),
     ABCMP (bcmp, W_sites_x.v abcmp_realizes_x, runtime lane), AMOVE (__asan_memmove, W_sites_x.v
     amemmove_realizes_x, runtime lane), AFREE (free, W_journal_x.v afree_cf_rule_c_x at the caller contexts CTX_AFREE,
     the allocator instance) with HCTX_cnl_free (the free site's context is in CTX_AFREE),
     ALDROP (W1's representation step of list_drop, lib/A/W_list_drop.v alist_at_drop).
   The room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the spec carries the room record RP; the loop keeps the room budget
   (gesture_model's MT_rk charge and one free per record still owed, W_cnl_cnt.v cnl_rk_step) and the live counts plus
   the peak of the plain model's trace still owed (W_cnl_cnt.v cnl_cnt / cnl_cntm), which give gesture_model's and
   free's room and count premises at each call.
   The AR statement pb_check_no_loss, byte-identical, is re-derived from it at ARx := ARi0, PST := [] (Section cAR),
   where the callees are the AR walk's: nl_spec, gm_spec_g, YG0d.v abcmp_realizes, W_sites.v amemmove_realizes and
   W_journal.v afree_cf_rule (its caller-context form by afree_cf_rule_c_weak at the free site's singleton). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rom_place.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
(* the room round's count and budget bookkeeping of this walk's loop *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_cnl_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the model's side *)
(* The model's vocabulary the contract names (capstep, capb, tbytes, hbytes, cnl_cap, cnl_room, txs, bsr, cpos) lives
   in W_contract.v, just above Section w3n, with the contract. *)

Lemma cn_filter_len_aux : forall (T : list (list Z)) x, (length (List.filter (fun y => negb (RelayModel.list_eqb x y)) T) <= length T)%nat.
Proof. intros T x. induction T as [|y T IH]; cbn [List.filter length]; [lia|]. destruct (negb (RelayModel.list_eqb x y)); cbn [length]; lia. Qed.
(* The pure facts the walk uses about the model. *)
Lemma txs_app : forall a b, txs (a ++ b) = txs a ++ txs b.
Proof. intros a b. unfold txs. apply map_app. Qed.
Lemma upds_snoc : forall T a r, RelayModel.upds T (txs (a ++ [r])) = RelayModel.upd (RelayModel.upds T (txs a)) (bzs (snd r)).
Proof. intros T a r. unfold RelayModel.upds. rewrite txs_app, fold_left_app. reflexivity. Qed.
Lemma cnl_cap_snoc : forall T c a r, cnl_cap T c (a ++ [r]) =
capstep (RelayModel.upds T (txs a)) (bzs (snd r)) (cnl_cap T c a).
Proof. intros T c a. revert T c. induction a as [|x a IH]; intros T c r; [reflexivity|]. cbn [app cnl_cap]. rewrite IH. reflexivity. Qed.
Lemma cnl_room_snoc : forall MMAX bb T c a r rs, cnl_room MMAX bb T c (a ++ r :: rs) -> exists bb',
cnl_room MMAX bb' (RelayModel.upds T (txs a)) (cnl_cap T c a) (r :: rs).
Proof.
intros MMAX bb T c a. revert bb T c. induction a as [|x a IH]; intros bb T c r rs H; [exists bb; exact H|].
cbn [app cnl_room] in H. destruct H as (_ & _ & H). destruct (IH _ _ _ r rs H) as (bb' & H'). exists bb'. exact H'.
Qed.
Lemma bzs_length : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma tbytes_app : forall a b, tbytes (a ++ b) = tbytes a + tbytes b.
Proof. intros a b. unfold tbytes. induction a as [|x a IH]; cbn [app fold_right]; lia. Qed.
Lemma bsum_recs : forall rs : list (Z * list byte),
bsum (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs) = tbytes (map (fun r => bzs (snd r)) rs).
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite bsum_cons, IH. unfold tbytes. cbn [fold_right snd].
rewrite bzs_length. lia.
Qed.
Lemma bsum_list_blks : forall l, bsum (list_blks l) = hbytes (texts l) (hl_cap l).
Proof.
intros l. unfold list_blks, hbytes, texts. rewrite bsum_app, bsum_recs. f_equal.
destruct (hl_cap l =? 0); cbn [bsum fold_right snd]; lia.
Qed.
(* the drop of the first record: its text's block leaves the list's blocks *)
Lemma list_blks_drop0 : forall v cap r rs jk jk',
Permutation (list_blks (HL v cap (r :: rs) jk)) ((fst r, Z.of_nat (length (snd r)) + 1) :: list_blks (HL v cap rs jk')).
Proof.
intros v cap r rs jk jk'. unfold list_blks. cbn [hl_cap hl_v hl_recs map]. apply Permutation_sym, Permutation_middle.
Qed.
(* a duplicate-free list inside another is a part of it *)
Lemma perm_of_incl : forall (l L : list (Z * Z)), List.NoDup l -> incl l L -> exists rest, Permutation L (l ++ rest).
Proof.
induction l as [|x l IH]; intros L ND Hi; [exists L; reflexivity|].
apply List.NoDup_cons_iff in ND as [Hx NDl].
assert (Hin : In x L) by (apply Hi; left; reflexivity).
apply in_split in Hin as (L1 & L2 & ->).
destruct (IH (L1 ++ L2) NDl) as (rest & HP).
{ intros y Hy. assert (Hy' : In y (L1 ++ x :: L2)) by (apply Hi; right; exact Hy).
  apply in_app_or in Hy' as [Hy' | [<- | Hy']]; [apply in_or_app; left; exact Hy' | exfalso; exact (Hx Hy) | apply in_or_app; right; exact Hy']. }
exists rest. rewrite <- Permutation_middle. cbn [app]. apply perm_skip. exact HP.
Qed.
(* the held list's length after one line: at most one more, and one more exactly when the line begins a key *)
Lemma upd_len : forall T l, (length (RelayModel.upd T l) <= S (length T))%nat /\
((length T < length (RelayModel.upd T l))%nat -> is_begin l = true /\ length (RelayModel.upd T l) = S (length T)).
Proof.
intros T l. unfold RelayModel.upd, is_begin. destruct (RelayModel.gesture l) as [[g x]|]; [destruct g|].
- destruct (existsb (RelayModel.list_eqb x) T); [split; [lia | intros H; lia]|]. rewrite length_app. cbn [length].
  split; [lia | intros _; split; [reflexivity | lia]].
- pose proof (cn_filter_len_aux T x) as Hf. split; [lia | intros H; lia].
- split; [lia | intros H; lia].
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_check_no_loss : Z := AF_fr_check_no_loss.
Definition A_check_no_lossP : Z := BASE + A_check_no_loss.
(* The vector's records as 8-byte cells: W1's garr8_val_mem8 / text_recs_length / alist_rec_fields
   (lib/A/W_list_find.v:49-98 on a working branch), copied here because that file is not in this branch. *)
Lemma cnl_garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
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
Lemma cnl_text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
Lemma cnl_rec_fields : forall B ly S W mem LA l lines j,
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
apply garr8_app in Hg as [_ Hg]. rewrite length_map, cnl_text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 Hg]. apply garr8_app in Hg as [H2 _].
rewrite length_map, length_N_to_le_bytes in H2.
apply cnl_garr8_val_mem8 in H1. apply cnl_garr8_val_mem8 in H2.
rewrite Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1, H2 by lia.
split; [exact H1|]. replace (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) with (HarnessRep.hl_v l + 16 * Z.of_nat j + Z.of_nat 8) by lia.
exact H2.
Qed.
(* W1's lib/A/W_list_drop.v helpers (a working branch 5bc6dd7b8b5), copied here because that file is not in
   this branch: writability across a call, a region chunk read back, two equal values give equal bytes. *)
Lemma cnl_writable_kept_w : forall (W W' : world SEGS) (m m' : word -> option byte) a,
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
Lemma cnl_val_mem_of_chunk4 : forall E (m : word -> option byte) base off e v,
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
Lemma cnl_aview_of_val_mem2 : forall H H' (m m' : word -> option byte) a n v k,
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H' m' (a + k) = aview SEGS H m (a + k).
Proof.
intros H H' m m' a n v k H1 H2 Hk. unfold aview.
rewrite (val_mem_agree SEGS _ _ a n v H1 H2 k Hk). reflexivity.
Qed.
(* a value, a byte string and the stream, carried over a step that keeps their bytes *)
Lemma cnl_vm_keep : forall (W W' : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v.
Proof.
intros W W' m m' a n v Hk Hv i Hi. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat i) (Hk (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.
Lemma cnl_g8_keep : forall (W W' : world SEGS) m m' a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W m) a l -> garr8 SEGS (arm W' m') a l.
Proof.
intros W W' m m' a l Hk Hg. apply (garr8_frame SEGS (arm W m) (arm W' m') a l Hg).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (Hk x Hx).
Qed.
Lemma cnl_ob_keep : forall (W W' : world SEGS) m m' x l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W') m' (x + i) = aview SEGS (w_H W) m (x + i)) ->
ob_at W m x l -> ob_at W' m' x l.
Proof. intros W W' m m' x l Hk Hl i Hi. rewrite (Hk i Hi). exact (Hl i Hi). Qed.
(* two neighbours of a duplicate-free list are apart from every other member *)
Lemma cnl_nodup_two : forall (P Q M L : list Z) (x y : Z),
List.NoDup (P ++ Q ++ (x :: y :: M) ++ L) -> forall z, In z (P ++ Q ++ M ++ L) -> z <> x /\ z <> y.
Proof.
intros P Q M L x y ND z Hz.
replace (P ++ Q ++ (x :: y :: M) ++ L) with ((P ++ Q) ++ x :: (y :: (M ++ L))) in ND
  by (rewrite <- !app_assoc; reflexivity).
apply List.NoDup_remove in ND as [ND Hx].
apply List.NoDup_remove in ND as [_ Hy].
assert (Hz' : In z ((P ++ Q) ++ M ++ L)) by (rewrite <- !app_assoc; exact Hz).
split; intros ->.
- apply Hx. apply in_app_or in Hz' as [Hz'|Hz']; apply in_or_app; [left; exact Hz' | right; right; exact Hz'].
- apply Hy. exact Hz'.
Qed.
(* the block addresses of a source, and of a list that has a vector *)
Lemma cnl_blocks_set : forall h0 (e l : hlist), HarnessRep.hs_blocks (set_exp_held h0 e l) =
HarnessRep.list_blocks (HarnessRep.hs_pending h0) ++ [HarnessRep.hs_partial h0] ++
HarnessRep.list_blocks e ++ HarnessRep.list_blocks l.
Proof. intros h0 e l. reflexivity. Qed.
Lemma cnl_lb_nil : forall v cap xs jk0, 0 < cap ->
HarnessRep.list_blocks (HL v cap xs jk0) = v :: map fst xs.
Proof.
intros v cap xs jk0 Hc. unfold HarnessRep.list_blocks.
cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs].
destruct (cap =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.
(* the shadow address of a byte, as the walk's srli / add leave it in a register *)
Lemma cnl_shr3_add : forall x, 0 <= x < 2 ^ 63 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SB) = Z_to_bv 64 (x / 8 + SB).
Proof.
intros x Hx.
assert (Hd : 0 <= x / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hsrl : alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8)).
{ apply bv_eq. rewrite YO0c.alu64_srl, !unsigned_lit_small by lia.
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  reflexivity. }
rewrite Hsrl, YI08.alu64_add_lit. reflexivity.
Qed.
(* the memmove's byte count at 0x85ae0: ((n - 1) << 4), as the walk's 32-bit addiw / slli leave it *)
Lemma cnl_cnt16 : forall x, 1 <= x < 2 ^ 32 ->
alu64 ALU_ADD (alu64 ALU_SLL (Z_to_bv 64 x) (Z_to_bv 64 4)) (Z_to_bv 64 (-16)) = Z_to_bv 64 (16 * x - 16).
Proof.
intros x Hx. rewrite (YI08.alu64_sll_lit x 4) by (cbn; lia). rewrite YI08.alu64_add_lit. f_equal. cbn. lia.
Qed.
(* a list without one of its elements has no duplicate either; two parts of a duplicate-free list are apart *)
Lemma cnl_nodup_drop : forall (P Q X M L : list Z) (x : Z),
List.NoDup (P ++ Q ++ (X ++ x :: M) ++ L) -> List.NoDup (P ++ Q ++ (X ++ M) ++ L).
Proof.
intros P Q X M L x H.
replace (P ++ Q ++ (X ++ M) ++ L) with ((P ++ Q ++ X) ++ (M ++ L)) by (rewrite <- !app_assoc; reflexivity).
apply (List.NoDup_remove_1 _ _ x).
replace ((P ++ Q ++ X) ++ x :: M ++ L) with (P ++ Q ++ (X ++ x :: M) ++ L) by (rewrite <- !app_assoc; reflexivity).
exact H.
Qed.
Lemma cnl_nodup_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
cbn [app] in ND. apply List.NoDup_cons_iff in ND as [Hy ND].
destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x ND H1 H2)].
Qed.

(* ------------------------------------------------------------------ the contract *)
(* check_no_loss' contract (gmc, cnl_go, cnl_cost, CNL_FRAME, CNL_STK, cnl_post, cnl_spec, cnl_objs_apart, cnl_ro,
   and A_g_s) lives in W_contract.v Section w3n, so mkbkit.py (sha256 999741ae2b33; internal record) twins it into lib/B (B's measured frame and
   stack bound come in as the cfg's b_facts).  The uses below pass this file's B, MT, G and MMAX explicitly. *)
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): check_no_loss over any allocator relation
   ARx with its laws, stated as W_contract_x.cnl_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl /
   LAWS (the generic relation), HP0 (the unit's hidden-head set is empty in every ARx state: a Theorem Labs lane's ruling, so the
   heap-block shadow facts are W_journal_x's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x), and
   IMGC / BLKN (W_kit_x.v Section g, for blk_off_imgP_x), and HPST (no image byte in PST: the generic journal's image
   clause keeps a byte only outside PST; it holds at PST = []).  The callees are their generic twins. ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): cnl_spec_x's room record *)
Variable RP : roomp.
Variable G : list (Z * Z).
Variable MMAX : Z.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
(* No gx_rt of the caller's G: G_fr / G_SL hold errno, so it could never be discharged (W5, 2026-10-29). *)
Hypothesis CNLAP : cnl_objs_apart.
Hypothesis ML : ameter_laws MT.
Hypothesis HGR : gx_ok SEGS B cnl_ro.
Hypothesis HGRR : gx_rt B cnl_ro.
(* An image read-only byte is not errno, and, if the runtime owns it, it is pinned to its image value (rom_pinned,
   W_journal.v; owned .rodata ranges lie inside image A's read-only LOAD, so `~ owned` was false). *)
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
(* rom_out's fourth clause: the sink's overflow head (.bss, 0x5f9b68) is no read-only byte (at PB_fr:
   W_rom_place_fr.v ofl_head_rom_fr). With ROMNS and CNLAP's g_s clause it gives rom_out at gesture_model's G
   (W_rom_place.v cnl_g_rom_out), which gm_spec_g now asks. *)
Hypothesis ROMOH : forall a, in_rom SEGS a -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis GM : gm_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the free's caller context: at the free (0x85abc) s0 = HA + 72 is no stack address, so chain_pre's chain is [] and
   the context is the singleton [ra], ra = 0x85ac0 = check_no_loss + 0x168 (fuzz_reply.objdump) *)
Hypothesis HCTX_cnl_free : In [BASE + AF_fr_check_no_loss + 0x168] CTX_AFREE.
(* W1's representation step of list_drop (lib/A/W_list_drop.v alist_at_drop, Qed on a working branch), verbatim. *)
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
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* ------------------------------------------------------------------ one placement of the out-parameter window *)
Section d.
Variable XO : Z. Variable AT : Z.
Let RUN := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* The source's address: g_s[j], 8-aligned, in the image, apart from the objects the walk reads. *)
Lemma cnl_ha : forall HA (j : nat), HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) ->
0x10000 <= HA /\ HA + 96 <= 0x5fb000 /\ HA mod 8 = 0 /\ HA mod 16 = 0 /\
(VAL A_g_gone + 1 <= HA + 64 \/ HA + 96 <= VAL A_g_gone) /\
(VAL (A_OBJ 0) + 8 <= HA + 64 \/ HA + 96 <= VAL (A_OBJ 0)) /\ (VAL (A_OBJ 32) + 8 <= HA + 64 \/ HA + 96 <= VAL (A_OBJ 32)).
Proof.
intros HA j EHA Hj HGa.
pose proof CNLAP as (A16 & A1 & _ & _ & A4 & A5 & _). cbv zeta in A16, A1, A4, A5.
pose proof (pa_obj_img 22 ltac:(lia)) as Hs. change (A_OBJ 22) with A_g_s in Hs.
pose proof (pa_img_range (HA + 95) (proj1 (HG (HA + 95) (HGa (HA + 95) ltac:(lia))))) as Hi.
assert (Hm : HA mod 16 = 0).
{ rewrite EHA. unfold ASRC. rewrite Z.add_mod, A16 by lia. cbn [Z.add].
  replace (96 * Z.of_nat j) with ((6 * Z.of_nat j) * 16) by lia. rewrite Z_mod_mult. reflexivity. }
assert (Hm8 : HA mod 8 = 0).
{ apply Z.mod_divide in Hm; [|lia]. apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hm]. }
unfold ASRC in EHA. split; [lia|]. split; [lia|]. split; [exact Hm8|]. split; [exact Hm|].
split; [destruct A1; lia|]. split; [destruct A4; lia | destruct A5; lia].
Qed.
(* What AR says of a live block, in the form the walk uses. *)
Lemma cnl_blk : forall ly S {hp : list Z} W mem md p n, ARx ly S hp W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ 0 <= n /\ n <= req_size n /\ 1 <= req_size n /\ p + req_size n <= alloc_ceiling /\
alloc_ceiling <= 0x7fffff800000 /\ off_img p (req_size n) /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S hp W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpr & _).
pose proof (BLKN ly S hp W mem md p n HAR Hin) as Hn.
pose proof (req_size_pos n ltac:(lia)) as [R1 R2]. pose proof asan_consts as (C1 & _).
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p n HAR Hin) as Hoff.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hoff|]. split; [exact Hia|]. exact Hpr.
Qed.
(* alist_at at a list given by its four fields, with the projections already taken: the walk reads the
   expected list in this shape at every step, and conversion alone does not simplify `hl_v (HL ...)`
   inside a hypothesis. *)
Lemma cnl_alist_parts : forall ly S W mem LA v cap recs junk lines,
alist_at B ly S W mem LA (HL v cap recs junk) lines ->
val_mem SEGS (arm W mem) LA 8 v /\ val_mem SEGS (arm W mem) (LA + 8) 4 (Z.of_nat (length recs)) /\
val_mem SEGS (arm W mem) (LA + 12) 4 cap /\ awr W mem LA 16 /\
Z.of_nat (length recs) <= cap < 2 ^ 30 /\
((cap = 0 /\ v = 0) \/
 (0 < cap /\ In (v, AREC * cap) (ablocks B ly S) /\
  Z.of_nat (length junk) = AREC * (cap - Z.of_nat (length recs)) /\
  garr8 SEGS (arm W mem) v (bzs (concat (map HarnessRep.text_rec recs) ++ junk)))) /\
NoDup (map fst recs) /\ ~ In v (map fst recs) /\
Forall (fun rr =>
  In (fst rr, Z.of_nat (length (snd rr)) + 1) (ablocks B ly S) /\
  garr8 SEGS (arm W mem) (fst rr) (bzs (snd rr ++ [Z_to_bv 8 0])) /\
  (lines = true -> ~ In (Z_to_bv 8 0) (snd rr) /\ Z.of_nat (length (snd rr)) <= APARTIAL) /\
  (lines = false -> (1 <= length (snd rr))%nat)) recs.
Proof. intros ly S W mem LA v cap recs junk lines H. exact H. Qed.
(* every block a list owns starts above the null page, so a walk whose footprint is those blocks never
   holds the sink's overflow head: the journal's image clause has no side condition for it *)
Lemma cnl_blks_pos : forall ly S {hp : list Z} W mem md LA l lines,
ARx ly S hp W mem md -> alist_at B ly S W mem LA l lines -> Forall (fun b => 0 < fst b) (list_blks l).
Proof.
intros ly S hp W mem md LA l lines HAR HL0. apply Forall_forall. intros x Hx.
unfold list_blks in Hx. apply in_app_or in Hx as [Hx | Hx].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hx|]. destruct Hx as [<- | []].
  destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _);
  [exfalso; rewrite Hc in Ec; discriminate|].
  cbn [fst]. destruct (cnl_blk ly S W mem md _ _ HAR Hin) as (_ & H4 & _). lia.
- apply in_map_iff in Hx as (y & <- & Hy).
  destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. destruct (HF y Hy) as (Hin & _).
  cbn [fst]. destruct (cnl_blk ly S W mem md _ _ HAR Hin) as (_ & H4 & _). lia.
Qed.
Lemma cnl_fps : forall bs, Forall (fun b => 0 < fst b) bs -> forall a, fp_spares (blk_FP bs) a.
Proof.
intros bs HF a. apply fp_spares_closed. unfold blk_FP.
exact (sink_closed_ablocks_fp bs HF).
Qed.
(* the meter's cost of a run of records is never negative *)
Lemma capstep_nonneg : forall T l cap, 0 <= cap -> 0 <= capstep T l cap.
Proof.
intros T l cap Hc. unfold capstep, grow_cap.
destruct (Nat.ltb (length T) (length (RelayModel.upd T l))); [|lia].
destruct (Z.of_nat (length T) =? cap); [destruct (cap =? 0)|]; lia.
Qed.
Lemma cnl_go_nonneg : forall rsx T cap, 0 <= cap -> 0 <= cnl_go MT T cap rsx.
Proof.
induction rsx as [|x rsx IH]; intros T cap Hc; [cbn [cnl_go]; lia|].
cbn [cnl_go].
pose proof (mo_free_nonneg MT ML) as Hf.
pose proof (IH (RelayModel.upd T (bzs (snd x))) (capstep T (bzs (snd x)) cap) (capstep_nonneg T (bzs (snd x)) cap Hc)) as Hrec.
assert (Hg : 0 <= gmc MT T cap (snd x)).
{ unfold gmc. destruct (RelayModel.gesture (bzs (snd x))) as [[[|] y]|]; cbv beta iota; [| |lia].
  - destruct (existsb (RelayModel.list_eqb y) T); [lia|].
    pose proof (mo_malloc_nonneg MT ML (Z.of_nat (length y) + 1) ltac:(pose proof (Nat2Z.is_nonneg (length y)); lia)) as Hm1.
    destruct (Z.of_nat (length T) =? cap); [|lia].
    pose proof (mo_malloc_nonneg MT ML (AREC * grow_cap (Z.of_nat (length T)) cap)
      ltac:(unfold grow_cap, AREC; destruct (Z.of_nat (length T) =? cap); [destruct (cap =? 0)|]; lia)) as Hm2.
    lia.
  - destruct (existsb (RelayModel.list_eqb y) T); lia. }
lia.
Qed.
(* the entry 0x85958: the frame, the GOT slot and the shadow cell, and s->expected's head (v at +64, n at +72) *)
Definition Bx : sv := SOff 32 0.
Definition cnl_head : YP09.region :=
YP09.mkRegion (Some 10%nat) 64 80 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 4 (SOff 34 0))].
Definition cnl_regions : smem := [ stack_region CNL_FRAME; got_regionP; bcell_regionP 32; cnl_head ].
Definition cnl_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 0x5fb000 4); (32%nat, mkAF SB SB 0);
(33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_cnl : sstate := mkSS A_check_no_loss sr_atoms cnl_regions None cnl_facts.
Definition cnl_SH : list shent := [ mkSHE 10 64 80 ].
Definition cnl_extra (v n : Z) : list word := map (Z_to_bv 64) [SB; v; n].
Lemma cnl_entry : forall W ly S {hp : list Z} regs mem md ch HA (j : nat) E,
afn_pre_x SEGS B ARx CNL_STK ly S hp W regs mem md ch ->
getr regs 10 = w64 HA -> HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
alist_at B ly S W mem (HA + 64) E true -> hl_n E < 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cnl_extra (hl_v E) (hl_n E)))) ss_cnl
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_no_lossP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx cnl_SH (Eimg (Ereg regs (cnl_extra (hl_v E) (hl_n E)))) (mrestrict (w_H W) mem).
Proof.
intros W ly S hp regs mem md ch HA j E HPRE H10 EHA Hj HGa Hzs HE HnE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16656) by reflexivity.
destruct (cnl_ha HA j EHA Hj HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
destruct (alx_const _ _ _ LAWS ly S hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof HE as (Mv & Mn & _ & _ & (Hnc & _) & _).
assert (Rv : 0 <= hl_v E < 2 ^ 64).
{ destruct HE as (_ & _ & _ & _ & _ & [(_ & ->) | (_ & Hin & _)] & _); [lia|].
  destruct (cnl_blk ly S W mem md _ _ HAR Hin) as (_ & H4096 & _ & _ & Hr1 & Hc & CC & _). lia. }
assert (Rn : 0 <= hl_n E) by (unfold hl_n; lia).
rewrite restrict_mkst_fx.
set (Ev := Eimg (Ereg regs (cnl_extra (hl_v E) (hl_n E)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew Ev 2 = getr regs 2) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew Ev 10 = Z_to_bv 64 HA) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew Ev 32 = Z_to_bv 64 SB) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v E)) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew Ev 34 = Z_to_bv 64 (hl_n E)) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO : forall i, (i < 33)%nat -> ew Ev (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst Ev; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew Ev m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val Ev (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (VBO : forall i, (i < 33)%nat -> base_val Ev (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | exact (pa_val_range _)]. }
split.
- unfold ss_cnl, A_check_no_lossP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cnl_regions, stack_region, got_regionP, bcell_regionP, cnl_head.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. unfold CNL_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VBO 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS Ev _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite (EO 32%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VBO 32%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS Ev _ (VAL (A_OBJ 32)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat HA E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS Ev _ HA 64 8 (SOff 33 0) (hl_v E));
   [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
-- apply (chunk_ok_val SEGS Ev _ HA 72 4 (SOff 34 0) (hl_n E));
   [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
   replace (HA + 72) with (HA + 64 + 8) by lia. exact Mn.
+ apply pairwise_disjoint_of_extents. unfold cnl_regions, stack_region, got_regionP, bcell_regionP, cnl_head, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VBO 0%nat ltac:(lia)), (VBO 32%nat ltac:(lia)), (VB 10%nat HA E10) by lia. cbn [base_val]. rewrite Usp.
unfold CNL_FRAME. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HAlo HAhi Dgot Dcell. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cnl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HAlo HAhi HA16 Rv Rn HnE. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cnl_SH. constructor; [|constructor].
eapply shent_ok_of_range.
+ apply (azs_range_addressable_x B ARx LAWS ly S hp W mem md (HA + 64) 32 HAR Hzs).
+ unfold Bx. rewrite (U_atom Ev 32 SB E32) by (unfold SB; lia). reflexivity.
+ rewrite (U_atom Ev 10 HA E10) by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
(* the loop head 0x859dc and the return point 0x85a9c of gesture_model: s1 = s, s0 = s + 72, s3 = s + 64, s2 = at,
   s6 = SB, s7 / s10 the shadow cells of s + 72 / s + 64, s8 = the hi page of g_gone, s9 = 3, s11 = 1; the frame
   holds the caller's ra and s0..s11 at sp + 24 .. sp + 128 *)
Definition A_cnl_loop : Z := AF_fr_check_no_loss + 0x84.
Definition A_cnl_back : Z := AF_fr_check_no_loss + 0x144.
Definition BxL : sv := SOff 22 0.
Definition cnl_sr : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff 9 72)) 19 (SOff 9 64))
  23 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 72) (SLit 3)) (SOff 22 0)))
  24 (SOff (A_HI 106) 0)) 25 (SLit 3)) 26 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 64) (SLit 3)) (SOff 22 0))) 27 (SLit 1).
Definition cnl_saved : YP09.region := YP09.mkRegion (Some 2%nat) 24 128 0 0
[YP09.mkChunk 24 (CVal 8 (SOff 37 0)); YP09.mkChunk 32 (CVal 8 (SOff 38 0)); YP09.mkChunk 40 (CVal 8 (SOff 39 0));
 YP09.mkChunk 48 (CVal 8 (SOff 40 0)); YP09.mkChunk 56 (CVal 8 (SOff 41 0)); YP09.mkChunk 64 (CVal 8 (SOff 42 0));
 YP09.mkChunk 72 (CVal 8 (SOff 43 0)); YP09.mkChunk 80 (CVal 8 (SOff 44 0)); YP09.mkChunk 88 (CVal 8 (SOff 45 0));
 YP09.mkChunk 96 (CVal 8 (SOff 46 0)); YP09.mkChunk 104 (CVal 8 (SOff 47 0)); YP09.mkChunk 112 (CVal 8 (SOff 48 0));
 YP09.mkChunk 120 (CVal 8 (SOff 49 0))].
Definition cnl_gone : YP09.region := YP09.mkRegion (Some A_g_gone) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition cnl_headL : YP09.region :=
YP09.mkRegion (Some 9%nat) 64 80 72 76 [YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 4 (SOff 34 0))].
Definition cnl_vec : YP09.region :=
YP09.mkRegion (Some 33%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0))].
Definition cnl_lregions : smem := [ cnl_saved; cnl_gone; cnl_headL; cnl_vec ].
Definition cnl_lfacts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0x10000 0x5fb000 4); (22%nat, mkAF SB SB 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 0x7fffff800000 4); (34%nat, mkAF 1 (2 ^ 26) 0);
(35%nat, mkAF 4096 0x7fffff800000 4); (36%nat, mkAF 0 6000 0) ] [] [].
Definition ss_cnll (pc : Z) : sstate := mkSS pc cnl_sr cnl_lregions None cnl_lfacts.
Definition cnl_lSH : list shent := [ mkSHE 9 64 80; mkSHE 33 0 16 ].
(* The caller's ra and s0..s11, as the prologue saved them at sp + 24 .. sp + 128 (sp the loop's sp). *)
Definition CNL_SAVED : list (bv 5) := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition cnl_svals (regs0 : bvmap 5 word) : list Z := map (fun r => bv_unsigned (getr regs0 r)) CNL_SAVED.
Definition cnl_frame_ok (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall i, (i < 13)%nat -> val_mem SEGS (arm W mem) (sp0 - 104 + 8 * Z.of_nat i) 8 (nth i (cnl_svals regs0) 0).
(* The loop's registers (sp0 the entry sp). *)
Definition cnl_regs_ok (regs : bvmap 5 word) (sp0 HA : Z) : Prop :=
getr regs 2 = w64 (sp0 - 128) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (HA + 72) /\ getr regs 9 = w64 HA /\ getr regs 18 = w64 AT /\ getr regs 19 = w64 (HA + 64) /\
getr regs 22 = w64 SB /\ getr regs 23 = w64 ((HA + 72) / 8 + SB) /\ getr regs 24 = w64 (VAL (A_HI 106)) /\
getr regs 25 = w64 3 /\ getr regs 26 = w64 ((HA + 64) / 8 + SB) /\ getr regs 27 = w64 1.
Definition cnl_lx (gone v n s0 n0 : Z) (sv : list Z) : list word := map (Z_to_bv 64) ([gone; v; n; s0; n0] ++ sv).
Lemma U_shadow_reg : forall E m bx c x, ew E m = Z_to_bv 64 x -> ew E bx = Z_to_bv 64 SB -> 0 <= x < 2 ^ 63 -> x + c < 2 ^ 63 -> 0 <= x + c ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff bx 0)) = Z_to_bv 64 ((x + c) / 8 + SB).
Proof.
intros E m bx c x Hm H22 Hx Hc Hc0. apply bv_eq.
fold (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff bx 0))).
rewrite !U_SAlu, (U_atom_off E m x c Hm) by lia. rewrite (U_atom E bx SB H22) by (unfold SB; lia). rewrite U_lit by lia.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
assert (D : 0 <= (x + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite Z.mod_small by (unfold SB; lia). reflexivity.
Qed.
Lemma cnl_chunk_saved : forall E (m : word -> option byte) base sp0 regs0 k (o : Z),
(37 <= k < 50)%nat -> o = 24 + 8 * (Z.of_nat k - 37) -> base = sp0 - 128 ->
ew E k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0) ->
(forall i, (i < 13)%nat -> val_mem SEGS m (sp0 - 104 + 8 * Z.of_nat i) 8 (nth i (cnl_svals regs0) 0)) ->
YP09.chunk_ok SEGS E m base (YP09.mkChunk o (CVal 8 (SOff k 0))).
Proof.
intros E m base sp0 regs0 k o Hk -> -> Hek Hf.
assert (Hr : 0 <= nth (k - 37) (cnl_svals regs0) 0 < 2 ^ 64).
{ unfold cnl_svals. destruct (Nat.lt_ge_cases (k - 37) (length (map (fun r => bv_unsigned (getr regs0 r)) CNL_SAVED))) as [Hl|Hl].
  - pose proof (nth_In _ 0 Hl) as Hin. apply in_map_iff in Hin as (r & <- & _). apply bv_unsigned_in_range.
  - rewrite nth_overflow by exact Hl. lia. }
apply (chunk_ok_val SEGS E m (sp0 - 128) (24 + 8 * (Z.of_nat k - 37)) 8 (SOff k 0) (nth (k - 37) (cnl_svals regs0) 0));
[cbn [sv_denot]; rewrite Hek, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hr | lia |].
replace (sp0 - 128 + (24 + 8 * (Z.of_nat k - 37))) with (sp0 - 104 + 8 * Z.of_nat (k - 37)) by lia.
apply Hf. lia.
Qed.
(* The loop's symbolic state at pc (the head, or the return point of gesture_model), from the facts the loop keeps. *)
Lemma cnl_mk : forall pc W ly S {hp : list Z} mem md regs regs0 HA gone v n s0 n0 N0,
ARx ly S hp W mem md ->
cnl_regs_ok regs (spZ regs0) HA ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + 128 <= spZ regs0 <= 2 ^ 47 ->
0x10000 <= HA -> HA + 96 <= 0x5fb000 -> HA mod 16 = 0 -> (VAL A_g_gone + 1 <= HA + 64 \/ HA + 96 <= VAL A_g_gone) ->
azs B (HA + 64) 32 -> awr W mem (HA + 64) 16 ->
cnl_frame_ok W mem (spZ regs0) regs0 ->
val_mem SEGS (arm W mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (arm W mem) (HA + 64) 8 v -> val_mem SEGS (arm W mem) (HA + 72) 4 n -> 1 <= n <= 2 ^ 26 ->
In (v, N0) (ablocks B ly S) -> 16 <= req_size N0 ->
val_mem SEGS (arm W mem) v 8 s0 -> val_mem SEGS (arm W mem) (v + 8) 8 n0 ->
4096 <= s0 <= 0x7fffff800000 -> s0 mod 16 = 0 -> 0 <= n0 <= 6000 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cnl_lx gone v n s0 n0 (cnl_svals regs0)))) (ss_cnll pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS BxL cnl_lSH (Eimg (Ereg regs (cnl_lx gone v n s0 n0 (cnl_svals regs0)))) (mrestrict (w_H W) mem).
Proof.
intros pc W ly S hp mem md regs regs0 HA gone v n s0 n0 N0 HAR HR Hal Hsp HAlo HAhi HA16 Dgn Hzs Hwn Hfr Mg Rg Mv Mn Rn
Hvin Hv16 Ms0 Mn0 Rs0 Hs016 Rn0.
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (cnl_blk ly S W mem md v N0 HAR Hvin) as (Hv0 & Hv4096 & _ & _ & Hvr1 & Hvc & _ & Hvoff & Hvapp & _).
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
rewrite restrict_mkst_fx.
set (Ev := Eimg (Ereg regs (cnl_lx gone v n s0 n0 (cnl_svals regs0)))). pose proof pa_B_ok as HBASE.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs rr).
{ intros m rr Hm. subst Ev. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 18)%nat -> ew Ev (32 + j) = nth j (cnl_lx gone v n s0 n0 (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros j Hj. subst Ev. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (spZ regs0 - 128)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E32 : ew Ev 32 = Z_to_bv 64 gone) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew Ev 33 = Z_to_bv 64 v) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew Ev 34 = Z_to_bv 64 n) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 s0) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew Ev 36 = Z_to_bv 64 n0) by exact (EX 4%nat ltac:(lia)).
assert (ES : forall k, (37 <= k < 50)%nat -> ew Ev k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0)).
{ intros k Hk. assert (Ek : k = (32 + (5 + (k - 37)))%nat) by lia. rewrite Ek at 1.
  rewrite (EX (5 + (k - 37))%nat ltac:(lia)). unfold cnl_lx. rewrite map_app. cbn [map app nth Nat.add].
  apply map_nth. }
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (subst Ev; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall m w, ew Ev m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val Ev (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Hsp2 : base_val Ev (Some 2%nat) = spZ regs0 - 128) by (apply VB; [exact E2 | lia]).
assert (Hsp9 : base_val Ev (Some 9%nat) = HA) by (apply VB; [exact E9 | lia]).
assert (Hsp33 : base_val Ev (Some 33%nat) = v) by (apply VB; [exact E33 | lia]).
assert (Hspg : base_val Ev (Some A_g_gone) = VAL A_g_gone) by (apply VB; [exact Eg | exact (pa_val_range _)]).
split.
- unfold ss_cnll. apply pa_entry_st_ok_full.
  + unfold cnl_sr.
    apply regs_ok_pin; [| discriminate | rewrite R27; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R26, (U_shadow_reg Ev 9 22 64 HA E9 E22) by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R25; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R24; cbn [sv_denot]; subst Ev; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia);
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R23, (U_shadow_reg Ev 9 22 72 HA E9 E22) by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R19; cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R8; cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
    apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cnl_lregions, cnl_saved, cnl_gone, cnl_headL, cnl_vec.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite Hsp2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CVal 8 (SOff ?k 0))) =>
        apply (cnl_chunk_saved Ev _ _ (spZ regs0) regs0 k); [lia | reflexivity | reflexivity | apply ES; lia | exact Hfr] end.
    * rewrite Hspg. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS Ev _ (VAL A_g_gone) 0 1 (SOff 32 0) gone);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Mg.
    * rewrite Hsp9. split; [lia|]. split; [lia|]. split.
      { intros o Ho. unfold awr, arm in Hwn. replace (HA + o) with (HA + 64 + (o - 64)) by lia. exact (Hwn (o - 64) ltac:(lia)). }
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS Ev _ HA 64 8 (SOff 33 0) v);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
      -- apply (chunk_ok_val SEGS Ev _ HA 72 4 (SOff 34 0) n);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
    * rewrite Hsp33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS Ev _ v 0 8 (SOff 35 0) s0);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Ms0.
      -- apply (chunk_ok_val SEGS Ev _ v 8 8 (SOff 36 0) n0);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn0].
  + apply pairwise_disjoint_of_extents. unfold cnl_lregions, cnl_saved, cnl_gone, cnl_headL, cnl_vec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Hsp2, Hspg, Hsp9, Hsp33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsp C1 HgR HAlo HAhi Dgn Hv4096 Hvc Hvr1 Hv16 Hvoff. clear.
    unfold off_img. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cnl_lfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E22, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hsp16 : (spZ regs0 - 128) mod 16 = 0).
    { rewrite Zminus_mod, Hal. reflexivity. }
    revert Hsp C1 Hsp16 HAlo HAhi HA16 Rg Hv4096 Hvc Hvr1 Hv0 Rn Rs0 Hs016 Rn0. clear.
    unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
  + eapply shent_ok_of_range.
    * apply (azs_range_addressable_x B ARx LAWS ly S hp W mem md (HA + 64) 32 HAR Hzs).
    * unfold BxL. rewrite (U_atom Ev 22 SB E22) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom Ev 9 HA E9) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold SHADOW_OFF in *. lia.
  + eapply shent_ok_of_range.
    * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem md v N0 v 16 HAR Hvin); lia.
    * unfold BxL. rewrite (U_atom Ev 22 SB E22) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom Ev 33 v E33) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
(* the free of a block, lifted from the allocator parameter's rule to the walk's journal at any out-parameter window
   (W1's aj_free_gx, lib/A/W_list_drop.v on a working branch, is the XO = 0 case) *)
Lemma cnl_free_gx : forall XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb (o : Z) raw ch
  (kr : nat),
ajournal_gx_x SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own lyc Sc hpc W memT mdc k -> XO1 mod 16 = 0 ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch -> In (raZ regsT :: spine ch) CTX_AFREE ->
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
(* the source with its expected list replaced: the rest of its bytes kept, its other blocks still live *)
Lemma cnl_src_set : forall ly1 S1 W1 mem1 ly2 S2 W2 mem2 HA1 h1 e',
asrc_at B ly1 S1 W1 mem1 HA1 h1 ->
(forall x, HA1 <= x < HA1 + 64 \/ HA1 + 80 <= x < HA1 + 96 -> abyte_kept W1 mem1 W2 mem2 x) ->
akept W1 mem1 W2 mem2 (gfp (hs_partial h1) (bzs (hs_pjunk h1)) ::
  alist_fp (HA1 + 16) (hs_pending h1) ++ alist_fp (HA1 + 80) (hs_held h1)) ->
(forall b, In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks (hs_held h1)) ->
  In b (ablocks B ly2 S2)) ->
alist_at B ly2 S2 W2 mem2 (HA1 + 64) e' true ->
NoDup (hs_blocks (set_exp_held h1 e' (hs_held h1))) ->
asrc_at B ly2 S2 W2 mem2 HA1 (set_exp_held h1 e' (hs_held h1)).
Proof.
intros ly1 S1 W1 mem1 ly2 S2 W2 mem2 HA1 h1 e'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
   H21 & H22 & H23 & H24) KH HK HB HE ND.
assert (Hvm : forall a n v, HA1 <= a -> a + Z.of_nat n <= HA1 + 64 ->
  val_mem SEGS (arm W1 mem1) a n v -> val_mem SEGS (arm W2 mem2) a n v)
  by (intros a n v Ha Hn Hv; apply (akept_vm W1 mem1); [intros x Hx; apply KH; lia | exact Hv]).
split; [apply Hvm; [lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | exact H3]|].
split; [apply Hvm; [lia | cbn; lia | exact H4]|].
split.
{ intros i Hi. unfold ASRC in Hi.
  destruct (Z_lt_le_dec i 64) as [Hi1 | Hi1]; [apply (proj2 (KH (HA1 + i) ltac:(lia))); exact (H5 i ltac:(unfold ASRC; lia))|].
  destruct (Z_lt_le_dec i 80) as [Hi2 | Hi2]; [|apply (proj2 (KH (HA1 + i) ltac:(lia))); exact (H5 i ltac:(unfold ASRC; lia))].
  destruct HE as (_ & _ & _ & Hw & _). replace (HA1 + i) with (HA1 + 64 + (i - 64)) by lia. exact (Hw (i - 64) ltac:(lia)). }
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (alist_at_kept B ly1 S1 W1 mem1); [exact H10
  | eapply akept_sub; [exact HK | intros rr Hr; right; apply in_or_app; left; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; left; exact Hb]|].
split; [apply Hvm; [lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|].
split; [apply HB; left; reflexivity|].
split; [exact H19|].
split; [apply (akept_garr8 W1 mem1); [intros x Hx; apply (HK (gfp (hs_partial h1) (bzs (hs_pjunk h1))));
  [left; reflexivity | exact Hx] | exact H20]|].
split; [exact H21|].
split; [exact HE|].
split; [apply (alist_at_kept B ly1 S1 W1 mem1); [exact H23
  | eapply akept_sub; [exact HK | intros rr Hr; right; apply in_or_app; right; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; right; exact Hb]|].
exact ND.
Qed.
(* the bytes a list's predicate reads are kept when its head is and every block of it is *)
Lemma cnl_list_kept : forall ly1 S1 {hp1 : list Z} W1 m1 md1 W2 m2 LA l lines (P : Z -> Prop),
ARx ly1 S1 hp1 W1 m1 md1 -> alist_at B ly1 S1 W1 m1 LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (ablocks B ly1 S1) -> P b -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
(forall b, In b (list_blocks l) -> P b) ->
akept W1 m1 W2 m2 (alist_fp LA l).
Proof.
intros ly1 S1 hp1 W1 m1 md1 W2 m2 LA l lines P HAR HL KH KB HP rr Hr a Ha.
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [apply KH; exact Ha|].
apply in_app_or in Hr as [Hr | Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
  destruct HL as (_ & _ & _ & _ & _ & [(Hc & _) | (Hc & Hin & Hj & _)] & _); [apply Z.eqb_neq in Ec; lia|].
  destruct (cnl_blk ly1 S1 W1 m1 md1 _ _ HAR Hin) as (_ & _ & _ & Hn1 & _).
  apply (KB _ _ a Hin).
  + apply HP. unfold list_blocks. rewrite Ec. left. reflexivity.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, cnl_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul in Ha.
    change (Z.of_nat 16) with 16 in Ha. unfold hl_n in Hj. unfold AREC in *. lia.
- apply in_map_iff in Hr as (x & <- & Hx).
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF x Hx) as (Hin & _).
  destruct (cnl_blk ly1 S1 W1 m1 md1 _ _ HAR Hin) as (_ & _ & _ & Hn1 & _).
  apply (KB _ _ a Hin).
  + apply HP. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hx.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha. lia.
Qed.
(* after the free only the head s->expected is shadow-checked *)
Definition cnl_dSH : list shent := [ mkSHE 9 64 80 ].
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sections 0, 4, 5): the two call steps of the loop at a world relation R, for the loop's
   R twins below.  The journal ajournal_gx_x becomes ajournal_gx_xR R and SRr SEGS becomes SRrG SEGS R.  The free goes
   through the R form of the allocator's rule (W_journal_x.v Section hc afree_cf_rule_c_xR), which also takes the
   call-boundary premise RO on the call memory (part 3c removed its memnorm premise): RO_ARx gives it from the inner
   journal's ARx at the call state.  bcmp's contract stays strict (W_sites_x.v abcmp_realizes_x): its entry is
   W_sites_x.v's aj_gx_entry_at_xR, which lifts it by SRr_SRrG (WLE_R).  The strict cnl_free_gx above keeps its proof.
   ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* a strict gx journal (a strict callee's post journal) is one at R (W_journal_x.v ajournal_gx_xR_mono, WLE_R) *)
Lemma cnl_gx_lift_xR {Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq} :
ajournal_gx_x SEGS B PST ARx Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq ->
ajournal_gx_xR SEGS B PST ARx R Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq.
Proof. intros HJ. eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ]. Qed.
(* cnl_free_gx at R: the rule is AFREE_R, with RO at the call memory *)
Lemma cnl_free_gx_xR : forall XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb (o : Z) raw ch
  (kr : nat),
ajournal_gx_xR SEGS B PST ARx R G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own lyc Sc hpc W memT mdc k -> XO1 mod 16 = 0 ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch -> In (raZ regsT :: spine ch) CTX_AFREE ->
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
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
(* the call-boundary premise of the R rule, at the call state (the inner journal's ARx) *)
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
assert (Hal' : (o - XO1) mod 16 = 0) by (rewrite Zminus_mod, Hal, HX; reflexivity).
eapply SRrG_mono.
{ exact (AFREE_R W regsT memT (STK + XO1) (sp0 + XO1) FP ly S hp W0 memS md own lyc Sc hpc mdc k pa nb (o - XO1) raw ch kr
  HJi Hin Ha0 ltac:(lia) Hal' ltac:(lia) ltac:(lia)
  (* the stack room below the call (ACALL_PREFIX), from the journal's astk_ok *)
  (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o - XO1) regsT HJi ltac:(lia) ltac:(lia))
  Hgp Htp Hra Hraw Hch HRO Hctx HRM HCNT Hfp Hmo). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs & HK & Hle & HRM2 & Herr & Hpr).
replace (sp0 + XO1 + (o - XO1) - ASTACK) with (sp0 + o - ASTACK) in HK by lia.
replace (sp0 + XO1 + (o - XO1)) with (sp0 + o) in HK by lia.
exists ly2, S2, hp2, regs2, mem2, md2. split; [reflexivity|].
split; [|split; [exact HP2 | split; [exact Hbl | split; [exact Hfrs | split; [exact HK |
  split; [exact Hle | split; [exact HRM2 | split; [exact Herr | exact Hpr]]]]]]]].
apply (ajournal_gx_pack_xR SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply (proj1 HK); lia.
Qed.
End wR.
(* ------------------------------------------------------------------ the loop *)
Section loop.
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (HA : Z) (j : nat) (h : hsrc) (gone A0 NO OUT CO : Z) (ob : list byte).
(* the room round: the caller's room budget past this call (cnl_post_x's kr) *)
Variable kr : nat.
Local Notation EE := (hs_expected h).
Local Notation HH := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_expected h) ++ list_blks (hs_held h))).
Local Notation Post := (cnl_post_x B PST ARx MT RP G regs0 ly S hp W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
(* What the loop's two halves need of the entry: exactly the premises of cnl_spec that do not move, so the
   main theorem discharges them once before it takes cnl_loop. *)
Hypothesis APRE : afn_pre_x SEGS B ARx CNL_STK ly S hp W regs0 mem md ch.
Hypothesis AX0 : 0 <= XO.
Hypothesis AX16 : XO mod 16 = 0.
Hypothesis AXTOP : sp0 + XO <= ly_top ly.
Hypothesis AXPRES : forall a, sp0 <= a < sp0 + XO -> apresent (w_H W) mem a.
Hypothesis AHAE : HA = VAL A_g_s + ASRC * Z.of_nat j.
Hypothesis AJLT : (j < 4)%nat.
Hypothesis AAT8 : AT mod 8 = 0.
Hypothesis AATL : sp0 <= AT.
Hypothesis AATH : AT + 8 <= sp0 + XO.
Hypothesis AGA : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis AZS : azs B (HA + 64) 32.
Hypothesis AEN : hl_n EE < 2 ^ 26.
Hypothesis AHN : hl_n HH + Z.of_nat (count_begin (texts EE)) < 2 ^ 22.
Hypothesis AA0 : 0 <= A0 <= NO.
Hypothesis AGN : 0 <= gone < 256.
Hypothesis AOBN : Z.of_nat (length ob) = NO.
Hypothesis ANO : NO <= 2 ^ 40.
Hypothesis ANO32 : 0 < NO -> NO < 2 ^ 32.
Hypothesis AMRO : amem_range OUT (NO + 8).
Hypothesis AC32 : AREC * capb HH EE < 2 ^ 32.
Hypothesis APERM : exists rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest).
(* the blocks a list and a source name are live blocks of the state they are read in *)
Lemma cnl_alist_blks_in : forall ly0 S0 W0 m0 LA l lines, alist_at B ly0 S0 W0 m0 LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 LA l lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
  destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. exact (proj1 (HF x Hx)).
Qed.
Lemma cnl_src_blks : forall ly0 S0 W0 m0 HA0 h0, asrc_at B ly0 S0 W0 m0 HA0 h0 ->
forall b, In b (asrc_blks h0) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 HA0 h0 HS0 b Hb.
pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPd & _ & _ & _ & _ & _ & _ & _ & HPin & _ & _ & _ & HEx & HHl & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact HPin|].
apply in_app_or in Hb as [Hb | Hb]; [exact (cnl_alist_blks_in _ _ _ _ _ _ _ HPd b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
[exact (cnl_alist_blks_in _ _ _ _ _ _ _ HEx b Hb) | exact (cnl_alist_blks_in _ _ _ _ _ _ _ HHl b Hb)].
Qed.
(* the expected list once its first records are gone: same vector, records rs, junk jk *)
Definition cnl_E (rs : list (Z * list byte)) (jk : list byte) : hlist := HL (hl_v EE) (hl_cap EE) rs jk.
(* what the loop keeps unchanged: g_gone, g_nout, g_out, the stream, the rom, gesture_model's literals *)
Definition cnl_consts (W1 : world SEGS) (mem1 : word -> option byte) : Prop :=
val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone /\ val_mem SEGS (arm W1 mem1) (VAL A_g_nout) 8 NO /\
val_mem SEGS (arm W1 mem1) (VAL A_g_out) 8 OUT /\ ob_at W1 mem1 OUT ob /\ rom_view SEGS W1 mem1 /\
garr8 SEGS (arm W1 mem1) (VAL A_lit_gesture) RelayModel.K_GESTURE /\
garr8 SEGS (arm W1 mem1) (VAL A_lit_begin) RelayModel.W_BEGIN /\
garr8 SEGS (arm W1 mem1) (VAL A_lit_end) RelayModel.W_END.
(* what the memory side of the invariant says, without the journal: it moves across a run that writes nothing *)
Definition cnl_pack (ly1 : alayout) (S1 : astate) (H1 e : hlist) (p : list (Z * list byte))
(W1 : world SEGS) (mem1 : word -> option byte) : Prop :=
apres_kept B W mem W1 mem1 /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h e H1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 p) /\ cnl_consts W1 mem1 /\ cnl_frame_ok W1 mem1 sp0 regs0.
(* the pack moves across a step that writes nothing new *)
Lemma cnl_pack_keep : forall ly1 S1 (H1 e : hlist) p (W1 : world SEGS) m1 m2,
cnl_pack ly1 S1 H1 e p W1 m1 ->
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
cnl_pack ly1 S1 H1 e p W1 m2.
Proof.
intros ly1 S1 H1 e p W1 m1 m2 (Hpk & Herr & Hsrc & Hat & Hcst & Hfrm) AEQ MG.
assert (AQ : forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a. rewrite (aview_wrap64 (w_H W1) m2 a), (aview_wrap64 (w_H W1) m1 a).
  apply AEQ. pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)). lia. }
assert (AK : forall a, abyte_kept W1 m1 W1 m2 a)
  by (intros a; split; [apply AQ | intros Hw; eapply writable_at_grows; [exact MG | exact Hw]]).
split; [intros a Hi Ho He Hp; exact (apresent_grows (w_H W1) m1 m2 a MG (Hpk a Hi Ho He Hp))|].
split; [intros j0 Hj0; rewrite AQ; exact (Herr j0 Hj0)|].
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 HA _ Hsrc);
  [intros rr _ a _; apply AK | intros b Hb; exact (cnl_src_blks ly1 S1 W1 m1 HA _ Hsrc b Hb)]. }
split; [apply (cnl_vm_keep W1 W1 m1 m2); [intros x _; apply AQ | exact Hat]|].
split.
{ destruct Hcst as (Cg & Cn & Co & Cb & Cr & Cl1 & Cl2 & Cl3).
  split; [apply (cnl_vm_keep W1 W1 m1 m2); [intros x _; apply AQ | exact Cg]|].
  split; [apply (cnl_vm_keep W1 W1 m1 m2); [intros x _; apply AQ | exact Cn]|].
  split; [apply (cnl_vm_keep W1 W1 m1 m2); [intros x _; apply AQ | exact Co]|].
  split; [apply (cnl_ob_keep W1 W1 m1 m2); [intros i _; apply AQ | exact Cb]|].
  split; [intros a Hr; rewrite AQ; exact (Cr a Hr)|].
  split; [apply (cnl_g8_keep W1 W1 m1 m2); [intros x _; apply AQ | exact Cl1]|].
  split; [apply (cnl_g8_keep W1 W1 m1 m2); [intros x _; apply AQ | exact Cl2]
        | apply (cnl_g8_keep W1 W1 m1 m2); [intros x _; apply AQ | exact Cl3]]. }
intros i Hi. apply (cnl_vm_keep W1 W1 m1 m2); [intros x _; apply AQ | exact (Hfrm i Hi)].
Qed.
(* the invariant at the loop head: pre consumed, rs left (the plain proof's CI_t, lib/Prog/check_no_loss.v:674) *)
Definition cnl_inv (pre rs : list (Z * list byte)) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte)
(md1 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ rs /\
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E rs jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs pre) /\ hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E rs jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) /\ mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) rs /\
(* the room round: the room budget (gesture_model's charge and one free per record left, past the caller's kr) and
   the live counts plus the peak of the trace still owed (W_cnl_cnt.v) *)
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr) /\ cnl_cnt RP rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 pre) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E rs jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 pre)) ob = bsr rs ++ rest) /\
cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 sp0 HA.
(* after gesture_model returned (0x85a9c): r is fed to the model, not yet dropped (the plain proof's J1_t) *)
Definition cnl_mid (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) (W1 : world SEGS)
(regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ r :: rs /\
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E (r :: rs) jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs (pre ++ [r])) /\
hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (pre ++ [r]) /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs (pre ++ [r]))) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) (pre ++ [r]) - mo_free MT) /\
mo_ok MT S1 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)) (texts H1) (hl_cap H1) rs /\
(* the room round: r's free is still owed, before the rest's budget; its free and the rest still owe the counts *)
rp_RM RP S1 (Datatypes.S (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr))%nat /\ cnl_cntm RP r rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 (pre ++ [r])) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) /\
cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 sp0 HA.
Definition cnl_midQ (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) :
world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1, c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1 /\
cnl_mid pre r rs W1 regs1 mem1 md1.
(* ---------------------------------------------- helpers of cnl_step (hand NLStep) *)
(* the stream's first line is r's text: the NUL-free prefix before the first NUL is unique *)
Lemma nls_nul_split : forall (e ln t rest : list byte),
e ++ Z_to_bv 8 0 :: t = ln ++ Z_to_bv 8 0 :: rest -> ~ In (Z_to_bv 8 0) e -> ~ In (Z_to_bv 8 0) ln -> ln = e.
Proof.
induction e as [|x e IH]; intros [|y ln] t rest Heq He Hl; cbn in Heq.
- reflexivity.
- injection Heq as Hy _. exfalso. apply Hl. left. symmetry. exact Hy.
- injection Heq as Hx _. exfalso. apply He. left. exact Hx.
- injection Heq as -> Heq. f_equal. apply (IH ln t rest Heq); intros Hin; [apply He | apply Hl]; right; exact Hin.
Qed.
(* facts about bytes nobody wrote carry over in the aview form *)
Lemma nls_vm_kept : forall (W2 W3 : world SEGS) (m2 m3 : word -> option byte) a n v,
(forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W3) m3 (a + i) = aview SEGS (w_H W2) m2 (a + i)) ->
val_mem SEGS (arm W2 m2) a n v -> val_mem SEGS (arm W3 m3) a n v.
Proof.
intros W2 W3 m2 m3 a n v Hk Hv k Hlt. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W2) (w_H W3) m2 m3); [apply Hv; exact Hlt|]. apply Hk. lia.
Qed.
Lemma nls_garr8_kept : forall (W2 W3 : world SEGS) (m2 m3 : word -> option byte) a l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W3) m3 (a + i) = aview SEGS (w_H W2) m2 (a + i)) ->
garr8 SEGS (arm W2 m2) a l -> garr8 SEGS (arm W3 m3) a l.
Proof.
intros W2 W3 m2 m3 a l Hk Hg. apply (garr8_frame SEGS (arm W2 m2) (arm W3 m3) a l Hg).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). replace x with (a + (x - a)) by lia. apply Hk. lia.
Qed.
Lemma nls_ob_kept : forall (W2 W3 : world SEGS) (m2 m3 : word -> option byte) x l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W3) m3 (x + i) = aview SEGS (w_H W2) m2 (x + i)) ->
ob_at W2 m2 x l -> ob_at W3 m3 x l.
Proof. intros W2 W3 m2 m3 x l Hk Hl i Hi. rewrite Hk by exact Hi. exact (Hl i Hi). Qed.
Lemma nls_shv_sub : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* presence composes, and a writable byte is a present one *)
Lemma nls_apk_trans : forall (Wa : world SEGS) ma (Wb : world SEGS) mb (Wc : world SEGS) mc,
apres_kept B Wa ma Wb mb -> apres_kept B Wb mb Wc mc -> apres_kept B Wa ma Wc mc.
Proof. intros Wa ma Wb mb Wc mc H1 H2 a Hi Ho He Hp. exact (H2 a Hi Ho He (H1 a Hi Ho He Hp)). Qed.
Lemma nls_apk_of_pres : forall (Wa : world SEGS) (ma mb : word -> option byte),
(forall a, apresent (w_H Wa) ma a -> apresent (w_H Wa) mb a) -> apres_kept B Wa ma Wa mb.
Proof. intros Wa ma mb H a _ _ _ Hp. exact (H a Hp). Qed.
(* a byte stays writable when it stays present: where it is not present, writability is the segment's *)
Lemma nls_awr_kept : forall (Wa Wb : world SEGS) (ma mb : word -> option byte) a,
(apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a) ->
writable_at SEGS (arm Wa ma) a -> writable_at SEGS (arm Wb mb) a.
Proof.
intros Wa Wb ma mb a Hp Hw. unfold writable_at, wview, arm, mrestrict in Hw |- *.
destruct (w_H Wb (Z_to_bv 64 a)) eqn:EHb.
- destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [Hh _]. rewrite EHb in Hh. discriminate.
- destruct (mb (Z_to_bv 64 a)) as [b2|] eqn:Emb; [discriminate|].
  destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [_ [b3 Hb3]]. rewrite Emb in Hb3. discriminate.
Qed.
(* the live blocks are pairwise apart (AR): as pairs and by their addresses, they are duplicate-free *)
Lemma nls_pw_nodup_fst : forall (l : list (Z * Z)), (forall b, In b l -> 0 <= snd b) ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup (map fst l).
Proof.
induction l as [|x l IH]; intros HF HP; [constructor|].
cbn [map] in HP |- *. destruct HP as [HAx HP].
assert (Rx : 1 <= req_size (snd x)) by (apply (req_size_pos (snd x)); apply HF; left; reflexivity).
constructor.
- intros Hin. apply in_map_iff in Hin as (y & Hy & Hyl).
  assert (Ry : 1 <= req_size (snd y)) by (apply (req_size_pos (snd y)); apply HF; right; exact Hyl).
  assert (Hin2 : In (fst y, req_size (snd y)) (map (fun b : Z * Z => (fst b, req_size (snd b))) l)).
  { apply in_map_iff. exists y. split; [reflexivity | exact Hyl]. }
  assert (Hd : zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)));
  [ first [ exact (proj1 (Forall_forall _ _) HAx _ Hin2) | exact (HAx _ Hin2) ]
  | unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia ].
- apply IH; [intros b Hb; apply HF; right; exact Hb | exact HP].
Qed.
Lemma nls_nodup_map : forall (A' B' : Type) (f : A' -> B') (l : list A'), List.NoDup (map f l) -> List.NoDup l.
Proof.
intros A' B' f. induction l as [|x l IH]; intros H; [constructor|].
cbn [map] in H. apply List.NoDup_cons_iff in H as [Hx Hl]. constructor; [|exact (IH Hl)].
intros Hin. apply Hx. apply in_map. exact Hin.
Qed.
Lemma nls_nodup_blocks_fst : forall ly1 S1 {hp1 : list Z} (W1 : world SEGS) mem1 md1,
ARx ly1 S1 hp1 W1 mem1 md1 -> List.NoDup (map fst (ablocks B ly1 S1)).
Proof.
intros ly1 S1 hp1 W1 mem1 md1 HAR. apply nls_pw_nodup_fst.
- intros b Hb. destruct b as [p n].
  pose proof (BLKN ly1 S1 hp1 W1 mem1 md1 p n HAR Hb) as Hn. cbn [snd]. lia.
- destruct (ablocks B ly1 S1) as [|b l] eqn:Eb; [cbn; exact I|].
  destruct b as [p n].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 p n HAR ltac:(rewrite Eb; left; reflexivity))
    as (_ & _ & _ & _ & _ & Hpw).
  rewrite Eb in Hpw. exact Hpw.
Qed.
Lemma nls_nodup_blocks : forall ly1 S1 {hp1 : list Z} (W1 : world SEGS) mem1 md1,
ARx ly1 S1 hp1 W1 mem1 md1 -> List.NoDup (ablocks B ly1 S1).
Proof. intros ly1 S1 hp1 W1 mem1 md1 HAR. exact (nls_nodup_map _ _ fst _ (nls_nodup_blocks_fst ly1 S1 W1 mem1 md1 HAR)). Qed.
(* a list's blocks are live, and their addresses are the plain side's list_blocks *)
Lemma nls_blks_in : forall ly1 S1 (W1 : world SEGS) mem1 LA l lines,
alist_at B ly1 S1 W1 mem1 LA l lines -> forall b, In b (list_blks l) -> In b (ablocks B ly1 S1).
Proof.
intros ly1 S1 W1 mem1 LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & HF) b Hb.
unfold list_blks in Hb. destruct (hl_cap l =? 0) eqn:Ec; cbn [app] in Hb.
- apply in_map_iff in Hb as (rr & <- & Hrr). exact (proj1 (proj1 (Forall_forall _ _) HF rr Hrr)).
- destruct Hb as [<- | Hb].
  + apply Z.eqb_neq in Ec. destruct Hv as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (rr & <- & Hrr). exact (proj1 (proj1 (Forall_forall _ _) HF rr Hrr)).
Qed.
Lemma nls_map_fst_blks : forall l, map fst (list_blks l) = HarnessRep.list_blocks l.
Proof.
intros l. unfold list_blks, HarnessRep.list_blocks. rewrite map_app. f_equal.
- destruct (hl_cap l =? 0); reflexivity.
- rewrite map_map. reflexivity.
Qed.
Lemma nls_cb_app : forall l1 l2, count_begin (l1 ++ l2) = (count_begin l1 + count_begin l2)%nat.
Proof.
intros l1 l2. unfold count_begin. induction l1 as [|x l1 IH]; [reflexivity|].
cbn. destruct (decide (is_begin x)); cbn [length Nat.add]; [f_equal; exact IH | exact IH].
Qed.
Lemma nls_cb_one : forall x, count_begin [x] = (if is_begin x then 1 else 0)%nat.
Proof. intros x. unfold count_begin. cbn. destruct (is_begin x); reflexivity. Qed.
Lemma nls_nodup_disj : forall (T0 : Type) (l1 l2 : list T0) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros T0. induction l1 as [|y l1 IH]; intros l2 x H Hx Hy; [destruct Hx|]. cbn [app] in H.
apply List.NoDup_cons_iff in H as [Hn H].
destruct Hx as [<- | Hx]; [apply Hn; apply in_or_app; right; exact Hy | exact (IH l2 x H Hx Hy)].
Qed.
Lemma nls_perm_swap : forall (T0 : Type) (a b c : list T0), Permutation ((a ++ b) ++ c) (b ++ a ++ c).
Proof. intros T0 a b c. rewrite <- app_assoc. apply Permutation_app_swap_app. Qed.
Lemma nls_vec_len : forall l : hlist, Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l.
Proof.
intros l Hj. unfold bzs. rewrite length_map, length_app, cnl_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul.
unfold hl_n in Hj. change (Z.of_nat 16) with 16. unfold AREC in *. lia.
Qed.
Lemma nls_rec_len : forall r : Z * list byte,
Z.of_nat (length (bzs (snd r ++ [Z_to_bv 8 0]))) = Z.of_nat (length (snd r)) + 1.
Proof. intros r. unfold bzs. rewrite length_map, length_app. cbn [length]. lia. Qed.
Lemma nls_alist_blks : forall l, alist_blks l = list_blks l.
Proof. reflexivity. Qed.
(* every byte a list's predicate reads is its head's or one of its blocks' *)
Lemma nls_alist_fp_in : forall ly1 S1 (W1 : world SEGS) mem1 LA l lines, alist_at B ly1 S1 W1 mem1 LA l lines ->
forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr ->
LA <= a < LA + 16 \/ exists b, In b (list_blks l) /\ fst b <= a < fst b + snd b.
Proof.
intros ly1 S1 W1 mem1 LA l lines (_ & _ & _ & _ & Hcap & Hv & _ & _ & _) rr Hin a Ha.
unfold alist_fp in Hin. destruct Hin as [<- | Hin]; [left; cbn [fst snd] in Ha; exact Ha|]. right.
apply in_app_or in Hin as [Hin | Hin].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
  exists (hl_v l, AREC * hl_cap l). split; [unfold list_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  destruct Hv as [(Hc0 & _) | (_ & _ & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite (nls_vec_len l Hj) in Ha. exact Ha.
- apply in_map_iff in Hin as (r0 & <- & Hr0). exists (fst r0, Z.of_nat (length (snd r0)) + 1).
  split; [unfold list_blks; apply in_or_app; right; apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hr0|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite nls_rec_len in Ha. exact Ha.
Qed.
(* the read-only objects: image bytes outside the allocator's statics and errno *)
Lemma nls_ro : forall b n a, In (b, n) cnl_ro -> b <= a < b + n ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros b n a Hin Ha.
assert (HG' : inG cnl_ro a) by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hin | unfold in_zr; cbn [fst snd]; exact Ha]).
destruct (HGR a HG') as (Hi & Ho & _). destruct (HGRR a HG') as [He _]. split; [exact Hi|]. split; [exact Ho | exact He].
Qed.
Lemma nls_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
(* the source survives a step that keeps every byte below the allocator's ceiling and every present byte *)
Lemma nls_src_kept_low : forall ly1 S1 {hp1 : list Z} (W1 : world SEGS) m m' md1 hs,
ARx ly1 S1 hp1 W1 m md1 -> asrc_at B ly1 S1 W1 m HA hs ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
(forall a, apresent (w_H W1) m a -> apresent (w_H W1) m' a) ->
asrc_at B ly1 S1 W1 m' HA hs.
Proof.
intros ly1 S1 hp1 W1 m m' md1 hs HAR HS Heq Hp.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & _).
pose proof asan_consts as (AC & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & Hexp & Hheld & _).
assert (LB : forall LA l lines, alist_at B ly1 S1 W1 m LA l lines -> HA + 16 <= LA <= HA + 80 ->
  forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling).
{ intros LA l lines Hl HLA rr Hin a Ha.
  destruct (nls_alist_fp_in ly1 S1 W1 m LA l lines Hl rr Hin a Ha) as [Hh | (b & Hb & Hab)]; [lia|].
  destruct b as [p n].
  destruct (cnl_blk ly1 S1 W1 m md1 p n HAR (nls_blks_in ly1 S1 W1 m LA l lines Hl _ Hb)) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
  cbn [fst snd] in Hab. lia. }
apply (asrc_at_kept B ly1 S1 W1 m ly1 S1 W1 m' HA hs HS).
- intros rr Hin a Ha.
  assert (Hlow : 4096 <= a < alloc_ceiling).
  { unfold asrc_fp in Hin. destruct Hin as [<- | [<- | Hin]].
    + cbn [fst snd] in Ha. unfold ASRC in Ha. lia.
    + destruct (cnl_blk ly1 S1 W1 m md1 _ _ HAR Hpin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
      unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha. lia.
    + apply in_app_or in Hin as [Hin | Hin]; [exact (LB _ _ _ Hpend ltac:(lia) rr Hin a Ha)|].
      apply in_app_or in Hin as [Hin | Hin]; [exact (LB _ _ _ Hexp ltac:(lia) rr Hin a Ha) | exact (LB _ _ _ Hheld ltac:(lia) rr Hin a Ha)]. }
  split; [exact (Heq a Hlow)|]. apply nls_awr_kept. exact (Hp a).
- intros b Hb. unfold asrc_blks in Hb. rewrite !nls_alist_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hexp b Hb) | exact (nls_blks_in _ _ _ _ _ _ _ Hheld b Hb)].
Qed.
Lemma nls_lit_len : length RelayModel.K_GESTURE = 13%nat /\ length RelayModel.W_BEGIN = 5%nat /\ length RelayModel.W_END = 3%nat.
Proof. split; [|split]; reflexivity. Qed.
(* the constants survive a step that keeps every byte below the allocator's ceiling *)
Lemma nls_consts_kept_low : forall ly1 S1 {hp1 : list Z} (W1 : world SEGS) m m' md1,
ARx ly1 S1 hp1 W1 m md1 -> (ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO) ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
cnl_consts W1 m -> cnl_consts W1 m'.
Proof.
intros ly1 S1 hp1 W1 m m' md1 HAR Hob Heq (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
pose proof asan_consts as (AC & _). pose proof nls_lit_len as (L1 & L2 & L3).
assert (Rro : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> 4096 <= x < alloc_ceiling).
{ intros b n x Hin Hx. destruct (nls_ro b n x Hin Hx) as (Hi & _). pose proof (pa_img_range x Hi). lia. }
split; [apply (nls_vm_kept W1 W1 m m'); [|exact C1]; intros i Hi; apply Heq;
  apply (Rro (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia]|].
split; [apply (nls_vm_kept W1 W1 m m'); [|exact C2]; intros i Hi; apply Heq;
  apply (Rro (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia]|].
split; [apply (nls_vm_kept W1 W1 m m'); [|exact C3]; intros i Hi; apply Heq;
  apply (Rro (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia]|].
split.
{ apply (nls_ob_kept W1 W1 m m'); [|exact C4]. intros i Hi. apply Heq.
  destruct Hob as [-> | (Hin & HCO)]; [cbn [length] in Hi; lia|].
  destruct (cnl_blk ly1 S1 W1 m md1 OUT CO HAR Hin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
split.
{ intros a Hr. rewrite (Heq a) by (pose proof (pa_img_range a (nls_rom_img a Hr)); lia). exact (C5 a Hr). }
split; [apply (nls_garr8_kept W1 W1 m m'); [|exact C6]; intros i Hi; apply Heq;
  apply (Rro (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia]|].
split; [apply (nls_garr8_kept W1 W1 m m'); [|exact C7]; intros i Hi; apply Heq;
  apply (Rro (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia]|].
apply (nls_garr8_kept W1 W1 m m'); [|exact C8]; intros i Hi; apply Heq.
apply (Rro (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia].
Qed.
Lemma nls_frame_kept : forall (W1 W2 : world SEGS) m m', cnl_frame_ok W1 m sp0 regs0 ->
(forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W1) m a) -> cnl_frame_ok W2 m' sp0 regs0.
Proof. intros W1 W2 m m' Hf Hk i Hi. apply (nls_vm_kept W1 W2 m m'); [|exact (Hf i Hi)]. intros k Hk'. apply Hk. lia. Qed.
(* the source with its held list replaced: every other byte and block kept *)
Lemma nls_src_swap : forall ly1 S1 (W1 : world SEGS) m1 ly2 S2 (W2 : world SEGS) m2 HA0 (h0 : hsrc) (H' : hlist),
asrc_at B ly1 S1 W1 m1 HA0 h0 ->
(forall a, HA0 <= a < HA0 + 80 -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (gfp (hs_partial h0) (bzs (hs_pjunk h0)) :: alist_fp (HA0 + 16) (hs_pending h0) ++ alist_fp (HA0 + 64) (hs_expected h0)) ->
(forall b, In b ((hs_partial h0, APARTIAL) :: alist_blks (hs_pending h0) ++ alist_blks (hs_expected h0)) -> In b (ablocks B ly2 S2)) ->
alist_at B ly2 S2 W2 m2 (HA0 + 80) H' true ->
NoDup (hs_blocks (set_exp_held h0 (hs_expected h0) H')) ->
asrc_at B ly2 S2 W2 m2 HA0 (set_exp_held h0 (hs_expected h0) H').
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
(* the model's side of one step *)
Lemma nls_go_snoc : forall T c a r, cnl_go MT T c (a ++ [r]) =
cnl_go MT T c a + gmc MT (RelayModel.upds T (txs a)) (cnl_cap T c a) (snd r) + mo_free MT.
Proof.
intros T c a. revert T c. induction a as [|x a IH]; intros T c r.
- cbn [app cnl_go cnl_cap txs map]. unfold RelayModel.upds. cbn [fold_left]. lia.
- cbn [app cnl_go cnl_cap]. rewrite IH.
  assert (Eu : RelayModel.upds T (txs (x :: a)) = RelayModel.upds (RelayModel.upd T (bzs (snd x))) (txs a)) by reflexivity.
  rewrite Eu. lia.
Qed.
Lemma nls_gmc_nonneg : forall T cap ln, 0 <= cap -> 0 <= gmc MT T cap ln.
Proof.
intros T cap ln Hc. pose proof (mo_free_nonneg MT ML) as Hf.
unfold gmc. destruct (RelayModel.gesture (bzs ln)) as [[[|] x]|]; cbv beta iota; [| |lia].
- destruct (existsb (RelayModel.list_eqb x) T); [lia|].
  pose proof (mo_malloc_nonneg MT ML (Z.of_nat (length x) + 1) ltac:(pose proof (Nat2Z.is_nonneg (length x)); lia)) as Hm.
  destruct (Z.of_nat (length T) =? cap); [|lia].
  assert (Hg : 0 <= AREC * grow_cap (Z.of_nat (length T)) cap)
    by (unfold grow_cap, AREC; destruct (Z.of_nat (length T) =? cap), (cap =? 0); lia).
  pose proof (mo_malloc_nonneg MT ML _ Hg). lia.
- destruct (existsb (RelayModel.list_eqb x) T); lia.
Qed.
Lemma nls_capstep_nonneg : forall T l cap, 0 <= cap -> 0 <= capstep T l cap.
Proof. intros T l cap Hc. unfold capstep, grow_cap. destruct (Nat.ltb (length T) (length (RelayModel.upd T l))); [|lia]. destruct (Z.of_nat (length T) =? cap), (cap =? 0); lia. Qed.
Lemma nls_go_nonneg : forall rs0 T cap, 0 <= cap -> 0 <= cnl_go MT T cap rs0.
Proof.
induction rs0 as [|r0 rs0 IH]; intros T cap Hc; cbn [cnl_go]; [lia|].
pose proof (nls_gmc_nonneg T cap (snd r0) Hc).
pose proof (mo_free_nonneg MT ML). pose proof (IH (RelayModel.upd T (bzs (snd r0))) _ (nls_capstep_nonneg T (bzs (snd r0)) cap Hc)). lia.
Qed.
(* gesture_model's entry (0x85b9c, ra = 0x85a9c) to its return: either arm reaches it with a0 = s, a1 = the line
   (r's text, at LINE inside the live block (q, k) that is none of the held list's) and a2 = its length; the state
   is cnl_inv's with *at already at r's end.  gesture_model is taken at its own globals, the held list's head. *)
Lemma cnl_gm : forall pre r rs ly1 S1 hp1 kk (H1 : hlist) jk W1 regsc memc mdc LINE q k,
hl_recs EE = pre ++ r :: rs ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 memc mdc kk ->
apres_kept B W mem W1 memc ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) memc (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
asrc_at B ly1 S1 W1 memc HA (set_exp_held h (cnl_E (r :: rs) jk) H1) ->
NoDup (texts H1) -> texts H1 = RelayModel.upds (texts HH) (txs pre) -> hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre ->
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) -> hl_cap H1 <= capb HH EE ->
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) ->
frames S1 = frames S ->
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) -> mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) (r :: rs)) ->
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) (r :: rs) ->
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) (r :: rs)) + kr) -> cnl_cnt RP (r :: rs) H1 (ablocks B ly1 S1) ->
val_mem SEGS (arm W1 memc) AT 8 (cpos gone A0 (pre ++ [r])) -> cnl_consts W1 memc ->
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) ->
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) ->
cnl_frame_ok W1 memc sp0 regs0 -> cnl_regs_ok regsc sp0 HA ->
getr regsc 1 = Z_to_bv 64 (BASE + A_cnl_back) -> getr regsc 10 = w64 HA -> getr regsc 11 = w64 LINE ->
getr regsc 12 = w64 (Z.of_nat (length (snd r))) ->
garr8 SEGS (arm W1 memc) LINE (bzs (snd r)) ->
In (q, k) (ablocks B ly1 S1) -> ~ In (q, k) (list_blks H1) -> q <= LINE -> LINE + Z.of_nat (length (snd r)) <= q + req_size k ->
SRr SEGS W1 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_model)) memc (seg_rom SEGS)) mdc) (cnl_midQ pre r rs).
Proof.
intros pre r rs ly1 S1 hp1 kk H1 jk W1 regsc memc mdc LINE q k HEQ HJ HPK HERR HSRC HND HTX HCAP HN HCB HPERM HFR HMLE HMOK
  HROOM HRMr HCNTr HAT HCONST HOB HSTR HFRM HREGS R1 R10 R11 R12 HLG Hqk Hqn Hq1 Hq2.
pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof APRE as (_ & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16656) by reflexivity. assert (WG : GM_STK = 16528) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & _ & _ & _).
(* W4's gesture_model takes this premise once a working branch f58b3f26c80 is merged *)
assert (HA80 : (HA + 80) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide; [lia | exact HA8] | exists 10; reflexivity]. }
assert (Hs1 : VAL A_g_s <= HA /\ HA + 96 <= VAL A_g_s + 384) by (rewrite AHAE; unfold ASRC; lia).
assert (HAR1 : ARx ly1 S1 hp1 W1 memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
set (E1 := cnl_E (r :: rs) jk) in *.
assert (HrE1 : hl_recs E1 = r :: rs) by reflexivity.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HH1 & HNDB).
cbn [set_exp_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HH1.
pose proof HE1 as (_ & _ & _ & _ & _ & _ & _ & _ & HrecE).
rewrite HrE1 in HrecE. apply Forall_cons_iff in HrecE as [(Hrb & Hrg & Hrl & _) _].
destruct (Hrl eq_refl) as [Hr0 HrA].
pose proof HH1 as (_ & _ & _ & _ & HcapH1 & _).
destruct HCONST as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
(* the source's blocks at the call: pending's, the partial buffer, the expected list's, then the held list's *)
set (HL1 := list_blks H1) in *.
set (Ab := list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)] ++ list_blks E1).
assert (HNDl : List.NoDup (Ab ++ HL1)).
{ apply (nls_nodup_map _ _ fst). apply NoDup_ListNoDup in HNDB.
  replace (map fst (Ab ++ HL1)) with (hs_blocks (set_exp_held h E1 H1)); [exact HNDB|].
  unfold hs_blocks, Ab, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
  rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
assert (Hinc : incl (Ab ++ HL1) (ablocks B ly1 S1)).
{ intros b Hb. unfold Ab, HL1 in Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (nls_blks_in _ _ _ _ _ _ _ HH1 b Hb)].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [destruct Hb as [<- | []]; exact Hpin | exact (nls_blks_in _ _ _ _ _ _ _ HE1 b Hb)]. }
destruct (perm_of_incl _ _ HNDl Hinc) as (rest0 & Hp0).
assert (Hp1 : Permutation (ablocks B ly1 S1) (HL1 ++ Ab ++ rest0)) by (eapply Permutation_trans; [exact Hp0 | apply nls_perm_swap]).
pose proof (nls_nodup_blocks _ _ _ _ _ HAR1) as HND1b.
(* gesture_model's footprint: a held block live at entry was one of FPc's, by APERM *)
assert (HFP : forall a, inFP (blk_FP HL1) a ->
  (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb). cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by exact (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb).
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly S)) as [Hin0 | Hnin0].
  - left. split; [|exists p, n; split; [exact Hb1 | exact Ha]].
    destruct APERM as (rest & HQ0). pose proof (HPERM rest HQ0) as HP1.
    assert (Hx : In (p, n) (list_blks EE ++ list_blks HH)).
    { pose proof (Permutation_in _ HQ0 Hin0) as Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx]; [exact Hx|].
      exfalso. pose proof (Permutation_NoDup HP1 HND1b) as HNx. apply NoDup_app_remove_l in HNx.
      exact (nls_nodup_disj _ HL1 rest (p, n) HNx Hb Hx). }
    exists (p, p + req_size n). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n)). exact Hx.
  - right. exists p, n. split; [exact Hb1|]. split; [exact Hnin0 | exact Ha]. }
(* gesture_model's globals: the held list's head only *)
set (G' := [(HA + 80, 16)]).
assert (HG'G : forall a, inG G' a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply AGA; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG' : forall a, ~ (HA + 80 <= a < HA + 96) -> ~ inG G' a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G' G HG'G HG) as HG'.
(* gx_rt of gesture_model's G' comes from g_s's own placement fact HGRR, never from the caller's G: a caller's G
   (G_fr, G_SL) holds errno, so `gx_rt B G` was unsatisfiable at every caller (W5's finding on re_spec_g). *)
assert (HG'R : forall a, inG G' a -> inG cnl_ro a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. unfold inG. apply Exists_exists. exists (VAL A_g_s, 384).
  split; [cbv [cnl_ro]; right; right; right; left; reflexivity|].
  unfold in_zr; cbn [fst snd]. rewrite AHAE in Ha. unfold ASRC in *. lia. }
assert (HGRT' : gx_rt B G') by (eapply gx_rt_sub; [exact HG'R | exact HGRR]).
(* gesture_model's entry *)
assert (Usp : spZ regsc = sp0 - 128).
{ destruct HREGS as (Q2 & _). unfold spZ at 1. rewrite Q2. apply unsigned_lit_small. lia. }
destruct (ajournal_gx_inner_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 memc mdc kk HJ) as (memS & HJi & _).
assert (HPREg : afn_pre_x SEGS B ARx GM_STK ly1 S1 hp1 W1 regsc memc mdc []).
{ destruct HREGS as (_ & Q3 & Q4 & Q8 & _).
  eapply (afn_pre_x_at SEGS B PST ARx (CNL_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W1 memc mdc kk regsc GM_STK (- 128 - XO) [] HJi).
  - rewrite Usp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-8); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
  - lia.
  - rewrite WG; lia.
  - rewrite WS, WG. lia.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold A_cnl_back, AF_fr_check_no_loss; lia | reflexivity].
  - unfold raZ. rewrite R1. unfold A_cnl_back, AF_fr_check_no_loss. destruct HBASE as (B1 & B2 & _).
    rewrite unsigned_lit_small by lia. lia.
  - exact Q3.
  - exact Q4.
  - apply achain_low. unfold s0Z. rewrite Q8, unsigned_lit_small by lia. lia. }
assert (Hazs : azs B (HA + 80) 16)
  by (destruct AZS as (zr & Hzr & Hz8 & Hz1 & Hz2); exists zr; split; [exact Hzr|]; split; [exact Hz8|]; split; lia).
assert (HnT1 : Z.of_nat (length (texts H1)) = hl_n H1) by (unfold texts, hl_n; rewrite length_map; reflexivity).
cbn [cnl_room] in HROOM. destruct HROOM as (HRM1 & HRM2 & HRM3).
assert (HGC : gm_cost MT H1 (snd r) = gmc MT (texts H1) (hl_cap H1) (snd r)).
{ unfold gm_cost, lp_cost, gmc, lp_grow, lp_vbytes. rewrite HnT1. reflexivity. }
cbn [cnl_go] in HMOK.
eapply SRr_mono.
{ pose proof CNLAP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CNLROM).
  refine (GM G' HG' HGRT' (W_rom_place.cnl_g_rom_out B HA j AHAE AJLT CNLROM ROMOH ROMNS)
    W1 ly1 S1 hp1 regsc memc mdc [] HA LINE (snd r) H1 q k HPREg R10 R11 R12 HH1 HND _ Hazs HA80 HLG Hr0 HrA
    Hqk Hqn Hq1 Hq2 C6 C7 C8 C5 _ _ _ _
    (Datatypes.S (Z.to_nat (cnl_go MT_rk (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
      + kr))%nat _ _).
  - intros a Ha. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros Hg. unfold lp_vbytes. rewrite <- HnT1. apply HRM1. unfold lp_grow in Hg. apply Z.eqb_eq in Hg. lia.
  - unfold AREC in *. lia.
  - unfold lp_grow, lp_vbytes. rewrite <- HnT1. exact HRM2.
  - rewrite HGC. eapply (mo_ok_le MT ML); [exact HMOK|]. pose proof (mo_free_nonneg MT ML).
    assert (Hc0 : 0 <= hl_cap H1) by (unfold hl_n in HcapH1; lia).
    pose proof (nls_go_nonneg rs (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1))
      (nls_capstep_nonneg (texts H1) (bzs (snd r)) (hl_cap H1) Hc0)). lia.
  - (* the room: gesture_model's charge, then r's free, then the rest (W_cnl_cnt.v cnl_rk_step) *)
    rewrite <- (cnl_rk_step H1 r rs kr). exact HRMr.
  - (* the counts: gesture_model's peak is at most 2 (W_cnl_cnt.v cnl_cnt_gm_pre) *)
    exact (cnl_cnt_gm_pre RP r rs H1 _ HCNTr). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & hp2 & regs2 & mem2 & md2 & kk2 & H2 & -> & HJg & HPg & HPKg & HERRg & HLH2 & HND2 & HT2 & HC2 & HPm & HFR2 & HMLE2 & HRMg).
set (HL2 := list_blks H2) in *.
assert (HAR2 : ARx ly2 S2 hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJg).
pose proof (HPm _ Hp1) as Hp2.
pose proof (Permutation_NoDup Hp2 (nls_nodup_blocks _ _ _ _ _ HAR2)) as HNDp2.
(* what gesture_model kept: its journal at G' *)
pose proof HJg as HJg0. eapply ajournal_gx_inner_x in HJg0. destruct HJg0 as (memS2 & HJgi & HgS2).
rewrite Usp in HJgi. destruct HJgi as (_ & _ & _ & _ & _ & _ & _ & _ & KF & KB & KI & _).
assert (Hcl : ~ YI16.sink_open_fp (blk_FP HL1)).
{ apply sink_closed_pos. apply Forall_forall. intros rr Hrr. unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 128 - GM_STK <= a < sp0 - 128) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Ha Hn. rewrite KF by lia. apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 80 <= a < HA + 96) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as Hr.
  rewrite KI; [|exact Hi | exact Ho | exact He | exact (HPST a Hi) | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. exact Hn. }
assert (Kblk : forall p n i, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) HL1 ->
  0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W1) memc (p + i)).
{ intros p n i Hb1 Hb2 Hn Hi. destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i Hb1 Hb2 Hi).
  - apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. unfold off_img in Hoff. lia.
  - intros (rr & Hrr & Hr). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p' & n') & <- & Hb'). cbn [fst snd] in Hr.
    assert (Hne : (p', n') <> (p, n)) by (intros E'; rewrite E' in Hb'; exact (Hn Hb')).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 memc mdc p' n' p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb') Hb1 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W1 memc) a -> writable_at SEGS (arm W2 mem2) a).
{ intros a Hi Ho He Hw. apply (nls_awr_kept W1 W2 memc mem2 a); [|exact Hw]. intros Hp. exact (HPKg a Hi Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W2 mem2) a).
{ intros p n a Hb Ha. destruct (cnl_blk ly2 S2 W2 mem2 md2 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
(* the source's own bytes (outside the held head) and the blocks of Ab *)
assert (KHd : forall a, HA <= a < HA + 80 -> abyte_kept W1 memc W2 mem2 a).
{ intros a Ha. destruct (nls_ro (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; do 3 right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
  split; [apply Kimg; [exact Hi | exact Ho | exact He | lia] | apply Pimg; assumption]. }
assert (KAb : forall b a, In b Ab -> fst b <= a < fst b + snd b -> abyte_kept W1 memc W2 mem2 a).
{ intros (p & n) a Hb Ha. cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by (apply Hinc; apply in_or_app; left; exact Hb).
  assert (Hb2 : In (p, n) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; apply in_or_app; left; exact Hb).
  assert (Hn1 : ~ In (p, n) HL1) by exact (nls_nodup_disj _ Ab HL1 (p, n) HNDl Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr & _).
  replace a with (p + (a - p)) by lia.
  split; [apply (Kblk p n); [exact Hb1 | exact Hb2 | exact Hn1 | lia] | intros _; apply (Pblk p n); [exact Hb2 | lia]]. }
assert (HOB2 : ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ In (OUT, CO) (ablocks B ly2 S2) /\
  ~ In (OUT, CO) (list_blks E1 ++ HL1) /\ ~ In (OUT, CO) HL2)).
{ destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [left; exact Hob0 | right].
  assert (HOr : In (OUT, CO) (Ab ++ rest0)).
  { pose proof (Permutation_in _ Hp1 HOin) as Hx. apply in_app_or in Hx as [Hx | Hx]; [|exact Hx].
    exfalso. apply HOn. apply in_or_app. right. exact Hx. }
  split; [exact HCO|]. split; [exact HOin|].
  split; [apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; exact HOr|].
  split; [exact HOn|]. intros Hx. exact (nls_nodup_disj _ HL2 (Ab ++ rest0) (OUT, CO) HNDp2 Hx HOr). }
clear HOB.
assert (HnT2 : Z.of_nat (length (texts H2)) = hl_n H2) by (unfold texts, hl_n; rewrite length_map; reflexivity).
assert (HCS : hl_cap H2 = capstep (texts H1) (bzs (snd r)) (hl_cap H1)).
{ unfold capstep. rewrite <- HT2, HC2, <- HnT1, <- HnT2.
  destruct (Nat.ltb_spec (length (texts H1)) (length (texts H2)));
  destruct (Z.ltb_spec (Z.of_nat (length (texts H1))) (Z.of_nat (length (texts H2)))); try reflexivity; lia. }
pose proof (upd_len (texts H1) (bzs (snd r))) as (U1 & U2). rewrite <- HT2 in U1, U2.
pose proof nls_lit_len as (L1 & L2 & L3).
assert (KR : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> ~ (HA + 80 <= x < HA + 96) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) memc x).
{ intros b n x Hin Hx Hn. destruct (nls_ro b n x Hin Hx) as (Hi & Ho & He). exact (Kimg x Hi Ho He Hn). }
(* the state at 0x85a9c *)
exists regs2, mem2, md2. split; [rewrite R1; reflexivity|].
exists ly2, S2, hp2, (kk + kk2), H2, jk.
split; [exact HEQ|].
split.
{ pose proof (ajournal_gx_G_mono_x SEGS B PST ARx G' G 0 [] GM_STK (spZ regsc) (blk_FP HL1) ly1 S1 hp1 W1 memc mdc [] ly2 S2 hp2 W2 mem2 md2 kk2
    HG'G HJg) as HJg'. rewrite Usp in HJg'.
  pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md [] ly1 S1 hp1 W1 memc mdc kk
    GM_STK (sp0 - 128) 0 [] (blk_FP HL1) [] ly2 S2 hp2 W2 mem2 md2 kk2 HJ HJg' ltac:(rewrite WS, WG; lia) ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP) as HJ2.
  cbn [app] in HJ2. exact HJ2. }
split; [exact (nls_apk_trans _ _ _ _ _ _ HPK HPKg)|].
split; [intros j0 Hj0; rewrite (HERRg j0 Hj0); exact (HERR j0 Hj0)|].
split.
{ refine (nls_src_swap ly1 S1 W1 memc ly2 S2 W2 mem2 HA (set_exp_held h E1 H1) H2 HSRC KHd _ _ HLH2 _).
  - intros rr Hrr a Ha. cbn [set_exp_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KAb (hs_partial h, APARTIAL)); [unfold Ab; apply in_or_app; right; apply in_or_app; left; left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ HE1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. cbn [set_exp_held hs_partial hs_pending hs_expected] in Hb. rewrite !nls_alist_blks in Hb.
    apply (Permutation_in _ (Permutation_sym Hp2)). apply in_or_app. right. apply in_or_app. left. unfold Ab.
    destruct Hb as [<- | Hb]; [apply in_or_app; right; apply in_or_app; left; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
  - apply NoDup_ListNoDup.
    replace (hs_blocks (set_exp_held (set_exp_held h E1 H1) (hs_expected (set_exp_held h E1 H1)) H2)) with (map fst (Ab ++ HL2)).
    + pose proof (nls_nodup_blocks_fst _ _ _ _ _ HAR2) as Hf.
      pose proof (Permutation_NoDup (Permutation_map fst (Permutation_trans Hp2 (Permutation_sym (nls_perm_swap _ Ab HL2 rest0)))) Hf) as Hf2.
      rewrite map_app in Hf2. exact (NoDup_app_remove_r _ _ Hf2).
    + unfold hs_blocks, Ab, HL2. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
      rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
split; [exact HND2|].
split; [rewrite upds_snoc, <- HTX; exact HT2|].
split; [rewrite cnl_cap_snoc, <- HTX, <- HCAP; exact HCS|].
split.
{ rewrite txs_app, nls_cb_app. change (txs [r]) with [bzs (snd r)]. rewrite nls_cb_one.
  destruct (is_begin (bzs (snd r))) eqn:Eb; [lia|].
  destruct (Nat.lt_ge_cases (length (texts H1)) (length (texts H2))) as [Hlt | Hge]; [destruct (U2 Hlt) as [Hb _]; congruence | lia]. }
split.
{ rewrite HC2. destruct (Z.ltb_spec (hl_n H1) (hl_n H2)) as [Hlt | Hge]; [|exact HCB].
  destruct (U2 ltac:(lia)) as (Hbeg & _).
  assert (Hcbe : (count_begin (txs pre) + 1 <= count_begin (texts EE))%nat).
  { change (texts EE) with (txs (hl_recs EE)). rewrite HEQ, txs_app, nls_cb_app.
    change (txs (r :: rs)) with ([bzs (snd r)] ++ txs rs). rewrite nls_cb_app, nls_cb_one, Hbeg. lia. }
  unfold capb, grow_cap in *. destruct (hl_n H1 =? hl_cap H1) eqn:Eq; [|lia]. apply Z.eqb_eq in Eq. destruct (hl_cap H1 =? 0); lia. }
split.
{ intros rest HQ0. pose proof (HPERM rest HQ0) as HP1x.
  assert (HP1y : Permutation (ablocks B ly1 S1) (HL1 ++ list_blks E1 ++ rest))
    by (eapply Permutation_trans; [exact HP1x|]; rewrite app_assoc; apply nls_perm_swap).
  eapply Permutation_trans; [exact (HPm _ HP1y)|]. rewrite app_assoc. apply nls_perm_swap. }
split; [rewrite HFR2; exact HFR|].
split.
{ eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLE2)|].
  rewrite nls_go_snoc, HGC, HTX, HCAP. lia. }
split.
{ replace (cnl_go MT (texts H2) (hl_cap H2) rs) with
    (cnl_go MT (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
    by (rewrite <- HT2, <- HCS; reflexivity).
  apply (mo_ok_step MT ML S1 S2 (gm_cost MT H1 (snd r))); [|exact HMLE2].
  rewrite HGC, Z.add_assoc. exact HMOK. }
split.
{ rewrite <- HT2, <- HCS in HRM3.
  assert (BB : blocks_bytes S2 = blocks_bytes S1 - hbytes (texts H1) (hl_cap H1) + hbytes (texts H2) (hl_cap H2)).
  { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hp1), (bsum_perm _ _ Hp2), !bsum_app.
    unfold HL1, HL2. rewrite !bsum_list_blks. lia. }
  rewrite BB. exact HRM3. }
split.
{ (* the room past gesture_model: its post's kr *)
  rewrite HT2, HCS. exact HRMg. }
split.
{ (* the live counts past gesture_model (W_cnl_cnt.v cnl_cnt_gm_post) *)
  apply (cnl_cnt_gm_post RP r rs H1 H2 (ablocks B ly1 S1) (ablocks B ly2 S2) (Ab ++ rest0));
  [first [exact HND | apply NoDup_ListNoDup; exact HND] | exact HT2 | exact HCS | exact Hp1 | exact Hp2 | exact HCNTr]. }
split.
{ apply (nls_vm_kept W1 W2 memc mem2 AT 8); [|exact HAT]. intros i Hi. apply Kstk; [|lia]. split; [lia|]. cbn in Hi. lia. }
split.
{ pose proof CNLAP as (_ & Agn & _ & _ & _ & _ & Ano & Aou & Alg & Alb & Ale & Arom).
  cbv zeta in Agn, Ano, Aou, Alg, Alb, Ale, Arom.
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C1]; intros i Hi;
    apply (KR (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C2]; intros i Hi;
    apply (KR (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C3]; intros i Hi;
    apply (KR (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split.
  { apply (nls_ob_kept W1 W2 memc mem2); [|exact C4]. intros i Hi.
    destruct HOB2 as [-> | (HCO & HOin & HOin2 & HOn & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly1 S1 W1 memc mdc OUT CO HAR1 HOin) as (_ & _ & _ & Hnr & _).
    apply (Kblk OUT CO); [exact HOin | exact HOin2 | intros Hx; apply HOn; apply in_or_app; right; exact Hx | lia]. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as [He Hrp].
    assert (Hd : forall rr, {in_zr a rr} + {~ in_zr a rr}).
    { intros rr. unfold in_zr. destruct (Z_le_gt_dec (fst rr) a); destruct (Z_lt_ge_dec a (fst rr + snd rr));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Ho].
    - exact (rom_pinned_view_x SEGS B ARx LAWS ly2 S2 hp2 W2 mem2 md2 a HAR2 (Hrp Hown)).
    - rewrite (Kimg a (nls_rom_img a Hr) Ho He (fun Hn => Arom a ltac:(lia) Hr)). exact (C5 a Hr). }
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C6]; intros i Hi;
    apply (KR (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia | rewrite L1 in Hi; lia]|].
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C7]; intros i Hi;
    apply (KR (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia | rewrite L2 in Hi; lia]|].
  apply (nls_garr8_kept W1 W2 memc mem2); [|exact C8]; intros i Hi.
  apply (KR (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia | rewrite L3 in Hi; lia]. }
split.
{ destruct HOB2 as [Hob0 | (HCO & _ & HOin2 & HOn & HOn2)]; [left; exact Hob0 | right].
  split; [exact HCO|]. split; [exact HOin2|].
  intros Hx. apply in_app_or in Hx as [Hx | Hx]; [apply HOn; apply in_or_app; left; exact Hx | exact (HOn2 Hx)]. }
split; [exact HSTR|].
split; [apply (nls_frame_kept W1 W2 memc mem2 HFRM); intros a Ha; apply Kstk; lia|].
destruct HREGS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
assert (P2 : getr regs2 2 = getr regsc 2) by (apply (HPg 2); unfold acallee_saved; lia).
assert (P3 : getr regs2 3 = getr regsc 3) by (apply (HPg 3); unfold acallee_saved; lia).
assert (P4 : getr regs2 4 = getr regsc 4) by (apply (HPg 4); unfold acallee_saved; lia).
assert (P8 : getr regs2 8 = getr regsc 8) by (apply (HPg 8); unfold acallee_saved; lia).
assert (P9 : getr regs2 9 = getr regsc 9) by (apply (HPg 9); unfold acallee_saved; lia).
assert (P18 : getr regs2 18 = getr regsc 18) by (apply (HPg 18); unfold acallee_saved; lia).
assert (P19 : getr regs2 19 = getr regsc 19) by (apply (HPg 19); unfold acallee_saved; lia).
assert (P22 : getr regs2 22 = getr regsc 22) by (apply (HPg 22); unfold acallee_saved; lia).
assert (P23 : getr regs2 23 = getr regsc 23) by (apply (HPg 23); unfold acallee_saved; lia).
assert (P24 : getr regs2 24 = getr regsc 24) by (apply (HPg 24); unfold acallee_saved; lia).
assert (P25 : getr regs2 25 = getr regsc 25) by (apply (HPg 25); unfold acallee_saved; lia).
assert (P26 : getr regs2 26 = getr regsc 26) by (apply (HPg 26); unfold acallee_saved; lia).
assert (P27 : getr regs2 27 = getr regsc 27) by (apply (HPg 27); unfold acallee_saved; lia).
unfold cnl_regs_ok. rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P24, P25, P26, P27.
repeat split; assumption.
Qed.
(* the head region of s->expected without the n write window: cnl_step stores nothing before gesture_model *)
Definition cnl_headS : YP09.region :=
YP09.mkRegion (Some 9%nat) 64 80 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 4 (SOff 34 0))].
(* next_line's two out cells in this frame: len at sp + 8 (= |r|, atom 36) and line at sp + 16 (atom 66) *)
Definition cnl_cells : YP09.region :=
YP09.mkRegion (Some 2%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 66 0))].
Lemma nls_nowin : forall E (rs : smem) (m m' : word -> option byte), frame_of E rs m m' ->
forallb (fun r => Z.eqb (YP09.r_wlo r) (YP09.r_whi r)) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' Hf Hb x. apply Hf. intros (r & Hin & Hr). rewrite forallb_forall in Hb.
pose proof (Hb r Hin) as He. apply Z.eqb_eq in He. lia.
Qed.
Lemma nls_eqv_view : forall (W1 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W1) m' x = mrestrict (w_H W1) m x) ->
(forall a, aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) /\ (forall a, apresent (w_H W1) m a -> apresent (w_H W1) m' a).
Proof.
intros W1 m m' Hq. split.
- intros a. apply aview_eq_of. apply Hq.
- intros a (Hh & b & Hb). split; [exact Hh|]. exists b. pose proof (Hq (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx.
  rewrite Hh in Hx. rewrite Hx. exact Hb.
Qed.
(* the loop's facts survive a step that keeps the bytes below the allocator's ceiling and the saved registers *)
Lemma nls_inv_kept : forall ly1 S1 {hp1 : list Z} (W1 : world SEGS) m m' md1 hs,
ARx ly1 S1 hp1 W1 m md1 ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
(forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
(forall a, apresent (w_H W1) m a -> apresent (w_H W1) m' a) ->
(ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO) ->
asrc_at B ly1 S1 W1 m HA hs -> cnl_consts W1 m -> cnl_frame_ok W1 m sp0 regs0 -> apres_kept B W mem W1 m ->
asrc_at B ly1 S1 W1 m' HA hs /\ cnl_consts W1 m' /\ cnl_frame_ok W1 m' sp0 regs0 /\ apres_kept B W mem W1 m'.
Proof.
intros ly1 S1 hp1 W1 m m' md1 hs HAR Hlo Hfr Hp Hob HS HC HF HK.
split; [exact (nls_src_kept_low ly1 S1 W1 m m' md1 hs HAR HS Hlo Hp)|].
split; [exact (nls_consts_kept_low ly1 S1 W1 m m' md1 HAR Hob Hlo HC)|].
split; [exact (nls_frame_kept W1 W1 m m' HF Hfr)|].
exact (nls_apk_trans _ _ _ _ _ _ HK (nls_apk_of_pres W1 m m' Hp)).
Qed.
(* errno is an image byte (api_env), so a step that keeps the bytes below the allocator's ceiling keeps its view *)
Lemma nls_err_kept : forall (W1 : world SEGS) m m',
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) m (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
forall j, 0 <= j < 4 -> aview SEGS (w_H W1) m' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j).
Proof.
intros W1 m m' Hlo He j0 Hj0.
pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + j0) ltac:(lia)) as Hi.
pose proof (pa_img_range _ Hi) as Hr. pose proof asan_consts as (AC & _).
rewrite (Hlo (as_errno B + j0) ltac:(lia)). exact (He j0 Hj0).
Qed.
Lemma nls_exp_held_nodup : forall ly1 S1 (W1 : world SEGS) m1 hs, asrc_at B ly1 S1 W1 m1 HA hs ->
List.NoDup (list_blks (hs_expected hs) ++ list_blks (hs_held hs)).
Proof.
intros ly1 S1 W1 m1 hs HS.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HND).
apply NoDup_ListNoDup in HND. unfold hs_blocks in HND. rewrite <- !nls_map_fst_blks in HND.
apply NoDup_app_remove_l in HND. cbn [app] in HND. apply List.NoDup_cons_iff in HND as [_ HND].
rewrite <- map_app in HND. exact (nls_nodup_map _ _ fst _ HND).
Qed.
Lemma nls_view_of_garr8 : forall (W1 : world SEGS) m a (l : list byte) i, garr8 SEGS (arm W1 m) a (bzs l) ->
(i < length l)%nat -> aview SEGS (w_H W1) m (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
intros W1 m a l i Hg Hi. unfold aview, arm in *.
rewrite (garr8_mbyte SEGS _ _ _ i Hg) by (unfold bzs; rewrite length_map; exact Hi). cbn [option_map]. f_equal.
unfold bzs. rewrite (nth_indep _ 0 (HarnessRep.bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hi).
rewrite map_nth. unfold HarnessRep.bz. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma nls_nth_skipn : forall (T0 : Type) n m (l : list T0) d, nth m (skipn n l) d = nth (n + m) l d.
Proof. intros T0. induction n as [|n IH]; intros m [|x l] d; cbn; try reflexivity; [destruct m; reflexivity | apply IH]. Qed.
Lemma nls_bsr_cons : forall r0 rs0, bsr (r0 :: rs0) = snd r0 ++ Z_to_bv 8 0 :: bsr rs0.
Proof. intros r0 rs0. unfold bsr. cbn [map concat]. rewrite <- app_assoc. reflexivity. Qed.
Lemma nls_bsr_app : forall a b, bsr (a ++ b) = bsr a ++ bsr b.
Proof. intros a b. unfold bsr. rewrite map_app, concat_app. reflexivity. Qed.
(* the stack's shadow is zero: the laws' per-byte zero-shadow field of the real stack (YCbqG.v alx_zshadow_byte) *)
Lemma nls_ra_stack : forall ly1 S1 {hp1 : list Z} (W1 : world SEGS) mem1 md1 a len,
ARx ly1 S1 hp1 W1 mem1 md1 -> ly_stk_lo ly1 <= a -> a + len <= ly_stk_hi ly1 -> 0 <= len ->
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF a len.
Proof.
intros ly1 S1 hp1 W1 mem1 md1 a len HAR Hlo Hhi Hlen x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 x HAR ltac:(lia)).
Qed.
(* bytes seen through the ASan view, as a byte array *)
Lemma nls_garr8_of_view : forall (W1 : world SEGS) m a (ln : list byte),
(forall i, (i < length ln)%nat -> aview SEGS (w_H W1) m (a + Z.of_nat i) = Some (bv_unsigned (nth i ln (Z_to_bv 8 0)))) ->
garr8 SEGS (arm W1 m) a (bzs ln).
Proof.
intros W1 m a ln Hv jj Hj. unfold bzs in Hj. rewrite length_map in Hj.
assert (Hn : nth jj (bzs ln) 0 = bv_unsigned (nth jj ln (Z_to_bv 8 0))).
{ unfold bzs. rewrite (nth_indep _ 0 (HarnessRep.bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth. reflexivity. }
pose proof (bv_unsigned_in_range 8 (nth jj ln (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite Hn. split; [|lia].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hv jj Hj) as Hj'. unfold aview, arm in *. destruct (mbyte SEGS (mrestrict (w_H W1) m) (a + Z.of_nat jj)) as [b|] eqn:Eb;
  cbn [option_map] in Hj'; [|discriminate]. injection Hj' as Hj'. f_equal. apply bv_eq. rewrite Hj'.
assert (Hlb : forall z, 0 <= z < 256 -> le_byte z 1 0 = z).
{ intros z Hz. unfold le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (8 * Z.of_nat 1) with 8 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small z (2 ^ 8)) by lia. apply Z.mod_small. lia. }
rewrite Hlb by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* a run over regions with no write window writes nothing *)
Ltac nls_nowin_awr :=
  let a := fresh "a" in let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (rr & Hin & Hr);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]);
  destruct Hin.
(* one iteration up to gesture_model's return *)
Lemma cnl_step : forall pre r rs W1 regs1 mem1 md1, cnl_inv pre (r :: rs) W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) (cnl_midQ pre r rs).
Proof.
intros pre r rs W1 regs1 mem1 md1 HI.
destruct HI as (ly1 & S1 & hp1 & kk & H1 & jk & HEQ & HJ & HPK & HERR & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (_ & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16656) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR1 : ARx ly1 S1 hp1 W1 mem1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE1 & _).
cbn [set_exp_held hs_expected] in HE1.
pose proof HE1 as (MvE & MnE & _ & MwE & (HnleC & HcapLt) & HvvE & _ & _ & HFallE).
unfold cnl_E, hl_n in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE. cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR).
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))) by (cbn [length]; lia).
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, length_app in HnE. lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
destruct (cnl_rec_fields B ly1 S1 W1 mem1 (HA + 64) (cnl_E (r :: rs) jk) true 0%nat HE1 ltac:(cbn; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0) by (cbn; lia). exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by (unfold APARTIAL in HlenR; lia).
  replace (hl_v EE + 8) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0 + 8) by (cbn; lia). exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
destruct (cnl_mk A_cnl_loop W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn AZS MwE HFRM Cgone AGN MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(unfold APARTIAL in HlenR; lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27).
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall k, (k < 18)%nat -> ew Ev (32 + k) = nth k (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEv. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew Ev 32 = Z_to_bv 64 gone) by exact (EX 0%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 (fst r)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew Ev 36 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 4%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew Ev 2) = sp0 - 128) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Vb9 : base_val Ev (Some 9%nat) = HA) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v EE)) by exact (EX 1%nat ltac:(lia)).
assert (Vb33 : base_val Ev (Some 33%nat) = hl_v EE) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (rewrite HEv; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Vbg : base_val Ev (Some 271%nat) = VAL A_g_gone)
  by (change (Some 271%nat) with (Some A_g_gone); cbn [base_val]; rewrite Eg; apply unsigned_lit_small; exact (pa_val_range _)).
assert (Vb2 : base_val Ev (Some 2%nat) = sp0 - 128) by (cbn [base_val]; exact Usp).
clear HEv EX.
(* the head of s->expected without its write window: nothing below is stored until gesture_model returns *)
pose proof (st_ok_pi_region_nth Ev (ss_cnll A_cnl_loop) _ 2 cnl_headL HS eq_refl) as Hrh.
assert (HrS : region_ok SEGS Ev (ms_mem (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS))))
  cnl_headS).
{ unfold cnl_headL, cnl_headS, region_ok in Hrh |- *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in Hrh |- *.
  destruct Hrh as (A1 & A2 & _ & A4). split; [exact A1|]. split; [exact A2|]. split; [intros o Ho; lia | exact A4]. }
pose proof (ast_ok_pi_set_region Ev (ss_cnll A_cnl_loop) _ 2 cnl_headL cnl_headS HS eq_refl ltac:(reflexivity)
  ltac:(vm_compute; reflexivity) HrS) as HS'.
clear HS Hrh HrS. rename HS' into HS.
(* the callee-saved registers at the loop head, as the state names them *)
prreg HS (2%bv : bv 5) O2. prreg HS (3%bv : bv 5) O3. prreg HS (4%bv : bv 5) O4. prreg HS (8%bv : bv 5) O8.
prreg HS (9%bv : bv 5) O9. prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (22%bv : bv 5) O22.
prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24. prreg HS (25%bv : bv 5) O25. prreg HS (26%bv : bv 5) O26.
prreg HS (27%bv : bv 5) O27.
assert (HOBx : ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO)
  by (destruct HOB as [H0 | (Hc1 & Hc2 & _)]; [left; exact H0 | right; split; assumption]).
assert (HinR1 : In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks (cnl_E (r :: rs) jk))).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). left. reflexivity. }
assert (HnH1 : ~ In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks H1)).
{ pose proof (nls_exp_held_nodup _ _ _ _ _ HSRC) as Hnd. cbn [set_exp_held hs_expected hs_held] in Hnd.
  exact (nls_nodup_disj _ _ _ _ Hnd HinR1). }
assert (HgarR0 : garr8 SEGS (arm W1 mem1) (fst r) (bzs (snd r))).
{ unfold bzs in HgarR. rewrite map_app in HgarR. apply garr8_app in HgarR as [Hg _]. exact Hg. }
unfold A_cnl_loop.
(* ---- 0x859dc: lbu a0, g_gone; beqz ---- *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { nls_nowin_awr. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* g_gone clear: next_line, the two compares, bcmp *)
  assert (Hg0 : gone = 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_eq in Hc; exact Hc).
  destruct (HSTR Hg0) as (rest0 & Hsk). rewrite nls_bsr_cons, <- app_assoc in Hsk. cbn [app] in Hsk.
  set (An := cpos gone A0 pre) in *.
  assert (HAn0 : 0 <= An) by (unfold An, cpos; rewrite Hg0; cbn; lia).
  assert (HAnO : An + Z.of_nat (length (snd r)) + 1 <= NO).
  { pose proof (f_equal (@length byte) Hsk) as Hl. rewrite length_skipn, length_app in Hl. cbn [length] in Hl. lia. }
  destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [rewrite Hob0 in AOBN; cbn [length] in AOBN; lia|].
  destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (HO16 & HO4096 & _ & HOle & HOreq1 & HOceil & _ & HOoff & HOapp & HOpres).
  (* ---- to next_line(at, sp + 16, sp + 8) ---- *)
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_next_line. { nls_nowin_awr. }
  assert (MQ1 : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ1) as (AV1 & AP1).
  pmkst HS.
  prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
  prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
  assert (UspN : spZ (ms_regs ms0) = sp0 - 128) by (unfold spZ at 1; rewrite N2, E2; apply unsigned_lit_small; lia).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdN := mdq) in * end.
  destruct (ajournal_gx_inner_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 (ms_mem ms0) mdN kk HJ)
    as (memS & HJi & _).
  pose proof HJi as (HARN & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRN & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (HPREn : afn_pre_x SEGS B ARx NL_STK ly1 S1 hp1 W1 (ms_regs ms0) (ms_mem ms0) mdN []).
  { eapply (afn_pre_x_at SEGS B PST ARx (CNL_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W1 (ms_mem ms0) mdN kk (ms_regs ms0)
      NL_STK (- 128 - XO) [] HJi).
    - rewrite UspN. lia.
    - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-8); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
    - lia.
    - unfold NL_STK, NL_FRAME, ESTACK; lia.
    - rewrite WS. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - rewrite N1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite N1. destruct HBASE as (B1 & B2 & _). rewrite unsigned_lit_small by lia. lia.
    - rewrite N3, (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite N4, (EEo 4%nat 4%bv eq_refl). exact R4.
    - apply achain_low. unfold s0Z. rewrite N8, E9, (unsigned_lit_small HA) by lia. rewrite unsigned_lit_small by lia. lia. }
  assert (HATn : val_mem SEGS (arm W1 (ms_mem ms0)) AT 8 An) by (apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact HAT]).
  eapply SRr_bind.
  { eapply (NL W1 ly1 S1 hp1 (ms_regs ms0) (ms_mem ms0) mdN [] (128 + XO) AT (sp0 - 112) (sp0 - 120) An NO OUT ob HPREn).
    - lia.
    - rewrite Z.add_mod, AX16 by lia. reflexivity.
    - rewrite UspN, Etop. lia.
    - intros a Ha. apply HPRN. rewrite UspN in Ha. lia.
    - rewrite N10, (EEo 18%nat 18%bv eq_refl). exact R18.
    - rewrite N11, Usp. f_equal. lia.
    - rewrite N12, Usp. f_equal. lia.
    - exact AAT8.
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 14; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 15; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - lia.
    - lia.
    - lia.
    - apply (nls_ra_stack ly1 S1 (hp1 := hp1) W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 (hp1 := hp1) W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 (hp1 := hp1) W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - exact HATn.
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cno].
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cout].
    - exact AOBN.
    - apply (nls_ob_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cob].
    - lia.
    - intros _. split; [lia|]. split; [lia|]. split; [apply ANO32; lia|].
      intros a Ha. rewrite UspN. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - intros _. split; [rewrite Hsk; apply in_or_app; right; left; reflexivity|].
      split; [exact AMRO|].
      split; [apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia]|].
      { exact HOin. }
      split; [apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia | lia]|].
      { exact HOin. }
      intros a Hr. unfold rom_view in Crom. rewrite (AV1 a). exact (Crom a Hr). }
  cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
  subst W2.
  destruct HARM as [(HAO & _) | (ln & _ & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
  assert (Hln : ln = snd r).
  { destruct Hfl as (rest & Hsk2 & Hnz'). rewrite Hsk in Hsk2. exact (nls_nul_split (snd r) ln (bsr rs ++ rest0) rest Hsk2 HnzR Hnz'). }
  subst ln.
  (* next_line's journal inside this one *)
  pose proof HJn as (_ & _ & _ & HXOn). rewrite UspN in HXOn, HFRn.
  pose proof (ajournal_gx_G_mono_x SEGS B PST ARx [] G (128 + XO) (nl_cells AT (sp0 - 112) (sp0 - 120)) NL_STK (spZ (ms_regs ms0)) []
    ly1 S1 hp1 W1 (ms_mem ms0) mdN [] ly1 S1 hp1 W1 mem2 md2 0 (fun a Ha => False_ind _ (inG_nil a Ha)) HJn) as HJn'.
  rewrite UspN in HJn'.
  pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md [] ly1 S1 hp1 W1 (ms_mem ms0) mdN kk
    NL_STK (sp0 - 128) (128 + XO) (nl_cells AT (sp0 - 112) (sp0 - 120)) [] [] ly1 S1 hp1 W1 mem2 md2 0 HJ HJn'
    ltac:(rewrite WS; unfold NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)) as HJ2.
  specialize (HJ2 ltac:(intros a (rr & Hrr & Ha); cbn [nl_cells In] in Hrr;
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
    [right; exists (AT, AT + 8); split; [left; reflexivity | cbn [fst snd]; lia] | left; rewrite WS; lia | left; rewrite WS; lia])
    HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))).
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (KEEPn : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 128 - NL_STK <= a < sp0 - 128) ->
    ~ inFP (nl_cells AT (sp0 - 112) (sp0 - 120)) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) (ms_mem ms0) a).
  { intros a Ha Hn Hcx. destruct (Z_lt_le_dec a (sp0 - 128)) as [Hlt | Hge]; [apply HFRn; [exact Ha | lia | exact Hcx]|].
    destruct (Z_lt_le_dec a (sp0 - 128 + (128 + XO))) as [Hlt2 | Hge2]; [apply HXOn; [lia | exact Hcx]|].
    apply HFRn; [exact Ha | lia | exact Hcx]. }
  assert (Hncell : forall a, ~ (sp0 - 120 <= a < sp0 - 104) -> a < AT \/ AT + 8 <= a ->
    ~ inFP (nl_cells AT (sp0 - 112) (sp0 - 120)) a).
  { intros a Hx1 Hx2 (rr & Hrr & Ha). cbn [nl_cells In] in Hrr.
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia. }
  (* back at 0x85a34: keep the four regions, reseat the frame cells line (sp + 16) and len (sp + 8) *)
  jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); apply KEEPn.
    - rewrite Vb2 in Ha. lia.
    - rewrite Vb2 in Ha. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb2 in Ha; lia.
    - rewrite Vbg in Ha. lia.
    - rewrite Vbg in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vbg in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb9 in Ha. lia.
    - rewrite Vb9 in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb9 in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. unfold AREC in *. lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC, NL_STK, NL_FRAME, ESTACK in *. lia.
    - apply Hncell; rewrite Vb33 in Ha; rewrite HreqV in Hvceil; rewrite WS in Hslo; unfold AREC in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc Ev 50 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 50)%nat -> ew Ea m = ew Ev m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (F54 : ew Ea 54 = Z_to_bv 64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
  clear HEa.
  (* atom 66: the line's address, the value next_line left at sp + 16 *)
  apply (st_ok_pi_havoc_hi 66 Ea _ _ [Z_to_bv 64 (OUT + An)]) in HS; [|vm_compute; reflexivity].
  remember (havoc Ea 66 [Z_to_bv 64 (OUT + An)]) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 66)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  assert (F66 : ew Eb 66 = Z_to_bv 64 (OUT + An)) by (rewrite HEb; reflexivity).
  clear HEb.
  assert (OLD : forall m, (m < 50)%nat -> ew Eb m = ew Ev m) by (intros m Hm; rewrite OLDb by lia; exact (OLDa m Hm)).
  assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (Vb2b : base_val Eb (Some 2%nat) = sp0 - 128) by (cbn [base_val]; rewrite OLD by lia; exact Usp).
  assert (Vb9b : base_val Eb (Some 9%nat) = HA) by (rewrite <- Vb9; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vb33b : base_val Eb (Some 33%nat) = hl_v EE) by (rewrite <- Vb33; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vbgb : base_val Eb (Some 271%nat) = VAL A_g_gone).
  { cbn [base_val]. assert (Hb : (A_TEXT <= 271 < A_LIM)%nat) by (cbv [A_TEXT A_LIM]; lia). exact (HEIb 271%nat Hb). }
  assert (HAR2 : ARx ly1 S1 hp1 W1 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
  apply (st_ok_pi_add_region Eb _ _ cnl_cells) in HS; [| reflexivity | | ].
  2: { unfold region_ok, cnl_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
    rewrite Vb2b. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 128) 8 8 (SOff 36 0) (Z.of_nat (length (snd r))));
      [cbn [sv_denot]; rewrite OLD by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; unfold APARTIAL in HlenR; lia | cbn; lia |].
      replace (sp0 - 128 + 8) with (sp0 - 120) by lia. exact Vlen2.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 128) 16 8 (SOff 66 0) (OUT + An));
      [cbn [sv_denot]; rewrite F66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (sp0 - 128 + 16) with (sp0 - 112) by lia. exact Vln2. }
  2: { apply all_disjoint_of_extents. unfold cnl_cells, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem].
    rewrite Vb2b, Vbgb, Vb9b, Vb33b. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC in *. repeat split; lia. }
  assert (SHOK2 : sh_ok SEGS BxL cnl_lSH Eb (mrestrict (w_H W1) mem2)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem2 md2 (HA + 64) 32 HAR2 AZS).
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 9 HA) by (first [rewrite OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem2 md2 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR2 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 33 (hl_v EE)) by (first [rewrite OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85a34: beqz a0 (abort); the length compare (abort) ---- *)
  rewrite N1. paj_run_tok_x RUN HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUN BR HS SHOK2 Bspan.
  { (* next_line returned 0: impossible, it found r's line *)
    exfalso. rewrite branch_eq_U, (U_atom Eb 54 1), U_lit in Hc0 by (first [rewrite OLDb by lia; exact F54 | lia]).
    apply Z.eqb_eq in Hc0. lia. }
  clear Hc0. paj_run_tok_x RUN HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  (* ---- bcmp(line, v[0].s, len) at 0x85a84, returning to 0x85a88 ---- *)
  assert (MQ2 : forall x, mrestrict (w_H W1) (ms_mem ms2) x = mrestrict (w_H W1) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr2 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem2 (ms_mem ms2) MQ2) as (AV2 & AP2).
  assert (AVc : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite AV2, KEEPn; [apply AV1 | lia | rewrite WS in Hslo; unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; rewrite WS in Hslo; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  assert (UspB : spZ (ms_regs ms2) = sp0 - 128) by (unfold spZ at 1; rewrite T2, OLD by lia; rewrite E2; apply unsigned_lit_small; lia).
  assert (HARB : ARx ly1 S1 hp1 W1 (ms_mem ms2) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat1 md2)) mat2
    (with_vm_backing (m_vm_lazy md2) mat1 md2))) by (eapply ajournal_gx_AR_x; exact HJ2).
  eapply SRr_bind.
  { eapply (aj_bcmp_gx_at_x B PST ARx LAWS (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms2) (ms_mem ms2) CNL_STK sp0 FPc ly S hp W mem md []
      ly1 S1 hp1 _ kk (OUT + An) (fst r) (Z.of_nat (length (snd r))) (-128) (Z_to_bv 64 (BASE + 14236)) HG AX16 HJ2).
    - rewrite T10. exact F66.
    - rewrite T11, OLD by lia. exact E35.
    - rewrite T12, OLD by lia. exact E36.
    - unfold APARTIAL in HlenR. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite UspB. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ESTACK. lia.
    - rewrite T3, OLD by lia. rewrite (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite T4, OLD by lia. rewrite (EEo 4%nat 4%bv eq_refl). exact R4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AV2. replace a with (OUT + (a - OUT)) by lia. rewrite (Hob2 (a - OUT)) by lia. discriminate.
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AVc by lia. unfold aview, arm in *. replace a with (fst r + Z.of_nat (Z.to_nat (a - fst r))) by lia.
      rewrite (garr8_mbyte SEGS _ _ _ _ HgarR0) by (unfold bzs; rewrite length_map; lia). discriminate.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - unfold amem_range in *. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
    - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - intros Hp. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia.
    - intros Hp. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia. }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & vb & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
  (* r's line in the stream, as next_line left it *)
  assert (STR : forall i, (i < length (snd r))%nat ->
    aview SEGS (w_H W1) mem2 (OUT + An + Z.of_nat i) = Some (bv_unsigned (nth i (snd r) (Z_to_bv 8 0)))).
  { intros i Hi. replace (OUT + An + Z.of_nat i) with (OUT + (An + Z.of_nat i)) by lia.
    rewrite (Hob2 (An + Z.of_nat i)) by lia. do 2 f_equal.
    replace (Z.to_nat (An + Z.of_nat i)) with (Z.to_nat An + i)%nat by lia.
    rewrite <- nls_nth_skipn, Hsk. rewrite app_nth1 by exact Hi. reflexivity. }
  (* the line is v[0].s's text: bcmp returned 0 *)
  assert (Hv0 : vb = w64 0).
  { apply Hcmp. intros i Hi. rewrite AV2, AVc by lia.
    replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite STR by lia.
    rewrite (nls_view_of_garr8 W1 mem1 (fst r) (snd r) (Z.to_nat i) HgarR0) by lia. reflexivity. }
  assert (HAR3 : ARx ly1 S1 hp1 W1 mem3 md3) by (eapply ajournal_gx_AR_x; exact HJ3).
  jafter_call_keep_pi HS 67%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); rewrite ?Vb2b, ?Vbgb, ?Vb9b, ?Vb33b in Ha; apply Hfr3;
    rewrite ?HreqV in Hvceil; rewrite ?WS in Hslo; unfold AREC, ESTACK in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Eb 67 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
  assert (OLDc : forall m, (m < 67)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
  assert (F71 : ew Ec 71 = Z_to_bv 64 0) by (rewrite HEc; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv, Hv0; reflexivity).
  clear HEc.
  assert (SHOK3 : sh_ok SEGS BxL cnl_lSH Ec (mrestrict (w_H W1) mem3)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem3 md3 (HA + 64) 32 HAR3 AZS).
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 9 HA) by (first [rewrite OLDc, OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem3 md3 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR3 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 33 (hl_v EE)) by (first [rewrite OLDc, OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85a88: bnez a0 (abort), then gesture_model(s, line, len) ---- *)
  paj_run_tok_x RUN HS HJ3 SHOK3 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  { exfalso. rewrite branch_ne_U, (U_atom Ec 71 0 F71), U_lit in Hc0 by lia. cbn in Hc0. discriminate. }
  clear Hc0. paj_run_to_tok_x RUNTO HS HJ3 SHOK3 Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ3 : forall x, mrestrict (w_H W1) (ms_mem ms4) x = mrestrict (w_H W1) mem3 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr4 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr3 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem3 (ms_mem ms4) MQ3) as (AV3 & AP3).
  assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 128 - 2 * ESTACK <= a < sp0 - 128) ->
    aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) (ms_mem ms2) a).
  { intros a Ha Hn. rewrite AV3. apply Hfr3; [exact Ha | lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  assert (LOW : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). exact (AVc a Ha). }
  assert (FRM : forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (unfold ESTACK; lia). rewrite AV2, KEEPn; [apply AV1 | lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; lia. }
  assert (PRS : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms4) a)
    by (intros a Hp; apply AP3, Hpres3, AP2, HPn, AP1, Hp).
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms4) md1 _ HAR1 LOW FRM PRS (or_intror (conj HOin HCO)) HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  pose proof (nls_err_kept W1 mem1 (ms_mem ms4) LOW HERR) as HERR'.
  assert (Ecp' : cpos gone A0 (pre ++ [r]) = An + Z.of_nat (length (snd r)) + 1).
  { unfold An, cpos. rewrite Hg0. cbn [Z.eqb]. rewrite nls_bsr_app, length_app, nls_bsr_cons, length_app. cbn [length].
    change (bsr []) with (@nil byte). cbn [length]. lia. }
  eapply (cnl_gm pre r rs ly1 S1 hp1 kk H1 jk W1 (ms_regs ms4) (ms_mem ms4) _ (OUT + An) OUT CO
    HEQ HJ3 HPK' HERR' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite Ecp'. apply (nls_vm_kept W1 W1 mem2 (ms_mem ms4)); [|exact Vat2].
    intros i Hi. rewrite KEEPb by (cbn in Hi; unfold ESTACK; lia). exact (AV2 _).
  + exact HCONST'.
  + right. split; [exact HCO|]. split; [exact HOin | exact HOn].
  + intros _. exists rest0. rewrite Ecp'.
    replace (Z.to_nat (An + Z.of_nat (length (snd r)) + 1)) with ((length (snd r) + 1) + Z.to_nat An)%nat by lia.
    rewrite <- skipn_skipn, Hsk, skipn_app, skipn_all2 by lia.
    replace (length (snd r) + 1 - length (snd r))%nat with 1%nat by lia. reflexivity.
  + exact HFRM'.
  + unfold cnl_regs_ok.
    assert (OLDx : forall m, (m < 50)%nat -> ew Ec m = ew Ev m) by (intros m Hm; rewrite OLDc, OLD by lia; reflexivity).
    assert (P24 : getr (ms_regs ms4) 24 = getr regs1 24).
    { rewrite Q24, O24. apply bv_eq. rewrite (HEIc 386%nat ltac:(cbv [A_TEXT A_LIM]; lia)), (HEI 386%nat ltac:(cbv [A_TEXT A_LIM]; lia)).
      reflexivity. }
    rewrite P24.
    rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q22, Q23, Q25, Q26, Q27. repeat (rewrite OLDx by lia).
    rewrite <- O23, <- O26, <- O8, <- O19, <- O2, <- O3, <- O4, <- O9, <- O18, <- O22, <- O25, <- O27.
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10, OLDc, OLD by lia. exact E9.
  + rewrite Q11, OLDc by lia. exact F66.
  + rewrite Q12, OLDc, OLD by lia. exact E36.
  + apply nls_garr8_of_view. intros i Hi. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). rewrite AV2. exact (STR i Hi).
  + exact HOin.
  + intros Hx. apply HOn. apply in_or_app. right. exact Hx.
  + lia.
  + lia.
- (* g_gone set: the text v[0] goes to gesture_model unread *)
  assert (Hg1 : gone <> 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_neq in Hc; exact Hc).
  assert (Ecp : forall p, cpos gone A0 p = A0) by (intros p; unfold cpos; destruct (Z.eqb_spec gone 0); [contradiction | reflexivity]).
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ) as (AV & AP).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms0) md1 _ HAR1 (fun a _ => AV a) (fun a _ => AV a) AP HOBx HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  pose proof (nls_err_kept W1 mem1 (ms_mem ms0) (fun a _ => AV a) HERR) as HERR'.
  eapply (cnl_gm pre r rs ly1 S1 hp1 kk H1 jk W1 (ms_regs ms0) (ms_mem ms0) _ (fst r) (fst r) (Z.of_nat (length (snd r)) + 1)
    HEQ HJ HPK' HERR' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite !Ecp in *. apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HAT].
  + exact HCONST'.
  + exact HOB.
  + intros Hg0. contradiction.
  + exact HFRM'.
  + unfold cnl_regs_ok.
    rewrite (eq_trans Q2 (eq_sym O2)), (eq_trans Q3 (eq_sym O3)), (eq_trans Q4 (eq_sym O4)), (eq_trans Q8 (eq_sym O8)),
      (eq_trans Q9 (eq_sym O9)), (eq_trans Q18 (eq_sym O18)), (eq_trans Q19 (eq_sym O19)), (eq_trans Q22 (eq_sym O22)),
      (eq_trans Q23 (eq_sym O23)), (eq_trans Q24 (eq_sym O24)), (eq_trans Q25 (eq_sym O25)), (eq_trans Q26 (eq_sym O26)),
      (eq_trans Q27 (eq_sym O27)).
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10. exact E9.
  + rewrite Q11. exact E35.
  + rewrite Q12. exact E36.
  + apply (nls_garr8_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HgarR0].
  + exact HinR.
  + exact HnH1.
  + lia.
  + lia.
Qed.
(* the rest of the iteration: free, memmove, n - 1, then the loop test *)
(* `~ in_wrange E rs a` for the regions this walk's runs carry: their one write window is s->expected.n,
   [HA + 72, HA + 76).  EQ: the env's base_val of register 9 is HA; Hout: a is off that window. *)
Ltac cnl_nowr EQ Hout :=
let rr := fresh "rr" in let Hinr := fresh "Hinr" in let Hrr := fresh "Hrr" in
intros (rr & Hinr & Hrr);
lazymatch type of Hinr with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hinr end;
cbn [In] in Hinr;
repeat (destruct Hinr as [<- | Hinr]);
try (destruct Hinr);
try (cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrr);
rewrite ?EQ in Hrr;
first [exfalso; lia | apply Hout; lia | apply Hout; clear - Hrr; lia].
Lemma cnl_drop : forall pre r rs W1 regs1 mem1 md1,
(rs <> [] -> forall W2 regs2 mem2 md2, cnl_inv (pre ++ [r]) rs W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cnl_loop)) mem2 (seg_rom SEGS)) md2) Post) ->
cnl_mid pre r rs W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
pose proof AX16 as HX16. pose proof AHAE as EHA. pose proof AJLT as Hj4. pose proof AGA as HGa.
pose proof AZS as Hzs. pose proof AEN as HnEE. pose proof AGN as Hgone. pose proof APRE as HPRE.
intros pre r rs W1 regs1 mem1 md1 IHl HM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16656) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (cnl_ha HA j EHA Hj4 HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
destruct HM as (ly1 & S1 & hp1 & kk & H1 & jk & HrecE & HJ0 & HPK & HERR & HSRC & HND & HTX & HCAP & HNn & HCb &
  HPERM & HFRS & HMLE & HMOK & HROOM & HRMr & HCNTr & HATv & HCONST & HOB & HSKIP & HFRM & HREGS).
assert (HAR1 : ARx ly1 S1 hp1 W1 mem1 md1) by (eapply ajournal_gx_AR_x; exact HJ0).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAE0 & HAH0 & _).
assert (HAE : alist_at B ly1 S1 W1 mem1 (HA + 64) (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) true) by exact HAE0.
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0.
clear HAE0 HAH0.
destruct (cnl_alist_parts ly1 S1 W1 mem1 (HA + 64) (hl_v EE) (hl_cap EE) (r :: rs) jk true HAE)
  as (MvE & MnE & McE & MwE & (HnleC & HcapLt) & HvvE & HNDvE & HninE & HFallE).
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR). unfold APARTIAL in HlenR.
assert (HsndNN : 0 <= Z.of_nat (length (snd r))) by apply Nat2Z.is_nonneg.
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))).
{ cbn [length]. rewrite Nat2Z.inj_succ. pose proof (Nat2Z.is_nonneg (length rs)). lia. }
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ unfold hl_n in HnEE. rewrite HrecE, length_app, Nat2Z.inj_add in HnEE.
  pose proof (Nat2Z.is_nonneg (length pre)). lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
pose proof CNLAP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CNR). cbv zeta in CNR.
assert (ROMIMG : forall a, in_rom SEGS a -> in_img SEGS a)
  by (intros a (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
assert (ROMW : forall a, in_rom SEGS a -> ~ (HA + 72 <= a < HA + 76)).
{ intros a Hrom Hc. apply (CNR a); [rewrite EHA in Hc; unfold ASRC in Hc; pose proof (Nat2Z.is_nonneg j); lia | exact Hrom]. }
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & _ & Hrreq1 & Hrceil & Hceil2 & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
destruct (cnl_rec_fields B ly1 S1 W1 mem1 (HA + 64)
  (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) true 0%nat HAE ltac:(cbn [hl_recs length]; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) + 16 * Z.of_nat 0) by (cbn; lia).
  exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by lia.
  replace (hl_v EE + 8) with (hl_v (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) + 16 * Z.of_nat 0 + 8) by (cbn; lia).
  exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
destruct (cnl_mk A_cnl_back W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn Hzs MwE HFRM (proj1 HCONST) Hgone MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(lia)) as [HS SHOK].
(* the disjunctive facts go into a pair (not a Prop), so that lia does not split on them; unpacked at the end *)
pose proof (Dgn, Dgot, Dcell, HOB) as DPACK. clear Dgn Dgot Dcell HOB.
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew Ev 3 = w64 (as_gp B)) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew Ev 4 = w64 (as_tp B)) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (Usp : bv_unsigned (ew Ev 2) = sp0 - 128) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Vb9 : base_val Ev (Some 9%nat) = HA) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (EX : forall k, (k < 18)%nat -> ew Ev (32 + k) = nth k (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEv. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v EE)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew Ev 34 = Z_to_bv 64 (Z.of_nat (length (r :: rs)))) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 (fst r)) by exact (EX 3%nat ltac:(lia)).
assert (ES : forall k, (37 <= k < 50)%nat -> ew Ev k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0)).
{ intros k Hk. assert (Ek : k = (32 + (5 + (k - 37)))%nat) by lia. rewrite Ek at 1.
  rewrite (EX (5 + (k - 37))%nat ltac:(lia)). unfold cnl_lx. rewrite map_app. cbn [map app nth Nat.add].
  apply map_nth. }
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone))
  by (rewrite HEv; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Vb2 : base_val Ev (Some 2%nat) = sp0 - 128) by (cbn [base_val]; exact Usp).
assert (Vbg : base_val Ev (Some A_g_gone) = VAL A_g_gone)
  by (cbn [base_val]; rewrite Eg; apply unsigned_lit_small; exact (pa_val_range _)).
clear HEv EX.
pose proof HG as HGok. pose proof (pal_free B TL) as HBfree.
assert (QA : ASTACK = 16384) by reflexivity.
(* the image bytes the walk reads: the 96 bytes of the source (in g_s and in G), g_gone, g_nout, g_out, the literals *)
assert (RO : forall b n a, In (b, n) cnl_ro -> b <= a < b + n ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros b n a Hin Ha.
  assert (Hg : inG cnl_ro a) by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  destruct (HGR a Hg) as (Hi & Ho & _). split; [exact Hi|]. split; [exact Ho | exact (proj1 (HGRR a Hg))]. }
assert (GH : forall a, HA <= a < HA + 96 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. apply (RO (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; right; right; right; left; reflexivity)).
  rewrite EHA in Ha. unfold ASRC in Ha. lia. }
(* ---- 0x85a9c .. 0x85abc: shadow checks, a0 = v[0].s, jal free ---- *)
paj_run_tok_x RUN HS HJ0 SHOK Bspan.
{ cbv [ss_mem ss_cnll cnl_lregions cnl_saved cnl_gone cnl_headL cnl_vec].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g;
  [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9 in Ha; apply HGa; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
rename HF into HFa. rename HFr into HFra. rename HG0 into HGra.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite HBfree.
assert (HAR1m : ARx ly1 S1 hp1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR_x; exact HJ0).
assert (HXnn : 0 <= cnl_go MT (texts H1) (hl_cap H1) rs).
{ apply cnl_go_nonneg. destruct HAH as (_ & _ & _ & _ & (HnH & _) & _). unfold hl_n in HnH. lia. }
assert (Usp2 : spZ (ms_regs ms) = sp0 + -128)
  by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite Q2, Usp; lia).
(* ---- free(v[0].s) at 0x85abc, returning to 0x85ac0 (BASE + 14292) ---- *)
eapply SRr_bind.
{ apply (cnl_free_gx XO [(AT, AT + 8)] W1 (ms_regs ms) (ms_mem ms) CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 _ kk
    (fst r) (Z.of_nat (length (snd r)) + 1) (-128) (Z_to_bv 64 (BASE + 14292)) []
    (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr)%nat HJ0 HX16 HinR).
  - rewrite Q10, E35. reflexivity.
  - exact Usp2.
  - reflexivity.
  - lia.
  - rewrite WS, QA. lia.
  - rewrite Q3, E3. reflexivity.
  - rewrite Q4, E4. reflexivity.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly1 _ (spZ (ms_regs ms)) (HA + 72) [] (ms_regs ms)).
    + apply achain_low. lia.
    + rewrite Usp2. lia.
    + unfold s0Z. rewrite Q8, E9, (unsigned_lit_small HA) by lia. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_check_no_loss + 0x168); [exact HCTX_cnl_free|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold AF_fr_check_no_loss. lia.
  - (* the room round: r's free is the one free the budget owes before the rest *)
    exact HRMr.
  - exact (cnl_cntm_free_pre _ r rs H1 _ HCNTr).
  - intros _ i Hi. exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; lia].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r, Z.of_nat (length (snd r)) + 1)).
    apply in_or_app. left. unfold list_blks. apply in_or_app. right.
    apply (in_map (fun rr => (fst rr, Z.of_nat (length (snd rr)) + 1))). rewrite HrecE. apply in_or_app. right. left. reflexivity.
  - apply (mok_station MT S1 S1 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) 0 (mo_free MT) ML HMOK
      (mo_le_refl MT ML S1) (mo_free_nonneg MT ML)). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs2 & HK & Hle & HRM2 & Herr2 & Hpres2).
assert (HAR2 : ARx ly2 S2 hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
(* an image byte outside the allocator's statics and errno: the free kept its view and its presence *)
assert (IMGK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a /\
  (apresent (w_H W1) (ms_mem ms) a -> apresent (w_H W2) mem2 a)).
{ intros a Hi Ho He. split; [exact (proj1 (proj2 (proj2 HK)) a Hi Ho He)|].
  apply (Hpres2 a Hi).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly1 S1 hp1 W1 (ms_mem ms) _ a HAR1m Hi) Hw)).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 hp2 W2 mem2 md2 a HAR2 Hi) Hw)).
  - exact He.
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 (ms_mem ms) _ (fst r) _ a HAR1m HinR Hr Hi). }
jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
   rewrite ?Vb2, ?(Vbg : base_val Ev (Some 271%nat) = VAL A_g_gone), ?Vb9).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK); lia.
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (RO (VAL A_g_gone) 1 a ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    exact (proj1 (IMGK a Hi Ho He)).
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GH a ltac:(lia)) as (Hi & Ho & He). exact (proj1 (IMGK a Hi Ho He)).
  - intros a Ha Hw. destruct (GH a ltac:(lia)) as (Hi & Ho & He).
    apply (cnl_writable_kept_w W1 W2 (ms_mem ms) mem2 a); [exact (proj2 (IMGK a Hi Ho He)) | exact Hwle2 | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc Ev 50 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 50)%nat -> ew Ea m0 = ew Ev m0)
  by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
clear HEa.
assert (F2 : ew Ea 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite OLDa by lia; exact E2).
assert (F9 : ew Ea 9 = Z_to_bv 64 HA) by (rewrite OLDa by lia; exact E9).
assert (F22 : ew Ea 22 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E22).
assert (Vb9a : base_val Ea (Some 9%nat) = HA) by (cbn [base_val]; rewrite F9; apply unsigned_lit_small; lia).
assert (SHOK2 : sh_ok SEGS BxL cnl_dSH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cnl_dSH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - apply (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold BxL. rewrite (U_atom Ea 22 SB F22) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 9 HA F9) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x85ac0 .. 0x85ae4: shadow checks, a1 = v + 16, a2 = (n - 1) * 16, jal __asan_memmove ---- *)
paj_run_tok_x RUN HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g;
  [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
rename HF into HFb. rename HFr into HFrb. rename HG0 into HGrb.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 (ms_mem ms0) _ (kk + 1) HJ2) as HAR3.
(* the vector is still live after the free (it is not r's block) *)
assert (Hvin2 : In (hl_v EE, AREC * hl_cap EE) (ablocks B ly2 S2)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in HvinE.
  apply in_app_or in HvinE as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. apply HninE. cbn [map]. left. first [exact Ex | exact (eq_sym Ex)]. }
destruct (alx_blocks _ _ _ LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ _ _ HAR3 Hvin2) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
rewrite HreqV in Vceil, Vapp, Vpres.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
assert (F33 : ew Ea 33 = Z_to_bv 64 (hl_v EE)) by (rewrite OLDa by lia; exact E33).
assert (F34 : ew Ea 34 = Z_to_bv 64 (Z.of_nat (length (r :: rs)))) by (rewrite OLDa by lia; exact E34).
assert (F3 : ew Ea 3 = w64 (as_gp B)) by (rewrite OLDa by lia; exact E3).
assert (F4 : ew Ea 4 = w64 (as_tp B)) by (rewrite OLDa by lia; exact E4).
assert (Uspm : spZ (ms_regs ms0) = sp0 - 128)
  by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite P2, F2;
      apply unsigned_lit_small; lia).
assert (R10 : getr (ms_regs ms0) 10 = w64 (hl_v EE)) by (rewrite P10, F33; reflexivity).
assert (R11 : getr (ms_regs ms0) 11 = w64 (hl_v EE + 16)).
{ rewrite P11, F33, unsigned_lit_small by lia. reflexivity. }
assert (R12 : getr (ms_regs ms0) 12 = w64 (AREC * (Z.of_nat (length (r :: rs)) - 1))).
{ rewrite P12, F34, cnl_cnt16 by lia. unfold w64, AREC. f_equal. lia. }
assert (Ecap : (hl_cap EE =? 0) = false) by (apply Z.eqb_neq; lia).
assert (HvFP : forall a, hl_v EE <= a < hl_v EE + AREC * hl_cap EE -> inFP FPc a).
{ intros a Ha. exists (hl_v EE, hl_v EE + req_size (AREC * hl_cap EE)). split; [|cbn [fst snd]; rewrite HreqV; lia].
  unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v EE, AREC * hl_cap EE)).
  apply in_or_app. left. unfold list_blks. rewrite Ecap. left. reflexivity. }
(* rom_view across the free: the two runs wrote only s->expected.n (no rom byte of g_s), and the free keeps a rom
   byte either because the runtime owns it and it is pinned, or because it is an image byte it did not touch
   (W_journal.v acall_kept_rom_view; the only place this walk reads ROMNS) *)
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a ltac:(lia));
    [exact (Crom a Hrom) | cnl_nowr Vb9 (ROMW a Hrom)] end. }
assert (ROM2 : rom_view SEGS W2 mem2)
  by (eapply (acall_kept_rom_view_x SEGS B ARx LAWS); [exact HAR2 | exact HK | exact ROMNS | exact ROM1]).
assert (ROMK : rom_view SEGS W2 (ms_mem ms0)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a ltac:(lia));
    [exact (ROM2 a Hrom) | cnl_nowr Vb9a (ROMW a Hrom)] end. }
(* ---- the memmove of the records above 0, 0x85ae4 ---- *)
eapply SRr_bind.
{ clear HSKIP IHl.
  eapply (aj_gx_entry_at_x B PST ARx LAWS G XO [(AT, AT + 8)] ESTACK (SIGMA WS_asan_memmove)
  (fun a => hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1)) _
  W2 (ms_regs ms0) (ms_mem ms0) CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 _ (kk + 1)
  (- 128) (Z_to_bv 64 (BASE + 14332)) HGok HX16 HJ2).
- exact Uspm.
- reflexivity.
- lia.
- lia.
- rewrite WS, Hes. lia.
- rewrite P3. exact F3.
- rewrite P4. exact F4.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a. destruct (Z_le_gt_dec (hl_v EE) a) as [Hd1|Hd1]; [|right; lia].
  destruct (Z_lt_ge_dec a (hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))) as [Hd2|Hd2]; [left; lia | right; lia].
- intros a Ha HGb. exfalso.
  apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact (proj1 (HGok a HGb))].
- intros a Ha HnG. split; [|unfold AREC in *; lia].
  right. left. split; [apply HvFP; unfold AREC in *; lia|].
  exists (hl_v EE), (AREC * hl_cap EE). split; [exact Hvin2 | rewrite HreqV; unfold AREC in *; lia].
- intros HPRE2 HSC.
  (* the destination is a heap block, so no byte of it is an image byte (the premise W_sites.v's amemmove_realizes
     gains in its proved form, pf-calls 84b1925e3d3 W_sites.v:197; W1's W_list_drop.v:1097-1099 proves it the same way) *)
  assert (MNIMG : forall a, hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1) -> ~ in_img SEGS a).
  { intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE) a HAR3 Hvin2).
    rewrite HreqV. unfold AREC in *. lia. }
  apply (AMOVE ly2 S2 hp2 W2 (ms_regs ms0) (ms_mem ms0) _
    (hl_v EE) (hl_v EE + 16) (AREC * (Z.of_nat (length (r :: rs)) - 1)) HPRE2 R10 R11 R12).
  + unfold AREC in *; lia.
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split; [|split].
    * apply (apresent_writable SEGS). exact (proj1 (Vpres a ltac:(unfold AREC in *; lia))).
    * exact (proj2 (Vpres a ltac:(unfold AREC in *; lia))).
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *. lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split.
    * destruct (proj1 (Vpres a ltac:(unfold AREC in *; lia))) as [Hh [b Hb]].
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *. lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + exact ROMK.
  + intros Hpos. split;
    unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *; lia.
  + exact MNIMG. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hres3 & Hmov) & Hfr3 & Hpres3).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 mem3 md3 (kk + 1) HJ3) as HAR4.
assert (Vb2a : base_val Ea (Some 2%nat) = sp0 - 128)
  by (cbn [base_val]; rewrite F2; apply unsigned_lit_small; lia).
assert (Vbga : base_val Ea (Some A_g_gone) = VAL A_g_gone)
  by (cbn [base_val]; apply HEIa; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
(* the memmove wrote only inside the vector: the frame slots and the two image regions are kept *)
assert (MOFF : forall a, in_img SEGS a -> ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))).
{ intros a Hi Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact Hi]. }
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0;1;2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ clear HSKIP IHl.
  cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
   rewrite ?Vb2a, ?(Vbga : base_val Ea (Some 271%nat) = VAL A_g_gone), ?Vb9a).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold AREC, ESTACK in *; lia.
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3;
    [pose proof (pa_val_range A_g_gone); lia
    | apply MOFF; exact (proj1 (RO (VAL A_g_gone) 1 a ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)))
    | pose proof (pa_img_range a (proj1 (RO (VAL A_g_gone) 1 a ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)))); lia].
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3;
    [pose proof (pa_img_range a (proj1 (GH a ltac:(lia)))); lia
    | apply MOFF; exact (proj1 (GH a ltac:(lia)))
    | pose proof (pa_img_range a (proj1 (GH a ltac:(lia)))); lia].
  - intros a Ha Hw. apply (cnl_writable_kept_w W2 W2 (ms_mem ms0) mem3 a);
    [intros Hp; exact (Hpres3 a Hp) | apply wle_refl | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 66 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m0, (m0 < 66)%nat -> ew Eb m0 = ew Ea m0)
  by (intros m0 Hm0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm0).
clear HEb.
assert (K2 : ew Eb 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite OLDb by lia; exact F2).
assert (K9 : ew Eb 9 = Z_to_bv 64 HA) by (rewrite OLDb by lia; exact F9).
assert (K22 : ew Eb 22 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact F22).
assert (K33 : ew Eb 33 = Z_to_bv 64 (hl_v EE)) by (rewrite OLDb by lia; exact F33).
assert (K34 : ew Eb 34 = Z_to_bv 64 (Z.of_nat (length (r :: rs)))) by (rewrite OLDb by lia; exact F34).
assert (K3 : ew Eb 3 = w64 (as_gp B)) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E3).
assert (K4 : ew Eb 4 = w64 (as_tp B)) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E4).
assert (E18 : ew Ev 18 = w64 AT) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (K18 : ew Eb 18 = w64 AT) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E18).
assert (KS : forall k, (37 <= k < 50)%nat -> ew Eb k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0))
  by (intros k Hk; rewrite OLDb by lia; rewrite OLDa by lia; exact (ES k Hk)).
assert (Vb9b : base_val Eb (Some 9%nat) = HA) by (cbn [base_val]; rewrite K9; apply unsigned_lit_small; lia).
assert (SHOK3 : sh_ok SEGS BxL cnl_dSH Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, cnl_dSH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - apply (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem3 md3 (HA + 64) 32 HAR4 Hzs).
  - unfold BxL. rewrite (U_atom Eb 22 SB K22) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Eb 9 HA K9) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x85ae8 .. 0x85af4: n - 1 into s->expected.n, then the loop test ---- *)
paj_run_tok_x RUN HS HJ3 SHOK3 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g;
  [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
rename HF into HFc. rename HFr into HFrc. rename HG0 into HGrc.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 (ms_mem ms1) _ (kk + 1) HJ3) as HARF.
(* ---- what the free, the memmove and the three runs kept, from (W1, mem1) to (W2, ms_mem ms1) ---- *)
(* an image byte off s->expected.n *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 72 <= a < HA + 76) -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hi Ho He Hw. pose proof (pa_img_range a Hi) as Har.
  clear HSKIP IHl.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a ltac:(lia)); [| cnl_nowr Vb9b Hw] end.
  rewrite (Hfr3 a ltac:(lia) ltac:(apply MOFF; exact Hi) ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a ltac:(lia)); [| cnl_nowr Vb9a Hw] end.
  rewrite (proj1 (proj2 (proj2 HK)) a Hi Ho He).
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a ltac:(lia)); [reflexivity | cnl_nowr Vb9 Hw] end. }
(* a byte of a live block other than the freed text, off the moved records *)
assert (KBLK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1)) ->
  ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1)) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros p n a Hin Ha Hnr Hnm.
  clear HSKIP IHl.
  destruct (cnl_blk ly1 S1 W1 mem1 md1 p n HAR1 Hin) as (_ & Hp4096 & _ & _ & Hpr1 & Hpc & _).
  assert (Hni : ~ in_img SEGS a) by exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 p n a HAR1 Hin Ha).
  assert (Hnw : ~ (HA + 72 <= a < HA + 76)) by (intros Hc; apply Hni; exact (proj1 (GH a ltac:(lia)))).
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a Ha64); [| cnl_nowr Vb9b Hnw] end.
  rewrite (Hfr3 a Ha64 Hnm ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a Ha64); [| cnl_nowr Vb9a Hnw] end.
  replace a with (p + (a - p)) by lia.
  rewrite (proj1 (proj2 HK) p n (a - p) Hin ltac:(lia) ltac:(cbv beta; intros Hc; apply Hnr; rewrite HreqR; lia)).
  replace (p + (a - p)) with a by lia.
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a Ha64); [reflexivity | cnl_nowr Vb9 Hnw] end. }
(* a byte above the allocator's ceiling, off the scratch the callees used *)
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 128 - ASTACK <= a < sp0 - 128) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hs.
  clear HSKIP IHl.
  assert (Hnw : ~ (HA + 72 <= a < HA + 76)) by lia.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a ltac:(lia)); [| cnl_nowr Vb9b Hnw] end.
  rewrite (Hfr3 a ltac:(lia) ltac:(unfold AREC in *; lia) ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a ltac:(lia)); [| cnl_nowr Vb9a Hnw] end.
  rewrite (proj1 HK a Ha ltac:(lia)).
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a ltac:(lia)); [reflexivity | cnl_nowr Vb9 Hnw] end. }
(* the records that moved down by one *)
assert (KMOV : forall k, 0 <= k < AREC * (Z.of_nat (length (r :: rs)) - 1) ->
  aview SEGS (w_H W2) (ms_mem ms1) (hl_v EE + k) = aview SEGS (w_H W1) mem1 (hl_v EE + AREC + k)).
{ intros k Hk.
  clear HSKIP IHl.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) (fst r)
    (Z.of_nat (length (snd r)) + 1) HAR1 HvinE HinR
    ltac:(intros Heq; injection Heq as Heq _; apply HninE; cbn [map]; left; first [exact Heq | exact (eq_sym Heq)])) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite HreqV, HreqR in DJ.
  assert (Hni1 : ~ in_img SEGS (hl_v EE + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE)); [exact HAR1 | exact HvinE | rewrite HreqV; unfold AREC in *; lia]).
  assert (Hni2 : ~ in_img SEGS (hl_v EE + AREC + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE)); [exact HAR1 | exact HvinE | rewrite HreqV; unfold AREC in *; lia]).
  assert (Hnw1 : ~ (HA + 72 <= hl_v EE + k < HA + 76))
    by (intros Hc; apply Hni1; exact (proj1 (GH (hl_v EE + k) ltac:(lia)))).
  assert (Hnw2 : ~ (HA + 72 <= hl_v EE + AREC + k < HA + 76))
    by (intros Hc; apply Hni2; exact (proj1 (GH (hl_v EE + AREC + k) ltac:(lia)))).
  assert (Hnw2b : ~ (HA + 72 <= hl_v EE + 16 + k < HA + 76)) by (unfold AREC in Hnw2; exact Hnw2).
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc (hl_v EE + k) ltac:(unfold AREC in *; lia));
    [| cnl_nowr Vb9b Hnw1] end.
  rewrite (Hmov k Hk).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb (hl_v EE + 16 + k) ltac:(unfold AREC in *; lia));
    [| cnl_nowr Vb9a Hnw2b] end.
  replace (hl_v EE + 16 + k) with (hl_v EE + (16 + k)) by lia.
  rewrite (proj1 (proj2 HK) (hl_v EE) (AREC * hl_cap EE) (16 + k) HvinE
    ltac:(rewrite HreqV; unfold AREC in *; lia) ltac:(cbv beta; unfold AREC in *; lia)).
  replace (hl_v EE + (16 + k)) with (hl_v EE + AREC + k) by (unfold AREC; lia).
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra (hl_v EE + AREC + k) ltac:(unfold AREC in *; lia));
    [reflexivity | cnl_nowr Vb9 Hnw2] end. }
(* presence: an image byte that was there is there *)
assert (KPRES : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) (ms_mem ms1) a).
{ intros a Hi Ho He Hp.
  apply (apresent_grows (w_H W2) mem3 (ms_mem ms1) a HGrc). apply Hpres3.
  apply (apresent_grows (w_H W2) mem2 (ms_mem ms0) a HGrb).
  apply (proj2 (IMGK a Hi Ho He)). apply (apresent_grows (w_H W1) mem1 (ms_mem ms) a HGra). exact Hp. }
(* the blocks that survive the free *)
assert (BLK2 : forall p n, In (p, n) (ablocks B ly1 S1) -> (p, n) <> (fst r, Z.of_nat (length (snd r)) + 1) ->
  In (p, n) (ablocks B ly2 S2)).
{ intros p n Hin Hne2. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | exfalso; exact (Hne2 (eq_sym Hx)) | right; exact Hx]. }
(* the source's block addresses are pairwise apart, so every block but the freed text survives untouched *)
assert (NDB : NoDup (hs_blocks (set_exp_held h (cnl_E (r :: rs) jk) H1)))
  by (pose proof HSRC as HSRCx; repeat (destruct HSRCx as [_ HSRCx]); exact HSRCx).
apply NoDup_ListNoDup in NDB. unfold cnl_E in NDB.
rewrite cnl_blocks_set, (cnl_lb_nil (hl_v EE) (hl_cap EE) (r :: rs) jk Hcpos) in NDB. cbn [map] in NDB.
pose proof (cnl_nodup_two (list_blocks (hs_pending h)) [hs_partial h] (map fst rs) (list_blocks H1)
  (hl_v EE) (fst r) NDB) as NDX.
assert (NDnew : NoDup (hs_blocks (set_exp_held h (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) H1))).
{ apply NoDup_ListNoDup. unfold cnl_E.
  rewrite cnl_blocks_set, (cnl_lb_nil (hl_v EE) (hl_cap EE) rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk) Hcpos).
  exact (cnl_nodup_drop (list_blocks (hs_pending h)) [hs_partial h] [hl_v EE] (map fst rs) (list_blocks H1)
    (fst r) NDB). }
(* every live block but the freed text and the vector keeps its bytes and its writability *)
assert (HreqT : forall x : Z * list byte, req_size (Z.of_nat (length (snd x)) + 1) = Z.of_nat (length (snd x)) + 1).
{ intros x. unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq;
  [apply Z.eqb_eq in Eq; pose proof (Nat2Z.is_nonneg (length (snd x))); lia | reflexivity]. }
assert (KOFF : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1))).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 p n (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 Hin HinR
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. lia. }
assert (KOFV : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> hl_v EE -> p <= a < p + req_size n ->
  ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 p n (hl_v EE) (AREC * hl_cap EE) HAR1 Hin HvinE
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite HreqV in DJx. unfold AREC in *. lia. }
assert (KBK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <> hl_v EE -> p <= a < p + req_size n ->
  abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros p n a Hin Hp1 Hp2 Ha. split.
  - exact (KBLK p n a Hin Ha (KOFF p n a Hin Hp1 Ha) (KOFV p n a Hin Hp2 Ha)).
  - intros Hw.
    destruct (cnl_blk ly2 S2 W2 (ms_mem ms1) _ p n HARF
      (BLK2 p n Hin ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))))
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres).
    exact (apresent_writable SEGS _ _ _ (proj1 (Hpres a Ha))). }
(* the head bytes of the source, off s->expected.n *)
assert (KHD : forall a, HA <= a < HA + 96 -> ~ (HA + 72 <= a < HA + 76) -> abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros a Ha Hw. destruct (GH a Ha) as (Hi & Ho & He). split.
  - exact (KIMG a Hi Ho He Hw).
  - intros Hwr. apply (cnl_writable_kept_w W1 W2 mem1 (ms_mem ms1) a);
    [intros Hp; exact (KPRES a Hi Ho He Hp) | exact Hwle2 | exact Hwr]. }
(* the blocks a list names, as members of the state before the free *)
assert (ABLK : forall (l : hlist) LA lines, alist_at B ly1 S1 W1 mem1 LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly1 S1)).
{ intros l LA lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
    destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
  - apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
    rewrite Forall_forall in HF. exact (proj1 (HF x Hx)). }
assert (ABF : forall (l : hlist) b, In b (alist_blks l) -> In (fst b) (list_blocks l)).
{ intros l b Hb. unfold alist_blks, list_blocks in Hb |- *. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app.
  - left. destruct (hl_cap l =? 0); [destruct Hb|]. destruct Hb as [<- | []]. cbn [fst]. left. reflexivity.
  - right. apply in_map_iff in Hb as (x & <- & Hx). cbn [fst]. apply in_map. exact Hx. }
(* the head cells after the store: v and cap kept, n is n - 1 *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok _ ltac:(cbn [ss_mem]; right; right; left; reflexivity)) as (_ & _ & _ & Hchs).
pose proof (proj1 (Forall_forall _ _) Hchs (YP09.mkChunk 72 (CVal 4%N (SOff 34 (-1))))
  ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch72.
assert (MnF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 72) 4 (Z.of_nat (length rs))).
{ replace (HA + 72) with (base_val Eb (Some 9%nat) + 72) by (rewrite Vb9b; lia).
  apply (cnl_val_mem_of_chunk4 Eb _ _ 72 (SOff 34 (-1)) (Z.of_nat (length rs)) Hch72);
  [| pose proof (Nat2Z.is_nonneg (length rs)); cbn [length] in HNNhi; rewrite Nat2Z.inj_succ in HNNhi; lia].
  rewrite (U_atom_off Eb 34 (Z.of_nat (length (r :: rs))) (-1) K34) by lia.
  cbn [length]. rewrite Nat2Z.inj_succ. lia. }
assert (MvF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 64) 8 (hl_v EE)).
{ apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact MvE].
  intros x Hx. cbn [Z.of_nat] in Hx. exact (proj1 (KHD x ltac:(lia) ltac:(lia))). }
assert (McF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 64 + 12) 4 (hl_cap EE)).
{ apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact McE].
  intros x Hx. cbn [Z.of_nat] in Hx. exact (proj1 (KHD x ltac:(lia) ltac:(lia))). }
assert (AwF : awr W2 (ms_mem ms1) (HA + 64) 16).
{ intros i Hi. destruct (GH (HA + 64 + i) ltac:(lia)) as (Hi1 & Ho1 & He1).
  apply (cnl_writable_kept_w W1 W2 mem1 (ms_mem ms1) (HA + 64 + i));
  [intros Hp; exact (KPRES _ Hi1 Ho1 He1 Hp) | exact Hwle2 | exact (MwE i Hi)]. }
assert (VNE : hl_v EE <> fst r) by (intros Heq; apply HninE; cbn [map]; left; exact (eq_sym Heq)).
(* ---- the expected list, one record shorter ---- *)
assert (HLD : ldrop_list (cnl_E (r :: rs) jk) 0 =
  cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
  by (unfold cnl_E, ldrop_list;
      cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk firstn skipn app]; reflexivity).
assert (HE2 : alist_at B ly2 S2 W2 (ms_mem ms1) (HA + 64)
  (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) true).
{ rewrite <- HLD.
  apply (ALDROP ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) (HA + 64) (cnl_E (r :: rs) jk) true 0%nat HAE).
  - unfold cnl_E. cbn [HarnessRep.hl_recs length]. lia.
  - unfold cnl_E. cbn [HarnessRep.hl_recs nth]. exact Hbl.
  - intros a Ha. exact (proj1 (KHD a ltac:(lia) ltac:(lia))).
  - exact AwF.
  - replace (HA + 64 + 8) with (HA + 72) by lia.
    assert (Hn1 : hl_n (cnl_E (r :: rs) jk) - 1 = Z.of_nat (length rs))
      by (unfold hl_n, cnl_E; cbn [HarnessRep.hl_recs length]; rewrite Nat2Z.inj_succ; lia).
    rewrite Hn1. exact MnF.
  - intros k Hk.
    change (HarnessRep.hl_v (cnl_E (r :: rs) jk)) with (hl_v EE).
    change (HarnessRep.hl_n (cnl_E (r :: rs) jk)) with (Z.of_nat (length (r :: rs))) in Hk.
    change (Z.of_nat 0) with 0 in Hk |- *.
    replace (hl_v EE + AREC * 0 + k) with (hl_v EE + k) by lia.
    replace (hl_v EE + AREC * 0 + AREC + k) with (hl_v EE + AREC + k) by lia.
    apply KMOV. lia.
  - intros a Ha.
    change (HarnessRep.hl_v (cnl_E (r :: rs) jk)) with (hl_v EE) in Ha.
    change (HarnessRep.hl_cap (cnl_E (r :: rs) jk)) with (hl_cap EE) in Ha.
    change (HarnessRep.hl_n (cnl_E (r :: rs) jk)) with (Z.of_nat (length (r :: rs))) in Ha.
    change (Z.of_nat 0) with 0 in Ha.
    assert (Ha2 : hl_v EE <= a < hl_v EE + req_size (AREC * hl_cap EE)) by (rewrite HreqV; unfold AREC in *; lia).
    assert (Ha3 : ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))) by (unfold AREC in *; lia).
    exact (KBLK (hl_v EE) (AREC * hl_cap EE) a HvinE Ha2 (KOFF (hl_v EE) (AREC * hl_cap EE) a HvinE VNE Ha2) Ha3).
  - intros r' Hr' a Ha. change (In r' rs) in Hr'.
    assert (Hin' : In (fst r', Z.of_nat (length (snd r')) + 1) (ablocks B ly1 S1))
      by (rewrite Forall_forall in HFallE; exact (proj1 (HFallE r' (or_intror Hr')))).
    assert (Hne1 : fst r' <> fst r).
    { intros Heq. pose proof HNDvE as ND1. apply NoDup_ListNoDup in ND1. cbn [map] in ND1.
      apply List.NoDup_cons_iff in ND1 as [Hnin _]. apply Hnin. rewrite <- Heq. apply in_map. exact Hr'. }
    assert (Hne2 : fst r' <> hl_v EE)
      by (intros Heq; apply HninE; cbn [map]; right; rewrite <- Heq; apply in_map; exact Hr').
    exact (proj1 (KBK (fst r') (Z.of_nat (length (snd r')) + 1) a Hin' Hne1 Hne2
      ltac:(rewrite (HreqT r'); lia))). }
(* ---- the source with the shorter expected list ---- *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPD & _ & _ & _ & _ & _ & _ & _ & HPIN & HPJLEN & _ & _ & _ & _ & _).
cbn [hs_pending hs_partial hs_pjunk set_exp_held] in HPD, HPIN, HPJLEN.
assert (HreqP : req_size APARTIAL = APARTIAL)
  by (unfold req_size, APARTIAL; destruct (6000 =? 0) eqn:Ez; [discriminate | reflexivity]).
assert (SFP : akept W1 mem1 W2 (ms_mem ms1)
  (gfp (hs_partial h) (bzs (hs_pjunk h)) :: alist_fp (HA + 16) (hs_pending h) ++ alist_fp (HA + 80) H1)).
{ intros rr Hrr a Ha. cbn [In] in Hrr. destruct Hrr as [<- | Hrr].
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, HPJLEN in Ha.
    destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (Hp1 & Hp2).
    exact (KBK (hs_partial h) APARTIAL a HPIN Hp2 Hp1 ltac:(rewrite HreqP; unfold APARTIAL in *; lia)).
  - apply in_app_or in Hrr as [Hrr | Hrr]; revert rr Hrr a Ha.
    + apply (cnl_list_kept ly1 S1 W1 mem1 md1 W2 (ms_mem ms1) (HA + 16) (hs_pending h) false
        (fun b => b <> fst r /\ b <> hl_v EE) HAR1 HPD).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. destruct (NDX b ltac:(apply in_or_app; left; exact Hb)) as (Hb1 & Hb2).
        split; [exact Hb2 | exact Hb1].
    + apply (cnl_list_kept ly1 S1 W1 mem1 md1 W2 (ms_mem ms1) (HA + 80) H1 true
        (fun b => b <> fst r /\ b <> hl_v EE) HAR1 HAH).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. destruct (NDX b ltac:(apply in_or_app; right; apply in_or_app; right;
          apply in_or_app; right; exact Hb)) as (Hb1 & Hb2). split; [exact Hb2 | exact Hb1]. }
assert (SBLK : forall b, In b ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks H1) ->
  In b (ablocks B ly2 S2)).
{ intros b Hb. cbn [In] in Hb. destruct Hb as [<- | Hb].
  - destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & Hp2).
    exact (BLK2 (hs_partial h) APARTIAL HPIN ltac:(intros Heq; injection Heq as Heq _; exact (Hp2 Heq))).
  - apply in_app_or in Hb as [Hb | Hb]; destruct b as [p n].
    + assert (Hin1 : In (p, n) (ablocks B ly1 S1)) by exact (ABLK (hs_pending h) (HA + 16) false HPD _ Hb).
      destruct (NDX p ltac:(apply in_or_app; left; exact (ABF (hs_pending h) (p, n) Hb))) as (_ & Hp2).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp2 Heq))).
    + assert (Hin1 : In (p, n) (ablocks B ly1 S1)) by exact (ABLK H1 (HA + 80) true HAH _ Hb).
      destruct (NDX p ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; right;
        exact (ABF H1 (p, n) Hb))) as (_ & Hp2).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp2 Heq))). }
assert (SRC2 : asrc_at B ly2 S2 W2 (ms_mem ms1) HA
  (set_exp_held h (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) H1)).
{ apply (cnl_src_set ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) HA
    (set_exp_held h (cnl_E (r :: rs) jk) H1)
    (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) HSRC);
  [intros x Hx; apply KHD; lia | exact SFP | exact SBLK | exact HE2 | exact NDnew]. }
(* the stream's block is neither the freed text nor the vector *)
assert (OUTNE : forall CO0, In (OUT, CO0) (ablocks B ly1 S1) ->
  ~ In (OUT, CO0) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1) -> OUT <> fst r /\ OUT <> hl_v EE).
{ intros CO0 Hin Hni.
  assert (Hr1 : In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1)).
  { apply in_or_app. left. unfold list_blks, cnl_E.
    cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs]. apply in_or_app. right. cbn [map]. left. reflexivity. }
  assert (Hv1 : In (hl_v EE, AREC * hl_cap EE) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1)).
  { apply in_or_app. left. unfold list_blks, cnl_E.
    cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs]. rewrite Ecap. apply in_or_app. left. left. reflexivity. }
  destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO0 HAR1 Hin) as (_ & _ & _ & _ & HCreq & _).
  split; intros Heq.
  - pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO0 (fst r) (Z.of_nat (length (snd r)) + 1)
      HAR1 Hin HinR ltac:(intros Heq2; apply Hni; rewrite Heq2; exact Hr1)) as DJo.
    unfold zdisjoint in DJo. cbn [fst snd] in DJo. rewrite HreqR in DJo. lia.
  - pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO0 (hl_v EE) (AREC * hl_cap EE)
      HAR1 Hin HvinE ltac:(intros Heq2; apply Hni; rewrite Heq2; exact Hv1)) as DJo.
    unfold zdisjoint in DJo. cbn [fst snd] in DJo. rewrite HreqV in DJo. unfold AREC in *. lia. }
(* ---- the rest of the memory pack at the loop test ---- *)
assert (ATF : val_mem SEGS (arm W2 (ms_mem ms1)) AT 8 (cpos gone A0 (pre ++ [r]))).
{ apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact HATv].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KHI; lia. }
assert (FRM2 : cnl_frame_ok W2 (ms_mem ms1) sp0 regs0).
{ intros i Hi. apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact (HFRM i Hi)].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KHI; [|lia].
  assert (Hib : 0 <= Z.of_nat i <= 12) by (pose proof (Nat2Z.is_nonneg i); lia). lia. }
assert (PK2 : apres_kept B W mem W2 (ms_mem ms1))
  by (intros a Hi Ho He Hp; exact (KPRES a Hi Ho He (HPK a Hi Ho He Hp))).
(* errno's view at the loop test: errno is an image byte off g_s (HGRR), so none of the three runs wrote it; the
   free keeps it (its rule says so); the memmove wrote only inside the vector, a heap block *)
assert (ERRF : forall j0, 0 <= j0 < 4 ->
  aview SEGS (w_H W2) (ms_mem ms1) (as_errno B + j0) = aview SEGS (w_H W) mem (as_errno B + j0)).
{ intros j0 Hj0. set (e0 := as_errno B + j0).
  pose proof (proj1 (proj2 (pal_env B TL)) e0 ltac:(unfold e0; lia)) as Hi.
  pose proof (pa_img_range _ Hi) as Har.
  assert (Hnw : ~ (HA + 72 <= e0 < HA + 76)).
  { intros Hc. destruct (GH e0 ltac:(lia)) as (_ & _ & He). apply He. unfold e0. lia. }
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc e0 ltac:(lia)); [| cnl_nowr Vb9b Hnw] end.
  rewrite (Hfr3 e0 ltac:(lia) ltac:(apply MOFF; exact Hi) ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb e0 ltac:(lia)); [| cnl_nowr Vb9a Hnw] end.
  unfold e0. rewrite (Herr2 j0 Hj0). fold e0.
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra e0 ltac:(lia)); [| cnl_nowr Vb9 Hnw] end.
  exact (HERR j0 Hj0). }
(* rom_view at the loop test: the memmove wrote only inside the vector, the last run only s->expected.n *)
assert (ROMF : rom_view SEGS W2 (ms_mem ms1)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a ltac:(lia));
    [| cnl_nowr Vb9b (ROMW a Hrom)] end.
  rewrite (Hfr3 a ltac:(lia) ltac:(apply MOFF; exact Hi) ltac:(lia)).
  exact (ROMK a Hrom). }
assert (CONST2 : cnl_consts W2 (ms_mem ms1)).
{ destruct DPACK as [[[Dgn Dgot] Dcell] HOBx].
  pose proof CNLAP as (_ & _ & _ & _ & _ & _ & Dno & Dout & Dlg & Dlb & Dle & _).
  cbv zeta in Dno, Dout, Dlg, Dlb, Dle.
  assert (OFFW : forall base len x, (VAL A_g_s + 384 <= base \/ base + len <= VAL A_g_s) ->
    base <= x < base + len -> ~ (HA + 72 <= x < HA + 76)).
  { intros base len x Hd Hx Hc. rewrite EHA in Hc. unfold ASRC in Hc.
    pose proof (Nat2Z.is_nonneg j) as Hj0. destruct Hd; lia. }
  assert (LKG : Z.of_nat (length RelayModel.K_GESTURE) = 13) by reflexivity.
  assert (LKB : Z.of_nat (length RelayModel.W_BEGIN) = 5) by reflexivity.
  assert (LKE : Z.of_nat (length RelayModel.W_END) = 3) by reflexivity.
  split.
  { apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cgone]. intros x Hx. cbn [Z.of_nat] in Hx.
    destruct (RO (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    apply (KIMG x Hi Ho He). destruct Dgn; lia. }
  split.
  { apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cno]. intros x Hx. cbn [Z.of_nat] in Hx.
    destruct (RO (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_g_nout) 8 x Dno ltac:(lia))). }
  split.
  { apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cout]. intros x Hx. cbn [Z.of_nat] in Hx.
    destruct (RO (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_g_out) 8 x Dout ltac:(lia))). }
  split.
  { destruct HOBx as [Hnil | (HCO & HCOin & HCOni)].
    - rewrite Hnil. intros i Hi. cbn [length] in Hi. lia.
    - destruct (OUTNE CO HCOin HCOni) as (HO1 & HO2).
      destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HCOin) as (_ & _ & _ & HCle & _).
      apply (cnl_ob_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cob].
      intros i Hi. exact (proj1 (KBK OUT CO (OUT + i) HCOin HO1 HO2 ltac:(lia))). }
  split.
  { exact ROMF. }
  split.
  { apply (cnl_g8_keep W1 W2 mem1 (ms_mem ms1)); [|exact Clg]. intros x Hx. rewrite LKG in Hx.
    destruct (RO (VAL A_lit_gesture) 13 x ltac:(cbv [cnl_ro]; right; right; right; right; left; reflexivity)
      ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_lit_gesture) 13 x Dlg ltac:(lia))). }
  split.
  { apply (cnl_g8_keep W1 W2 mem1 (ms_mem ms1)); [|exact Clb]. intros x Hx. rewrite LKB in Hx.
    destruct (RO (VAL A_lit_begin) 5 x ltac:(cbv [cnl_ro]; right; right; right; right; right; left; reflexivity)
      ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_lit_begin) 5 x Dlb ltac:(lia))). }
  { apply (cnl_g8_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cle]. intros x Hx. rewrite LKE in Hx.
    destruct (RO (VAL A_lit_end) 3 x ltac:(cbv [cnl_ro]; right; right; right; right; right; right; left; reflexivity)
      ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_lit_end) 3 x Dle ltac:(lia))). } }
assert (PACK1 : cnl_pack ly2 S2 H1 (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
  (pre ++ [r]) W2 (ms_mem ms1))
  by (split; [exact PK2 | split; [exact ERRF | split; [exact SRC2 | split; [exact ATF |
      split; [exact CONST2 | exact FRM2]]]]]).
(* ---- the model-side facts, which no memory touches ---- *)
assert (HrecE2 : hl_recs EE = (pre ++ [r]) ++ rs) by (rewrite <- app_assoc; cbn [app]; exact HrecE).
assert (FRS2 : frames S2 = frames S) by (rewrite Hfrs2; exact HFRS).
assert (MLE2 : mo_le MT S S2 (cnl_go MT (texts HH) (hl_cap HH) (pre ++ [r]))).
{ apply (mle_weaken MT S S2 _ _ ML (mle_station MT S S1 S2 _ _ ML HMLE Hle)). lia. }
assert (MOK2 : mo_ok MT S2 (cnl_go MT (texts H1) (hl_cap H1) rs)).
{ apply (mok_station MT S1 S2 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) (mo_free MT)
    (cnl_go MT (texts H1) (hl_cap H1) rs) ML HMOK Hle HXnn). lia. }
assert (BB2 : blocks_bytes S1 = blocks_bytes S2 + (Z.of_nat (length (snd r)) + 1)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2).
  rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), Eb1, Eb2, !bsum_app, bsum_cons.
  cbn [snd]. lia. }
assert (ROOM2 : cnl_room MMAX (blocks_bytes S2) (texts H1) (hl_cap H1) rs)
  by (replace (blocks_bytes S2) with (blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)) by lia; exact HROOM).
(* the room round: the free's post room is the rest's budget; the counts fell by r's line (W_cnl_cnt.v cnl_cnt_free) *)
assert (RM2 : rp_RM RP S2 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr)) by exact HRM2.
assert (CNT2 : cnl_cnt RP rs H1 (ablocks B ly2 S2)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in HCNTr.
  exact (cnl_cnt_free RP r rs H1 l1 l2 (fst r) HCNTr). }
assert (PERM2 : forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly2 S2)
    (list_blks (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) ++ list_blks H1 ++ rest)).
{ intros rest Hp. pose proof (HPERM rest Hp) as HP1.
  destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb1 in HP1. rewrite Eb2.
  unfold list_blks, cnl_E in HP1 |- *. cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs] in HP1 |- *.
  rewrite Ecap in HP1 |- *. cbn [app map] in HP1 |- *.
  apply (Permutation_cons_inv (a := (fst r, Z.of_nat (length (snd r)) + 1))).
  eapply Permutation_trans; [apply Permutation_middle|].
  eapply Permutation_trans; [exact HP1|]. apply perm_swap. }
assert (OB2 : ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly2 S2) /\
  ~ In (OUT, CO) (list_blks (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) ++ list_blks H1))).
{ destruct DPACK as [[[_ _] _] HOBx]. destruct HOBx as [Hnil | (HCO & HCOin & HCOni)]; [left; exact Hnil|].
  right. destruct (OUTNE CO HCOin HCOni) as (HO1 & HO2).
  split; [exact HCO|]. split.
  - exact (BLK2 OUT CO HCOin ltac:(intros Heq; injection Heq as Heq _; exact (HO1 Heq))).
  - intros Hc. apply HCOni. apply in_app_or in Hc as [Hc | Hc]; apply in_or_app; [left | right; exact Hc].
    unfold list_blks, cnl_E in Hc |- *. cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs] in Hc |- *.
    rewrite Ecap in Hc |- *. cbn [app map] in Hc |- *.
    destruct Hc as [Hc | Hc]; [left; exact Hc | right; right; exact Hc]. }
assert (SGN : bv_signed (sv_denot Eb (SOff 34 0)) = Z.of_nat (length (r :: rs))).
{ cbn [sv_denot]. rewrite K34, Z.add_0_r, Z_to_bv_bv_unsigned.
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (r :: rs)))) = Z.of_nat (length (r :: rs)))
    by (apply unsigned_lit_small; lia).
  rewrite bv_signed_small by (rewrite Hu; lia). exact Hu. }
assert (SG1 : bv_signed (sv_denot Eb (SLit 1)) = 1) by reflexivity.
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* 1 < n: the records left are not empty, back to the loop head *)
  assert (Hne : rs <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc. rewrite SGN, SG1 in Hc.
    destruct rs as [|x rs']; [exfalso; cbn [length] in Hc; lia | discriminate]. }
  paj_run_to_tok_x RUNTO HS HJ3 SHOK3 Bspan A_cnl_loop.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9b in Ha; apply HGa; lia|].
    apply awr_ok_x_nil. }
  rename HF into HFd. rename HFr into HFrd. rename HG0 into HGrd.
  (* the run from the test to the head wrote nothing, so the pack moves to it *)
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok2 & _).
  pose proof (proj1 (Forall_forall _ _) Hrok2 _ ltac:(cbn [ss_mem add_cond]; right; right; left; reflexivity))
    as (_ & _ & _ & Hchs2).
  pose proof (proj1 (Forall_forall _ _) Hchs2 (YP09.mkChunk 72 (CVal 4%N (SOff 34 (-1))))
    ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch72b.
  assert (MnG : val_mem SEGS (arm W2 (ms_mem ms2)) (HA + 72) 4 (Z.of_nat (length rs))).
  { replace (HA + 72) with (base_val Eb (Some 9%nat) + 72) by (rewrite Vb9b; lia).
    apply (cnl_val_mem_of_chunk4 Eb _ _ 72 (SOff 34 (-1)) (Z.of_nat (length rs)) Hch72b);
    [| pose proof (Nat2Z.is_nonneg (length rs)); cbn [length] in HNNhi; rewrite Nat2Z.inj_succ in HNNhi; lia].
    rewrite (U_atom_off Eb 34 (Z.of_nat (length (r :: rs))) (-1) K34) by lia.
    cbn [length]. rewrite Nat2Z.inj_succ. lia. }
  assert (AEQ : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { intros a Ha.
    destruct (Z_le_gt_dec (HA + 72) a) as [Hl|Hl]; [destruct (Z_lt_ge_dec a (HA + 76)) as [Hh|Hh]|].
    - replace a with (HA + 72 + (a - (HA + 72))) by lia.
      exact (cnl_aview_of_val_mem2 (w_H W2) (w_H W2) (ms_mem ms1) (ms_mem ms2) (HA + 72) 4
        (Z.of_nat (length rs)) (a - (HA + 72)) MnF MnG ltac:(cbn [Z.of_nat]; lia)).
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFrd with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFrd a Ha
          ltac:(cnl_nowr Vb9b Hout)) end.
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFrd with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFrd a Ha
          ltac:(cnl_nowr Vb9b Hout)) end. }
  destruct (cnl_pack_keep ly2 S2 H1 (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
    (pre ++ [r]) W2 (ms_mem ms1) (ms_mem ms2) PACK1 AEQ HGrd) as (PKF & ERRFF & SRCF & ATFF & CSTF & FRMF).
  (* the loop's registers are back where the head wants them *)
  assert (REGS2 : cnl_regs_ok (ms_regs ms2) sp0 HA).
  { prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (19%bv : bv 5) T19. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
    prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
    prreg HS (27%bv : bv 5) T27.
    split; [rewrite T2, K2; reflexivity|].
    split; [rewrite T3, K3; reflexivity|].
    split; [rewrite T4, K4; reflexivity|].
    split; [rewrite T8, K9, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite T9, K9; reflexivity|].
    split; [rewrite T18, K18; reflexivity|].
    split; [rewrite T19, K9, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite T22, K22; reflexivity|].
    split; [rewrite T23, K22, K9, (unsigned_lit_small HA ltac:(lia)), cnl_shr3_add by lia; reflexivity|].
    split; [rewrite T24; apply bv_eq; unfold w64;
            rewrite (HEIb 386%nat ltac:(unfold A_TEXT, A_LIM; lia)),
                    (unsigned_lit_small (VAL (A_HI 106)) (pa_val_range (A_HI 106))); reflexivity|].
    split; [rewrite T25; reflexivity|].
    split; [rewrite T26, K22, K9, (unsigned_lit_small HA ltac:(lia)), cnl_shr3_add by lia; reflexivity|].
    rewrite T27; reflexivity. }
  pmkst HS.
  apply (IHl Hne W2 (ms_regs ms2) (ms_mem ms2) _).
  exists ly2, S2, hp2, (kk + 1), H1, (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk).
  split; [exact HrecE2|]. split; [exact HJ3|]. split; [exact PKF|]. split; [exact ERRFF|]. split; [exact SRCF|].
  split; [exact HND|]. split; [exact HTX|]. split; [exact HCAP|]. split; [exact HNn|].
  split; [exact HCb|]. split; [exact PERM2|]. split; [exact FRS2|]. split; [exact MLE2|].
  split; [exact MOK2|]. split; [exact ROOM2|]. split; [exact RM2|]. split; [exact CNT2|].
  split; [exact ATFF|]. split; [exact CSTF|].
  split; [exact OB2|]. split; [exact HSKIP|]. split; [exact FRMF | exact REGS2].
- (* n <= 1: no record left, the epilogue *)
  assert (Hnil : rs = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_ge in Hc. rewrite SGN, SG1 in Hc.
    destruct rs as [|x rs']; [reflexivity | exfalso; cbn [length] in Hc; pose proof (Nat2Z.is_nonneg (length rs')); lia]. }
  paj_run_tok_x RUN HS HJ3 SHOK3 Bspan.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9b in Ha; apply HGa; lia|].
    apply awr_ok_x_nil. }
  rename HF into HFe. rename HFr into HFre. rename HG0 into HGre.
  (* the epilogue only loads, so the pack moves to the return *)
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok2 & _).
  pose proof (proj1 (Forall_forall _ _) Hrok2 _ ltac:(cbn [ss_mem add_cond]; right; right; left; reflexivity))
    as (_ & _ & _ & Hchs2).
  pose proof (proj1 (Forall_forall _ _) Hchs2 (YP09.mkChunk 72 (CVal 4%N (SOff 34 (-1))))
    ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch72b.
  assert (MnG : val_mem SEGS (arm W2 (ms_mem ms2)) (HA + 72) 4 (Z.of_nat (length rs))).
  { replace (HA + 72) with (base_val Eb (Some 9%nat) + 72) by (rewrite Vb9b; lia).
    apply (cnl_val_mem_of_chunk4 Eb _ _ 72 (SOff 34 (-1)) (Z.of_nat (length rs)) Hch72b);
    [| pose proof (Nat2Z.is_nonneg (length rs)); cbn [length] in HNNhi; rewrite Nat2Z.inj_succ in HNNhi; lia].
    rewrite (U_atom_off Eb 34 (Z.of_nat (length (r :: rs))) (-1) K34) by lia.
    cbn [length]. rewrite Nat2Z.inj_succ. lia. }
  assert (AEQ : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { intros a Ha.
    destruct (Z_le_gt_dec (HA + 72) a) as [Hl|Hl]; [destruct (Z_lt_ge_dec a (HA + 76)) as [Hh|Hh]|].
    - replace a with (HA + 72 + (a - (HA + 72))) by lia.
      exact (cnl_aview_of_val_mem2 (w_H W2) (w_H W2) (ms_mem ms1) (ms_mem ms2) (HA + 72) 4
        (Z.of_nat (length rs)) (a - (HA + 72)) MnF MnG ltac:(cbn [Z.of_nat]; lia)).
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFre with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFre a Ha
          ltac:(cnl_nowr Vb9b Hout)) end.
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFre with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFre a Ha
          ltac:(cnl_nowr Vb9b Hout)) end. }
  destruct (cnl_pack_keep ly2 S2 H1 (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
    (pre ++ [r]) W2 (ms_mem ms1) (ms_mem ms2) PACK1 AEQ HGre) as (PKF & ERRFF & SRCF & ATFF & CSTF & FRMF).
  (* the epilogue put every callee-saved register back *)
  prreg HS (Z_to_bv 5 1 : bv 5) U1. prreg HS (Z_to_bv 5 2 : bv 5) U2.
  prreg HS (Z_to_bv 5 3 : bv 5) U3. prreg HS (Z_to_bv 5 4 : bv 5) U4.
  prreg HS (Z_to_bv 5 8 : bv 5) U8. prreg HS (Z_to_bv 5 9 : bv 5) U9.
  prreg HS (Z_to_bv 5 18 : bv 5) U18. prreg HS (Z_to_bv 5 19 : bv 5) U19.
  prreg HS (Z_to_bv 5 20 : bv 5) U20. prreg HS (Z_to_bv 5 21 : bv 5) U21.
  prreg HS (Z_to_bv 5 22 : bv 5) U22. prreg HS (Z_to_bv 5 23 : bv 5) U23.
  prreg HS (Z_to_bv 5 24 : bv 5) U24. prreg HS (Z_to_bv 5 25 : bv 5) U25.
  prreg HS (Z_to_bv 5 26 : bv 5) U26. prreg HS (Z_to_bv 5 27 : bv 5) U27.
  prreg HS (1%bv : bv 5) U1b.
  assert (RA1 : getr (ms_regs ms2) 1 = getr regs0 1).
  { rewrite U1b, (KS 49%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
    apply Z_to_bv_bv_unsigned. }
  assert (RPRES : aregs_preserved regs0 (ms_regs ms2)).
  { intros rr Hrr. unfold acallee_saved in Hrr.
    assert (Hcs : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/
      rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - rewrite U2, K2, (unsigned_lit_small (sp0 - 128) ltac:(lia)).
      replace (sp0 - 128 + 128) with sp0 by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    - rewrite U3, K3. symmetry. exact Hgp0.
    - rewrite U4, K4. symmetry. exact Htp0.
    - rewrite U8, (KS 48%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U9, (KS 47%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U18, (KS 46%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U19, (KS 45%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U20, (KS 44%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U21, (KS 43%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U22, (KS 42%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U23, (KS 41%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U24, (KS 40%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U25, (KS 39%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U26, (KS 38%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U27, (KS 37%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned. }
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?dd = _ /\ _ =>
    exists ly2, S2, hp2, rg, mm, dd, (kk + 1),
      (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)), H1 end.
  split; [cbn [ms_regs ms_mem]; rewrite RA1, Hra0; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ3|].
  split; [exact RPRES|].
  split; [exact PKF|].
  split; [exact ERRFF|].
  split; [exact SRCF|].
  split; [rewrite Hnil; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split.
  { rewrite HTX. unfold texts. rewrite HrecE2, Hnil, app_nil_r. reflexivity. }
  split; [unfold capb in HCb; exact HCb|].
  split.
  { replace (if gone =? 0 then A0 + Z.of_nat (length (bstream EE)) else A0)
      with (cpos gone A0 (pre ++ [r])); [exact ATFF|].
    unfold cpos, bsr, bstream. rewrite HrecE2, Hnil, app_nil_r. reflexivity. }
  destruct CSTF as (Cg2 & Cn2 & Co2 & Cb2 & _).
  split; [exact Cg2|]. split; [exact Cn2|]. split; [exact Co2|]. split; [exact Cb2|].
  split; [exact PERM2|]. split; [exact FRS2|].
  split; [unfold cnl_cost; rewrite HrecE2, Hnil, app_nil_r; exact MLE2|].
  split; [rewrite Hnil in RM2; exact RM2|].
  (* the held list's capacity (cnl_post_x's last two conjuncts): H' = H1, whose capacity is cnl_cap over every
     record (cnl_mid's HCAP at pre ++ [r] = hl_recs EE, rs = []); it never shrinks (W_cnl_cnt.v cnl_cap_ge) *)
  assert (ECAP : hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (hl_recs EE))
    by (rewrite HCAP, HrecE2, Hnil, app_nil_r; reflexivity).
  split; [rewrite ECAP; apply cnl_cap_ge | exact ECAP].
Qed.
Lemma cnl_loop : forall k pre rs W1 regs1 mem1 md1, length rs = k -> rs <> [] ->
cnl_inv pre rs W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction k as [|k IH]; intros pre rs W1 regs1 mem1 md1 Hk Hne HI; [destruct rs; [exfalso; exact (Hne eq_refl) | discriminate Hk]|].
destruct rs as [|r rs]; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hk. injection Hk as Hk.
eapply SRr_bind; [exact (cnl_step pre r rs W1 regs1 mem1 md1 HI)|].
cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HM).
apply (cnl_drop pre r rs W2 regs2 mem2 md2); [|exact HM].
intros Hne2 W3 regs3 mem3 md3 HI3. exact (IH (pre ++ [r]) rs W3 regs3 mem3 md3 Hk Hne2 HI3).
Qed.
Lemma cnl_enter : forall W1 regs1 mem1 md1, hl_recs EE <> [] -> cnl_inv [] (hl_recs EE) W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros W1 regs1 mem1 md1 Hne HI.
exact (cnl_loop (length (hl_recs EE)) [] (hl_recs EE) W1 regs1 mem1 md1 eq_refl Hne HI).
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sections 0, 3, 4): the loop at a world relation R.  cnl_inv / cnl_mid / cnl_midQ /
   Post get R twins (the journal ajournal_gx_xR R, the post cnl_post_xR R); each loop lemma is its strict proof with
   the journal at R, the step relation SRrG SEGS R, and:
    the runs over the R journal concluding SRrG (RUNg / RUNTOg := W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, tactics
     W_kit_x.v paj_run_tok_xR / paj_run_to_tok_xR, branches BRg := W_kit.v paj_branch_xR);
    gesture_model at its R contract GM_R (it calls list_push's realloc and list_drop's free), the free by cnl_free_gx_xR
     (AFREE_R), both composed by SRrG_bind (R_trans) and their post journals by ajournal_gx_sub_xR (R_trans);
    next_line, bcmp and __asan_memmove stay strict leaves: next_line's SRr fact and the return step lift by SRr_SRrG
     (WLE_R), next_line's post journal by cnl_gx_lift_xR; bcmp by W_sites_x.v aj_bcmp_gx_at_xR, the memmove by W_sites_x.v
     aj_gx_entry_at_xR;
    the free's world step is R, not wle, so writability across it comes from presence (nls_awr_kept) in place of
     cnl_writable_kept_w.
   The strict loop lemmas above keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis GM_R : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Let RUNg := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let RUNTOg := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let BRg := paj_branch_xR (PI := PI) (R := R).
Local Notation Post_xR := (cnl_post_xR B PST ARx R MT RP G regs0 ly S hp W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
(* cnl_inv at R: the journal from the entry is ajournal_gx_xR R *)
Definition cnl_inv_xR (pre rs : list (Z * list byte)) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte)
(md1 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ rs /\
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E rs jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs pre) /\ hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E rs jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) /\ mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) rs /\
(* the room round: the room budget (gesture_model's charge and one free per record left, past the caller's kr) and
   the live counts plus the peak of the trace still owed (W_cnl_cnt.v) *)
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr) /\ cnl_cnt RP rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 pre) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E rs jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 pre)) ob = bsr rs ++ rest) /\
cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 sp0 HA.
(* cnl_mid at R *)
Definition cnl_mid_xR (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) (W1 : world SEGS)
(regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ r :: rs /\
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E (r :: rs) jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs (pre ++ [r])) /\
hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (pre ++ [r]) /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs (pre ++ [r]))) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) (pre ++ [r]) - mo_free MT) /\
mo_ok MT S1 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)) (texts H1) (hl_cap H1) rs /\
(* the room round: r's free is still owed, before the rest's budget; its free and the rest still owe the counts *)
rp_RM RP S1 (Datatypes.S (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr))%nat /\ cnl_cntm RP r rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 (pre ++ [r])) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) /\
cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 sp0 HA.
Definition cnl_midQ_xR (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) :
world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1, c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1 /\
cnl_mid_xR pre r rs W1 regs1 mem1 md1.
(* cnl_gm at R: gesture_model by GM_R *)
Lemma cnl_gm_xR : forall pre r rs ly1 S1 hp1 kk (H1 : hlist) jk W1 regsc memc mdc LINE q k,
hl_recs EE = pre ++ r :: rs ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 memc mdc kk ->
apres_kept B W mem W1 memc ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) memc (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
asrc_at B ly1 S1 W1 memc HA (set_exp_held h (cnl_E (r :: rs) jk) H1) ->
NoDup (texts H1) -> texts H1 = RelayModel.upds (texts HH) (txs pre) -> hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre ->
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) -> hl_cap H1 <= capb HH EE ->
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) ->
frames S1 = frames S ->
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) -> mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) (r :: rs)) ->
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) (r :: rs) ->
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) (r :: rs)) + kr) -> cnl_cnt RP (r :: rs) H1 (ablocks B ly1 S1) ->
val_mem SEGS (arm W1 memc) AT 8 (cpos gone A0 (pre ++ [r])) -> cnl_consts W1 memc ->
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) ->
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) ->
cnl_frame_ok W1 memc sp0 regs0 -> cnl_regs_ok regsc sp0 HA ->
getr regsc 1 = Z_to_bv 64 (BASE + A_cnl_back) -> getr regsc 10 = w64 HA -> getr regsc 11 = w64 LINE ->
getr regsc 12 = w64 (Z.of_nat (length (snd r))) ->
garr8 SEGS (arm W1 memc) LINE (bzs (snd r)) ->
In (q, k) (ablocks B ly1 S1) -> ~ In (q, k) (list_blks H1) -> q <= LINE -> LINE + Z.of_nat (length (snd r)) <= q + req_size k ->
SRrG SEGS R W1 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_model)) memc (seg_rom SEGS)) mdc) (cnl_midQ_xR pre r rs).
Proof.
intros pre r rs ly1 S1 hp1 kk H1 jk W1 regsc memc mdc LINE q k HEQ HJ HPK HERR HSRC HND HTX HCAP HN HCB HPERM HFR HMLE HMOK
  HROOM HRMr HCNTr HAT HCONST HOB HSTR HFRM HREGS R1 R10 R11 R12 HLG Hqk Hqn Hq1 Hq2.
pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof APRE as (_ & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16656) by reflexivity. assert (WG : GM_STK = 16528) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & _ & _ & _).
(* gesture_model's premise (HA + 80) mod 8 = 0 *)
assert (HA80 : (HA + 80) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide; [lia | exact HA8] | exists 10; reflexivity]. }
assert (Hs1 : VAL A_g_s <= HA /\ HA + 96 <= VAL A_g_s + 384) by (rewrite AHAE; unfold ASRC; lia).
assert (HAR1 : ARx ly1 S1 hp1 W1 memc mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
set (E1 := cnl_E (r :: rs) jk) in *.
assert (HrE1 : hl_recs E1 = r :: rs) by reflexivity.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HH1 & HNDB).
cbn [set_exp_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HH1.
pose proof HE1 as (_ & _ & _ & _ & _ & _ & _ & _ & HrecE).
rewrite HrE1 in HrecE. apply Forall_cons_iff in HrecE as [(Hrb & Hrg & Hrl & _) _].
destruct (Hrl eq_refl) as [Hr0 HrA].
pose proof HH1 as (_ & _ & _ & _ & HcapH1 & _).
destruct HCONST as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
(* the source's blocks at the call: pending's, the partial buffer, the expected list's, then the held list's *)
set (HL1 := list_blks H1) in *.
set (Ab := list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)] ++ list_blks E1).
assert (HNDl : List.NoDup (Ab ++ HL1)).
{ apply (nls_nodup_map _ _ fst). apply NoDup_ListNoDup in HNDB.
  replace (map fst (Ab ++ HL1)) with (hs_blocks (set_exp_held h E1 H1)); [exact HNDB|].
  unfold hs_blocks, Ab, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
  rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
assert (Hinc : incl (Ab ++ HL1) (ablocks B ly1 S1)).
{ intros b Hb. unfold Ab, HL1 in Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (nls_blks_in _ _ _ _ _ _ _ HH1 b Hb)].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [destruct Hb as [<- | []]; exact Hpin | exact (nls_blks_in _ _ _ _ _ _ _ HE1 b Hb)]. }
destruct (perm_of_incl _ _ HNDl Hinc) as (rest0 & Hp0).
assert (Hp1 : Permutation (ablocks B ly1 S1) (HL1 ++ Ab ++ rest0)) by (eapply Permutation_trans; [exact Hp0 | apply nls_perm_swap]).
pose proof (nls_nodup_blocks _ _ _ _ _ HAR1) as HND1b.
(* gesture_model's footprint: a held block live at entry was one of FPc's, by APERM *)
assert (HFP : forall a, inFP (blk_FP HL1) a ->
  (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb). cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by exact (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb).
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly S)) as [Hin0 | Hnin0].
  - left. split; [|exists p, n; split; [exact Hb1 | exact Ha]].
    destruct APERM as (rest & HQ0). pose proof (HPERM rest HQ0) as HP1.
    assert (Hx : In (p, n) (list_blks EE ++ list_blks HH)).
    { pose proof (Permutation_in _ HQ0 Hin0) as Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx]; [exact Hx|].
      exfalso. pose proof (Permutation_NoDup HP1 HND1b) as HNx. apply NoDup_app_remove_l in HNx.
      exact (nls_nodup_disj _ HL1 rest (p, n) HNx Hb Hx). }
    exists (p, p + req_size n). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n)). exact Hx.
  - right. exists p, n. split; [exact Hb1|]. split; [exact Hnin0 | exact Ha]. }
(* gesture_model's globals: the held list's head only *)
set (G' := [(HA + 80, 16)]).
assert (HG'G : forall a, inG G' a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply AGA; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG' : forall a, ~ (HA + 80 <= a < HA + 96) -> ~ inG G' a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G' G HG'G HG) as HG'.
(* gx_rt of gesture_model's G' comes from g_s's own placement fact HGRR, never from the caller's G: a caller's G
   (G_fr, G_SL) holds errno *)
assert (HG'R : forall a, inG G' a -> inG cnl_ro a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. unfold inG. apply Exists_exists. exists (VAL A_g_s, 384).
  split; [cbv [cnl_ro]; right; right; right; left; reflexivity|].
  unfold in_zr; cbn [fst snd]. rewrite AHAE in Ha. unfold ASRC in *. lia. }
assert (HGRT' : gx_rt B G') by (eapply gx_rt_sub; [exact HG'R | exact HGRR]).
(* gesture_model's entry *)
assert (Usp : spZ regsc = sp0 - 128).
{ destruct HREGS as (Q2 & _). unfold spZ at 1. rewrite Q2. apply unsigned_lit_small. lia. }
destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 memc mdc kk HJ) as (memS & HJi & _).
assert (HPREg : afn_pre_x SEGS B ARx GM_STK ly1 S1 hp1 W1 regsc memc mdc []).
{ destruct HREGS as (_ & Q3 & Q4 & Q8 & _).
  eapply (afn_pre_x_atR SEGS B PST ARx (CNL_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W1 memc mdc kk regsc GM_STK (- 128 - XO) [] HJi).
  - rewrite Usp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-8); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
  - lia.
  - rewrite WG; lia.
  - rewrite WS, WG. lia.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold A_cnl_back, AF_fr_check_no_loss; lia | reflexivity].
  - unfold raZ. rewrite R1. unfold A_cnl_back, AF_fr_check_no_loss. destruct HBASE as (B1 & B2 & _).
    rewrite unsigned_lit_small by lia. lia.
  - exact Q3.
  - exact Q4.
  - apply achain_low. unfold s0Z. rewrite Q8, unsigned_lit_small by lia. lia. }
assert (Hazs : azs B (HA + 80) 16)
  by (destruct AZS as (zr & Hzr & Hz8 & Hz1 & Hz2); exists zr; split; [exact Hzr|]; split; [exact Hz8|]; split; lia).
assert (HnT1 : Z.of_nat (length (texts H1)) = hl_n H1) by (unfold texts, hl_n; rewrite length_map; reflexivity).
cbn [cnl_room] in HROOM. destruct HROOM as (HRM1 & HRM2 & HRM3).
assert (HGC : gm_cost MT H1 (snd r) = gmc MT (texts H1) (hl_cap H1) (snd r)).
{ unfold gm_cost, lp_cost, gmc, lp_grow, lp_vbytes. rewrite HnT1. reflexivity. }
cbn [cnl_go] in HMOK.
eapply SRrG_mono.
{ pose proof CNLAP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CNLROM).
  refine (GM_R G' HG' HGRT' (W_rom_place.cnl_g_rom_out B HA j AHAE AJLT CNLROM ROMOH ROMNS)
    W1 ly1 S1 hp1 regsc memc mdc [] HA LINE (snd r) H1 q k HPREg R10 R11 R12 HH1 HND _ Hazs HA80 HLG Hr0 HrA
    Hqk Hqn Hq1 Hq2 C6 C7 C8 C5 _ _ _ _
    (Datatypes.S (Z.to_nat (cnl_go MT_rk (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
      + kr))%nat _ _).
  - intros a Ha. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros Hg. unfold lp_vbytes. rewrite <- HnT1. apply HRM1. unfold lp_grow in Hg. apply Z.eqb_eq in Hg. lia.
  - unfold AREC in *. lia.
  - unfold lp_grow, lp_vbytes. rewrite <- HnT1. exact HRM2.
  - rewrite HGC. eapply (mo_ok_le MT ML); [exact HMOK|]. pose proof (mo_free_nonneg MT ML).
    assert (Hc0 : 0 <= hl_cap H1) by (unfold hl_n in HcapH1; lia).
    pose proof (nls_go_nonneg rs (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1))
      (nls_capstep_nonneg (texts H1) (bzs (snd r)) (hl_cap H1) Hc0)). lia.
  - (* the room: gesture_model's charge, then r's free, then the rest (W_cnl_cnt.v cnl_rk_step) *)
    rewrite <- (cnl_rk_step H1 r rs kr). exact HRMr.
  - (* the counts: gesture_model's peak is at most 2 (W_cnl_cnt.v cnl_cnt_gm_pre) *)
    exact (cnl_cnt_gm_pre RP r rs H1 _ HCNTr). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & hp2 & regs2 & mem2 & md2 & kk2 & H2 & -> & HJg & HPg & HPKg & HERRg & HLH2 & HND2 & HT2 & HC2 & HPm & HFR2 & HMLE2 & HRMg).
set (HL2 := list_blks H2) in *.
assert (HAR2 : ARx ly2 S2 hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJg).
pose proof (HPm _ Hp1) as Hp2.
pose proof (Permutation_NoDup Hp2 (nls_nodup_blocks _ _ _ _ _ HAR2)) as HNDp2.
(* what gesture_model kept: its journal at G' *)
pose proof HJg as HJg0. eapply ajournal_gx_inner_xR in HJg0. destruct HJg0 as (memS2 & HJgi & HgS2).
rewrite Usp in HJgi. destruct HJgi as (_ & _ & _ & _ & _ & _ & _ & _ & KF & KB & KI & _).
assert (Hcl : ~ YI16.sink_open_fp (blk_FP HL1)).
{ apply sink_closed_pos. apply Forall_forall. intros rr Hrr. unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 128 - GM_STK <= a < sp0 - 128) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Ha Hn. rewrite KF by lia. apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 80 <= a < HA + 96) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as Hr.
  rewrite KI; [|exact Hi | exact Ho | exact He | exact (HPST a Hi) | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. exact Hn. }
assert (Kblk : forall p n i, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) HL1 ->
  0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W1) memc (p + i)).
{ intros p n i Hb1 Hb2 Hn Hi. destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i Hb1 Hb2 Hi).
  - apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. unfold off_img in Hoff. lia.
  - intros (rr & Hrr & Hr). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p' & n') & <- & Hb'). cbn [fst snd] in Hr.
    assert (Hne : (p', n') <> (p, n)) by (intros E'; rewrite E' in Hb'; exact (Hn Hb')).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 memc mdc p' n' p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb') Hb1 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W1 memc) a -> writable_at SEGS (arm W2 mem2) a).
{ intros a Hi Ho He Hw. apply (nls_awr_kept W1 W2 memc mem2 a); [|exact Hw]. intros Hp. exact (HPKg a Hi Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W2 mem2) a).
{ intros p n a Hb Ha. destruct (cnl_blk ly2 S2 W2 mem2 md2 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
(* the source's own bytes (outside the held head) and the blocks of Ab *)
assert (KHd : forall a, HA <= a < HA + 80 -> abyte_kept W1 memc W2 mem2 a).
{ intros a Ha. destruct (nls_ro (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; do 3 right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
  split; [apply Kimg; [exact Hi | exact Ho | exact He | lia] | apply Pimg; assumption]. }
assert (KAb : forall b a, In b Ab -> fst b <= a < fst b + snd b -> abyte_kept W1 memc W2 mem2 a).
{ intros (p & n) a Hb Ha. cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by (apply Hinc; apply in_or_app; left; exact Hb).
  assert (Hb2 : In (p, n) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; apply in_or_app; left; exact Hb).
  assert (Hn1 : ~ In (p, n) HL1) by exact (nls_nodup_disj _ Ab HL1 (p, n) HNDl Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr & _).
  replace a with (p + (a - p)) by lia.
  split; [apply (Kblk p n); [exact Hb1 | exact Hb2 | exact Hn1 | lia] | intros _; apply (Pblk p n); [exact Hb2 | lia]]. }
assert (HOB2 : ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ In (OUT, CO) (ablocks B ly2 S2) /\
  ~ In (OUT, CO) (list_blks E1 ++ HL1) /\ ~ In (OUT, CO) HL2)).
{ destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [left; exact Hob0 | right].
  assert (HOr : In (OUT, CO) (Ab ++ rest0)).
  { pose proof (Permutation_in _ Hp1 HOin) as Hx. apply in_app_or in Hx as [Hx | Hx]; [|exact Hx].
    exfalso. apply HOn. apply in_or_app. right. exact Hx. }
  split; [exact HCO|]. split; [exact HOin|].
  split; [apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; exact HOr|].
  split; [exact HOn|]. intros Hx. exact (nls_nodup_disj _ HL2 (Ab ++ rest0) (OUT, CO) HNDp2 Hx HOr). }
clear HOB.
assert (HnT2 : Z.of_nat (length (texts H2)) = hl_n H2) by (unfold texts, hl_n; rewrite length_map; reflexivity).
assert (HCS : hl_cap H2 = capstep (texts H1) (bzs (snd r)) (hl_cap H1)).
{ unfold capstep. rewrite <- HT2, HC2, <- HnT1, <- HnT2.
  destruct (Nat.ltb_spec (length (texts H1)) (length (texts H2)));
  destruct (Z.ltb_spec (Z.of_nat (length (texts H1))) (Z.of_nat (length (texts H2)))); try reflexivity; lia. }
pose proof (upd_len (texts H1) (bzs (snd r))) as (U1 & U2). rewrite <- HT2 in U1, U2.
pose proof nls_lit_len as (L1 & L2 & L3).
assert (KR : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> ~ (HA + 80 <= x < HA + 96) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) memc x).
{ intros b n x Hin Hx Hn. destruct (nls_ro b n x Hin Hx) as (Hi & Ho & He). exact (Kimg x Hi Ho He Hn). }
(* the state at 0x85a9c *)
exists regs2, mem2, md2. split; [rewrite R1; reflexivity|].
exists ly2, S2, hp2, (kk + kk2), H2, jk.
split; [exact HEQ|].
split.
{ pose proof (ajournal_gx_G_mono_xR SEGS B PST ARx G' G 0 [] GM_STK (spZ regsc) (blk_FP HL1) ly1 S1 hp1 W1 memc mdc [] ly2 S2 hp2 W2 mem2 md2 kk2
    HG'G HJg) as HJg'. rewrite Usp in HJg'.
  pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md [] ly1 S1 hp1 W1 memc mdc kk
    GM_STK (sp0 - 128) 0 [] (blk_FP HL1) [] ly2 S2 hp2 W2 mem2 md2 kk2 HJ HJg' ltac:(rewrite WS, WG; lia) ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP) as HJ2.
  cbn [app] in HJ2. exact HJ2. }
split; [exact (nls_apk_trans _ _ _ _ _ _ HPK HPKg)|].
split; [intros j0 Hj0; rewrite (HERRg j0 Hj0); exact (HERR j0 Hj0)|].
split.
{ refine (nls_src_swap ly1 S1 W1 memc ly2 S2 W2 mem2 HA (set_exp_held h E1 H1) H2 HSRC KHd _ _ HLH2 _).
  - intros rr Hrr a Ha. cbn [set_exp_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KAb (hs_partial h, APARTIAL)); [unfold Ab; apply in_or_app; right; apply in_or_app; left; left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ HE1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. cbn [set_exp_held hs_partial hs_pending hs_expected] in Hb. rewrite !nls_alist_blks in Hb.
    apply (Permutation_in _ (Permutation_sym Hp2)). apply in_or_app. right. apply in_or_app. left. unfold Ab.
    destruct Hb as [<- | Hb]; [apply in_or_app; right; apply in_or_app; left; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
  - apply NoDup_ListNoDup.
    replace (hs_blocks (set_exp_held (set_exp_held h E1 H1) (hs_expected (set_exp_held h E1 H1)) H2)) with (map fst (Ab ++ HL2)).
    + pose proof (nls_nodup_blocks_fst _ _ _ _ _ HAR2) as Hf.
      pose proof (Permutation_NoDup (Permutation_map fst (Permutation_trans Hp2 (Permutation_sym (nls_perm_swap _ Ab HL2 rest0)))) Hf) as Hf2.
      rewrite map_app in Hf2. exact (NoDup_app_remove_r _ _ Hf2).
    + unfold hs_blocks, Ab, HL2. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
      rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
split; [exact HND2|].
split; [rewrite upds_snoc, <- HTX; exact HT2|].
split; [rewrite cnl_cap_snoc, <- HTX, <- HCAP; exact HCS|].
split.
{ rewrite txs_app, nls_cb_app. change (txs [r]) with [bzs (snd r)]. rewrite nls_cb_one.
  destruct (is_begin (bzs (snd r))) eqn:Eb; [lia|].
  destruct (Nat.lt_ge_cases (length (texts H1)) (length (texts H2))) as [Hlt | Hge]; [destruct (U2 Hlt) as [Hb _]; congruence | lia]. }
split.
{ rewrite HC2. destruct (Z.ltb_spec (hl_n H1) (hl_n H2)) as [Hlt | Hge]; [|exact HCB].
  destruct (U2 ltac:(lia)) as (Hbeg & _).
  assert (Hcbe : (count_begin (txs pre) + 1 <= count_begin (texts EE))%nat).
  { change (texts EE) with (txs (hl_recs EE)). rewrite HEQ, txs_app, nls_cb_app.
    change (txs (r :: rs)) with ([bzs (snd r)] ++ txs rs). rewrite nls_cb_app, nls_cb_one, Hbeg. lia. }
  unfold capb, grow_cap in *. destruct (hl_n H1 =? hl_cap H1) eqn:Eq; [|lia]. apply Z.eqb_eq in Eq. destruct (hl_cap H1 =? 0); lia. }
split.
{ intros rest HQ0. pose proof (HPERM rest HQ0) as HP1x.
  assert (HP1y : Permutation (ablocks B ly1 S1) (HL1 ++ list_blks E1 ++ rest))
    by (eapply Permutation_trans; [exact HP1x|]; rewrite app_assoc; apply nls_perm_swap).
  eapply Permutation_trans; [exact (HPm _ HP1y)|]. rewrite app_assoc. apply nls_perm_swap. }
split; [rewrite HFR2; exact HFR|].
split.
{ eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLE2)|].
  rewrite nls_go_snoc, HGC, HTX, HCAP. lia. }
split.
{ replace (cnl_go MT (texts H2) (hl_cap H2) rs) with
    (cnl_go MT (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
    by (rewrite <- HT2, <- HCS; reflexivity).
  apply (mo_ok_step MT ML S1 S2 (gm_cost MT H1 (snd r))); [|exact HMLE2].
  rewrite HGC, Z.add_assoc. exact HMOK. }
split.
{ rewrite <- HT2, <- HCS in HRM3.
  assert (BB : blocks_bytes S2 = blocks_bytes S1 - hbytes (texts H1) (hl_cap H1) + hbytes (texts H2) (hl_cap H2)).
  { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hp1), (bsum_perm _ _ Hp2), !bsum_app.
    unfold HL1, HL2. rewrite !bsum_list_blks. lia. }
  rewrite BB. exact HRM3. }
split.
{ (* the room past gesture_model: its post's kr *)
  rewrite HT2, HCS. exact HRMg. }
split.
{ (* the live counts past gesture_model (W_cnl_cnt.v cnl_cnt_gm_post) *)
  apply (cnl_cnt_gm_post RP r rs H1 H2 (ablocks B ly1 S1) (ablocks B ly2 S2) (Ab ++ rest0));
  [first [exact HND | apply NoDup_ListNoDup; exact HND] | exact HT2 | exact HCS | exact Hp1 | exact Hp2 | exact HCNTr]. }
split.
{ apply (nls_vm_kept W1 W2 memc mem2 AT 8); [|exact HAT]. intros i Hi. apply Kstk; [|lia]. split; [lia|]. cbn in Hi. lia. }
split.
{ pose proof CNLAP as (_ & Agn & _ & _ & _ & _ & Ano & Aou & Alg & Alb & Ale & Arom).
  cbv zeta in Agn, Ano, Aou, Alg, Alb, Ale, Arom.
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C1]; intros i Hi;
    apply (KR (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C2]; intros i Hi;
    apply (KR (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C3]; intros i Hi;
    apply (KR (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split.
  { apply (nls_ob_kept W1 W2 memc mem2); [|exact C4]. intros i Hi.
    destruct HOB2 as [-> | (HCO & HOin & HOin2 & HOn & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly1 S1 W1 memc mdc OUT CO HAR1 HOin) as (_ & _ & _ & Hnr & _).
    apply (Kblk OUT CO); [exact HOin | exact HOin2 | intros Hx; apply HOn; apply in_or_app; right; exact Hx | lia]. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as [He Hrp].
    assert (Hd : forall rr, {in_zr a rr} + {~ in_zr a rr}).
    { intros rr. unfold in_zr. destruct (Z_le_gt_dec (fst rr) a); destruct (Z_lt_ge_dec a (fst rr + snd rr));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Ho].
    - exact (rom_pinned_view_x SEGS B ARx LAWS ly2 S2 hp2 W2 mem2 md2 a HAR2 (Hrp Hown)).
    - rewrite (Kimg a (nls_rom_img a Hr) Ho He (fun Hn => Arom a ltac:(lia) Hr)). exact (C5 a Hr). }
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C6]; intros i Hi;
    apply (KR (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia | rewrite L1 in Hi; lia]|].
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C7]; intros i Hi;
    apply (KR (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia | rewrite L2 in Hi; lia]|].
  apply (nls_garr8_kept W1 W2 memc mem2); [|exact C8]; intros i Hi.
  apply (KR (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia | rewrite L3 in Hi; lia]. }
split.
{ destruct HOB2 as [Hob0 | (HCO & _ & HOin2 & HOn & HOn2)]; [left; exact Hob0 | right].
  split; [exact HCO|]. split; [exact HOin2|].
  intros Hx. apply in_app_or in Hx as [Hx | Hx]; [apply HOn; apply in_or_app; left; exact Hx | exact (HOn2 Hx)]. }
split; [exact HSTR|].
split; [apply (nls_frame_kept W1 W2 memc mem2 HFRM); intros a Ha; apply Kstk; lia|].
destruct HREGS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
assert (P2 : getr regs2 2 = getr regsc 2) by (apply (HPg 2); unfold acallee_saved; lia).
assert (P3 : getr regs2 3 = getr regsc 3) by (apply (HPg 3); unfold acallee_saved; lia).
assert (P4 : getr regs2 4 = getr regsc 4) by (apply (HPg 4); unfold acallee_saved; lia).
assert (P8 : getr regs2 8 = getr regsc 8) by (apply (HPg 8); unfold acallee_saved; lia).
assert (P9 : getr regs2 9 = getr regsc 9) by (apply (HPg 9); unfold acallee_saved; lia).
assert (P18 : getr regs2 18 = getr regsc 18) by (apply (HPg 18); unfold acallee_saved; lia).
assert (P19 : getr regs2 19 = getr regsc 19) by (apply (HPg 19); unfold acallee_saved; lia).
assert (P22 : getr regs2 22 = getr regsc 22) by (apply (HPg 22); unfold acallee_saved; lia).
assert (P23 : getr regs2 23 = getr regsc 23) by (apply (HPg 23); unfold acallee_saved; lia).
assert (P24 : getr regs2 24 = getr regsc 24) by (apply (HPg 24); unfold acallee_saved; lia).
assert (P25 : getr regs2 25 = getr regsc 25) by (apply (HPg 25); unfold acallee_saved; lia).
assert (P26 : getr regs2 26 = getr regsc 26) by (apply (HPg 26); unfold acallee_saved; lia).
assert (P27 : getr regs2 27 = getr regsc 27) by (apply (HPg 27); unfold acallee_saved; lia).
unfold cnl_regs_ok. rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P24, P25, P26, P27.
repeat split; assumption.
Qed.
(* cnl_step at R *)
Lemma cnl_step_xR : forall pre r rs W1 regs1 mem1 md1, cnl_inv_xR pre (r :: rs) W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) (cnl_midQ_xR pre r rs).
Proof.
intros pre r rs W1 regs1 mem1 md1 HI.
destruct HI as (ly1 & S1 & hp1 & kk & H1 & jk & HEQ & HJ & HPK & HERR & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (_ & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16656) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR1 : ARx ly1 S1 hp1 W1 mem1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE1 & _).
cbn [set_exp_held hs_expected] in HE1.
pose proof HE1 as (MvE & MnE & _ & MwE & (HnleC & HcapLt) & HvvE & _ & _ & HFallE).
unfold cnl_E, hl_n in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE. cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR).
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))) by (cbn [length]; lia).
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, length_app in HnE. lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
destruct (cnl_rec_fields B ly1 S1 W1 mem1 (HA + 64) (cnl_E (r :: rs) jk) true 0%nat HE1 ltac:(cbn; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0) by (cbn; lia). exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by (unfold APARTIAL in HlenR; lia).
  replace (hl_v EE + 8) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0 + 8) by (cbn; lia). exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
destruct (cnl_mk A_cnl_loop W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn AZS MwE HFRM Cgone AGN MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(unfold APARTIAL in HlenR; lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27).
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall k, (k < 18)%nat -> ew Ev (32 + k) = nth k (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEv. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew Ev 32 = Z_to_bv 64 gone) by exact (EX 0%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 (fst r)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew Ev 36 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 4%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew Ev 2) = sp0 - 128) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Vb9 : base_val Ev (Some 9%nat) = HA) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v EE)) by exact (EX 1%nat ltac:(lia)).
assert (Vb33 : base_val Ev (Some 33%nat) = hl_v EE) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (rewrite HEv; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Vbg : base_val Ev (Some 271%nat) = VAL A_g_gone)
  by (change (Some 271%nat) with (Some A_g_gone); cbn [base_val]; rewrite Eg; apply unsigned_lit_small; exact (pa_val_range _)).
assert (Vb2 : base_val Ev (Some 2%nat) = sp0 - 128) by (cbn [base_val]; exact Usp).
clear HEv EX.
(* the head of s->expected without its write window: nothing below is stored until gesture_model returns *)
pose proof (st_ok_pi_region_nth Ev (ss_cnll A_cnl_loop) _ 2 cnl_headL HS eq_refl) as Hrh.
assert (HrS : region_ok SEGS Ev (ms_mem (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS))))
  cnl_headS).
{ unfold cnl_headL, cnl_headS, region_ok in Hrh |- *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in Hrh |- *.
  destruct Hrh as (A1 & A2 & _ & A4). split; [exact A1|]. split; [exact A2|]. split; [intros o Ho; lia | exact A4]. }
pose proof (ast_ok_pi_set_region Ev (ss_cnll A_cnl_loop) _ 2 cnl_headL cnl_headS HS eq_refl ltac:(reflexivity)
  ltac:(vm_compute; reflexivity) HrS) as HS'.
clear HS Hrh HrS. rename HS' into HS.
(* the callee-saved registers at the loop head, as the state names them *)
prreg HS (2%bv : bv 5) O2. prreg HS (3%bv : bv 5) O3. prreg HS (4%bv : bv 5) O4. prreg HS (8%bv : bv 5) O8.
prreg HS (9%bv : bv 5) O9. prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (22%bv : bv 5) O22.
prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24. prreg HS (25%bv : bv 5) O25. prreg HS (26%bv : bv 5) O26.
prreg HS (27%bv : bv 5) O27.
assert (HOBx : ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO)
  by (destruct HOB as [H0 | (Hc1 & Hc2 & _)]; [left; exact H0 | right; split; assumption]).
assert (HinR1 : In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks (cnl_E (r :: rs) jk))).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). left. reflexivity. }
assert (HnH1 : ~ In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks H1)).
{ pose proof (nls_exp_held_nodup _ _ _ _ _ HSRC) as Hnd. cbn [set_exp_held hs_expected hs_held] in Hnd.
  exact (nls_nodup_disj _ _ _ _ Hnd HinR1). }
assert (HgarR0 : garr8 SEGS (arm W1 mem1) (fst r) (bzs (snd r))).
{ unfold bzs in HgarR. rewrite map_app in HgarR. apply garr8_app in HgarR as [Hg _]. exact Hg. }
unfold A_cnl_loop.
(* ---- 0x859dc: lbu a0, g_gone; beqz ---- *)
paj_run_tok_xR RUNg HS HJ SHOK Bspan. { nls_nowin_awr. }
psrr_branch_tok RUNg BRg HS SHOK Bspan.
- (* g_gone clear: next_line, the two compares, bcmp *)
  assert (Hg0 : gone = 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_eq in Hc; exact Hc).
  destruct (HSTR Hg0) as (rest0 & Hsk). rewrite nls_bsr_cons, <- app_assoc in Hsk. cbn [app] in Hsk.
  set (An := cpos gone A0 pre) in *.
  assert (HAn0 : 0 <= An) by (unfold An, cpos; rewrite Hg0; cbn; lia).
  assert (HAnO : An + Z.of_nat (length (snd r)) + 1 <= NO).
  { pose proof (f_equal (@length byte) Hsk) as Hl. rewrite length_skipn, length_app in Hl. cbn [length] in Hl. lia. }
  destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [rewrite Hob0 in AOBN; cbn [length] in AOBN; lia|].
  destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (HO16 & HO4096 & _ & HOle & HOreq1 & HOceil & _ & HOoff & HOapp & HOpres).
  (* ---- to next_line(at, sp + 16, sp + 8) ---- *)
  paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan AF_fr_next_line. { nls_nowin_awr. }
  assert (MQ1 : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ1) as (AV1 & AP1).
  pmkst HS.
  prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
  prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
  assert (UspN : spZ (ms_regs ms0) = sp0 - 128) by (unfold spZ at 1; rewrite N2, E2; apply unsigned_lit_small; lia).
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdN := mdq) in * end.
  destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 (ms_mem ms0) mdN kk HJ)
    as (memS & HJi & _).
  pose proof HJi as (HARN & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRN & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (HPREn : afn_pre_x SEGS B ARx NL_STK ly1 S1 hp1 W1 (ms_regs ms0) (ms_mem ms0) mdN []).
  { eapply (afn_pre_x_atR SEGS B PST ARx (CNL_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W1 (ms_mem ms0) mdN kk (ms_regs ms0)
      NL_STK (- 128 - XO) [] HJi).
    - rewrite UspN. lia.
    - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-8); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
    - lia.
    - unfold NL_STK, NL_FRAME, ESTACK; lia.
    - rewrite WS. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - rewrite N1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite N1. destruct HBASE as (B1 & B2 & _). rewrite unsigned_lit_small by lia. lia.
    - rewrite N3, (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite N4, (EEo 4%nat 4%bv eq_refl). exact R4.
    - apply achain_low. unfold s0Z. rewrite N8, E9, (unsigned_lit_small HA) by lia. rewrite unsigned_lit_small by lia. lia. }
  assert (HATn : val_mem SEGS (arm W1 (ms_mem ms0)) AT 8 An) by (apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact HAT]).
  eapply (SRrG_bind SEGS R R_trans).
  { (* next_line is a strict leaf: its SRr fact lifts to R *)
    apply (SRr_SRrG SEGS R WLE_R).
    eapply (NL W1 ly1 S1 hp1 (ms_regs ms0) (ms_mem ms0) mdN [] (128 + XO) AT (sp0 - 112) (sp0 - 120) An NO OUT ob HPREn).
    - lia.
    - rewrite Z.add_mod, AX16 by lia. reflexivity.
    - rewrite UspN, Etop. lia.
    - intros a Ha. apply HPRN. rewrite UspN in Ha. lia.
    - rewrite N10, (EEo 18%nat 18%bv eq_refl). exact R18.
    - rewrite N11, Usp. f_equal. lia.
    - rewrite N12, Usp. f_equal. lia.
    - exact AAT8.
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 14; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 15; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - lia.
    - lia.
    - lia.
    - apply (nls_ra_stack ly1 S1 (hp1 := hp1) W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 (hp1 := hp1) W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 (hp1 := hp1) W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - exact HATn.
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cno].
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cout].
    - exact AOBN.
    - apply (nls_ob_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cob].
    - lia.
    - intros _. split; [lia|]. split; [lia|]. split; [apply ANO32; lia|].
      intros a Ha. rewrite UspN. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - intros _. split; [rewrite Hsk; apply in_or_app; right; left; reflexivity|].
      split; [exact AMRO|].
      split; [apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia]|].
      { exact HOin. }
      split; [apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia | lia]|].
      { exact HOin. }
      intros a Hr. unfold rom_view in Crom. rewrite (AV1 a). exact (Crom a Hr). }
  cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
  subst W2.
  destruct HARM as [(HAO & _) | (ln & _ & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
  assert (Hln : ln = snd r).
  { destruct Hfl as (rest & Hsk2 & Hnz'). rewrite Hsk in Hsk2. exact (nls_nul_split (snd r) ln (bsr rs ++ rest0) rest Hsk2 HnzR Hnz'). }
  subst ln.
  (* next_line's journal inside this one *)
  pose proof HJn as (_ & _ & _ & HXOn). rewrite UspN in HXOn, HFRn.
  pose proof (ajournal_gx_G_mono_x SEGS B PST ARx [] G (128 + XO) (nl_cells AT (sp0 - 112) (sp0 - 120)) NL_STK (spZ (ms_regs ms0)) []
    ly1 S1 hp1 W1 (ms_mem ms0) mdN [] ly1 S1 hp1 W1 mem2 md2 0 (fun a Ha => False_ind _ (inG_nil a Ha)) HJn) as HJn'.
  rewrite UspN in HJn'.
  pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md [] ly1 S1 hp1 W1 (ms_mem ms0) mdN kk
    NL_STK (sp0 - 128) (128 + XO) (nl_cells AT (sp0 - 112) (sp0 - 120)) [] [] ly1 S1 hp1 W1 mem2 md2 0 HJ (cnl_gx_lift_xR R WLE_R HJn')
    ltac:(rewrite WS; unfold NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)) as HJ2.
  specialize (HJ2 ltac:(intros a (rr & Hrr & Ha); cbn [nl_cells In] in Hrr;
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
    [right; exists (AT, AT + 8); split; [left; reflexivity | cbn [fst snd]; lia] | left; rewrite WS; lia | left; rewrite WS; lia])
    HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))).
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (KEEPn : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 128 - NL_STK <= a < sp0 - 128) ->
    ~ inFP (nl_cells AT (sp0 - 112) (sp0 - 120)) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) (ms_mem ms0) a).
  { intros a Ha Hn Hcx. destruct (Z_lt_le_dec a (sp0 - 128)) as [Hlt | Hge]; [apply HFRn; [exact Ha | lia | exact Hcx]|].
    destruct (Z_lt_le_dec a (sp0 - 128 + (128 + XO))) as [Hlt2 | Hge2]; [apply HXOn; [lia | exact Hcx]|].
    apply HFRn; [exact Ha | lia | exact Hcx]. }
  assert (Hncell : forall a, ~ (sp0 - 120 <= a < sp0 - 104) -> a < AT \/ AT + 8 <= a ->
    ~ inFP (nl_cells AT (sp0 - 112) (sp0 - 120)) a).
  { intros a Hx1 Hx2 (rr & Hrr & Ha). cbn [nl_cells In] in Hrr.
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia. }
  (* back at 0x85a34: keep the four regions, reseat the frame cells line (sp + 16) and len (sp + 8) *)
  jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); apply KEEPn.
    - rewrite Vb2 in Ha. lia.
    - rewrite Vb2 in Ha. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb2 in Ha; lia.
    - rewrite Vbg in Ha. lia.
    - rewrite Vbg in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vbg in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb9 in Ha. lia.
    - rewrite Vb9 in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb9 in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. unfold AREC in *. lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC, NL_STK, NL_FRAME, ESTACK in *. lia.
    - apply Hncell; rewrite Vb33 in Ha; rewrite HreqV in Hvceil; rewrite WS in Hslo; unfold AREC in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc Ev 50 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 50)%nat -> ew Ea m = ew Ev m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (F54 : ew Ea 54 = Z_to_bv 64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
  clear HEa.
  (* atom 66: the line's address, the value next_line left at sp + 16 *)
  apply (st_ok_pi_havoc_hi 66 Ea _ _ [Z_to_bv 64 (OUT + An)]) in HS; [|vm_compute; reflexivity].
  remember (havoc Ea 66 [Z_to_bv 64 (OUT + An)]) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 66)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  assert (F66 : ew Eb 66 = Z_to_bv 64 (OUT + An)) by (rewrite HEb; reflexivity).
  clear HEb.
  assert (OLD : forall m, (m < 50)%nat -> ew Eb m = ew Ev m) by (intros m Hm; rewrite OLDb by lia; exact (OLDa m Hm)).
  assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (Vb2b : base_val Eb (Some 2%nat) = sp0 - 128) by (cbn [base_val]; rewrite OLD by lia; exact Usp).
  assert (Vb9b : base_val Eb (Some 9%nat) = HA) by (rewrite <- Vb9; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vb33b : base_val Eb (Some 33%nat) = hl_v EE) by (rewrite <- Vb33; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vbgb : base_val Eb (Some 271%nat) = VAL A_g_gone).
  { cbn [base_val]. assert (Hb : (A_TEXT <= 271 < A_LIM)%nat) by (cbv [A_TEXT A_LIM]; lia). exact (HEIb 271%nat Hb). }
  assert (HAR2 : ARx ly1 S1 hp1 W1 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
  apply (st_ok_pi_add_region Eb _ _ cnl_cells) in HS; [| reflexivity | | ].
  2: { unfold region_ok, cnl_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
    rewrite Vb2b. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 128) 8 8 (SOff 36 0) (Z.of_nat (length (snd r))));
      [cbn [sv_denot]; rewrite OLD by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; unfold APARTIAL in HlenR; lia | cbn; lia |].
      replace (sp0 - 128 + 8) with (sp0 - 120) by lia. exact Vlen2.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 128) 16 8 (SOff 66 0) (OUT + An));
      [cbn [sv_denot]; rewrite F66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (sp0 - 128 + 16) with (sp0 - 112) by lia. exact Vln2. }
  2: { apply all_disjoint_of_extents. unfold cnl_cells, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem].
    rewrite Vb2b, Vbgb, Vb9b, Vb33b. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC in *. repeat split; lia. }
  assert (SHOK2 : sh_ok SEGS BxL cnl_lSH Eb (mrestrict (w_H W1) mem2)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem2 md2 (HA + 64) 32 HAR2 AZS).
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 9 HA) by (first [rewrite OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem2 md2 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR2 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 33 (hl_v EE)) by (first [rewrite OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85a34: beqz a0 (abort); the length compare (abort) ---- *)
  rewrite N1. paj_run_tok_xR RUNg HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUNg BRg HS SHOK2 Bspan.
  { (* next_line returned 0: impossible, it found r's line *)
    exfalso. rewrite branch_eq_U, (U_atom Eb 54 1), U_lit in Hc0 by (first [rewrite OLDb by lia; exact F54 | lia]).
    apply Z.eqb_eq in Hc0. lia. }
  clear Hc0. paj_run_tok_xR RUNg HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  (* ---- bcmp(line, v[0].s, len) at 0x85a84, returning to 0x85a88 ---- *)
  assert (MQ2 : forall x, mrestrict (w_H W1) (ms_mem ms2) x = mrestrict (w_H W1) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr2 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem2 (ms_mem ms2) MQ2) as (AV2 & AP2).
  assert (AVc : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite AV2, KEEPn; [apply AV1 | lia | rewrite WS in Hslo; unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; rewrite WS in Hslo; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  assert (UspB : spZ (ms_regs ms2) = sp0 - 128) by (unfold spZ at 1; rewrite T2, OLD by lia; rewrite E2; apply unsigned_lit_small; lia).
  assert (HARB : ARx ly1 S1 hp1 W1 (ms_mem ms2) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat1 md2)) mat2
    (with_vm_backing (m_vm_lazy md2) mat1 md2))) by (eapply ajournal_gx_AR_xR; exact HJ2).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_bcmp_gx_at_xR B PST ARx LAWS R_trans WLE_R (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms2) (ms_mem ms2) CNL_STK sp0 FPc ly S hp W mem md []
      ly1 S1 hp1 _ kk (OUT + An) (fst r) (Z.of_nat (length (snd r))) (-128) (Z_to_bv 64 (BASE + 14236)) HG AX16 HJ2).
    - rewrite T10. exact F66.
    - rewrite T11, OLD by lia. exact E35.
    - rewrite T12, OLD by lia. exact E36.
    - unfold APARTIAL in HlenR. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite UspB. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ESTACK. lia.
    - rewrite T3, OLD by lia. rewrite (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite T4, OLD by lia. rewrite (EEo 4%nat 4%bv eq_refl). exact R4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AV2. replace a with (OUT + (a - OUT)) by lia. rewrite (Hob2 (a - OUT)) by lia. discriminate.
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AVc by lia. unfold aview, arm in *. replace a with (fst r + Z.of_nat (Z.to_nat (a - fst r))) by lia.
      rewrite (garr8_mbyte SEGS _ _ _ _ HgarR0) by (unfold bzs; rewrite length_map; lia). discriminate.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - unfold amem_range in *. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
    - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - intros Hp. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia.
    - intros Hp. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia. }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & vb & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
  (* r's line in the stream, as next_line left it *)
  assert (STR : forall i, (i < length (snd r))%nat ->
    aview SEGS (w_H W1) mem2 (OUT + An + Z.of_nat i) = Some (bv_unsigned (nth i (snd r) (Z_to_bv 8 0)))).
  { intros i Hi. replace (OUT + An + Z.of_nat i) with (OUT + (An + Z.of_nat i)) by lia.
    rewrite (Hob2 (An + Z.of_nat i)) by lia. do 2 f_equal.
    replace (Z.to_nat (An + Z.of_nat i)) with (Z.to_nat An + i)%nat by lia.
    rewrite <- nls_nth_skipn, Hsk. rewrite app_nth1 by exact Hi. reflexivity. }
  (* the line is v[0].s's text: bcmp returned 0 *)
  assert (Hv0 : vb = w64 0).
  { apply Hcmp. intros i Hi. rewrite AV2, AVc by lia.
    replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite STR by lia.
    rewrite (nls_view_of_garr8 W1 mem1 (fst r) (snd r) (Z.to_nat i) HgarR0) by lia. reflexivity. }
  assert (HAR3 : ARx ly1 S1 hp1 W1 mem3 md3) by (eapply ajournal_gx_AR_xR; exact HJ3).
  jafter_call_keep_pi HS 67%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); rewrite ?Vb2b, ?Vbgb, ?Vb9b, ?Vb33b in Ha; apply Hfr3;
    rewrite ?HreqV in Hvceil; rewrite ?WS in Hslo; unfold AREC, ESTACK in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Eb 67 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
  assert (OLDc : forall m, (m < 67)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
  assert (F71 : ew Ec 71 = Z_to_bv 64 0) by (rewrite HEc; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv, Hv0; reflexivity).
  clear HEc.
  assert (SHOK3 : sh_ok SEGS BxL cnl_lSH Ec (mrestrict (w_H W1) mem3)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem3 md3 (HA + 64) 32 HAR3 AZS).
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 9 HA) by (first [rewrite OLDc, OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem3 md3 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR3 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 33 (hl_v EE)) by (first [rewrite OLDc, OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85a88: bnez a0 (abort), then gesture_model(s, line, len) ---- *)
  paj_run_tok_xR RUNg HS HJ3 SHOK3 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUNg BRg HS SHOK3 Bspan.
  { exfalso. rewrite branch_ne_U, (U_atom Ec 71 0 F71), U_lit in Hc0 by lia. cbn in Hc0. discriminate. }
  clear Hc0. paj_run_to_tok_xR RUNTOg HS HJ3 SHOK3 Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ3 : forall x, mrestrict (w_H W1) (ms_mem ms4) x = mrestrict (w_H W1) mem3 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr4 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr3 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem3 (ms_mem ms4) MQ3) as (AV3 & AP3).
  assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 128 - 2 * ESTACK <= a < sp0 - 128) ->
    aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) (ms_mem ms2) a).
  { intros a Ha Hn. rewrite AV3. apply Hfr3; [exact Ha | lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  assert (LOW : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). exact (AVc a Ha). }
  assert (FRM : forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (unfold ESTACK; lia). rewrite AV2, KEEPn; [apply AV1 | lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; lia. }
  assert (PRS : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms4) a)
    by (intros a Hp; apply AP3, Hpres3, AP2, HPn, AP1, Hp).
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms4) md1 _ HAR1 LOW FRM PRS (or_intror (conj HOin HCO)) HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  pose proof (nls_err_kept W1 mem1 (ms_mem ms4) LOW HERR) as HERR'.
  assert (Ecp' : cpos gone A0 (pre ++ [r]) = An + Z.of_nat (length (snd r)) + 1).
  { unfold An, cpos. rewrite Hg0. cbn [Z.eqb]. rewrite nls_bsr_app, length_app, nls_bsr_cons, length_app. cbn [length].
    change (bsr []) with (@nil byte). cbn [length]. lia. }
  eapply (cnl_gm_xR pre r rs ly1 S1 hp1 kk H1 jk W1 (ms_regs ms4) (ms_mem ms4) _ (OUT + An) OUT CO
    HEQ HJ3 HPK' HERR' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite Ecp'. apply (nls_vm_kept W1 W1 mem2 (ms_mem ms4)); [|exact Vat2].
    intros i Hi. rewrite KEEPb by (cbn in Hi; unfold ESTACK; lia). exact (AV2 _).
  + exact HCONST'.
  + right. split; [exact HCO|]. split; [exact HOin | exact HOn].
  + intros _. exists rest0. rewrite Ecp'.
    replace (Z.to_nat (An + Z.of_nat (length (snd r)) + 1)) with ((length (snd r) + 1) + Z.to_nat An)%nat by lia.
    rewrite <- skipn_skipn, Hsk, skipn_app, skipn_all2 by lia.
    replace (length (snd r) + 1 - length (snd r))%nat with 1%nat by lia. reflexivity.
  + exact HFRM'.
  + unfold cnl_regs_ok.
    assert (OLDx : forall m, (m < 50)%nat -> ew Ec m = ew Ev m) by (intros m Hm; rewrite OLDc, OLD by lia; reflexivity).
    assert (P24 : getr (ms_regs ms4) 24 = getr regs1 24).
    { rewrite Q24, O24. apply bv_eq. rewrite (HEIc 386%nat ltac:(cbv [A_TEXT A_LIM]; lia)), (HEI 386%nat ltac:(cbv [A_TEXT A_LIM]; lia)).
      reflexivity. }
    rewrite P24.
    rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q22, Q23, Q25, Q26, Q27. repeat (rewrite OLDx by lia).
    rewrite <- O23, <- O26, <- O8, <- O19, <- O2, <- O3, <- O4, <- O9, <- O18, <- O22, <- O25, <- O27.
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10, OLDc, OLD by lia. exact E9.
  + rewrite Q11, OLDc by lia. exact F66.
  + rewrite Q12, OLDc, OLD by lia. exact E36.
  + apply nls_garr8_of_view. intros i Hi. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). rewrite AV2. exact (STR i Hi).
  + exact HOin.
  + intros Hx. apply HOn. apply in_or_app. right. exact Hx.
  + lia.
  + lia.
- (* g_gone set: the text v[0] goes to gesture_model unread *)
  assert (Hg1 : gone <> 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_neq in Hc; exact Hc).
  assert (Ecp : forall p, cpos gone A0 p = A0) by (intros p; unfold cpos; destruct (Z.eqb_spec gone 0); [contradiction | reflexivity]).
  paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ) as (AV & AP).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms0) md1 _ HAR1 (fun a _ => AV a) (fun a _ => AV a) AP HOBx HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  pose proof (nls_err_kept W1 mem1 (ms_mem ms0) (fun a _ => AV a) HERR) as HERR'.
  eapply (cnl_gm_xR pre r rs ly1 S1 hp1 kk H1 jk W1 (ms_regs ms0) (ms_mem ms0) _ (fst r) (fst r) (Z.of_nat (length (snd r)) + 1)
    HEQ HJ HPK' HERR' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite !Ecp in *. apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HAT].
  + exact HCONST'.
  + exact HOB.
  + intros Hg0. contradiction.
  + exact HFRM'.
  + unfold cnl_regs_ok.
    rewrite (eq_trans Q2 (eq_sym O2)), (eq_trans Q3 (eq_sym O3)), (eq_trans Q4 (eq_sym O4)), (eq_trans Q8 (eq_sym O8)),
      (eq_trans Q9 (eq_sym O9)), (eq_trans Q18 (eq_sym O18)), (eq_trans Q19 (eq_sym O19)), (eq_trans Q22 (eq_sym O22)),
      (eq_trans Q23 (eq_sym O23)), (eq_trans Q24 (eq_sym O24)), (eq_trans Q25 (eq_sym O25)), (eq_trans Q26 (eq_sym O26)),
      (eq_trans Q27 (eq_sym O27)).
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10. exact E9.
  + rewrite Q11. exact E35.
  + rewrite Q12. exact E36.
  + apply (nls_garr8_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HgarR0].
  + exact HinR.
  + exact HnH1.
  + lia.
  + lia.
Qed.
(* cnl_drop at R *)
Lemma cnl_drop_xR : forall pre r rs W1 regs1 mem1 md1,
(rs <> [] -> forall W2 regs2 mem2 md2, cnl_inv_xR (pre ++ [r]) rs W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cnl_loop)) mem2 (seg_rom SEGS)) md2) Post_xR) ->
cnl_mid_xR pre r rs W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1) Post_xR.
Proof.
pose proof AX16 as HX16. pose proof AHAE as EHA. pose proof AJLT as Hj4. pose proof AGA as HGa.
pose proof AZS as Hzs. pose proof AEN as HnEE. pose proof AGN as Hgone. pose proof APRE as HPRE.
intros pre r rs W1 regs1 mem1 md1 IHl HM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16656) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (cnl_ha HA j EHA Hj4 HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
destruct HM as (ly1 & S1 & hp1 & kk & H1 & jk & HrecE & HJ0 & HPK & HERR & HSRC & HND & HTX & HCAP & HNn & HCb &
  HPERM & HFRS & HMLE & HMOK & HROOM & HRMr & HCNTr & HATv & HCONST & HOB & HSKIP & HFRM & HREGS).
assert (HAR1 : ARx ly1 S1 hp1 W1 mem1 md1) by (eapply ajournal_gx_AR_xR; exact HJ0).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAE0 & HAH0 & _).
assert (HAE : alist_at B ly1 S1 W1 mem1 (HA + 64) (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) true) by exact HAE0.
assert (HAH : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH0.
clear HAE0 HAH0.
destruct (cnl_alist_parts ly1 S1 W1 mem1 (HA + 64) (hl_v EE) (hl_cap EE) (r :: rs) jk true HAE)
  as (MvE & MnE & McE & MwE & (HnleC & HcapLt) & HvvE & HNDvE & HninE & HFallE).
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR). unfold APARTIAL in HlenR.
assert (HsndNN : 0 <= Z.of_nat (length (snd r))) by apply Nat2Z.is_nonneg.
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))).
{ cbn [length]. rewrite Nat2Z.inj_succ. pose proof (Nat2Z.is_nonneg (length rs)). lia. }
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ unfold hl_n in HnEE. rewrite HrecE, length_app, Nat2Z.inj_add in HnEE.
  pose proof (Nat2Z.is_nonneg (length pre)). lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
pose proof CNLAP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CNR). cbv zeta in CNR.
assert (ROMIMG : forall a, in_rom SEGS a -> in_img SEGS a)
  by (intros a (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
assert (ROMW : forall a, in_rom SEGS a -> ~ (HA + 72 <= a < HA + 76)).
{ intros a Hrom Hc. apply (CNR a); [rewrite EHA in Hc; unfold ASRC in Hc; pose proof (Nat2Z.is_nonneg j); lia | exact Hrom]. }
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & _ & Hrreq1 & Hrceil & Hceil2 & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
destruct (cnl_rec_fields B ly1 S1 W1 mem1 (HA + 64)
  (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) true 0%nat HAE ltac:(cbn [hl_recs length]; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) + 16 * Z.of_nat 0) by (cbn; lia).
  exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by lia.
  replace (hl_v EE + 8) with (hl_v (HL (hl_v EE) (hl_cap EE) (r :: rs) jk) + 16 * Z.of_nat 0 + 8) by (cbn; lia).
  exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
destruct (cnl_mk A_cnl_back W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn Hzs MwE HFRM (proj1 HCONST) Hgone MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(lia)) as [HS SHOK].
(* the disjunctive facts go into a pair (not a Prop), so that lia does not split on them; unpacked at the end *)
pose proof (Dgn, Dgot, Dcell, HOB) as DPACK. clear Dgn Dgot Dcell HOB.
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew Ev 3 = w64 (as_gp B)) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew Ev 4 = w64 (as_tp B)) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (Usp : bv_unsigned (ew Ev 2) = sp0 - 128) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Vb9 : base_val Ev (Some 9%nat) = HA) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (EX : forall k, (k < 18)%nat -> ew Ev (32 + k) = nth k (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEv. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v EE)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew Ev 34 = Z_to_bv 64 (Z.of_nat (length (r :: rs)))) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 (fst r)) by exact (EX 3%nat ltac:(lia)).
assert (ES : forall k, (37 <= k < 50)%nat -> ew Ev k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0)).
{ intros k Hk. assert (Ek : k = (32 + (5 + (k - 37)))%nat) by lia. rewrite Ek at 1.
  rewrite (EX (5 + (k - 37))%nat ltac:(lia)). unfold cnl_lx. rewrite map_app. cbn [map app nth Nat.add].
  apply map_nth. }
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone))
  by (rewrite HEv; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Vb2 : base_val Ev (Some 2%nat) = sp0 - 128) by (cbn [base_val]; exact Usp).
assert (Vbg : base_val Ev (Some A_g_gone) = VAL A_g_gone)
  by (cbn [base_val]; rewrite Eg; apply unsigned_lit_small; exact (pa_val_range _)).
clear HEv EX.
pose proof HG as HGok. pose proof (pal_free B TL) as HBfree.
assert (QA : ASTACK = 16384) by reflexivity.
(* the image bytes the walk reads: the 96 bytes of the source (in g_s and in G), g_gone, g_nout, g_out, the literals *)
assert (ROc : forall b n a, In (b, n) cnl_ro -> b <= a < b + n ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros b n a Hin Ha.
  assert (Hg : inG cnl_ro a) by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  destruct (HGR a Hg) as (Hi & Ho & _). split; [exact Hi|]. split; [exact Ho | exact (proj1 (HGRR a Hg))]. }
assert (GH : forall a, HA <= a < HA + 96 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. apply (ROc (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; right; right; right; left; reflexivity)).
  rewrite EHA in Ha. unfold ASRC in Ha. lia. }
(* ---- 0x85a9c .. 0x85abc: shadow checks, a0 = v[0].s, jal free ---- *)
paj_run_tok_xR RUNg HS HJ0 SHOK Bspan.
{ cbv [ss_mem ss_cnll cnl_lregions cnl_saved cnl_gone cnl_headL cnl_vec].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g;
  [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9 in Ha; apply HGa; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
rename HF into HFa. rename HFr into HFra. rename HG0 into HGra.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite HBfree.
assert (HAR1m : ARx ly1 S1 hp1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR_xR; exact HJ0).
assert (HXnn : 0 <= cnl_go MT (texts H1) (hl_cap H1) rs).
{ apply cnl_go_nonneg. destruct HAH as (_ & _ & _ & _ & (HnH & _) & _). unfold hl_n in HnH. lia. }
assert (Usp2 : spZ (ms_regs ms) = sp0 + -128)
  by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite Q2, Usp; lia).
(* ---- free(v[0].s) at 0x85abc, returning to 0x85ac0 (BASE + 14292) ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ apply (cnl_free_gx_xR R RO RO_ARx AFREE_R XO [(AT, AT + 8)] W1 (ms_regs ms) (ms_mem ms) CNL_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 _ kk
    (fst r) (Z.of_nat (length (snd r)) + 1) (-128) (Z_to_bv 64 (BASE + 14292)) []
    (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr)%nat HJ0 HX16 HinR).
  - rewrite Q10, E35. reflexivity.
  - exact Usp2.
  - reflexivity.
  - lia.
  - rewrite WS, QA. lia.
  - rewrite Q3, E3. reflexivity.
  - rewrite Q4, E4. reflexivity.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly1 _ (spZ (ms_regs ms)) (HA + 72) [] (ms_regs ms)).
    + apply achain_low. lia.
    + rewrite Usp2. lia.
    + unfold s0Z. rewrite Q8, E9, (unsigned_lit_small HA) by lia. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_check_no_loss + 0x168); [exact HCTX_cnl_free|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold AF_fr_check_no_loss. lia.
  - (* the room round: r's free is the one free the budget owes before the rest *)
    exact HRMr.
  - exact (cnl_cntm_free_pre _ r rs H1 _ HCNTr).
  - intros _ i Hi. exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; lia].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r, Z.of_nat (length (snd r)) + 1)).
    apply in_or_app. left. unfold list_blks. apply in_or_app. right.
    apply (in_map (fun rr => (fst rr, Z.of_nat (length (snd rr)) + 1))). rewrite HrecE. apply in_or_app. right. left. reflexivity.
  - apply (mok_station MT S1 S1 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) 0 (mo_free MT) ML HMOK
      (mo_le_refl MT ML S1) (mo_free_nonneg MT ML)). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs2 & HK & Hle & HRM2 & Herr2 & Hpres2).
assert (HAR2 : ARx ly2 S2 hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
(* an image byte outside the allocator's statics and errno: the free kept its view and its presence *)
assert (IMGK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a /\
  (apresent (w_H W1) (ms_mem ms) a -> apresent (w_H W2) mem2 a)).
{ intros a Hi Ho He. split; [exact (proj1 (proj2 (proj2 HK)) a Hi Ho He)|].
  apply (Hpres2 a Hi).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly1 S1 hp1 W1 (ms_mem ms) _ a HAR1m Hi) Hw)).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 hp2 W2 mem2 md2 a HAR2 Hi) Hw)).
  - exact He.
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 (ms_mem ms) _ (fst r) _ a HAR1m HinR Hr Hi). }
jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
   rewrite ?Vb2, ?(Vbg : base_val Ev (Some 271%nat) = VAL A_g_gone), ?Vb9).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK); lia.
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (ROc (VAL A_g_gone) 1 a ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    exact (proj1 (IMGK a Hi Ho He)).
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GH a ltac:(lia)) as (Hi & Ho & He). exact (proj1 (IMGK a Hi Ho He)).
  - intros a Ha Hw. destruct (GH a ltac:(lia)) as (Hi & Ho & He).
    (* writability follows presence (nls_awr_kept): the free's world step is R, not wle *)
    exact (nls_awr_kept W1 W2 (ms_mem ms) mem2 a (proj2 (IMGK a Hi Ho He)) Hw). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc Ev 50 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 50)%nat -> ew Ea m0 = ew Ev m0)
  by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
clear HEa.
assert (F2 : ew Ea 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite OLDa by lia; exact E2).
assert (F9 : ew Ea 9 = Z_to_bv 64 HA) by (rewrite OLDa by lia; exact E9).
assert (F22 : ew Ea 22 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E22).
assert (Vb9a : base_val Ea (Some 9%nat) = HA) by (cbn [base_val]; rewrite F9; apply unsigned_lit_small; lia).
assert (SHOK2 : sh_ok SEGS BxL cnl_dSH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cnl_dSH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - apply (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold BxL. rewrite (U_atom Ea 22 SB F22) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 9 HA F9) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x85ac0 .. 0x85ae4: shadow checks, a1 = v + 16, a2 = (n - 1) * 16, jal __asan_memmove ---- *)
paj_run_tok_xR RUNg HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g;
  [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
rename HF into HFb. rename HFr into HFrb. rename HG0 into HGrb.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 (ms_mem ms0) _ (kk + 1) HJ2) as HAR3.
(* the vector is still live after the free (it is not r's block) *)
assert (Hvin2 : In (hl_v EE, AREC * hl_cap EE) (ablocks B ly2 S2)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in HvinE.
  apply in_app_or in HvinE as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. apply HninE. cbn [map]. left. first [exact Ex | exact (eq_sym Ex)]. }
destruct (alx_blocks _ _ _ LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ _ _ HAR3 Hvin2) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
rewrite HreqV in Vceil, Vapp, Vpres.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
assert (F33 : ew Ea 33 = Z_to_bv 64 (hl_v EE)) by (rewrite OLDa by lia; exact E33).
assert (F34 : ew Ea 34 = Z_to_bv 64 (Z.of_nat (length (r :: rs)))) by (rewrite OLDa by lia; exact E34).
assert (F3 : ew Ea 3 = w64 (as_gp B)) by (rewrite OLDa by lia; exact E3).
assert (F4 : ew Ea 4 = w64 (as_tp B)) by (rewrite OLDa by lia; exact E4).
assert (Uspm : spZ (ms_regs ms0) = sp0 - 128)
  by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite P2, F2;
      apply unsigned_lit_small; lia).
assert (R10 : getr (ms_regs ms0) 10 = w64 (hl_v EE)) by (rewrite P10, F33; reflexivity).
assert (R11 : getr (ms_regs ms0) 11 = w64 (hl_v EE + 16)).
{ rewrite P11, F33, unsigned_lit_small by lia. reflexivity. }
assert (R12 : getr (ms_regs ms0) 12 = w64 (AREC * (Z.of_nat (length (r :: rs)) - 1))).
{ rewrite P12, F34, cnl_cnt16 by lia. unfold w64, AREC. f_equal. lia. }
assert (Ecap : (hl_cap EE =? 0) = false) by (apply Z.eqb_neq; lia).
assert (HvFP : forall a, hl_v EE <= a < hl_v EE + AREC * hl_cap EE -> inFP FPc a).
{ intros a Ha. exists (hl_v EE, hl_v EE + req_size (AREC * hl_cap EE)). split; [|cbn [fst snd]; rewrite HreqV; lia].
  unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v EE, AREC * hl_cap EE)).
  apply in_or_app. left. unfold list_blks. rewrite Ecap. left. reflexivity. }
(* rom_view across the free: the two runs wrote only s->expected.n (no rom byte of g_s), and the free keeps a rom
   byte either because the runtime owns it and it is pinned, or because it is an image byte it did not touch
   (W_journal.v acall_kept_rom_view; the only place this walk reads ROMNS) *)
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a ltac:(lia));
    [exact (Crom a Hrom) | cnl_nowr Vb9 (ROMW a Hrom)] end. }
assert (ROM2 : rom_view SEGS W2 mem2)
  by (eapply (acall_kept_rom_view_x SEGS B ARx LAWS); [exact HAR2 | exact HK | exact ROMNS | exact ROM1]).
assert (ROMK : rom_view SEGS W2 (ms_mem ms0)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a ltac:(lia));
    [exact (ROM2 a Hrom) | cnl_nowr Vb9a (ROMW a Hrom)] end. }
(* ---- the memmove of the records above 0, 0x85ae4 ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ clear HSKIP IHl.
  eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G XO [(AT, AT + 8)] ESTACK (SIGMA WS_asan_memmove)
  (fun a => hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1)) _
  W2 (ms_regs ms0) (ms_mem ms0) CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 _ (kk + 1)
  (- 128) (Z_to_bv 64 (BASE + 14332)) HGok HX16 HJ2).
- exact Uspm.
- reflexivity.
- lia.
- lia.
- rewrite WS, Hes. lia.
- rewrite P3. exact F3.
- rewrite P4. exact F4.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a. destruct (Z_le_gt_dec (hl_v EE) a) as [Hd1|Hd1]; [|right; lia].
  destruct (Z_lt_ge_dec a (hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))) as [Hd2|Hd2]; [left; lia | right; lia].
- intros a Ha HGb. exfalso.
  apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact (proj1 (HGok a HGb))].
- intros a Ha HnG. split; [|unfold AREC in *; lia].
  right. left. split; [apply HvFP; unfold AREC in *; lia|].
  exists (hl_v EE), (AREC * hl_cap EE). split; [exact Hvin2 | rewrite HreqV; unfold AREC in *; lia].
- intros HPRE2 HSC.
  (* the destination is a heap block, so no byte of it is an image byte (amemmove_realizes_x's premise) *)
  assert (MNIMG : forall a, hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1) -> ~ in_img SEGS a).
  { intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE) a HAR3 Hvin2).
    rewrite HreqV. unfold AREC in *. lia. }
  apply (AMOVE ly2 S2 hp2 W2 (ms_regs ms0) (ms_mem ms0) _
    (hl_v EE) (hl_v EE + 16) (AREC * (Z.of_nat (length (r :: rs)) - 1)) HPRE2 R10 R11 R12).
  + unfold AREC in *; lia.
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split; [|split].
    * apply (apresent_writable SEGS). exact (proj1 (Vpres a ltac:(unfold AREC in *; lia))).
    * exact (proj2 (Vpres a ltac:(unfold AREC in *; lia))).
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *. lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split.
    * destruct (proj1 (Vpres a ltac:(unfold AREC in *; lia))) as [Hh [b Hb]].
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *. lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE));
    [exact HAR3 | exact Hvin2 | lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + exact ROMK.
  + intros Hpos. split;
    unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *; lia.
  + exact MNIMG. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hres3 & Hmov) & Hfr3 & Hpres3).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 mem3 md3 (kk + 1) HJ3) as HAR4.
assert (Vb2a : base_val Ea (Some 2%nat) = sp0 - 128)
  by (cbn [base_val]; rewrite F2; apply unsigned_lit_small; lia).
assert (Vbga : base_val Ea (Some A_g_gone) = VAL A_g_gone)
  by (cbn [base_val]; apply HEIa; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
(* the memmove wrote only inside the vector: the frame slots and the two image regions are kept *)
assert (MOFF : forall a, in_img SEGS a -> ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))).
{ intros a Hi Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v EE) (AREC * hl_cap EE) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact Hi]. }
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0;1;2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ clear HSKIP IHl.
  cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
   rewrite ?Vb2a, ?(Vbga : base_val Ea (Some 271%nat) = VAL A_g_gone), ?Vb9a).
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold AREC, ESTACK in *; lia.
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3;
    [pose proof (pa_val_range A_g_gone); lia
    | apply MOFF; exact (proj1 (ROc (VAL A_g_gone) 1 a ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)))
    | pose proof (pa_img_range a (proj1 (ROc (VAL A_g_gone) 1 a ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)))); lia].
  - intros a Ha; lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3;
    [pose proof (pa_img_range a (proj1 (GH a ltac:(lia)))); lia
    | apply MOFF; exact (proj1 (GH a ltac:(lia)))
    | pose proof (pa_img_range a (proj1 (GH a ltac:(lia)))); lia].
  - intros a Ha Hw. apply (cnl_writable_kept_w W2 W2 (ms_mem ms0) mem3 a);
    [intros Hp; exact (Hpres3 a Hp) | apply wle_refl | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 66 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m0, (m0 < 66)%nat -> ew Eb m0 = ew Ea m0)
  by (intros m0 Hm0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm0).
clear HEb.
assert (K2 : ew Eb 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite OLDb by lia; exact F2).
assert (K9 : ew Eb 9 = Z_to_bv 64 HA) by (rewrite OLDb by lia; exact F9).
assert (K22 : ew Eb 22 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact F22).
assert (K33 : ew Eb 33 = Z_to_bv 64 (hl_v EE)) by (rewrite OLDb by lia; exact F33).
assert (K34 : ew Eb 34 = Z_to_bv 64 (Z.of_nat (length (r :: rs)))) by (rewrite OLDb by lia; exact F34).
assert (K3 : ew Eb 3 = w64 (as_gp B)) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E3).
assert (K4 : ew Eb 4 = w64 (as_tp B)) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E4).
assert (E18 : ew Ev 18 = w64 AT) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (K18 : ew Eb 18 = w64 AT) by (rewrite OLDb by lia; rewrite OLDa by lia; exact E18).
assert (KS : forall k, (37 <= k < 50)%nat -> ew Eb k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0))
  by (intros k Hk; rewrite OLDb by lia; rewrite OLDa by lia; exact (ES k Hk)).
assert (Vb9b : base_val Eb (Some 9%nat) = HA) by (cbn [base_val]; rewrite K9; apply unsigned_lit_small; lia).
assert (SHOK3 : sh_ok SEGS BxL cnl_dSH Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, cnl_dSH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - apply (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem3 md3 (HA + 64) 32 HAR4 Hzs).
  - unfold BxL. rewrite (U_atom Eb 22 SB K22) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Eb 9 HA K9) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- 0x85ae8 .. 0x85af4: n - 1 into s->expected.n, then the loop test ---- *)
paj_run_tok_xR RUNg HS HJ3 SHOK3 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g;
  [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
rename HF into HFc. rename HFr into HFrc. rename HG0 into HGrc.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 (ms_mem ms1) _ (kk + 1) HJ3) as HARF.
(* ---- what the free, the memmove and the three runs kept, from (W1, mem1) to (W2, ms_mem ms1) ---- *)
(* an image byte off s->expected.n *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 72 <= a < HA + 76) -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hi Ho He Hw. pose proof (pa_img_range a Hi) as Har.
  clear HSKIP IHl.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a ltac:(lia)); [| cnl_nowr Vb9b Hw] end.
  rewrite (Hfr3 a ltac:(lia) ltac:(apply MOFF; exact Hi) ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a ltac:(lia)); [| cnl_nowr Vb9a Hw] end.
  rewrite (proj1 (proj2 (proj2 HK)) a Hi Ho He).
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a ltac:(lia)); [reflexivity | cnl_nowr Vb9 Hw] end. }
(* a byte of a live block other than the freed text, off the moved records *)
assert (KBLK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1)) ->
  ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1)) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros p n a Hin Ha Hnr Hnm.
  clear HSKIP IHl.
  destruct (cnl_blk ly1 S1 W1 mem1 md1 p n HAR1 Hin) as (_ & Hp4096 & _ & _ & Hpr1 & Hpc & _).
  assert (Hni : ~ in_img SEGS a) by exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 p n a HAR1 Hin Ha).
  assert (Hnw : ~ (HA + 72 <= a < HA + 76)) by (intros Hc; apply Hni; exact (proj1 (GH a ltac:(lia)))).
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a Ha64); [| cnl_nowr Vb9b Hnw] end.
  rewrite (Hfr3 a Ha64 Hnm ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a Ha64); [| cnl_nowr Vb9a Hnw] end.
  replace a with (p + (a - p)) by lia.
  rewrite (proj1 (proj2 HK) p n (a - p) Hin ltac:(lia) ltac:(cbv beta; intros Hc; apply Hnr; rewrite HreqR; lia)).
  replace (p + (a - p)) with a by lia.
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a Ha64); [reflexivity | cnl_nowr Vb9 Hnw] end. }
(* a byte above the allocator's ceiling, off the scratch the callees used *)
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 128 - ASTACK <= a < sp0 - 128) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hs.
  clear HSKIP IHl.
  assert (Hnw : ~ (HA + 72 <= a < HA + 76)) by lia.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a ltac:(lia)); [| cnl_nowr Vb9b Hnw] end.
  rewrite (Hfr3 a ltac:(lia) ltac:(unfold AREC in *; lia) ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb a ltac:(lia)); [| cnl_nowr Vb9a Hnw] end.
  rewrite (proj1 HK a Ha ltac:(lia)).
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra a ltac:(lia)); [reflexivity | cnl_nowr Vb9 Hnw] end. }
(* the records that moved down by one *)
assert (KMOV : forall k, 0 <= k < AREC * (Z.of_nat (length (r :: rs)) - 1) ->
  aview SEGS (w_H W2) (ms_mem ms1) (hl_v EE + k) = aview SEGS (w_H W1) mem1 (hl_v EE + AREC + k)).
{ intros k Hk.
  clear HSKIP IHl.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) (fst r)
    (Z.of_nat (length (snd r)) + 1) HAR1 HvinE HinR
    ltac:(intros Heq; injection Heq as Heq _; apply HninE; cbn [map]; left; first [exact Heq | exact (eq_sym Heq)])) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite HreqV, HreqR in DJ.
  assert (Hni1 : ~ in_img SEGS (hl_v EE + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE)); [exact HAR1 | exact HvinE | rewrite HreqV; unfold AREC in *; lia]).
  assert (Hni2 : ~ in_img SEGS (hl_v EE + AREC + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE)); [exact HAR1 | exact HvinE | rewrite HreqV; unfold AREC in *; lia]).
  assert (Hnw1 : ~ (HA + 72 <= hl_v EE + k < HA + 76))
    by (intros Hc; apply Hni1; exact (proj1 (GH (hl_v EE + k) ltac:(lia)))).
  assert (Hnw2 : ~ (HA + 72 <= hl_v EE + AREC + k < HA + 76))
    by (intros Hc; apply Hni2; exact (proj1 (GH (hl_v EE + AREC + k) ltac:(lia)))).
  assert (Hnw2b : ~ (HA + 72 <= hl_v EE + 16 + k < HA + 76)) by (unfold AREC in Hnw2; exact Hnw2).
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc (hl_v EE + k) ltac:(unfold AREC in *; lia));
    [| cnl_nowr Vb9b Hnw1] end.
  rewrite (Hmov k Hk).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb (hl_v EE + 16 + k) ltac:(unfold AREC in *; lia));
    [| cnl_nowr Vb9a Hnw2b] end.
  replace (hl_v EE + 16 + k) with (hl_v EE + (16 + k)) by lia.
  rewrite (proj1 (proj2 HK) (hl_v EE) (AREC * hl_cap EE) (16 + k) HvinE
    ltac:(rewrite HreqV; unfold AREC in *; lia) ltac:(cbv beta; unfold AREC in *; lia)).
  replace (hl_v EE + (16 + k)) with (hl_v EE + AREC + k) by (unfold AREC; lia).
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra (hl_v EE + AREC + k) ltac:(unfold AREC in *; lia));
    [reflexivity | cnl_nowr Vb9 Hnw2] end. }
(* presence: an image byte that was there is there *)
assert (KPRES : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) (ms_mem ms1) a).
{ intros a Hi Ho He Hp.
  apply (apresent_grows (w_H W2) mem3 (ms_mem ms1) a HGrc). apply Hpres3.
  apply (apresent_grows (w_H W2) mem2 (ms_mem ms0) a HGrb).
  apply (proj2 (IMGK a Hi Ho He)). apply (apresent_grows (w_H W1) mem1 (ms_mem ms) a HGra). exact Hp. }
(* the blocks that survive the free *)
assert (BLK2 : forall p n, In (p, n) (ablocks B ly1 S1) -> (p, n) <> (fst r, Z.of_nat (length (snd r)) + 1) ->
  In (p, n) (ablocks B ly2 S2)).
{ intros p n Hin Hne2. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | exfalso; exact (Hne2 (eq_sym Hx)) | right; exact Hx]. }
(* the source's block addresses are pairwise apart, so every block but the freed text survives untouched *)
assert (NDB : NoDup (hs_blocks (set_exp_held h (cnl_E (r :: rs) jk) H1)))
  by (pose proof HSRC as HSRCx; repeat (destruct HSRCx as [_ HSRCx]); exact HSRCx).
apply NoDup_ListNoDup in NDB. unfold cnl_E in NDB.
rewrite cnl_blocks_set, (cnl_lb_nil (hl_v EE) (hl_cap EE) (r :: rs) jk Hcpos) in NDB. cbn [map] in NDB.
pose proof (cnl_nodup_two (list_blocks (hs_pending h)) [hs_partial h] (map fst rs) (list_blocks H1)
  (hl_v EE) (fst r) NDB) as NDX.
assert (NDnew : NoDup (hs_blocks (set_exp_held h (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) H1))).
{ apply NoDup_ListNoDup. unfold cnl_E.
  rewrite cnl_blocks_set, (cnl_lb_nil (hl_v EE) (hl_cap EE) rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk) Hcpos).
  exact (cnl_nodup_drop (list_blocks (hs_pending h)) [hs_partial h] [hl_v EE] (map fst rs) (list_blocks H1)
    (fst r) NDB). }
(* every live block but the freed text and the vector keeps its bytes and its writability *)
assert (HreqT : forall x : Z * list byte, req_size (Z.of_nat (length (snd x)) + 1) = Z.of_nat (length (snd x)) + 1).
{ intros x. unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq;
  [apply Z.eqb_eq in Eq; pose proof (Nat2Z.is_nonneg (length (snd x))); lia | reflexivity]. }
assert (KOFF : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <= a < p + req_size n ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1))).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 p n (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 Hin HinR
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. lia. }
assert (KOFV : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> hl_v EE -> p <= a < p + req_size n ->
  ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))).
{ intros p n a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 p n (hl_v EE) (AREC * hl_cap EE) HAR1 Hin HvinE
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite HreqV in DJx. unfold AREC in *. lia. }
assert (KBK : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <> fst r -> p <> hl_v EE -> p <= a < p + req_size n ->
  abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros p n a Hin Hp1 Hp2 Ha. split.
  - exact (KBLK p n a Hin Ha (KOFF p n a Hin Hp1 Ha) (KOFV p n a Hin Hp2 Ha)).
  - intros Hw.
    destruct (cnl_blk ly2 S2 W2 (ms_mem ms1) _ p n HARF
      (BLK2 p n Hin ltac:(intros Heq; injection Heq as Heq _; exact (Hp1 Heq))))
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres).
    exact (apresent_writable SEGS _ _ _ (proj1 (Hpres a Ha))). }
(* the head bytes of the source, off s->expected.n *)
assert (KHD : forall a, HA <= a < HA + 96 -> ~ (HA + 72 <= a < HA + 76) -> abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros a Ha Hw. destruct (GH a Ha) as (Hi & Ho & He). split.
  - exact (KIMG a Hi Ho He Hw).
  - intros Hwr. exact (nls_awr_kept W1 W2 mem1 (ms_mem ms1) a (fun Hp => KPRES a Hi Ho He Hp) Hwr). }
(* the blocks a list names, as members of the state before the free *)
assert (ABLK : forall (l : hlist) LA lines, alist_at B ly1 S1 W1 mem1 LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly1 S1)).
{ intros l LA lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
    destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
  - apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
    rewrite Forall_forall in HF. exact (proj1 (HF x Hx)). }
assert (ABF : forall (l : hlist) b, In b (alist_blks l) -> In (fst b) (list_blocks l)).
{ intros l b Hb. unfold alist_blks, list_blocks in Hb |- *. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app.
  - left. destruct (hl_cap l =? 0); [destruct Hb|]. destruct Hb as [<- | []]. cbn [fst]. left. reflexivity.
  - right. apply in_map_iff in Hb as (x & <- & Hx). cbn [fst]. apply in_map. exact Hx. }
(* the head cells after the store: v and cap kept, n is n - 1 *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok _ ltac:(cbn [ss_mem]; right; right; left; reflexivity)) as (_ & _ & _ & Hchs).
pose proof (proj1 (Forall_forall _ _) Hchs (YP09.mkChunk 72 (CVal 4%N (SOff 34 (-1))))
  ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch72.
assert (MnF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 72) 4 (Z.of_nat (length rs))).
{ replace (HA + 72) with (base_val Eb (Some 9%nat) + 72) by (rewrite Vb9b; lia).
  apply (cnl_val_mem_of_chunk4 Eb _ _ 72 (SOff 34 (-1)) (Z.of_nat (length rs)) Hch72);
  [| pose proof (Nat2Z.is_nonneg (length rs)); cbn [length] in HNNhi; rewrite Nat2Z.inj_succ in HNNhi; lia].
  rewrite (U_atom_off Eb 34 (Z.of_nat (length (r :: rs))) (-1) K34) by lia.
  cbn [length]. rewrite Nat2Z.inj_succ. lia. }
assert (MvF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 64) 8 (hl_v EE)).
{ apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact MvE].
  intros x Hx. cbn [Z.of_nat] in Hx. exact (proj1 (KHD x ltac:(lia) ltac:(lia))). }
assert (McF : val_mem SEGS (arm W2 (ms_mem ms1)) (HA + 64 + 12) 4 (hl_cap EE)).
{ apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact McE].
  intros x Hx. cbn [Z.of_nat] in Hx. exact (proj1 (KHD x ltac:(lia) ltac:(lia))). }
assert (AwF : awr W2 (ms_mem ms1) (HA + 64) 16).
{ intros i Hi. destruct (GH (HA + 64 + i) ltac:(lia)) as (Hi1 & Ho1 & He1).
  exact (nls_awr_kept W1 W2 mem1 (ms_mem ms1) (HA + 64 + i) (fun Hp => KPRES _ Hi1 Ho1 He1 Hp) (MwE i Hi)). }
assert (VNE : hl_v EE <> fst r) by (intros Heq; apply HninE; cbn [map]; left; exact (eq_sym Heq)).
(* ---- the expected list, one record shorter ---- *)
assert (HLD : ldrop_list (cnl_E (r :: rs) jk) 0 =
  cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
  by (unfold cnl_E, ldrop_list;
      cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk firstn skipn app]; reflexivity).
assert (HE2 : alist_at B ly2 S2 W2 (ms_mem ms1) (HA + 64)
  (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) true).
{ rewrite <- HLD.
  apply (ALDROP ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) (HA + 64) (cnl_E (r :: rs) jk) true 0%nat HAE).
  - unfold cnl_E. cbn [HarnessRep.hl_recs length]. lia.
  - unfold cnl_E. cbn [HarnessRep.hl_recs nth]. exact Hbl.
  - intros a Ha. exact (proj1 (KHD a ltac:(lia) ltac:(lia))).
  - exact AwF.
  - replace (HA + 64 + 8) with (HA + 72) by lia.
    assert (Hn1 : hl_n (cnl_E (r :: rs) jk) - 1 = Z.of_nat (length rs))
      by (unfold hl_n, cnl_E; cbn [HarnessRep.hl_recs length]; rewrite Nat2Z.inj_succ; lia).
    rewrite Hn1. exact MnF.
  - intros k Hk.
    change (HarnessRep.hl_v (cnl_E (r :: rs) jk)) with (hl_v EE).
    change (HarnessRep.hl_n (cnl_E (r :: rs) jk)) with (Z.of_nat (length (r :: rs))) in Hk.
    change (Z.of_nat 0) with 0 in Hk |- *.
    replace (hl_v EE + AREC * 0 + k) with (hl_v EE + k) by lia.
    replace (hl_v EE + AREC * 0 + AREC + k) with (hl_v EE + AREC + k) by lia.
    apply KMOV. lia.
  - intros a Ha.
    change (HarnessRep.hl_v (cnl_E (r :: rs) jk)) with (hl_v EE) in Ha.
    change (HarnessRep.hl_cap (cnl_E (r :: rs) jk)) with (hl_cap EE) in Ha.
    change (HarnessRep.hl_n (cnl_E (r :: rs) jk)) with (Z.of_nat (length (r :: rs))) in Ha.
    change (Z.of_nat 0) with 0 in Ha.
    assert (Ha2 : hl_v EE <= a < hl_v EE + req_size (AREC * hl_cap EE)) by (rewrite HreqV; unfold AREC in *; lia).
    assert (Ha3 : ~ (hl_v EE <= a < hl_v EE + AREC * (Z.of_nat (length (r :: rs)) - 1))) by (unfold AREC in *; lia).
    exact (KBLK (hl_v EE) (AREC * hl_cap EE) a HvinE Ha2 (KOFF (hl_v EE) (AREC * hl_cap EE) a HvinE VNE Ha2) Ha3).
  - intros r' Hr' a Ha. change (In r' rs) in Hr'.
    assert (Hin' : In (fst r', Z.of_nat (length (snd r')) + 1) (ablocks B ly1 S1))
      by (rewrite Forall_forall in HFallE; exact (proj1 (HFallE r' (or_intror Hr')))).
    assert (Hne1 : fst r' <> fst r).
    { intros Heq. pose proof HNDvE as ND1. apply NoDup_ListNoDup in ND1. cbn [map] in ND1.
      apply List.NoDup_cons_iff in ND1 as [Hnin _]. apply Hnin. rewrite <- Heq. apply in_map. exact Hr'. }
    assert (Hne2 : fst r' <> hl_v EE)
      by (intros Heq; apply HninE; cbn [map]; right; rewrite <- Heq; apply in_map; exact Hr').
    exact (proj1 (KBK (fst r') (Z.of_nat (length (snd r')) + 1) a Hin' Hne1 Hne2
      ltac:(rewrite (HreqT r'); lia))). }
(* ---- the source with the shorter expected list ---- *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPD & _ & _ & _ & _ & _ & _ & _ & HPIN & HPJLEN & _ & _ & _ & _ & _).
cbn [hs_pending hs_partial hs_pjunk set_exp_held] in HPD, HPIN, HPJLEN.
assert (HreqP : req_size APARTIAL = APARTIAL)
  by (unfold req_size, APARTIAL; destruct (6000 =? 0) eqn:Ez; [discriminate | reflexivity]).
assert (SFP : akept W1 mem1 W2 (ms_mem ms1)
  (gfp (hs_partial h) (bzs (hs_pjunk h)) :: alist_fp (HA + 16) (hs_pending h) ++ alist_fp (HA + 80) H1)).
{ intros rr Hrr a Ha. cbn [In] in Hrr. destruct Hrr as [<- | Hrr].
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, HPJLEN in Ha.
    destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (Hp1 & Hp2).
    exact (KBK (hs_partial h) APARTIAL a HPIN Hp2 Hp1 ltac:(rewrite HreqP; unfold APARTIAL in *; lia)).
  - apply in_app_or in Hrr as [Hrr | Hrr]; revert rr Hrr a Ha.
    + apply (cnl_list_kept ly1 S1 W1 mem1 md1 W2 (ms_mem ms1) (HA + 16) (hs_pending h) false
        (fun b => b <> fst r /\ b <> hl_v EE) HAR1 HPD).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. destruct (NDX b ltac:(apply in_or_app; left; exact Hb)) as (Hb1 & Hb2).
        split; [exact Hb2 | exact Hb1].
    + apply (cnl_list_kept ly1 S1 W1 mem1 md1 W2 (ms_mem ms1) (HA + 80) H1 true
        (fun b => b <> fst r /\ b <> hl_v EE) HAR1 HAH).
      * intros x Hx. apply KHD; lia.
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. destruct (NDX b ltac:(apply in_or_app; right; apply in_or_app; right;
          apply in_or_app; right; exact Hb)) as (Hb1 & Hb2). split; [exact Hb2 | exact Hb1]. }
assert (SBLK : forall b, In b ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks H1) ->
  In b (ablocks B ly2 S2)).
{ intros b Hb. cbn [In] in Hb. destruct Hb as [<- | Hb].
  - destruct (NDX (hs_partial h) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & Hp2).
    exact (BLK2 (hs_partial h) APARTIAL HPIN ltac:(intros Heq; injection Heq as Heq _; exact (Hp2 Heq))).
  - apply in_app_or in Hb as [Hb | Hb]; destruct b as [p n].
    + assert (Hin1 : In (p, n) (ablocks B ly1 S1)) by exact (ABLK (hs_pending h) (HA + 16) false HPD _ Hb).
      destruct (NDX p ltac:(apply in_or_app; left; exact (ABF (hs_pending h) (p, n) Hb))) as (_ & Hp2).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp2 Heq))).
    + assert (Hin1 : In (p, n) (ablocks B ly1 S1)) by exact (ABLK H1 (HA + 80) true HAH _ Hb).
      destruct (NDX p ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; right;
        exact (ABF H1 (p, n) Hb))) as (_ & Hp2).
      exact (BLK2 p n Hin1 ltac:(intros Heq; injection Heq as Heq _; exact (Hp2 Heq))). }
assert (SRC2 : asrc_at B ly2 S2 W2 (ms_mem ms1) HA
  (set_exp_held h (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) H1)).
{ apply (cnl_src_set ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) HA
    (set_exp_held h (cnl_E (r :: rs) jk) H1)
    (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) HSRC);
  [intros x Hx; apply KHD; lia | exact SFP | exact SBLK | exact HE2 | exact NDnew]. }
(* the stream's block is neither the freed text nor the vector *)
assert (OUTNE : forall CO0, In (OUT, CO0) (ablocks B ly1 S1) ->
  ~ In (OUT, CO0) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1) -> OUT <> fst r /\ OUT <> hl_v EE).
{ intros CO0 Hin Hni.
  assert (Hr1 : In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1)).
  { apply in_or_app. left. unfold list_blks, cnl_E.
    cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs]. apply in_or_app. right. cbn [map]. left. reflexivity. }
  assert (Hv1 : In (hl_v EE, AREC * hl_cap EE) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1)).
  { apply in_or_app. left. unfold list_blks, cnl_E.
    cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs]. rewrite Ecap. apply in_or_app. left. left. reflexivity. }
  destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO0 HAR1 Hin) as (_ & _ & _ & _ & HCreq & _).
  split; intros Heq.
  - pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO0 (fst r) (Z.of_nat (length (snd r)) + 1)
      HAR1 Hin HinR ltac:(intros Heq2; apply Hni; rewrite Heq2; exact Hr1)) as DJo.
    unfold zdisjoint in DJo. cbn [fst snd] in DJo. rewrite HreqR in DJo. lia.
  - pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO0 (hl_v EE) (AREC * hl_cap EE)
      HAR1 Hin HvinE ltac:(intros Heq2; apply Hni; rewrite Heq2; exact Hv1)) as DJo.
    unfold zdisjoint in DJo. cbn [fst snd] in DJo. rewrite HreqV in DJo. unfold AREC in *. lia. }
(* ---- the rest of the memory pack at the loop test ---- *)
assert (ATF : val_mem SEGS (arm W2 (ms_mem ms1)) AT 8 (cpos gone A0 (pre ++ [r]))).
{ apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact HATv].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KHI; lia. }
assert (FRM2 : cnl_frame_ok W2 (ms_mem ms1) sp0 regs0).
{ intros i Hi. apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact (HFRM i Hi)].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KHI; [|lia].
  assert (Hib : 0 <= Z.of_nat i <= 12) by (pose proof (Nat2Z.is_nonneg i); lia). lia. }
assert (PK2 : apres_kept B W mem W2 (ms_mem ms1))
  by (intros a Hi Ho He Hp; exact (KPRES a Hi Ho He (HPK a Hi Ho He Hp))).
(* errno's view at the loop test: errno is an image byte off g_s (HGRR), so none of the three runs wrote it; the
   free keeps it (its rule says so); the memmove wrote only inside the vector, a heap block *)
assert (ERRF : forall j0, 0 <= j0 < 4 ->
  aview SEGS (w_H W2) (ms_mem ms1) (as_errno B + j0) = aview SEGS (w_H W) mem (as_errno B + j0)).
{ intros j0 Hj0. set (e0 := as_errno B + j0).
  pose proof (proj1 (proj2 (pal_env B TL)) e0 ltac:(unfold e0; lia)) as Hi.
  pose proof (pa_img_range _ Hi) as Har.
  assert (Hnw : ~ (HA + 72 <= e0 < HA + 76)).
  { intros Hc. destruct (GH e0 ltac:(lia)) as (_ & _ & He). apply He. unfold e0. lia. }
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc e0 ltac:(lia)); [| cnl_nowr Vb9b Hnw] end.
  rewrite (Hfr3 e0 ltac:(lia) ltac:(apply MOFF; exact Hi) ltac:(lia)).
  lazymatch type of HFrb with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem2 (ms_mem ms0) HFrb e0 ltac:(lia)); [| cnl_nowr Vb9a Hnw] end.
  unfold e0. rewrite (Herr2 j0 Hj0). fold e0.
  lazymatch type of HFra with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W1) mem1 (ms_mem ms) HFra e0 ltac:(lia)); [| cnl_nowr Vb9 Hnw] end.
  exact (HERR j0 Hj0). }
(* rom_view at the loop test: the memmove wrote only inside the vector, the last run only s->expected.n *)
assert (ROMF : rom_view SEGS W2 (ms_mem ms1)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hi. pose proof (pa_img_range a Hi) as Har.
  lazymatch type of HFrc with frame_of ?Ev0 ?rs0 _ _ =>
    rewrite (aview_kept_out Ev0 rs0 (w_H W2) mem3 (ms_mem ms1) HFrc a ltac:(lia));
    [| cnl_nowr Vb9b (ROMW a Hrom)] end.
  rewrite (Hfr3 a ltac:(lia) ltac:(apply MOFF; exact Hi) ltac:(lia)).
  exact (ROMK a Hrom). }
assert (CONST2 : cnl_consts W2 (ms_mem ms1)).
{ destruct DPACK as [[[Dgn Dgot] Dcell] HOBx].
  pose proof CNLAP as (_ & _ & _ & _ & _ & _ & Dno & Dout & Dlg & Dlb & Dle & _).
  cbv zeta in Dno, Dout, Dlg, Dlb, Dle.
  assert (OFFW : forall base len x, (VAL A_g_s + 384 <= base \/ base + len <= VAL A_g_s) ->
    base <= x < base + len -> ~ (HA + 72 <= x < HA + 76)).
  { intros base len x Hd Hx Hc. rewrite EHA in Hc. unfold ASRC in Hc.
    pose proof (Nat2Z.is_nonneg j) as Hj0. destruct Hd; lia. }
  assert (LKG : Z.of_nat (length RelayModel.K_GESTURE) = 13) by reflexivity.
  assert (LKB : Z.of_nat (length RelayModel.W_BEGIN) = 5) by reflexivity.
  assert (LKE : Z.of_nat (length RelayModel.W_END) = 3) by reflexivity.
  split.
  { apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cgone]. intros x Hx. cbn [Z.of_nat] in Hx.
    destruct (ROc (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    apply (KIMG x Hi Ho He). destruct Dgn; lia. }
  split.
  { apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cno]. intros x Hx. cbn [Z.of_nat] in Hx.
    destruct (ROc (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_g_nout) 8 x Dno ltac:(lia))). }
  split.
  { apply (cnl_vm_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cout]. intros x Hx. cbn [Z.of_nat] in Hx.
    destruct (ROc (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_g_out) 8 x Dout ltac:(lia))). }
  split.
  { destruct HOBx as [Hnil | (HCO & HCOin & HCOni)].
    - rewrite Hnil. intros i Hi. cbn [length] in Hi. lia.
    - destruct (OUTNE CO HCOin HCOni) as (HO1 & HO2).
      destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HCOin) as (_ & _ & _ & HCle & _).
      apply (cnl_ob_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cob].
      intros i Hi. exact (proj1 (KBK OUT CO (OUT + i) HCOin HO1 HO2 ltac:(lia))). }
  split.
  { exact ROMF. }
  split.
  { apply (cnl_g8_keep W1 W2 mem1 (ms_mem ms1)); [|exact Clg]. intros x Hx. rewrite LKG in Hx.
    destruct (ROc (VAL A_lit_gesture) 13 x ltac:(cbv [cnl_ro]; right; right; right; right; left; reflexivity)
      ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_lit_gesture) 13 x Dlg ltac:(lia))). }
  split.
  { apply (cnl_g8_keep W1 W2 mem1 (ms_mem ms1)); [|exact Clb]. intros x Hx. rewrite LKB in Hx.
    destruct (ROc (VAL A_lit_begin) 5 x ltac:(cbv [cnl_ro]; right; right; right; right; right; left; reflexivity)
      ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_lit_begin) 5 x Dlb ltac:(lia))). }
  { apply (cnl_g8_keep W1 W2 mem1 (ms_mem ms1)); [|exact Cle]. intros x Hx. rewrite LKE in Hx.
    destruct (ROc (VAL A_lit_end) 3 x ltac:(cbv [cnl_ro]; right; right; right; right; right; right; left; reflexivity)
      ltac:(lia)) as (Hi & Ho & He).
    exact (KIMG x Hi Ho He (OFFW (VAL A_lit_end) 3 x Dle ltac:(lia))). } }
assert (PACK1 : cnl_pack ly2 S2 H1 (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
  (pre ++ [r]) W2 (ms_mem ms1))
  by (split; [exact PK2 | split; [exact ERRF | split; [exact SRC2 | split; [exact ATF |
      split; [exact CONST2 | exact FRM2]]]]]).
(* ---- the model-side facts, which no memory touches ---- *)
assert (HrecE2 : hl_recs EE = (pre ++ [r]) ++ rs) by (rewrite <- app_assoc; cbn [app]; exact HrecE).
assert (FRS2 : frames S2 = frames S) by (rewrite Hfrs2; exact HFRS).
assert (MLE2 : mo_le MT S S2 (cnl_go MT (texts HH) (hl_cap HH) (pre ++ [r]))).
{ apply (mle_weaken MT S S2 _ _ ML (mle_station MT S S1 S2 _ _ ML HMLE Hle)). lia. }
assert (MOK2 : mo_ok MT S2 (cnl_go MT (texts H1) (hl_cap H1) rs)).
{ apply (mok_station MT S1 S2 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) (mo_free MT)
    (cnl_go MT (texts H1) (hl_cap H1) rs) ML HMOK Hle HXnn). lia. }
assert (BB2 : blocks_bytes S1 = blocks_bytes S2 + (Z.of_nat (length (snd r)) + 1)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2).
  rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), Eb1, Eb2, !bsum_app, bsum_cons.
  cbn [snd]. lia. }
assert (ROOM2 : cnl_room MMAX (blocks_bytes S2) (texts H1) (hl_cap H1) rs)
  by (replace (blocks_bytes S2) with (blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)) by lia; exact HROOM).
(* the room round: the free's post room is the rest's budget; the counts fell by r's line (W_cnl_cnt.v cnl_cnt_free) *)
assert (RM2 : rp_RM RP S2 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr)) by exact HRM2.
assert (CNT2 : cnl_cnt RP rs H1 (ablocks B ly2 S2)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in HCNTr.
  exact (cnl_cnt_free RP r rs H1 l1 l2 (fst r) HCNTr). }
assert (PERM2 : forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly2 S2)
    (list_blks (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) ++ list_blks H1 ++ rest)).
{ intros rest Hp. pose proof (HPERM rest Hp) as HP1.
  destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb1 in HP1. rewrite Eb2.
  unfold list_blks, cnl_E in HP1 |- *. cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs] in HP1 |- *.
  rewrite Ecap in HP1 |- *. cbn [app map] in HP1 |- *.
  apply (Permutation_cons_inv (a := (fst r, Z.of_nat (length (snd r)) + 1))).
  eapply Permutation_trans; [apply Permutation_middle|].
  eapply Permutation_trans; [exact HP1|]. apply perm_swap. }
assert (OB2 : ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly2 S2) /\
  ~ In (OUT, CO) (list_blks (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)) ++ list_blks H1))).
{ destruct DPACK as [[[_ _] _] HOBx]. destruct HOBx as [Hnil | (HCO & HCOin & HCOni)]; [left; exact Hnil|].
  right. destruct (OUTNE CO HCOin HCOni) as (HO1 & HO2).
  split; [exact HCO|]. split.
  - exact (BLK2 OUT CO HCOin ltac:(intros Heq; injection Heq as Heq _; exact (HO1 Heq))).
  - intros Hc. apply HCOni. apply in_app_or in Hc as [Hc | Hc]; apply in_or_app; [left | right; exact Hc].
    unfold list_blks, cnl_E in Hc |- *. cbn [HarnessRep.hl_cap HarnessRep.hl_v HarnessRep.hl_recs] in Hc |- *.
    rewrite Ecap in Hc |- *. cbn [app map] in Hc |- *.
    destruct Hc as [Hc | Hc]; [left; exact Hc | right; right; exact Hc]. }
assert (SGN : bv_signed (sv_denot Eb (SOff 34 0)) = Z.of_nat (length (r :: rs))).
{ cbn [sv_denot]. rewrite K34, Z.add_0_r, Z_to_bv_bv_unsigned.
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (r :: rs)))) = Z.of_nat (length (r :: rs)))
    by (apply unsigned_lit_small; lia).
  rewrite bv_signed_small by (rewrite Hu; lia). exact Hu. }
assert (SG1 : bv_signed (sv_denot Eb (SLit 1)) = 1) by reflexivity.
psrr_branch_tok RUNg BRg HS SHOK3 Bspan.
- (* 1 < n: the records left are not empty, back to the loop head *)
  assert (Hne : rs <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc. rewrite SGN, SG1 in Hc.
    destruct rs as [|x rs']; [exfalso; cbn [length] in Hc; lia | discriminate]. }
  paj_run_to_tok_xR RUNTOg HS HJ3 SHOK3 Bspan A_cnl_loop.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9b in Ha; apply HGa; lia|].
    apply awr_ok_x_nil. }
  rename HF into HFd. rename HFr into HFrd. rename HG0 into HGrd.
  (* the run from the test to the head wrote nothing, so the pack moves to it *)
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok2 & _).
  pose proof (proj1 (Forall_forall _ _) Hrok2 _ ltac:(cbn [ss_mem add_cond]; right; right; left; reflexivity))
    as (_ & _ & _ & Hchs2).
  pose proof (proj1 (Forall_forall _ _) Hchs2 (YP09.mkChunk 72 (CVal 4%N (SOff 34 (-1))))
    ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch72b.
  assert (MnG : val_mem SEGS (arm W2 (ms_mem ms2)) (HA + 72) 4 (Z.of_nat (length rs))).
  { replace (HA + 72) with (base_val Eb (Some 9%nat) + 72) by (rewrite Vb9b; lia).
    apply (cnl_val_mem_of_chunk4 Eb _ _ 72 (SOff 34 (-1)) (Z.of_nat (length rs)) Hch72b);
    [| pose proof (Nat2Z.is_nonneg (length rs)); cbn [length] in HNNhi; rewrite Nat2Z.inj_succ in HNNhi; lia].
    rewrite (U_atom_off Eb 34 (Z.of_nat (length (r :: rs))) (-1) K34) by lia.
    cbn [length]. rewrite Nat2Z.inj_succ. lia. }
  assert (AEQ : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { intros a Ha.
    destruct (Z_le_gt_dec (HA + 72) a) as [Hl|Hl]; [destruct (Z_lt_ge_dec a (HA + 76)) as [Hh|Hh]|].
    - replace a with (HA + 72 + (a - (HA + 72))) by lia.
      exact (cnl_aview_of_val_mem2 (w_H W2) (w_H W2) (ms_mem ms1) (ms_mem ms2) (HA + 72) 4
        (Z.of_nat (length rs)) (a - (HA + 72)) MnF MnG ltac:(cbn [Z.of_nat]; lia)).
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFrd with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFrd a Ha
          ltac:(cnl_nowr Vb9b Hout)) end.
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFrd with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFrd a Ha
          ltac:(cnl_nowr Vb9b Hout)) end. }
  destruct (cnl_pack_keep ly2 S2 H1 (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
    (pre ++ [r]) W2 (ms_mem ms1) (ms_mem ms2) PACK1 AEQ HGrd) as (PKF & ERRFF & SRCF & ATFF & CSTF & FRMF).
  (* the loop's registers are back where the head wants them *)
  assert (REGS2 : cnl_regs_ok (ms_regs ms2) sp0 HA).
  { prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (19%bv : bv 5) T19. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
    prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
    prreg HS (27%bv : bv 5) T27.
    split; [rewrite T2, K2; reflexivity|].
    split; [rewrite T3, K3; reflexivity|].
    split; [rewrite T4, K4; reflexivity|].
    split; [rewrite T8, K9, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite T9, K9; reflexivity|].
    split; [rewrite T18, K18; reflexivity|].
    split; [rewrite T19, K9, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite T22, K22; reflexivity|].
    split; [rewrite T23, K22, K9, (unsigned_lit_small HA ltac:(lia)), cnl_shr3_add by lia; reflexivity|].
    split; [rewrite T24; apply bv_eq; unfold w64;
            rewrite (HEIb 386%nat ltac:(unfold A_TEXT, A_LIM; lia)),
                    (unsigned_lit_small (VAL (A_HI 106)) (pa_val_range (A_HI 106))); reflexivity|].
    split; [rewrite T25; reflexivity|].
    split; [rewrite T26, K22, K9, (unsigned_lit_small HA ltac:(lia)), cnl_shr3_add by lia; reflexivity|].
    rewrite T27; reflexivity. }
  pmkst HS.
  apply (IHl Hne W2 (ms_regs ms2) (ms_mem ms2) _).
  exists ly2, S2, hp2, (kk + 1), H1, (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk).
  split; [exact HrecE2|]. split; [exact HJ3|]. split; [exact PKF|]. split; [exact ERRFF|]. split; [exact SRCF|].
  split; [exact HND|]. split; [exact HTX|]. split; [exact HCAP|]. split; [exact HNn|].
  split; [exact HCb|]. split; [exact PERM2|]. split; [exact FRS2|]. split; [exact MLE2|].
  split; [exact MOK2|]. split; [exact ROOM2|]. split; [exact RM2|]. split; [exact CNT2|].
  split; [exact ATFF|]. split; [exact CSTF|].
  split; [exact OB2|]. split; [exact HSKIP|]. split; [exact FRMF | exact REGS2].
- (* n <= 1: no record left, the epilogue *)
  assert (Hnil : rs = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_ge in Hc. rewrite SGN, SG1 in Hc.
    destruct rs as [|x rs']; [reflexivity | exfalso; cbn [length] in Hc; pose proof (Nat2Z.is_nonneg (length rs')); lia]. }
  paj_run_tok_xR RUNg HS HJ3 SHOK3 Bspan.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite Vb9b in Ha; apply HGa; lia|].
    apply awr_ok_x_nil. }
  rename HF into HFe. rename HFr into HFre. rename HG0 into HGre.
  (* the epilogue only loads, so the pack moves to the return *)
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok2 & _).
  pose proof (proj1 (Forall_forall _ _) Hrok2 _ ltac:(cbn [ss_mem add_cond]; right; right; left; reflexivity))
    as (_ & _ & _ & Hchs2).
  pose proof (proj1 (Forall_forall _ _) Hchs2 (YP09.mkChunk 72 (CVal 4%N (SOff 34 (-1))))
    ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch72b.
  assert (MnG : val_mem SEGS (arm W2 (ms_mem ms2)) (HA + 72) 4 (Z.of_nat (length rs))).
  { replace (HA + 72) with (base_val Eb (Some 9%nat) + 72) by (rewrite Vb9b; lia).
    apply (cnl_val_mem_of_chunk4 Eb _ _ 72 (SOff 34 (-1)) (Z.of_nat (length rs)) Hch72b);
    [| pose proof (Nat2Z.is_nonneg (length rs)); cbn [length] in HNNhi; rewrite Nat2Z.inj_succ in HNNhi; lia].
    rewrite (U_atom_off Eb 34 (Z.of_nat (length (r :: rs))) (-1) K34) by lia.
    cbn [length]. rewrite Nat2Z.inj_succ. lia. }
  assert (AEQ : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { intros a Ha.
    destruct (Z_le_gt_dec (HA + 72) a) as [Hl|Hl]; [destruct (Z_lt_ge_dec a (HA + 76)) as [Hh|Hh]|].
    - replace a with (HA + 72 + (a - (HA + 72))) by lia.
      exact (cnl_aview_of_val_mem2 (w_H W2) (w_H W2) (ms_mem ms1) (ms_mem ms2) (HA + 72) 4
        (Z.of_nat (length rs)) (a - (HA + 72)) MnF MnG ltac:(cbn [Z.of_nat]; lia)).
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFre with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFre a Ha
          ltac:(cnl_nowr Vb9b Hout)) end.
    - assert (Hout : ~ (HA + 72 <= a < HA + 76)) by lia.
      lazymatch type of HFre with frame_of ?Ev0 ?rs0 _ _ =>
        exact (aview_kept_out Ev0 rs0 (w_H W2) (ms_mem ms1) (ms_mem ms2) HFre a Ha
          ltac:(cnl_nowr Vb9b Hout)) end. }
  destruct (cnl_pack_keep ly2 S2 H1 (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk))
    (pre ++ [r]) W2 (ms_mem ms1) (ms_mem ms2) PACK1 AEQ HGre) as (PKF & ERRFF & SRCF & ATFF & CSTF & FRMF).
  (* the epilogue put every callee-saved register back *)
  prreg HS (Z_to_bv 5 1 : bv 5) U1. prreg HS (Z_to_bv 5 2 : bv 5) U2.
  prreg HS (Z_to_bv 5 3 : bv 5) U3. prreg HS (Z_to_bv 5 4 : bv 5) U4.
  prreg HS (Z_to_bv 5 8 : bv 5) U8. prreg HS (Z_to_bv 5 9 : bv 5) U9.
  prreg HS (Z_to_bv 5 18 : bv 5) U18. prreg HS (Z_to_bv 5 19 : bv 5) U19.
  prreg HS (Z_to_bv 5 20 : bv 5) U20. prreg HS (Z_to_bv 5 21 : bv 5) U21.
  prreg HS (Z_to_bv 5 22 : bv 5) U22. prreg HS (Z_to_bv 5 23 : bv 5) U23.
  prreg HS (Z_to_bv 5 24 : bv 5) U24. prreg HS (Z_to_bv 5 25 : bv 5) U25.
  prreg HS (Z_to_bv 5 26 : bv 5) U26. prreg HS (Z_to_bv 5 27 : bv 5) U27.
  prreg HS (1%bv : bv 5) U1b.
  assert (RA1 : getr (ms_regs ms2) 1 = getr regs0 1).
  { rewrite U1b, (KS 49%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
    apply Z_to_bv_bv_unsigned. }
  assert (RPRES : aregs_preserved regs0 (ms_regs ms2)).
  { intros rr Hrr. unfold acallee_saved in Hrr.
    assert (Hcs : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/
      rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - rewrite U2, K2, (unsigned_lit_small (sp0 - 128) ltac:(lia)).
      replace (sp0 - 128 + 128) with sp0 by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    - rewrite U3, K3. symmetry. exact Hgp0.
    - rewrite U4, K4. symmetry. exact Htp0.
    - rewrite U8, (KS 48%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U9, (KS 47%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U18, (KS 46%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U19, (KS 45%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U20, (KS 44%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U21, (KS 43%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U22, (KS 42%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U23, (KS 41%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U24, (KS 40%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U25, (KS 39%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U26, (KS 38%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned.
    - rewrite U27, (KS 37%nat ltac:(lia)). cbn [Nat.sub]. unfold cnl_svals, CNL_SAVED. cbn [map nth].
      apply Z_to_bv_bv_unsigned. }
  (* the return moves no world: the strict return step lifts to R *)
  apply (SRr_SRrG SEGS R WLE_R).
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_xR.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?dd = _ /\ _ =>
    exists ly2, S2, hp2, rg, mm, dd, (kk + 1),
      (cnl_E rs (HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk)), H1 end.
  split; [cbn [ms_regs ms_mem]; rewrite RA1, Hra0; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ3|].
  split; [exact RPRES|].
  split; [exact PKF|].
  split; [exact ERRFF|].
  split; [exact SRCF|].
  split; [rewrite Hnil; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split.
  { rewrite HTX. unfold texts. rewrite HrecE2, Hnil, app_nil_r. reflexivity. }
  split; [unfold capb in HCb; exact HCb|].
  split.
  { replace (if gone =? 0 then A0 + Z.of_nat (length (bstream EE)) else A0)
      with (cpos gone A0 (pre ++ [r])); [exact ATFF|].
    unfold cpos, bsr, bstream. rewrite HrecE2, Hnil, app_nil_r. reflexivity. }
  destruct CSTF as (Cg2 & Cn2 & Co2 & Cb2 & _).
  split; [exact Cg2|]. split; [exact Cn2|]. split; [exact Co2|]. split; [exact Cb2|].
  split; [exact PERM2|]. split; [exact FRS2|].
  split; [unfold cnl_cost; rewrite HrecE2, Hnil, app_nil_r; exact MLE2|].
  split; [rewrite Hnil in RM2; exact RM2|].
  (* the held list's capacity (cnl_post_x's last two conjuncts): H' = H1, whose capacity is cnl_cap over every
     record (cnl_mid's HCAP at pre ++ [r] = hl_recs EE, rs = []); it never shrinks (W_cnl_cnt.v cnl_cap_ge) *)
  assert (ECAP : hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (hl_recs EE))
    by (rewrite HCAP, HrecE2, Hnil, app_nil_r; reflexivity).
  split; [rewrite ECAP; apply cnl_cap_ge | exact ECAP].
Qed.
(* cnl_loop / cnl_enter at R *)
Lemma cnl_loop_xR : forall k pre rs W1 regs1 mem1 md1, length rs = k -> rs <> [] ->
cnl_inv_xR pre rs W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post_xR.
Proof.
induction k as [|k IH]; intros pre rs W1 regs1 mem1 md1 Hk Hne HI; [destruct rs; [exfalso; exact (Hne eq_refl) | discriminate Hk]|].
destruct rs as [|r rs]; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hk. injection Hk as Hk.
eapply (SRrG_bind SEGS R R_trans); [exact (cnl_step_xR pre r rs W1 regs1 mem1 md1 HI)|].
cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HM).
apply (cnl_drop_xR pre r rs W2 regs2 mem2 md2); [|exact HM].
intros Hne2 W3 regs3 mem3 md3 HI3. exact (IH (pre ++ [r]) rs W3 regs3 mem3 md3 Hk Hne2 HI3).
Qed.
Lemma cnl_enter_xR : forall W1 regs1 mem1 md1, hl_recs EE <> [] -> cnl_inv_xR [] (hl_recs EE) W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post_xR.
Proof.
intros W1 regs1 mem1 md1 Hne HI.
exact (cnl_loop_xR (length (hl_recs EE)) [] (hl_recs EE) W1 regs1 mem1 md1 eq_refl Hne HI).
Qed.
End wR.
End loop.
(* ------------------------------------------------------------------ keeping the source across a frame-only run *)
(* Two memories that agree at a byte keep its view and its writability. *)
Lemma abyte_kept_meq : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) -> abyte_kept W1 m W1 m' a.
Proof.
intros W1 m m' a Hq. split.
- unfold aview, mbyte. rewrite Hq. reflexivity.
- unfold writable_at, wview, arm. rewrite Hq. exact (fun H => H).
Qed.
Lemma cnl_vec_len : forall l : hlist, Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l.
Proof.
intros l Hj. unfold bzs. rewrite length_map, length_app, cnl_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul.
unfold hl_n in Hj. change (Z.of_nat 16) with 16. unfold AREC in *. lia.
Qed.
Lemma cnl_rec_len : forall r : Z * list byte,
Z.of_nat (length (bzs (snd r ++ [Z_to_bv 8 0]))) = Z.of_nat (length (snd r)) + 1.
Proof. intros r. unfold bzs. rewrite length_map, length_app. cbn [length]. lia. Qed.
(* Every byte the source's predicate reads is an application byte below the allocator's ceiling. *)
Lemma cnl_src_low : forall ly1 S1 {hp1 : list Z} W1 mem1 md1 HA1 h1,
ARx ly1 S1 hp1 W1 mem1 md1 -> asrc_at B ly1 S1 W1 mem1 HA1 h1 -> 0x10000 <= HA1 -> HA1 + 96 <= 0x5fb000 ->
forall rr, In rr (asrc_fp HA1 h1) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling.
Proof.
intros ly1 S1 hp1 W1 mem1 md1 HA1 h1 HAR HS HAlo HAhi.
pose proof asan_consts as (C1 & _).
assert (LB : forall (l : hlist) LA, alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false ->
  0x10000 <= LA -> LA + 16 <= 0x5fb000 ->
  forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling).
{ intros l LA Hl Hlo Hhi rr Hin a Ha.
  assert (HL : alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false) by exact Hl.
  destruct HL as [HA2 | HA2];
  (destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec);
   unfold alist_fp in Hin; cbn [In] in Hin;
   destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; lia|];
   apply in_app_or in Hin as [Hin | Hin];
   [ destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|];
     destruct Hin as [<- | []];
     destruct Hv as [(Hc0 & _) | (Hc & Hvin & Hj & Hg)]; [apply Z.eqb_neq in Ec; lia|];
     destruct (cnl_blk ly1 S1 W1 mem1 md1 _ _ HAR Hvin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     unfold gfp in Ha; cbn [fst snd] in Ha; rewrite (cnl_vec_len l Hj) in Ha; lia
   | apply in_map_iff in Hin as (r & <- & Hr);
     rewrite Forall_forall in Hrec; destruct (Hrec r Hr) as (Hin2 & _);
     destruct (cnl_blk ly1 S1 W1 mem1 md1 _ _ HAR Hin2) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     cbn [fst snd gfp] in Ha; unfold bzs in Ha; rewrite length_map, length_app in Ha; cbn [length] in Ha; lia ]). }
intros rr Hin a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & Hpg & _ & Hexp & Hheld & _).
unfold asrc_fp in Hin. cbn [In] in Hin.
destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; unfold ASRC in Ha; lia|].
destruct Hin as [<- | Hin].
{ destruct (cnl_blk ly1 S1 W1 mem1 md1 _ _ HAR Hpin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
  cbn [fst snd gfp] in Ha. unfold bzs in Ha. rewrite length_map in Ha. unfold APARTIAL in *. lia. }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_pending h1) (HA1 + 16) (or_intror Hpend) ltac:(lia) ltac:(lia) rr Hin a Ha). }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_expected h1) (HA1 + 64) (or_introl Hexp) ltac:(lia) ltac:(lia) rr Hin a Ha). }
exact (LB (hs_held h1) (HA1 + 80) (or_introl Hheld) ltac:(lia) ltac:(lia) rr Hin a Ha).
Qed.
(* The source survives a step that changes no byte below the allocator's ceiling. *)
Lemma cnl_src_kept : forall ly1 S1 {hp1 : list Z} W1 mem1 md1 mem2 HA1 h1 lo,
ARx ly1 S1 hp1 W1 mem1 md1 -> asrc_at B ly1 S1 W1 mem1 HA1 h1 -> 0x10000 <= HA1 -> HA1 + 96 <= 0x5fb000 ->
alloc_ceiling <= lo ->
(forall a, 4096 <= a < lo -> mrestrict (w_H W1) mem2 (Z_to_bv 64 a) = mrestrict (w_H W1) mem1 (Z_to_bv 64 a)) ->
asrc_at B ly1 S1 W1 mem2 HA1 h1.
Proof.
intros ly1 S1 hp1 W1 mem1 md1 mem2 HA1 h1 lo HAR HS HAlo HAhi Hlo Hq.
apply (asrc_at_kept B ly1 S1 W1 mem1 ly1 S1 W1 mem2 HA1 h1 HS).
- intros rr Hin a Ha. apply abyte_kept_meq. apply Hq.
  destruct (cnl_src_low ly1 S1 W1 mem1 md1 HA1 h1 HAR HS HAlo HAhi rr Hin a Ha). lia.
- intros b Hb. pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & _ & _ & _ & Hexp & Hheld & _).
  unfold asrc_blks in Hb. cbn [In] in Hb.
  assert (LB : forall (l : hlist) LA, alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false ->
    In b (alist_blks l) -> In b (ablocks B ly1 S1)).
  { intros l LA Hl Hin. destruct Hl as [HA2 | HA2];
    (destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec);
     unfold alist_blks in Hin; apply in_app_or in Hin as [Hin | Hin];
     [ destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]; destruct Hin as [<- | []];
       destruct Hv as [(Hc0 & _) | (_ & Hvin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hvin]
     | apply in_map_iff in Hin as (r & <- & Hr); rewrite Forall_forall in Hrec; exact (proj1 (Hrec r Hr)) ]). }
  destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (LB (hs_pending h1) (HA1 + 16) (or_intror Hpend) Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (LB (hs_expected h1) (HA1 + 64) (or_introl Hexp) Hb)
  | exact (LB (hs_held h1) (HA1 + 80) (or_introl Hheld) Hb)].
Qed.
Lemma set_exp_held_id : forall hh, set_exp_held hh (hs_expected hh) (hs_held hh) = hh.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? ? ?]. reflexivity. Qed.
Lemma cnl_E_id : forall (l : hlist), HL (hl_v l) (hl_cap l) (hl_recs l) (hl_junk l) = l.
Proof. intros [? ? ? ?]. reflexivity. Qed.
Lemma val_mem_meq : forall (W1 : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> mrestrict (w_H W1) m' (Z_to_bv 64 x) = mrestrict (w_H W1) m (Z_to_bv 64 x)) ->
val_mem SEGS (arm W1 m) a n v -> val_mem SEGS (arm W1 m') a n v.
Proof.
intros W1 m m' a n v Hq Hv. apply (akept_vm W1 m W1 m' a n v); [|exact Hv].
intros x Hx. apply abyte_kept_meq. apply Hq. exact Hx.
Qed.
Lemma garr8_meq : forall (W1 : world SEGS) m m' a l,
(forall x, a <= x < a + Z.of_nat (length l) -> mrestrict (w_H W1) m' (Z_to_bv 64 x) = mrestrict (w_H W1) m (Z_to_bv 64 x)) ->
garr8 SEGS (arm W1 m) a l -> garr8 SEGS (arm W1 m') a l.
Proof.
intros W1 m m' a l Hq Hg. apply (akept_garr8 W1 m W1 m' a l); [|exact Hg].
intros x Hx. apply abyte_kept_meq. apply Hq. exact Hx.
Qed.
Lemma aview_meq : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) ->
aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a.
Proof. intros W1 m m' a Hq. exact (proj1 (abyte_kept_meq W1 m m' a Hq)). Qed.
(* The image bytes the walk keeps are below the allocator's ceiling, so a frame-only step keeps them. *)
Lemma cnl_ro_low : forall a, inG cnl_ro a -> 4096 <= a < alloc_ceiling.
Proof.
intros a Ha. pose proof asan_consts as (C1 & _).
pose proof (pa_img_range a (proj1 (HGR a Ha))) as Hi. lia.
Qed.
Lemma cnl_ro_in : forall b n a, In (b, n) cnl_ro -> b <= a < b + n -> inG cnl_ro a.
Proof.
intros b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin|].
unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
Lemma cnl_ro_keep : forall b n a, In (b, n) cnl_ro -> b <= a < b + n -> 4096 <= a < alloc_ceiling.
Proof. intros b n a Hin Ha. apply cnl_ro_low. exact (cnl_ro_in b n a Hin Ha). Qed.
(* this walk's runs write only its own frame, which is below the out-parameter window *)
Ltac cnl_nowin Uspx :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspx in Hr; unfold CNL_FRAME in Hr; lia|]);
  destruct Hin.
(* The caller's ra and s0..s11, read back from the frame region of the symbolic state at the loop head. *)
Lemma cnl_frame_of_region : forall E (W1 : world SEGS) mem1 regs0 lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W1) mem1) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs0 ->
(forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs0 rr) ->
Forall (fun p => In (YP09.mkChunk (fst p) (CVal 8 (SOff (snd p) 0))) cs)
  [(-104, 27%nat); (-96, 26%nat); (-88, 25%nat); (-80, 24%nat); (-72, 23%nat); (-64, 22%nat); (-56, 21%nat);
   (-48, 20%nat); (-40, 19%nat); (-32, 18%nat); (-24, 9%nat); (-16, 8%nat); (-8, 1%nat)] ->
cnl_frame_ok W1 mem1 (spZ regs0) regs0.
Proof.
intros E W1 mem1 regs0 lo hi wlo whi cs HR Hsp HE HF.
assert (G1 : forall od k (rr : bv 5), In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs -> Z.of_nat k = bv_unsigned rr ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs0 + od) 8 (bv_unsigned (getr regs0 rr))).
{ intros od k rr Hc Hk.
  apply (slot_of_region E _ (spZ regs0) cs lo hi wlo whi od (SOff k 0));
  [exact HR | exact Hsp | exact Hc | | apply bv_unsigned_in_range].
  cbn [sv_denot]. rewrite (HE k rr Hk), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
repeat (let Hc := fresh "Hc" in pose proof (Forall_inv HF) as Hc; apply Forall_inv_tail in HF; cbn [fst snd] in Hc).
intros i Hi. unfold arm, cnl_svals, CNL_SAVED.
do 13 (destruct i as [|i]; [cbn [map nth];
  lazymatch goal with |- val_mem _ _ ?a _ (bv_unsigned (getr regs0 ?rr)) =>
    match goal with Hc : In (YP09.mkChunk ?od (CVal 8 (SOff ?k 0))) cs |- _ =>
      replace a with (spZ regs0 + od) by lia; exact (G1 od k rr Hc eq_refl) end end|]).
lia.
Qed.
Lemma cnl_nodup_app_r : forall {A : Type} (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l'.
Proof. intros A l l' H. induction l as [|x l IH]; [exact H|]. apply IH. inversion H; subst. assumption. Qed.
Lemma cnl_list_blks_fst : forall l, map fst (list_blks l) = list_blocks l.
Proof.
intros l. unfold list_blks, list_blocks. rewrite map_app, map_map. cbn [fst].
destruct (hl_cap l =? 0); reflexivity.
Qed.
Theorem pb_check_no_loss_at : forall W ly S hp regs mem md ch HA (j : nat) (h : hsrc) gone A0 NO OUT (ob : list byte),
afn_pre_x SEGS B ARx CNL_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 AT ->
HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
asrc_at B ly S W mem HA h ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
NoDup (texts (hs_held h)) ->
hl_n (hs_expected h) < 2 ^ 26 ->
hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
val_mem SEGS (arm W mem) AT 8 A0 -> 0 <= A0 <= NO ->
val_mem SEGS (arm W mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (arm W mem) (VAL A_g_nout) 8 NO -> val_mem SEGS (arm W mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = NO -> NO <= 2 ^ 40 -> (0 < NO -> NO < 2 ^ 32) -> amem_range OUT (NO + 8) ->
(ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
(gone = 0 -> exists rest, skipn (Z.to_nat A0) ob = bstream (hs_expected h) ++ rest) ->
rom_view SEGS W mem ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
cnl_room MMAX (blocks_bytes S) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) ->
mo_ok MT S (cnl_cost MT (hs_expected h) (hs_held h)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cnl_cost MT_rk (hs_expected h) (hs_held h)) + kr) ->
cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S) ->
AREC * capb (hs_held h) (hs_expected h) < 2 ^ 32 ->
SRr SEGS W (cfg_at SEGS A_check_no_lossP regs mem md)
  (cnl_post_x B PST ARx MT RP G regs ly S hp W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
Proof.
intros W ly S hp regs mem md ch HA j h gone A0 NO OUT ob HPRE HXO HX16 HXtop HXp H10 H11 EHA Hj
HAT8 HATlo HAThi HSRC HGa Hzs HND HnE HnH MAT RA0 Mg Rg Mno Mout HOB Hlen HNO40 HNO32 HmrO HOBK HSKP Hrom
Hlg Hlb Hle HROOM HMOK kr HRM0 HCNT0 HCAPB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16656) by reflexivity.
destruct (cnl_ha HA j EHA Hj HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE & HH0 & _).
destruct (cnl_entry W ly S regs mem md ch HA j (hs_expected h) HPRE H10 EHA Hj HGa Hzs HE HnE) as [HS SHOK].
pose proof (ajournal_gx_init_x SEGS B PST ARx G XO [(AT, AT + 8)] CNL_STK
  (blk_FP (list_blks (hs_expected h) ++ list_blks (hs_held h))) ly S hp W regs mem md ch HPRE HXO HX16 HXtop HXp) as HJ.
remember (Eimg (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs rr).
{ intros m rr Hm. subst Ev. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E1 : ew Ev 1 = getr regs 1) by exact (EEo 1%nat 1%bv eq_refl).
assert (E2 : ew Ev 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E34 : ew Ev 34 = Z_to_bv 64 (hl_n (hs_expected h)))
  by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h)))) Ev)
  by (rewrite HEv; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew Ev 32 = Z_to_bv 64 SB) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HEv.
unfold cfg_at. change (w64 A_check_no_lossP) with (Z_to_bv 64 A_check_no_lossP).
unfold A_check_no_lossP, A_check_no_loss.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_ok_tac; exact Usp | cnl_nowin Usp]. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s->expected.n <= 0: nothing to check, straight to the return *)
  assert (Hn0 : hl_recs (hs_expected h) = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc.
    destruct (hl_recs (hs_expected h)) as [|r rs]; [reflexivity|]. cbn [length] in Hc. lia. }
  paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_ok_tac; exact Usp | cnl_nowin Usp]. }
  assert (MEQ : forall x, ~ (spZ regs - 128 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 128 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
    exists ly, S, hp, r, m, d, 0, (hs_expected h), (hs_held h) end.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ|].
  split.
  { lazymatch type of HS with st_ok_pi _ _ ?Eq _ _ =>
    eapply (aregs_preserved_of_st_ok SEGS _ Eq _ _ regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))) HS);
    [exact HAE | vm_compute; reflexivity] end. }
  split.
  { intros a Hi Hno Hne Hp. cbn [ms_mem]. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { intros j0 Hj0. cbn [ms_mem].
    pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + j0) ltac:(lia)) as Hi.
    pose proof (pa_img_range _ Hi) as Hr.
    apply aview_eq_of. apply MEQa. lia. }
  split.
  { cbn [ms_mem]. rewrite set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 128) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact Hn0|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split; [unfold texts; rewrite Hn0; reflexivity|].
  split; [unfold capb in *; lia|].
  split.
  { cbn [ms_mem]. replace (if gone =? 0 then A0 + Z.of_nat (length (bstream (hs_expected h))) else A0) with A0.
    - apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
      intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia.
    - unfold bstream. rewrite Hn0. cbn [map concat length Z.of_nat]. destruct (gone =? 0); lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
    apply MEQa. destruct HOBK as [-> | (CO & HCO & HCOin & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly S W mem md OUT CO HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
  split; [intros rest Hp; exact Hp|]. split; [reflexivity|].
  split; [unfold cnl_cost; rewrite Hn0; cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HRM0; rewrite Hn0 in HRM0; exact HRM0|].
  (* the held list's capacity: no record, H' = H *)
  split; [lia | rewrite Hn0; reflexivity].
- (* s->expected.n > 0: the rest of the prologue (0x859c0 .. 0x859d8) to the loop head 0x859dc, then the loop *)
  assert (Hne : hl_recs (hs_expected h) <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc. intros He. rewrite He in Hc. cbn [length Z.of_nat] in Hc. lia. }
  (* the blocks of the two lists are a part of the live blocks (asrc_at: NoDup (hs_blocks h)) *)
  assert (APERM0 : exists rest, Permutation (ablocks B ly S) (list_blks (hs_expected h) ++ list_blks (hs_held h) ++ rest)).
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNDb).
    assert (LB : forall (l : hlist) LA, alist_at B ly S W mem LA l true -> incl (list_blks l) (ablocks B ly S)).
    { intros l LA HA2 b Hin. destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec).
      unfold list_blks in Hin. apply in_app_or in Hin as [Hin | Hin].
      - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
        destruct Hv as [(Hc0 & _) | (_ & Hvin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hvin].
      - apply in_map_iff in Hin as (r & <- & Hr). rewrite Forall_forall in Hrec. exact (proj1 (Hrec r Hr)). }
    assert (ND : List.NoDup (list_blks (hs_expected h) ++ list_blks (hs_held h))).
    { apply (NoDup_map_inv fst). rewrite map_app, !cnl_list_blks_fst.
      unfold hs_blocks in HNDb. apply NoDup_ListNoDup in HNDb.
      apply cnl_nodup_app_r in HNDb. apply cnl_nodup_app_r in HNDb. exact HNDb. }
    destruct (perm_of_incl _ (ablocks B ly S) ND (incl_app (LB _ _ HE) (LB _ _ HH0))) as (rest & HP).
    exists rest. rewrite <- app_assoc in HP. exact HP. }
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_check_no_loss + 0x84).
  { apply awr_ok_x_of; [awr_ok_tac; exact Usp | cnl_nowin Usp]. }
  rewrite !wvb_collapse in HJ.
  assert (MEQ : forall x, ~ (spZ regs - 128 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 128 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  (* the registers at the loop head *)
  assert (E3 : ew Ev 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
  assert (E4 : ew Ev 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
  assert (E10 : ew Ev 10 = Z_to_bv 64 HA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew Ev 11 = Z_to_bv 64 AT) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (UHA : bv_unsigned (ew Ev 10) = HA) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (E386 : bv_unsigned (ew Ev 386) = VAL (A_HI 106)) by exact (HEI 386%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?Hh ?ms1) =>
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (23%bv : bv 5) HS) as Q23;
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (26%bv : bv 5) HS) as Q26;
    let e23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
    change (sr_get (ss_regs ss) (23%bv : bv 5)) with e23 in Q23;
    let e26 := eval vm_compute in (sr_get (ss_regs ss) (26%bv : bv 5)) in
    change (sr_get (ss_regs ss) (26%bv : bv 5)) with e26 in Q26 end.
  rewrite (U_shadow_reg Ev 10 32 72 HA E10 E32) in Q23 by lia.
  rewrite (U_shadow_reg Ev 10 32 64 HA E10 E32) in Q26 by lia.
  (* the frame cells: the prologue's 13 stores *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ss) 0%nat) in
    lazymatch r0 with Some ?r => pose proof (st_ok_pi_region_nth Ev ss _ 0%nat r HS eq_refl) as HR0 end end.
  cbn [ms_mem restrict] in HR0.
  assert (Hcp : cpos gone A0 [] = A0) by (unfold cpos, bsr; cbn [map concat length Z.of_nat]; destruct (gone =? 0); lia).
  assert (HCO : exists CO, ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\
    ~ In (OUT, CO) (list_blks (hs_expected h) ++ list_blks (hs_held h)))).
  { destruct HOBK as [-> | (CO & H1 & H2 & H3)]; [exists 0; left; reflexivity|].
    exists CO. right. split; [exact H1|]. split; [exact H2|].
    intros Hin. apply H3. apply (in_map fst) in Hin. cbn [fst] in Hin. rewrite map_app, !cnl_list_blks_fst in Hin.
    unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. exact Hin. }
  destruct HCO as (CO & HCO).
  pmkst HS.
  assert (Epc : 14064 = A_cnl_loop) by reflexivity. rewrite Epc.
  (* the Section-loop hypotheses go by `assumption`: which of them cnl_enter is discharged over depends on what
     cnl_step and cnl_drop use, so a positional list would break on every change in either half *)
  apply (cnl_enter regs ly S hp W mem md ch HA j h gone A0 NO OUT CO ob kr); try assumption.
  unfold cnl_inv.
  exists ly, S, hp, 0, (hs_held h), (hl_junk (hs_expected h)).
  split; [reflexivity|].
  split; [exact HJ|].
  split.
  { intros a Hi Hno Hne' Hp. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { intros j0 Hj0.
    pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + j0) ltac:(lia)) as Hi.
    pose proof (pa_img_range _ Hi) as Hr.
    apply aview_eq_of. apply MEQa. lia. }
  split.
  { unfold cnl_E. rewrite cnl_E_id, set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 128) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact HND|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [unfold txs, count_begin; cbn [map filter length Z.of_nat]; lia|].
  split; [unfold capb; lia|].
  split; [intros rest Hp; unfold cnl_E; rewrite cnl_E_id; exact Hp|].
  split; [reflexivity|].
  split; [cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HMOK; exact HMOK|].
  split; [exact HROOM|].
  split; [exact HRM0|].
  split; [exact (cnl_cnt_entry RP (hs_expected h) (hs_held h) _ HCNT0)|].
  split.
  { rewrite Hcp. apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
    intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia. }
  split.
  { unfold cnl_consts.
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
      apply MEQa. destruct HOBK as [-> | (CO' & HCO' & HCOin & _)]; [cbn [length] in Hi; lia|].
      destruct (cnl_blk ly S W mem md OUT CO' HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
    split.
    { intros a Hin. rewrite (aview_meq W mem (ms_mem ms0) a); [exact (Hrom a Hin)|].
      apply MEQa. destruct Hin as (sg & Hsg & _ & Hsr).
      pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hsr])) as HI. lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.K_GESTURE); [|exact Hlg].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.K_GESTURE) <= 13) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_gesture) 13 x
        ltac:(cbv [cnl_ro]; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_BEGIN); [|exact Hlb].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_BEGIN) <= 5) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_begin) 5 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_END); [|exact Hle].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_END) <= 3) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_end) 3 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. } }
  split; [exact HCO|].
  split.
  { intros Hg0. rewrite Hcp. destruct (HSKP Hg0) as (rest & Hr). exists rest. unfold bsr. unfold bstream in Hr. exact Hr. }
  split.
  { apply (cnl_frame_of_region Ev W (ms_mem ms0) regs _ _ _ _ _ HR0 Usp EEo).
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd In]; repeat (first [left; reflexivity | right]). }
  unfold cnl_regs_ok.
  split; [rewrite Q2, Usp; unfold w64; f_equal; lia|].
  split; [rewrite Q3, E3; exact Hgp|].
  split; [rewrite Q4, E4; exact Htp|].
  split; [rewrite Q8, UHA; reflexivity|].
  split; [rewrite Q9, E10; reflexivity|].
  split; [rewrite Q18, E11; reflexivity|].
  split; [rewrite Q19, UHA; reflexivity|].
  split; [rewrite Q22, E32; reflexivity|].
  split; [exact Q23|].
  split; [rewrite Q24; unfold w64; rewrite <- E386, Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Q25|].
  split; [exact Q26|].
  exact Q27.
Qed.
(* ---- route R: pb_check_no_loss_at at a world relation R.  Its strict proof with the journal at R (from
   ajournal_gx_init_xR, R_refl), the prologue's runs concluding SRrG (RUNg / RUNTOg, BRg), the empty case's return lifted
   by SRr_SRrG (WLE_R), and the loop by cnl_enter_xR.  The strict pb_check_no_loss_at above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis GM_R : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Let RUNg := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let RUNTOg := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let BRg := paj_branch_xR (PI := PI) (R := R).
Theorem pb_check_no_loss_at_xR : forall W ly S hp regs mem md ch HA (j : nat) (h : hsrc) gone A0 NO OUT (ob : list byte),
afn_pre_x SEGS B ARx CNL_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 AT ->
HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
asrc_at B ly S W mem HA h ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
NoDup (texts (hs_held h)) ->
hl_n (hs_expected h) < 2 ^ 26 ->
hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
val_mem SEGS (arm W mem) AT 8 A0 -> 0 <= A0 <= NO ->
val_mem SEGS (arm W mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (arm W mem) (VAL A_g_nout) 8 NO -> val_mem SEGS (arm W mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = NO -> NO <= 2 ^ 40 -> (0 < NO -> NO < 2 ^ 32) -> amem_range OUT (NO + 8) ->
(ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
(gone = 0 -> exists rest, skipn (Z.to_nat A0) ob = bstream (hs_expected h) ++ rest) ->
rom_view SEGS W mem ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
cnl_room MMAX (blocks_bytes S) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) ->
mo_ok MT S (cnl_cost MT (hs_expected h) (hs_held h)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cnl_cost MT_rk (hs_expected h) (hs_held h)) + kr) ->
cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S) ->
AREC * capb (hs_held h) (hs_expected h) < 2 ^ 32 ->
SRrG SEGS R W (cfg_at SEGS A_check_no_lossP regs mem md)
  (cnl_post_xR B PST ARx R MT RP G regs ly S hp W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
Proof.
intros W ly S hp regs mem md ch HA j h gone A0 NO OUT ob HPRE HXO HX16 HXtop HXp H10 H11 EHA Hj
HAT8 HATlo HAThi HSRC HGa Hzs HND HnE HnH MAT RA0 Mg Rg Mno Mout HOB Hlen HNO40 HNO32 HmrO HOBK HSKP Hrom
Hlg Hlb Hle HROOM HMOK kr HRM0 HCNT0 HCAPB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16656) by reflexivity.
destruct (cnl_ha HA j EHA Hj HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE & HH0 & _).
destruct (cnl_entry W ly S regs mem md ch HA j (hs_expected h) HPRE H10 EHA Hj HGa Hzs HE HnE) as [HS SHOK].
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G XO [(AT, AT + 8)] CNL_STK
  (blk_FP (list_blks (hs_expected h) ++ list_blks (hs_held h))) ly S hp W regs mem md ch HPRE HXO HX16 HXtop HXp) as HJ.
remember (Eimg (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs rr).
{ intros m rr Hm. subst Ev. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E1 : ew Ev 1 = getr regs 1) by exact (EEo 1%nat 1%bv eq_refl).
assert (E2 : ew Ev 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E34 : ew Ev 34 = Z_to_bv 64 (hl_n (hs_expected h)))
  by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h)))) Ev)
  by (rewrite HEv; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew Ev 32 = Z_to_bv 64 SB) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HEv.
unfold cfg_at. change (w64 A_check_no_lossP) with (Z_to_bv 64 A_check_no_lossP).
unfold A_check_no_lossP, A_check_no_loss.
paj_run_tok_xR RUNg HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_ok_tac; exact Usp | cnl_nowin Usp]. }
psrr_branch_tok RUNg BRg HS SHOK Bspan.
- (* s->expected.n <= 0: nothing to check, straight to the return *)
  assert (Hn0 : hl_recs (hs_expected h) = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc.
    destruct (hl_recs (hs_expected h)) as [|r rs]; [reflexivity|]. cbn [length] in Hc. lia. }
  paj_run_tok_xR RUNg HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_ok_tac; exact Usp | cnl_nowin Usp]. }
  assert (MEQ : forall x, ~ (spZ regs - 128 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 128 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  prreg HS (1%bv : bv 5) R1.
  (* the return moves no world: the strict return step lifts to R *)
  apply (SRr_SRrG SEGS R WLE_R).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_xR.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
    exists ly, S, hp, r, m, d, 0, (hs_expected h), (hs_held h) end.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ|].
  split.
  { lazymatch type of HS with st_ok_pi _ _ ?Eq _ _ =>
    eapply (aregs_preserved_of_st_ok SEGS _ Eq _ _ regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))) HS);
    [exact HAE | vm_compute; reflexivity] end. }
  split.
  { intros a Hi Hno Hne Hp. cbn [ms_mem]. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { intros j0 Hj0. cbn [ms_mem].
    pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + j0) ltac:(lia)) as Hi.
    pose proof (pa_img_range _ Hi) as Hr.
    apply aview_eq_of. apply MEQa. lia. }
  split.
  { cbn [ms_mem]. rewrite set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 128) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact Hn0|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split; [unfold texts; rewrite Hn0; reflexivity|].
  split; [unfold capb in *; lia|].
  split.
  { cbn [ms_mem]. replace (if gone =? 0 then A0 + Z.of_nat (length (bstream (hs_expected h))) else A0) with A0.
    - apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
      intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia.
    - unfold bstream. rewrite Hn0. cbn [map concat length Z.of_nat]. destruct (gone =? 0); lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
    apply MEQa. destruct HOBK as [-> | (CO & HCO & HCOin & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly S W mem md OUT CO HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
  split; [intros rest Hp; exact Hp|]. split; [reflexivity|].
  split; [unfold cnl_cost; rewrite Hn0; cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HRM0; rewrite Hn0 in HRM0; exact HRM0|].
  (* the held list's capacity: no record, H' = H *)
  split; [lia | rewrite Hn0; reflexivity].
- (* s->expected.n > 0: the rest of the prologue (0x859c0 .. 0x859d8) to the loop head 0x859dc, then the loop *)
  assert (Hne : hl_recs (hs_expected h) <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc. intros He. rewrite He in Hc. cbn [length Z.of_nat] in Hc. lia. }
  (* the blocks of the two lists are a part of the live blocks (asrc_at: NoDup (hs_blocks h)) *)
  assert (APERM0 : exists rest, Permutation (ablocks B ly S) (list_blks (hs_expected h) ++ list_blks (hs_held h) ++ rest)).
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNDb).
    assert (LB : forall (l : hlist) LA, alist_at B ly S W mem LA l true -> incl (list_blks l) (ablocks B ly S)).
    { intros l LA HA2 b Hin. destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec).
      unfold list_blks in Hin. apply in_app_or in Hin as [Hin | Hin].
      - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
        destruct Hv as [(Hc0 & _) | (_ & Hvin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hvin].
      - apply in_map_iff in Hin as (r & <- & Hr). rewrite Forall_forall in Hrec. exact (proj1 (Hrec r Hr)). }
    assert (ND : List.NoDup (list_blks (hs_expected h) ++ list_blks (hs_held h))).
    { apply (NoDup_map_inv fst). rewrite map_app, !cnl_list_blks_fst.
      unfold hs_blocks in HNDb. apply NoDup_ListNoDup in HNDb.
      apply cnl_nodup_app_r in HNDb. apply cnl_nodup_app_r in HNDb. exact HNDb. }
    destruct (perm_of_incl _ (ablocks B ly S) ND (incl_app (LB _ _ HE) (LB _ _ HH0))) as (rest & HP).
    exists rest. rewrite <- app_assoc in HP. exact HP. }
  paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan (AF_fr_check_no_loss + 0x84).
  { apply awr_ok_x_of; [awr_ok_tac; exact Usp | cnl_nowin Usp]. }
  rewrite !wvb_collapse in HJ.
  assert (MEQ : forall x, ~ (spZ regs - 128 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 128 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  (* the registers at the loop head *)
  assert (E3 : ew Ev 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
  assert (E4 : ew Ev 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
  assert (E10 : ew Ev 10 = Z_to_bv 64 HA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew Ev 11 = Z_to_bv 64 AT) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (UHA : bv_unsigned (ew Ev 10) = HA) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (E386 : bv_unsigned (ew Ev 386) = VAL (A_HI 106)) by exact (HEI 386%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?Hh ?ms1) =>
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (23%bv : bv 5) HS) as Q23;
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (26%bv : bv 5) HS) as Q26;
    let e23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
    change (sr_get (ss_regs ss) (23%bv : bv 5)) with e23 in Q23;
    let e26 := eval vm_compute in (sr_get (ss_regs ss) (26%bv : bv 5)) in
    change (sr_get (ss_regs ss) (26%bv : bv 5)) with e26 in Q26 end.
  rewrite (U_shadow_reg Ev 10 32 72 HA E10 E32) in Q23 by lia.
  rewrite (U_shadow_reg Ev 10 32 64 HA E10 E32) in Q26 by lia.
  (* the frame cells: the prologue's 13 stores *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ss) 0%nat) in
    lazymatch r0 with Some ?r => pose proof (st_ok_pi_region_nth Ev ss _ 0%nat r HS eq_refl) as HR0 end end.
  cbn [ms_mem restrict] in HR0.
  assert (Hcp : cpos gone A0 [] = A0) by (unfold cpos, bsr; cbn [map concat length Z.of_nat]; destruct (gone =? 0); lia).
  assert (HCO : exists CO, ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\
    ~ In (OUT, CO) (list_blks (hs_expected h) ++ list_blks (hs_held h)))).
  { destruct HOBK as [-> | (CO & H1 & H2 & H3)]; [exists 0; left; reflexivity|].
    exists CO. right. split; [exact H1|]. split; [exact H2|].
    intros Hin. apply H3. apply (in_map fst) in Hin. cbn [fst] in Hin. rewrite map_app, !cnl_list_blks_fst in Hin.
    unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. exact Hin. }
  destruct HCO as (CO & HCO).
  pmkst HS.
  assert (Epc : 14064 = A_cnl_loop) by reflexivity. rewrite Epc.
  (* the Section-loop hypotheses and the R ones go by `eassumption`, as in the strict proof; AFREE_R first, so that
     its RO fixes the relation's RO before RO_ARx's goal is met *)
  eapply (cnl_enter_xR regs ly S hp W mem md ch HA j h gone A0 NO OUT CO ob kr).
  all: try exact AFREE_R.
  all: try eassumption.
  unfold cnl_inv_xR.
  exists ly, S, hp, 0, (hs_held h), (hl_junk (hs_expected h)).
  split; [reflexivity|].
  split; [exact HJ|].
  split.
  { intros a Hi Hno Hne' Hp. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { intros j0 Hj0.
    pose proof (proj1 (proj2 (pal_env B TL)) (as_errno B + j0) ltac:(lia)) as Hi.
    pose proof (pa_img_range _ Hi) as Hr.
    apply aview_eq_of. apply MEQa. lia. }
  split.
  { unfold cnl_E. rewrite cnl_E_id, set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 128) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact HND|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [unfold txs, count_begin; cbn [map filter length Z.of_nat]; lia|].
  split; [unfold capb; lia|].
  split; [intros rest Hp; unfold cnl_E; rewrite cnl_E_id; exact Hp|].
  split; [reflexivity|].
  split; [cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HMOK; exact HMOK|].
  split; [exact HROOM|].
  split; [exact HRM0|].
  split; [exact (cnl_cnt_entry RP (hs_expected h) (hs_held h) _ HCNT0)|].
  split.
  { rewrite Hcp. apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
    intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia. }
  split.
  { unfold cnl_consts.
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
      apply MEQa. destruct HOBK as [-> | (CO' & HCO' & HCOin & _)]; [cbn [length] in Hi; lia|].
      destruct (cnl_blk ly S W mem md OUT CO' HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
    split.
    { intros a Hin. rewrite (aview_meq W mem (ms_mem ms0) a); [exact (Hrom a Hin)|].
      apply MEQa. destruct Hin as (sg & Hsg & _ & Hsr).
      pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hsr])) as HI. lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.K_GESTURE); [|exact Hlg].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.K_GESTURE) <= 13) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_gesture) 13 x
        ltac:(cbv [cnl_ro]; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_BEGIN); [|exact Hlb].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_BEGIN) <= 5) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_begin) 5 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_END); [|exact Hle].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_END) <= 3) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_end) 3 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. } }
  split; [exact HCO|].
  split.
  { intros Hg0. rewrite Hcp. destruct (HSKP Hg0) as (rest & Hr). exists rest. unfold bsr. unfold bstream in Hr. exact Hr. }
  split.
  { apply (cnl_frame_of_region Ev W (ms_mem ms0) regs _ _ _ _ _ HR0 Usp EEo).
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd In]; repeat (first [left; reflexivity | right]). }
  unfold cnl_regs_ok.
  split; [rewrite Q2, Usp; unfold w64; f_equal; lia|].
  split; [rewrite Q3, E3; exact Hgp|].
  split; [rewrite Q4, E4; exact Htp|].
  split; [rewrite Q8, UHA; reflexivity|].
  split; [rewrite Q9, E10; reflexivity|].
  split; [rewrite Q18, E11; reflexivity|].
  split; [rewrite Q19, UHA; reflexivity|].
  split; [rewrite Q22, E32; reflexivity|].
  split; [exact Q23|].
  split; [rewrite Q24; unfold w64; rewrite <- E386, Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Q25|].
  split; [exact Q26|].
  exact Q27.
Qed.
End wR.
End d.
Theorem pb_check_no_loss_x : cnl_spec_x B PST ARx MT RP G MMAX A_check_no_lossP.
Proof.
intros W ly S hp regs mem md ch XO1 HA j AT1 h gone A0 NO OUT ob.
pose proof (pb_check_no_loss_at XO1 AT1 W ly S hp regs mem md ch HA j h gone A0 NO OUT ob) as HQ.
repeat (let P := fresh "P" in intro P; specialize (HQ P)).
(* the last premise, the readable stack above sp, is image B's (its unwinder); A's walk does not read it *)
intros _. exact HQ.
Qed.
(* ---- route R: the arm lemma, cnl_spec_xR (W_contract_xR_g6.v) at a world relation R.  Beyond R and its laws it takes
   RO / RO_ARx and the R rules AFREE_R (free) and GM_R (gesture_model, which calls realloc and free); next_line,
   bcmp and __asan_memmove stay at their strict contracts (NL, ABCMP, AMOVE).  The re-hiding instance is
   R := wle' SEGS RZ_cf.  The strict pb_check_no_loss_x above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis GM_R : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Theorem pb_check_no_loss_xR : cnl_spec_xR B PST ARx R MT RP G MMAX A_check_no_lossP.
Proof.
intros W ly S hp regs mem md ch XO1 HA j AT1 h gone A0 NO OUT ob.
intros HPRE HXO HX16 HXtop HXp H10 H11 EHA Hj HAT8 HATlo HAThi HSRC HGa Hzs HND HnE HnH MAT RA0 Mg Rg Mno Mout HOB
  Hlen HNO40 HNO32 HmrO HOBK HSKP Hrom Hlg Hlb Hle HROOM HMOK kr HRM0 HCNT0 HCAPB _.
(* the last premise, the readable stack above sp, is image B's (its unwinder); A's walk does not read it *)
eapply (pb_check_no_loss_at_xR XO1 AT1).
(* AFREE_R first, so that its RO fixes the relation's RO before RO_ARx's goal is met *)
all: try exact AFREE_R.
all: eassumption.
Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.): pb_check_no_loss's statement is the AR
   walk's, byte-identical, now a corollary of pb_check_no_loss_x at ARx := ARi0 (cgif's AR with the head set empty),
   PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's ruling (a)) in place of LAWS: the instance builds
   it once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridges are the kit's: W_contract_x
   cnl_spec_x_AR0 for the conclusion; nl_spec_x_of_AR0, gm_spec_g_x_of_AR0 (W_contract_x), abcmp_realizes_x_of_AR0,
   amemmove_realizes_x_of_AR0 (W_sites_x), and afree_cf_rule_c_weak (W_journal) then afree_cf_rule_c_x_of_AR0
   (W_journal_x) at the free site's singleton context for the callees; HP0 at ARi0 is
   ARi0_hp0; IMGC / BLKN are W_kit_x.AR_imgc / AR_blkn; HPST holds at PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Variable MMAX : Z.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
(* No gx_rt of the caller's G: G_fr / G_SL hold errno, so it could never be discharged (W5, 2026-10-29). *)
Hypothesis CNLAP : cnl_objs_apart.
Hypothesis ML : ameter_laws MT.
Hypothesis HGR : gx_ok SEGS B cnl_ro.
Hypothesis HGRR : gx_rt B cnl_ro.
(* An image read-only byte is not errno, and, if the runtime owns it, it is pinned to its image value (rom_pinned,
   W_journal.v; owned .rodata ranges lie inside image A's read-only LOAD, so `~ owned` was false). *)
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
(* rom_out's fourth clause: the sink's overflow head (.bss, 0x5f9b68) is no read-only byte (at PB_fr:
   W_rom_place_fr.v ofl_head_rom_fr). With ROMNS and CNLAP's g_s clause it gives rom_out at gesture_model's G
   (W_rom_place.v cnl_g_rom_out), which gm_spec_g now asks. *)
Hypothesis ROMOH : forall a, in_rom SEGS a -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8).
Hypothesis NL : nl_spec B (BASE + AF_fr_next_line).
Hypothesis GM : gm_spec_g B MT MMAX (BASE + AF_fr_gesture_model).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
(* W1's representation step of list_drop (lib/A/W_list_drop.v alist_at_drop, Qed on a working branch), verbatim. *)
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
Theorem pb_check_no_loss : cnl_spec B MT G MMAX A_check_no_lossP.
Proof.
apply cnl_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
assert (HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
assert (NLx : nl_spec_x B [] (ARi0 SEGS B) (BASE + AF_fr_next_line)) by (apply nl_spec_x_of_AR0; exact NL).
assert (GMx : gm_spec_g_x B [] (ARi0 SEGS B) MT RP_AR MMAX (BASE + AF_fr_gesture_model)) by (apply gm_spec_g_x_of_AR0; exact GM).
assert (ABCx : abcmp_realizes_x SEGS B (ARi0 SEGS B) (SIGMA WS_bcmp)) by (apply abcmp_realizes_x_of_AR0; exact ABCMP).
assert (AMOVEx : amemmove_realizes_x B (ARi0 SEGS B) (SIGMA WS_asan_memmove)) by (apply amemmove_realizes_x_of_AR0; exact AMOVE).
assert (AFREEx : afree_cf_rule_c_x SEGS B [] (ARi0 SEGS B) MT RP_AR [[BASE + AF_fr_check_no_loss + 0x168]])
  by (apply afree_cf_rule_c_x_of_AR0; apply afree_cf_rule_c_weak; exact AFREE).
assert (HCTXf : In [BASE + AF_fr_check_no_loss + 0x168] [[BASE + AF_fr_check_no_loss + 0x168]]) by (cbn; tauto).
eapply pb_check_no_loss_x; eassumption.
Qed.
End cAR.
End b.
End a.
