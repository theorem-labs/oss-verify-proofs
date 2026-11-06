(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a lemma of the image-B relay_add walk (lib/B/W_relay_add_cut.v, segment APP):
   the bytes the relay's old entries read are off the slot relay_add appends.
   arelay_at (lib/B/W_rep.v) does not separate the table block from the entries' own blocks: an entry's held array
   may be the table block itself (re_hp e = T, re_kh e = 896).  The new slot [T + 56 |es|, T + 56 |es| + 56) is still
   never read by an old entry e (index j): a buffer block (cap 8192 or 16384) and a key block are never the table block
   (a key block at T of 896 bytes would hold the table's byte T + 5, the second byte of entry 0's eof field, which is
   0, in its NUL-free text), so they are disjoint from it (AR's pairwise separation); a held array at T that reached the
   slot would hold key 7 j + 5, whose pointer is the 8 bytes at T + 56 j + 40 = e's own hp field = T, a key block at T:
   excluded as above. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_rep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Notation LE8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Local Notation LE4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.
Local Notation LEN8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8.
Local Notation LEN4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Section c.
Variable B : asyms.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.

(* ------------------------------------------------------------------ lists and bytes *)
Lemma ra_sep_req_pos : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
(* W_relay_add_tail.v's tl_key_ptrs_len (a working branch 22c3862876d) *)
Lemma ra_sep_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
rewrite LEN8. cbn [length]. lia.
Qed.
Lemma ra_sep_key_ptrs_app : forall ks1 k ks2,
key_ptrs (ks1 ++ k :: ks2) = key_ptrs ks1 ++ LE8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs ks2.
Proof. intros ks1 k ks2. unfold key_ptrs. rewrite map_app, concat_app. reflexivity. Qed.
(* an entry's 56 bytes: the 40 bytes before its hp field, the hp field, the rest *)
Lemma ra_sep_eb_split : forall e, entry_bytes e =
(LE4 (Z_to_bv 64 (re_fd e)) ++ LE4 (Z_to_bv 64 (re_eof e)) ++ LE4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e ++
 LE8 (Z_to_bv 64 (re_buf e)) ++ LE8 (Z_to_bv 64 (re_used e)) ++ LE8 (Z_to_bv 64 (re_cap e))) ++
LE8 (Z_to_bv 64 (re_hp e)) ++ (LE4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e).
Proof. intros e. unfold entry_bytes. rewrite <- !app_assoc. reflexivity. Qed.
Lemma ra_sep_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (entry_bytes e) = 56%nat.
Proof. intros e H1 H2. unfold entry_bytes. rewrite !length_app, !LEN4, !LEN8, H1, H2. reflexivity. Qed.
Lemma ra_sep_concat_len : forall ly S W mem es, Forall (aentry_ok B ly S W mem) es ->
length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
intros ly S W mem. induction es as [|e es IH]; intros H; [reflexivity|].
apply Forall_cons_iff in H as ((_ & _ & H3 & H4 & _) & Ht).
cbn [map concat length]. rewrite length_app, (ra_sep_eb_len e H3 H4), (IH Ht). lia.
Qed.
Lemma ra_sep_split_at : forall {X : Type} (l : list X) i, (i < length l)%nat ->
exists l1 x l2, l = l1 ++ x :: l2 /\ length l1 = i.
Proof.
intros X l. induction l as [|x l IH]; intros i Hi; [cbn in Hi; lia|].
destruct i as [|i]; [exists [], x, l; split; reflexivity|].
destruct (IH i ltac:(cbn in Hi; lia)) as (l1 & y & l2 & E & L).
exists (x :: l1), y, l2. rewrite E. split; [reflexivity | cbn; lia].
Qed.
Lemma ra_sep_nth_bzs : forall (L : list byte) j, (j < length L)%nat -> nth j (bzs L) 0 = bz (nth j L (Z_to_bv 8 0)).
Proof.
intros L j Hj. unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
apply map_nth.
Qed.
(* two garr8 facts of one memory describe one byte at one address: the bytes are equal *)
Lemma ra_sep_byte : forall m a a' (L1 L2 : list byte) j1 j2,
garr8 SEGS m a (bzs L1) -> garr8 SEGS m a' (bzs L2) -> (j1 < length L1)%nat -> (j2 < length L2)%nat ->
a + Z.of_nat j1 = a' + Z.of_nat j2 -> nth j1 L1 (Z_to_bv 8 0) = nth j2 L2 (Z_to_bv 8 0).
Proof.
intros m a a' L1 L2 j1 j2 H1 H2 Hj1 Hj2 Ha.
assert (Hl1 : (j1 < length (bzs L1))%nat) by (unfold bzs; rewrite length_map; exact Hj1).
assert (Hl2 : (j2 < length (bzs L2))%nat) by (unfold bzs; rewrite length_map; exact Hj2).
pose proof (garr8_mbyte SEGS m a (bzs L1) j1 H1 Hl1) as E1.
pose proof (garr8_mbyte SEGS m a' (bzs L2) j2 H2 Hl2) as E2.
rewrite Ha, E2 in E1.
assert (E3 : Z_to_bv 8 (nth j2 (bzs L2) 0) = Z_to_bv 8 (nth j1 (bzs L1) 0)) by congruence.
rewrite !ra_sep_nth_bzs in E3 by assumption. unfold bz in E3. rewrite !Z_to_bv_bv_unsigned in E3.
symmetry. exact E3.
Qed.
Lemma ra_sep_same : forall m a (L1 L2 : list byte), garr8 SEGS m a (bzs L1) -> garr8 SEGS m a (bzs L2) ->
length L1 = length L2 -> L1 = L2.
Proof.
intros m a L1 L2 H1 H2 Hl. apply (nth_ext L1 L2 (Z_to_bv 8 0) (Z_to_bv 8 0) Hl).
intros j Hj. apply (ra_sep_byte m a a L1 L2 j j H1 H2 Hj); [lia | reflexivity].
Qed.
Lemma ra_sep_mid : forall m a (X M Y : list byte), garr8 SEGS m a (bzs (X ++ M ++ Y)) ->
garr8 SEGS m (a + Z.of_nat (length X)) (bzs M).
Proof.
intros m a X M Y H. unfold bzs in *. rewrite !map_app in H.
apply (proj1 (garr8_app SEGS m a _ _)) in H as [_ H]. rewrite length_map in H.
apply (proj1 (garr8_app SEGS m _ _ _)) in H as [H _]. exact H.
Qed.
Lemma ra_sep_garr8_at : forall m a b l, garr8 SEGS m a l -> a = b -> garr8 SEGS m b l.
Proof. intros m a b l H <-. exact H. Qed.
Lemma ra_sep_le8 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
LE8 (Z_to_bv 64 x) = LE8 (Z_to_bv 64 y) -> x = y.
Proof.
intros x y Hx Hy E.
pose proof (OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le_bytes_to_word_le8 (Z_to_bv 64 x)) as Ex.
rewrite E, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le_bytes_to_word_le8 in Ex.
apply (f_equal bv_unsigned) in Ex. rewrite !unsigned_lit_small in Ex by lia. lia.
Qed.

(* ------------------------------------------------------------------ blocks *)
(* two live blocks that are not the same are disjoint (W_gse_loop.v gsl_disj) *)
Lemma ra_sep_disj : forall ly S (W : world SEGS) mem md p n q m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S W mem md p n q m HAR H1 H2 Hne.
apply in_split in H1 as (a1 & a2 & E1).
assert (H2' : In (q, m) (a1 ++ a2)).
{ rewrite E1 in H2. apply in_app_or in H2 as [H2 | [H2 | H2]];
  [apply in_or_app; left; exact H2 | exfalso; exact (Hne H2) | apply in_or_app; right; exact H2]. }
apply in_split in H2' as (b1 & b2 & E2).
assert (T1 : Permutation ((p, n) :: (q, m) :: b1 ++ b2) ((p, n) :: (a1 ++ a2)))
  by (apply perm_skip; rewrite E2; apply Permutation_middle).
assert (T2 : Permutation ((p, n) :: (a1 ++ a2)) (a1 ++ (p, n) :: a2)) by apply Permutation_middle.
assert (HP : Permutation (ablocks B ly S) ((p, n) :: (q, m) :: b1 ++ b2))
  by (rewrite E1; apply Permutation_sym; exact (perm_trans T1 T2)).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (p, n) (q, m) (b1 ++ b2) HAR HP) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

(* No key of an old entry lies at the table's address: its block would be the table's (two live blocks at one
   address are one block), so |text| = 895, and the key's byte T + 5 (NUL-free text) is the table's byte T + 5,
   the second byte of entry 0's eof field (0 or 1), which is 0. *)
Lemma ra_sep_key_off : forall ly S W mem md T es e k,
AR SEGS B ly S W mem md -> arelay_at B RG ly S W mem T es -> In e es -> In k (re_keys e) -> key_addr k <> T.
Proof.
intros ly S W mem md T es e k HAR HR He Hk Heq.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & (tail & _ & Hlen & Htab) & HF & _).
rewrite Forall_forall in HF.
pose proof (HF e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H15).
rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & _).
rewrite Heq in K1, K2.
assert (HL : Z.of_nat (length (key_text k)) + 1 = ATABLE).
{ destruct (Z.eq_dec (Z.of_nat (length (key_text k)) + 1) ATABLE) as [E|E]; [exact E|exfalso].
  assert (Hne : (T, Z.of_nat (length (key_text k)) + 1) <> (T, ATABLE)) by (intros Hq; apply E; congruence).
  pose proof (ra_sep_disj ly S W mem md _ _ _ _ HAR K1 HinT Hne) as D.
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(clear; lia)) as R1.
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as R2.
  clear - D R1 R2. lia. }
destruct es as [|e0 es']; [destruct He|].
pose proof (HF e0 (or_introl eq_refl)) as (Heof & _).
assert (Eb : nth 5 (key_text k ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) =
  nth 5 (concat (map entry_bytes (e0 :: es')) ++ tail) (Z_to_bv 8 0)).
{ apply (ra_sep_byte (arm W mem) T T _ _ 5 5 K2 Htab);
    [rewrite length_app; cbn [length]; clear - HL; unfold ATABLE in HL; lia
    | clear - Hlen; unfold ATABLE in Hlen; lia | reflexivity]. }
assert (Et : nth 5 (concat (map entry_bytes (e0 :: es')) ++ tail) (Z_to_bv 8 0) = Z_to_bv 8 0).
{ cbn [map concat]. rewrite ra_sep_eb_split, <- !app_assoc.
  rewrite app_nth2 by (rewrite LEN4; lia). rewrite LEN4. change (5 - 4)%nat with 1%nat.
  rewrite app_nth1 by (rewrite LEN4; lia).
  destruct Heof as [-> | ->]; apply bv_eq; vm_compute; reflexivity. }
rewrite Et in Eb. rewrite app_nth1 in Eb by (clear - HL; unfold ATABLE in HL; lia).
apply K3. rewrite <- Eb. apply nth_In. clear - HL. unfold ATABLE in HL. lia.
Qed.

Lemma ra_efp_off_slot : forall ly S W mem md T es,
AR SEGS B ly S W mem md -> arelay_at B RG ly S W mem T es -> (length es < 16)%nat ->
forall e r a, In e es -> In r (aentry_fp e) -> fst r <= a < snd r ->
~ (T + AENT * Z.of_nat (length es) <= a < T + AENT * Z.of_nat (length es) + AENT).
Proof.
intros ly S W mem md T es HAR HR Hn e r a He Hr Ha Hs.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & (tail & _ & _ & Htab) & HF & _).
pose proof (proj1 (Forall_forall _ _) HF e He) as HE.
unfold AENT in Hs.
assert (HsT : T <= a < T + 896) by (clear - Hn Hs; lia).
assert (RT : req_size ATABLE = 896) by reflexivity.
(* a live block other than the table holds no byte of the slot *)
assert (Dt : forall p n0, In (p, n0) (ablocks B ly S) -> (p, n0) <> (T, ATABLE) -> 0 < n0 -> p <= a < p + n0 -> False).
{ intros p n0 Hin Hne Hpos Hpa. pose proof (ra_sep_req_pos n0 Hpos) as Rn.
  destruct (ra_sep_disj ly S W mem md _ _ _ _ HAR Hin HinT Hne) as [D|D]; clear - D Rn RT Hpa HsT; lia. }
unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- (* the buffer block: cap 8192 or 16384, not the table *)
  destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []].
  destruct HE as (_ & _ & _ & _ & _ & H6 & H7 & _ & _ & H10 & _).
  destruct H10 as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [exact (Hc Hc0)|].
  unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd] in Ha.
  apply (Dt (re_buf e) (re_cap e) Hin); [| exact Hcp | clear - Ha H7 Hj; lia].
  intros Hq. assert (Hq2 : re_cap e = ATABLE) by congruence. clear - H6 Hq2. unfold ATABLE in Hq2. lia.
- destruct Hr as [<- | Hr].
  + (* the held array *)
    pose proof HE as (_ & _ & H3 & _ & _ & _ & _ & _ & _ & _ & _ & H12 & _).
    destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & Hkp)].
    * unfold gfp, bzs in Ha. rewrite length_map, Hk in Ha. cbn in Ha. clear - Ha. lia.
    * unfold gfp, bzs in Ha. rewrite length_map, ra_sep_key_ptrs_len in Ha. cbn [fst snd] in Ha.
      destruct (Z.eq_dec (re_hp e) T) as [EhT | EhT].
      2: { apply (Dt (re_hp e) (re_kh e) Hin); [intros Hq; apply EhT; congruence | clear - Hk2; lia |].
           unfold re_nheld in Hk1. clear - Ha Hk1. lia. }
      (* the array is at T and reaches the slot: key 7 j + 5 exists, its pointer is e's own hp field, T *)
      pose proof He as He0.
      apply in_split in He as (es1 & es2 & Hes).
      assert (Hle : length es = (length es1 + 1 + length es2)%nat) by (rewrite Hes, length_app; cbn [length]; lia).
      assert (Hi : (7 * length es1 + 5 < length (re_keys e))%nat) by (clear - Ha Hs Hle EhT; lia).
      destruct (ra_sep_split_at (re_keys e) (7 * length es1 + 5) Hi) as (ks1 & k & ks2 & Hks & Hks1).
      assert (Hkin : In k (re_keys e)) by (rewrite Hks; apply in_or_app; right; left; reflexivity).
      pose proof (ra_sep_key_off ly S W mem md T es e k HAR HR He0 Hkin) as Hoff.
      pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H15).
      rewrite Forall_forall in H15. destruct (H15 k Hkin) as (K1 & _).
      pose proof (al_blocks _ _ LAWS ly S W mem md _ _ HAR K1) as (_ & Hk4096 & Hkceil & _).
      pose proof (al_blocks _ _ LAWS ly S W mem md _ _ HAR HinT) as (_ & HT4096 & HTceil & _).
      pose proof asan_consts as (C1 & _).
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(clear; lia)) as Rk.
      rewrite RT in HTceil.
      (* the key's pointer: the 8 bytes at T + 8 (7 j + 5) *)
      rewrite Hks, ra_sep_key_ptrs_app, EhT in Hkp.
      pose proof (ra_sep_mid _ _ _ _ _ Hkp) as Gk.
      rewrite ra_sep_key_ptrs_len, Hks1 in Gk.
      (* e's hp field: the 8 bytes at T + 56 j + 40 of the table *)
      assert (EQt : concat (map entry_bytes es) ++ tail =
        concat (map entry_bytes es1) ++ entry_bytes e ++ (concat (map entry_bytes es2) ++ tail))
        by (rewrite Hes, map_app, concat_app; cbn [map concat]; rewrite <- !app_assoc; reflexivity).
      rewrite EQt in Htab.
      pose proof (ra_sep_mid _ _ _ _ _ Htab) as Ge.
      rewrite ra_sep_eb_split in Ge.
      pose proof (ra_sep_mid _ _ _ _ _ Ge) as Gh.
      assert (HF1 : Forall (aentry_ok B ly S W mem) es1)
        by (rewrite Hes in HF; apply Forall_app in HF; exact (proj1 HF)).
      rewrite (ra_sep_concat_len ly S W mem es1 HF1) in Gh.
      rewrite !length_app, !LEN4, !LEN8, H3 in Gh.
      rewrite EhT in Gh.
      assert (EqB : LE8 (Z_to_bv 64 (key_addr k)) = LE8 (Z_to_bv 64 T)).
      { apply (ra_sep_same (arm W mem) (T + 56 * Z.of_nat (length es1) + 40)).
        - eapply ra_sep_garr8_at; [exact Gk | clear; lia].
        - eapply ra_sep_garr8_at; [exact Gh | clear; lia].
        - rewrite !LEN8. reflexivity. }
      assert (EK : key_addr k = T).
      { apply (ra_sep_le8 (key_addr k) T); [clear - Hk4096 Hkceil Rk C1; lia | clear - HT4096 HTceil C1; lia | exact EqB]. }
      exact (Hoff EK).
  + (* a key's block: not the table (ra_sep_key_off), so disjoint from it *)
    apply in_map_iff in Hr as (k & <- & Hk).
    pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H15).
    rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & _ & _ & K4).
    unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd length] in Ha.
    destruct (Z.eq_dec (key_addr k) T) as [EkT | EkT].
    * exact (ra_sep_key_off ly S W mem md T es e k HAR HR He Hk EkT).
    * apply (Dt (key_addr k) (Z.of_nat (length (key_text k)) + 1) K1);
        [intros Hq; apply EkT; congruence | clear - K4; lia | clear - Ha; lia].
Qed.
End c.
End b.
End a.
