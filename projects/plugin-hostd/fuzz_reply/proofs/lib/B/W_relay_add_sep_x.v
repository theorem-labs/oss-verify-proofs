(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the ARx twins of the three AR lemmas of lib/B/W_relay_add_sep.v, for the
   APP segment of the image-B walk of relay_add over a generic allocator relation ARx (lib/B/W_relay_add_app_x.v):
   ra_sep_disj -> ra_sep_disj_x, ra_sep_key_off -> ra_sep_key_off_x, ra_efp_off_slot -> ra_efp_off_slot_x.  Each is
   W_relay_add_sep.v's statement over ARx with its laws (LAWS : AR_laws_x SEGS B ARx hl; the ghost head set Hp after S),
   and W_relay_add_sep.v's proof with AR's laws al_* -> AR_laws_x's alx_* and YCbq.v's sep_blocks_perm -> YCbqG.v's
   sep_blocks_x.  The AR-free lemmas of W_relay_add_sep.v (bytes, lists, garr8) are cited from it, not copied.
   The argument is W_relay_add_sep.v's: the new slot [T + 56 |es|, T + 56 |es| + 56) is never read by an old entry e
   (index j).  A buffer block (cap 8192 or 16384) and a key block are never the table block (a key block at T of 896
   bytes would hold the table's byte T + 5, the second byte of entry 0's eof field, which is 0, in its NUL-free text),
   so they are disjoint from it (ARx's pairwise separation of the live blocks, alx_sep); a held array at T that reached
   the slot would hold key 7 j + 5, whose pointer is the 8 bytes at T + 56 j + 40 = e's own hp field = T, a key block
   at T: excluded as above. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_add_sep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Notation LE8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Local Notation LEN8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8.
Local Notation LEN4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Section c.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

(* two live blocks that are not the same are disjoint (W_relay_add_sep.v ra_sep_disj; YCbqG.v sep_blocks_x) *)
Lemma ra_sep_disj_x : forall ly S Hp (W : world SEGS) mem md p n q m,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S Hp W mem md p n q m HAR H1 H2 Hne.
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md p n q m HAR H1 H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

(* No key of an old entry lies at the table's address: its block would be the table's (two live blocks at one
   address are one block), so |text| = 895, and the key's byte T + 5 (NUL-free text) is the table's byte T + 5,
   the second byte of entry 0's eof field (0 or 1), which is 0.  (W_relay_add_sep.v ra_sep_key_off) *)
Lemma ra_sep_key_off_x : forall ly S Hp W mem md T es e k,
ARx ly S Hp W mem md -> arelay_at B RG ly S W mem T es -> In e es -> In k (re_keys e) -> key_addr k <> T.
Proof.
intros ly S Hp W mem md T es e k HAR HR He Hk Heq.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & (tail & _ & Hlen & Htab) & HF & _).
rewrite Forall_forall in HF.
pose proof (HF e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H15).
rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & _).
rewrite Heq in K1, K2.
assert (HL : Z.of_nat (length (key_text k)) + 1 = ATABLE).
{ destruct (Z.eq_dec (Z.of_nat (length (key_text k)) + 1) ATABLE) as [E|E]; [exact E|exfalso].
  assert (Hne : (T, Z.of_nat (length (key_text k)) + 1) <> (T, ATABLE)) by (intros Hq; apply E; congruence).
  pose proof (ra_sep_disj_x ly S Hp W mem md _ _ _ _ HAR K1 HinT Hne) as D.
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

(* the bytes an old entry's predicate reads are off the new slot (W_relay_add_sep.v ra_efp_off_slot) *)
Lemma ra_efp_off_slot_x : forall ly S Hp W mem md T es,
ARx ly S Hp W mem md -> arelay_at B RG ly S W mem T es -> (length es < 16)%nat ->
forall e r a, In e es -> In r (aentry_fp e) -> fst r <= a < snd r ->
~ (T + AENT * Z.of_nat (length es) <= a < T + AENT * Z.of_nat (length es) + AENT).
Proof.
intros ly S Hp W mem md T es HAR HR Hn e r a He Hr Ha Hs.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & (tail & _ & _ & Htab) & HF & _).
pose proof (proj1 (Forall_forall _ _) HF e He) as HE.
unfold AENT in Hs.
assert (HsT : T <= a < T + 896) by (clear - Hn Hs; lia).
assert (RT : req_size ATABLE = 896) by reflexivity.
(* a live block other than the table holds no byte of the slot *)
assert (Dt : forall p n0, In (p, n0) (ablocks B ly S) -> (p, n0) <> (T, ATABLE) -> 0 < n0 -> p <= a < p + n0 -> False).
{ intros p n0 Hin Hne Hpos Hpa. pose proof (ra_sep_req_pos n0 Hpos) as Rn.
  destruct (ra_sep_disj_x ly S Hp W mem md _ _ _ _ HAR Hin HinT Hne) as [D|D]; clear - D Rn RT Hpa HsT; lia. }
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
      pose proof (ra_sep_key_off_x ly S Hp W mem md T es e k HAR HR He0 Hkin) as Hoff.
      pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H15).
      rewrite Forall_forall in H15. destruct (H15 k Hkin) as (K1 & _).
      pose proof (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR K1) as (_ & Hk4096 & Hkceil & _).
      pose proof (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR HinT) as (_ & HT4096 & HTceil & _).
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
      rewrite (ra_sep_concat_len B ly S W mem es1 HF1) in Gh.
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
  + (* a key's block: not the table (ra_sep_key_off_x), so disjoint from it *)
    apply in_map_iff in Hr as (k & <- & Hk).
    pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H15).
    rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & _ & _ & K4).
    unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd length] in Ha.
    destruct (Z.eq_dec (key_addr k) T) as [EkT | EkT].
    * exact (ra_sep_key_off_x ly S Hp W mem md T es e k HAR HR He Hk EkT).
    * apply (Dt (key_addr k) (Z.of_nat (length (key_text k)) + 1) K1);
        [intros Hq; apply EkT; congruence | clear - K4; lia | clear - Ha; lia].
Qed.
End c.
End b.
End a.
