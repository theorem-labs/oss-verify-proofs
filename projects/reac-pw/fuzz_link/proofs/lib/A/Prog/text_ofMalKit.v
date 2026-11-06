(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module names changed; 265 of its 299 lines of code are new or changed and 305 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeArmsA.v; 185 of its 284 lines of code are new or changed and 200 lines of the source are left out. *)
(* text_of on image A: three facts of the walk past THE MALLOC CUT (lib/A/Prog/text_ofKit.v to_gi_mal), used by
   lib/A/Prog/text_ofMal.v:
   - to_chain: wrapper_malloc's frame record at the call links to o (s0 = o, +0x44): the journal-level rule's
     `chain_pre` holds for a chain of at most one record (YG0d.v:219-224), given the two words under o and the word at
     o - 16 at most o (text_of_c.v THE MALLOC TRACE);
   - to_admits: every trace of the call starts with the wild prefix [pc_malloc_ra0; 0x87ff0] (text_of_traces), so it
     is admitted with the room LedPre gives (YG01.v:142-155);
   - to_fresh_not_akb: the fresh block is no byte of the call's read classes (akb): stack row above the ceiling,
     blocks of the call (pairwise disjoint), image (AR_client_img_law), frames (sep_block_frame).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 link_aaddr link_amem link_ajkit LinkWalk LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs LinkWalkShadow LinkWalkWseg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE7f AB1v.
From Stdlib Require Import Classical.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma to_admits : forall U pc0 ra sp s0 (ch : list (Z * Z * Z)) (S : astate),
  In [pc0; ra] (u_wild U) -> ra <> pc0 ->
  (length (wild_part U (st_depot S)) + 1 <= u_wmax U)%nat ->
  admits U (unwind_of_chain pc0 ((sp, ra, s0) :: ch)) S.
Proof.
  intros U pc0 ra sp s0 ch S Hw Hne Hroom. unfold admits, inU.
  split; [split|].
  - unfold unwind_of_chain. apply firstn_le_length.
  - right. unfold wild_shape.
    exists [pc0; ra], (firstn 28 (flat_map (fun r => match r with (_, ra0, _) => if ra0 =? pc0 then [] else [ra0] end) ch)).
    split; [exact Hw|]. unfold unwind_of_chain. cbn [flat_map]. rewrite (proj2 (Z.eqb_neq ra pc0) Hne).
    unfold kUnwindMax. cbn [app firstn]. reflexivity.
  - right; right. lia.
Qed.

Lemma to_chain : forall ly (rd : reader) (R : bvmap 5 word) o,
  4096 <= raZ R -> s0Z R = o ->
  (o mod 8 = 0 -> spZ R < o -> o < ly_top ly - 16 ->
     spZ R + 16 <= o /\ exists v8 v16, rdword rd (o - 8) = Some v8 /\ rdword rd (o - 16) = Some v16 /\ 0 <= v8 /\ v16 <= o) ->
  exists ch, chain_pre ly rd R ch.
Proof.
  intros ly rd R o Hra Hs0 HW. unfold chain_pre.
  destruct (frame0_ok ly R) eqn:Ef; [|exists []; split; [exact Hra | reflexivity]].
  destruct (bad_next (spZ R) (ly_top ly) (s0Z R)) eqn:Eb; [exists []; split; [exact Hra | reflexivity]|].
  unfold bad_next in Eb. rewrite Hs0 in Eb.
  apply orb_false_iff in Eb as [Eb Eb3]. apply orb_false_iff in Eb as [Eb1 Eb2].
  apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb2. apply negb_false_iff in Eb3. apply Z.eqb_eq in Eb3.
  destruct (HW Eb3 Eb1 Eb2) as (H16 & v8 & v16 & H8 & H16v & Hv8 & Hv16).
  rewrite Hs0.
  destruct (Z_lt_le_dec v8 4096) as [Hlt | Hge].
  - exists []. split; [exact Hra|]. split; [exact H16|]. cbn [fpchain]. exists v8. split; [exact H8 | lia].
  - exists [(o, v8, v16)]. split; [exact Hra|]. split; [exact H16|]. cbn [fpchain].
    split; [reflexivity|]. split; [exact Eb3|]. split; [exact H8|]. split; [exact H16v|]. split; [exact Hge|].
    unfold bad_next. replace (v16 <=? o) with true by (symmetry; apply Z.leb_le; exact Hv16). reflexivity.
Qed.


(* byte-list facts of one memory (adapted from lib/A/Prog/model_readStr.v) *)
Section u.
Variable segs : list Segment.

Lemma tm_abytes_head : forall (m : word -> option byte) a b l,
  abytes segs m a (b :: l) -> mbyte segs m a = Some b.
Proof.
  intros m a b l (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0.
Qed.

Lemma tm_abytes_tail : forall (m : word -> option byte) a b l,
  abytes segs m a (b :: l) -> abytes segs m (a + 1) l.
Proof.
  intros m a b l (H0 & H1 & H2). cbn [length] in H1.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia.
  exact (H2 (S i) ltac:(cbn [length] in *; lia)).
Qed.

Lemma tm_abytes_unique : forall (m : word -> option byte) a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L.
  apply lw_list_ext; [exact L|]. intros i Hi.
  rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
Qed.

Lemma tm_val_mem_det : forall (m : word -> option byte) a n v1 v2,
  val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  0 <= v1 < 2 ^ (8 * Z.of_nat n) -> 0 <= v2 < 2 ^ (8 * Z.of_nat n) -> v1 = v2.
Proof.
  intros m a n v1 v2 H1 H2 R1 R2.
  assert (E : forall k, (k < n)%nat -> Z_to_bv 8 (le_byte v1 n k) = Z_to_bv 8 (le_byte v2 n k)).
  { intros k Hk. pose proof (H1 k Hk) as A1. pose proof (H2 k Hk) as A2.
    rewrite A1 in A2. injection A2 as A2. apply bv_eq. exact A2. }
  pose (l := map (fun k : nat => Z_to_bv 8 (le_byte v1 n k)) (seq 0 n)).
  assert (Hlen : length l = n) by (unfold l; rewrite length_map, length_seq; reflexivity).
  assert (L1 : bytes_le_to_Z l = v1).
  { apply (lw_bytes_of_vals n); [exact Hlen | exact R1 |].
    intros k Hk. unfold l.
    rewrite (lw_nth_error_map_seq (fun k : nat => Z_to_bv 8 (le_byte v1 n k)) n 0 k Hk).
    rewrite Nat.add_0_l. reflexivity. }
  assert (L2 : bytes_le_to_Z l = v2).
  { apply (lw_bytes_of_vals n); [exact Hlen | exact R2 |].
    intros k Hk. unfold l.
    rewrite (lw_nth_error_map_seq (fun k : nat => Z_to_bv 8 (le_byte v1 n k)) n 0 k Hk).
    rewrite Nat.add_0_l, (E k Hk). reflexivity. }
  rewrite <- L1, <- L2. reflexivity.
Qed.

Lemma tm_au64_det : forall (m : word -> option byte) a p1 p2,
  au64_at segs m a p1 -> au64_at segs m a p2 -> 0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> p1 = p2.
Proof.
  intros m a p1 p2 H1 H2 R1 R2.
  exact (tm_val_mem_det m a 8 p1 p2 H1 H2 ltac:(change (8 * Z.of_nat 8) with 64; lia)
           ltac:(change (8 * Z.of_nat 8) with 64; lia)).
Qed.

Lemma tm_abytes_move : forall (m m' : word -> option byte) a l,
  abytes segs m a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a l.
Proof.
  intros m m' a l (H0 & H1 & H2) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (HK (a + Z.of_nat i) ltac:(lia)). exact (H2 i Hi).
Qed.

Lemma tm_val_mem_move : forall (m m' : word -> option byte) a n v,
  val_mem segs m a n v ->
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m' a n v.
Proof. intros m m' a n v H HK k Hk. rewrite (HK (a + Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.

Lemma tm_anlk_move : forall (m m' : word -> option byte) g bs,
  anlk_at segs m g bs ->
  (forall x, g <= x < g + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, g <= x < g + NK_SIZE -> writable_at segs m' x) ->
  anlk_at segs m' g bs.
Proof.
  intros m m' g bs ((B & _) & L) HK HW. split; [split|exact L].
  - apply (tm_abytes_move m m' g bs B). intros x Hx. apply HK. lia.
  - intros i Hi. apply HW. lia.
Qed.


Lemma tm_apart_of_disj : forall p n q m, 0 < n -> 0 < m ->
  (forall a, p <= a < p + n -> q <= a < q + m -> False) -> p + n <= q \/ q + m <= p.
Proof.
  intros p n q m Hn Hm H.
  destruct (Z.le_gt_cases (p + n) q) as [H1 | H1]; [left; exact H1|].
  destruct (Z.le_gt_cases (q + m) p) as [H2 | H2]; [right; exact H2|].
  exfalso. apply (H (Z.max p q)); lia.
Qed.

Lemma tm_ra_sub : forall (rd : reader) Bs p n q k,
  range_addressable rd Bs p n -> p <= q -> q + k <= p + n -> range_addressable rd Bs q k.
Proof. intros rd Bs p n q k H H1 H2 x Hx. apply H. lia. Qed.

Lemma tm_hull_sub : forall (rd : reader) p n q k,
  shadow_hull_vis rd p n -> p <= q -> 0 < k -> q + k <= p + n -> 0 <= p -> shadow_hull_vis rd q k.
Proof.
  intros rd p n q k H H1 H2 H3 H4 s Hs. apply H. unfold shadow_addr in *.
  pose proof (Z.div_le_mono (SHADOW_OFF + p / 8) (SHADOW_OFF + q / 8) 8 ltac:(lia)
    ltac:(pose proof (Z.div_le_mono p q 8 ltac:(lia) H1); lia)).
  pose proof (Z.div_le_mono (SHADOW_OFF + (q + k - 1) / 8) (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)
    ltac:(pose proof (Z.div_le_mono (q + k - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)); lia)).
  lia.
Qed.

(* a byte range's shadow facts move to a reader that agrees on the low shadow span *)
Lemma tm_ra_move : forall (rd rd' : reader) p n, 0 <= p -> p + n <= 2 ^ 47 ->
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) ->
  range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof.
  intros rd rd' p n H0 H1 HE H x Hx. destruct (H x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
  rewrite HE; [exact Hv|]. unfold shadow_of_addr, SHADOW_OFF.
  split; [pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma tm_hull_move : forall (rd rd' : reader) p n, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 ->
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) ->
  shadow_hull_vis rd p n -> shadow_hull_vis rd' p n.
Proof.
  intros rd rd' p n H0 Hn H1 HE H s Hs. rewrite HE; [exact (H s Hs)|]. unfold shadow_addr, SHADOW_OFF in *.
  pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (p + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (2147450880 + p / 8) 8 ltac:(lia)).
  pose proof (Z.div_le_mono (2147450880 + p / 8) (2147450880 + p / 8) 8 ltac:(lia) ltac:(lia)).
  assert (2147450880 + p / 8 - 7 <= (2147450880 + p / 8) / 8 * 8)
    by (pose proof (Z.mod_pos_bound (2147450880 + p / 8) 8 ltac:(lia)); pose proof (Z_div_mod_eq_full (2147450880 + p / 8) 8); lia).
  pose proof (Z.mul_div_le (2147450880 + (p + n - 1) / 8) 8 ltac:(lia)).
  split; lia.
Qed.

(* writability moves to a later memory: an image byte off the rom by its segment, any other byte by its view *)
Lemma tm_wr_move : forall (HS : segs = AB1v.tfibsegs) H1 (m1 : word -> option byte) H2 (m2 : word -> option byte) a,
  0 <= a < 2 ^ 64 -> writable_at segs (mrestrict H1 m1) a -> ~ in_rom segs a ->
  (~ in_img segs a -> aview segs H2 m2 a = aview segs H1 m1 a) ->
  writable_at segs (mrestrict H2 m2) a.
Proof.
  intros HS H1 m1 H2 m2 a Ha Hw Hr Hv. subst segs.
  destruct (classic (in_img AB1v.tfibsegs a)) as [Hi | Hn].
  - apply wseg_writable_tfib. destruct Hi as (sg & Hin & Hrr). exists sg. split; [exact Hin|]. split; [|exact Hrr].
    destruct (seg_writable sg) eqn:Ew; [reflexivity|]. exfalso. apply Hr. exists sg. split; [exact Hin|].
    split; [exact Ew | exact Hrr].
  - apply apresent_writable. apply (apresent_transfer AB1v.tfibsegs H1 H2 m1 m2 a Ha Hn (Hv Hn)).
    exact (AE7f.apresent_of_writable H1 m1 a Ha Hn Hw).
Qed.

Lemma tm_aview_rng : forall H (m : word -> option byte) x b, aview segs H m x = Some b -> 0 <= b < 256.
Proof.
  intros H m x b E. unfold aview in E. destruct (mbyte segs (mrestrict H m) x) as [y|]; cbn in E; [|discriminate].
  injection E as <-. pose proof (bv_unsigned_in_range 8 y) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

Lemma tm_rdword_rng : forall H (m : word -> option byte) a v, rdword (aview segs H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H m a v E. unfold rdword in E.
  destruct (aview segs H m a) as [b0|] eqn:E0; [|discriminate].
  destruct (aview segs H m (a + 1)) as [b1|] eqn:E1; [|discriminate].
  destruct (aview segs H m (a + 2)) as [b2|] eqn:E2; [|discriminate].
  destruct (aview segs H m (a + 3)) as [b3|] eqn:E3; [|discriminate].
  destruct (aview segs H m (a + 4)) as [b4|] eqn:E4; [|discriminate].
  destruct (aview segs H m (a + 5)) as [b5|] eqn:E5; [|discriminate].
  destruct (aview segs H m (a + 6)) as [b6|] eqn:E6; [|discriminate].
  destruct (aview segs H m (a + 7)) as [b7|] eqn:E7; [|discriminate].
  injection E as <-.
  apply tm_aview_rng in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.
End u.

Section a. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Lemma to_fresh_not_akb : forall lyc Sc ly2 S2 (W2 : world segs) mem2 md2 res n slo shi a,
  AR segs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] ->
  frames S2 = frames Sc -> (forall c q, frame_addr ly2 c q = frame_addr lyc c q) ->
  alloc_ceiling <= ly_stk_lo lyc ->
  akb segs B lyc Sc slo shi a -> ~ (res <= a < res + req_size n).
Proof.
  intros lyc Sc ly2 S2 W2 mem2 md2 res n slo shi a HAR Hbl Hfr Hfa Hst Hk Ha.
  assert (HinP : In (res, n) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HAR HinP) as (_ & _ & Hbc & _ & _ & _ & Hn).
  assert (Hrq : 1 <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]).
  assert (HnotSc : ~ In (res, n) (ablocks B lyc Sc)).
  { intros Hin. apply in_split in Hin as (l1 & l2 & El).
    pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR
      ltac:(rewrite Hbl, El, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
  destruct Hk as [(Hs & _) | [(b & m & Hb & Hm) | [(Hi & _) | (cid & pos & Hc & Hz)]]].
  - lia.
  - assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hb).
    assert (Hne : (b, m) <> (res, n)) by (intros E; rewrite E in Hb; exact (HnotSc Hb)).
    pose proof (sep_blocks segs B LAWS ly2 S2 W2 mem2 md2 b m res n HAR Hb2 HinP Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - apply (proj2 (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR
      (or_introl (ex_intro _ res (ex_intro _ n (conj HinP Ha)))))). exact Hi.
  - assert (Hc2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hc).
    pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 res n cid pos HAR HinP Hc2) as Hd.
    rewrite Hfa in Hd. unfold zdisjoint in Hd. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hd, Hz. lia.
Qed.

(* the same of the shadow classes (LinkWalkShadow.v sclass): a write-set byte of the call is no byte of the block *)
Lemma to_fresh_not_sclass : forall lyc Sc ly2 S2 (W2 : world segs) mem2 md2 res n a,
  AR segs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] ->
  frames S2 = frames Sc -> (forall c q, frame_addr ly2 c q = frame_addr lyc c q) ->
  alloc_ceiling <= ly_stk_lo lyc ->
  sclass segs B lyc Sc a -> ~ (res <= a < res + req_size n).
Proof.
  intros lyc Sc ly2 S2 W2 mem2 md2 res n a HAR Hbl Hfr Hfa Hst Hk Ha.
  assert (HinP : In (res, n) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HAR HinP) as (_ & _ & Hbc & _ & _ & _ & Hn).
  assert (Hrq : 1 <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]).
  assert (HnotSc : ~ In (res, n) (ablocks B lyc Sc)).
  { intros Hin. apply in_split in Hin as (l1 & l2 & El).
    pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR
      ltac:(rewrite Hbl, El, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
  destruct Hk as [Hs | [(b & m & Hb & Hm) | [Hi | (cid & pos & Hc & Hz)]]].
  - lia.
  - assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hb).
    assert (Hne : (b, m) <> (res, n)) by (intros E; rewrite E in Hb; exact (HnotSc Hb)).
    pose proof (sep_blocks segs B LAWS ly2 S2 W2 mem2 md2 b m res n HAR Hb2 HinP Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - apply (proj2 (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR
      (or_introl (ex_intro _ res (ex_intro _ n (conj HinP Ha)))))). exact Hi.
  - assert (Hc2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hc).
    pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 res n cid pos HAR HinP Hc2) as Hd.
    rewrite Hfa in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* a byte of a shadow class, off the image, the window and the exception set, keeps its view across a kept clause *)
Lemma tm_akept_sclass : forall lyc Sc (W : world segs) m (W2 : world segs) m2 slo shi (E : Z -> Prop) a,
  akept segs B lyc Sc W m W2 m2 slo shi E -> alloc_ceiling <= ly_stk_lo lyc ->
  sclass segs B lyc Sc a -> ~ in_img segs a -> ~ (slo <= a < shi) -> ~ E a -> a < 2 ^ 64 ->
  aview segs (w_H W2) m2 a = aview segs (w_H W) m a.
Proof.
  intros lyc Sc W m W2 m2 slo shi E a (K1 & K2 & K3 & K4 & _) Hst Hs Hi Hw HE H64.
  destruct Hs as [Hs | [(b & mm & Hb & Hm) | [Hs | (c & q & Hc & Hz)]]].
  - apply K1; [lia | exact Hw | exact HE].
  - replace a with (b + (a - b)) by lia. apply (K2 b mm (a - b) Hb); [lia|]. replace (b + (a - b)) with a by lia. exact HE.
  - exfalso. exact (Hi Hs).
  - apply (K4 c q a Hc); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HE].
Qed.
End a.
