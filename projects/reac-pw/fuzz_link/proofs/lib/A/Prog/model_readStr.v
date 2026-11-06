(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module names changed; 265 of its 299 lines of code are new or changed and 305 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeArmsA.v; 51 of its 219 lines of code are new or changed and 131 lines of the source are left out. *)
(* model_read on image A: byte-level facts its walk uses (C strings, words and the fake kernel's tables read from a
   memory, and moved to a memory with the same bytes), and the model-side arithmetic of a refusal. The text is that of
   lib/A/Prog/model_writeArmsA.v, names prefixed mr_.
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c LinkWalkWseg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma mr_rc_einval : - E_INVAL = -22. Proof. reflexivity. Qed.
Lemma mr_rc_etoolong : - E_NAMETOOLONG = -36. Proof. reflexivity. Qed.
Lemma mr_rc_enodev : - E_NODEV = -19. Proof. reflexivity. Qed.
Lemma mr_norm_neg : forall rc, rc <= 0 -> norm_rc rc = rc.
Proof. intros rc H. unfold norm_rc. replace (0 <? rc) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

(* the two model_wf consequences the Post needs when nothing moved *)
Lemma mr_next_kstate : forall mbs kbs, model_wf mbs -> Z.of_nat (k_next (md_kstate mbs kbs)) = md_next mbs.
Proof. intros mbs kbs (_ & (Hlo & _) & _). cbn [md_kstate k_next]. lia. Qed.

Lemma mr_n_req_length : forall mbs, model_wf mbs -> Z.of_nat (length (md_reqs mbs)) = md_n_req mbs.
Proof.
  intros mbs ((Hlo & _) & _). unfold md_reqs.
  rewrite length_map, length_seq. lia.
Qed.

(* ==========================================================================
   2. The A views: determined by the memory, and moved with its bytes
   ========================================================================== *)

Section u.
Variable segs : list Segment.

Lemma mr_abytes_head : forall (m : word -> option byte) a b l,
  abytes segs m a (b :: l) -> mbyte segs m a = Some b.
Proof.
  intros m a b l (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0.
Qed.

Lemma mr_abytes_tail : forall (m : word -> option byte) a b l,
  abytes segs m a (b :: l) -> abytes segs m (a + 1) l.
Proof.
  intros m a b l (H0 & H1 & H2). cbn [length] in H1.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia.
  exact (H2 (S i) ltac:(cbn [length] in *; lia)).
Qed.

Lemma mr_abytes_unique : forall (m : word -> option byte) a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L.
  apply lw_list_ext; [exact L|]. intros i Hi.
  rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
Qed.

Lemma mr_acstr_unique : forall (m : word -> option byte) p s1 s2,
  acstr_at segs m p s1 -> acstr_at segs m p s2 -> s1 = s2.
Proof.
  intros m p s1. revert p.
  induction s1 as [|x s1 IH]; intros p s2 (B1 & N1) (B2 & N2); destruct s2 as [|y s2].
  - reflexivity.
  - exfalso. cbn [app] in B1, B2.
    pose proof (mr_abytes_head m p _ _ B1) as E1. pose proof (mr_abytes_head m p _ _ B2) as E2.
    rewrite E1 in E2. injection E2 as E2. apply N2. left. symmetry. exact E2.
  - exfalso. cbn [app] in B1, B2.
    pose proof (mr_abytes_head m p _ _ B1) as E1. pose proof (mr_abytes_head m p _ _ B2) as E2.
    rewrite E1 in E2. injection E2 as E2. apply N1. left. exact E2.
  - cbn [app] in B1, B2.
    pose proof (mr_abytes_head m p _ _ B1) as E1. pose proof (mr_abytes_head m p _ _ B2) as E2.
    rewrite E1 in E2. injection E2 as E2. subst y.
    f_equal. apply (IH (p + 1) s2).
    + split; [exact (mr_abytes_tail m p x _ B1) | intros Hin; apply N1; right; exact Hin].
    + split; [exact (mr_abytes_tail m p x _ B2) | intros Hin; apply N2; right; exact Hin].
Qed.

Lemma mr_astr_arg_unique : forall (m : word -> option byte) p o1 o2,
  astr_arg segs m p o1 -> astr_arg segs m p o2 -> o1 = o2.
Proof.
  intros m p [s1|] [s2|] H1 H2; cbn in H1, H2.
  - f_equal. exact (mr_acstr_unique m p s1 s2 (proj2 H1) (proj2 H2)).
  - exfalso. exact (proj1 H1 H2).
  - exfalso. exact (proj1 H2 H1).
  - reflexivity.
Qed.

Lemma mr_anlk_unique : forall (m : word -> option byte) g b1 b2,
  anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 ((B1 & _) & L1) ((B2 & _) & L2).
  exact (mr_abytes_unique m g b1 b2 B1 B2 ltac:(lia)).
Qed.

Lemma mr_amodel_unique : forall (m : word -> option byte) p b1 b2,
  amodel_at segs m p b1 -> amodel_at segs m p b2 -> b1 = b2.
Proof.
  intros m p b1 b2 ((B1 & _) & L1) ((B2 & _) & L2).
  exact (mr_abytes_unique m p b1 b2 B1 B2 ltac:(lia)).
Qed.

(* a value a memory shows over n bytes is the only one in [0, 2 ^ (8 n)) it shows *)
Lemma mr_val_mem_det : forall (m : word -> option byte) a n v1 v2,
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

Lemma mr_au64_det : forall (m : word -> option byte) a p1 p2,
  au64_at segs m a p1 -> au64_at segs m a p2 -> 0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> p1 = p2.
Proof.
  intros m a p1 p2 H1 H2 R1 R2.
  exact (mr_val_mem_det m a 8 p1 p2 H1 H2 ltac:(change (8 * Z.of_nat 8) with 64; lia)
           ltac:(change (8 * Z.of_nat 8) with 64; lia)).
Qed.

Lemma mr_au32_det : forall (m : word -> option byte) a v1 v2,
  au32_at segs m a v1 -> au32_at segs m a v2 -> 0 <= v1 < 2 ^ 31 -> 0 <= v2 < 2 ^ 31 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 R1 R2.
  exact (mr_val_mem_det m a 4 v1 v2 H1 H2 ltac:(change (8 * Z.of_nat 4) with 32; lia)
           ltac:(change (8 * Z.of_nat 4) with 32; lia)).
Qed.

Lemma mr_acstr_range : forall (m : word -> option byte) p s,
  acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s ((H0 & H1 & _) & _). rewrite length_app in H1. cbn [length] in H1. lia.
Qed.

Lemma mr_aiftab_unique : forall (m : word -> option byte) g bs t1 t2,
  aiftab_at segs m g bs t1 -> aiftab_at segs m g bs t2 -> t1 = t2.
Proof.
  intros m g bs t1 t2 (L1 & _ & H1) (L2 & _ & H2).
  apply nth_error_ext. intros i.
  destruct (nth_error t1 i) as [[n1 x1]|] eqn:E1; destruct (nth_error t2 i) as [[n2 x2]|] eqn:E2.
  - destruct (H1 i n1 x1 E1) as (R1 & p1 & U1 & _ & C1 & I1).
    destruct (H2 i n2 x2 E2) as (R2 & p2 & U2 & _ & C2 & I2).
    pose proof (mr_acstr_range m p1 n1 C1) as Hr1. pose proof (mr_acstr_range m p2 n2 C2) as Hr2.
    assert (p1 = p2) as -> by (apply (mr_au64_det m _ p1 p2 U1 U2); lia).
    rewrite (mr_acstr_unique m p2 n1 n2 C1 C2), (mr_au32_det m _ x1 x2 I1 I2 R1 R2). reflexivity.
  - exfalso. assert (Hi1 : (i < length t1)%nat) by (apply nth_error_Some; rewrite E1; discriminate).
    apply nth_error_None in E2. lia.
  - exfalso. assert (Hi2 : (i < length t2)%nat) by (apply nth_error_Some; rewrite E2; discriminate).
    apply nth_error_None in E1. lia.
  - reflexivity.
Qed.

Lemma mr_abytes_move : forall (m m' : word -> option byte) a l,
  abytes segs m a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a l.
Proof.
  intros m m' a l (H0 & H1 & H2) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (HK (a + Z.of_nat i) ltac:(lia)). exact (H2 i Hi).
Qed.

Lemma mr_acstr_move : forall (m m' : word -> option byte) p s,
  acstr_at segs m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> mbyte segs m' x = mbyte segs m x) ->
  acstr_at segs m' p s.
Proof.
  intros m m' p s (B & N) HK. split; [|exact N].
  apply (mr_abytes_move m m' p (s ++ [zb 0]) B).
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply HK. lia.
Qed.

Lemma mr_val_mem_move : forall (m m' : word -> option byte) a n v,
  val_mem segs m a n v ->
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m' a n v.
Proof. intros m m' a n v H HK k Hk. rewrite (HK (a + Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.

Lemma mr_anlk_move : forall (m m' : word -> option byte) g bs,
  anlk_at segs m g bs ->
  (forall x, g <= x < g + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, g <= x < g + NK_SIZE -> writable_at segs m' x) ->
  anlk_at segs m' g bs.
Proof.
  intros m m' g bs ((B & _) & L) HK HW. split; [split|exact L].
  - apply (mr_abytes_move m m' g bs B). intros x Hx. apply HK. lia.
  - intros i Hi. apply HW. lia.
Qed.

Lemma mr_aiftab_move : forall (m m' : word -> option byte) g bs tab,
  aiftab_at segs m g bs tab ->
  (forall x, g <= x < g + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at segs m (g + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at segs m p n2 ->
     forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte segs m' x = mbyte segs m x) ->
  aiftab_at segs m' g bs tab.
Proof.
  intros m m' g bs tab (L1 & L2 & H) HK HS.
  split; [exact L1|]. split; [exact L2|].
  intros i n2 ix Hi. destruct (H i n2 ix Hi) as (Rx & p & U & Hp0 & C & I).
  assert (Hilt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [exact Rx|]. exists p.
  split.
  { apply (mr_val_mem_move m m' _ 8 p U). intros x Hx.
    apply HK. change (Z.of_nat 8) with 8 in Hx.
    unfold NK_IF_NAME, NK_SIZE in *. lia. }
  split; [exact Hp0|]. split.
  { apply (mr_acstr_move m m' p n2 C). intros x Hx. exact (HS i n2 ix p Hi U C x Hx). }
  apply (mr_val_mem_move m m' _ 4 ix I). intros x Hx.
  apply HK. change (Z.of_nat 4) with 4 in Hx.
  unfold NK_IF_INDEX, NK_SIZE in *. lia.
Qed.

End u.
