(* reac-pw/fuzz_link, image A: two readings of the same bytes through an A view of lib/A/Prog/link_amem.v are equal
   (acstr_at, anlk_at, amarks_at, aiftab_at at g_nl, astr_arg, au64_at / au32_at), and a view moves to a memory whose
   bytes it reads have the same aview (srm_mbyte_eq, srm_val_mem_move, srm_abytes_move, srm_acstr_move). Generic in
   the segments; shared by reac_served_mark's segment files and the Kit (reac_served_markKit.v). Model:
   reac_link_alias_readPost.v (ar_* lemmas).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- uniqueness of the A views (reac_link_alias_readPost.v ar_*, generic in the segments) ---- *)
Section u.
Variable segs : list Segment.

Lemma srm_lb_inj : forall (n : nat) (p1 p2 : Z),
  (forall k, (k < n)%nat ->
     Z_to_bv 8 (Z.shiftr (p1 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256) =
     Z_to_bv 8 (Z.shiftr (p2 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256)) ->
  p1 mod 2 ^ (8 * Z.of_nat n) = p2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n p1 p2 H. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (8 * Z.of_nat n)) as [Hl|Hl].
  - pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hr.
    set (q := i / 8) in *. set (r := i mod 8) in *. clearbody q r.
    assert (Hq : 0 <= q) by lia.
    assert (Hk : (Z.to_nat q < n)%nat) by lia.
    specialize (H (Z.to_nat q) Hk).
    apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
    change (bv_modulus 8) with 256 in H. rewrite !Z.mod_mod in H by lia.
    rewrite Z2Nat.id in H by exact Hq.
    apply (f_equal (fun z => Z.testbit z r)) in H. cbv beta in H.
    change 256 with (2 ^ 8) in H. rewrite !Z.mod_pow2_bits_low in H by lia.
    rewrite !Z.shiftr_spec in H by lia.
    replace (r + 8 * q) with i in H by lia. exact H.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma srm_vm_unique : forall m a (n : nat) v1 v2, val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2. apply srm_lb_inj. intros k Hk.
  pose proof (eq_trans (eq_sym (H1 k Hk)) (H2 k Hk)) as E.
  exact (f_equal (fun o : option byte => match o with Some b => b | None => Z_to_bv 8 0 end) E).
Qed.

Lemma srm_abytes_unique : forall m a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

Lemma srm_acstr_short : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 ->
  (length s1 < length s2)%nat -> False.
Proof.
  intros m a s1 s2 [(_ & _ & B1) _] [(_ & _ & B2) N2] L.
  assert (E1 : mbyte segs m (a + Z.of_nat (length s1)) = Some (zb 0)).
  { rewrite (B1 (length s1)) by (rewrite length_app; cbn [length]; lia).
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (E2 : mbyte segs m (a + Z.of_nat (length s1)) = nth_error s2 (length s1)).
  { rewrite (B2 (length s1)) by (rewrite length_app; cbn [length]; lia).
    apply nth_error_app1. exact L. }
  apply N2. apply (nth_error_In s2 (length s1)). rewrite <- E2. exact E1.
Qed.

Lemma acstr_at_unique : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 -> s1 = s2.
Proof.
  intros m a s1 s2 H1 H2.
  destruct (Nat.lt_trichotomy (length s1) (length s2)) as [L|[L|L]].
  - exfalso. exact (srm_acstr_short m a s1 s2 H1 H2 L).
  - destruct H1 as [B1 _]. destruct H2 as [B2 _].
    apply (app_inv_tail [zb 0]). apply (srm_abytes_unique m a); [exact B1 | exact B2 |].
    rewrite !length_app, L. reflexivity.
  - exfalso. exact (srm_acstr_short m a s2 s1 H2 H1 L).
Qed.

Lemma anlk_at_unique : forall m g b1 b2, anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (srm_abytes_unique m g); [exact B1 | exact B2 | lia].
Qed.

Lemma amarks_at_unique : forall m p g1 g2, amarks_at segs m p g1 -> amarks_at segs m p g2 -> g1 = g2.
Proof.
  intros m p g1 g2 [[B1 _] L1] [[B2 _] L2]. apply (srm_abytes_unique m p); [exact B1 | exact B2 | lia].
Qed.

Lemma srm_au64_unique : forall m a p1 p2, au64_at segs m a p1 -> au64_at segs m a p2 ->
  p1 mod 2 ^ 64 = p2 mod 2 ^ 64.
Proof.
  intros m a p1 p2 H1 H2. pose proof (srm_vm_unique m a 8 p1 p2 H1 H2) as E.
  change (8 * Z.of_nat 8) with 64 in E. exact E.
Qed.

Lemma srm_au32_small_unique : forall m a x1 x2, au32_at segs m a x1 -> au32_at segs m a x2 ->
  0 <= x1 < 2 ^ 31 -> 0 <= x2 < 2 ^ 31 -> x1 = x2.
Proof.
  intros m a x1 x2 H1 H2 R1 R2. pose proof (srm_vm_unique m a 4 x1 x2 H1 H2) as E.
  change (8 * Z.of_nat 4) with 32 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma srm_acstr_range : forall m p s, acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s [(Ha & Hl & _) _]. rewrite length_app in Hl. cbn [length] in Hl. lia.
Qed.

Lemma aiftab_at_unique : forall m bs tab1 tab2,
  aiftab_at segs m LA_G_NL bs tab1 -> aiftab_at segs m LA_G_NL bs tab2 -> tab1 = tab2.
Proof.
  intros m bs tab1 tab2 (L1 & _ & E1) (L2 & _ & E2).
  assert (L : length tab1 = length tab2) by lia.
  apply nth_error_ext. intros i.
  destruct (nth_error tab1 i) as [[n1 x1]|] eqn:H1; destruct (nth_error tab2 i) as [[n2 x2]|] eqn:H2.
  - destruct (E1 i n1 x1 H1) as (R1 & p1 & P1 & _ & C1 & I1).
    destruct (E2 i n2 x2 H2) as (R2 & p2 & P2 & _ & C2 & I2).
    pose proof (srm_au64_unique _ _ _ _ P1 P2) as Ep.
    pose proof (srm_acstr_range _ _ _ C1). pose proof (srm_acstr_range _ _ _ C2).
    rewrite !Z.mod_small in Ep by lia. subst p2.
    rewrite (acstr_at_unique _ _ _ _ C1 C2).
    rewrite (srm_au32_small_unique _ _ _ _ I1 I2 R1 R2). reflexivity.
  - exfalso. apply nth_error_None in H2. assert (i < length tab1)%nat by (apply nth_error_Some; congruence). lia.
  - exfalso. apply nth_error_None in H1. assert (i < length tab2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

Lemma astr_arg_unique : forall m a o1 o2, astr_arg segs m a o1 -> astr_arg segs m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|] H1 H2; cbn [astr_arg] in H1, H2.
  - f_equal. exact (acstr_at_unique m a s1 s2 (proj2 H1) (proj2 H2)).
  - destruct H1 as [Hn _]. contradiction.
  - destruct H2 as [Hn _]. contradiction.
  - reflexivity.
Qed.

(* a byte whose view is the same in two memories reads the same through mbyte *)
Lemma srm_mbyte_eq : forall H H' (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma srm_val_mem_move : forall H H' (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs H' m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v E Hv k Hk. rewrite (srm_mbyte_eq H H' m m' (a + Z.of_nat k)) by (apply E; lia).
  exact (Hv k Hk).
Qed.

Lemma srm_abytes_move : forall H H' (m m' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> aview segs H' m' x = aview segs H m x) ->
  abytes segs (mrestrict H m) a bs -> abytes segs (mrestrict H' m') a bs.
Proof.
  intros H H' m m' a bs E (Ha & Hl & Hb). split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite (srm_mbyte_eq H H' m m' (a + Z.of_nat i)) by (apply E; lia). exact (Hb i Hi).
Qed.

Lemma srm_acstr_move : forall H H' (m m' : word -> option byte) a s,
  (forall x, a <= x <= a + Z.of_nat (length s) -> aview segs H' m' x = aview segs H m x) ->
  acstr_at segs (mrestrict H m) a s -> acstr_at segs (mrestrict H' m') a s.
Proof.
  intros H H' m m' a s E [Hb Hn]. split; [|exact Hn]. apply (srm_abytes_move H H' m m'); [|exact Hb].
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply E. lia.
Qed.
End u.

