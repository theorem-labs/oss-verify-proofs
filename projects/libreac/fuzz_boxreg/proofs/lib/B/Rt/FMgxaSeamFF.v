(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeamFF.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan-ubsan: module paths changed; 0 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMsnprintfShared, FMsnprintfPf, FMupoison -> lib.A.Rt. *)
(* What the format-generic chain asks of the seam's families: pf_family (FMsnprintfShared.v:92) and pf_family_ro
   (FMgxaSeamDef.v:60) keep under a memory change inside the regions rs outside the shadow, asked at 64-bit addresses
   only, and they keep when the regions shrink (ff_mono, FMsnprintfShared.v:107).
   The stable64 statements are the body of a Theorem Labs lane's ff_stable64 (FMsnprintfSx.v:21,
   a working branch 1ad8495e209) with FF substituted; this file does not Require that file (here lib/A/Rt/FMsnprintfSx.v), and a consumer
   closes `ff_stable64 (pf_family PK)` with `exact`.
   Every read the family makes through rd is
   - a format byte or its NUL, in [f, f + |fmt| + 1), which fmt_at keeps disjoint from rs;
   - a string byte, its NUL or its slack, in [w, str_end w s), which pf_arg_asan keeps disjoint from rs;
   - a shadow byte of one of those, read by range_addressable or shadow_hull_vis.  amem_range puts the byte below
     kHighMemEnd, so its shadow lies in [SHADOW_OFF, kHighMemBeg), where the change premise leaves rd alone.
   All other conjuncts do not mention rd or rs. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf FMsnprintfShared.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import FMgxaSeamDef.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- where the reads lie ---- *)
Lemma amem_range_top : forall p n, amem_range p n -> p + n <= kHighMemEnd - 1.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. Qed.

Lemma below_top_64 : forall a, 0 <= a < kHighMemEnd + 8 -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. unfold kHighMemEnd in Ha. change (2 ^ 64) with 18446744073709551616. lia. Qed.

Lemma shadow_band_64 : forall a, SHADOW_OFF <= a < kHighMemBeg -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. unfold SHADOW_OFF, kHighMemBeg in Ha. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

(* range_addressable rd SHADOW_OFF x _ reads rd (SHADOW_OFF + x / 8) *)
Lemma shadow_of_addr_band : forall x, 0 <= x < kHighMemEnd ->
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
Z.div_mod_to_equations. lia.
Qed.

(* shadow_hull_vis rd x n reads the shadow granules from shadow_addr x to shadow_addr (x + n - 1) *)
Lemma shadow_hull_band : forall x n s, 0 <= x -> x + n <= kHighMemEnd ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF <= s < kHighMemBeg.
Proof.
intros x n s H0 Hx Hs. unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
Z.div_mod_to_equations. lia.
Qed.

Lemma zdisjoint_not_in : forall p L rs a, Forall (zdisjoint (p, L)) rs -> p <= a < p + L -> ~ Exists (in_zr a) rs.
Proof.
intros p L rs a HF Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
rewrite Forall_forall in HF. specialize (HF r Hr). unfold zdisjoint, in_zr in *. simpl in *. lia.
Qed.

Lemma str_end_ge : forall w s, w + Z.of_nat (length s) + 1 <= str_end w s <= w + Z.of_nat (length s) + 8.
Proof. intros w s. unfold str_end. pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8). lia. Qed.

(* ---- one helper per reader-using predicate: agreement on its read set keeps it ---- *)
Lemma range_addressable_stable : forall (rd rd' : reader) B a len,
  (forall x, a <= x < a + len -> rd' (shadow_of_addr B x) = rd (shadow_of_addr B x)) ->
  range_addressable rd B a len -> range_addressable rd' B a len.
Proof. intros rd rd' B a len E H x Hx. rewrite E by exact Hx. exact (H x Hx). Qed.

Lemma shadow_hull_vis_stable : forall (rd rd' : reader) x n,
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros rd rd' x n E H s Hs. rewrite E by exact Hs. exact (H s Hs). Qed.

(* the shadow of an app range is read inside [SHADOW_OFF, kHighMemBeg) *)
Lemma shadow_pair_stable : forall (rd rd' : reader) p n,
  (forall a, SHADOW_OFF <= a < kHighMemBeg -> rd' a = rd a) ->
  0 <= p -> amem_range p n ->
  range_addressable rd SHADOW_OFF p n -> shadow_hull_vis rd p n ->
  range_addressable rd' SHADOW_OFF p n /\ shadow_hull_vis rd' p n.
Proof.
intros rd rd' p n Es Hp Ham Hra Hsh. pose proof (amem_range_top p n Ham) as Ht. split.
- apply (range_addressable_stable rd); [|exact Hra].
  intros x Hx. apply Es. apply shadow_of_addr_band. lia.
- apply (shadow_hull_vis_stable rd); [|exact Hsh].
  intros s Hs. apply Es. exact (shadow_hull_band p n s Hp ltac:(lia) Hs).
Qed.

(* fmt_at reads the format and its NUL, and their shadow *)
Lemma fmt_at_stable : forall (rd rd' : reader) rs f fmt,
  (forall a, f <= a < f + Z.of_nat (length fmt) + 1 -> rd' a = rd a) ->
  (forall a, SHADOW_OFF <= a < kHighMemBeg -> rd' a = rd a) ->
  fmt_at rd rs f fmt -> fmt_at rd' rs f fmt.
Proof.
intros rd rd' rs f fmt Ef Es (Hf & Hb & Hd & Ham & Hra & Hsh).
destruct (shadow_pair_stable rd rd' f (Z.of_nat (length fmt) + 1) Es ltac:(lia) Ham Hra Hsh) as [Hra' Hsh'].
refine (conj Hf (conj _ (conj Hd (conj Ham (conj Hra' Hsh'))))).
intros i Hi. rewrite Ef by lia. exact (Hb i Hi).
Qed.

(* pf_arg_asan reads a string, its NUL and its slack up to str_end, and their shadow *)
Lemma pf_arg_asan_stable : forall (rd rd' : reader) rs w a,
  (forall s x, a = APtr s -> w <= x < str_end w s -> rd' x = rd x) ->
  (forall x, SHADOW_OFF <= x < kHighMemBeg -> rd' x = rd x) ->
  pf_arg_asan rd rs w a -> pf_arg_asan rd' rs w a.
Proof.
intros rd rd' rs w a Ea Es H. destruct a as [v | u | s]; [exact H | exact H |].
destruct H as (Hc & Hw & Hl & Hb & Hsl & Hd & Ham & Hra & Hsh).
pose proof (str_end_ge w s) as Hse.
destruct (shadow_pair_stable rd rd' w (Z.of_nat (length s) + 1) Es ltac:(lia) Ham Hra Hsh) as [Hra' Hsh'].
refine (conj Hc (conj Hw (conj Hl (conj _ (conj _ (conj Hd (conj Ham (conj Hra' Hsh')))))))).
- intros i Hi. rewrite (Ea s) by (reflexivity || lia). exact (Hb i Hi).
- intros x Hx. rewrite (Ea s) by (reflexivity || lia). exact (Hsl x Hx).
Qed.

(* pf_args_asan: each string's read set is disjoint from rs by its own conjunct, so agreement at the 64-bit
   addresses off rs and on the shadow keeps it *)
Lemma pf_args_asan_stable : forall (rd rd' : reader) rs ws args,
  (forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) rs -> rd' a = rd a) ->
  (forall a, SHADOW_OFF <= a < kHighMemBeg -> rd' a = rd a) ->
  pf_args_asan rd rs ws args -> pf_args_asan rd' rs ws args.
Proof.
intros rd rd' rs ws args Eo Es. revert ws. induction args as [|a args IH]; intros ws H; [destruct ws; exact I|].
destruct ws as [|w ws]; [exact (False_ind _ H)|]. destruct H as [Ha Hr]. split; [|exact (IH ws Hr)].
apply (pf_arg_asan_stable rd rd' rs w a); [|exact Es|exact Ha].
intros s x -> Hx. destruct Ha as (_ & Hw & _ & _ & _ & Hd & Ham & _ & _).
pose proof (amem_range_top _ _ Ham) as Ht. pose proof (str_end_ge w s) as Hse.
apply Eo; [apply below_top_64; lia|]. apply (zdisjoint_not_in w (str_end w s - w) rs x Hd). lia.
Qed.

(* ---- the change premise splits into agreement off rs and agreement on the shadow ---- *)
Lemma chg64_off : forall (rd rd' : reader) rs,
  (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a \/ (Exists (in_zr a) rs /\ ~ (SHADOW_OFF <= a < kHighMemBeg))) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) rs -> rd' a = rd a.
Proof. intros rd rd' rs H a Ha Hn. destruct (H a Ha) as [E | [E _]]; [exact E | contradiction]. Qed.

Lemma chg64_shadow : forall (rd rd' : reader) rs,
  (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a \/ (Exists (in_zr a) rs /\ ~ (SHADOW_OFF <= a < kHighMemBeg))) ->
  forall a, SHADOW_OFF <= a < kHighMemBeg -> rd' a = rd a.
Proof.
intros rd rd' rs H a Ha. destruct (H a (shadow_band_64 a Ha)) as [E | [_ N]]; [exact E | contradiction].
Qed.

(* the two conjuncts both families share that read rd *)
Lemma fam_reads_stable64 : forall (rd rd' : reader) rs f fmt ws args,
  (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a \/ (Exists (in_zr a) rs /\ ~ (SHADOW_OFF <= a < kHighMemBeg))) ->
  fmt_at rd rs f fmt -> pf_args_asan rd rs ws args ->
  fmt_at rd' rs f fmt /\ pf_args_asan rd' rs ws args.
Proof.
intros rd rd' rs f fmt ws args Hc Hf Ha. pose proof (chg64_off rd rd' rs Hc) as Eo.
pose proof (chg64_shadow rd rd' rs Hc) as Es. split; [|exact (pf_args_asan_stable rd rd' rs ws args Eo Es Ha)].
apply (fmt_at_stable rd rd' rs f fmt); [|exact Es|exact Hf].
intros a Ha'. destruct Hf as (Hf0 & _ & Hd & Ham & _ & _). pose proof (amem_range_top _ _ Ham) as Ht.
apply Eo; [apply below_top_64; lia|]. apply (zdisjoint_not_in f _ rs a Hd). lia.
Qed.

(* ---- regions each inside one of rs ---- *)
Lemma zdisjoint_mono : forall x rs rs',
  Forall (zdisjoint x) rs ->
  (forall r', In r' rs' -> exists r, In r rs /\ fst r <= fst r' /\ fst r' + snd r' <= fst r + snd r) ->
  Forall (zdisjoint x) rs'.
Proof.
intros x rs rs' H Hs. rewrite Forall_forall in H |- *. intros r' Hr'.
destruct (Hs r' Hr') as (r & Hr & H1 & H2). specialize (H r Hr). unfold zdisjoint in *. lia.
Qed.

Lemma fmt_at_mono : forall (rd : reader) rs rs' f fmt, fmt_at rd rs f fmt ->
  (forall r', In r' rs' -> exists r, In r rs /\ fst r <= fst r' /\ fst r' + snd r' <= fst r + snd r) ->
  fmt_at rd rs' f fmt.
Proof.
intros rd rs rs' f fmt (Hf & Hb & Hd & Hr) Hs. exact (conj Hf (conj Hb (conj (zdisjoint_mono _ rs rs' Hd Hs) Hr))).
Qed.

Lemma pf_arg_asan_mono : forall (rd : reader) rs rs' w a, pf_arg_asan rd rs w a ->
  (forall r', In r' rs' -> exists r, In r rs /\ fst r <= fst r' /\ fst r' + snd r' <= fst r + snd r) ->
  pf_arg_asan rd rs' w a.
Proof.
intros rd rs rs' w a H Hs. destruct a as [v | u | s]; [exact H | exact H |].
destruct H as (Hc & Hw & Hl & Hb & Hsl & Hd & Hr).
exact (conj Hc (conj Hw (conj Hl (conj Hb (conj Hsl (conj (zdisjoint_mono _ rs rs' Hd Hs) Hr)))))).
Qed.

Lemma pf_args_asan_mono : forall (rd : reader) rs rs' ws args, pf_args_asan rd rs ws args ->
  (forall r', In r' rs' -> exists r, In r rs /\ fst r <= fst r' /\ fst r' + snd r' <= fst r + snd r) ->
  pf_args_asan rd rs' ws args.
Proof.
intros rd rs rs' ws args H Hs. revert ws H. induction args as [|a args IH]; intros ws H; [destruct ws; exact I|].
destruct ws as [|w ws]; [exact (False_ind _ H)|]. destruct H as [Ha Hr].
exact (conj (pf_arg_asan_mono rd rs rs' w a Ha Hs) (IH ws Hr)).
Qed.

(* ---- the four statements ---- *)
Lemma pf_family_stable64 : forall PK,
forall (rd rd' : reader) rs f ws T, pf_family PK rd rs f ws T ->
(forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a \/ (Exists (in_zr a) rs /\ ~ (SHADOW_OFF <= a < kHighMemBeg))) ->
pf_family PK rd' rs f ws T.
Proof.
intros PK rd rd' rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq) Hc.
destruct (fam_reads_stable64 rd rd' rs f fmt ws args Hc Hf Ha) as [Hf' Ha'].
exists fmt, ps, args. exact (conj Hf' (conj Hp (conj Hk (conj Ha' (conj Ht Hq))))).
Qed.

Lemma pf_family_mono : forall PK, ff_mono (pf_family PK).
Proof.
intros PK rd rs rs' f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq) Hs.
exists fmt, ps, args.
exact (conj (fmt_at_mono rd rs rs' f fmt Hf Hs)
  (conj Hp (conj Hk (conj (pf_args_asan_mono rd rs rs' ws args Ha Hs) (conj Ht Hq))))).
Qed.

Lemma pf_family_ro_stable64 : forall PK lo hi,
forall (rd rd' : reader) rs f ws T, pf_family_ro PK lo hi rd rs f ws T ->
(forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a \/ (Exists (in_zr a) rs /\ ~ (SHADOW_OFF <= a < kHighMemBeg))) ->
pf_family_ro PK lo hi rd' rs f ws T.
Proof.
intros PK lo hi rd rd' rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl) Hc.
destruct (fam_reads_stable64 rd rd' rs f fmt ws args Hc Hf Ha) as [Hf' Ha'].
exists fmt, ps, args.
exact (conj Hf' (conj Hp (conj Hk (conj Ha' (conj Ht (conj Hq (conj Hlo (conj Hhi Hsl)))))))).
Qed.

Lemma pf_family_ro_mono : forall PK lo hi, ff_mono (pf_family_ro PK lo hi).
Proof.
intros PK lo hi rd rs rs' f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl) Hs.
exists fmt, ps, args.
exact (conj (fmt_at_mono rd rs rs' f fmt Hf Hs)
  (conj Hp (conj Hk (conj (pf_args_asan_mono rd rs rs' ws args Ha Hs)
  (conj Ht (conj Hq (conj Hlo (conj Hhi Hsl)))))))).
Qed.
