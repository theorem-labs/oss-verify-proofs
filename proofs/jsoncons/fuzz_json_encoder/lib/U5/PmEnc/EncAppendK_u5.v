(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From stdpp.bitvector Require Import definitions.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanSoundSums StartupAux HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EAK.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma bytes_of_defined : forall (M : mem) (n : nat) p, 0 <= p -> p + Z.of_nat n <= 2 ^ 63 -> L5.defined M p (Z.of_nat n) ->
  exists bs : list Z, length bs = n /\ L5.bytes_at RSEGS M p bs.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hn D.
  - exists []. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & Hb).
    { intros i Hi. replace (p + 1 + i) with (p + (1 + i)) by lia. apply D. lia. }
    pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:EM; [|contradiction].
    exists (bv_unsigned b :: bs). split; [cbn; lia|]. intros i Hi. destruct i as [|i].
    + cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. rewrite EM. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply Hb. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma u64_of_defined : forall (M : mem) a, L5.defined M a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at RSEGS M a v.
Proof.
  intros M a Hd.
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn RSEGS M (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD 8%nat a Hd) as (bs & Hr & Hl). exists (bytes_le_to_Z bs).
  pose proof (PropExec.bytes_le_to_Z_nonneg bs) as N0. pose proof (AX2S.bytes_le_to_Z_bound bs) as N1. rewrite Hl in N1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in N1.
  split; [lia|]. unfold L5.u64_at. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl | lia].
Qed.
Lemma u64_low_byte : forall (M : mem) a w b, L5.u64_at RSEGS M a w -> L5.u8_at RSEGS M a b -> 0 <= w < 2 ^ 64 -> 0 <= b < 256 -> w mod 256 = b.
Proof.
  intros M a w b H H0 Hw Hb. unfold L5.u64_at, L5.u8_at in *.
  pose proof (rdn_low_bytes RSEGS M (Z_to_bv 64 a) (Z_to_bv 64 w) 1 ltac:(lia) H) as X. rewrite H0 in X.
  assert (X' : Z_to_bv 8 b = Z_to_bv 8 (bv_unsigned (Z_to_bv 64 w))) by (unfold word_to_le_bytes in X; cbn [Z_to_le_bytes] in X; congruence).
  rewrite (L5.unsigned_lit w Hw) in X'. apply (f_equal bv_unsigned) in X'. rewrite !Z_to_bv_unsigned in X'.
  unfold bv_wrap, bv_modulus in X'. change (2 ^ Z.of_N 8) with 256 in X'. rewrite (Z.mod_small b) in X' by lia. symmetry. exact X'.
Qed.
(* [comment removed for export] *)
Lemma short_word0 : forall (M : mem) o (s : list Z), L5.lstr_short RSEGS M o s -> L5.defined M o 24 ->
  exists u, 0 <= u < 2 ^ 56 /\ L5.u64_at RSEGS M o (2 * Z.of_nat (length s) + 256 * u).
Proof.
  intros M o s (Hl & B0 & _) D. destruct (u64_of_defined M o) as (w & Hw & W0); [intros i Hi; apply D; lia|].
  pose proof (u64_low_byte M o w _ W0 B0 Hw ltac:(lia)) as E. exists (w / 256).
  pose proof (Z.div_mod w 256 ltac:(lia)) as DM. rewrite E in DM.
  split; [split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]|]. replace (2 * Z.of_nat (length s) + 256 * (w / 256)) with w by lia. exact W0.
Qed.

Lemma long_intro : forall (M : mem) o cap p sz,
  L5.u64_at RSEGS M o (cap + 1) -> L5.u64_at RSEGS M (o + 8) sz -> L5.u64_at RSEGS M (o + 16) p -> L5.u8_at RSEGS M (p + sz) 0 ->
  L5.defined M p cap -> 0 <= sz < cap -> cap mod 8 = 0 -> 0 <= p -> p + cap <= 2 ^ 63 ->
  exists s', len s' = sz /\ PML.str_at M o (PML.SLong cap p s').
Proof.
  intros M o cap p sz W0 W8 W16 NUL D Hsz Hc8 Hp Hpc.
  destruct (bytes_of_defined M (Z.to_nat sz) p Hp ltac:(lia)) as (bs & Hl & Hb).
  { intros i Hi. apply D. lia. }
  assert (Hlz : Z.of_nat (length bs) = sz) by (rewrite Hl; lia).
  exists bs. split; [exact Hlz|]. cbn [PML.str_at]. split; [|split; [exact Hc8 | rewrite Hlz; lia]].
  unfold L5.lstr_long. rewrite Hlz. split; [|split; [exact W0 | split; [exact W8 | split; [exact W16 | split; [exact Hb | exact NUL]]]]].
  rewrite Z.bit0_odd, Z.odd_add, <- Z.negb_even. assert (E : Z.even cap = true).
  { rewrite (Z.div_mod cap 8) by lia. rewrite Hc8, Z.add_0_r. rewrite Z.even_mul. reflexivity. }
  rewrite E. reflexivity.
Qed.

Lemma short_intro : forall (M : mem) o sz,
  L5.u8_at RSEGS M o (2 * sz) -> L5.u8_at RSEGS M (o + 1 + sz) 0 -> L5.defined M o 24 -> 0 <= sz <= 22 -> 0 <= o -> o + 24 <= 2 ^ 63 ->
  exists s', len s' = sz /\ PML.str_at M o (PML.SShort s').
Proof.
  intros M o sz B0 NUL D Hsz Ho Ho2.
  destruct (bytes_of_defined M (Z.to_nat sz) (o + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & Hb).
  { intros i Hi. replace (o + 1 + i) with (o + (1 + i)) by lia. apply D. lia. }
  assert (Hlz : Z.of_nat (length bs) = sz) by (rewrite Hl; lia).
  exists bs. split; [exact Hlz|]. cbn [PML.str_at]. unfold L5.lstr_short. rewrite Hlz.
  split; [lia|]. split; [exact B0|]. split; [exact Hb | exact NUL].
Qed.

Section Src.
Variable L : heap_layout.
Hypothesis LAY : PmLayout.pm0_layout L.

Lemma other_in_drop : forall LB rep (b : Z * Z), In b LB -> ~ In b (PML.srep_blocks rep) -> List.NoDup (map fst LB) -> rep_live rep LB -> In b (lb_drop rep LB).
Proof.
  intros LB rep [bb bm] Hb Hnb Hnd Hlive.
  destruct rep as [s|cap p s]; cbn [lb_drop]; [exact Hb|]. cbn [rep_live] in Hlive. cbn [PML.srep_blocks In] in Hnb.
  apply L5C.in_lb_remove_neq; [exact Hb|]. intros ->. apply Hnb. left.
  clear - Hnd Hb Hlive. induction LB as [|[c m] LB IH]; [destruct Hb|]. cbn [map fst] in Hnd. inversion Hnd as [|x l Hni Hnd']. subst.
  destruct Hb as [Hb|Hb]; destruct Hlive as [Hl|Hl].
  + congruence.
  + exfalso. apply Hni. injection Hb as -> ->. apply (in_map fst _ _ Hl).
  + exfalso. apply Hni. injection Hl as -> ->. apply (in_map fst _ _ Hb).
  + exact (IH Hb Hnd' Hl).
Qed.

(* [comment removed for export] *)
Lemma src_kept : forall (M : mem) LB sp o rep q k scr,
  src_ok L M LB sp o rep q k -> 1 <= k ->
  hl_sptop L - 2 ^ 23 + scr <= sp -> 0 <= scr -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> hl_ceil L <= sp -> sp <= o -> o + 24 <= hl_sptop L ->
  (forall b, In b LB -> block_range L (fst b) (snd b)) -> List.NoDup (map fst LB) -> rep_live rep LB ->
  forall a, q <= a < q + k -> L5C.kept L (lb_drop rep LB) sp scr [(o, 24)] a.
Proof.
  intros M LB sp o rep q k scr Hsrc Hk Hfl Hscr Htop Hceil Hspo Ho Hbr Hnd Hlive a Ha.
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as LE.
  assert (OUT : a < o \/ o + 24 <= a -> L5.outside [(o, 24)] a).
  { intros H w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  destruct Hsrc as [H0 | [(I1 & I2 & _) | [(S1 & S2 & S3 & _) | (b & Hb & Hnb & B1 & B2 & _)]]].
  - lia.
  - unfold PML.IMG_RO_HI in I2.
    apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LE; lia|].
    apply OUT. left. lia.
  - apply L5C.kept_stack; [exact Hfl | exact Hscr | lia | rewrite LE; lia | lia|]. apply OUT. unfold PML.apart in S3. lia.
  - destruct (Hbr b Hb) as (B3 & B4 & B5 & B6 & B7). destruct b as [bb bm]. cbn [fst snd] in *.
    pose proof (other_in_drop LB rep (bb, bm) Hb Hnb Hnd Hlive) as Hin.
    apply (L5C.kept_block L _ sp scr [(o, 24)] bb bm a Hin); [lia | lia | lia | rewrite LE, ILO, IHI in *; lia|]. apply OUT. left. lia.
Qed.

Lemma src_rdn : forall (M : mem) q (src : list Z), 0 <= q -> q + len src <= 2 ^ 62 -> L5.bytes_at RSEGS M q src ->
  exists bs, rdn (hl_segs L) M (Z_to_bv 64 q) (Z.to_nat (len src)) = Some bs /\ length bs = Z.to_nat (len src).
Proof.
  intros M q src Hq Hn Hb. rewrite (PmLayout.ly_segs L LAY). unfold len in *. rewrite Nat2Z.id.
  exists (map (fun z => Z_to_bv 8 z) src). split; [|apply length_map]. apply (L5C.bytes_at_rdn RSEGS M src q Hq); [lia | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma src_apart : forall (M : mem) LB sp o rep q k scr,
  src_ok L M LB sp o rep q k -> 1 <= k -> 0 <= scr -> hl_ceil L + scr <= sp -> 0x7fff7f800000 <= hl_ceil L -> sp <= o ->
  (forall b, In b LB -> block_range L (fst b) (snd b) /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB)) -> List.NoDup (map fst LB) -> rep_live rep LB ->
  (q + k <= sp - scr \/ sp <= q) /\ (q + k <= o \/ o + 24 <= q) /\
  match rep with PML.SShort _ => True | PML.SLong cap p _ => q + k <= p \/ p + cap <= q end.
Proof.
  intros M LB sp o rep q k scr Hsrc Hk Hscr Hceil Hclo Hspo Hbr Hnd Hlive.
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  assert (OWN : match rep with PML.SShort _ => True | PML.SLong cap p _ => block_range L p cap end).
  { destruct rep as [s|cap p s]; [exact I|]. cbn [rep_live] in Hlive. exact (proj1 (Hbr _ Hlive)). }
  destruct Hsrc as [H0 | [(I1 & I2 & _) | [(S1 & S2 & S3 & _) | (b & Hb & Hnb & B1 & B2 & _)]]].
  - lia.
  - unfold PML.IMG_RO_HI in I2. split; [lia|]. split; [lia|]. destruct rep as [s|cap p s]; [exact I|]. destruct OWN as (B3 & B4 & B5 & B6 & B7). rewrite ILO, IHI in B4. lia.
  - unfold PML.apart in S3. split; [lia|]. split; [lia|]. destruct rep as [s|cap p s]; [exact I|]. destruct OWN as (B3 & B4 & B5 & B6 & B7). lia.
  - destruct (Hbr b Hb) as ((B3 & B4 & B5 & B6 & B7) & _). split; [lia|]. split; [lia|]. destruct rep as [s|cap p s]; [exact I|].
    pose proof (other_in_drop LB _ b Hb Hnb Hnd Hlive) as Hin. cbn [lb_drop] in Hin. cbn [rep_live] in Hlive.
    destruct (Hbr _ Hlive) as (_ & Hap). cbn [fst snd] in Hap. specialize (Hap b Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma src_range : forall (M : mem) LB sp o rep q k,
  src_ok L M LB sp o rep q k -> 1 <= k -> 4096 <= sp -> hl_sptop L <= 2 ^ 47 -> (forall b, In b LB -> block_range L (fst b) (snd b)) -> hl_ceil L <= 2 ^ 47 ->
  4096 <= q /\ q + k <= 2 ^ 47.
Proof.
  intros M LB sp o rep q k Hsrc Hk Hsp Htop Hbr Hc.
  destruct Hsrc as [H0 | [(I1 & I2 & _) | [(S1 & S2 & S3 & _) | (b & Hb & Hnb & B1 & B2 & _)]]].
  - lia.
  - unfold PML.IMG_RO_HI in I2. lia.
  - lia.
  - destruct (Hbr b Hb) as (B3 & B4 & B5 & B6 & B7). lia.
Qed.
End Src.
End EAK.
