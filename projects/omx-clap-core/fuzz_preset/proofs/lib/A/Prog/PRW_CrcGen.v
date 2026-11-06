(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, program part, the GENERIC djb2 byte loop of check_reject_clean_starved
   (fuzz_pick, fuzz.h:65-72, inlined three times on each image). Lane BCrs of h-rw-pre-5; the A walk (h-w6u-rep) and
   the B walk (BCrs) cite it, each three times. Image-free: no listing, no address, no allocator instance.
   rule 24: proves no function (kind: segment lemma - the loop induction and the per-byte facts of a loop that each
   image's run lemmas step).
   WHAT IS GENERIC AND WHAT IS NOT. The six loop copies (A 0x821f8 / 0x822b0 / 0x82364, B 0x822bc / 0x8238c / 0x8245c)
   do not share a register allocation (A's third copy counts down the caller's size register and walks the caller's
   data register; B's three keep a separate counter and two pointer registers), and B's copies carry three UBSan
   checks per byte that A's do not. So ONE iteration of a copy is a run over that image's listing (the engine's
   paj_run_x), proved by the image's walk; this file gives what is the same for all six:
   - djb_head: the state at a loop head, over the loop pc and the register NUMBERS: the hash register rh holds djb2 of
     the bytes read so far, the counter register rc the bytes left (every copy counts down), each register of rps the
     address of the next byte (a copy may keep one, two or the caller's data register), the bytes themselves (garr8)
     and the ONE memory premise of the per-byte ASan check, range_addressable over [data, data + size) (the src_rd
     gives both); J is the walk's own frame (journal, saved registers, the registers the loop does not touch);
   - djb_loop: the induction (SRr_loopZ, YA0n.v:95) from one-iteration steps to the exit pc;
   - the per-iteration facts a step needs: the hash update (PRW_CrsModel.v crs_djb2_snoc, frozen), the counter, the
     shadow byte of the next byte (saddr_ok, so the check's fast path or its in-granule arm), the UBSan facts
     (no pointer wrap, non-null) and the byte's value.
   Numerals: 5381, 33, 32 (WORD: fuzz_pick's seed and multiplier, `slli r, r, 5`); 2 ^ 64 (WORD: the machine word);
   2 ^ 62 (DERIVED: the data bound); 8 (LENGTH: the shadow granule). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure: the bytes read so far ---- *)
Lemma djb_firstn_S : forall (x : list Z) i, (i < length x)%nat -> firstn (S i) x = firstn i x ++ [nth i x 0].
Proof.
  induction x as [|c r IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

(* the hash after one more byte: h' = 32 h + h + c (mod 2 ^ 64), the copies' `slli; add; add` *)
Lemma djb_hash_step : forall (x : list Z) i, (i < length x)%nat ->
  ck_djb2 5381 (firstn (S i) x) =
  (32 * ck_djb2 5381 (firstn i x) + ck_djb2 5381 (firstn i x) + nth i x 0) mod 2 ^ 64.
Proof.
  intros x i Hi. rewrite (djb_firstn_S x i Hi), crs_djb2_snoc. f_equal. lia.
Qed.

Lemma djb_hash_range : forall l, 0 <= ck_djb2 5381 l < 2 ^ 64.
Proof. intros l. apply crs_djb2_range. lia. Qed.

Lemma djb_firstn_all : forall (x : list Z), ck_djb2 5381 (firstn (length x) x) = ck_djb2 5381 x.
Proof. intros x. rewrite firstn_all. reflexivity. Qed.

(* the counter after one more byte *)
Lemma djb_count_step : forall (x : list Z) i,
  Z.of_nat (length x) - Z.of_nat (S i) = Z.of_nat (length x) - Z.of_nat i - 1.
Proof. intros x i. lia. Qed.

(* the per-byte ASan check: the shadow byte of the next byte exists and admits it (0, or a partial granule whose
   valid prefix covers the byte), from the ONE range premise *)
Lemma djb_byte_shadow : forall (rd : Z -> option Z) (Bs d n i : Z),
  range_addressable rd Bs d n -> 0 <= i < n ->
  exists s, rd (shadow_of_addr Bs (d + i)) = Some s /\ saddr_ok (d + i) s.
Proof. intros rd Bs d n i H Hi. apply H. lia. Qed.

Lemma djb_byte_addressable : forall (rd : Z -> option Z) (Bs d n i : Z),
  range_addressable rd Bs d n -> 0 <= i < n -> range_addressable rd Bs (d + i) 1.
Proof. intros rd Bs d n i H Hi. apply (range_addressable_sub rd Bs d n); [exact H | lia | lia]. Qed.

(* image B's UBSan checks on the next byte's address (pointer overflow, null), not taken *)
Lemma djb_ptr_ok : forall d n i, 0 < d -> d + n < 2 ^ 62 -> 0 <= i <= n ->
  0 < d + i /\ d <= d + i /\ d + i < 2 ^ 64.
Proof. intros d n i H1 H2 H3. lia. Qed.

(* the byte read: garr8 gives its value, an unsigned byte *)
Lemma djb_byte : forall (segs : list Segment) (m : word -> option byte) (d : Z) (x : list Z) i,
  garr8 segs m d x -> (i < length x)%nat ->
  mbyte segs m (d + Z.of_nat i) = Some (Z_to_bv 8 (nth i x 0)) /\ 0 <= nth i x 0 < 256.
Proof.
  intros segs m d x i H Hi. split; [exact (garr8_mbyte segs m d x i H Hi) | exact (proj2 (H i Hi))].
Qed.

(* ---- the loop head and the induction ---- *)
Section l. Context {fx : YK11.FPState}.
Variable segs : list Segment.

Definition djb_head (pc : Z) (rh rc : bv 5) (rps : list (bv 5)) (data : Z) (x : list Z)
  (J : world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) (i : nat)
  : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
    c = cfg_at segs pc regs mem md /\ (i <= length x)%nat /\
    getr regs rh = w64 (ck_djb2 5381 (firstn i x)) /\
    getr regs rc = w64 (Z.of_nat (length x) - Z.of_nat i) /\
    Forall (fun r => getr regs r = w64 (data + Z.of_nat i)) rps /\
    garr8 segs (mrestrict (w_H W) mem) data x /\
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF data (Z.of_nat (length x)) /\
    J W regs mem md.

(* from one-iteration steps (each image's run lemma of the copy: from the head at i < size to the head at i + 1, at
   the loop pc while bytes remain and at the exit pc pcx after the last) to the exit with every byte read *)
Theorem djb_loop : forall (pc pcx : Z) (rh rc : bv 5) (rps : list (bv 5)) (data : Z) (x : list Z)
  (J : world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  (forall i W c, (i < length x)%nat -> djb_head pc rh rc rps data x J i W c ->
     SRr segs W c (djb_head (if (S i <? length x)%nat then pc else pcx) rh rc rps data x J (S i))) ->
  forall W c, (0 < length x)%nat -> djb_head pc rh rc rps data x J 0 W c ->
  SRr segs W c (djb_head pcx rh rc rps data x J (length x)).
Proof.
  intros pc pcx rh rc rps data x J Hstep W c Hn H0.
  refine (SRr_loopZ segs nat (fun i => Z.of_nat (length x) - Z.of_nat i)
    (fun i W' c' => (i < length x)%nat /\ djb_head pc rh rc rps data x J i W' c')
    (djb_head pcx rh rc rps data x J (length x)) _ 0%nat W c (conj Hn H0)).
  intros i W1 c1 [Hi H1].
  eapply SRr_mono; [exact (Hstep i W1 c1 Hi H1)|].
  intros W2 c2 _. destruct (Nat.ltb_spec (S i) (length x)) as [Hlt|Hge]; intros H2.
  - right. exists (S i). split; [lia|]. split; [exact Hlt | exact H2].
  - left. replace (length x) with (S i) by lia. exact H2.
Qed.

(* the head's hash register at the exit is djb2 of the whole text, and fuzz_pick's value its remainder *)
Lemma djb_exit_hash : forall (pcx : Z) rh rc rps data (x : list Z) J W c,
  djb_head pcx rh rc rps data x J (length x) W c ->
  exists regs mem md, c = cfg_at segs pcx regs mem md /\
    getr regs rh = w64 (ck_djb2 5381 x) /\ getr regs rc = w64 0 /\
    Forall (fun r => getr regs r = w64 (data + Z.of_nat (length x))) rps /\ J W regs mem md.
Proof.
  intros pcx rh rc rps data x J W c (regs & mem & md & Hc & _ & Hh & Hcnt & Hp & _ & _ & HJ).
  exists regs, mem, md. rewrite djb_firstn_all in Hh. rewrite Z.sub_diag in Hcnt.
  split; [exact Hc|]. split; [exact Hh|]. split; [exact Hcnt|]. split; [exact Hp | exact HJ].
Qed.
End l.
