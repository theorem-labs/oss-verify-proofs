(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the post-construction kit for musl fread's walk inside libreac/fuzz_pcap
   (libreac v1.9.0, ASan build): rread_kept and rfread_post's conjuncts (lib/A/Stdio/PFreadM.v)
   from memory-agreement facts, and the stream predicate asource_at (lib/A/Stdio/PSource.v)
   rebuilt after the window copy.

   rule 24: no function proved. These are composition and transport lemmas, not a function walk.

   WHAT EACH PART GIVES THE WALK.
   1. frd_kept_of_agree: the six clauses of rread_kept (PFreadM.v:344-360). Its first premise is
      rread_kept's first clause, word for word. The block clause (:349-350) and the frame clause
      (:354-357) speak of bytes BELOW alloc_ceiling: AR_blocks_law puts every live block in
      [4096, alloc_ceiling) (YG0d.v:423-426), frames_bounds every frame (YCbq.v:447-450), and
      shadow_addr_bounds every frame shadow in [kLowMemEnd, kHighShadowEnd) (YCbq.v:462). The
      first premise is silent there, so the lemma takes a second agreement premise for
      [0, alloc_ceiling) outside E. frd_kept_of_agree_all takes the one agreement fact a
      memory-copy call gives (every byte of [0, 2^64) outside the window), when the window lies
      at or above alloc_ceiling.
      A path that ends after __toread or mread has no agreement for all of [0, alloc_ceiling):
      rtoread_post and rmread_post keep low memory only clause by clause (live blocks, frames,
      image, band). Those paths compose rread_kept facts instead: frd_kept_trans composes two of
      them, and frd_kept_of_acall turns YCbq's acall_kept (what acall_kept_of_journal,
      YCbq.v:971-977, gives from __toread's journal) into rread_kept.
   2. frd_band_of_low / frd_band_of_agree: the shadow band clause of rfread_post (:418-419). The
      band [kLowMemEnd, kHighShadowEnd) lies below alloc_ceiling, so it is off the callee
      window; it is off the FILE block because a live block lies in application memory
      (in_app, YG0f.v:277), and off the destination because of amem_range (YG0d.v:317).
   3. asource_at_w is asource_at (PSource.v:258-281) with its window named, and asource_at is
      convertibly `exists Wl, asource_at_w ... Wl` (asource_at_w_of, asource_at_of_w).
      asource_at_w_build / asource_at_build are the introduction forms.
   4. asource_at_drain_w / asource_at_drain: the stream after the walk copies j bytes out of the
      window and advances rpos (+8) by j, with the orientation word (+136) rewritten.
   5. frd_garr8_*: the delivered-bytes conjunct of rfread_post for a read of 0 bytes. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YM05 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20.
(* YE00 only for YE00.val_mem_frame, as PSourceFrame.v: imported, its U32M1 would shadow PSource's. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceFrame PFreadM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The two list facts of the window copy.                                  *)
(* ---------------------------------------------------------------------- *)
(* The window holds C[p .. cpos); after j bytes leave it, it holds C[p+j .. cpos). *)
Lemma frd_window_drain : forall (C : list Z) p cpos j,
  0 <= p -> 0 <= j -> p + j <= cpos ->
  skipn (Z.to_nat j) (firstn (Z.to_nat (cpos - p)) (skipn (Z.to_nat p) C)) =
  firstn (Z.to_nat (cpos - (p + j))) (skipn (Z.to_nat (p + j)) C).
Proof.
intros C p cpos j Hp Hj Hc.
rewrite skipn_firstn_comm, skipn_skipn.
replace (Z.to_nat (cpos - p) - Z.to_nat j)%nat with (Z.to_nat (cpos - (p + j))) by lia.
replace (Z.to_nat j + Z.to_nat p)%nat with (Z.to_nat (p + j)) by lia.
reflexivity.
Qed.

Lemma frd_window_drain_length : forall (Wl : list Z) j, 0 <= j <= Z.of_nat (length Wl) ->
  Z.of_nat (length (skipn (Z.to_nat j) Wl)) = Z.of_nat (length Wl) - j.
Proof. intros Wl j Hj. rewrite length_skipn. lia. Qed.

Section post. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* ---------------------------------------------------------------------- *)
(* 1. rread_kept.                                                          *)
(* ---------------------------------------------------------------------- *)
Lemma frd_kept_of_agree : forall RSTK lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 sp
    (E : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RSTK <= a < sp) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, in_img segs a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) ->
  (forall a, sp - RSTK <= a < sp -> apresent (w_H W2) mem2 a) ->
  rread_kept segs B RSTK lyc Sc W memc W2 mem2 sp E.
Proof.
intros RSTK lyc Sc W memc mdc W2 mem2 sp E HAR Hhi Hlo Himg Hpres Hwin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact Hhi|].
split.
{ intros b m i Hb Hi HnE.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hceil & _).
  apply Hlo; [lia | exact HnE]. }
split; [intros a Ha _ _; exact (Himg a Ha)|].
split.
{ intros cid pos a Hin Hr HnE.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  apply Hlo; [destruct Hr as [Hr|Hr]; zlia | exact HnE]. }
split; [intros a _ _ Hp; exact (Hpres a Hp)|].
exact Hwin.
Qed.

(* The same from the one agreement fact a memory-copy call gives (aintrin_realizes, YG0d.v:318-336):
   every byte of [0, 2^64) outside the window, for a window at or above alloc_ceiling. *)
Lemma frd_kept_of_agree_all : forall RSTK lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 sp
    (E : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= sp - RSTK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - RSTK <= a < sp) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, in_img segs a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) ->
  (forall a, sp - RSTK <= a < sp -> apresent (w_H W2) mem2 a) ->
  rread_kept segs B RSTK lyc Sc W memc W2 mem2 sp E.
Proof.
intros RSTK lyc Sc W memc mdc W2 mem2 sp E HAR Hc Hall Himg Hpres Hwin.
pose proof alloc_ceiling_lt as Hlt. pose proof alloc_ceiling_value as Hcv.
apply (frd_kept_of_agree RSTK lyc Sc W memc mdc W2 mem2 sp E HAR); [| | exact Himg | exact Hpres | exact Hwin].
- intros a Ha Hs HnE. apply Hall; [lia | exact Hs | exact HnE].
- intros a Ha HnE. apply Hall; [lia | lia | exact HnE].
Qed.

(* Two calls in sequence, both inside the window [sp - R, sp) and both writing inside E, keep what
   one call with that window and E keeps. The state at the first call must have its window
   present: the caller's journal gives it (YCbq.v:365, with rread_call's window inclusion). *)
Lemma frd_kept_trans : forall R1 R2 R lyc Sc (W : world segs) memc (W1 : world segs) mem1
    (W2 : world segs) mem2 sp1 sp2 sp (E1 E2 E : Z -> Prop),
  rread_kept segs B R1 lyc Sc W memc W1 mem1 sp1 E1 ->
  rread_kept segs B R2 lyc Sc W1 mem1 W2 mem2 sp2 E2 ->
  sp - R <= sp1 - R1 -> sp1 <= sp -> sp - R <= sp2 - R2 -> sp2 <= sp ->
  alloc_ceiling <= sp - R -> sp <= 2 ^ 64 ->
  (forall a, sp - R <= a < sp -> apresent (w_H W) memc a) ->
  (forall a, E1 a -> E a) -> (forall a, E2 a -> E a) ->
  rread_kept segs B R lyc Sc W memc W2 mem2 sp E.
Proof.
intros R1 R2 R lyc Sc W memc W1 mem1 W2 mem2 sp1 sp2 sp E1 E2 E
  (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6)
  Hw1lo Hw1hi Hw2lo Hw2hi Hceil Hsp Hpres0 HE1 HE2.
split.
{ intros a Ha Hs HnE.
  rewrite (B1 a Ha ltac:(lia) (fun h => HnE (HE2 a h))).
  exact (A1 a Ha ltac:(lia) (fun h => HnE (HE1 a h))). }
split.
{ intros b m i Hb Hi HnE.
  rewrite (B2 b m i Hb Hi (fun h => HnE (HE2 _ h))).
  exact (A2 b m i Hb Hi (fun h => HnE (HE1 _ h))). }
split.
{ intros a Ha Hs He. rewrite (B3 a Ha Hs He). exact (A3 a Ha Hs He). }
split.
{ intros cid pos a Hin Hr HnE.
  rewrite (B4 cid pos a Hin Hr (fun h => HnE (HE2 _ h))).
  exact (A4 cid pos a Hin Hr (fun h => HnE (HE1 _ h))). }
split.
{ intros a Ha Hs Hp. apply B5; [exact Ha | lia |]. apply A5; [exact Ha | lia | exact Hp]. }
assert (P1 : forall a, sp - R <= a < sp -> apresent (w_H W1) mem1 a).
{ intros a Ha.
  destruct (Z_lt_le_dec a (sp1 - R1)) as [H|H];
    [| destruct (Z_lt_le_dec a sp1) as [H'|H']; [apply A6; lia |]];
    (apply A5; [lia | lia | apply Hpres0; lia]). }
intros a Ha.
destruct (Z_lt_le_dec a (sp2 - R2)) as [H|H];
  [| destruct (Z_lt_le_dec a sp2) as [H'|H']; [apply B6; lia |]];
  (apply B5; [lia | lia | apply P1; lia]).
Qed.

(* YCbq's acall_kept (YCbq.v:822-833) over the window [sp - RSTK, sp) is rread_kept: its first
   clause holds without the ~ E premise. *)
Lemma frd_kept_of_acall : forall RSTK lyc Sc (W : world segs) memc (W2 : world segs) mem2 sp
    (E : Z -> Prop),
  acall_kept segs B lyc Sc W memc W2 mem2 (sp - RSTK) sp E ->
  rread_kept segs B RSTK lyc Sc W memc W2 mem2 sp E.
Proof.
intros RSTK lyc Sc W memc W2 mem2 sp E (A1 & A2 & A3 & A4 & A5 & A6).
split; [intros a Ha Hs _; exact (A1 a Ha Hs)|].
exact (conj A2 (conj A3 (conj A4 (conj A5 A6)))).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The shadow band clause of rfread_post.                               *)
(* ---------------------------------------------------------------------- *)
Lemma frd_band_of_low : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 f d l,
  AR segs B lyc Sc W memc mdc ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) ->
  amem_range d l ->
  (forall a, 0 <= a < alloc_ceiling -> ~ rread_wrset f d l a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  forall s, kLowMemEnd <= s < kHighShadowEnd ->
    aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s.
Proof.
intros lyc Sc W memc mdc W2 mem2 f d l HAR Hf Hd Hlo s Hs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hf) as (_ & _ & _ & Happ & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Happ.
apply Hlo; [zlia|].
unfold rread_wrset, SRC_FILE_BLOCK. intros [Hx|Hx]; zlia.
Qed.

(* The same from the memory-copy form of the agreement fact, for a window at or above
   alloc_ceiling. *)
Lemma frd_band_of_agree : forall RSTK lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 sp
    f d l,
  AR segs B lyc Sc W memc mdc ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) ->
  amem_range d l ->
  alloc_ceiling <= sp - RSTK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - RSTK <= a < sp) -> ~ rread_wrset f d l a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  forall s, kLowMemEnd <= s < kHighShadowEnd ->
    aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s.
Proof.
intros RSTK lyc Sc W memc mdc W2 mem2 sp f d l HAR Hf Hd Hc Hall.
pose proof alloc_ceiling_lt as Hlt.
apply (frd_band_of_low lyc Sc W memc mdc W2 mem2 f d l HAR Hf Hd).
intros a Ha Hn. apply Hall; [lia | lia | exact Hn].
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. asource_at with its window named, and its introduction form.         *)
(* ---------------------------------------------------------------------- *)
Definition asource_at_w (m : word -> option byte) (f b : Z) (C : list Z) (p : Z) (Wl : list Z) : Prop :=
  exists (cpos fl md : Z),
    let n := Z.of_nat (length C) in
    0 <= p /\ p <= cpos /\ cpos <= n /\
    n < 2 ^ 63 /\
    b + n <= 2 ^ 64 /\
    cpos = p + Z.of_nat (length Wl) /\
    Wl = firstn (Z.to_nat (cpos - p)) (skipn (Z.to_nat p) C) /\
    bytes_ok C /\ garr8 segs m b C /\
    source_static segs K m f b n /\ source_window segs m f Wl /\
    source_flags segs m f fl /\ (fl = 24 -> p = n) /\ source_mode segs m f md /\
    val_mem segs m (f + SRC_COOKIE_OFF) 8 cpos /\
    asrc_stdio_env segs K m /\
    val_mem segs m (as_ofl_head K) 8 f /\ f <> 0.

Lemma asource_at_w_of : forall m f b C p,
  asource_at segs K m f b C p -> exists Wl, asource_at_w m f b C p Wl.
Proof. intros m f b C p H. exact H. Qed.

Lemma asource_at_of_w : forall m f b C p Wl,
  asource_at_w m f b C p Wl -> asource_at segs K m f b C p.
Proof. intros m f b C p Wl H. exists Wl. exact H. Qed.

Lemma asource_at_w_build : forall (m : word -> option byte) f b (C : list Z) p cpos fl md (Wl : list Z),
  0 <= p -> p <= cpos -> cpos <= Z.of_nat (length C) -> Z.of_nat (length C) < 2 ^ 63 ->
  b + Z.of_nat (length C) <= 2 ^ 64 ->
  cpos = p + Z.of_nat (length Wl) ->
  Wl = firstn (Z.to_nat (cpos - p)) (skipn (Z.to_nat p) C) ->
  bytes_ok C -> garr8 segs m b C ->
  source_static segs K m f b (Z.of_nat (length C)) ->
  source_window segs m f Wl -> source_flags segs m f fl -> (fl = 24 -> p = Z.of_nat (length C)) ->
  source_mode segs m f md ->
  val_mem segs m (f + SRC_COOKIE_OFF) 8 cpos ->
  asrc_stdio_env segs K m ->
  val_mem segs m (as_ofl_head K) 8 f -> f <> 0 ->
  asource_at_w m f b C p Wl.
Proof.
intros m f b C p cpos fl md Wl H0 H1 H2 H3 Hbw H4 H5 Hok HC Hs Hw Hfl Hfl24 Hmd Hcp Henv Hhd Hf0.
exists cpos, fl, md. cbv zeta.
exact (conj H0 (conj H1 (conj H2 (conj H3 (conj Hbw (conj H4 (conj H5 (conj Hok (conj HC (conj Hs
  (conj Hw (conj Hfl (conj Hfl24 (conj Hmd (conj Hcp (conj Henv (conj Hhd Hf0))))))))))))))))).
Qed.

Lemma asource_at_build : forall (m : word -> option byte) f b (C : list Z) p cpos fl md (Wl : list Z),
  0 <= p -> p <= cpos -> cpos <= Z.of_nat (length C) -> Z.of_nat (length C) < 2 ^ 63 ->
  b + Z.of_nat (length C) <= 2 ^ 64 ->
  cpos = p + Z.of_nat (length Wl) ->
  Wl = firstn (Z.to_nat (cpos - p)) (skipn (Z.to_nat p) C) ->
  bytes_ok C -> garr8 segs m b C ->
  source_static segs K m f b (Z.of_nat (length C)) ->
  source_window segs m f Wl -> source_flags segs m f fl -> (fl = 24 -> p = Z.of_nat (length C)) ->
  source_mode segs m f md ->
  val_mem segs m (f + SRC_COOKIE_OFF) 8 cpos ->
  asrc_stdio_env segs K m ->
  val_mem segs m (as_ofl_head K) 8 f -> f <> 0 ->
  asource_at segs K m f b C p.
Proof.
intros m f b C p cpos fl md Wl H0 H1 H2 H3 Hbw H4 H5 Hok HC Hs Hw Hfl Hfl24 Hmd Hcp Henv Hhd Hf0.
apply (asource_at_of_w m f b C p Wl).
exact (asource_at_w_build m f b C p cpos fl md Wl H0 H1 H2 H3 Hbw H4 H5 Hok HC Hs Hw Hfl Hfl24 Hmd Hcp
  Henv Hhd Hf0).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The window copy: j bytes leave the window and rpos (+8) moves by j.  *)
(* ---------------------------------------------------------------------- *)
(* source_static reads neither rpos / rend [+8, +16) nor the orientation word [+136, +140). *)
Lemma source_static_frame_rw : forall (m m' : word -> option byte) f b n,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 8 <= a < f + 16) -> ~ (f + 136 <= a < f + 140) ->
     mbyte segs m' a = mbyte segs m a) ->
  source_static segs K m f b n -> source_static segs K m' f b n.
Proof.
intros m m' f b n Hfr Hs.
assert (HFB : SRC_FILE_BLOCK = 1304) by reflexivity.
assert (HCO : SRC_COOKIE_OFF = 232) by reflexivity.
assert (HV : forall off (k : nat) v, 0 <= off -> off + Z.of_nat k <= SRC_FILE_BLOCK ->
               (off + Z.of_nat k <= 8 \/ 16 <= off) -> (off + Z.of_nat k <= 136 \/ 140 <= off) ->
               val_mem segs m (f + off) k v -> val_mem segs m' (f + off) k v).
{ intros off k v H0 H1 H2 H3 Hv. apply (YE00.val_mem_frame segs m m'); [|exact Hv].
  intros x Hx. apply Hfr; lia. }
unfold source_static in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end;
  first [ assumption | (apply HV; [lia | lia | lia | lia | assumption]) ].
Qed.

Lemma asource_at_drain_w : forall (m m' : word -> option byte) f b (C : list Z) p (Wl : list Z) j md',
  asource_at_w m f b C p Wl ->
  0 <= j <= Z.of_nat (length Wl) ->
  source_window segs m' f (skipn (Z.to_nat j) Wl) ->
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 8 <= a < f + 16) -> ~ (f + 136 <= a < f + 140) ->
     mbyte segs m' a = mbyte segs m a) ->
  source_mode segs m' f md' ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs m' a = mbyte segs m a) ->
  asource_at_w m' f b C (p + j) (skipn (Z.to_nat j) Wl).
Proof.
intros m m' f b C p Wl j md'
  (cpos & fl & md & H0 & H1 & H2 & H3 & Hbw & H4 & H5 & Hok & HC & Hs & Hw & Hfl & Hfl24 & Hmd & Hcp & Henv & Hhd & Hf0)
  Hj Hw' Hf Hmd' Hb He Hh.
assert (HFB : SRC_FILE_BLOCK = 1304) by reflexivity.
assert (HCO : SRC_COOKIE_OFF = 232) by reflexivity.
pose proof (frd_window_drain_length Wl j Hj) as HL.
apply (asource_at_w_build m' f b C (p + j) cpos fl md' (skipn (Z.to_nat j) Wl)).
- lia.
- lia.
- exact H2.
- exact H3.
- exact Hbw.
- rewrite HL. lia.
- rewrite H5. apply frd_window_drain; lia.
- exact Hok.
- exact (garr8_frame segs m m' b C HC Hb).
- exact (source_static_frame_rw m m' f b _ Hf Hs).
- exact Hw'.
- apply (source_flags_frame segs m m'); [intros x Hx; apply Hf; lia | exact Hfl].
- intros E24. specialize (Hfl24 E24). lia.
- exact Hmd'.
- apply (YE00.val_mem_frame segs m m'); [intros x Hx; apply Hf; lia | exact Hcp].
- exact (asrc_stdio_env_frame segs K m m' He Henv).
- apply (YE00.val_mem_frame segs m m'); [intros x Hx; apply Hh; lia | exact Hhd].
- exact Hf0.
Qed.

Lemma asource_at_drain : forall (m m' : word -> option byte) f b (C : list Z) p (Wl : list Z) j md',
  asource_at_w m f b C p Wl ->
  0 <= j <= Z.of_nat (length Wl) ->
  source_window segs m' f (skipn (Z.to_nat j) Wl) ->
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 8 <= a < f + 16) -> ~ (f + 136 <= a < f + 140) ->
     mbyte segs m' a = mbyte segs m a) ->
  source_mode segs m' f md' ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs m' a = mbyte segs m a) ->
  asource_at segs K m' f b C (p + j).
Proof.
intros m m' f b C p Wl j md' HA Hj Hw' Hf Hmd' Hb He Hh.
exact (asource_at_of_w m' f b C (p + j) _ (asource_at_drain_w m m' f b C p Wl j md' HA Hj Hw' Hf Hmd' Hb He Hh)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. The delivered bytes of a read of 0 bytes.                            *)
(* ---------------------------------------------------------------------- *)
Lemma frd_garr8_nil : forall (m : word -> option byte) d, garr8 segs m d [].
Proof. intros m d. apply garr8_nil. Qed.

Lemma frd_garr8_firstn_nil : forall (m : word -> option byte) d (l : list Z), garr8 segs m d (firstn 0 l).
Proof. intros m d l. cbn [firstn]. apply garr8_nil. Qed.

(* rfread_post's conjunct at nm = 0, as it reads before rread_k is unfolded. *)
Lemma frd_garr8_rread_k0 : forall (m : word -> option byte) d n p (l : list Z),
  garr8 segs m d (firstn (Z.to_nat (rread_k 0 n p)) l).
Proof.
intros m d n p l. replace (Z.to_nat (rread_k 0 n p)) with 0%nat by (unfold rread_k; lia).
apply frd_garr8_firstn_nil.
Qed.

End post.
