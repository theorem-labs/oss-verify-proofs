(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 1087 of its 1155 lines of code are new or changed and 336 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): THE TRANSPORT
   LEMMAS of the walk's cut invariants (lib/A/Prog/LLVMFuzzerTestOneInputDefs.v). Every phase carries the
   interface's memory clauses across a step that changes only some bytes: a run of the walk's own instructions
   (the symbolic runner's `frame_of`: the memory is unchanged outside the written ranges), or a callee (its
   `akept`: the views are unchanged outside its window and its write set). This file states, once for all lanes:

   1. per predicate of link_amem.v / AMemFileSink.v / YG0v.v, over a general exception set X: the predicate at
      the old memory gives it at the new one when the new memory reads as the old one off X (`kagree X m m'`,
      over `mbyte`) and the predicate's bytes miss X; predicates that name writability (`awrange`, `au8arr`,
      `abuf`, the views over them) also take `wcarry m m' a n` (each of their bytes writable before is writable
      after: a run gives it from `mem_grows` by `wcarry_of_grows`, a callee step from AR's block law or from the
      writable segments);
   2. per predicate of the interface (lf_data, lf_blocks, lf_ifp, lf_gnames_at, lf_gnames_w, lf_odd_at,
      lf_texts_at, lf_la_at, lf_cur, lf_slots, lf_saved, lf_header, lf_fshadow and the memory clauses of
      lf_jbk): the same, with the footprint the predicate reads written out as a set (`lf_*_fp`), so a caller
      shows `forall a, lf_*_fp a -> ~ X a` from the separations the interface already carries;
   3. placement: the data and the blocks' shadow lie below the allocator's ceiling (lf_data_fp_low,
      lf_blocks_fp_low, in_roP_low);
   4. across a callee called with sp = s1 (`lf_call cx K ..`: window [lf_sp1 cx - K, lf_sp1 cx), write set E,
      akept and ashadow_kept from the cut's state): the exception set is `lf_X` (what akept and ashadow_kept do
      not keep), with one lemma per class of kept byte (lfx_above, lfx_side, lfx_blk, lfx_img / lfx_imgfp,
      lfx_sh, lfx_data), one per interface predicate (lf_saved/slots/cur/header/fshadow/blocks/jbk/data_callee,
      lf_aro_callee, lf_la_nul_callee; each takes only the footprint its predicate reads, `forall a, fp a -> ~ E a`)
      and the whole cut at once (lf_cut_callee). The image facts they take (lf_img_ok, lf_relro_img) are decided
      on link's image by lf_img_facts.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD1y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Per predicate, over an exception set X
   ========================================================================== *)

Section kg.
Variable segs : list Segment.

(* the new memory reads as the old one off X *)
Definition kagree (X : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, ~ X a -> mbyte segs m' a = mbyte segs m a.

Lemma kagree_refl : forall X m, kagree X m m.
Proof. intros X m a _. reflexivity. Qed.

Lemma kagree_mono : forall (X Y : Z -> Prop) m m', (forall a, X a -> Y a) -> kagree X m m' -> kagree Y m m'.
Proof. intros X Y m m' HXY HK a Ha. apply HK. intros HX. exact (Ha (HXY a HX)). Qed.

Lemma kagree_trans : forall (X Y : Z -> Prop) m1 m2 m3,
  kagree X m1 m2 -> kagree Y m2 m3 -> kagree (fun a => X a \/ Y a) m1 m3.
Proof.
  intros X Y m1 m2 m3 H1 H2 a Ha. rewrite (H2 a), (H1 a); [reflexivity| |]; intros H; apply Ha; [left | right]; exact H.
Qed.

(* from the views a runner or a callee contract states *)
Lemma kagree_of_aview : forall (X : Z -> Prop) H H' (mem mem' : word -> option byte),
  (forall a, ~ X a -> aview segs H' mem' a = aview segs H mem a) ->
  kagree X (mrestrict H mem) (mrestrict H' mem').
Proof.
  intros X H H' mem mem' HV a Ha. specialize (HV a Ha). unfold aview in HV.
  destruct (mbyte segs (mrestrict H' mem') a) as [b'|];
  destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn in HV; try discriminate; [|reflexivity].
  injection HV as HV. f_equal. apply bv_eq. exact HV.
Qed.

Lemma aview_of_kagree : forall (X : Z -> Prop) H H' (mem mem' : word -> option byte) a,
  kagree X (mrestrict H mem) (mrestrict H' mem') -> ~ X a -> aview segs H' mem' a = aview segs H mem a.
Proof. intros X H H' mem mem' a HK Ha. unfold aview. rewrite (HK a Ha). reflexivity. Qed.

(* from the raw equality a run's frame_of gives *)
Lemma kagree_of_raw : forall (X : Z -> Prop) (m m' : word -> option byte),
  (forall x : word, ~ X (bv_unsigned x) -> m' x = m x) ->
  kagree (fun a => X (bv_unsigned (Z_to_bv 64 a))) m m'.
Proof.
  intros X m m' HR a Ha. unfold mbyte. rewrite (HR (Z_to_bv 64 a) Ha). reflexivity.
Qed.

(* writability only needs presence kept *)
Lemma writable_at_grows : forall m m' a, mem_grows m m' -> writable_at segs m a -> writable_at segs m' a.
Proof.
  intros m m' a Hg Hw. unfold writable_at, wview in *.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [discriminate|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|exact Hw].
  exfalso. apply (Hg (Z_to_bv 64 a)); [rewrite E; discriminate | exact E'].
Qed.

Lemma abytes_keep : forall X m m' a bs, kagree X m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ X (a + i)) ->
  abytes segs m a bs -> abytes segs m' a bs.
Proof.
  intros X m m' a bs HK HX (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (HK (a + Z.of_nat i)) by (apply HX; lia). exact (H2 i Hi).
Qed.

(* writability is carried per byte (a run gives it from mem_grows by writable_at_grows; a callee step from AR's
   block law or the writable segments) *)
Definition wcarry (m m' : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> writable_at segs m (a + i) -> writable_at segs m' (a + i).

Lemma wcarry_of_grows : forall m m' a n, mem_grows m m' -> wcarry m m' a n.
Proof. intros m m' a n Hg i _. exact (writable_at_grows m m' (a + i) Hg). Qed.

Lemma awrange_keep : forall m m' a n, wcarry m m' a n -> awrange segs m a n -> awrange segs m' a n.
Proof. intros m m' a n HW H i Hi. exact (HW i Hi (H i Hi)). Qed.

Lemma au8arr_keep : forall X m m' a bs, kagree X m m' -> wcarry m m' a (Z.of_nat (length bs)) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ X (a + i)) ->
  au8arr segs m a bs -> au8arr segs m' a bs.
Proof.
  intros X m m' a bs HK HW HX (Hb & Hw). split; [exact (abytes_keep X m m' a bs HK HX Hb) | exact (awrange_keep m m' a _ HW Hw)].
Qed.

Lemma abuf_keep : forall X m m' a n, kagree X m m' -> wcarry m m' a n ->
  (forall i, 0 <= i < n -> ~ X (a + i)) -> abuf segs m a n -> abuf segs m' a n.
Proof.
  intros X m m' a n HK HW HX (junk & Hl & Hj). exists junk. split; [exact Hl|].
  apply (au8arr_keep X m m' a junk HK); [rewrite Hl; exact HW | intros i Hi; apply HX; lia | exact Hj].
Qed.

Lemma val_mem_keep : forall X m m' a n v, kagree X m m' ->
  (forall k, 0 <= k < Z.of_nat n -> ~ X (a + k)) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros X m m' a n v HK HX H k Hk. rewrite (HK (a + Z.of_nat k)) by (apply HX; lia). exact (H k Hk). Qed.

Lemma au16_keep : forall X m m' a v, kagree X m m' -> (forall k, 0 <= k < 2 -> ~ X (a + k)) ->
  au16_at segs m a v -> au16_at segs m' a v.
Proof. intros X m m' a v HK HX. apply (val_mem_keep X m m' a 2 v HK). exact HX. Qed.
Lemma au32_keep : forall X m m' a v, kagree X m m' -> (forall k, 0 <= k < 4 -> ~ X (a + k)) ->
  au32_at segs m a v -> au32_at segs m' a v.
Proof. intros X m m' a v HK HX. apply (val_mem_keep X m m' a 4 v HK). exact HX. Qed.
Lemma au64_keep : forall X m m' a v, kagree X m m' -> (forall k, 0 <= k < 8 -> ~ X (a + k)) ->
  au64_at segs m a v -> au64_at segs m' a v.
Proof. intros X m m' a v HK HX. apply (val_mem_keep X m m' a 8 v HK). exact HX. Qed.

Lemma acstr_keep : forall X m m' a s, kagree X m m' ->
  (forall i, 0 <= i <= Z.of_nat (length s) -> ~ X (a + i)) ->
  acstr_at segs m a s -> acstr_at segs m' a s.
Proof.
  intros X m m' a s HK HX (Hb & Hn). split; [|exact Hn].
  apply (abytes_keep X m m' a _ HK); [|exact Hb]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HX. lia.
Qed.

Lemma anlk_keep : forall X m m' g bs, kagree X m m' -> wcarry m m' g NK_SIZE ->
  (forall i, 0 <= i < NK_SIZE -> ~ X (g + i)) -> anlk_at segs m g bs -> anlk_at segs m' g bs.
Proof.
  intros X m m' g bs HK HW HX (H & Hl). split; [|exact Hl].
  apply (au8arr_keep X m m' g bs HK); [rewrite Hl; exact HW | intros i Hi; apply HX; lia | exact H].
Qed.
Lemma amodel_keep : forall X m m' p bs, kagree X m m' -> wcarry m m' p MD_SIZE ->
  (forall i, 0 <= i < MD_SIZE -> ~ X (p + i)) -> amodel_at segs m p bs -> amodel_at segs m' p bs.
Proof.
  intros X m m' p bs HK HW HX (H & Hl). split; [|exact Hl].
  apply (au8arr_keep X m m' p bs HK); [rewrite Hl; exact HW | intros i Hi; apply HX; lia | exact H].
Qed.
Lemma amarks_keep : forall X m m' p bs, kagree X m m' -> wcarry m m' p MK_SIZE ->
  (forall i, 0 <= i < MK_SIZE -> ~ X (p + i)) -> amarks_at segs m p bs -> amarks_at segs m' p bs.
Proof.
  intros X m m' p bs HK HW HX (H & Hl). split; [|exact Hl].
  apply (au8arr_keep X m m' p bs HK); [rewrite Hl; exact HW | intros i Hi; apply HX; lia | exact H].
Qed.

(* the shadow facts read the shadow bytes only *)
Lemma ra_keep : forall X m m' Bs p n, kagree X m m' ->
  (forall x, p <= x < p + n -> ~ X (shadow_of_addr Bs x)) ->
  range_addressable (ard segs m) Bs p n -> range_addressable (ard segs m') Bs p n.
Proof.
  intros X m m' Bs p n HK HX H x Hx. specialize (H x Hx). unfold ard in *.
  rewrite (HK _ (HX x Hx)). exact H.
Qed.

Lemma shvis_keep : forall X m m' x n, kagree X m m' ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ X s) ->
  shadow_hull_vis (ard segs m) x n -> shadow_hull_vis (ard segs m') x n.
Proof.
  intros X m m' x n HK HX H s Hs. specialize (H s Hs). unfold ard in *. rewrite (HK _ (HX s Hs)). exact H.
Qed.

(* a word read through the reader *)
Lemma rdword_keep : forall X m m' a v, kagree X m m' -> (forall i, 0 <= i < 8 -> ~ X (a + i)) ->
  rdword (ard segs m) a = Some v -> rdword (ard segs m') a = Some v.
Proof.
  intros X m m' a v HK HX H. unfold rdword, ard in *.
  rewrite (HK a) by (replace a with (a + 0) by lia; apply HX; lia).
  rewrite (HK (a + 1)), (HK (a + 2)), (HK (a + 3)), (HK (a + 4)), (HK (a + 5)), (HK (a + 6)), (HK (a + 7))
    by (apply HX; lia).
  exact H.
Qed.

(* the read-only image *)
Lemma arodata_keep : forall X m m' rlo rhi B, kagree X m m' ->
  (forall a, in_roP segs rlo rhi a -> ~ X a) ->
  arodata_okP segs rlo rhi B (ard segs m) -> arodata_okP segs rlo rhi B (ard segs m').
Proof.
  intros X m m' rlo rhi B HK HX H a Hro Hno Her. specialize (H a Hro Hno Her). unfold ard in *.
  rewrite (HK a (HX a Hro)). exact H.
Qed.

(* the same, where X may hold read-only bytes the runtime owns (a callee's kept clause spares only the owned
   statics and errno) *)
Lemma arodata_keep_ns : forall X m m' rlo rhi B, kagree X m m' ->
  (forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> ~ X a) ->
  arodata_okP segs rlo rhi B (ard segs m) -> arodata_okP segs rlo rhi B (ard segs m').
Proof.
  intros X m m' rlo rhi B HK HX H a Hro Hno Her. specialize (H a Hro Hno Her). unfold ard in *.
  rewrite (HK a (HX a Hro Hno Her)). exact H.
Qed.

(* the interface table: g_nl's two arrays and each entry's name string *)
Lemma aiftab_keep : forall X m m' g bs tab, kagree X m m' ->
  (forall i, 0 <= i < 80 -> forall k, 0 <= k < 8 -> ~ X (g + NK_IF_NAME + 8 * i + k)) ->
  (forall i, 0 <= i < 80 -> forall k, 0 <= k < 4 -> ~ X (g + NK_IF_INDEX + 4 * i + k)) ->
  (forall i nm ix p, nth_error tab i = Some (nm, ix) -> au64_at segs m (g + NK_IF_NAME + 8 * Z.of_nat i) p ->
     acstr_at segs m p nm -> forall j, 0 <= j <= Z.of_nat (length nm) -> ~ X (p + j)) ->
  aiftab_at segs m g bs tab -> aiftab_at segs m' g bs tab.
Proof.
  intros X m m' g bs tab HK HN HI HS (Hn & H80 & Ht). split; [exact Hn|]. split; [exact H80|].
  intros i nm ix Hi. destruct (Ht i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
  assert (Hil : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [exact Hix|]. exists p. split; [|split; [exact Hp0|split]].
  - apply (au64_keep X m m' _ p HK); [intros k Hk; apply HN; lia | exact Hp].
  - apply (acstr_keep X m m' p nm HK); [exact (HS i nm ix p Hi Hp Hs) | exact Hs].
  - apply (au32_keep X m m' _ ix HK); [intros k Hk; apply HI; lia | exact Hx].
Qed.
End kg.

(* ==========================================================================
   1b. The memory FILE (AMemFileSink.v)
   ========================================================================== *)

Section ka.
Variable segs : list Segment.
Variable MS : amemfile_syms.

Definition amf_fp (T : list (Z * Z)) (a : Z) : Prop :=
  amf_head_addr MS a \/ amf_env_addr MS a \/ exists f n, In (f, n) T /\ f <= a < f + AMF_BLOCK.

Lemma amf_env_keep : forall X m m', kagree segs X m m' -> (forall a, amf_env_addr MS a -> ~ X a) ->
  amf_env segs MS m -> amf_env segs MS m'.
Proof.
  intros X m m' HK HX (H1 & H2 & H3). unfold amf_env_addr in HX.
  split; [|split].
  - apply (val_mem_keep segs X m m' _ 1 0 HK); [intros k Hk; apply HX; left; lia | exact H1].
  - apply (val_mem_keep segs X m m' _ 1 0 HK); [intros k Hk; apply HX; right; left; lia | exact H2].
  - apply (val_mem_keep segs X m m' _ 4 0 HK); [intros k Hk; apply HX; right; right; lia | exact H3].
Qed.

Lemma amf_heads_keep : forall X m m' v, kagree segs X m m' -> (forall a, amf_head_addr MS a -> ~ X a) ->
  amf_heads segs MS m v -> amf_heads segs MS m' v.
Proof.
  intros X m m' v HK HX (H1 & H2 & H3). unfold amf_head_addr in HX.
  split; [|split].
  - apply (val_mem_keep segs X m m' _ 8 v HK); [intros k Hk; apply HX; left; lia | exact H1].
  - apply (val_mem_keep segs X m m' _ 8 v HK); [intros k Hk; apply HX; right; left; lia | exact H2].
  - apply (val_mem_keep segs X m m' _ 8 v HK); [intros k Hk; apply HX; right; right; lia | exact H3].
Qed.

Lemma amemfile_at_keep : forall X m m' f, kagree segs X m m' ->
  (forall i, 0 <= i < AMF_BLOCK -> ~ X (f + i)) ->
  amemfile_at segs MS m f -> amemfile_at segs MS m' f.
Proof.
  intros X m m' f HK HX Hf.
  assert (FK : forall off n v, 0 <= off -> off + Z.of_nat n <= AMF_BLOCK ->
             val_mem segs m (f + off) n v -> val_mem segs m' (f + off) n v).
  { intros off n v H0 H1 H. apply (val_mem_keep segs X m m' _ n v HK); [|exact H].
    intros k Hk. replace (f + off + k) with (f + (off + k)) by lia. apply HX. lia. }
  unfold amemfile_at, amemfile_static, amemfile_flags, amemfile_omode, amemfile_window, amemfile_cookie in *.
  unfold AMF_BLOCK, AMF_COOKIE in *.
  destruct Hf as (Hf0 & Hf1 & Hf2 & Hs & Hfl & Hom & Hw & Hc).
  split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [|split; [|split; [|split]]].
  - repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    repeat (split; [apply FK; [lia | cbn; lia | assumption] |]).
    apply FK; [lia | cbn; lia | assumption].
  - destruct Hfl as [H|H]; [left | right]; apply FK; first [lia | cbn; lia | exact H].
  - destruct Hom as [H|H]; [left | right]; apply FK; first [lia | cbn; lia | exact H].
  - destruct Hw as (Hw1 & Hw2 & [(Hw3 & Hw4 & Hw5) | (k & Hk & Hw3 & Hw4 & Hw5)]).
    + split; [apply FK; [lia | cbn; lia | exact Hw1]|]. split; [apply FK; [lia | cbn; lia | exact Hw2]|].
      left. split; [apply FK; [lia | cbn; lia | exact Hw3]|]. split; [apply FK; [lia | cbn; lia | exact Hw4]|].
      apply FK; [lia | cbn; lia | exact Hw5].
    + split; [apply FK; [lia | cbn; lia | exact Hw1]|]. split; [apply FK; [lia | cbn; lia | exact Hw2]|].
      right. exists k. split; [exact Hk|]. split; [apply FK; [lia | cbn; lia | exact Hw3]|].
      split; [apply FK; [lia | cbn; lia | exact Hw4]|]. apply FK; [lia | cbn; lia | exact Hw5].
  - destruct Hc as (pos & len & Hp & Hl & Hc1 & Hc2). exists pos, len. split; [exact Hp|]. split; [exact Hl|].
    split; apply FK; first [lia | cbn; lia | assumption].
Qed.

Lemma amf_gi_keep : forall X m m' T, kagree segs X m m' -> (forall a, amf_fp T a -> ~ X a) ->
  amf_gi segs MS T m -> amf_gi segs MS T m'.
Proof.
  intros X m m' T HK HX [(Hh & HT) | (f & Hh & HT & Hf)].
  - left. split; [|exact HT]. apply (amf_heads_keep X m m' 0 HK); [|exact Hh].
    intros a Ha. apply HX. left. exact Ha.
  - right. exists f. split; [|split; [exact HT|]].
    + apply (amf_heads_keep X m m' f HK); [|exact Hh]. intros a Ha. apply HX. left. exact Ha.
    + apply (amemfile_at_keep X m m' f HK); [|exact Hf].
      intros i Hi. apply HX. right; right. exists f, AMF_BLOCK. split; [rewrite HT; left; reflexivity | lia].
Qed.
End ka.

(* ==========================================================================
   2. The interface's predicates
   ========================================================================== *)

Lemma le_byte_mod64 : forall x k, YG0f.le_byte (x mod 2 ^ 64) 8 k = YG0f.le_byte x 8 k.
Proof. intros x k. unfold YG0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* an 8-byte word view fixes its value modulo 2 ^ 64 *)
Lemma val_mem8_mod : forall segs (m : word -> option byte) a v v',
  val_mem segs m a 8 v -> val_mem segs m a 8 v' -> v mod 2 ^ 64 = v' mod 2 ^ 64.
Proof.
  intros segs m a v v' H H'.
  assert (E : forall k, (k < 8)%nat -> YG0f.le_byte v 8 k = YG0f.le_byte v' 8 k).
  { intros k Hk. pose proof (H k Hk) as A. rewrite (H' k Hk) in A.
    assert (A' : Z_to_bv 8 (YO0f.le_byte v' 8 k) = Z_to_bv 8 (YO0f.le_byte v 8 k)) by congruence.
    apply (f_equal (fun x : bv 8 => bv_unsigned x)) in A'. rewrite !Z_to_bv_unsigned in A'.
    unfold bv_wrap, bv_modulus in A'. change (2 ^ Z.of_N 8) with 256 in A'.
    unfold YO0f.le_byte in A'. unfold YG0f.le_byte. rewrite !Z.mod_mod in A' by lia. symmetry. exact A'. }
  pose proof (le_bytes8 (v mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as R1.
  pose proof (le_bytes8 (v' mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as R2.
  rewrite !le_byte_mod64 in R1, R2. rewrite <- R1, <- R2. rewrite !E by lia. reflexivity.
Qed.

(* the table's entries: the 60 g_names names are at most 4 bytes, entries 60..63 are odd[1..4] *)
Definition lf_tab_chk (i : nat) : bool :=
  match nth_error lf_tab i with
  | Some (nm, _) => if (i <? 60)%nat then (length nm <=? 4)%nat else bl_eqb nm (nth (i - 59) lf_odd_strs [])
  | None => true
  end.
Lemma lf_tab_chk_all : forallb lf_tab_chk (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lf_tab_entry : forall i nm ix, nth_error lf_tab i = Some (nm, ix) ->
  (i < 64)%nat /\ ((i < 60)%nat -> (length nm <= 4)%nat) /\ ((60 <= i)%nat -> nm = nth (i - 59) lf_odd_strs []).
Proof.
  intros i nm ix Hi.
  assert (Hl : (i < 64)%nat) by (rewrite <- lf_tab_len; apply nth_error_Some; rewrite Hi; discriminate).
  pose proof (proj1 (forallb_forall _ _) lf_tab_chk_all i ltac:(apply in_seq; lia)) as C.
  unfold lf_tab_chk in C. rewrite Hi in C.
  split; [exact Hl|]. split; intros Hc.
  - assert (Hn : (i <? 60)%nat = true) by (apply Nat.ltb_lt; exact Hc). rewrite Hn in C. apply Nat.leb_le. exact C.
  - assert (Hn : (i <? 60)%nat = false) by (apply Nat.ltb_ge; exact Hc). rewrite Hn in C. apply bl_eqb_iff. exact C.
Qed.

Section ki.
Context {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.

(* writability carried on a set of bytes *)
Definition wcarry_on (m m' : word -> option byte) (F : Z -> Prop) : Prop :=
  forall a, F a -> writable_at SEGS m a -> writable_at SEGS m' a.
Lemma wcarry_on_sub : forall m m' (F : Z -> Prop) a n,
  wcarry_on m m' F -> (forall i, 0 <= i < n -> F (a + i)) -> wcarry SEGS m m' a n.
Proof. intros m m' F a n H HF i Hi. apply H, HF, Hi. Qed.
Lemma wcarry_on_grows : forall m m' (F : Z -> Prop), mem_grows m m' -> wcarry_on m m' F.
Proof. intros m m' F Hg a _. exact (writable_at_grows SEGS m m' a Hg). Qed.

(* --- the data of a loop head: g_nl, g_names, long_alias, the two blocks, the read-only image ------------- *)
Definition lf_data_fp (md mk a : Z) : Prop :=
  (LA_G_NL <= a < LA_G_NL + NK_SIZE) \/ (LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE) \/
  (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304) \/ (md <= a < md + MD_SIZE) \/ (mk <= a < mk + MK_SIZE) \/
  in_roP SEGS PCAP_RLO PCAP_RHI a.

Lemma lf_gnames_at_keep : forall X m m' j, kagree SEGS X m m' -> j <= 64 ->
  (forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a) ->
  lf_gnames_at j m -> lf_gnames_at j m'.
Proof.
  intros X m m' j HK Hj HX H k Hk. destruct (H k Hk) as (rest & Hb & Hl). exists rest. split; [|exact Hl].
  apply (abytes_keep SEGS X m m' _ _ HK); [|exact Hb]. intros i Hi. rewrite Hl in Hi. change (Z.of_nat 8) with 8 in Hi.
  apply HX. unfold G_NAMES_SIZE. lia.
Qed.

Lemma lf_gnames_w_keep : forall X m m', kagree SEGS X m m' ->
  wcarry SEGS m m' LA_G_NAMES G_NAMES_SIZE ->
  (forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a) ->
  lf_gnames_w m -> lf_gnames_w m'.
Proof.
  intros X m m' HK HW HX H. unfold lf_gnames_w in *. apply (abuf_keep SEGS X m m' _ _ HK HW); [|exact H].
  intros i Hi. apply HX. lia.
Qed.

Lemma lf_odd_at_keep : forall X m m', kagree SEGS X m m' ->
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ X a) -> lf_odd_at m -> lf_odd_at m'.
Proof.
  intros X m m' HK HX H i Hi. destruct (H i Hi) as (q & Hq & Hq0 & Hs & Hro). exists q.
  split; [|split; [exact Hq0 | split; [|exact Hro]]].
  - apply (au64_keep SEGS X m m' _ q HK); [|exact Hq]. intros k Hk. apply HX. right.
    unfold LA_ODD, PCAP_RLO, PCAP_RHI. lia.
  - apply (acstr_keep SEGS X m m' q _ HK); [|exact Hs]. intros j Hj. apply HX, Hro, Hj.
Qed.

Lemma lf_texts_at_keep : forall X m m', kagree SEGS X m m' ->
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ X a) -> lf_texts_at m -> lf_texts_at m'.
Proof.
  intros X m m' HK HX H i Hi. destruct (H i Hi) as (q & s & Hq & Hq0 & Hs & Hro). exists q, s.
  split; [|split; [exact Hq0 | split; [|exact Hro]]].
  - apply (au64_keep SEGS X m m' _ q HK); [|exact Hq]. intros k Hk. apply HX. right.
    unfold LA_TEXTS, PCAP_RLO, PCAP_RHI. lia.
  - apply (acstr_keep SEGS X m m' q _ HK); [|exact Hs]. intros j Hj. apply HX, Hro, Hj.
Qed.

Lemma lf_la_at_keep : forall X m m', kagree SEGS X m m' ->
  wcarry SEGS m m' LA_LONG_ALIAS 304 ->
  (forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304 -> ~ X a) -> lf_la_at m -> lf_la_at m'.
Proof.
  intros X m m' HK HW HX ((la & Hla & Hl) & Hn & (sl & Hsl & Hs)). split; [|split].
  - exists la. split; [|exact Hl]. apply (au8arr_keep SEGS X m m' _ la HK); [| |exact Hla].
    + rewrite Hl. intros i Hi. apply HW. lia.
    + intros i Hi. apply HX. lia.
  - apply (val_mem_keep SEGS X m m' _ 1 0 HK); [|exact Hn]. intros k Hk. apply HX. lia.
  - exists sl. split; [|exact Hs]. apply (au8arr_keep SEGS X m m' _ sl HK); [| |exact Hsl].
    + rewrite Hs. intros i Hi. replace (LA_LONG_ALIAS + 301 + i) with (LA_LONG_ALIAS + (301 + i)) by lia.
      apply HW. change (Z.of_nat 3) with 3 in Hi. lia.
    + intros i Hi. apply HX. rewrite Hs in Hi. change (Z.of_nat 3) with 3 in Hi. lia.
Qed.

(* long_alias's three slack bytes after its NUL: any bytes, present and writable. They lie in long_alias's
   redzone, a row of the runtime's owned statics that akept's image clause does not keep, but at link's image they
   hold at every memory (lf_la_slack_any, the image's ROM fallback and its writable segment) *)
Definition lf_la_slack (m : word -> option byte) : Prop :=
  exists sl, au8arr SEGS m (LA_LONG_ALIAS + 301) sl /\ length sl = 3%nat.

Lemma lf_la_at_keep_ns : forall X m m', kagree SEGS X m m' ->
  wcarry SEGS m m' LA_LONG_ALIAS 301 ->
  (forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 -> ~ X a) -> lf_la_slack m' -> lf_la_at m -> lf_la_at m'.
Proof.
  intros X m m' HK HW HX Hsl' ((la & Hla & Hl) & Hn & _). split; [|split; [|exact Hsl']].
  - exists la. split; [|exact Hl]. apply (au8arr_keep SEGS X m m' _ la HK); [| |exact Hla].
    + rewrite Hl. intros i Hi. apply HW. lia.
    + intros i Hi. apply HX. lia.
  - apply (val_mem_keep SEGS X m m' _ 1 0 HK); [|exact Hn]. intros k Hk. apply HX. lia.
Qed.

Lemma lf_ifp_keep : forall X m m' n, kagree SEGS X m m' -> n <= 64 ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) ->
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ X a) -> lf_ifp m n -> lf_ifp m' n.
Proof.
  intros X m m' n HK Hn HG HR H e He. destruct (H e He) as (q & Hq & H1 & H2). exists q.
  split; [|split; [exact H1|]].
  - apply (au64_keep SEGS X m m' _ q HK); [|exact Hq]. intros k Hk. apply HG. unfold NK_IF_NAME, NK_SIZE. lia.
  - intros He60. apply (au64_keep SEGS X m m' _ q HK); [|exact (H2 He60)]. intros k Hk. apply HR. right.
    unfold LA_ODD, PCAP_RLO, PCAP_RHI. lia.
Qed.

(* the bytes lf_data states writability of (long_alias with its three slack bytes) *)
Definition lf_data_fp_w (md mk a : Z) : Prop :=
  (LA_G_NL <= a < LA_G_NL + NK_SIZE) \/ (LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE) \/
  (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304) \/ (md <= a < md + MD_SIZE) \/ (mk <= a < mk + MK_SIZE).
(* lf_data's bytes a callee must keep: the five objects (long_alias without its slack) and odd's words *)
Definition lf_data_fp_ro (md mk a : Z) : Prop :=
  (LA_G_NL <= a < LA_G_NL + NK_SIZE) \/ (LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE) \/
  (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301) \/ (md <= a < md + MD_SIZE) \/ (mk <= a < mk + MK_SIZE) \/
  (LA_ODD <= a < LA_ODD + 48).

Lemma lf_ifp_keep_ro : forall X m m' n, kagree SEGS X m m' -> n <= 64 ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) ->
  (forall a, LA_ODD <= a < LA_ODD + 48 -> ~ X a) -> lf_ifp m n -> lf_ifp m' n.
Proof.
  intros X m m' n HK Hn HG HO H e He. destruct (H e He) as (q & Hq & H1 & H2). exists q.
  split; [|split; [exact H1|]].
  - apply (au64_keep SEGS X m m' _ q HK); [|exact Hq]. intros k Hk. apply HG. unfold NK_IF_NAME, NK_SIZE. lia.
  - intros He60. apply (au64_keep SEGS X m m' _ q HK); [|exact (H2 He60)]. intros k Hk. apply HO. lia.
Qed.

(* g_nl's interface table, its name strings in g_names (entries 0 .. 59) and in odd's strings (60 .. 63) *)
Lemma lf_aiftab_keep_ro : forall X m m' kbs, kagree SEGS X m m' ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) ->
  (forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a) ->
  lf_ifp m 64 -> lf_ifp m' 64 -> lf_odd_at m' ->
  aiftab_at SEGS m LA_G_NL kbs lf_tab -> aiftab_at SEGS m' LA_G_NL kbs lf_tab.
Proof.
  intros X m m' kbs HK XG XN Hifp Hifp' Hodd' (Hn & H80 & Ht). split; [exact Hn|]. split; [exact H80|].
  intros i nm ix Hi. destruct (Ht i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
  destruct (lf_tab_entry i nm ix Hi) as (H64 & Hlt & Hge).
  assert (Hp' : au64_at SEGS m' (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { apply (au64_keep SEGS X m m' _ p HK); [|exact Hp]. intros k Hk. apply XG. unfold NK_IF_NAME, NK_SIZE. lia. }
  split; [exact Hix|]. exists p. split; [exact Hp'|]. split; [exact Hp0|].
  split; [|apply (au32_keep SEGS X m m' _ ix HK); [|exact Hx]; intros k Hk; apply XG; unfold NK_IF_INDEX, NK_SIZE; lia].
  pose proof Hs as ((Hpa & Hpb & _) & _). rewrite length_app in Hpb. cbn [length] in Hpb.
  destruct (Nat.lt_ge_cases i 60) as [Hi60 | Hi60].
  - destruct (Hifp (Z.of_nat i) ltac:(lia)) as (q & Hq & Hq1 & _).
    pose proof (val_mem8_mod SEGS m _ p q Hp Hq) as Epq. rewrite (Hq1 ltac:(lia)) in Epq.
    pose proof (Hlt Hi60) as Hlen. assert (Hd : 0 <= Z.of_nat i / 15 <= 3) by lia.
    rewrite (Z.mod_small p) in Epq by lia. rewrite Z.mod_small in Epq by (unfold LA_G_NAMES; lia).
    apply (acstr_keep SEGS X m m' p nm HK); [|exact Hs]. intros j Hj. apply XN. unfold G_NAMES_SIZE. lia.
  - pose proof (Hge Hi60) as Hnm.
    destruct (Hodd' (i - 59)%nat ltac:(lia)) as (q' & Hq' & _ & Hs' & _).
    destruct (Hifp' (Z.of_nat i) ltac:(lia)) as (q & Hq & _ & Hq2).
    pose proof (val_mem8_mod SEGS m' _ p q Hp' Hq) as Epq.
    assert (Eq : q mod 2 ^ 64 = q' mod 2 ^ 64).
    { apply (val_mem8_mod SEGS m' (LA_ODD + 8 * Z.of_nat (i - 59))); [|exact Hq'].
      replace (Z.of_nat (i - 59)) with (Z.of_nat i - 59) by lia. exact (Hq2 ltac:(lia)). }
    pose proof Hs' as ((Hqa & Hqb & _) & _). rewrite length_app in Hqb. cbn [length] in Hqb.
    rewrite (Z.mod_small p) in Epq by lia. rewrite (Z.mod_small q') in Eq by lia.
    assert (Ep : p = q') by (rewrite Epq; exact Eq).
    rewrite Ep, Hnm. exact Hs'.
Qed.

(* across a step that may change read-only bytes the walk does not own (a callee's kept clause spares the
   runtime's owned statics only): the odd and texts tables and long_alias's slack are taken at the new memory,
   where a lane re-derives the tables from arodata_okP by computation and the slack by lf_la_slack_any *)
Lemma lf_data_keep_ro : forall X m m' cx md mk kbs mbs gbs, kagree SEGS X m m' ->
  wcarry_on m m' (lf_data_fp_w md mk) -> (forall a, lf_data_fp_ro md mk a -> ~ X a) ->
  lf_odd_at m' -> lf_texts_at m' -> lf_la_slack m' ->
  lf_data cx md mk kbs mbs gbs m -> lf_data cx md mk kbs mbs gbs m'.
Proof.
  intros X m m' cx md mk kbs mbs gbs HK HW HX Hodd' Htx' Hsl'
    (Hnl & Hwf & Hif & Ho & Hmi & Hoc & Hmd & Hmwf & Hmk & Hkwf & Hare & Hifp & Hgn & Hgw & Hodd & Htx & Hla).
  unfold lf_data_fp_ro in HX.
  assert (XG : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) by (intros a Ha; apply HX; tauto).
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a) by (intros a Ha; apply HX; tauto).
  assert (XL : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 -> ~ X a) by (intros a Ha; apply HX; tauto).
  assert (XO : forall a, LA_ODD <= a < LA_ODD + 48 -> ~ X a) by (intros a Ha; apply HX; tauto).
  assert (WS : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) -> wcarry SEGS m m' a n)
    by (intros a n Ha; exact (wcarry_on_sub m m' _ a n HW Ha)).
  assert (Hifp' : lf_ifp m' 64) by exact (lf_ifp_keep_ro X m m' 64 HK ltac:(lia) XG XO Hifp).
  assert (Hnl' : anlk_at SEGS m' LA_G_NL kbs).
  { apply (anlk_keep SEGS X m m' _ kbs HK); [|intros i Hi; apply XG; lia | exact Hnl].
    apply WS. intros i Hi. unfold lf_data_fp_w. left. lia. }
  assert (Hif' : aiftab_at SEGS m' LA_G_NL kbs lf_tab)
    by exact (lf_aiftab_keep_ro X m m' kbs HK XG XN Hifp Hifp' Hodd' Hif).
  assert (Hmd' : amodel_at SEGS m' md mbs).
  { apply (amodel_keep SEGS X m m' _ mbs HK); [|intros i Hi; apply HX; right; right; right; left; lia | exact Hmd].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; left. lia. }
  assert (Hmk' : amarks_at SEGS m' mk gbs).
  { apply (amarks_keep SEGS X m m' _ gbs HK); [|intros i Hi; apply HX; right; right; right; right; left; lia | exact Hmk].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; right. lia. }
  assert (Hgw' : lf_gnames_w m').
  { apply (lf_gnames_w_keep X m m' HK); [|exact XN | exact Hgw].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; left. unfold G_NAMES_SIZE in *. lia. }
  assert (Hla' : lf_la_at m').
  { apply (lf_la_at_keep_ns X m m' HK); [|exact XL | exact Hsl' | exact Hla].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; left. lia. }
  exact (conj Hnl' (conj Hwf (conj Hif' (conj Ho (conj Hmi (conj Hoc (conj Hmd' (conj Hmwf (conj Hmk' (conj Hkwf
    (conj Hare (conj Hifp' (conj (lf_gnames_at_keep X m m' 64 HK ltac:(lia) XN Hgn) (conj Hgw'
    (conj Hodd' (conj Htx' Hla')))))))))))))))).
Qed.

(* across a step that changes no read-only byte (a run of the body, or a callee whose X misses in_roP) *)
Lemma lf_data_keep : forall X m m' cx md mk kbs mbs gbs, kagree SEGS X m m' ->
  wcarry_on m m' (lf_data_fp_w md mk) -> (forall a, lf_data_fp md mk a -> ~ X a) ->
  lf_data cx md mk kbs mbs gbs m -> lf_data cx md mk kbs mbs gbs m'.
Proof.
  intros X m m' cx md mk kbs mbs gbs HK HW HX H.
  assert (XR : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ X a)
    by (intros a Ha; apply HX; right; right; right; right; right; exact Ha).
  pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hodd & Htx & Hla).
  assert (Hsl' : lf_la_slack m').
  { destruct Hla as (_ & _ & (sl & Hsl & Hs)). exists sl. split; [|exact Hs].
    apply (au8arr_keep SEGS X m m' _ sl HK); [| |exact Hsl]; rewrite Hs; change (Z.of_nat 3) with 3; intros i Hi.
    - replace (LA_LONG_ALIAS + 301 + i) with (LA_LONG_ALIAS + (301 + i)) by lia.
      apply (wcarry_on_sub m m' (lf_data_fp_w md mk) LA_LONG_ALIAS 304 HW); [|lia].
      intros j Hj. unfold lf_data_fp_w. right; right; left. lia.
    - apply HX. unfold lf_data_fp. right; right; left. lia. }
  apply (lf_data_keep_ro X m m' cx md mk kbs mbs gbs HK HW);
    [| exact (lf_odd_at_keep X m m' HK XR Hodd) | exact (lf_texts_at_keep X m m' HK XR Htx) | exact Hsl' | exact H].
  intros a Ha. unfold lf_data_fp_ro in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]; apply HX; unfold lf_data_fp.
  - left. exact Ha.
  - right; left. exact Ha.
  - right; right; left. lia.
  - right; right; right; left. exact Ha.
  - right; right; right; right; left. exact Ha.
  - right; right; right; right; right; right. unfold LA_ODD, PCAP_RLO, PCAP_RHI in *. lia.
Qed.

(* --- the two blocks' shadow ------------------------------------------------------------------------------ *)
Definition lf_blocks_fp (md mk a : Z) : Prop :=
  (exists x, md <= x < md + MD_SIZE /\ a = shadow_of_addr SHADOW_OFF x) \/
  (exists x, mk <= x < mk + MK_SIZE /\ a = shadow_of_addr SHADOW_OFF x).

Lemma lf_blocks_keep : forall X m m' cx md mk T3 ly3 S3, kagree SEGS X m m' ->
  (forall a, lf_blocks_fp md mk a -> ~ X a) ->
  lf_blocks B cx md mk T3 ly3 S3 m -> lf_blocks B cx md mk T3 ly3 S3 m'.
Proof.
  intros X m m' cx md mk T3 ly3 S3 HK HX
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
  do 13 (split; [assumption|]).
  split; [apply (ra_keep SEGS X m m' SHADOW_OFF md MD_SIZE HK); [|exact H14];
          intros x Hx; apply HX; left; exists x; split; [exact Hx | reflexivity]|].
  split; [apply (ra_keep SEGS X m m' SHADOW_OFF mk MK_SIZE HK); [|exact H15];
          intros x Hx; apply HX; right; exists x; split; [exact Hx | reflexivity]|].
  split; [exact H16 | exact H17].
Qed.

(* --- the journal's bookkeeping: the FILE, long_alias's NUL, the read-only image, the payload ------------ *)
Definition lf_jbk_fp_rw (cx : lcx) (T3 : list (Z * Z)) (a : Z) : Prop :=
  amf_fp MS T3 a \/ (la_nul <= a < la_nul + 1) \/ (c_p cx <= a < c_p cx + c_n cx).
Definition lf_jbk_fp (cx : lcx) (T3 : list (Z * Z)) (a : Z) : Prop :=
  amf_fp MS T3 a \/ (la_nul <= a < la_nul + 1) \/ in_roP SEGS PCAP_RLO PCAP_RHI a \/
  (c_p cx <= a < c_p cx + c_n cx).

(* with arodata_okP taken at the new memory (across a callee, whose kept clause spares the owned statics only;
   arodata_keep_ns carries it when X misses the non-owned read-only bytes) *)
Lemma lf_jbk_keep_ro : forall X cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own W3' ms3' md3',
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  m_fds md3' = m_fds md3 -> m_fs md3' = m_fs md3 ->
  (forall a, lf_jbk_fp_rw cx T3 a -> ~ X a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3') (ms_mem ms3')) ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3' ms3' md3' T3 own.
Proof.
  intros X cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own W3' ms3' md3' HK Hfd Hfs HX Hro'
    (J1 & JL & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15).
  split; [exact J1|]. split; [exact JL|]. split; [exact J2|]. split; [exact J3|].
  split; [rewrite Hfd; exact J4|]. split; [rewrite Hfs; exact J5|]. split; [exact J6|]. split; [exact J7|].
  split; [apply (amf_gi_keep SEGS MS X _ _ T3 HK); [intros a Ha; apply HX; left; exact Ha | exact J8]|].
  split; [apply (amf_env_keep SEGS MS X _ _ HK); [intros a Ha; apply HX; left; right; left; exact Ha | exact J9]|].
  split; [exact J10|]. split; [exact J11|].
  split; [apply (val_mem_keep SEGS X _ _ la_nul 1 0 HK); [intros k Hk; apply HX; right; left; lia | exact J12]|].
  split; [exact Hro'|].
  split; [apply (abytes_keep SEGS X _ _ (c_p cx) (c_pl cx) HK); [|exact J14];
          intros i Hi; apply HX; right; right; unfold c_n; lia|].
  intros a Ha. rewrite <- (J15 a Ha). apply (aview_of_kagree SEGS X _ _ _ _ _ HK).
  apply HX. right; right. lia.
Qed.

Lemma lf_jbk_keep : forall X cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own W3' ms3' md3',
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  m_fds md3' = m_fds md3 -> m_fs md3' = m_fs md3 ->
  (forall a, lf_jbk_fp cx T3 a -> ~ X a) ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3' ms3' md3' T3 own.
Proof.
  intros X cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own W3' ms3' md3' HK Hfd Hfs HX HJ.
  apply (lf_jbk_keep_ro X cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own W3' ms3' md3' HK Hfd Hfs); [| |exact HJ].
  - intros a Ha. apply HX. unfold lf_jbk_fp_rw, lf_jbk_fp in *. tauto.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J13 & _).
    change (arodata_okP SEGS PCAP_RLO PCAP_RHI B (ard SEGS (rdW W3' (ms_mem ms3')))).
    apply (arodata_keep SEGS X (rdW W3 (ms_mem ms3)) _ PCAP_RLO PCAP_RHI B HK); [|exact J13].
    intros a Ha. apply HX. right; right; left. exact Ha.
Qed.

(* --- the frame: spill slots, the cursor, the saved registers, the side frame's header and shadow ------- *)
Lemma lf_at_keep : forall X W3 ms3 W3' ms3' a v,
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) -> (forall i, 0 <= i < 8 -> ~ X (a + i)) ->
  lf_at W3 ms3 a v -> lf_at W3' ms3' a v.
Proof. intros X W3 ms3 W3' ms3' a v HK HX H. unfold lf_at in *. exact (rdword_keep SEGS X _ _ a v HK HX H). Qed.

Lemma lf_slot_keep : forall X cx W3 ms3 W3' ms3' off v,
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  (forall i, 0 <= i < 8 -> ~ X (lf_sp1 cx + off + i)) ->
  lf_slot cx W3 ms3 off v -> lf_slot cx W3' ms3' off v.
Proof. intros X cx W3 ms3 W3' ms3' off v HK HX H. unfold lf_slot in *. exact (lf_at_keep X _ _ _ _ _ v HK HX H). Qed.

Definition lf_slots_fp (cx : lcx) (a : Z) : Prop :=
  (lf_sp1 cx + 0x18 <= a < lf_sp1 cx + 0x100) \/ (lf_sp1 cx + 0x110 <= a < lf_sp1 cx + 0x118).
Definition lf_cur_fp (cx : lcx) (a : Z) : Prop := lf_sp1 cx + 0x118 <= a < lf_sp1 cx + 0x128.
Definition lf_saved_fp (cx : lcx) (a : Z) : Prop := spZ (c_regs cx) - 104 <= a < spZ (c_regs cx).
Definition lf_header_fp (cx : lcx) (fp a : Z) : Prop :=
  (lf_F cx fp <= a < lf_F cx fp + 24) \/
  (lf_F cx fp + fs_frame_bytes LF_CID - 8 <= a < lf_F cx fp + fs_frame_bytes LF_CID).
Definition lf_fshadow_fp (cx : lcx) (fp n a : Z) : Prop := lf_SH cx fp <= a < lf_SH cx fp + n.

Ltac slot_off :=
  unfold LS_J18, LS_J20, LS_J28, LS_J30, LS_F, LS_FK, LS_B1A0, LS_ODD, LS_MARK0, LS_STR1, LS_B160, LS_NIF, LS_WA,
    LS_B330, LS_B2E0, LS_MK, LS_NMARK, LS_SH_NREQ, LS_SH_NEXT, LS_SH_SE, LS_JT, LS_GNL42, LS_SH_M, LS_NREQ, LS_NEXT,
    LS_SE, LS_M, LS_GNL40, LS_SHB, LS_F0, LS_P, LS_N in *.

Lemma lf_slots_keep : forall X cx md mk fp W3 ms3 W3' ms3',
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  (forall a, lf_slots_fp cx a -> ~ X a) ->
  lf_slots cx md mk fp W3 ms3 -> lf_slots cx md mk fp W3' ms3'.
Proof.
  intros X cx md mk fp W3 ms3 W3' ms3' HK HX H. unfold lf_slots in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat split;
    (eapply (lf_slot_keep X cx W3 ms3 W3' ms3'); [exact HK | | eassumption];
     intros i Hi; apply HX; unfold lf_slots_fp; slot_off; lia).
Qed.

Lemma lf_cur_keep : forall X cx W3 ms3 W3' ms3' P N,
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  (forall a, lf_cur_fp cx a -> ~ X a) ->
  lf_cur cx W3 ms3 P N -> lf_cur cx W3' ms3' P N.
Proof.
  intros X cx W3 ms3 W3' ms3' P N HK HX (H1 & H2 & H3). split; [|split; [|exact H3]];
    (eapply (lf_slot_keep X cx W3 ms3 W3' ms3'); [exact HK | | eassumption];
     intros i Hi; apply HX; unfold lf_cur_fp; slot_off; lia).
Qed.

Lemma lf_saved_keep : forall X cx W3 ms3 W3' ms3',
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  (forall a, lf_saved_fp cx a -> ~ X a) ->
  lf_saved cx W3 ms3 -> lf_saved cx W3' ms3'.
Proof.
  intros X cx W3 ms3 W3' ms3' HK HX (H1 & H2). split.
  - apply (lf_at_keep X W3 ms3 W3' ms3' _ _ HK); [|exact H1]. intros i Hi. apply HX. unfold lf_saved_fp. lia.
  - intros j Hj. apply (lf_at_keep X W3 ms3 W3' ms3' _ _ HK); [|exact (H2 j Hj)].
    intros i Hi. apply HX. unfold lf_saved_fp. lia.
Qed.

Lemma lf_header_keep : forall X cx fp W3 ms3 W3' ms3',
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  (forall a, lf_header_fp cx fp a -> ~ X a) ->
  lf_header cx fp W3 ms3 -> lf_header cx fp W3' ms3'.
Proof.
  intros X cx fp W3 ms3 W3' ms3' HK HX (H1 & H2 & H3 & H4). unfold lf_header_fp in HX.
  split; [|split; [|split]];
    (eapply (lf_at_keep X W3 ms3 W3' ms3'); [exact HK | | eassumption]); intros i Hi; apply HX; lia.
Qed.

Lemma lf_fshadow_keep : forall X cx fp W3 ms3 W3' ms3' sh,
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  (forall a, lf_fshadow_fp cx fp (Z.of_nat (length sh)) a -> ~ X a) ->
  lf_fshadow cx fp W3 ms3 sh -> lf_fshadow cx fp W3' ms3' sh.
Proof.
  intros X cx fp W3 ms3 W3' ms3' sh HK HX H i Hi. rewrite <- (H i Hi).
  apply (aview_of_kagree SEGS X _ _ _ _ _ HK). apply HX. unfold lf_fshadow_fp. lia.
Qed.

(* --- the memory clauses every cut of the loop carries, at once ------------------------------------------ *)
Definition lf_cut_fp (cx : lcx) (fp md mk : Z) (T3 : list (Z * Z)) (a : Z) : Prop :=
  lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
  lf_jbk_fp cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a.

Lemma lf_cut_keep_sh : forall X cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 W3 ms3 md3 W3' ms3' md3' sh,
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  wcarry_on (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) (lf_data_fp_w md mk) ->
  m_fds md3' = m_fds md3 -> m_fs md3' = m_fs md3 ->
  (forall a, lf_cut_fp cx fp md mk T3 a -> ~ X a) -> (length sh = 112)%nat ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 sh ->
  lf_slots cx md mk fp W3 ms3 ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W3' ms3' /\ lf_header cx fp W3' ms3' /\ lf_fshadow cx fp W3' ms3' sh /\
  lf_slots cx md mk fp W3' ms3' /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3' ms3' md3' T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3' (ms_mem ms3')) /\
  lf_data cx md mk kbs mbs gbs (rdW W3' (ms_mem ms3')).
Proof.
  intros X cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 W3 ms3 md3 W3' ms3' md3' sh
    HK HW Hfd Hfs HX Hl H1 H2 H3 H4 H5 H6 H7.
  unfold lf_cut_fp in HX.
  split; [apply (lf_saved_keep X cx W3 ms3 W3' ms3' HK); [intros a Ha; apply HX; tauto | exact H1]|].
  split; [apply (lf_header_keep X cx fp W3 ms3 W3' ms3' HK); [intros a Ha; apply HX; tauto | exact H2]|].
  split; [apply (lf_fshadow_keep X cx fp W3 ms3 W3' ms3' sh HK); [|exact H3];
          intros a Ha; apply HX; rewrite Hl in Ha; change (Z.of_nat 112) with 112 in Ha; tauto|].
  split; [apply (lf_slots_keep X cx md mk fp W3 ms3 W3' ms3' HK); [intros a Ha; apply HX; tauto | exact H4]|].
  split; [apply (lf_jbk_keep X cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own W3' ms3' md3' HK Hfd Hfs);
          [intros a Ha; apply HX; tauto | exact H5]|].
  split; [apply (lf_blocks_keep X _ _ cx md mk T3 ly3 S3 HK); [intros a Ha; apply HX; tauto | exact H6]|].
  apply (lf_data_keep X _ _ cx md mk kbs mbs gbs HK HW); [intros a Ha; apply HX; tauto | exact H7].
Qed.

Lemma lf_cut_keep : forall X cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 W3 ms3 md3 W3' ms3' md3',
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) ->
  wcarry_on (rdW W3 (ms_mem ms3)) (rdW W3' (ms_mem ms3')) (lf_data_fp_w md mk) ->
  m_fds md3' = m_fds md3 -> m_fs md3' = m_fs md3 ->
  (forall a, lf_cut_fp cx fp md mk T3 a -> ~ X a) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W3' ms3' /\ lf_header cx fp W3' ms3' /\ lf_fshadow cx fp W3' ms3' LF_SH0 /\
  lf_slots cx md mk fp W3' ms3' /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3' ms3' md3' T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3' (ms_mem ms3')) /\
  lf_data cx md mk kbs mbs gbs (rdW W3' (ms_mem ms3')).
Proof.
  intros X cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 W3 ms3 md3 W3' ms3' md3' HK HW Hfd Hfs HX.
  exact (lf_cut_keep_sh X cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 W3 ms3 md3 W3' ms3' md3' LF_SH0
    HK HW Hfd Hfs HX ltac:(rewrite LF_SH0_len; reflexivity)).
Qed.

(* ==========================================================================
   3. The instances: where each footprint lies
   ========================================================================== *)

Lemma in_roP_low : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> 0 <= a < kLowMemEnd.
Proof.
  intros a [(s & Hs & _ & Hr) | Hr].
  - apply pa_segs_low. exists s. split; [exact Hs | exact Hr].
  - unfold PCAP_RLO, PCAP_RHI, kLowMemEnd in *. lia.
Qed.

(* the data and the blocks' shadow lie below the allocator's ceiling, given the two blocks below it (AR's block
   law, al_blocks) *)
Lemma lf_data_fp_low : forall md mk a, md + MD_SIZE <= alloc_ceiling -> mk + MK_SIZE <= alloc_ceiling ->
  lf_data_fp md mk a -> a < alloc_ceiling.
Proof.
  intros md mk a Hmd Hmk H. pose proof asan_consts as ((C1a & C1b) & _).
  destruct H as [H|[H|[H|[H|[H|H]]]]];
    try (unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS in H; lia).
  pose proof (in_roP_low a H) as L. unfold kLowMemEnd in L. lia.
Qed.

Lemma lf_blocks_fp_low : forall md mk a, 0 <= md -> md + MD_SIZE <= alloc_ceiling -> 0 <= mk ->
  mk + MK_SIZE <= alloc_ceiling ->
  lf_blocks_fp md mk a -> a < alloc_ceiling.
Proof.
  intros md mk a H0 Hmd H1 Hmk H. pose proof asan_consts as ((C1a & C1b) & _).
  assert (SH : forall x, 0 <= x < alloc_ceiling -> shadow_of_addr SHADOW_OFF x < alloc_ceiling).
  { intros x Hx. unfold shadow_of_addr. pose proof (Z.mul_div_le x 8 ltac:(lia)) as Q.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Q0.
    remember (x / 8) as y eqn:Ey. clear Ey. unfold SHADOW_OFF. lia. }
  destruct H as [(x & Hx & ->) | (x & Hx & ->)].
  - apply SH. lia.
  - apply SH. lia.
Qed.

End ki.

(* ==========================================================================
   4. Across a callee: the cut's memory clauses from the callee's kept clauses (link_amem.v akept,
      ashadow_kept), the window [lf_sp1 cx - K, lf_sp1 cx) of a callee called with sp = s1
   ========================================================================== *)

Lemma obyte_eq_dec : forall (x y : option byte), {x = y} + {x <> y}.
Proof.
  intros [b|] [c|]; try (right; discriminate); try (left; reflexivity).
  destruct (Z.eq_dec (bv_unsigned b) (bv_unsigned c)) as [E|E].
  - left. f_equal. apply bv_eq. exact E.
  - right. intros H. injection H as H. apply E. rewrite H. reflexivity.
Qed.

Section kc.
Context {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.

(* the bytes whose view a step keeps, as a set K: the step's byte agreement is off its complement *)
Lemma kagree_of_kept : forall (K : Z -> Prop) H H' (mem mem' : word -> option byte),
  (forall a, K a -> aview SEGS H' mem' a = aview SEGS H mem a) ->
  kagree SEGS (fun a => ~ K a) (mrestrict H mem) (mrestrict H' mem').
Proof.
  intros K H H' mem mem' HK a Hnn.
  destruct (obyte_eq_dec (mbyte SEGS (mrestrict H' mem') a) (mbyte SEGS (mrestrict H mem) a)) as [E|E]; [exact E|].
  exfalso. apply Hnn. intros Ka. apply E.
  assert (HV : forall b, ~ (b <> a) -> aview SEGS H' mem' b = aview SEGS H mem b).
  { intros b Hb. destruct (Z.eq_dec b a) as [->|Hne]; [exact (HK a Ka) | exfalso; exact (Hb Hne)]. }
  exact (kagree_of_aview SEGS (fun b => b <> a) H H' mem mem' HV a (fun C => C eq_refl)).
Qed.

(* what akept and ashadow_kept keep; the step's byte agreement holds off lf_X, its complement *)
Definition lf_kept (ly3 : alayout) (S3 : astate) (ly2 : alayout) (S2 : astate) (slo shi : Z) (E : Z -> Prop)
    (a : Z) : Prop :=
  (((alloc_ceiling <= a < 2 ^ 64 /\ ~ (slo <= a < shi)) \/
    (exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m) \/
    (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
    (exists cid pos, In (cid, pos) (frames S3) /\
       (in_zr a (frame_rng ly3 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8))))
   /\ ~ E a) \/
  (exists b m x, In (b, m) (ablocks B ly3 S3) /\ In (b, m) (ablocks B ly2 S2) /\ b <= x < b + req_size m /\
     a = shadow_addr x).
Definition lf_X (ly3 : alayout) (S3 : astate) (ly2 : alayout) (S2 : astate) (slo shi : Z) (E : Z -> Prop)
    (a : Z) : Prop := ~ lf_kept ly3 S3 ly2 S2 slo shi E a.

Lemma lf_kept_view : forall ly3 S3 ly2 S2 W3 mem3 W2 mem2 slo shi (E : Z -> Prop),
  akept SEGS B ly3 S3 W3 mem3 W2 mem2 slo shi E -> ashadow_kept SEGS B ly3 S3 ly2 S2 W3 mem3 W2 mem2 ->
  forall a, lf_kept ly3 S3 ly2 S2 slo shi E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a.
Proof.
  intros ly3 S3 ly2 S2 W3 mem3 W2 mem2 slo shi E (K1 & K2 & K3 & K4 & _ & _) HSK a
    [([(H1 & H2) | [(b & m & Hin & Hb) | [(Hi & Ho & Her) | (cid & pos & Hin & Hr)]]] & HE) | (b & m & x & H1 & H2 & Hx & ->)].
  - exact (K1 a H1 H2 HE).
  - replace a with (b + (a - b)) by lia.
    apply (K2 b m (a - b)); [exact Hin | lia | replace (b + (a - b)) with a by lia; exact HE].
  - exact (K3 a Hi Ho Her HE).
  - exact (K4 cid pos a Hin Hr HE).
  - exact (HSK b m x H1 H2 Hx).
Qed.

Lemma lf_callee_kagree : forall ly3 S3 ly2 S2 (W3 : world SEGS) mem3 (W2 : world SEGS) mem2 slo shi (E : Z -> Prop),
  akept SEGS B ly3 S3 W3 mem3 W2 mem2 slo shi E -> ashadow_kept SEGS B ly3 S3 ly2 S2 W3 mem3 W2 mem2 ->
  kagree SEGS (lf_X ly3 S3 ly2 S2 slo shi E) (rdW W3 mem3) (rdW W2 mem2).
Proof.
  intros ly3 S3 ly2 S2 W3 mem3 W2 mem2 slo shi E HK HS.
  exact (kagree_of_kept (lf_kept ly3 S3 ly2 S2 slo shi E) (w_H W3) (w_H W2) mem3 mem2
    (lf_kept_view ly3 S3 ly2 S2 W3 mem3 W2 mem2 slo shi E HK HS)).
Qed.

(* the five classes of kept bytes, as ~ lf_X *)
Lemma lfx_stk : forall ly3 S3 ly2 S2 slo shi (E : Z -> Prop) a,
  alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a -> ~ lf_X ly3 S3 ly2 S2 slo shi E a.
Proof.
  unfold lf_X. intros ly3 S3 ly2 S2 slo shi E a H1 H2 H3 HX. apply HX. left.
  split; [left; split; assumption | exact H3].
Qed.

Lemma lfx_blk : forall ly3 S3 ly2 S2 slo shi (E : Z -> Prop) b m a,
  In (b, m) (ablocks B ly3 S3) -> b <= a < b + m -> ~ E a -> ~ lf_X ly3 S3 ly2 S2 slo shi E a.
Proof.
  unfold lf_X. intros ly3 S3 ly2 S2 slo shi E b m a Hin Ha HnE HX. apply HX. left. split; [|exact HnE].
  right; left. exists b, m. split; [exact Hin|].
  unfold req_size. destruct (m =? 0) eqn:Em; [apply Z.eqb_eq in Em; subst m; lia | lia].
Qed.

Lemma lfx_img : forall ly3 S3 ly2 S2 slo shi (E : Z -> Prop) a,
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ E a ->
  ~ lf_X ly3 S3 ly2 S2 slo shi E a.
Proof.
  unfold lf_X. intros ly3 S3 ly2 S2 slo shi E a H1 H2 H3 HnE HX. apply HX. left. split; [|exact HnE].
  right; right; left. split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma lfx_frm : forall ly3 S3 ly2 S2 slo shi (E : Z -> Prop) cid pos a,
  In (cid, pos) (frames S3) ->
  (in_zr a (frame_rng ly3 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8)) ->
  ~ E a -> ~ lf_X ly3 S3 ly2 S2 slo shi E a.
Proof.
  unfold lf_X. intros ly3 S3 ly2 S2 slo shi E cid pos a Hin Hr HnE HX. apply HX. left. split; [|exact HnE].
  right; right; right. exists cid, pos. split; [exact Hin | exact Hr].
Qed.

Lemma lfx_sh : forall ly3 S3 ly2 S2 slo shi (E : Z -> Prop) b m x,
  In (b, m) (ablocks B ly3 S3) -> In (b, m) (ablocks B ly2 S2) -> b <= x < b + req_size m ->
  ~ lf_X ly3 S3 ly2 S2 slo shi E (shadow_addr x).
Proof.
  unfold lf_X. intros ly3 S3 ly2 S2 slo shi E b m x H1 H2 Hx HX. apply HX. right.
  exists b, m, x. split; [exact H1|]. split; [exact H2|]. split; [exact Hx | reflexivity].
Qed.

(* the image bytes the interface reads besides the read-only ones: akept keeps them by its image clause *)
Definition lf_img_fp (a : Z) : Prop :=
  (LA_G_NL <= a < LA_G_NL + NK_SIZE) \/ (LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE) \/
  (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301) \/ amf_head_addr MS a \/ amf_env_addr MS a \/
  (la_nul <= a < la_nul + 1) \/ (LA_ODD <= a < LA_ODD + 48).
Definition lf_img_ok : Prop := forall a, lf_img_fp a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition lf_relro_img : Prop := forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.

Lemma lfx_imgfp : forall ly3 S3 ly2 S2 slo shi (E : Z -> Prop) a, lf_img_ok -> lf_img_fp a -> ~ E a ->
  ~ lf_X ly3 S3 ly2 S2 slo shi E a.
Proof.
  intros ly3 S3 ly2 S2 slo shi E a HI Ha HnE. destruct (HI a Ha) as (H1 & H2 & H3).
  exact (lfx_img ly3 S3 ly2 S2 slo shi E a H1 H2 H3 HnE).
Qed.

(* --- a callee called with sp = s1 (lf_sp1 cx), window K, write set E, from a cut's state ------------------ *)
Definition lf_call (cx : lcx) (K : Z) (ly3 : alayout) (S3 : astate) (ly2 : alayout) (S2 : astate)
    (W3 : world SEGS) (mem3 : word -> option byte) (W2 : world SEGS) (mem2 : word -> option byte) (E : Z -> Prop)
    : Prop :=
  0 <= K /\ alloc_ceiling <= lf_sp1 cx - K /\
  akept SEGS B ly3 S3 W3 mem3 W2 mem2 (lf_sp1 cx - K) (lf_sp1 cx) E /\
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 mem3 W2 mem2.

#[local] Notation LX cx K ly3 S3 ly2 S2 E := (lf_X ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E).

Lemma lf_call_kagree : forall cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E,
  lf_call cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E -> kagree SEGS (LX cx K ly3 S3 ly2 S2 E) (rdW W3 mem3) (rdW W2 mem2).
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E (_ & _ & H1 & H2).
  exact (lf_callee_kagree ly3 S3 ly2 S2 W3 mem3 W2 mem2 _ _ E H1 H2).
Qed.

Lemma lf_sp1_le : forall cx, lf_sp1 cx + LF_MFRAME <= spZ (c_regs cx) /\ spZ (c_regs cx) < 2 ^ 64.
Proof.
  intros cx. unfold lf_sp1, lf_sp1_of, spZ.
  pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 2)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  pose proof (Z.mul_div_le (bv_unsigned (getr (c_regs cx) 2) - LF_MFRAME) 32 ltac:(lia)) as Q. lia.
Qed.

(* the real frame's bytes above s1 *)
Lemma lfx_above : forall cx K ly3 S3 ly2 S2 (E : Z -> Prop) a,
  0 <= K -> alloc_ceiling <= lf_sp1 cx - K -> lf_sp1 cx <= a < spZ (c_regs cx) -> ~ E a ->
  ~ LX cx K ly3 S3 ly2 S2 E a.
Proof.
  intros cx K ly3 S3 ly2 S2 E a HK0 HK1 Ha HnE. pose proof (lf_sp1_le cx) as (P1 & P2).
  apply lfx_stk; [lia | lia | exact HnE].
Qed.

(* the side frame and its shadow *)
Lemma lfx_side : forall cx fp K ly3 S3 ly2 S2 (E : Z -> Prop) a,
  In (LF_CID, fp) (frames S3) -> (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) ->
  (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ E a ->
  ~ LX cx K ly3 S3 ly2 S2 E a.
Proof.
  intros cx fp K ly3 S3 ly2 S2 E a HFR J2 Ha HnE. pose proof LF_frame_slot as (F1024 & _).
  apply (lfx_frm ly3 S3 ly2 S2 _ _ E LF_CID fp a HFR); [|exact HnE].
  unfold lf_SH, lf_F, shadow_of_addr in Ha. unfold frame_rng, in_zr, shadow_addr. cbn [fst snd].
  rewrite J2, F1024. lia.
Qed.

(* the call's data: g_nl, g_names, long_alias and odd (image), the model and the marks (blocks of the call) *)
Lemma lfx_data : forall cx K ly3 S3 ly2 S2 (E : Z -> Prop) md mk a,
  lf_img_ok -> In (md, MD_SIZE) (ablocks B ly3 S3) -> In (mk, MK_SIZE) (ablocks B ly3 S3) ->
  lf_data_fp_ro md mk a -> ~ E a -> ~ LX cx K ly3 S3 ly2 S2 E a.
Proof.
  intros cx K ly3 S3 ly2 S2 E md mk a HI B1 B2 Ha HnE.
  unfold lf_data_fp_ro in Ha.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]];
    try (apply (lfx_imgfp ly3 S3 ly2 S2 _ _ E a HI); [unfold lf_img_fp; tauto | exact HnE]).
  - exact (lfx_blk ly3 S3 ly2 S2 _ _ E md MD_SIZE a B1 Ha HnE).
  - exact (lfx_blk ly3 S3 ly2 S2 _ _ E mk MK_SIZE a B2 Ha HnE).
Qed.

(* --- per predicate, across the callee ------------------------------------------------------------------- *)
Lemma lf_saved_callee : forall cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E,
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, lf_saved_fp cx a -> ~ E a) -> lf_saved cx W3 ms3 -> lf_saved cx W2 ms2.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC HE H. pose proof HC as (HK0 & HK1 & _).
  pose proof (lf_sp1_le cx) as (P1 & P2).
  apply (lf_saved_keep _ cx W3 ms3 W2 ms2 (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact H].
  intros a Ha. apply lfx_above; [exact HK0 | exact HK1 | unfold lf_saved_fp, LF_MFRAME in *; lia | exact (HE a Ha)].
Qed.

Lemma lf_slots_callee : forall cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp,
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, lf_slots_fp cx a -> ~ E a) -> lf_slots cx md mk fp W3 ms3 -> lf_slots cx md mk fp W2 ms2.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp HC HE H. pose proof HC as (HK0 & HK1 & _).
  pose proof (lf_sp1_le cx) as (P1 & P2).
  apply (lf_slots_keep _ cx md mk fp W3 ms3 W2 ms2 (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact H].
  intros a Ha. apply lfx_above; [exact HK0 | exact HK1 | unfold lf_slots_fp, LF_MFRAME in *; lia | exact (HE a Ha)].
Qed.

Lemma lf_cur_callee : forall cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N,
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, lf_cur_fp cx a -> ~ E a) -> lf_cur cx W3 ms3 P N -> lf_cur cx W2 ms2 P N.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N HC HE H. pose proof HC as (HK0 & HK1 & _).
  pose proof (lf_sp1_le cx) as (P1 & P2).
  apply (lf_cur_keep _ cx W3 ms3 W2 ms2 P N (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact H].
  intros a Ha. apply lfx_above; [exact HK0 | exact HK1 | unfold lf_cur_fp, LF_MFRAME in *; lia | exact (HE a Ha)].
Qed.

Lemma lf_header_callee : forall cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E,
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  In (LF_CID, fp) (frames S3) -> (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) ->
  (forall a, lf_header_fp cx fp a -> ~ E a) -> lf_header cx fp W3 ms3 -> lf_header cx fp W2 ms2.
Proof.
  intros cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC HFR J2 HE H. pose proof LF_frame_slot as (F1024 & _).
  apply (lf_header_keep _ cx fp W3 ms3 W2 ms2 (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact H].
  intros a Ha. apply (lfx_side cx fp K ly3 S3 ly2 S2 E a HFR J2); [|exact (HE a Ha)].
  unfold lf_header_fp in Ha. rewrite F1024 in Ha. lia.
Qed.

Lemma lf_fshadow_callee : forall cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E,
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  In (LF_CID, fp) (frames S3) -> (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) ->
  (forall a, lf_fshadow_fp cx fp 112 a -> ~ E a) -> lf_fshadow cx fp W3 ms3 LF_SH0 -> lf_fshadow cx fp W2 ms2 LF_SH0.
Proof.
  intros cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC HFR J2 HE H.
  apply (lf_fshadow_keep _ cx fp W3 ms3 W2 ms2 LF_SH0 (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact H].
  intros a Ha. rewrite LF_SH0_len in Ha. change (Z.of_nat LF_NSH) with 112 in Ha.
  apply (lfx_side cx fp K ly3 S3 ly2 S2 E a HFR J2); [|exact (HE a Ha)].
  unfold lf_fshadow_fp in Ha. lia.
Qed.

(* the two blocks' shadow: ashadow_kept keeps it whatever E is *)
Lemma lf_blocks_callee : forall cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E md mk T3,
  lf_call cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 mem3) -> lf_blocks B cx md mk T3 ly3 S3 (rdW W2 mem2).
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E md mk T3 HC HMD2 HMK2 Hblk.
  pose proof Hblk as (B1 & B2 & _).
  apply (lf_blocks_keep B _ _ _ cx md mk T3 ly3 S3 (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact Hblk].
  intros a [(x & Hx & ->) | (x & Hx & ->)]; change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  - apply (lfx_sh ly3 S3 ly2 S2 _ _ E md MD_SIZE x B1 HMD2). unfold req_size, MD_SIZE in *. cbn. lia.
  - apply (lfx_sh ly3 S3 ly2 S2 _ _ E mk MK_SIZE x B2 HMK2). unfold req_size, MK_SIZE in *. cbn. lia.
Qed.

(* the read-only image: E misses it (a callee's apre: its write set misses in_roP) *)
Lemma lf_aro_callee : forall cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E,
  lf_relro_img -> lf_call cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E ->
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) mem3) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2).
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E HREL HC HE H.
  change (arodata_okP SEGS PCAP_RLO PCAP_RHI B (ard SEGS (rdW W2 mem2))).
  apply (arodata_keep_ns SEGS _ (rdW W3 mem3) _ PCAP_RLO PCAP_RHI B (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC));
    [|exact H].
  intros a Hro Hno Her. apply (lfx_img ly3 S3 ly2 S2 _ _ E a); [| exact Hno | exact Her | exact (HE a Hro)].
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HREL a Hr)].
Qed.

(* long_alias's NUL, when E misses it *)
Lemma lf_la_nul_callee : forall cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E,
  lf_img_ok -> lf_call cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E -> ~ E la_nul ->
  val_mem SEGS (rdW W3 mem3) la_nul 1 0 -> val_mem SEGS (rdW W2 mem2) la_nul 1 0.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E HI HC HnE H.
  apply (val_mem_keep SEGS _ _ _ la_nul 1 0 (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact H].
  intros k Hk. replace (la_nul + k) with la_nul by lia.
  apply (lfx_imgfp ly3 S3 ly2 S2 _ _ E la_nul HI); [|exact HnE].
  unfold lf_img_fp. right; right; right; right; right; left. lia.
Qed.

(* the journal's memory clauses; the allocator-state clauses stay at the call's state ly3 S3; long_alias's NUL is
   taken at the new memory (lf_la_nul_callee gives it when E misses it) *)
Definition lf_jbk_fp_c (cx : lcx) (T3 : list (Z * Z)) (a : Z) : Prop :=
  amf_fp MS T3 a \/ (c_p cx <= a < c_p cx + c_n cx).

Lemma lf_jbk_callee : forall cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E,
  lf_img_ok -> lf_relro_img ->
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, lf_jbk_fp_c cx T3 a -> ~ E a) -> (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0 ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own.
Proof.
  intros cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E HI HREL HC HE HEro HPAY Hfd Hfs Hla
    (J1 & JL & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15).
  pose proof (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC) as HKG.
  set (X := LX cx K ly3 S3 ly2 S2 E) in HKG.
  assert (XI : forall a, lf_img_fp a -> ~ E a -> ~ X a)
    by (intros a Ha HnE; exact (lfx_imgfp ly3 S3 ly2 S2 _ _ E a HI Ha HnE)).
  assert (XF : forall a, amf_fp MS T3 a -> ~ X a).
  { intros a Ha. assert (HnE : ~ E a) by (apply HE; left; exact Ha).
    destruct Ha as [Ha | [Ha | (f & n & Hf & Ha)]].
    - apply XI; [unfold lf_img_fp; tauto | exact HnE].
    - apply XI; [unfold lf_img_fp; tauto | exact HnE].
    - destruct (amf_gi_shape SEGS MS T3 _ J8) as [Et | (f' & Et)]; rewrite Et in Hf; [destruct Hf|].
      destruct Hf as [Hf | []]. injection Hf as E1 E2. subst f' n.
      apply (lfx_blk ly3 S3 ly2 S2 _ _ E f AMF_BLOCK a); [apply J11; rewrite Et; left; reflexivity | exact Ha | exact HnE]. }
  assert (XP : forall a, c_p cx <= a < c_p cx + c_n cx -> ~ X a).
  { intros a Ha. apply (lfx_blk ly3 S3 ly2 S2 _ _ E (c_p cx) (c_n cx) a); [apply HPAY; lia | exact Ha |].
    apply HE. right. exact Ha. }
  split; [exact J1|]. split; [exact JL|]. split; [exact J2|]. split; [exact J3|].
  split; [rewrite Hfd; exact J4|]. split; [rewrite Hfs; exact J5|]. split; [exact J6|]. split; [exact J7|].
  split; [apply (amf_gi_keep SEGS MS X _ _ T3 HKG); [exact XF | exact J8]|].
  split; [apply (amf_env_keep SEGS MS X _ _ HKG); [intros a Ha; apply XF; right; left; exact Ha | exact J9]|].
  split; [exact J10|]. split; [exact J11|]. split; [exact Hla|].
  split; [exact (lf_aro_callee cx K ly3 S3 ly2 S2 W3 _ W2 _ E HREL HC HEro J13)|].
  split; [apply (abytes_keep SEGS X _ _ (c_p cx) (c_pl cx) HKG); [|exact J14];
          intros i Hi; apply XP; unfold c_n; lia|].
  intros a Ha. rewrite <- (J15 a Ha). apply (aview_of_kagree SEGS X _ _ _ _ _ HKG). apply XP. lia.
Qed.

Lemma lf_data_callee : forall cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E md mk kbs mbs gbs,
  lf_img_ok -> lf_call cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E ->
  In (md, MD_SIZE) (ablocks B ly3 S3) -> In (mk, MK_SIZE) (ablocks B ly3 S3) ->
  wcarry_on (rdW W3 mem3) (rdW W2 mem2) (lf_data_fp_w md mk) ->
  (forall a, lf_data_fp_ro md mk a -> ~ E a) ->
  lf_odd_at (rdW W2 mem2) -> lf_texts_at (rdW W2 mem2) -> lf_la_slack (rdW W2 mem2) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 mem3) -> lf_data cx md mk kbs mbs gbs (rdW W2 mem2).
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E md mk kbs mbs gbs HI HC B1 B2 HW HE HODD HTX HSL H.
  apply (lf_data_keep_ro _ _ _ cx md mk kbs mbs gbs (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC) HW);
    [|exact HODD | exact HTX | exact HSL | exact H].
  intros a Ha. exact (lfx_data cx K ly3 S3 ly2 S2 E md mk a HI B1 B2 Ha (HE a Ha)).
Qed.

(* the same with the frame's shadow at any 112 values (op_read calls free while two frame objects are in scope) *)
Lemma lf_fshadow_callee_sh : forall cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E sh,
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  In (LF_CID, fp) (frames S3) -> (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) ->
  (length sh = 112)%nat ->
  (forall a, lf_fshadow_fp cx fp 112 a -> ~ E a) -> lf_fshadow cx fp W3 ms3 sh -> lf_fshadow cx fp W2 ms2 sh.
Proof.
  intros cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E sh HC HFR J2 Hl HE H.
  apply (lf_fshadow_keep _ cx fp W3 ms3 W2 ms2 sh (lf_call_kagree _ _ _ _ _ _ _ _ _ _ _ HC)); [|exact H].
  intros a Ha. rewrite Hl in Ha. change (Z.of_nat 112) with 112 in Ha.
  apply (lfx_side cx fp K ly3 S3 ly2 S2 E a HFR J2); [|exact (HE a Ha)].
  unfold lf_fshadow_fp in Ha. lia.
Qed.

(* --- the whole cut at once, when E misses every footprint ----------------------------------------------- *)
Lemma lf_cut_callee_sh : forall cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2
    K (E : Z -> Prop) sh, (length sh = 112)%nat ->
    lf_img_ok -> lf_relro_img ->
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  In (LF_CID, fp) (frames S3) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  (forall a, E a -> ~ (lf_cut_fp MS la_nul cx fp md mk T3 a \/ lf_cur_fp cx a \/
                       in_roP SEGS PCAP_RLO PCAP_RHI a)) ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  wcarry_on (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) (lf_data_fp_w md mk) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  lf_odd_at (rdW W2 (ms_mem ms2)) -> lf_texts_at (rdW W2 (ms_mem ms2)) -> lf_la_slack (rdW W2 (ms_mem ms2)) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 sh ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 sh /\
  lf_slots cx md mk fp W2 ms2 /\ lf_cur cx W2 ms2 P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)) /\
  lf_data cx md mk kbs mbs gbs (rdW W2 (ms_mem ms2)) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 K E sh Hl
    HI HREL HC HFR HPAY HE HMD2 HMK2 HW Hfd Hfs HODD HTX HSL Hsv Hhd Hfs0 Hsl Hcur Hjbk Hblk Hdat.
  assert (NE : forall a, (lf_cut_fp MS la_nul cx fp md mk T3 a \/ lf_cur_fp cx a \/
                          in_roP SEGS PCAP_RLO PCAP_RHI a) -> ~ E a) by (intros a Ha HEa; exact (HE a HEa Ha)).
  unfold lf_cut_fp in NE.
  pose proof Hjbk as (_ & _ & J2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & J12 & J13 & _).
  pose proof Hblk as (B1 & B2 & _).
  assert (HRO : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2))).
  { apply (lf_aro_callee cx K ly3 S3 ly2 S2 W3 _ W2 _ E HREL HC); [|exact J13].
    intros a Ha. apply NE. right; right. exact Ha. }
  split; [apply (lf_saved_callee cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC); [|exact Hsv];
          intros a Ha; apply NE; left; left; exact Ha|].
  split; [apply (lf_header_callee cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC HFR J2); [|exact Hhd];
          intros a Ha; apply NE; left; right; left; exact Ha|].
  split; [apply (lf_fshadow_callee_sh cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E sh HC HFR J2 Hl); [|exact Hfs0];
          intros a Ha; apply NE; left; right; right; left; exact Ha|].
  split; [apply (lf_slots_callee cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp HC); [|exact Hsl];
          intros a Ha; apply NE; left; right; right; right; left; exact Ha|].
  split; [apply (lf_cur_callee cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N HC); [|exact Hcur];
          intros a Ha; apply NE; right; left; exact Ha|].
  split.
  { apply (lf_jbk_callee cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E HI HREL HC);
      [| |exact HPAY | exact Hfd | exact Hfs | |exact Hjbk].
    - intros a Ha. apply NE. left; right; right; right; right; left. unfold lf_jbk_fp_c, lf_jbk_fp in *. tauto.
    - intros a Ha. apply NE. right; right. exact Ha.
    - apply (lf_la_nul_callee cx K ly3 S3 ly2 S2 W3 _ W2 _ E HI HC); [|exact J12].
      apply NE. left; right; right; right; right; left. unfold lf_jbk_fp. right; left. lia. }
  split; [exact (lf_blocks_callee cx K ly3 S3 ly2 S2 W3 _ W2 _ E md mk T3 HC HMD2 HMK2 Hblk)|].
  split; [|exact HRO].
  apply (lf_data_callee cx K ly3 S3 ly2 S2 W3 _ W2 _ E md mk kbs mbs gbs HI HC B1 B2 HW);
    [|exact HODD | exact HTX | exact HSL | exact Hdat].
  intros a Ha. apply NE. left; right; right; right; right; right; right.
  unfold lf_data_fp_ro in Ha. unfold lf_data_fp.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
  - left. exact Ha.
  - right; left. exact Ha.
  - right; right; left. lia.
  - right; right; right; left. exact Ha.
  - right; right; right; right; left. exact Ha.
  - right; right; right; right; right; right. unfold LA_ODD, PCAP_RLO, PCAP_RHI in *. lia.
Qed.
Lemma lf_cut_callee : forall cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2
    K (E : Z -> Prop),
  lf_img_ok -> lf_relro_img ->
  lf_call cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  In (LF_CID, fp) (frames S3) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  (forall a, E a -> ~ (lf_cut_fp MS la_nul cx fp md mk T3 a \/ lf_cur_fp cx a \/
                       in_roP SEGS PCAP_RLO PCAP_RHI a)) ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  wcarry_on (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) (lf_data_fp_w md mk) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  lf_odd_at (rdW W2 (ms_mem ms2)) -> lf_texts_at (rdW W2 (ms_mem ms2)) -> lf_la_slack (rdW W2 (ms_mem ms2)) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 LF_SH0 /\
  lf_slots cx md mk fp W2 ms2 /\ lf_cur cx W2 ms2 P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)) /\
  lf_data cx md mk kbs mbs gbs (rdW W2 (ms_mem ms2)) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 K E.
  exact (lf_cut_callee_sh cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 K E
    LF_SH0 ltac:(rewrite LF_SH0_len; reflexivity)).
Qed.

(* the instance facts, decided on link's image: the image objects the interface reads are image bytes outside the
   runtime's statics and errno, and the relro window is in the image *)
Definition lf_img_rngs : list (Z * Z) :=
  [(LA_G_NL, NK_SIZE); (LA_G_NAMES, G_NAMES_SIZE); (LA_LONG_ALIAS, 301);
   (0x62fec0, 8); (0x6312e0, 8); (0x652308, 8); (0x651ea1, 1); (0x651ea3, 1); (0x652300, 4);
   (LA_NUL, 1); (LA_ODD, 48); (PCAP_RLO, PCAP_RHI - PCAP_RLO)].
Definition lf_rng_ok (r : Z * Z) : bool :=
  (0x10000 <=? fst r) && (fst r + snd r <=? PcapImgEnd.pcap_img_end).
Definition lf_rng_free (r : Z * Z) : bool :=
  forallb (g_avoids (fst r) (snd r)) Tfib_owned_static && g_avoids (fst r) (snd r) (TFIB_ERRNO, 4).
Lemma lf_img_rngs_ok : forallb lf_rng_ok lf_img_rngs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lf_img_rngs_free : forallb lf_rng_free (removelast lf_img_rngs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lf_img_facts : pa_segs = tfibsegs -> PcapSyms B -> MS = link_amf -> la_nul = LA_NUL ->
  lf_img_ok /\ lf_relro_img.
Proof.
  intros HSEGS TB HMS Hla.
  assert (RNG : forall lo n a, In (lo, n) lf_img_rngs -> lo <= a < lo + n -> in_img SEGS a).
  { intros lo n a Hin Ha. rewrite HSEGS. apply AD1y.in_img_hull.
    pose proof (proj1 (forallb_forall _ _) lf_img_rngs_ok (lo, n) Hin) as X.
    unfold lf_rng_ok in X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
    apply Z.leb_le in X1. apply Z.leb_le in X2. lia. }
  assert (FREE : forall lo n a, In (lo, n) (removelast lf_img_rngs) -> lo <= a < lo + n ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
  { intros lo n a Hin Ha. pose proof (proj1 (forallb_forall _ _) lf_img_rngs_free (lo, n) Hin) as X.
    unfold lf_rng_free in X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
    rewrite (ts_owned B TB), (ts_errno B TB). split.
    - intros Ho. apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
      pose proof (proj1 (forallb_forall _ _) X1 r Hr) as Y. unfold g_avoids in Y.
      apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia.
    - intros He. unfold g_avoids in X2. cbn [fst snd] in X2.
      apply orb_prop in X2 as [Y|Y]; apply Z.leb_le in Y; lia. }
  split.
  - intros a Ha.
    unfold lf_img_fp, amf_head_addr, amf_env_addr, amf_ofl_head in Ha. rewrite HMS, Hla in Ha.
    cbn [amf_sink_addr amf_say_addr amf_threaded amf_need_locks amf_ofl_lock link_amf] in Ha.
    assert (Hr : exists lo n, In (lo, n) (removelast lf_img_rngs) /\ lo <= a < lo + n).
    { unfold LA_NUL in Ha.
      destruct Ha as [Ha|[Ha|[Ha|[[Ha|[Ha|Ha]]|[[Ha|[Ha|Ha]]|[Ha|Ha]]]]]];
        [ exists LA_G_NL, NK_SIZE | exists LA_G_NAMES, G_NAMES_SIZE | exists LA_LONG_ALIAS, 301
        | exists 0x62fec0, 8 | exists 0x6312e0, 8 | exists 0x652308, 8
        | exists 0x651ea1, 1 | exists 0x651ea3, 1 | exists 0x652300, 4
        | exists (LA_LONG_ALIAS + 300), 1 | exists LA_ODD, 48 ];
        (split; [cbn; repeat (first [left; reflexivity | right]) | lia]). }
    destruct Hr as (lo & n & Hin & Hlo).
    split; [apply (RNG lo n a); [cbn [removelast lf_img_rngs In] in Hin |- *; tauto | exact Hlo]
           | exact (FREE lo n a Hin Hlo)].
  - intros a Ha. apply (RNG PCAP_RLO (PCAP_RHI - PCAP_RLO) a); [cbn; repeat (first [left; reflexivity | right]) | lia].
Qed.

(* long_alias's three slack bytes hold at every memory of link's image: each reads through the image's ROM
   fallback when the memory has no byte for it, and lies in a writable segment *)
Lemma lf_la_slack_any : pa_segs = tfibsegs -> forall m, lf_la_slack m.
Proof.
  intros HSEGS m. unfold lf_la_slack. rewrite HSEGS.
  assert (R : forall i, (i < 3)%nat -> exists b, mbyte tfibsegs m (LA_LONG_ALIAS + 301 + Z.of_nat i) = Some b).
  { intros i Hi. unfold mbyte.
    destruct (m (Z_to_bv 64 (LA_LONG_ALIAS + 301 + Z.of_nat i))) as [b|]; [exists b; reflexivity|].
    destruct (seg_rom tfibsegs (Z_to_bv 64 (LA_LONG_ALIAS + 301 + Z.of_nat i))) as [b|] eqn:ES;
      [exists b; reflexivity|].
    exfalso. destruct i as [|[|[|i]]]; [vm_compute in ES; discriminate ES .. | lia]. }
  destruct (R 0%nat ltac:(lia)) as (b0 & E0).
  destruct (R 1%nat ltac:(lia)) as (b1 & E1).
  destruct (R 2%nat ltac:(lia)) as (b2 & E2).
  exists [b0; b1; b2]. split; [|reflexivity]. split.
  - split; [unfold LA_LONG_ALIAS; lia|]. split; [cbn [length]; unfold LA_LONG_ALIAS; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|[|[|i]]]; cbn [nth_error]; [exact E0 | exact E1 | exact E2 | lia].
  - intros i Hi. cbn [length] in Hi. change (Z.of_nat 3) with 3 in Hi.
    apply (writable_at_of_wseg tfibsegs m (LA_LONG_ALIAS + 301) 3);
      [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia | vm_compute; reflexivity | lia].
Qed.
End kc.
