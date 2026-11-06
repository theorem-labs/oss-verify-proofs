(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACaa.v:43-46; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-143, 148-156, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/write_uint.v; 60 of its 136 lines of code are new or changed and 1267 lines of the source are left out. *)
(* The run-independent lemmas the post-condition of write_uint's build-B walk (lib/B/Prog/write_uint.v,
   twrite_uint_post) needs: the kept-set of the whole call (tcj_kept, IdentBCJ.v) from "outside the call's
   window, the destination, the side-stack frame, its shadow and its flag cell nothing changed", one destination
   byte as a value out of a region's chunk, and garr8 from the byte values. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YC5d YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ IdentBFrame YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require write_uint_c write_uint.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
(* The shadow of an address below the allocation ceiling lies in [kLowMemEnd, kLowMemEnd + 0xffffff00000]:
   above every low application address and below kHighMemBeg (and so below the ceiling). *)
Lemma wu_shadow_rng : forall x, 0 <= x <= alloc_ceiling ->
  kLowMemEnd <= shadow_addr x <= kLowMemEnd + 0xffffff00000.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _).
assert (Hq2 : x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; clear - Hx C1; lia).
assert (Hq1 : 0 <= x / 8) by (apply Z.div_pos; clear - Hx; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in Hq2.
unfold shadow_addr, SHADOW_OFF, kLowMemEnd.
set (y := x / 8) in *. clearbody y. clear - Hq1 Hq2. lia.
Qed.
Section post.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* 1. The kept-set of the whole call, from "outside D nothing changed" plus the separation facts.
   D = the callee's stack window, the destination [q, q + m), the side-stack frame F it took, F's shadow and
   F's flag cell. The window lies above the allocation ceiling (the caller's journal: astk_ok), and the
   destination lies in heap blocks and side-stack frames of the call state (tdst_ok), so off the image. *)
Lemma wu_tcj_of_kept : forall (STK : Z) lyc Sc (W : world SEGS) memc mdc mem2 ly2 S2 md2 (sp q m F FL : Z),
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B ly2 S2 W mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ (q <= a < q + m) ->
     ~ (F <= a < F + 64) -> ~ (shadow_addr F <= a < shadow_addr F + 8) -> a <> FL ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, sp - STK <= a < sp -> apresent (w_H W) mem2 a) ->
  alloc_ceiling <= sp - STK -> tdst_ok B lyc Sc q m ->
  4096 <= F -> F + 64 <= alloc_ceiling -> F mod 64 = 0 -> FL < alloc_ceiling -> 4096 <= FL ->
  (forall b w i, In (b, w) (ablocks B lyc Sc) -> 0 <= i < req_size w ->
     ~ (F <= b + i < F + 64) /\ b + i <> FL) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (F <= a < F + 64) /\ ~ (shadow_addr F <= a < shadow_addr F + 8) /\ a <> FL) ->
  (forall a, in_img SEGS a -> ~ (F <= a < F + 64) /\ ~ (shadow_addr F <= a < shadow_addr F + 8) /\ a <> FL) ->
  tcj_kept B STK lyc Sc W memc W mem2 sp (fun a => q <= a < q + m).
Proof.
intros STK lyc Sc W memc mdc mem2 ly2 S2 md2 sp q m F FL HAR _ HK HP HPw Hsp HD HF0 HFc _ HFL _ HBL HFR HIM.
pose proof asan_consts as (C1 & _).
(* F's shadow lies in [kLowMemEnd, kHighMemBeg) *)
assert (HSH : forall a, shadow_addr F <= a < shadow_addr F + 8 -> kLowMemEnd <= a < kHighMemBeg).
{ intros a Ha. pose proof (wu_shadow_rng F ltac:(clear - HF0 HFc; lia)) as HS.
  unfold kLowMemEnd, kHighMemBeg in *. clear - Ha HS. lia. }
(* the destination is off the image *)
assert (HDI : forall a, q <= a < q + m -> ~ in_img SEGS a).
{ intros a Ha. destruct (HD a Ha) as [(b & w & Hin & Hr) | (cid & pos & Hin & Hr)].
  - exact (blk_img SEGS B LAWS lyc Sc W memc mdc b w a HAR Hin Hr).
  - unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr). }
unfold tcj_kept.
split.
{ (* above the ceiling: the frame, its shadow and the flag cell are all below it *)
  intros a Ha Hw HE. apply HK; [clear - Ha C1; lia | exact Hw | exact HE | | | ].
  - clear - Ha HFc. lia.
  - intros Hs. pose proof (HSH a Hs) as Hz. unfold kHighMemBeg in Hz. clear - Ha Hz C1. lia.
  - clear - Ha HFL. lia. }
split.
{ (* a heap-block byte of Sc: application memory below the ceiling, so off F's shadow and the window *)
  intros b w i Hin Hi HE.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b w HAR Hin) as (_ & Hb0 & Hbc & Hbapp & _).
  destruct (HBL b w i Hin Hi) as (HnF & HnFL).
  pose proof (in_app_addr b (req_size w) (b + i) Hbapp ltac:(clear - Hi; lia)) as Happ.
  apply HK; [clear - Hb0 Hbc Hi C1; lia | clear - Hb0 Hbc Hi Hsp; lia | exact HE | exact HnF | | exact HnFL].
  intros Hs. pose proof (HSH _ Hs) as Hz. destruct Happ as (_ & [Hl | (Hh & _)]).
  - unfold kLowShadowBeg, kLowMemEnd in *. clear - Hz Hl. lia.
  - clear - Hz Hh. lia. }
split.
{ (* an image byte: below kLowMemEnd, so off the window; off the destination by tdst_ok *)
  intros a Him _ _.
  destruct (HIM a Him) as (HnF & HnS & HnFL).
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  apply HK; [clear - Hlo C1; lia | clear - Hlo Hsp C1; lia | | exact HnF | exact HnS | exact HnFL].
  intros Hq. exact (HDI a Hq Him). }
split.
{ (* a byte of a frame of Sc or of its shadow: below the ceiling, so off the window *)
  intros cid pos a Hin Hr HE.
  destruct (HFR cid pos a Hin Hr) as (HnF & HnS & HnFL).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  assert (Hz : 0 <= a < alloc_ceiling).
  { unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    destruct Hr as [Hr | Hr]; [clear - Hr Hf0 Hfc; lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Sh3.
    pose proof (wu_shadow_rng (frame_addr lyc cid pos) ltac:(clear - Hf0 Hfc Hnn; lia)) as Sh1.
    pose proof (wu_shadow_rng (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(clear - Hf0 Hfc Hnn; lia)) as Sh2.
    unfold kLowMemEnd in Sh1, Sh2. clear - Hr Sh1 Sh2 Sh3 C1.
    set (k8 := fs_frame_bytes cid / 8) in *. clearbody k8. lia. }
  apply HK; [clear - Hz C1; lia | clear - Hz Hsp; lia | exact HE | exact HnF | exact HnS | exact HnFL]. }
split; [exact HP | exact HPw].
Qed.
(* 2. A one-byte value out of a region's chunk (the walk reads the destination's bytes off the out region). *)
Lemma wu_val_of_chunk1 : forall E (m : word -> option byte) (r : YP09.region) (nn : nat) (base off val : Z) (e : sv),
  region_ok SEGS E m r -> YP09.r_base r = Some nn -> bv_unsigned (ew E nn) = base ->
  In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 val -> 0 <= val < 256 ->
  val_mem SEGS m (base + off) 1 val.
Proof.
intros E m r nn base off val e HR Hb Hbase Hin He Hv.
pose proof (region_ok_chunk SEGS E m r _ HR Hin) as HC.
unfold base_val in HC. rewrite Hb, Hbase in HC.
change 1%nat with (N.to_nat 1).
apply (val_of_chunk_ok SEGS E m base off 1 e val HC He).
- change (2 ^ (8 * Z.of_N 1)) with 256. exact Hv.
- change (Z.of_N 1) with 1. lia.
Qed.
(* 3. garr8 from the byte-by-byte values. *)
Lemma wu_garr8_of_vals : forall (m : word -> option byte) (o : Z) (l : list Z),
  (forall j, (j < length l)%nat -> val_mem SEGS m (o + Z.of_nat j) 1 (nth j l 0)) ->
  (forall j, (j < length l)%nat -> 0 <= nth j l 0 < 256) ->
  garr8 SEGS m o l.
Proof. intros m o l Hv Hr j Hj. split; [exact (Hv j Hj) | exact (Hr j Hj)]. Qed.
End post.
End f.
End d.
