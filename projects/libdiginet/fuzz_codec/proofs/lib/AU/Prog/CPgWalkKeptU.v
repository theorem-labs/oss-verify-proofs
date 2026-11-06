(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CPgWalkKept.v and moved to image B (the ASan-UBSan build):
   the image-A core modules are image B's (lib/AU), YImgTop is YImgTopU, the CA_ constants are CB_ ones with
   image B's values; lemma and tactic names unchanged. *)
(* Modified by Theorem Labs, 2026-10: cw_fresh, cw_kept0, cw_kept_step and cw_kept_call are the text of
   proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v:63-153 (origin/ossv/recipes 4b6f0df50aa7: sbd_fresh,
   sbd_kept0, sbd_kept_step, sbd_kept_call), with the segment list made image B's tfibsegs, the call's window a
   parameter and the world after the call generalized, for libdiginet/fuzz_codec's ASan build; cw_kept_cj is new. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================= what a frame-owning walk keeps of its entry state =======================
   After a side-stack frame request (acall_kept) or a caller-journal callee (its post's tcj_kept) the walk
   keeps only blocks, the image, the frames of the call state and memory above the allocator ceiling, so it
   carries tcj_kept itself (projects/libreac/fuzz_identity/proofs/lib/A/Prog/sb_dec_A.v:59-153, with the world
   generalized). *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* A byte the walk may change besides its window and its write set: its own new frame, the frame's shadow,
   the frame's flag byte; none is above the allocator ceiling, in the image, in a heap block of the call state
   or in a frame of it (or that frame's shadow). *)
Definition cw_fresh (lyc : alayout) (Sc : astate) (a : Z) : Prop :=
  a < alloc_ceiling /\ ~ in_img tfibsegs a /\
  (forall bb m i, In (bb, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> a <> bb + i) /\
  (forall cid pos, In (cid, pos) (frames Sc) ->
     ~ in_zr a (frame_rng lyc (cid, pos)) /\ ~ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
Lemma cw_kept0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T (E : Z -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= sp - T -> sp <= sp0 ->
  tcj_kept tfibsegs B T lyc Sc W memc W memc sp E.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T E HJ Hwin Hsp.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ Hp; exact Hp|].
intros a Ha. apply Hpres. clear - Ha Hwin Hsp. lia.
Qed.
Section k.
Hypothesis LAWS : AR_laws tfibsegs B.
(* A run that changes only bytes of X, each in the walk's window, its write set, or fresh. *)
Lemma cw_kept_step : forall T lyc Sc W m0 mdc W1 m1 m2 sp (E X : Z -> Prop),
  alloc_ceiling <= sp - T -> AR tfibsegs B lyc Sc W m0 mdc ->
  tcj_kept tfibsegs B T lyc Sc W m0 W1 m1 sp E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H W1) m2 a = aview tfibsegs (w_H W1) m1 a) ->
  (forall a, X a -> (sp - T <= a < sp) \/ (E a /\ ~ in_img tfibsegs a) \/ cw_fresh lyc Sc a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
  tcj_kept tfibsegs B T lyc Sc W m0 W1 m2 sp E.
Proof.
intros T lyc Sc W m0 mdc W1 m1 m2 sp E X Hce HAR (K1 & K2 & K3 & K4 & K5 & K6) HX HXc Hpr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split.
{ intros a Ha Hw HE. rewrite HX; [exact (K1 a Ha Hw HE) | clear - Ha C1; lia |].
  intros Hx. destruct (HXc a Hx) as [Hw' | [(HE' & _) | (Hf & _)]]; [exact (Hw Hw') | exact (HE HE') | clear - Ha Hf; lia]. }
split.
{ intros bb m i Hin Hi HE.
  destruct (al_blocks _ _ LAWS lyc Sc W m0 mdc bb m HAR Hin) as (_ & H4096 & Hceil & _).
  rewrite HX; [exact (K2 bb m i Hin Hi HE) | clear - H4096 Hceil Hi C1; lia |].
  intros Hx. destruct (HXc _ Hx) as [Hw' | [(HE' & _) | (_ & _ & Hf & _)]];
  [clear - Hw' Hce Hceil Hi; lia | exact (HE HE') | exact (Hf bb m i Hin Hi eq_refl)]. }
split.
{ intros a Him Hns Herr. pose proof (tfib_segs_low a Him) as Hlo.
  rewrite HX; [exact (K3 a Him Hns Herr) | unfold kLowMemEnd in Hlo; clear - Hlo; lia |].
  intros Hx. destruct (HXc _ Hx) as [Hw' | [(_ & HE') | (_ & Hf & _)]];
  [unfold kLowMemEnd in Hlo; clear - Hw' Hce Hlo C1; lia | exact (HE' Him) | exact (Hf Him)]. }
split.
{ intros cid pos a Hin Hr HE.
  destruct (frames_bounds tfibsegs B LAWS lyc Sc W m0 mdc cid pos HAR Hin) as (H4096 & Hceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    assert (D1 : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= alloc_ceiling / 8)
      by (apply Z.div_le_mono; [lia | clear - Hceil; lia]).
    assert (D3 : frame_addr lyc cid pos / 8 + fs_frame_bytes cid / 8 <= (frame_addr lyc cid pos + fs_frame_bytes cid) / 8).
    { pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
      pose proof (Z.div_mod (frame_addr lyc cid pos + fs_frame_bytes cid) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (frame_addr lyc cid pos + fs_frame_bytes cid) 8 ltac:(lia)).
      clear - H H0 H1 H2 H3 H4. lia. }
    assert (D4 : 8 * (alloc_ceiling / 8) <= alloc_ceiling).
    { pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)). pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)). clear - H H0. lia. }
    assert (D5 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
    clear - Hr H4096 Hceil C1 D1 D3 D4 D5. destruct Hr as [Hr | Hr]; lia. }
  rewrite HX; [exact (K4 cid pos a Hin Hr HE) | clear - Ha C1; lia |].
  intros Hx. destruct (HXc _ Hx) as [Hw' | [(HE' & _) | (_ & _ & _ & Hf)]];
  [clear - Hw' Hce Ha; lia | exact (HE HE') | destruct (Hf cid pos Hin) as (Hf1 & Hf2); destruct Hr as [Hr | Hr]; [exact (Hf1 Hr) | exact (Hf2 Hr)]]. }
split; [intros a Ha Hw Hp; apply Hpr; exact (K5 a Ha Hw Hp)|].
intros a Ha. apply Hpr. exact (K6 a Ha).
Qed.
(* A byte of a frame of a state or of that frame's shadow lies below the allocator ceiling. *)
Lemma cw_frame_zone_low : forall lyc Sc W m mdc cid pos a, AR tfibsegs B lyc Sc W m mdc -> In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  0 <= a < alloc_ceiling.
Proof.
intros lyc Sc W m mdc cid pos a HAR Hin Hr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W m mdc cid pos HAR Hin) as (H4096 & Hceil & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
assert (D1 : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= alloc_ceiling / 8)
  by (apply Z.div_le_mono; [lia | clear - Hceil; lia]).
assert (D3 : frame_addr lyc cid pos / 8 + fs_frame_bytes cid / 8 <= (frame_addr lyc cid pos + fs_frame_bytes cid) / 8).
{ pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
  pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
  pose proof (Z.div_mod (frame_addr lyc cid pos + fs_frame_bytes cid) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (frame_addr lyc cid pos + fs_frame_bytes cid) 8 ltac:(lia)).
  clear - H H0 H1 H2 H3 H4. lia. }
assert (D4 : 8 * (alloc_ceiling / 8) <= alloc_ceiling).
{ pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)). pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)). clear - H H0. lia. }
assert (D5 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
clear - Hr H4096 Hceil C1 D1 D3 D4 D5. destruct Hr as [Hr | Hr]; lia.
Qed.
(* A caller-journal callee: its post's tcj_kept (window [sp1 - T1, sp1), write set E1), taken at the state of
   the call (ly3, S3: the call state plus the walk's own frames), composed into the walk's. Each byte of E1 is in
   the walk's window, in its write set E, or fresh. *)
Lemma cw_kept_cj : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own3 ly3 S3 W3 mem3 md3 k3
  W4 mem4 T T1 sp sp1 (E E1 : Z -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own3 ly3 S3 W3 mem3 md3 k3 ->
  incl (frames Sc) (frames S3) -> Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) ->
  alloc_ceiling <= sp - T -> sp <= 2 ^ 47 -> sp - T <= sp1 - T1 -> sp1 <= sp ->
  (forall a, E1 a -> (sp - T <= a < sp) \/ (E a /\ ~ in_img tfibsegs a) \/ cw_fresh lyc Sc a) ->
  tcj_kept tfibsegs B T lyc Sc W memc W3 mem3 sp E ->
  tcj_kept tfibsegs B T1 ly3 S3 W3 mem3 W4 mem4 sp1 E1 ->
  tcj_kept tfibsegs B T lyc Sc W memc W4 mem4 sp E.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own3 ly3 S3 W3 mem3 md3 k3 W4 mem4 T T1 sp sp1 E E1
  HJ HJ3 Hfr Hbl Hce H47 Hw1 Hw2 HE1 (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6).
pose proof HJ as (HAR & Hly & _). pose proof HJ3 as (_ & Hly3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Efr : forall cid pos, frame_addr ly3 cid pos = frame_addr lyc cid pos).
{ intros cid pos. unfold frame_addr.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF, EF3. reflexivity. }
split.
{ intros a Ha Hw HE. rewrite (L1 a Ha).
  - exact (K1 a Ha Hw HE).
  - intros H. apply Hw. clear - H Hw1 Hw2. lia.
  - intros H1. destruct (HE1 a H1) as [Hx | [(Hx & _) | (Hx & _)]]; [exact (Hw Hx) | exact (HE Hx) | clear - Ha Hx; lia]. }
split.
{ intros bb m i Hin Hi HE.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HAR Hin) as (_ & H4096 & Hceil & _).
  rewrite (L2 bb m i (Permutation_in _ (Permutation_sym Hbl) Hin)).
  - exact (K2 bb m i Hin Hi HE).
  - exact Hi.
  - intros H1. destruct (HE1 _ H1) as [Hx | [(Hx & _) | (_ & _ & Hx & _)]];
    [clear - Hx Hce Hceil Hi; lia | exact (HE Hx) | exact (Hx bb m i Hin Hi eq_refl)]. }
split.
{ intros a Him Hns Herr. rewrite (L3 a Him Hns Herr). exact (K3 a Him Hns Herr). }
split.
{ intros cid pos a Hin Hr HE.
  assert (Hr3 : in_zr a (frame_rng ly3 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8))
    by (unfold frame_rng in *; cbn [fst snd] in *; rewrite Efr; exact Hr).
  pose proof (cw_frame_zone_low lyc Sc W memc mdc cid pos a HAR Hin Hr) as Ha.
  rewrite (L4 cid pos a (Hfr _ Hin) Hr3).
  - exact (K4 cid pos a Hin Hr HE).
  - intros H1. destruct (HE1 _ H1) as [Hx | [(Hx & _) | (_ & _ & _ & Hx)]];
    [clear - Hx Hce Ha; lia | exact (HE Hx) | destruct (Hx cid pos Hin) as (Hf1 & Hf2); destruct Hr as [Hr | Hr]; [exact (Hf1 Hr) | exact (Hf2 Hr)]]. }
split.
{ intros a Ha Hw Hp. apply L5; [exact Ha | intros H; apply Hw; clear - H Hw1 Hw2; lia | exact (K5 a Ha Hw Hp)]. }
intros a Ha. destruct (Z_lt_le_dec a (sp1 - T1)) as [Hl | Hl]; [|destruct (Z_lt_le_dec a sp1) as [Hh | Hh]].
- apply L5; [clear - Ha Hce H47 Hl; lia | clear - Hl; lia | exact (K6 a Ha)].
- apply L6. clear - Hl Hh. lia.
- apply L5; [clear - Ha Hce H47 Hh; lia | clear - Hh; lia | exact (K6 a Ha)].
Qed.
(* The walk's own frame (cid, pos), requested since the call state (frames S3 = (cid, pos) :: frames Sc, the
   blocks a permutation of the call state's): each byte of it and of its shadow is fresh. *)
Lemma cw_fresh_own : forall lyc Sc ly3 S3 W3 m3 md3 cid pos a,
  AR tfibsegs B ly3 S3 W3 m3 md3 -> frames S3 = (cid, pos) :: frames Sc ->
  Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly3 c p = frame_addr lyc c p) ->
  (in_zr a (frame_rng ly3 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8)) ->
  cw_fresh lyc Sc a.
Proof.
intros lyc Sc ly3 S3 W3 m3 md3 cid pos a HAR Hfr Hbl Efr Hr.
assert (Hin : In (cid, pos) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (cw_frame_zone_low ly3 S3 W3 m3 md3 cid pos a HAR Hin Hr) as Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split.
{ intros Him. pose proof (tfib_img_range a Him) as (Hlo & Hhi).
  pose proof (frm_off_img B ly3 S3 W3 m3 md3 cid pos HAR Hin) as Hoff.
  unfold TFIB_IMG_LO, TFIB_IMG_END in Hlo, Hhi. unfold YCbqU.off_img, YImgTopU.IMG_LO, YImgTopU.IMG_TOP in Hoff.
  unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
  pose proof (Z.div_pos (frame_addr ly3 cid pos) 8 ltac:(destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 m3 md3 cid pos HAR Hin); lia) ltac:(lia)).
  destruct Hr as [Hr | Hr]; lia. }
split.
{ intros bb m i Hb Hi ->. apply (block_not_frame_zone tfibsegs B LAWS ly3 S3 W3 m3 md3 bb m i cid pos HAR
    (Permutation_in _ (Permutation_sym Hbl) Hb) Hin Hi Hr). }
intros cid' pos' Hin'. apply in_split in Hin' as (l2 & l3 & El).
assert (Hd : forall x, in_zr x (frame_rng ly3 (cid', pos')) \/ in_zr x (shadow_addr (frame_addr ly3 cid' pos'), fs_frame_bytes cid' / 8) ->
  (in_zr x (frame_rng ly3 (cid, pos)) \/ in_zr x (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8)) -> False).
{ intros x Hx1 Hx2. apply (frames_zone_disj tfibsegs B LAWS ly3 S3 W3 m3 md3 (cid, pos) (cid', pos') [] l2 l3 x HAR).
  - rewrite Hfr, El. reflexivity.
  - cbn [fst snd]. exact Hx2.
  - cbn [fst snd]. exact Hx1. }
unfold frame_rng in *. cbn [fst snd] in *. rewrite <- !Efr.
split; intros Hx; apply (Hd a); [left; exact Hx | exact Hr | right; exact Hx | exact Hr].
Qed.
End k.
(* A runtime call whose clobbered stack [slo, shi) lies in the walk's window. *)
Lemma cw_kept_call : forall T lyc Sc W m0 W1 m1 m2 sp slo shi (E : Z -> Prop),
  alloc_ceiling <= sp - T -> sp <= 2 ^ 47 -> sp - T <= slo -> shi <= sp ->
  tcj_kept tfibsegs B T lyc Sc W m0 W1 m1 sp E ->
  acall_kept tfibsegs B lyc Sc W1 m1 W1 m2 slo shi (fun _ => False) ->
  tcj_kept tfibsegs B T lyc Sc W m0 W1 m2 sp E.
Proof.
intros T lyc Sc W m0 W1 m1 m2 sp slo shi E Hce H47 Hlo Hhi (K1 & K2 & K3 & K4 & K5 & K6) (A1 & A2 & A3 & A4 & A5 & A6).
split.
{ intros a Ha Hw HE. rewrite (A1 a Ha) by (intros H; apply Hw; clear - H Hlo Hhi; lia). exact (K1 a Ha Hw HE). }
split.
{ intros bb m i Hin Hi HE. rewrite (A2 bb m i Hin Hi (fun H => H)). exact (K2 bb m i Hin Hi HE). }
split.
{ intros a Him Hns Herr. rewrite (A3 a Him Hns Herr). exact (K3 a Him Hns Herr). }
split.
{ intros cid pos a Hin Hr HE. rewrite (A4 cid pos a Hin Hr (fun H => H)). exact (K4 cid pos a Hin Hr HE). }
split.
{ intros a Ha Hw Hp. apply A5; [exact Ha | intros H; apply Hw; clear - H Hlo Hhi; lia | exact (K5 a Ha Hw Hp)]. }
intros a Ha. destruct (Z_lt_le_dec a slo) as [Hl | Hl]; [|destruct (Z_lt_le_dec a shi) as [Hh | Hh]].
- apply A5; [clear - Ha Hce H47 Hl; lia | clear - Hl; lia | exact (K6 a Ha)].
- apply A6. clear - Hl Hh. lia.
- apply A5; [clear - Ha Hce H47 Hh; lia | clear - Hh; lia | exact (K6 a Ha)].
Qed.
End b.
