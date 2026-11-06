(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* DgnDecodeKept: acall_kept (YCbq.v), what a caller-journal call keeps of its caller's memory, carried step by step
   by a walk: dk_kept_refl at the entry; after each step that changes only the bytes Zs, dk_kept_run (no own
   side-stack frame, or an own frame given by its separation facts) or dk_kept_own (the walk owns a frame of class
   cid); after a call, dk_kept_trans (the callee's acall_kept at the same call state) or dk_kept_trans_nf (the
   callee's call state has the walk's own frame). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun PaShadow PaJournal DgnTransportSyms DgnTransportList DgnTransportPa DgnTransportPaLib YC4b YC1g YC1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Context {L : ptable tsym} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* A live side-stack frame starts on 64 bytes and has a multiple of 64 bytes, at least 64. *)
Lemma dk_frame_al64 : forall ly S W mem md cid pos,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
intros ly S W mem md cid pos [M _] Hin.
destruct (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
(* What the call keeps of the caller's memory, carried from the entry memory memc to the current one. *)
Lemma dk_kept_refl : forall lyc Sc W memc slo shi (Eo : Z -> Prop),
(forall a, slo <= a < shi -> apresent (w_H W) memc a) ->
acall_kept SEGS B lyc Sc W memc W memc slo shi Eo.
Proof.
intros lyc Sc W memc slo shi Eo Hp. unfold acall_kept.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros a _ _ H; exact H|]. intros a Ha; exact (Hp a Ha).
Qed.
Lemma dk_kept_trans : forall lyc Sc W memc W1 memX W2 memY slo shi slo' shi' (Eo Eo' : Z -> Prop),
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
acall_kept SEGS B lyc Sc W memc W1 memX slo shi Eo ->
acall_kept SEGS B lyc Sc W1 memX W2 memY slo' shi' Eo' ->
slo <= slo' -> shi' <= shi -> (forall a, Eo' a -> Eo a) ->
acall_kept SEGS B lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros lyc Sc W memc W1 memX W2 memY slo shi slo' shi' Eo Eo' Hce Hshi (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hlo Hhi HE.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite L1 by lia. apply K1; assumption.
- intros b m i Hb Hi Hn. rewrite (L2 b m i Hb Hi) by (intros X; exact (Hn (HE _ X))). apply (K2 b m i Hb Hi Hn).
- intros a Hi Hno He. rewrite L3 by assumption. apply K3; assumption.
- intros cid pos a Hin Hr Hn. rewrite (L4 cid pos a Hin Hr) by (intros X; exact (Hn (HE _ X))). apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply L5; [lia | intros [? ?]; apply Hw; lia |]. apply K5; assumption.
- intros a Ha. destruct (Z_lt_ge_dec a slo') as [H1|H1]; [|destruct (Z_lt_ge_dec a shi') as [H2|H2]].
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
+ apply L6. lia.
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
Qed.
Lemma dk_kept_step : forall lyc Sc W memc mdc memX memY slo shi (Eo Zs : Z -> Prop),
AR SEGS B lyc Sc W memc mdc ->
acall_kept SEGS B lyc Sc W memc W memX slo shi Eo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) memY a = aview SEGS (w_H W) memX a) ->
(forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
(forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
(forall a, Zs a -> in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> False) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> Zs a -> Eo a) ->
acall_kept SEGS B lyc Sc W memc W memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc memX memY slo shi Eo Zs HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | intros HZ; exact (Hw (HZw a HZ Ha))].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HZ; exact (Hn (HZb b m i Hb Hi HZ))].
- intros a Hi Hno He. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
rewrite Hkp; [apply K3; assumption | lia | intros HZ; exact (HZi a HZ Hi Hno He)].
- intros cid pos a Hin Hr Hn. destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
assert (Ha : 0 <= a < 2 ^ 64).
{ destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | exact Ha | intros HZ; exact (Hn (HZf cid pos a Hin Hr HZ))].
- intros a Ha Hw Hp. apply Hgr. apply K5; assumption.
- intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.
(* The written range Eo lies in the caller's side-stack frames (the frames of the call state Sc). *)
Definition dk_in_frames (lyc : alayout) (Sc : astate) (Eo : Z -> Prop) : Prop :=
forall a, Eo a -> exists cid pos, In (cid, pos) (frames Sc) /\
frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid.
Lemma dk_in_frames_range : forall lyc Sc cid pos q n,
In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= q -> q + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
dk_in_frames lyc Sc (fun a => q <= a < q + n).
Proof. intros lyc Sc cid pos q n Hin Hlo Hhi a Ha. exists cid, pos. split; [exact Hin | lia]. Qed.
Lemma dk_in_frames_or : forall lyc Sc (E1 E2 : Z -> Prop),
dk_in_frames lyc Sc E1 -> dk_in_frames lyc Sc E2 -> dk_in_frames lyc Sc (fun a => E1 a \/ E2 a).
Proof. intros lyc Sc E1 E2 H1 H2 a [Ha|Ha]; [exact (H1 a Ha) | exact (H2 a Ha)]. Qed.
(* One step of the walk keeps the caller's memory when every byte it may change is in the call's stack
   window, in the written range Eo, or in the function's own side-stack frame (NF), which is apart from the
   caller's. *)
Lemma dk_kept_run : forall lyc Sc W memc mdc memX memY slo shi (Eo NF Zs : Z -> Prop),
AR SEGS B lyc Sc W memc mdc ->
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
dk_in_frames lyc Sc Eo ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> NF (b + i) -> False) ->
(forall a, NF a -> in_img SEGS a -> False) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> NF a -> False) ->
(forall a, NF a -> a < alloc_ceiling) ->
(forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ NF a) ->
acall_kept SEGS B lyc Sc W memc W memX slo shi Eo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) memY a = aview SEGS (w_H W) memX a) ->
(forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
acall_kept SEGS B lyc Sc W memc W memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc memX memY slo shi Eo NF Zs HAR Hce Hshi HEf HNb HNi HNf HNc HZ KP Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (dk_kept_step lyc Sc W memc mdc memX memY slo shi Eo Zs HAR KP Hkp Hgr).
- intros a Ha Hc. destruct (HZ a Ha) as [Hw | [Ho | Hn]]; [exact Hw | | pose proof (HNc a Hn); lia].
destruct (HEf a Ho) as (c0 & p0 & Hin0 & Hr0).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c0 p0 HAR Hin0) as (_ & Fce & _). lia.
- intros b m i Hb Hi Ha. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
destruct (HZ _ Ha) as [Hw | [Ho | Hn]]; [lia | exact Ho | exfalso; exact (HNb b m i Hb Hi Hn)].
- intros a Ha Hi _ _. pose proof (pa_segs_low a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hr. unfold kLowMemEnd in Hlow.
destruct (HZ a Ha) as [Hw | [Ho | Hn]]; [lia | | exact (HNi a Hn Hi)].
destruct (HEf a Ho) as (c0 & p0 & Hin0 & Hr0).
pose proof (frm_off_imgP B lyc Sc W memc mdc c0 p0 HAR Hin0) as Hoff. lia.
- intros cid pos a Hin Hr Ha. destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4096 & Gce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
destruct (HZ a Ha) as [Hw | [Ho | Hn]]; [|exact Ho | exfalso; exact (HNf cid pos a Hin Hr Hn)].
exfalso. destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.
(* The caller's bytes and their shadow bytes outside the written range are those at entry. *)
Lemma dk_kept_frame_byte : forall lyc Sc W memc memX slo shi (Eo : Z -> Prop) cid pos a,
acall_kept SEGS B lyc Sc W memc W memX slo shi Eo -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ Eo a ->
aview SEGS (w_H W) memX a = aview SEGS (w_H W) memc a.
Proof.
intros lyc Sc W memc memX slo shi Eo cid pos a (_ & _ & _ & K4 & _) Hin Ha Hn.
apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hn].
Qed.
Lemma dk_kept_ra : forall lyc Sc W memc mdc memX slo shi (Eo : Z -> Prop) cid pos a n,
AR SEGS B lyc Sc W memc mdc ->
acall_kept SEGS B lyc Sc W memc W memX slo shi Eo -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= a -> a + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall x, a <= x < a + n -> ~ Eo (shadow_addr x)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n ->
range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF a n.
Proof.
intros lyc Sc W memc mdc memX slo shi Eo cid pos a n HAR (_ & _ & _ & K4 & _) Hin Hlo Hhi Hn HRA x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hal & _ & _ & _).
destruct (dk_frame_al64 lyc Sc W memc mdc cid pos HAR Hin) as (_ & Hfs64 & Hfs).
set (F := frame_addr lyc cid pos) in *.
assert (HR : in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr F, fs_frame_bytes cid / 8)).
{ unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D32. rewrite Hal, Z.add_0_r in D32. rewrite D32. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
assert (HS8 : fs_frame_bytes cid mod 8 = 0).
{ pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D64. rewrite Hfs64, Z.add_0_r in D64. rewrite D64. replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia. apply Z_mod_mult. }
split.
- assert (F / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
- assert (x / 8 < F / 8 + fs_frame_bytes cid / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite <- Hs. apply (K4 cid pos _ Hin (or_intror HR)). unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). apply Hn. exact Hx.
Qed.
(* The bytes of the function's own side-stack frame of class cid (fs_frame_bytes cid bytes at F), its shadow
   bytes and its flag byte FL. *)
Definition dk_nf (cid F FL a : Z) : Prop :=
(F <= a < F + fs_frame_bytes cid) \/
(SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + fs_frame_bytes cid / 8) \/ a = FL.
Lemma dk_awr_cons : forall STK sp0 FP bl0 blc ly own x a,
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H|[H|[H|(cid & pos & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.
Lemma dk_own_sep : forall ly S W mem md c p Sc c' p',
AR SEGS B ly S W mem md -> frames S = (c, p) :: frames Sc -> In (c', p') (frames Sc) ->
zdisjoint (frame_rng ly (c, p)) (frame_rng ly (c', p')).
Proof.
intros ly S W mem md c p Sc c' p' HAR Hfr Hin.
destruct (in_split _ _ Hin) as (l2 & l3 & E). rewrite E in Hfr.
exact (sep_frames_pos SEGS B LAWS ly S W mem md (c, p) (c', p') [] l2 l3 HAR Hfr).
Qed.
(* The own frame is apart from everything acall_kept keeps: the caller's blocks, the image, the caller's
   frames and their shadow bytes; and it lies below the allocation ceiling. *)
Lemma dk_nf_sep : forall lyc Sc S2 W mem2 md2 cid fpos F FL,
AR SEGS B lyc S2 W mem2 md2 ->
frames S2 = (cid, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos ->
frame_flag_lawP SEGS B ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> dk_nf cid F FL (b + i) -> False) /\
(forall a, dk_nf cid F FL a -> in_img SEGS a -> False) /\
(forall c pos a, In (c, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (c, pos)) \/ in_zr a (shadow_addr (frame_addr lyc c pos), fs_frame_bytes c / 8)) -> dk_nf cid F FL a -> False) /\
(forall a, dk_nf cid F FL a -> a < alloc_ceiling).
Proof.
intros lyc Sc S2 W mem2 md2 cid fpos F FL HAR2 Hfrs Eab -> -> FFL. unfold dk_nf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (cid, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid fpos HAR2 Hfin) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP B _ _ _ _ _ cid fpos HAR2 Hfin) as HFimg.
destruct (FFL _ _ _ _ _ cid fpos HAR2 Hfin) as (_ & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
destruct (dk_frame_al64 _ _ _ _ _ cid fpos HAR2 Hfin) as (HF64 & HFs64 & HFs).
set (F := frame_addr lyc cid fpos) in *. set (FL := flag_addr lyc cid fpos) in *.
set (fs := fs_frame_bytes cid) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. pose proof (Z.div_mod fs 64 ltac:(lia)) as DS.
rewrite HF64, Z.add_0_r in DF. rewrite HFs64, Z.add_0_r in DS.
assert (EF : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (ES : fs / 8 = 8 * (fs / 64)) by (rewrite DS at 1; replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : 0 <= F / 64) by (apply Z.div_pos; lia).
assert (HFS : SHADOW_OFF + F / 8 + fs / 8 <= kHighShadowEnd /\ kLowShadowBeg < SHADOW_OFF + F / 8).
{ unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg. lia. }
unfold kHighShadowEnd, kLowShadowBeg, SHADOW_OFF in HFS.
split; [|split; [|split]].
- intros b m i Hb Hi Hn. rewrite <- Eab in Hb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & Hb4096 & Hbce & Hbapp & Hbown & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid fpos HAR2 Hb Hfin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F fs in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia |].
exact (proj2 (Hbown (b + i) ltac:(lia)) ltac:(rewrite Hn; exact HFLown)).
- intros a Hn Hi. pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | subst a; exact (HFLimg Hi)].
- intros c pos a Hin Hr Hn.
assert (Hin2 : In (c, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
destruct (al_frames _ _ LAWS _ _ _ _ _ c pos HAR2 Hin2) as (HGal & HGapp & HGpres & HGSpres).
destruct (dk_frame_al64 _ _ _ _ _ c pos HAR2 Hin2) as (HG64 & HGs64 & HGs).
pose proof (dk_own_sep _ _ _ _ _ cid fpos Sc c pos HAR2 Hfrs Hin) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F fs in Hd.
set (G := frame_addr lyc c pos) in *. set (gs := fs_frame_bytes c) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
destruct Hn as [Hn|[Hn|Hn]].
+ destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end G gs ltac:(lia)) as Hse. unfold shadow_addr in Hse, Hr. fold G in Hr.
assert ((G + gs) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). assert (0 <= G / 8) by (apply Z.div_pos; lia).
change (2 ^ 47 / 8) with (2 ^ 44) in *. unfold SHADOW_OFF in Hr, Hse. lia.
+ destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [unfold SHADOW_OFF in Hn; lia|].
unfold shadow_addr in Hr. fold G in Hr.
pose proof (Z.div_mod G 64 ltac:(lia)) as DG. pose proof (Z.div_mod gs 64 ltac:(lia)) as DGS.
rewrite HG64, Z.add_0_r in DG. rewrite HGs64, Z.add_0_r in DGS.
assert (EG : G / 8 = 8 * (G / 64)) by (rewrite DG at 1; replace (64 * (G / 64)) with ((8 * (G / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (EGS : gs / 8 = 8 * (gs / 64)) by (rewrite DGS at 1; replace (64 * (gs / 64)) with ((8 * (gs / 64)) * 8) by lia; apply Z.div_mul; lia).
unfold SHADOW_OFF in Hn, Hr. lia.
+ subst a. destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
* exact (proj2 (HGpres FL ltac:(fold G gs; lia)) HFLown).
* unfold shadow_addr in Hr. fold G in Hr.
exact (proj2 (HGSpres (FL - shadow_addr G) ltac:(unfold shadow_addr; fold G; lia))
ltac:(replace (shadow_addr G + (FL - shadow_addr G)) with FL by lia; exact HFLown)).
- intros a [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | lia].
Qed.
(* One step of the walk keeps the caller's memory when each byte it may change is in the call's stack
   window, in the written range Eo or in the own frame of class cid. *)
Lemma dk_kept_own : forall lyc Sc S2 W memc mdc mem2 md2 memX memY slo shi cid fpos F FL (Eo Zs : Z -> Prop),
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W mem2 md2 ->
frames S2 = (cid, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos -> frame_flag_lawP SEGS B ->
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
dk_in_frames lyc Sc Eo ->
(forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ dk_nf cid F FL a) ->
acall_kept SEGS B lyc Sc W memc W memX slo shi Eo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) memY a = aview SEGS (w_H W) memX a) ->
(forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
acall_kept SEGS B lyc Sc W memc W memY slo shi Eo.
Proof.
intros lyc Sc S2 W memc mdc mem2 md2 memX memY slo shi cid fpos F FL Eo Zs HAR HAR2 Hfrs Eab EF EFL FFL Hce Hshi HEf HZ KP Hkp Hgr.
destruct (dk_nf_sep lyc Sc S2 W mem2 md2 cid fpos F FL HAR2 Hfrs Eab EF EFL FFL) as (N1 & N2 & N3 & N4).
exact (dk_kept_run lyc Sc W memc mdc memX memY slo shi Eo (dk_nf cid F FL) Zs HAR Hce Hshi HEf N1 N2 N3 N4 HZ KP Hkp Hgr).
Qed.
(* A callee called while the walk owns a side-stack frame: its acall_kept is stated at its call state (ly2, S2),
   whose frames and blocks contain the caller's (Sc), and its written range Eo' lies in the walk's Eo or in the
   own frame NF (given by its separation facts, as dk_nf_sep gives them). *)
Lemma dk_kept_trans_nf : forall lyc Sc ly2 S2 W memc W1 memX W2 memY slo shi slo' shi' (Eo Eo' NF : Z -> Prop),
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
(forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
(forall f, In f (frames Sc) -> In f (frames S2)) ->
(forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> NF (b + i) -> False) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> NF a -> False) ->
acall_kept SEGS B lyc Sc W memc W1 memX slo shi Eo ->
acall_kept SEGS B ly2 S2 W1 memX W2 memY slo' shi' Eo' ->
slo <= slo' -> shi' <= shi -> (forall a, Eo' a -> Eo a \/ NF a) ->
acall_kept SEGS B lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros lyc Sc ly2 S2 W memc W1 memX W2 memY slo shi slo' shi' Eo Eo' NF Hce Hshi Hfa Hfr Hbl HNb HNf
(K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hlo Hhi HE.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite L1 by lia. apply K1; assumption.
- intros b m i Hb Hi Hn. rewrite (L2 b m i (Hbl _ Hb) Hi)
by (intros X; destruct (HE _ X) as [Y|Y]; [exact (Hn Y) | exact (HNb b m i Hb Hi Y)]).
apply (K2 b m i Hb Hi Hn).
- intros a Hi Hno He. rewrite L3 by assumption. apply K3; assumption.
- intros cid pos a Hin Hr Hn.
assert (Hr2 : in_zr a (frame_rng ly2 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8))
by (unfold frame_rng in *; cbn [fst snd] in *; rewrite Hfa; exact Hr).
rewrite (L4 cid pos a (Hfr _ Hin) Hr2)
by (intros X; destruct (HE _ X) as [Y|Y]; [exact (Hn Y) | exact (HNf cid pos a Hin Hr Y)]).
apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply L5; [lia | intros [? ?]; apply Hw; lia |]. apply K5; assumption.
- intros a Ha. destruct (Z_lt_ge_dec a slo') as [H1|H1]; [|destruct (Z_lt_ge_dec a shi') as [H2|H2]].
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
+ apply L6. lia.
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
Qed.
End c.
End b.
