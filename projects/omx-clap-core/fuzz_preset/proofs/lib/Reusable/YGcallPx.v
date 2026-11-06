(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): ecall_pre_at_xR and ajournal_x_shd_writeR are
   ecall_pre_at_x and ajournal_x_shd_write over a journal at any world relation R (YCbqG.ajournal_xR; the steps keep
   the world, so the journal's world conjunct passes through unchanged); the old names keep their statements and are
   the instances at wle. aj_poison_at_xR, aj_unpoison_at_xR, aj_poison_xR and aj_unpoison_xR are the four call rules
   over a journal at a reflexive and transitive R (binders first; no law of R is read); the old names are their
   instances at wle. *)
(* Theorem Labs, 2026-10: the harness's two shadow calls, __asan_poison_memory_region and
   __asan_unpoison_memory_region, GENERIC over the allocator invariant ARx of YCbqG.v (Section Variables
   segs B PST ARx) and a head length hd (preset instantiates hd := cf_head, which is 16 at CfParams_preset).
   No allocator instance, no image class, no address and no ledger is named here.

   1. THE TEXTS (Section px): apoison_realizes_x / aunpoison_realizes_x are h-rw-man-5's cf contracts
      apoison_realizes_cf / aunpoison_realizes_cf (YGcfHp.v:127-153, h-mani-a8 a17a5c82661) word for word with
      ARcf segs B -> ARx, cf_head -> hd, cf_pc_poison / cf_pc_unpoison -> the parameter pc, ecall_pre_cf ->
      ecall_pre_x (FCiface.v, the x twin of YG0d.v:278-284), and ONE difference: the size premise is
      `hd <= req_size n`, where YGcfHp.v:131 / :145 has `cf_head < req_size n`, so that a harness block of user
      size 0 (one head of 16 bytes and nothing after it) is covered; PresetS1 asked h-rw-man-5 to relax the cf
      texts to `<=`. Until that lands the walks take these texts as STAND-INs for the relaxed cf texts;
      YGcallPcf.v proves each generic text implies its cf text (the cf text is the generic one with the size
      premise narrowed), and becomes the equation by reflexivity once the cf texts read `<=`. Their shape is
      port-fm's (FMupoison.v at
      origin/cold/port-fm-poison 52efd1c871f: ARU_poison_step :263, ARU_unpoison_step :333): a poison of
      [p, p + hd) for p the base of a live block of more than hd bytes returns with ARx at p :: Hp and the head's
      hd / 8 shadow bytes 0xf7 (YGcfNames.shUserPoison); an unpoison of p in Hp returns with ARx at
      remove Z.eq_dec p Hp and those bytes 0. The post is cgif's aintrin_realizes (YG0d.v:318-336): W unchanged,
      the callee-saved registers kept, the model only materialized, every byte kept but the ESTACK window below
      sp and the head's shadow, the window present.

   2. THE CALL-SITE RULES (Section l): ecall_pre_at_x is cgif's ecall_pre_at (YCbq.v:1913) over ajournal_x.
      ajournal_x_shd_write is the journal step of a write to the shadow of a live block plus a stack window:
      the shadow bytes are runtime-owned and not application addresses, so YCbqG.v's ajournal_x_after_write
      (:246) does not cover them; every journal clause is re-proved from the address bands (the shadow lies in
      [SHADOW_OFF, kHighShadowEnd), below alloc_ceiling, above the image, off every block, frame and extra
      range). aj_poison_at_x / aj_unpoison_at_x are cgif's aj_intrin_at (YCbq.v:1955) shape; aj_poison_x /
      aj_unpoison_x are the same from a symbolic state, as cgif's aj_free (:2111) over aj_free_at.
      The journal keeps its layout, state and event count k; only its ghost set moves. The rules restate the
      text's shadow fact per address (shd_idx_g): for b <= g < b + hd the byte at shadow_addr g.

   SK (the sink-head class of YCbqG's ajournal_x) is passed explicitly at every ajournal_x, so no global instance
   (YI5b.v's src0_sink_head) can be inferred for it.

   Numerals: 8 is LENGTH (the shadow granule), 16 and 32 are DERIVED (the block and frame alignments of the
   blocks / frames laws), 2 and 4 are DERIVED (16 / 8 and 32 / 8), 10 / 11 / 1 / 2 / 3 / 4 are register indices
   (WORD), 0 is WORD (the shadow value of an addressable granule), 2 ^ 64 is WORD. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section px. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* the head length a0's block hides; LENGTH, a parameter (preset: cf_head) *)
Variable hd : Z.

(* The shadow addresses lie in [SHADOW_OFF, kHighShadowEnd), which no application address reaches. *)
Lemma shd_not_app : forall a, SHADOW_OFF <= a < kHighShadowEnd -> ~ app_addr a.
Proof.
intros a Ha Happ. unfold app_addr, ASAN_CEIL, YG0f.kLowShadowBeg, YG0f.kHighMemBeg in Happ.
unfold SHADOW_OFF, kHighShadowEnd in Ha. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 1. The texts: YGcfHp.v:127-153 over ARx, hd and pc, with `hd <= req_size n` (YGcallPcf.v). *)
Definition apoison_realizes_x (pc : Z) : Prop :=
forall ly S Hp (W : world segs) regs mem md p n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 p -> getr regs 11 = w64 hd -> hd mod 8 = 0 ->
In (p, n) (ablocks B ly S) -> hd <= req_size n ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S (p :: Hp) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < hd / 8 -> aview segs (w_H W) mem' (shadow_addr p + i) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ (shadow_addr p <= a < shadow_addr p + hd / 8) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

Definition aunpoison_realizes_x (pc : Z) : Prop :=
forall ly S Hp (W : world segs) regs mem md p n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 p -> getr regs 11 = w64 hd -> hd mod 8 = 0 -> In p Hp ->
In (p, n) (ablocks B ly S) -> hd <= req_size n ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S (remove Z.eq_dec p Hp) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < hd / 8 -> aview segs (w_H W) mem' (shadow_addr p + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ (shadow_addr p <= a < shadow_addr p + hd / 8) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* The shadow byte of an address g of the head is the text's byte (g - b) / 8. *)
Lemma shd_idx_g : forall b g, b mod 8 = 0 -> hd mod 8 = 0 -> b <= g < b + hd ->
shadow_addr g = shadow_addr b + (g - b) / 8 /\ 0 <= (g - b) / 8 < hd / 8.
Proof.
intros b g Hb Hh Hg.
apply Z.mod_divide in Hb as [x Hx]; [|lia]. apply Z.mod_divide in Hh as [c Hc]; [|lia].
assert (Eg : g / 8 = x + (g - x * 8) / 8) by (rewrite <- Z.div_add_l by lia; f_equal; lia).
assert (Ec : hd / 8 = c) by (rewrite Hc; apply Z.div_mul; lia).
rewrite Ec. rewrite Hx in Hg |- *. split.
- unfold shadow_addr. rewrite Eg, Z.div_mul by lia. lia.
- split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

(* The unpoison post's shadow fact in cgif's range_addressable form (YG0v.v:33). *)
Lemma shd0_range_addressable : forall (rd : reader) b,
(forall g, b <= g < b + hd -> rd (shadow_addr g) = Some 0) -> range_addressable rd SHADOW_OFF b hd.
Proof. intros rd b H x Hx. exists 0. split; [exact (H x Hx) | left; reflexivity]. Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The call-site rules.                                                        *)
Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* cgif's ecall_pre_at (YCbq.v:1911) over a journal at any world relation R (the world conjunct is not read). *)
Lemma ecall_pre_at_xR : forall (R : world segs -> world segs -> Prop)
STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc (o : Z),
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
ecall_pre_x segs B ARx lyc Sc Hpc W regsc memc mdc.
Proof.
intros R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc o HJ Hsp Hal Hneg Hbud Hra Hgp Htp.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop). pose proof (ajxR_qt HJ) as HQT.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
split; [exact HAR|]. split; [exact Hra|]. split; [rewrite Hsp, Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp; zlia|]. split; [rewrite Eshi, Hsp; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp in Ha; zlia|]. split; [exact Hgp | exact Htp].
Qed.

(* cgif's ecall_pre_at (YCbq.v:1913) over ajournal_x. *)
Lemma ecall_pre_at_x : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc (o : Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
ecall_pre_x segs B ARx lyc Sc Hpc W regsc memc mdc.
Proof. exact (ecall_pre_at_xR (@wle segs)). Qed.

(* The journal step of a call that writes only the shadow of the first hd bytes of a live block and a stack
   window [lo, hi) inside the journal's own stack, leaves the window present, and leaves the invariant at a
   new ghost set Hp'; over a journal at any world relation R (the write keeps the world). *)
Lemma ajournal_x_shd_writeR : forall (R : world segs -> world segs -> Prop)
STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Hp' b n lo hi,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
sp0 - STK <= lo -> hi <= sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, lo <= a < hi -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
ARx lyc Sc Hp' Wc memc' mdc' ->
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hp' Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Hp' b n lo hi
HJ Hin Hhd Hlo Hhi Heqw Hgr Hsame HAR'.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc Wc memc mdc b n HAR Hin) as (Hb16 & Hb4k & Hbc & _ & _ & _).
(* b is 16-aligned (DERIVED from the blocks law), so its shadow starts at SHADOW_OFF + 2 * (b / 16). *)
assert (Hq : b = 16 * (b / 16)) by (pose proof (Z.div_mod b 16 ltac:(lia)); lia).
assert (Esb : shadow_addr b = SHADOW_OFF + 2 * (b / 16)).
{ unfold shadow_addr. rewrite Hq at 1. replace (16 * (b / 16)) with (2 * (b / 16) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.mul_div_le hd 8 ltac:(lia)) as Hd8.
assert (HSR : forall a, shadow_addr b <= a < shadow_addr b + hd / 8 -> SHADOW_OFF <= a < kHighShadowEnd /\ a < alloc_ceiling).
{ intros a Ha. rewrite Esb in Ha. unfold SHADOW_OFF in Ha |- *. zlia. }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia | zlia |].
intros Hr. pose proof (HSR a Hr). zlia. }
split.
{ intros p m i H1 H2 Hi Hnf. rewrite <- (F2 p m i H1 H2 Hi Hnf).
destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc Wc memc mdc p m HAR H2) as (_ & Hp4k & Hpce & [Hh1 Hh2] & _ & _).
pose proof (in_app_addr _ _ (p + i) (conj Hh1 Hh2) ltac:(zlia)) as Happ.
apply Heqw; [zlia | zlia |].
intros Hr. exact (shd_not_app (p + i) (proj1 (HSR _ Hr)) Happ). }
split.
{ intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia | zlia |].
intros Hr. pose proof (HSR a Hr) as Hsr. unfold SHADOW_OFF in Hsr. zlia. }
split.
{ intros cid pos a Hinf Hr Hnf. rewrite <- (F4 cid pos a Hinf Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hinf).
destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (alx_frames segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf32 & _ & _ & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as Hfd8.
(* a frame is 32-aligned (DERIVED from the frames law), so its shadow starts at SHADOW_OFF + 4 * (f / 32). *)
assert (Hqf : frame_addr lyc cid pos = 32 * (frame_addr lyc cid pos / 32))
by (pose proof (Z.div_mod (frame_addr lyc cid pos) 32 ltac:(lia)); lia).
assert (Esf : shadow_addr (frame_addr lyc cid pos) = SHADOW_OFF + 4 * (frame_addr lyc cid pos / 32)).
{ unfold shadow_addr. rewrite Hqf at 1.
replace (32 * (frame_addr lyc cid pos / 32)) with (4 * (frame_addr lyc cid pos / 32) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity. }
pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b n cid pos HAR Hin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- Efa in Hr.
apply Heqw.
- destruct Hr as [Hr|Hr]; [zlia|]. rewrite Esf in Hr. unfold SHADOW_OFF in Hr. zlia.
- destruct Hr as [Hr|Hr]; [zlia|]. rewrite Esf in Hr. unfold SHADOW_OFF in Hr. zlia.
- intros Hs. destruct Hr as [Hr|Hr].
+ exact (shd_not_app a (proj1 (HSR a Hs)) (in_app_addr _ _ a Hfh Hr)).
+ rewrite Esb in Hs. rewrite Esf in Hr. unfold SHADOW_OFF in Hs, Hr. zlia. }
split; [exact Hgone|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a lo) as [L1|L1]; [|destruct (Z_lt_le_dec a hi) as [L2|L2]; [apply Hgr; lia|]];
(eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia
| apply Heqw; [zlia | zlia | intros Hr; pose proof (HSR a Hr); zlia] | apply Hpres; exact Ha]). }
split; [exact Hstatic|]. split; [|split; [exact HQT | exact (ajxR_wild HJ)]].
{ intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (alx_extra segs B ARx LAWS lyc Sc Hpc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by zlia.
apply Heqw; [exact Ha64 | |].
- intros Hw. apply Xs. rewrite Eslo, Eshi. zlia.
- intros Hr. exact (Xsh (proj1 (HSR a Hr))). }
Qed.

(* The journal step of a call that writes only the shadow of the first hd bytes of a live block and a stack
   window [lo, hi) inside the journal's own stack, leaves the window present, and leaves the invariant at a
   new ghost set Hp'. *)
Lemma ajournal_x_shd_write : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Hp' b n lo hi,
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
sp0 - STK <= lo -> hi <= sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, lo <= a < hi -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
ARx lyc Sc Hp' Wc memc' mdc' ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hp' Wc memc' mdc' k.
Proof. exact (ajournal_x_shd_writeR (@wle segs)). Qed.

(* aj_poison_at_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_poison_at_x is its case R := wle *)
Lemma aj_poison_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, apoison_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AP W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o raw
HJ Ha0 Ha1 H8 Hin Hhd Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & _).
destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc W memT mdc b n HAR Hin) as (Hb16 & _).
assert (Hb8 : b mod 8 = 0) by (apply Z.mod_divide in Hb16 as [x Hx]; [|lia]; rewrite Hx;
replace (x * 16) with ((x * 2) * 8) by lia; apply Z.mod_mul; lia).
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ eapply (ecall_pre_at_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k regsT o); try eassumption.
rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AP lyc Sc Hpc W regsT memT mdc b n HPRE Ha0 Ha1 H8 Hin Hhd). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hsh & Hfr & Hpres2 & _).
rewrite Hsp' in Hfr, Hpres2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_shd_writeR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2 (b :: Hpc)
b n (sp0 + o - ESTACK) (sp0 + o) HJ Hin ltac:(lia)); [zlia | zlia | exact Hfr | exact Hpres2 | exact Hsame | exact HAR2]. }
split; [exact HP|]. split; [|split; [exact Hfr | exact Hpres2]].
intros g Hg. destruct (shd_idx_g b g Hb8 H8 Hg) as [Eg Hi]. rewrite Eg. exact (Hsh _ Hi).
Qed.

(* __asan_poison_memory_region(b, hd) at a call site: cgif's aj_intrin_at (YCbq.v:1955) shape. *)
Lemma aj_poison_at_x : forall pc, apoison_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof. exact (aj_poison_at_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_unpoison_at_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_unpoison_at_x is its case R := wle *)
Lemma aj_unpoison_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, aunpoison_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AU W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o raw
HJ Ha0 Ha1 H8 Hhp Hin Hhd Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & _).
destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc W memT mdc b n HAR Hin) as (Hb16 & _).
assert (Hb8 : b mod 8 = 0) by (apply Z.mod_divide in Hb16 as [x Hx]; [|lia]; rewrite Hx;
replace (x * 16) with ((x * 2) * 8) by lia; apply Z.mod_mul; lia).
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ eapply (ecall_pre_at_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k regsT o); try eassumption.
rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AU lyc Sc Hpc W regsT memT mdc b n HPRE Ha0 Ha1 H8 Hhp Hin Hhd). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hsh & Hfr & Hpres2 & _).
rewrite Hsp' in Hfr, Hpres2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_shd_writeR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2 (remove Z.eq_dec b Hpc)
b n (sp0 + o - ESTACK) (sp0 + o) HJ Hin ltac:(lia)); [zlia | zlia | exact Hfr | exact Hpres2 | exact Hsame | exact HAR2]. }
split; [exact HP|]. split; [|split; [exact Hfr | exact Hpres2]].
intros g Hg. destruct (shd_idx_g b g Hb8 H8 Hg) as [Eg Hi]. rewrite Eg. exact (Hsh _ Hi).
Qed.

(* __asan_unpoison_memory_region(b, hd) at a call site, b in the ghost set. *)
Lemma aj_unpoison_at_x : forall pc, aunpoison_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof. exact (aj_unpoison_at_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_poison_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_poison_x is its case R := wle *)
Lemma aj_poison_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, apoison_realizes_x pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AP W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o spw raw
HS Hpc' Hrv HJ Ha0 Ha1 H8 Hin Hhd Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof (ajxR_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpc'.
eapply (aj_poison_at_xR R R_refl R_trans); eassumption.
Qed.

(* The same two calls from a symbolic state at the callee's entry (cgif's aj_free, YCbq.v:2111, over aj_free_at). *)
Lemma aj_poison_x : forall pc, apoison_realizes_x pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof. exact (aj_poison_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_unpoison_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_unpoison_x is its case R := wle *)
Lemma aj_unpoison_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, aunpoison_realizes_x pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AU W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o spw raw
HS Hpc' Hrv HJ Ha0 Ha1 H8 Hhp Hin Hhd Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof (ajxR_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpc'.
eapply (aj_unpoison_at_xR R R_refl R_trans); eassumption.
Qed.

Lemma aj_unpoison_x : forall pc, aunpoison_realizes_x pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof. exact (aj_unpoison_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End px.

(* A predicate P on the layout and the allocator state, conjoined to the allocator relation, lifts both texts:
   poison and unpoison keep ly and S, so P passes from the pre to the post unchanged. Use: a walk whose relation is
   ARx' := fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S gets its text at ARx' from the text at ARx. *)
Lemma apoison_realizes_x_conj : forall {fx : YK11.FPState} segs B ARx hd (P : alayout -> astate -> Prop) pc,
apoison_realizes_x segs B ARx hd pc ->
apoison_realizes_x segs B (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S) hd pc.
Proof.
intros fx segs B ARx hd P pc H ly S Hp W regs mem md p n ((HAR & HP) & Hpre) Ha0 Ha1 H8 Hin Hn.
eapply SRr_mono; [exact (H ly S Hp W regs mem md p n (conj HAR Hpre) Ha0 Ha1 H8 Hin Hn)|].
cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & Hc & HAR' & Rest).
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [exact (conj HAR' HP) | exact Rest].
Qed.

Lemma aunpoison_realizes_x_conj : forall {fx : YK11.FPState} segs B ARx hd (P : alayout -> astate -> Prop) pc,
aunpoison_realizes_x segs B ARx hd pc ->
aunpoison_realizes_x segs B (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S) hd pc.
Proof.
intros fx segs B ARx hd P pc H ly S Hp W regs mem md p n ((HAR & HP) & Hpre) Ha0 Ha1 H8 Hhp Hin Hn.
eapply SRr_mono; [exact (H ly S Hp W regs mem md p n (conj HAR Hpre) Ha0 Ha1 H8 Hhp Hin Hn)|].
cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & Hc & HAR' & Rest).
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [exact (conj HAR' HP) | exact Rest].
Qed.
