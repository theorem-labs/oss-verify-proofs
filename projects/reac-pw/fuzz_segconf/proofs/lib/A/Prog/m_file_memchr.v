(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 75 of its 125 lines of code are new or changed and 2912 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A): the journal step of a call of the memchr wrapper (0x43a3c), for m_file's
   two sites 0x862d4 (']') and 0x86344 ('='). The wrapper's contract (interface row 20, as the image-A owner confirmed it
   16:49Z) is lib/Rt/MemchrDef.v's amemchr_realizesM at musl memchr's constant window SegInstA.memchr_loA .. hiA;
   amemchr_realizes (rom_view) and amemchr_realizesM (consts_view lo hi) are the one shape amemchr_ro below, with
   the read-only premise RO a parameter. The step is fuzz_segconf lib/Reusable/YCbq.v's aj_bcmp_at (lines
   2444-2492) with bcmp's 2 * ESTACK window replaced by memchr's ESTACK and its result by memchr's first_byte.
   The window's consts_view at a call comes from arodata_okP and the image fact memchr_rom_fact (a Section
   hypothesis of the walk; the close discharges it). The KEYA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* musl memchr's constant window in image A is SegInstA.memchr_loA .. memchr_hiA (0x10350 .. 0x10370): memchr at
   0x9a2f8 loads two 8-byte .rodata words, 0x9a354 `ld a3,24(a3)` from 0x10368 and 0x9a35c `ld a4,-8(a4)` from
   0x10350 (this lane's reading of `neutral_dis.py reac-pw/asan/fuzz_segconf 0x9a2f8`, image sha256 48c5355bdacb,
   agrees). The image fact: the window is read-only image bytes, no runtime-owned static and not the errno cell. *)
Definition memchr_rom_fact (segs : list Segment) (B : asyms) : Prop :=
forall a, SegInstA.memchr_loA <= a < SegInstA.memchr_hiA ->
in_rom segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* MemchrDef's two texts, with the read-only premise as the parameter RO *)
Definition amemchr_ro (RO : world segs -> (word -> option byte) -> Prop) (pc : Z) : Prop :=
forall ly S W regs mem md x c n,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
RO W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Lemma amemchr_ro_of_realizes : forall pc, amemchr_realizes segs B pc -> amemchr_ro (rom_view segs) pc.
Proof. intros pc H. exact H. Qed.
Lemma amemchr_ro_of_realizesM : forall lo hi pc, amemchr_realizesM segs B lo hi pc -> amemchr_ro (consts_view segs lo hi) pc.
Proof. intros lo hi pc H. exact H. Qed.
(* the window's read-only view at any state, from arodata_okP and the image fact *)
Lemma memchr_consts_view : forall RLO RHI (W : world segs) mem,
memchr_rom_fact segs B -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
consts_view segs SegInstA.memchr_loA SegInstA.memchr_hiA W mem.
Proof.
intros RLO RHI W mem MC HR a Ha. destruct (MC a Ha) as (Hrom & Ho & He).
apply HR; [left; exact Hrom | exact Ho | exact He].
Qed.

(* the call as a journal step: the entry's window is [sp - ESTACK, sp), inside the caller's STK *)
Lemma aj_memchr_at : forall RO pc, amemchr_ro RO pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> amem_range x n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
RO W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 kk,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
first_byte segs W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros RO pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx HRO.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsx Hmx Hrx Hhx HRO). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & (kk & Hfb & Hres) & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, kk.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hfb|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
(* the same step for the row-20 hypothesis form, amemchr_realizesM at memchr_loA .. memchr_hiA, its read-only
   premise from arodata_okP and the image fact *)
Lemma aj_memchr_atM : forall pc RLO RHI,
amemchr_realizesM segs B SegInstA.memchr_loA SegInstA.memchr_hiA pc -> memchr_rom_fact segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> amem_range x n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 kk,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
first_byte segs W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc RLO RHI AM MC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx HRO.
exact (aj_memchr_at _ pc (amemchr_ro_of_realizesM _ _ pc AM) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
  x c n o raw HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx
  (memchr_consts_view RLO RHI W memT MC HRO)).
Qed.
End e.
End c.
