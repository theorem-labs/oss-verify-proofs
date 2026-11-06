(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite fuzz_knock's image (YImgTop.IMG_LO, YImgTop.IMG_TOP = 0x5f3000, both knock ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Reusable/YCbq.v, with its module paths and module names changed; 986 of its 1333 lines of code are new or changed and 2813 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the journal lemmas rdp_aj_write_U, rdp_ecall_preU_k and rdp_aj_roU of
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_rd_pre_k.v (lines 494-584 at origin/ossv/recipes 09c6822d886), the
   frame law ARU_frame of lib/A/FMupoison.v (lines 166-187) and the post rt_post_roU of lib/A/FMH_Rt.v (lines 97-104)
   of the same tree, restated for a hole in the shadow of a real-stack frame in place of fuzz_manifest's user-poisoned
   heap granules; the chunk runners SRr_chain_tok_AJ / SRr_run_tok_AJ / SRr_run_to_tok_AJ / SRr_chain_AJ /
   SRr_run_AJ / SRr_run_to_AJ of lib/Reusable/YCbq.v (lines 2408-2546) restated with the journal over the unpoisoned
   memory. The rest is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgHole.v, with its module paths and module names changed; 117 of its 217 lines of code are new or changed and 1233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgCallsStr.v at fb8dd36cfd17 (its strncmp
   adapter hc_strncmp_at and its call-site lemma hc_strncmp_key_call); image B's callee address and call site only:
   the strncmp trampoline is 0x41c24 (A: 0x41ba4), the harness's `jal` is 0x8329c with the return address 0x832a0
   (A: 0x83190 / 0x83194), and the literal is 0x20f40 (A: 0x20f00), which is lib/AU/HPgImgB.v headamp_himg_B's
   hi_hkey. The contract is taken as the Section hypothesis STRNCMP at every float state (the donor states it at
   the Section's own float state); the string premises (hc_awrap_blk, hc_awrap_cstr), the read-only premise
   (hc_aro_of_arodata) and the frame lemmas (hc_core, hc_core_R, hc_ret_ok) are the donor's and are used as they
   stand: their texts name no image. Prefix hc_ -> hkn_ for the two lemmas restated here. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the CALL ADAPTER of the strncmp wrapper. Proves no function (kind: segment lemma).

   THE CALLEE. __interceptor_trampoline_strncmp 0x41c24 is the 4-byte jump to the wrapper ___interceptor_strncmp
   0x4270c. The wrapper compares the two strings byte by byte by musl strncmp 0x96078, up to the first index where
   the bytes differ or one of them is 0, or until n bytes are compared; then it checks that the bytes it read are
   marked usable in the shadow map, and returns musl's result. It uses at most 2 ESTACK bytes of stack below sp and
   writes no byte outside them. Its contract is reac-pw/fuzz_pin's text, lib/A/PPgWrap.v lines 82-133 (awrap_str,
   awrap_post, astrncmp_realizes), with aro_unowned of libreac/fuzz_identity lib/A/Rt/WrapRo.v
   line 24 (origin/ossv/recipes 2d2ff01bb6f2). No file this one Requires, directly or through another, defines
   those four names (lib/A/HPgWrap.v and lib/A/Rt/WrapRo.v do), so the Section below takes the contract at 0x41c24
   as the hypothesis STRNCMP, with the four definitions unfolded and beta-reduced word for word and quantified over
   the float state (only cfg_at reads it): the port of the wrapper's walk gives
   `fun fx' => astrncmp_realizes segs B 0x41c24` here. strncmp_model is lib/Spec/StrFun.v:157.

   THE CALL SITE (capstone over the unstripped twin): 0x8329c in LLVMFuzzerTestOneInput (fuzz_headamp.c:120, the
   key test of expect_of): `jal` 0x41c24, ra 0x832a0, a0 = s7 = the key (the body of entry m of the pod_ent table
   inside the pp block), a1 = 0x20f40 (auipc 0x83284 + addi 0x83288: the harness's "reac.headamp."), a2 = 13
   (0x8328c). The parse's own call of the same wrapper is a different lane's.

   WHAT EACH LEMMA GIVES:
   - hkn_strncmp_at: the call inside a caller's journal, at any sp = sp0 + o of that journal. The journal after the
     call is the caller's, at the same allocator state; every byte outside [sp0 + o - 2 ESTACK, sp0 + o) is kept;
     a0 = 0 exactly when strncmp_model's d = 0.
   - hkn_strncmp_key_call: the call at 0x8329c in the continuation form of lib/A/HPgCalls.v (hc_call): from hc_core
     at the call, the walk continues at 0x832a0 with hc_core again (the wrapper keeps the allocator state), the
     callee-saved registers, the I/O state, every byte outside [R - 2 ESTACK, R) as at the call, and a0 = 0 exactly
     when d = 0. The walk gets d and its meaning (d = 0 exactly when Pod/Headamp.v ha_prefix of the key is true)
     from lib/Prog/HeadCheck/PairFacts.v strncmp_prefix; this file does not restate it.
   The float state: the wrapper's post returns in a configuration of the float state the call is made at, so the
   continuation runs at the caller's own float state; the two binary32 bounds and image B's third one, which
   LLVMFuzzerTestOneInput sets before the call and reads after it, are kept.

   Section hypotheses: segs_low (the image lies below the shadow map: lib/Reusable/YCbq.v's ajournal_after_write
   asks it) and STRNCMP (the wrapper's contract at 0x41c24). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgCallsStr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== image B: the callee, the return address, the literal ======================================== *)
Definition B_STRNCMP : Z := 0x41c24.          (* __interceptor_trampoline_strncmp: `j` ___interceptor_strncmp 0x4270c *)
Definition RB_STRNCMP : Z := 0x832a0.         (* LLVMFuzzerTestOneInput's `jal` 0x8329c plus 4 *)
Definition B_HKEY : Z := 0x20f40.             (* the harness's "reac.headamp." *)

Lemma hkn_hkey_B : B_HKEY = hi_hkey headamp_himg_B.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* The strncmp wrapper's contract at image B's trampoline: reac-pw/fuzz_pin lib/A/PPgWrap.v:121-133
   `astrncmp_realizes segs B B_STRNCMP`, with awrap_str (PPgWrap.v:82-93), awrap_post
   (PPgWrap.v:98-106) and aro_unowned (libreac/fuzz_identity lib/A/Rt/WrapRo.v:24-26 at origin/ossv/recipes
   2d2ff01bb6f2) unfolded and beta-reduced, at every float state fx' (only cfg_at reads it). *)
Hypothesis STRNCMP : forall fx' : YK11.FPState,
forall ly S W regs mem md x y n (ls rs : list byte) (d : Z),
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 32 ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok segs W regs mem x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview segs (w_H W) mem a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok segs W regs mem y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview segs (w_H W) mem a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (@cfg_at fx' segs B_STRNCMP regs mem md)
(fun (W' : world segs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
 AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ======================================== the call inside a caller's journal ======================================== *)
Lemma hkn_strncmp_at :
forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (ls rs : list byte) (d o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memT) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok segs W regsT memT x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview segs (w_H W) memT) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview segs (w_H W) memT a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memT) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok segs W regsT memT y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview segs (w_H W) memT) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview segs (w_H W) memT a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) memT a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (cfg_at segs B_STRNCMP regsT memT mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ same_io mdc md2 /\
 (exists v : word, getr regs2 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n ls rs d o raw
HJ Ha0 Ha1 Ha2 Hn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hx Hy Hmx Hmy Hmd Hro.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg);
  [clear - Hbud Hes; lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT)
by (rewrite Eslo, Hsp'; clear - Hslo Hbud; lia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a).
{ intros a Ha. apply Hpres. rewrite Hsp' in Ha. clear - Ha Hneg Hbud. lia. }
eapply SRr_mono.
{ exact (STRNCMP fx lyc Sc W regsT memT mdc x y n ls rs d HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx Hy Hmx Hmy Hmd Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; clear - Ha Hneg Hbud Hes Hceil Hslo; zlia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [apply same_io_materialized; exact Hsame|].
split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ======================================== the harness's call at 0x8329c ======================================== *)
(* strncmp(key, "reac.headamp.", 13) in LLVMFuzzerTestOneInput (fuzz_headamp.c:120, the key test of expect_of), in
   hc_call's continuation form: the key a C string inside a live block, the literal the image's string at 0x20f40.
   The continuation runs at 0x832a0 at the caller's own float state, with hc_core at the call's allocator state
   again. *)
Lemma hkn_strncmp_key_call : forall RLO RHI (Q : world segs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R key p m d : Z) (kb : list byte),
hc_core segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RB_STRNCMP ->
getr regs 10 = w64 key -> getr regs 11 = w64 B_HKEY -> getr regs 12 = w64 13 ->
In (p, m) (ablocks B lyc Sc) -> p <= key -> key + Z.of_nat (length kb) + 1 <= p + req_size m ->
garr8 segs (mrestrict (w_H W) memc) key (hd_zbytes kb ++ [0]) ->
~ In (Z_to_bv 8 0) kb ->
hd_str_tail (aview segs (w_H W) memc) (key + Z.of_nat (length kb)) ->
hd_cstr segs (w_H W) memc B_HKEY (hd_zbytes Headamp.HA_PREFIX) ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) ->
StrFun.strncmp_model (kb ++ [Z_to_bv 8 0]) (Headamp.HA_PREFIX ++ [Z_to_bv 8 0]) 13 = Some d ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 hc_core segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> same_io mdc md2 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - 2 * ESTACK <= x < R) ->
  aview segs (w_H W) mem2 x = aview segs (w_H W) memc x) ->
 (exists v : word, getr regs2 10 = v /\ (v = w64 0 <-> d = 0)) ->
 SRr segs W (cfg_at segs RB_STRNCMP regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs B_STRNCMP regs memc mdc) Q.
Proof.
intros RLO RHI Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R key p m d kb
HC Hra Ha0 Ha1 Ha2 Hin Hpk Hke Hg Hnz Htl Hlit Hro Hmd K.
pose proof (hc_core_R segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC) as (HRc & _ & Hsp).
pose proof HC as (HJ & Hev & H2 & H3 & H4 & HRal & Hwin & HRs).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (Hsp0al & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hts : T_SEG_STK = 16384) by reflexivity.
pose proof asan_consts as (C1 & _).
assert (Hsp' : spZ regs = sp0 + (R - sp0)) by (rewrite Hsp; ring).
assert (Hal' : (R - sp0) mod 16 = 0) by (clear - HRal Hsp0al; Z.div_mod_to_equations; lia).
assert (Hneg : R - sp0 <= 0) by (clear - HRs; lia).
assert (Hbud : 2 * ESTACK - (R - sp0) <= STK) by (clear - Hwin Hes Hts; lia).
destruct (hc_awrap_blk segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (R - sp0) p m key kb
  HJ Hsp' Hneg Hbud Hin Hpk Hke Hg Hnz Htl) as (Hkey & Hk8).
assert (Hoff : hd_off_stack regs (2 * ESTACK) B_HKEY (Z.of_nat (length Headamp.HA_PREFIX) + 1)).
{ intros x Hx. rewrite Hsp. rewrite hc_prefix_len in Hx. unfold B_HKEY in Hx. clear - Hx HRc C1 Hes Hts. lia. }
destruct (hc_awrap_cstr segs segs_low W regs memc B_HKEY Headamp.HA_PREFIX Hlit Hoff) as (Hpre & Hp8).
eapply SRr_bind.
{ exact (hkn_strncmp_at W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k key B_HKEY 13 kb
    Headamp.HA_PREFIX d (R - sp0) (w64 RB_STRNCMP) HJ Ha0 Ha1 Ha2 ltac:(lia) Hsp' Hal' Hneg Hbud H3 H4 Hra
    ltac:(apply hc_ret_ok; unfold RB_STRNCMP; lia) Hkey Hpre Hk8 Hp8 Hmd
    (hc_aro_of_arodata segs B RLO RHI _ Hro)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hio & Hv & Hkeep & _).
apply (K regs2 mem2 md2).
- split; [exact HJ2|]. split; [exact Hev|].
  split; [rewrite <- H2; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H3; exact (HP 3 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H4; exact (HP 4 ltac:(unfold acallee_saved; lia))|].
  split; [exact HRal|]. split; [exact Hwin | exact HRs].
- exact HP.
- exact Hio.
- intros x Hx Hs. apply Hkeep; [exact Hx|]. replace (sp0 + (R - sp0)) with R by ring. exact Hs.
- exact Hv.
Qed.

End c.
End b.

Print Assumptions hkn_hkey_B.
Print Assumptions hkn_strncmp_at.
Print Assumptions hkn_strncmp_key_call.
