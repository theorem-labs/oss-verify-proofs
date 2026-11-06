(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of the ASan strcmp interceptor (and of the one-`j` trampoline
   __interceptor_trampoline_strcmp = __wrap_strcmp that enters it), in the form of abcmp_realizes
   (projects/cgif/cgif_file_fuzzer/proofs/lib/YG0d.v) over the asan-state definitions of that proof as libreac/fuzz_grant holds
   them. The interceptor compares byte by byte up to the first index k where the bytes differ or s1's byte is 0, checks
   [s1, s1 + k + 1) and [s2, s2 + k + 1) with the READ_RANGE checks (QuickCheck below 64 bytes, else
   __asan_region_is_poisoned), calls the empty weak hook, and returns CharCmpX (-1, 0 or 1). Target-independent: every
   address comes from the layout or the registers. R1: the strings are disjoint from the callee's stack window
   [sp - 2 ESTACK, sp). R2: not stated, because this interceptor does not touch the AddrHashMap metadata (no FILE
   object). It subsumes the literal instance of libreac/fuzz_pcap lib/A/Rt/StrcmpDef.v (x = y, k = the literal's
   length, c1 = c2 = 0, result 0). *)
(* Modified by Theorem Labs, 2026-10-29: taken by path from libreac/fuzz_grant lib/Reusable/AStrcmpDef.v
   (a working branch 97c611eec86, owner a Theorem Labs lane, the text of record for the strcmp trampoline contract in
   a Theorem Labs lane's registry). Only the module paths change (fuzz_grant -> fuzz_identity); the statement is identical. The
   walk is a Theorem Labs lane's lib/A/Rt/Strcmp.v, relocated to identity's addresses separately. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/AStrcmpDef.v (donor image sha256 c954b804786c), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Reusable/AStrcmpDef.v, with its module paths changed; 325 of its 358 lines of code are new or changed and 20 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the call-site form of lib/Reusable/YCbq.v's aj_bcmp_at (lines 2262-2310), restated
   for the strcmp wrapper's contract astrcmp_realizes of lib/Reusable/AStrcmpDef.v (fuzz_identity's text, module paths
   changed): the same journal threading through ecall_pre_at and ajournal_after_write, with the strcmp contract's
   str_meet premise and its strcmp_res result in place of bcmp's n-byte compare. The string lemmas below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgKcStr.v at 4a37309420ef (image A's twin of
   this adapter); image B's callee address and call sites only: the strcmp jump is 0x41c20 (A: 0x41ba0), the three
   `jal` sites are 0x83418 / 0x8342c / 0x83440 with the return addresses 0x8341c / 0x83430 / 0x83444 (A: 0x832e8 /
   0x832fc / 0x83310), and the three literals are 0x21380 / 0x213a0 / 0x213c0 (A: 0x21340 / 0x21360 / 0x21380),
   which are lib/AU/HPgImgB.v headamp_himg_B's hi_hph / hi_hpad / hi_hsens. Every lemma's text and proof is the
   donor's: the adapter names no image but the callee's address. Prefix hks_ -> hksu_. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the CALL ADAPTER of the strcmp wrapper. Proves no function (kind: segment lemma).

   THE CALLEE. The strcmp jump at 0x41c20 enters the ASan strcmp interceptor (the same runtime as image A's and
   libreac/fuzz_identity's; the runtime of the two images is byte-identical over every shared FUNC name). It
   compares byte by byte up to the first index k where the bytes differ or s1's byte is 0, checks that the bytes it
   read are marked usable in the shadow map, and returns CharCmpX (-1, 0 or 1). It uses at most 2 ESTACK bytes of
   stack below sp and writes no byte outside them. Its contract is libreac/fuzz_identity lib/Reusable/AStrcmpDef.v
   astrcmp_realizes at origin/ossv/recipes 2d2ff01bb6f. No file this one Requires, directly or through another,
   defines astrcmp_realizes (lib/Reusable/AStrcmpDef.v and lib/A/Rt/StrcmpDef.v do), so the Section below takes
   the contract at 0x41c20 as the hypothesis STRCMP, with str_meet and strcmp_res unfolded and beta-reduced word for
   word, and quantified over the float state: `exact (fun fx' => @astrcmp_realizes fx' rc
   segs B 0x41c20)`, from a walk of the wrapper that holds for every float state, discharges it. Only cfg_at reads
   the float state.

   THE THREE CALL SITES (LLVMFuzzerTestOneInput, fuzz_headamp.c:132-133, expect_of's strcmp chain on the name after
   the channel's '.'): `jal` 0x41c20 at 0x83418 (ra 0x8341c, a1 = 0x21380 "phantom"), 0x8342c (ra 0x83430,
   a1 = 0x213a0 "pad"), 0x83440 (ra 0x83444, a1 = 0x213c0 "sens"); a0 = s7 = the name, a C string inside the pp
   block (the tail of a key of the pod_ent table).

   WHAT EACH LEMMA GIVES:
   - hksu_strcmp_at: the call inside a caller's journal at sp = sp0 + o: the journal after the call is the caller's
     at the same allocator state, every byte outside [sp0 + o - 2 ESTACK, sp0 + o) is kept, a0 = hksu_res c1 c2.
   - hksu_meet_of_cstr: two NUL-terminated strings in the view meet at an index kk no larger than either length,
     and hksu_res c1 c2 = 0 exactly when the two texts are equal.
   - hksu_cstr_args / hksu_blk_args: the wrapper's premises on the bytes [a, a + kk + 1) it reads, from a read-only
     string of the image (hd_cstr) / from a C string inside a live block of the journal's end state.
   - hksu_strcmp_call: the call in the continuation form of lib/A/HPgCalls.v hc_call: from hc_core at the call with
     ra = ret, a0 = a C string kb inside a live block given by its bytes and NUL, a1 = an image string lit
     (hd_cstr), the walk continues at ret with hc_core again, the callee-saved registers, the I/O state, every byte
     outside [R - 2 ESTACK, R) as at the call, a0 = hksu_res c1 c2 of the bytes where the two strings meet, and
     a0 = 0 exactly when kb = lit.

   Section hypotheses: segs_low (the image lies below the shadow map: YCbq.v's ajournal_after_write asks it) and
   STRCMP (the wrapper's contract at 0x41c20). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgCallsStr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== image B: the callee, the return addresses, the literals ======================================== *)
Definition B_STRCMP : Z := 0x41c20.          (* the strcmp jump *)
Definition RB_STRCMP1 : Z := 0x8341c.        (* the `jal` 0x83418 plus 4: against "phantom" *)
Definition RB_STRCMP2 : Z := 0x83430.        (* the `jal` 0x8342c plus 4: against "pad" *)
Definition RB_STRCMP3 : Z := 0x83444.        (* the `jal` 0x83440 plus 4: against "sens" *)
Definition B_HPH : Z := 0x21380.             (* the harness's "phantom" *)
Definition B_HPAD : Z := 0x213a0.            (* the harness's "pad" *)
Definition B_HSENS : Z := 0x213c0.           (* the harness's "sens" *)

Lemma hksu_lits_B : B_HPH = hi_hph headamp_himg_B /\ B_HPAD = hi_hpad headamp_himg_B /\
  B_HSENS = hi_hsens headamp_himg_B.
Proof. repeat split; reflexivity. Qed.

(* AStrcmpDef.v's strcmp_res, word for word: sanitizer_common's CharCmpX *)
Definition hksu_res (c1 c2 : Z) : Z := if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1.

Lemma hksu_res_0 : forall c1 c2, hksu_res c1 c2 = 0 <-> c1 = c2.
Proof.
intros c1 c2. unfold hksu_res.
destruct (Z.eqb_spec c1 c2) as [E|E]; [tauto|].
destruct (c1 <? c2); split; intros H; first [discriminate H | exfalso; exact (E H)].
Qed.

Lemma hksu_res_range : forall c1 c2, hksu_res c1 c2 = -1 \/ hksu_res c1 c2 = 0 \/ hksu_res c1 c2 = 1.
Proof. intros c1 c2. unfold hksu_res. destruct (c1 =? c2); [|destruct (c1 <? c2)]; auto. Qed.

(* the byte lists of two texts are equal exactly when their values are *)
Lemma hksu_zbytes_inj : forall a b : list byte, hd_zbytes a = hd_zbytes b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate H; [reflexivity|].
injection H as Hxy Hab. f_equal; [apply bv_eq; exact Hxy | exact (IH b Hab)].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* AStrcmpDef.v's str_meet, word for word: the bytes before k are equal and nonzero; at k they differ or s1's byte
   is 0 *)
Definition hksu_meet (W : world segs) (mem : word -> option byte) (x y k c1 c2 : Z) : Prop :=
  0 <= k /\
  (forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\
                                     aview segs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
  aview segs (w_H W) mem (x + k) = Some c1 /\ aview segs (w_H W) mem (y + k) = Some c2 /\
  (c1 <> c2 \/ c1 = 0).

(* The strcmp wrapper's contract at image B's jump 0x41c20: libreac/fuzz_identity lib/Reusable/AStrcmpDef.v
   `astrcmp_realizes segs B B_STRCMP` (origin/ossv/recipes 2d2ff01bb6f; the same statement as reac-pw/fuzz_role
   lib/Reusable/AStrcmpDef.v), with str_meet and strcmp_res unfolded and beta-reduced, at every float
   state fx' (only cfg_at reads it). `exact` of the wrapper walk's theorem at 0x41c20, stated for every float state,
   discharges it. *)
Hypothesis STRCMP : forall fx' : YK11.FPState,
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  (0 <= k /\
   (forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\
                                      aview segs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
   aview segs (w_H W) mem (x + k) = Some c1 /\ aview segs (w_H W) mem (y + k) = Some c2 /\
   (c1 <> c2 \/ c1 = 0)) ->
  src_ok segs W regs mem x (k + 1) -> src_ok segs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (k + 1) ->
  SRr segs W (@cfg_at fx' segs B_STRCMP regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ============================ the call inside a caller's journal ============================ *)
Lemma hksu_strcmp_at :
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y kk c1 c2 (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 -> y + kk + 1 <= 2 ^ 63 ->
hksu_meet W memT x y kk c1 c2 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x (kk + 1) -> src_ok segs W regsT memT y (kk + 1) ->
(forall a, x <= a <= x + kk -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + kk -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (kk + 1) -> amem_range y (kk + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kk + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kk + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (kk + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (kk + 1) ->
SRr segs W (cfg_at segs B_STRCMP regsT memT mdc)
(fun W2 c2' => W2 = W /\ exists regs2 mem2 md2,
 c2' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ same_io mdc md2 /\ getr regs2 10 = w64 (hksu_res c1 c2) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y kk c1 c2 o raw
HJ Ha0 Ha1 Hx0 Hy0 Hkk Hxk Hyk Hmeet Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
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
{ exact (STRCMP fx lyc Sc W regsT memT mdc x y kk c1 c2 HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hkk Hxk Hyk Hmeet Hsx Hsy
    ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2' _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
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

(* ============================ two strings meet ============================ *)
(* A NUL-terminated string in the view: the bytes s at a (each nonzero), then the NUL. *)
Definition hksu_cstr_at (W : world segs) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs (w_H W) mem (a + i) = Some (nth (Z.to_nat i) s 0)) /\
aview segs (w_H W) mem (a + Z.of_nat (length s)) = Some 0 /\
Forall (fun b => 0 < b < 256) s.

Lemma hksu_cstr_cons : forall W mem a b s, hksu_cstr_at W mem a (b :: s) ->
aview segs (w_H W) mem a = Some b /\ 0 < b < 256 /\ hksu_cstr_at W mem (a + 1) s.
Proof.
intros W mem a b s (Hc & Hn & Hf). inversion Hf as [|b' s' Hb Hs]; subst.
cbn [length] in Hc, Hn. rewrite Nat2Z.inj_succ in Hc, Hn.
split; [specialize (Hc 0 ltac:(lia)); rewrite Z.add_0_r in Hc; exact Hc|].
split; [exact Hb|].
split; [|split; [replace (a + 1 + Z.of_nat (length s)) with (a + Z.succ (Z.of_nat (length s))) by lia; exact Hn | exact Hs]].
intros i Hi. specialize (Hc (i + 1) ltac:(lia)). replace (a + (i + 1)) with (a + 1 + i) in Hc by lia.
rewrite Hc. f_equal. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma hksu_cstr_nil : forall W mem a, hksu_cstr_at W mem a [] -> aview segs (w_H W) mem a = Some 0.
Proof. intros W mem a (_ & Hn & _). cbn [length Z.of_nat] in Hn. rewrite Z.add_0_r in Hn. exact Hn. Qed.

Lemma hksu_meet_of_cstr : forall s W mem x t y,
hksu_cstr_at W mem x s -> hksu_cstr_at W mem y t ->
exists kk c1 c2, hksu_meet W mem x y kk c1 c2 /\ 0 <= kk <= Z.of_nat (length s) /\ kk <= Z.of_nat (length t) /\
(hksu_res c1 c2 = 0 <-> s = t).
Proof.
induction s as [|b s IH]; intros W mem x t y Hx Hy.
- pose proof (hksu_cstr_nil W mem x Hx) as X0.
  destruct t as [|b' t].
  + pose proof (hksu_cstr_nil W mem y Hy) as Y0.
    exists 0, 0, 0. split; [|cbn [length Z.of_nat]; split; [lia|]; split; [lia|]; rewrite hksu_res_0; tauto].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. right; reflexivity.
  + destruct (hksu_cstr_cons W mem y b' t Hy) as (Y0 & Hb' & _).
    exists 0, 0, b'. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite hksu_res_0; split; [lia | discriminate]].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. right; reflexivity.
- destruct (hksu_cstr_cons W mem x b s Hx) as (X0 & Hb & Hx').
  destruct t as [|b' t].
  + pose proof (hksu_cstr_nil W mem y Hy) as Y0.
    exists 0, b, 0. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite hksu_res_0; split; [lia | discriminate]].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. left; lia.
  + destruct (hksu_cstr_cons W mem y b' t Hy) as (Y0 & Hb' & Hy').
    destruct (Z.eq_dec b b') as [<-|Hne].
    * destruct (IH W mem (x + 1) t (y + 1) Hx' Hy') as (kk & c1 & c2 & (Hk0 & Heq & Hc1 & Hc2 & Hend) & Hks & Hkt & Hres).
      exists (kk + 1), c1, c2. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite Hres; split; [intros ->; reflexivity | intros H; injection H; tauto]].
      split; [lia|].
      split; [|split; [replace (x + (kk + 1)) with (x + 1 + kk) by lia; exact Hc1|];
              split; [replace (y + (kk + 1)) with (y + 1 + kk) by lia; exact Hc2 | exact Hend]].
      intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
      { exists b. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. lia. }
      destruct (Heq (i - 1) ltac:(lia)) as (bb & B1 & B2 & B3).
      exists bb. replace (x + i) with (x + 1 + (i - 1)) by lia. replace (y + i) with (y + 1 + (i - 1)) by lia. tauto.
    * exists 0, b, b'. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite hksu_res_0; split; [intros E; exfalso; exact (Hne E) | intros E; injection E; intros _ E'; exfalso; exact (Hne E')]].
      split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. left; exact Hne.
Qed.

(* ============================ the bytes the wrapper reads ============================ *)
Lemma hksu_hull_sub : forall rd a n m, 0 < m <= n -> shadow_hull_vis rd a n -> shadow_hull_vis rd a m.
Proof. intros rd a n m Hm H. exact (hc_hull_sub rd a n a m H ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

Lemma hksu_src_sub : forall W regs mem s n m, m <= n -> src_ok segs W regs mem s n -> src_ok segs W regs mem s m.
Proof. intros W regs mem s n m Hm H a Ha. apply H. lia. Qed.

(* The bytes and NUL of a C string (garr8, as the walks hold the key in pp) are a string in the view. *)
Lemma hksu_cstr_of_garr8 : forall (W : world segs) mem a (l : list byte),
garr8 segs (mrestrict (w_H W) mem) a (hd_zbytes l ++ [0]) -> ~ In (Z_to_bv 8 0) l ->
hksu_cstr_at W mem a (hd_zbytes l).
Proof.
intros W mem a l Hg Hnz.
assert (Ll : length (hd_zbytes l) = length l) by (unfold hd_zbytes; apply length_map).
assert (Lz : length (hd_zbytes l ++ [0]) = S (length l)) by (rewrite length_app, Ll; cbn [length]; lia).
assert (Hat : forall j, (j < S (length l))%nat ->
  aview segs (w_H W) mem (a + Z.of_nat j) = Some (nth j (hd_zbytes l ++ [0]) 0)).
{ intros j Hj. destruct (Hg j ltac:(rewrite Lz; exact Hj)) as [Hv Hr].
  exact (HPgMem.hm_val1_aview segs (w_H W) mem _ _ Hv Hr). }
split; [|split].
- intros i Hi. rewrite Ll in Hi. rewrite <- (Z2Nat.id i) at 1 by lia.
  rewrite (Hat (Z.to_nat i) ltac:(lia)). rewrite app_nth1 by (rewrite Ll; lia). reflexivity.
- rewrite Ll. rewrite (Hat (length l) ltac:(lia)). rewrite app_nth2 by (rewrite Ll; lia).
  rewrite Ll, Nat.sub_diag. reflexivity.
- apply Forall_forall. intros v Hv. unfold hd_zbytes in Hv. apply in_map_iff in Hv as (b & <- & Hb).
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia].
  exfalso. apply Hnz. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

(* A read-only string of the image (HPgBase.hd_cstr) gives the wrapper's premises on [a, a + kk + 1), kk <= len,
   when no byte of the string lies in the wrapper's window below sp. *)
Lemma hksu_cstr_args : forall W (regs : bvmap 5 word) mem a s kk,
hd_cstr segs (w_H W) mem a s -> 0 <= kk <= Z.of_nat (length s) ->
(forall b, a <= b <= a + Z.of_nat (length s) -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) ->
0 < a /\ a + kk + 1 <= 2 ^ 63 /\ src_ok segs W regs mem a (kk + 1) /\
(forall b, a <= b <= a + kk -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) /\ amem_range a (kk + 1) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a (kk + 1) /\ shadow_hull_vis (aview segs (w_H W) mem) a (kk + 1).
Proof.
intros W regs mem a s kk (Hc & Hn & Hf & Ha0 & Hhi & _ & Ham & Hra & Hhv & _) Hk Hst.
assert (ESTACK = 4096) as Hes by reflexivity.
split; [exact Ha0|]. split; [lia|].
split.
{ intros b Hb. split; [|intros Hw; apply (Hst b ltac:(lia)); lia].
  destruct (Z.eq_dec b (a + Z.of_nat (length s))) as [->|Hne]; [rewrite Hn; discriminate|].
  replace b with (a + (b - a)) by lia. rewrite (Hc (b - a) ltac:(lia)). discriminate. }
split; [intros b Hb; apply Hst; lia|].
split; [eapply hd_amem_range_le; [|exact Ham]; lia|].
split; [eapply range_addressable_sub; [exact Hra | lia | lia] | eapply hksu_hull_sub; [|exact Hhv]; lia].
Qed.

(* A C string inside a live block [p, p + req_size m) of the journal's end state (its bytes and NUL known, garr8)
   gives the wrapper's premises on [a, a + kk + 1), kk <= len: the block lies in application memory below the
   allocator's ceiling, so below every stack window of the journal; its bytes are marked usable and their shadow hull
   is readable (AR's shadow law). *)
Lemma hksu_blk_args : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
(o p m a kk : Z) (l : list byte),
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs = sp0 + o -> o <= 0 -> 2 * ESTACK - o <= STK ->
In (p, m) (ablocks B lyc Sc) -> p <= a -> a + Z.of_nat (length l) + 1 <= p + req_size m ->
garr8 segs (mrestrict (w_H W) memc) a (hd_zbytes l ++ [0]) -> 0 <= kk <= Z.of_nat (length l) ->
0 < a /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\ a + kk + 1 <= 2 ^ 63 /\ src_ok segs W regs memc a (kk + 1) /\
(forall b, a <= b <= a + kk -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) /\ amem_range a (kk + 1) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF a (kk + 1) /\
shadow_hull_vis (aview segs (w_H W) memc) a (kk + 1).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs o p m a kk l
HJ Hsp Hneg Hbud Hin Hpa Hae Hg Hk.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ (AR_laws_ok segs B) _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hmax).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hlo & Hslo & _).
pose proof asan_consts as (C1 & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hrs : 1 <= req_size m <= Z.max m 1) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Lz : length (hd_zbytes l ++ [0]) = (length l + 1)%nat)
by (unfold hd_zbytes; rewrite length_app, length_map; cbn [length]; lia).
split; [lia|].
split; [unfold MALLOC_MAX in Hmax; clear - Hmax Hrs Hpa Hae; lia|].
split; [unfold MALLOC_MAX in Hmax; clear - Hmax Hrs Hpa Hae Hk Hceil C1; lia|].
split.
{ intros b Hb. split.
  - apply (hc_garr8_some segs (w_H W) memc a _ Hg). rewrite Lz. lia.
  - rewrite Hsp. clear - Hb Hpa Hae Hk Hceil Hlo Hslo Hbud Hes. lia. }
split; [intros b Hb; rewrite Hsp; clear - Hb Hpa Hae Hk Hceil Hlo Hslo Hbud Hes; lia|].
split.
{ clear - Happ C1 Hpa Hae Hk. unfold in_app in Happ. destruct Happ as (_ & [Hl | (Hh1 & Hh2)]); unfold amem_range;
  [left | right]; unfold ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia. }
split.
- exact (range_addressable_of_block segs B LAWS lyc Sc W memc mdc p m a (kk + 1) HAR Hin Hpa ltac:(lia)).
- exact (shadow_hull_vis_of_block segs B LAWS lyc Sc W memc mdc p m a (kk + 1) HAR Hin Hpa ltac:(lia) ltac:(lia)).
Qed.

(* ============================ the call in the walk's continuation form ============================ *)
(* strcmp(name, lit) at a cut of the harness: a0 = key, a C string kb inside a live block; a1 = alit, one of the
   image's strings with its hd_cstr facts. The continuation runs at ret with hc_core at the call's allocator state
   again; a0 = hksu_res c1 c2 of the bytes where the two strings meet, and a0 = 0 exactly when kb = lit. *)
Lemma hksu_strcmp_call : forall (Q : world segs -> config -> Prop) (ret alit : Z) (lit : list byte)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R key p m : Z) (kb : list byte),
hc_core segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
getr regs 10 = w64 key -> getr regs 11 = w64 alit ->
In (p, m) (ablocks B lyc Sc) -> p <= key -> key + Z.of_nat (length kb) + 1 <= p + req_size m ->
garr8 segs (mrestrict (w_H W) memc) key (hd_zbytes kb ++ [0]) ->
~ In (Z_to_bv 8 0) kb ->
hd_cstr segs (w_H W) memc alit (hd_zbytes lit) ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 hc_core segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> same_io mdc md2 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - 2 * ESTACK <= x < R) ->
  aview segs (w_H W) mem2 x = aview segs (w_H W) memc x) ->
 (exists c1 c2, getr regs2 10 = w64 (hksu_res c1 c2) /\ (hksu_res c1 c2 = 0 <-> kb = lit)) ->
 SRr segs W (cfg_at segs ret regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs B_STRCMP regs memc mdc) Q.
Proof.
intros Q ret alit lit STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R key p m kb
HC Hra Hret Hret2 Ha0 Ha1 Hin Hpk Hke Hg Hnz Hlit K.
pose proof (hc_core_R segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC) as (HRc & _ & Hsp).
pose proof HC as (HJ & Hev & H2 & H3 & H4 & HRal & Hwin & HRs).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (Hsp0al & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hts : T_SEG_STK = 16384) by reflexivity.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hsp' : spZ regs = sp0 + (R - sp0)) by (rewrite Hsp; ring).
assert (Hal' : (R - sp0) mod 16 = 0) by (clear - HRal Hsp0al; Z.div_mod_to_equations; lia).
assert (Hneg : R - sp0 <= 0) by (clear - HRs; lia).
assert (Hbud : 2 * ESTACK - (R - sp0) <= STK) by (clear - Hwin Hes Hts; lia).
assert (Llit : length (hd_zbytes lit) = length lit) by (unfold hd_zbytes; apply length_map).
(* the two strings meet *)
assert (Hkc : hksu_cstr_at W memc key (hd_zbytes kb)) by exact (hksu_cstr_of_garr8 W memc key kb Hg Hnz).
assert (Hlc : hksu_cstr_at W memc alit (hd_zbytes lit)).
{ destruct Hlit as (Hc & Hn & Hf & _). split; [exact Hc|]. split; [exact Hn | exact Hf]. }
destruct (hksu_meet_of_cstr (hd_zbytes kb) W memc key (hd_zbytes lit) alit Hkc Hlc)
  as (kk & c1 & c2 & Hmeet & Hk1 & Hk2 & Hres).
assert (Lkb : length (hd_zbytes kb) = length kb) by (unfold hd_zbytes; apply length_map).
rewrite Lkb in Hk1. rewrite Llit in Hk2.
(* the premises on [key, key + kk + 1) and [alit, alit + kk + 1) *)
destruct (hksu_blk_args STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (R - sp0) p m key kk kb
  HJ Hsp' Hneg Hbud Hin Hpk Hke Hg Hk1) as (Hx0 & Hlen & Hxk & Hsx & Hbx & Hmx & Hrx & Hhx).
assert (Hlow : forall b, alit <= b <= alit + Z.of_nat (length lit) -> 0 <= b < kLowMemEnd).
{ intros b Hb. pose proof Hlit as (_ & _ & _ & _ & _ & Himg & _). rewrite Llit in Himg.
  replace b with (alit + (b - alit)) by lia. apply segs_low. apply Himg. lia. }
destruct (hksu_cstr_args W regs memc alit (hd_zbytes lit) kk Hlit ltac:(rewrite Llit; lia)
  ltac:(intros b Hb; rewrite Llit in Hb; pose proof (Hlow b Hb) as Hb'; rewrite Hsp; rewrite C5 in Hb';
        clear - Hb' HRc C1 Hes Hts; lia))
  as (Hy0 & Hyk & Hsy & Hby & Hmy & Hry & Hhy).
eapply SRr_bind.
{ exact (hksu_strcmp_at W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k key alit kk c1 c2 (R - sp0) (w64 ret)
    HJ Ha0 Ha1 Hx0 Hy0 ltac:(lia) Hxk Hyk Hmeet Hsp' Hal' Hneg Hbud H3 H4 Hra
    ltac:(apply hc_ret_ok; [exact Hret | exact Hret2]) Hsx Hsy
    ltac:(rewrite <- Hsp'; exact Hbx) ltac:(rewrite <- Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hio & Hv & Hkeep & _).
apply (K regs2 mem2 md2).
- split; [exact HJ2|]. split; [exact Hev|].
  split; [rewrite <- H2; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H3; exact (HP 3 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H4; exact (HP 4 ltac:(unfold acallee_saved; lia))|].
  split; [exact HRal|]. split; [exact Hwin | exact HRs].
- exact HP.
- exact Hio.
- intros x Hx Hs. apply Hkeep; [exact Hx|]. replace (sp0 + (R - sp0)) with R by ring. exact Hs.
- exists c1, c2. split; [exact Hv|]. rewrite Hres. split; [apply hksu_zbytes_inj | intros ->; reflexivity].
Qed.

End c.
End b.

Print Assumptions hksu_lits_B.
Print Assumptions hksu_res_0.
Print Assumptions hksu_res_range.
Print Assumptions hksu_zbytes_inj.
Print Assumptions hksu_strcmp_at.
Print Assumptions hksu_cstr_cons.
Print Assumptions hksu_cstr_nil.
Print Assumptions hksu_meet_of_cstr.
Print Assumptions hksu_hull_sub.
Print Assumptions hksu_src_sub.
Print Assumptions hksu_cstr_of_garr8.
Print Assumptions hksu_cstr_args.
Print Assumptions hksu_blk_args.
Print Assumptions hksu_strcmp_call.
