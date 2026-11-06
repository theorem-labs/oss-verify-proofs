(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: a live block's user range, terminator included, satisfies YGcfStr.amem_range8, the
   strengthened range premise of astrcmp_realizes_cf / astrlen_realizes_cf. AR_blocks_law_cf (YG0dcf.v) gives the
   user range's in_app and 16-alignment only; amem_range8's high arm also needs the START at least
   kHighMemBeg + 15. It comes from the chunk (chunk_facts_cf, YG0scf.v): the chunk's whole extent is in one
   application region (in_app of ck_base, ck_extent), and the user pointer is ck_base + ck_rz with ck_rz >= 16, so a
   user pointer in high memory is at least kHighMemBeg + 16. The end needs no slack from the chunk: the user range ends
   by kLowShadowBeg (low) or by ASAN_CEIL (high), and amem_range8 allows up to kLowMemEnd - 1 = kLowShadowBeg + 4095
   and kHighMemEnd - 1 > ASAN_CEIL + 2 ^ 23, so the terminator byte and the 8 bytes past it fit for every k <= n.
   No address, no unit numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfStr.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section BR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The user pointer of a live block: at least 16 bytes into its chunk, and the chunk is in one application region. *)
Lemma block_user_range_cf : forall segs B ly S Hp W mem md p n, ARcf segs B ly S Hp W mem md -> In (p, n) (blocks S) ->
0 <= n /\
((4096 + 16 <= sptr_addr B ly p /\ sptr_addr B ly p + req_size n <= kLowShadowBeg) \/
 (kHighMemBeg + 16 <= sptr_addr B ly p /\ sptr_addr B ly p + req_size n <= ASAN_CEIL)).
Proof.
intros segs B ly S Hp W mem md p n (M & _) Hin.
unfold blocks in Hin. apply in_map_iff in Hin as (c & Ec & Hc). apply filter_In in Hc as [Hc _].
injection Ec as <- <-.
pose proof (chunk_facts_cf B ly S Hp _ c M Hc) as (IA & _ & _ & EU & RZ & _ & RQ & EX & _).
rewrite EU. unfold in_app in IA. destruct IA as [I0 [IL | [IH1 IH2]]].
- split; [lia|]. left. lia.
- split; [lia|]. right. lia.
Qed.

(* THE LEMMA: the bytes [p, p + k] (k <= n: the string and its terminator) with 8 bytes to spare. *)
Lemma block_amem_range8_cf : forall segs B ly S Hp W mem md p n k, ARcf segs B ly S Hp W mem md ->
In (p, n) (blocks S) -> 0 <= k <= n -> YGcfStr.amem_range8 (sptr_addr B ly p) (k + 1).
Proof.
intros segs B ly S Hp W mem md p n k HA Hin Hk.
destruct (block_user_range_cf segs B ly S Hp W mem md p n HA Hin) as (Hn & [[L1 L2] | [H1 H2]]).
- assert (R : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  unfold YGcfStr.amem_range8. left. unfold kLowMemEnd, kLowShadowBeg in *. lia.
- assert (R : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  pose proof (@ASAN_CEIL_range rc) as CR.
  unfold YGcfStr.amem_range8. right. unfold kHighMemEnd, kHighMemBeg in *. lia.
Qed.

(* The same without the terminator, the form Main named. *)
Corollary block_amem_range8_cf_k : forall segs B ly S Hp W mem md p n k, ARcf segs B ly S Hp W mem md ->
In (p, n) (blocks S) -> 0 <= k <= n -> YGcfStr.amem_range8 (sptr_addr B ly p) k.
Proof.
intros segs B ly S Hp W mem md p n k HA Hin Hk.
pose proof (block_amem_range8_cf segs B ly S Hp W mem md p n k HA Hin Hk) as H.
unfold YGcfStr.amem_range8 in *. lia.
Qed.

(* Two facts a walk cites by name (h-hpreset-7's walk S9, stand-ins S9_BMAX / S9_STK64). *)
(* A live block's request is below the instance's malloc ceiling: AR_blocks_law_cf's last conjunct (YG0dcf.v). *)
Corollary ablock_n_lt_max_cf : forall segs B ly S Hp W mem md p n, ARcf segs B ly S Hp W mem md ->
In (p, n) (ablocks B ly S) -> 0 <= n < cf_malloc_max.
Proof.
intros segs B ly S Hp W mem md p n HA Hin.
destruct (AR_blocks_law_ok_cf segs B ly S Hp W mem md p n HA Hin) as (_ & _ & _ & _ & _ & _ & X). exact X.
Qed.

(* The stack's top is 64-aligned: layout_ok's lo_top makes it page-aligned (YG0f.v). *)
Corollary stk_hi_mod64_cf : forall segs B ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0.
Proof.
intros segs B ly S Hp W mem md HA.
destruct (lo_top _ (amc_layout _ _ _ _ _ (proj1 HA))) as (_ & _ & _ & _ & _ & PA & _).
unfold page_aligned in PA. apply Z.mod_divide in PA; [|lia]. destruct PA as [k Hk].
apply Z.mod_divide; [lia|]. exists (64 * k). lia.
Qed.

End BR.
