(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 42 of its 69 lines of code are new or changed and 1278 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: a string argument of the strcmp wrapper at a call site, from the caller's Pre. The
   helper contracts state each string the wrapper reads as `acstr_at segs m p s` and index_of_c.v's
   `astrcmp_arg segs regs K m p s` at the call's entry memory m = rdW W memc; LinkWalk.v aj_gx_strcmp_at (over
   lib/A/Rt/RtString.v astrcmp_realizes) asks, at the wrapper's entry (sp' = sp - F, memory memT),
   `astr_at W memT p s`, `aread_ok (2 * ESTACK) W regsT memT p (|s| + 1)` and `atail_vis W memT (p + |s|)`.
   `astr_call` gives the three, when memT agrees with memc outside the caller's window [sp - K, sp) (which holds
   F + 2 * ESTACK) and the window's bytes are present (they are the journal's).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem index_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma sa_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 45.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma astr_call : forall (W : world segs) (regs regsT : bvmap 5 word) (memc memT : word -> option byte) K F p s,
  0 <= F -> F + 2 * ESTACK <= K -> spZ regsT = spZ regs - F -> 2 ^ 46 <= spZ regs - K -> spZ regs <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
     aview segs (w_H W) memT a = aview segs (w_H W) memc a) ->
  (forall a, spZ regs - K <= a < spZ regs -> aview segs (w_H W) memT a <> None) ->
  acstr_at segs (rdW W memc) p s -> astrcmp_arg segs regs K (rdW W memc) p s ->
  astr_at segs W memT p s /\ aread_ok segs (2 * ESTACK) W regsT memT p (astr_len s + 1) /\
  atail_vis segs W memT (p + astr_len s).
Proof.
intros W regs regsT memc memT K F p s HF HK HspT Hlo Hhi UN Hwin [[Hp0 [Hpl Hab]] Hnz]
  (Hp & Hn & Hamr & Hra & Hhull & Hapf & Htail).
assert (ESTACK = 4096) as Hes by reflexivity.
unfold apart_frame in Hapf. unfold astr_len.
rewrite length_app in Hpl. cbn [length] in Hpl.
assert (Hamr' : p + (Z.of_nat (length s) + 1) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
(* a byte of the string, its NUL included *)
assert (Hbyte : forall i, (i < length (s ++ [zb 0]))%nat ->
          aview segs (w_H W) memT (p + Z.of_nat i) = Some (bv_unsigned (nth i (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite UN by lia. rewrite <- (ard_aview segs). unfold ard. rewrite (Hab i ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia). reflexivity. }
split; [|split].
- split; [|exact Hnz]. intros i Hi. exact (Hbyte i Hi).
- split; [lia|]. split; [lia|]. split; [lia|]. split; [|split; [exact Hamr | split]].
  + intros a Ha. split.
    * pose proof (Hbyte (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
      rewrite Z2Nat.id in Hb by lia. replace (p + (a - p)) with a in Hb by lia. rewrite Hb. discriminate.
    * unfold ascratch_stk. lia.
  + apply (ra_shadow_eq (ard segs (rdW W memc))); [exact Hra|].
    intros x Hx. rewrite (ard_aview segs). pose proof (sa_shadow_low x ltac:(lia)). apply UN; lia.
  + intros _ t Ht. pose proof (sa_shadow_low p ltac:(lia)) as S0.
    pose proof (sa_shadow_low (p + (Z.of_nat (length s) + 1) - 1) ltac:(lia)) as S1.
    rewrite UN; [rewrite <- (ard_aview segs); exact (Hhull t Ht) | unfold shadow_addr, SHADOW_OFF in *; lia |].
    unfold shadow_addr, SHADOW_OFF in *. lia.
- intros a Ha. destruct (Z_lt_le_dec a (spZ regs - K)) as [H1|H1]; [|destruct (Z_lt_le_dec a (spZ regs)) as [H2|H2]].
  + rewrite UN by lia. rewrite <- (ard_aview segs). apply Htail. lia.
  + apply Hwin. lia.
  + rewrite UN by (pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)); lia).
    rewrite <- (ard_aview segs). apply Htail. lia.
Qed.
End a.
