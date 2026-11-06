(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v; 43 of its 89 lines of code are new or changed and 1259 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the two kept clauses of remember's Post (lib/A/Prog/remember_c.v
   `remember_acontract`), for a function whose WRITE SET IS A HEAP BLOCK.

   LinkWalk.v's `ashadow_kept_run` and `apost_leaf` ask `forall x, E x -> x < SHADOW_OFF` of the exception set
   E. That holds of a write set of image globals (link's G lies below kLowMemEnd = SHADOW_OFF = 0x7fff8000,
   which is why the kit states it that way), but NOT of remember's: its write set is the marks block, a block
   of the allocator's ledger, and `amem_range` (YG0d.v:325) puts such a block either below kLowMemEnd OR above
   kHighMemBeg. What the kit's proof actually uses is only that E misses the SHADOW BAND, since the clause it
   proves is about `shadow_addr a` for a byte a of a heap block; `amem_range` gives that on both arms. These two
   lemmas are the kit's two with that weaker premise, and nothing else changed.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

(* `ashadow_kept_run` with `E` only required to miss the shadow band *)
Lemma rem_ashadow_kept : forall lyc Sc ly2 S2 (W : world pa_segs) memc mdc (W2 : world pa_segs) mem2 slo shi
    (E : Z -> Prop),
  AR pa_segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview pa_segs (w_H W2) mem2 a = aview pa_segs (w_H W) memc a) ->
  (forall x, E x -> ~ (SHADOW_OFF <= x < kHighShadowEnd)) ->
  ashadow_kept pa_segs B lyc Sc ly2 S2 W memc W2 mem2.
Proof.
intros lyc Sc ly2 S2 W memc mdc W2 mem2 slo shi E HAR Hceil UN HE b m a Hin _ Ha.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
assert (Ha0 : 0 <= a < kHighMemEnd) by lia.
assert (Ha1 : a <= alloc_ceiling) by lia.
pose proof (shadow_addr_bounds a Ha0) as Hsb.
pose proof (shadow_mono a alloc_ceiling Ha1) as Hsle.
assert (Hsh : shadow_addr alloc_ceiling < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Hlo : SHADOW_OFF <= shadow_addr a)
  by (unfold shadow_addr; pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); lia).
apply UN; [unfold kHighShadowEnd in Hsb; lia | lia |].
intros HEa. apply (HE _ HEa). split; [exact Hlo | lia].
Qed.

(* `apost_leaf` over it: the whole apost of a leaf whose write set is a heap block *)
Lemma rem_apost_leaf : forall (K EV : Z) (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc
    (W : world pa_segs) memc mdc k (regs regs2 : bvmap 5 word) mem2 md2
    (Q : alayout -> astate -> world pa_segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  0 <= EV -> sp0 - STK <= spZ regs - K -> spZ regs - K <= spZ regs ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ E a ->
     aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  (forall x, E x -> ~ (SHADOW_OFF <= x < kHighShadowEnd)) ->
  Q lyc Sc W regs2 mem2 md2 ->
  apost SK pa_segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom pa_segs)) md2).
Proof.
intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 Q
  HJ HJ2 HEV Hlo Hwin Hfds Hfs HP UN Hgrow Hpw HE HQ.
pose proof (aj_stk_ceiling SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
  as Hceil.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|].
split; [eapply ajournal_gx_mono_k; [exact HJ2 | lia]|].
split; [exact HP|]. split; [reflexivity|].
split; [exact Hfds|]. split; [exact Hfs|].
split; [exact (akept_run pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W mem2 (spZ regs - K) (spZ regs) E
                 HAR ltac:(lia) Hwin UN Hgrow Hpw)|].
split; [exact (rem_ashadow_kept lyc Sc lyc Sc W memc mdc W mem2 (spZ regs - K) (spZ regs) E
                 HAR ltac:(lia) UN HE)|].
exact HQ.
Qed.

End b.
End a.
