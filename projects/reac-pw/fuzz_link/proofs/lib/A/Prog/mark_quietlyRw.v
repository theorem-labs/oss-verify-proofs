(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 94 of its 132 lines of code are new or changed and 1267 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the call of rewind's wrapper on the caller's journal, for mark_quietly's walk
   (+0x50 `jal 0x430d4`: the later arm flushes the previous line into g_said).

   aj_gx_rewind_at lifts lib/A/Rt/LinkMfDefs.v `arewind_mf_realizes` (rewind(f) at the wrapper's jump, on link's
   memory FILE link_amf) onto the caller's journal `ajournal_gx G XO OUT` (lib/A/W_journalG.v), in the shape of
   link_ajkit.v aj_gx_call_at. The contract's pre-state comes from link_ajkit.v aj_gx_ecall_pre at the window
   ARW_STK (ESTACK <= ARW_STK). rewind writes its window, the FILE's first AMF_ZEROED bytes, g_said (the cookie's
   buffer) and errno (mwrite's ENOSPC arm). The first three are bytes the journal lets a callee write (the window
   by awr_byte, the other two by the two `ajw` premises). errno is no such byte, and the journal does not track it
   (LinkWalkErrno.v's header). So the journal moves in two steps: first to the call's memory with rewind's errno
   bytes (LinkWalkErrno.v ajournal_gx_exec_e, errno bytes only), then to rewind's memory (link_ajkit.v
   ajournal_gx_after_write, at the AR the contract gives). The return config is the post's `cfg_at segs (raZ regsT)`
   with ra = raw.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalkErrno.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ENV : api_env segs B.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma aj_gx_rewind_at : forall pc, arewind_mf_realizes segs B link_amf pc ->
  forall G XO OUT (W : world segs) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
    f kk fl om wend wpos wbase pos len (pb : list Z),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ARW_STK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 f ->
  In (f, AMF_BLOCK) (ablocks B lyc Sc) ->
  amf_k segs link_amf (rdW W memT) f kk ->
  amf_dyn segs link_amf (rdW W memT) f fl om wend wpos wbase pos len ->
  amf_pend segs (rdW W memT) f pb -> Z.of_nat (length pb) = kk ->
  amf_buf_ok segs B link_amf ARW_STK lyc Sc W regsT memT ->
  rdword (aview segs (w_H W) memT) LA_GOT_GUARD = Some LA_GUARD ->
  (exists g, rdword (aview segs (w_H W) memT) LA_GUARD = Some g) ->
  (forall a, f <= a < f + AMF_ZEROED -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  (forall a, amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf ->
     ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\
       amf_k segs link_amf (rdW W mem2) f 0 /\
       amf_dyn segs link_amf (rdW W mem2) f AF_NORD om 0 0 0
         (if amf_n1 link_amf kk pos <? kk then pos + amf_n1 link_amf kk pos else 0)
         (Z.max len (pos + amf_n1 link_amf kk pos)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ARW_STK <= a < spZ regsT) ->
          ~ (f <= a < f + AMF_ZEROED) ->
          ~ (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) ->
          ~ (as_errno B <= a < as_errno B + 4) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       (forall a, spZ regsT - ARW_STK <= a < spZ regsT -> apresent (w_H W) mem2 a)).
Proof.
intros pc HRW G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
  f kk fl om wend wpos wbase pos len pb HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Ha0 Hblk Hk Hdyn Hpend Hlen Hbuf
  Hgot Hguard HwF HwB.
assert (Hes : ESTACK <= ARW_STK) by (unfold ARW_STK; lia).
destruct (aj_gx_ecall_pre SK segs B ARW_STK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  Hes H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (Hpre & Hroom & Hwin).
eapply SRr_mono.
{ exact (HRW lyc Sc W regsT memT mdc f kk fl om wend wpos wbase pos len pb Hpre Hroom Hwin Ha0 Hblk Hk Hdyn Hpend
    Hlen Hbuf Hgot Hguard). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & Hrp & Hsame & Hk2 & _ & _ & Hdyn2 & Hkept & Hgr & Hwin2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|exact (conj Hrp (conj Hsame (conj Hk2 (conj Hdyn2 (conj Hkept (conj Hgr Hwin2))))))].
(* the call's memory with rewind's errno bytes *)
set (memE := fun x : word => if aerrnob B (bv_unsigned x) then mem2 x else memT x).
assert (EE : forall x, aerrnob B (bv_unsigned x) = true -> memE x = mem2 x)
  by (intros x Hx; unfold memE; rewrite Hx; reflexivity).
assert (EN : forall x, aerrnob B (bv_unsigned x) = false -> memE x = memT x)
  by (intros x Hx; unfold memE; rewrite Hx; reflexivity).
(* 1. the errno bytes *)
assert (HJE : ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memE mdc k).
{ apply (ajournal_gx_exec_e SK segs B LAWS segs_low ENV ERRF G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT
    mdc k memE mdc (aerrno B) HG HJX).
  - intros x Hx. unfold mrestrict. destruct (w_H W x); [reflexivity|].
    apply EN. apply aerrnob_false. exact Hx.
  - intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H W x) eqn:Eh; [exact Hx|].
    destruct (aerrnob B (bv_unsigned x)) eqn:Ee; [rewrite (EE x Ee) | rewrite (EN x Ee); exact Hx].
    destruct (memT x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
    assert (Hp : apresent (w_H W) memT (bv_unsigned x)).
    { unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
    destruct (Hgr _ Hp) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. congruence.
  - intros x Hh. destruct (aerrnob B (bv_unsigned x)) eqn:Ee; [|exact (EN x Ee)].
    exfalso. apply aerrnob_spec in Ee.
    rewrite (hidden_not_img segs W x (proj1 (proj2 ENV) _ Ee)) in Hh. discriminate Hh.
  - apply same_but_materialized_refl.
  - intros a Ha. right. exact Ha. }
(* 2. the other bytes: the window, the FILE's first AMF_ZEROED bytes, g_said *)
apply (ajournal_gx_after_write SK segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memE mdc k
  mem2 md2 (fun a => (spZ regsT - ARW_STK <= a < spZ regsT) \/ (f <= a < f + AMF_ZEROED) \/
     (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf)) HG HJE).
- intros a Ha Hn. destruct (aerrnob B (bv_unsigned (Z_to_bv 64 a))) eqn:Ee.
  + apply aview_eq_of. unfold mrestrict. rewrite (EE _ Ee). reflexivity.
  + assert (E1 : aview segs (w_H W) memE a = aview segs (w_H W) memT a)
      by (apply aview_eq_of; unfold mrestrict; rewrite (EN _ Ee); reflexivity).
    rewrite E1. rewrite unsigned_lit_small in Ee by lia. apply aerrnob_false in Ee.
    apply (Hkept a Ha).
    * intros H'. apply Hn. left. exact H'.
    * intros H'. apply Hn. right. left. exact H'.
    * intros H'. apply Hn. right. right. exact H'.
    * exact Ee.
- intros a Hp. destruct (aerrnob B (bv_unsigned (Z_to_bv 64 a))) eqn:Ee.
  + destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- (EE _ Ee). exact Hb.
  + apply Hgr. destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- (EN _ Ee). exact Hb.
- exact Hsame.
- intros a [Ha | [Ha | Ha]].
  + left. split; [left; lia | lia].
  + exact (HwF a Ha).
  + exact (HwB a Ha).
- exact HAR2.
Qed.

End r.

Print Assumptions aj_gx_rewind_at.
