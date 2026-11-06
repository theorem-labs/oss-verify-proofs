(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfRoomPre.v, sha256 fcc5b2a4a4acdec4d1cf96fa601d062759275b61e4cd97d5b92fbb02e14b3bd6 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: acall_pre_cf_intro's stack-bottom premise is A7d's `ly_bot ly + ACALL_PREFIX < spZ regs` (a3e599d9f79e Reusable/YGcfRoomPre.v:38), following acall_pre_cf (YG0dcf.v). *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the INPUT-DRIVEN ROOM.
   acall_pre_cf (YG0dcf.v) carries five conjuncts beyond cgif's call form. Two are free: qmeter_cf follows
   from qtight and Wf_cf (mroom_cf_of_live, YG08cf.v), and the free path's FA_GROW headroom from
   abudget_room_cf (YG08cf.v), since FA_GROW_MAX + FA_GROW_MAX / 8 = 19,327,352,832 <= 2 ^ 36. The other
   three come from the PROGRAM, through the input, and no allocator invariant bounds them: ROOM_cf collects them,
   so a walk carries one named premise. Their maintenance across malloc_cf / free_cf is in YGcfRoomKeep.v. No
   address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG08cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The three input-driven conjuncts of acall_pre_cf: the live-secondary count (strict, so a
   secondary malloc's +1 keeps wfc_sec_live), the error-buffer room for one class-full report,
   and the batch class's room (it keeps cgif's vacuous class-full arm). *)
Definition ROOM_cf (S : astate) : Prop :=
Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\ ERRB_ROOM S /\ batch_room_cf S.

Lemma FA_GROW_MAX_le : 0 <= FA_GROW_MAX + FA_GROW_MAX / 8 <= 2 ^ 36.
Proof. unfold FA_GROW_MAX, kFreeArrayMax. split; apply Z.leb_le; reflexivity. Qed.

(* acall_pre_cf from ARcf, qtight, ROOM_cf, the unit's hull admission cf_hull_ok (the driver's run meter at the call),
   the read-only bytes arodata_ok_cf at the call (field round 3; part 3c: no memnorm) and cgif's own non-state
   premises, which are unchanged. qmeter_cf and the FA_GROW headroom are derived. *)
Theorem acall_pre_cf_intro : forall segs B ly S Hp W regs mem md ch,
ARcf segs B ly S Hp W mem md -> qtight S -> ROOM_cf S -> cf_hull_ok S ->
arodata_ok_cf segs B mem ->
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + ASTACK <= spZ regs -> ly_bot ly + ACALL_PREFIX < spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
chain_pre ly (aview segs (w_H W) mem) regs ch ->
acall_pre_cf segs B ly S Hp W regs mem md ch.
Proof.
intros segs B ly S Hp W regs mem md ch HAR HQ [R1 [R2 R3]] HO AD H1 H2 H3 H4 H5 H6 H7 H8 H9.
pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as W0. unfold Wf_cf in W0.
pose proof (qtight_qloose S HQ) as QL.
assert (QM : qmeter_cf S) by (split; [exact HQ | exact (mroom_cf_of_live _ _ _ _ _ W0 QL HO)]).
assert (FA : abudget_cf S + (FA_GROW_MAX + FA_GROW_MAX / 8) <= CF_MAX)
by exact (abudget_room_cf _ _ _ _ _ _ W0 QL HO FA_GROW_MAX_le).
rewrite Z.add_assoc in FA.
unfold acall_pre_cf.
exact (conj HAR (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
(conj QM (conj R1 (conj R2 (conj FA (conj R3 (conj HO AD)))))))))))))))).
Qed.

(* The converse direction a walk uses to re-establish ROOM_cf after a call: acall_pre_cf
   contains it. *)
Lemma ROOM_cf_of_acall_pre_cf : forall segs B ly S Hp W regs mem md ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf S.
Proof.
intros segs B ly S Hp W regs mem md ch H. unfold acall_pre_cf in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R1 & R2 & _ & R3 & _).
exact (conj R1 (conj R2 R3)).
Qed.

End P.
