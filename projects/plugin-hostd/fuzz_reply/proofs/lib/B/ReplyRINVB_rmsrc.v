(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file.  proves no function (rule 24; kind: one model rule): RI_rm_src, the
   remove arm's model rule that the picked source's expected list is empty, at RINV := ReplyRINVB.fr_RINV (image B,
   fuzz_reply.asan-ubsan): the image-B twin of lib/A/ReplyRINV_rmsrc.v.
   The rule is a new Section hypothesis of the remove arm (lib/B/W_LLVMFuzzerTestOneInput_remove.v Section rmw and its
   _x twin), the remove-side twin of the drain arm's RI_src.  Its text, as the remove arm states its other RINV rules
   (the binders cx t m si h j0, then RINV, then rm_at):
     forall cx t m si h j0, RINV cx t m -> rm_at cx m si h j0 -> hl_recs (hs_expected h) = []
   with rm_at := lib/B/W_LLVMFuzzerTestOneInput_remove.v's rm_at, stated here at RINV := ReplyRINVB.fr_RINV.
   Why it holds: rm_at says slot si < 4 holds h; fr_relay pairs every open slot with a relay entry (fr_pair_of_open,
   from the closed-slot clause), and that pair's fr_pair_ok says the source's expected list is empty (its clause from
   SlotInv.v:260: between operations check_no_loss has emptied it).
   RELOCATED, not re-proved: every proof is the image-A twin's, moved to lib/B's names.
     - from lib/A/ReplyRINV_rmsrc.v: RI_rm_src_holds, RI_rm_src_sat;
     - from lib/A/ReplyRINV.v: fr_Forall2_comb, fr_pair_of_open (A has them; ReplyRINVB.v has not);
     - from lib/A/ReplyRINV_a12.v: the open-entry state a12_* that RI_rm_src_sat uses (a12_cx .. a12_m0, a12_pick,
       a12_RINV0, a12_rm_at0).
   A -> B: fr_RINV, fr_relay, fr_pair_ok are lib/B/ReplyRINVB.v's (the same text as lib/A/ReplyRINV.v's), and rm_at /
   rm_kb / rm_ent are lib/B/W_LLVMFuzzerTestOneInput_remove.v's (the same text as lib/A's); _cut.v's lfcx / LFCX,
   lmod / LM, OPS_MAX, in_byte, nopen and pick have the same text on both images.  So no proof step changes.
   Imports: lib/B/ReplyRINVB.v's import list with its W_LLVMFuzzerTestOneInput_head replaced by
   W_LLVMFuzzerTestOneInput_remove, then ReplyRINVB, both Imported (A's file only Requires _remove and ReplyRINV and
   names them qualified): the relocated text (from ReplyRINV.v and ReplyRINV_a12.v) names fr_RINV, fr_pair_ok, the
   other fr_* names and rm_at without a module prefix, as A's files do; SlotInv.* and gestures_end_b_c.* keep their
   short prefix and come from ReplyRINVB.v's lib.Prog Require line.
   No image address is read: every numeral is a model constant of fr_RINV's text (FIRST_FD 100, 4 slots, CLIENT_FD 3,
   op modulus 10; ReplyRINVB.v's CONSTANT-SWAP TABLE gives each B value) or a byte / length of the constructed state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c gestures_end_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
(* RelocB's sink-instance guard (after the Import of YE2k), as lib/B/ReplyRINVB.v Requires it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section rinvb_rmsrc.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== helpers of lib/A/ReplyRINV.v, relocated *)
Lemma fr_Forall2_comb : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In (x, y) (combine l1 l2) /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* an open slot is some entry's source *)
Lemma fr_pair_of_open : forall m t hj i h, Forall2 (fr_pair_ok m t) (lm_es m) hj ->
  (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) ->
  (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  exists e p, In (e, p) (combine (lm_es m) hj) /\ fr_pair_ok m t e p /\ snd p = i /\ fst p = h.
Proof.
  intros m t hj i h HF Hcl Hi Hh.
  destruct (SlotInv.slot_open hj i) eqn:Ho; [|rewrite (Hcl i Hi Ho) in Hh; discriminate Hh].
  unfold SlotInv.slot_open in Ho. apply existsb_exists in Ho as (x & Hx & Hxi).
  apply Nat.eqb_eq in Hxi. subst x. apply in_map_iff in Hx as (p & Hpi & Hp).
  destruct (fr_Forall2_comb _ _ _ _ _ HF p Hp) as (e & Hin & HR).
  exists e, p. split; [exact Hin|]. split; [exact HR|]. split; [exact Hpi|].
  destruct HR as (_ & Hn & _). rewrite Hpi, Hh in Hn. injection Hn as Ef. exact (eq_sym Ef).
Qed.

(* ================================================================== the remove arm's RI_rm_src at RINV := fr_RINV *)
Lemma RI_rm_src_holds : forall cx t m si h j0,
  ReplyRINVB.fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> hl_recs (hs_expected h) = [].
Proof.
  intros cx t m si h j0 (_ & HR & _ & _) (_ & _ & _ & _ & Hsi & Hh & _).
  destruct HR as (_ & _ & _ & _ & hj & HF & _ & Hcl & _).
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & _ & HRp & _ & <-).
  destruct HRp as (_ & _ & _ & _ & _ & _ & Hexp & _). exact Hexp.
Qed.

(* ================================================================== the premises are satisfiable (VERIFY rule 10)
   lib/A/ReplyRINV_a12.v's open-entry state, relocated: from any call context cx0 (its layout, state, world,
   registers, memory and model are kept; the input is replaced), one open slot 0 with source a12_src (fd 100, held
   list [(0, "a")]), one relay entry a12_ent0 (fd 100, not at eof, one key of text "a"), op 4 at the cursor 6, and
   the controller CTL 3 0 0 0 0. *)
Definition a12_cx (cx0 : lfcx) (n : Z) (pl : list byte) : lfcx :=
  LFCX (c_ly cx0) (c_S cx0) (c_W cx0) (c_regs cx0) (c_mem cx0) (c_md cx0) 0 n pl 0.
Definition a12_pad : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition a12_E0 : hlist := HL 0 0 [] [].
Definition a12_src (H : hlist) : hsrc := HS 100 1 0 0 a12_E0 0 0 [] 0 0 [] a12_E0 H.
Definition a12_pl : list byte := repeat (Z_to_bv 8 4) 10.
Definition a12_H1 (x : list byte) : hlist := HL 0 8 [(0, x)] [].
Definition a12_ks1 (x : list byte) : list (Z * list byte * list byte) := [(0, x, [])].
Definition a12_a : list byte := [Z_to_bv 8 97].   (* "a" *)
Definition a12_ent0 : rentry := RE 100 0 0 a12_pad 0 0 0 0 0 a12_pad (a12_ks1 a12_a) [] [].
Definition a12_m0 : lmod :=
  LM 6 [Some (a12_src (a12_H1 a12_a)); None; None; None] 0 [a12_ent0] (CTL 3 0 0 0 0) [] 0 0 0 0 1.
Lemma a12_pick : forall h kb, pick [Some h; None; None; None] kb = Some 0%nat.
Proof. intros h kb. unfold pick. cbn -[Z.modulo]. rewrite Z.mod_1_r. reflexivity. Qed.
(* the open entry's state: fr_pair_ok's eof clause is met (skip 0 = overlong 0, the unfinished line [] = hs_W []) *)
Lemma a12_RINV0 : forall cx0, fr_RINV (a12_cx cx0 10 a12_pl) 0 a12_m0.
Proof.
  intros cx0. split; [|split; [|split]].
  - unfold fr_count, nopen, OPS_MAX, a12_m0. cbn [lm_nfd lm_hs List.filter length Z.of_nat]. lia.
  - unfold fr_relay, a12_m0. cbn [lm_hs lm_es lm_nfd lm_k length].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok, a12_ent0, a12_pad.
      cbn [re_eof re_pad1 re_pad2 re_keys re_skip length].
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros [] | left; reflexivity]. }
    exists [(a12_src (a12_H1 a12_a), 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok, a12_src, a12_ent0.
      cbn [fst snd nth lm_hs re_eof re_fd hs_fd re_keys hs_held hs_expected hs_off hl_recs hl_cap].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|].
      split; [intros y; split; intros Hy; exact Hy|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [reflexivity|]. split; [left; reflexivity|]. split; [cbn; lia|].
      split; [unfold pending_stream, a12_E0; cbn [hs_pending hl_recs length Z.of_nat]; unfold SlotInv.WRITE_MAX; lia
             | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *; first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost, a12_ent0, a12_src, pending_stream, a12_E0, a12_ks1, a12_a,
      gestures_end_b_c.keys_total, gestures_end_b_c.key_text.
    cbn. lia.
  - unfold a12_cx. cbn [c_n]. lia.
  - unfold fr_gone, a12_m0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros E; [repeat split | discriminate E].
Qed.
Lemma a12_rm_at0 : forall cx0, rm_at (a12_cx cx0 10 a12_pl) a12_m0 0 (a12_src (a12_H1 a12_a)) 0.
Proof.
  intros cx0. unfold rm_at, a12_m0. cbn [lm_k lm_O lm_hs lm_es length].
  split; [unfold a12_cx; cbn [c_n]; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply a12_pick|].
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. intros q Hq. lia.
Qed.
Lemma RI_rm_src_sat : lfcx -> exists cx t m si h j0,
  ReplyRINVB.fr_RINV cx t m /\ W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0.
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, a12_m0, 0%nat, (a12_src (a12_H1 a12_a)), 0%nat.
  split; [exact (a12_RINV0 cx0) | exact (a12_rm_at0 cx0)].
Qed.

End rinvb_rmsrc.
