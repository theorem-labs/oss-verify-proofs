(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainS.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 c89843b58e01) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainS.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the value facts of the segment at 0x33a90 (Recycle after
   MergeBatches, DMseg_rj.v) at the merge's post values, i.e. every field of DMseg_rj.free_hyps except its seed:
   fh_Hsp (DMseg_rj.v:79), fh_Hsp_al (:80), fh_Hl (:81) and fh_Ht (:82), with
     lcnt   = the kept list's length,          lfirst = its first address,
     lbytes = the entry bytes less kBatchBytes per extracted batch,
     tcnt   = the extracted list's length,     tlast  = its last address,
   which is what DMwalkIF.mb_post leaves at the return (DMwalkIF.v mb_post).  The seed (fh_SEED, st_ok at
   0x33a90 over DMseg_rj.SS0) is built in the next file from the same facts, as DMdeq.SEED1_ok (DMdeq.v:373)
   builds YFgl's.
   rule 24: no function proved (kind: arithmetic over the model's lists; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFeu YFey.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DMwalkIF DMdrainQ DMdrainR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section vals.
Variable ly : alayout.
Variables (L0 Lk ex : list batch).
Hypothesis HB0 : forall b, In b L0 ->
  kHighMemBeg <= addrb ly b /\ addrb ly b + kBatchBytes <= ASAN_CEIL /\ addrb ly b mod 8192 = 0 /\
  (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HN0 : forall k, In k (flat_map b_items L0) -> 0 <= ck_n k.
Hypothesis HS0 : sum_bytes L0 <= 2 ^ 31.
Hypothesis HIN : forall b, In b (Lk ++ ex) -> In (b_self b) (map b_self L0).
Hypothesis HSUM : sum_bytes Lk + kBatchBytes * Z.of_nat (length ex) = sum_bytes L0.
Hypothesis HEX : forall b, In b ex -> b_items b = [].
Hypothesis HITEMS : flat_map b_items Lk = flat_map b_items L0.

Local Notation lcnt := (Z.of_nat (length Lk)).
Local Notation lfirst := (fa ly Lk 0).
Local Notation lbytes := (sum_bytes L0 - kBatchBytes * Z.of_nat (length ex)).
Local Notation tcnt := (Z.of_nat (length ex)).
Local Notation tlast := (la ly ex).

(* DMseg_rj.free_hyps' fh_Hl (DMseg_rj.v:81). *)
Lemma rj_Hl : 0 <= lcnt <= 2 ^ 40 /\ 0 <= lfirst < ASAN_CEIL /\ lfirst mod 8192 = 0 /\ 0 <= lbytes <= 2 ^ 31.
Proof.
assert (KL : 0 <= Z.of_nat (length Lk) <= 2 ^ 40) by (eapply kept_len_range; eassumption).
assert (F : 0 <= fa ly Lk 0 < ASAN_CEIL /\ fa ly Lk 0 mod 8192 = 0).
{ eapply fa_range; try eassumption. intros b Hb. apply in_app_iff. left. exact Hb. }
assert (KB : 0 <= sum_bytes L0 - kBatchBytes * Z.of_nat (length ex) <= 2 ^ 31)
  by (eapply kept_bytes_range; eassumption).
destruct F as [F1 F2]. splits; first [exact F2 | lia].
Qed.

(* DMseg_rj.free_hyps' fh_Ht (DMseg_rj.v:82). *)
Lemma rj_Ht : 0 <= tcnt <= 2 ^ 40 /\ 0 <= tlast < ASAN_CEIL /\ tlast mod 8192 = 0.
Proof.
assert (EL : 0 <= Z.of_nat (length ex) <= 2 ^ 40) by (eapply ext_len_range; eassumption).
assert (L : 0 <= la ly ex < ASAN_CEIL /\ la ly ex mod 8192 = 0).
{ eapply la_range; try eassumption. intros b Hb. apply in_app_iff. right. exact Hb. }
destruct L as [L1 L2]. splits; first [exact L2 | lia].
Qed.

(* The dequeue loop's byte premise: the kept list's bytes are what the loop pops from (DMdeq.tfib_deq_ok's
   `qc_bytes gm = sum_bytes Lk`), and they are the byte word the merge left at inst + o_quar + 184. *)
Lemma rj_kept_bytes : sum_bytes Lk = lbytes.
Proof. lia. Qed.

End vals.
End d.
