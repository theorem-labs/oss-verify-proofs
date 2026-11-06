(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainT3.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 8c43991cc887) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 4 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the TRANSFER's list facts - after Drain moves the thread cache
   onto the global cache (0x33838-0x338a4, the relink of the global list's last next word), the quarantine is one
   linked list, the global list's batches followed by the thread list's; and a linked list survives a walk whose
   window avoids its cells.  Both arms of the drain need these: the return arm states the transferred cells in
   DMiface.dmem_q, and the no-merge arm hands the same list to the dequeue loop.
   rule 24: no function proved (kind: list and memory-shape lemmas; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [lcn_keep]: a linked list survives a frame that avoids its cells;
   - [lcn_transfer]: the two caches, with the relink, are one linked list.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0h YK14 YK1b YK1a YK15 YK18 YP03 YP02 YP0k YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMwalkIF DMdrainK DMdrainN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable ly : alayout.
Variable iw : chunk -> Z.
Variable H : word -> bool.

(* A linked list survives a frame whose window avoids its cell words. *)
Lemma lcn_keep : forall (Win : Z -> Prop) (mem mem' : word -> option byte) (l : list batch) (z : Z),
(forall x : word, ~ Win (bv_unsigned x) -> mem' x = mem x) ->
(forall b, In b l -> 0 <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64 /\
   forall a, addrb ly b <= a < addrb ly b + 24 + 8 * zl (b_items b) -> ~ Win a) ->
lcn ly iw (mrestrict H mem) l z -> lcn ly iw (mrestrict H mem') l z.
Proof.
intros Win mem mem' l. induction l as [|b t IH]; intros z HM HB HL; [exact I|].
cbn [lcn] in HL |- *. destruct HL as [Hb Ht]. destruct (HB b (or_introl eq_refl)) as (A1 & A2 & A3).
split.
- destruct Hb as (V0 & V8 & V16 & VS). unfold bcell. splits.
  + apply (val_mem_frame H mem mem' _ 8 _); [|exact V0].
    intros k Hk. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    apply HM. rewrite unsigned_lit_small by lia. apply A3. lia.
  + apply (val_mem_frame H mem mem' _ 8 _); [|exact V8].
    intros k Hk. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    apply HM. rewrite unsigned_lit_small by lia. apply A3. lia.
  + apply (val_mem_frame H mem mem' _ 8 _); [|exact V16].
    intros k Hk. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    apply HM. rewrite unsigned_lit_small by lia. apply A3. lia.
  + intros j k Hj. pose proof (proj1 (nth_error_Some (b_items b) j) ltac:(rewrite Hj; discriminate)) as LT.
    apply (val_mem_frame H mem mem' _ 8 _); [|exact (VS j k Hj)].
    intros i Hi. apply HM. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    rewrite unsigned_lit_small by (unfold zl in *; lia). apply A3. unfold zl in *. lia.
- apply (IH z HM); [intros b' Hb'; exact (HB b' (or_intror Hb')) | exact Ht].
Qed.

(* The transfer: the global list's last next word now points at the thread list's first batch, so the two
   caches are one linked list (the machine's 0x33838-0x338a4; YFgj.at_RETD's last clause). *)
Lemma lcn_transfer : forall (m : word -> option byte) (G T : list batch),
lcn ly iw m G 0 -> lcn ly iw m T 0 ->
(G <> [] -> val_mem tfibsegs m (la ly G) 8 (fa ly T 0)) ->
lcn ly iw m (G ++ T) 0.
Proof.
intros m G T HG HT HR. apply (lcn_app_link ly iw m G T 0); [|exact HT].
destruct G as [|b t]; [exact I|].
apply (lcn_relink ly iw m (b :: t) (fa ly T 0)); [exact HG|]. intros _. apply HR. discriminate.
Qed.
End e.
End c.
