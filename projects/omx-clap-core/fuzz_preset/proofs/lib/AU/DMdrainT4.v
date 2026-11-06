(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainT4.v (commit ce1a656b52b7, file sha256 72c9686a0a36) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainT4.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 b70b1e40fef5) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT4.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the list surgery the TRANSFER needs - splitting a linked list at
   an append, and rebuilding the last batch's cell when the walk rewrote its next word (Drain's relink at
   0x33890-0x338fc, YFgj.at_RETD's last clause).  With DMdrainT3.lcn_keep and lcn_transfer these give the joined
   quarantine list at a drain cut, which DMiface.dmem_q states.
   rule 24: no function proved (kind: list and memory-shape lemmas; the lane's reuse search is
   the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [lcn_app_split]: the inverse of DMdrainK.lcn_app_link;
   - [bcell_relink]: the last batch's cell at the cut, its next word rewritten, the rest framed;
   - [lcn_snoc]: a list and its last batch join.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK0h YK14 YK1b YK1a YK15 YK18 YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP03 YP02 YP0k YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF DMdrainK DMdrainT3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable ly : alayout.
Variable iw : chunk -> Z.
Variable H : word -> bool.

Lemma lcn_app_split : forall m l1 l2 z, lcn ly iw m (l1 ++ l2) z -> lcn ly iw m l1 (fa ly l2 z) /\ lcn ly iw m l2 z.
Proof.
intros m l1. induction l1 as [|b t IH]; intros l2 z HL; [split; [exact I | exact HL]|].
cbn [app lcn] in HL. destruct HL as [Hb Ht]. destruct (IH l2 z Ht) as [H1 H2].
split; [|exact H2]. cbn [lcn]. split; [|exact H1].
rewrite (fa_app_k ly t l2 z) in Hb. exact Hb.
Qed.

(* The last batch's cell after the walk rewrote its next word: the other three fields are framed. *)
Lemma bcell_relink : forall (Win : Z -> Prop) (mem mem' : word -> option byte) b nx z',
(forall x : word, ~ Win (bv_unsigned x) -> mem' x = mem x) ->
0 <= addrb ly b -> addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64 ->
(forall a, addrb ly b + 8 <= a < addrb ly b + 24 + 8 * zl (b_items b) -> ~ Win a) ->
val_mem tfibsegs (mrestrict H mem') (addrb ly b) 8 z' ->
bcell ly iw (mrestrict H mem) b nx -> bcell ly iw (mrestrict H mem') b z'.
Proof.
intros Win mem mem' b nx z' HM A1 A2 HA HZ (V0 & V8 & V16 & VS).
assert (HZl : 0 <= zl (b_items b)) by (unfold zl; lia).
unfold bcell. splits.
- exact HZ.
- apply (val_mem_frame H mem mem' _ 8 _); [|exact V8].
  intros k Hk. apply HM. rewrite unsigned_lit_small by lia. apply HA. lia.
- apply (val_mem_frame H mem mem' _ 8 _); [|exact V16].
  intros k Hk. apply HM. rewrite unsigned_lit_small by lia. apply HA. lia.
- intros j k Hj. pose proof (proj1 (nth_error_Some (b_items b) j) ltac:(rewrite Hj; discriminate)) as LT.
  apply (val_mem_frame H mem mem' _ 8 _); [|exact (VS j k Hj)].
  intros i Hi. apply HM. rewrite unsigned_lit_small by (unfold zl in *; lia).
  apply HA. unfold zl in *. lia.
Qed.

(* A list and its last batch join: the inverse direction of the append. *)
Lemma lcn_snoc : forall m init lastb z',
lcn ly iw m init (addrb ly lastb) -> bcell ly iw m lastb z' -> lcn ly iw m (init ++ [lastb]) z'.
Proof.
intros m init lastb z' HI HB. apply (lcn_app_link ly iw m init [lastb] z').
- cbn [fa addrb]. exact HI.
- cbn [lcn fa]. split; [exact HB | exact I].
Qed.
End e.
End c.
