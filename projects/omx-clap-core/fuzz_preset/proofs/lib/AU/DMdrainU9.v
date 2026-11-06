(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainU9.v (commit ce1a656b52b7, file sha256 c43a342ba1ef) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 3 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU9.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 bd6674d041da) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 4 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU9.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (4 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the INPUT of the drain's shared recycle tail - what each recycle
   arm hands over at Recycle's call of DoRecycle (0x345c8), so that one tail (the cut's invariant, DoRecycle,
   the epilogue, the drain's leaf) serves both the no-merge arm (DMdrainV0) and the merge arm (DMdrainV1).
   The arms differ only in STAGE 1, the walk from Drain's entry 0x342b8 to the dequeue loop's head 0x34558:
   the no-merge arm writes YFgj.WIN; the merge arm also writes MergeBatches' frame [sp0 - 96, sp0 - 80) and the
   cell words of the transfer list, of gm and of ex, and leaves s0 .. s4 holding Recycle's arguments.  So
   stage 1 is stated over its written set [F1], which must lie inside the cut's window DMiface.dwin_q, with
   presence kept off the quarantine header, every batch's size / count / slot words in place, the six words
   Recycle's prologue saved (the epilogue's seed, DMdrainT9.v:46-52), the thread header's four zero words, and
   register equality only on DMsegD.SREGS_M (DMsegD.v:48).  STAGE 2 ends in the released dequeue loop's post
   DMdeq.ATDR (DMdeq.v:193-207) at DoRecycle's call - through the loop, or, on the merge arm's at_RJX exit, read
   off the call state directly (DMdrainV1's atdr_of_cells).
   rule 24: no function proved (kind: a statement only - the tail's input; the lane's reuse search is
   the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF DMdrainK.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMsegD DMdeq.
Import ListNotations.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.

(* [recyc_cut_in ... F1 regs1 mem1 gk P W' c']: the drain entered at [regs] / [mem] reaches the configuration
   [c'] at DoRecycle's call, with the temp list [P] at Recycle's sp and the kept global cache [gk]; [regs1] /
   [mem1] are the registers and memory stage 2 starts from - the dequeue loop's head, or, on the merge arm's
   at_RJX exit (Recycle calls DoRecycle without dequeueing, DMdrainV1's atdr_of_cells), the DoRecycle-call
   state itself - and [F1] what stage 1 may have written. *)
Definition recyc_cut_in (inst : Z) (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (F1 : Z -> Prop) (regs1 : bvmap 5 word) (mem1 : word -> option byte)
(gk : qcache) (P : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
let sp0 := bv_unsigned (getr regs 2) in
let S' := set_qglobal gk (set_qthread qc0 X) in
let m1 := mrestrict (w_H W) mem1 in
(* the drain's entry and the model's recycle cut (DMiface.drain_recyc, DMiface.v:54-58) *)
drain_pre_cf B ARX L24 QB inst ly X W regs mem md /\
drain_recyc X S' P /\
(* stage 1, the arm's own walk to the dequeue loop's head 0x34558: its written set, inside the cut's window *)
(forall x : word, ~ F1 (bv_unsigned x) -> mem1 x = mem x) /\
(forall a, F1 a -> dwin_q inst ly sp0 X S' P a) /\
(* presence off the quarantine's header *)
(forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem1 a) /\
(* the cut's two lists: their batch objects are placed in the primary space, 8192 apart, with at most
   kBatchSlots items each (on the merge arm these are MergeBatches' batches, not X's records) *)
(forall b, In b (P ++ qc_list gk) ->
   ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
   addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL) /\
(forall b, In b (P ++ qc_list gk) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat) /\
List.NoDup (map b_self (P ++ qc_list gk)) /\
(* ... and they are X's batch objects: the drain writes only owned cells (DMiface.di_qowned's bobj) *)
(forall b, In b (P ++ qc_list gk) -> exists b0, In b0 (all_batches X) /\ b_self b0 = b_self b) /\
(* every batch of the cut's two lists keeps its size, count and slot words (the next words are stage 2's) *)
(forall b, In b (P ++ qc_list gk) ->
   val_mem tfibsegs m1 (addrb ly b + 8) 8 (b_bytes b) /\
   val_mem tfibsegs m1 (addrb ly b + 16) 8 (zl (b_items b)) /\
   (forall j k, nth_error (b_items b) j = Some k ->
      val_mem tfibsegs m1 (addrb ly b + 24 + 8 * Z.of_nat j) 8 (DMdrainK.iwB B ly k))) /\
(* the six words Recycle's prologue saved: ra, s0, s1, s2, s3, s4 at Drain's entry *)
val_mem tfibsegs m1 (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem tfibsegs m1 (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem tfibsegs m1 (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs m1 (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs m1 (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs m1 (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\
(* the thread cache's header, zero since the transfer *)
val_mem tfibsegs m1 (ly_T ly + t_qc) 8 0 /\ val_mem tfibsegs m1 (ly_T ly + t_qc + 8) 8 0 /\
val_mem tfibsegs m1 (ly_T ly + t_qc + 16) 8 0 /\ val_mem tfibsegs m1 (ly_T ly + t_qc + 24) 8 0 /\
(* the loop's stack pointer and the registers stage 1 keeps *)
bv_unsigned (getr regs1 2) = sp0 - 80 /\
(forall r : bv 5, In r DMsegD.SREGS_M -> getr regs1 r = getr regs r) /\
(* DoRecycle's a2 at the loop's head (YFgj.at_L0 / DMsegD.at_MB: T + t_cache), which the loop keeps *)
getr regs1 12 = w64 (ly_T ly + t_cache) /\
(* the kept cache's byte count is its list's weight (tfib_deq_ok's premise, carried through the pops) *)
qc_bytes gk = sum_bytes (qc_list gk) /\
(* stage 2, the released dequeue loop, to DoRecycle's call *)
DMdeq.ATDR W ly md regs1 mem1 P (qc_list gk) W' c'.
End g.
End f.
