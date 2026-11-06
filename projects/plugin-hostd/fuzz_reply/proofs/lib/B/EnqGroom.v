(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/EnqGroom.v (commit 384adc62265, B2 FINAL; file sha256 9b212701fdea) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/EnqGroom.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B2; integrator ReallocPrimary).
   rule 24: proves function __sanitizer::QuarantineCache<__asan::QuarantineCallback>::Enqueue (the ROOM arm, the
   last batch has a free slot), frame-generic, at cgif_file_fuzzer's asan-ubsan image (Enqueue 0x360ec).  Reuse
   search: LOOKUP-B2-enqueue.txt (sha256 7fa7207b8221; internal record) 2026-10-29T23:07:48Z exit 3; rule-24 check B2LookupCheck: CONFIRM.

   The room arm over the interface EnqGbase.EnqIfaceRoom.  Generalized from the released arm (YFg4 with YFf1,
   1,055 lines) as MnEnqArms.v:51-112 runs it: every call there to a cgif model lemma, and every mention of
   cgif's image, is a parameter here.

   What this file proves, once for every instance and every image:
   - the model's step at the arm (YFfp.enqueue_room_eq);
   - the run, from the field [ir_walk] to the field [ir_post];
   - the RAW frame of CLenq.acall_post_x, which the released post (a view frame) does not carry: it follows from
     the walk's own window frame ([ir_frame]) and the field [ir_owned];
   - the memnorm keep of the post of record, from the same window frame and the field [ir_safe]. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0l YG0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLenq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import EnqGbase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

Section b.
Variable segs : list Segment.
Variable A_ENQ : Z.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable EPRE : Z -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk -> Prop.
Variable NMAXD : Z.
Variable ARETr : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk ->
  world segs -> config -> Prop.
Variable WINr : alayout -> bvmap 5 word -> astate -> Z -> Prop.
Hypothesis IF : EnqIfaceRoom segs A_ENQ B ARX AOX EPRE NMAXD ARETr WINr.

Theorem enq_room_g : forall inst ly X W regs mem md k,
EPRE inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = false ->
amreal segs (enqueue k X) W (cfg_at segs A_ENQ regs mem md)
(enq_arm_post_g segs B ARX AOX inst ly X W regs mem md k).
Proof.
intros inst ly X W regs mem md k PRE HNB.
pose proof (ir_nmax segs A_ENQ B ARX AOX EPRE NMAXD ARETr WINr IF inst ly X W regs mem md k PRE) as HN.
rewrite (enqueue_room_eq k X HNB). cbn [amreal].
eapply SRr_mono;
[exact (ir_walk segs A_ENQ B ARX AOX EPRE NMAXD ARETr WINr IF inst ly X W regs mem md k PRE HNB HN)|].
intros W' c' _ HR.
pose proof (ir_post segs A_ENQ B ARX AOX EPRE NMAXD ARETr WINr IF inst ly X W regs mem md k W' c' PRE HNB HR)
  as LEAF.
destruct (ir_frame segs A_ENQ B ARX AOX EPRE NMAXD ARETr WINr IF ly X W regs mem md k W' c' HR)
  as (regs2 & mem2 & md2 & Hc2 & MEQ').
destruct LEAF as (regs' & mem' & md' & nb & Hc & POST & Hqt & Hnbm & Hch & Hqg & Hfs).
assert (Em : mem' = mem2).
{ pose proof (cfg_mem_eq_g _ _ (eq_trans (eq_sym Hc) Hc2)) as E. cbn in E. exact E. }
(* The raw frame: off the arm's window the walk kept the bytes, and the window is owned or is stack scratch. *)
assert (FRs : forall x : word, ~ AOX ly X (bv_unsigned x) ->
  ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) -> mem' x = mem x).
{ intros x NO NS. rewrite Em. apply MEQ'. intros HW.
  destruct (ir_owned segs A_ENQ B ARX AOX EPRE NMAXD ARETr WINr IF inst ly X W regs mem md k
    (bv_unsigned x) PRE HNB (u64_range x) HW) as [O|O]; [exact (NO O) | exact (NS O)]. }
(* The memnorm keep: the same window frame, and every byte of the window is memnorm-safe. *)
assert (MNK : MemnormT.memnorm_keep segs mem mem').
{ eapply (MemnormT.memnorm_frame segs (WINr ly regs X)).
  - intros x HW.
    exact (ir_safe segs A_ENQ B ARX AOX EPRE NMAXD ARETr WINr IF inst ly X W regs mem md k x PRE HNB HW).
  - intros x NW. rewrite Em. exact (MEQ' x NW). }
split; [| exists regs', mem', md'; split; [exact Hc | exact MNK]].
split; [| exists regs', mem', md'; split; [exact Hc | exact FRs]].
exists regs', mem', md', nb.
split; [exact Hc|].
split.
{ destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
  split; [exact AR'|]. split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
  split; [exact AGV|]. split; [| exact PRS].
  intros x NO NO' NS NE. apply FRs; [exact NO|]. intros O. apply NS. unfold ascratch. left. exact O. }
split; [exact Hqt|]. split; [exact Hnbm|]. split; [exact Hch|]. split; [exact Hqg|]. exact Hfs.
Qed.

End b.
End a.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check enq_room_g.
Print Assumptions enq_room_g.
