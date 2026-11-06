(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/EnqGhit.v (a working branch f38a2a07767b, file sha256 7d4f29496b52), lane B2's frame-generic Enqueue arm on the cf layer 987b886cbb10 (no image numeral); module paths changed only: 53 modules to this unit's lib/Reusable. No other edit; no image numeral is stated here. *)
(* Theorem Labs, 2026-10-30 (lane B2; integrator ReallocPrimary).
   rule 24: proves function __sanitizer::QuarantineCache<__asan::QuarantineCallback>::Enqueue (the HIT arm: a new
   batch is needed and the class-24 cache is not empty), frame-generic, at cgif_file_fuzzer's asan-ubsan image
   (Enqueue 0x35800).  Reuse search: the internal file LOOKUP-B2-enqueue.txt 2026-10-29T23:07:48Z exit 3; rule-24 check
   B2LookupCheck: CONFIRM.

   The hit arm over EnqGbase.EnqIfaceHit, generalized from the released arm (YFg5 with YFf2, 1,521 lines) as
   MnEnqArms.v:115-183 runs it.  The three derivations this file owns are the room arm's: the step at the arm
   (here the field [ih_shape], because the equation reads the class-24 cache), the raw frame of
   CLenq.acall_post_x from the walk's window frame and [ih_owned], and the memnorm keep from [ih_safe]. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import EnqGbase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
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
Variables (NMAXD RMAXD : Z).
Variable ARETh : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk ->
  list Z -> world segs -> config -> Prop.
Variable WINh : alayout -> bvmap 5 word -> astate -> list Z -> Z -> Prop.
Variable Shit : astate -> chunk -> list Z -> astate.
Hypothesis IF : EnqIfaceHit segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit.

Theorem enq_hit_g : forall inst ly X W regs mem md k l,
EPRE inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] ->
amreal segs (enqueue k X) W (cfg_at segs A_ENQ regs mem md)
(enq_arm_post_g segs B ARX AOX inst ly X W regs mem md k).
Proof.
intros inst ly X W regs mem md k l PRE HNB Hl Hlne.
pose proof (ih_nmax segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
  inst ly X W regs mem md k PRE) as HN.
pose proof (ih_rmax segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
  inst ly X W regs mem md k l PRE HNB Hl Hlne) as HRM.
rewrite (ih_shape segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
  inst ly X W regs mem md k l PRE HNB Hl Hlne). cbn [amreal].
eapply SRr_mono;
[exact (ih_walk segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
   inst ly X W regs mem md k l PRE HNB Hl Hlne HN HRM)|].
intros W' c' _ HR.
pose proof (ih_post segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
  inst ly X W regs mem md k l W' c' PRE HNB Hl Hlne HR) as LEAF.
destruct (ih_frame segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
  ly X W regs mem md k l W' c' HR) as (regs2 & mem2 & md2 & Hc2 & MEQ').
destruct LEAF as (regs' & mem' & md' & nb & Hc & POST & Hqt & Hnbm & Hch & Hqg & Hfs).
assert (Em : mem' = mem2).
{ pose proof (cfg_mem_eq_g _ _ (eq_trans (eq_sym Hc) Hc2)) as E. cbn in E. exact E. }
assert (FRs : forall x : word, ~ AOX ly X (bv_unsigned x) ->
  ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) -> mem' x = mem x).
{ intros x NO NS. rewrite Em. apply MEQ'. intros HW.
  destruct (ih_owned segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
    inst ly X W regs mem md k l (bv_unsigned x) PRE HNB Hl Hlne (u64_range x) HW) as [O|O];
    [exact (NO O) | exact (NS O)]. }
assert (MNK : MemnormT.memnorm_keep segs mem mem').
{ eapply (MemnormT.memnorm_frame segs (WINh ly regs X l)).
  - intros x HW.
    exact (ih_safe segs A_ENQ B ARX AOX EPRE NMAXD RMAXD ARETh WINh Shit IF
      inst ly X W regs mem md k l x PRE HNB Hl Hlne HW).
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
Check enq_hit_g.
Print Assumptions enq_hit_g.
