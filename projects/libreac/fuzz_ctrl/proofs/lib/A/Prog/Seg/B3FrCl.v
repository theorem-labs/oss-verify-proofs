(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 153 of its 180 lines of code are new or changed and 369 lines of the source are left out. *)
(* Batch-B3 helper for the asan slot segment lemmas of fuzz_ctrl LLVMFuzzerTestOneInput: b3_fr_cl, the FRA transport
   across a callee run whose write set W is app + rt_disjoint and avoids the FRA-read cells (low image [0,6283264),
   frame header [fr,fr+24), the fr spill [A+304,A+312), the fr reload and selector spills [A+16,A+32), the saved caller registers
   [S-104,S), and the 392 frame shadow bytes [Sfr,Sfr+392)), but MAY touch the frame body [fr+24,fr+3136) and the
   callee's stack slice [sp-K,sp).  It is Tac_slot_b2.sl_fr_cl restated against the push-5 FRA (b6dbb4eafee):
   the stack window is entry-anchored [S - SLOT_STACK, S) (kept by rd_mono + wmono), the new conjuncts fr + 3136 <= A,
   S - 4096 < sp, S < APPMEM_END are pure, the side-arm FS separation reads the tp word (low image, kept), and the
   frame_AG globals stay addressable (W is app memory, so no shadow byte changes: sl_addr_keep).  The spill-base
   premises carry push 5's guard 0 <= A < 2^64.  Push 5b: FRA carries no mem_inv (so neither does this lemma), and
   the side arm's FakeStack frame record FSREC moves because W avoids the FakeStack [FS, FS + FS_SIZE) outside the
   frame body (the premise after the frame-shadow one; the tp word is in the low image). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Frame MState Mem.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma b3_fr_cl : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  lib.A.Tk.UL.Frame.munch W mem mem' -> lib.A.Tk.UL.Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < 6283264 -> lib.A.Tk.UL.Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> lib.A.Tk.UL.Frame.outside W x) ->
  (forall A, lib.A.Reusable.YK11.getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 304 <= x < A + 312 -> lib.A.Tk.UL.Frame.outside W x) ->
  (forall A, lib.A.Reusable.YK11.getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 16 <= x < A + 32 -> lib.A.Tk.UL.Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> lib.A.Tk.UL.Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> lib.A.Tk.UL.Frame.outside W x) ->
  (forall FS x, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS <= x < FS + AC.FS_SIZE ->
     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> lib.A.Tk.UL.Frame.outside W x) ->
  rd_mono mem mem' ->
  lib.A.Reusable.YK11.getr regs' 2 = lib.A.Reusable.YK11.getr regs 2 -> lib.A.Reusable.YK11.getr regs' 3 = lib.A.Reusable.YK11.getr regs 3 -> lib.A.Reusable.YK11.getr regs' 4 = lib.A.Reusable.YK11.getr regs 4 ->
  lib.A.Reusable.YK11.getr regs' 8 = lib.A.Reusable.YK11.getr regs 8 -> lib.A.Reusable.YK11.getr regs' 9 = lib.A.Reusable.YK11.getr regs 9 -> lib.A.Reusable.YK11.getr regs' 19 = lib.A.Reusable.YK11.getr regs 19 ->
  lib.A.Reusable.YK11.getr regs' 26 = lib.A.Reusable.YK11.getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK
    HWlo HWhdr HWspill HWsel HWsaved HWsh HWfs HRDM E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as Hw. unfold lib.A.Tk.UL.Frame.stk in Hw. destruct Hw as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite lib.A.Tk.UL.MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite lib.A.Tk.UL.Mem.length_le8. intros x Hx. exact (HWspill A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite lib.A.Tk.UL.Mem.length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite lib.A.Tk.UL.Mem.length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * (* FSREC: the tp word is in the low image; the class-6 flag byte and the slot's last word are
             FakeStack bytes outside the frame body (fsrec_munch's layout facts). *)
          destruct Hrec as (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail).
          assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
          assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
          assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
          assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
          assert (Hfrv : fr = FS + 6328320 + j * 4096)
            by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
          rewrite HM6 in Hj.
          exists FS, j.
          split.
          { intros k Hk. rewrite KBlo.
            - exact (Htp k Hk).
            - unfold AC.as_tp, AC.ASYMS. cbn. lia.
            - unfold AC.as_tp, AC.ASYMS. cbn. lia. }
          split; [exact HFSr|].
          split; [rewrite HM6; exact Hj|].
          split; [exact Hfr|].
          split.
          { eapply fl_bytes; [exact Hflag | exact MU |].
            cbn [length]. intros x Hx. apply (HWfs FS x Htp HFSr); lia. }
          { eapply fl_bytes; [exact Htail | exact MU |].
            rewrite lib.A.Tk.UL.Mem.length_le8. intros x Hx. apply (HWfs FS x Htp HFSr); rewrite HB6 in *; lia. } }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite lib.A.Tk.UL.Mem.length_le8. intros x Hx. apply HWhdr; lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite lib.A.Tk.UL.Mem.length_le8. intros x Hx. apply HWhdr; lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split.
  { exact (stk_mono mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin WM HRDM). }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !lib.A.Tk.UL.Mem.length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2; exact (sl_addr_keep mem mem' W a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

End S.
