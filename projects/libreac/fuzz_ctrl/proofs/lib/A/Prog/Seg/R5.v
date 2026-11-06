(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and numbers changed; 1486 of its 1528 lines of code are new or changed and 354 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F12.v, with its module paths, module names and addresses changed; 540 of its 667 lines of code are new or changed and 1401 lines of the source are left out. *)
(* Segment R5 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81588, 0x815c8], 17 instructions, no call, no
   instrumented check, no branch. Turn b = 0 of the round trip: s7 = b = 0, the round-trip constants spilled at the
   spill base A = s1 ([A + 8] = s2 + 16, [A + 112] = s2 (the catalogue row), [A + 0] = s2 + 20, [A + 104] =
   round_trip.box 0x21140, [A + 96] = 0x1234, [A + 64] = 0xe38f0000), s8 = 36, and a0 = [A + 128] = fr + 544, then
   the round-trip head 0x815cc. Ubsan twin: lib/U/Prog/Seg/R04.v (a working branch).
   rule 24: no function proved (a slot segment).

   The six 8-byte stores hit the prologue save area [A, A + 416) of the real stack: in the entry-anchored slot window
   [S - SLOT_STACK, S) (so writable, FRA's stk fact), above stklo >= HIGHMEM_BEG (so a_store_ok, AH kept by
   a_laws_store, and outside every image segment and RT cell), above the frame (fr + 3136 <= A), below the saved
   registers (A + 416 <= S), and off the FRA spills [A + 16, A + 32) and [A + 304, A + 312). r5_fra_store moves
   FRA across one such store.

   Cuts (SlotInv push 5, b6dbb4eafee). Entry: Inv_A81588_loc = Inv_A81588 plus the two spills the exit carries and
   this segment does not write ([A + 128] = fr + 544, set 0x81378/0x814e4; [A + 168] = fr + 2624, set
   0x813b4/0x813f4). Exit: seg_R5 lands in the pushed Inv_A815cc_at at b = 0; seg_R5_loc lands in Inv_A815cc_loc_at,
   which adds what R6 / R7 read and only this segment (and the latch 0x81948-0x81950) sets: a0 = fr + 544 (loaded
   0x815c8), s8 = 36 (0x815ac) and [A + 64] = 0xe38f0000 (0x815c4). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot RcPro.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.

(* Build a list from a function defined on [0, n). *)
Lemma r5_ex_list : forall (f : nat -> option byte) n, (forall i, (i < n)%nat -> f i <> None) ->
  exists l, length l = n /\ forall i, (i < n)%nat -> f i = nth_error l i.
Proof.
  intros f n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - assert (H' : forall i, (i < n)%nat -> f i <> None) by (intros i Hi; apply H; lia).
    destruct (IH H') as (l & Hl & Hf).
    destruct (f n) as [b|] eqn:Eb; [|exfalso; exact (H n ltac:(lia) Eb)].
    exists (l ++ [b]). split; [rewrite length_app, Hl; cbn; lia|].
    intros i Hi. destruct (Nat.lt_ge_cases i n) as [Hlt|Hge].
    + rewrite nth_error_app1 by lia. exact (Hf i Hlt).
    + assert (Ei : i = n) by lia. subst i.
      rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn. exact Eb.
Qed.

(* A store keeps every byte readable that was readable before, so a readable n-byte range stays readable (with new
   contents where the store hit it). Used for FRA's 392-byte frame-shadow existential. *)
Lemma r5_bytes_ex_write : forall m p n a bs,
  (exists sh, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at rsegs m p sh /\ length sh = n) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  exists sh, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at rsegs (write_to_mem m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) bs) p sh /\ length sh = n.
Proof.
  intros m p n a bs (sh & (Hp & Hpl & Hrd) & <-) Ha Hal.
  assert (Hsome : forall i, (i < length sh)%nat ->
            OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.mrd rsegs (write_to_mem m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) bs) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (p + Z.of_nat i)) <> None).
  { intros i Hi. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.mrd. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.write_to_mem_spec by lia.
    match goal with |- context [if ?c then _ else _] => destruct c eqn:Ein end; cbv beta iota.
    - apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      match goal with |- context [nth_error bs ?k] => destruct (nth_error bs k) eqn:En end;
        cbv beta iota; [discriminate|].
      exfalso. apply nth_error_None in En. lia.
    - pose proof (Hrd i Hi) as H. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.mrd in H. rewrite H.
      destruct (nth_error sh i) eqn:En; [discriminate|].
      exfalso. apply nth_error_None in En. lia. }
  destruct (r5_ex_list (fun i => OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.mrd rsegs (write_to_mem m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) bs) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (p + Z.of_nat i))) (length sh) Hsome)
    as (l & Hl & Hf).
  exists l. split; [|exact Hl]. split; [exact Hp|]. split; [rewrite Hl; exact Hpl|].
  intros i Hi. rewrite Hl in Hi. exact (Hf i Hi).
Qed.

(* The image segments all end below the high application memory, so no high app address is in a segment. *)
Lemma r5_seg_high : forall z, HIGHMEM_BEG <= z -> find_segment rsegs z 1 = None.
Proof.
  intros z Hz. destruct (find_segment rsegs z 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (kb_find_segment rsegs z 1 s E) as (Hin & _ & Hhi).
  assert (Hall : forallb (fun s0 => Z.leb (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) HIGHMEM_BEG) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall s Hin). apply Z.leb_le in Hall. lia.
Qed.

(* A spill read off register 9 names the spill base FRA names, when that base is low enough. *)
Lemma r5_spill_base : forall (regs : bvmap 5 word) m A A' off v,
  rg regs 9 A -> rg regs 9 A' -> q64 m (A' + off) v -> 0 <= A < 2 ^ 60 -> 0 <= off < 1024 -> A' = A.
Proof.
  intros regs m A A' off v HA HA' Hq HAr Ho.
  pose proof (rg_eq64 regs 9 A' A HA' HA) as Hm.
  unfold q64 in Hq. destruct Hq as (H0 & H1 & _). rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 in H1.
  change (Z.of_nat 8) with 8 in H1.
  revert Hm H0 H1 HAr Ho. change (2 ^ 64) with 18446744073709551616. change (2 ^ 60) with 1152921504606846976.
  intros Hm H0 H1 HAr Ho. Z.div_mod_to_equations. lia.
Qed.

(* An 8-byte cell after an 8-byte store: the store at its address gives it, a store elsewhere keeps it. *)
Lemma r5_q64_other : forall m a (w : word) c v,
  q64 m c v -> 0 <= a -> a + 8 <= 2 ^ 64 -> (c + 8 <= a \/ a + 8 <= c) ->
  q64 (write_to_mem m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w)) c v.
Proof.
  intros m a w c v H Ha Hb Hd.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 w) as L1. pose proof (LM.length_le8 (Z_to_bv 64 v)) as L2.
  unfold q64 in *. apply LM.bytes_at_write_other; [exact H | lia | lia | lia].
Qed.

Lemma r5_q64_same : forall m a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  q64 (write_to_mem m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 (Z_to_bv 64 v))) a v.
Proof.
  intros m a v Ha Hb. pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 (Z_to_bv 64 v)) as L1. unfold q64.
  exact (LM.bytes_at_write_same rsegs m a (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 (Z_to_bv 64 v)) Ha ltac:(lia)).
Qed.

Lemma r5_q64_same_w : forall m a (w : word), 0 <= a -> a + 8 <= 2 ^ 64 ->
  q64 (write_to_mem m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w)) a (bv_unsigned w).
Proof.
  intros m a w Ha Hb. pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 w) as L1. unfold q64. rewrite Z_to_bv_lit_self.
  exact (LM.bytes_at_write_same rsegs m a (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w) Ha ltac:(lia)).
Qed.

(* An 8-byte cell after a chain of 8-byte stores, store by store (outermost first): the lemma is picked from the
   syntactic store address and given its arguments, so no failing unification runs. *)
Ltac r5_q1 m a w c v :=
  tryif constr_eq a c then
    lazymatch v with
    | bv_unsigned w => exact (r5_q64_same_w m a w ltac:(lia) ltac:(lia))
    | _ => exact (r5_q64_same m a v ltac:(lia) ltac:(lia))
    end
  else refine (r5_q64_other m a w c v _ ltac:(lia) ltac:(lia) ltac:(lia)).
Ltac r5_q :=
  repeat lazymatch goal with
  | |- q64 (write_to_mem ?m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa ?a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 ?w)) ?c ?v => r5_q1 m a w c v
  | |- q64 (write_to_mem ?m (Z_to_bv 64 ?a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 ?w)) ?c ?v => r5_q1 m a w c v
  end.

(* A one-interval footprint misses x. *)
Ltac r5_out := cbn [LF.outside]; split; [lia | exact I].

(* Discharge a `Sem.reg_get R k = ...` goal where R is a bvmap_set chain over mkR_of regs. *)
Ltac r5_regeq :=
  simp_regs;
  first [ reflexivity
        | symmetry; eassumption
        | symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
        | eassumption
        | apply Regs6ss.mkR_of_eqv; reflexivity
        | word_eq_tac
        | apply bv_eq; vm_compute; reflexivity ].

(* A literal word equality. *)
Ltac r5_wlit := first [ exact eq_refl | word_eq_tac | apply bv_eq; vm_compute; reflexivity ].

(* The catalogue row mrow = CAT + 296 * ((mode / 2) mod 11) lies in the 11-row catalogue. *)
Lemma r5_mrow_rng : forall inp, 0x9e800 <= mrow inp < 0x9e800 + 296 * 11.
Proof.
  intros inp. unfold mrow, istar, CAT, CAT_ROW, CAT_N.
  pose proof (Z.mod_pos_bound (mode inp / 2) 11 ltac:(lia)). lia.
Qed.

(* The word R5 stores at [A + 8] / [A + 0]: s2 + 16 / s2 + 20 with s2 = mrow. *)
Ltac r5_wsum :=
  first [ reflexivity
        | (f_equal; lia)
        | word_eq_tac
        | (match goal with |- ?G => idtac "R5WSUM" G end; fail) ].

Section R5.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The cuts are SlotInv.v's own (push 10, 09daa0603a8): Inv_A81588 is R4's exit, and Inv_A815cc_at at turn 0 is
   the loop head with a0 = fr + 544, s8 = 36 and [A + 64] = 0xe38f0000 (R6's build_as call reads a0; R7's
   Inv_A815ec_at needs s8 and [A + 64]), the row spill [A + 112] = mrow (0x81594 `sd s2,112(s1)` with the entry's
   s2 = mrow, before 0x81598 moves s2), RXS (this segment's own [A + 8] = mrow + 16 and [A + 0] = mrow + 20, the
   rest from the entry), and the facts R5 does not write: s5, the spills at A + 128 / 168 / 152 / 144 / 192 / 280
   / 240 / 48 / 56 / 72 / 80 / 88 / 200 / 216 (all outside the six stores), the four frame cells (below A), OUTA,
   and the id record's, the fragment record's and our[]'s bytes addressable (r5_addr_keep: the save area is
   application memory). *)

(* ENT across one 8-byte store in the save area [A, A + 120): the write is inside the entry-anchored slot
   window [S - SLOT_STACK, S), so none of the addresses ENT speaks of moves, and a_laws_store keeps the stack
   bounds and the runtime's owned set. *)
Lemma r5_ent_store : forall g fr hb regs mem md A off a (w : word),
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 60 -> 0 <= off -> off + 8 <= 120 -> a = A + off ->
  ENT APIf g hb (write_to_mem mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w)) md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md A off a w HFRA HENT Hs9 HAr Ho1 Ho2 ->.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP60 : 2 ^ 60 = 1152921504606846976) by reflexivity.
  assert (EA : A0 = A).
  { pose proof (rg_eq64 regs 9 A0 A Hr9 Hs9) as Hm.
    assert (HA0 : 0 <= A0 < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A0.
  remember (write_to_mem mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + off)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w)) as mem' eqn:Emem.
  assert (MU : LF.munch [(A + off, A + off + 8)] mem mem').
  { subst mem'. apply LF.munch_write; [apply LF.munch_refl | | | ];
      try (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8); try (cbn [LF.inside]; left); lia. }
  assert (WM : LF.wmono rsegs mem mem') by (subst mem'; apply LF.wmono_write, LF.wmono_refl).
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
    cbn [LF.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
    unfold AC.a_store_ok. right; left. unfold APPMEM_END in *. lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) (hb ++ g_H g) mem mem' md
              HAH HstoreC HwmL) as (HAH' & HOWN' & HSTK & HSHI).
  apply (ent_store B APIf ra g fr hb regs mem mem' md [(A + off, A + off + 8)] HENT HFRA MU).
  - intros x Hx.
    destruct (Z_lt_le_dec x (A + off)) as [H1|H1]; [|destruct (Z_lt_le_dec x (A + off + 8)) as [H2|H2]].
    + left. cbn [LF.outside]. split; [lia | exact I].
    + right; left. lia.
    + left. cbn [LF.outside]. split; [lia | exact I].
  - exact HSTK.
  - exact HSHI.
  - intros a _ Hown. exact (proj2 (HOWN' a) Hown).
Qed.

(* FRA survives one 8-byte store at A + off, 0 <= off < 120, off the fr reload and selector spills
   [A + 16, A + 32): RT via RT_store; AH / stklo via a_laws_store (above stklo, so a_store_ok); ro_agree
   because no high app address is in an image segment; the image, sink, spills, frame header, saved registers,
   frame_AG and the window's addressability are outside the store or kept by it (the store is app memory, so no
   shadow byte changes); the slot window by stk_write; the frame shadow existential is rebuilt by
   r5_bytes_ex_write; the side-arm FakeStack record is below stklo, hence below A. *)
Lemma r5_fra_store : forall g fr hb regs mem md A off a (w : word),
  FRA B APIf ra g fr hb regs mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 60 ->
  0 <= off -> off + 8 <= 120 -> (off + 8 <= 16 \/ 32 <= off) -> a = A + off ->
  FRA B APIf ra g fr hb regs (write_to_mem mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w)) md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md A off a w HFRA Hs9 HAr Ho1 Ho2 Ho3 ->.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) (hb ++ g_H g) mem md HAH)
    as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP60 : 2 ^ 60 = 1152921504606846976) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh. unfold APPMEM_END in HAPP.
  assert (EA : A0 = A).
  { pose proof (rg_eq64 regs 9 A0 A Hr9 Hs9) as Hm.
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A0.
  remember (write_to_mem mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + off)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w)) as mem' eqn:Emem.
  assert (MU : LF.munch [(A + off, A + off + 8)] mem mem').
  { subst mem'. apply LF.munch_write; [apply LF.munch_refl | | | ];
      try (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8); try (cbn [LF.inside]; left); lia. }
  assert (WM : LF.wmono rsegs mem mem') by (subst mem'; apply LF.wmono_write, LF.wmono_refl).
  assert (HRO' : ro_agree rsegs mem').
  { intros a Ha.
    assert (Hout : LF.outside [(A + off, A + off + 8)] (bv_unsigned a)).
    { cbn [LF.outside]. split; [|exact I]. intros Hin.
      assert (Hn : find_segment rsegs (bv_unsigned a) 1 = None)
        by (apply r5_seg_high; unfold HIGHMEM_BEG; lia).
      change ((match find_segment rsegs (bv_unsigned a) 1 with
               | Some seg => negb (seg_writable seg) | None => false end) = true) in Ha.
      rewrite Hn in Ha. discriminate Ha. }
    pose proof (Hro a Ha) as H.
    change ((match mem' a with Some b => Some b | None => seg_rom rsegs a end) = seg_rom rsegs a).
    rewrite (MU a Hout). exact H. }
  assert (Hsh' : exists sh, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { subst mem'. apply r5_bytes_ex_write; [exact Hsh | lia |]. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. lia. }
  assert (HAW : all_app [(A + off, A + off + 8)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
  assert (HD : rt_disjoint [(A + off, A + off + 8)]).
  { unfold rt_disjoint.
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    repeat split; left; lia. }
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
    cbn [LF.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
    unfold AC.a_store_ok. right; left. unfold APPMEM_END. lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) (hb ++ g_H g) mem mem' md
              HAH HstoreC HwmL) as (HAH' & _ & HSTK & _).
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. r5_out. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md [(A + off, A + off + 8)] HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO'|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia|].
        rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia|].
        rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [exact Hr2|].
  split; [exact Hspm|].
  split; [exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [exact Hr4|].
  split; [exact Hr8|].
  split; [exact Hr9|].
  split; [exact Hr3|].
  split; [exact Hr19|].
  split; [exact Hr26|].
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
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. intros x Hx. r5_out. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. intros x Hx. r5_out. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. intros x Hx. r5_out. }
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
        * (* the FakeStack lies below stklo <= S - SLOT_STACK < sp <= A, so the store misses its cells *)
          destruct Hrec as (FS & j & Htp & HFSr & Hj & Hfrv & Hflag & Htail).
          destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                      (hb ++ g_H g) mem md FS HAH Htp HFSr) as (HGTb & HFSend & _ & Happf).
          assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
          assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
          assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
          assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
          assert (Hfrv2 : fr = FS + 6328320 + j * 4096)
            by (rewrite Hfrv; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
          rewrite HM6 in Hj.
          exists FS, j.
          split.
          { intros k Hk. rewrite KBlo; [exact (Htp k Hk) | unfold AC.as_tp, AC.ASYMS; cbn; lia
            | unfold AC.as_tp, AC.ASYMS; cbn; lia]. }
          split; [exact HFSr|]. split; [rewrite HM6; exact Hj|]. split; [exact Hfrv|].
          split.
          { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
            cbn [LF.outside]. split; [lia | exact I]. }
          { eapply fl_bytes; [exact Htail | exact MU |]. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. intros x Hx.
            cbn [LF.outside]. rewrite HB6 in *. split; [lia | exact I]. } }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. intros x Hx. r5_out. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. intros x Hx. r5_out. }
  split; [exact Hsh'|].
  split.
  { subst mem'. apply LF.stk_write; [exact Hwin | lia | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8; lia]. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    unfold saved_bytes in Hx. rewrite !length_app, !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 in Hx. cbn in Hx. r5_out. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' [(A + off, A + off + 8)] a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2;
           exact (sl_addr_keep mem mem' [(A + off, A + off + 8)] a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* The save area [A, A + 120) is application memory, so storing into it changes no shadow byte: every
   addressable range stays addressable (OUTA, the id record's 38 bytes, our[]'s 6 bytes). *)
Lemma r5_addr_keep : forall A (mem mem' : word -> option byte) p n,
  LF.munch [(A, A + 120)] mem mem' ->
  (forall a, A <= a < A + 120 -> app_mem a) ->
  addressable mem p n -> addressable mem' p n.
Proof.
  intros A mem mem' p n MU Happ H.
  apply (sl_addr_keep mem mem' [(A, A + 120)] p n H MU).
  cbn [all_app]. split; [|exact I]. intros a Ha. apply Happ. lia.
Qed.

(* A frame cell the six stores miss (the frame lies below A, fr + FRAME_BYTES <= A). *)
Ltac r5_keep_cells Hc :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  destruct Hc as (k & Hk); exists k;
  lazymatch type of Hk with
  | _ _ ?m _ _ =>
      match goal with
      | MU : LF.munch ?W m ?m', WM : LF.wmono _ m ?m' |- _ =>
          apply (LF.rw_cells_transport rsegs W m m' _ _ Hk MU WM)
      end
  end;
  cbn; repeat split; lia.

Lemma seg_R5 : Hat B APIf ra (Inv_A815cc_at B APIf ra) 0%nat -> Hcut B APIf ra (Inv_A81588 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & HCUR & HOUR & HOUT & HID & HFG &
    (A1 & H9a & H128) & HPRO & H21 & (A3 & H9c & H152) & (A4 & H9d & H144) & (A5 & H9e & H208) &
    Hidr & Hjnk & (A6 & H9f & H280) & (A7 & H9g & H240) & Hjy & Hscr &
    (A8 & H9h & H48) & (A9 & H9i & H56) & (A10 & H9j & H88) & (A11 & H9k & H80) & (A12 & H9l & H72) &
    (A13 & H9m & H192) & (A14 & H9n & H216) & Hfg72 & Hid38 & H18).
  destruct HPRO as ((P1 & H9o & H40) & (P2 & H9p & H120) & (P3 & H9q & H136) & (P4 & H9r & H160) &
    (P5 & H9s & H168) & (P6 & H9t & H176) & (P7 & H9u & H200) & (P8 & H9v & H248) & Hour6 & Hinb & Hinl &
    (P9 & H9w & H184) & (P10 & H9x & H256) & (P11 & H9y & H264) & (P12 & H9z & H272) & (P13 & H9z2 & H32)).
  subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) ([] ++ g_H g) mem md HAH)
    as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP60 : 2 ^ 60 = 1152921504606846976) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh. unfold APPMEM_END in HAPP.
  assert (HAr : 0 <= A < 2 ^ 60) by lia.
  assert (EA1 : A1 = A) by exact (r5_spill_base regs mem A A1 128 (fr + 544) Hr9 H9a H128 HAr ltac:(lia)).
  assert (EP1 : P1 = A) by exact (r5_spill_base regs mem A P1 40 _ Hr9 H9o H40 HAr ltac:(lia)).
  assert (EP2 : P2 = A) by exact (r5_spill_base regs mem A P2 120 _ Hr9 H9p H120 HAr ltac:(lia)).
  assert (EP3 : P3 = A) by exact (r5_spill_base regs mem A P3 136 _ Hr9 H9q H136 HAr ltac:(lia)).
  assert (EP4 : P4 = A) by exact (r5_spill_base regs mem A P4 160 _ Hr9 H9r H160 HAr ltac:(lia)).
  assert (EP5 : P5 = A) by exact (r5_spill_base regs mem A P5 168 _ Hr9 H9s H168 HAr ltac:(lia)).
  assert (EP6 : P6 = A) by exact (r5_spill_base regs mem A P6 176 _ Hr9 H9t H176 HAr ltac:(lia)).
  assert (EP7 : P7 = A) by exact (r5_spill_base regs mem A P7 208 _ Hr9 H9u H200 HAr ltac:(lia)).
  assert (EP8 : P8 = A) by exact (r5_spill_base regs mem A P8 248 _ Hr9 H9v H248 HAr ltac:(lia)).
  assert (EP9 : P9 = A) by exact (r5_spill_base regs mem A P9 184 _ Hr9 H9w H184 HAr ltac:(lia)).
  assert (EP10 : P10 = A) by exact (r5_spill_base regs mem A P10 256 _ Hr9 H9x H256 HAr ltac:(lia)).
  assert (EP11 : P11 = A) by exact (r5_spill_base regs mem A P11 264 _ Hr9 H9y H264 HAr ltac:(lia)).
  assert (EP12 : P12 = A) by exact (r5_spill_base regs mem A P12 272 _ Hr9 H9z H272 HAr ltac:(lia)).
  assert (EP13 : P13 = A) by exact (r5_spill_base regs mem A P13 32 _ Hr9 H9z2 H32 HAr ltac:(lia)).
  subst P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13.
  clear H9o H9p H9q H9r H9s H9t H9u H9v H9w H9x H9y H9z H9z2.
  assert (EA3 : A3 = A) by exact (r5_spill_base regs mem A A3 152 (Sfr fr + 68) Hr9 H9c H152 HAr ltac:(lia)).
  assert (EA4 : A4 = A) by exact (r5_spill_base regs mem A A4 144 (fr + 2688) Hr9 H9d H144 HAr ltac:(lia)).
  assert (EA5 : A5 = A) by exact (r5_spill_base regs mem A A5 192 (fr + 2768) Hr9 H9e H208 HAr ltac:(lia)).
  assert (EA6 : A6 = A) by exact (r5_spill_base regs mem A A6 280 (fr + 3040) Hr9 H9f H280 HAr ltac:(lia)).
  assert (EA7 : A7 = A) by exact (r5_spill_base regs mem A A7 240 (fr + 3056) Hr9 H9g H240 HAr ltac:(lia)).
  assert (EA8 : A8 = A) by exact (r5_spill_base regs mem A A8 48 _ Hr9 H9h H48 HAr ltac:(lia)).
  assert (EA9 : A9 = A) by exact (r5_spill_base regs mem A A9 56 _ Hr9 H9i H56 HAr ltac:(lia)).
  assert (EA10 : A10 = A) by exact (r5_spill_base regs mem A A10 88 _ Hr9 H9j H88 HAr ltac:(lia)).
  assert (EA11 : A11 = A) by exact (r5_spill_base regs mem A A11 80 _ Hr9 H9k H80 HAr ltac:(lia)).
  assert (EA12 : A12 = A) by exact (r5_spill_base regs mem A A12 72 _ Hr9 H9l H72 HAr ltac:(lia)).
  assert (EA13 : A13 = A) by exact (r5_spill_base regs mem A A13 200 _ Hr9 H9m H192 HAr ltac:(lia)).
  assert (EA14 : A14 = A) by exact (r5_spill_base regs mem A A14 216 _ Hr9 H9n H216 HAr ltac:(lia)).
  subst A1 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14.
  clear H9a H9c H9d H9e H9f H9g H9h H9i H9j H9k H9l H9m H9n.
  (* s2 = mrow, stored at 0x81594 into [A + 112] (the loop head's row spill) *)
  assert (E112 : Sem.reg_get regs 18 = Z_to_bv 64 (mrow (g_in g))).
  { unfold rg in H18. rewrite <- H18. unfold getr. cbn [bv_eqb negb]. reflexivity. }
  (* The stores' window [A, A + 120) is inside the entry-anchored slot window, so writable. *)
  assert (Hwr : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at rsegs mem A 120).
  { pose proof Hwin as (Hw0 & Hw1 & Hwv). split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (Hwv (A + i) ltac:(lia))). }
  eapply (sl_run regs (Z_to_bv 64 0x81588) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x815cc /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\
       Sem.reg_get R 4 = Sem.reg_get regs 4 /\ Sem.reg_get R 8 = Sem.reg_get regs 8 /\
       Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 25 = Sem.reg_get regs 25 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\
       Sem.reg_get R 23 = Z_to_bv 64 0 /\ Sem.reg_get R 24 = Z_to_bv 64 36 /\
       Sem.reg_get R 10 = Z_to_bv 64 (fr + 544) /\
       (exists w16 w112 w8 w104 w96 w64 : word,
          mem' = write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem mem
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 8)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w16)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 112)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w112)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa A) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w8))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 104)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w104)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 96)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w96)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 64)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w64) /\
          w104 = Z_to_bv 64 0x21140 /\ w96 = Z_to_bv 64 0x1234 /\ w64 = Z_to_bv 64 0xe38f0000 /\
          w112 = Sem.reg_get regs 18 /\
          w16 = Z_to_bv 64 (mrow (g_in g) + 16) /\ w8 = Z_to_bv 64 (mrow (g_in g) + 20)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* stepping 0x81588 .. 0x815c8 *)
    assert (Hs9r : Sem.reg_get regs (9%bv) = Z_to_bv 64 A) by
      (unfold rg in Hr9; rewrite <- Hr9; unfold getr; reflexivity).
    assert (IDW : bvmap_set (9%bv) (Z_to_bv 64 A) (Regs6ss.mkR_of regs) = Regs6ss.mkR_of regs)
      by (rewrite <- Hs9r; cbn; reflexivity).
    rewrite <- IDW.
    (* s2 = mrow as a literal word, so the 0x8158c / 0x81598 additions give mrow + 16 / mrow + 20 *)
    assert (IDW18 : bvmap_set (18%bv) (Z_to_bv 64 (mrow (g_in g))) (Regs6ss.mkR_of regs) = Regs6ss.mkR_of regs)
      by (rewrite <- E112; cbn; reflexivity).
    rewrite <- IDW18.
    pose proof (r5_mrow_rng (g_in g)) as Hmr.
    step. (* 0x81588 li s7,0 *)
    step. (* 0x8158c addi a0,s2,16 *)
    assert (HS16 : store_ok rsegs mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 8)) 8 = true).
    { apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs mem A 120 8 8 Hwr); lia. }
    step. (* 0x81590 sd a0,8(s1) *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (HS112 : store_ok rsegs m1 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 112)) 8 = true) by
        (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs m1 A 120 112 8); [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_write; exact Hwr | lia | lia]) end.
    step. (* 0x81594 sd s2,112(s1) *)
    step. (* 0x81598 addi s2,s2,20 *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
      assert (HS8 : store_ok rsegs m2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa A) 8 = true) by
        (pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs m2 A 120 0 8 ltac:(repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_write; exact Hwr)
                       ltac:(lia) ltac:(lia)) as HS0;
         rewrite Z.add_0_r in HS0; exact HS0) end.
    step. (* 0x8159c sd s2,0(s1) *)
    step. (* 0x815a0 auipc a0,0xfffa0 *)
    step. (* 0x815a4 lui a1,0x1 *)
    step. (* 0x815a8 lui a2,0xe38f *)
    step. (* 0x815ac li s8,36 *)
    step. (* 0x815b0 addi a0,a0,-1064 *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
      assert (HS104 : store_ok rsegs m3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 104)) 8 = true) by
        (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs m3 A 120 104 8); [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_write; exact Hwr | lia | lia]) end.
    step. (* 0x815b4 sd a0,104(s1) *)
    step. (* 0x815b8 addiw a0,a1,564 *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
      assert (HS96 : store_ok rsegs m4 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 96)) 8 = true) by
        (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs m4 A 120 96 8); [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_write; exact Hwr | lia | lia]) end.
    step. (* 0x815bc sd a0,96(s1) *)
    step. (* 0x815c0 slli a2,a2,0x4 *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m5 _) =>
      assert (HS64 : store_ok rsegs m5 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 64)) 8 = true) by
        (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs m5 A 120 64 8); [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_write; exact Hwr | lia | lia]) end.
    step. (* 0x815c4 sd a2,64(s1) *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m6 _) =>
      assert (HB6 : q64 m6 (A + 128) (fr + 544)) by (r5_q; exact H128) end.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m6 _) =>
      assert (HR128 : ov_read_bytes rsegs m6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 128)) 8 = Some (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 (Z_to_bv 64 (fr + 544)))) end.
    { pose proof (LM.length_le8 (Z_to_bv 64 (fr + 544))) as L8.
      pose proof (LM.bytes_at_ov_read rsegs _ (A + 128) (LM.le8 (Z_to_bv 64 (fr + 544))) 0 8 HB6
          ltac:(lia)) as H.
      rewrite Z.add_0_r, skipn_O in H.
      rewrite firstn_all2 in H by lia. exact H. }
    step. (* 0x815c8 ld a0,128(s1) *)
    apply evt_done. hnf. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 13 (split; [r5_regeq|]).
    do 6 eexists. split; [reflexivity|].
    split; [r5_wlit|]. split; [r5_wlit|]. split; [r5_wlit|]. split; [r5_regeq|].
    split; r5_wsum.
  - intros R pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E22 & E25 & E21 & E23 & E24 & E10 & Hmem) Hreg Hmat.
    subst pc'.
    destruct Hmem as (w16 & w112 & w8 & w104 & w96 & w64 & -> & -> & -> & -> & -> & -> & ->).
    assert (G2 : getr regs' 2 = getr regs 2)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G3 : getr regs' 3 = getr regs 3)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G4 : getr regs' 4 = getr regs 4)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G8 : getr regs' 8 = getr regs 8)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G9 : getr regs' 9 = getr regs 9)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G19 : getr regs' 19 = getr regs 19)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G26 : getr regs' 26 = getr regs 26)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G22 : getr regs' 22 = getr regs 22)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G25 : getr regs' 25 = getr regs 25)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G23 : getr regs' 23 = Z_to_bv 64 0)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G21 : getr regs' 21 = getr regs 21)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G24 : getr regs' 24 = Z_to_bv 64 36)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G10 : getr regs' 10 = Z_to_bv 64 (fr + 544))
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    match goal with |- SR _ (mkCfg (mkst _ _ ?m6 _) _) _ =>
      assert (HFRA6 : FRA B APIf ra g fr [] regs m6 md);
      [| assert (MU : LF.munch [(A, A + 120)] mem m6)] end.
    { apply (r5_fra_store g fr [] regs _ md A 64 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 96 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 104 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 8 _ _); [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia]. }
    { apply LF.munch_write; [ apply LF.munch_write; [ apply LF.munch_write; [ apply LF.munch_write;
        [ apply LF.munch_write; [ apply LF.munch_write; [ apply LF.munch_refl | | | ] | | | ] | | | ] | | | ]
        | | | ] | | | ];
        try (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8); try (cbn [LF.inside]; left); lia. }
    match goal with |- SR _ (mkCfg (mkst _ _ ?m6 _) _) _ =>
      assert (WM : LF.wmono rsegs mem m6) by (repeat apply LF.wmono_write; apply LF.wmono_refl) end.
    (* the save area [A, A + 120) is application memory (it is in the slot window, above stklo) *)
    assert (Happ8 : forall a, A <= a < A + 120 -> app_mem a)
      by (intros a Ha; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
    assert (HFRA' := sl_fra_move B APIf ra g fr [] regs regs' _ md md' HFRA6 G2 G3 G4 G8 G9 G19 G26 Hmat).
    (* ENT across the same six stores, then across the model step *)
    match goal with |- SR _ (mkCfg (mkst _ _ ?m6 _) _) _ =>
      assert (HENT6 : ENT APIf g [] m6 md) end.
    { apply (r5_ent_store g fr [] regs _ md A 64 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
      - apply (r5_fra_store g fr [] regs _ md A 96 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 104 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 8 _ _); [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
      - apply (r5_ent_store g fr [] regs _ md A 96 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
        + apply (r5_fra_store g fr [] regs _ md A 104 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
          apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
          apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
          apply (r5_fra_store g fr [] regs _ md A 8 _ _); [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
        + apply (r5_ent_store g fr [] regs _ md A 104 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
          * apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
            apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
            apply (r5_fra_store g fr [] regs _ md A 8 _ _);
              [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
          * apply (r5_ent_store g fr [] regs _ md A 0 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
            -- apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
               apply (r5_fra_store g fr [] regs _ md A 8 _ _);
                 [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
            -- apply (r5_ent_store g fr [] regs _ md A 112 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
               ++ apply (r5_fra_store g fr [] regs _ md A 8 _ _);
                    [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
               ++ apply (r5_ent_store g fr [] regs _ md A 8 _ _);
                    [exact HFRA | exact HENT | exact Hr9 | exact HAr | lia | lia | lia]. }
    assert (HENT' : ENT APIf g [] _ md') by exact (ent_mat APIf g [] _ md md' HENT6 Hmat).
    assert (Hr9' : rg regs' 9 A) by (unfold rg; rewrite G9; exact Hr9).
    assert (LID : length (RID (g_in g) 0) = 38%nat) by reflexivity.
    assert (LFG : length (RFG (g_in g) 0) = 72%nat) by reflexivity.
    rewrite <- SEGS. apply Hexit.
    do 4 eexists. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hn|].
    split.
    { destruct HCUR as (Hc7 & H22 & H25).
      unfold RS, RB, CUR, OURb, IDBr, FGBr, rg in *.
      split; [lia|].
      split; [split; [exact Hc7|]; split; [rewrite G22; exact H22 | rewrite G25; exact H25]|].
      split.
      { eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length. intros x Hx. r5_out. }
      split; [rewrite G23; reflexivity|].
      split.
      { eapply fl_bytes; [exact HID | exact MU |]. rewrite LID. intros x Hx. r5_out. }
      { eapply fl_bytes; [exact HFG | exact MU |]. rewrite LFG. intros x Hx. r5_out. } }
    split; [exact (r5_addr_keep A mem _ (fr + 544) 1492 MU Happ8 HOUT)|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H128. }
    (* PRO (push 13B): the eight spills by the store chain, our[]'s shadow byte (the save area is application
       memory), and the input pair (the save area is at or above the slot window's base: RcPro.rc_away_hi) *)
    split.
    { unfold PRO.
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H40. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H120. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H136. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H160. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H168. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H176. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H200. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H248. }
      split; [exact (r5_addr_keep A mem _ (fr + 2624) 6 MU Happ8 Hour6)|].
      pose proof (rc_in_keep B APIf ra g fr [] regs mem _ md _ HFRA MU) as HK.
      specialize (HK ltac:(intros x Hx; cbn [LF.outside] in Hx;
                           apply (rc_away_hi B APIf ra g fr [] regs mem md x HFRA); lia) (conj Hinb Hinl)).
      destruct HK as (Hinb' & Hinl').
      split; [exact Hinb'|]. split; [exact Hinl'|].
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H184. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H256. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H264. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H272. }
      exists A. split; [exact Hr9'|]. r5_q. exact H32. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. }
    split; [exact G10|].
    split; [exact G24|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. }
    split.
    { exists A. split; [exact Hr9'|]. rewrite E112. r5_q. }
    split; [unfold rg; rewrite G21; exact H21|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H152. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H144. }
    split; [exact (r5_addr_keep A mem _ (fr + 2176) 38 MU Happ8 Hid38)|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H208. }
    split; [r5_keep_cells Hidr|]. split; [r5_keep_cells Hjnk|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H280. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H240. }
    split; [r5_keep_cells Hjy|]. split; [r5_keep_cells Hscr|].
    (* push 10, RXS: [A + 48 / 56 / 88 / 80 / 72 / 200 / 216] carried (outside the six stores), this segment's own
       [A + 8] = mrow + 16 (0x8158c / 0x81590) and [A + 0] = mrow + 20 (0x81598 / 0x8159c), and the 72 fragment
       bytes addressable (the save area is application memory) *)
    unfold RXS.
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H48. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H56. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H88. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H80. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H72. }
    split. { exists A. split; [exact Hr9'|]. r5_q. }
    split. { exists A. split; [exact Hr9'|]. rewrite Z.add_0_r. r5_q. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H192. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H216. }
    exact (r5_addr_keep A mem _ (fr + 2256) 72 MU Happ8 Hfg72).
Qed.

End R5.
