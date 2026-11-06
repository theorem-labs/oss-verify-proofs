(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths changed; 297 of its 332 lines of code are new or changed and 361 lines of the source are left out. *)
(* Segment F27 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0 image B), 0x828b4-0x82928: the head
   of the inlined check_ports after the second reac_ports_unknown call (0x828b0), up to the port-slot loop head
   0x8292c (F28's cut). The v1.9.0 move of the patched-image seg_F27 (a working branch 4131ff88f40, patched
   0x82838-0x828b8), itself the image-B port of the image-A seg_F27 (lib/A/Prog/Seg/F27.v).
   Entry cut: the official Inv_B828b4_at of lib/B/Prog/SlotInv.v (F27K, s9 = r = t_rp, s7 = unk = t_unk from the
   first count, a0 = the second count = t_unk, PORTS, FIRSTb, s4 = len, FTL, FTURN, IFS (S j), s5 = fr + 128). Exit
   cuts: the official Inv_B8292c_at (v1.9 pc 0x8292c; r = 0; F28's entry), whose body carries SlotInv's F28GAP (the
   F27K window state, r = 0, s7 = unk, PORTS, FIRSTb and the loop registers that the port-slot loop reads;
   Seg/F28.v starts from it), and the official Inv_B82aa4_at (v1.9 pc 0x82aa4; r <> 0; F29's entry).
     0x828b4  bne  a0,s7,82fa4   -- not taken: both counts are t_unk.
     0x828b8  seqz a0,s9 ; 0x828bc slti a1,s7,0
     0x828c0  beq  a0,a1,82fa4   -- not taken: t_rp = 0 exactly when 0 <= t_unk (ports fact C5.3).
     0x828c4  beqz s9,828f0
   r <> 0 (t_rp = t_unk = -1): 0x828c8-0x828e8 load the three ports words through s5 = fr + 128 (lw, no
   instrumented check: frame variables; the patched image reloaded [A+248] before each) and compare them with -7;
   each `bne _,a1,82fa4` is not taken because PORTS keeps the three words at -7 (C5.4); `j 82aa4` reaches the exit
   Inv_B82aa4_at.
   r = 0 (0 <= t_unk <= 48): 0x828f0 li t3,12 (v1.9 sets t3 here; the patched image set it at the cut 0x82838);
   0x828f4 ld a0,312(s1) = blk = phi + 18; 0x828f8 `beqz a0,82fa0` (trap row T55) is not taken since 0 < phi and
   phi + 50 <= 2^64; 0x828fc-0x82928 set a5 = a3 = a1 = a2 = 0, a4 = a0 = blk + 8 = phi + 26, a6 = s11 - blk =
   -8 - (phi + 18) (the room 2^64 - 8 - blk that F28's T56 check reads: sltiu/neg/and keep it whole, it is below
   2^64 - 7), a7 = 12, and reach the exit Inv_B8292c_at (port-slot loop head) with t3 = 12.
   No call, no store, no instrumented check: memory is unchanged and FRA moves by sl_fra_move. The exits' LK, FTL,
   FTURN, IFS (S j) and F27K are the entry's: they read memory and s1, s2, s4, s5, s8, s11 only, which the run keeps.
   The ports facts are the plain twin's (a Theorem Labs lane's lib/Prog/Seg/Tac_b7.v, b7_ prefix kept). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* Tac_ro's chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this file's
   registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module ULPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.PropExec.

(* ---- Ports facts C5.3 / C5.4 (plain twin Tac_b7.v; block = phi + 18, pbs = its first 20 bytes) ---- *)

(* C5.3: reac_ports_parse and reac_ports_unknown accept the same blocks. *)
Lemma b7_decl_same : forall bs, RcLeaf.decl bs = RcPorts.pu_decl bs.
Proof. intros bs. reflexivity. Qed.

Lemma b7_nunk_nonneg : forall bs k, 0 <= RcPorts.pu_nunk bs k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_nunk_le : forall bs k, RcPorts.pu_nunk bs k <= Z.of_nat k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_unk_rp0 : forall inp j, t_rp inp j = 0 -> 0 <= t_unk inp j <= 48 /\ RcPorts.pu_decl (t_pbs inp j) = true.
Proof.
  intros inp j H. unfold t_rp, t_unk in *. rewrite <- b7_decl_same.
  destruct (RcLeaf.decl (t_pbs inp j)); [|discriminate H].
  pose proof (b7_nunk_nonneg (t_pbs inp j) 12). pose proof (b7_nunk_le (t_pbs inp j) 12).
  change (Z.of_nat 12) with 12 in *. split; [lia | reflexivity].
Qed.

Lemma b7_unk_rpm : forall inp j, t_rp inp j <> 0 -> t_rp inp j = -1 /\ t_unk inp j = -1.
Proof.
  intros inp j H. unfold t_rp, t_unk in *.
  change (RcPorts.pu_decl (t_pbs inp j)) with (RcLeaf.decl (t_pbs inp j)).
  destruct (RcLeaf.decl (t_pbs inp j)); [exfalso; apply H; reflexivity | split; reflexivity].
Qed.

(* ---- Register transport of the window's bundles (SlotInv's F27K, LK, FTL) ---- *)

(* F27K reads only s1 (the spills), s2, s8 (the sum flag, v1.9), s11 and memory. *)
Lemma f27_K : forall g j phi fr regs regs' m,
  F27K g j phi fr regs m ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 27 = getr regs 27 ->
  getr regs' 24 = getr regs 24 ->
  F27K g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m H E9 E18 E27 E24.
  unfold F27K, LK, FLI, spill, rg in *. rewrite E9, E18, E27, E24. exact H.
Qed.

(* LK reads only s1 (the spills), s11 and memory. *)
Lemma f27_lk : forall g fr j regs regs' m,
  LK g fr j regs m -> getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 -> LK g fr j regs' m.
Proof.
  intros g fr j regs regs' m H E9 E27.
  unfold LK, FLI, spill, rg in *. rewrite E9, E27. exact H.
Qed.

(* FTL reads only s1 (the spills), s5, s8 and memory. *)
Lemma f27_ftl : forall g j phi fr regs regs' m,
  FTL g j phi fr regs m ->
  getr regs' 9 = getr regs 9 -> getr regs' 21 = getr regs 21 -> getr regs' 24 = getr regs 24 ->
  FTL g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m H E9 E21 E24.
  unfold FTL, spill, rg in *. rewrite E9, E21, E24. exact H.
Qed.

(* The frame bytes at phi are at most len many (f_phi takes the first len bytes of the rest of the input). *)
Lemma f27_phi_len : forall inp j, 0 <= t_len inp j -> Z.of_nat (length (t_phi inp j)) <= t_len inp j.
Proof.
  intros inp j H. unfold t_phi, f_phi, t_len in *. rewrite length_firstn.
  rewrite Nat2Z.inj_min, Z2Nat.id by exact H. lia.
Qed.

Section F27C.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* A cut of this window: FCUT (the frame-loop cut with the live block Phi) with phi passed to the body, plus F27K.
   lib/B/Prog/Seg/Tac_f23.v states its local cuts Inv_B82878_loc / Inv_B82888_loc with it. *)
Definition F27CUT (g : ghost) (pc : Z) (j : nat) (P : Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop)
    (c : config) : Prop :=
  exists phi, CUTST B APIf ra g pc (hb1 phi (flen g j))
    (fun fr regs m => g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ F27K g j phi fr regs m /\
                      P phi fr regs m) c.

(* The gap of F28's entry 0x828bc is now SlotInv's own F28GAP (adopt 12, this file's text verbatim): the F27K
   window state, r = t_rp = 0 (0x8284c `beqz s9` taken), s7 = unk (0x82828 `mv s7,a0`), the ports words PORTS and
   the first byte FIRSTb, and the loop registers 0x8288c-0x828b8 set: a0 = a4 = blk + 8, a6 = s11 - blk, a7 = 12,
   a1 = a2 = a3 = a5 = 0, t3 = 12 (0x82838). So the r = 0 exit proves the official Inv_B8292c_at directly. *)

End F27C.

(* ---- Stepping helpers (asan engine) ---- *)

(* A carried `bytes_at` fact in the `ov_read_bytes _ _ _ n = Some bs` form the UL load step consumes. *)
Lemma f27_rd4 : forall m a bs, bytes_at rsegs m a bs -> length bs = 4%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 4 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 4 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f27_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* Two spill bases equal as 64-bit values give the same word address at every offset. *)
Lemma f27_wa_shift : forall x y d, Z_to_bv 64 x = Z_to_bv 64 y -> ULMem.wa (x + d) = ULMem.wa (y + d).
Proof.
  intros x y d E. unfold ULMem.wa. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  assert (E' : x mod 2 ^ 64 = y mod 2 ^ 64) by exact E.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change ((x + d) mod 2 ^ 64 = (y + d) mod 2 ^ 64).
  rewrite Zplus_mod, E', <- Zplus_mod. reflexivity.
Qed.

(* slti a1,s7,0 with s7 = t_unk >= 0 gives 0. *)
Lemma f27_slti0 : forall u, 0 <= u < 2 ^ 63 -> ULPE.v_slti (Z_to_bv 64 u) 0 = Z_to_bv 64 0.
Proof.
  intros u Hu. unfold ULPE.v_slti, ULPE.zsig.
  assert (E : bv_unsigned (Z_to_bv 64 u) = u) by (apply MState.unsigned_lit; lia).
  rewrite (ULPE.bv_signed_small (Z_to_bv 64 u)) by (rewrite E; lia). rewrite E.
  destruct (Z.ltb_spec u 0); [lia | reflexivity].
Qed.

(* beqz on a non-zero value (0x82888, blk = phi + 18 <> 0) is not taken. *)
Lemma f27_eqb0 : forall v, 0 < v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !MState.unsigned_lit in HC by lia. lia.
Qed.

(* sltiu with a first operand below the (unsigned) immediate gives 1. *)
Lemma f27_sltiu1 : forall (x : word) imm, bv_unsigned x < bv_wrap 64 imm -> ULPE.v_sltiu x imm = Z_to_bv 64 1.
Proof.
  intros x imm H. unfold ULPE.v_sltiu. destruct (Z.ltb_spec (bv_unsigned x) (bv_wrap 64 imm)); [reflexivity | lia].
Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot rewritten to
   a concrete value. *)
Lemma f27_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a register slot `getr regs r` to its carried value, from H : rg regs r v. *)
Ltac f27_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* Replace the condition of the branch at the head of the goal by its value v: closed conditions by computation
   (f27_brc), others by the proof pf of `c = v` (f27_br). *)
Ltac f27_brc v :=
  lazymatch goal with
  | |- context [if ?c then _ else _] => replace c with v by (vm_compute; reflexivity); cbv_concl_iota
  end.
Ltac f27_br v pf :=
  lazymatch goal with
  | |- context [if ?c then _ else _] => replace c with v by (symmetry; pf); cbv_concl_iota
  end.

(* and with the all-ones mask (neg of 1) keeps a 64-bit value. *)
Lemma f27_land_m1 : forall b, 0 <= b < 18446744073709551616 -> Z.land 18446744073709551615 b = b.
Proof.
  intros b Hb. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small.
  change (2 ^ 64) with 18446744073709551616. exact Hb.
Qed.

(* a6 after 0x828a0-0x828b0 (sub a0,s11,a4 ; sltiu a6,a0,-7 ; neg a6,a6 ; and a6,a6,a0) with s11 = -8 and
   a4 = blk = phi + 18: a0 = 2^64 - 8 - blk is below 2^64 - 7, so the sltiu gives 1, its negation is the all-ones
   mask and a6 = a0 = -8 - blk (the left side is the register value the step tactics leave). *)
Lemma f27_a6_eq : forall phi, 0 < phi -> phi + 50 <= 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (ULPE.v_sltiu
      (Z_to_bv 64 (18446744073709551608 - bv_unsigned (Z_to_bv 64 (phi + 18)))) (-7)))))
    (bv_unsigned (Z_to_bv 64 (18446744073709551608 - bv_unsigned (Z_to_bv 64 (phi + 18))))))
  = Z_to_bv 64 (-8 - (phi + 18)).
Proof.
  intros phi H0 H50.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  rewrite (MState.unsigned_lit (phi + 18)) by lia.
  rewrite (MState.unsigned_lit (18446744073709551608 - (phi + 18))) by lia.
  rewrite f27_sltiu1
    by (rewrite MState.unsigned_lit by lia; change (bv_wrap 64 (-7)) with 18446744073709551609; lia).
  change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with 18446744073709551615.
  rewrite f27_land_m1 by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  replace (18446744073709551608 - (phi + 18)) with ((-8 - (phi + 18)) + 1 * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* A byte of a live block of the cut is neither a frame byte nor a side-stack byte: the allocator laws put the
   block below stklo and off the side stack (a_laws_blocks), and the frame is at or above stklo (FRA's real arm) or
   on the side stack (side arm). *)
Lemma f27_blk : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> ~ (fr <= a < fr + FRAME_BYTES) /\ ~ AC.a_in_fs AC.ASYMS mem a.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha.
  assert (HAH : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md)
    by (destruct HFRA as (A0 & sp0 & s50 & HF); tauto).
  assert (Hloc : (forall x, fr <= x < fr + FRAME_BYTES ->
                    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END) \/
                 (forall x, fr <= x < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem x))
    by (destruct HFRA as (A0 & sp0 & s50 & HF); tauto).
  destruct (lw_blocks (APIf rc) _ mem md p n HAH Hin) as [_ _ Hend _ Hall].
  destruct (Hall a Ha) as (_ & _ & _ & _ & Hnfs).
  split; [|exact Hnfs].
  intros Hfa. destruct Hloc as [Hreal|Hfs].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* With 50 <= len the cut's block (phi, len) lies apart from the frame, and its first byte is off the side stack. *)
Lemma f27_order : forall g fr regs mem md phi n, FRA B APIf ra g fr (hb1 phi n) regs mem md -> 50 <= n ->
  (fr + FRAME_BYTES <= phi \/ phi + 50 <= fr) /\ ~ AC.a_in_fs AC.ASYMS mem phi.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr regs mem md phi n HFRA Hn.
  assert (Hin : In (phi, n) (hb1 phi n ++ g_H g)) by (apply in_or_app; left; left; reflexivity).
  split; [|exact (proj2 (f27_blk g fr _ regs mem md phi n phi HFRA Hin ltac:(lia)))].
  destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (phi + 50) fr) as [R|R]; [right; exact R|].
  exfalso. apply (proj1 (f27_blk g fr _ regs mem md phi n (Z.max phi fr) HFRA Hin ltac:(lia))). lia.
Qed.

(* The official exits' common part at a state with the entry's memory: s2 = phi, s4 = len, FTURN, LK, FTL and
   IFS (S j) read memory and s1, s2, s4, s5, s8, s11 only. *)
Lemma f27_exit : forall g j phi fr regs regs' mem,
  F27K g j phi fr regs mem -> rg regs 20 (flen g j) -> FTL g j phi fr regs mem -> FTURN g j phi regs mem ->
  IFS g fr (S j) regs mem ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 20 = getr regs 20 ->
  getr regs' 21 = getr regs 21 -> getr regs' 24 = getr regs 24 -> getr regs' 27 = getr regs 27 ->
  rg regs' 18 phi /\ rg regs' 20 (flen g j) /\ FTURN g j phi regs' mem /\
  LK g fr j regs' mem /\ FTL g j phi fr regs' mem /\ IFS g fr (S j) regs' mem.
Proof.
  intros g j phi fr regs regs' mem HK H20 HFTL HFT HIFS E9 E18 E20 E21 E24 E27.
  pose proof HK as (HLK & H18 & _).
  split; [unfold rg in *; rewrite E18; exact H18|].
  split; [unfold rg in *; rewrite E20; exact H20|].
  split; [exact (Tac_ro.turn_reg g j phi regs regs' mem E9 HFT)|].
  split; [exact (f27_lk g fr j regs regs' mem HLK E9 E27)|].
  split; [exact (f27_ftl g j phi fr regs regs' mem HFTL E9 E21 E24)|].
  exact (Tac_ro.ifs_reg g fr (S j) regs regs' mem E9 HIFS).
Qed.

(* S_F27 (v1.9.0). The r = 0 exit proves the official Inv_B8292c_at (adopt 12: its body carries F28GAP) and hands
   it to the exit premise. *)
Lemma seg_F27 : forall j, Hat B APIf ra (Inv_B8292c_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82aa4_at B APIf ra) j -> Hat B APIf ra (Inv_B828b4_at B APIf ra) j.
Proof.
  intros j H0 H1 g c HInv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_B828b4_at, CUTST in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HK & Hs4 & HFTL &
    Hs9 & Hs7 & Ha0 & HPO & HFI & HFT & HIFS & Hs5). subst c.
  rewrite SEGS.
  assert (Hhalt : m_halted md = None) by (destruct HFRA as (A0 & sp0 & s50 & HF); tauto).
  pose proof HK as (HLK & H18 & H27 & Hphi0 & Hphi50 & Hflen & Hblk & HS312 & HS272 & HS24 & HS104 & HS136).
  destruct HS312 as (A1 & H91 & Hq312).
  pose proof (f27_rd8 mem _ _ Hq312 ltac:(apply length_le8)) as RD312.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  destruct (Z.eq_dec (t_rp (g_in g) j) 0) as [Er|Er].
  - (* r = 0: the loop registers are set; exit at 0x8292c. *)
    destruct (b7_unk_rp0 _ _ Er) as (Hu & _).
    assert (Hu63 : 0 <= t_unk (g_in g) j < 2 ^ 63) by lia.
    apply (sl_run regs (Z_to_bv 64 0x828b4) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x8292c /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 23 = getr regs 23 /\
         getr R 27 = getr regs 27 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
         getr R 24 = getr regs 24 /\
         getr R 10 = Z_to_bv 64 (phi + 26) /\ getr R 14 = Z_to_bv 64 (phi + 26) /\
         getr R 16 = Z_to_bv 64 (-8 - (phi + 18)) /\ getr R 17 = Z_to_bv 64 12 /\
         getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\ getr R 13 = Z_to_bv 64 0 /\
         getr R 15 = Z_to_bv 64 0 /\ getr R 28 = Z_to_bv 64 12)
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite f27_mkR_of_expand.
      rewrite Er in Hs9.
      f27_slot Hs9. f27_slot Hs7. f27_slot Ha0. f27_slot H91. f27_slot H27.
      (* 0x828b4 bne a0,s7: both counts are t_unk, not taken *)
      step. f27_br false ltac:(rewrite bv_eqb_refl; reflexivity).
      (* 0x828b8 seqz a0,s9 ; 0x828bc slti a1,s7,0 *)
      step. step.
      (* 0x828c0 beq a0,a1: seqz r = 1, slti unk = 0, not taken *)
      step. f27_br false ltac:(rewrite (f27_slti0 (t_unk (g_in g) j) Hu63); vm_compute; reflexivity).
      (* 0x828c4 beqz s9: r = 0, taken to 0x828f0 *)
      step. f27_brc true.
      (* 0x828f0 li t3,12 *)
      step.
      (* 0x828f4 ld a0,312(s1) = blk = phi + 18 ; 0x828f8 beqz a0,82fa0 (T55): blk <> 0, not taken *)
      step. step. f27_br false ltac:(apply f27_eqb0; lia).
      (* 0x828fc-0x82908: li a5,0 ; li a3,0 ; li a1,0 ; li a2,0 *)
      step. step. step. step.
      (* 0x8290c ld a4,312(s1) ; 0x82910 sub a0,s11,a4 ; 0x82914 addi a4,a4,8 ; 0x82918 sltiu a6,a0,-7 ;
         0x8291c neg a6,a6 ; 0x82920 and a6,a6,a0 ; 0x82924 li a7,12 ; 0x82928 mv a0,a4 *)
      step. step. step. step. step. step. step. step.
      finish. all: simp_regs; try reflexivity; try (f_equal; lia).
      (* a6 = s11 - blk (f27_a6_eq) *)
      exact (f27_a6_eq phi Hphi0 Hphi50).
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR18 & HR23 & HR27 & HR20 & HR21 & HR24 &
         HR10 & HR14 & HR16 & HR17 & HR11 & HR12 & HR13 & HR15 & HR28) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply H0. unfold Inv_B8292c_at, FCUTP, CUTST.
      destruct (f27_exit g j phi fr regs regs'' mem HK Hs4 HFTL HFT HIFS)
        as (E18 & E20 & EFT & ELK & EFTL & EIFS); try (rewrite Hreg; assumption).
      exists phi, regs'', mem, md', fr.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr _ regs regs'' mem md md' HFRA);
          [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [eapply ent_mat; [exact HENT | exact Hmat]|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact E18|]. split; [exact E20|]. split; [exact EFT|].
      split; [exact ELK|]. split; [exact EFTL|]. split; [exact EIFS|].
      unfold F28GAP.
      split; [apply (f27_K g j phi fr regs regs'' mem HK); rewrite Hreg; assumption|].
      split; [exact Er|].
      split; [unfold rg; rewrite Hreg, HR23; exact Hs7|].
      split; [exact HPO|].
      split; [exact HFI|].
      split; [unfold rg; rewrite Hreg; exact HR10|].
      split; [unfold rg; rewrite Hreg; exact HR14|].
      split; [unfold rg; rewrite Hreg; exact HR16|].
      split; [unfold rg; rewrite Hreg; exact HR17|].
      split; [unfold rg; rewrite Hreg; exact HR11|].
      split; [unfold rg; rewrite Hreg; exact HR12|].
      split; [unfold rg; rewrite Hreg; exact HR13|].
      split; [unfold rg; rewrite Hreg; exact HR15|].
      unfold rg; rewrite Hreg; exact HR28.
  - (* r <> 0: r = unk = -1, the three ports words are -7; exit at 0x82aa4. *)
    destruct (b7_unk_rpm _ _ Er) as (Er' & Eu).
    destruct (proj2 HPO Er) as (P0 & P4 & P8).
    pose proof (f27_rd4 mem _ _ P0 ltac:(apply length_le4)) as RD0.
    pose proof (f27_rd4 mem _ _ P4 ltac:(apply length_le4)) as RD4.
    pose proof (f27_rd4 mem _ _ P8 ltac:(apply length_le4)) as RD8.
    apply (sl_run regs (Z_to_bv 64 0x828b4) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x82aa4 /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27 /\
         getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\ getr R 24 = getr regs 24)
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite f27_mkR_of_expand.
      rewrite Er' in Hs9. rewrite Eu in Hs7, Ha0.
      f27_slot Hs9. f27_slot Hs7. f27_slot Ha0. f27_slot Hs5.
      (* 0x828b4 bne a0,s7: both -1, not taken *)
      step. f27_brc false.
      (* seqz a0,s9 = 0 ; slti a1,s7,0 = 1 ; 0x828c0 beq a0,a1 not taken *)
      step. step. step. f27_brc false.
      (* 0x828c4 beqz s9 (= -1) not taken *)
      step. f27_brc false.
      (* 0x828c8 lw a0,0(s5) = -7 (s5 = fr + 128) ; li a1,-7 ; 0x828d0 bne a0,a1 not taken *)
      step. step. step. f27_brc false.
      (* 0x828d4 lw a0,4(s5) ; li a1,-7 ; 0x828dc bne a0,a1 not taken *)
      step. step. step. f27_brc false.
      (* 0x828e0 lw a0,8(s5) ; li a1,-7 ; 0x828e8 bne a0,a1 not taken *)
      step. step. step. f27_brc false.
      (* 0x828ec j 82aa4 *)
      step.
      finish. all: simp_regs; try reflexivity; try (f_equal; lia).
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR18 & HR27 & HR20 & HR21 & HR24) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply H1.
      destruct (f27_exit g j phi fr regs regs'' mem HK Hs4 HFTL HFT HIFS)
        as (E18 & E20 & EFT & ELK & EFTL & EIFS); try (rewrite Hreg; assumption).
      exists phi, regs'', mem, md', fr.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr _ regs regs'' mem md md' HFRA);
          [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [eapply ent_mat; [exact HENT | exact Hmat]|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact E18|]. split; [exact E20|]. split; [exact EFT|].
      split; [exact ELK|]. split; [exact EFTL | exact EIFS].
Qed.

End S.
