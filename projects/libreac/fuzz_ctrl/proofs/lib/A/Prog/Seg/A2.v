(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 358 of its 400 lines of code are new or changed and 354 lines of the source are left out. *)
(* Segment A2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x80f54-0x80f84 (plan-asan FP.2), from the cut
   Inv_A80f54 (after the class-6 frame request, a0 = r) to the cut Inv_A80f88. 0x80f54 s5 = a0, 0x80f58 j, 0x80f60
   s6 = s5, 0x80f64 bnez s5,0x80f88.
   - Side-stack arm (a0 <> 0): to 0x80f88 with fr = s6 = s5 = r, sp = A, memory unchanged; the frame-location facts
     (r mod 32 = 0, [r, r + 3136) in FS, FS + 6328320 <= r, the FakeStack record FSREC r) come from the cut.
   - Real-stack arm (a0 = 0): 0x80f68-0x80f70 s6 = (A - 3136) & -32 = A - 3136 (A mod 32 = 0); the probe loop
     0x80f74-0x80f80 runs one turn: sp = A - 4096, `sd zero,0(sp)` writes [A - 4096, A - 4088) (inside the slot
     window [S - SLOT_STACK, S), above stklo, app memory), `blt s6,sp` is false (A - 3136 > A - 4096); 0x80f84
     sp = s6 = fr = A - 3136.
   The pre-frame subset PREF moves to the new sp / memory / model; the stack-low bound and the window are relative
   to the entry sp S, so they hold at sp = A - 3136. ENT and the input facts (push 6c: the input bytes at p, the
   live addressable block (p, n)) move across the probe store, which writes stack bytes above stklo only. *)
(* libreac v1.9.0 (S_A2 IDENTICAL-RENUMBER): pcs +0x20 (0x80f34 -> 0x80f54), cut names per v190-cutnames-A.tsv,
   the real-stack frame A - 3136 (0x80f68 / 0x80f6c `addi a0,sp,-0x800 ; addi a0,a0,-0x440`), FRAME_BYTES in the
   cut texts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

Lemma mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.



Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia.
  rewrite Z.mod_small by lia. rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* Every GNU_RELRO block of FrameAPI lies below GT = 0x5fe000 (computed over the list, whatever its entries). *)
Lemma relro_blk_below : forall lo len, In (lo, len) AF.frame_RELRO -> 0 <= lo /\ lo + len <= 6283264.
Proof.
  intros lo len Hil.
  assert (HR : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) AF.frame_RELRO = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HR. specialize (HR _ Hil). apply andb_true_iff in HR as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. lia.
Qed.

(* The image's segments all end at or below ASAN_GT = 0x5fe000 (as A/BzBridge.v's seg_tops_below, for that top). *)
Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma rsegs_below_gt : seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_below : forall segs top x n s,
  seg_tops_below segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* A run whose writes W are all at or above 0x5fe000 keeps every read-only byte, so it keeps ro_agree. *)
Lemma ro_agree_hi : forall W mem mem', ro_agree rsegs mem -> LF.munch W mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x -> 0x5fe000 <= x) -> ro_agree rsegs mem'.
Proof.
  intros W mem mem' Hro MU HW a Hra.
  pose proof Hra as Hra2. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr in Hra2.
  pose proof (bv_unsigned_in_range 64 a) as Hrange. unfold bv_modulus in Hrange.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrange.
  assert (L : bv_unsigned a < 0x5fe000).
  { revert Hra2. match goal with |- context [find_segment ?sg ?x ?n] =>
      destruct (find_segment sg x n) as [s|] eqn:E; intros Hra2; [|discriminate Hra2];
      destruct (find_segment_below sg 0x5fe000 x n s rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
      [exact L | cbn in L; lia] end. }
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite MU; [exact (Hro a Hra)|].
  destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho]; [exact Ho|].
  exfalso. pose proof (HW (bv_unsigned a) Hrange Ho). lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The heap laws this file reads (Contract.a_laws), each taken apart once, here: a Theorem Labs lane's generations append
   conjuncts at every level, so a position is read only in these lemmas. *)

Lemma a2_mat : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md md' Hm. destruct (lw_mat_le (APIf rc) H mem md md' Hm) as [X _ Y _].
  split; [exact X | exact Y].
Qed.

Lemma a2_store : forall H mem mem' md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hst Hw. destruct (lw_store (APIf rc) H mem mem' md HAH Hst Hw) as [X O Y Z].
  split; [exact X | split; [exact O | split; [exact Y | exact Z]]].
Qed.

Lemma a2_blocks : forall H mem md p n, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_img a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin. destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ X _ Y].
  split; [exact X|].
  intros a Ha. destruct (Y a Ha) as (Y1 & _ & Y3 & _ & Y5). split; [exact Y1 | split; [exact Y3 | exact Y5]].
Qed.

Lemma a2_fs_place : forall H mem md b, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ b mod 4096 = 0 /\ (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb. destruct (lw_fs_place (APIf rc) H mem md b HAH Hw Hb) as [X1 X2 X3 X4].
  split; [exact X1 | split; [exact X2 | split; [exact X3 | exact X4]]].
Qed.

(* PREF moves across a register change that keeps sp, gp, tp, s0, s1, s10 and across lazy-page materialization. *)
Lemma pref_move : forall g A sp regs regs' mem md md',
  PREF B APIf ra g A sp regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  PREF B APIf ra g A sp regs' mem md'.
Proof.
  intros g A sp regs regs' mem md md' HP E2 E3 E4 E8 E9 E26 Hmat.
  destruct HP as (HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 & Hr3 &
    Hr26 & HAm & HAS & HS432 & Hspa & HA416 & HS4096 & HSapp & Hstk & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & HnMax & Hlive).
  destruct (a2_mat (g_H g) mem md md' Hmat) as (HAHm & Hstklo_eq).
  split; [exact (AsanRTInv.RT_any sp sp mem md md' HRT)|].
  split; [exact (HAHm HAH)|].
  split; [exact Hro|].
  split; [destruct Hsn as (He & Hh & Hf); split; [exact He|];
          split; [exact Hh|]; rewrite (sl_mat_fds md md' Hmat); exact Hf|].
  split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
  split; [exact Hgimg|].
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite Hstklo_eq; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  repeat (split; [assumption|]). exact Hlive.
Qed.

(* The real-stack arm run 0x80f54-0x80f88 (a0 = 0). *)
Lemma a2_real_evt : forall regs mem A,
  getr regs 2 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 0 ->
  0x5fe000 <= A - 4096 -> A < 2 ^ 63 -> A mod 32 = 0 ->
  ULMem.wr_at rsegs mem (A - 4096) 8 ->
  evt rsegs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
     pc' = Z_to_bv 64 0x80f88 /\ mem' = write_to_mem mem (ULMem.wa (A - 4096)) (le8 (Z_to_bv 64 0)) /\
     getr R 2 = Z_to_bv 64 (A - 3136) /\ getr R 22 = Z_to_bv 64 (A - 3136) /\ getr R 21 = Z_to_bv 64 0 /\
     getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
     getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26)
    (MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x80f54) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem A Hr2 Hr10 HA1 HA2 HAm Hwr.
  pose proof (ULMem.wr_at_store_ok rsegs mem (A - 4096) 8 0 8 Hwr ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS.
  rewrite mkR_of_expand. rewrite Hr2, Hr10.
  (* 0x80f54 mv s5,a0 ; j ; mv s6,s5 ; bnez s5 (s5 = 0, not taken) *)
  step. step. step. step. if_false.
  (* 0x80f68 addi ; addi ; andi s6,a0,-32 = A - 3136 *)
  step. step. step.
  rewrite ?(MState.unsigned_lit (A + -3136)) by lia.
  rewrite (land_align32 (A + -3136)) by lia.
  replace ((A + -3136) / 32 * 32) with (A - 3136) by (Z.div_mod_to_equations; lia).
  (* 0x80f74 lui a0,0x1 ; 0x80f78 sub sp,sp,a0 = A - 4096 *)
  step. step.
  rewrite ?(MState.unsigned_lit A) by lia.
  (* 0x80f7c sd zero,0(sp) ; 0x80f80 blt s6,sp (A - 3136 < A - 4096 is false) *)
  step. step.
  assert (HL : bv_lts (Z_to_bv 64 (A - 3136)) (Z_to_bv 64 (A - 4096)) = false)
    by (unfold bv_lts; rewrite !signed_lit by lia; apply Z.ltb_ge; lia).
  rewrite HL. cbv_concl_iota.
  (* 0x80f84 mv sp,s6 *)
  step.
  finish.
  all: simp_regs; reflexivity.
Qed.

(* The side-stack arm run 0x80f54-0x80f88 (a0 = r <> 0). *)
Lemma a2_side_evt : forall regs mem r,
  getr regs 10 = Z_to_bv 64 r -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = false ->
  evt rsegs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
     pc' = Z_to_bv 64 0x80f88 /\ mem' = mem /\ getr R 22 = Z_to_bv 64 r /\ getr R 21 = Z_to_bv 64 r /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
     getr R 9 = getr regs 9 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26)
    (MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x80f54) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem r Hr10 E.
  rewrite mkR_of_expand. rewrite Hr10.
  step. step. step. step.
  rewrite E. cbn [negb]. cbv_concl_iota.
  finish.
  all: simp_regs; reflexivity.
Qed.

Lemma seg_A2 : Hcut B APIf ra (Inv_A80f88 B APIf ra) -> Hcut B APIf ra (Inv_A80f54 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof FRAME_BYTES_val as HFBv.
  destruct HInv as (regs & mem & md & A & r & Ec & HP & HENT & Hr10 & Hrr & H23 & H24 & Hsel & Hinb & Hina).
  subst c.
  pose proof HP as HP2.
  destruct HP2 as (HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 & Hr3 &
    Hr26 & HAm & HAS & HS432 & Hspa & HA416 & HS4096 & HSapp & Hstk & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & HnMax & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (g_H g) mem md HAH) as Hhigh.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as HAb.
  unfold AC.aspZ in Haspz. rewrite Haspz in HAb. unfold bv_modulus in HAb. change (2 ^ Z.of_N 64) with (2 ^ 64) in HAb.
  unfold HIGHMEM_BEG in Hhigh. unfold APPMEM_END in HSapp. unfold AF.SLOT_STACK in Hstklo.
  rewrite SEGS.
  destruct (bv_eqb (getr regs 10) (Z_to_bv 64 0)) eqn:E.
  - (* real-stack arm: a0 = 0 *)
    apply bv_eqb_eq in E.
    assert (Hwr : ULMem.wr_at rsegs mem (A - 4096) 8).
    { destruct Hstk as (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi.
      exact (proj1 (H (A - 4096 + i) ltac:(unfold AF.SLOT_STACK; lia))). }
    apply (sl_run regs (Z_to_bv 64 0x80f54) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x80f88 /\
         mem' = write_to_mem mem (ULMem.wa (A - 4096)) (le8 (Z_to_bv 64 0)) /\
         getr R 2 = Z_to_bv 64 (A - 3136) /\ getr R 22 = Z_to_bv 64 (A - 3136) /\ getr R 21 = Z_to_bv 64 0 /\
         getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
         getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + apply a2_real_evt; [exact Hr2 | exact E | lia | lia | exact HAm | exact Hwr].
    + intros R pc' mem2 regs'' md' (Hpc & Hmem & HR2 & HR22 & HR21 & HR3 & HR4 & HR8 & HR9 & HR23 & HR24 & HR26)
        Hreg Hmat.
      subst pc' mem2.
      set (mem' := write_to_mem mem (ULMem.wa (A - 4096)) (le8 (Z_to_bv 64 0))).
      assert (Hlen : Z.of_nat (length (le8 (Z_to_bv 64 0))) = 8) by reflexivity.
      assert (MU : LF.munch [(A - 4096, A - 4088)] mem mem').
      { unfold mem'. apply (LF.munch_write [(A - 4096, A - 4088)] mem mem (A - 4096) (le8 (Z_to_bv 64 0))).
        - apply LF.munch_refl.
        - lia.
        - rewrite Hlen; lia.
        - rewrite Hlen. cbn. left. lia. }
      assert (WM : LF.wmono rsegs mem mem') by (unfold mem'; apply LF.wmono_write; apply LF.wmono_refl).
      assert (HWout : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside [(A - 4096, A - 4088)] x -> A - 4096 <= x < A - 4088).
      { intros x Hx Ho. destruct (Z.le_gt_cases (A - 4096) x); destruct (Z.lt_ge_cases x (A - 4088)); try lia;
          exfalso; apply Ho; cbn [LF.outside]; (split; [lia | exact I]). }
      assert (HAW : all_app [(A - 4096, A - 4088)]).
      { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END. lia. }
      assert (HD : rt_disjoint [(A - 4096, A - 4088)]).
      { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
          RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
      pose proof (AsanRTInv.RT_store A (A - 3136) mem mem' md md' _ HRT MU WM HAW HD) as HRT'.
      assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok (g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
        mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
        destruct (kb_outside_dec [(A - 4096, A - 4088)] a) as [Ho|Ho]; [exact Ho|].
        exfalso. apply Hns. pose proof (HWout a Ha Ho). unfold AC.a_store_ok. right; left. unfold APPMEM_END. lia. }
      assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
        by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
      destruct (a2_store (g_H g) mem mem' md HAH HstoreC HwmL) as (HAH1 & _ & HSTK1 & HSTKhi1).
      destruct (a2_mat (g_H g) mem' md md' Hmat) as (HAHm & HSTK2).
      assert (Hro' : ro_agree rsegs mem').
      { apply (ro_agree_hi [(A - 4096, A - 4088)] mem mem' Hro MU). intros x Hx Ho.
        pose proof (HWout x Hx Ho). lia. }
      pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _).
      assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
      { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { apply MU. rewrite MState.unsigned_lit by lia. cbn [LF.outside]. split; [lia | exact I]. }
        unfold mbyte. rewrite Hm. reflexivity. }
      assert (Hsn' : sink_none B mem' md').
      { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split].
        - destruct Hcse as (Hthrm & Hlockm). split.
          + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
          + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
        - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia].
        - rewrite (sl_mat_fds md md' Hmat). exact Hfd. }
      assert (Hgimg' : G_img_c B AF.frame_RELRO mem').
      { intros a Hin. rewrite KBlo.
        - exact (Hgimg a Hin).
        - destruct Hin as (lo & len & Hil & Hr). pose proof (relro_blk_below lo len Hil). lia.
        - destruct Hin as (lo & len & Hil & Hr). pose proof (relro_blk_below lo len Hil). lia. }
      assert (Hstk' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
      { unfold mem'. apply LF.stk_write; [exact Hstk | lia | rewrite Hlen; lia]. }
      assert (Hsaved' : bytes_at rsegs mem' (g_S g - 104) (saved_bytes ra g)).
      { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
        unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
        cbn [LF.outside]. split; [lia | exact I]. }
      rewrite <- SEGS. apply Hexit.
      exists regs'', mem', md', A, (A - 3136), (A - 3136), 0.
      split; [reflexivity|].
      split.
      { split; [exact HRT'|].
        split; [exact (HAHm HAH1)|].
        split; [exact Hro'|].
        split; [exact Hsn'|].
        split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
        split; [exact Hgimg'|].
        split; [rewrite Hreg; exact HR2|].
        split; [Z.div_mod_to_equations; lia|].
        split; [unfold AC.aspZ; rewrite Hreg, HR2; apply MState.unsigned_lit; lia|].
        split; [rewrite HSTK2, HSTK1; unfold AF.SLOT_STACK; lia|].
        split; [rewrite Hreg, HR4; exact Hr4|].
        split; [unfold rg in *; rewrite Hreg, HR8; exact Hr8|].
        split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|].
        split; [rewrite Hreg, HR3; exact Hr3|].
        split; [unfold rg in *; rewrite Hreg, HR26; exact Hr26|].
        split; [exact HAm|].
        split; [exact HAS|].
        split; [exact HS432|].
        split; [lia|].
        split; [exact HA416|].
        split; [lia|].
        split; [unfold APPMEM_END; lia|].
        split; [exact Hstk'|].
        split; [exact Hsaved'|].
        split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
        split; [intros a Ha; exact (addressable_kept mem mem' a 1 (HAG a Ha) (munch_meta _ mem mem' MU HAW))|].
        split; [intros a Ha; exact (addressable_kept mem mem' a 1 (HWA a Ha) (munch_meta _ mem mem' MU HAW))|].
        split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
        split; [exact HnMax|].
        exact Hlive. }
      split.
      { apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
        apply (ent_munch APIf g [] mem mem' md [(A - 4096, A - 4088)] HENT HAH MU).
        - intros x Hk. cbn [LF.outside]. split; [|exact I]. intros [Hx1 Hx2].
          destruct Hk as [(q & kk & i & Hin & _ & Hi & ->) | [Himg | [Habv | [(b & Hb & ->) | (q & kk & i & Hin & _ & Hi & ->)]]]].
          + destruct (a2_blocks (g_H g) mem md q kk HAH Hin) as (Hqk & _).
            unfold AF.SLOT_STACK in Hstklo. lia.
          + pose proof (img_below_GT x Himg) as X. unfold AC.GT in X. unfold AF.SLOT_STACK in Hstklo. lia.
          + lia.
          + unfold shadow_addr, ASAN_K in Hx1, Hx2.
            assert (Hb0 : 0 <= b < 140737488355328).
            { destruct Hb as [Hb|Hb]; [pose proof (img_below_GT b Hb) as X; unfold AC.GT in X; lia | unfold APPMEM_END in Hb; lia]. }
            assert (Hd : 0 <= b / 8 < 17592186044416)
              by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
            unfold AF.SLOT_STACK in Hstklo. lia.
          + (* the shadow byte of an entry block byte (frame batch 2): a shadow byte, below the stack *)
            destruct (a2_blocks (g_H g) mem md q kk HAH Hin) as (_ & Hall).
            destruct (Hall (q + i) ltac:(lia)) as (Hap & _ & _).
            unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap.
            unfold shadow_addr, ASAN_K in Hx1, Hx2.
            assert (Hd : 0 <= (q + i) / 8 < 17592186044416)
              by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
            unfold AF.SLOT_STACK in Hstklo. lia.
        - exact HSTK1.
        - exact HSTKhi1.
        - intros a Hia Ho.
          assert (Htp16 : forall i, 0 <= i < 16 ->
                    mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
            by (intros i Hi; apply KBlo; unfold AC.as_tp, AC.ASYMS; cbn; lia).
          exact (proj1 (ent_owned_img APIf (g_H g) (g_H g) mem md mem' md a HAH HAH1 HSTK1 Htp16 Hia) Ho). }
      split; [unfold rg; rewrite Hreg; exact HR22|].
      split; [Z.div_mod_to_equations; lia|].
      split; [unfold rg; rewrite Hreg; exact HR21|].
      split; [lia|].
      split; [lia|].
      split; [left; reflexivity|].
      split; [unfold rg in *; rewrite Hreg, HR23; exact H23|].
      split; [unfold rg in *; rewrite Hreg, HR24; exact H24|].
      split.
      { left. split; [reflexivity|]. split; [reflexivity|]. intros a Ha.
        rewrite HSTK2, HSTK1. unfold APPMEM_END. lia. }
      (* the input facts: the probe store [A - 4096, A - 4088) is on the stack, above stklo; the input block is
         an entry block, below stklo (a_laws_blocks), and the store writes no shadow byte (all_app). *)
      split.
      { eapply fl_bytes; [exact Hinb | exact MU |]. intros x Hx.
        rewrite <- (g_n_len g) in Hx.
        destruct (Z.lt_ge_cases 0 (g_n g)) as [Hn|Hn]; [|lia].
        destruct (Hina Hn) as (Hinp & _).
        destruct (a2_blocks (g_H g) mem md (g_p g) (g_n g) HAH Hinp) as (Hpk & _).
        cbn [LF.outside]. split; [lia | exact I]. }
      intros Hn. destruct (Hina Hn) as (Hinp & Hadp). split; [exact Hinp|].
      exact (addressable_kept mem mem' (g_p g) (g_n g) Hadp (munch_meta _ mem mem' MU HAW)).
  - (* side-stack arm: a0 = r <> 0 *)
    assert (E' : bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = false) by (unfold rg in Hr10; rewrite <- Hr10; exact E).
    destruct Hsel as [Er|(Hrm & HFS & Hfs & Hrec)].
    { subst r. rewrite bv_eqb_refl in E'. discriminate E'. }
    assert (HfrFB : r + FRAME_BYTES <= A).
    { destruct (Hfs (r + FRAME_BYTES - 1) ltac:(lia)) as (b & Hb & Hw & Hbr).
      destruct (a2_fs_place (g_H g) mem md b HAH Hw Hb) as (_ & Hbs & _).
      unfold AC.FS_SIZE in *. lia. }
    apply (sl_run regs (Z_to_bv 64 0x80f54) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x80f88 /\ mem' = mem /\ getr R 22 = Z_to_bv 64 r /\
         getr R 21 = Z_to_bv 64 r /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
         getr R 9 = getr regs 9 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + apply a2_side_evt; [exact Hr10 | exact E'].
    + intros R pc' mem2 regs'' md' (Hpc & Hmem & HR22 & HR21 & HR2 & HR3 & HR4 & HR8 & HR9 & HR23 & HR24 & HR26)
        Hreg Hmat.
      subst pc' mem2.
      rewrite <- SEGS. apply Hexit.
      exists regs'', mem, md', A, r, A, r.
      split; [reflexivity|].
      split.
      { apply (pref_move g A A regs regs'' mem md md' HP); first [rewrite Hreg; assumption | exact Hmat]. }
      split; [exact (ent_mat APIf g [] mem md md' HENT Hmat)|].
      split; [unfold rg; rewrite Hreg; exact HR22|].
      split; [exact Hrm|].
      split; [unfold rg; rewrite Hreg; exact HR21|].
      split; [exact Hrr|].
      split; [exact HfrFB|].
      split; [right; reflexivity|].
      split; [unfold rg in *; rewrite Hreg, HR23; exact H23|].
      split; [unfold rg in *; rewrite Hreg, HR24; exact H24|].
      split.
      { right. split; [reflexivity|]. split; [reflexivity|]. split; [exact HFS|]. split; [exact Hfs | exact Hrec]. }
      split; [exact Hinb | exact Hina].
Qed.

End S.
