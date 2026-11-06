(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its numbers changed; 308 of its 392 lines of code are new or changed and 2473 lines of the source are left out. *)
(* Segment A2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the frame-arm selection,
   0x81090 .. 0x810c4 (cut Inv_B81090 -> cut Inv_B810c4). The segment moves the frame request result a0 into s8 and
   s9 (0x81090 mv s8,a0;
   0x81094 j; 0x8109c mv s9,s8) and branches on it (0x810a0 bnez s8,0x810c4):
   - side-stack arm (a0 <> 0): the frame is the request result fr = a0 in the side stack, sp stays A; the join is
     reached at once.
   - real-stack arm (a0 = 0): s9 = (A - 3136) & -32 = A - 3136 (A mod 32 = 0; 0x810a4 / 0x810a8 addi -2048 / -1088,
     0x810ac andi), then the stack-probe loop 0x810b4..0x810bc (sub sp,sp,0x1000; sd zero,0(sp); blt s9,sp,0x810b4)
     runs exactly once, since sp - 4096 = A - 4096 < A - 3136 = s9, and 0x810c0 mv sp,s9 lowers sp to
     fr = A - 3136. The one probe store writes 8 bytes at A - 4096, inside the slot window [S - SLOT_STACK, S) and
     in the real stack [stklo, APPMEM_END) (AH's stack-high law puts stklo in HighMem), so the asan runtime cells,
     the heap invariant, stklo, the image bytes and the saved caller registers are kept.
   No instrumented shadow check and no trap is in range. The pre-frame subset PREF is re-established conjunct by
   conjunct at the join (a2_pref_move for the side arm, a2_pref_real for the real arm). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

(* The start register map of sl_run, written with the stepping engine's mkR so the engine reads it. *)
Lemma a2_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (Sem.reg_get regs 1) (Sem.reg_get regs 2) (Sem.reg_get regs 3) (Sem.reg_get regs 4) (Sem.reg_get regs 5)
      (Sem.reg_get regs 6) (Sem.reg_get regs 7) (Sem.reg_get regs 8) (Sem.reg_get regs 9) (Sem.reg_get regs 10)
      (Sem.reg_get regs 11) (Sem.reg_get regs 12) (Sem.reg_get regs 13) (Sem.reg_get regs 14) (Sem.reg_get regs 15)
      (Sem.reg_get regs 16) (Sem.reg_get regs 17) (Sem.reg_get regs 18) (Sem.reg_get regs 19) (Sem.reg_get regs 20)
      (Sem.reg_get regs 21) (Sem.reg_get regs 22) (Sem.reg_get regs 23) (Sem.reg_get regs 24) (Sem.reg_get regs 25)
      (Sem.reg_get regs 26) (Sem.reg_get regs 27) (Sem.reg_get regs 28) (Sem.reg_get regs 29) (Sem.reg_get regs 30)
      (Sem.reg_get regs 31).
Proof. intros regs. reflexivity. Qed.

(* The arm test 0x810a0 bnez s8: s8 = a0 = Z_to_bv 64 r is non-zero exactly when r mod 2^64 <> 0. *)
Lemma a2_cond : forall r, negb (bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0)) = negb (r mod 2 ^ 64 =? 0).
Proof. intros r. unfold bv_eqb. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma a2_c1 : forall r, r mod 2 ^ 64 <> 0 -> negb (bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0)) = true.
Proof. intros r H. rewrite a2_cond. apply negb_true_iff, Z.eqb_neq. exact H. Qed.

Lemma a2_c0 : forall r, r mod 2 ^ 64 = 0 -> negb (bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0)) = false.
Proof. intros r H. rewrite a2_cond, H. reflexivity. Qed.

(* 0x810ac andi s9,a0,-32 on a 32-aligned value keeps it. *)
Lemma a2_land : forall x, 0 <= x < 2 ^ 64 -> x mod 32 = 0 -> Z.land x 18446744073709551584 = x.
Proof.
  intros x Hx Hm. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 5) as [H5|H5].
  - assert (Ex : x = (x / 32) * 2 ^ 5).
    { change (2 ^ 5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia. }
    assert (Hb : Z.testbit x n = false).
    { rewrite Ex. apply Z.mul_pow2_bits_low. lia. }
    rewrite Hb. reflexivity.
  - destruct (Z.lt_ge_cases n 64) as [H64|H64].
    + replace 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity.
      rewrite Z.ldiff_spec, Z.ones_spec_low by lia. rewrite Z.ones_spec_high by lia.
      rewrite andb_true_r. reflexivity.
    + assert (Hb : Z.testbit x n = false).
      { rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite Hb. reflexivity.
Qed.

(* s9 after 0x810ac: the real-arm frame base fr = A - 3136. *)
Lemma a2_s9 : forall A, 4096 <= A < 2 ^ 63 -> A mod 32 = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + -3136))) 18446744073709551584) = Z_to_bv 64 (A - 3136).
Proof.
  intros A HA Hm. rewrite MState.unsigned_lit by lia.
  rewrite a2_land by (Z.div_mod_to_equations; lia). f_equal; lia.
Qed.

(* The probe-loop latch 0x810bc blt s9,sp is not taken after the first turn: s9 = A - 3136 >= A - 4096 = sp. *)
Lemma a2_blt : forall A, 4096 <= A < 2 ^ 63 -> A mod 32 = 0 ->
  bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + -3136))) 18446744073709551584))
         (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) = false.
Proof.
  intros A HA Hm.
  rewrite (MState.unsigned_lit (A + -3136)) by lia.
  rewrite (MState.unsigned_lit A) by lia.
  rewrite a2_land by (Z.div_mod_to_equations; lia).
  unfold bv_lts.
  rewrite !bv_signed_small; rewrite ?MState.unsigned_lit by lia; try lia.
  all: apply Z.ltb_ge; lia.
Qed.

(* The image's loaded segments all end below HighMem, so no byte of the real stack is read-only. *)
Lemma a2_rsegs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? HIGHMEM_BEG) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma a2_ro_high : forall x, HIGHMEM_BEG <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) a2_rsegs_low s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). lia.
Qed.

(* The side-stack arm 0x81090 .. 0x810a0 (bnez s8 taken): s9 = s8 = a0, the other registers and memory kept. *)
Lemma a2_side_evt : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  getr regs 10 = Z_to_bv 64 r -> r mod 2 ^ 64 <> 0 ->
  evt rsegs (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x810c4) fc None m (seg_rom rsegs) /\
      getr R 25 = Z_to_bv 64 r /\ getr R 24 = Z_to_bv 64 r /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
      getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
      getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x81090) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m r E10 Hr.
  rewrite a2_mkR_of.
  assert (E : Sem.reg_get regs 10 = Z_to_bv 64 r) by exact E10.
  rewrite E.
  do 4 step.
  if_true_by (a2_c1 r Hr).
  finish.
  all: reflexivity.
Qed.

(* The real-stack arm 0x81090 .. 0x810c0 (bnez s8 not taken): s9 = sp = A - 3136 after one probe-loop turn whose
   store writes the 8 bytes at A - 4096. *)
Lemma a2_real_evt : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r A : Z),
  getr regs 10 = Z_to_bv 64 r -> r mod 2 ^ 64 = 0 ->
  getr regs 2 = Z_to_bv 64 A -> 4096 <= A < 2 ^ 63 -> A mod 32 = 0 ->
  store_ok rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) 8 = true ->
  evt rsegs (fun ms' => exists R bs, ms' = MS R F (Z_to_bv 64 0x810c4) fc None
         (write_to_mem m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) bs) (seg_rom rsegs) /\
      length bs = 8%nat /\
      getr R 25 = Z_to_bv 64 (A - 3136) /\ getr R 2 = Z_to_bv 64 (A - 3136) /\ getr R 24 = Z_to_bv 64 r /\
      getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
      getr R 26 = getr regs 26 /\ getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x81090) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m r A E10 Hr E2 HA HAm HS.
  rewrite a2_mkR_of.
  assert (E : Sem.reg_get regs 10 = Z_to_bv 64 r) by exact E10.
  assert (E' : Sem.reg_get regs 2 = Z_to_bv 64 A) by exact E2.
  rewrite E, E'.
  do 4 step.
  if_false_by (a2_c0 r Hr).
  do 7 step.
  if_false_by (a2_blt A HA HAm).
  step.
  finish.
  all: first [reflexivity | exact (a2_s9 A HA HAm)].
Qed.

Section A2.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The generated allocator laws are read through SlotInv.v's lw_* lemmas (one lemma per law, by statement); ENT is
   moved only by Seg/Tac_slot.v's transports (ent_munch, ent_mat), never taken apart here. *)

(* PREF moves across a register change that keeps sp, gp, tp, s0, s1, s10 and across lazy-page materialization
   (the side arm: memory unchanged). *)
Lemma a2_pref_move : forall g A sp regs regs' mem md md',
  PREF B APIf ra g A sp regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  PREF B APIf ra g A sp regs' mem md'.
Proof.
  intros g A sp regs regs' mem md md' HP E2 E3 E4 E8 E9 E26 Hmat.
  destruct HP as (HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 & Hr3 &
    Hr26 & Hrest).
  destruct (lw_mat_le (APIf rc) (g_H g) mem md md' Hmat) as [HAHm _ Hstklo_eq _].
  unfold PREF.
  split; [exact (AsanRTInv.RT_any sp sp mem md md' HRT)|].
  split; [exact (HAHm HAH)|].
  split; [exact Hro|].
  split; [destruct Hsn as (He & Hh & Hf); split; [exact He|]; split; [exact Hh|];
          rewrite (sl_mat_fds md md' Hmat); exact Hf|].
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
  exact Hrest.
Qed.

(* PREF moves across the real arm: sp lowered from A to A - 3136, the probe store of 8 bytes at A - 4096, and
   lazy-page materialization. The store is app memory in [stklo, APPMEM_END) (a_store_ok, so AH / stklo kept by
   a_laws_store), away from the runtime's cells (rt_disjoint, so RT kept by RT_store), above every image byte (so
   ro_agree, the sink words and the RELRO bytes are kept) and below the saved caller registers. The frame
   [A - 3136, A) lies in the real stack. ENT moves across the same store with ent_munch (the probe byte is none of
   the addresses ENT speaks of: it lies in the slot window, below the entry sp S, above every image byte and every
   entry block, and it is not a shadow byte) and then with ent_mat. *)
Lemma a2_pref_real : forall g A regs regs' mem md md' bs,
  PREF B APIf ra g A A regs mem md -> ENT APIf g [] mem md -> length bs = 8%nat ->
  getr regs' 2 = Z_to_bv 64 (A - 3136) -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  PREF B APIf ra g A (A - 3136) regs' (write_to_mem mem (Lib.Mem.wa (A - 4096)) bs) md' /\
  ENT APIf g [] (write_to_mem mem (Lib.Mem.wa (A - 4096)) bs) md' /\
  (forall a, A - 3136 <= a < A - 3136 + FRAME_BYTES ->
     AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) (write_to_mem mem (Lib.Mem.wa (A - 4096)) bs) md' <= a < APPMEM_END).
Proof.
  intros g A regs regs' mem md md' bs HP HENT Hlen E2 E3 E4 E8 E9 E26 Hmat.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HP as (HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr26 &
    HAm & HAS & HA464 & HspA & HA448 & Hsp4096 & HSapp & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hnmax & Hlive & Hinb & Hinblk).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) (g_H g) mem md HAH) as Hhi.
  unfold AF.SLOT_STACK in *.
  assert (HB : HIGHMEM_BEG + 4096 <= A - 4096 /\ A < APPMEM_END) by lia.
  unfold HIGHMEM_BEG, APPMEM_END in HB.
  remember (write_to_mem mem (Lib.Mem.wa (A - 4096)) bs) as mem' eqn:Emem.
  assert (MU : Lib.Frame.munch [(A - 4096, A - 4088)] mem mem').
  { subst mem'. apply Lib.Frame.munch_write;
      [apply Lib.Frame.munch_refl | lia | rewrite Hlen; change (Z.of_nat 8) with 8; lia |].
    rewrite Hlen. cbn. left. lia. }
  assert (WM : Lib.Frame.wmono rsegs mem mem') by (subst mem'; apply Lib.Frame.wmono_write, Lib.Frame.wmono_refl).
  assert (KB : forall x : word, ~ (A - 4096 <= bv_unsigned x < A - 4088) -> mem' x = mem x).
  { intros x Hx. apply MU. cbn. split; [exact Hx | exact I]. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite KB; [reflexivity|]. rewrite MState.unsigned_lit by lia. lia. }
  assert (HAHs : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn. apply KB. rewrite MState.unsigned_lit by lia. intro Hin. apply Hn.
    unfold AC.a_store_ok. right; left. unfold APPMEM_END. lia. }
  assert (HWs : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (lw_store (APIf rc) (g_H g) mem mem' md HAH HAHs HWs) as [HAH1 Hown1 Hlo1 Hhi1].
  destruct (lw_mat_le (APIf rc) (g_H g) mem' md md' Hmat) as [HAHm _ Hlo2 _].
  assert (HAW : all_app [(A - 4096, A - 4088)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, APPMEM_END. lia. }
  assert (HD : rt_disjoint [(A - 4096, A - 4088)]).
  { unfold rt_disjoint. cbn [disjoint_from].
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    repeat split; try exact I; left; lia. }
  assert (Hro' : ro_agree rsegs mem').
  { intros a Ha. unfold Lib.Mem.mrd. rewrite KB; [exact (Hro a Ha)|]. intro Hin.
    rewrite (a2_ro_high a ltac:(unfold HIGHMEM_BEG; lia)) in Ha. discriminate Ha. }
  assert (Hsn' : sink_none B mem' md').
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|rewrite (sl_mat_fds md md' Hmat); exact Hfd]].
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
  assert (Hgimg' : G_img_c B AF.frame_RELRO mem').
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  (* ENT across the probe store: no byte of an entry block (they end at or below stklo <= S - SLOT_STACK), of the
     image (below GT), of the stack at or above S, or of a shadow byte (always below HIGHMEM_BEG: the shadow of
     the image, of the stack above S and of the entry blocks) lies in [A - 4096, A - 4088). *)
  assert (MUu : Frame.munch [(A - 4096, A - 4088)] mem mem') by exact MU.
  assert (HENTm : ENT APIf g [] mem' md).
  { eapply ent_munch; [exact HENT | exact HAH | exact MUu | | exact Hlo1 | exact Hhi1 |
                       intros a Hia Ho; exact (proj2 (Hown1 a) Ho)].
    intros x Hk.
    destruct Hk as [(q & k & i & Hin & Hni & Hi & ->) | [Hik | [Habk | [(b & Hor & ->) |
                    (q & k & i & Hin & Hni & Hi & ->)]]]].
    - destruct (lw_blocks (APIf rc) (g_H g) mem md q k HAH Hin) as [_ _ Hend _ _].
      apply out1. left. lia.
    - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg. apply out1. left. lia.
    - apply out1. right. lia.
    - assert (Happb : app_mem b).
      { unfold app_mem. destruct Hor as [Hib|Hrb].
        - pose proof (img_below_GT b Hib) as X. unfold AC.GT in X. left. unfold LOWMEM_END. lia.
        - right. split; [unfold HIGHMEM_BEG; lia | exact (proj2 Hrb)]. }
      pose proof (shadow_of_app b Happb) as Hsb.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb.
      apply out1. left. lia.
    - destruct (lw_blocks (APIf rc) (g_H g) mem md q k HAH Hin) as [_ _ _ _ Hall].
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _).
      pose proof (shadow_of_app (q + i) Happq) as Hsb.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb.
      apply out1. left. lia. }
  assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
  split.
  - unfold PREF.
    split; [exact (AsanRTInv.RT_store A (A - 3136) mem mem' md md' _ HRT MU WM HAW HD)|].
    split; [exact (HAHm HAH1)|].
    split; [exact Hro'|].
    split; [exact Hsn'|].
    split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
    split; [exact Hgimg'|].
    split; [exact E2|].
    split; [Z.div_mod_to_equations; lia|].
    split; [unfold AC.aspZ; rewrite E2; apply MState.unsigned_lit; lia|].
    split; [rewrite Hlo2, Hlo1; exact Hstklo|].
    split; [rewrite E4; exact Hr4|].
    split; [unfold rg in *; rewrite E8; exact Hr8|].
    split; [unfold rg in *; rewrite E9; exact Hr9|].
    split; [rewrite E3; exact Hr3|].
    split; [unfold rg in *; rewrite E26; exact Hr26|].
    split; [exact HAm|]. split; [exact HAS|]. split; [exact HA464|]. split; [lia|]. split; [exact HA448|].
    split; [lia|]. split; [exact HSapp|].
    split; [subst mem'; exact (Lib.Frame.stk_write rsegs mem _ _ (A - 4096) bs Hwin ltac:(lia)
                                 ltac:(rewrite Hlen; change (Z.of_nat 8) with 8; lia))|].
    split; [eapply fl_bytes; [exact Hsaved | exact MU |]; intros x Hx; unfold saved_bytes in Hx;
            rewrite !length_app, !length_le8 in Hx; cbn in Hx; cbn; split; [lia | exact I]|].
    split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
    split; [intros a Ha; exact (sl_addr_keep mem mem' [(A - 4096, A - 4088)] a 1 (HAG a Ha) MU HAW)|].
    split; [intros a Ha; exact (sl_addr_keep mem mem' [(A - 4096, A - 4088)] a 1 (HWA a Ha) MU HAW)|].
    split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
    split; [exact Hnmax|].
    split; [exact Hlive|].
    (* the input block: for n > 0 a live entry block, so it ends at or below stklo <= S - SLOT_STACK < A - 4096 *)
    apply (fra_in_keep g mem mem' [(A - 4096, A - 4088)] Hinb Hinblk MUu HAW).
    intros x Hx.
    destruct (Hinblk ltac:(lia)) as (Hin & _).
    destruct (lw_blocks (APIf rc) (g_H g) mem md (g_p g) (g_n g) HAH Hin) as [_ _ Hend _ _].
    apply out1. left. lia.
  - split; [exact HENT'|].
    intros a Ha. rewrite FRAME_BYTES_val in Ha. rewrite Hlo2, Hlo1. unfold APPMEM_END. lia.
Qed.

Lemma seg_A2 : Hcut B APIf ra (Inv_B810c4 B APIf ra) -> Hcut B APIf ra (Inv_B81090 B APIf ra).
Proof.
  intros Hbc g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & A & r & Ec & HP & HENT & Hr10 & Hr64 & Hp & Hn & Hsel). subst c.
  rewrite SEGS.
  pose proof HP as (HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 & Hr3 &
    Hr26 & HAm & HAS & HA464 & HspA & HA448 & Hsp4096 & HSapp & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hnmax & Hlive).
  unfold rg in Hr10, Hp, Hn.
  destruct (Z.eq_dec r 0) as [Hz|Hnz].
  - (* real-stack arm: the request result is 0 *)
    subst r.
    pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) (g_H g) mem md HAH) as Hhi.
    unfold AF.SLOT_STACK in Hstklo, Hwin.
    assert (HB : HIGHMEM_BEG + 4096 <= A - 4096 /\ A < APPMEM_END) by lia.
    unfold HIGHMEM_BEG, APPMEM_END in HB.
    assert (HS : store_ok rsegs mem (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) 8 = true).
    { rewrite MState.unsigned_lit by lia.
      replace (Z_to_bv 64 (A - 4096)) with (Lib.Mem.wa (A - 4096 + 0)) by (unfold Lib.Mem.wa; f_equal; lia).
      apply (Lib.Mem.wr_at_store_ok rsegs mem (A - 4096) 8 0 8); [| lia | change (Z.of_nat 8) with 8; lia].
      destruct Hwin as (Hw0 & Hw1 & Hw).
      split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hw (A - 4096 + i) ltac:(lia))). }
    apply (sl_run regs (Z_to_bv 64 0x81090) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x810c4 /\ exists bs, length bs = 8%nat /\
         mem' = write_to_mem mem (Lib.Mem.wa (A - 4096)) bs /\
         getr R 25 = Z_to_bv 64 (A - 3136) /\ getr R 2 = Z_to_bv 64 (A - 3136) /\ getr R 24 = Z_to_bv 64 0 /\
         getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
         getr R 26 = getr regs 26 /\ getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono;
        [exact (a2_real_evt regs fp_regs fp_csr mem 0 A Hr10 ltac:(reflexivity) Hr2 ltac:(lia) HAm HS)|].
      intros ms' (R & bs & -> & Hlen & H25 & H2 & H24 & H3 & H4 & H8 & H9 & H26 & H22 & H18).
      exists R, (Z_to_bv 64 0x810c4), (write_to_mem mem (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) - 4096)) bs).
      split; [reflexivity|].
      split; [reflexivity|].
      exists bs. split; [exact Hlen|].
      split; [rewrite MState.unsigned_lit by lia; reflexivity|].
      repeat (split; [assumption|]); assumption.
    + intros R pc' mem' regs'' md'
        (Hpc & bs & Hlen & Hmem & H25 & H2 & H24 & H3 & H4 & H8 & H9 & H26 & H22 & H18) Hreg Hmat.
      subst pc' mem'.
      destruct (a2_pref_real g A regs regs'' mem md md' bs HP HENT Hlen
                  ltac:(rewrite Hreg; exact H2) ltac:(rewrite Hreg; exact H3) ltac:(rewrite Hreg; exact H4)
                  ltac:(rewrite Hreg; exact H8) ltac:(rewrite Hreg; exact H9) ltac:(rewrite Hreg; exact H26) Hmat)
        as (HP' & HENT' & Hloc).
      rewrite <- SEGS.
      apply Hbc.
      exists regs'', (write_to_mem mem (Lib.Mem.wa (A - 4096)) bs), md', A, (A - 3136), (A - 3136), 0.
      split; [reflexivity|].
      split; [exact HP'|].
      split; [exact HENT'|].
      split; [unfold rg; rewrite Hreg; exact H25|].
      split; [Z.div_mod_to_equations; lia|].
      split; [unfold rg; rewrite Hreg; exact H24|].
      split; [lia|].
      split; [rewrite FRAME_BYTES_val; lia|].
      split; [left; reflexivity|].
      split; [unfold rg; rewrite Hreg, H22; exact Hp|].
      split; [unfold rg; rewrite Hreg, H18; exact Hn|].
      left. split; [reflexivity|]. split; [reflexivity|]. exact Hloc.
  - (* side-stack arm: the request result fr = r <> 0, in the side stack above the FakeStack metadata *)
    destruct Hsel as [Hr0|(Hr32 & Hsep & Hfs & Hrec)]; [contradiction|].
    assert (Hnz' : r mod 2 ^ 64 <> 0) by (rewrite Z.mod_small by lia; exact Hnz).
    apply (sl_run regs (Z_to_bv 64 0x81090) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x810c4 /\ mem' = mem /\
         getr R 25 = Z_to_bv 64 r /\ getr R 24 = Z_to_bv 64 r /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
         getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
         getr R 22 = getr regs 22 /\ getr R 18 = getr regs 18)
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono; [exact (a2_side_evt regs fp_regs fp_csr mem r Hr10 Hnz')|].
      intros ms' (R & -> & H25 & H24 & H2 & H3 & H4 & H8 & H9 & H26 & H22 & H18).
      exists R, (Z_to_bv 64 0x810c4), mem.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      repeat (split; [assumption|]); assumption.
    + intros R pc' mem' regs'' md' (Hpc & Hmem & H25 & H24 & H2 & H3 & H4 & H8 & H9 & H26 & H22 & H18) Hreg Hmat.
      subst pc' mem'.
      pose proof (a2_pref_move g A A regs regs'' mem md md' HP
                    ltac:(rewrite Hreg; exact H2) ltac:(rewrite Hreg; exact H3) ltac:(rewrite Hreg; exact H4)
                    ltac:(rewrite Hreg; exact H8) ltac:(rewrite Hreg; exact H9) ltac:(rewrite Hreg; exact H26) Hmat)
        as HP'.
      rewrite <- SEGS.
      apply Hbc.
      exists regs'', mem, md', A, r, A, r.
      split; [reflexivity|].
      split; [exact HP'|].
      (* the memory is unchanged on this arm, so ENT moves with the model step alone (ent_mat) *)
      split; [eapply ent_mat; [exact HENT | exact Hmat]|].
      split; [unfold rg; rewrite Hreg; exact H25|].
      split; [exact Hr32|].
      split; [unfold rg; rewrite Hreg; exact H24|].
      split; [exact Hr64|].
      split.
      { (* fr + 3136 <= A: the frame's last byte is in FS, FS ends at or below stklo, stklo <= S - SLOT_STACK < A *)
        destruct (Hfs (r + 3135) ltac:(rewrite FRAME_BYTES_val; lia)) as (b & Hb64 & Hbw & Hbr).
        destruct (lw_fs_place (APIf rc) (g_H g) mem md b HAH Hbw Hb64) as [_ Hbs _ _].
        unfold AF.SLOT_STACK in Hstklo. rewrite FRAME_BYTES_val. lia. }
      split; [right; reflexivity|].
      split; [unfold rg; rewrite Hreg, H22; exact Hp|].
      split; [unfold rg; rewrite Hreg, H18; exact Hn|].
      right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsep|]. split; [exact Hfs|]. exact Hrec.
Qed.

End A2.
