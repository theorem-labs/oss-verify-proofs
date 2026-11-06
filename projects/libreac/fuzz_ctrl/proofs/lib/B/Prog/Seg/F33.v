(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and addresses changed; 105 of its 141 lines of code are new or changed and 360 lines of the source are left out. *)
(* Segment F33 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): 0x82bcc-0x82bf0, the set-up
   and the head of row_of_block (row F33 (plan-asan-ubsan section 2 (a working note, not in this delivery)); ubsan twin W01; v1.8 0x82b68-0x82b8c, a Theorem Labs lane's
   row S_F33 (v190-segment-table (a working note, not in this delivery)): IDENTICAL). Image-B port of the image-A lemma seg_F33 (lib/A/Prog/Seg/F33.v,
   127a27ab2ec; image A v1.8 0x827b0-0x827bc).

     0x82bcc  beqz a0,82c84     -- NOT taken: a0 = BOX_CATALOGUE = 0x9f620, the catalogue's result (F32).
     0x82bd0  mv s5,a0          -- s5 = T, the catalogue base.
     0x82bd4  ld a0,0(s7)       -- s7 = fr + 32, the count variable (0x82bbc ld s7,160(s1)); the catalogue wrote 11
                                   there (F32), so a0 = 11.
     0x82bd8  beqz a0,82c84     -- NOT taken: a0 = 11.
     0x82bdc  li s9,0           -- s9 = i = 0, the row index.
     0x82be0  mv s7,s5          -- s7 = T, the row pointer of row 0.
     0x82be4  li a0,296         -- the row_of_block head (back edge 0x82c80 bltu s9,a0,82be4):
     0x82be8  mulh a1,s9,a0     --   a1 = the high 64 bits of i * 296 = 0;
     0x82bec  mul a0,s9,a0      --   a0 = i * 296 = 0;
     0x82bf0  srai a2,a0,0x3f   --   a2 = the sign word of a0 = 0 (F34's 0x82c04 bne a1,a2 compares a1 and a2).

   Image A's row_of_block head (v1.8 0x827c0) is the first instruction of its F34; image B's head 0x82be4 is inside
   F33, and the F34 cut 0x82bf4 follows the four head instructions. The row latch 0x82c80 (in F36) runs the same
   four head instructions to reach 0x82bf4 at row i + 1.

  Entry Inv_B82bcc_at (F32's exit); exits Inv_B82bf4_at at row i = 0 (F34's entry, W02) and Inv_B82c84_at (the
  target of both branches and of the row loop's fall-through 0x82c80; not reached here).
   No memory is written and no call is made, so FRA moves by sl_fra_move alone. No FAIL, trap or shadow-check rows.

   The cut bundles PTL (pass-through of the row loop) and RL (row-loop state) are shared with the later row-loop
   segments F34 / F35 / F36: RL g j i holds at 0x82bf4 for row i. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* lib.B.Prog's catalogue chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy;
   this file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.

(* ========================= the machine run ========================= *)

(* The start register map of sl_run, written with the stepping engine's mkR so the engine reads it. *)
Lemma f33_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (Sem.reg_get regs 1) (Sem.reg_get regs 2) (Sem.reg_get regs 3) (Sem.reg_get regs 4) (Sem.reg_get regs 5)
      (Sem.reg_get regs 6) (Sem.reg_get regs 7) (Sem.reg_get regs 8) (Sem.reg_get regs 9) (Sem.reg_get regs 10)
      (Sem.reg_get regs 11) (Sem.reg_get regs 12) (Sem.reg_get regs 13) (Sem.reg_get regs 14) (Sem.reg_get regs 15)
      (Sem.reg_get regs 16) (Sem.reg_get regs 17) (Sem.reg_get regs 18) (Sem.reg_get regs 19) (Sem.reg_get regs 20)
      (Sem.reg_get regs 21) (Sem.reg_get regs 22) (Sem.reg_get regs 23) (Sem.reg_get regs 24) (Sem.reg_get regs 25)
      (Sem.reg_get regs 26) (Sem.reg_get regs 27) (Sem.reg_get regs 28) (Sem.reg_get regs 29) (Sem.reg_get regs 30)
      (Sem.reg_get regs 31).
Proof. intros regs. reflexivity. Qed.

(* 0x82bcc -> 0x82bf4 with a0 = 0x9f620 and the 8 bytes at s7 = c holding 11: both branches to 0x82c84 fall
   through; s5 = s7 = 0x9f620, s9 = 0, a0 = a1 = a2 = 0; memory and the other registers kept. The run reads the 8
   bytes [c, c + 8) and writes no memory. *)
Lemma f33_evt : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z),
  getr regs 10 = Z_to_bv 64 0x9f620 -> getr regs 23 = Z_to_bv 64 c ->
  ov_read_bytes rsegs m (Z_to_bv 64 c) 8 = Some (ULMem.le8 (Z_to_bv 64 11)) ->
  evt rsegs (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs) /\
      getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
      getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
      getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
      getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
      getr R 10 = Z_to_bv 64 0 /\ getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\
      getr R 21 = Z_to_bv 64 0x9f620 /\ getr R 23 = Z_to_bv 64 0x9f620 /\ getr R 25 = Z_to_bv 64 0)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82bcc) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m c E10 E23 RD.
  rewrite f33_mkR_of.
  assert (E : Sem.reg_get regs 10 = Z_to_bv 64 0x9f620) by exact E10.
  assert (E' : Sem.reg_get regs 23 = Z_to_bv 64 c) by exact E23.
  rewrite E, E'.
  (* 0x82bcc beqz a0,82c20: a0 = 0x9f620, not taken *)
  step. if_false.
  (* 0x82bd0 mv s5,a0 *)
  step.
  (* 0x82bd4 ld a0,0(s7): the count 11 *)
  step.
  (* 0x82bd8 beqz a0,82c20: a0 = 11, not taken *)
  step. if_false.
  (* 0x82bdc li s9,0; 0x82be0 mv s7,s5; 0x82be4 li a0,296; 0x82be8 mulh; 0x82bec mul; 0x82bf0 srai *)
  do 6 step.
  finish.
  all: reflexivity.
Qed.

Section F33.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ===================== the cut states ===================== *)

(* The facts the row loop carries unchanged from 0x82bcc to its exits are SlotInv's PTL (adopted from this file),
   and the row-loop state is SlotInv's RL: image A's bundles with the image-B registers and spills. Phi in s2 (18)
   and len in s4 (20) (bundles FT / FC; image A: s7 / s2); the declaration buffer fr + 64 in the spill [A + 152]
   (0x815a0 sd a7,152(s1) with a7 = fr + 64; read 0x82c18 for declaration_of; image A: s9); the block pointer
   Phi + 18 in the spill [A + 312] (bundle FB; read 0x82c2c for the bcmp; image A: s6); the count pointer fr + 32
   in the spill [A + 160] (0x815a4 sd a6,160(s1) with a6 = fr + 32; read 0x82bbc and by the row latch 0x82c70;
   image A: [A + 40]) and the count 11 at fr + 32, which image B's row latch reads again on every row (0x82c74 ld
   a0,0(a0), 0x82c80 bltu s9,a0; image A counted down in s8). Image A's FakeStack bound, its SLOT_STACK
   frame-placement disjunction and its spill-base bound are not there: fra_frame derives all three from FRA (the
   placement for every window up to FN_STACK); image A's AG is an FRA conjunct. Push 5c drops three more: mem_inv (a
   callee that needs it takes it from MemNorm.evt_normalize and ro_agree), AC.GT <= fr with the frame's app memory
   (fra_app), and aspZ <= APPMEM_END (FRA: sp <= A, A + 448 <= S < APPMEM_END).
   RL g j i holds at 0x82bf4 for row i: s9 = i, s7 = the row pointer T + 296 i, s5 = T, the head's overflow-check
   operands a0 = 296 i, a1 = 0 (mulh) and a2 = 0 (srai 63), and the rows before i did not match the block (ubsan
   WB). Image A held the row pointer in s4 and the rows left 11 - i in s8. *)

(* The cuts are SlotInv's: entry Inv_B82bcc_at (image A's v1.8 0x827b0 cut with the image-B registers and spills:
   a0 = the catalogue result CAT, s7 = fr + 32 and the count 11 there, Phi = s2, len = s4, [A + 152] = fr + 64,
   [A + 160] = fr + 32, [A + 312] = Phi + 18; FTK (the spills tfill [A + 184] and k [A + 272], s6 = 1, s8 = k, s9 =
   sum_ok), FTURN and IFS (S j) of the turn), exit Inv_B82bf4_at at row 0 (RL; s6 = 1, s8 = k and the spill
   [A + 272] = k; FTURN, IFS (S j)) and exit Inv_B82c84_at (not reached here). The run writes no memory and keeps
   s1, s6, s8 and s11, so every pass-through bundle moves by its register-9 / register-27 transporter alone.
   The exit's [A + 248] conjunct is `True` on the bundle d2c4b19fac8 (v1.9.0 reads [A + 248] only at 0x81700 and
   0x8246c, before the row loop; 0x82bdc `li s9,0` reuses s9 as the row counter). *)

(* ===================== the segment lemma ===================== *)

Lemma seg_F33 : forall j : nat, Hat2 B APIf ra (Inv_B82bf4_at B APIf ra) j 0%nat ->
  Hat B APIf ra (Inv_B82c84_at B APIf ra) j -> Hat B APIf ra (Inv_B82bcc_at B APIf ra) j.
Proof.
  intros j H90 _ g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & HFTK & Hsel &
    H10 & H23 & Hcnt & H18 & H20 & H152 & Hphi & Hplen & H160 & Hfstk & H312 & HTURN & HIFS).
  destruct HFTK as (_ & H22 & H24 & H272 & _).
  subst c. rewrite SEGS.
  assert (Hhalt : m_halted md = None) by (destruct HFRA as (A & sp & s5 & HF); tauto).
  assert (RDc : ov_read_bytes rsegs mem (Z_to_bv 64 (fr + 32)) 8 = Some (ULMem.le8 (Z_to_bv 64 11))).
  { pose proof (ULMem.bytes_at_ov_read rsegs mem (fr + 32) (ULMem.le8 (Z_to_bv 64 11)) 0 8 Hcnt
      ltac:(rewrite ULMem.length_le8; lia)) as HH.
    change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite ULMem.length_le8; lia). exact HH. }
  assert (H10' : getr regs 10 = Z_to_bv 64 0x9f620) by exact H10.
  (* The run 0x82bcc -> 0x82bf4 (sl_run, the lazy bridge of Tac_slot): it reads the 8 bytes [fr + 32, fr + 40)
     and writes no memory. *)
  apply (sl_run regs (Z_to_bv 64 0x82bcc) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82bf4 /\ mem' = mem /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 22 = getr regs 22 /\
       getr R0 24 = getr regs 24 /\ getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 0 /\ getr R0 11 = Z_to_bv 64 0 /\ getr R0 12 = Z_to_bv 64 0 /\
       getr R0 21 = Z_to_bv 64 0x9f620 /\ getr R0 23 = Z_to_bv 64 0x9f620 /\ getr R0 25 = Z_to_bv 64 0)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply evt_mono; [exact (f33_evt regs fp_regs fp_csr mem (fr + 32) H10' H23 RDc)|].
    intros ms' (R0 & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E22 & E24 & E26 & E27 &
                E10 & E11 & E12 & E21 & E23 & E25).
    exists R0, (Z_to_bv 64 0x82bf4), mem.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    repeat (split; [assumption|]); assumption.
  - intros R0 pc' mem' regs' md'
      (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E22 & E24 & E26 & E27 &
       E10 & E11 & E12 & E21 & E23 & E25) Hreg Hmat.
    subst pc' mem'.
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Hsp9 : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem off v).
    { intros off v _ Hs. exact (Tac_ro.spill_reg9 regs regs' mem off v F9 Hs). }
    pose proof HLK as (_ & _ & HOURb & HFLI).
    pose proof (Tac_ro.fli_mem g fr regs mem HFLI) as (Had & Hstk & Hid & Hfg & HKNT & Hfst).
    assert (HIexit : Inv_B82bf4_at B APIf ra g j 0%nat
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82bf4) mem (seg_rom rsegs)) md')).
    { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
          rewrite ?Hreg; assumption. }
      split; [eapply ent_mat; [exact HENT | exact Hmat]|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split.
      { apply (Tac_ro.lk_keep g fr j regs regs' mem mem HLK); try assumption.
        unfold rg in *. rewrite Hreg, E27. exact (proj1 HFLI). }
      split; [unfold rg in *; rewrite Hreg, E22; exact H22|].
      split; [intros _; unfold rg in *; rewrite Hreg, E24; exact H24|].
      split; [apply Hsp9; [lia | exact H272]|].
      (* [A + 248]: `True` on the v1.9 cut (no read after 0x8246c). *)
      split; [exact I|].
      split.
      { split; [lia|].
        split; [unfold rg; rewrite Hreg, E23; first [reflexivity | f_equal; unfold CAT, CAT_ROW; lia]|].
        split; [unfold rg; rewrite Hreg, E25; reflexivity|].
        split; [unfold rg; rewrite Hreg, E21; reflexivity|].
        split; [unfold rg; rewrite Hreg, E10; first [reflexivity | f_equal; unfold CAT_ROW; lia]|].
        split; [unfold rg; rewrite Hreg, E11; reflexivity|].
        split; [unfold rg; rewrite Hreg, E12; reflexivity|].
        split; [intros i' Hi'; exfalso; lia|].
        split; [exact Hsel|].
        split; [unfold rg in *; rewrite Hreg, E18; exact H18|].
        split; [unfold rg in *; rewrite Hreg, E20; exact H20|].
        split; [apply Hsp9; [lia | exact H152]|].
        split; [apply Hsp9; [lia | exact H312]|].
        split; [exact Hphi|]. split; [exact Hplen|].
        split; [apply Hsp9; [lia | exact H160]|].
        split; [exact Hcnt|].
        exact Hfstk. }
      split; [exact (Tac_ro.turn_reg g j phi regs regs' mem F9 HTURN)|].
      exact (Tac_ro.ifs_reg g fr (S j) regs regs' mem F9 HIFS). }
    pose proof (H90 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F33.
