(* Segment W04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13d6c, 0x13d78], row_of_block's loop end.
   K13d6c, K13d70 -> K13d80 (blk = decl_i), K13d4c (i + 1 < 11), K13d7c (i + 1 = 11).
   libreac v1.9.0 (table 5a S_W04: IDENTICAL, OLD 0x13d3c .. 0x13d48): pcs only; cuts K13d3c -> K13d6c, K13d40 ->
   K13d70, K13d50 -> K13d80, K13d1c -> K13d4c, K13d4c -> K13d7c (SlotInv.v's renames), so seg_W04 is stated on the
   renamed cuts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma kW04z : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  x10 = Z_to_bv 64 0 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d80) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d6c) fc None m ro).
Proof.
  intros. subst x10. step.
  first [if_cases HC; [apply evt_done; reflexivity | exfalso; vm_compute in HC; discriminate HC]
        | apply evt_done; reflexivity].
Qed.

Lemma kW04b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  x10 <> Z_to_bv 64 0 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d70) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d6c) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro H10. step.
  if_cases HC; [exfalso; apply H10; unfold bv_eqb in HC; apply Z.eqb_eq in HC; apply bv_eq; exact HC|].
  apply evt_done. reflexivity.
Qed.

Lemma kW04m : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (s r : Z),
  x8 = Z_to_bv 64 s -> x23 = Z_to_bv 64 r ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (s + -1)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 (Z_to_bv 64 (r + 296)) x24 x25 x26 x27 x28 x29 x30 x31) F
                  (if negb (bv_eqb (Z_to_bv 64 (s + -1)) (Z_to_bv 64 0)) then Z_to_bv 64 0x13d4c else Z_to_bv 64 0x13d7c)
                  fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d70) fc None m ro).
Proof.
  intros. subst x8 x23. step. step. step. apply evt_done. reflexivity.
Qed.

Section W04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_W04 : forall j i : nat,
  Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j (S i) ->
  Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j ->
  Hat2 B APIf ra (Inv_K13d6c_at B APIf ra empty) j i /\ Hat2 B APIf ra (Inv_K13d70_at B APIf ra empty) j i.
Proof.
  intros j i H50 H1c H4c.
  assert (H40 : Hat2 B APIf ra (Inv_K13d70_at B APIf ra empty) j i).
  { intros g c (phi & HC).
    eapply (b8_cut_open B APIf ra empty); [exact HC|].
    intros L A regs mem md HF HP (((HC7 & Hsel) & Hi & H23 & H8 & Hprev) & Hne).
    eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; eapply kW04m; [exact H8 | exact H23] |].
    intros regs' HG. rewrite (b8_eqb_lit _ 0) by lia.
    assert (E8 : getr regs' 8 = Z_to_bv 64 (11 - Z.of_nat i + -1)) by b8rg HG.
    assert (E23 : getr regs' 23 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i + 296)) by b8rg HG.
    assert (HC7' : CC7 g j phi regs' mem) by (apply (b8_CC7_regs _ _ _ regs); [exact HC7 | b8rg HG ..]).
    assert (HFR' : FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs' mem md)
      by (apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG).
    destruct (Nat.eq_dec i 10) as [E10|N10].
    - replace (11 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      apply H4c. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A); [exact HFR' | exact HP |].
      split; [exact HC7'|]. unfold t_want_m. rewrite Hsel. apply b8_row_none.
      intros i' Hi'. destruct (Nat.eq_dec i' i) as [->|N]; [exact Hne | apply Hprev; lia].
    - replace (11 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      apply H1c. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A); [exact HFR' | exact HP |].
      split; [split; [exact HC7' | exact Hsel]|]. split; [lia|].
      split; [unfold rg; rewrite E23; f_equal; unfold CAT_ROW; lia|].
      split; [unfold rg; rewrite E8; f_equal; lia|].
      intros i' Hi'. destruct (Nat.eq_dec i' i) as [->|N]; [exact Hne | apply Hprev; lia]. }
  split; [|exact H40].
  intros g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (HWB & Hdecl & Hiff).
  pose proof HWB as ((HC7 & Hsel) & Hi & H23 & H8 & Hprev).
  destruct (decide (t_blk (g_in g) j = decl_i (Z.of_nat i))) as [E|N].
  - eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kW04z; apply Hiff; exact E |].
    intros regs' HG. apply H50. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
    + apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
    + exact HP.
    + split; [apply (b8_CC7_regs _ _ _ regs); [exact HC7 | b8rg HG ..]|].
      unfold t_want_m. rewrite Hsel. rewrite (b8_row_hit (t_blk (g_in g) j) i) by (lia || (symmetry; exact E) || exact Hprev).
      unfold rg. rewrite HG. exact H23.
  - eapply (b8_run_to B APIf ra empty FF);
      [exact HF | unfold rmk; apply kW04b; intros E0; apply N; apply Hiff; exact E0 |].
    intros regs' HG. apply H40. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
    + apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
    + exact HP.
    + split; [|exact N]. split; [split; [apply (b8_CC7_regs _ _ _ regs); [exact HC7 | b8rg HG ..] | exact Hsel]|].
      split; [exact Hi|]. split; [unfold rg; rewrite HG; exact H23|]. split; [unfold rg; rewrite HG; exact H8|].
      exact Hprev.
Qed.

End W04.
