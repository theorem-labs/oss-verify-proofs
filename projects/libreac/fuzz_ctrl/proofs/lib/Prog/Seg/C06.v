(* Segment C06 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13d98, 0x13db0], the frame-loop latch.
   K13d98 -> K13694 (j + 1) when j <= 254 and left_(j+1) != 0; K13db4 otherwise.
   libreac v1.9.0 (table 5a S_C06: CHANGED, OLD 0x13d68 .. 0x13d7c): the latch reloads the body pointer from the
   spill (new step 0x13da0 `ld s5,32(sp)`, then `add s5,s5,s4`; v1.8 `add s5,s3,s4`) and keeps left - h in s11
   (0x13da8 `sub s11,s11,s4`, 0x13db0 `bnez s11`; v1.8 s1 / s7). kC06r is re-walked on the v1.9 instructions (its
   statement now takes sp, the [sp+32] spill and s11, and sets s5 / s11); cuts K13d68 -> K13d98, K1368c -> K13694,
   K13d80 -> K13db4 (SlotInv.v's renames), so seg_C06 is stated on the renamed cuts. *)
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

Lemma c06_swrap : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac c06_bad HC := exfalso; zify_cond HC; rewrite ?unsigned_lit in HC by lia; lia.

Lemma kC06x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (j : Z),
  x26 = Z_to_bv 64 j -> 255 <= j < 2 ^ 63 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 254) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13db4) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d98) fc None m ro).
Proof.
  intros. subst x26. step. step. if_cases HC; [apply evt_done; reflexivity | c06_bad HC].
Qed.

(* j <= 254: a = left - h (s11), b = Φ's body pointer (the spill [sp+32]), c = len (s4). *)
Lemma kC06r : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp0 a b c : Z) (j : nat),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 1936 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 32)) 8 = Some (le8 (Z_to_bv 64 b)) ->
  x27 = Z_to_bv 64 a -> x20 = Z_to_bv 64 c -> x26 = Z_to_bv 64 (Z.of_nat j) ->
  (j <= 254)%nat -> 0 <= c <= a -> a < 2 ^ 64 -> 0 <= b -> b + c < 2 ^ 64 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 254) x11 x12 x13 x14 x15 x16 x17 x18
                           x19 (Z_to_bv 64 c) (Z_to_bv 64 (b + c)) x22 x23 x24 x25
                           (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 (a - c)) x28 x29 x30 x31) F
                  (if negb (bv_eqb (Z_to_bv 64 (a - c)) (Z_to_bv 64 0)) then Z_to_bv 64 0x13694 else Z_to_bv 64 0x13db4)
                  fc None m (seg_rom rsegs))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d98) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m sp0 a b c j E2 H0 H1 R32 E27 E20 E26 Hj Hc Ha Hb Hbc.
  subst x2 x27 x20 x26. step. step. if_cases HC; [c06_bad HC|].
  step. step. step. step.
  rewrite ?unsigned_lit by lia. rewrite c06_swrap by lia.
  step.
  apply evt_done. reflexivity.
Qed.

Section C06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_C06 : forall j : nat, Hat B APIf ra (Inv_K13694_at B APIf ra empty) (S j) ->
  Hcut B APIf ra (Inv_K13db4 B APIf ra empty) -> Hat B APIf ra (Inv_K13d98_at B APIf ra empty) j.
Proof.
  intros j H1 H2 g c HC.
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (Hj & H26 & (H27 & H32 & H20) & HOUR & HM7 & HIFS).
  pose proof (b8_t_facts (g_in g) j) as (Rc & EL & Rh & Eh & Rl & Eb & Ec & ELS).
  pose proof (b8_t_facts (g_in g) (S j)) as (Rc' & EL' & _).
  pose proof (b8_p_range B APIf ra empty FF g [] L A regs mem md HF HP) as (Hp0 & Hpn & Hn).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  unfold g_n in *.
  assert (K80 : forall regs', getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
      (S j = 256%nat \/ t_left (g_in g) (S j) = 0) ->
      SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x13db4) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g)).
  { intros regs' E2 E3 E4 Hx. apply H2. apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
    - exact (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF E2 E3 E4).
    - exact HP.
    - destruct HIFS as (HID & _). unfold IDj in *. rewrite (b8_fJ_ID (g_in g) j Hj Hx). exact HID. }
  destruct (Nat.le_gt_cases 255 j) as [Hx|Hx].
  - eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kC06x with (j := Z.of_nat j); [exact H26 | lia] |].
    intros regs' HG. apply K80; [b8rg HG | b8rg HG | b8rg HG | left; lia].
  - assert (R32 : ov_read_bytes rsegs mem (wa (g_S g - 1936 + 32)) 8 =
                  Some (le8 (Z_to_bv 64 (g_p g + t_body (g_in g) j)))).
    { replace (g_S g - 1936 + 32) with (spk g 32) by (unfold spk, fsp, SLOT_FRAME; lia).
      apply b8_bytes_le8. exact H32. }
    eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; eapply kC06r with (sp0 := g_S g - 1936) (j := j);
      [exact Hsp | lia | lia | exact R32 | exact H27 | exact H20 | exact H26 | lia | lia | lia | lia | lia] |].
    intros regs' HG.
    rewrite (b8_eqb_lit _ 0) by lia.
    destruct (Z.eq_dec (t_left (g_in g) (S j)) 0) as [E0|E0].
    + replace (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. apply K80; [b8rg HG | b8rg HG | b8rg HG | right; exact E0].
    + replace (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. apply H1. apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
      * apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
      * exact HP.
      * unfold LI, CUR, g_n. split; [lia|].
        split; [unfold rg; rewrite HG; transitivity (Z_to_bv 64 (Z.of_nat j + 1)); [reflexivity | f_equal; lia]|].
        split; [split; [lia|]; split|].
        -- unfold rg; rewrite HG.
           transitivity (Z_to_bv 64 (g_p g + t_body (g_in g) j + t_len (g_in g) j)); [reflexivity | f_equal; lia].
        -- unfold rg; rewrite HG.
           transitivity (Z_to_bv 64 (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j)); [reflexivity | f_equal; lia].
        -- split; [lia|]. split; [exact HOUR|].
           split; [apply (b8_IFS_regs _ _ regs); [exact HIFS | b8rg HG] | exact HM7].
Qed.

End C06.
