(* Segment C06 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x140dc, 0x140f4], the frame-loop latch (AF5').
   U140dc -> U137d0 (j + 1) when j <= 254 and left_(j+1) != 0; U140f8 otherwise. A2 is s2 = 1 (kept from LK's S2;
   v1.9.0 sets no a2 here); the cursor update s7 = body + len, s6 = (left - h) - len reads q64 sp+24; j in s1. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Ltac c06_cond := unfold_cond; fold_lit_ux; rewrite ?MState.unsigned_lit by lia; solve_cond_rec.
Ltac c06_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (symmetry; c06_cond); cbv iota
  end.

Lemma c06_swrap : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

(* j >= 255: `bltu a0,s1` (a0 = 254) exits to 0x140f8. *)
Lemma c06_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : Z),
    s1 = Z_to_bv 64 j -> 255 <= j < 2 ^ 63 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 254) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x140f8) fc None m
                     (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140dc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m j -> Hj.
  step. step. c06_if true.
  apply evt_done. reflexivity.
Qed.

(* j <= 254: the cursor update and j++, then `bnez s6` to 0x137d0, else 0x140f8. *)
Lemma c06_r :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv a b c j : Z),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    s5 = Z_to_bv 64 b -> s6 = Z_to_bv 64 c -> s1 = Z_to_bv 64 j ->
    0 <= j <= 254 -> 0 <= c <= a -> a < 2 ^ 64 -> 0 <= b -> b + c < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 24)) 8 = Some (le8 (Z_to_bv 64 a)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (j + 1)) (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 (Z_to_bv 64 (a - c)) (Z_to_bv 64 (b + c)) s8 s9 s10 s11
                              t3 t4 t5 t6) F
                     (if negb (bv_eqb (Z_to_bv 64 (a - c)) (Z_to_bv 64 0)) then Z_to_bv 64 0x137d0
                      else Z_to_bv 64 0x140f8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140dc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv a b c j -> Hs0 Hs1 -> -> -> Hj Hc Ha Hb Hbc HL.
  step. step. c06_if false.
  step. step. step. step.
  rewrite ?MState.unsigned_lit by lia. rewrite c06_swrap by lia.
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

Lemma seg_C06 : forall j : nat, Hat B APIf ra (Inv_U137d0_at B APIf ra empty) (S j) ->
  Hcut B APIf ra (Inv_U140f8 B APIf ra empty) -> Hat B APIf ra (Inv_U140dc_at B APIf ra empty) j.
Proof.
  intros j H1 H2 g c (L & A & regs & mem & md & -> & HF & HP & (HLK & HFC & HIFS)).
  pose proof HLK as (Hj & H9 & HOUR & HM7 & HOVF & HS2).
  pose proof HFC as (H24 & H21 & H22).
  pose proof (u8_t_facts (g_in g) j) as (Rc & EL & Rh & Eh & Rl & Eb & Ec & ELS).
  pose proof (u8_p_range B APIf ra empty FF g (proj1 HF)) as (Hp0 & Hpn & Hn).
  pose proof (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF) as (Hsp & H16 & HSK & HS47 & HMI).
  unfold g_n in *. unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (K80 : forall regs', YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
      YK11.getr regs' 4 = YK11.getr regs 4 -> (S j = 256%nat \/ t_left (g_in g) (S j) = 0) ->
      SR (ms_segs B) (mkCfg (YK11.mkst regs' (Z_to_bv 64 0x140f8) mem (YK11.seg_rom (ms_segs B))) md)
        (Post B APIf ra g)).
  { intros regs' E2 E3 E4 Hx. apply H2. apply (u8_cut_close B APIf ra empty _ _ _ _ L A).
    - exact (u8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF E2 E3 E4).
    - exact HP.
    - destruct HIFS as (HID & _). unfold IDj in *. rewrite (u8_fJ_ID (g_in g) j Hj Hx). exact HID. }
  destruct (Nat.le_gt_cases 255 j) as [Hx|Hx].
  - eapply (u8_run_to B APIf ra empty FF);
      [exact HF | unfold rmk; apply c06_x with (j := Z.of_nat j); [exact H9 | lia] |].
    intros regs' HG. apply K80; [rewrite HG; reflexivity .. | left; lia].
  - eapply (u8_run_to B APIf ra empty FF);
      [exact HF | unfold rmk; eapply c06_r with (j := Z.of_nat j) (spv := g_S g - 1936)
                    (a := t_left (g_in g) j - t_h (g_in g) j) (b := g_p g + t_body (g_in g) j)
                    (c := t_len (g_in g) j);
                  [exact Hsp | lia | lia | exact H21 | exact H22 | exact H9 | lia | lia | lia | lia | lia |] |].
    { replace (g_S g - 1936 + 24) with (spk g 24) by (unfold spk, fsp, SLOT_FRAME; lia).
      exact (u8_ld8 mem _ _ H24). }
    intros regs' HG.
    destruct (Z.eq_dec (t_left (g_in g) (S j)) 0) as [E0|E0].
    + replace (bv_eqb (Z_to_bv 64 (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j)) (Z_to_bv 64 0))
        with true by (symmetry; unfold bv_eqb; rewrite !MState.unsigned_lit by lia; apply Z.eqb_eq; lia).
      cbn [negb]. apply K80; [rewrite HG; reflexivity .. | right; exact E0].
    + replace (bv_eqb (Z_to_bv 64 (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j)) (Z_to_bv 64 0))
        with false by (symmetry; unfold bv_eqb; rewrite !MState.unsigned_lit by lia; apply Z.eqb_neq; lia).
      cbn [negb]. apply (H1 g). apply (u8_cut_close B APIf ra empty _ _ _ _ L A).
      * apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HF | rewrite HG; reflexivity ..].
      * exact HP.
      * unfold LI, LK, CUR, A2, S2, rg, g_n.
        split; [split; [lia|]|].
        { split; [rewrite HG; transitivity (Z_to_bv 64 (Z.of_nat j + 1)); [reflexivity | f_equal; lia]|].
          split; [exact HOUR|]. split; [exact HM7|]. split; [unfold OVF, rg in *; rewrite HG; exact HOVF|].
          rewrite HG. exact HS2. }
        split; [split; [unfold t_c in *; lia|]; split|].
        -- rewrite HG. transitivity (Z_to_bv 64 (g_p g + t_body (g_in g) j + t_len (g_in g) j));
             [reflexivity | f_equal; unfold t_c in *; lia].
        -- rewrite HG. transitivity (Z_to_bv 64 (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j));
             [reflexivity | f_equal; unfold t_c in *; lia].
        -- split; [lia|]. split; [exact HIFS|]. rewrite HG. exact HS2.
Qed.

End C06.
