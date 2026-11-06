(* Segment W04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x140a4, 0x140bc], row_of_block's result test and
   latch. U140a4 -> U140c4 (blk = decl_i), U140a4 / U140b0 -> U14064 (i + 1 < 11) or U140c0 (i = 10). T72 (0x140a8)
   is not reached: 0x140a4 `bnez s4` is taken, s4 = T' + 296 i <> 0 (CATU). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Ltac w04_cond := unfold_cond; fold_lit_ux; rewrite ?MState.unsigned_lit by lia; solve_cond_rec.
Ltac w04_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (symmetry; w04_cond); cbv iota
  end.
Ltac w04_by b H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

(* blk = decl_i: 0x140a4 `bnez s4` taken, 0x140ac `beqz a0` taken. *)
Lemma w04_hit :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
    s4 = Z_to_bv 64 r -> 0 < r < 2 ^ 64 -> bv_eqb a0 (Z_to_bv 64 0) = true ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) F (Z_to_bv 64 0x140c4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r -> Hr Ha0.
  step. w04_if true.
  step. w04_by true Ha0.
  apply evt_done. reflexivity.
Qed.

(* blk <> decl_i: 0x140a4 `bnez s4` taken, 0x140ac `beqz a0` not taken. *)
Lemma w04_miss :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
    s4 = Z_to_bv 64 r -> 0 < r < 2 ^ 64 -> bv_eqb a0 (Z_to_bv 64 0) = false ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) F (Z_to_bv 64 0x140b0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r -> Hr Ha0.
  step. w04_if true.
  step. w04_by false Ha0.
  apply evt_done. reflexivity.
Qed.

(* 0x140b0: count reload, i++ (s3), row += 296 (s9), `bltu s3,a0`: to 0x14064 when i + 1 < 11, else to 0x140c0. *)
Lemma w04_latch :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv i r : Z),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    s3 = Z_to_bv 64 i -> 0 <= i <= 10 -> s9 = Z_to_bv 64 r -> 0 <= r -> r + 296 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 1824)) 8 = Some (le8 (Z_to_bv 64 11)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7
                              s2 (Z_to_bv 64 (i + 1)) s4 s5 s6 s7 s8 (Z_to_bv 64 (r + 296)) s10 s11 t3 t4 t5 t6) F
                     (Z_to_bv 64 (if i + 1 <? 11 then 0x14064 else 0x140c0)) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv i r -> Hs0 Hs1 -> Hi -> Hr0 Hr1 HL.
  step. step. step.
  rewrite ?MState.unsigned_lit by lia.
  step.
  destruct (Z.ltb_spec (i + 1) 11) as [Hlt|Hge].
  - w04_if true. apply evt_done. reflexivity.
  - w04_if false. apply evt_done. reflexivity.
Qed.

Section W04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_W04 : forall j i : nat,
  Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j -> Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j (S i) ->
  Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j ->
  Hat2 B APIf ra (Inv_U140a4_at B APIf ra empty) j i /\ Hat2 B APIf ra (Inv_U140b0_at B APIf ra empty) j i.
Proof.
  intros j i Hd0 H70 Hcc.
  (* From 0x140b0 (blk <> decl_i): the latch. *)
  assert (Kbc : forall g phi L A regs mem md,
      FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs mem md ->
      Permutation (blocks L A) (hb1 phi (t_len (g_in g) j) ++ blocks (g_L g) (g_A g)) ->
      WB g j i phi regs mem -> t_blk (g_in g) j <> decl_i (Z.of_nat i) ->
      SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 0x140b0) mem (YK11.seg_rom (ms_segs B))) md)
        (Post B APIf ra g)).
  { intros g phi L A regs mem md HFR HP (HRS & Hi & H26 & H19 & H25 & Hq & Hne) Hn.
    pose proof (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    eapply (u8_run_to B APIf ra empty FF g _ L A regs mem md);
      [exact HFR | unfold rmk; eapply w04_latch with (spv := g_S g - 1936) (i := Z.of_nat i)
                     (r := CAT + CAT_ROW * Z.of_nat i);
                   [exact Hsp | lia | lia | exact H19 | lia | exact H25 | unfold CAT, CAT_ROW; lia
                   | unfold CAT, CAT_ROW; lia |] |].
    { replace (g_S g - 1936 + 1824) with (spk g 1824) by (unfold spk, fsp, SLOT_FRAME; lia).
      exact (u8_ld8 mem _ _ Hq). }
    intros regs' HG.
    assert (HF' : FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs' mem md)
      by (apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HFR | rewrite HG; reflexivity ..]).
    destruct HRS as (HC7 & Hsel).
    assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
    pose proof (u8_CC7_keep g j phi regs regs' mem mem [] HC7 HK (munch_refl [] mem) I I I) as HC7'.
    destruct (Z.ltb_spec (Z.of_nat i + 1) 11) as [Hlt|Hge].
    - apply (H70 g). exists phi. apply (u8_cut_close B APIf ra empty _ _ _ _ L A); [exact HF' | exact HP|].
      split; [split; [exact HC7' | exact Hsel]|].
      split; [lia|].
      split; [unfold rg; rewrite HG; exact H26|].
      split; [unfold rg; rewrite HG; transitivity (Z_to_bv 64 (Z.of_nat i + 1)); [reflexivity | f_equal; lia]|].
      split; [unfold rg; rewrite HG; transitivity (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i + 296));
              [reflexivity | f_equal; unfold CAT_ROW; lia]|].
      split; [exact Hq|].
      intros i' Hi'. destruct (Nat.eq_dec i' i) as [->|Hne']; [exact Hn | apply Hne; lia].
    - apply (Hcc g). exists phi. apply (u8_cut_close B APIf ra empty _ _ _ _ L A); [exact HF' | exact HP|].
      split; [exact HC7'|].
      unfold t_want_m. rewrite Hsel. cbv iota. apply u8_row_none.
      intros i' Hi'. destruct (Nat.eq_dec i' i) as [->|Hne']; [exact Hn | apply Hne; lia]. }
  split.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HWB & H20 & HD & Ha0)).
    pose proof HWB as (HRS & Hi & H26 & H19 & H25 & Hq & Hne).
    destruct (bv_eqb (getr regs 10) (Z_to_bv 64 0)) eqn:E0.
    + eapply (u8_run_to B APIf ra empty FF g _ L A regs mem md);
        [exact HFR | unfold rmk; eapply w04_hit with (r := CAT + CAT_ROW * Z.of_nat i);
                     [exact H20 | unfold CAT, CAT_ROW; lia | exact E0] |].
      intros regs' HG.
      assert (Hb : t_blk (g_in g) j = decl_i (Z.of_nat i)).
      { apply Ha0. unfold bv_eqb in E0. apply Z.eqb_eq in E0. apply bv_eq. exact E0. }
      apply (Hd0 g). exists phi. apply (u8_cut_close B APIf ra empty _ _ _ _ L A).
      * apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HFR | rewrite HG; reflexivity ..].
      * exact HP.
      * destruct HRS as (HC7 & Hsel).
        assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
        split; [exact (u8_CC7_keep g j phi regs regs' mem mem [] HC7 HK (munch_refl [] mem) I I I)|].
        unfold t_want_m. rewrite Hsel. rewrite (u8_row_hit _ i ltac:(lia) (eq_sym Hb) Hne).
        unfold rg. rewrite HG. exact H25.
    + eapply (u8_run_to B APIf ra empty FF g _ L A regs mem md);
        [exact HFR | unfold rmk; eapply w04_miss with (r := CAT + CAT_ROW * Z.of_nat i);
                     [exact H20 | unfold CAT, CAT_ROW; lia | exact E0] |].
      intros regs' HG.
      assert (HKg : forall r, YK11.getr regs' r = YK11.getr regs r) by (intros r; rewrite HG; apply kb_rmk_getr).
      apply (Kbc g phi L A regs' mem md).
      * apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HFR | apply HKg ..].
      * exact HP.
      * destruct HRS as (HC7 & Hsel).
        assert (HK : CK regs regs') by (repeat split; apply HKg).
        split; [split; [exact (u8_CC7_keep g j phi regs regs' mem mem [] HC7 HK (munch_refl [] mem) I I I)
                       | exact Hsel]|].
        split; [exact Hi|].
        split; [exact (u8_rg _ _ _ _ (HKg _) H26)|].
        split; [exact (u8_rg _ _ _ _ (HKg _) H19)|].
        split; [exact (u8_rg _ _ _ _ (HKg _) H25)|].
        split; [exact Hq | exact Hne].
      * intros Hb. apply Ha0 in Hb. change (YK11.getr regs 10) with (PropExec.getr regs 10) in Hb.
        rewrite Hb in E0. rewrite bv_eqb_refl in E0. discriminate.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HWB & Hn)).
    exact (Kbc g phi L A regs mem md HFR HP HWB Hn).
Qed.

End W04.
