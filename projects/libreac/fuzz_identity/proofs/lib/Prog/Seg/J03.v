From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP URzKP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sj.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import strcmp_c.

Lemma kJ03a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e I O i o : Z),
  x23 = Z_to_bv 64 0x1dec0 -> x19 = Z_to_bv 64 e -> x9 = Z_to_bv 64 i -> x18 = Z_to_bv 64 o ->
  0 <= e -> e + 24 < 2 ^ 64 -> -2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 -> 0 <= i < 2 ^ 31 -> 0 <= o < 2 ^ 31 ->
  ov_read_bytes rsegs m (wa (e + 16)) 4 = Some (le4 (Z_to_bv 64 I)) ->
  ov_read_bytes rsegs m (wa (e + 20)) 4 = Some (le4 (Z_to_bv 64 O)) ->
  Exec.evt rsegs
    (fun ms' => exists y10, ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x10 (Z_to_bv 64 (if (I =? i) && (O =? o) then 0 else 1)) y10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x13c78) fc None m (seg_rom rsegs))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c28) fc None m (seg_rom rsegs)).
Proof.
  intros. subst x23 x19 x9 x18.
  step. step. if_false. step. rewrite sj_sx32 by lia. step. rewrite sj_bv_eqb by lia.
  destruct (Z.eqb_spec I i) as [EI|EI]; cbn [negb andb].
  - step. rewrite sj_sx32 by lia. step. rewrite sj_bv_eqb by lia.
    destruct (Z.eqb_spec O o) as [EO|EO]; cbn [negb].
    + step. step. apply evt_done. eexists. reflexivity.
    + step. apply evt_done. eexists. reflexivity.
  - step. apply evt_done. eexists. reflexivity.
Qed.

Lemma kJ03c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e : Z),
  x19 = Z_to_bv 64 e -> 0 <= e -> e + 24 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (e + 8)) 8 = Some (le8 (Z_to_bv 64 0)) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c94) fc None m (seg_rom rsegs))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c78) fc None m (seg_rom rsegs)).
Proof.
  intros. subst x19. step. step. if_true. apply evt_done. reflexivity.
Qed.

Lemma kJ03b : strcmp_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (e P dp : Z) (sP sd : list byte),
  x19 = Z_to_bv 64 e -> x22 = Z_to_bv 64 dp -> 0 <= e -> e + 24 < 2 ^ 64 -> 0 < P < 2 ^ 64 -> 0 <= dp < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (e + 8)) 8 = Some (le8 (Z_to_bv 64 P)) ->
  bytes_at rsegs m P (sP ++ [z8]) -> ~ In z8 sP -> bytes_at rsegs m dp (sd ++ [z8]) -> ~ In z8 sd ->
  Exec.evt rsegs
    (fun ms' => exists r y11 y12 y13, ms' = MS (mkR (Z_to_bv 64 0x13c88) x2 x3 x4 x5 x6 x7 x8 x9 r y11 y12 y13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x13c88) fc None m (seg_rom rsegs) /\ (r = Z_to_bv 64 0 <-> sP = sd))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c78) fc None m (seg_rom rsegs)).
Proof.
  intros SC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m e P dp sP sd E19 E22 He1 He2 HP1 Hd RD BP NP BD ND. subst x19 x22.
  step. step.
  replace (bv_eqb (Z_to_bv 64 P) (Z_to_bv 64 0)) with false
    by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  cbv beta iota. step. step.
  eapply Exec.evt_cut.
  - eapply SC with (sx := sP) (sy := sd).
    + rewrite unsigned_lit by lia. exact BP.
    + exact NP.
    + rewrite unsigned_lit by lia. exact BD.
    + exact ND.
  - intros ms' (r & y11 & y12 & y13 & -> & Hr). apply evt_done. exists r, y11, y12, y13. split; [|exact Hr].
    rewrite (sj_ret_pc_ra 0x13c88) by reflexivity. reflexivity.
Qed.

Ltac v3 HG E := rewrite HG; lazymatch type of E with getr ?R1 ?r = _ => transitivity (getr R1 r); [reflexivity | exact E] end.

Section J03.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis STRCMP : strcmp_contract.

Lemma seg_J03 : Hcut B APIf ra (Inv_K13c60 B APIf ra empty) -> Hcut B APIf ra (Inv_K13c94 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c88 B APIf ra empty) -> Hcut B APIf ra (Inv_K13c28 B APIf ra empty).
Proof.
  intros H60 H94 H88 g c (nm & tk & dp & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (HIR & H9 & I & O & P & sP & HCE & H23 & H19 & H10).
  pose proof HCE as (HI & HO & HP0 & B8 & B16 & B20 & HS).
  pose proof (sj_cat_e_pos (g_in g)) as He. unfold CAT, CAT_ROW, CAT_N in He.
  pose proof HIR as (HID & H18 & H20 & H21 & H22 & H24 & H25 & H27 & HOUT & Hr & HN1 & HN2).
  pose proof (inb_range (g_in g) (cT (g_in g) + 1)) as Hi. pose proof (inb_range (g_in g) (cT (g_in g) + 2)) as Ho.
  change (inb (g_in g) (cT (g_in g) + 1)) with (t_in (g_in g)) in Hi.
  change (inb (g_in g) (cT (g_in g) + 2)) with (t_out (g_in g)) in Ho.
  assert (Hin : In (dp, bsz (t_cap_disp (g_in g))) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); right; right; left; reflexivity).
  destruct (sj_block_pos B APIf ra empty g _ _ L A regs mem md _ _ HF Hin) as [Hd1 Hd2].
  pose proof alloc_ceiling_lt as HAC.
  assert (Hdp : 0 <= dp < 2 ^ 64) by (unfold bsz in Hd2; lia).
  set (w := if (I =? t_in (g_in g)) && (O =? t_out (g_in g)) then 0 else 1) in *.
  eapply (run_ex B APIf ra empty FF); [exact HF | |intros y regs1 HG1].
  { apply (kJ03a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cat_e (g_in g)) I O
      (t_in (g_in g)) (t_out (g_in g))); try assumption; try lia.
    - apply sj_bytes_le4. exact B16.
    - apply sj_bytes_le4. exact B20. }
  assert (F1 : FR B APIf ra empty g (2 * NR g + 5) (NMB g nm tk dp) L A regs1 mem md)
    by (apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [exact HF | rg HG1 | rg HG1 | rg HG1]).
  assert (E19 : getr regs1 19 = Z_to_bv 64 (cat_e (g_in g))) by (rewrite HG1; exact H19).
  assert (E18 : getr regs1 18 = Z_to_bv 64 (t_out (g_in g))) by (rewrite HG1; exact H18).
  assert (E20 : getr regs1 20 = Z_to_bv 64 nm) by (rewrite HG1; exact H20).
  assert (E21 : getr regs1 21 = Z_to_bv 64 tk) by (rewrite HG1; exact H21).
  assert (E22 : getr regs1 22 = Z_to_bv 64 dp) by (rewrite HG1; exact H22).
  assert (E24 : getr regs1 24 = Z_to_bv 64 (t_cap_name (g_in g))) by (rewrite HG1; exact H24).
  assert (E25 : getr regs1 25 = Z_to_bv 64 (n_r (g_in g))) by (rewrite HG1; exact H25).
  assert (E27 : getr regs1 27 = Z_to_bv 64 (t_cap_disp (g_in g))) by (rewrite HG1; exact H27).
  assert (E8 : getr regs1 8 = Z_to_bv 64 (cat_mask (g_in g) dp I O P sP)) by (rewrite HG1; exact H10).
  assert (E9 : getr regs1 9 = Z_to_bv 64 w) by (rewrite HG1; reflexivity).
  destruct (Z.eq_dec P 0) as [EP|EP].
  - subst P. eapply (run_to B APIf ra empty FF); [exact F1 | |intros regs2 HG2].
    { apply (kJ03c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cat_e (g_in g)));
        [exact E19 | lia | lia | apply sj_bytes_le8; exact B8]. }
    apply H94. exists nm, tk, dp. apply (cut_close B APIf ra empty _ _ _ _ _ L A).
    + apply (FR_regs B APIf ra empty _ _ _ _ _ regs1); [exact F1 | rg HG2 | rg HG2 | rg HG2].
    + exact HP.
    + split.
      * split; [exact HID|].
        split; [v3 HG2 E18|]. split; [v3 HG2 E20|]. split; [v3 HG2 E21|].
        split; [v3 HG2 E22|]. split; [v3 HG2 E24|]. split; [v3 HG2 E25|].
        split; [v3 HG2 E27|]. split; [exact HOUT|]. split; [exact Hr|]. split; [exact HN1 | exact HN2].
      * left. exists I, O, 0, sP. split; [exact HCE|]. split; [v3 HG2 E8|].
        rewrite HG2. transitivity (getr regs1 9); [reflexivity|]. rewrite E9. unfold exp_mask. fold w.
        f_equal. cbn [Z.eqb]. lia.
  - destruct (kb_md B (APIf rc) L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ F1)) as [Hh Hl].
    apply (kb_run_rz B regs1 (Z_to_bv 64 0x13c78) mem md
      (fun R pc' m' => exists r y11 y12 y13, R = mkR (Z_to_bv 64 0x13c88) (getr regs1 2) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6) (getr regs1 7) (getr regs1 8) (getr regs1 9) r y11 y12 y13 (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20) (getr regs1 21) (getr regs1 22) (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27) (getr regs1 28) (getr regs1 29) (getr regs1 30) (getr regs1 31) /\ pc' = Z_to_bv 64 0x13c88 /\ m' = mem /\
         (r = Z_to_bv 64 0 <-> sP = n_EXP_DP (g_in g))) _ Hh Hl).
    + rewrite (sj_segs B APIf ra empty FF). eapply Exec.evt_mono.
      * apply (kJ03b STRCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cat_e (g_in g)) P dp sP
          (n_EXP_DP (g_in g))); try lia.
        -- exact E19.
        -- exact E22.
        -- apply sj_bytes_le8. exact B8.
        -- exact (proj1 (HS EP)).
        -- exact (proj2 (HS EP)).
        -- exact (proj2 (proj2 (HOUT Hr))).
        -- apply NZ_EXP_DP.
      * intros ms (r & y11 & y12 & y13 & -> & Hrr). do 3 eexists. split; [reflexivity|].
        exists r, y11, y12, y13. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact Hrr].
    + intros R pc' m' regs3 (r & y11 & y12 & y13 & -> & -> & -> & Hrr) HG3.
      apply H88. exists nm, tk, dp. apply (cut_close B APIf ra empty _ _ _ _ _ L A).
      * apply (FR_regs B APIf ra empty _ _ _ _ _ regs1); [exact F1 | rg HG3 | rg HG3 | rg HG3].
      * exact HP.
      * split.
        -- split; [exact HID|].
        split; [v3 HG3 E18|]. split; [v3 HG3 E20|]. split; [v3 HG3 E21|].
        split; [v3 HG3 E22|]. split; [v3 HG3 E24|]. split; [v3 HG3 E25|].
        split; [v3 HG3 E27|]. split; [exact HOUT|]. split; [exact Hr|]. split; [exact HN1 | exact HN2].
        -- exists I, O, P, sP. split; [exact HCE|]. split; [exact EP|]. split; [v3 HG3 E19|].
           split; [v3 HG3 E8|]. split; [v3 HG3 E9|]. rewrite HG3. exact Hrr.
Qed.

End J03.
