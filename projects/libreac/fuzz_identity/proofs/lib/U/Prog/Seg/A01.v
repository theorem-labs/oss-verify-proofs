From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_identity_init_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma a01_cond0 : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Lemma a01_evt : reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 384 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a1 < 2 ^ 26 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12f50) (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp t0' t1' t2' s0 a1
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x12f50) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 384, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned sp - 104)
           (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++
            le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12efc) fc None m (seg_rom rsegs)).
Proof.
  intros IC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO MI Ha1.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 384%nat ST.
  do 16 step.
  step.
  if_true_by (a01_cond0 (bv_unsigned a1) ltac:(lia)).
  step. step. step.
  eapply evt_cut.
  { eapply IC with (id := 0) (idb := []);
      [ first [reflexivity | apply bv_eq; reflexivity] | lia | intros C; exfalso; apply C; reflexivity | exact MI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & Hz & _).
  subst ms'. specialize (Hz eq_refl). subst m'.
  replace (ret_pc (Z_to_bv 64 77648)) with (Z_to_bv 64 77648) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (sa_bytes_cells_tail _ _ _ _ _ FR) as SB.
  cbn [Cells.cells_bytes] in SB. rewrite app_nil_r in SB.
  replace (bv_unsigned sp + -384 + Z.of_nat 280) with (bv_unsigned sp - 104) in SB by lia.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

Section A01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis INIT : reac_identity_init_contract.

Lemma seg_A01 : Hcut B APIf ra (Inv_U12f50 B APIf ra empty) -> Hcut B APIf ra (Inv_U13f4c B APIf ra empty) ->
  Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  intros H1 _ g c (Ec & HGV & Hpre & Hsn & HMI & Hrel & Hres).
  subst c.
  pose proof (sa_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & _ & HS16 & HSK & HS47 & _ & Hsp & HGtp & HPB).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_K, SLOT_STACK in *.
  assert (Esp2 : bv_unsigned (lib.Reusable.YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  assert (En : bv_unsigned (lib.Reusable.YK11.getr (g_regs g) 11) = g_n g).
  { rewrite Hn. apply MState.unsigned_lit. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sa_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sa_mkR_of. unfold ENTRY.
    apply (a01_evt INIT) with (lo := g_S g - 65536).
    + rewrite Esp2. apply sa_stk_norm; [exact HMI | unfold SA_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + rewrite Esp2. lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + rewrite En. lia.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _). do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' &
                    HE & MU & WM & MI' & ST' & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g + -384, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel') SB) as SB'.
    rewrite <- SEGS. apply H1.
    unfold Inv_U12f50, CUTST.
    exists (g_L g), (g_A g), regs', m', (g_md g).
    split; [reflexivity|].
    split.
    + apply (sa_fr_of B APIf ra empty FF) with (mem0 := g_mem g).
      * exact HGV.
      * exact HM.
      * exact HW.
      * exact HB.
      * exact HID.
      * exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      * intros a _ _ _. split; [reflexivity | tauto].
      * intros a _ _ _ _. split; [reflexivity | tauto].
      * intros a k i _ _. reflexivity.
      * intros a k Hin. exact Hin.
      * exact Herr.
      * exact Hsn.
      * exact (resb_start (g_b g) (g_A g) Hres).
      * intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. exact Ha.
      * exact Hrel.
      * apply (sa_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g + -384) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      * exact WM'.
      * exact Hro'.
      * rewrite (sa_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (lib.Reusable.YK11.getr (g_regs g) 2) + -384)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal.
      * rewrite (sa_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sa_getr_eqv _ _ _ Hx). reflexivity.
      * unfold saved_bytes. rewrite <- Hra. exact SB'.
    + split; [cbn [app]; apply Permutation_refl|].
      split; rewrite (sa_getr_eqv _ _ _ Hx); [exact Hn | exact Hp].
Qed.

End A01.
