(* Segment A01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x131f8, 0x13248], ENTRY -> K1324c (t = 0);
   the exit to K13dd0 (n >= 2^26) is excluded by GV (S1.3). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. S_A01 is IDENTICAL-RENUMBER (plain segment table
   v190-segment-table-plain.md (a working note, not in this delivery)): the same 21 instructions; the frame 1920 -> 1936
   (0x131f8 `addi sp,sp,-1936`), the saved registers at sp+1832 .. sp+1928 = S - 104 .. S - 8 (were sp+1816 ..
   sp+1912), `our` at sp+76 (0x13240 `addi a3,sp,76`; was sp+60); the excluded exit 0x13234 `bnez a2` now targets
   0x13dd0 (cut K13d9c renamed K13dd0). Statements: seg_A01 names K13dd0 for K13d9c (SlotInv.v's rename). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

Lemma a01_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Lemma a01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 1936 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a1 < 2 ^ 26 ->
    evt rsegs
      (fun ms' => exists (a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1936)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3'
                       (Z_to_bv 64 7) (Z_to_bv 64 6) a6 a7 s2 s3 s4 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1324c) fc None m' (seg_rom rsegs) /\
         bv_unsigned a3' = bv_unsigned sp - 1936 + 76 /\
         munch [(bv_unsigned sp - 1936, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned sp - 104)
           (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++
            le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x131f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO MI Ha1.
  pose proof (munch_refl [(bv_unsigned sp - 1936, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 1936%nat ST.
  do 16 step.
  if_false_by (a01_cond (bv_unsigned a1) ltac:(lia)).
  do 5 step.
  pose proof (sl_bytes_cells_tail _ _ _ _ _ FR) as SB.
  cbn [Cells.cells_bytes] in SB. rewrite app_nil_r in SB.
  replace (bv_unsigned sp + -1936 + Z.of_nat 1832) with (bv_unsigned sp - 104) in SB by lia.
  release_frame FR ST (bv_unsigned sp).
  finish.
  all: rewrite ?MState.unsigned_lit by lia; lia.
Qed.

Section A01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_A01 : Hat B APIf ra (Inv_K1324c_at B APIf ra empty) 0 -> Hcut B APIf ra (Inv_K13dd0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  intros H1 _ g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & _ & HS16 & HSK & HS47 & _ & HGsp & HGtp).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_K, SLOT_STACK in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = g_n g).
  { rewrite Hn. apply MState.unsigned_lit. unfold g_n, nlen in *. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY.
    apply a01_evt with (lo := g_S g - 65536).
    + rewrite Esp2. apply sl_stk_norm; [exact HMI | unfold SL_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + rewrite Esp2. lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + rewrite En. lia.
  - intros ms (? & ? & ? & -> & _). do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (a2' & a3' & m'' & HE & Ha3 & MU & WM & MI' & ST' & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB, Ha3.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 1936, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel') SB) as SB'.
    rewrite <- SEGS. apply H1.
    unfold Inv_K1324c_at, CUTST.
    exists (g_L g), (g_A g), regs', m', (g_md g).
    split; [reflexivity|].
    split.
    + apply (sl_fr_of B APIf ra empty FF) with (mem0 := g_mem g).
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
      * apply (sl_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 1936) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      * exact WM'.
      * exact Hro'.
      * rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -1936)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * unfold saved_bytes. rewrite <- Hra. exact SB'.
    + split; [cbn [app]; apply Permutation_refl|].
      unfold rg. rewrite !(sl_getr_eqv _ _ _ Hx).
      pose proof (bv_unsigned_in_range 64 a3') as Ra3. unfold bv_modulus in Ra3.
      change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra3.
      split; [lia|]. split; [unfold g_n, nlen; lia|].
      split; [reflexivity|]. split; [rewrite Z.sub_0_r; exact Hn|]. split; [rewrite Z.add_0_r; exact Hp|].
      split; [transitivity a3'; [reflexivity|]; apply bv_eq; rewrite Ha3;
              rewrite MState.unsigned_lit; unfold spk, fsp, SLOT_FRAME; lia|].
      split; [reflexivity|]. split; [reflexivity|].
      cbn [firstn Z.to_nat]. apply sl_bytes_nil. unfold spk, fsp, SLOT_FRAME. lia.
Qed.

End A01.
