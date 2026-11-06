From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import SceneRunU.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require SceneEU.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.SegCF Require Import CInv CTac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv STac SGlue SCut.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Segment E: entry 0x14ee4 runs to the first `jal malloc` (nb bytes, ra 0x15010); the malloc returns at 0x15010. *)

Lemma se_bv : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z <-. symmetry. apply MState.Z_to_bv_bv_unsigned. Qed.

Lemma se_inp_wf : forall d, cells_wf (inp_cells d).
Proof.
  intros d. unfold inp_cells. apply cells_wf_app. split.
  - induction (firstn 11 d) as [|b l IH]; cbn [map cells_wf cell_wf]; tauto.
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
Qed.

Lemma se_inp_bytes : forall d, cells_bytes (inp_cells d) = d.
Proof.
  intros d. unfold inp_cells. rewrite cells_bytes_app.
  assert (E : forall l, cells_bytes (map C1 l) = l).
  { induction l as [|b l IH]; cbn [map cells_bytes cbytes app]; [reflexivity | rewrite IH; reflexivity]. }
  rewrite E. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply firstn_skipn.
Qed.

Lemma se_inp_size : forall d, cells_size (inp_cells d) = length d.
Proof. intros d. rewrite <- (cells_bytes_length _ (se_inp_wf d)), se_inp_bytes. reflexivity. Qed.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MALLOC : malloc_contract_cf B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Lemma seg_E_cf : Hcut_cf B APIf ra (Inv_K15010 B APIf ra empty) -> Hcut_cf B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  intros HX g c HCAP (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres).
  subst c.
  pose proof (ss_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hblk & HS16 & HSK & HS47 & _ & _ & _).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_K, SLOT_STACK in *.
  assert (Esp2 : bv_unsigned (getr (g_regs g) 2) = g_S g) by (rewrite Hsp; apply MState.unsigned_lit; lia).
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* the input block: its range and writability *)
  assert (Hrange : 0 < g_p g /\ g_p g + g_n g <= alloc_ceiling).
  { destruct Hpl as [[Hn0 Hpe] | [Hnpos Hin]].
    - pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        Hemp & _).
      rewrite Hpe, Hn0, Hemp. lia.
    - destruct (ss_blk_facts B APIf ra empty FF _ _ _ _ _ _ 0 HM Hin ltac:(lia)) as (_ & H1 & H2 & _). lia. }
  assert (Hwr : forall i, 0 <= i < g_n g ->
            wview rsegs (MemNorm.normalize rsegs (g_mem g)) (wa (g_p g + i)) <> None).
  { intros i Hi. destruct Hpl as [[Hn0 _] | [Hnpos Hin]]; [lia|].
    destruct (ss_blk_facts B APIf ra empty FF _ _ _ _ _ _ i HM Hin Hi) as ((b & Hb) & H1 & H2 & _ & Himg).
    pose proof (ss_noimg_fs B APIf ra empty FF _ Himg) as Hfs.
    assert (Hro : Mem.ro_addr rsegs (wa (g_p g + i)) = false).
    { unfold Mem.ro_addr. rewrite wa_unsigned by lia. rewrite Hfs. reflexivity. }
    assert (E : MemNorm.normalize rsegs (g_mem g) (wa (g_p g + i)) = Some b).
    { unfold MemNorm.normalize. rewrite Hro. exact Hb. }
    unfold wview. rewrite E. discriminate. }
  assert (Ep : bv_unsigned (getr (g_regs g) 10) = g_p g) by (rewrite Hp; apply MState.unsigned_lit; lia).
  unfold MI in HMI. rewrite SEGS in HMI.
  assert (HBA : bytes_at rsegs (g_mem g) (g_p g) (g_in g)).
  { split; [lia|]. split; [unfold g_n in Hrange; lia|]. intros i Hi.
    pose proof (Hblk (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity. }
  assert (HRW : rw_cells rsegs (MemNorm.normalize rsegs (g_mem g)) (g_p g) (inp_cells (g_in g))).
  { unfold rw_cells, cells_at. split; [split|].
    - apply se_inp_wf.
    - rewrite se_inp_bytes. apply MemNorm.bytes_at_normalize; [exact HMI | exact HBA].
    - rewrite se_inp_size. change (Z.of_nat (length (g_in g))) with (g_n g).
      split; [lia|]. split; [lia|]. intros i Hi. apply Hwr. exact Hi. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  eapply (ss_run_cf B APIf ra empty FF (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite ss_mkR_of. unfold ENTRY. rewrite Hnn.
    pose proof (SceneEU.scene_entry_x
      (getr (g_regs g) 1) (getr (g_regs g) 2) (getr (g_regs g) 3) (getr (g_regs g) 4)
      (getr (g_regs g) 8) (getr (g_regs g) 9)
      (getr (g_regs g) 18) (getr (g_regs g) 19) (getr (g_regs g) 20) (getr (g_regs g) 21) (getr (g_regs g) 22)
      (getr (g_regs g) 23) (getr (g_regs g) 24) (getr (g_regs g) 25) (getr (g_regs g) 26) (getr (g_regs g) 27)
      fp_regs fp_csr
      (getr (g_regs g) 5) (getr (g_regs g) 6) (getr (g_regs g) 7)
      (getr (g_regs g) 12) (getr (g_regs g) 13) (getr (g_regs g) 14) (getr (g_regs g) 15) (getr (g_regs g) 16)
      (getr (g_regs g) 17)
      (getr (g_regs g) 28) (getr (g_regs g) 29) (getr (g_regs g) 30) (getr (g_regs g) 31)
      (MemNorm.normalize rsegs (g_mem g)) (g_S g - 65536) (getr (g_regs g) 10) (g_in g)) as HE.
    unfold entry_stmt in HE.
    change (lenZ (g_in g)) with (g_n g) in HE.
    rewrite Esp2, Ep in HE.
    apply HE.
    + exact HRW.
    + exact (MemNorm.mem_inv_normalize rsegs (g_mem g)).
    + apply ss_stk_norm; [exact HMI | unfold SS_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + lia.
    + exact HS16.
    + left. lia.
    + lia.
    + lia.
    + lia.
  - intros ms (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
      & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & mm & macb & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17
      & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & mm & macb & HE' & E1
      & E2 & E3 & E4 & E9 & E18 & E10 & E24 & E21 & E19 & E22 & E23 & E8 & E25 & E26 & E27 & E20 & MU & WM & MI'
      & ST' & SB & SM & Hml & _).
    injection HE'; intros; subst R pc' m0'.
    rewrite Esp2 in MU, SB, SM, E2.
    pose proof (MemNorm.mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 9072, g_S g)] (g_mem g) m')
      by exact (MemNorm.munch_rel rsegs _ (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' mm HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (MemNorm.wmono_rel rsegs (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' mm HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (MemNorm.ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - 9072 <= a < g_S g) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { apply (ss_unch _ _ _ (g_S g - 9072) (g_S g) MU').
      intros x Hx0 O. destruct (Z_le_dec (g_S g - 9072) x); destruct (Z_lt_dec x (g_S g)); try lia;
        exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]). }
    pose proof (proj2 (MemNorm.bytes_at_rel rsegs m' mm _ _ Hrel') SB) as SB'.
    pose proof (proj2 (MemNorm.bytes_at_rel rsegs m' mm _ _ Hrel') SM) as SM'.
    assert (G1 : getr regs' 1 = Z_to_bv 64 0x15010).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x1; [reflexivity | exact E1]. }
    assert (G2 : getr regs' 2 = Z_to_bv 64 (fsp g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x2; [reflexivity|].
      apply se_bv. rewrite E2. unfold fsp, SLOT_FRAME. reflexivity. }
    assert (G3 : getr regs' 3 = getr (g_regs g) 3).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x3; [reflexivity | exact E3]. }
    assert (G4 : getr regs' 4 = getr (g_regs g) 4).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x4; [reflexivity | exact E4]. }
    assert (G8 : getr regs' 8 = Z_to_bv 64 (nG g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x8; [reflexivity|]. apply se_bv. exact E8. }
    assert (G10 : getr regs' 10 = Z_to_bv 64 (nbG g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x10; [reflexivity|]. apply se_bv. exact E10. }
    assert (G24 : getr regs' 24 = Z_to_bv 64 (nbG g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x24; [reflexivity|]. rewrite E24. apply se_bv. exact E10. }
    assert (G21 : getr regs' 21 = Z_to_bv 64 (g_p g + cG g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x21; [reflexivity|]. apply se_bv. exact E21. }
    assert (G19 : getr regs' 19 = Z_to_bv 64 (stG g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x19; [reflexivity | exact E19]. }
    assert (G20 : getr regs' 20 = Z_to_bv 64 (flG g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x20; [reflexivity | exact E20]. }
    assert (G22 : getr regs' 22 = Z_to_bv 64 (g_n g - cG g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x22; [reflexivity|]. apply se_bv. exact E22. }
    assert (G23 : getr regs' 23 = Z_to_bv 64 (s7G g)).
    { rewrite (ss_getr_eqv _ _ _ Hx). transitivity x23; [reflexivity | exact E23]. }
    assert (HF1 : FR B APIf ra empty g 0 [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (ss_fr_of B APIf ra empty FF g 0 [] (g_L g) (g_A g) (g_mem g) (g_md g) regs' m').
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact Hsn.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. lia.
      - exact Hrel.
      - intros a Ha Hn. apply UN; [exact Ha | unfold SLOT_K, SLOT_STACK in Hn; lia].
      - exact WM'.
      - exact Hro'.
      - exact G2.
      - exact G3.
      - exact G4.
      - unfold saved_bytes. rewrite <- Hra. unfold saved in SB'. cbn [cells_bytes cbytes] in SB'.
        rewrite app_nil_r in SB'. exact SB'. }
    assert (HP1 : Permutation (blocks (g_L g) (g_A g)) ([] ++ blocks (g_L g) (g_A g))) by apply Permutation_refl.
    pose proof (nbG_range g) as Hnb.
    try rewrite <- SEGS. rewrite <- (ss_malloc_pc B APIf ra empty FF).
    apply (ss_malloc_step_cf B APIf ra empty FF MALLOC LIMLAW g HCAP 0 [] (g_L g) (g_A g) regs' m' (g_md g) (nbG g) _ HF1 HP1).
    + cbn [length]. lia.
    + unfold hb_bytes. cbn. lia.
    + lia.
    + rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + exact G10.
    + intros L' A' regs2 mem2 md2 res HF2 HP2 RP2 R10 Hr0 FRM2 HBM2.
      rewrite G1. apply HX; [exact HCAP|]. exists res, L', A', regs2, mem2, md2.
      split; [reflexivity|]. split; [exact HF2|]. split; [exact HP2|].
      pose proof (ss_CSeq_pres _ _ RP2) as CS.
      unfold P15010.
      split; [exact R10|].
      split; [ss_cs CS 8; exact G8|].
      split; [ss_cs CS 24; exact G24|].
      split; [ss_cs CS 21; exact G21|].
      split; [ss_cs CS 19; exact G19|].
      split; [ss_cs CS 22; exact G22|].
      split; [ss_cs CS 23; exact G23|].
      split; [ss_cs CS 20; exact G20|].
      exists macb. split; [exact Hml|].
      apply (ss_bytes_mbyte rsegs m' mem2); [|exact SM'].
      intros i Hi. rewrite <- SEGS. apply FRM2.
      rewrite Hml in Hi. unfold fsp, SLOT_FRAME. lia.
Qed.

End E.
