From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI MemNorm.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv STac.
Import ListNotations.
Open Scope Z_scope.

(* A middle segment that writes the stack below the saved registers, the slot heap blocks hb, and rewrites the
   saved-register bytes with the same values keeps FR (ss_mid allows only the stack below the saved registers). *)

Lemma sm_mrd_hi : forall (m : word -> option byte) a, IMG_HI <= a < 2 ^ 64 -> mrd rsegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. unfold mrd. destruct (m (wa a)); [reflexivity|].
  apply seg_rom_unmapped. unfold IMG_HI in Ha. rewrite wa_unsigned by lia. apply ss_fs_none. unfold IMG_HI. lia.
Qed.

Section Mid.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma sm_saved_eq : forall g (m m' : word -> option byte) x,
  bytes_at rsegs m (g_S g - 104) (saved_bytes ra g) -> bytes_at rsegs m' (g_S g - 104) (saved_bytes ra g) ->
  IMG_HI <= g_S g - 104 -> g_S g <= 2 ^ 64 -> g_S g - 104 <= x < g_S g -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
  intros g m m' x H1 H2 Hlo Hhi Hx.
  assert (L : length (saved_bytes ra g) = 104%nat)
    by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
  destruct H1 as (_ & _ & R1). destruct H2 as (_ & _ & R2).
  assert (Hi : (Z.to_nat (x - (g_S g - 104)) < length (saved_bytes ra g))%nat) by (rewrite L; lia).
  specialize (R1 _ Hi). specialize (R2 _ Hi).
  replace (g_S g - 104 + Z.of_nat (Z.to_nat (x - (g_S g - 104)))) with x in R1, R2 by lia.
  rewrite (sm_mrd_hi m x) in R1 by lia. rewrite (sm_mrd_hi m' x) in R2 by lia.
  unfold wa in R1, R2. rewrite R1, R2. reflexivity.
Qed.

Lemma sm_mid : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg g hb y \/ g_S g - 104 <= y < g_S g)) /\
     bytes_at rsegs m' (g_S g - 104) (saved_bytes ra g) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof (ss_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (HGV & _ & _ & _ & Hsv & _ & HMI & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof alloc_ceiling_value as HAC.
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (ss_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & (W & MU & WM & HW) & HSV & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel).
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM) as WM'.
    apply (proj2 (bytes_at_rel rsegs m' m1 _ _ Hrel)) in HSV.
    apply (ss_FR_kA B APIf ra empty FF g km hb L A regs mem md regs' m' HFR HP).
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E4.
    + intros x Hx64 Hk.
      assert (Hdec : (g_S g - 104 <= x < g_S g) \/ ~ (g_S g - 104 <= x < g_S g)) by lia.
      destruct Hdec as [Hs|Hs].
      * apply (sm_saved_eq g mem m' x Hsv HSV); [unfold IMG_HI, SLOT_K, SLOT_STACK in *; lia | lia | exact Hs].
      * apply MU'. rewrite (unsigned_lit x Hx64).
        apply (ss_outside (fun y => kreg g hb y \/ g_S g - 104 <= y < g_S g) W x HW). tauto.
    + exact WM'.
Qed.

End Mid.
