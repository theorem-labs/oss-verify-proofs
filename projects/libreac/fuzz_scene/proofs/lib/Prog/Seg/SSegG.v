From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require SceneRun.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require Import SInv STac SGlue SCut.
Import ListNotations.
Open Scope Z_scope.

(* Segment G: the epilogue at 0x15348 restores s0-s11, ra and sp and returns 0 to ra. *)

Lemma sg_cells_of_stk : forall m lo hi a cs, Frame.stk rsegs m lo hi -> lo <= a ->
  a + Z.of_nat (Cells.cells_size cs) <= hi -> Cells.cells_wf cs -> bytes_at rsegs m a (Cells.cells_bytes cs) ->
  Step.rw_cells rsegs m a cs.
Proof.
  intros m lo hi a cs ST H1 H2 Hwf Hb.
  destruct (ss_rw_of_stk m lo hi a (Cells.cells_size cs) ST H1 H2) as (bs & _ & W).
  split; [split; assumption|]. cbn [Cells.cells_size Cells.csize] in W. rewrite Nat.add_0_r in W. exact W.
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Abbreviation segs := (ms_segs B).

Lemma seg_G : Hcut B APIf ra (Inv_K15348 B APIf ra empty).
Proof.
  intros g c (km & HC).
  eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP _.
  pose proof HF as (HGV & Hsp & Hgp & Htp & HSV & HST & _).
  destruct (sg_GV_S B empty g HGV) as [HSP HS].
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  pose proof alloc_ceiling_value as HAC.
  pose proof (proj1 (proj2 FF)) as Hra.
  assert (HK : SLOT_K = 65536) by reflexivity.
  set (spv := Z_to_bv 64 (g_S g)).
  assert (Esp : bv_unsigned spv = g_S g) by (unfold spv; apply unsigned_lit; lia).
  pose proof (SceneRun.scene_exit (Z_to_bv 64 ra) spv (getr regs 3) (getr regs 4)
    (getr (g_regs g) 8) (getr (g_regs g) 9) (getr (g_regs g) 18) (getr (g_regs g) 19) (getr (g_regs g) 20)
    (getr (g_regs g) 21) (getr (g_regs g) 22) (getr (g_regs g) 23) (getr (g_regs g) 24) (getr (g_regs g) 25)
    (getr (g_regs g) 26) (getr (g_regs g) 27) fp_regs fp_csr
    (getr regs 1) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10)
    (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
    (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
    (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) mem)
    as EX.
  assert (E0 : Z_to_bv 64 (SceneRun.S0 spv) = getr regs 2).
  { rewrite Hsp. unfold SceneRun.S0, fsp, SLOT_FRAME. rewrite Esp. f_equal; lia. }
  rewrite E0 in EX.
  apply (KindBGlue.kb_run B regs (Z_to_bv 64 0x15348) mem md
    (fun R pc' mem' => SceneRun.Qret (Z_to_bv 64 ra) spv (getr regs 3) (getr regs 4)
      (getr (g_regs g) 8) (getr (g_regs g) 9) (getr (g_regs g) 18) (getr (g_regs g) 19) (getr (g_regs g) 20)
      (getr (g_regs g) 21) (getr (g_regs g) 22) (getr (g_regs g) 23) (getr (g_regs g) 24) (getr (g_regs g) 25)
      (getr (g_regs g) 26) (getr (g_regs g) 27) fp_regs fp_csr mem (MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)))
    (Post B APIf ra g) Hh Hl).
  - rewrite (sg_segs B APIf ra empty FF). eapply Exec.evt_mono.
    + apply EX.
      * rewrite Esp. lia.
      * rewrite Esp. unfold SLOT_K in HST.
        apply (sg_cells_of_stk mem (g_S g - SLOT_STACK) (g_S g)).
        -- exact HST.
        -- unfold SLOT_STACK. lia.
        -- unfold SceneRun.saved. cbn [Cells.cells_size Cells.csize Nat.add]. lia.
        -- unfold SceneRun.saved. cbn. tauto.
        -- unfold SceneRun.saved. cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r.
           replace (g_S g + -104) with (g_S g - 104) by lia. unfold saved_bytes in HSV. exact HSV.
    + intros ms HQ. pose proof HQ as HQ'.
      destruct HQ' as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E).
      rewrite E in HQ |- *. do 3 eexists. split; [reflexivity | exact HQ].
  - intros R pc' mem' regs' HQ HG.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E).
    injection E as ER Epc Em. subst R pc' mem'.
    rewrite (ss_ret_pc_ra ra Hra). apply SR_ret.
    apply (post_FR B APIf ra empty g km L A regs regs' mem md HF HP).
    + rewrite HG. reflexivity.
    + intros r Hr. ss_cs_split r Hr; rewrite HG; try reflexivity.
      * destruct HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _).
        transitivity (Z_to_bv 64 (g_S g)); [reflexivity | symmetry; exact E2].
      * exact Hgp.
      * exact Htp.
Qed.

End G.
