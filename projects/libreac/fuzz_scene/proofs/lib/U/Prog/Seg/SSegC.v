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
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv STac SGlue SCut.
Import ListNotations.
Open Scope Z_scope.

(* Segment C: 0x15294 `ld s8,16(sp)` reloads nb after the transfer path. *)

Section KA.
Context {fx : YK11.FPState}.

Lemma C_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp0 : Z) (v16 : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 24 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 16)) 8 = Some (le8 v16) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 v16 x25 x26 x27 x28 x29 x30 x31 /\
       pc' = Z_to_bv 64 0x15298 /\ m' = m)
    (MS (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        fp_regs (Z_to_bv 64 0x15294) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp0 v16 E2 H0 H1 R16.
  subst x2.
  step.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

End KA.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_C : Hcut B APIf ra (Inv_K15298 B APIf ra empty) -> Hcut B APIf ra (Inv_K15294 B APIf ra empty).
Proof.
  intros HX g c (body & HC).
  eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (H9 & H8 & HN & Q16 & HB & HM).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & HIH & H8k & HfS & _ & HS47 & HSK & Hsp).
  unfold IMG_HI in HIH.
  pose proof alloc_ceiling_value as HAC.
  eapply (ss_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x15294) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of. apply C_x with (sp0 := fsp g).
    - exact Hsp.
    - lia.
    - lia.
    - apply ss_rd_q64. exact Q16. }
  intros R pc' m' regs1 (-> & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9] regs regs1) by ss_kp XR regs.
  assert (G24 : getr regs1 24 = Z_to_bv 64 (nbG g)).
  { rewrite (ss_getr_x _ _ 24 XR) by reflexivity. unfold nbG. rewrite HN. reflexivity. }
  assert (HF1 : FR B APIf ra empty g 2 [(body, nbG g)] L A regs1 mem md).
  { apply (ss_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply ss_wmono_eq. intros w. reflexivity. }
  apply HX. exists body, 2. split; [right; reflexivity|].
  exists L, A, regs1, mem, md. split; [reflexivity|]. split; [exact HF1|]. split; [exact HP|].
  split; [transitivity (getr regs 9); [exact (KP1 9 ltac:(ss_in)) | exact H9]|].
  split; [exact G24|]. split; [transitivity (getr regs 8); [exact (KP1 8 ltac:(ss_in)) | exact H8]|].
  split; [unfold nbG; rewrite HN; exact HB | exact HM].
Qed.

End C.
