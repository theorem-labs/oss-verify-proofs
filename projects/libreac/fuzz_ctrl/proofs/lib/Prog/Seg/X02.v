(* Segment X02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13dcc, 0x13e0c], P4n's check (#94) and the epilogue.
   K13dcc, K13dd0 -> RET.
   libreac v1.9.0 (table 5a S_X02: IDENTICAL-RENUMBER, OLD 0x13d98 .. 0x13dd8): pcs, the saved-register slots
   1912 .. 1816 -> 1928 .. 1832 (still S - 8 .. S - 104), the frame 1920 -> 1936 (0x13e08 `addi sp,sp,1936`);
   cuts K13d98 -> K13dcc, K13d9c -> K13dd0 (SlotInv.v's renames), so seg_X02 is stated on the renamed cuts. *)
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

Lemma kX02a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  x10 <> Z_to_bv 64 0 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13dd0) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13dcc) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro H10. step.
  if_cases HC; [exfalso; apply H10; unfold bv_eqb in HC; apply Z.eqb_eq in HC; apply bv_eq; exact HC|].
  apply evt_done. reflexivity.
Qed.

Lemma kX02 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z)
    (r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 1936 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 1928)) 8 = Some (le8 r1) ->
  ov_read_bytes rsegs m (wa (sp0 + 1920)) 8 = Some (le8 r8) ->
  ov_read_bytes rsegs m (wa (sp0 + 1912)) 8 = Some (le8 r9) ->
  ov_read_bytes rsegs m (wa (sp0 + 1904)) 8 = Some (le8 r18) ->
  ov_read_bytes rsegs m (wa (sp0 + 1896)) 8 = Some (le8 r19) ->
  ov_read_bytes rsegs m (wa (sp0 + 1888)) 8 = Some (le8 r20) ->
  ov_read_bytes rsegs m (wa (sp0 + 1880)) 8 = Some (le8 r21) ->
  ov_read_bytes rsegs m (wa (sp0 + 1872)) 8 = Some (le8 r22) ->
  ov_read_bytes rsegs m (wa (sp0 + 1864)) 8 = Some (le8 r23) ->
  ov_read_bytes rsegs m (wa (sp0 + 1856)) 8 = Some (le8 r24) ->
  ov_read_bytes rsegs m (wa (sp0 + 1848)) 8 = Some (le8 r25) ->
  ov_read_bytes rsegs m (wa (sp0 + 1840)) 8 = Some (le8 r26) ->
  ov_read_bytes rsegs m (wa (sp0 + 1832)) 8 = Some (le8 r27) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR r1 (Z_to_bv 64 (sp0 + 1936)) x3 x4 x5 x6 x7 r8 r9 (Z_to_bv 64 0) x11 x12 x13 x14 x15
                           x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31) F (ret_pc r1) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13dd0) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 E2 H0 H1
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  subst x2.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

Section X02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma b8_saved_split : forall g mem, bytes_at rsegs mem (g_S g - 104) (saved_bytes ra g) ->
  bytes_at rsegs mem (g_S g - 104) (le8 (getr (g_regs g) 27)) /\
  bytes_at rsegs mem (g_S g - 96) (le8 (getr (g_regs g) 26)) /\
  bytes_at rsegs mem (g_S g - 88) (le8 (getr (g_regs g) 25)) /\
  bytes_at rsegs mem (g_S g - 80) (le8 (getr (g_regs g) 24)) /\
  bytes_at rsegs mem (g_S g - 72) (le8 (getr (g_regs g) 23)) /\
  bytes_at rsegs mem (g_S g - 64) (le8 (getr (g_regs g) 22)) /\
  bytes_at rsegs mem (g_S g - 56) (le8 (getr (g_regs g) 21)) /\
  bytes_at rsegs mem (g_S g - 48) (le8 (getr (g_regs g) 20)) /\
  bytes_at rsegs mem (g_S g - 40) (le8 (getr (g_regs g) 19)) /\
  bytes_at rsegs mem (g_S g - 32) (le8 (getr (g_regs g) 18)) /\
  bytes_at rsegs mem (g_S g - 24) (le8 (getr (g_regs g) 9)) /\
  bytes_at rsegs mem (g_S g - 16) (le8 (getr (g_regs g) 8)) /\
  bytes_at rsegs mem (g_S g - 8) (le8 (Z_to_bv 64 ra)).
Proof.
  intros g mem H. unfold saved_bytes in H.
  repeat (apply bytes_at_app in H; destruct H as [?H H]; rewrite length_le8 in H).
  repeat match goal with |- _ /\ _ => split end;
    match goal with H : bytes_at _ _ ?a (le8 ?v) |- bytes_at _ _ ?b (le8 ?v) => replace b with a by lia; exact H end.
Qed.

Lemma seg_X02 : Hcut B APIf ra (Inv_K13dcc B APIf ra empty) /\ Hcut B APIf ra (Inv_K13dd0 B APIf ra empty).
Proof.
  assert (H9c : Hcut B APIf ra (Inv_K13dd0 B APIf ra empty)).
  { intros g c HC.
    eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP _.
    pose proof HF as (HGV & Hsp & Hgp & Htp & HSV & _).
    destruct (b8_GV_S B empty g HGV) as [HSP HS].
    pose proof alloc_ceiling_value as HAC.
    destruct (b8_saved_split g mem HSV) as (B27 & B26 & B25 & B24 & B23 & B22 & B21 & B20 & B19 & B18 & B9 & B8 & B1).
    unfold fsp, SLOT_FRAME in Hsp. unfold SLOT_K, SLOT_STACK in HS.
    eapply (b8_run_to B APIf ra empty FF); [exact HF | | intros regs' HG].
    - unfold rmk. eapply kX02 with (sp0 := g_S g - 1936).
      + exact Hsp.
      + lia.
      + lia.
      + replace (g_S g - 1936 + 1928) with (g_S g - 8) by lia. apply b8_bytes_le8. exact B1.
      + replace (g_S g - 1936 + 1920) with (g_S g - 16) by lia. apply b8_bytes_le8. exact B8.
      + replace (g_S g - 1936 + 1912) with (g_S g - 24) by lia. apply b8_bytes_le8. exact B9.
      + replace (g_S g - 1936 + 1904) with (g_S g - 32) by lia. apply b8_bytes_le8. exact B18.
      + replace (g_S g - 1936 + 1896) with (g_S g - 40) by lia. apply b8_bytes_le8. exact B19.
      + replace (g_S g - 1936 + 1888) with (g_S g - 48) by lia. apply b8_bytes_le8. exact B20.
      + replace (g_S g - 1936 + 1880) with (g_S g - 56) by lia. apply b8_bytes_le8. exact B21.
      + replace (g_S g - 1936 + 1872) with (g_S g - 64) by lia. apply b8_bytes_le8. exact B22.
      + replace (g_S g - 1936 + 1864) with (g_S g - 72) by lia. apply b8_bytes_le8. exact B23.
      + replace (g_S g - 1936 + 1856) with (g_S g - 80) by lia. apply b8_bytes_le8. exact B24.
      + replace (g_S g - 1936 + 1848) with (g_S g - 88) by lia. apply b8_bytes_le8. exact B25.
      + replace (g_S g - 1936 + 1840) with (g_S g - 96) by lia. apply b8_bytes_le8. exact B26.
      + replace (g_S g - 1936 + 1832) with (g_S g - 104) by lia. apply b8_bytes_le8. exact B27.
    - rewrite (b8_ret_pc_ra ra (b8_ra B APIf ra empty FF)). apply SR_ret.
      apply (b8_post_FR B APIf ra empty g L A regs regs' mem md HF HP).
      + b8rg HG.
      + intros r Hr. unfold callee_saved in Hr.
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; rewrite HG;
          try reflexivity.
        * destruct HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _). transitivity (Z_to_bv 64 (g_S g)); [|symmetry; exact E2].
          transitivity (Z_to_bv 64 (g_S g - 1936 + 1936)); [reflexivity | f_equal; lia].
        * exact Hgp.
        * exact Htp. }
  split; [|exact H9c].
  intros g c HC.
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HID & Hhas & H10).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (_ & _ & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  set (fz := Z.of_nat (RcIdentModel.first_zero (RcIdentModel.model_name (t_ID (g_in g) (fJ (g_in g)))))) in *.
  assert (Hfz : 0 <= fz <= 17) by (unfold fz; pose proof (b8_fz_mn (t_ID (g_in g) (fJ (g_in g)))); lia).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kX02a |].
  { unfold rg in H10. rewrite H10. intros E. apply (f_equal bv_unsigned) in E.
    rewrite !unsigned_lit in E by (unfold spk, fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *; lia).
    unfold spk, fsp, SLOT_FRAME in E. lia. }
  intros regs' HG. apply H9c. apply (b8_cut_close B APIf ra empty _ _ _ _ L A); [| exact HP | exact I].
  apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
Qed.

End X02.
