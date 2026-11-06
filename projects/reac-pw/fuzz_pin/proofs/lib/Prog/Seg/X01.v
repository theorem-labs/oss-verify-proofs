(* Segment X01 of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (plain): [0x12de4, 0x12e0c], free(phi) and the epilogue.
   K12de4 -> RET (Prog/LLVMFuzzerTestOneInput_c.v's S_X01).
   0x12de4 `mv a0,s0`, 0x12de8 `jal free` (ra 0x12dec; free at 0x13aa8 = frame_facts_plain's ms_free) through
   Tac_b8's b8_free_call (the live block (phi, k + 1) is a user block by CUTST's Permutation, as libreac/fuzz_ctrl's
   Seg/C05.v), which leaves FR with hb = []; then 0x12dec `mv a0,zero`, the six restores ra, s0 .. s4 from the saved
   bytes at S - 48 (0x12df0 .. 0x12e04), 0x12e08 `addi sp,sp,64`, 0x12e0c `ret`: Post by b8_post_FR (as ctrl's
   Seg/X02.v). The callee-saved registers: sp, gp, tp from FR, s0 .. s4 from the saved bytes, s5 .. s11 from KS (free
   keeps them). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.Seg Require Import Tac_slot Tac_b8.
Import ListNotations.
Open Scope Z_scope.

(* 0x12de4 `mv a0,s0`; 0x12de8 `jal free`. *)
Lemma kX01a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x12dec) x2 x3 x4 x5 x6 x7 x8 x9 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13aa8) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x12de4) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x12dec `mv a0,zero`; the restores of ra, s0 .. s4 from [sp + 16, sp + 64); `addi sp,sp,64`; `ret`. *)
Lemma kX01b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z)
    (r1 r8 r9 r18 r19 r20 : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 64 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 56)) 8 = Some (le8 r1) ->
  ov_read_bytes rsegs m (wa (sp0 + 48)) 8 = Some (le8 r8) ->
  ov_read_bytes rsegs m (wa (sp0 + 40)) 8 = Some (le8 r9) ->
  ov_read_bytes rsegs m (wa (sp0 + 32)) 8 = Some (le8 r18) ->
  ov_read_bytes rsegs m (wa (sp0 + 24)) 8 = Some (le8 r19) ->
  ov_read_bytes rsegs m (wa (sp0 + 16)) 8 = Some (le8 r20) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR r1 (Z_to_bv 64 (sp0 + 64)) x3 x4 x5 x6 x7 r8 r9 (Z_to_bv 64 0) x11 x12 x13 x14 x15
                           x16 x17 r18 r19 r20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (ret_pc r1) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x12dec) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 r1 r8 r9 r18 r19 r20 E2 H0 H1 R1 R8 R9 R18 R19 R20.
  subst x2.
  step. step. step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

Section X01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract B (APIf rc).

(* The saved bytes at S - 48: s4, s3, s2, s1, s0, ra. *)
Lemma x01_saved_split : forall g mem, bytes_at rsegs mem (g_S g - SLOT_SAVE) (saved_bytes ra g) ->
  bytes_at rsegs mem (g_S g - 48) (le8 (getr (g_regs g) 20)) /\
  bytes_at rsegs mem (g_S g - 40) (le8 (getr (g_regs g) 19)) /\
  bytes_at rsegs mem (g_S g - 32) (le8 (getr (g_regs g) 18)) /\
  bytes_at rsegs mem (g_S g - 24) (le8 (getr (g_regs g) 9)) /\
  bytes_at rsegs mem (g_S g - 16) (le8 (getr (g_regs g) 8)) /\
  bytes_at rsegs mem (g_S g - 8) (le8 (Z_to_bv 64 ra)).
Proof.
  intros g mem H. unfold saved_bytes, SLOT_SAVE in H.
  repeat (apply bytes_at_app in H; destruct H as [?H H]; rewrite length_le8 in H).
  repeat match goal with |- _ /\ _ => split end;
    match goal with H : bytes_at _ _ ?a (le8 ?v) |- bytes_at _ _ ?b (le8 ?v) => replace b with a by lia; exact H end.
Qed.

Lemma seg_X01 : S_X01 B APIf ra empty.
Proof.
  intros g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (H8 & HKS).
  destruct HKS as (K21 & K22 & K23 & K24 & K25 & K26 & K27).
  assert (Hin : In (phi, g_k g + 1) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kX01a | intros regs_c HG].
  unfold hb1 in HF, HP. rewrite <- Ep in HF, HP.
  apply (b8_free_call B APIf ra empty FF FREE g L A regs mem md regs_c p (g_k g + 1)).
  - exact HF.
  - exact HP.
  - exact Hp.
  - b8rg HG.
  - b8rg HG.
  - b8rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG. transitivity (getr regs 8); [reflexivity|]. rewrite Ep. exact H8.
  - intros L' A' regs' mem' md' HF' HP' RP' _.
    replace (getr regs_c 1) with (Z_to_bv 64 0x12dec) by (rewrite HG; reflexivity).
    pose proof HF' as (HGV & Hsp & Hgp & Htp & HSV & _).
    pose proof (b8_GV_S B empty g HGV) as (_ & HS).
    pose proof alloc_ceiling_value as HAC.
    destruct (x01_saved_split g mem' HSV) as (B20 & B19 & B18 & B9 & B8 & B1).
    unfold fsp, SLOT_FRAME in Hsp. unfold SLOT_K, SLOT_STACK in HS.
    (* s5 .. s11 after free: free keeps regs_c's, which are the cut's, which KS ties to the entry's. *)
    assert (HKS' : forall r : Z, 21 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr (g_regs g) (Z_to_bv 5 r)).
    { intros r Hr. rewrite (RP' r ltac:(unfold callee_saved; lia)), HG.
      assert (Hr' : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->| ->]]]]]];
        first [exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]. }
    eapply (b8_run_to B APIf ra empty FF); [exact HF' | | intros regs'' HG'].
    + unfold rmk. eapply kX01b with (sp0 := g_S g - 64).
      * exact Hsp.
      * lia.
      * lia.
      * replace (g_S g - 64 + 56) with (g_S g - 8) by lia. apply b8_bytes_le8. exact B1.
      * replace (g_S g - 64 + 48) with (g_S g - 16) by lia. apply b8_bytes_le8. exact B8.
      * replace (g_S g - 64 + 40) with (g_S g - 24) by lia. apply b8_bytes_le8. exact B9.
      * replace (g_S g - 64 + 32) with (g_S g - 32) by lia. apply b8_bytes_le8. exact B18.
      * replace (g_S g - 64 + 24) with (g_S g - 40) by lia. apply b8_bytes_le8. exact B19.
      * replace (g_S g - 64 + 16) with (g_S g - 48) by lia. apply b8_bytes_le8. exact B20.
    + rewrite (b8_ret_pc_ra ra (b8_ra B APIf ra empty FF)). apply SR_ret.
      apply (b8_post_FR B APIf ra empty g L' A' regs' regs'' mem' md' HF' HP').
      * b8rg HG'.
      * intros r Hr. unfold callee_saved in Hr.
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; rewrite HG';
          try reflexivity.
        -- destruct HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _). transitivity (Z_to_bv 64 (g_S g)); [|symmetry; exact E2].
           transitivity (Z_to_bv 64 (g_S g - 64 + 64)); [reflexivity | f_equal; lia].
        -- exact Hgp.
        -- exact Htp.
        -- exact (HKS' 21 ltac:(lia)).
        -- exact (HKS' 22 ltac:(lia)).
        -- exact (HKS' 23 ltac:(lia)).
        -- exact (HKS' 24 ltac:(lia)).
        -- exact (HKS' 25 ltac:(lia)).
        -- exact (HKS' 26 ltac:(lia)).
        -- exact (HKS' 27 ltac:(lia)).
Qed.

End X01.
