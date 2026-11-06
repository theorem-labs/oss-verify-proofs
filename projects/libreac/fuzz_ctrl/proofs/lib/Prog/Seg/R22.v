(* Segment R22 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x1351c, 0x13520], K1351c (turn b) ->
   K1330c (turn b + 1, when b + 1 < 7) or K13524 (b + 1 = 7): R00's latch `addiw s1,s1,1; bne s1,s7,1330c`. libreac v1.9.0:
   the bound 7 in s7 (v1.8 s8), CUR's length in s11 (SlotInv.v CUR / RT). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b3.
Import ListNotations.
Open Scope Z_scope.

Lemma r22_next :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z),
    s1 = Z_to_bv 64 bz -> s7 = Z_to_bv 64 7 -> 0 <= bz <= 5 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (bz + 1)) a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x1330c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1351c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bz
    -> -> Hb.
  step. step.
  rewrite MState.unsigned_lit by lia. rewrite b3_swrap32 by lia. rewrite b3_bv_eqb by lia.
  if_true. apply evt_done. reflexivity.
Qed.

Lemma r22_last :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s1 = Z_to_bv 64 6 -> s7 = Z_to_bv 64 7 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 7) a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x13524) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1351c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    -> ->.
  step. step.
  rewrite ?MState.unsigned_lit by lia. rewrite ?b3_swrap32 by lia. rewrite ?b3_bv_eqb by lia.
  if_false. apply evt_done. reflexivity.
Qed.

Section R22.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R22 : forall b, Hat B APIf ra (Inv_K1330c_at B APIf ra empty) (S b) ->
  Hcut B APIf ra (Inv_K13524 B APIf ra empty) ->
  Hat B APIf ra (Inv_K1351c_at B APIf ra empty) b.
Proof.
  intros b H1 H2 g c (L & A & regs & mem & md & -> & HFR & HP & HRB).
  pose proof HRB as (Hb6 & (Hc & H21 & H27) & HOUR & (H8 & H18 & H19 & H23 & H24 & H25 & H26) & H9 & HID & HFG).
  destruct (Nat.eq_dec b 6) as [Eb | Eb].
  - subst b.
    eapply (b3_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b3_fp g _ x _ Hx O). apply Forall_nil.
    + rewrite sl_mkR_of. apply r22_last; [exact H9 | exact H23].
    + intros ms ->.
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      injection HQ as E1 E2 E3. subst R pc' m0'.
      apply H2. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      destruct (b3_RB_bytes g 6 _ _ regs mem m' [] HRB MU' I I I) as (B1 & B2 & B3).
      unfold RA, CUR, IDB, OURb, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
      refine (conj (conj _ (conj (conj Hc (conj H21 H27)) B1)) (conj H8 B2)). lia.
  - assert (Hbz : (b <= 5)%nat) by lia.
    eapply (b3_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b3_fp g _ x _ Hx O). apply Forall_nil.
    + rewrite sl_mkR_of. apply (r22_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat b));
        [exact H9 | exact H23 | lia].
    + intros ms ->.
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      injection HQ as E1 E2 E3. subst R pc' m0'.
      apply H1. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      destruct (b3_RB_bytes g b _ _ regs mem m' [] HRB MU' I I I) as (B1 & B2 & B3).
      apply (b3_RB_S g b _ _ regs mem regs' m' HRB); try exact B1; try exact B2; try exact B3; try lia;
        rewrite (sl_getr_eqv _ _ _ Hx); [reflexivity | | reflexivity ..].
      transitivity (Z_to_bv 64 (Z.of_nat b + 1)); [reflexivity | f_equal; lia].
Qed.

End R22.
