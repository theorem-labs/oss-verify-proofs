(* Segment R22 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x1364c, 0x13650], U1364c (turn b) ->
   U133e8 (turn b + 1, b <= 5) or U13654 (b = 6): `addiw s1,s1,1; bne s1,s9,133e8` with s9 = 7 (RT). M8 is carried. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u3.
Import ListNotations.
Open Scope Z_scope.

Lemma r22_next :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z),
    s1 = Z_to_bv 64 bz -> s9 = Z_to_bv 64 7 -> 0 <= bz <= 5 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (bz + 1)) a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x133e8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1364c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bz
    -> -> Hb.
  step. step.
  rewrite MState.unsigned_lit by lia. rewrite u3_swrap32 by lia. rewrite u3_bv_eqb by lia.
  if_true. apply evt_done. reflexivity.
Qed.

Lemma r22_last :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s1 = Z_to_bv 64 6 -> s9 = Z_to_bv 64 7 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 7) a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x13654) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1364c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    -> ->.
  step. step.
  rewrite ?MState.unsigned_lit by lia. rewrite ?u3_swrap32 by lia. rewrite ?u3_bv_eqb by lia.
  if_false. apply evt_done. reflexivity.
Qed.

Section R22.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R22 : forall b : nat, Hat B APIf ra (Inv_U133e8_at B APIf ra empty) (S b) ->
  Hcut B APIf ra (Inv_U13654 B APIf ra empty) ->
  Hat B APIf ra (Inv_U1364c_at B APIf ra empty) b.
Proof.
  intros b H1 H2 g c (L & A & regs & mem & md & -> & HFR & HP & HRB).
  pose proof HRB as (Hb6 & (Hc & H22 & H23) & HOUR & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & HM8 & H9 & HID & HFG).
  destruct (Nat.eq_dec b 6) as [Eb | Eb].
  - subst b.
    eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (u3_fp g _ x _ Hx O). apply Forall_nil.
    + rewrite sl_mkR_of. apply r22_last; [exact H9 | exact H25].
    + intros ms ->.
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      injection HQ as E1 E2 E3. subst R pc' m0'.
      apply H2. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      destruct (u3_RB_bytes g 6 _ _ regs mem m' [] HRB MU' I I I I) as (B1 & B2 & B3 & B4).
      unfold RA, CUR, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
      refine (conj (conj _ (conj (conj Hc (conj H22 H23)) B1)) (conj H8 (conj B4 B2))). lia.
  - assert (Hbz : (b <= 5)%nat) by lia.
    eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (u3_fp g _ x _ Hx O). apply Forall_nil.
    + rewrite sl_mkR_of. apply (r22_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat b));
        [exact H9 | exact H25 | lia].
    + intros ms ->.
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      injection HQ as E1 E2 E3. subst R pc' m0'.
      apply H1. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      destruct (u3_RB_bytes g b _ _ regs mem m' [] HRB MU' I I I I) as (B1 & B2 & B3 & B4).
      apply (u3_RB_S g b _ _ regs mem regs' m' HRB); try exact B1; try exact B2; try exact B3; try exact B4; try lia;
        rewrite (sl_getr_eqv _ _ _ Hx); [reflexivity | | reflexivity ..].
      transitivity (Z_to_bv 64 (Z.of_nat b + 1)); [reflexivity | f_equal; lia].
Qed.

End R22.
