(* Segment R24 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x1358c, 0x13590], K1358c -> K13598:
   strcmp's 0 (equal names) takes `beqz a0,13598`. libreac v1.9.0: K13598 stays at 0x13598 (SlotInv.v), so the
   walk is v1.8's (the memset of `first` is S_P01's head); CUR's length register is s11 (SlotInv.v CUR). *)
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

Lemma r24_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x13598) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1358c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step. if_true. apply evt_done. reflexivity.
Qed.

Section R24.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R24 : Hcut B APIf ra (Inv_K13598 B APIf ra empty) -> Hcut B APIf ra (Inv_K1358c B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (H7 & (Hc & H21 & H27) & HOUR) & H8 & HID & H10).
  eapply (b3_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (b3_fp g _ x _ Hx O). apply Forall_nil.
  - rewrite sl_mkR_of. apply r24_evt. exact H10.
  - intros ms ->.
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    injection HQ as E1 E2 E3. subst R pc' m0'.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (E7 : c0 (g_in g) = 7) by (unfold c0; unfold g_n in H7; lia).
    unfold PB, CUR, OURb, rg in *. rewrite E7, !(sl_getr_eqv _ _ _ Hx).
    refine (conj (conj Hc (conj H21 H27)) _).
    apply (bytes_at_transport rsegs _ mem m' _ _ HOUR MU'). exact I.
Qed.

End R24.
