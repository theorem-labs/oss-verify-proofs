(* Segment R04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x132e4, 0x13308], K132e4 -> K1330c (b = 0)
   (b = 0 and the round-trip loop constants: box 0x105c9, counter 0x1234, bound 7, 1, 36, 0xe38f0000).
   libreac v1.9.0: the same ten instructions with the constants one register lower (0x132f0 `li s7,7`,
   0x132f4 `lui s10,0xe38f`, 0x132f8 `li s9,36`, 0x132fc `li s8,1`, 0x13308 `slli s10,s10,4`; v1.8 s8 / s11 /
   s10 / s9 / s11); s11 keeps n - c. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

Lemma r04_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => exists (a0' a1' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) a0' a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0x105c9) (Z_to_bv 64 0x1234) s4 s5 s6 (Z_to_bv 64 7) (Z_to_bv 64 1)
                       (Z_to_bv 64 36) (Z_to_bv 64 0xe38f0000) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1330c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x132e4) fc None m (seg_rom rsegs)).
Proof.
  intros. do 10 step.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Section R04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R04 : Hat B APIf ra (Inv_K1330c_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_K132e4 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn7 & HCUR & HOUR) & Hs0 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of. apply r04_evt.
  - intros ms (a0' & a1' & ->). do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros z Hz O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (a0' & a1' & HE).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    destruct HCUR as (Hc7 & Hp7 & Hn7').
    unfold RS, RB, RT, CUR, OURb, IDB, FGB, rg, RID, RFG in *. cbn [rt_st fst snd].
    rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [lia|]. split; [split; [exact Hc7|]; split; [exact Hp7 | exact Hn7']|].
    split; [exact (b1_keep [] mem _ m' _ _ HMI (munch_refl _ _) Hrel I HOUR)|].
    split.
    { split; [exact Hs0|]. do 5 (split; [reflexivity|]). reflexivity. }
    split; [reflexivity|].
    split; [exact (b1_keep [] mem _ m' _ _ HMI (munch_refl _ _) Hrel I HID)|].
    exact (b1_keep [] mem _ m' _ _ HMI (munch_refl _ _) Hrel I HFG).
Qed.

End R04.
