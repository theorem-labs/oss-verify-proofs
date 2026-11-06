(* Segment R04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x133b8, 0x133e4], U133b8 -> U133e8
   (b = 0) (b = 0, q64 sp+24 = m & 7 = 0 (M8 starts; CATU), the round-trip constants RT). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

Lemma r04_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv md : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 md -> 0 <= md < 2 ^ 64 -> md mod 8 = 0 ->
    rw_cells rsegs m (spv + 24) [Cells.CB 8 junk] ->
    evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) a0' a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0x105c9) (Z_to_bv 64 0x1234) s4 s5 s6 s7 (Z_to_bv 64 32) (Z_to_bv 64 7)
                       (Z_to_bv 64 0xe38f0000) (Z_to_bv 64 36) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x133e8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 24, spv + 32)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 24) (le8 (Z_to_bv 64 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x133b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv md junk -> -> Hmd H8 HC.
  pose proof (munch_refl [(spv + 24, spv + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (E7 : Z.land md 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact H8).
  step. step.
  rewrite (MState.unsigned_lit md) by lia. rewrite E7.
  step.
  do 9 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  pose proof (sl_cells_bytes _ _ _ HC) as HB. cbn [Cells.cells_bytes Cells.cbytes] in HB.
  rewrite ?app_nil_r in HB.
  split; [exact MU|]. split; [exact WM|]. exact HB.
Qed.

Section R04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R04 : Hat B APIf ra (Inv_U133e8_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_U133b8 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn7 & HCUR & HOUR) & Hs0 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof alloc_ceiling_value as Hac.
  pose proof (u1_mrow (g_in g)) as (_ & Hm32 & Hm8).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 24) 8 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply r04_evt with (spv := g_S g - 1936) (md := mrow (g_in g)) (junk := junk);
      [exact Hsp | exact Hs0 | lia | exact Hm8 | exact HC].
  - intros ms (a0' & a1' & m' & -> & MU & WM & _). do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 + 24, g_S g - 1936 + 32)]. split; [exact MU|]. split; [exact WM|].
    intros z Hz O. apply (sl_fp1 g (g_S g - 1936 + 24) (g_S g - 1936 + 32) z);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hz | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (a0' & a1' & m'' & HE & MU & _ & HZ).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    destruct HCUR as (Hc7 & Hp7 & Hn7').
    unfold RS, RB, RT, CUR, OURb, RIDB, IDB, FGB, M8, q64, rg, RID, RFG in *. cbn [rt_st fst snd].
    rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [lia|]. split; [split; [exact Hc7|]; split; [exact Hp7 | exact Hn7']|].
    split.
    { apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HOUR].
      rewrite OUR_length. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME. lia. }
    split.
    { split; [exact Hs0|]. do 5 (split; [reflexivity|]). reflexivity. }
    split; [exact (u1_out _ _ _ _ Hrel HZ)|].
    split; [reflexivity|].
    split.
    { apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HID].
      unfold RcIdentModel.ID0. rewrite repeat_length. cbn [disjoint_from]. split; [|exact I].
      unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE. lia. }
    apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HFG].
    rewrite z72_length. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME. lia.
Qed.

End R04.
