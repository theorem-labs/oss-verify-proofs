(* Segment R03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x133a8, 0x133b4], U133a8 -> U133b8
   (memset(frag = sp+120, 0, 72)). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

Lemma r03_evt : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> 0 < spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 120) [Cells.CB 72 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x133b8) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x133b8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 120, spv + 192)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 120) z72)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x133a8) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk -> Hsp0 Hsp HC MI.
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk).
    - rewrite !MState.unsigned_lit by lia. exact HC.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & HZ).
  subst ms'. rewrite !MState.unsigned_lit in MUc, HZ by lia.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [|split; [exact WMc | exact (sl_rw_bytes _ _ _ _ HZ)]].
  eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
Qed.

Section R03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MSET : memset_contract.

Lemma seg_R03 : Hcut B APIf ra (Inv_U133b8 B APIf ra empty) -> Hcut B APIf ra (Inv_U133a8 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn7 & HCUR & HOUR) & Hs0 & HID).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 120) 72 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r03_evt MSET) with (spv := g_S g - 1936) (junk := junk);
      [exact Hsp | lia | lia | exact HC | exact (mem_inv_normalize rsegs mem)].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 + 120, g_S g - 1936 + 192)]. split; [exact MU|]. split; [exact WM|].
    intros z Hz O. apply (sl_fp1 g (g_S g - 1936 + 120) (g_S g - 1936 + 192) z);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hz | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HZ).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    destruct HCUR as (Hc7 & Hp7 & Hn7').
    unfold RA, CUR, OURb, RIDB, IDB, FGB, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split.
    { split; [exact Hn7|]. split; [split; [exact Hc7|]; split; [exact Hp7 | exact Hn7']|].
      apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HOUR].
      rewrite OUR_length. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME. lia. }
    split; [exact Hs0|]. split.
    { apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HID].
      unfold RcIdentModel.ID0. rewrite repeat_length. cbn [disjoint_from]. split; [|exact I].
      unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE. lia. }
    exact (u1_out _ _ _ _ Hrel HZ).
Qed.

End R03.
