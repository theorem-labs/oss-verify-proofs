From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_identity_init_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma a02_evt : reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv lo : Z) (idb : list byte),
    sp = Z_to_bv 64 spv -> 0 <= lo <= spv -> spv + 384 <= 2 ^ 64 -> spv mod 2 = 0 ->
    rw_cells rsegs m (spv + 146) [Cells.CB 38 idb] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12f58) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (spv + 146))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x12f58) fc None m' (seg_rom rsegs) /\
         munch [(lo, spv + 280)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 146) (repeat (Z_to_bv 8 0) 38))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f50) fc None m (seg_rom rsegs)).
Proof.
  intros IC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo idb -> Hlo Hsp Hev HC MI.
  step. step.
  eapply evt_cut.
  { eapply IC with (id := spv + 146) (idb := idb);
      [ first [reflexivity | apply bv_eq; reflexivity] | lia | intros _; split; [rewrite Zplus_mod, Hev; reflexivity | exact HC]
      | exact MI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & _ & Hz).
  subst ms'. specialize (Hz ltac:(lia)).
  replace (ret_pc (Z_to_bv 64 77656)) with (Z_to_bv 64 77656) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [|split; [exact WMc|]].
  - eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x [H _]. split; [lia | exact I].
  - exact (sa_rw_bytes _ _ _ _ Hz).
Qed.

Section A02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis INIT : reac_identity_init_contract.

Lemma seg_A02 : Hcut B APIf ra (Inv_U12f58 B APIf ra empty) -> Hcut B APIf ra (Inv_U12f50 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & Hn & Hp).
  destruct (sa_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sa_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SA_TOP, fsp, SLOT_FRAME in *.
  destruct (sa_rw_of_stk _ _ _ (g_S g - 384 + 146) 38 ST ltac:(lia) ltac:(lia)) as (idb & HC).
  eapply (sa_mid B APIf ra empty FF g 0 [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sa_mkR_of.
    apply (a02_evt INIT) with (spv := g_S g - 384) (lo := g_S g - 65536) (idb := idb).
    + exact Hsp.
    + lia.
    + lia.
    + lia.
    + exact HC.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 65536, g_S g - 384 + 280)]. split; [exact MU|]. split; [exact WM|].
    exact (sa_fp g).
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; rewrite (sa_getr_eqv _ _ _ Hx); [exact Hn | exact Hp]|].
    exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) HZ).
Qed.

End A02.
