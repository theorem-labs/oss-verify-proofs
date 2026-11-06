(* Segment E02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13c78, 0x13c90], U13c78 -> U13c94 (#67 not taken:
   a0 = 0; T43 not taken: Φ + 6 >= 7; bcmp of p.src at sp+1756 with Φ[6 .. 12) returns 0, struct P5.2). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u6.
Import ListNotations.
Open Scope Z_scope.

(* 0x13c6c -> 0x13c88 (v1.8 0x13c78 -> 0x13c94): bnez a0 (#67); addi a1,s7,6; li a0,7; bltu a1,a0 (T43); li a2,6;
   addi a0,sp,1756; jal bcmp. Φ is s7 (v1.8 s6). *)
Lemma e02_evt : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> a0 = Z_to_bv 64 0 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 4096 <= phi -> phi + 50 <= 2 ^ 64 -> mem_inv rsegs m ->
    bytes_at rsegs m (spv + 1756) ls -> bytes_at rsegs m (phi + 6) rs -> StrFun.memcmp_model ls rs 6 = Some 0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13c88) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13c88) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c6c) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi ls rs -> -> -> Hs Hsp Hp0 Hp1 MI H1 H2 H3.
  step. if_false.
  step. step. step. u6_nt false.
  step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := ls) (rs := rs) (v := 0).
    - rewrite MState.unsigned_lit by lia. exact H1.
    - rewrite MState.unsigned_lit by lia. exact H2.
    - rewrite MState.unsigned_lit by lia. exact H3.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13c88)) with (Z_to_bv 64 0x13c88)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Section E02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BCMP : bcmp_contract.

Lemma seg_E02 : forall j,
  Hat B APIf ra (Inv_U13c88_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13c6c_at B APIf ra empty) j.
Proof.
  intros j H94 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEA & H88) & H10).
  destruct (u6_S_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  destruct (u6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof alloc_ceiling_lt as Hac.
  pose proof HEA as ((HT & H7 & H1 & H0 & H2 & HC) & HIFS).
  pose proof HT as (HLK & HFC & H23 & HPhi & H18).
  pose proof HC as (H24 & H16 & HB).
  unfold SLOT_K, SLOT_STACK in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  destruct (u6_8819 (g_in g) j H88) as (Hl & _ & Hs).
  (* p.src = B[4 .. 10) at sp+1756 equals Φ[6 .. 12) (struct P5.2) *)
  pose proof (u6_ba_sub mem (spk g 1752) (t_B (g_in g) j) 4 6 HB
                ltac:(unfold t_B; rewrite RcParse.ctrlparse_length; lia)) as XL.
  replace (spk g 1752 + Z.of_nat 4) with (fsp g + 1756) in XL by (unfold spk; lia).
  pose proof (u6_ba_sub mem phi (t_g (g_in g) j) 6 6 (u6_ba_g mem phi (g_in g) j HPhi Hl)
                ltac:(rewrite u6_g_len; lia)) as XR.
  replace (phi + Z.of_nat 6) with (phi + 6) in XR by lia.
  eapply (u6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I].
  - rewrite sl_mkR_of.
    apply (e02_evt BCMP) with (spv := fsp g) (phi := phi)
      (ls := firstn 6 (skipn 4 (t_B (g_in g) j))) (rs := firstn 6 (skipn 6 (t_g (g_in g) j))).
    + exact Hsp.
    + exact H23.
    + exact H10.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact (mem_inv_normalize rsegs mem).
    + exact (u6_norm mem _ _ HMI XL).
    + exact (u6_norm mem _ _ HMI XR).
    + rewrite Hs. apply u6_mcmp_refl. rewrite length_firstn, length_skipn, u6_g_len. lia.
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; [exact (u6_munch0 _ _ MU)|]. split; [exact WM|].
    split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & HE & _ & _).
    injection HE; intros; subst.
    assert (AV : u6_av g phi (t_len (g_in g) j) 0 0) by (apply u6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (AI : u6_ai g 0 0) by (apply u6_ai0; unfold fsp, SLOT_FRAME; lia).
    assert (K : u6_kT regs regs') by (unfold u6_kT; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
    assert (E19 : YK11.getr regs' 19 = YK11.getr regs 19) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E27 : YK11.getr regs' 27 = YK11.getr regs 27) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    pose proof (u6_EA_keep g j phi regs regs' mem m' 0 0 HEA K E19 E27 MU AV AI) as HEA'.
    apply H94. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [exact HEA' | exact H88]|].
    unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End E02.
