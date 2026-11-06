(* Segment E02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13a94, 0x13aa4], K13a94 -> K13aa8 (#67 not taken: the
   p.dst bcmp returned 0; bcmp of p.src at sp+1756 with Φ[6 .. 12) returns 0, struct P5.2).
   libreac v1.9.0 (table 5a S_E02, IDENTICAL-RENUMBER): pcs + 0x30, p = sp+1752 so p.src = sp+1756 (v1.8 1740), the
   frame 1936 bytes. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b6.
Import ListNotations.
Open Scope Z_scope.

Lemma e02_evt : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 phi -> a0 = Z_to_bv 64 0 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 <= phi -> phi + 50 <= 2 ^ 64 -> mem_inv rsegs m ->
    bytes_at rsegs m (spv + 1756) ls -> bytes_at rsegs m (phi + 6) rs -> StrFun.memcmp_model ls rs 6 = Some 0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13aa8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13aa8) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a94) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi ls rs -> -> -> Hs Hsp Hp0 Hp1 MI H1 H2 H3.
  step. if_false. step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := ls) (rs := rs) (v := 0).
    - rewrite MState.unsigned_lit by lia. exact H1.
    - rewrite MState.unsigned_lit by lia. exact H2.
    - rewrite MState.unsigned_lit by lia. exact H3.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13aa8)) with (Z_to_bv 64 0x13aa8)
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
  Hat B APIf ra (Inv_K13aa8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13a94_at B APIf ra empty) j.
Proof.
  intros j H78 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEA & H8) & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (b6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof HEA as (HT & H7 & H9 & H0 & H2 & HC & HIFS).
  pose proof HT as (Hj & H26 & HFC & H21 & HPhi & HOUR & HM7).
  pose proof HC as (H8r & H22 & HTF & HB).
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  destruct (b6_8819 (g_in g) j H8) as (Hl & _ & Hs).
  (* p.src = B[4 .. 10) at sp+1756 equals Φ[6 .. 12) (struct P5.2) *)
  pose proof (b6_ba_sub mem (spk g 1752) (t_B (g_in g) j) 4 6 HB
                ltac:(unfold t_B; rewrite RcParse.ctrlparse_length; lia)) as XL.
  replace (spk g 1752 + Z.of_nat 4) with (fsp g + 1756) in XL by (unfold spk; lia).
  pose proof (b6_ba_sub mem phi (t_g (g_in g) j) 6 6 (b6_ba_g mem phi (g_in g) j HPhi Hl)
                ltac:(rewrite b6_g_len; lia)) as XR.
  replace (phi + Z.of_nat 6) with (phi + 6) in XR by lia.
  eapply (b6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I].
  - rewrite sl_mkR_of.
    apply (e02_evt BCMP) with (spv := fsp g) (phi := phi)
      (ls := firstn 6 (skipn 4 (t_B (g_in g) j))) (rs := firstn 6 (skipn 6 (t_g (g_in g) j))).
    + exact Hsp.
    + exact H21.
    + exact H10.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact (mem_inv_normalize rsegs mem).
    + exact (b6_norm mem _ _ HMI XL).
    + exact (b6_norm mem _ _ HMI XR).
    + rewrite Hs. apply b6_mcmp_refl. rewrite length_firstn, length_skipn, b6_g_len. lia.
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; [exact (b6_munch0 _ _ MU)|]. split; [exact WM|].
    split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & HE & _ & _).
    injection HE; intros; subst.
    assert (AV : b6_av g phi (t_len (g_in g) j) 0 0) by (apply b6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (O154 : b6_out 0 0 (spk g 154) 38) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    assert (O16 : b6_out 0 0 (spk g 16) 60) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    assert (K : b6_kS regs regs') by (unfold b6_kS; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
    assert (E18 : YK11.getr regs' 18 = YK11.getr regs 18) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    pose proof (b6_EA_keep g j phi regs regs' mem m' 0 0 HEA K E18 MU AV O154 O16) as HEA'.
    apply H78. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [exact HEA' | exact H8]|].
    unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End E02.
