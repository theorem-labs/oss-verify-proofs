(* Segment E01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13a80, 0x13a90], K13a80 -> K13a94 (is_8819: bcmp of
   p.dst at sp+1762 with Φ[0 .. 6) returns 0, struct P5.2), K13ca0 (not is_8819).
   libreac v1.9.0 (table 5a S_E01, CHANGED: register): is_8819 is s0 (0x13a80 `beqz s0`; v1.8 s11), p = sp+1752 so
   p.dst = sp+1762 (v1.8 1746), pcs + 0x30, the frame 1936 bytes; K13ca0 keeps VCm (SlotInv.v: CC7 / EQ carry VC
   without is_8819). rule 24: no function proved. *)
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

Lemma e01_evt : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (t : bool) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 phi -> s0 = Z_to_bv 64 (b2z t) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 <= phi < 2 ^ 64 -> mem_inv rsegs m ->
    (t = true ->
       bytes_at rsegs m (spv + 1762) ls /\ bytes_at rsegs m phi rs /\ StrFun.memcmp_model ls rs 6 = Some 0) ->
    evt rsegs
      (fun ms' =>
         (t = false /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13ca0) fc None m (seg_rom rsegs)) \/
         (t = true /\
          exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x13a94) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13a94) fc None m' (seg_rom rsegs) /\
            munch [] m m' /\ wmono rsegs m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a80) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi t ls rs -> -> Hs0 Hs Hsp Hphi MI Hb.
  destruct t; cbn [b2z] in Hs0; subst s0.
  - destruct (Hb eq_refl) as (H1 & H2 & H3).
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
    replace (ret_pc (Z_to_bv 64 0x13a94)) with (Z_to_bv 64 0x13a94)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    apply evt_done. right. split; [reflexivity|].
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU | exact WM].
  - step. if_true. apply evt_done. left. split; reflexivity.
Qed.

Section E01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BCMP : bcmp_contract.

Lemma seg_E01 : forall j,
  Hat B APIf ra (Inv_K13a94_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13a80_at B APIf ra empty) j.
Proof.
  intros j H64 H70 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HEA).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (b6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof HEA as (HT & H7 & H9 & H0 & H2 & HC & HIFS).
  pose proof HT as (Hj & H26 & HFC & H21 & HPhi & HOUR & HM7).
  pose proof HC as (H8r & H22 & HTF & HB).
  pose proof (b6_len_range (g_in g) j) as (Hl0 & _ & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  (* is_8819: p.dst = B[10 .. 16) at sp+1762 equals Φ[0 .. 6) (struct P5.2), so bcmp returns 0 *)
  assert (D : t_8819 (g_in g) j = true ->
              bytes_at rsegs (normalize rsegs mem) (fsp g + 1762) (firstn 6 (skipn 10 (t_B (g_in g) j))) /\
              bytes_at rsegs (normalize rsegs mem) phi (firstn 6 (skipn 0 (t_g (g_in g) j))) /\
              StrFun.memcmp_model (firstn 6 (skipn 10 (t_B (g_in g) j))) (firstn 6 (skipn 0 (t_g (g_in g) j))) 6 =
                Some 0).
  { intros H8. destruct (b6_8819 (g_in g) j H8) as (Hl & Hd & _).
    split; [|split].
    - pose proof (b6_ba_sub mem (spk g 1752) (t_B (g_in g) j) 10 6 HB
                    ltac:(unfold t_B; rewrite RcParse.ctrlparse_length; lia)) as X.
      replace (spk g 1752 + Z.of_nat 10) with (fsp g + 1762) in X by (unfold spk; lia).
      exact (b6_norm mem _ _ HMI X).
    - pose proof (b6_ba_sub mem phi (t_g (g_in g) j) 0 6 (b6_ba_g mem phi (g_in g) j HPhi Hl)
                    ltac:(rewrite b6_g_len; lia)) as X.
      replace (phi + Z.of_nat 0) with phi in X by lia.
      exact (b6_norm mem _ _ HMI X).
    - rewrite Hd. apply b6_mcmp_refl. rewrite length_firstn, length_skipn, b6_g_len. lia. }
  eapply (b6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I].
  - rewrite sl_mkR_of.
    apply (e01_evt BCMP) with (spv := fsp g) (phi := phi) (t := t_8819 (g_in g) j)
      (ls := firstn 6 (skipn 10 (t_B (g_in g) j))) (rs := firstn 6 (skipn 0 (t_g (g_in g) j))).
    + exact Hsp.
    + exact H21.
    + exact H8r.
    + lia.
    + lia.
    + lia.
    + exact (mem_inv_normalize rsegs mem).
    + exact D.
  - intros ms [(_ & ->) | (_ & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                           m' & -> & MU & WM)].
    + do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity | split; reflexivity].
    + do 3 eexists. split; [reflexivity|]. split; [exact (b6_munch0 _ _ MU)|]. split; [exact WM|].
      split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    assert (AV : b6_av g phi (t_len (g_in g) j) 0 0) by (apply b6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (O154 : b6_out 0 0 (spk g 154) 38) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    assert (O16 : b6_out 0 0 (spk g 16) 60) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    destruct HQ as [(Ht & HE) | (Ht & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' &
                                 t6' & m'' & HE & _ & _)];
      injection HE; intros; subst;
      (assert (K : b6_kS regs regs') by (unfold b6_kS; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split));
      (assert (E18 : YK11.getr regs' 18 = YK11.getr regs 18) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity));
      pose proof (b6_EA_keep g j phi regs regs' mem m' 0 0 HEA K E18 MU AV O154 O16) as HEA'.
    + (* not is_8819: K13ca0 (VCm: VC without is_8819) *)
      destruct HEA' as (HT' & H7' & _ & _ & H2' & HC' & HI').
      apply H70. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [split; [exact HT'|]; split; [exact H2'|]; split; [exact (proj2 HC') | exact HI'] | exact H7'].
    + (* is_8819: K13a94 *)
      apply H64. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [split; [exact HEA' | exact Ht]|].
      unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End E01.
