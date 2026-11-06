(* Segment E01 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13c58, 0x13c68], U13c64 (v1.9 pc
   0x13c58) -> U13c78 (v1.9 pc 0x13c6c; is_8819: bcmp of p.dst at sp+1762 with Φ[0 .. 6) returns 0, struct P5.2),
   U13fa4 (v1.9 pc 0x13f98; not is_8819). is_8819 is s3, Φ is s7 (v1.8 s1, s6). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u6.
Import ListNotations.
Open Scope Z_scope.

(* 0x13c58 -> 0x13c6c: beqz s3 (is_8819) to 0x13f98; li a2,6; addi a0,sp,1762; mv a1,s7; jal bcmp. *)
Lemma e01_evt : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (t : bool) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s3 = Z_to_bv 64 (b2z t) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 <= phi < 2 ^ 64 -> mem_inv rsegs m ->
    (t = true ->
       bytes_at rsegs m (spv + 1762) ls /\ bytes_at rsegs m phi rs /\ StrFun.memcmp_model ls rs 6 = Some 0) ->
    evt rsegs
      (fun ms' =>
         (t = false /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f98) fc None m (seg_rom rsegs)) \/
         (t = true /\
          exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x13c6c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13c6c) fc None m' (seg_rom rsegs) /\
            munch [] m m' /\ wmono rsegs m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c58) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi t ls rs -> -> Hs3 Hs Hsp Hphi MI Hb.
  destruct t; cbn [b2z] in Hs3; subst s3.
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
    replace (ret_pc (Z_to_bv 64 0x13c6c)) with (Z_to_bv 64 0x13c6c)
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
  Hat B APIf ra (Inv_U13c6c_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13c58_at B APIf ra empty) j.
Proof.
  intros j H78 Hfa g c (phi & L & A & regs & mem & md & -> & HFR & HP & HEA).
  destruct (u6_S_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  destruct (u6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof alloc_ceiling_lt as Hac.
  pose proof HEA as ((HT & H7 & H1 & H0 & H2 & HC) & HIFS).
  pose proof HT as (HLK & HFC & H23 & HPhi & H18).
  pose proof HC as (H24 & H16 & HB).
  pose proof (u6_len_range (g_in g) j) as (Hl0 & _ & _).
  unfold SLOT_K, SLOT_STACK in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  (* is_8819: p.dst = B[10 .. 16) at sp+1762 equals Φ[0 .. 6) (struct P5.2), so bcmp returns 0 *)
  assert (D : t_8819 (g_in g) j = true ->
              bytes_at rsegs (normalize rsegs mem) (fsp g + 1762) (firstn 6 (skipn 10 (t_B (g_in g) j))) /\
              bytes_at rsegs (normalize rsegs mem) phi (firstn 6 (skipn 0 (t_g (g_in g) j))) /\
              StrFun.memcmp_model (firstn 6 (skipn 10 (t_B (g_in g) j))) (firstn 6 (skipn 0 (t_g (g_in g) j))) 6 =
                Some 0).
  { intros H88. destruct (u6_8819 (g_in g) j H88) as (Hl & Hd & _).
    split; [|split].
    - pose proof (u6_ba_sub mem (spk g 1752) (t_B (g_in g) j) 10 6 HB
                    ltac:(unfold t_B; rewrite RcParse.ctrlparse_length; lia)) as X.
      replace (spk g 1752 + Z.of_nat 10) with (fsp g + 1762) in X by (unfold spk; lia).
      exact (u6_norm mem _ _ HMI X).
    - pose proof (u6_ba_sub mem phi (t_g (g_in g) j) 0 6 (u6_ba_g mem phi (g_in g) j HPhi Hl)
                    ltac:(rewrite u6_g_len; lia)) as X.
      replace (phi + Z.of_nat 0) with phi in X by lia.
      exact (u6_norm mem _ _ HMI X).
    - rewrite Hd. apply u6_mcmp_refl. rewrite length_firstn, length_skipn, u6_g_len. lia. }
  eapply (u6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I].
  - rewrite sl_mkR_of.
    apply (e01_evt BCMP) with (spv := fsp g) (phi := phi) (t := t_8819 (g_in g) j)
      (ls := firstn 6 (skipn 10 (t_B (g_in g) j))) (rs := firstn 6 (skipn 0 (t_g (g_in g) j))).
    + exact Hsp.
    + exact H23.
    + exact H1.
    + lia.
    + lia.
    + lia.
    + exact (mem_inv_normalize rsegs mem).
    + exact D.
  - intros ms [(_ & ->) | (_ & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                           m' & -> & MU & WM)].
    + do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity | split; reflexivity].
    + do 3 eexists. split; [reflexivity|]. split; [exact (u6_munch0 _ _ MU)|]. split; [exact WM|].
      split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    assert (AV : u6_av g phi (t_len (g_in g) j) 0 0) by (apply u6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (AI : u6_ai g 0 0) by (apply u6_ai0; unfold fsp, SLOT_FRAME; lia).
    destruct HQ as [(Ht & HE) | (Ht & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' &
                                 t6' & m'' & HE & _ & _)];
      injection HE; intros; subst;
      (assert (K : u6_kT regs regs') by (unfold u6_kT; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split));
      (assert (E19 : YK11.getr regs' 19 = YK11.getr regs 19) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity));
      (assert (E27 : YK11.getr regs' 27 = YK11.getr regs 27) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity));
      pose proof (u6_EA_keep g j phi regs regs' mem m' 0 0 HEA K E19 E27 MU AV AI) as HEA'.
    + (* not is_8819: U13fa4 (v1.9 pc 0x13f98) *)
      destruct HEA' as ((HT' & H7' & _ & _ & H2' & HC') & HI').
      apply Hfa. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [split; [exact HT'|]; split; [exact HC' | exact HI'] | split; [exact H2' | exact H7']].
    + (* is_8819: U13c78 (v1.9 pc 0x13c6c) *)
      apply H78. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [split; [exact HEA' | exact Ht]|].
      unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End E01.
