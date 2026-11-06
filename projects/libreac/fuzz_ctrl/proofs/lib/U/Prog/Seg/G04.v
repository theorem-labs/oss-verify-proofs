(* Segment G04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13ab0, 0x13aec], U13ab0 (#57's bcmp
   result 0), U13ab4 -> U13af0 (v1.8 U13af8, section-8 anchor) (rf = 1: #58-#61 by the fragment outputs pp = buf +
   11 = sp+139, pll_f + 2 <= 53 (AF7 with base = buf = sp+128, len = 64), T26 on buf not taken by SR, #62), U13b64
   (v1.8 U13b6c) (rf = 0). No call. v1.9 keeps buf = &frag + 8 in s0 (set at 0x137b8) where v1.8 recomputed
   `addi a?,sp,90` at 0x13abc / 0x13ae4, compares rf (s10; v1.8 s9) with s2 = 1 (v1.8 s0 = 1), and has 15
   instructions here (v1.8 17). Port of the plain seg_G04 (a working branch lib/Prog/Seg/G04.v). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

Lemma g04_e0 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pc : Z),
    (pc = 0x13ab4 \/ (pc = 0x13ab0 /\ a0 = Z_to_bv 64 0)) -> s10 = Z_to_bv 64 0 -> s2 = Z_to_bv 64 1 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x13b64) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pc Hpc -> ->.
  destruct Hpc as [-> | [-> ->]].
  - step. u5_br true. apply evt_done. reflexivity.
  - step. u5_br false. step. u5_br true. apply evt_done. reflexivity.
Qed.

Lemma g04_e1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pc spv pll : Z),
    (pc = 0x13ab4 \/ (pc = 0x13ab0 /\ a0 = Z_to_bv 64 0)) ->
    sp = Z_to_bv 64 spv -> s10 = Z_to_bv 64 1 -> s2 = Z_to_bv 64 1 -> s0 = Z_to_bv 64 (spv + 128) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    1 <= pll <= 51 ->
    ov_read_bytes rsegs m (wa (spv + 1736)) 8 = Some (le8 (Z_to_bv 64 (spv + 139))) ->
    ov_read_bytes rsegs m (wa (spv + 1728)) 8 = Some (le8 (Z_to_bv 64 pll)) ->
    evt rsegs
      (fun ms' => exists a0' a2' a3' a4' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 pll) a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13af0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pc spv pll Hpc -> -> -> -> Hlo Hhi Hpll R1736 R1728.
  destruct Hpc as [-> | [-> ->]]; [|step; u5_br false].
  all: step; u5_br false.
  all: step; step; u5_br false.
  all: step; step; step; u5_br false.
  all: step; step; step; step; step; u5_br false.
  all: step; step; u5_br false.
  all: step; step; u5_br false.
  all: apply evt_done; do 4 eexists; reflexivity.
Qed.

Section G04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_G04 : forall j : nat,
  Hat B APIf ra (Inv_U13af0_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13b64_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13ab0_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U13ab4_at B APIf ra empty) j.
Proof.
  intros j Haf0 Hb64.
  assert (RUN : forall g phi L A regs mem md pc,
    (pc = 0x13ab4 \/ (pc = 0x13ab0 /\ YK11.getr regs 10 = Z_to_bv 64 0)) ->
    FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs mem md ->
    Permutation (blocks L A) (hb1 phi (t_len (g_in g) j) ++ blocks (g_L g) (g_A g)) ->
    GF g j phi regs mem -> rg regs 26 (t_rf (g_in g) j) ->
    SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g)).
  { intros g phi L A regs mem md pc Hpc HFR HP HGF H26.
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
    pose proof HGF as (((HLK & _) & _) & _).
    pose proof (u4_LK_s2 g j regs mem HLK) as H18.
    pose proof (u4_LK_s0 g j regs mem HLK) as H8.
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    destruct (u5_rf01 (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j)) as [Hrf | Hrf];
      fold (t_rf (g_in g) j) in Hrf; rewrite Hrf in H26.
    - (* rf = 0: U13b64 *)
      eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []);
        [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
      + rewrite sl_mkR_of. apply g04_e0; [exact Hpc | exact H26 | exact H18].
      + intros ms ->. do 3 eexists. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [reflexivity | split; reflexivity].
      + intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
        injection HQ; intros; subst.
        assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
        pose proof (u5_GF_keep g j phi regs regs' mem m' _ HGF HKP MU ltac:(u4_dj) ltac:(u4_dj) ltac:(u4_dj)
                      ltac:(u4_dj) ltac:(u4_dj) ltac:(u4_dj) ltac:(u4_dj) ltac:(u4_dj) ltac:(u4_dj)
                      ltac:(u4_dj)) as (HB & HI & HG & HS & _).
        apply Hb64. exists phi, L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        split; [exact HB|]. split; [|split; [exact HG | exact HS]].
        unfold IDj. rewrite (u5_tID_S0 (g_in g) j ltac:(lia)). exact HI.
    - (* rf = 1: U13af0 *)
      pose proof HGF as (_ & _ & _ & _ & _ & Hrs). destruct (Hrs Hrf) as (_ & Hpl & Hpll).
      destruct (u5_close_facts (g_in g) j Hrf) as (HT & _).
      unfold spk, fsp, SLOT_FRAME in Hpl, Hpll.
      eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []);
        [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
      + rewrite sl_mkR_of.
        apply g04_e1 with (spv := g_S g - 1936) (pll := f_pll (t_FG (g_in g) j) (t_g (g_in g) j));
          [exact Hpc | exact Hsp | exact H26 | exact H18 | exact H8 | lia | lia | unfold f_pll; lia
          | exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Hpl))
          | exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Hpll))].
      + intros ms (? & ? & ? & ? & ->). do 3 eexists. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [reflexivity | split; reflexivity].
      + intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
        destruct HQ as (? & ? & ? & ? & HE). injection HE; intros; subst.
        assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
        apply Haf0. exists phi, L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        split; [apply (u5_GF_keep g j phi regs regs' mem m' _ HGF HKP MU); u4_dj|].
        split; [unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); rewrite Hrf; exact H26|].
        split; [exact Hrf|].
        unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
  split.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H26 & _ & H10).
    exact (RUN g phi L A regs mem md 0x13ab0 (or_intror (conj eq_refl H10)) HFR HP HGF H26).
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H26).
    exact (RUN g phi L A regs mem md 0x13ab4 (or_introl eq_refl) HFR HP HGF H26).
Qed.

End G04.
