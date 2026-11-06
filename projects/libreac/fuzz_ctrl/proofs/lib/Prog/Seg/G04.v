(* Segment G04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13910, 0x1394c], K13910, K13914 -> K13950 (rf = 1),
   K139e8 (rf = 0).
   libreac v1.9.0 (table 5a S_G04, IDENTICAL-RENUMBER): pcs + 0xc, the fragment outputs pl / pll at sp+1736 /
   sp+1728 (v1.8 1720 / 1712), &frag + 8 = sp+90 and &frag + 19 = sp+101 (v1.8 74 / 85), the frame 1936 bytes.
   rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b6.
Import ListNotations.
Open Scope Z_scope.

Lemma g04_e0 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pc : Z),
    (pc = 0x13914 \/ (pc = 0x13910 /\ a0 = Z_to_bv 64 0)) -> s8 = Z_to_bv 64 0 ->
    evt rsegs
      (fun ms' => exists a0' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x139e8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pc Hpc ->.
  destruct Hpc as [-> | [-> ->]]; [|step; if_false].
  all: step; step; if_true; apply evt_done; eexists; reflexivity.
Qed.

Lemma g04_e1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pc spv pll : Z),
    (pc = 0x13914 \/ (pc = 0x13910 /\ a0 = Z_to_bv 64 0)) ->
    sp = Z_to_bv 64 spv -> s8 = Z_to_bv 64 1 -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> 1 <= pll <= 51 ->
    ov_read_bytes rsegs m (wa (spv + 1736)) 8 = Some (le8 (Z_to_bv 64 (spv + 101))) ->
    ov_read_bytes rsegs m (wa (spv + 1728)) 8 = Some (le8 (Z_to_bv 64 pll)) ->
    evt rsegs
      (fun ms' => exists a0' a1' a4' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 (spv + 101)) (Z_to_bv 64 pll) a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13950) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pc spv pll Hpc -> -> Hs Hsp Hp R1 R2.
  destruct Hpc as [-> | [-> ->]]; [|step; if_false].
  all: step; step; if_false.
  all: step; step; step; rewrite b6_ltu by lia; if_false.
  all: step; step; step; rewrite ?MState.unsigned_lit by lia; rewrite b6_ltu by lia; if_false.
  all: step; step; step; step; step; rewrite ?MState.unsigned_lit by lia; rewrite b6_ltu by lia; if_false.
  all: step; step; if_false.
  all: apply evt_done; do 3 eexists; reflexivity.
Qed.

Section G04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_G04 : forall j,
  Hat B APIf ra (Inv_K13950_at B APIf ra empty) j -> Hat B APIf ra (Inv_K139e8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13910_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K13914_at B APIf ra empty) j.
Proof.
  intros j H944 H9b8.
  assert (RUN : forall g phi L A regs mem md pc,
    (pc = 0x13914 \/ (pc = 0x13910 /\ YK11.getr regs 10 = Z_to_bv 64 0)) ->
    FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs mem md ->
    Permutation (blocks L A) (hb1 phi (t_len (g_in g) j) ++ blocks (g_L g) (g_A g)) ->
    GF g j phi regs mem -> rg regs 24 (t_rf (g_in g) j) ->
    SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g)).
  { intros g phi L A regs mem md pc Hpc HFR HP HGF H24.
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    destruct (b6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    assert (HW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside [(0, 0)] x ->
                 g_S g - SLOT_K <= x < g_S g - 104).
    { intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I]. }
    assert (AV : b6_av g phi (t_len (g_in g) j) 0 0) by (apply b6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (O154 : b6_out 0 0 (spk g 154) 38) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    assert (O16 : b6_out 0 0 (spk g 16) 60) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    destruct (b6_rf01 (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j)) as [Hrf | Hrf];
      fold (t_rf (g_in g) j) in Hrf; rewrite Hrf in H24.
    - (* rf = 0: K139e8 *)
      eapply (b6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | exact HW | | |].
      + rewrite sl_mkR_of. apply g04_e0; [exact Hpc | exact H24].
      + intros ms (? & ->). do 3 eexists. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [reflexivity | split; reflexivity].
      + intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
        destruct HQ as (a0' & HE). injection HE; intros; subst.
        assert (K : b6_kS regs regs') by (unfold b6_kS; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
        assert (E18 : YK11.getr regs' 18 = YK11.getr regs 18) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
        destruct (b6_GF_keep g j phi regs regs' mem m' 0 0 HGF K E18 MU AV O154 O16) as (HB & HI & HG & HS & _).
        apply H9b8. exists phi, L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        split; [exact HB|]. split; [|split; [exact HG | exact HS]].
        unfold IDj. rewrite (b6_tID_S0 (g_in g) j ltac:(lia)). exact HI.
    - (* rf = 1: K13950 *)
      pose proof HGF as (_ & _ & _ & _ & _ & Hrs).
      destruct (Hrs Hrf) as (_ & Hpl & Hpll).
      destruct (b6_close_facts (g_in g) j Hrf) as (HT & _).
      eapply (b6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | exact HW | | |].
      + rewrite sl_mkR_of.
        apply (g04_e1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pc (g_S g - 1936)
                 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)));
          [exact Hpc | exact Hsp | exact H24 | lia | lia | unfold f_pll; lia | |].
        * apply b6_q64_ovr. apply (b6_q64_norm mem _ _ HMI Hpl).
        * apply b6_q64_ovr. apply (b6_q64_norm mem _ _ HMI Hpll).
      + intros ms (? & ? & ? & ->). do 3 eexists. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [reflexivity | split; reflexivity].
      + intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
        destruct HQ as (a0' & a1' & a4' & HE). injection HE; intros; subst.
        assert (K : b6_kS regs regs') by (unfold b6_kS; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
        assert (E18 : YK11.getr regs' 18 = YK11.getr regs 18) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
        pose proof (b6_GF_keep g j phi regs regs' mem m' 0 0 HGF K E18 MU AV O154 O16) as HGF'.
        apply H944. exists phi, L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        split; [exact HGF'|]. unfold rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [rewrite Hrf; exact H24|]. split; [exact Hrf|].
        split; reflexivity. }
  split.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H24 & _ & H10).
    exact (RUN g phi L A regs mem md 0x13910 (or_intror (conj eq_refl H10)) HFR HP HGF H24).
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H24).
    exact (RUN g phi L A regs mem md 0x13914 (or_introl eq_refl) HFR HP HGF H24).
Qed.

End G04.
