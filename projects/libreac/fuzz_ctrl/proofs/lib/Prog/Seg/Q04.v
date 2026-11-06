(* Segment Q04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13ba8, 0x13bd4], K13ba8 -> K13bd8 (r_p = 0) or
   K13ca0 (r_p != 0). Branches #75 (PU C1.5: both calls return unk), #76 (C5.3: r_p = 0 exactly when unk >= 0) and
   #77-#79 (C5.4: r_p != 0 leaves the three -7 words) are not taken. *)
(* libreac v1.9.0 (IDENTICAL-RENUMBER, segment table 5a S_Q04): v1.8 [0x13b78, 0x13ba4] K13b78 -> K13ba8 / K13c70;
   the ports slots sp+1672 / 1676 / 1680 -> sp+1688 / 1692 / 1696; VC -> VCm in EQ and CC7 (SlotInv.v). Statement
   kept on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b7.
Import ListNotations.
Open Scope Z_scope.

(* #76 with r_p = 0 and 0 <= unk: seqz s9 = 1, slti s8 = 0. *)
Lemma q04_c76 : forall uk, 0 <= uk <= 48 ->
  bv_eqb (v_sltiu (Z_to_bv 64 0) 1) (v_slti (Z_to_bv 64 uk) 0) = false.
Proof.
  intros uk Hu. unfold v_slti, zsig. rewrite ZBridge.zb_signed, (MState.unsigned_lit uk) by lia.
  replace (uk <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (uk <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  vm_compute. reflexivity.
Qed.

(* 0x13ba8 -> 0x13bd8: r_p = 0, s8 = a0 = unk >= 0. *)
Lemma q04_evt0 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (uk : Z),
    a0 = Z_to_bv 64 uk -> s8 = Z_to_bv 64 uk -> s9 = Z_to_bv 64 0 -> 0 <= uk <= 48 ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13bd8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13ba8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m uk -> -> -> Hu.
  step. b7_br false ltac:(rewrite bv_eqb_refl; reflexivity).
  step. step. step. b7_br false ltac:(exact (q04_c76 uk Hu)).
  step. b7_br true ltac:(vm_compute; reflexivity).
  apply evt_done. do 2 eexists. reflexivity.
Qed.

(* 0x13ba8 -> 0x13ca0: r_p = unk = -1, the three ports words still -7 (s2 = -7). *)
Lemma q04_evt1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 (-1) -> s9 = Z_to_bv 64 (-1) ->
    s2 = Z_to_bv 64 (-7) ->
    u32 m (spv + 1688) (-7) -> u32 m (spv + 1692) (-7) -> u32 m (spv + 1696) (-7) ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ca0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13ba8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv -> -> -> -> -> P0 P4 P8.
  pose proof (b7_rdn m _ _ P0) as R0. pose proof (b7_rdn m _ _ P4) as R4. pose proof (b7_rdn m _ _ P8) as R8.
  rewrite length_le4 in R0, R4, R8.
  step. b7_br false ltac:(rewrite bv_eqb_refl; reflexivity).
  step. step. step. b7_br false ltac:(vm_compute; reflexivity).
  step. b7_br false ltac:(vm_compute; reflexivity).
  step. step. b7_br false ltac:(vm_compute; reflexivity).
  step. step. b7_br false ltac:(vm_compute; reflexivity).
  step. step. b7_br false ltac:(vm_compute; reflexivity).
  step.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Section Q04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_Q04 : forall j, Hat B APIf ra (Inv_K13bd8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13ba8_at B APIf ra empty) j.
Proof.
  intros j H0 H1 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HQB & H24 & H10)).
  pose proof HQB as (HEQ & H25 & HPO & H1792).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  destruct (b7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  destruct (Z.eq_dec (t_rp (g_in g) j) 0) as [Er|Er].
  - destruct (b7_unk_rp0 _ _ Er) as (Hu & _).
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply q04_evt0 with (uk := t_unk (g_in g) j).
      * exact H10.
      * exact H24.
      * unfold rg in H25. rewrite Er in H25. exact H25.
      * exact Hu.
    + intros ms (a0' & a1' & ->). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros x _ O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a0' & a1' & HE). apply b7_MS_inj in HE as (ER & EPC & EM). subst R pc' m0'.
      apply H0. unfold Inv_K13bd8_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (MT0 : MT [] mem m') by exact (b7_mt [] mem _ m' HMI (munch_refl _ _) Hrel).
      split; [|split; [|split; [exact Er | lia]]].
      * apply (b7_QB g j phi regs mem regs' m' []); [exact HQB | exact MT0 | apply b7_DJE_nil | apply b7_DJQ_nil | |].
        -- unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
        -- rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * apply (b7_rg regs); [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact H24].
  - destruct (b7_unk_rpm _ _ Er) as (Er' & Eu).
    destruct (proj2 HPO Er) as (P0 & P4 & P8).
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply q04_evt1 with (spv := fsp g).
      * exact Hsp.
      * unfold rg in H10. rewrite Eu in H10. exact H10.
      * unfold rg in H24. rewrite Eu in H24. exact H24.
      * unfold rg in H25. rewrite Er' in H25. exact H25.
      * exact H2.
      * exact (b7_norm _ _ _ HMI P0).
      * exact (b7_norm _ _ _ HMI P4).
      * exact (b7_norm _ _ _ HMI P8).
    + intros ms (a0' & a1' & ->). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros x _ O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a0' & a1' & HE). apply b7_MS_inj in HE as (ER & EPC & EM). subst R pc' m0'.
      apply H1. unfold Inv_K13ca0_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (MT0 : MT [] mem m') by exact (b7_mt [] mem _ m' HMI (munch_refl _ _) Hrel).
      assert (HEQ' : EQ g j phi regs' m').
      { apply (b7_EQ g j phi regs mem regs' m' []); [exact HEQ | exact MT0 | apply b7_DJE_nil |].
        unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity. }
      destruct HEQ' as (HFT' & H7' & H2' & HVC' & HIFS' & _).
      split; [|exact H7']. split; [exact HFT'|]. split; [exact H2'|]. split; [exact HVC' | exact HIFS'].
Qed.

End Q04.
