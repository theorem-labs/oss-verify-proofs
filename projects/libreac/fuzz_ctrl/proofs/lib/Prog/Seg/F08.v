(* Segment F08 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x137d8, 0x137e8], K137d8 -> K137ec
   (the parse result is k (P1b), p.kind = k (P1c), then reac_ctrl_kind_name(k)). *)
(* libreac v1.9.0 (IDENTICAL-RENUMBER, segment table 5a S_F08): v1.8 [0x137cc, 0x137dc] K137cc -> K137e0; p.kind
   read at sp+1752 (v1.8 sp+1736), the frame 1920 -> 1936, reac_ctrl_kind_name 0x141a0 (contract; return 0x137ec).
   Statement kept on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv
  reac_ctrl_kind_name_c reac_ctrl_kind_name.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Open Scope Z_scope.

Lemma f08_c1 : forall k, negb (bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 k)) = false.
Proof. intros k. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma f08_c2 : forall k, 0 <= k <= 13 -> negb (bv_eqb (Z_to_bv 64 k) (sx32 (Z_to_bv 64 k))) = false.
Proof. intros k Hk. b5_cases13 k. Qed.

Lemma f08_evt : reac_ctrl_kind_name_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv k : Z),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 k -> s7 = Z_to_bv 64 k -> 0 <= k <= 13 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 1752)) 4 = Some (le4 (Z_to_bv 64 k)) -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR (Z_to_bv 64 0x137ec) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr k))
                       a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x137ec) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x137d8) fc None m (seg_rom rsegs)).
Proof.
  intros KN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv k Hsp Ha0 Hs7 Hk Hlo Hhi HR MI.
  subst sp a0 s7.
  step. if_false_by (f08_c1 k).
  step. step. if_false_by (f08_c2 k Hk).
  step. step.
  destruct (reac_ctrl_kind_name_in_image m MI) as (H1 & H2).
  eapply evt_cut; [eapply KN; [exact H1 | exact H2]|].
  intros ms' (a1' & E & _). subst ms'.
  rewrite (MState.unsigned_lit k) by lia.
  replace (ret_pc (Z_to_bv 64 0x137ec)) with (Z_to_bv 64 0x137ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists a1'. reflexivity.
Qed.

Section F08.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis KN : reac_ctrl_kind_name_contract.

Lemma seg_F08 : forall j, Hat B APIf ra (Inv_K137ec_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K137d8_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof HFB as (_ & (H23 & _ & _ & _ & (_ & _ & _ & HB))).
  pose proof (b5_k_range (g_in g) j) as Hk.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME, spk in *.
  eapply (b5_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply (f08_evt KN) with (spv := g_S g - 1936) (k := t_k (g_in g) j);
      [exact Hsp | exact H10 | exact H23 | exact Hk | lia | lia | | exact (mem_inv_normalize rsegs mem)].
    exact (b5_tB_read _ _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HB)).
  - intros ms (? & ->). do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|].
    split; [apply wmono_refl|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & HE). injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split].
    + apply (b5_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); b5_dj.
    + apply (b5_IFS_keep g j regs regs' mem m' _ HIFS HKP MU'); b5_dj.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End F08.
