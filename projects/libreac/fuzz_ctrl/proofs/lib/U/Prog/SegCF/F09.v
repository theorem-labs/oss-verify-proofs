(* Segment F09 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13978, 0x13980], U13978 -> U13984
   (kind_name(k) is not NULL (P1c), then reac_ctrl_kind_name(k) (0x1477c) again; k in s9, v1.8 s8). Port of the
   plain seg_F09 (a working branch lib/Prog/Seg/F09.v). KIND_NAME bytes: Section Hypothesis KNB (u1's image
   fact). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF
  reac_ctrl_kind_name_c reac_ctrl_kind_name.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u4.
Import ListNotations.
Open Scope Z_scope.

Lemma f09_c1 : forall k, 0 <= k <= 13 -> bv_eqb (Z_to_bv 64 (kind_name_addr k)) (Z_to_bv 64 0) = false.
Proof. intros k Hk. u4_cases13 k. Qed.

Lemma f09_evt : reac_ctrl_kind_name_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : Z),
    a0 = Z_to_bv 64 (kind_name_addr k) -> s9 = Z_to_bv 64 k -> 0 <= k <= 13 -> mem_inv rsegs m ->
    bytes_at rsegs m KIND_NAME kind_name_bytes ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13984) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr k))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13984) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13978) fc None m (seg_rom rsegs)).
Proof.
  intros KN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m k Ha0 Hs9 Hk MI HKB.
  subst a0 s9.
  step. if_false_by (f09_c1 k Hk).
  step. step.
  pose proof (reac_ctrl_kind_name_strings_in_image m MI) as H2.
  eapply evt_cut; [eapply KN; [exact HKB | exact H2]|].
  intros ms' (a1' & a2' & a3' & E & _). subst ms'.
  rewrite (MState.unsigned_lit k) by lia.
  replace (ret_pc (Z_to_bv 64 0x13984)) with (Z_to_bv 64 0x13984) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists a1', a2', a3'. reflexivity.
Qed.

Section F09.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis KN : reac_ctrl_kind_name_contract.
(* KIND_NAME's 112 bytes in GNU_RELRO: the form of u1_kind_name_bytes (Seg/Tac_u1.v). *)
Hypothesis KNB : forall mem, relro B mem -> bytes_at rsegs mem KIND_NAME kind_name_bytes.

Lemma seg_F09 : forall j : nat, Hat B APIf ra (Inv_U13984_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13978_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMI).
  pose proof HFB as (_ & (H25 & _)).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & Hrelro & _).
  pose proof (KNB mem Hrelro) as HKB.
  pose proof (u4_k_range (g_in g) j) as Hk.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply (f09_evt KN) with (k := t_k (g_in g) j);
      [exact H10 | exact H25 | exact Hk | exact (mem_inv_normalize rsegs mem) |
       exact (bytes_at_normalize rsegs mem _ _ HMI HKB)].
  - intros ms (? & ? & ? & ->). do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|].
    split; [apply wmono_refl|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & HE). injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split].
    + apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj.
    + apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End F09.
