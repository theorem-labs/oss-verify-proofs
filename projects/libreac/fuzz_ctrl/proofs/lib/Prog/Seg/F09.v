(* Segment F09 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x137ec, 0x137f4], K137ec -> K137f8
   (kind_name(k) is not NULL (P1c), then reac_ctrl_kind_name(k) again). *)
(* libreac v1.9.0 (IDENTICAL, segment table 5a S_F09): v1.8 [0x137e0, 0x137e8] K137e0 -> K137ec, pcs only
   (reac_ctrl_kind_name 0x141a0, contract; return 0x137f8). Statement kept on the renamed cuts. rule 24: no function
   proved. *)
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

Lemma f09_c1 : forall k, 0 <= k <= 13 -> bv_eqb (Z_to_bv 64 (kind_name_addr k)) (Z_to_bv 64 0) = false.
Proof. intros k Hk. b5_cases13 k. Qed.

Lemma f09_evt : reac_ctrl_kind_name_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : Z),
    a0 = Z_to_bv 64 (kind_name_addr k) -> s7 = Z_to_bv 64 k -> 0 <= k <= 13 -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR (Z_to_bv 64 0x137f8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr k))
                       a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x137f8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x137ec) fc None m (seg_rom rsegs)).
Proof.
  intros KN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m k Ha0 Hs7 Hk MI.
  subst a0 s7.
  step. if_false_by (f09_c1 k Hk).
  step. step.
  destruct (reac_ctrl_kind_name_in_image m MI) as (H1 & H2).
  eapply evt_cut; [eapply KN; [exact H1 | exact H2]|].
  intros ms' (a1' & E & _). subst ms'.
  rewrite (MState.unsigned_lit k) by lia.
  replace (ret_pc (Z_to_bv 64 0x137f8)) with (Z_to_bv 64 0x137f8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists a1'. reflexivity.
Qed.

Section F09.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis KN : reac_ctrl_kind_name_contract.

Lemma seg_F09 : forall j, Hat B APIf ra (Inv_K137f8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K137ec_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & H10).
  pose proof HFB as (_ & (H23 & _)).
  pose proof (b5_k_range (g_in g) j) as Hk.
  eapply (b5_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply (f09_evt KN) with (k := t_k (g_in g) j);
      [exact H10 | exact H23 | exact Hk | exact (mem_inv_normalize rsegs mem)].
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

End F09.
