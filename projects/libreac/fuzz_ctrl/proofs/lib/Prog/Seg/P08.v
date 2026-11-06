(* Segment P08 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13648, 0x1365c], K13648 -> K13660
   (#36: ports_unknown's -1; #37: the code byte at sp+1824 is 0; reac_ctrl_kind_name(14) = QMARK). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. S_P08 is IDENTICAL-RENUMBER (plain segment table
   v190-segment-table-plain.md (a working note, not in this delivery)): the same 6 instructions at pc +0x10 (the abort
   targets 0x13de4 -> 0x13e18 are not taken), `code` sp+1808 -> sp+1824 (0x13650 `lbu a0,1824(sp)`), frame 1920 ->
   1936. Statements: seg_P08 names K13648 / K13660 for K13638 / K13650 (SlotInv.v's renames). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

Lemma p08_evt : reac_ctrl_kind_name_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (-1) -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    b8 m (spv + 1824) 0 -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13660) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QMARK)
                       a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13660) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13648) fc None m (seg_rom rsegs)).
Proof.
  intros KN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv -> -> Hs0 Hs1 Hb MI.
  pose proof (b4_ld1 m _ _ Hb) as HR.
  step. step. if_false. step. step. if_false. step. step.
  destruct (reac_ctrl_kind_name_in_image m MI) as (H1 & H2).
  eapply evt_cut; [eapply KN; [exact H1 | exact H2]|].
  intros ms' (a1' & E & _). subst ms'.
  rewrite (MState.unsigned_lit 14) by lia.
  change (kind_name_addr 14) with QMARK.
  rewrite (MState.ret_pc_even 0x13660) by (first [reflexivity | lia]).
  apply evt_done. exists a1'. reflexivity.
Qed.

Section P08.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis KN : reac_ctrl_kind_name_contract.

Lemma seg_P08 : Hcut B APIf ra (Inv_K13660 B APIf ra empty) -> Hcut B APIf ra (Inv_K13648 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HP0 & HPZ & H10).
  pose proof (sl_fr_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (Hsp & _ & HS1 & HS2 & HMI).
  destruct HPZ as (HZ1 & _).
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME, SL_TOP in *.
  eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of. apply (p08_evt KN) with (spv := g_S g - 1936).
    + exact Hsp.
    + exact H10.
    + lia.
    + lia.
    + unfold b8. exact (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem HMI)) HZ1).
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & HE).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split].
    + apply (b4_P0_keep g regs regs' mem m' [] HP0 MU' I).
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + exact (bytes_at_transport rsegs [] mem m' _ _ HZ1 MU' I).
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End P08.
