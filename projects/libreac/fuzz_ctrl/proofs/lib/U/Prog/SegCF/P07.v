(* Segment P07 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13774, 0x13780], U13774 -> U13784
   (#35: ports_parse's -1; reac_ports_unknown(0, sp+1824) = -1 and writes 0 to the code byte sp+1824). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u3.
Import ListNotations.
Open Scope Z_scope.

Lemma p07_nok : forall bs, pu_ok 0 bs = false.
Proof. intros bs. reflexivity. Qed.

Lemma p07_evt : reac_ports_unknown_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (-1) -> s0 = Z_to_bv 64 (-1) ->
    0 <= spv -> spv + 1936 < 2 ^ 64 ->
    Step.rw_cells rsegs m (spv + 1824) [Cells.CB 1 junk] ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13784) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13784) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1824, spv + 1825)] m m' /\ wmono rsegs m m' /\ b8 m' (spv + 1824) 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13774) fc None m (seg_rom rsegs)).
Proof.
  intros PU ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk -> -> -> Hs0 Hs1 HC.
  destruct HC as [_ HW]. cbn [Cells.cells_size Cells.csize Nat.add] in HW.
  step. if_false. step. step. step.
  eapply evt_cut.
  { eapply PU with (p := 0) (c := spv + 1824) (bs := repeat (Z_to_bv 8 0) 20).
    - reflexivity.
    - rewrite MState.unsigned_lit by lia. lia.
    - intros Hp. exfalso. apply Hp. reflexivity.
    - intros _. split; [exact HW | intros Hp; exfalso; apply Hp; reflexivity]. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & m' & -> & MUc & WMc & _ & _ & Hc).
  rewrite p07_nok in Hc |- *.
  replace (spv + 1824 =? 0) with false in MUc by (symmetry; apply Z.eqb_neq; lia).
  replace (spv + 1824 + 1) with (spv + 1825) in MUc by lia.
  rewrite (MState.ret_pc_even 0x13784) by (first [reflexivity | lia]).
  apply evt_done. eexists _, _, _, _, _, _, m'. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|].
  apply Hc. lia.
Qed.

Section P07.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PU : reac_ports_unknown_contract.

Lemma seg_P07 : Hcut B APIf ra (Inv_U13784 B APIf ra empty) -> Hcut B APIf ra (Inv_U13774 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HP0 & HPZ & H8 & H10).
  pose proof (sl_fr_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (Hsp & _ & HS1 & HS2 & _).
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HFR) as ST.
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME, SL_TOP in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1824) 1 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  set (W := [(g_S g - 1936 + 1824, g_S g - 1936 + 1825)]).
  eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (u3_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
    apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  - rewrite sl_mkR_of. apply (p07_evt PU) with (spv := g_S g - 1936) (junk := junk).
    + exact Hsp.
    + exact H10.
    + exact H8.
    + lia.
    + lia.
    + exact HC.
  - intros ms (? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & Hb).
    injection HE; intros; subst.
    destruct HPZ as (_ & HZ2).
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split; [split|]].
    + apply (u3_P0_keep g regs regs' mem m' W HP0 MU').
      * unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold b8, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) Hb).
    + apply (bytes_at_transport rsegs W mem m' _ _ HZ2 MU').
      rewrite repeat_length. unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End P07.
