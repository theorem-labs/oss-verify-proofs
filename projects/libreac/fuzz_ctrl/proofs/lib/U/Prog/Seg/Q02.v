(* Segment Q02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13dc0, 0x13dd4], U13dcc (v1.9 pc
   0x13dc0) -> U13de4 (v1.9 pc 0x13dd8) (s11 = r_p; byte 0xee at sp+1792; call reac_ports_unknown(blk, sp+1792) at
   0x13dd4 with blk = s8: a0 = unk, sp+1792 = first(blk), C22 C1.2, C1.3). v1.8: r_p s10, blk s7. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u7.
Import ListNotations.
Open Scope Z_scope.

Lemma q02_le1 : le1 (Z_to_bv 64 (-18)) = [Z_to_bv 8 0xee].
Proof. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* 0x13dc0 -> 0x13dd8: mv s11,a0; li a0,-18; sb a0,1792(sp); addi a1,sp,1792; mv a0,s8; jal reac_ports_unknown. *)
Lemma q02_evt : reac_ports_unknown_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv blk : Z) (bs j1 : list byte),
    sp = Z_to_bv 64 spv -> s8 = Z_to_bv 64 blk ->
    0 < blk -> blk + 20 <= spv -> spv + 1936 <= 2 ^ 64 ->
    length bs = 20%nat -> bytes_at rsegs m blk bs ->
    rw_cells rsegs m (spv + 1792) [Cells.CB 1 j1] ->
    evt rsegs
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' s11' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13dd8) fc None m' (seg_rom rsegs) /\
         a0' = Z_to_bv 64 (if RcPorts.pu_decl bs then 4 * RcPorts.pu_nunk bs 12 else -1) /\
         s11' = a0 /\ munch [(spv + 1792, spv + 1793)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1792) [Z_to_bv 8 (if RcPorts.pu_decl bs then RcPorts.pu_first bs 12 else 0)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13dc0) fc None m (seg_rom rsegs)).
Proof.
  intros PU ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv blk bs j1 -> -> Hb0 Hbs Hsp Hl HB HC.
  pose proof (proj2 HC) as HW. change (Z.of_nat (Cells.cells_size [Cells.CB 1 j1])) with 1 in HW.
  pose proof (munch_refl [(spv + 1792, spv + 1793)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step.
  rewrite q02_le1. mem_after_store.
  step. step. step.
  eapply evt_cut.
  { eapply PU with (p := blk) (c := spv + 1792) (bs := bs).
    - u7_zeq.
    - u7_zeq.
    - intros _. split; [lia|]. split; [exact Hl | exact HB].
    - intros _. split; [exact HW | intros _; lia]. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & m' & -> & MUc & WMc & _ & _ & HF).
  rewrite (MState.ret_pc_even 0x13dd8) by (first [reflexivity | lia]).
  unfold RcPorts.pu_ok in HF |- *.
  replace (blk =? 0) with false in HF |- * by (symmetry; apply Z.eqb_neq; lia).
  replace (spv + 1792 =? 0) with false in MUc by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb andb] in HF, MUc |- *.
  apply evt_done. do 10 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [u7_weq|].
  split.
  { apply (u7_munch_join _ _ _ _ _ MU MUc). intros x Hx. cbn [Frame.outside] in *. destruct Hx as [Hx _].
    split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM WMc)|].
  apply HF. lia.
Qed.

Section Q02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PU : reac_ports_unknown_contract.

Lemma seg_Q02 : forall j, Hat B APIf ra (Inv_U13dd8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13dc0_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEQ & H10 & HPO)).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (HLK & HFC & H23 & Hphi & H18).
  pose proof HVC as (H24 & H16 & HB).
  pose proof (u7_big_8819 _ _ H88) as Hbig.
  rewrite (u7_big_true _ _ H88) in H24.
  destruct (u7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  destruct (u7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  pose proof alloc_ceiling_value as Hac.
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK in ST.
  destruct (sl_rw_of_stk _ _ _ (fsp g + 1792) 1 ST ltac:(unfold fsp, SLOT_FRAME; lia)
              ltac:(unfold fsp, SLOT_FRAME; lia)) as (j1 & HC).
  eapply (u7_mid B APIf ra empty FF g _ L A regs mem md _ [(fsp g + 1792, fsp g + 1793)]);
    [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (u7_fp g _ x _ Hx O).
    repeat (apply Forall_cons; [cbn [fst snd]; unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME; lia|]). apply Forall_nil.
  - rewrite sl_mkR_of.
    apply (q02_evt PU) with (spv := fsp g) (blk := phi + 18) (bs := t_pbs (g_in g) j) (j1 := j1).
    + exact Hsp.
    + exact H24.
    + lia.
    + unfold fsp, SLOT_FRAME. lia.
    + unfold fsp, SLOT_FRAME. lia.
    + apply u7_pbs_length.
    + apply u7_norm; [exact HMI|]. apply u7_pbs_bytes. apply u7_g_bytes; [exact Hphi | exact Hbig].
    + exact HC.
  - intros ms (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & s11' & m' & -> & _ & _ & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & s11' & m'' & HE & E0 & E11 & _ & _ & HF).
    destruct (u7_MS_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & Epc & Em). subst R pc' m0' s11'.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (DJ : DJE g j phi [(fsp g + 1792, fsp g + 1793)]).
    { intros a n Hn Ha. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME in *. lia. }
    pose proof (u7_mt _ _ _ MU') as MT.
    split; [|unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); transitivity a0'; [reflexivity|]; rewrite E0;
             unfold t_unk; reflexivity].
    split; [apply (u7_EQ g j phi regs mem regs' m' _ HEQ MT DJ);
            unfold EQR; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split; reflexivity|].
    split; [unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); exact H10|].
    split.
    + apply (u7_PORTS3 g j mem m' _ HPO MT); cbn [disjoint_from]; unfold spk, fsp, SLOT_FRAME;
        (split; [lia | exact I]).
    + exact (u7_back _ _ _ _ Hrel HF).
Qed.

End Q02.
