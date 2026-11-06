(* Segment Q03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13de4, 0x13df0], U13de4 -> U13df4 (s9 = unk; call
   reac_ports_unknown(blk, NULL) at 0x13df0: a0 = unk again, no byte written, C22 C1.5). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u7.
Import ListNotations.
Open Scope Z_scope.

(* 0x13dd8 -> 0x13de8: mv s10,a0; mv a0,s8; li a1,0; jal reac_ports_unknown (C22 C1.2, C1.3 with c = 0). v1.8:
   unk s9, blk s7. *)
Lemma q03_evt : reac_ports_unknown_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (blk : Z) (bs : list byte),
    s8 = Z_to_bv 64 blk -> 0 < blk -> blk + 20 <= 2 ^ 64 -> length bs = 20%nat -> bytes_at rsegs m blk bs ->
    evt rsegs
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' s10' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10' s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13de8) fc None m' (seg_rom rsegs) /\
         a0' = Z_to_bv 64 (if RcPorts.pu_decl bs then 4 * RcPorts.pu_nunk bs 12 else -1) /\
         s10' = a0 /\ munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13dd8) fc None m (seg_rom rsegs)).
Proof.
  intros PU ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m blk bs -> Hb0 Hb20 Hl HB.
  step. step. step. step.
  eapply evt_cut.
  { eapply PU with (p := blk) (c := 0) (bs := bs).
    - u7_zeq.
    - u7_zeq.
    - intros _. split; [lia|]. split; [exact Hl | exact HB].
    - intros Hc. exfalso. apply Hc. reflexivity. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & m' & -> & MU & WM & _).
  rewrite (MState.ret_pc_even 0x13de8) by (first [reflexivity | lia]).
  apply evt_done. do 10 eexists. split; [reflexivity|].
  split; [unfold RcPorts.pu_ok; replace (blk =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
          cbn [negb andb]; reflexivity|].
  split; [u7_weq|]. split; [exact MU | exact WM].
Qed.

Section Q03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PU : reac_ports_unknown_contract.

Lemma seg_Q03 : forall j, Hat B APIf ra (Inv_U13de8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13dd8_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HQB & H10)).
  pose proof HQB as (HEQ & H27 & HPO & H1792).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (HLK & HFC & H23 & Hphi & H18).
  pose proof HVC as (H24 & H16 & HB).
  pose proof (u7_big_8819 _ _ H88) as Hbig.
  rewrite (u7_big_true _ _ H88) in H24.
  destruct (u7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  destruct (u7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  pose proof alloc_ceiling_value as Hac.
  eapply (u7_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x _ O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of. apply (q03_evt PU) with (blk := phi + 18) (bs := t_pbs (g_in g) j).
    + exact H24.
    + lia.
    + lia.
    + apply u7_pbs_length.
    + apply u7_norm; [exact HMI|]. apply u7_pbs_bytes. apply u7_g_bytes; [exact Hphi | exact Hbig].
  - intros ms (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & s10' & m' & -> & _ & _ & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & s10' & m'' & HE & E10 & E10' & _ & _).
    destruct (u7_MS_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & Epc & Em). subst R pc' m0' s10'.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split].
    + apply (u7_QB g j phi regs mem regs' m' [] HQB (u7_mt _ _ _ MU') (u7_DJE_nil g j phi) (u7_DJQ_nil g)).
      * unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). exact H10.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). transitivity a0'; [reflexivity|]. rewrite E10. unfold t_unk.
      reflexivity.
Qed.

End Q03.
