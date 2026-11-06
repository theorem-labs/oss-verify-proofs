(* Segment Q02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13b80, 0x13b94], K13b80 -> K13b98 (call
   reac_ports_unknown at 0x13b94 with c = sp+1792): s9 = r_p; first = 0xee is stored, then PU C1.2, C1.3 write the
   byte first(blk) (0 when not decl) and return unk. *)
(* libreac v1.9.0 (IDENTICAL-RENUMBER, segment table 5a S_Q02): v1.8 [0x13b50, 0x13b64] K13b50 -> K13b68; the
   check_ports `first` byte sp+1776 -> sp+1792, the frame 1920 -> 1936; VC -> VCm in EQ (SlotInv.v). Statement kept
   on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b7.
Import ListNotations.
Open Scope Z_scope.

(* 0x13b80 -> 0x13b98 with sp = spv, a0 = r_p, s6 = blk = Φ + 18, bs = blk's 20 bytes. *)
Lemma q02_evt : reac_ports_unknown_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi rp uk fb : Z) (bs junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 rp -> s6 = Z_to_bv 64 (phi + 18) ->
    0 <= spv -> spv + 1936 < 2 ^ 64 -> 0 < phi -> phi + 50 <= spv ->
    Step.rw_cells rsegs m (spv + 1792) [Cells.CB 1 junk] ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    uk = (if RcPorts.pu_decl bs then 4 * RcPorts.pu_nunk bs 12 else -1) ->
    fb = (if RcPorts.pu_decl bs then RcPorts.pu_first bs 12 else 0) ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' s9' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 uk)
                       a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9' s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13b98) fc None m' (seg_rom rsegs) /\
         s9' = Z_to_bv 64 rp /\
         munch [(spv + 1792, spv + 1793)] m m' /\ wmono rsegs m m' /\
         b8 m' (spv + 1792) fb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b80) fc None m (seg_rom rsegs)).
Proof.
  intros PU ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi rp uk fb bs junk -> -> -> Hs0 Hs1 Hp1 Hp2 HC Hl HB Huk Hfb.
  pose proof (Step.rw_cells_store_ok rsegs m (spv + 1792) [Cells.CB 1 junk] 0 (Cells.CB 1 junk) 1 HC
                eq_refl eq_refl) as HS.
  destruct HC as [_ HW]. cbn [Cells.cells_size Cells.csize Nat.add] in HW.
  pose proof (munch_refl [(spv + 1792, spv + 1793)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. store_done. step. step. step.
  eapply evt_cut.
  { eapply PU with (p := phi + 18) (c := spv + 1792) (bs := bs).
    - rewrite MState.unsigned_lit by lia. lia.
    - rewrite MState.unsigned_lit by lia. lia.
    - intros _. split; [lia | split; [exact Hl | exact HB]].
    - intros _. split; [exact HW | intros _; lia]. }
  intros ms' (a2' & a3' & a4' & a5' & m' & -> & MUc & WMc & _ & _ & Hc).
  rewrite (MState.ret_pc_even 0x13b98) by (first [reflexivity | lia]).
  assert (Eok : RcPorts.pu_ok (phi + 18) bs = RcPorts.pu_decl bs).
  { unfold RcPorts.pu_ok. replace (phi + 18 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite Eok in Hc |- *. rewrite <- Huk. rewrite <- Hfb in Hc.
  replace (spv + 1792 =? 0) with false in MUc by (symmetry; apply Z.eqb_neq; lia).
  apply evt_done. eexists _, _, _, _, _, _, _, m'. split; [reflexivity|].
  split; [first [reflexivity | f_equal; lia]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUc]]|].
  { unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  split; [exact (wmono_trans _ _ _ _ WM WMc)|].
  apply Hc. lia.
Qed.

Section Q02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PU : reac_ports_unknown_contract.

Lemma seg_Q02 : forall j, Hat B APIf ra (Inv_K13b98_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13b80_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEQ & H10 & HPO)).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (Hj & H26 & HFC & H21 & Hphi & HOUR & HM7).
  pose proof HVC as (H22 & H24 & HB).
  pose proof (b7_big_8819 _ _ H88) as Hbig.
  destruct (b7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  destruct (b7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  pose proof alloc_ceiling_value as Hac.
  assert (H22' : rg regs 22 (phi + 18)).
  { unfold t_big in H22. rewrite (proj2 (Z.leb_le _ _) Hbig) in H22. exact H22. }
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HFR) as ST.
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1792) 1 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  remember (t_unk (g_in g) j) as UK eqn:EUK. remember (t_first (g_in g) j) as FB eqn:EFB.
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (q02_evt PU) with (spv := g_S g - 1936) (phi := phi) (rp := t_rp (g_in g) j) (uk := UK) (fb := FB)
      (bs := t_pbs (g_in g) j) (junk := junk).
    + exact Hsp.
    + exact H10.
    + exact H22'.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact HC.
    + apply b7_pbs_length.
    + apply b7_pbs_bytes. apply b7_norm; [exact HMI|]. apply b7_g_bytes; [exact Hphi | exact Hbig].
    + rewrite EUK. unfold t_unk. reflexivity.
    + rewrite EFB. unfold t_first. reflexivity.
  - intros ms (ra' & a1' & a2' & a3' & a4' & a5' & s9' & m' & -> & _ & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 + 1792, g_S g - 1936 + 1793)]. split; [exact MU|]. split; [exact WM|].
    intros x Hx O. apply (sl_fp1 g (g_S g - 1936 + 1792) (g_S g - 1936 + 1793) x);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & s9' & m'' & HE & E9 & MU & WM & H1792).
    apply b7_MS_inj in HE as (ER & EPC & EM). subst R pc' m0'.
    apply H. unfold Inv_K13b98_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    set (W := [(g_S g - 1936 + 1792, g_S g - 1936 + 1793)]) in *.
    assert (MTW : MT W mem m') by exact (b7_mt W mem _ m' HMI MU Hrel).
    split; [|rewrite <- EUK; unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity].
    split; [|split; [|split]].
    + apply (b7_EQ g j phi regs mem regs' m' W); [exact HEQ | exact MTW | |].
      * intros a n Hn Ha. unfold W. cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME in Ha. split; [lia | exact I].
      * unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). first [exact E9 | reflexivity].
    + apply (b7_PORTS g j mem m' W HPO MTW).
      unfold DJP, W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. repeat split; lia.
    + rewrite <- EFB. exact (b7_back _ _ _ _ Hrel H1792).
Qed.

End Q02.
