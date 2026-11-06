(* Segment R14 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13564, 0x1357c], U13564 -> U13580 (b = 0:
   #14 not taken (match = m), T06 not taken (Φ < 2^64 - 18 by HBR), `addi s5,s4,18`,
   reac_ports_parse(Φ + 18, sp+1688) = 0). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

Lemma r14_evt : reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi mr : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 mr -> a0 = Z_to_bv 64 mr -> s4 = Z_to_bv 64 phi ->
    65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 -> 0 < phi -> phi + 50 <= spv ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs -> wr_at rsegs m (spv + 1688) 12 ->
    ports_ok (phi + 18) (spv + 1688) bs = true ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13580) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 (Z_to_bv 64 (phi + 18)) s6 s7 s8 s9 s10 s11
                       t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13580) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1688, spv + 1700)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1688) (le4 (Z_to_bv 64 (4 * n_in bs))) /\
         bytes_at rsegs m' (spv + 1692) (le4 (Z_to_bv 64 (4 * n_out bs))) /\
         bytes_at rsegs m' (spv + 1696) (le4 (Z_to_bv 64 (16 * bt bs 7))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13564) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi mr bs -> -> -> -> Hsp0 Hsp H16 Hph0 Hph Hl HB HW Hok.
  step. if_false_by (u2_neqb_refl (Z_to_bv 64 mr)).
  step. step. u2_if_false.
  step. step. step. step.
  eapply evt_cut.
  { eapply PP with (p := phi + 18) (q := spv + 1688) (bs := bs);
      first [ reflexivity | lia | intros _ _; split; [exact Hl | exact HB]
            | intros _ _; split; [apply u2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
              split; [exact HW | lia] ]. }
  intros ms' PO. unfold reac_ports_parse_post in PO. rewrite Hok in PO.
  destruct PO as (t0' & t1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & HI & HO & HE & MU & WM & _).
  subst ms'.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [exact HI|].
  replace (spv + 1692) with (spv + 1688 + 4) by lia. replace (spv + 1696) with (spv + 1688 + 8) by lia.
  split; [exact HO | exact HE].
Qed.

Section R14.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PP : reac_ports_parse_contract.

Lemma seg_R14 : Hcut B APIf ra (Inv_U13580 B APIf ra empty) -> Hcut B APIf ra (Inv_U13564 B APIf ra empty).
Proof.
  intros H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & Hk & Hsum & H10).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
  pose proof HRB as (Hb6 & _ & _ & (H8 & _) & _ & H9 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (u2_hb B APIf ra empty FF g phi (rnb g 0) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  destruct (u2_RS_len (g_in g) 0) as (LI & LF).
  unfold rnb, rFb, rgb in *.
  destruct (u2_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HL).
  change (Z.of_nat 0) with 0 in *.
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (HG : bytes_at rsegs (normalize rsegs mem) phi (rt_g (g_in g) 0)).
  { apply u2_fr50_at; [exact (bytes_at_normalize rsegs mem phi _ HMI HF) | lia]. }
  assert (L50 : length (rt_g (g_in g) 0) = 50%nat) by apply fr50_length.
  assert (HB : bytes_at rsegs (normalize rsegs mem) (phi + 18) (rt_pbs (g_in g))).
  { unfold rt_pbs. apply u2_bsl_at; [exact HG | lia | lia | rewrite L50; lia]. }
  assert (Hl : length (rt_pbs (g_in g)) = 20%nat).
  { unfold rt_pbs. rewrite u2_bsl_len; [reflexivity | lia | lia | rewrite L50; lia]. }
  pose proof (u2_wr_of_stk _ _ _ (g_S g - 1936 + 1688) 12 ST ltac:(lia) ltac:(lia) ltac:(lia)) as HW.
  pose proof (u2_ports_ok (phi + 18) (g_S g - 1936 + 1688) (rt_pbs (g_in g)) ltac:(lia) ltac:(lia)
                (u2_rtm_decl (g_in g))) as Hok.
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r14_evt PP) with (spv := g_S g - 1936) (phi := phi) (mr := mrow (g_in g)) (bs := rt_pbs (g_in g));
      [exact Hsp | exact H8 | exact H10 | exact H20 | lia | lia | exact H16 | lia | lia | exact Hl | exact HB
      | exact HW | exact Hok].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    eexists. split; [exact MU|]. split; [exact WM|].
    intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HI & HO & HE7).
    injection HE; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (KR : u2_kr regs' regs).
    { unfold u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    split.
    { apply (u2_RFb_keep g 0 _ _ phi regs regs' mem m'' m' _ HMI MU Hrel LI LF); [| | exact KR | | exact (proj1 HRF)].
      - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
      - cbn [disjoint_from]. unfold rnb. change (Z.of_nat 0) with 0. lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    unfold rg, u32, spk, fsp, SLOT_FRAME in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact (u2_out _ _ _ _ Hrel HI)|]. split; [exact (u2_out _ _ _ _ Hrel HO)|].
    exact (u2_out _ _ _ _ Hrel HE7).
Qed.

End R14.
