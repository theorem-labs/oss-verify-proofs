(* Segment R18 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x135cc, 0x135ec], U135cc -> U135f0 (b = 5:
   k_5 = 11 (#20 not taken), reac_ctrl_identity_fragment(sp+120, Φ, n_5, sp+1824, sp+1752, sp+1688) = FIRST). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

Lemma r18_evt : reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n k : Z) (st g : list byte),
    sp = Z_to_bv 64 spv -> s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 n -> a0 = Z_to_bv 64 k ->
    k = 11 -> 65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> phi + 50 <= spv - 96 -> 50 <= n < 2 ^ 64 ->
    stk rsegs m (spv - 96) spv -> mem_inv rsegs m -> length g = 50%nat -> length st = 72%nat ->
    bytes_at rsegs m phi g -> rw_cells rsegs m (spv + 120) [CB 72 st] ->
    wr_at rsegs m (spv + 1824) 2 -> wr_at rsegs m (spv + 1752) 8 -> wr_at rsegs m (spv + 1688) 8 ->
    fcls n st g = FgFirst ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x135f0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x135f0) fc None m' (seg_rom rsegs) /\
         munch [(spv + 120, spv + 192); (spv - 96, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 120) (fg_first st g))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x135cc) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n k st g -> -> -> -> Hk Hsp0 Hsp H16 Hph0 Hph Hn ST MI Lg Ls HG HF WA WP WN Hc.
  subst k.
  step. step. if_false.
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply (u2_frag_call FRAG) with (spv := spv) (phi := phi) (n := n) (st := st) (g := g) (c := FgFirst);
      first [ reflexivity | eassumption | lia ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & HM).
  subst ms'. cbn [fg_ret fg_fp fg_mem] in *.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM | exact HM].
Qed.

Section R18.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FRAG : reac_ctrl_identity_fragment_contract.

Lemma seg_R18 : Hcut B APIf ra (Inv_U135f0 B APIf ra empty) -> Hcut B APIf ra (Inv_U135cc B APIf ra empty).
Proof.
  intros H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & H10).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
  pose proof HRB as (Hb6 & _ & _ & _ & _ & H9 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (u2_hb B APIf ra empty FF g phi (rnb g 5) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  destruct (u2_RS_len (g_in g) 5) as (LI & LF).
  unfold rnb, rFb, rgb in *.
  destruct (u2_rtn (g_in g) (Z.of_nat 5) Hnz) as (_ & Hnb & HL).
  destruct (u2_RS_56 (g_in g) 5 ltac:(lia) Hnz) as (E1 & E2).
  change (Z.of_nat 5) with 5 in *.
  pose proof (u2_rtm_first (g_in g) Hnz) as Hfi.
  pose proof (u2_rtm_k11 (g_in g) 5 (or_introl eq_refl) Hnz) as Hk.
  unfold fg_st in E2. rewrite Hfi in E2. cbn [fg_next] in E2.
  unfold fg_id, fg_rf in E1. rewrite Hfi in E1. cbn [fg_ret Z.eqb] in E1.
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  unfold RIDB, FGB, spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (ST96 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 96) (g_S g - 1936))
    by (apply (u2_stk_sub _ _ _ _ _ ST); lia).
  assert (HG : bytes_at rsegs (normalize rsegs mem) phi (rt_g (g_in g) 5)).
  { apply u2_fr50_at; [exact (bytes_at_normalize rsegs mem phi _ HMI HF) | lia]. }
  pose proof (u2_rw_at _ _ _ (g_S g - 1936 + 120) (RFG (g_in g) 5) ST ltac:(lia) ltac:(rewrite LF; lia)
                (bytes_at_normalize rsegs mem _ _ HMI HFG)) as HFw.
  rewrite LF in HFw.
  pose proof (u2_wr_of_stk _ _ _ (g_S g - 1936 + 1824) 2 ST ltac:(lia) ltac:(lia) ltac:(lia)) as WA.
  pose proof (u2_wr_of_stk _ _ _ (g_S g - 1936 + 1752) 8 ST ltac:(lia) ltac:(lia) ltac:(lia)) as WP.
  pose proof (u2_wr_of_stk _ _ _ (g_S g - 1936 + 1688) 8 ST ltac:(lia) ltac:(lia) ltac:(lia)) as WN.
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r18_evt FRAG) with (spv := g_S g - 1936) (phi := phi) (n := rt_n (g_in g) 5) (k := rt_k (g_in g) 5)
      (st := RFG (g_in g) 5) (g := rt_g (g_in g) 5);
      [exact Hsp | exact H20 | exact H21 | exact H10 | exact Hk | lia | lia | exact H16
      | lia | lia | lia | exact ST96 | exact (mem_inv_normalize rsegs mem) | apply fr50_length | exact LF
      | exact HG | exact HFw | exact WA | exact WP | exact WN | exact Hfi].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    eexists. split; [exact MU|]. split; [exact WM|].
    intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HF').
    injection HE; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (KR : u2_ks regs' regs).
    { unfold u2_ks, u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    split.
    { eapply (u2_RFx_new g 5 _ _ _ _ phi regs regs' mem m'' m' _ HMI MU Hrel); [| | | exact KR | exact HRF | |].
      - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
      - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
      - cbn [disjoint_from]. unfold rnb. lia.
      - unfold RIDB, spk, fsp, SLOT_FRAME. rewrite E1. apply (u2_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HID].
        rewrite LI. cbn [disjoint_from]. lia.
      - unfold FGB, spk, fsp, SLOT_FRAME. rewrite E2. exact (u2_out _ _ _ _ Hrel HF'). }
    unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End R18.
