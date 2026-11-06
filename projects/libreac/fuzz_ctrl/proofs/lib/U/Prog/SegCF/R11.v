(* Segment R11 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x134ac, 0x134dc], U134ac (b = 5, 6) -> U135cc
   (b = 5) or U134e0 (b = 6: k_6 = 11 (#9 not taken), then reac_ctrl_identity_fragment(sp+120, Φ, n_6, sp+1824,
   sp+1752, sp+1688) = CLOSE); 0x134b8 (b != 6 -> U135f8) is not taken (b <= 6). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

(* b = 5: beq b, 5 to 0x135cc. *)
Lemma r11_five :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s1 = Z_to_bv 64 5 ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x135cc) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x134ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step. step. if_true. apply evt_done. eexists. reflexivity.
Qed.

(* b = 6: k_6 = 11, then the fragment call, which closes the record. *)
Lemma r11_six : reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n k : Z) (st g : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 6 -> s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 n -> a0 = Z_to_bv 64 k ->
    k = 11 -> 65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> phi + 50 <= spv - 96 -> 50 <= n < 2 ^ 64 ->
    stk rsegs m (spv - 96) spv -> mem_inv rsegs m -> length g = 50%nat -> length st = 72%nat ->
    bytes_at rsegs m phi g -> rw_cells rsegs m (spv + 120) [CB 72 st] ->
    wr_at rsegs m (spv + 1824) 2 -> wr_at rsegs m (spv + 1752) 8 -> wr_at rsegs m (spv + 1688) 8 ->
    fcls n st g = FgClose ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x134e0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x134e0) fc None m' (seg_rom rsegs) /\
         munch [(spv + 120, spv + 192); (spv + 1824, spv + 1826); (spv + 1752, spv + 1760);
                (spv + 1688, spv + 1696); (spv - 96, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 120) (fg_clear (fg_join st g)) /\
         bytes_at rsegs m' (spv + 1824) (le2 (Z_to_bv 64 (fg_addr st g))) /\
         bytes_at rsegs m' (spv + 1752) (le8 (Z_to_bv 64 (spv + 139))) /\
         bytes_at rsegs m' (spv + 1688) (le8 (Z_to_bv 64 (fg_T st g - 13))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x134ac) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n k st g -> -> -> -> -> Hk Hsp0 Hsp H16 Hph0 Hph Hn ST MI Lg Ls HG HF WA WP WN Hc.
  subst k.
  step. step. if_false. step. step. if_false. step. step. if_false.
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply (u2_frag_call FRAG) with (spv := spv) (phi := phi) (n := n) (st := st) (g := g) (c := FgClose);
      first [ reflexivity | eassumption | lia ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & HM).
  subst ms'. cbn [fg_ret fg_fp fg_mem] in *.
  destruct HM as (H1 & H2 & H3 & H4).
  replace (spv + 120 + 19) with (spv + 139) in H3 by lia.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Section R11.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FRAG : reac_ctrl_identity_fragment_contract.

Lemma seg_R11 : forall b : nat, (b = 6%nat -> Hcut B APIf ra (Inv_U134e0 B APIf ra empty)) ->
  (b = 5%nat -> Hcut B APIf ra (Inv_U135cc B APIf ra empty)) ->
  Hat B APIf ra (Inv_U135f8_at B APIf ra empty) b -> Hat B APIf ra (Inv_U134ac_at B APIf ra empty) b.
Proof.
  intros b H6 H5 _ g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & Hb & H10).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
  pose proof HRB as (Hb6 & _ & _ & _ & _ & H9 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (u2_hb B APIf ra empty FF g phi (rnb g b) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  destruct (u2_RS_len (g_in g) b) as (LI & LF).
  unfold rnb, rFb, rgb in *.
  destruct (u2_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  destruct Hb as [-> | ->].
  - (* b = 5: U135cc *)
    specialize (H5 eq_refl).
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply r11_five. exact H9.
    + intros ms (a1' & ->). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
      intros x _ O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a1' & HE). injection HE; intros; subst.
      apply H5. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : u2_ks regs' regs).
      { unfold u2_ks, u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      split; [exact (u2_RFx_keep g 5 _ _ phi regs regs' mem (normalize rsegs mem) m' [] HMI (munch_refl _ _) Hrel
                       LI LF I I KR HRF)|].
      unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). exact H10.
  - (* b = 6: the fragment call, U134e0 *)
    specialize (H6 eq_refl).
    destruct (u2_RS_56 (g_in g) 6 ltac:(lia) Hnz) as (_ & E2).
    change (Z.of_nat 6) with 6 in *.
    pose proof (u2_rtm_close (g_in g) Hnz) as Hcl.
    pose proof (u2_rtm_k11 (g_in g) 6 (or_intror eq_refl) Hnz) as Hk.
    unfold fg_st in E2. rewrite Hcl in E2. cbn [fg_next] in E2.
    unfold RIDB, FGB, spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    assert (ST96 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 96) (g_S g - 1936))
      by (apply (u2_stk_sub _ _ _ _ _ ST); lia).
    assert (HG : bytes_at rsegs (normalize rsegs mem) phi (rt_g (g_in g) 6)).
    { apply u2_fr50_at; [exact (bytes_at_normalize rsegs mem phi _ HMI HF) | lia]. }
    pose proof (u2_rw_at _ _ _ (g_S g - 1936 + 120) (RFG (g_in g) 6) ST ltac:(lia) ltac:(rewrite LF; lia)
                  (bytes_at_normalize rsegs mem _ _ HMI HFG)) as HFw.
    rewrite LF in HFw.
    pose proof (u2_wr_of_stk _ _ _ (g_S g - 1936 + 1824) 2 ST ltac:(lia) ltac:(lia) ltac:(lia)) as WA.
    pose proof (u2_wr_of_stk _ _ _ (g_S g - 1936 + 1752) 8 ST ltac:(lia) ltac:(lia) ltac:(lia)) as WP.
    pose proof (u2_wr_of_stk _ _ _ (g_S g - 1936 + 1688) 8 ST ltac:(lia) ltac:(lia) ltac:(lia)) as WN.
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply (r11_six FRAG) with (spv := g_S g - 1936) (phi := phi) (n := rt_n (g_in g) 6) (k := rt_k (g_in g) 6)
        (st := RFG (g_in g) 6) (g := rt_g (g_in g) 6);
        [exact Hsp | exact H9 | exact H20 | exact H21 | exact H10 | exact Hk | lia | lia | exact H16
        | lia | lia | lia | exact ST96 | exact (mem_inv_normalize rsegs mem) | apply fr50_length | exact LF
        | exact HG | exact HFw | exact WA | exact WP | exact WN | exact Hcl].
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      eexists. split; [exact MU|]. split; [exact WM|].
      intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ &
                      HF' & HA' & HP' & HN').
      injection HE; intros; subst.
      apply H6. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : u2_ks regs' regs).
      { unfold u2_ks, u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      unfold rnb, rgb. change (Z.of_nat 6) with 6.
      split.
      { eapply (u2_RFx_new g 6 _ _ _ _ phi regs regs' mem m'' m' _ HMI MU Hrel); [| | | exact KR | exact HRF | |].
        - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
        - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
        - cbn [disjoint_from]. unfold rnb. lia.
        - unfold RIDB, spk, fsp, SLOT_FRAME. apply (u2_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HID].
          rewrite LI. cbn [disjoint_from]. lia.
        - unfold FGB, spk, fsp, SLOT_FRAME. rewrite E2. exact (u2_out _ _ _ _ Hrel HF'). }
      split; [exact Hk|].
      split; [unfold fg_rf; rewrite Hcl; reflexivity|].
      unfold rg, u16, q64, spk, fsp, SLOT_FRAME in *. rewrite (sl_getr_eqv _ _ _ Hx).
      split; [reflexivity|].
      split; [exact (u2_out _ _ _ _ Hrel HA')|]. split; [exact (u2_out _ _ _ _ Hrel HP')|].
      exact (u2_out _ _ _ _ Hrel HN').
Qed.

End R11.
