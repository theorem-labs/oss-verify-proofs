(* Segment R10 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): 0x134a8, [0x134e0, 0x134f8], U134a8 (b = 3, 4) and
   U134e0 (b = 6) -> U134fc (reac_identity_ingest(sp+36, addr, pl, pll), the one ingest site); 0x134a8 is
   `j 134e0`, so the one check #8 = #10 (`li a1,1; bne a0,a1`: reply = 1, fragment = 1) runs on both. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply RcFrag RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

(* The shared tail at 0x134e0: the check #8 = #10, the three loads, id = sp+36, the call. *)
Lemma r10_tail : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv ad p len : Z) (idb pb : list byte),
    a0 = Z_to_bv 64 1 ->
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 <= ad < 65536 -> 0 < p < 2 ^ 64 -> 0 < len < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 1824)) 2 = Some (le2 (Z_to_bv 64 ad)) ->
    ov_read_bytes rsegs m (wa (spv + 1752)) 8 = Some (le8 (Z_to_bv 64 p)) ->
    ov_read_bytes rsegs m (wa (spv + 1688)) 8 = Some (le8 (Z_to_bv 64 len)) ->
    rw_cells rsegs m (spv + 36) [Cells.CB 38 idb] ->
    length pb = Z.to_nat len -> bytes_at rsegs m p pb -> p + len <= spv + 36 \/ spv + 74 <= p ->
    fst (ING idb ad pb) = 1 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x134fc) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x134fc) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 74)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 36) (snd (ING idb ad pb)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x134e0) fc None m (seg_rom rsegs)).
Proof.
  intros INGC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv ad p len idb pb -> -> Hsp0 Hsp H16 Had Hp Hlen R1 R2 R3 HI Hpb HB HD HING.
  assert (NR : ingest_refused (spv + 36) p len = false).
  { unfold ingest_refused.
    replace (spv + 36 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  step. step. if_false. step. step. step. step. step.
  eapply evt_cut.
  { eapply INGC with (id := spv + 36) (ad := ad) (p := p) (len := len) (idb := idb) (pb := pb);
      first [ apply u2_zx16; lia | reflexivity | lia | exact Hpb
            | intros _; split; [apply u2_mod; [exact H16 | lia | reflexivity | reflexivity] | exact HI]
            | intros _ _; exact HB | intros _ _ _; lia ]. }
  intros ms' PO. unfold reac_identity_ingest_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MUc & WMc & _ & _ & HZ).
  subst ms'. specialize (HZ NR).
  unfold ingest_ret. rewrite NR, HING.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 11 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MUc]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WMc|]. exact (sl_rw_bytes _ _ _ _ HZ).
Qed.

Lemma r10_a : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv ad p len : Z) (idb pb : list byte),
    a0 = Z_to_bv 64 1 ->
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 <= ad < 65536 -> 0 < p < 2 ^ 64 -> 0 < len < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 1824)) 2 = Some (le2 (Z_to_bv 64 ad)) ->
    ov_read_bytes rsegs m (wa (spv + 1752)) 8 = Some (le8 (Z_to_bv 64 p)) ->
    ov_read_bytes rsegs m (wa (spv + 1688)) 8 = Some (le8 (Z_to_bv 64 len)) ->
    rw_cells rsegs m (spv + 36) [Cells.CB 38 idb] ->
    length pb = Z.to_nat len -> bytes_at rsegs m p pb -> p + len <= spv + 36 \/ spv + 74 <= p ->
    fst (ING idb ad pb) = 1 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x134fc) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x134fc) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 74)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 36) (snd (ING idb ad pb)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x134a8) fc None m (seg_rom rsegs)).
Proof.
  intros INGC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv ad p len idb pb Ha0.
  intros. step.
  eapply (r10_tail INGC) with (spv := spv) (ad := ad) (p := p) (len := len) (idb := idb) (pb := pb); eassumption.
Qed.

Section R10.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis INGC : reac_identity_ingest_contract.

Lemma seg_R10 :
  (forall b : nat, Hat B APIf ra (Inv_U134fc_at B APIf ra empty) b -> Hat B APIf ra (Inv_U134a8_at B APIf ra empty) b) /\
  (Hat B APIf ra (Inv_U134fc_at B APIf ra empty) 6%nat -> Hcut B APIf ra (Inv_U134e0 B APIf ra empty)).
Proof.
  split.
  - (* b = 3, 4: after the reply *)
    intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & Hb & Hk & Hir & H10 & HA & HPp & HPn).
    pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
    pose proof HRB as (Hb6 & _ & _ & _ & _ & H9 & HID & HFG).
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    destruct (u2_hb B APIf ra empty FF g phi (rnb g b) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
    destruct (u2_RS_len (g_in g) b) as (LI & LF).
    unfold rnb, rFb, rgb in *.
    destruct (u2_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
    destruct (u2_RS_34 (g_in g) b Hb Hnz) as (E1 & E2).
    pose proof (u2_rtm_ing34 (g_in g) b Hb) as HING.
    pose proof (ir_true _ _ Hir) as (_ & _ & _ & _ & Hs & _).
    pose proof (u2_r_addr_rng (rt_g (g_in g) (Z.of_nat b))) as Had.
    pose proof alloc_ceiling_value as Hac.
    pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
    unfold RIDB, FGB, q64, spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    assert (HG : bytes_at rsegs (normalize rsegs mem) phi (rt_g (g_in g) (Z.of_nat b))).
    { apply u2_fr50_at; [exact (bytes_at_normalize rsegs mem phi _ HMI HF) | lia]. }
    assert (Hpll : 1 <= r_pll (rt_g (g_in g) (Z.of_nat b)) <= 10) by (unfold r_pll; lia).
    assert (L50 : length (rt_g (g_in g) (Z.of_nat b)) = 50%nat) by apply fr50_length.
    assert (HPB : bytes_at rsegs (normalize rsegs mem) (phi + 38) (r_pl (rt_g (g_in g) (Z.of_nat b)))).
    { unfold r_pl. apply u2_bsl_at; [exact HG | lia | lia | rewrite L50; lia]. }
    assert (LPB : length (r_pl (rt_g (g_in g) (Z.of_nat b))) = Z.to_nat (r_pll (rt_g (g_in g) (Z.of_nat b)))).
    { unfold r_pl. apply u2_bsl_len; [lia | lia | rewrite L50; lia]. }
    rewrite u2_reply_addr in HA.
    pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HA)) as R1. rewrite length_le2 in R1.
    pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HPp)) as R2. rewrite length_le8 in R2.
    pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HPn)) as R3. rewrite length_le8 in R3.
    pose proof (u2_rw_at _ _ _ (g_S g - 1936 + 36) (RID (g_in g) b) ST ltac:(lia) ltac:(rewrite LI; lia)
      (bytes_at_normalize rsegs mem _ _ HMI HID)) as HI.
    rewrite LI in HI.
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply (r10_a INGC) with (spv := g_S g - 1936) (ad := r_addr (rt_g (g_in g) (Z.of_nat b))) (p := phi + 38)
        (len := r_pll (rt_g (g_in g) (Z.of_nat b))) (idb := RID (g_in g) b)
        (pb := r_pl (rt_g (g_in g) (Z.of_nat b)));
        [exact H10 | exact Hsp | lia | lia | exact H16 | exact Had | lia | lia | exact R1 | exact R2
        | exact R3 | exact HI | exact LPB | exact HPB | lia | exact HING].
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      eexists. split; [exact MU|]. split; [exact WM|].
      intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HI').
      injection HE; intros; subst.
      apply H. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : u2_ks regs' regs).
      { unfold u2_ks, u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      rewrite E1, E2. unfold rp_id. rewrite Hir.
      split.
      { eapply (u2_RFx_new g b _ _ _ _ phi regs regs' mem m'' m' _ HMI MU Hrel); [| | | exact KR | exact HRF | |].
        - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
        - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
        - cbn [disjoint_from]. unfold rnb. lia.
        - unfold RIDB, spk, fsp, SLOT_FRAME. exact (u2_out _ _ _ _ Hrel HI').
        - unfold FGB, spk, fsp, SLOT_FRAME. apply (u2_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HFG].
          rewrite LF. cbn [disjoint_from]. lia. }
      split; [lia|].
      unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
  - (* b = 6: after the fragment's CLOSE *)
    intros H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & Hk & Hrf & H10 & HA & HPp & HPn).
    pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
    pose proof HRB as (Hb6 & _ & _ & _ & _ & H9 & HID & HFG).
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    destruct (u2_hb B APIf ra empty FF g phi (rnb g 6) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
    destruct (u2_RS_len (g_in g) 6) as (LI & _).
    destruct (u2_RS_len (g_in g) 7) as (_ & LF7).
    unfold rnb, rFb, rgb in *.
    destruct (u2_RS_56 (g_in g) 6 ltac:(lia) Hnz) as (E1 & E2).
    change (Z.of_nat 6) with 6 in *.
    destruct (u2_rtm_close_vals (g_in g) Hnz) as (Hfa & Hpll).
    pose proof (u2_rtm_ing6 (g_in g) Hnz) as HING.
    pose proof alloc_ceiling_value as Hac.
    pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
    unfold RIDB, FGB, u16, q64, spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    assert (HPB : bytes_at rsegs (normalize rsegs mem) (g_S g - 1936 + 139)
                    (f_pl (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6))).
    { unfold f_pl, fg_st. unfold fg_st in E2. rewrite <- E2. rewrite Hpll.
      replace (g_S g - 1936 + 139) with (g_S g - 1936 + 120 + 19) by lia.
      apply u2_bsl_at; [exact (bytes_at_normalize rsegs mem _ _ HMI HFG) | lia | lia | rewrite LF7; lia]. }
    assert (LPB : length (f_pl (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6)) =
                  Z.to_nat (f_pll (RFG (g_in g) 6) (rt_g (g_in g) 6))).
    { unfold f_pl, fg_st. unfold fg_st in E2. rewrite <- E2. rewrite Hpll.
      apply u2_bsl_len; [lia | lia | rewrite LF7; lia]. }
    rewrite Hfa in HA, HING. rewrite Hpll in HPn, LPB.
    pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HA)) as R1. rewrite length_le2 in R1.
    pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HPp)) as R2. rewrite length_le8 in R2.
    pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HPn)) as R3. rewrite length_le8 in R3.
    pose proof (u2_rw_at _ _ _ (g_S g - 1936 + 36) (RID (g_in g) 6) ST ltac:(lia) ltac:(rewrite LI; lia)
      (bytes_at_normalize rsegs mem _ _ HMI HID)) as HI.
    rewrite LI in HI.
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply (r10_tail INGC) with (spv := g_S g - 1936) (ad := 0x1000) (p := g_S g - 1936 + 139) (len := 17)
        (idb := RID (g_in g) 6) (pb := f_pl (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6));
        [exact H10 | exact Hsp | lia | lia | exact H16 | lia | lia | lia | exact R1 | exact R2
        | exact R3 | exact HI | exact LPB | exact HPB | lia | exact HING].
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      eexists. split; [exact MU|]. split; [exact WM|].
      intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HI').
      injection HE; intros; subst.
      apply H. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : u2_ks regs' regs).
      { unfold u2_ks, u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      change (Z.of_nat 6) with 6 in *.
      rewrite E1. unfold fg_id. rewrite Hrf, Hfa, Z.eqb_refl.
      split.
      { eapply (u2_RFx_new g 6 _ _ _ _ phi regs regs' mem m'' m' _ HMI MU Hrel); [| | | exact KR | exact HRF | |].
        - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
        - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
        - cbn [disjoint_from]. unfold rnb. lia.
        - unfold RIDB, spk, fsp, SLOT_FRAME. exact (u2_out _ _ _ _ Hrel HI').
        - unfold FGB, spk, fsp, SLOT_FRAME. apply (u2_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HFG].
          rewrite LF7. cbn [disjoint_from]. lia. }
      split; [right; right; reflexivity|].
      unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End R10.
