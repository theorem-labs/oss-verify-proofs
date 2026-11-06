From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uabj.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma kB02 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (pl sp0 k : Z),
  x10 = Z_to_bv 64 pl -> 0 <= pl < 2 ^ 64 -> x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 64 < 2 ^ 64 ->
  x20 = Z_to_bv 64 k -> 0 <= k <= 255 -> (k = 0 \/ 0 < pl) ->
  store_ok rsegs m (wa (sp0 + 56)) 8 = true ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 (Z_to_bv 64 sp0) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 pl) x11 x12 x13 x14 x15 x16 x17
                           x18 x19 (Z_to_bv 64 k) (Z_to_bv 64 pl) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 (if k =? 0 then 0x13124 else 0x13114)) fc None (write_to_mem m (wa (sp0 + 56)) (le8 x25)) ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x130fc) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro pl sp0 k E10 Hpl E2 H0 H1 E20 Hk Hz HS.
  subst x10 x2 x20.
  destruct (Z.eq_dec k 0) as [K0|K0].
  - subst k. step. step. if_true. step. step. if_true. apply evt_done. reflexivity.
  - destruct Hz as [Hz|Hz]; [lia|].
    step. step. if_cases HB; zify_cond HB; [exfalso; lia|].
    step. if_cases HC; zify_cond HC; try (exfalso; lia).
    step. step. if_cases HD; zify_cond HD; [exfalso; lia|].
    apply evt_done. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Ltac stepx s1 s2 := lazymatch goal with
  | |- evt _ _ (MState.MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      tryif (first [unify pc s1 | unify pc s2]) then fail else step
  | |- evt _ _ (MState.MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "HB" in if_cases H; zify_cond H; try (exfalso; lia)
  end.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis MEMCPY : memcpy_contract.

Lemma seg_B02 : forall i,
  Hrec B APIf ra (Inv_U13124_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U130fc_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP ((HREC & E22 & E20 & E26) & E23 & E25 & HID & E10).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (Gn & _ & _ & _ & HSc & HS47 & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in HSc.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HF))))))))))))))))))) as WIN.
  unfold SLOT_K, SLOT_STACK in WIN.
  pose proof (rec_k_range (g_in g) i) as Hk.
  pose proof (rec_bounds (g_in g) i) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
  pose proof (t_pbnd B APIf ra empty FF g _ _ L A regs mem md HF HP) as PB. unfold g_n in PB.
  assert (Hpl : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR Hpl) as [PL1 PL2].
  assert (WR : wr_at rsegs mem (fsp g + 56) 8).
  { split; [unfold fsp, SLOT_FRAME; lia|]. split; [unfold fsp, SLOT_FRAME; lia|]. intros j Hj.
    pose proof (WIN (fsp g + 56 + j) ltac:(unfold fsp, SLOT_FRAME; lia)) as W.
    unfold writable_at in W. rewrite SEG in W. exact W. }
  assert (HS : store_ok rsegs mem (wa (fsp g + 56)) 8 = true).
  { replace (fsp g + 56) with (fsp g + 56 + 0) by lia. apply (wr_at_store_ok rsegs mem (fsp g + 56) 8); [exact WR | lia | lia]. }
  eapply (run_to B APIf ra empty FF);
    [exact HF | eapply kB02 with (pl := pl) (sp0 := fsp g) (k := rec_k (g_in g) i);
      [exact E10 | lia | exact Hsp | unfold fsp, SLOT_FRAME; lia | unfold fsp, SLOT_FRAME; lia | exact E20 | lia
      | lia | exact HS]
    | intros regs1 HG].
  rewrite E25.
  set (m1 := write_to_mem mem (wa (fsp g + 56)) (le8 (Z_to_bv 64 (rec_Lp (g_in g) i)))).
  assert (MU1 : munch [(fsp g + 56, fsp g + 64)] mem m1).
  { apply munch_write; [apply munch_refl | unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia |].
    cbn [Frame.inside]. rewrite ?length_le8. lia. }
  assert (WM1 : wmono rsegs mem m1) by (apply wmono_write; apply wmono_refl).
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> a < fsp g + 56 \/ fsp g + 64 <= a -> mbyte rsegs m1 a = mbyte rsegs mem a)
    by (intros a Ha Ho; exact (t_mb1 rsegs _ _ mem m1 a MU1 Ha Ho)).
  assert (LP1 : LPm g i m1).
  { unfold LPm, q64, spk. apply bytes_at_write_same; [unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia]. }
  assert (HF1 : FR B APIf ra empty g (2 * Z.of_nat i + 1) (hb_pl g i pl) L A regs1 m1 md).
  { apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [| rewrite HG, Hsp; reflexivity | rg HG | rg HG].
    apply (FR_mem B APIf ra empty FF g _ _ L A regs mem md m1 _ HF HP MU1 WM1).
    intros x Hx Hs _. cbn. split; [unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *; lia | exact I]. }
  assert (REC1 : REC g i regs1 m1).
  { apply (t_REC_keep g i regs regs1 mem m1 HREC); [rg HG|]. intros a Ha. apply M1; unfold fsp, SLOT_FRAME in *; lia. }
  assert (ID1 : IDb g i m1).
  { unfold IDb in *. apply (t_keep_at mem m1 _ _ HID). rewrite rec_id_length.
    intros x Hx. apply M1; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia. }
  assert (G20 : getr regs1 20 = Z_to_bv 64 (rec_k (g_in g) i)) by (rewrite HG; reflexivity).
  assert (G21 : getr regs1 21 = Z_to_bv 64 pl) by (rewrite HG; reflexivity).
  assert (G22 : getr regs1 22 = Z_to_bv 64 (rec_addr (g_in g) i)) by (rewrite HG; exact E22).
  assert (G23 : getr regs1 23 = Z_to_bv 64 (g_p g + rec_body (g_in g) i)) by (rewrite HG; exact E23).
  assert (G25 : getr regs1 25 = Z_to_bv 64 (rec_Lp (g_in g) i)) by (rewrite HG; exact E25).
  assert (G26 : getr regs1 26 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i))) by (rewrite HG; exact E26).
  destruct (Z.eqb_spec (rec_k (g_in g) i) 0) as [K0|K0].
  - change (Z_to_bv 64 (if true then 0x13124 else 0x13114)) with (Z_to_bv 64 0x13124).
    apply HX. exists pl.
    apply (cut_close B APIf ra empty _ _ _ _ _ L A); [exact HF1 | exact HP |].
    assert (E0 : rec_pl (g_in g) i = []) by (apply length_zero_iff_nil; rewrite rec_pl_length; lia).
    split; [split; [split; [exact REC1 | split; [exact G22 | split; [exact G20 | exact G26]]]|]|].
    { split; [exact G21|]. unfold PLB. rewrite E0. split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. lia. }
    split; [exact G23|]. split; [exact G25|]. split; [exact LP1 | exact ID1].
  - change (Z_to_bv 64 (if false then 0x13124 else 0x13114)) with (Z_to_bv 64 0x13114).
    pose proof HF1 as (_ & _ & _ & _ & _ & _ & HMI1 & _ & HMR1 & _).
    unfold MI in HMI1. rewrite SEG in HMI1.
    eapply (t_run_norm B APIf ra empty FF regs1 _ m1 md L A
      (fun R pc' mem' => pc' = Z_to_bv 64 0x13124 /\
         Sem.reg_get R 2 = getr regs1 2 /\ Sem.reg_get R 3 = getr regs1 3 /\ Sem.reg_get R 4 = getr regs1 4 /\
         Sem.reg_get R 9 = getr regs1 9 /\ Sem.reg_get R 20 = Z_to_bv 64 (rec_k (g_in g) i) /\
         Sem.reg_get R 21 = Z_to_bv 64 pl /\ Sem.reg_get R 22 = getr regs1 22 /\
         Sem.reg_get R 23 = getr regs1 23 /\ Sem.reg_get R 25 = getr regs1 25 /\
         Sem.reg_get R 26 = getr regs1 26 /\
         munch [(pl, pl + rec_k (g_in g) i)] m1 mem' /\ wmono rsegs m1 mem' /\
         bytes_at rsegs mem' pl (rec_pl (g_in g) i))); [exact HMR1 | exact HMI1 | |].
    + unfold KindBGlue.rmk. rewrite G21, G20, G23. unfold Frame.mkR.
      repeat (stepx 117232 78116).
      destruct (t_present_rw_cells m1 pl (Z.to_nat (rec_k (g_in g) i)) ltac:(lia) ltac:(lia)) as [junk RW0].
      { intros j Hj. destruct (t_block B APIf ra empty FF L A m1 md pl _ j HMR1 Hpl ltac:(lia)) as (Hp & _). exact Hp. }
      assert (RWN : rw_cells rsegs (normalize rsegs m1) pl [Cells.CB (Z.to_nat (rec_k (g_in g) i)) junk]).
      { apply (t_rw_cells_norm m1 pl _ HMI1 RW0). intros j Hj. cbn [cells_size csize] in Hj.
        destruct (t_block B APIf ra empty FF L A m1 md pl _ j HMR1 Hpl ltac:(lia)) as (_ & _ & _ & _ & NI & _).
        apply (t_ro_out B APIf ra empty FF); [lia | exact NI]. }
      assert (SRC : bytes_at rsegs (normalize rsegs m1) (g_p g + rec_body (g_in g) i) (rec_pl (g_in g) i)).
      { apply bytes_at_normalize; [exact HMI1|].
        exact (t_payload_bytes B APIf ra empty FF g _ _ L A regs1 m1 md HF1 HP (rec_body (g_in g) i)
          (rec_k (g_in g) i) RB2 ltac:(lia) ltac:(unfold g_n; lia)). }
      assert (DISJ : g_p g + rec_body (g_in g) i + rec_k (g_in g) i <= pl \/
                     pl + rec_k (g_in g) i <= g_p g + rec_body (g_in g) i).
      { pose proof HGV as (_ & Gp & _). destruct Gp as [[Hn0 _]|[Hn1 Hin]]; [unfold g_n in *; lia|].
        pose proof (t_perm_rd _ _ _ _ _ (mr_blocks_disjoint B _ (ff_laws B APIf ra empty FF) L A mem md HMR) HP
          (or_introl eq_refl) Hin) as D.
        unfold ranges_disjoint in D. cbn in D. unfold g_n in *. lia. }
      eapply evt_cut.
      { eapply (MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rec_pl (g_in g) i) junk).
        - rewrite t_unsigned by lia. exact SRC.
        - rewrite t_unsigned by lia. apply rec_pl_length.
        - rewrite !t_unsigned by lia. exact RWN.
        - rewrite !t_unsigned by lia. lia.
        - apply mem_inv_normalize. }
      intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & RW & BS).
      rewrite !t_unsigned in MU, RW by lia.
      rewrite (t_ret_pc _ (t_ret_ok_lit 78116 ltac:(lia) eq_refl)).
      apply evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HR HS'.
      do 11 (split; [reflexivity|]).
      split; [exact (munch_rel rsegs _ m1 (normalize rsegs m1) mem' m' (mem_rel_normalize rsegs m1 HMI1) HR HS' MU)|].
      split; [exact (wmono_rel rsegs m1 (normalize rsegs m1) mem' m' (mem_rel_normalize rsegs m1 HMI1) HR HS' WM)|].
      exact (t_cb_bytes _ _ _ _ (t_rw_cells_rel _ _ _ _ HR RW)).
    + intros R pc' mem' regs2 (-> & K2 & K3 & K4 & K9 & K20 & K21 & K22 & K23 & K25 & K26 & MU2 & WM2 & PLB2) HG2.
      assert (GR : forall r, bv_eqb r 0 = false -> getr regs2 r = Sem.reg_get R r)
        by (intros r Hr; rewrite HG2; exact (t_getr_R R r Hr)).
      assert (M2 : forall a, 0 <= a < 2 ^ 64 -> a < pl \/ pl + rec_k (g_in g) i <= a ->
          mbyte rsegs mem' a = mbyte rsegs m1 a)
        by (intros a Ha Ho; exact (t_mb1 rsegs _ _ m1 mem' a MU2 Ha Ho)).
      apply HX. exists pl.
      apply (cut_close B APIf ra empty _ _ _ _ _ L A); [| exact HP |].
      { apply (FR_regs B APIf ra empty _ _ _ _ _ regs1);
          [| rewrite GR by reflexivity; exact K2 | rewrite GR by reflexivity; exact K3
           | rewrite GR by reflexivity; exact K4].
        apply (FR_mem B APIf ra empty FF g _ _ L A regs1 m1 md mem' _ HF1 HP MU2 WM2).
        intros x Hx _ Hn. cbn. split; [|exact I].
        intros Hx2. apply (Hn pl (rec_k (g_in g) i)); [left; reflexivity | lia]. }
      split; [split; [split; [|split; [|split]]|]|].
      * apply (t_REC_keep g i regs1 regs2 m1 mem' REC1); [rewrite GR by reflexivity; exact K9|].
        intros a Ha. apply M2; unfold fsp, SLOT_FRAME in *; lia.
      * rewrite GR by reflexivity. rewrite K22. exact G22.
      * rewrite GR by reflexivity. exact K20.
      * rewrite GR by reflexivity. rewrite K26. exact G26.
      * split; [rewrite GR by reflexivity; exact K21 | exact PLB2].
      * unfold S7B, S9L. split; [rewrite GR by reflexivity; rewrite K23; exact G23|].
        split; [rewrite GR by reflexivity; rewrite K25; exact G25|].
        split.
        -- unfold LPm, q64 in *. apply (t_keep_at m1 mem' _ _ LP1). rewrite length_le8.
           intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME in *; lia.
        -- unfold IDb in *. apply (t_keep_at m1 mem' _ _ ID1). rewrite rec_id_length.
           intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia.
Qed.

End S.
