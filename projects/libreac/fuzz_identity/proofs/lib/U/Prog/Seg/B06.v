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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uabj UTac_uab3b.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma kB06 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (k : Z),
  x20 = Z_to_bv 64 k -> 0 <= k <= 255 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                           x18 x19 (Z_to_bv 64 k) x21 x22 x10 x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 (if k =? 0 then 0x13174 else 0x13164)) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x1315c) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro k E20 Hk.
  subst x20.
  step. step. if_cases HC; zify_cond HC.
  - apply evt_done. replace (k =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - apply evt_done. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
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

Lemma seg_B06 : forall i,
  Hrec B APIf ra (Inv_U13174_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U1315c_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & gb & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (HB03 & HS7 & HS9 & HLP & HID & HBF & HRR & E10).
  pose proof HB03 as ((HREC & E22 & E20 & E26) & E21 & HPL).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in HSc.
  pose proof (rec_k_range (g_in g) i) as Hk.
  assert (Hpl : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  assert (Hgb : In (gb, rec_k (g_in g) i + 1) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR Hpl) as [PL1 PL2].
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR Hgb) as [GB1 GB2].
  assert (PW : pairwise ranges_disjoint ((pl, rec_k (g_in g) i) :: (gb, rec_k (g_in g) i + 1) ::
      blocks (g_L g) (g_A g)))
    by exact (sj_pairwise_perm _ _ sj_rd_sym _ _ HP (mr_blocks_disjoint _ _ (aa_laws (APIf rc)) _ _ _ _ HMR)).
  pose proof (sj_disj_head _ _ (gb, rec_k (g_in g) i + 1) PW ltac:(left; reflexivity)) as D.
  unfold ranges_disjoint in D. cbn [fst snd] in D.
  eapply (run_to B APIf ra empty FF);
    [exact HF | eapply kB06 with (k := rec_k (g_in g) i); [exact E20 | lia] | intros regs1 HG].
  assert (G23 : getr regs1 23 = Z_to_bv 64 gb) by (rewrite HG; exact E10).
  assert (HF1 : FR B APIf ra empty g (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)]) L A regs1 mem md)
    by (apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [exact HF | rg HG | rg HG | rg HG]).
  assert (B031 : B03 g i pl regs1 mem).
  { apply (fb_B03_keep g i pl regs regs1 mem mem HB03); [rg HG | rewrite HG, E20; reflexivity | rg HG | rg HG | rg HG |].
    intros a _. reflexivity. }
  assert (G24 : getr regs1 24 = getr regs 24) by (rewrite HG; reflexivity).
  assert (G25 : getr regs1 25 = getr regs 25) by (rewrite HG; reflexivity).
  destruct (Z.eqb_spec (rec_k (g_in g) i) 0) as [K0|K0].
  - change (Z_to_bv 64 (if true then 0x13174 else 0x13164)) with (Z_to_bv 64 0x13174).
    apply HX. exists pl, gb.
    apply (cut_close B APIf ra empty _ _ _ _ _ L A); [exact HF1 | exact HP |].
    split; [exact B031|]. split; [unfold S9L in *; rewrite G25; exact HS9|]. split; [exact HLP|].
    split; [exact HID|]. split; [exact HBF|]. split; [unfold RRr in *; rewrite G24; exact HRR|].
    split; [exact G23|].
    assert (E0 : rec_pl (g_in g) i = []) by (apply length_zero_iff_nil; rewrite rec_pl_length; lia).
    unfold PLB. rewrite E0. split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. lia.
  - change (Z_to_bv 64 (if false then 0x13174 else 0x13164)) with (Z_to_bv 64 0x13164).
    assert (G20 : getr regs1 20 = Z_to_bv 64 (rec_k (g_in g) i)) by (rewrite HG; reflexivity).
    assert (G21 : getr regs1 21 = Z_to_bv 64 pl) by (rewrite HG; exact E21).
    unfold MI in HMI. rewrite SEG in HMI.
    eapply (t_run_norm B APIf ra empty FF regs1 _ mem md L A
      (fun R pc' mem' => pc' = Z_to_bv 64 0x13174 /\
         Sem.reg_get R 2 = getr regs1 2 /\ Sem.reg_get R 3 = getr regs1 3 /\ Sem.reg_get R 4 = getr regs1 4 /\
         Sem.reg_get R 9 = getr regs1 9 /\ Sem.reg_get R 20 = Z_to_bv 64 (rec_k (g_in g) i) /\
         Sem.reg_get R 21 = Z_to_bv 64 pl /\ Sem.reg_get R 22 = getr regs1 22 /\
         Sem.reg_get R 23 = Z_to_bv 64 gb /\ Sem.reg_get R 24 = getr regs1 24 /\
         Sem.reg_get R 25 = getr regs1 25 /\ Sem.reg_get R 26 = getr regs1 26 /\
         munch [(gb, gb + rec_k (g_in g) i)] mem mem' /\ wmono rsegs mem mem' /\
         bytes_at rsegs mem' gb (rec_pl (g_in g) i))); [exact HMR | exact HMI | |].
    + unfold KindBGlue.rmk. rewrite G23, G21, G20. unfold Frame.mkR.
      repeat (stepx 117232 78196).
      destruct (t_present_rw_cells mem gb (Z.to_nat (rec_k (g_in g) i)) ltac:(lia) ltac:(lia)) as [junk RW0].
      { intros j Hj. destruct (t_block B APIf ra empty FF L A mem md gb _ j HMR Hgb ltac:(lia)) as (Hp & _). exact Hp. }
      assert (RWN : rw_cells rsegs (normalize rsegs mem) gb [Cells.CB (Z.to_nat (rec_k (g_in g) i)) junk]).
      { apply (t_rw_cells_norm mem gb _ HMI RW0). intros j Hj. cbn [cells_size csize] in Hj.
        destruct (t_block B APIf ra empty FF L A mem md gb _ j HMR Hgb ltac:(lia)) as (_ & _ & _ & _ & NI & _).
        apply (t_ro_out B APIf ra empty FF); [lia | exact NI]. }
      assert (SRC : bytes_at rsegs (normalize rsegs mem) pl (rec_pl (g_in g) i))
        by (apply bytes_at_normalize; [exact HMI | exact HPL]).
      eapply evt_cut.
      { eapply (MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rec_pl (g_in g) i) junk).
        - rewrite t_unsigned by lia. exact SRC.
        - rewrite t_unsigned by lia. apply rec_pl_length.
        - rewrite !t_unsigned by lia. exact RWN.
        - rewrite !t_unsigned by lia. lia.
        - apply mem_inv_normalize. }
      intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & RW & BS).
      rewrite !t_unsigned in MU, RW by lia.
      rewrite (t_ret_pc _ (t_ret_ok_lit 78196 ltac:(lia) eq_refl)).
      apply evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HR HS'.
      do 12 (split; [reflexivity|]).
      split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) mem' m' (mem_rel_normalize rsegs mem HMI) HR HS' MU)|].
      split; [exact (wmono_rel rsegs mem (normalize rsegs mem) mem' m' (mem_rel_normalize rsegs mem HMI) HR HS' WM)|].
      exact (t_cb_bytes _ _ _ _ (t_rw_cells_rel _ _ _ _ HR RW)).
    + intros R pc' mem' regs2 (-> & K2 & K3 & K4 & K9 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & MU2 & WM2 & PLB2) HG2.
      assert (GR : forall r, bv_eqb r 0 = false -> getr regs2 r = Sem.reg_get R r)
        by (intros r Hr; rewrite HG2; exact (t_getr_R R r Hr)).
      assert (M2 : forall a, 0 <= a < 2 ^ 64 -> a < gb \/ gb + rec_k (g_in g) i <= a ->
          mbyte rsegs mem' a = mbyte rsegs mem a)
        by (intros a Ha Ho; exact (t_mb1 rsegs _ _ mem mem' a MU2 Ha Ho)).
      apply HX. exists pl, gb.
      apply (cut_close B APIf ra empty _ _ _ _ _ L A); [| exact HP |].
      { apply (FR_regs B APIf ra empty _ _ _ _ _ regs1);
          [| rewrite GR by reflexivity; exact K2 | rewrite GR by reflexivity; exact K3
           | rewrite GR by reflexivity; exact K4].
        apply (FR_mem B APIf ra empty FF g _ _ L A regs1 mem md mem' _ HF1 HP MU2 WM2).
        intros x Hx _ Hn. cbn. split; [|exact I].
        intros Hx2. apply (Hn gb (rec_k (g_in g) i + 1)); [right; left; reflexivity | lia]. }
      split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      * apply (fb_B03_keep g i pl regs1 regs2 mem mem' B031);
          [ rewrite GR by reflexivity; exact K9
          | rewrite GR by reflexivity; rewrite K20, G20; reflexivity | rewrite GR by reflexivity; rewrite K21, G21; reflexivity
          | rewrite GR by reflexivity; exact K22 | rewrite GR by reflexivity; exact K26 |].
        intros a Ha. apply M2; unfold fsp, SLOT_FRAME in *; lia.
      * unfold S9L in *. rewrite GR by reflexivity. rewrite K25, G25. exact HS9.
      * unfold LPm, q64 in *. apply (t_keep_at mem mem' _ _ HLP). rewrite length_le8.
        intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME in *; lia.
      * unfold IDb in *. apply (t_keep_at mem mem' _ _ HID). rewrite rec_id_length.
        intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia.
      * unfold BEF in *. apply (t_keep_at mem mem' _ _ HBF). rewrite rec_id_length.
        intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia.
      * unfold RRr in *. rewrite GR by reflexivity. rewrite K24, G24. exact HRR.
      * rewrite GR by reflexivity. exact K23.
      * exact PLB2.
Qed.

End S.
