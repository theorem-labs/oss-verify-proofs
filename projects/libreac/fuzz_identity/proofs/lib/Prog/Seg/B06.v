From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb1 Tac_sj Tac_sb3b.
Import ListNotations.
Open Scope Z_scope.

Lemma kB06 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (gb sp0 k : Z),
  x10 = Z_to_bv 64 gb -> 0 < gb < 2 ^ 64 -> x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 48 < 2 ^ 64 ->
  x21 = Z_to_bv 64 k -> 0 <= k <= 255 ->
  store_ok rsegs m (wa (sp0 + 40)) 8 = true ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 (Z_to_bv 64 sp0) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 gb) x11 x12 x13 x14 x15 x16 x17
                           x18 x19 x20 (Z_to_bv 64 k) x22 x23 (Z_to_bv 64 gb) x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 (if k =? 0 then 0x130dc else 0x130cc)) fc None (write_to_mem m (wa (sp0 + 40)) (le8 x26)) ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x130bc) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro gb sp0 k E10 Hg E2 H0 H1 E21 Hk HS.
  subst x10 x2 x21.
  step. if_cases HB; zify_cond HB; [exfalso; lia|].
  step. step. step. if_cases HC; zify_cond HC.
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
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MEMCPY : memcpy_contract.

Lemma seg_B06 : forall i,
  Hrec B APIf ra (Inv_K130dc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K130bc_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & gb & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (HB03 & HID & HBF & HRR & E10).
  pose proof HB03 as ((HREC & E23 & E21 & E20) & E26 & E22 & HPL).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in HSc.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HF))))))))))))))))))) as WIN.
  unfold SLOT_K, SLOT_STACK in WIN.
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
  assert (WR : wr_at rsegs mem (fsp g + 40) 8).
  { split; [unfold fsp, SLOT_FRAME; lia|]. split; [unfold fsp, SLOT_FRAME; lia|]. intros j Hj.
    pose proof (WIN (fsp g + 40 + j) ltac:(unfold fsp, SLOT_FRAME; lia)) as W.
    unfold writable_at in W. rewrite SEG in W. exact W. }
  assert (HS : store_ok rsegs mem (wa (fsp g + 40)) 8 = true).
  { replace (fsp g + 40) with (fsp g + 40 + 0) by lia. apply (wr_at_store_ok rsegs mem (fsp g + 40) 8); [exact WR | lia | lia]. }
  eapply (run_to B APIf ra empty FF);
    [exact HF | eapply kB06 with (gb := gb) (sp0 := fsp g) (k := rec_k (g_in g) i);
      [exact E10 | lia | exact Hsp | unfold fsp, SLOT_FRAME; lia | unfold fsp, SLOT_FRAME; lia | exact E21 | lia
      | exact HS]
    | intros regs1 HG].
  rewrite E26.
  set (m1 := write_to_mem mem (wa (fsp g + 40)) (le8 (Z_to_bv 64 (rec_Lp (g_in g) i)))).
  assert (MU1 : munch [(fsp g + 40, fsp g + 48)] mem m1).
  { apply munch_write; [apply munch_refl | unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia |].
    cbn [Frame.inside]. rewrite ?length_le8. lia. }
  assert (WM1 : wmono rsegs mem m1) by (apply wmono_write; apply wmono_refl).
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> a < fsp g + 40 \/ fsp g + 48 <= a -> mbyte rsegs m1 a = mbyte rsegs mem a)
    by (intros a Ha Ho; exact (t_mb1 rsegs _ _ mem m1 a MU1 Ha Ho)).
  assert (LP1 : LPm g i m1).
  { unfold LPm, q64, spk. apply bytes_at_write_same; [unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia]. }
  assert (HF1 : FR B APIf ra empty g (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)]) L A regs1 m1 md).
  { apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [| rewrite HG, Hsp; reflexivity | rg HG | rg HG].
    apply (FR_mem B APIf ra empty FF g _ _ L A regs mem md m1 _ HF HP MU1 WM1).
    intros x Hx Hs _. cbn. split; [unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *; lia | exact I]. }
  assert (G24 : getr regs1 24 = Z_to_bv 64 gb) by (rewrite HG; reflexivity).
  assert (G9 : getr regs1 9 = getr regs 9) by (rewrite HG; reflexivity).
  assert (B031 : B03 g i pl regs1 m1).
  { apply (fb_B03_keep g i pl regs regs1 mem m1 HB03); [rg HG | rg HG | rewrite HG, E21; reflexivity | rg HG | rg HG | rg HG |].
    intros a [Ha|[Ha|Ha]]; apply M1; unfold fsp, SLOT_FRAME in *; lia. }
  assert (ID1 : IDb g (S i) m1).
  { unfold IDb in *. apply (t_keep_at mem m1 _ _ HID). rewrite rec_id_length.
    intros x Hx. apply M1; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia. }
  assert (BF1 : BEF g i m1).
  { unfold BEF in *. apply (t_keep_at mem m1 _ _ HBF). rewrite rec_id_length.
    intros x Hx. apply M1; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia. }
  assert (PL1' : PLB g i pl m1).
  { unfold PLB in *. apply (t_keep_at mem m1 _ _ HPL). rewrite rec_pl_length.
    intros x Hx. apply M1; unfold fsp, SLOT_FRAME in *; lia. }
  destruct (Z.eqb_spec (rec_k (g_in g) i) 0) as [K0|K0].
  - change (Z_to_bv 64 (if true then 0x130dc else 0x130cc)) with (Z_to_bv 64 0x130dc).
    apply HX. exists pl, gb.
    apply (cut_close B APIf ra empty _ _ _ _ _ L A); [exact HF1 | exact HP |].
    split; [exact B031|]. split; [exact ID1|]. split; [exact BF1|].
    split; [unfold RRr in *; rewrite G9; exact HRR|]. split; [exact G24|]. split; [exact LP1|].
    assert (E0 : rec_pl (g_in g) i = []) by (apply length_zero_iff_nil; rewrite rec_pl_length; lia).
    unfold PLB. rewrite E0. split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. lia.
  - change (Z_to_bv 64 (if false then 0x130dc else 0x130cc)) with (Z_to_bv 64 0x130cc).
    assert (G21 : getr regs1 21 = Z_to_bv 64 (rec_k (g_in g) i)) by (rewrite HG; reflexivity).
    assert (G22 : getr regs1 22 = Z_to_bv 64 pl) by (rewrite HG; exact E22).
    pose proof HF1 as (_ & _ & _ & _ & _ & _ & HMI1 & _ & HMR1 & _).
    unfold MI in HMI1. rewrite SEG in HMI1.
    eapply (t_run_norm B APIf ra empty FF regs1 _ m1 md L A
      (fun R pc' mem' => pc' = Z_to_bv 64 0x130dc /\
         Sem.reg_get R 2 = getr regs1 2 /\ Sem.reg_get R 3 = getr regs1 3 /\ Sem.reg_get R 4 = getr regs1 4 /\
         Sem.reg_get R 9 = getr regs1 9 /\ Sem.reg_get R 19 = getr regs1 19 /\ Sem.reg_get R 20 = getr regs1 20 /\
         Sem.reg_get R 21 = Z_to_bv 64 (rec_k (g_in g) i) /\ Sem.reg_get R 22 = Z_to_bv 64 pl /\
         Sem.reg_get R 23 = getr regs1 23 /\ Sem.reg_get R 24 = Z_to_bv 64 gb /\
         Sem.reg_get R 26 = getr regs1 26 /\
         munch [(gb, gb + rec_k (g_in g) i)] m1 mem' /\ wmono rsegs m1 mem' /\
         bytes_at rsegs mem' gb (rec_pl (g_in g) i))); [exact HMR1 | exact HMI1 | |].
    + unfold KindBGlue.rmk. rewrite G24, G22, G21. unfold Frame.mkR.
      repeat (stepx 115900 78044).
      destruct (t_present_rw_cells m1 gb (Z.to_nat (rec_k (g_in g) i)) ltac:(lia) ltac:(lia)) as [junk RW0].
      { intros j Hj. destruct (t_block B APIf ra empty FF L A m1 md gb _ j HMR1 Hgb ltac:(lia)) as (Hp & _). exact Hp. }
      assert (RWN : rw_cells rsegs (normalize rsegs m1) gb [Cells.CB (Z.to_nat (rec_k (g_in g) i)) junk]).
      { apply (t_rw_cells_norm m1 gb _ HMI1 RW0). intros j Hj. cbn [cells_size csize] in Hj.
        destruct (t_block B APIf ra empty FF L A m1 md gb _ j HMR1 Hgb ltac:(lia)) as (_ & _ & _ & _ & NI & _).
        apply (t_ro_out B APIf ra empty FF); [lia | exact NI]. }
      assert (SRC : bytes_at rsegs (normalize rsegs m1) pl (rec_pl (g_in g) i))
        by (apply bytes_at_normalize; [exact HMI1 | exact PL1']).
      eapply evt_cut.
      { eapply (MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rec_pl (g_in g) i) junk).
        - rewrite t_unsigned by lia. exact SRC.
        - rewrite t_unsigned by lia. apply rec_pl_length.
        - rewrite !t_unsigned by lia. exact RWN.
        - rewrite !t_unsigned by lia. lia.
        - apply mem_inv_normalize. }
      intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & RW & BS).
      rewrite !t_unsigned in MU, RW by lia.
      rewrite (t_ret_pc _ (t_ret_ok_lit 78044 ltac:(lia) eq_refl)).
      apply evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HR HS'.
      do 12 (split; [reflexivity|]).
      split; [exact (munch_rel rsegs _ m1 (normalize rsegs m1) mem' m' (mem_rel_normalize rsegs m1 HMI1) HR HS' MU)|].
      split; [exact (wmono_rel rsegs m1 (normalize rsegs m1) mem' m' (mem_rel_normalize rsegs m1 HMI1) HR HS' WM)|].
      exact (t_cb_bytes _ _ _ _ (t_rw_cells_rel _ _ _ _ HR RW)).
    + intros R pc' mem' regs2 (-> & K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K26 & MU2 & WM2 & PLB2) HG2.
      assert (GR : forall r, bv_eqb r 0 = false -> getr regs2 r = Sem.reg_get R r)
        by (intros r Hr; rewrite HG2; exact (t_getr_R R r Hr)).
      assert (M2 : forall a, 0 <= a < 2 ^ 64 -> a < gb \/ gb + rec_k (g_in g) i <= a ->
          mbyte rsegs mem' a = mbyte rsegs m1 a)
        by (intros a Ha Ho; exact (t_mb1 rsegs _ _ m1 mem' a MU2 Ha Ho)).
      apply HX. exists pl, gb.
      apply (cut_close B APIf ra empty _ _ _ _ _ L A); [| exact HP |].
      { apply (FR_regs B APIf ra empty _ _ _ _ _ regs1);
          [| rewrite GR by reflexivity; exact K2 | rewrite GR by reflexivity; exact K3
           | rewrite GR by reflexivity; exact K4].
        apply (FR_mem B APIf ra empty FF g _ _ L A regs1 m1 md mem' _ HF1 HP MU2 WM2).
        intros x Hx _ Hn. cbn. split; [|exact I].
        intros Hx2. apply (Hn gb (rec_k (g_in g) i + 1)); [right; left; reflexivity | lia]. }
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      * apply (fb_B03_keep g i pl regs1 regs2 m1 mem' B031);
          [ rewrite GR by reflexivity; exact K19 | rewrite GR by reflexivity; exact K20
          | rewrite GR by reflexivity; rewrite K21, G21; reflexivity | rewrite GR by reflexivity; rewrite K22, G22; reflexivity
          | rewrite GR by reflexivity; exact K23 | rewrite GR by reflexivity; exact K26 |].
        intros a Ha. apply M2; unfold fsp, SLOT_FRAME in *; lia.
      * unfold IDb in *. apply (t_keep_at m1 mem' _ _ ID1). rewrite rec_id_length.
        intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia.
      * unfold BEF in *. apply (t_keep_at m1 mem' _ _ BF1). rewrite rec_id_length.
        intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia.
      * unfold RRr in *. rewrite GR by reflexivity. rewrite K9, G9. exact HRR.
      * rewrite GR by reflexivity. exact K24.
      * unfold LPm, q64 in *. apply (t_keep_at m1 mem' _ _ LP1). rewrite length_le8.
        intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME in *; lia.
      * exact PLB2.
Qed.

End S.
