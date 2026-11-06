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

Lemma kB07 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (gb k sp0 : Z),
  x23 = Z_to_bv 64 gb -> x20 = Z_to_bv 64 k -> x2 = Z_to_bv 64 sp0 ->
  0 <= gb -> 0 <= k -> gb + k + 1 < 2 ^ 64 -> 0 <= sp0 -> sp0 + 280 < 2 ^ 64 ->
  store_ok rsegs m (wa (gb + k)) 1 = true ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13198) (Z_to_bv 64 sp0) x3 x4 x5 x6 x7 x8 x9
                           (Z_to_bv 64 (sp0 + 242)) (Z_to_bv 64 (sp0 + 64)) (Z_to_bv 64 38) x13 x14 x15 x16 x17 x18 x19
                           (Z_to_bv 64 k) x21 x22 (Z_to_bv 64 gb) x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 0x1c9f0) fc None (write_to_mem m (wa (gb + k)) [Z_to_bv 8 90]) ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13174) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro gb k sp0 E23 E20 E2 H0 H1 H2 H3 H4 HS.
  subst x23 x20 x2.
  step. rewrite ua_not by lia.
  step. rewrite ua_ltu by lia. replace (2 ^ 64 - 1 - gb <? k) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv iota.
  step. step. step. step. step. step. step. apply evt_done. reflexivity.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis MEMCPY : memcpy_contract.

Lemma seg_B07 : forall i,
  Hrec B APIf ra (Inv_U13198_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13174_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & gb & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (HB03 & HS9 & HLP & HID & HBF & HRR & E23 & HPLg).
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
  destruct (t_block B APIf ra empty FF L A mem md gb _ (rec_k (g_in g) i) HMR Hgb ltac:(lia))
    as (_ & _ & _ & _ & _ & WG).
  assert (HS : store_ok rsegs mem (wa (gb + rec_k (g_in g) i)) 1 = true).
  { replace (gb + rec_k (g_in g) i) with (gb + rec_k (g_in g) i + 0) by lia.
    apply (wr_at_store_ok rsegs mem (gb + rec_k (g_in g) i) 1); [|lia|lia].
    split; [lia|]. split; [lia|]. intros j Hj. replace j with 0 by lia. rewrite Z.add_0_r. exact WG. }
  eapply (run_to B APIf ra empty FF);
    [exact HF | eapply kB07 with (gb := gb) (k := rec_k (g_in g) i) (sp0 := fsp g);
      [exact E23 | exact E20 | exact Hsp | lia | lia | lia | unfold fsp, SLOT_FRAME; lia | unfold fsp, SLOT_FRAME; lia
      | exact HS]
    | intros regs1 HG].
  set (m1 := write_to_mem mem (wa (gb + rec_k (g_in g) i)) [Z_to_bv 8 90]).
  assert (MU1 : munch [(gb + rec_k (g_in g) i, gb + rec_k (g_in g) i + 1)] mem m1).
  { apply munch_write; [apply munch_refl | lia | cbn [length]; lia |]. cbn [Frame.inside length]. lia. }
  assert (WM1 : wmono rsegs mem m1) by (apply wmono_write; apply wmono_refl).
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> a < gb + rec_k (g_in g) i \/ gb + rec_k (g_in g) i + 1 <= a ->
      mbyte rsegs m1 a = mbyte rsegs mem a)
    by (intros a Ha Ho; exact (t_mb1 rsegs _ _ mem m1 a MU1 Ha Ho)).
  assert (HF1 : FR B APIf ra empty g (2 * Z.of_nat i + 2) (hb_pl g i pl ++ [(gb, rec_k (g_in g) i + 1)]) L A regs1 m1 md).
  { apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [| rewrite HG, Hsp; reflexivity | rg HG | rg HG].
    apply (FR_mem B APIf ra empty FF g _ _ L A regs mem md m1 _ HF HP MU1 WM1).
    intros x Hx _ Hn. cbn. split; [|exact I].
    intros Hx2. apply (Hn gb (rec_k (g_in g) i + 1)); [right; left; reflexivity | lia]. }
  assert (B8 : b8 m1 (gb + rec_k (g_in g) i) 0x5a).
  { unfold b8. apply bytes_at_write_same; [lia | cbn [length]; lia]. }
  assert (B031 : B03 g i pl regs1 m1).
  { apply (fb_B03_keep g i pl regs regs1 mem m1 HB03); [rg HG | rewrite HG, E20; reflexivity | rg HG | rg HG | rg HG |].
    intros a [Ha|[Ha|Ha]]; apply M1; unfold fsp, SLOT_FRAME in *; lia. }
  assert (ID1 : IDb g (S i) m1).
  { unfold IDb in *. apply (t_keep_at mem m1 _ _ HID). rewrite rec_id_length.
    intros x Hx. apply M1; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia. }
  assert (BF1 : BEF g i m1).
  { unfold BEF in *. apply (t_keep_at mem m1 _ _ HBF). rewrite rec_id_length.
    intros x Hx. apply M1; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia. }
  assert (LP1 : LPm g i m1).
  { unfold LPm, q64 in *. apply (t_keep_at mem m1 _ _ HLP). rewrite length_le8.
    intros x Hx. apply M1; unfold spk, fsp, SLOT_FRAME in *; lia. }
  assert (PG1 : PLB g i gb m1).
  { unfold PLB in *. apply (t_keep_at mem m1 _ _ HPLg). rewrite rec_pl_length.
    intros x Hx. apply M1; lia. }
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x13198) by (rewrite HG; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (fsp g + 242)) by (rewrite HG; reflexivity).
  assert (G11 : getr regs1 11 = Z_to_bv 64 (fsp g + 64)) by (rewrite HG; reflexivity).
  assert (G12 : getr regs1 12 = Z_to_bv 64 38) by (rewrite HG; reflexivity).
  pose proof HF1 as (_ & _ & _ & _ & _ & _ & HMI1 & _ & HMR1 & _).
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HF1))))))))))))))))))) as WIN1.
  unfold SLOT_K, SLOT_STACK in WIN1.
  unfold MI in HMI1. rewrite SEG in HMI1.
  eapply (t_run_norm B APIf ra empty FF regs1 _ m1 md L A
    (fun R pc' mem' => pc' = Z_to_bv 64 0x13198 /\
       Sem.reg_get R 2 = getr regs1 2 /\ Sem.reg_get R 3 = getr regs1 3 /\ Sem.reg_get R 4 = getr regs1 4 /\
       Sem.reg_get R 9 = getr regs1 9 /\ Sem.reg_get R 20 = getr regs1 20 /\
       Sem.reg_get R 21 = getr regs1 21 /\ Sem.reg_get R 22 = getr regs1 22 /\
       Sem.reg_get R 23 = getr regs1 23 /\ Sem.reg_get R 24 = getr regs1 24 /\
       Sem.reg_get R 25 = getr regs1 25 /\ Sem.reg_get R 26 = getr regs1 26 /\
       munch [(fsp g + 242, fsp g + 280)] m1 mem' /\ wmono rsegs m1 mem' /\
       bytes_at rsegs mem' (fsp g + 242) (rec_id (g_in g) i))); [exact HMR1 | exact HMI1 | |].
  - unfold KindBGlue.rmk. rewrite G1, G10, G11, G12. unfold Frame.mkR.
    destruct (t_present_rw_cells m1 (fsp g + 242) 38 ltac:(unfold fsp, SLOT_FRAME; lia)
      ltac:(unfold fsp, SLOT_FRAME; lia)) as [junk RW0].
    { intros j Hj. apply t_wr_present; [unfold fsp, SLOT_FRAME; lia|]. rewrite <- SEG. apply WIN1.
      unfold fsp, SLOT_FRAME; lia. }
    assert (RWN : rw_cells rsegs (normalize rsegs m1) (fsp g + 242) [Cells.CB 38 junk]).
    { apply (t_rw_cells_norm m1 _ _ HMI1 RW0). intros j Hj. apply t_ro_hi. cbn in Hj. unfold fsp, SLOT_FRAME. lia. }
    assert (SRC : bytes_at rsegs (normalize rsegs m1) (fsp g + 64) (rec_id (g_in g) i))
      by (apply bytes_at_normalize; [exact HMI1 | exact BF1]).
    eapply evt_cut.
    { eapply (MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rec_id (g_in g) i) junk).
      - rewrite t_unsigned by (unfold fsp, SLOT_FRAME; lia). exact SRC.
      - rewrite t_unsigned by lia. rewrite rec_id_length. reflexivity.
      - rewrite !t_unsigned by (unfold fsp, SLOT_FRAME; lia). exact RWN.
      - rewrite !t_unsigned by (unfold fsp, SLOT_FRAME; lia). lia.
      - apply mem_inv_normalize. }
    intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & RW & BS).
    rewrite !t_unsigned in MU, RW by (unfold fsp, SLOT_FRAME; lia).
    replace (fsp g + 242 + 38) with (fsp g + 280) in MU by ring.
    rewrite (t_ret_pc _ (t_ret_ok_lit 0x13198 ltac:(lia) eq_refl)).
    apply evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HR HS'.
    do 12 (split; [reflexivity|]).
    split; [exact (munch_rel rsegs _ m1 (normalize rsegs m1) mem' m' (mem_rel_normalize rsegs m1 HMI1) HR HS' MU)|].
    split; [exact (wmono_rel rsegs m1 (normalize rsegs m1) mem' m' (mem_rel_normalize rsegs m1 HMI1) HR HS' WM)|].
    exact (t_cb_bytes _ _ _ _ (t_rw_cells_rel _ _ _ _ HR RW)).
  - intros R pc' mem' regs2 (-> & K2 & K3 & K4 & K9 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & MU2 & WM2 & AG2) HG2.
    assert (GR : forall r, bv_eqb r 0 = false -> getr regs2 r = Sem.reg_get R r)
      by (intros r Hr; rewrite HG2; exact (t_getr_R R r Hr)).
    assert (M2 : forall a, 0 <= a < 2 ^ 64 -> a < fsp g + 242 \/ fsp g + 280 <= a ->
        mbyte rsegs mem' a = mbyte rsegs m1 a)
      by (intros a Ha Ho; exact (t_mb1 rsegs _ _ m1 mem' a MU2 Ha Ho)).
    apply HX. exists pl, gb.
    apply (cut_close B APIf ra empty _ _ _ _ _ L A); [| exact HP |].
    { apply (FR_regs B APIf ra empty _ _ _ _ _ regs1);
        [| rewrite GR by reflexivity; exact K2 | rewrite GR by reflexivity; exact K3
         | rewrite GR by reflexivity; exact K4].
      apply (FR_mem B APIf ra empty FF g _ _ L A regs1 m1 md mem' _ HF1 HP MU2 WM2).
      intros x Hx Hs _. cbn. split; [unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *; lia | exact I]. }
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    + apply (fb_B03_keep g i pl regs1 regs2 m1 mem' B031);
        [ rewrite GR by reflexivity; exact K9 | rewrite GR by reflexivity; exact K20
        | rewrite GR by reflexivity; exact K21 | rewrite GR by reflexivity; exact K22
        | rewrite GR by reflexivity; exact K26 |].
      intros a Ha. apply M2; unfold fsp, SLOT_FRAME in *; lia.
    + unfold S9L in *. rewrite GR by reflexivity. rewrite K25, HG. exact HS9.
    + unfold LPm, q64 in *. apply (t_keep_at m1 mem' _ _ LP1). rewrite length_le8.
      intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME in *; lia.
    + unfold IDb in *. apply (t_keep_at m1 mem' _ _ ID1). rewrite rec_id_length.
      intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia.
    + unfold BEF in *. apply (t_keep_at m1 mem' _ _ BF1). rewrite rec_id_length.
      intros x Hx. apply M2; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE in *; lia.
    + unfold RRr in *. rewrite GR by reflexivity. rewrite K24, HG. exact HRR.
    + rewrite GR by reflexivity. rewrite K23, HG. reflexivity.
    + unfold PLB in *. apply (t_keep_at m1 mem' _ _ PG1). rewrite rec_pl_length.
      intros x Hx. apply M2; unfold fsp, SLOT_FRAME in *; lia.
    + unfold b8 in *. apply (t_keep_at m1 mem' _ _ B8). cbn [length].
      intros x Hx. apply M2; unfold fsp, SLOT_FRAME in *; lia.
    + unfold AGN, spk. exact AG2.
Qed.

End S.
