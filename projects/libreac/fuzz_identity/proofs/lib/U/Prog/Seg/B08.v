From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState Exec Regs6ss RegisterBridge Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Step Exec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Section B08.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis INGEST : reac_identity_ingest_contract.

Ltac stepx s1 s2 := lazymatch goal with
  | |- evt _ _ (MState.MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      tryif (first [unify pc s1 | unify pc s2]) then fail else step
  | |- evt _ _ (MState.MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "HB" in if_cases H; zify_cond H; try (exfalso; lia)
  end.

Ltac saved_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
     r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hr' as [Hr'|Hr']; [subst r; simp_regs; first [reflexivity | symmetry; assumption] |]);
  subst r; simp_regs; first [reflexivity | symmetry; assumption].

Lemma seg_B08 : forall i,
  Hrec B APIf ra (Inv_U131ac_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13198_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & gb & L & A & regs & mem & md & -> & HFR & HP &
    (HB03 & HS9 & HLP & HID & HBEF & HRR & E23 & HPLg & HB8 & HAG)).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof HFR as (HGV & SPF & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (Gn & _ & _ & GS16 & GSK & GS47 & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in GSK.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HFR))))))))))))))))))) as WIN.
  unfold SLOT_K, SLOT_STACK in WIN.
  set (sp := fsp g) in *. assert (SPE : sp = g_S g - 384) by reflexivity.
  destruct (t_md B APIf ra empty FF L A mem md HMR) as [Hh Hl].
  pose proof HB03 as ((HREC & HS6 & HS4 & HS10) & HS5 & HPLB).
  assert (HPL : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  assert (HGB : In (gb, rec_k (g_in g) i + 1) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR HPL) as [PL1 PL2].
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR HGB) as [GB1 GB2].
  pose proof (rec_k_range (g_in g) i) as KR.
  eapply (kb_run_rz B regs _ mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x131ac /\
       (forall r, callee_saved r -> Sem.reg_get R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       Sem.reg_get R 10 = Z_to_bv 64 (rec_r (g_in g) i) /\
       munch [(sp + 242, sp + 280)] mem mem' /\ wmono rsegs mem mem' /\
       bytes_at rsegs mem' (sp + 242) (rec_id (g_in g) (S i)))); [exact Hh | exact Hl | |].
  - rewrite SEG. unfold KindBGlue.rmk. rewrite SPF, HS6, E23, HS4. unfold Frame.mkR.
    repeat (stepx 84328 0).
    pose proof (t_addr_range (g_in g) i) as AR.
    assert (RWAG : rw_cells rsegs mem (sp + 242) [Cells.CB 38 (rec_id (g_in g) i)]).
    { unfold AGN, spk in HAG. fold sp in HAG. pose proof (t_rw_cells_of mem _ _ HAG) as H.
      rewrite rec_id_length in H. apply H. split; [lia|]. split; [unfold RcIdentModel.ID_SIZE; lia|].
      intros j Hj. pose proof (WIN (sp + 242 + j) ltac:(unfold RcIdentModel.ID_SIZE in Hj; lia)) as W.
      rewrite SEG in W. exact W. }
    eapply evt_cut.
    { eapply (INGEST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sp + 242) (rec_addr (g_in g) i) gb (rec_k (g_in g) i)
        (rec_id (g_in g) i) (rec_pl (g_in g) i)); try reflexivity; try lia.
      - intros _. split; [rewrite SPE; Z.div_mod_to_equations; lia | exact RWAG].
      - apply rec_pl_length.
      - intros _ _. exact HPLg. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM & _ & _ & RW).
    assert (NR : ingest_refused (sp + 242) gb (rec_k (g_in g) i) = false).
    { unfold ingest_refused. destruct (Z.eqb_spec (sp + 242) 0); [lia|]. destruct (Z.eqb_spec gb 0); [lia|].
      rewrite andb_false_r. reflexivity. }
    replace (sp + 242 + 38) with (sp + 280) in MU by ring.
    specialize (RW NR). unfold ingest_ret. rewrite NR.
    rewrite (t_ret_pc _ (t_ret_ok_lit 78252 ltac:(lia) eq_refl)).
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [saved_tac|].
    split; [simp_regs; reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    exact (t_cb_bytes _ _ _ _ RW).
  - intros R pc' mem' regs' (-> & KC & K10 & MU & WM & AGS) HG.
    pose proof (t_cs_regs regs regs' R HG KC) as CS.
    assert (E10 : getr regs' 10 = Z_to_bv 64 (rec_r (g_in g) i)) by (rewrite HG, t_getr_R by reflexivity; exact K10).
    apply (HX g). exists pl, gb, L, A, regs', mem', md. split; [reflexivity|].
    assert (MB : forall a, 0 <= a < 2 ^ 64 -> a < sp + 242 \/ sp + 280 <= a -> mbyte rsegs mem' a = mbyte rsegs mem a)
      by (intros a Ha Ho; exact (t_mb1 rsegs _ _ mem mem' a MU Ha Ho)).
    split.
    { apply (FR_regs B APIf ra empty FF g _ _ L A regs regs' mem' md);
        [| exact (CS 2 ltac:(unfold callee_saved; lia)) | exact (CS 3 ltac:(unfold callee_saved; lia))
         | exact (CS 4 ltac:(unfold callee_saved; lia))].
      apply (FR_mem B APIf ra empty FF g _ _ L A regs mem md mem' _ HFR HP MU WM).
      intros x Hx Hs _. unfold SLOT_K, SLOT_STACK in Hs. cbn. split; [lia | exact I]. }
    split; [exact HP|].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
    + apply (t_B03_keep g i pl regs regs' mem mem' HB03 CS). intros a Ha. apply MB; lia.
    + unfold S9L in *. etransitivity; [exact (CS 25 ltac:(unfold callee_saved; lia))|]. exact HS9.
    + unfold LPm, q64 in *. apply (t_keep_at mem mem' _ _ HLP). rewrite length_le8. unfold spk. fold sp.
      intros x Hx. apply MB; lia.
    + unfold IDb in *. apply (t_keep_at mem mem' _ _ HID). rewrite rec_id_length. unfold spk, RcIdentModel.ID_SIZE. fold sp.
      intros x Hx. apply MB; lia.
    + unfold BEF in *. apply (t_keep_at mem mem' _ _ HBEF). rewrite rec_id_length. unfold spk, RcIdentModel.ID_SIZE. fold sp.
      intros x Hx. apply MB; lia.
    + unfold RRr in *. etransitivity; [exact (CS 24 ltac:(unfold callee_saved; lia))|]. exact HRR.
    + etransitivity; [exact (CS 23 ltac:(unfold callee_saved; lia))|]. exact E23.
    + unfold PLB in *. apply (t_keep_at mem mem' _ _ HPLg). rewrite rec_pl_length.
      intros x Hx. apply MB; lia.
    + unfold b8 in *. apply (t_keep_at mem mem' _ _ HB8). cbn [length].
      intros x Hx. apply MB; lia.
    + unfold AGN, spk. fold sp. exact AGS.
    + exact E10.
Qed.
End B08.
