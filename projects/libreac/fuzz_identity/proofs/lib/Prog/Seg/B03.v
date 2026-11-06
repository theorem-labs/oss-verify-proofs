From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState Exec Regs6ss RegisterBridge Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Step Exec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb1.
Import ListNotations.
Open Scope Z_scope.

Section B03.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MEMCPY : memcpy_contract.

Ltac stepx s1 s2 := lazymatch goal with
  | |- evt _ _ (MState.MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      tryif (first [unify pc s1 | unify pc s2]) then fail else step
  | |- evt _ _ (MState.MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "HB" in if_cases H; zify_cond H; try (exfalso; lia)
  end.

Ltac saved_tac SPF :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
     r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hr' as [Hr'|Hr']; [subst r; simp_regs; first [reflexivity | symmetry; exact SPF] |]);
  subst r; simp_regs; first [reflexivity | symmetry; exact SPF].

Lemma seg_B03 : forall i,
  Hrec B APIf ra (Inv_K13098_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13088_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & L & A & regs & mem & md & -> & HFR & HP & (HB03 & HID)).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof HFR as (HGV & SPF & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (Gn & _ & _ & _ & GSK & GS47 & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in GSK.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HFR))))))))))))))))))) as WIN.
  unfold SLOT_K, SLOT_STACK in WIN.
  unfold MI in HMI. rewrite SEG in HMI.
  set (sp := fsp g) in *. assert (SPE : sp = g_S g - 368) by reflexivity.
  eapply (t_run_norm B APIf ra empty FF regs _ mem md L A
    (fun R pc' mem' => pc' = Z_to_bv 64 0x13098 /\
       (forall r, callee_saved r -> Sem.reg_get R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       munch [(sp + 48, sp + 86)] mem mem' /\ wmono rsegs mem mem' /\
       bytes_at rsegs mem' (sp + 48) (rec_id (g_in g) i))); [exact HMR | exact HMI | |].
  - unfold KindBGlue.rmk. rewrite SPF. fold sp. unfold Frame.mkR.
    repeat (stepx 115900 0).
    destruct (t_present_rw_cells mem (sp + 48) 38 ltac:(lia) ltac:(lia)) as [junk RW0].
    { intros j Hj. apply t_wr_present; [lia|]. rewrite <- SEG. apply WIN. lia. }
    assert (RWN : rw_cells rsegs (normalize rsegs mem) (sp + 48) [Cells.CB 38 junk]).
    { apply (t_rw_cells_norm mem _ _ HMI RW0). intros j Hj. apply t_ro_hi. cbn in Hj. lia. }
    assert (SRC : bytes_at rsegs (normalize rsegs mem) (sp + 130) (rec_id (g_in g) i))
      by (apply bytes_at_normalize; [exact HMI | exact HID]).
    eapply evt_cut.
    { eapply (MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rec_id (g_in g) i) junk).
      - rewrite t_unsigned by lia. exact SRC.
      - rewrite t_unsigned by lia. rewrite rec_id_length. reflexivity.
      - rewrite !t_unsigned by lia. exact RWN.
      - rewrite !t_unsigned by lia. lia.
      - apply mem_inv_normalize. }
    intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & RW & BS).
    rewrite !t_unsigned in MU, RW by lia. replace (sp + 48 + 38) with (sp + 86) in MU by ring.
    rewrite (t_ret_pc _ (t_ret_ok_lit 77976 ltac:(lia) eq_refl)).
    apply evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HR HS.
    split; [reflexivity|].
    split; [saved_tac SPF|].
    split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) mem' m' (mem_rel_normalize rsegs mem HMI) HR HS MU)|].
    split; [exact (wmono_rel rsegs mem (normalize rsegs mem) mem' m' (mem_rel_normalize rsegs mem HMI) HR HS WM)|].
    exact (t_cb_bytes _ _ _ _ (t_rw_cells_rel _ _ _ _ HR RW)).
  - intros R pc' mem' regs' (-> & KC & MU & WM & BEF') HG.
    pose proof (t_cs_regs regs regs' R HG KC) as CS.
    apply (HX g). exists pl, L, A, regs', mem', md. split; [reflexivity|].
    assert (MB : forall a, 0 <= a < 2 ^ 64 -> a < sp + 48 \/ sp + 86 <= a -> mbyte rsegs mem' a = mbyte rsegs mem a)
      by (intros a Ha Ho; exact (t_mb1 rsegs _ _ mem mem' a MU Ha Ho)).
    pose proof (proj1 (proj2 (proj2 (proj2 HB03)))) as PLB0. unfold PLB in PLB0.
    assert (HPL : In (pl, rec_k (g_in g) i) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
    destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR HPL) as [PL1 PL2].
    pose proof (rec_k_range (g_in g) i) as KR.
    split.
    { apply (FR_regs B APIf ra empty FF g _ _ L A regs regs' mem' md);
        [| exact (CS 2 ltac:(unfold callee_saved; lia)) | exact (CS 3 ltac:(unfold callee_saved; lia))
         | exact (CS 4 ltac:(unfold callee_saved; lia))].
      apply (FR_mem B APIf ra empty FF g _ _ L A regs mem md mem' _ HFR HP MU WM).
      intros x Hx Hs _. unfold SLOT_K, SLOT_STACK in Hs. cbn. split; [lia | exact I]. }
    split; [exact HP|].
    split; [|split].
    + apply (t_B03_keep g i pl regs regs' mem mem' HB03 CS). intros a Ha. apply MB; lia.
    + unfold IDb in *. apply (t_keep_at mem mem' _ _ HID). rewrite rec_id_length. unfold spk, RcIdentModel.ID_SIZE. fold sp.
      intros x Hx. apply MB; lia.
    + exact BEF'.
Qed.
End B03.
