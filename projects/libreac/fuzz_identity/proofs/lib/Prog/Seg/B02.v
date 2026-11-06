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

Section B02.
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

Lemma seg_B02 : forall i,
  Hrec B APIf ra (Inv_K13088_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13068_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & L & A & regs & mem & md & -> & HFR & HP & ((HREC & HS7 & HS5 & HS4) & HID & HS10 & HA0)).
  pose proof (ff_segs B APIf ra empty FF) as SEG.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (Gn & _).
  assert (HPL : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR HPL) as [PL1 PL2].
  pose proof alloc_ceiling_lt as AC.
  pose proof (t_pbnd B APIf ra empty FF g _ _ L A regs mem md HFR HP) as PB. unfold g_n in PB.
  pose proof (rec_k_range (g_in g) i) as KR. pose proof (rec_bounds (g_in g) i) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
  unfold MI in HMI. rewrite SEG in HMI.
  eapply (t_run_norm B APIf ra empty FF regs _ mem md L A
    (fun R pc' mem' => pc' = Z_to_bv 64 0x13088 /\
       Sem.reg_get R 2 = getr regs 2 /\ Sem.reg_get R 3 = getr regs 3 /\ Sem.reg_get R 4 = getr regs 4 /\
       Sem.reg_get R 19 = getr regs 19 /\ Sem.reg_get R 23 = getr regs 23 /\
       Sem.reg_get R 21 = Z_to_bv 64 (rec_k (g_in g) i) /\
       Sem.reg_get R 20 = Z_to_bv 64 (g_p g + rec_body (g_in g) i) /\
       Sem.reg_get R 26 = getr regs 26 /\ Sem.reg_get R 22 = Z_to_bv 64 pl /\
       munch [(pl, pl + rec_k (g_in g) i)] mem mem' /\ wmono rsegs mem mem' /\
       bytes_at rsegs mem' pl (rec_pl (g_in g) i))); [exact HMR | exact HMI | |].
  - unfold KindBGlue.rmk. rewrite HA0, HS5, HS4. unfold Frame.mkR.
    repeat (stepx 115900 77960).
    + apply evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HR HS. simp_regs.
      assert (EQ : forall x, mem' x = mem x)
        by exact (mem_unchanged_rel rsegs mem (normalize rsegs mem) mem' (normalize rsegs mem)
                    (mem_rel_normalize rsegs mem HMI) HR HS (fun x => eq_refl)).
      do 10 (split; [reflexivity|]).
      split; [intros x _; apply EQ|]. split; [intros x Hx; unfold wview in *; rewrite EQ; exact Hx|].
      assert (E0 : rec_pl (g_in g) i = []) by (apply length_zero_iff_nil; rewrite rec_pl_length; lia).
      rewrite E0. split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. lia.
    + destruct (t_present_rw_cells mem pl (Z.to_nat (rec_k (g_in g) i)) ltac:(lia) ltac:(lia)) as [junk RW0].
      { intros j Hj. destruct (t_block B APIf ra empty FF L A mem md pl _ j HMR HPL ltac:(lia)) as (Hp & _). exact Hp. }
      assert (RWN : rw_cells rsegs (normalize rsegs mem) pl [Cells.CB (Z.to_nat (rec_k (g_in g) i)) junk]).
      { apply (t_rw_cells_norm mem pl _ HMI RW0). intros j Hj. cbn [cells_size csize] in Hj.
        destruct (t_block B APIf ra empty FF L A mem md pl _ j HMR HPL ltac:(lia)) as (_ & _ & _ & _ & NI & _).
        apply (t_ro_out B APIf ra empty FF); [lia | exact NI]. }
      assert (SRC : bytes_at rsegs (normalize rsegs mem) (g_p g + rec_body (g_in g) i) (rec_pl (g_in g) i)).
      { apply bytes_at_normalize; [exact HMI|].
        exact (t_payload_bytes B APIf ra empty FF g _ _ L A regs mem md HFR HP (rec_body (g_in g) i)
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
      rewrite (t_ret_pc _ (t_ret_ok_lit 77960 ltac:(lia) eq_refl)).
      apply evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HR HS.
      do 10 (split; [reflexivity|]).
      split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) mem' m' (mem_rel_normalize rsegs mem HMI) HR HS MU)|].
      split; [exact (wmono_rel rsegs mem (normalize rsegs mem) mem' m' (mem_rel_normalize rsegs mem HMI) HR HS WM)|].
      exact (t_cb_bytes _ _ _ _ (t_rw_cells_rel _ _ _ _ HR RW)).
  - intros R pc' mem' regs' (-> & K2 & K3 & K4 & K19 & K23 & K21 & K20 & K26 & K22 & MU & WM & PLB') HG.
    assert (GR : forall r, bv_eqb r 0 = false -> getr regs' r = Sem.reg_get R r)
      by (intros r Hr; rewrite HG; exact (t_getr_R R r Hr)).
    assert (E2 : getr regs' 2 = getr regs 2) by (rewrite GR by reflexivity; exact K2).
    assert (E3 : getr regs' 3 = getr regs 3) by (rewrite GR by reflexivity; exact K3).
    assert (E4 : getr regs' 4 = getr regs 4) by (rewrite GR by reflexivity; exact K4).
    apply (HX g). exists pl, L, A, regs', mem', md. split; [reflexivity|].
    assert (OUT : forall x, 0 <= x < 2 ^ 64 -> ~ (pl <= x < pl + rec_k (g_in g) i) ->
      outside [(pl, pl + rec_k (g_in g) i)] x) by (intros x _ Hx; cbn; split; [exact Hx | exact I]).
    split.
    { apply (FR_regs B APIf ra empty FF g _ _ L A regs regs' mem' md); [|exact E2 | exact E3 | exact E4].
      apply (FR_mem B APIf ra empty FF g _ _ L A regs mem md mem' _ HFR HP MU WM).
      intros x Hx _ Hn. apply OUT; [exact Hx|]. apply (Hn pl (rec_k (g_in g) i)). left. reflexivity. }
    split; [exact HP|].
    pose proof HFR as (HGV' & SPF & _). pose proof HGV' as (_ & _ & _ & _ & GSK & GS47 & _).
    unfold SLOT_K, SLOT_STACK in GSK.
    assert (SOUT : forall a bs, bytes_at rsegs mem a bs -> fsp g <= a -> a + Z.of_nat (length bs) <= g_S g ->
      bytes_at rsegs mem' a bs).
    { intros a bs Hb H1 H2. apply (t_bytes_munch _ _ mem mem' a bs Hb MU). intros j Hj.
      unfold fsp, SLOT_FRAME in *. pose proof alloc_ceiling_value. apply OUT; lia. }
    destruct HREC as (HiN & HS3 & HNR & HG16 & HHW).
    unfold NRb, G16, HWb, IDb, q64, u32 in *. destruct HHW as (HW1 & HW2 & HW3).
    split; [split; [split; [split; [exact HiN|] |] |] |].
    + split; [rewrite GR by reflexivity; rewrite K19; exact HS3|].
      split; [apply SOUT; [exact HNR | unfold spk; lia | rewrite length_le8; unfold spk, fsp, SLOT_FRAME; lia]|].
      split; [apply SOUT; [exact HG16 | unfold spk; lia | rewrite length_le8; unfold spk, fsp, SLOT_FRAME; lia]|].
      split; [apply SOUT; [exact HW1 | unfold spk; lia | rewrite length_le8; unfold spk, fsp, SLOT_FRAME; lia]|].
      split; [apply SOUT; [exact HW2 | unfold spk; lia | rewrite length_le4; unfold spk, fsp, SLOT_FRAME; lia]|].
      apply SOUT; [exact HW3 | unfold spk; lia | rewrite t_hwb_len; unfold spk, fsp, SLOT_FRAME; lia].
    + split; [rewrite GR by reflexivity; rewrite K23; exact HS7|].
      split; [rewrite GR by reflexivity; exact K21|].
      rewrite GR by reflexivity; exact K20.
    + split; [rewrite GR by reflexivity; rewrite K26; exact HS10|].
      split; [rewrite GR by reflexivity; exact K22|].
      exact PLB'.
    + apply SOUT; [exact HID | unfold spk; lia | rewrite rec_id_length; unfold spk, fsp, SLOT_FRAME, RcIdentModel.ID_SIZE; lia].
Qed.
End B02.
