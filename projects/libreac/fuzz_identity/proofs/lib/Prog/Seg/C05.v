From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_scd.
Import ListNotations.
Open Scope Z_scope.

Lemma c05_fam_row : forall hw j, (j < 3)%nat -> map bv_unsigned hw = HWT j -> fam_cmp hw = Z.of_nat j + 1.
Proof.
  intros hw j Hj H. unfold fam_cmp. cbv zeta. rewrite H.
  destruct j as [|[|[|j]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

Lemma c05_P7 : forall inp, FAM (idT inp) = fam_hw (haveT inp) (hwbT inp).
Proof. intros inp. apply rec_P7. Qed.

Section C05.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma c05_exit : forall g L A regs mem md R regs',
  Hcut B APIf ra (Inv_K13544 B APIf ra empty) ->
  FR B APIf ra empty g (2 * NR g) [] L A regs mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  CUR g (cT (g_in g)) regs -> TID g mem ->
  getr R 2 = getr regs 2 -> getr R 3 = getr regs 3 -> getr R 4 = getr regs 4 ->
  getr R 20 = getr regs 20 -> getr R 26 = getr regs 26 ->
  (forall r, getr regs' r = getr R r) ->
  Rz (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x13544) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros g L A regs mem md R regs' H544 HF HP HCUR HTID E2 E3 E4 E20 E26 Hg.
  apply H544. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem md); [| exact HP |].
  - apply (sc_FR_regs B APIf ra empty g _ _ L A regs regs' mem md HF); rewrite Hg; assumption.
  - split; [|split; [exact HTID | apply c05_P7]].
    destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. rewrite !Hg, E20, E26. split; assumption.
Qed.

Definition c05_K (regs : bvmap 5 word) (mem : word -> option byte) (R : bvmap 5 word) (pc' : word)
    (mem' : word -> option byte) : Prop :=
  mem' = mem /\ pc' = Z_to_bv 64 0x13544 /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
  getr R 4 = getr regs 4 /\ getr R 20 = getr regs 20 /\ getr R 26 = getr regs 26.

Lemma seg_C05 :
  Hcut B APIf ra (Inv_K13544 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) /\
  Hcut B APIf ra (Inv_K13540 B APIf ra empty) /\
  Hcut B APIf ra (Inv_K13c68 B APIf ra empty).
Proof.
  intros H544. split; [|split].
  - intros g c Hc.
    destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HCUR & HTID & H9 & Hfh).
    pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
    assert (E0 : FAM (idT (g_in g)) = 0) by (rewrite c05_P7; exact Hfh).
    apply (sc_run B APIf ra empty FF regs (Z_to_bv 64 0x1353c) mem md L A (c05_K regs mem) _ HMR).
    + unfold rmk, c05_K. rewrite H9, E0.
      step. step. if_false.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity.
    + intros R pc' mem' regs' (-> & -> & E2 & E3 & E4 & E20 & E26) Hg.
      exact (c05_exit g L A regs mem md R regs' H544 HF HP HCUR HTID E2 E3 E4 E20 E26 Hg).
  - intros g c Hc.
    destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HCUR & HTID & H9 & Hhv & H10).
    pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
    assert (E0 : FAM (idT (g_in g)) = 0) by (rewrite c05_P7, Hhv; reflexivity).
    apply (sc_run B APIf ra empty FF regs (Z_to_bv 64 0x13540) mem md L A (c05_K regs mem) _ HMR).
    + unfold rmk, c05_K. rewrite H9, E0, H10.
      step. if_false.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity.
    + intros R pc' mem' regs' (-> & -> & E2 & E3 & E4 & E20 & E26) Hg.
      exact (c05_exit g L A regs mem md R regs' H544 HF HP HCUR HTID E2 E3 E4 E20 E26 Hg).
  - intros g c [j Hc].
    destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HCB & Hhv & H9 & H18 & Hj & Hrow & Hmiss).
    pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
    pose proof HCB as (_ & _ & HG16 & _ & HCUR & HID).
    assert (HTID : TID g mem) by (split; assumption).
    assert (EF : FAM (idT (g_in g)) = Z.of_nat j + 1).
    { rewrite c05_P7, Hhv. unfold fam_hw. cbn [Z.eqb]. apply c05_fam_row; assumption. }
    assert (Hro : ro_agree rsegs mem) by (unfold MI in HMI; rewrite (sc_segs B APIf ra empty FF) in HMI; exact HMI).
    apply (sc_run B APIf ra empty FF regs (Z_to_bv 64 0x13c68) mem md L A (c05_K regs mem) _ HMR).
    + unfold rmk, c05_K. rewrite H9, EF, H18.
      destruct j as [|[|[|j]]]; [| | | lia].
      * assert (HR : ov_read_bytes rsegs mem (wa 66984) 4 = Some [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
        { apply (sc_ovr mem 66984 [_; _; _; _]). apply sc_img_bytes; [exact Hro | lia | cbn; lia | vm_compute; reflexivity]. }
        change (HWT_ADDR + 12 * Z.of_nat 0) with 66988. change (Z.of_nat 0 + 1) with 1.
        step. step. if_true.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
        repeat (split; [reflexivity|]). reflexivity.
      * assert (HR : ov_read_bytes rsegs mem (wa 66996) 4 = Some [Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
        { apply (sc_ovr mem 66996 [_; _; _; _]). apply sc_img_bytes; [exact Hro | lia | cbn; lia | vm_compute; reflexivity]. }
        change (HWT_ADDR + 12 * Z.of_nat 1) with 67000. change (Z.of_nat 1 + 1) with 2.
        step. step. if_true.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
        repeat (split; [reflexivity|]). reflexivity.
      * assert (HR : ov_read_bytes rsegs mem (wa 67008) 4 = Some [Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
        { apply (sc_ovr mem 67008 [_; _; _; _]). apply sc_img_bytes; [exact Hro | lia | cbn; lia | vm_compute; reflexivity]. }
        change (HWT_ADDR + 12 * Z.of_nat 2) with 67012. change (Z.of_nat 2 + 1) with 3.
        step. step. if_true.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
        repeat (split; [reflexivity|]). reflexivity.
    + intros R pc' mem' regs' (-> & -> & E2 & E3 & E4 & E20 & E26) Hg.
      exact (c05_exit g L A regs mem md R regs' H544 HF HP HCUR HTID E2 E3 E4 E20 E26 Hg).
Qed.

End C05.
