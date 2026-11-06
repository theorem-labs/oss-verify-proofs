From Stdlib Require Import ZArith List Bool Lia Permutation String.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_family_of_c reac_box_family_stem_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import ZBridge.
Import ListNotations.
Open Scope Z_scope.

Section G02.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis STEMC : reac_box_family_stem_c.reac_box_family_stem_contract.

Lemma g02_stem_table : relro_chk reac_box_family_stem_c.STEM_T
  (le8 (Z_to_bv 64 0x102d0) ++ le8 (Z_to_bv 64 0x103a4) ++ le8 (Z_to_bv 64 0x104e9)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma g02_same : forall g regs mem regs' m',
  (forall x, m' x = mem x) -> TID g mem -> TLr g regs mem ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  TID g m' /\ TLr g regs' m'.
Proof.
  intros g regs mem regs' m' HE (HG16 & HID) (H9 & H18 & H19 & H24 & H25 & H40) E9 E18 E19 E24 E25.
  unfold TID, TLr, G16, IDb, q64 in *.
  split; [split; [exact (sg_bytes_same B APIf ra empty FF mem m' _ _ HG16 HE) |
                  exact (sg_bytes_same B APIf ra empty FF mem m' _ _ HID HE)]|].
  rewrite E9, E18, E19, E24, E25. repeat (split; [assumption|]).
  exact (sg_bytes_same B APIf ra empty FF mem m' _ _ H40 HE).
Qed.

Lemma g02_tail : Hcut B APIf ra (Inv_K13704 B APIf ra empty) ->
  forall g L A regs mem md, FR B APIf ra empty g (2 * NR g + 2) [] L A regs mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  TID g mem -> TL g regs mem -> getr regs 27 = Z_to_bv 64 (t_cap_disp (g_in g)) ->
  getr regs 26 = Z_to_bv 64 (n_fam (g_in g)) ->
  Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x136fc) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros H704 g L A regs mem md HF HP HTID (H8 & HTLr) H27 H26.
  pose proof HF as (HGV & Hsp & Hgp & Htp & _ & _ & HMI & Hrelro & HMR & _).
  destruct (sg_md B APIf ra empty FF L A mem md HMR) as [Hh Hl].
  pose proof HMI as HMI'. unfold MI in HMI'. rewrite (sg_segs B APIf ra empty FF) in HMI'.
  pose proof (sg_relro_bytes B APIf ra empty FF mem _ _ Hrelro g02_stem_table
    ltac:(unfold reac_box_family_stem_c.STEM_T; lia) ltac:(unfold reac_box_family_stem_c.STEM_T; rewrite !length_app, !length_le8; lia)) as HST.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI' HST) as HSTn.
  pose proof (sg_nfam_range (g_in g)) as Hf.
  apply (sg_run B APIf ra empty FF regs (Z_to_bv 64 0x136fc) mem md
    (fun R pc' m0 => m0 = normalize (ms_segs B) mem /\ pc' = Z_to_bv 64 0x13704 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       getr R 10 = Z_to_bv 64 (reac_box_family_stem_c.STEM_Addr (n_fam (g_in g)))) _ Hh Hl HMI).
  - rewrite (sg_segs B APIf ra empty FF). unfold rmk. rewrite Hsp, H26.
    step. step.
    eapply Exec.evt_cut.
    { eapply STEMC with (f := n_fam (g_in g)); [lia | | exact HSTn].
      first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned, ?MState.unsigned_lit by lia; f_equal; lia]. }
    intros ms' (a1' & Ems & _). subst ms'. rewrite MState.ret_pc_even by (first [lia | reflexivity]).
    apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). reflexivity.
  - intros R pc' m0 m' regs' (-> & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E24 & E25 & E26 & E27 & E10) Hrel Hsame Hg.
    pose proof (sg_same_mem B APIf ra empty FF mem m' HMI Hrel Hsame) as HE.
    assert (HF1 : FR B APIf ra empty g (2 * NR g + 2) [] L A regs' m' md).
    { apply (sg_FR_same B APIf ra empty FF g _ _ L A regs mem md regs' m' HF HP HE); rewrite Hg; assumption. }
    apply H704. apply (sg_cut B APIf ra empty FF g _ _ _ _ L A regs' m' md HF1 HP).
    destruct (g02_same g regs mem regs' m' HE HTID HTLr) as [T1 T2]; try (rewrite Hg; assumption).
    split; [exact T1|]. split; [split; [rewrite Hg, E8; exact H8 | exact T2]|].
    split; [rewrite Hg, E27; exact H27|]. split; [rewrite Hg, E26; exact H26|]. rewrite Hg, E10. reflexivity.
Qed.

Lemma seg_G02 : Hcut B APIf ra (Inv_K13704 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K136f0 B APIf ra empty) /\ Hcut B APIf ra (Inv_K136f8 B APIf ra empty).
Proof.
  intros H704. split.
  - intros g c Hc.
    destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HTID & (H8 & HTLr) & H27 & Hlt & H10).
    pose proof HF as (HGV & Hsp & Hgp & Htp & _ & _ & HMI & _ & HMR & _).
    destruct (sg_md B APIf ra empty FF L A mem md HMR) as [Hh Hl].
    apply (sg_run B APIf ra empty FF regs (Z_to_bv 64 0x136f0) mem md
      (fun R pc' m0 => m0 = normalize (ms_segs B) mem /\ pc' = Z_to_bv 64 0x136fc /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
         getr R 27 = getr regs 27 /\ getr R 26 = Z_to_bv 64 (FAM (idT (g_in g)))) _ Hh Hl HMI).
    + rewrite (sg_segs B APIf ra empty FF). unfold rmk. rewrite Hsp, H10.
      step. step.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). reflexivity.
    + intros R pc' m0 m' regs' (-> & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E24 & E25 & E27 & E26) Hrel Hsame Hg.
      pose proof (sg_same_mem B APIf ra empty FF mem m' HMI Hrel Hsame) as HE.
      assert (HF1 : FR B APIf ra empty g (2 * NR g + 2) [] L A regs' m' md).
      { apply (sg_FR_same B APIf ra empty FF g _ _ L A regs mem md regs' m' HF HP HE); rewrite Hg; assumption. }
      destruct (g02_same g regs mem regs' m' HE HTID HTLr) as [T1 T2]; try (rewrite Hg; assumption).
      apply (g02_tail H704 g L A regs' m' md HF1 HP T1).
      * split; [rewrite Hg, E8; exact H8 | exact T2].
      * rewrite Hg, E27. exact H27.
      * rewrite Hg, E26. unfold n_fam. replace (128 <=? t_fam_raw (g_in g)) with false by (symmetry; apply Z.leb_gt; lia).
        reflexivity.
  - intros g c Hc.
    destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HTID & (H8 & HTLr) & H27 & Hge).
    pose proof HF as (HGV & Hsp & Hgp & Htp & _ & _ & HMI & _ & HMR & _).
    destruct (sg_md B APIf ra empty FF L A mem md HMR) as [Hh Hl].
    pose proof (inb_range (g_in g) (cT (g_in g) + 0)) as Hfr. fold (tb (g_in g) 0) in Hfr. fold (t_fam_raw (g_in g)) in Hfr.
    apply (sg_run B APIf ra empty FF regs (Z_to_bv 64 0x136f8) mem md
      (fun R pc' m0 => m0 = normalize (ms_segs B) mem /\ pc' = Z_to_bv 64 0x136fc /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
         getr R 27 = getr regs 27 /\ getr R 26 = Z_to_bv 64 (n_fam (g_in g))) _ Hh Hl HMI).
    + rewrite (sg_segs B APIf ra empty FF). unfold rmk. rewrite Hsp, H8.
      step.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [reflexivity|]).
      unfold n_fam. replace (128 <=? t_fam_raw (g_in g)) with true by (symmetry; apply Z.leb_le; lia).
      first [reflexivity | rewrite MState.unsigned_lit by lia; reflexivity].
    + intros R pc' m0 m' regs' (-> & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E24 & E25 & E27 & E26) Hrel Hsame Hg.
      pose proof (sg_same_mem B APIf ra empty FF mem m' HMI Hrel Hsame) as HE.
      assert (HF1 : FR B APIf ra empty g (2 * NR g + 2) [] L A regs' m' md).
      { apply (sg_FR_same B APIf ra empty FF g _ _ L A regs mem md regs' m' HF HP HE); rewrite Hg; assumption. }
      destruct (g02_same g regs mem regs' m' HE HTID HTLr) as [T1 T2]; try (rewrite Hg; assumption).
      apply (g02_tail H704 g L A regs' m' md HF1 HP T1).
      * split; [rewrite Hg, E8; exact H8 | exact T2].
      * rewrite Hg, E27. exact H27.
      * rewrite Hg, E26. reflexivity.
Qed.

End G02.
