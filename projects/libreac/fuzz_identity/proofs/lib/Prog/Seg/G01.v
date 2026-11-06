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

Lemma g01_slli : forall x, 0 <= x < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 56)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  intros x Hx. rewrite bv_lts_zero_r, MState.unsigned_lit_wrap, (MState.unsigned_lit x) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  destruct (Z.leb_spec (2 ^ 63) (x * 2 ^ 56)); destruct (Z.leb_spec 128 x); reflexivity || lia.
Qed.

Section G01.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FAMOF : reac_box_family_of_c.reac_box_family_of_contract.

Lemma seg_G01 : Hcut B APIf ra (Inv_K136f0 B APIf ra empty) -> Hcut B APIf ra (Inv_K136f8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K136dc B APIf ra empty).
Proof.
  intros H6f0 H6f8 g c Hc.
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & (((HTID & (H8 & HTLr) & H20) & H21 & H22 & HEF & HFW) & H27 & H10)).
  pose proof HF as (HGV & Hsp & Hgp & Htp & _ & Hstk & HMI & _ & HMR & _).
  pose proof HGV as (_ & _ & _ & GS16 & GSc & GS47 & _).
  pose proof HTLr as (H9 & H18 & H19 & H24 & H25 & H40).
  pose proof HTID as (HG16 & HID).
  destruct (sg_md B APIf ra empty FF L A mem md HMR) as [Hh Hl].
  pose proof (inb_range (g_in g) (cT (g_in g) + 0)) as Hfr. fold (tb (g_in g) 0) in Hfr. fold (t_fam_raw (g_in g)) in Hfr.
  pose proof (sg_ceil B APIf ra empty FF) as Hc20. pose proof alloc_ceiling_lt as Hc47.
  unfold SLOT_K, SLOT_STACK in GSc, Hstk.
  assert (Hfsp : 0 <= fsp g < 2 ^ 64) by (unfold fsp, SLOT_FRAME; lia).
  pose proof (rec_id_length (g_in g) (NRn g)) as Ln. unfold RcIdentModel.ID_SIZE in Ln.
  assert (HB : forall m' a bs, bytes_at rsegs mem a bs -> (forall x, m' x = mem x) -> bytes_at rsegs m' a bs)
    by (intros m' a bs Hb HE; exact (sg_bytes_same B APIf ra empty FF mem m' a bs Hb HE)).
  destruct (Z_lt_ge_dec (t_fam_raw (g_in g)) 128) as [Lt|Ge].
  - apply (sg_run B APIf ra empty FF regs (Z_to_bv 64 0x136dc) mem md
      (fun R pc' m0 => pc' = Z_to_bv 64 0x136f0 /\
         munch [(fsp g - 32, fsp g)] (normalize (ms_segs B) mem) m0 /\ wmono (ms_segs B) (normalize (ms_segs B) mem) m0 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
         getr R 27 = getr regs 27 /\ getr R 10 = Z_to_bv 64 (FAM (idT (g_in g)))) _ Hh Hl HMI).
    + rewrite (sg_segs B APIf ra empty FF). unfold rmk. rewrite Hsp, H10, H8.
      step. if_false. step. step.
      rewrite (g01_slli _ Hfr). replace (128 <=? t_fam_raw (g_in g)) with false by (symmetry; apply Z.leb_gt; lia).
      cbv iota. step. step.
      pose proof HMI as HMI'. unfold MI in HMI'. rewrite (sg_segs B APIf ra empty FF) in HMI'.
      unfold IDb in HID.
      eapply Exec.evt_cut.
      { eapply FAMOF with (lo := g_S g - 65536) (idb := idT (g_in g)).
        - rewrite MState.unsigned_lit by exact Hfsp.
          apply sg_stk_norm; [| lia]. destruct (stk_split rsegs mem _ (fsp g) _ Hstk) as [S1 _]; [unfold fsp, SLOT_FRAME; lia|].
          exact S1.
        - rewrite MState.unsigned_lit by exact Hfsp. unfold reac_box_family_of_c.REAC_BOX_FAMILY_OF_FRAME, fsp, SLOT_FRAME. lia.
        - apply mem_inv_normalize.
        - right. rewrite !MState.unsigned_lit by (unfold fsp, SLOT_FRAME in *; lia). split; [|split; [exact Ln | right; lia]].
          apply bytes_at_normalize; [exact HMI'|]. exact HID. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems & MU & WM & _).
      subst ms'. rewrite MState.ret_pc_even by (first [lia | reflexivity]).
      rewrite MState.unsigned_lit in MU by exact Hfsp. unfold reac_box_family_of_c.REAC_BOX_FAMILY_OF_FRAME in MU.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      repeat (split; [reflexivity|]).
      rewrite MState.unsigned_lit by (unfold fsp, SLOT_FRAME in *; lia). rewrite sg_famof by (unfold fsp, SLOT_FRAME; lia).
      reflexivity.
    + intros R pc' m0 m' regs' (-> & MU & WM & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E24 & E25 & E27 & E10) Hrel Hsame Hg.
      pose proof (mem_rel_normalize (ms_segs B) mem HMI) as Hr0.
      pose proof (munch_rel (ms_segs B) _ mem _ m' _ Hr0 Hrel Hsame MU) as MU'.
      pose proof (wmono_rel (ms_segs B) mem _ m' _ Hr0 Hrel Hsame WM) as WM'.
      assert (HF1 : FR B APIf ra empty g (2 * NR g + 2) [] L A regs' m' md).
      { apply (sg_FR_munch B APIf ra empty FF g _ [] L A regs mem md regs' m' [(fsp g - 32, fsp g)] HF HP); try (rewrite Hg; assumption).
        - exact MU'.
        - exact WM'.
        - exact Hsame.
        - intros x Hx Ho. left. apply sg_out1 in Ho. unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME in *. lia. }
      apply H6f0. apply (sg_cut B APIf ra empty FF g _ _ _ _ L A regs' m' md HF1 HP).
      unfold TID, TL, TLr, G16, IDb, q64 in *. unfold spk, fsp, SLOT_FRAME in *.
      split; [split|]; [| | split; [split|]; [| | split; [| split]]].
      * apply (sg_ba_win mem m' _ _ _ _ HG16 MU'). rewrite length_le8. lia.
      * apply (sg_ba_win mem m' _ _ _ _ HID MU'). rewrite Ln. lia.
      * rewrite Hg, E8. exact H8.
      * split; [rewrite Hg, E9; exact H9|]. split; [rewrite Hg, E18; exact H18|].
        split; [rewrite Hg, E19; exact H19|]. split; [rewrite Hg, E24; exact H24|].
        split; [rewrite Hg, E25; exact H25|].
        apply (sg_ba_win mem m' _ _ _ _ H40 MU'). rewrite length_le8. lia.
      * rewrite Hg, E27. exact H27.
      * exact Lt.
      * rewrite Hg, E10. reflexivity.
  - apply (sg_run B APIf ra empty FF regs (Z_to_bv 64 0x136dc) mem md
      (fun R pc' m0 => m0 = normalize (ms_segs B) mem /\ pc' = Z_to_bv 64 0x136f8 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
         getr R 27 = getr regs 27) _ Hh Hl HMI).
    + rewrite (sg_segs B APIf ra empty FF). unfold rmk. rewrite Hsp, H10, H8.
      step. if_false. step. step.
      rewrite (g01_slli _ Hfr). replace (128 <=? t_fam_raw (g_in g)) with true by (symmetry; apply Z.leb_le; lia).
      cbv iota.
      apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). reflexivity.
    + intros R pc' m0 m' regs' (-> & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E24 & E25 & E27) Hrel Hsame Hg.
      pose proof (sg_same_mem B APIf ra empty FF mem m' HMI Hrel Hsame) as HE.
      assert (HF1 : FR B APIf ra empty g (2 * NR g + 2) [] L A regs' m' md).
      { apply (sg_FR_same B APIf ra empty FF g _ _ L A regs mem md regs' m' HF HP HE); rewrite Hg; assumption. }
      apply H6f8. apply (sg_cut B APIf ra empty FF g _ _ _ _ L A regs' m' md HF1 HP).
      unfold TID, TL, TLr, G16, IDb, q64 in *.
      split; [split; [exact (HB m' _ _ HG16 HE) | exact (HB m' _ _ HID HE)]|].
      split; [split|]; [rewrite Hg, E8; exact H8 | |].
      * split; [rewrite Hg, E9; exact H9|]. split; [rewrite Hg, E18; exact H18|].
        split; [rewrite Hg, E19; exact H19|]. split; [rewrite Hg, E24; exact H24|].
        split; [rewrite Hg, E25; exact H25|]. exact (HB m' _ _ H40 HE).
      * split; [rewrite Hg, E27; exact H27 | lia].
Qed.

End G01.
