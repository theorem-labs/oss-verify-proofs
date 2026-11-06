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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sg.
Import ListNotations.
Open Scope Z_scope.

Section G05.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_G05 : Hcut B APIf ra (Inv_K13748 B APIf ra empty) -> Hcut B APIf ra (Inv_K13734 B APIf ra empty).
Proof.
  intros H748 g c Hc.
  destruct Hc as (nm & tk & L & A & regs & mem & md & -> & HF & HP & (HTID & HTLr & H8 & H27 & H26) & H20 & H23 & H10).
  pose proof HF as (HGV & Hsp & Hgp & Htp & _ & _ & HMI & _ & HMR & _).
  pose proof HTLr as (H9 & H18 & H19 & H24 & H25 & H40).
  pose proof HTID as (HG16 & HID).
  destruct (sg_md B APIf ra empty FF L A mem md HMR) as [Hh Hl].
  destruct (sg_caps (g_in g)) as (Cn & Ct & Cd).
  pose proof (nrec_range (g_in g)) as Hnr.
  assert (Htk : In (tk, bsz (t_cap_tok (g_in g))) [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))])
    by (right; left; reflexivity).
  pose proof (sg_hb_nz B APIf ra empty FF L A mem md _ _ _ _ HMR HP Htk ltac:(unfold bsz; lia)) as Hnz.
  apply (sg_run B APIf ra empty FF regs (Z_to_bv 64 0x13734) mem md
    (fun R pc' m0 => m0 = normalize (ms_segs B) mem /\ pc' = Z_to_bv 64 0x15580 /\
       getr R 1 = Z_to_bv 64 0x13748 /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
       getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
       getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       getr R 20 = getr regs 20 /\ getr R 23 = getr regs 23 /\
       getr R 21 = Z_to_bv 64 tk /\
       getr R 10 = Z_to_bv 64 (bsz (t_cap_disp (g_in g)))) _ Hh Hl HMI).
  - rewrite (sg_segs B APIf ra empty FF). unfold rmk. rewrite Hsp, H10, H27.
    step. rewrite Hnz. cbv iota.
    step. step. step. step.
    first [ rewrite (sg_bufsz2 (t_cap_disp (g_in g))) by lia | rewrite (sg_bufsz3 (t_cap_disp (g_in g))) by lia ].
    apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
    repeat (split; [reflexivity|]). reflexivity.
  - intros R pc' m0 m' regs' (-> & -> & E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E24 & E25 & E26 & E27 & E20 & E23 & E21 & E10)
      Hrel Hsame Hg.
    pose proof (sg_same_mem B APIf ra empty FF mem m' HMI Hrel Hsame) as HE.
    assert (HF1 : FR B APIf ra empty g (2 * NR g + 4)
      [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))] L A regs' m' md).
    { apply (sg_FR_same B APIf ra empty FF g _ _ L A regs mem md regs' m' HF HP HE);
        rewrite Hg; assumption. }
    destruct (sg_syms B APIf ra empty FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmal).
    replace (Z_to_bv 64 87424) with (Z_to_bv 64 (ms_malloc B)) by (rewrite Hmal; reflexivity).
    apply (sg_malloc B APIf ra empty FF g (2 * NR g + 4) _ L A regs' m' md (bsz (t_cap_disp (g_in g)))
      (Post B APIf ra g) HF1 HP).
    + rewrite Hg, E1. apply sg_ret_ok; [lia | reflexivity].
    + rewrite Hg. exact E10.
    + unfold bsz. lia.
    + cbn [Datatypes.length]. lia.
    + unfold hb_bytes. cbn [map fold_right snd]. unfold bsz. lia.
    + intros L' A' regs'' mem'' md' res HF2 HP2 Hpres H10' Hres0 Hfr.
      rewrite Hg, E1. apply H748. exists nm, tk, res.
      replace (2 * NR g + 4 + 1) with (2 * NR g + 5) in HF2 by lia.
      apply (sg_cut B APIf ra empty FF g _ _ _ _ L' A' regs'' mem'' md' HF2 HP2).
      assert (HB : forall a bs, bytes_at rsegs mem a bs -> fsp g <= a -> a + Z.of_nat (length bs) <= g_S g ->
                bytes_at rsegs mem'' a bs).
      { intros a bs Hb Hlo Hhi. apply (sg_bytes_frame B APIf ra empty FF m' mem'' a bs (fsp g) (g_S g)); [| lia | lia |].
        - exact (sg_bytes_same B APIf ra empty FF mem m' a bs Hb HE).
        - intros x Hx. exact (Hfr x Hx). }
      unfold G71c, TID, TLr, G16, IDb, q64 in *.
      pose proof (rec_id_length (g_in g) (NRn g)) as Ln. unfold RcIdentModel.ID_SIZE in Ln.
      unfold spk, fsp, SLOT_FRAME in *.
      split; [split; [split | split; [| split; [| split]]] |].
      * apply HB; [exact HG16 | lia | rewrite length_le8; lia].
      * apply HB; [exact HID | lia | rewrite Ln; lia].
      * split; [sg_pres Hpres 9; rewrite Hg, E9; exact H9|].
        split; [sg_pres Hpres 18; rewrite Hg, E18; exact H18|].
        split; [sg_pres Hpres 19; rewrite Hg, E19; exact H19|].
        split; [sg_pres Hpres 24; rewrite Hg, E24; exact H24|].
        split; [sg_pres Hpres 25; rewrite Hg, E25; exact H25|].
        apply HB; [exact H40 | lia | rewrite length_le8; lia].
      * sg_pres Hpres 8. rewrite Hg, E8. exact H8.
      * sg_pres Hpres 27. rewrite Hg, E27. exact H27.
      * sg_pres Hpres 26. rewrite Hg, E26. exact H26.
      * split; [sg_pres Hpres 20; rewrite Hg, E20; exact H20|].
        split; [sg_pres Hpres 23; rewrite Hg, E23; exact H23|].
        split; [sg_pres Hpres 21; rewrite Hg, E21; reflexivity|].
        exact H10'.
Qed.

End G05.
