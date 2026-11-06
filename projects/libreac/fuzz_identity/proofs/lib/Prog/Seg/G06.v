From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv
  disco_box_name_model reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : YK11.FPState}.

Lemma G06_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp h dp fam cd lo : Z),
  reac_box_name_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x8 = Z_to_bv 64 h -> x10 = Z_to_bv 64 dp -> x26 = Z_to_bv 64 fam -> x27 = Z_to_bv 64 cd ->
  0 <= h < 256 -> 4096 <= dp < 2 ^ 63 -> 0 <= fam < 128 -> 0 <= cd < 64 ->
  IMG_HI <= lo -> lo + 288 <= sp -> sp + 368 <= 2 ^ 64 -> sp mod 16 = 0 ->
  stk rsegs m lo sp -> wr_at rsegs m sp 368 ->
  bytes_at rsegs m BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3)) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x1378c) x2 x3 x4 t0 t1 t2 x8 x9 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 x18 x19
                x20 x21 (Z_to_bv 64 dp) x23 x24 (Z_to_bv 64 (if h =? 0 then 0 else sp + 133)) x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x1378c /\
       munch [(sp - 288, sp + 16)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' sp (le8 (Z_to_bv 64 dp)) /\ bytes_at rsegs m' (sp + 8) (le8 (Z_to_bv 64 cd)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x13748) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp h dp fam cd lo BN HRO E2 E8 E10 E26 E27 Hh Hdp Hf Hcd HLO HL Hsp Hal ST WR HT.
  subst x2 x8 x10 x26 x27.
  unfold IMG_HI in HLO.
  step. rewrite (sf_eqb dp 0) by lia. rewrite (proj2 (Z.eqb_neq dp 0)) by lia. cbv iota.
  step. step. step. step. step.
  rewrite (sf_said h (sp + 133)) by lia.
  step. step. step.
  pose proof (wr_at_store_ok rsegs m sp 368 0 8 WR ltac:(lia) ltac:(lia)) as HS. rewrite Z.add_0_r in HS.
  step.
  match goal with |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?aa _) _) =>
    replace aa with (Z_to_bv 64 sp) by (first [reflexivity | f_equal; lia])
  end.
  remember (write_to_mem m (Z_to_bv 64 sp) (le8 (Z_to_bv 64 dp))) as m1 eqn:Em1.
  assert (W1 : wr_at rsegs m1 sp 368) by (rewrite Em1; apply wr_at_write; exact WR).
  assert (B1 : bytes_at rsegs m1 sp (le8 (Z_to_bv 64 dp)))
    by (rewrite Em1; apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (R1 : ro_agree rsegs m1).
  { rewrite Em1. apply sf_ro_write; [exact HRO | unfold IMG_HI; lia | rewrite length_le8; lia]. }
  assert (S1 : stk rsegs m1 lo sp) by (rewrite Em1; apply stk_write; [exact ST | lia | rewrite length_le8; lia]).
  assert (M1 : munch [(sp - 288, sp + 16)] m m1).
  { rewrite Em1. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m m1) by (rewrite Em1; apply wmono_write; apply wmono_refl).
  assert (T1 : bytes_at rsegs m1 BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3))).
  { rewrite Em1. apply bytes_at_write_other; [exact HT | lia | rewrite length_le8; lia |].
    rewrite !length_app, !length_le8. unfold BN_TS. lia. }
  clear Em1.
  pose proof (wr_at_store_ok rsegs m1 sp 368 8 8 W1 ltac:(lia) ltac:(lia)) as HS2.
  step.
  match goal with |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?aa _) _) =>
    replace aa with (Z_to_bv 64 (sp + 8)) by (first [reflexivity | f_equal; lia])
  end.
  remember (write_to_mem m1 (Z_to_bv 64 (sp + 8)) (le8 (Z_to_bv 64 cd))) as m2 eqn:Em2.
  assert (B2 : bytes_at rsegs m2 (sp + 8) (le8 (Z_to_bv 64 cd)))
    by (rewrite Em2; apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (B1' : bytes_at rsegs m2 sp (le8 (Z_to_bv 64 dp))).
  { rewrite Em2. apply bytes_at_write_other; [exact B1 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (R2 : ro_agree rsegs m2).
  { rewrite Em2. apply sf_ro_write; [exact R1 | unfold IMG_HI; lia | rewrite length_le8; lia]. }
  assert (S2 : stk rsegs m2 lo sp) by (rewrite Em2; apply stk_write; [exact S1 | lia | rewrite length_le8; lia]).
  assert (M2 : munch [(sp - 288, sp + 16)] m m2).
  { rewrite Em2. apply munch_write; [exact M1 | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM2 : wmono rsegs m m2) by (rewrite Em2; apply wmono_write; exact WM1).
  assert (T2 : bytes_at rsegs m2 BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3))).
  { rewrite Em2. apply bytes_at_write_other; [exact T1 | lia | rewrite length_le8; lia |].
    rewrite !length_app, !length_le8. unfold BN_TS. lia. }
  clear Em2.
  step. step. step. step. step. step.
  eapply (sf_box_name_call BN) with (lo := lo) (f := fam) (i := 8) (o := 8) (display := Z_to_bv 64 dp)
    (display_len := Z_to_bv 64 cd) (sd := []).
  - exact R2.
  - reflexivity.
  - lia.
  - reflexivity.
  - lia.
  - reflexivity.
  - lia.
  - rewrite (unsigned_lit sp) by lia. apply bytes_at_app. split; [exact B1'|].
    rewrite length_le8. replace (sp + Z.of_nat 8) with (sp + 8) by lia. exact B2.
  - rewrite (unsigned_lit sp) by lia. exact S2.
  - rewrite (unsigned_lit sp) by lia. unfold BN_K. lia.
  - rewrite (unsigned_lit sp) by lia. exact Hal.
  - unfold IMG_HI. lia.
  - exact T2.
  - intros HA. exfalso. vm_compute in HA. discriminate HA.
  - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' WM RO HIF.
    match type of HIF with (if ?b then _ else _) =>
      replace b with false in HIF by (symmetry; vm_compute; reflexivity) end.
    destruct HIF as (-> & MU).
    rewrite (unsigned_lit sp) in MU by lia. unfold BN_K in MU.
    rewrite sf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 14 eexists; reflexivity|].
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m m2 m' M2). eapply munch_weaken; [|exact MU]. sf_subfp. }
    split; [eapply wmono_trans; [exact WM2 | exact WM]|].
    split; [exact RO|].
    split.
    + apply (bytes_at_transport rsegs _ m2 m' _ _ B1' MU). cbn [disjoint_from]. rewrite length_le8.
      split; [right; lia | exact I].
    + apply (bytes_at_transport rsegs _ m2 m' _ _ B2 MU). cbn [disjoint_from]. rewrite length_le8.
      split; [right; lia | exact I].
Qed.

End KA.

Section G06.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BN : reac_box_name_contract.

Lemma seg_G06 : Hcut B APIf ra (Inv_K1378c B APIf ra empty) -> Hcut B APIf ra (Inv_K13748 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & L & A & regs & mem & md & -> & HF & HP & (HG & H20 & H23 & H21 & H10)).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & _).
  destruct (sf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HG as (HTID & (H9 & H18 & H19 & H24 & H25 & H40) & H8 & H27 & H26).
  destruct (sf_hb_blk B APIf ra empty FF g _ _ L A regs mem md dp (bsz (t_cap_disp (g_in g))) HF HP
              ltac:(right; right; left; reflexivity)) as (_ & Hd1 & Hd2 & _).
  set (h := RcIdentModel.has_model_name (idT (g_in g))) in *.
  assert (Hh8 : 0 <= h < 256) by (unfold h, RcIdentModel.has_model_name; apply sf_bz_range).
  pose proof (sf_nfam_range (g_in g)) as Hfam.
  assert (Hcd : 0 <= t_cap_disp (g_in g) < 64) by (unfold t_cap_disp; apply Z.mod_pos_bound; lia).
  assert (WR : wr_at rsegs mem (fsp g) 368).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  pose proof (sf_bn_ts B APIf ra empty FF mem Hrel) as HT.
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x13748) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (G06_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) h dp (n_fam (g_in g))
             (t_cap_disp (g_in g)) (g_S g - SLOT_K) BN).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 8) by reflexivity. exact H8.
    - rewrite <- (sf_getr_reg regs 10) by reflexivity. exact H10.
    - rewrite <- (sf_getr_reg regs 26) by reflexivity. exact H26.
    - rewrite <- (sf_getr_reg regs 27) by reflexivity. exact H27.
    - exact Hh8.
    - unfold bsz in Hd2. lia.
    - lia.
    - exact Hcd.
    - exact HI.
    - lia.
    - lia.
    - unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    - exact ST.
    - exact WR.
    - exact HT. }
  intros R pc' m' regs1 (Hreg & -> & MU & WM & RO & B0 & B8) XR.
  destruct Hreg as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26; 27] regs regs1) by sf_kp XR regs.
  assert (G22 : getr regs1 22 = Z_to_bv 64 dp) by (rewrite (sf_getr_x _ _ 22 XR) by reflexivity; reflexivity).
  assert (G25 : getr regs1 25 = Z_to_bv 64 (said_v g)).
  { rewrite (sf_getr_x _ _ 25 XR) by reflexivity. unfold said_v, n_said, spk. fold h.
    destruct (h =? 0); reflexivity. }
  assert (G10 : getr regs1 10 = Z_to_bv 64 (-1)) by (rewrite (sf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
  assert (OUT : FRout g [(fsp g - 288, fsp g + 16)]).
  { intros lo hi y Hy Hr. destruct Hy as [Hy|[]]. injection Hy as <- <-. unfold spk. lia. }
  assert (B40 : q64 m' (spk g 40) (t_cap_disp (g_in g))).
  { unfold q64 in *. apply (bytes_at_transport rsegs _ mem m' _ _ H40 MU). cbn [disjoint_from]. rewrite length_le8.
    unfold spk. split; [right; lia | exact I]. }
  apply HX. exists nm, tk, dp, L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (sf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(sf_in)) (KP1 3 ltac:(sf_in)) (KP1 4 ltac:(sf_in)) MU WM).
    intros lo hi y Hy Hr. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
  split; [exact HP|].
  split; [|exact G10].
  split; [exact (sf_TID_munch g _ mem m' MU OUT HTID)|].
  split; [sf_k KP1 8; exact H8|]. split; [sf_k KP1 9; exact H9|]. split; [sf_k KP1 18; exact H18|].
  split; [sf_k KP1 19; exact H19|]. split; [sf_k KP1 20; exact H20|]. split; [sf_k KP1 21; exact H21|].
  split; [exact G22|]. split; [sf_k KP1 23; exact H23|]. split; [sf_k KP1 24; exact H24|].
  split; [exact G25|]. split; [sf_k KP1 26; exact H26|]. split; [sf_k KP1 27; exact H27|].
  split; [exact B40|].
  split; [unfold q64, spk; rewrite Z.add_0_r; exact B0 | unfold q64, spk; exact B8].
Qed.

End G06.
