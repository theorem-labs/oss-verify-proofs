From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv
  reac_identity_fw_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : YK11.FPState}.

Lemma E02_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp s cap t9 t10 v : Z),
  reac_identity_fw_str_contract ->
  x2 = Z_to_bv 64 sp -> x10 = Z_to_bv 64 s -> x22 = Z_to_bv 64 cap -> x20 = Z_to_bv 64 t10 -> x27 = Z_to_bv 64 t9 ->
  0 < s < 2 ^ 64 -> 0 <= sp -> sp + 132 < 2 ^ 64 -> 0 <= cap < 16 -> 0 <= t9 < 256 -> 0 <= t10 < 256 ->
  0 <= v < 65536 ->
  ov_read_bytes rsegs m (wa (sp + 130)) 2 = Some (le2 (Z_to_bv 64 v)) ->
  (8 <= cap -> wr_at rsegs m s 8) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x135c0) x2 x3 x4 t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 x18 x19
                (Z_to_bv 64 (t9 + 256 * t10)) x21 x22 (Z_to_bv 64 s) x24 x25 x26 x27 t3 t4 t5 t6 /\
          r = Z_to_bv 64 (fw_res v cap)) /\
       pc' = Z_to_bv 64 0x135c0 /\ wmono rsegs m m' /\
       (cap < 8 -> m' = m) /\
       (8 <= cap -> bytes_at rsegs m' s (FW v ++ [Z_to_bv 8 0]) /\ munch [(s, s + L v + 1)] m m'))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x135a0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp s cap t9 t10 v FWS E2 E10 E22 E20 E27 Hs Hsp Hsp2 Hc H9 H10 Hv HRD HWR.
  subst x2 x10 x22 x20 x27.
  step. rewrite (sf_eqb s 0) by lia. rewrite (proj2 (Z.eqb_neq s 0)) by lia. cbv iota.
  step. step. rewrite sf_zx16 by lia. step. step. rewrite sf_lor8 by lia. step. step. step.
  eapply evt_cut.
  { eapply FWS; try reflexivity; try lia. intros _ Hc8. exact (HWR Hc8). }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & HW
    & HA & HB).
  rewrite sf_ret_pc_lit by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split.
  { do 15 eexists. split; [reflexivity|]. unfold fw_res.
    destruct (Z.ltb_spec cap 8) as [Hl|Hl]; [exact (proj1 (HA (or_intror Hl)))|].
    exact (proj1 (HB ltac:(lia) Hl)). }
  split; [reflexivity|]. split; [exact HW|].
  split; [intros Hl; exact (proj2 (HA (or_intror Hl)))|].
  intros Hl. exact (proj2 (HB ltac:(lia) Hl)).
Qed.

End KA.

Section E02.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FWS : reac_identity_fw_str_contract.

Lemma seg_E02 : Hcut B APIf ra (Inv_K135c0 B APIf ra empty) -> Hcut B APIf ra (Inv_K135a0 B APIf ra empty).
Proof.
  intros HX g c (s & L & A & regs & mem & md & -> & HF & HP & HD & H10).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HD as (HTID & HTL & H22 & H21 & H27 & H20).
  set (cap := t_cap_fw (g_in g)) in *.
  assert (Hcap : 0 <= cap < 16) by (unfold cap, t_cap_fw; apply Z.mod_pos_bound; lia).
  destruct (sf_hb_blk B APIf ra empty FF g _ _ L A regs mem md s (bsz cap) HF HP (or_introl eq_refl))
    as (HBW & Hs1 & Hs2 & Hs16).
  assert (Hbsz : 1 <= bsz cap) by (unfold bsz; lia).
  pose proof (inb_range (g_in g) (cT (g_in g) + 9)) as H9r.
  pose proof (inb_range (g_in g) (cT (g_in g) + 10)) as H10r.
  set (v := fwT g).
  assert (Hv : 0 <= v < 65536).
  { unfold v, fwT, RcIdentModel.fw_milli. pose proof (sf_bz_range (RcIdentModel.nthb (idT (g_in g)) 0)).
    pose proof (sf_bz_range (RcIdentModel.nthb (idT (g_in g)) 1)). unfold RcIdentModel.bz. lia. }
  assert (HRD : ov_read_bytes rsegs mem (wa (fsp g + 130)) 2 = Some (le2 (Z_to_bv 64 v))).
  { destruct HTID as [_ HID]. unfold IDb, spk in HID.
    pose proof (sf_rd2 mem (fsp g + 130) _ 0 HID ltac:(lia)
                  ltac:(rewrite rec_id_length; unfold RcIdentModel.ID_SIZE; cbn; lia)) as R.
    rewrite Z.add_0_r in R. exact R. }
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x135a0) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (E02_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) s cap
             (tb (g_in g) 9) (tb (g_in g) 10) v FWS).
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 10) by reflexivity. exact H10.
    - rewrite <- (sf_getr_reg regs 22) by reflexivity. exact H22.
    - rewrite <- (sf_getr_reg regs 20) by reflexivity. exact H20.
    - rewrite <- (sf_getr_reg regs 27) by reflexivity. exact H27.
    - lia.
    - unfold fsp, SLOT_FRAME. unfold SLOT_K, SLOT_STACK in HSc. lia.
    - unfold fsp, SLOT_FRAME. unfold SLOT_K, SLOT_STACK in HSc. lia.
    - exact Hcap.
    - exact H9r.
    - exact H10r.
    - exact Hv.
    - exact HRD.
    - intros Hc8. split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (proj1 (HBW i ltac:(unfold bsz; lia))) as W. rewrite SEG in W. exact W. }
  intros R pc' m' regs1 (Hreg & -> & HWM & HA & HB) XR.
  destruct Hreg as (t0 & t1 & t2 & r & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & -> & Er).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 25] regs regs1) by sf_kp XR regs.
  assert (G20 : getr regs1 20 = Z_to_bv 64 (t_any_fw (g_in g)))
    by (rewrite (sf_getr_x _ _ 20 XR) by reflexivity; reflexivity).
  assert (G23 : getr regs1 23 = Z_to_bv 64 s) by (rewrite (sf_getr_x _ _ 23 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (fw_res (fwT g) cap))
    by (rewrite (sf_getr_x _ _ 10 XR) by reflexivity; exact Er).
  assert (HU : forall x, 0 <= x < 2 ^ 64 -> ~ in_hb [(s, bsz cap)] x -> m' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Hn. destruct (Z.ltb_spec cap 8) as [Hq|Hq]; [rewrite (HA Hq); reflexivity|].
    destruct (HB Hq) as (_ & Hm). apply Hm. rewrite unsigned_lit by exact Hx. cbn [outside]. split; [|exact I].
    pose proof (reac_identity_fw_str_c3_len v Hv) as (_ & HL). intros Hr. apply Hn. apply sf_hb_in1.
    unfold bsz. destruct (v <? 10000); lia. }
  pose proof (sf_FReq_hb B APIf ra empty FF g _ _ L A regs mem md m' HF HP HU) as FRe.
  apply HX. exists s, L, A, regs1, m', md. split; [reflexivity|].
  split; [exact (sf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 m' HF HP
                   (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) HU HWM)|].
  split; [exact HP|].
  split; [|split; [exact G10 | intros Hq; exact (proj1 (HB Hq))]].
  split; [exact (sf_TID_tr g mem m' FRe HTID)|].
  split; [exact (sf_TL_kp g regs regs1 mem m' (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) FRe HTL)|].
  split; [sf_k KP1 21; exact H21|]. split; [sf_k KP1 22; exact H22|]. split; [exact G23 | exact G20].
Qed.

End E02.
