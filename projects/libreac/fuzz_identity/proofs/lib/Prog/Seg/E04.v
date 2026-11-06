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

Lemma E04_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (s cap v : Z),
  reac_identity_fw_str_contract ->
  x20 = Z_to_bv 64 v -> x23 = Z_to_bv 64 s -> x22 = Z_to_bv 64 cap ->
  0 < s < 2 ^ 64 -> 0 <= cap < 16 -> 0 <= v < 65536 ->
  (8 <= cap -> wr_at rsegs m s 8) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x135dc) x2 x3 x4 t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 x18 x19
                x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 /\
          r = Z_to_bv 64 (fw_res v cap)) /\
       pc' = Z_to_bv 64 0x135dc /\ wmono rsegs m m' /\
       (cap < 8 -> m' = m) /\
       (8 <= cap -> bytes_at rsegs m' s (FW v ++ [Z_to_bv 8 0]) /\ munch [(s, s + L v + 1)] m m'))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x135cc) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m s cap v FWS E20 E23 E22 Hs Hc Hv HWR.
  subst x20 x23 x22.
  step. step. step. step.
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

Section E04.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FWS : reac_identity_fw_str_contract.

Lemma seg_E04 : Hcut B APIf ra (Inv_K135dc B APIf ra empty) -> Hcut B APIf ra (Inv_K135cc B APIf ra empty).
Proof.
  intros HX g c (s & L & A & regs & mem & md & -> & HF & HP & HE & HO).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H21 & H22 & H23 & H20).
  set (cap := t_cap_fw (g_in g)) in *.
  assert (Hcap : 0 <= cap < 16) by (unfold cap, t_cap_fw; apply Z.mod_pos_bound; lia).
  destruct (sf_hb_blk B APIf ra empty FF g _ _ L A regs mem md s (bsz cap) HF HP (or_introl eq_refl))
    as (HBW & Hs1 & Hs2 & Hs16).
  assert (Hbsz : 1 <= bsz cap) by (unfold bsz; lia).
  set (v := t_any_fw (g_in g)) in *.
  assert (Hv : 0 <= v < 65536).
  { unfold v, t_any_fw, tb. pose proof (inb_range (g_in g) (cT (g_in g) + 9)).
    pose proof (inb_range (g_in g) (cT (g_in g) + 10)). lia. }
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x135cc) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (E04_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem s cap v FWS).
    - rewrite <- (sf_getr_reg regs 20) by reflexivity. exact H20.
    - rewrite <- (sf_getr_reg regs 23) by reflexivity. exact H23.
    - rewrite <- (sf_getr_reg regs 22) by reflexivity. exact H22.
    - lia.
    - exact Hcap.
    - exact Hv.
    - intros Hc8. split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (proj1 (HBW i ltac:(unfold bsz; lia))) as W. rewrite SEG in W. exact W. }
  intros R pc' m' regs1 (Hreg & -> & HWM & HA & HB) XR.
  destruct Hreg as (t0 & t1 & t2 & r & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & -> & Er).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25] regs regs1) by sf_kp XR regs.
  assert (G10 : getr regs1 10 = Z_to_bv 64 (fw_res v cap))
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
  split; [sf_k KP1 21; exact H21|]. split; [sf_k KP1 22; exact H22|].
  split; [sf_k KP1 23; exact H23 | sf_k KP1 20; exact H20].
Qed.

End E04.
