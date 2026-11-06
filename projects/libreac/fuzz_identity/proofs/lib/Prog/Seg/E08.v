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
  write_uint_c reac_identity_reac_ver_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : YK11.FPState}.

Lemma E08_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp s cap ma mi pa lo : Z),
  reac_identity_reac_ver_str_contract ->
  x2 = Z_to_bv 64 sp -> x10 = Z_to_bv 64 s -> x21 = Z_to_bv 64 cap ->
  0 < s < 2 ^ 64 -> 0 <= sp -> sp + 158 < 2 ^ 64 -> 0 <= cap < 32 ->
  0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  ov_read_bytes rsegs m (wa (sp + 152)) 2 = Some (le2 (Z_to_bv 64 ma)) ->
  ov_read_bytes rsegs m (wa (sp + 154)) 2 = Some (le2 (Z_to_bv 64 mi)) ->
  ov_read_bytes rsegs m (wa (sp + 156)) 2 = Some (le2 (Z_to_bv 64 pa)) ->
  stk rsegs m lo sp -> lo + 64 <= sp ->
  (20 <= cap -> wr_at rsegs m s 20 /\ s + 20 <= sp - 64) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x1361c) x2 x3 x4 t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 x18 x19
                x20 x21 (Z_to_bv 64 s) x23 x24 x25 x26 x27 t3 t4 t5 t6 /\
          r = Z_to_bv 64 (if cap <? 20 then -1 else reac_ver_str_LV ma mi pa)) /\
       pc' = Z_to_bv 64 0x1361c /\ wmono rsegs m m' /\
       (cap < 20 -> munch [(sp - 64, sp)] m m') /\
       (20 <= cap -> munch [(sp - 64, sp); (s, s + reac_ver_str_LV ma mi pa + 1)] m m' /\
          bytes_at rsegs m' s (reac_ver_str_VER ma mi pa ++ [Z_to_bv 8 0])))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x135fc) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp s cap ma mi pa lo VS E2 E10 E21 Hs Hsp Hsp2 Hc Hma Hmi Hpa R1 R2 R3 ST HL HWR.
  subst x2 x10 x21.
  step. rewrite (sf_eqb s 0) by lia. rewrite (proj2 (Z.eqb_neq s 0)) by lia. cbv iota.
  step. step. step. step. rewrite !sf_zx16 by lia. step. step. step.
  eapply evt_cut.
  { eapply VS with (ma := ma) (mi := mi) (pa := pa) (o := s) (c := cap) (lo := lo); try reflexivity; try lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia.
    - intros _ Hc20. destruct (HWR Hc20) as [W1 W2]. split; [exact W1|]. left. rewrite unsigned_lit by lia. lia. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & m' & -> & HW & _ & HIF).
  rewrite (proj2 (Z.eqb_neq s 0)) in HIF by lia. rewrite !unsigned_lit in HIF by lia.
  rewrite sf_ret_pc_lit by lia.
  destruct (Z.ltb_spec cap 20) as [Hq|Hq]; cbn [orb] in HIF.
  - destruct HIF as (Er & MU).
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 15 eexists; split; [reflexivity | exact Er]|].
    split; [reflexivity|]. split; [exact HW|]. split; [intros _; exact MU | intros Hq'; lia].
  - destruct HIF as (Er & MU & BY).
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 15 eexists; split; [reflexivity | exact Er]|].
    split; [reflexivity|]. split; [exact HW|]. split; [intros Hq'; lia | intros _; split; [exact MU | exact BY]].
Qed.

End KA.

Section E08.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis VS : reac_identity_reac_ver_str_contract.

Lemma seg_E08 : Hcut B APIf ra (Inv_K1361c B APIf ra empty) -> Hcut B APIf ra (Inv_K135fc B APIf ra empty).
Proof.
  intros HX g c (s & L & A & regs & mem & md & -> & HF & HP & HE & H10).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (sf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H21 & H20).
  set (cap := t_cap_ver (g_in g)) in *.
  assert (Hcap : 0 <= cap < 32) by (unfold cap, t_cap_ver; apply Z.mod_pos_bound; lia).
  destruct (sf_hb_blk B APIf ra empty FF g _ _ L A regs mem md s (bsz cap) HF HP (or_introl eq_refl))
    as (HBW & Hs1 & Hs2 & Hs16).
  unfold bsz in Hs2.
  set (idb := idT (g_in g)).
  pose proof (sf_LV_le (RcIdentModel.major idb) (RcIdentModel.minor idb) (RcIdentModel.patch idb)) as HLV.
  assert (Hid : forall k, (k < 3)%nat ->
    0 <= RcIdentModel.bz (RcIdentModel.nthb idb (22 + 2 * k)) + 256 * RcIdentModel.bz (RcIdentModel.nthb idb (23 + 2 * k))
      < 65536).
  { intros k _. pose proof (sf_bz_range (RcIdentModel.nthb idb (22 + 2 * k))).
    pose proof (sf_bz_range (RcIdentModel.nthb idb (23 + 2 * k))). unfold RcIdentModel.bz. lia. }
  pose proof (Hid 0%nat ltac:(lia)) as Hma. pose proof (Hid 1%nat ltac:(lia)) as Hmi.
  pose proof (Hid 2%nat ltac:(lia)) as Hpa. cbn [Nat.add Nat.mul] in Hma, Hmi, Hpa.
  pose proof HTID as (_ & HID). unfold IDb, spk in HID.
  assert (HRD : forall k, (k < 3)%nat ->
    ov_read_bytes rsegs mem (wa (fsp g + (152 + 2 * Z.of_nat k))) 2 =
    Some (le2 (Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb idb (Z.to_nat (22 + 2 * Z.of_nat k))) +
                           256 * RcIdentModel.bz (RcIdentModel.nthb idb (S (Z.to_nat (22 + 2 * Z.of_nat k)))))))).
  { intros k Hk. pose proof (sf_rd2 mem (fsp g + 130) _ (22 + 2 * Z.of_nat k) HID ltac:(lia)
      ltac:(rewrite rec_id_length; unfold RcIdentModel.ID_SIZE; lia)) as R.
    replace (fsp g + 130 + (22 + 2 * Z.of_nat k)) with (fsp g + (152 + 2 * Z.of_nat k)) in R by lia. exact R. }
  pose proof (HRD 0%nat ltac:(lia)) as R1. pose proof (HRD 1%nat ltac:(lia)) as R2.
  pose proof (HRD 2%nat ltac:(lia)) as R3. cbn [Z.of_nat Z.mul Z.add Z.to_nat] in R1, R2, R3.
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x135fc) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (E08_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) s cap
             (RcIdentModel.major idb) (RcIdentModel.minor idb) (RcIdentModel.patch idb) (g_S g - SLOT_K) VS).
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 10) by reflexivity. exact H10.
    - rewrite <- (sf_getr_reg regs 21) by reflexivity. exact H21.
    - lia.
    - lia.
    - lia.
    - exact Hcap.
    - exact Hma.
    - exact Hmi.
    - exact Hpa.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact ST.
    - lia.
    - intros Hc20. split; [|lia]. split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (proj1 (HBW i ltac:(unfold bsz; lia))) as W. rewrite SEG in W. exact W. }
  intros R pc' m' regs1 (Hreg & -> & HWM & HA & HB) XR.
  destruct Hreg as (t0 & t1 & t2 & r & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & -> & Er).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] regs regs1) by sf_kp XR regs.
  assert (G22 : getr regs1 22 = Z_to_bv 64 s) by (rewrite (sf_getr_x _ _ 22 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (ver_res idb cap))
    by (rewrite (sf_getr_x _ _ 10 XR) by reflexivity; exact Er).
  set (LV := reac_ver_str_LV (RcIdentModel.major idb) (RcIdentModel.minor idb) (RcIdentModel.patch idb)) in *.
  set (hw := if cap <? 20 then s else s + LV + 1).
  assert (MU : munch [(fsp g - 64, fsp g); (s, hw)] mem m').
  { unfold hw. destruct (Z.ltb_spec cap 20) as [Hq|Hq].
    - intros x Hx. apply (HA Hq). cbn [outside] in Hx |- *. destruct Hx as [H1 _]. split; [exact H1 | exact I].
    - exact (proj1 (HB Hq)). }
  assert (HWin : forall lo hi y, In (lo, hi) [(fsp g - 64, fsp g); (s, hw)] -> lo <= y < hi ->
                   (fsp g - 64 <= y < fsp g) \/ (s <= y < s + bsz cap)).
  { intros lo hi y Hy Hr. destruct Hy as [Hy|[Hy|[]]]; injection Hy as <- <-; [left; lia|].
    right. unfold bsz. unfold hw in Hr. destruct (Z.ltb_spec cap 20); lia. }
  assert (FRe : FReq g mem m').
  { unfold FReq. apply (sf_FReq_munch g _ mem m' MU); [| lia | lia].
    intros lo hi y Hy Hr. destruct (HWin lo hi y Hy Hr) as [H|H]; left; [lia|].
    unfold bsz in H. lia. }
  apply HX. exists s, L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (sf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(sf_in)) (KP1 3 ltac:(sf_in)) (KP1 4 ltac:(sf_in)) MU HWM).
    intros lo hi y Hy Hr. destruct (HWin lo hi y Hy Hr) as [H|H]; [left; lia | right; exact (sf_hb_in1 _ _ _ H)]. }
  split; [exact HP|].
  split; [|split; [exact G22 | split; [exact G10 | intros Hq; exact (proj2 (HB Hq))]]].
  split; [exact (sf_TID_tr g mem m' FRe HTID)|].
  split; [exact (sf_TL_kp g regs regs1 mem m' (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) FRe HTL)|].
  split; [sf_k KP1 21; exact H21 | sf_k KP1 20; exact H20].
Qed.

End E08.
