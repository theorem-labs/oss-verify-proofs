From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem
  fuzz_alloc_live_c fuzz_alloc_fail_c check_reject_clean_c KindB.
Import ListNotations.
Open Scope Z_scope.

Lemma crcs_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (live count : word),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x50000 <= lo ->
  bytes_at rsegs m G_LIVE (le8 live) -> bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 ->
  fuzz_alloc_live_contract -> fuzz_alloc_fail_contract ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x132d0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a1 a0 a0 a1 a2 a3 a4 a5 a6 a7
                    live s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13c1c) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
      bytes_at rsegs m' G_FAIL_AT (le8 (fail_at_of count (Z_to_bv 64 0))) /\
      munch ([(bv_unsigned sp + -32, bv_unsigned sp)] ++ [(G_FAIL_AT, G_FAIL_AT + 8)]) m m' /\
      wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13298) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    live count ST LO LO5 BL BC WF LIVE FAIL.
  unfold G_LIVE, G_COUNT, G_FAIL_AT in *.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  carve_frame 32%nat ST.
  do 8 zstep.
  eapply evt_cut; [eapply LIVE; exact BL|]. intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x132b8)) with (Z_to_bv 64 0x132b8) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  eapply evt_cut; [eapply FAIL; [exact BC | exact WF] |].
  intros ms' (a1' & m2 & E & BF & MUf & WMf). subst ms'.
  replace (ret_pc (Z_to_bv 64 0x132c4)) with (Z_to_bv 64 0x132c4) by (apply bv_eq; vm_compute; reflexivity).
  unfold G_FAIL_AT in MUf, BF.
  pose proof MUf as MUf0.
  pose proof (munch_cat _ _ _ _ _ MU MUf0) as MUa. clear MU.
  transport_after_call rsegs m1 m2 MUf WMf.
  do 3 zstep.
  apply evt_done. exists m2. split; [reflexivity|].
  split; [exact FR|]. split; [exact BF|].
  split; [exact MUa|]. exact WM.
Qed.

Lemma crcs_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (count xra xs0 xs1 xs2 : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> 0x50000 <= lo -> bv_unsigned sp + 32 < 2 ^ 64 ->
  ro_agree rsegs m ->
  bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 -> bytes_at rsegs m G_LIVE (le8 s2) ->
  fuzz_alloc_fail_contract -> check_reject_clean_contract ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0' t1' t2' xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7'
                    xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc xra) fc None m' (seg_rom rsegs) /\
      bytes_at rsegs m' G_FAIL_AT (le8 (fail_at_of count (Z_to_bv 64 (-1)))) /\
      munch ([(G_FAIL_AT, G_FAIL_AT + 8)] ++ [(bv_unsigned sp + 16, bv_unsigned sp + 32)]) m m' /\
      wmono rsegs m m' /\ ro_agree rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x132d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    count xra xs0 xs1 xs2 FR ST LOs LO5 HI RA BC WF BL FAIL CRC.
  unfold G_LIVE, G_COUNT, G_FAIL_AT in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 2 zstep.
  eapply evt_cut; [eapply FAIL; [exact BC | exact WF] |].
  intros ms' (a1' & m2 & E & BF & MUf & WMf). subst ms'.
  replace (ret_pc (Z_to_bv 64 0x132d8)) with (Z_to_bv 64 0x132d8) by (apply bv_eq; vm_compute; reflexivity).
  unfold G_FAIL_AT in MUf, BF.
  pose proof MUf as MUf0. pose proof WMf as WMf0.
  assert (RA2 : ro_agree rsegs m2).
  { apply (ro_agree_munch _ m m2 RA MUf0). intros x Hx. apply outside_one. lia. }
  transport_after_call rsegs m m2 MUf WMf.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp + 32).
  assert (U32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 32)) = bv_unsigned sp + 32)
    by (apply inr64_unsigned_lit; unfold inr64; lia).
  pose proof (mem_rel_normalize rsegs m2 RA2) as MRm.
  eapply evt_cut.
  { eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA2 |].
    eapply CRC.
    - exact (bytes_at_normalize rsegs _ _ _ RA2 BL).
    - exact (mem_inv_normalize rsegs m2).
    - rewrite U32. apply stk_normalize; [exact ST | lia].
    - rewrite U32. unfold CHECK_REJECT_CLEAN_FRAME. lia.
    - rewrite U32. unfold G_LIVE, CHECK_REJECT_CLEAN_FRAME. left. lia. }
  intros ss (ss0 & POST & REL & ROS).
  destruct POST as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 &
    E & MUc & WMc & MIc & STc). subst ss0.
  destruct (rel_shape _ _ _ _ _ _ _ _ REL) as [Es MR3].
  remember (ms_mem ss) as m4 eqn:Em4. rewrite Es. clear Es Em4 REL ss.
  pose proof (munch_rel rsegs _ m2 _ m4 m3 MRm MR3 ROS MUc) as MU4.
  pose proof (wmono_rel rsegs m2 _ m4 m3 MRm MR3 ROS WMc) as WM4.
  pose proof (ro_agree_same rsegs m2 m4 RA2 ROS) as RA4.
  rewrite U32 in MU4. unfold CHECK_REJECT_CLEAN_FRAME in MU4.
  apply evt_done. do 15 eexists. exists m4. split; [reflexivity|].
  split; [eapply bytes_at_transport; [exact BF | exact MU4 | cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I]]|].
  split; [replace (bv_unsigned sp + 16) with (bv_unsigned sp + 32 - 16) by lia; exact (munch_cat _ _ _ _ _ MUf0 MU4)|].
  split; [exact (wmono_trans _ _ _ _ WMf0 WM4) | exact RA4].
Qed.

Lemma fail_at_zero : forall c, 0 <= c < 2 ^ 64 -> fail_at_of (Z_to_bv 64 c) (Z_to_bv 64 0) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold fail_at_of. rewrite (inr64_unsigned_lit c) by (unfold inr64; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r.
  destruct (c <? 2 ^ 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. lia.
Qed.

Lemma fail_at_max : forall c, 0 <= c < 2 ^ 64 -> fail_at_of (Z_to_bv 64 c) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1).
Proof.
  intros c Hc. unfold fail_at_of. rewrite (inr64_unsigned_lit c) by (unfold inr64; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 (-1)) = 2 ^ 64 - 1) by (vm_compute; reflexivity). rewrite E1.
  destruct (c + (2 ^ 64 - 1) <? 2 ^ 64) eqn:E; [apply Z.ltb_lt in E; f_equal; lia | reflexivity].
Qed.

Lemma gfail_wr : forall m, wr_at rsegs m G_FAIL_AT 8.
Proof.
  intros m. unfold G_FAIL_AT. split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; unfold wview;
    (destruct (m _); [discriminate | intros H; vm_compute in H; discriminate H]).
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger ManifestB names_c
  check_reject_clean_starved_c.
Local Open Scope Z_scope.

Lemma lsum_nonneg : forall Lam : list (Z * Z), Forall (fun ak => 0 <= snd ak) Lam -> 0 <= lsum Lam.
Proof.
  induction Lam as [|[a k] Lam IH]; intros H; cbn; [lia|].
  inversion H as [|? ? Hk Hr]; subst. cbn in Hk. specialize (IH Hr). lia.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis ERR : errno_low B.
Hypothesis SF : statics_free B MR.
Hypothesis SFA : statics_facts B.
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis GS : guard_syms B.

Lemma MR_static : forall L A m m' md W, MR L A m md -> munch W m m' ->
  (forall x, 0 <= x < alloc_ceiling -> ~ alloc_statics x -> outside W x) -> MR L A m' md.
Proof.
  intros L A m m' md W HM HW Ho. pose proof alloc_ceiling_val as Hac.
  destruct (mr_model _ _ (aa_laws API) L A m md HM) as (Hh & Hl & Hm).
  eapply (mr_frame _ _ (aa_laws API) L A m m' md md HM).
  - intros a Hown. pose proof (mr_owned_low _ _ (aa_laws API) L A m md a HM Hown).
    apply (mbyte_munch _ W); [exact HW | lia | apply Ho; [lia | intros Hs; exact (SF L A m md a HM Hs Hown)]].
  - intros a Hown Hp. pose proof (mr_owned_low _ _ (aa_laws API) L A m md a HM Hown).
    apply (present_munch W m); [exact HW | lia | apply Ho; [lia | intros Hs; exact (SF L A m md a HM Hs Hown)] | exact Hp].
  - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L A m md p n i HM Hin Hi) as (Hp & H1 & H2 & _).
    apply (present_munch W m); [exact HW | lia | | exact Hp].
    apply Ho; [lia|]. intros Hs.
    exact (YL01.ax_blocks_img AX L A m md p n i HM Hin Hi (proj1 (SFA _ Hs))).
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hm.
Qed.

Lemma ledger_set_fail : forall L A m md m' W Lam peak cnt fail fail', MR L A m md ->
  ledger B L A m Lam peak cnt fail -> munch W m m' ->
  (forall x, 0 <= x < alloc_ceiling -> ~ alloc_statics x -> outside W x) ->
  (forall x, G_LIVE <= x < G_COUNT + 8 -> outside W x) ->
  word_mem (ms_segs B) m' G_FAIL fail' -> 0 <= fail' < 2 ^ 64 -> ledger B L A m' Lam peak cnt fail'.
Proof.
  intros L A m md m' W Lam peak cnt fail fail' HM (AW & R1 & R2 & R3 & ND & FA) HW Ho Ho2 HF HfR.
  pose proof alloc_ceiling_val as Hac.
  destruct AW as (WL & WP & WC & _).
  split.
  { unfold alloc_words. unfold G_LIVE, G_PEAK, G_COUNT in *. split; [|split; [|split]].
    - apply (word_mem_munch _ W m m'); [exact HW | lia | lia | intros x Hx; apply Ho2; lia | exact WL].
    - apply (word_mem_munch _ W m m'); [exact HW | lia | lia | intros x Hx; apply Ho2; lia | exact WP].
    - apply (word_mem_munch _ W m m'); [exact HW | lia | lia | intros x Hx; apply Ho2; lia | exact WC].
    - exact HF. }
  split; [exact R1|]. split; [exact R2|]. split; [exact HfR|]. split; [exact ND|].
  eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Himg). cbn [fst snd] in *.
  split; [exact Hk|]. split; [exact Hin|]. split; [|exact Himg].
  pose proof (KindB.blocks_low B API L A m md (a - 16) (k + 16) 0 HM Hin ltac:(lia)) as B0.
  pose proof (KindB.blocks_low B API L A m md (a - 16) (k + 16) 7 HM Hin ltac:(lia)) as B7.
  apply (word_mem_munch _ W m m'); [exact HW | lia | lia | | exact Hw].
  intros x Hx. apply Ho; [lia|].
  replace x with ((a - 16) + (x - (a - 16))) by lia.
  apply (KindB.static_not_block B API SFA AX L A m md (a - 16) (k + 16) (x - (a - 16)) HM Hin). lia.
Qed.

Theorem check_reject_clean_starved_holds : fuzz_alloc_live_contract -> fuzz_alloc_fail_contract ->
  (forall fx', @names_contract fx' rc B API) -> check_reject_clean_contract ->
  check_reject_clean_starved_contract B API.
Proof.
  intros LIVE FAIL NAMES CRC. unfold check_reject_clean_starved_contract.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail SEG PRE INIT TS FRM RA GC CT CU HT HU T4 U4 LT LU IMG DT DU
    OT OU LG QT RES CAP BY0 BYQ.
  pose proof CT as (_ & _ & CTa). pose proof CU as (_ & _ & CUa).
  pose proof alloc_ceiling_val as Hacv.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  assert (EK : CHECK_REJECT_CLEAN_STARVED_K = 8448%Z) by reflexivity. rewrite EK in *.
  assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  pose proof (zr_word (reg_get regs 2)) as Rsp. unfold inr64 in Rsp. rewrite SP in Rsp.
  destruct QT as (QF & QC0 & QC1).
  pose proof LG as ((WL & WP & WC & WFl) & LR1 & LR2 & LR3 & LND & LFA).
  assert (LS0 : 0 <= lsum Lam).
  { apply lsum_nonneg. eapply Forall_impl; [|exact LFA]. intros [a k] (Hk & _). exact Hk. }
  rewrite SEG in WL, WC.
  assert (STK : stk rsegs mem (spZ regs - 8448) (spZ regs)).
  { apply stk_of_writable; [lia | unfold spZ in *; lia |].
    intros a Ha. rewrite <- SEG. apply HWS. exact Ha. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (crcs_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (spZ regs - 8448)
              (Z_to_bv 64 (lsum Lam)) (Z_to_bv 64 cnt)).
    - exact STK.
    - rewrite SP. lia.
    - lia.
    - apply word_mem_bytes; [lia | unfold fuzz_alloc_live_c.G_LIVE; lia | unfold fuzz_alloc_live_c.G_LIVE; lia | exact WL].
    - apply word_mem_bytes; [lia | unfold fuzz_alloc_fail_c.G_COUNT; lia | unfold fuzz_alloc_fail_c.G_COUNT; lia | exact WC].
    - exact (gfail_wr mem).
    - exact LIVE.
    - exact FAIL. }
  intros ms1 (can & (m1 & Ecan & FR & BF & MU1 & WM1) & EQV). subst can.
  apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
  set (regs1 := ms_regs ms1) in *.
  rewrite SP in MU1, FR. unfold G_FAIL_AT in MU1.
  assert (RA1 : ro_agree rsegs m1).
  { apply (ro_agree_munch _ mem m1 RA MU1). intros x Hx. cbn [outside app]. split; [lia|]. split; [lia | exact I]. }
  assert (GC1 : guard_cells B m1).
  { apply (guard_cells_munch B mem m1 _ GS GC MU1). intros x Hx. cbn [outside app]. split; [lia|]. split; [lia | exact I]. }
  rewrite (fail_at_zero cnt ltac:(lia)) in BF.
  apply bytes_word_mem in BF; [|lia].
  assert (R1 : getr regs1 1 = Z_to_bv 64 0x132d0) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (S32 : bv_unsigned (getr regs1 2) = spZ regs - 32).
  { rewrite <- (getr_eqv _ _ XR1).
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -32)) = spZ regs - 32).
    rewrite SP. rewrite (inr64_unsigned_lit _) by (unfold inr64; lia). lia. }
  assert (R10 : getr regs1 10 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R11 : getr regs1 11 = getr regs 11) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R4 : getr regs1 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R18 : getr regs1 18 = Z_to_bv 64 (lsum Lam)) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  unfold off_stack in DT, DU.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in DT, DU.
  unfold off_statics, G_LIVE, G_COUNT, G_FAIL in OT, OU.
  assert (OW1 : forall x, 0 <= x < alloc_ceiling -> ~ alloc_statics x ->
     outside ([(spZ regs + -32, spZ regs)] ++ [(127224, 127232)]) x).
  { intros x Hx Hs. cbn [outside app]. split; [lia|]. split; [|exact I].
    intros Hg. apply Hs. unfold alloc_statics, G_FAIL. lia. }
  assert (HM1 : aa_MR API L A m1 md) by exact (MR_static L A mem m1 md _ HM MU1 OW1).
  assert (LG1 : ledger B L A m1 Lam peak cnt cnt).
  { apply (ledger_set_fail L A mem md m1 _ Lam peak cnt fail cnt HM LG MU1 OW1).
    - intros x Hx. cbn [outside app]. unfold G_FAIL_AT.
      cbv delta [Ledger.G_LIVE Ledger.G_COUNT fuzz_alloc_live_c.G_LIVE fuzz_alloc_fail_c.G_COUNT] in Hx.
      split; [lia|]. split; [lia | exact I].
    - rewrite SEG. exact BF.
    - lia. }
  replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
  eapply SR_bind.
  { apply (NAMES fx L A regs1 m1 md b tb ts ub us Lam peak cnt cnt).
    - exact SEG.
    - unfold call_pre_k. unfold spZ at 1 2 3 4 5. rewrite S32.
      split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite R1; apply ret_ok_even; vm_compute; reflexivity|].
      split; [Z.div_mod_to_equations; lia|].
      split; [unfold NAMES_K, READINGS_KB, ALLOC_STACK; lia|].
      split; [lia|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HWS.
        unfold NAMES_K, READINGS_KB, ALLOC_STACK in Ha. lia. }
      split; [rewrite R4; exact HTP|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HER. exact Ha. }
      intros H. rewrite INIT in H. discriminate.
    - exact INIT.
    - rewrite S32. change (bv_unsigned (getr regs 2)) with (spZ regs) in TS. lia.
    - exact FRM.
    - exact RA1.
    - exact GC1.
    - rewrite R10. eapply cstr_munch; [exact CT | exact MU1 |]. cbn [app disjoint_from].
      split; [lia|]. split; [unfold G_FAIL in OT; lia | exact I].
    - rewrite R11. eapply cstr_munch; [exact CU | exact MU1 |]. cbn [app disjoint_from].
      split; [lia|]. split; [unfold G_FAIL in OU; lia | exact I].
    - rewrite R10. exact HT.
    - rewrite R11. exact HU.
    - rewrite R10. exact T4.
    - rewrite R11. exact U4.
    - exact LT.
    - exact LU.
    - exact (img_strings_keep mem m1 RA RA1 IMG).
    - unfold off_stack. rewrite S32, R10. unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - unfold off_stack. rewrite S32, R11. unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - unfold off_stack. rewrite S32. unfold NAMES_K, READINGS_KB, ALLOC_STACK, PREFIX_LC_STR. left. lia.
    - unfold off_stack. rewrite S32. unfold NAMES_K, READINGS_KB, ALLOC_STACK, PREFIX_UC_STR. left. lia.
    - unfold off_stack. rewrite S32. unfold NAMES_K, READINGS_KB, ALLOC_STACK, FMT_WHOLE_STR. left. lia.
    - rewrite R10. exact OT.
    - rewrite R11. exact OU.
    - exact LG1.
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' POST.
  destruct POST as (fx2 & L' & A' & regs2 & mem2 & md' & res & -> & FRM2 & INIT2 & BP & RES10 & (ts2 & CT2) &
    (us2 & CU2) & ARMS & SLOTS).
  pose proof BP as (HM2 & HWF2 & HBD2 & RP2 & HMD & HBL & HBB & HFR & HSC & RA2 & GK2).
  rewrite SEG in HFR, HSC, RA2.
  destruct (mr_model _ _ (aa_laws API) L' A' mem2 md' HM2) as (Hh2 & Hl2 & _).
  assert (LG2 : exists cnt2 fl2, ledger B L' A' mem2 Lam peak cnt2 fl2 /\
                  ((ub = [] /\ cnt2 = cnt) \/ (ub <> [] /\ cnt2 = cnt + 1))).
  { destruct ARMS as [(Eub & _ & L2) | [(Nub & _ & _ & L2) | (_ & Ncf & _)]].
    - exists cnt, cnt. split; [exact L2 | left; split; [exact Eub | reflexivity]].
    - exists ((cnt + 1) mod 2 ^ 64), (2 ^ 64 - 1). split; [exact L2|]. right. split; [exact Nub|].
      apply Z.mod_small. lia.
    - exfalso. apply Ncf. reflexivity. }
  destruct LG2 as (cnt2 & fl2 & LG2 & HCN).
  pose proof LG2 as ((WL2 & WP2 & WC2 & WF2) & L2R1 & L2R2 & L2R3 & _ & _).
  rewrite SEG in WL2, WC2.
  assert (CS : forall k, callee_saved k -> getr regs2 (Z_to_bv 5 k) = getr regs1 (Z_to_bv 5 k)) by exact RP2.
  assert (S2 : bv_unsigned (reg_get regs2 2) = spZ regs - 32).
  { change (bv_unsigned (getr regs2 (Z_to_bv 5 2)) = spZ regs - 32).
    rewrite (CS 2 ltac:(unfold callee_saved; lia)). exact S32. }
  assert (Q18 : reg_get regs2 18 = Z_to_bv 64 (lsum Lam)).
  { change (getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 (lsum Lam)). rewrite (CS 18 ltac:(unfold callee_saved; lia)).
    exact R18. }
  rewrite R10 in CT2. rewrite R11 in CU2.
  destruct (cstr_trim _ _ _ _ CT2) as (sl & CT2' & Lsl). destruct (cstr_trim _ _ _ _ CU2) as (slu & CU2' & Lslu).
  rewrite R1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (crcs_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2
              (spZ regs - 32 - NAMES_K) (Z_to_bv 64 cnt2) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)).
    - rewrite S2. replace (spZ regs - 32) with (spZ regs + -32) by lia.
      apply (rw_cells_keep m1 mem2 _ _ FR). intros a Ha. cbn in Ha.
      apply HFR.
      + left. lia.
      + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho). lia.
      + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
      + unfold scratch_k, spZ. rewrite S32. unfold errno_low in ERR. lia.
      + unfold stat_writes, G_LIVE, G_COUNT, G_FAIL. lia.
    - rewrite S2. apply stk_of_writable; [unfold NAMES_K, READINGS_KB, ALLOC_STACK; lia | lia |].
      intros a Ha. apply HSC. left. unfold spZ. rewrite S32. lia.
    - rewrite S2. unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - rewrite S2. lia.
    - exact RA2.
    - apply word_mem_bytes; [lia | unfold fuzz_alloc_fail_c.G_COUNT; lia | unfold fuzz_alloc_fail_c.G_COUNT; lia | exact WC2].
    - exact (gfail_wr mem2).
    - rewrite Q18. apply word_mem_bytes; [lia | unfold fuzz_alloc_live_c.G_LIVE; lia | unfold fuzz_alloc_live_c.G_LIVE; lia | exact WL2].
    - exact FAIL.
    - exact CRC. }
  intros ms3 (can & (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
    Ecan & BF3 & MU3 & WM3 & RA3) & EQV).
  subst can. apply eqv_shape in EQV as [Ems3 XR3]. rewrite Ems3.
  rewrite S2 in MU3. unfold G_FAIL_AT in MU3, BF3.
  rewrite (fail_at_max cnt2 ltac:(lia)) in BF3.
  apply bytes_word_mem in BF3; [|lia].
  assert (OW3 : forall x, 0 <= x < alloc_ceiling -> ~ alloc_statics x ->
     outside ([(127224, 127232)] ++ [(spZ regs - 32 + 16, spZ regs - 32 + 32)]) x).
  { intros x Hx Hs. cbn [outside app]. split; [|split; [lia | exact I]].
    intros Hg. apply Hs. unfold alloc_statics, G_FAIL. lia. }
  apply SR_ret. unfold check_reject_clean_starved_post.
  exists fx2, L', A', (ms_regs ms3), m3, md'.
  split; [rewrite (ret_pc_ok _ HRA); rewrite SEG; reflexivity|].
  split; [exact FRM2|]. split; [exact INIT2|].
  split.
  { eapply (bpost_sandwich_s B API SF SFA AX 8448 NAMES_K stat_writes L A regs mem md m1 regs1 L' A' regs2 mem2 md' m3
      (ms_regs ms3) ([(spZ regs + -32, spZ regs)] ++ [(127224, 127232)])
      ([(127224, 127232)] ++ [(spZ regs - 32 + 16, spZ regs - 32 + 32)])).
    - exact HM.
    - exact HWS.
    - exact HAC.
    - exact H63.
    - intros a [Ha|Ha]; [left | right; exact Ha].
      unfold spZ in Ha at 1 2. rewrite S32 in Ha. unfold NAMES_K, READINGS_KB, ALLOC_STACK in Ha. lia.
    - intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia.
    - intros a Ha. unfold alloc_statics, stat_writes, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *. lia.
    - exact (in_img_low B SEG).
    - intros x Hx H1 H2. cbn [outside app]. split; [lia|]. split; [|exact I].
      intros Hg. apply H2. unfold alloc_statics, G_FAIL. lia.
    - intros x Hx H1 H2. cbn [outside app]. split; [|split; [lia | exact I]].
      intros Hg. apply H2. unfold alloc_statics, G_FAIL. lia.
    - exact MU1.
    - rewrite SEG. exact WM1.
    - exact BP.
    - exact MU3.
    - rewrite SEG. exact WM3.
    - exact GS.
    - rewrite SEG. exact RA3.
    - intros r Hr. rewrite <- (getr_eqv _ _ XR3 (Z_to_bv 5 r)). unfold callee_saved in Hr.
      assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                   r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | HC]]]]]].
      + change (Z_to_bv 64 (bv_unsigned (reg_get regs2 2) + 32) = getr regs (Z_to_bv 5 2)).
        rewrite S2. replace (spZ regs - 32 + 32) with (spZ regs) by lia. unfold spZ.
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      + transitivity (getr regs2 (Z_to_bv 5 3)); [reflexivity|].
        rewrite (CS 3 ltac:(unfold callee_saved; lia)). rewrite <- (getr_eqv _ _ XR1). reflexivity.
      + transitivity (getr regs2 (Z_to_bv 5 4)); [reflexivity|].
        rewrite (CS 4 ltac:(unfold callee_saved; lia)). rewrite <- (getr_eqv _ _ XR1). reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + assert (HR : 19 <= r <= 27) by lia.
        transitivity (getr regs2 (Z_to_bv 5 r)).
        { destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; reflexivity. }
        rewrite (CS r ltac:(unfold callee_saved; lia)). rewrite <- (getr_eqv _ _ XR1).
        destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; reflexivity. }
  split.
  { exists sl. eapply cstr_munch; [exact CT2' | exact MU3 |]. cbn [app disjoint_from].
    split; [lia|]. split; [lia | exact I]. }
  split.
  { exists slu. eapply cstr_munch; [exact CU2' | exact MU3 |]. cbn [app disjoint_from].
    split; [lia|]. split; [lia | exact I]. }
  split; [|exact SLOTS].
  assert (HL3 : forall c, ledger B L' A' mem2 Lam peak c fl2 -> ledger B L' A' m3 Lam peak c (2 ^ 64 - 1)).
  { intros c Hc. apply (ledger_set_fail L' A' mem2 md' m3 _ Lam peak c fl2 (2 ^ 64 - 1) HM2 Hc MU3 OW3).
    - intros x Hx. cbn [outside app].
      cbv delta [Ledger.G_LIVE Ledger.G_COUNT fuzz_alloc_live_c.G_LIVE fuzz_alloc_fail_c.G_COUNT] in Hx.
      split; [lia|]. split; [lia | exact I].
    - rewrite SEG. exact BF3.
    - lia. }
  destruct HCN as [(Eub & ->) | (Nub & ->)].
  - left. split; [exact Eub | exact (HL3 _ LG2)].
  - right. split; [exact Nub | exact (HL3 _ LG2)].
Qed.

End P.
