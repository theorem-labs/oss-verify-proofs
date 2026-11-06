From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
Import ListNotations.
Open Scope Z_scope.

Lemma nm_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x13e24) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1
                    (Z_to_bv 64 (bv_unsigned sp + -16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13e30) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -16) [C8 (Z_to_bv 64 0); C8 ra] /\
      munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e10) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO.
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  do 5 zstep.
  apply evt_done. exists m1. split; [reflexivity|].
  exact (conj FR (conj MU WM)).
Qed.

Lemma nm_tail : forall (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ra : word),
  rw_cells rsegs m (bv_unsigned sp + 8) [C8 ra] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e24) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ra FR.
  do 3 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma rw_cells_head8 : forall m A v cs, rw_cells rsegs m A (C8 v :: cs) -> bytes_at rsegs m A (le8 v) /\ wr_at rsegs m A 8.
Proof.
  intros m A v cs [[Hwf Hb] (Ha & Hn & Hw)]. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [Hb _]. split; [exact Hb|].
  cbn [cells_size csize] in Hn, Hw. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
Qed.

Lemma rw_cells_tail1 : forall m A c cs, rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[[Hc Hcs] Hb] (Ha & Hn & Hw)]. cbn [cells_bytes cells_size] in Hb, Hn, Hw.
  apply bytes_at_app in Hb as [_ Hb]. rewrite (cbytes_length c Hc) in Hb.
  split; [split; [exact Hcs | exact Hb]|].
  pose proof (bytes_at_bound _ _ _ _ Hb) as BB.
  split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia.
  apply Hw. lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB names_c readings_c KindB.
Local Open Scope Z_scope.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERR : errno_low B.
Let MR := aa_MR API.

Lemma guard_low : forall L A mem md, MR L A mem md ->
  0 <= ms_got_guard B /\ ms_got_guard B + 8 <= alloc_ceiling /\ 0 <= ms_guard B /\ ms_guard B + 8 <= alloc_ceiling.
Proof.
  intros L A mem md HM.
  assert (Lo : forall a, static_owned B a -> 0 <= a < alloc_ceiling).
  { intros a Ha. exact (mr_owned_low _ _ (aa_laws API) L A mem md a HM (or_intror Ha)). }
  pose proof (Lo (ms_got_guard B) ltac:(unfold static_owned; do 4 right; left; lia)).
  pose proof (Lo (ms_got_guard B + 7) ltac:(unfold static_owned; do 4 right; left; lia)).
  pose proof (Lo (ms_guard B) ltac:(unfold static_owned; do 5 right; left; lia)).
  pose proof (Lo (ms_guard B + 7) ltac:(unfold static_owned; do 5 right; left; lia)).
  lia.
Qed.

Lemma guard_cells_munch : forall L A mem md m' W, MR L A mem md -> guard_cells B mem -> munch W mem m' ->
  (forall x, 0 <= x < alloc_ceiling -> outside W x) -> guard_cells B m'.
Proof.
  intros L A mem md m' W HM (G1 & g & G2) HW Ho. pose proof (guard_low L A mem md HM) as GL.
  split; [|exists g]; (eapply word_mem_munch; [exact HW | lia | pose proof alloc_ceiling_lt; lia | intros x Hx; apply Ho; lia |]);
    assumption.
Qed.

Lemma guard_kept_munch : forall L A mem md m' W, MR L A mem md -> munch W mem m' ->
  (forall x, 0 <= x < alloc_ceiling -> outside W x) -> guard_kept B mem m'.
Proof.
  intros L A mem md m' W HM HW Ho i Hi. pose proof (guard_low L A mem md HM) as GL.
  apply (KindB.mbyte_munch _ W mem m'); [exact HW | pose proof alloc_ceiling_lt; lia | apply Ho; lia].
Qed.

Lemma bpost_push16 : forall L A regs mem md mem1 regs1 L' A' regs2 mem2 md' regs3,
  ms_segs B = rsegs ->
  MR L A mem md ->
  (forall a, spZ regs - NAMES_K <= a < spZ regs -> writable_at (ms_segs B) mem a) ->
  alloc_ceiling + NAMES_K <= spZ regs -> spZ regs < 2 ^ 63 ->
  spZ regs1 = spZ regs - 16 ->
  munch [(spZ regs - 16, spZ regs)] mem mem1 -> wmono (ms_segs B) mem mem1 ->
  bpost B MR READINGS_KB (rd_writes (spZ regs - 16)) L A regs1 mem1 md L' A' regs2 mem2 md' ->
  wr_at rsegs mem2 (spZ regs - 16) 8 ->
  regs_preserved regs regs3 ->
  bpost B MR NAMES_K stat_writes L A regs mem md L' A' regs3 mem2 md'.
Proof.
  intros L A regs mem md mem1 regs1 L' A' regs2 mem2 md' regs3 SEG HM HWs Hac H63 Hsp1 MU1 WM1 BP WR2 RP.
  pose proof alloc_ceiling_val as Hacv.
  assert (EK : NAMES_K = 8432) by reflexivity. assert (EKB : READINGS_KB = 8416) by reflexivity.
  rewrite EK in *. rewrite EKB in BP.
  destruct BP as (HM2 & HWF & HBD & _ & Hmd & Hbl & Hbb & Hfr & Hsc & RA2 & GK2).
  assert (O1 : forall x, 0 <= x < spZ regs - 16 -> outside [(spZ regs - 16, spZ regs)] x)
    by (intros x Hx; apply outside_one; lia).
  assert (NO : forall L0 A0 m0 md0 a, MR L0 A0 m0 md0 -> alloc_ceiling <= a -> ~ owned B L0 A0 a).
  { intros L0 A0 m0 md0 a H0 Ha Ho. pose proof (mr_owned_low _ _ (aa_laws API) L0 A0 m0 md0 a H0 Ho). lia. }
  assert (HM1 : MR L A mem1 md).
  { apply (MR_high B API L A mem mem1 md _ HM MU1). intros x Hx. apply outside_one. lia. }
  split; [exact HM2|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact RP|]. split; [exact Hmd|].
  split; [exact Hbl|].
  split.
  { intros a k i Hin Hi.
    pose proof (blocks_low B API L A mem md a k i HM Hin Hi) as Hlow.
    rewrite (Hbb a k i Hin Hi).
    apply (mbyte_munch _ [(spZ regs - 16, spZ regs)] mem mem1); [exact MU1 | lia | apply O1; lia]. }
  split.
  { intros a Hr HnA HnA' Hsc0 HnE.
    assert (Hn1 : ~ scratch_k B 8416 regs1 a).
    { intros [Hs|Hs]; apply Hsc0; [left; unfold spZ in *; lia | right; exact Hs]. }
    assert (Hout : ~ (spZ regs - 8432 <= a < spZ regs)) by (intros Hs; apply Hsc0; left; exact Hs).
    assert (HnE1 : ~ rd_writes (spZ regs - 16) a) by (intros [He|He]; [exact (HnE He) | lia]).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEG a Hr); lia]).
    destruct (Hfr a Hr HnA HnA' Hn1 HnE1) as [Hm2 Hw2].
    split.
    - rewrite Hm2. apply (mbyte_munch _ [(spZ regs - 16, spZ regs)] mem mem1); [exact MU1 | lia | apply outside_one; lia].
    - rewrite (writable_munch _ [(spZ regs - 16, spZ regs)] mem mem1 a MU1) by first [lia | apply outside_one; lia].
      exact Hw2. }
  split; [|split; [exact RA2|]].
  2:{ intros i Hi. rewrite (GK2 i Hi).
      apply (guard_kept_munch L A mem md mem1 [(spZ regs - 16, spZ regs)] HM MU1); [|exact Hi].
      intros x Hx. apply outside_one. lia. }
  intros a Hs.
  assert (D : scratch_k B 8416 regs1 a \/ ~ scratch_k B 8416 regs1 a).
  { unfold scratch_k. destruct (Z.le_gt_cases (spZ regs1 - 8416) a); destruct (Z.lt_ge_cases a (spZ regs1));
      destruct (Z.le_gt_cases (errno_addr B) a); destruct (Z.lt_ge_cases a (errno_addr B + 4));
      first [left; lia | right; lia]. }
  destruct D as [Hs1|Hs1]; [exact (Hsc a Hs1)|].
  destruct Hs as [Hs|Hs]; [|exfalso; apply Hs1; right; exact Hs].
  destruct (Z.lt_ge_cases a (spZ regs - 8)) as [Hlt|Hge].
  - destruct WR2 as (_ & _ & Hw). rewrite SEG. unfold writable_at.
    replace a with (spZ regs - 16 + (a - (spZ regs - 16))) by lia. apply Hw.
    assert (spZ regs - 16 <= a) by (unfold scratch_k, spZ in *; lia). lia.
  - assert (Hw1 : writable_at (ms_segs B) mem1 a) by (apply WM1; apply HWs; exact Hs).
    assert (Hr : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
    assert (Hn1 : ~ owned B L A a) by (apply (NO _ _ _ _ a HM1); lia).
    assert (Hn2 : ~ owned B L' A' a) by (apply (NO _ _ _ _ a HM2); lia).
    assert (Hn3 : ~ rd_writes (spZ regs - 16) a).
    { intros [He|He]; [unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in He; lia | lia]. }
    destruct (Hfr a Hr Hn1 Hn2 Hs1 Hn3) as [_ Hw2].
    apply Hw2. exact Hw1.
Qed.

Theorem names_holds : (forall fx', @readings_contract fx' rc B API) -> names_contract B API.
Proof.
  intros READ. unfold names_contract.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail SEG PRE INIT TS FRM MI GC CT CU HT HU T4 U4 LT LU IMG DT DU
    DP1 DP2 DP3 OT OU LED RES CAP BY0 BYQ.
  pose proof alloc_ceiling_val as Hacv.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  assert (EK : NAMES_K = 8432) by reflexivity. rewrite EK in *.
  assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  pose proof (zr_word (reg_get regs 2)) as Rsp. unfold inr64 in Rsp. rewrite SP in Rsp.
  assert (STK : stk rsegs mem (spZ regs - 8432) (spZ regs)).
  { apply stk_of_writable; [lia | unfold spZ in *; lia |].
    intros a Ha. rewrite <- SEG. apply HWS. exact Ha. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (nm_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (spZ regs - 8432)).
    - exact STK.
    - rewrite SP. lia. }
  intros ms1 (can & (m1 & Ecan & FR & MU1 & WM1) & EQV). subst can.
  apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
  set (regs1 := ms_regs ms1) in *.
  rewrite SP in MU1, FR.
  assert (R1 : getr regs1 1 = Z_to_bv 64 0x13e24) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (S16 : bv_unsigned (getr regs1 2) = spZ regs - 16).
  { rewrite <- (getr_eqv _ _ XR1).
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -16)) = spZ regs - 16).
    rewrite SP. rewrite (inr64_unsigned_lit _) by (unfold inr64; lia). lia. }
  assert (R12 : bv_unsigned (getr regs1 12) = spZ regs - 16).
  { rewrite <- (getr_eqv _ _ XR1).
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -16)) = spZ regs - 16).
    rewrite SP. rewrite (inr64_unsigned_lit _) by (unfold inr64; lia). lia. }
  assert (R10 : getr regs1 10 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R11 : getr regs1 11 = getr regs 11) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R4 : getr regs1 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  unfold off_stack in DT, DU.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in DT, DU.
  assert (HM1 : aa_MR API L A m1 md).
  { apply (MR_high B API L A mem m1 md _ HM MU1). intros x Hx. apply outside_one. lia. }
  destruct (rw_cells_head8 m1 _ _ _ FR) as [RPB RPW].
  replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
  eapply SR_bind.
  { apply (READ fx L A regs1 m1 md b tb ts ub us Lam peak cnt fail (Z_to_bv 64 0)).
    - exact SEG.
    - unfold call_pre_k. unfold spZ at 1 2 3 4 5. rewrite S16.
      split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite R1; apply ret_ok_even; vm_compute; reflexivity|].
      split; [Z.div_mod_to_equations; lia|].
      split; [unfold READINGS_KB, ALLOC_STACK; lia|].
      split; [lia|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HWS.
        unfold READINGS_KB, ALLOC_STACK in Ha. lia. }
      split; [rewrite R4; exact HTP|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HER. exact Ha. }
      intros H. rewrite INIT in H. discriminate.
    - exact INIT.
    - rewrite R12. change (bv_unsigned (getr regs 2)) with (spZ regs) in TS. lia.
    - exact FRM.
    - apply (ro_agree_munch _ mem m1 MI MU1). intros x Hx. apply outside_one. lia.
    - apply (guard_cells_munch L A mem md m1 _ HM GC MU1). intros x Hx. apply outside_one. lia.
    - rewrite R10. eapply cstr_munch; [exact CT | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
    - rewrite R11. eapply cstr_munch; [exact CU | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
    - rewrite R10. exact HT.
    - rewrite R11. exact HU.
    - rewrite R10. exact T4.
    - rewrite R11. exact U4.
    - exact LT.
    - exact LU.
    - apply (img_strings_keep mem m1 MI); [|exact IMG].
      apply (ro_agree_munch _ mem m1 MI MU1). intros x Hx. apply outside_one. lia.
    - unfold off_stack. rewrite S16, R10. unfold READINGS_KB, ALLOC_STACK. lia.
    - unfold off_stack. rewrite S16, R11. unfold READINGS_KB, ALLOC_STACK. lia.
    - rewrite R12. replace (spZ regs - 16) with (spZ regs + -16) by lia. exact RPB.
    - rewrite R12. replace (spZ regs - 16) with (spZ regs + -16) by lia. exact RPW.
    - rewrite S16, R12. lia.
    - rewrite R10, R11, R12. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - eapply ledger_munch; [exact HM | exact LED | exact MU1 | intros x Hx; apply outside_one; lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' POST.
  destruct POST as (fx2 & L' & A' & regs2 & mem2 & md' & res & -> & FRM2 & INIT2 & BP & WR2 & RES10 & CT2 & CU2 &
    ARMS & SLOTS).
  rewrite R12 in BP, WR2.
  pose proof BP as (HM2 & HWF2 & HBD2 & RP2 & HMD & HBL & HBB & HFR & HSC & RA2 & GK2).
  destruct (mr_model _ _ (aa_laws API) L' A' mem2 md' HM2) as (Hh2 & Hl2 & _).
  assert (CS : forall k, callee_saved k -> getr regs2 (Z_to_bv 5 k) = getr regs1 (Z_to_bv 5 k)) by exact RP2.
  assert (S2 : bv_unsigned (reg_get regs2 2) = spZ regs - 16).
  { change (bv_unsigned (getr regs2 (Z_to_bv 5 2)) = spZ regs - 16).
    rewrite (CS 2 ltac:(unfold callee_saved; lia)). exact S16. }
  rewrite R10 in CT2. rewrite R11 in CU2.
  assert (FR2 : rw_cells rsegs mem2 (spZ regs - 8) [C8 (reg_get regs 1)]).
  { assert (FR8 : rw_cells rsegs m1 (spZ regs - 8) [C8 (reg_get regs 1)]).
    { pose proof (rw_cells_tail1 _ _ _ _ FR) as T. cbn [csize Z.of_nat] in T.
      replace (spZ regs - 8) with (spZ regs + -16 + 8) by lia. exact T. }
    apply (rw_cells_keep m1 mem2 _ _ FR8). intros a Ha. cbn in Ha.
    rewrite <- SEG. apply HFR.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho). lia.
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    + unfold scratch_k, spZ. rewrite S16. unfold errno_low in ERR. lia.
    + unfold rd_writes, stat_writes, G_LIVE, G_COUNT, G_FAIL. lia. }
  rewrite R1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (nm_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 (reg_get regs 1)).
    rewrite S2. replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia. exact FR2. }
  intros ms3 (can & Ecan & EQV). subst can.
  apply eqv_shape in EQV as [Ems3 XR3]. rewrite Ems3.
  apply SR_ret. unfold names_post.
  exists fx2, L', A', (ms_regs ms3), mem2, md', res.
  split; [change (ret_pc (reg_get regs 1)) with (ret_pc (getr regs 1)); rewrite (ret_pc_ok _ HRA); rewrite SEG; reflexivity|].
  split; [exact FRM2|]. split; [exact INIT2|].
  split.
  { eapply (bpost_push16 L A regs mem md m1 regs1 L' A' regs2 mem2 md' (ms_regs ms3)).
    - exact SEG.
    - exact HM.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. exact HWS.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - exact H63.
    - exact S16.
    - replace (spZ regs - 16) with (spZ regs + -16) by lia. exact MU1.
    - rewrite SEG. exact WM1.
    - exact BP.
    - exact WR2.
    - intros r Hr. rewrite <- (getr_eqv _ _ XR3 (Z_to_bv 5 r)). unfold callee_saved in Hr.
      assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                   r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct HC as [-> | HC].
      + change (Z_to_bv 64 (bv_unsigned (reg_get regs2 2) + 16) = getr regs (Z_to_bv 5 2)).
        rewrite S2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ.
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      + assert (CR : callee_saved r) by (unfold callee_saved; lia).
        transitivity (getr regs2 (Z_to_bv 5 r)).
        { destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
            reflexivity. }
        rewrite (CS r CR). rewrite <- (getr_eqv _ _ XR1).
        destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
          reflexivity. }
  split.
  { rewrite <- (getr_eqv _ _ XR3). exact RES10. }
  split; [exact CT2|]. split; [exact CU2|]. split; [|exact SLOTS].
  destruct ARMS as [(E1 & E2 & E3 & _) | [(E1 & E2 & E3 & E4 & _) | (E1 & E2 & E3 & E4 & _)]].
  - left. exact (conj E1 (conj E2 E3)).
  - right. left. exact (conj E1 (conj E2 (conj E3 E4))).
  - right. right. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.

End P.
