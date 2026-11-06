From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import memcpy_c fuzz_alloc_live_c fuzz_alloc_peak_reset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import check_no_overread_steps slot_steps_c.
Import ListNotations.
Open Scope Z_scope.

Ltac sb_fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
  end.

Lemma sb_split1 : forall segs m a n junk, 0 <= n ->
  rw_cells segs m a [CB (Z.to_nat (n + 1)) junk] ->
  exists j0 j1, rw_cells segs m a [CB (Z.to_nat n) j0] /\ rw_cells segs m (a + n) [CB 1 j1].
Proof.
  intros segs m a n junk Hn H.
  rewrite (Z2Nat.inj_add n 1) in H by lia. change (Z.to_nat 1) with 1%nat in H.
  apply rwcb_split in H as [B0 B1]. rewrite Z2Nat.id in B1 by lia.
  eexists _, _. split; [exact B0 | exact B1].
Qed.

Lemma sb_mem_inv_wr : forall m m' A n, mem_inv rsegs m -> munch [(A, A + n)] m m' -> wr_at rsegs m A n ->
  mem_inv rsegs m'.
Proof.
  intros m m' A n Hi Hm (Ha & Hn & Hw) x b Hx.
  destruct (m x) as [b'|] eqn:E; [exact (Hi x b' E)|].
  destruct (Z_le_gt_dec A (bv_unsigned x)) as [L|L];
    [destruct (Z_lt_ge_dec (bv_unsigned x) (A + n)) as [U|U]|].
  - apply (wview_not_ro rsegs m x); [|exact E].
    assert (Ex : wa (A + (bv_unsigned x - A)) = x) by (apply wa_of_var; lia).
    rewrite <- Ex. apply Hw. lia.
  - rewrite (Hm x) in Hx by (cbn [outside]; split; [lia|exact I]). congruence.
  - rewrite (Hm x) in Hx by (cbn [outside]; split; [lia|exact I]). congruence.
Qed.

Lemma sl_s2_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ua un tn : Z) (ub j1 : list byte),
  s1 = Z_to_bv 64 ua -> s0 = Z_to_bv 64 un -> s3 = Z_to_bv 64 tn ->
  4096 <= ua -> ua + un + 1 < 2 ^ 62 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length ub) = un ->
  bytes_at rsegs m ua ub -> rw_cells rsegs m (ua + un) [CB 1 j1] -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
     exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x12fa8) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ua) (Z_to_bv 64 (tn + 1))
                     a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
       bytes_at rsegs m' ua (ub ++ [Z_to_bv 8 0]) /\
       munch [(ua, ua + (un + 1))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12f98) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ua un tn ub j1 -> -> -> HA HA2 HU HT HL C0 B1 HMI.
  pose proof (munch_refl [(ua, ua + (un + 1))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep.
  remember (ua + un) as p eqn:Hp.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  do 2 zstep.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (CP : bytes_at rsegs mm ua (ub ++ [Z_to_bv 8 0]))
  end.
  { subst p. apply rw_cells_bytes in B1. cbn [cells_bytes cbytes app] in B1.
    apply bytes_at_app. split; [exact C0|]. rewrite HL. exact B1. }
  finish.
Qed.

Lemma sl_s2 : memcpy_contract -> sl_s2_stmt.
Proof.
  intros MEMCPY. unfold sl_s2_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ua un tn uri ub junk -> -> -> -> HA HA2 HU HT HL SRC DJ BLK HMI.
  destruct (sb_split1 rsegs m ua un junk ltac:(lia) BLK) as (j0 & j1 & B0 & B1). clear BLK.
  pose proof (munch_refl [(ua, ua + (un + 1))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UA : bv_unsigned (Z_to_bv 64 ua) = ua) by (apply unsigned_lit; lia).
  assert (UU : bv_unsigned (Z_to_bv 64 un) = un) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep. zstep.
  destruct (Z.eq_dec un 0) as [U0|U0].
  - if_true.
    assert (C0 : bytes_at rsegs m ua ub).
    { destruct ub; [apply bytes_at_nil; lia | cbn [length] in HL; lia]. }
    eapply sl_s2_tail with (ua := ua) (un := un) (tn := tn) (ub := ub);
      first [reflexivity | eassumption | lia].
  - if_false. do 4 zstep.
    pose proof (bytes_at_bound rsegs m uri ub SRC) as SB.
    assert (UI : bv_unsigned (Z_to_bv 64 uri) = uri) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply MEMCPY.
      - rewrite UI. exact SRC.
      - rewrite UU, <- HL, Nat2Z.id. reflexivity.
      - rewrite UA, UU. exact B0.
      - rewrite UI, UA, UU. lia.
      - exact HMI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MUc & WMc & MIc & RW0 & SRC1).
    subst ms'. rewrite UA, UU in MUc, RW0. clear SRC1.
    sb_fix_ret.
    transport_after_call rsegs m m1 MUc WMc.
    clear MUc WMc HMI.
    apply rw_cells_bytes in RW0. cbn [cells_bytes cbytes] in RW0. rewrite app_nil_r in RW0.
    eapply evt_mono.
    { eapply sl_s2_tail with (ua := ua) (un := un) (tn := tn) (ub := ub);
        first [reflexivity | eassumption | lia]. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 &
                E & CP & MU2 & WM2 & MI2).
    exists t0'', t1'', t2'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact E|]. split; [exact CP|]. split; [eapply munch_trans; eassumption|].
    split; [eapply wmono_trans; eassumption | exact MI2].
Qed.

Lemma sl_s3_tail : fuzz_alloc_live_contract -> fuzz_alloc_peak_reset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ta tn : Z) (live : word) (tb j1 : list byte),
  s4 = Z_to_bv 64 ta -> s3 = Z_to_bv 64 tn ->
  4096 <= ta -> ta + tn + 1 < 2 ^ 62 -> (ta + (tn + 1) <= 0x2f370 \/ 0x2f380 <= ta) ->
  0 <= tn <= 2 ^ 22 -> Z.of_nat (length tb) = tn ->
  bytes_at rsegs m ta tb -> rw_cells rsegs m (ta + tn) [CB 1 j1] ->
  bytes_at rsegs m 0x2f370 (le8 live) -> wr_at rsegs m 0x2f378 8 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
     exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x12fe4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ta) s1
                     a2' a3' a4' a5' a6' a7' live (Z_to_bv 64 (ta + tn)) (Z_to_bv 64 ta) s5
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13c1c) fc None m' (seg_rom rsegs) /\
       bytes_at rsegs m' ta (tb ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m' 0x2f378 (le8 live) /\
       munch [(ta, ta + (tn + 1)); (0x2f378, 0x2f380)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12fc4) fc None m (seg_rom rsegs)).
Proof.
  intros LIVE RESET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ta tn live tb j1 -> -> HA HA2 DG HT HL C0 B1 HG WP HMI.
  pose proof (munch_refl [(ta, ta + (tn + 1)); (0x2f378, 0x2f380)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep.
  remember (ta + tn) as p eqn:Hp.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (CP : bytes_at rsegs mm ta (tb ++ [Z_to_bv 8 0]))
  end.
  { subst p. apply rw_cells_bytes in B1. cbn [cells_bytes cbytes app] in B1.
    apply bytes_at_app. split; [exact C0|]. rewrite HL. exact B1. }
  clear C0 B1.
  zstep.
  eapply evt_cut.
  { eapply LIVE. exact HG. }
  intros ms' Hq. cbv beta in Hq. subst ms'.
  sb_fix_ret.
  do 2 zstep.
  eapply evt_cut.
  { eapply RESET; [exact HG | exact WP]. }
  intros ms' Hq. cbv beta in Hq. destruct Hq as (a0' & a1' & m3 & E & HP & MUc & WMc). subst ms'.
  unfold G_PEAK in HP, MUc. change (0x2f378 + 8) with 0x2f380 in MUc.
  lazymatch type of MUc with
  | munch _ ?ma ?mb =>
      pose proof (sb_mem_inv_wr ma mb 0x2f378 8 HMI MUc WP) as MI3;
      sb_fix_ret;
      transport_after_call rsegs ma mb MUc WMc
  end.
  clear MUc WMc HMI.
  do 3 zstep.
  finish.
Qed.

Lemma sl_s3 : memcpy_contract -> fuzz_alloc_live_contract -> fuzz_alloc_peak_reset_contract -> sl_s3_stmt.
Proof.
  intros MEMCPY LIVE RESET. unfold sl_s3_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ta tn text live tb junk -> -> -> HA HA2 DG HT HL SRC DJ BLK HG WP HMI.
  destruct (sb_split1 rsegs m ta tn junk ltac:(lia) BLK) as (j0 & j1 & B0 & B1). clear BLK.
  pose proof (munch_refl [(ta, ta + (tn + 1)); (0x2f378, 0x2f380)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UA : bv_unsigned (Z_to_bv 64 ta) = ta) by (apply unsigned_lit; lia).
  assert (UT : bv_unsigned (Z_to_bv 64 tn) = tn) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep. zstep.
  destruct (Z.eq_dec tn 0) as [T0|T0].
  - if_true.
    assert (C0 : bytes_at rsegs m ta tb).
    { destruct tb; [apply bytes_at_nil; lia | cbn [length] in HL; lia]. }
    eapply (sl_s3_tail LIVE RESET) with (ta := ta) (tn := tn) (tb := tb);
      first [reflexivity | eassumption | lia].
  - if_false. do 4 zstep.
    pose proof (bytes_at_bound rsegs m text tb SRC) as SB.
    assert (UX : bv_unsigned (Z_to_bv 64 text) = text) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply MEMCPY.
      - rewrite UX. exact SRC.
      - rewrite UT, <- HL, Nat2Z.id. reflexivity.
      - rewrite UA, UT. exact B0.
      - rewrite UX, UA, UT. lia.
      - exact HMI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MUc & WMc & MIc & RW0 & SRC1).
    subst ms'. rewrite UA, UT in MUc, RW0. clear SRC1.
    sb_fix_ret.
    transport_after_call rsegs m m1 MUc WMc.
    clear MUc WMc HMI.
    apply rw_cells_bytes in RW0. cbn [cells_bytes cbytes] in RW0. rewrite app_nil_r in RW0.
    eapply evt_mono.
    { eapply (sl_s3_tail LIVE RESET) with (ta := ta) (tn := tn) (tb := tb);
        first [reflexivity | eassumption | lia]. }
    intros ms' (t0'' & t1'' & t2'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 &
                E & CP & HP & MU2 & WM2 & MI2).
    exists t0'', t1'', t2'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact E|]. split; [exact CP|]. split; [exact HP|]. split; [eapply munch_trans; eassumption|].
    split; [eapply wmono_trans; eassumption | exact MI2].
Qed.
