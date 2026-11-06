From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memcpy_c memset_c past_nul_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB.
Import ListNotations.
Open Scope Z_scope.

Lemma pn_find_in : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c end.
  - injection H as <-. left. reflexivity.
  - right. eapply IH. exact H.
Qed.

Lemma pn_wr_rd : forall seg, In seg rsegs -> seg_writable seg = true -> seg_readable seg = true.
Proof.
  intros seg Hin Hw.
  assert (C : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). rewrite Hw in C. exact C.
Qed.

Lemma pn_rd : forall m x, wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x H. unfold mrd. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  unfold wview in H. rewrite E in H.
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:FS; [|exfalso; apply H; reflexivity].
  destruct (seg_writable seg) eqn:W; [|exfalso; apply H; reflexivity].
  rewrite (pn_wr_rd seg (pn_find_in _ _ _ _ FS) W).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at _ _) as [b|]; [exists b; reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma pn_rw_sub : forall m a n a' k, wr_at rsegs m a n -> a <= a' -> a' + Z.of_nat k <= a + n ->
  exists junk, rw_cells rsegs m a' [CB k junk].
Proof.
  intros m a n a' k (H1 & H2 & H) Ha Hk.
  assert (S : stk rsegs m a' (a' + Z.of_nat k)).
  { split; [lia|]. split; [lia|]. intros x Hx.
    assert (W : wview rsegs m (wa x) <> None) by (replace x with (a + (x - a)) by lia; apply H; lia).
    split; [exact W | apply pn_rd, W]. }
  destruct (stk_carve rsegs m a' (a' + Z.of_nat k) k S ltac:(lia)) as [_ (junk & J)].
  exists junk. replace (a' + Z.of_nat k - Z.of_nat k) with a' in J by lia. exact J.
Qed.

Lemma pn_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x13fd8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a2 s1
                    (Z_to_bv 64 (bv_unsigned a1 + 18)) a1 a2 a3 a4 a5 a6 a7
                    a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16c7c) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fa8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 48%nat ST.
  do 12 zstep.
  apply evt_done. exists m1. split; [reflexivity|].
  exact (conj FR (conj MU (conj WM MI))).
Qed.

Lemma pn_le1 : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 (z mod 256)].
Proof.
  intros z Hz. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. f_equal.
  apply Z_to_bv8_mod. rewrite Zmod_mod. reflexivity.
Qed.

Lemma pn_ltu_f : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b Ha Hb H. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.

Lemma pn_neq_m1 : forall a, 0 <= a < 2 ^ 64 - 1 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 (-1)) = false.
Proof.
  intros a Ha. unfold bv_eqb. rewrite (unsigned_lit a) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by (vm_compute; reflexivity).
  apply Z.eqb_neq. lia.
Qed.

Lemma pn_tail2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res n c : Z) (db j0 j1 j2 : list byte)
    (xra xs0 xs1 xs2 xs3 xs4 : word),
  memset_contract ->
  rw_cells rsegs m (bv_unsigned sp) [C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  bytes_at rsegs m res db ->
  rw_cells rsegs m (res + n) [CB 1 j0] ->
  rw_cells rsegs m (res + n + 1) [CB 16 j1] ->
  rw_cells rsegs m (res + n + 17) [CB 1 j2] ->
  s0 = Z_to_bv 64 c -> s1 = Z_to_bv 64 res -> s2 = Z_to_bv 64 n ->
  0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> 0 <= c < 2 ^ 64 -> 4096 <= res ->
  res + n + 18 <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' xs0 xs1 (Z_to_bv 64 res)
                    a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc xra) fc None m' (seg_rom rsegs) /\
      munch [(res + n, res + n + 18)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      bytes_at rsegs m' res (pn_copy db c))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ff4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res n c db j0 j1 j2 xra xs0 xs1 xs2 xs3 xs4 MEMSET FR DB R0 R1 R2 E0 E1 E2 Hn Hl Hc Hr Hsp Hsp2 MI.
  subst s0 s1 s2.
  pose proof (munch_refl [(res + n, res + n + 18)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep.
  zstep.
  rewrite (zb_lxor_ones res) by lia.
  rewrite (pn_ltu_f (18446744073709551615 - res) n) by lia; cbv iota.
  zstep. zstep.
  remember (res + n) as q eqn:Hq.
  zstep.
  rewrite (pn_le1 0) by lia. mem_after_store.
  zstep.
  rewrite (pn_neq_m1 q) by lia; cbv iota.
  do 5 zstep.
  eapply evt_cut.
  { eapply MEMSET with (junk := j1).
    - rewrite (unsigned_lit (q + 1)) by lia. exact R1.
    - exact MI. }
  intros ms' POST. unfold memset_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
    E & MUc & WMc & MIc & RVc).
  subst ms'.
  rewrite (unsigned_lit (q + 1)) in MUc, RVc by lia.
  change (bv_unsigned (Z_to_bv 64 16)) with 16 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 16))) with 16%nat in RVc.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc.
  replace (ret_pc (Z_to_bv 64 81952)) with (Z_to_bv 64 81952) by (apply bv_eq; vm_compute; reflexivity).
  assert (MU2 : munch [(q, q + 18)] m m2).
  { apply (munch_trans _ m m0 m2 MU). eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside].
    intros x Hx. lia. }
  pose proof (wmono_trans rsegs m m0 m2 WM WMc) as WM2.
  apply (rw_cells_transport rsegs [(q + 1, q + 1 + 16)] m0 m2) in FR;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  apply (rw_cells_transport rsegs [(q + 1, q + 1 + 16)] m0 m2) in R0;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  apply (rw_cells_transport rsegs [(q + 1, q + 1 + 16)] m0 m2) in R2;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  apply (bytes_at_transport rsegs [(q + 1, q + 1 + 16)] m0 m2) in DB;
    [| exact MUc | cbn [disjoint_from]; lia].
  clear MU WM MI R1 MUc WMc.
  rename MU2 into MU, WM2 into WM, MIc into MI, RVc into R1.
  zstep.
  rewrite (pn_ltu_f (18446744073709551615 - res) (n + 17)) by lia; cbv iota.
  zstep. zstep.
  zstep.
  rewrite (pn_le1 c) by lia. mem_after_store.
  zstep.
  rewrite (pn_le1 65) by lia. mem_after_store.
  replace (Z_to_bv 64 (res + (n + 17))) with (Z_to_bv 64 (q + 17)) by (f_equal; lia).
  zstep.
  rewrite (pn_le1 0) by lia. mem_after_store.
  do 9 zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
  subst q.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  destruct R0 as [[_ B0] _]. destruct R1 as [[_ B1] _]. destruct R2 as [[_ B2] _].
  cbn [cells_bytes cbytes app] in B0, B1, B2.
  unfold pn_copy. apply bytes_at_app. split; [exact DB|]. rewrite Hl.
  lazymatch type of B0 with bytes_at _ _ _ ?L0 =>
  lazymatch type of B1 with bytes_at _ _ _ ?L1 =>
  lazymatch type of B2 with bytes_at _ _ _ ?L2 =>
    replace ([Z_to_bv 8 0; Z_to_bv 8 (c mod 256); Z_to_bv 8 65] ++ repeat (Z_to_bv 8 0) 15)
      with (L0 ++ (L1 ++ L2)) by reflexivity end end end.
  apply bytes_at_app. split; [exact B0|].
  apply bytes_at_app. split.
  - match goal with |- bytes_at _ _ ?a _ => replace a with (res + n + 1) by (cbn; lia) end. exact B1.
  - match goal with |- bytes_at _ _ ?a _ => replace a with (res + n + 17) by (cbn; lia) end. exact B2.
Qed.

Lemma pn_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res n c d : Z) (db : list byte)
    (xra xs0 xs1 xs2 xs3 xs4 : word),
  memcpy_contract -> memset_contract ->
  rw_cells rsegs m (bv_unsigned sp) [C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  wr_at rsegs m res (n + 18) ->
  a0 = Z_to_bv 64 res -> s0 = Z_to_bv 64 c -> s2 = Z_to_bv 64 n -> s3 = Z_to_bv 64 d ->
  0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> 0 <= c < 2 ^ 64 -> 4096 <= res ->
  res + n + 18 <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2 ^ 64 ->
  (0 < n -> bytes_at rsegs m d db /\ (d + n <= res \/ res + n + 18 <= d)) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' xs0 xs1 (Z_to_bv 64 res)
                    a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc xra) fc None m' (seg_rom rsegs) /\
      munch [(res, res + n + 18)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      bytes_at rsegs m' res (pn_copy db c))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res n c d db xra xs0 xs1 xs2 xs3 xs4 MEMCPY MEMSET FR WR E0 E1 E2 E3 Hn Hl Hc Hr Hsp Hsp2 HD MI.
  subst a0 s0 s2 s3.
  assert (Hres : res + n + 18 < 2 ^ 64) by lia.
  assert (B0 : bv_eqb (Z_to_bv 64 res) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  zstep. rewrite B0; cbv iota.
  zstep. zstep.
  destruct (Z.eq_dec n 0) as [->|N0].
  - destruct db as [|b db]; [|cbn in Hl; lia].
    assert (B1 : bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) = true) by reflexivity.
    rewrite B1; cbv iota.
    destruct (pn_rw_sub m res (0 + 18) (res + 0) 1 WR ltac:(lia) ltac:(lia)) as [j0 R0].
    destruct (pn_rw_sub m res (0 + 18) (res + 0 + 1) 16 WR ltac:(lia) ltac:(lia)) as [j1 R1].
    destruct (pn_rw_sub m res (0 + 18) (res + 0 + 17) 1 WR ltac:(lia) ltac:(lia)) as [j2 R2].
    eapply evt_mono.
    { eapply pn_tail2; [exact MEMSET | exact FR | exact (bytes_at_nil rsegs m res ltac:(lia)) | exact R0 | exact R1 |
        exact R2 | reflexivity | reflexivity | reflexivity | lia | reflexivity | lia | lia | lia | lia | exact MI]. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & E' & MU' & WM' & MI' & BY').
    do 14 eexists. exists m'. split; [exact E'|].
    split; [eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros x Hx; lia|].
    split; [exact WM'|]. split; [exact MI' | exact BY'].
  - assert (B1 : bv_eqb (Z_to_bv 64 n) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
    rewrite B1; cbv iota.
    destruct (HD ltac:(lia)) as [DB DJ].
    pose proof (bytes_at_bound rsegs m d db DB) as Hd.
    destruct (pn_rw_sub m res (n + 18) res (Z.to_nat n) WR ltac:(lia) ltac:(lia)) as [j0 R0].
    do 4 zstep.
    eapply evt_cut.
    { eapply MEMCPY with (src := db) (junk := j0).
      - rewrite (unsigned_lit d) by lia. exact DB.
      - rewrite (unsigned_lit n) by lia. lia.
      - rewrite (unsigned_lit res) by lia. rewrite (unsigned_lit n) by lia. exact R0.
      - rewrite !unsigned_lit by lia. lia.
      - exact MI. }
    intros ms' POST. unfold memcpy_post in POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
      E & MUc & WMc & MIc & RVc & DBc).
    subst ms'.
    rewrite (unsigned_lit res) in MUc, RVc by lia. rewrite (unsigned_lit n) in MUc, RVc by lia.
    replace (ret_pc (Z_to_bv 64 81908)) with (Z_to_bv 64 81908) by (apply bv_eq; vm_compute; reflexivity).
    destruct RVc as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    apply (rw_cells_transport rsegs [(res, res + n)] m m2) in FR;
      [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
    apply (wr_at_transport rsegs m m2) in WR; [| exact WMc].
    assert (MU2 : munch [(res, res + n + 18)] m m2).
    { eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    destruct (pn_rw_sub m2 res (n + 18) (res + n) 1 WR ltac:(lia) ltac:(lia)) as [k0 Q0].
    destruct (pn_rw_sub m2 res (n + 18) (res + n + 1) 16 WR ltac:(lia) ltac:(lia)) as [k1 Q1].
    destruct (pn_rw_sub m2 res (n + 18) (res + n + 17) 1 WR ltac:(lia) ltac:(lia)) as [k2 Q2].
    eapply evt_mono.
    { eapply pn_tail2; [exact MEMSET | exact FR | exact BY | exact Q0 | exact Q1 | exact Q2 |
        reflexivity | reflexivity | reflexivity | lia | exact Hl | lia | lia | lia | lia | exact MIc]. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & E' & MU' & WM' & MI' & BY').
    do 14 eexists. exists m'. split; [exact E'|].
    split.
    { apply (munch_trans _ m m2 m' MU2). eapply munch_weaken; [|exact MU']. unfold sub_fp. cbn [outside].
      intros x Hx. lia. }
    split; [exact (wmono_trans rsegs m m2 m' WMc WM')|]. split; [exact MI' | exact BY'].
Qed.

Lemma pn_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pn_ro_hi : forall a, 0x55000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
  rewrite (HsKindB.find_segment_above rsegs 0x55000 a 1 HsKindB.rsegs_top) by lia. reflexivity.
Qed.

Lemma pn_rw_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Lemma pn_rw_norm : forall m A cs, ro_agree rsegs m ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs m A cs -> rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RA Hro [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (bytes_at_normalize rsegs m A _ RA Hb).
  - exact (wr_at_norm rsegs m (normalize rsegs m) A _ (mem_rel_normalize rsegs m RA) Hw Hro).
Qed.

Lemma pn_stk_norm : forall m lo hi, ro_agree rsegs m -> 0x55000 <= lo ->
  stk rsegs m lo hi -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RA Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw Hr]. pose proof (mem_rel_normalize rsegs m RA) as HR. split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) (wa a) HR (pn_ro_hi a ltac:(lia))). exact Hw.
  - rewrite <- (mrd_rel rsegs m (normalize rsegs m) (wa a) HR). exact Hr.
Qed.

Lemma pn_rel_shape : forall s R F pc fc m0 ro, ms_rel rsegs s (MS R F pc fc None m0 ro) ->
  s = MS R F pc fc None (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma pn_pro_r : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x55000 <= lo -> ro_agree rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x13fd8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a2 s1
                    (Z_to_bv 64 (bv_unsigned a1 + 18)) a1 a2 a3 a4 a5 a6 a7
                    a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16c7c) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fa8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO HL RA.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  eapply evt_mono.
  { apply (evt_normalize rsegs); [exact pn_wx | exact RA |].
    apply pn_pro with (lo := lo); [exact (pn_stk_norm m lo _ RA HL ST) | exact LO | apply mem_inv_normalize]. }
  intros s (s0' & (m0 & E0 & FR & MU & WM & _) & REL & ROS). subst s0'.
  destruct (pn_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  exists (ms_mem s). split; [exact Es|].
  split; [exact (pn_rw_rel _ _ _ _ HR FR)|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS WM)|].
  exact (ro_agree_same rsegs m (ms_mem s) RA ROS).
Qed.

Lemma pn_tail_r : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res n c d : Z) (db : list byte)
    (xra xs0 xs1 xs2 xs3 xs4 : word),
  memcpy_contract -> memset_contract ->
  rw_cells rsegs m (bv_unsigned sp) [C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  wr_at rsegs m res (n + 18) ->
  a0 = Z_to_bv 64 res -> s0 = Z_to_bv 64 c -> s2 = Z_to_bv 64 n -> s3 = Z_to_bv 64 d ->
  0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> 0 <= c < 2 ^ 64 -> 4096 <= res ->
  res + n + 18 <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2 ^ 64 -> 0x55000 <= bv_unsigned sp ->
  (forall i, 0 <= i < n + 18 -> ro_addr rsegs (wa (res + i)) = false) ->
  (0 < n -> bytes_at rsegs m d db /\ (d + n <= res \/ res + n + 18 <= d)) ->
  ro_agree rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' xs0 xs1 (Z_to_bv 64 res)
                    a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc xra) fc None m' (seg_rom rsegs) /\
      munch [(res, res + n + 18)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
      bytes_at rsegs m' res (pn_copy db c))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res n c d db xra xs0 xs1 xs2 xs3 xs4 MEMCPY MEMSET FR WR E0 E1 E2 E3 Hn Hl Hc Hr Hsp Hsp2 Hsp3 HRO HD RA.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  eapply evt_mono.
  { apply (evt_normalize rsegs); [exact pn_wx | exact RA |].
    eapply pn_tail; [exact MEMCPY | exact MEMSET | | exact (wr_at_norm rsegs m (normalize rsegs m) res (n + 18) HR0 WR HRO) |
      exact E0 | exact E1 | exact E2 | exact E3 | exact Hn | exact Hl | exact Hc | exact Hr | exact Hsp |
      exact Hsp2 | | apply mem_inv_normalize].
    - apply (pn_rw_norm m _ _ RA); [|exact FR]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      apply pn_ro_hi. lia.
    - intros Hn0. destruct (HD Hn0) as [DB DJ]. split; [exact (bytes_at_normalize rsegs m d db RA DB) | exact DJ]. }
  intros s (s0' & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m0 & E & MU & WM & _ & BY) &
    REL & ROS).
  subst s0'.
  destruct (pn_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, (ms_mem s). split; [exact Es|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS WM)|].
  split; [exact (ro_agree_same rsegs m (ms_mem s) RA ROS)|].
  exact (proj2 (bytes_at_rel rsegs (ms_mem s) m0 res _ HR) BY).
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import KindBGlue.
Local Open Scope Z_scope.

Lemma pn_pairwise_mid : forall {X : Type} (R : X -> X -> Prop) l1 x l2 y,
  pairwise R (l1 ++ x :: l2) -> In y (l1 ++ l2) -> R x y \/ R y x.
Proof.
  intros X R l1. induction l1 as [|z l1 IH]; intros x l2 y H Hy; cbn [app] in *.
  - left. destruct H as [H _]. exact (H y Hy).
  - destruct H as [Hz H]. destruct Hy as [<- | Hy].
    + right. apply Hz. apply in_or_app. right. left. reflexivity.
    + exact (IH x l2 y H Hy).
Qed.

Lemma pn_in_mid : forall {X : Type} (l1 l2 : list X) x y, In y (l1 ++ l2) -> In y (l1 ++ x :: l2).
Proof. intros X l1 l2 x y H. apply in_app_or in H as [H|H]; apply in_or_app; [left | right; right]; exact H. Qed.

Lemma pn_wview_none : forall segs (m : word -> option byte) x, find_segment segs (bv_unsigned x) 1 = None ->
  wview segs m x <> None -> m x <> None.
Proof. intros segs m x F H E. apply H. unfold wview. rewrite E, F. reflexivity. Qed.

Lemma pn_wview_some : forall segs (m : word -> option byte) x, m x <> None -> wview segs m x <> None.
Proof. intros segs m x H. unfold wview. destruct (m x) as [b|] eqn:E; [discriminate | exfalso; exact (H eq_refl)]. Qed.

Lemma pn_not_out : forall lo hi x, ~ Frame.outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. destruct (Z.le_gt_cases lo x) as [H1|H1]; destruct (Z.lt_ge_cases x hi) as [H2|H2];
    first [ split; assumption | exfalso; apply H; apply outside_one; lia ].
Qed.

Definition pn_R1 (regs : bvmap 5 word) : bvmap 5 word :=
  mkR (Z_to_bv 64 0x13fd8) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -48)) (getr regs 3) (getr regs 4)
    (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 12) (getr regs 9) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 18))
    (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
    (getr regs 11) (getr regs 10) (getr regs 20) (getr regs 21) (getr regs 22)
    (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
    (getr regs 30) (getr regs 31).

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma pn_seg_img : ms_segs B = rsegs -> forall a seg, find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros SEG a seg F.
  destruct (kb_find_segment rsegs a 1 seg F) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun r => (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
              (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)))
              (segments_reserved rsegs)) rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C as (r & Hr & Hc).
  apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  split.
  - rewrite SEG. intros E. pose proof (f_equal (@length Segment) E) as Le. vm_compute in Le. discriminate.
  - exists r. rewrite SEG. split; [exact Hr | lia].
Qed.

Theorem past_nul_holds : ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] ->
  malloc_contract B API -> memcpy_contract -> memset_contract -> past_nul_contract B API.
Proof.
  intros SEG MAL ERR GF MALLOC MEMCPY MEMSET.
  unfold past_nul_contract.
  intros L A regs mem md d n c db b Lam peak cnt fail PRE RAm R10 R11 R12 Hc Hn Hl DB DBLK LG RES ROOM.
  pose proof alloc_ceiling_val as Hacv.
  assert (EK : ALLOC_STACK + PAST_NUL_FRAME = 8240) by reflexivity.
  assert (EA : ALLOC_STACK = 8192) by reflexivity.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  rewrite EK in HAC.
  destruct (kb_md B API L A mem md HM) as [Hh Hl0].
  assert (IL : img_low B).
  { apply (img_low_of_check B 0x55000); [unfold img_check; rewrite SEG; vm_compute; reflexivity | lia]. }
  assert (STK : Frame.stk rsegs mem (spZ regs - 8240) (spZ regs)).
  { pose proof (kb_stk B API IL (ALLOC_STACK + PAST_NUL_FRAME) L A regs mem md PRE ltac:(rewrite EK; lia)) as K.
    rewrite SEG, EK in K. exact K. }
  assert (RA0 : ro_agree rsegs mem) by (rewrite <- SEG; exact RAm).
  eapply (kb_run B regs (Z_to_bv 64 PAST_NUL) mem md
    (fun R pc' m' => R = pn_R1 regs /\ pc' = Z_to_bv 64 0x16c7c /\
       Step.rw_cells rsegs m' (spZ regs + -48)
         [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
       Frame.munch [(spZ regs + -48, spZ regs)] mem m' /\ Frame.wmono rsegs mem m' /\ ro_agree rsegs m'));
    [exact Hh | exact Hl0 | |].
  { rewrite SEG. unfold PAST_NUL. eapply Exec.evt_mono.
    - eapply pn_pro_r; [exact STK | unfold spZ in *; lia | lia | exact RA0].
    - intros ms' (m' & -> & FR & MU & WM & RA). do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM | exact RA]. }
  intros R pc1 mem1 regs1 (-> & -> & FR & MU1 & WM1 & RA1) HG.
  assert (R1_1 : getr regs1 1 = Z_to_bv 64 0x13fd8) by (rewrite HG; reflexivity).
  assert (S1 : getr regs1 2 = Z_to_bv 64 (spZ regs + -48)) by (rewrite HG; reflexivity).
  assert (SP1 : spZ regs1 = spZ regs - 48).
  { unfold spZ at 1. rewrite S1. rewrite unsigned_lit by lia. lia. }
  assert (MU1' : Frame.munch [(spZ regs - 48, spZ regs)] mem mem1).
  { replace (spZ regs - 48) with (spZ regs + -48) by lia. exact MU1. }
  assert (PRE1 : call_pre_k B MR ALLOC_STACK L A regs1 mem1 md).
  { apply (kb_pre_A B API (ALLOC_STACK + PAST_NUL_FRAME) 48 ALLOC_STACK L A regs mem md regs1 mem1
      [(spZ regs - 48, spZ regs)] PRE).
    - lia.
    - lia.
    - lia.
    - exact SP1.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - rewrite HG. reflexivity.
    - rewrite R1_1. vm_compute. reflexivity.
    - exact MU1'.
    - rewrite SEG. exact WM1.
    - intros x Hx Hx'. apply outside_one. lia.
    - intros x Hx Ho. apply outside_one. lia. }
  rewrite <- MAL.
  eapply SR_bind.
  { apply (MALLOC L A regs1 mem1 md (n + 18) b).
    - apply (proj2 (call_pre_k_alloc B MR L A regs1 mem1 md)). exact PRE1.
    - rewrite SEG. exact RA1.
    - rewrite HG. transitivity (Z_to_bv 64 (bv_unsigned (getr regs 11) + 18)); [reflexivity|].
      rewrite R11. rewrite unsigned_lit by lia. reflexivity.
    - exact RES.
    - exact ROOM. }
  intros c1 POST.
  destruct POST as (L' & A' & regs2 & mem2 & md' & res & -> & CP & R10' & Hres0 & Hres16 & FB & (b1 & b2 & BL' & BL) &
    BK & RA2 & GK2 & UB & INIT' & LEN & RES').
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP) as [MID2 RP2].
  pose proof CP as (HM2 & HWF2 & HBD2 & HLY & HPA & _ & HVM & HFR & HKB & HSC).
  destruct (kb_md B API _ _ _ _ HM2) as [Hh2 Hl2].
  assert (INB : In (res, n + 18) (blocks L' A')) by (rewrite BL'; apply in_or_app; right; left; reflexivity).
  pose proof INB as INB'. unfold blocks in INB'. apply in_map_iff in INB' as ([q k] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as Eq1 Eq2. subst k.
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q (n + 18) HM2 Hq) as RNG. rewrite Eq1 in RNG.
  assert (PRS : forall i, 0 <= i < n + 18 -> present mem2 (res + i)).
  { intros i Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q (n + 18) i HM2 Hq Hi) as (P & _).
    rewrite Eq1 in P. exact P. }
  assert (NOWN : forall x, res <= x < res + n + 18 -> ~ owned B L' A' x).
  { intros x Hx. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q (n + 18) (x - res) HM2 Hq ltac:(lia)) as (_ & _ & _ & No).
    rewrite Eq1 in No. replace (res + (x - res)) with x in No by lia. exact No. }
  assert (WR2 : Mem.wr_at rsegs mem2 res (n + 18)).
  { split; [lia|]. split; [lia|]. intros i Hi. destruct (PRS i Hi) as [bb Hb].
    unfold wview, Mem.wa. rewrite Hb. discriminate. }
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM2) as DISJ. rewrite BL' in DISJ.
  assert (OLD : forall a k, In (a, k) (blocks L A) -> a + k <= res \/ res + (n + 18) <= a).
  { intros a k Hin. rewrite BL in Hin. destruct (pn_pairwise_mid _ _ _ _ _ DISJ Hin) as [Hd|Hd];
      unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; lia. }
  assert (BRNG : forall a k, In (a, k) (blocks L A) -> 4096 <= a /\ a + k <= alloc_ceiling).
  { intros a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & Ep & Hp). cbn [fst snd] in Ep.
    injection Ep as Ep1 Ep2. subst k'. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hp) as RP.
    rewrite Ep1 in RP. exact RP. }
  assert (FR2 : Step.rw_cells rsegs mem2 (spZ regs + -48)
      [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (HsKindB.rw_cells_keep mem1 mem2 _ _ FR). intros a Ha.
    cbn [cells_size csize Nat.add] in Ha.
    rewrite <- SEG. apply HFR.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    - unfold scratch_k. rewrite SP1. lia.
    - cbv beta. tauto. }
  assert (HD2 : 0 < n -> Mem.bytes_at rsegs mem2 d db /\ (d + n <= res \/ res + n + 18 <= d)).
  { intros Hn0. destruct (DBLK Hn0) as (pd & k & Hin & Hpd & Hdk).
    pose proof (OLD pd k Hin) as Hdis. pose proof (BRNG pd k Hin) as Hb.
    split; [|lia].
    split; [lia|]. split; [lia|]. intros i Hi.
    change (Mem.mrd rsegs mem2 (Mem.wa (d + Z.of_nat i))) with (mbyte rsegs mem2 (d + Z.of_nat i)).
    rewrite <- SEG.
    replace (d + Z.of_nat i) with (pd + (d - pd + Z.of_nat i)) by lia.
    rewrite (BK pd k (d - pd + Z.of_nat i) Hin ltac:(cbv beta; tauto) ltac:(lia)).
    rewrite (mbyte_munch (ms_segs B) _ mem mem1 (pd + (d - pd + Z.of_nat i)) MU1' ltac:(lia) ltac:(apply outside_one; lia)).
    replace (pd + (d - pd + Z.of_nat i)) with (d + Z.of_nat i) by lia.
    rewrite DB by lia. rewrite Nat2Z.id. reflexivity. }
  assert (SV : forall k, callee_saved k -> getr regs2 (Z_to_bv 5 k) = getr (pn_R1 regs) (Z_to_bv 5 k)).
  { intros k Hk. rewrite (RP2 k Hk). apply HG. }
  assert (Q2 : getr regs2 2 = Z_to_bv 64 (spZ regs + -48)) by exact (SV 2 ltac:(unfold callee_saved; lia)).
  assert (Q8 : getr regs2 8 = Z_to_bv 64 c) by (rewrite <- R12; exact (SV 8 ltac:(unfold callee_saved; lia))).
  assert (Q18 : getr regs2 18 = Z_to_bv 64 n) by (rewrite <- R11; exact (SV 18 ltac:(unfold callee_saved; lia))).
  assert (Q19 : getr regs2 19 = Z_to_bv 64 d) by (rewrite <- R10; exact (SV 19 ltac:(unfold callee_saved; lia))).
  assert (SP2 : bv_unsigned (getr regs2 2) = spZ regs - 48) by (rewrite Q2; rewrite unsigned_lit by lia; lia).
  assert (HRO : forall i, 0 <= i < n + 18 -> Mem.ro_addr rsegs (Mem.wa (res + i)) = false).
  { intros i Hi. unfold Mem.ro_addr. rewrite Mem.wa_unsigned by lia.
    destruct (find_segment rsegs (res + i) 1) as [seg|] eqn:F; [|reflexivity].
    exfalso. destruct FB as (_ & _ & FI). exact (FI i Hi (pn_seg_img SEG _ _ F)). }
  rewrite R1_1.
  eapply (kb_run B regs2 (Z_to_bv 64 0x13fd8) mem2 md'
    (fun R pc' m' => regs_preserved regs R /\ getr R 10 = Z_to_bv 64 res /\ pc' = ret_pc (getr regs 1) /\
       Frame.munch [(res, res + n + 18)] mem2 m' /\ Frame.wmono rsegs mem2 m' /\ ro_agree rsegs m' /\
       Mem.bytes_at rsegs m' res (pn_copy db c))); [exact Hh2 | exact Hl2 | |].
  { rewrite SEG. eapply Exec.evt_mono.
    - eapply pn_tail_r; [exact MEMCPY | exact MEMSET | | exact WR2 | exact R10' | exact Q8 | exact Q18 | exact Q19 |
        exact Hn | exact Hl | exact Hc | lia | rewrite SP2; lia | rewrite SP2; lia | rewrite SP2; lia |
        exact HRO | exact HD2 | rewrite <- SEG; exact RA2].
      rewrite SP2. replace (spZ regs - 48) with (spZ regs + -48) by lia. exact FR2.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & MU' & WM' & RA' & BY').
      do 3 eexists. split; [reflexivity|].
      split.
      { intros r Hr. unfold callee_saved in Hr.
        assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                     r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct HC as [-> | HC].
        - transitivity (Z_to_bv 64 (bv_unsigned (getr regs2 2) + 48)); [reflexivity|].
          rewrite SP2. replace (spZ regs - 48 + 48) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
        - destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
            first [ reflexivity
                  | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
                      transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
                      rewrite (SV k ltac:(unfold callee_saved; lia)); reflexivity end ]. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|].
      split; [exact RA' | exact BY']. }
  intros R pc3 mem3 regs3 (RPR & R10'' & -> & MU3 & WM3 & RA3 & BY3) HG3.
  apply SR_ret.
  exists L', A', regs3, mem3, md', res.
  assert (KEEP : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
      mbyte (ms_segs B) mem3 (a + i) = mbyte (ms_segs B) mem (a + i)).
  { intros a k i Hin Hi. pose proof (OLD a k Hin) as Hd. pose proof (BRNG a k Hin) as Hb.
    rewrite (mbyte_munch (ms_segs B) _ mem2 mem3 (a + i) MU3 ltac:(lia) ltac:(apply outside_one; lia)).
    rewrite (BK a k i Hin ltac:(cbv beta; tauto) Hi).
    exact (mbyte_munch (ms_segs B) _ mem mem1 (a + i) MU1' ltac:(lia) ltac:(apply outside_one; lia)). }
  assert (MA : kb_mid B API (ALLOC_STACK + PAST_NUL_FRAME) (spZ regs) L A mem md (fun _ => False) L A mem1 md).
  { apply (kb_mid_A B API IL (ALLOC_STACK + PAST_NUL_FRAME) (spZ regs) L A mem md mem1 [(spZ regs - 48, spZ regs)]
      (fun _ => False) HM HWF HBD).
    - intros a [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha].
    - exact MU1'.
    - rewrite SEG. exact WM1.
    - intros x Hx Hs _. apply outside_one. lia.
    - intros x Hx _. apply outside_one. lia. }
  assert (MB : kb_mid B API (ALLOC_STACK + PAST_NUL_FRAME) (spZ regs) L A mem md (fun a => False \/ False)
      L' A' mem2 md').
  { apply (kb_mid_seqAX B API _ _ _ _ _ _ _ _ ALLOC_STACK (spZ regs1) (fun _ => False) _ _ _ _ MA MID2); lia. }
  assert (MC : kb_mid B API (ALLOC_STACK + PAST_NUL_FRAME) (spZ regs) L A mem md
      (fun a => (False \/ False) \/ (res <= a < res + n + 18)) L' A' mem3 md').
  { apply (kb_mid_tail B API IL (ALLOC_STACK + PAST_NUL_FRAME) (spZ regs) L A mem md (fun a => False \/ False)
      L' A' mem2 md' mem3 [(res, res + n + 18)] (fun a => res <= a < res + n + 18) MB MU3).
    - rewrite SEG. exact WM3.
    - intros x Hx. destruct (kb_outside_dec [(res, res + n + 18)] (bv_unsigned x)) as [Ho|Ho].
      + rewrite (MU3 x Ho). exact Hx.
      + pose proof (pn_not_out _ _ _ Ho) as Hin.
        apply (pn_wview_none rsegs mem3 x).
        * destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
          exfalso. destruct FB as (_ & _ & FI).
          apply (FI (bv_unsigned x - res) ltac:(lia)). replace (res + (bv_unsigned x - res)) with (bv_unsigned x) by lia.
          exact (pn_seg_img SEG _ _ F).
        * apply WM3. apply pn_wview_some. exact Hx.
    - intros x Hx _ He. cbv beta in He. apply outside_one. lia.
    - intros x Hx Ho. apply outside_one.
      destruct (Z.lt_ge_cases x res) as [H1|H1]; [left; exact H1|].
      destruct (Z.lt_ge_cases x (res + n + 18)) as [H2|H2]; [exfalso; exact (NOWN x ltac:(lia) Ho) | right; exact H2].
    - intros p k i Hp Hp' Hi. apply outside_one.
      assert (Hin : In (ptr_addr L p, k) (blocks L A)).
      { unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact Hp]. }
      pose proof (OLD _ _ Hin). lia. }
  assert (MD : kb_mid B API (ALLOC_STACK + PAST_NUL_FRAME) (spZ regs) L A mem md (fun a => res <= a < res + n + 18)
      L' A' mem3 md').
  { apply (kb_mid_E B API _ _ _ _ _ _ _ _ _ _ _ _ MC). intros a [[[]|[]]|Ha]. exact Ha. }
  assert (GK : guard_kept B mem mem3).
  { intros i Hi.
    assert (Ho : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; right; right; right; right; left; lia).
    assert (Ho' : owned B L' A' (ms_got_guard B + i)) by (right; unfold static_owned; right; right; right; right; left; lia).
    pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hlo.
    rewrite (mbyte_munch (ms_segs B) _ mem2 mem3 (ms_got_guard B + i) MU3 ltac:(lia)).
    - rewrite (GK2 i Hi). exact (mbyte_munch (ms_segs B) _ mem mem1 (ms_got_guard B + i) MU1' ltac:(lia) ltac:(apply outside_one; lia)).
    - apply outside_one. destruct (Z.lt_ge_cases (ms_got_guard B + i) res) as [H1|H1]; [left; exact H1|].
      destruct (Z.lt_ge_cases (ms_got_guard B + i) (res + n + 18)) as [H2|H2];
        [exfalso; exact (NOWN (ms_got_guard B + i) ltac:(lia) Ho') | right; exact H2]. }
  assert (KG : forall x, in_globals [(G_FAIL, 8); (G_LIVE, 24)] x -> mbyte (ms_segs B) mem3 x = mbyte (ms_segs B) mem x).
  { intros x Hx. destruct (GF x Hx) as (Hi & Hr & _ & He & Ho).
    destruct (Ho L' A' mem2 md' HM2) as [_ Hb2].
    pose proof (Hb2 res (n + 18) INB) as Hnb.
    rewrite (mbyte_munch (ms_segs B) _ mem2 mem3 x MU3 ltac:(lia) ltac:(apply outside_one; lia)).
    rewrite (kb_post_globals B API _ ALLOC_STACK L A regs1 mem1 md _ L' A' regs2 mem2 md' x GF (proj1 PRE1) CP
      ltac:(rewrite SP1; lia) Hx ltac:(cbv beta; tauto)).
    exact (mbyte_munch (ms_segs B) _ mem mem1 x MU1' ltac:(lia) ltac:(apply outside_one; lia)). }
  assert (WK : forall a v, (forall k, 0 <= k < 8 -> in_globals [(G_FAIL, 8); (G_LIVE, 24)] (a + k)) ->
     word_mem (ms_segs B) mem a v -> word_mem (ms_segs B) mem3 a v).
  { intros a v Hg Hw. apply (word_mem_frame (ms_segs B) mem mem3 a v Hw). intros k Hk. apply KG. exact (Hg k Hk). }
  split; [rewrite (kb_ret_pc _ HRA); reflexivity|].
  split; [apply (kb_post B API); [exact MD | exact (kb_preserved_getr _ _ _ RPR HG3)]|].
  split; [rewrite SEG; exact RA3|].
  split; [exact GK|].
  split; [exact INIT'|]. split; [exact LEN|].
  split; [rewrite HG3; exact R10''|].
  split; [exact Hres0|]. split; [exact Hres16|]. split; [exact FB|].
  split; [exists b1, b2; split; [exact BL' | exact BL]|].
  split; [intros a k i Hin _ Hi; exact (KEEP a k i Hin Hi)|].
  split; [intros q0 k0 Hq0 _; exact (UB q0 k0 Hq0)|].
  split.
  { intros i Hi. destruct BY3 as (_ & _ & HB).
    assert (LEN' : length (pn_copy db c) = Z.to_nat (n + 18)).
    { unfold pn_copy. rewrite !length_app, repeat_length. cbn [length]. lia. }
    rewrite SEG. replace (res + i) with (res + Z.of_nat (Z.to_nat i)) by lia.
    exact (HB (Z.to_nat i) ltac:(rewrite LEN'; lia)). }
  split; [|exact RES'].
  destruct LG as (AW & L1 & L2 & L3 & ND & FA). destruct AW as (W1 & W2 & W3 & W4).
  split.
  { split; [eapply WK; [|exact W1]; intros k Hk; exists G_LIVE, 24; split; [right; left; reflexivity | unfold G_LIVE; lia]|].
    split; [eapply WK; [|exact W2]; intros k Hk; exists G_LIVE, 24;
      split; [right; left; reflexivity | unfold G_LIVE, G_PEAK; lia]|].
    split; [eapply WK; [|exact W3]; intros k Hk; exists G_LIVE, 24;
      split; [right; left; reflexivity | unfold G_LIVE, G_COUNT; lia]|].
    eapply WK; [|exact W4]; intros k Hk; exists G_FAIL, 8; split; [left; reflexivity | lia]. }
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact ND|].
  eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Hni). cbn [fst snd] in *.
  split; [exact Hk|]. split; [rewrite BL'; apply pn_in_mid; rewrite <- BL; exact Hin|]. split; [|exact Hni].
  apply (word_mem_frame (ms_segs B) mem mem3 (a - 16) k Hw). intros j Hj.
  exact (KEEP (a - 16) (k + 16) j Hin ltac:(lia)).
Qed.

End P.
