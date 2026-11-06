From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memcpy_c memset_c bcmp_c past_nul_c past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import check_no_overread_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma cno_cz : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res n d : Z) (db j0 : list byte),
  memcpy_contract -> memset_contract ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 j0] ->
  wr_at rsegs m res (n + 18) ->
  a0 = Z_to_bv 64 res -> s3 = Z_to_bv 64 n -> s4 = Z_to_bv 64 d ->
  0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> 4096 <= res ->
  res + n + 18 <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2 ^ 64 ->
  (0 < n -> bytes_at rsegs m d db /\ (d + n <= res \/ res + n + 18 <= d)) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13580) sp gp tp t0' t1' t2' s0 s1 s0 (Z_to_bv 64 (bv_unsigned sp + 24))
                    a2' a3' a4' a5' a6' a7' (Z_to_bv 64 res) s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x15410) fc None m' (seg_rom rsegs) /\
      munch [(res, res + n + 18); (bv_unsigned sp + 8, bv_unsigned sp + 32)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\ bytes_at rsegs m' res (db ++ repeat (Z_to_bv 8 0) 18))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13514) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res n d db j0 MEMCPY MEMSET SL WR E0 E3 E4 Hn Hl Hr Hsp Hsp2 HD MI.
  subst a0 s3 s4.
  assert (B0 : bv_eqb (Z_to_bv 64 res) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  zstep. rewrite B0; cbv iota.
  zstep. zstep.
  destruct (Z.eq_dec n 0) as [->|N0].
  - destruct db as [|b db]; [|cbn in Hl; lia].
    assert (B1 : bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) = true) by reflexivity.
    rewrite B1; cbv iota.
    destruct (pn_rw_sub m res (0 + 18) (res + 0) 1 WR ltac:(lia) ltac:(lia)) as [k0 Q0].
    destruct (pn_rw_sub m res (0 + 18) (res + 0 + 1) 16 WR ltac:(lia) ltac:(lia)) as [k1 Q1].
    destruct (pn_rw_sub m res (0 + 18) (res + 0 + 17) 1 WR ltac:(lia) ltac:(lia)) as [k2 Q2].
    eapply evt_mono.
    { eapply cno_cz2; [exact MEMSET | exact SL | exact (bytes_at_nil rsegs m res ltac:(lia)) | exact Q0 | exact Q1 |
        exact Q2 | reflexivity | reflexivity | lia | reflexivity | lia | lia | lia | exact MI]. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & E' & MU' & WM' &
      MI' & BY').
    do 15 eexists. exists m'. split; [exact E'|].
    split; [eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros x Hx; lia|].
    split; [exact WM'|]. split; [exact MI' | exact BY'].
  - assert (B1 : bv_eqb (Z_to_bv 64 n) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
    rewrite B1; cbv iota.
    destruct (HD ltac:(lia)) as [DB DJ].
    pose proof (bytes_at_bound rsegs m d db DB) as Hd.
    destruct (pn_rw_sub m res (n + 18) res (Z.to_nat n) WR ltac:(lia) ltac:(lia)) as [j R0].
    do 4 zstep.
    eapply evt_cut.
    { eapply MEMCPY with (src := db) (junk := j).
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
    replace (ret_pc (Z_to_bv 64 0x13530)) with (Z_to_bv 64 0x13530) by (apply bv_eq; vm_compute; reflexivity).
    destruct RVc as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    apply (rw_cells_transport rsegs [(res, res + n)] m m2) in SL;
      [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
    apply (wr_at_transport rsegs m m2) in WR; [| exact WMc].
    assert (MU2 : munch [(res, res + n + 18); (bv_unsigned sp + 8, bv_unsigned sp + 32)] m m2).
    { eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    destruct (pn_rw_sub m2 res (n + 18) (res + n) 1 WR ltac:(lia) ltac:(lia)) as [k0 Q0].
    destruct (pn_rw_sub m2 res (n + 18) (res + n + 1) 16 WR ltac:(lia) ltac:(lia)) as [k1 Q1].
    destruct (pn_rw_sub m2 res (n + 18) (res + n + 17) 1 WR ltac:(lia) ltac:(lia)) as [k2 Q2].
    eapply evt_mono.
    { eapply cno_cz2; [exact MEMSET | exact SL | exact BY | exact Q0 | exact Q1 | exact Q2 |
        reflexivity | reflexivity | lia | exact Hl | lia | lia | lia | exact MIc]. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & E' & MU' & WM' &
      MI' & BY').
    do 15 eexists. exists m'. split; [exact E'|].
    split.
    { apply (munch_trans _ m m2 m' MU2). eapply munch_weaken; [|exact MU']. unfold sub_fp. cbn [outside].
      intros x Hx. lia. }
    split; [exact (wmono_trans rsegs m m2 m' WMc WM')|]. split; [exact MI' | exact BY'].
Qed.

Lemma cno_cz_r : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res n d : Z) (db j0 : list byte),
  memcpy_contract -> memset_contract ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 j0] ->
  wr_at rsegs m res (n + 18) ->
  a0 = Z_to_bv 64 res -> s3 = Z_to_bv 64 n -> s4 = Z_to_bv 64 d ->
  0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> 4096 <= res ->
  res + n + 18 <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2 ^ 64 -> 0x55000 <= bv_unsigned sp ->
  (forall i, 0 <= i < n + 18 -> ro_addr rsegs (wa (res + i)) = false) ->
  (0 < n -> bytes_at rsegs m d db /\ (d + n <= res \/ res + n + 18 <= d)) ->
  ro_agree rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13580) sp gp tp t0' t1' t2' s0 s1 s0 (Z_to_bv 64 (bv_unsigned sp + 24))
                    a2' a3' a4' a5' a6' a7' (Z_to_bv 64 res) s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x15410) fc None m' (seg_rom rsegs) /\
      munch [(res, res + n + 18); (bv_unsigned sp + 8, bv_unsigned sp + 32)] m m' /\ wmono rsegs m m' /\
      ro_agree rsegs m' /\ bytes_at rsegs m' res (db ++ repeat (Z_to_bv 8 0) 18))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13514) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res n d db j0 MEMCPY MEMSET SL WR E0 E3 E4 Hn Hl Hr Hsp Hsp2 Hsp3 HRO HD RA.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  eapply evt_mono.
  { apply (evt_normalize rsegs); [exact pn_wx | exact RA |].
    eapply cno_cz; [exact MEMCPY | exact MEMSET | | exact (wr_at_norm rsegs m (normalize rsegs m) res (n + 18) HR0 WR HRO) |
      exact E0 | exact E3 | exact E4 | exact Hn | exact Hl | exact Hr | exact Hsp | exact Hsp2 | |
      apply mem_inv_normalize].
    - apply (pn_rw_norm m _ _ RA); [|exact SL]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      apply pn_ro_hi. lia.
    - intros Hn0. destruct (HD Hn0) as [DB DJ]. split; [exact (bytes_at_normalize rsegs m d db RA DB) | exact DJ]. }
  intros s (s0' & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m0 & E & MU & WM & _ &
    BY) &
    REL & ROS).
  subst s0'.
  destruct (pn_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, (ms_mem s). split; [exact Es|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS WM)|].
  split; [exact (ro_agree_same rsegs m (ms_mem s) RA ROS)|].
  exact (proj2 (bytes_at_rel rsegs (ms_mem s) m0 res _ HR) BY).
Qed.

Ltac cno_cond :=
  unfold bv_eqb, bv_ltu; cbn [negb]; zsimp; try decide_tests; cbn [Z.b2z negb]; try reflexivity; solve_cond_rec.

Ltac cno_br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; cno_cond]
  end.

Ltac cstep := zstep; try decide_tests; cbn [Z.b2z]; zb_fold_lits.

Lemma cno_cmp_none : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 0 -> s4 = Z_to_bv 64 0 ->
  evt rsegs (fun ms' => exists a1' : word,
      ms' = MS (mkR (Z_to_bv 64 0x13608) sp gp tp t0 t1 t2 s0 s1 s3 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 a0 s6
                    s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14378) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    E0 E3 E4.
  subst a0 s3 s4.
  cstep. cstep. cstep.
  cstep. cno_br false.
  cstep. cstep.
  cstep. cno_br false.
  cstep. cno_br true.
  cstep. cstep.
  apply evt_done. eexists. reflexivity.
Qed.

Lemma cno_cmp_some : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q1 q2 q3 len : Z) (xs : list byte),
  bcmp_contract ->
  a0 = Z_to_bv 64 q3 -> s3 = Z_to_bv 64 q1 -> s4 = Z_to_bv 64 q2 ->
  0 < q1 < 2 ^ 64 -> 0 < q2 < 2 ^ 64 -> 0 < q3 < 2 ^ 64 -> Z.of_nat (length xs) = len -> len < 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 len)] ->
  bytes_at rsegs m q1 xs -> bytes_at rsegs m q2 xs -> bytes_at rsegs m q3 xs ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13608) sp gp tp t0' t1' t2' s0 s1 s3 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 a0
                    (Z_to_bv 64 len) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14378) fc None m' (seg_rom rsegs) /\
      (forall x, m' x = m x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q1 q2 q3 len xs BCMP E0 E3 E4 Hq1 Hq2 Hq3 Hlen Hlen2 SL D1 D2 D3 MI.
  subst a0 s3 s4.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= len) by lia.
  cstep. cstep. cstep.
  cstep. cno_br false.
  cstep. cstep.
  cstep. cno_br false.
  cstep. cno_br false.
  cstep. cstep.
  cstep. cno_br false.
  cstep.
  destruct (Z.eq_dec len 0) as [LZ|LZ].
  - cno_br true.
    cstep.
    cstep. cno_br true.
    cstep. cstep.
    apply evt_done. do 15 eexists. split; [reflexivity|]. intros x. reflexivity.
  - cno_br false.
    cstep. cstep. cstep. cstep.
    eapply evt_cut.
    { eapply BCMP with (ls := xs) (rs := xs) (v := 0).
      - rewrite unsigned_lit by lia. exact D1.
      - rewrite unsigned_lit by lia. exact D3.
      - rewrite unsigned_lit by lia. replace (Z.to_nat len) with (length xs) by lia. apply cno_memcmp_refl.
      - exact MI. }
    intros ms' POST. unfold memcmp_post in POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
      E & MUc & WMc & MIc & B1c & B2c).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x135e0)) with (Z_to_bv 64 0x135e0) by (apply bv_eq; vm_compute; reflexivity).
    apply (rw_cells_transport rsegs [] m m2) in SL; [| exact MUc | exact WMc | cbn [disjoint_from]; exact I].
    apply (bytes_at_transport rsegs [] m m2) in D2; [| exact MUc | cbn [disjoint_from]; exact I].
    clear D1 D3 B1c.
    cstep. cno_br false.
    cstep.
    cstep. cno_br false.
    cstep. cstep. cstep. cstep.
    eapply evt_cut.
    { eapply BCMP with (ls := xs) (rs := xs) (v := 0).
      - rewrite unsigned_lit by lia. exact D2.
      - rewrite unsigned_lit by lia. rewrite unsigned_lit in B2c by lia. exact B2c.
      - rewrite unsigned_lit by lia. replace (Z.to_nat len) with (length xs) by lia. apply cno_memcmp_refl.
      - exact MIc. }
    intros ms' POST. unfold memcmp_post in POST.
    destruct POST as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
      E' & MUd & WMd & MId & _ & _).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x135fc)) with (Z_to_bv 64 0x135fc) by (apply bv_eq; vm_compute; reflexivity).
    cstep. cno_br false.
    cstep. cstep.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    intros x. rewrite (MUd x I), (MUc x I). reflexivity.
Qed.

Lemma cno_cmp_some_r : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q1 q2 q3 len : Z) (xs : list byte),
  bcmp_contract ->
  a0 = Z_to_bv 64 q3 -> s3 = Z_to_bv 64 q1 -> s4 = Z_to_bv 64 q2 ->
  0 < q1 < 2 ^ 64 -> 0 < q2 < 2 ^ 64 -> 0 < q3 < 2 ^ 64 -> Z.of_nat (length xs) = len -> len < 2 ^ 64 ->
  0x55000 <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 len)] ->
  bytes_at rsegs m q1 xs -> bytes_at rsegs m q2 xs -> bytes_at rsegs m q3 xs ->
  ro_agree rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13608) sp gp tp t0' t1' t2' s0 s1 s3 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 a0
                    (Z_to_bv 64 len) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14378) fc None m' (seg_rom rsegs) /\
      (forall x, m' x = m x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q1 q2 q3 len xs BCMP E0 E3 E4 Hq1 Hq2 Hq3 Hlen Hlen2 Hsp Hsp2 SL D1 D2 D3 RA.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  eapply evt_mono.
  { apply (evt_normalize rsegs); [exact pn_wx | exact RA |].
    eapply cno_cmp_some; [exact BCMP | exact E0 | exact E3 | exact E4 | exact Hq1 | exact Hq2 | exact Hq3 |
      exact Hlen | exact Hlen2 | | exact (bytes_at_normalize rsegs m q1 xs RA D1) |
      exact (bytes_at_normalize rsegs m q2 xs RA D2) | exact (bytes_at_normalize rsegs m q3 xs RA D3) |
      apply mem_inv_normalize].
    apply (pn_rw_norm m _ _ RA); [|exact SL]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    apply pn_ro_hi. lia. }
  intros s (s0' & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m0 & E & UN) &
    REL & ROS).
  subst s0'.
  destruct (pn_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, (ms_mem s). split; [exact Es|].
  exact (mem_unchanged_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS UN).
Qed.
