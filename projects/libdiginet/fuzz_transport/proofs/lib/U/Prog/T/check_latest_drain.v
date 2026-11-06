From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract check_latest_drain_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- machine words of the comparisons ---- *)

Lemma dr_eqb_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (x - y) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [c Ec]. nia.
Qed.

Lemma dr_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. apply dr_eqb_lit; lia. Qed.

Lemma dr_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

(* sltu then xori 1: the word of y <= x (unsigned) *)
Lemma dr_sltu_xori : forall x y, 0 <= y < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y))) 1) = Z_to_bv 64 (b2z (y <=? x mod 2^64)).
Proof.
  intros x y Hy. unfold v_sltu, c_ltu, bv_ltu. rewrite unsigned_lit_wrap, (unsigned_lit y) by lia.
  destruct (Z.ltb_spec (x mod 2^64) y) as [L|L].
  - rewrite (proj2 (Z.leb_gt y (x mod 2^64))) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le y (x mod 2^64))) by lia. reflexivity.
Qed.

(* seqz then or with a 0 / 1 word *)
Lemma dr_seqz_or : forall d (a : bool), -2^63 <= d < 2^63 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (v_sltiu (Z_to_bv 64 d) 1)) (bv_unsigned (Z_to_bv 64 (b2z a))))
  = Z_to_bv 64 (b2z (negb (truth d) || a)).
Proof.
  intros d a Hd. unfold v_sltiu, truth. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  assert (C : (d mod 2^64 <? 1) = (d =? 0)).
  { destruct (Z.eqb_spec d 0) as [->|N]; [reflexivity|]. apply Z.ltb_ge.
    pose proof (Z.mod_pos_bound d (2^64) ltac:(lia)) as P.
    destruct (Z.eq_dec (d mod 2^64) 0) as [E|E]; [|lia].
    apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia. }
  rewrite C. destruct (d =? 0), a; reflexivity.
Qed.

Lemma dr_and_b2z : forall a b : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (b2z a))) (bv_unsigned (Z_to_bv 64 (b2z b)))) = Z_to_bv 64 (b2z (a && b)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma dr_andi1_eqb : forall b : bool,
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (b2z b))) 1)) (Z_to_bv 64 0) = negb b.
Proof. intros [|]; reflexivity. Qed.

Lemma dr_b2z_eqb : forall b : bool, bv_eqb (Z_to_bv 64 (b2z b)) (Z_to_bv 64 0) = negb b.
Proof. intros [|]; reflexivity. Qed.

(* a 4-byte field below 2^31 reads the same signed and unsigned *)
Lemma dr_s32_small : forall B k, u_at B k 4 < 2^31 -> s32_at B k = u_at B k 4.
Proof.
  intros B k H. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the model ---- *)

Definition dr_allow (B : list byte) : bool :=
  negb (truth (M_display_sent B)) || (Cfg_display_gap_us B <=? u64 (g_now B - M_last_display B)).

Lemma dr_model : forall B B', check_latest_drain_m B = Some (B', tt) ->
  B' = B /\ exists rf, drain_loop (S (Z.to_nat CMDS_MAX)) B (dr_allow B) 0 false = Some rf /\
    ((M_state B =? S_ONLINE) && negb (truth (M_fly_on B)) && (M_backoff_until B <=? g_now B) && rf) = false.
Proof.
  intros B B' H. unfold check_latest_drain_m in H. cbv zeta in H. fold (dr_allow B) in H.
  destruct (drain_loop (S (Z.to_nat CMDS_MAX)) B (dr_allow B) 0 false) as [rf|] eqn:E; [|discriminate].
  destruct ((M_state B =? S_ONLINE) && negb (truth (M_fly_on B)) && (M_backoff_until B <=? g_now B) && rf) eqn:C;
    [discriminate|].
  injection H as <-. split; [reflexivity|]. exists rf. split; [reflexivity | exact C].
Qed.

Lemma dr_step : forall fuel B al i rf, drain_loop fuel B al i false = Some rf -> i < g_nq B ->
  exists fuel', fuel = S fuel' /\ i < CMDS_MAX /\ Q_at B i < CMDS_MAX /\
    drain_loop fuel' B al (i + 1) (negb (truth (Cmd_display B (Q_at B i))) || al) = Some rf.
Proof.
  intros [|fuel] B al i rf H Hi; [discriminate|]. cbn [drain_loop] in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hi) in H. cbn [negb andb] in H.
  destruct (CMDS_MAX <=? i) eqn:C1; [discriminate|].
  destruct (CMDS_MAX <=? Q_at B i) eqn:C2; [discriminate|].
  apply Z.leb_gt in C1, C2. exists fuel. auto.
Qed.

Lemma dr_exit : forall fuel B al i r rf, drain_loop fuel B al i r = Some rf -> (g_nq B <= i \/ r = true) -> rf = r.
Proof.
  intros [|fuel] B al i r rf H D; [discriminate|]. cbn [drain_loop] in H.
  destruct D as [D | ->].
  - rewrite (proj2 (Z.ltb_ge _ _) D) in H. cbn [andb] in H. congruence.
  - cbn [negb] in H. rewrite andb_false_r in H. congruence.
Qed.

Theorem check_latest_drain_holds : check_latest_drain_contract.
Proof.
  unfold check_latest_drain_contract, check_latest_drain_ENTRY, check_latest_drain_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' WM HM Hsp ST LO WOS MI.
  destruct (dr_model B B' HM) as [-> (rf & HL & HC)]. clear HM.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  wk_facts. unfold w_off_stack in WOS.
  carve_frame 16%nat ST.
  step. step.
  lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -16) _ |- _ => rename mm into mF end.
  lazymatch goal with H : rw_cells _ mF (bv_unsigned sp + -16) ?cs |- _ => set (FRC := cs) in H; rename H into FR end.
  (* the epilogue, 0x1686c *)
  assert (EPI : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 : word),
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
                     F (Z_to_bv 64 0x1686c) fc None mF (seg_rom rsegs))).
  { intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29.
    unfold FRC in FR.
    step.
    release_frame FR ST (bv_unsigned sp).
    step. step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMo|]. split; [exact MI|]. split; [exact ST|]. split; [reflexivity | exact WM]. }
  (* after the scan, 0x16840: t3 holds ready *)
  assert (EXIT : forall (x5 x6 x7 x12 x13 x14 x15 x16 x17 x29 : word),
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 209664) (Z_to_bv 64 274632)
                          x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (b2z rf)) x29 t5 t6)
                     F (Z_to_bv 64 0x16840) fc None mF (seg_rom rsegs))).
  { intros x5 x6 x7 x12 x13 x14 x15 x16 x17 x29.
    step. step. step.
    pose proof (s32_range B 12) as R12.
    rewrite dr_eqb_lit by lia.
    destruct (Z.eqb_spec (s32_at B 12) 2) as [S2|S2]; cbn [negb]; cbv iota.
    2:{ apply EPI. }
    step. step.
    pose proof (s32_range B 96) as R96.
    rewrite dr_eqb0 by lia.
    destruct (Z.eqb_spec (s32_at B 96) 0) as [F0|F0]; cbn [negb]; cbv iota.
    2:{ apply EPI. }
    do 5 step.
    pose proof (u_at_range B 65000 8) as RN. pose proof (u_at_range B 56 8) as RBk.
    change (8 * Z.of_nat 8) with 64 in RN, RBk.
    rewrite dr_sltu_xori by lia.
    rewrite dr_and_b2z.
    step.
    rewrite dr_b2z_eqb.
    assert (CF : ((u_at B 56 8 <=? u_at B 65000 8 mod 2^64) && rf) = false).
    { rewrite Z.mod_small by lia.
      change (s32_at B 12) with (M_state B) in S2. change (s32_at B 96) with (M_fly_on B) in F0.
      change (u_at B 56 8) with (M_backoff_until B). change (u_at B 65000 8) with (g_now B).
      rewrite S2, F0 in HC. exact HC. }
    rewrite CF. cbn [negb]. cbv iota.
    apply EPI. }
  (* the scan of g_q, 0x16800 *)
  assert (LOOP : forall fuel i (x7 x28 x29 x14 x5 : word),
    drain_loop fuel B (dr_allow B) i false = Some rf -> 0 <= i < g_nq B ->
    x14 = Z_to_bv 64 (i + 1) -> x5 = Z_to_bv 64 (270536 + 4 * i) ->
    x7 = Z_to_bv 64 (Z.lxor 229576 (2^64 - 1)) ->
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 (Z_to_bv 64 229576) x7 s0 s1
                          (Z_to_bv 64 209664) (Z_to_bv 64 274632) (Z_to_bv 64 (b2z (dr_allow B)))
                          (Z_to_bv 64 (u_at B 64980 4)) x14 (Z_to_bv 64 1025) (Z_to_bv 64 1023) (Z_to_bv 64 40)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
                     F (Z_to_bv 64 0x16800) fc None mF (seg_rom rsegs))).
  { induction fuel as [|fuel IH]; intros i x7 x28 x29 x14 x5 HLi Hi -> -> ->; [discriminate|].
    destruct (dr_step (S fuel) B (dr_allow B) i rf HLi ltac:(lia)) as (f' & Ef & Hi1 & Hq & HL1).
    injection Ef as <-. unfold CMDS_MAX in Hi1, Hq.
    pose proof (u_at_range B 64980 4) as RNQ. change (8 * Z.of_nat 4) with 32 in RNQ.
    change (g_nq B) with (u_at B 64980 4) in Hi.
    assert (RQ : 0 <= Q_at B i) by (unfold Q_at; apply u_at_range).
    step.
    rewrite dr_eqb_lit by lia. replace (i + 1 =? 1025) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    assert (RD1 : ov_read_bytes rsegs mF (Z_to_bv 64 (270536 + 4 * i)) 4 = Some (sub B (OFF_g_q + 4 * i) 4)).
    { apply (wm_read rsegs W_BASE_UBSAN mF B); [exact WM | unfold OFF_g_q; lia | unfold OFF_g_q; lia |].
      f_equal. unfold OFF_g_q. lia. }
    step.
    rewrite ?wm_lw.
    repeat match goal with |- context [s32_at B ?k] =>
      replace (s32_at B k) with (Q_at B i)
        by (replace k with (OFF_g_q + 4 * i) by (unfold OFF_g_q; lia);
            rewrite dr_s32_small; [reflexivity | exact (Z.lt_trans _ 1024 (2 ^ 31) Hq ltac:(lia))]) end.
    step.
    rewrite dr_ltu_lit by lia. replace (1023 <? Q_at B i) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step.
    rewrite (unsigned_lit (Q_at B i)) by lia.
    step.
    replace (Z.lxor 229576 (2 ^ 64 - 1)) with 18446744073709322039 by reflexivity.
    rewrite dr_ltu_lit by lia. replace (18446744073709322039 <? Q_at B i * 40) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    step.
    assert (RD2 : ov_read_bytes rsegs mF (Z_to_bv 64 (229576 + Q_at B i * 40 + 8)) 4
                  = Some (sub B (A_Cmd_display (Q_at B i)) 4)).
    { apply (wm_read rsegs W_BASE_UBSAN mF B); [exact WM | unfold A_Cmd_display, OFF_g_cmd; lia
                                               | unfold A_Cmd_display, OFF_g_cmd; lia |].
      f_equal. unfold A_Cmd_display, OFF_g_cmd. lia. }
    step.
    rewrite ?wm_lw.
    step. step.
    pose proof (s32_range B (A_Cmd_display (Q_at B i))) as RD.
    rewrite dr_seqz_or by lia.
    change (s32_at B (A_Cmd_display (Q_at B i))) with (Cmd_display B (Q_at B i)).
    remember (negb (truth (Cmd_display B (Q_at B i))) || dr_allow B) as r1 eqn:Er1.
    step.
    rewrite dr_ltu_lit by lia.
    destruct (Z.ltb_spec (i + 1) (u_at B 64980 4)) as [Lt|Ge]; cbn [negb]; cbv iota.
    - do 4 step.
      rewrite dr_andi1_eqb.
      destruct r1.
      + assert (rf = true) by (apply (dr_exit fuel B (dr_allow B) (i + 1) true rf HL1); right; reflexivity).
        subst rf. cbn [negb]. cbv iota. step. apply EXIT.
      + cbn [negb]. cbv iota.
        apply (IH (i + 1)); [exact HL1 | change (g_nq B) with (u_at B 64980 4); lia | f_equal; lia | f_equal; lia | reflexivity].
    - assert (rf = r1) by (apply (dr_exit fuel B (dr_allow B) (i + 1) r1 rf HL1); left; change (g_nq B) with (u_at B 64980 4); lia).
      subst rf. apply EXIT. }
  (* 0x167d4: a2 holds allow *)
  assert (JOIN : forall (x12 x13 x14 : word), x12 = Z_to_bv 64 (b2z (dr_allow B)) ->
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 209664) (Z_to_bv 64 274632)
                          x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x167d4) fc None mF (seg_rom rsegs))).
  { intros x12 x13 x14 ->.
    step. step.
    pose proof (u_at_range B 64980 4) as RNQ. change (8 * Z.of_nat 4) with 32 in RNQ.
    rewrite dr_eqb0 by lia.
    destruct (Z.eqb_spec (u_at B 64980 4) 0) as [N0|N0]; cbv iota.
    - step.
      assert (rf = false) by (apply (dr_exit _ B (dr_allow B) 0 false rf HL); left; change (g_nq B) with (u_at B 64980 4); lia).
      subst rf. apply EXIT.
    - do 9 step.
      apply (LOOP (S (Z.to_nat CMDS_MAX)) 0);
        [exact HL | change (g_nq B) with (u_at B 64980 4); lia | f_equal; lia | f_equal; lia | reflexivity]. }
  do 6 step.
  pose proof (s32_range B 72) as R72.
  rewrite dr_eqb0 by lia.
  destruct (Z.eqb_spec (s32_at B 72) 0) as [D0|D0]; cbv iota.
  - step.
    apply JOIN.
    unfold dr_allow. change (M_display_sent B) with (s32_at B 72). rewrite D0. reflexivity.
  - do 7 step.
    apply JOIN.
    pose proof (u_at_range B 65000 8) as RN. pose proof (u_at_range B 64 8) as RL. pose proof (u_at_range B 65072 4) as RG.
    change (8 * Z.of_nat 8) with 64 in RN, RL. change (8 * Z.of_nat 4) with 32 in RG.
    rewrite (unsigned_lit (u_at B 65000 8)) by lia. rewrite (unsigned_lit (u_at B 64 8)) by lia.
    rewrite dr_sltu_xori by lia.
    unfold dr_allow. change (M_display_sent B) with (s32_at B 72).
    replace (truth (s32_at B 72)) with true by (unfold truth; rewrite (proj2 (Z.eqb_neq _ _) D0); reflexivity).
    reflexivity.
Qed.
