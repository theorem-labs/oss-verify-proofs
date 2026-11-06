(* Case 4 of the op loop of LLVMFuzzerTestOneInput in the plain image, tagged arm, segment t3: 0x1408c -> 0x140ec
   (fuzz_transport.c:1102-1106, op_submit inlined): want in s7 (-10 when sys, else -5 when at < 0 and
   g_nq == QUEUE_MAX, else 0), diginet_session_submit(&g_s, &c), check_refusal_submit(&c, rc, before) and, when sys
   is 0, check_latest_submit(rc, want). s8 holds rc across the second call. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4k.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- diginet_session_submit_m (TSess0.v:156-175)
   Copied from the ubsan twin
   (lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_mid.v opt_pair_inv / submit_find_m_lt / submit_gf_upd / submit_gfn /
   submit_rc): model-only. *)

Lemma o4t3_pair_inv : forall (X Y : Type) (a a' : X) (b b' : Y), Some (a, b) = Some (a', b') -> a' = a /\ b' = b.
Proof. intros X Y a a' b b' H. inversion H. split; reflexivity. Qed.

Lemma o4t3_find_lt : forall B key fuel j i, submit_find_m B key j fuel = Some (Some i) -> j <= i < S_queue_N.
Proof.
  intros B key fuel. induction fuel as [|f IH]; intros j i H; cbn [submit_find_m] in H; [discriminate|].
  destruct (S_queue_N <=? j) eqn:E1; [discriminate|]. apply Z.leb_gt in E1.
  destruct (S_queue_key B j =? key).
  - injection H as <-. lia.
  - apply IH in H. lia.
Qed.

Lemma o4t3_gf_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= OFF_g_fail_next ->
  g_fail_next (upd B k v) = g_fail_next B /\ length (upd B k v) = length B.
Proof.
  intros B v k LB Hk Hv. split.
  - unfold g_fail_next. apply u_at_upd_out; rewrite ?LB; unfold OFF_g_fail_next, W_LEN in *; lia.
  - apply length_upd; [exact Hk|]. rewrite LB. unfold OFF_g_fail_next, W_LEN in *; lia.
Qed.

(* destructs the condition of the if a hypothesis H : (if b then _ else _) = _ starts with *)
Ltac o4t3_dest_if H := lazymatch type of H with (if ?b then _ else _) = _ => destruct b end.

(* diginet_session_submit writes only g_s (its queue, s->queued, two counters): g_fail_next stays *)
Lemma o4t3_submit_gfn : forall B c B' r, length B = Z.to_nat W_LEN -> length c = 32%nat ->
  diginet_session_submit_m B c = Some (B', r) -> g_fail_next B' = g_fail_next B.
Proof.
  intros B c B' r LB LC H. unfold diginet_session_submit_m in H. cbv zeta in H.
  o4t3_dest_if H.
  { apply o4t3_pair_inv in H. destruct H as [-> _]. reflexivity. }
  o4t3_dest_if H.
  { apply o4t3_pair_inv in H. destruct H as [-> _]. unfold set_S_stats_refused.
    apply o4t3_gf_upd; [exact LB | unfold A_S_stats_refused, OFF_g_s; lia |
      rewrite length_put; unfold A_S_stats_refused, OFF_g_s, OFF_g_fail_next; cbn; lia]. }
  destruct (if coalescable_m (cmd_key_of c) =? 0 then Some None
            else submit_find_m B (cmd_key_of c) 0 (Z.to_nat (S_queued B)))
    as [[i|]|] eqn:EF; [| |discriminate H].
  - apply o4t3_pair_inv in H. destruct H as [-> _].
    assert (Hi : 0 <= i < S_queue_N).
    { destruct (coalescable_m (cmd_key_of c) =? 0); [discriminate EF|]. apply o4t3_find_lt in EF. lia. }
    unfold S_queue_N in Hi.
    assert (GL : g_fail_next (upd B (A_S_queue_bytes i) c) = g_fail_next B /\
                 length (upd B (A_S_queue_bytes i) c) = length B).
    { apply o4t3_gf_upd; [exact LB | unfold A_S_queue_bytes, OFF_g_s; lia |
        rewrite LC; unfold A_S_queue_bytes, OFF_g_s, OFF_g_fail_next; lia]. }
    destruct GL as [G1 L1].
    unfold set_S_stats_coalesced. rewrite <- G1.
    apply o4t3_gf_upd; [rewrite L1; exact LB | unfold A_S_stats_coalesced, OFF_g_s; lia |
      rewrite length_put; unfold A_S_stats_coalesced, OFF_g_s, OFF_g_fail_next; cbn; lia].
  - destruct (S_queued B =? DIGINET_QUEUE_MAX).
    { apply o4t3_pair_inv in H. destruct H as [-> _]. reflexivity. }
    destruct (S_queue_N <=? S_queued B) eqn:EQ; [discriminate H|]. apply Z.leb_gt in EQ.
    apply o4t3_pair_inv in H. destruct H as [-> _].
    pose proof (u_at_range B A_S_queued 4) as RQ. change (u_at B A_S_queued 4) with (S_queued B) in RQ.
    unfold S_queue_N in EQ.
    assert (GL : g_fail_next (upd B (A_S_queue_bytes (S_queued B)) c) = g_fail_next B /\
                 length (upd B (A_S_queue_bytes (S_queued B)) c) = length B).
    { apply o4t3_gf_upd; [exact LB | unfold A_S_queue_bytes, OFF_g_s; lia |
        rewrite LC; unfold A_S_queue_bytes, OFF_g_s, OFF_g_fail_next; lia]. }
    destruct GL as [G1 L1].
    unfold set_S_queued. rewrite <- G1.
    apply o4t3_gf_upd; [rewrite L1; exact LB | unfold A_S_queued, OFF_g_s; lia |
      rewrite length_put; unfold A_S_queued, OFF_g_s, OFF_g_fail_next; cbn; lia].
Qed.

(* its return value is one of 0, -1, -5, -10 *)
Ltac o4t3_rc_small := lazymatch goal with |- -10 <= ?x <= 0 =>
  let v := eval vm_compute in x in change x with v; lia end.

Lemma o4t3_submit_rc : forall B c B' r, diginet_session_submit_m B c = Some (B', r) -> -10 <= r <= 0.
Proof.
  intros B c B' r H. unfold diginet_session_submit_m in H. cbv zeta in H.
  o4t3_dest_if H.
  { apply o4t3_pair_inv in H. destruct H as [_ ->]. o4t3_rc_small. }
  o4t3_dest_if H.
  { apply o4t3_pair_inv in H. destruct H as [_ ->]. o4t3_rc_small. }
  destruct (if coalescable_m (cmd_key_of c) =? 0 then Some None
            else submit_find_m B (cmd_key_of c) 0 (Z.to_nat (S_queued B)))
    as [[i|]|]; [| |discriminate H].
  - apply o4t3_pair_inv in H. destruct H as [_ ->]. o4t3_rc_small.
  - destruct (S_queued B =? DIGINET_QUEUE_MAX).
    { apply o4t3_pair_inv in H. destruct H as [_ ->]. o4t3_rc_small. }
    destruct (S_queue_N <=? S_queued B); [discriminate H|].
    apply o4t3_pair_inv in H. destruct H as [_ ->]. o4t3_rc_small.
Qed.

(* ---------------------------------------------------------------- want (0x14098-0x140b4), in Z *)

(* the signed and unsigned readings of a 32-bit field agree on a small value (after the ubsan twin,
   lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_m.v t4_s32_iff) *)
Lemma o4t3_s32_iff : forall B k v, 0 <= v < 2 ^ 31 -> (s32_at B k = v <-> u_at B k 4 = v).
Proof.
  intros B k v Hv.
  pose proof (u_at_range B k 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  unfold s32_at, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  split; intros E.
  - destruct (Z.lt_ge_cases (u_at B k 4) (2 ^ 31)) as [H|H].
    + rewrite Z.mod_small in E by lia. lia.
    + rewrite <- (Z.mod_add (u_at B k 4 + 2 ^ 31) (-1) (2 ^ 32)) in E by lia.
      rewrite Z.mod_small in E by lia. lia.
  - rewrite E. rewrite Z.mod_small by lia. lia.
Qed.

(* 0x1409c-0x140a0 sext.w a1, s2; slti a1, a1, 0 with s2 = at as a 32-bit value: at < 0 *)
Lemma o4t3_neg_at : forall at_, (at_ = -1 \/ 0 <= at_ < CMDS_MAX) ->
  Z.b2z (Z.lxor (bv_swrap 32 (at_ mod 4294967296 + 0) mod 18446744073709551616) 9223372036854775808
         <? 9223372036854775808)
  = Z.b2z (at_ <? 0).
Proof.
  intros at_ [->|H].
  - vm_compute. reflexivity.
  - unfold CMDS_MAX in H.
    rewrite (Z.mod_small at_ 4294967296) by lia.
    replace (bv_swrap 32 (at_ + 0)) with at_
      by (rewrite Z.add_0_r; symmetry; apply bv_swrap_small; change (bv_half_modulus 32) with (2 ^ 31); lia).
    rewrite (Z.mod_small at_ 18446744073709551616) by lia.
    change 9223372036854775808 with (2 ^ 63).
    rewrite (zb_lxor_pow2_small at_ 63) by lia.
    replace (at_ + 2 ^ 63 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (at_ <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
Qed.

(* 0x14098 lw a0, 0xc(s9) (g_nq at OFF_g_nq = 0xfdd4 = 64980), 0x140a4-0x140a8 addi a0, a0, -0x200; seqz:
   g_nq == QUEUE_MAX *)
Lemma o4t3_nq_full : forall B,
  Z.b2z ((s32_at B 64980 + -512) mod 18446744073709551616 <? 1) = Z.b2z (g_nq B =? QUEUE_MAX).
Proof.
  intros B. unfold g_nq, OFF_g_nq, QUEUE_MAX.
  pose proof (s32_range B 64980) as R.
  destruct (Z.eqb_spec (u_at B 64980 4) 512) as [E|E].
  - assert (S : s32_at B 64980 = 512) by (apply (proj2 (o4t3_s32_iff B 64980 512 ltac:(lia))); exact E).
    rewrite S. vm_compute. reflexivity.
  - assert (S : s32_at B 64980 <> 512)
      by (intros HS; apply E; exact (proj1 (o4t3_s32_iff B 64980 512 ltac:(lia)) HS)).
    replace ((s32_at B 64980 + -512) mod 18446744073709551616 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge.
    destruct (Z.lt_ge_cases (s32_at B 64980 + -512) 0).
    + rewrite <- (Z.mod_add (s32_at B 64980 + -512) 1 18446744073709551616) by lia.
      rewrite Z.mod_small by lia. lia.
    + rewrite Z.mod_small by lia. lia.
Qed.

(* 0x140ac-0x140b4 and a0, a1, a0; neg a0, a0; andi s7, a0, -5 *)
Lemma o4t3_mask : forall x y : bool,
  Z_to_bv 64 (Z.land ((0 - Z.land (Z.b2z x) (Z.b2z y)) mod 18446744073709551616) 18446744073709551611)
  = Z_to_bv 64 (if x && y then SPEC_E_SPACE else SPEC_OK).
Proof. intros [|] [|]; apply Z_to_bv_eqm; vm_compute; reflexivity. Qed.

Section OP4T3.
Context (data : Z) (D : list byte).

Lemma o4t3_want_rng : forall B1 c3 at_, -10 <= o4_want D B1 c3 at_ <= 0.
Proof.
  intros B1 c3 at_. unfold o4_want, SPEC_E_REFUSED, SPEC_E_SPACE, SPEC_OK.
  destruct (o4_sys D B1 c3); [lia|]. destruct ((at_ <? 0) && (g_nq (o4_B2 B1) =? QUEUE_MAX)); lia.
Qed.

(* a word equation up to 2^64, for the rc / want registers the moves leave *)
Ltac o4t3_weq := apply Z_to_bv_eqm; Z.div_mod_to_equations; lia.

(* the struct diginet_cmd c at sp + 0x50: its 32 bytes, read in place *)
Lemma o4t3_cs_at : forall m Sp v10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp (op4_fr (C8 v10) bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  bytes_at rsegs m (Sp + 80) cs /\ length cs = 32%nat.
Proof.
  intros m Sp v10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H. unfold op4_fr in H.
  pose proof (proj1 (op4_rw_app m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); C8 v10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30]
    ([CB 32 cs] ++ [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                    C8 s1; C8 s0; C8 ra])) H) as [_ H2].
  lazymatch type of H2 with rw_cells _ _ (Sp + ?z) _ => replace z with 80 in H2 by reflexivity end.
  apply (proj1 (op4_rw_app _ _ _ _)) in H2. destruct H2 as [[[W HB] _] _].
  cbn [cells_wf cell_wf cells_bytes cbytes] in W, HB. rewrite app_nil_r in HB.
  split; [exact HB | exact (proj1 W)].
Qed.

(* 0x140b8 -> 0x140ec: the three calls. vs5 = sys (0x13f7c-0x13fa0 / the scan), vs7 = want. *)
Lemma o4t3_calls : forall Sp lo ops c3 B1 before display key at_ B3 B4 B5 rc m0 gp tp
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Q : machine_state -> Prop)
    (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 t3 t4 t5 t6 vs5 vs7 : word) (m : word -> option byte)
    (j30 j70 : list byte),
  diginet_session_submit_contract -> check_refusal_submit_contract -> check_latest_submit_contract ->
  o4_tok D ops c3 B1 before display key ->
  op4_mem data D Sp lo (o4_B2 B1) m0 m
    (op4_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
            (o4_cs D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  vs5 = Z_to_bv 64 (b2z (o4_sys D B1 c3)) ->
  vs7 = Z_to_bv 64 (o4_want D B1 c3 at_) ->
  diginet_session_submit_m (o4_B2 B1) (o4_cs D B1 c3 display key) = Some (B3, rc) ->
  check_refusal_submit_m B3 (o4_cs D B1 c3 display key) rc before = Some (B4, tt) ->
  (if o4_sys D B1 c3 then Some (B4, tt) else check_latest_submit_m B4 rc (o4_want D B1 c3 at_))
    = Some (B5, tt) ->
  (forall ms', op4_t3 data D m0 gp tp Sp lo ops c3 B1 before display key at_ B5
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (at_ mod 2 ^ 32)) (Z_to_bv 64 (data + fi_off (o4_c4 D c3))) (Z_to_bv 64 0x37558)
             vs5 (Z_to_bv 64 (o4_n D c3)) vs7 x8
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
             (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x140b8) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 B1 before display key at_ B3 B4 B5 rc m0 gp tp
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 t3 t4 t5 t6 vs5 vs7 m j30 j70
    SUB CRS CLS HTOK HM E5 E7 HSUB HREF HLAT HK.
  subst vs5 vs7.
  pose proof HTOK as ((HOPS & HCUR & HBEF & HDIS & HKEY) & HSER).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM
                   & HFN & HRW & HSZ).
  destruct (o4t3_cs_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRW) as [HCS LCS].
  unfold op4_fr in HRW; cbn [app] in HRW.
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  wk_facts. wk_eq_fact OFF_g_s.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  pose proof (o4t3_submit_rc _ _ _ _ HSUB) as HRC.
  pose proof (o4t3_want_rng B1 c3 at_) as HWANT.
  assert (GF3 : g_fail_next B3 <= 1)
    by (rewrite (o4t3_submit_gfn _ _ _ _ LB LCS HSUB); exact HFN).
  (* ---- 0x140b8-0x140c4: a0 = 0x32e00 = &g_s (auipc + addi), a1 = sp + 0x50 = &c, jal diginet_session_submit ---- *)
  do 4 zstep.
  eapply evt_cut.
  { eapply SUB with (lo := lo) (cp := Sp + 80) (r := rc) (C := o4_cs D B1 c3 display key)
                    (B := o4_B2 B1) (B' := B3).
    - word_eq_tac.
    - word_eq_tac.
    - exact HCS.
    - exact LCS.
    - red. unfold off_world, off_window. rewrite unsigned_lit by lia.
      unfold diginet_session_submit_FRAME.
      split; [lia|]. split; [lia|]. split; [right; lia | right; lia].
    - lia.
    - exact HWM.
    - exact HSUB.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold diginet_session_submit_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold diginet_session_submit_FRAME. lia.
    - exact HMI. }
  intros ms1 PO1.
  destruct PO1 as (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & m1 &
                   -> & MU1 & WMO1 & MI1 & ST1 & WM1).
  rewrite unsigned_lit in MU1, ST1 by lia.
  assert (HM1 : op4_mem data D Sp lo B3 m0 m1
    (op4_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
            (o4_cs D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after_call data D Sp lo diginet_session_submit_FRAME (o4_B2 B1) B3 m0 m m1);
      [ exact HM | unfold diginet_session_submit_FRAME, LLVM_LOOP_K; lia | exact MU1 | exact WMO1
      | exact MI1 | exact ST1 | exact WM1 | exact GF3 ]. }
  clear HMU0 HWMO0 HD HSTK HMI HRO HWM HRW HCS MU1 WMO1 MI1 ST1 WM1 HM.
  pose proof HM1 as HM1c. unfold op4_mem in HM1c.
  destruct HM1c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & _ & HRW & _).
  destruct (o4t3_cs_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRW) as [HCS _].
  unfold op4_fr in HRW; cbn [app] in HRW.
  rewrite (ret_pc_even 0x140c8) by (first [lia | reflexivity]).
  (* ---- 0x140c8-0x140d8: s8 = rc; a0 = sp + 0x50, a1 = rc, a2 = ld 0x28(sp) = (int)before;
     jal check_refusal_submit ---- *)
  do 5 zstep.
  eapply evt_cut.
  { eapply CRS with (lo := lo) (B := B3) (B' := B4) (cp := Sp + 80) (c := o4_cs D B1 c3 display key)
                    (rc := rc) (before := before).
    - word_eq_tac.
    - o4t3_weq.
    - word_eq_tac.
    - lia.
    - exact HBEF.
    - lia.
    - lia.
    - exact HCS.
    - exact LCS.
    - unfold off_window. rewrite unsigned_lit by lia. unfold check_refusal_submit_FRAME. right. lia.
    - exact HWM.
    - exact HREF.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold check_refusal_submit_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold check_refusal_submit_FRAME. lia.
    - exact HMI. }
  intros ms2 PO2.
  destruct PO2 as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m2 &
                   -> & MU2 & WMO2 & MI2 & ST2 & EB4 & WM2).
  rewrite unsigned_lit in MU2, ST2 by lia.
  subst B4.
  assert (HM2 : op4_mem data D Sp lo B3 m0 m2
    (op4_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
            (o4_cs D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after_call data D Sp lo check_refusal_submit_FRAME B3 B3 m0 m1 m2);
      [ exact HM1 | unfold check_refusal_submit_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU2
      | exact WMO2 | exact MI2 | exact ST2 | exact WM2 | exact GF3 ]. }
  clear HD HSTK HMI HRO HWM HRW HCS MU2 WMO2 MI2 ST2 WM2 HM1.
  rewrite (ret_pc_even 0x140dc) by (first [lia | reflexivity]).
  (* ---- 0x140dc bnez s5 ---- *)
  destruct (o4_sys D B1 c3) eqn:ESYS; cbn [b2z]; try rewrite ESYS in HLAT; cbv iota in HLAT.
  - (* sys: straight to 0x140ec; the model skips check_latest_submit *)
    injection HLAT as EB5. subst B5.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota end.
    apply HK. unfold op4_t3. do 19 eexists. split; [reflexivity|].
    split; [exact HTOK|]. exists j30, j70. exact HM2.
  - (* not sys: 0x140e0-0x140e8 a0 = rc, a1 = want, jal check_latest_submit *)
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota end.
    pose proof HM2 as HM2c. unfold op4_mem in HM2c.
    destruct HM2c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & _ & HRW & _).
    unfold op4_fr in HRW; cbn [app] in HRW.
    do 3 zstep.
    eapply evt_cut.
    { eapply CLS with (lo := lo) (B := B3) (B' := B5) (rc := rc) (want := o4_want D B1 c3 at_).
      - o4t3_weq.
      - o4t3_weq.
      - lia.
      - lia.
      - exact HWM.
      - exact HLAT.
      - rewrite unsigned_lit by lia. exact HSP.
      - rewrite unsigned_lit by lia. exact HSTK.
      - rewrite unsigned_lit by lia. unfold check_latest_submit_FRAME. lia.
      - unfold w_off_stack. rewrite unsigned_lit by lia. unfold check_latest_submit_FRAME. lia.
      - exact HMI. }
    intros ms3 PO3.
    destruct PO3 as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & m3 &
                     -> & MU3 & WMO3 & MI3 & ST3 & EB5 & WM3).
    rewrite unsigned_lit in MU3, ST3 by lia.
    subst B5.
    assert (HM3 : op4_mem data D Sp lo B3 m0 m3
      (op4_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
              (o4_cs D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply (op4_mem_after_call data D Sp lo check_latest_submit_FRAME B3 B3 m0 m2 m3);
        [ exact HM2 | unfold check_latest_submit_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU3
        | exact WMO3 | exact MI3 | exact ST3 | exact WM3 | exact GF3 ]. }
    rewrite (ret_pc_even 0x140ec) by (first [lia | reflexivity]).
    apply HK. unfold op4_t3. do 19 eexists. split; [reflexivity|].
    split; [exact HTOK|]. exists j30, j70. exact HM3.
Qed.

(* 0x1408c -> 0x140ec *)
Lemma op4_tag3_sec : op4_tag3_stmt data D.
Proof.
  unfold op4_tag3_stmt.
  intros Sp lo ops c3 B1 before display key at_ B3 B4 B5 rc m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc ms Q SUB CRS CLS HT2 HAT HSUB HREF HLAT HK.
  destruct HT2 as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m &
                   -> & HTOK & (j30 & j70 & HM)).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM
                   & HFN & HRW & HSZ).
  unfold op4_fr in HRW; cbn [app] in HRW.
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  wk_facts. wk_eq_fact OFF_g_nq. wk_eq_fact OFF_g_fail_next.
  destruct (o4_sys D B1 c3) eqn:ESYS.
  - (* sys: 0x1408c beqz s5 not taken; 0x14090 s7 = -10 (SPEC_E_REFUSED); 0x14094 j 0x140b8 *)
    cbn [b2z].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota end.
    do 2 zstep.
    eapply (o4t3_calls Sp lo ops c3 B1 before display key at_ B3 B4 B5 rc m0 gp tp);
      [ exact SUB | exact CRS | exact CLS | exact HTOK | exact HM
      | rewrite ESYS; reflexivity
      | unfold o4_want; rewrite ESYS; unfold SPEC_E_REFUSED; word_eq_tac
      | exact HSUB | exact HREF | rewrite ESYS; exact HLAT | exact HK ].
  - (* not sys: 0x1408c beqz s5 taken; 0x14098-0x140b4 s7 = want *)
    cbn [b2z].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota end.
    do 8 zstep.
    eapply (o4t3_calls Sp lo ops c3 B1 before display key at_ B3 B4 B5 rc m0 gp tp);
      [ exact SUB | exact CRS | exact CLS | exact HTOK | exact HM
      | rewrite ESYS; reflexivity
      | | exact HSUB | exact HREF | rewrite ESYS; exact HLAT | exact HK ].
    rewrite (o4t3_neg_at at_ HAT), (o4t3_nq_full (o4_B2 B1)), o4t3_mask.
    unfold o4_want. rewrite ESYS. reflexivity.
Qed.

End OP4T3.

Lemma op4_tag3 : forall data D, op4_tag3_stmt data D.
Proof. exact op4_tag3_sec. Qed.
