(* Case 4 of the op loop of LLVMFuzzerTestOneInput in the plain image, the raw arm (g_raw != 0,
   fuzz_transport.c:1078-1083 `w = fuzz_u16(in); c.len = fuzz_take(in, w % (SPEC_CMD_MAX + 1), &p);
   memcpy(c.bytes, p, c.len); rc = diginet_session_submit(&g_s, &c); check_refusal_submit(&c, rc, before);`
   then settle(0) in the shared tail): from 0x13df4 (op4_j) to the latch 0x1428c. The walk is cut at
   0x13e88 (the u16 built, o4r_mod), 0x13ed0 (the take's n in a2, o4r_copy) and 0x13ee8 (memcpy done, o4r_calls). *)
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

(* ================================================================ the model's facts *)

(* the inversion of a pair option, by name (never injection on a world) *)
Lemma o4r_pair_inv : forall (X Y : Type) (a a' : X) (b b' : Y), Some (a, b) = Some (a', b') -> a' = a /\ b' = b.
Proof. intros X Y a a' b b' H. inversion H. split; reflexivity. Qed.

(* submit_find_m, submit_gfn and submit_rc: copied from the ubsan twin
   (lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_mid.v submit_find_m_lt / submit_gf_upd / submit_gfn / submit_rc), the
   model being the same TModel/TSess0.v. *)
Lemma o4r_find_lt : forall B key fuel j i, submit_find_m B key j fuel = Some (Some i) -> j <= i < S_queue_N.
Proof.
  intros B key fuel. induction fuel as [|f IH]; intros j i H; cbn [submit_find_m] in H; [discriminate|].
  destruct (S_queue_N <=? j) eqn:E1; [discriminate|]. apply Z.leb_gt in E1.
  destruct (S_queue_key B j =? key).
  - injection H as <-. lia.
  - apply IH in H. lia.
Qed.

Lemma o4r_gf_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= OFF_g_fail_next -> g_fail_next (upd B k v) = g_fail_next B /\ length (upd B k v) = length B.
Proof.
  intros B v k LB Hk Hv. split.
  - unfold g_fail_next. apply u_at_upd_out; rewrite ?LB; unfold OFF_g_fail_next, W_LEN in *; lia.
  - apply length_upd; [exact Hk|]. rewrite LB. unfold OFF_g_fail_next, W_LEN in *; lia.
Qed.

Ltac o4r_dest_if H := lazymatch type of H with (if ?b then _ else _) = _ => destruct b end.

(* diginet_session_submit writes only g_s (its queue, s->queued, two counters): g_fail_next stays *)
Lemma o4r_submit_gfn : forall B c B' r, length B = Z.to_nat W_LEN -> length c = 32%nat ->
  diginet_session_submit_m B c = Some (B', r) -> g_fail_next B' = g_fail_next B.
Proof.
  intros B c B' r LB LC H. unfold diginet_session_submit_m in H. cbv zeta in H.
  o4r_dest_if H.
  { apply o4r_pair_inv in H. destruct H as [-> _]. reflexivity. }
  o4r_dest_if H.
  { apply o4r_pair_inv in H. destruct H as [-> _]. unfold set_S_stats_refused.
    apply o4r_gf_upd; [exact LB | unfold A_S_stats_refused, OFF_g_s; lia |
      rewrite length_put; unfold A_S_stats_refused, OFF_g_s, OFF_g_fail_next; cbn; lia]. }
  destruct (if coalescable_m (cmd_key_of c) =? 0 then Some None
            else submit_find_m B (cmd_key_of c) 0 (Z.to_nat (S_queued B)))
    as [[i|]|] eqn:EF; [| |discriminate H].
  - apply o4r_pair_inv in H. destruct H as [-> _].
    assert (Hi : 0 <= i < S_queue_N).
    { destruct (coalescable_m (cmd_key_of c) =? 0); [discriminate EF|]. apply o4r_find_lt in EF. lia. }
    unfold S_queue_N in Hi.
    assert (GL : g_fail_next (upd B (A_S_queue_bytes i) c) = g_fail_next B /\
                 length (upd B (A_S_queue_bytes i) c) = length B).
    { apply o4r_gf_upd; [exact LB | unfold A_S_queue_bytes, OFF_g_s; lia |
        rewrite LC; unfold A_S_queue_bytes, OFF_g_s, OFF_g_fail_next; lia]. }
    destruct GL as [G1 L1].
    unfold set_S_stats_coalesced. rewrite <- G1.
    apply o4r_gf_upd; [rewrite L1; exact LB | unfold A_S_stats_coalesced, OFF_g_s; lia |
      rewrite length_put; unfold A_S_stats_coalesced, OFF_g_s, OFF_g_fail_next; cbn; lia].
  - destruct (S_queued B =? DIGINET_QUEUE_MAX).
    { apply o4r_pair_inv in H. destruct H as [-> _]. reflexivity. }
    destruct (S_queue_N <=? S_queued B) eqn:EQ; [discriminate H|]. apply Z.leb_gt in EQ.
    apply o4r_pair_inv in H. destruct H as [-> _].
    pose proof (u_at_range B A_S_queued 4) as RQ. change (u_at B A_S_queued 4) with (S_queued B) in RQ.
    unfold S_queue_N in EQ.
    assert (GL : g_fail_next (upd B (A_S_queue_bytes (S_queued B)) c) = g_fail_next B /\
                 length (upd B (A_S_queue_bytes (S_queued B)) c) = length B).
    { apply o4r_gf_upd; [exact LB | unfold A_S_queue_bytes, OFF_g_s; lia |
        rewrite LC; unfold A_S_queue_bytes, OFF_g_s, OFF_g_fail_next; lia]. }
    destruct GL as [G1 L1].
    unfold set_S_queued. rewrite <- G1.
    apply o4r_gf_upd; [rewrite L1; exact LB | unfold A_S_queued, OFF_g_s; lia |
      rewrite length_put; unfold A_S_queued, OFF_g_s, OFF_g_fail_next; cbn; lia].
Qed.

(* its return value is one of 0, -1, -5, -10 *)
Ltac o4r_rc_small := lazymatch goal with |- _ <= ?r <= _ => let v := eval vm_compute in r in change r with v; lia end.
Lemma o4r_submit_rc : forall B c B' r, diginet_session_submit_m B c = Some (B', r) -> -10 <= r <= 0.
Proof.
  intros B c B' r H. unfold diginet_session_submit_m in H. cbv zeta in H.
  o4r_dest_if H.
  { apply o4r_pair_inv in H. destruct H as [_ ->]. o4r_rc_small. }
  o4r_dest_if H.
  { apply o4r_pair_inv in H. destruct H as [_ ->]. o4r_rc_small. }
  destruct (if coalescable_m (cmd_key_of c) =? 0 then Some None
            else submit_find_m B (cmd_key_of c) 0 (Z.to_nat (S_queued B)))
    as [[i|]|]; [| |discriminate H].
  - apply o4r_pair_inv in H. destruct H as [_ ->]. o4r_rc_small.
  - destruct (S_queued B =? DIGINET_QUEUE_MAX).
    { apply o4r_pair_inv in H. destruct H as [_ ->]. o4r_rc_small. }
    destruct (S_queue_N <=? S_queued B); [discriminate H|].
    apply o4r_pair_inv in H. destruct H as [_ ->]. o4r_rc_small.
Qed.

(* ================================================================ bytes and cells *)

(* the byte a register's low 8 bits store (ubsan twin lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_lib.v op4_sb) *)
Lemma o4r_sb : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof.
  intros z. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
  pose proof (Z.div_mod z 18446744073709551616 ltac:(lia)) as E.
  replace (z mod 18446744073709551616)
    with (z + - (72057594037927936 * (z / 18446744073709551616)) * 256) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma o4r_skipn_repeat : forall (x : byte) k n, skipn k (repeat x n) = repeat x (n - k).
Proof.
  induction k as [|k IH]; intros n; [rewrite Nat.sub_0_r; reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn [repeat skipn Nat.sub]. apply IH.
Qed.

Lemma o4r_firstn_repeat : forall (x : byte) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof.
  induction k as [|k IH]; intros n H; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [repeat firstn]. f_equal. apply IH. lia.
Qed.

(* a 32-bit field against a small literal, as the zified branch states it (_op6.v op6_s32_eq) *)
Lemma o4r_s32_eq : forall x c, -2^31 <= x < 2^31 -> 0 <= c < 2^31 ->
  (x mod 18446744073709551616 = c <-> x = c).
Proof.
  intros x c Hx Hc. split; intros E; [|subst; apply Z.mod_small; lia].
  destruct (Z_le_gt_dec 0 x) as [P|N]; [rewrite Z.mod_small in E by lia; lia|].
  rewrite <- (Z.mod_add x 1 18446744073709551616) in E by lia. rewrite Z.mod_small in E by lia. lia.
Qed.

(* one byte of a list, as bytes_at reads it (the ubsan twin's
   lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_lib.v op4_sub1) *)
Lemma o4r_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* 0x13e90-0x13ec4 as the kit leaves it: the compiler's w % 25 and the & 0xffff. The kit also wraps the product
   q * 25 (0x13eb8 mul), which _op4k.v op4_mod25 does not state: q = w / 25 < 4096, so the wrap is the identity. *)
Lemma o4r_q25_small : forall X W, 0 <= W < 65536 ->
  0 <= Z.shiftr ((Z.shiftr (X mod 18446744073709551616) 49 + Z.shiftr ((W * 18351) mod 18446744073709551616) 16)
                 mod 18446744073709551616) 4 * 25 < 18446744073709551616.
Proof.
  intros X W HW.
  pose proof (Z.mod_pos_bound X 18446744073709551616 ltac:(lia)) as HX.
  rewrite (Z.mod_small (W * 18351) 18446744073709551616) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 49) with 562949953421312. change (2 ^ 16) with 65536. change (2 ^ 4) with 16.
  assert (Ha : 0 <= X mod 18446744073709551616 / 562949953421312 < 32768).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hb : 0 <= W * 18351 / 65536 < 18351).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small (X mod 18446744073709551616 / 562949953421312 + W * 18351 / 65536) 18446744073709551616)
    by lia.
  assert (Hc : 0 <= (X mod 18446744073709551616 / 562949953421312 + W * 18351 / 65536) / 16 < 4096).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

Lemma o4r_mod25 : forall W, 0 <= W < 65536 ->
  Z.land ((W - (Z.shiftr ((Z.shiftr (Z.shiftl (bv_swrap 32 (W - Z.shiftr ((W * 18351) mod 18446744073709551616) 16)
                                                mod 18446744073709551616) 48
                                      mod 18446744073709551616) 49
                          + Z.shiftr ((W * 18351) mod 18446744073709551616) 16)
                         mod 18446744073709551616) 4 * 25) mod 18446744073709551616)
          mod 18446744073709551616) 65535
  = W mod 25.
Proof.
  intros W HW.
  rewrite (Z.mod_small (_ * 25) 18446744073709551616) by (apply o4r_q25_small; exact HW).
  exact (op4_mod25 W HW).
Qed.

(* a branch whose condition the context decides (the ubsan twin's
   lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_defs.v brv / bsolve2) *)
Ltac o4r_zsolve := first [ lia | (Z.div_mod_to_equations; lia) ].
Ltac o4r_bsolve :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); o4r_bsolve
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); o4r_bsolve
  | |- Z.eqb _ _ = true => apply Z.eqb_eq; o4r_zsolve
  | |- Z.eqb _ _ = false => apply Z.eqb_neq; o4r_zsolve
  | |- Z.ltb _ _ = true => apply Z.ltb_lt; o4r_zsolve
  | |- Z.ltb _ _ = false => apply Z.ltb_ge; o4r_zsolve
  | |- Z.leb _ _ = true => apply Z.leb_le; o4r_zsolve
  | |- Z.leb _ _ = false => apply Z.leb_gt; o4r_zsolve
  | |- _ = _ => reflexivity
  end.
Ltac o4r_brv v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v;
      [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit_wrap; o4r_bsolve]
  end.

Lemma o4r_bytes_nil : forall m x, 0 <= x <= 2 ^ 64 -> bytes_at rsegs m x [].
Proof. intros m x Hx. split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia. Qed.

Lemma o4r_cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma o4r_cb_len : forall m A n bs, rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[W _] _]. cbn [cells_wf cell_wf] in W. tauto. Qed.

(* the model's u16 (ubsan twin lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_lib.v op4_u16_model) *)
Lemma o4r_u16 : forall lo8 hi8, 0 <= lo8 < 256 -> 0 <= hi8 < 256 ->
  Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16 = lo8 + 256 * hi8.
Proof.
  intros lo8 hi8 Hl Hh. rewrite lor_shiftl8_add by lia.
  apply Z.mod_small. change (2 ^ 16) with 65536. lia.
Qed.

(* the u16 the machine builds from the two bytes (ubsan twin lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_lib.v op4_w16) *)
Lemma o4r_w16 : forall lo8 hi8, 0 <= lo8 < 256 -> 0 <= hi8 < 256 ->
  Z.lor (Z.shiftl hi8 8 mod 18446744073709551616) lo8 = lo8 + 256 * hi8.
Proof.
  intros lo8 hi8 Hl Hh.
  rewrite (Z.mod_small (Z.shiftl hi8 8) 18446744073709551616)
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
  rewrite Z.lor_comm. apply lor_shiftl8_add; lia.
Qed.

Lemma o4r_at8_range : forall (D : list byte) k, 0 <= at8 D k < 256.
Proof.
  intros D k. unfold at8, bz. pose proof (bv_unsigned_in_range 8 (nth k D (b8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Section OP4R.
Context (data : Z) (D : list byte).

(* the take of :1079 (fuzz_take_m) and the struct of :1080 *)
Definition o4r_n (c4 : fuzz_in) (w : Z) : Z := if w mod 25 <? fi_n c4 then w mod 25 else fi_n c4.
Definition o4r_cout (c4 : fuzz_in) (n : Z) : fuzz_in := FuzzIn (fi_off c4 + n) (fi_n c4 - n).
Definition o4r_cs (c4 : fuzz_in) (n display key : Z) : list byte :=
  cmd_struct (sub D (fi_off c4) (Z.to_nat n) ++ repeat (b8 0) (Z.to_nat (24 - n))) n display key.

(* the struct cell of the frame, at sp + 0x50 *)
Lemma o4r_struct_at : forall m Sp j10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp (op4_fr (CB 8 j10) bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m (Sp + 80) [CB 32 cs].
Proof.
  intros m Sp j10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H. unfold op4_fr in H.
  change (rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] ++ [CB 32 cs] ++
     [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
    in H.
  apply op4_rw_app in H. destruct H as [_ H]. apply op4_rw_app in H. destruct H as [H _].
  exact H.
Qed.

(* 0x13ee8 (memcpy done) -> the latch: diginet_session_submit(&g_s, &c) (:1081), check_refusal_submit(&c, rc,
   before) (:1082), j 0x14280, then llvm_op4_tail (settle(0), :1083). s0 / s6 = the cursor after the take. *)
Lemma o4r_calls : forall Sp lo ops cout B1 B2 B3 B4 rc before cs m0 m gp tp
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q j10 j30 j70
    rz e0 e1 e2 q0 q1 q2 q3 q4 q5 q6 q7 x4 x7 r8 e3 e4 e5 e6,
  diginet_session_submit_contract -> check_refusal_submit_contract -> settle_contract ->
  op4_mem data D Sp lo B1 m0 m
    (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  0 <= before < 2 ^ 32 -> llvm_cursor D cout -> 0 <= ops < OPS_MAX ->
  diginet_session_submit_m B1 cs = Some (B2, rc) ->
  check_refusal_submit_m B2 cs rc before = Some (B3, tt) ->
  settle_m B3 0 = Some (B4, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops cout B4
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 (Z_to_bv 64 (data + fi_off cout)) (Z_to_bv 64 7)
             q0 q1 q2 q3 q4 q5 q6 q7 (Z_to_bv 64 0x39) x4 x7 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n cout)) r8 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13ee8) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops cout B1 B2 B3 B4 rc before cs m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    j10 j30 j70 rz e0 e1 e2 q0 q1 q2 q3 q4 q5 q6 q7 x4 x7 r8 e3 e4 e5 e6 SUB CRS STC HM HBF HC HOPS HS1 HS2 HS3 HK.
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold LLVM_LOOP_K, LLVM_FRAME in HLO, HSP2.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  wk_facts. wk_eq_fact OFF_g_s.
  pose proof (wm_len _ _ _ _ HWM) as LB1.
  pose proof (o4r_struct_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRW) as HCS.
  pose proof (o4r_cb_len _ _ _ _ HCS) as LCS.
  pose proof (o4r_cb_bytes _ _ _ _ HCS) as HCB.
  pose proof (o4r_submit_rc _ _ _ _ HS1) as HRC.
  assert (HFN2 : g_fail_next B2 <= 1) by (rewrite (o4r_submit_gfn B1 cs B2 rc LB1 LCS HS1); exact HFN).
  clear HMU0 HWMO0 HD HRO HOW HOWIN HCS HRW.
  (* 0x13ee8 auipc a0, 0x1f; 0x13eec addi a0, a0, -0xe8 (a0 = 0x32e00 = W_BASE_PLAIN + OFF_g_s);
     0x13ef0 addi a1, sp, 0x50; 0x13ef4 jal diginet_session_submit *)
  do 4 zstep.
  eapply evt_cut.
  { eapply SUB with (lo := lo) (cp := Sp + 80) (r := rc) (C := cs) (B := B1) (B' := B2).
    - reflexivity.
    - reflexivity.
    - exact HCB.
    - exact LCS.
    - split; [lia|]. split; [lia|].
      split; [unfold off_world; right; lia|].
      unfold off_window. rewrite unsigned_lit by lia. right; lia.
    - Z.div_mod_to_equations. lia.
    - exact HWM.
    - exact HS1.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold diginet_session_submit_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold diginet_session_submit_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m2 &
                     -> & MU2 & WMO2 & MI2 & ST2 & WM2).
  rewrite unsigned_lit in MU2, ST2 by lia.
  assert (HM2 : op4_mem data D Sp lo B2 m0 m2
    (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after_call data D Sp lo diginet_session_submit_FRAME B1 B2 m0 m m2);
      [ exact HM | unfold diginet_session_submit_FRAME, LLVM_LOOP_K; lia | exact MU2
      | exact WMO2 | exact MI2 | exact ST2 | exact WM2 | exact HFN2 ]. }
  clear HSTK HMI HWM MU2 WMO2 MI2 ST2 WM2 HCB.
  pose proof HM2 as HM2c. unfold op4_mem in HM2c.
  destruct HM2c as (_ & _ & _ & _ & HSTK2 & _ & _ & _ & _ & _ & _ & HMI2 & _ & HWM2 & _ & HRW2 & _).
  pose proof (o4r_cb_bytes _ _ _ _ (o4r_struct_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRW2)) as HCB2.
  unfold op4_fr in HRW2. cbn [app] in HRW2.
  rewrite (ret_pc_even 0x13ef8) by (first [lia | reflexivity]).
  (* 0x13ef8 mv a1, a0 (rc); 0x13efc addi a0, sp, 0x50; 0x13f00 ld a2, 0x28(sp) (the slot of (int)before,
     0x1391c); 0x13f04 jal check_refusal_submit *)
  do 4 zstep.
  eapply evt_cut.
  { eapply CRS with (lo := lo) (B := B2) (B' := B3) (cp := Sp + 80) (c := cs) (rc := rc) (before := before).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact HBF.
    - lia.
    - Z.div_mod_to_equations. lia.
    - exact HCB2.
    - exact LCS.
    - unfold off_window. rewrite unsigned_lit by lia. right; lia.
    - exact HWM2.
    - exact HS2.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK2.
    - rewrite unsigned_lit by lia. unfold check_refusal_submit_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold check_refusal_submit_FRAME. lia.
    - exact HMI2. }
  intros ms' Hpost.
  destruct Hpost as (u0' & u1' & u2' & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m3 &
                     -> & MU3 & WMO3 & MI3 & ST3 & EB3 & WM3).
  rewrite unsigned_lit in MU3, ST3 by lia.
  subst B3.
  assert (HM3 : op4_mem data D Sp lo B2 m0 m3
    (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after_call data D Sp lo check_refusal_submit_FRAME B2 B2 m0 m2 m3);
      [ exact HM2 | unfold check_refusal_submit_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU3
      | exact WMO3 | exact MI3 | exact ST3 | exact WM3 | exact HFN2 ]. }
  rewrite (ret_pc_even 0x13f08) by (first [lia | reflexivity]).
  (* 0x13f08 j 0x14280: the shared tail *)
  zstep.
  eapply (llvm_op4_tail data D Sp lo ops cout B2 B4 m0 m3 [CB 8 j10]
            [C8 (Z_to_bv 64 (bv_swrap 32 before)); CB 32 j30; CB 32 cs; CB 8 j70]);
    [ exact STC | exact HM3 | reflexivity | reflexivity | exact HC | exact HOPS | exact HS3 | exact HK ].
Qed.

(* the struct cell (sp + 0x50) regrouped as any cells of its bytes *)
Lemma o4r_fr_mid : forall m Sp j10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mid,
  rw_cells rsegs m Sp (op4_fr (CB 8 j10) bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  cells_wf mid -> cells_bytes mid = cs ->
  rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] ++ mid ++
     [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Proof.
  intros m Sp j10 bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mid H W E.
  apply (op4_rw_mid m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] [CB 32 cs] mid
    [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    H W).
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact E.
Qed.

(* memcpy's destination (the first k bytes of c.bytes) cut out of the frame, and the frame's two other parts *)
Lemma o4r_cut : forall m Sp j10 bf j30 bs b r j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k,
  rw_cells rsegs m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30; CB 24 bs; C1 b; CB 7 r;
     CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (k <= 24)%nat ->
  rw_cells rsegs m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] /\
  rw_cells rsegs m (Sp + 80) [CB k (firstn k bs)] /\
  rw_cells rsegs m (Sp + 80 + Z.of_nat k)
    [CB (24 - k) (skipn k bs); C1 b; CB 7 r;
     CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Proof.
  intros m Sp j10 bf j30 bs b r j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k H Hk.
  pose proof (proj1 (proj1 H)) as WF. cbn [cells_wf cell_wf] in WF.
  assert (LB : length bs = 24%nat) by tauto.
  pose proof (op4_rw_mid m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] [CB 24 bs]
    [CB k (firstn k bs); CB (24 - k) (skipn k bs)]
    [C1 b; CB 7 r;
     CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    H) as H'.
  assert (W' : cells_wf [CB k (firstn k bs); CB (24 - k) (skipn k bs)]).
  { cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn, LB.
    split; [lia|]. split; [lia | exact I]. }
  assert (E' : cells_bytes [CB k (firstn k bs); CB (24 - k) (skipn k bs)] = cells_bytes [CB 24 bs]).
  { cbn [cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn. }
  specialize (H' W' E'). clear W' E'.
  apply op4_rw_app in H'. destruct H' as [H1 H2].
  split; [exact H1|].
  cbn [cells_size csize Nat.add] in H2. change (Z.of_nat 80) with 80 in H2.
  apply (op4_rw_app m (Sp + 80) [CB k (firstn k bs)]) in H2. destruct H2 as [H2 H3].
  split; [exact H2|].
  cbn [cells_size csize] in H3. rewrite Nat.add_0_r in H3. exact H3.
Qed.

(* the frame whole again after memcpy, the struct cell = its bytes *)
Lemma o4r_join : forall m Sp j10 bf j30 k src bs b r j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cs,
  rw_cells rsegs m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] ->
  rw_cells rsegs m (Sp + 80) [CB k src] ->
  rw_cells rsegs m (Sp + 80 + Z.of_nat k)
    [CB (24 - k) bs; C1 b; CB 7 r;
     CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (k <= 24)%nat ->
  src ++ bs ++ b :: r = cs ->
  rw_cells rsegs m Sp (op4_fr (CB 8 j10) bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros m Sp j10 bf j30 k src bs b r j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cs H1 H2 H3 Hk E.
  pose proof (o4r_cb_len _ _ _ _ H2) as L2.
  pose proof (proj1 (proj1 H3)) as W3. cbn [cells_wf cell_wf] in W3.
  assert (L3 : length bs = (24 - k)%nat) by tauto.
  assert (L4 : length r = 7%nat) by tauto.
  assert (H23 : rw_cells rsegs m (Sp + 80)
    ([CB k src] ++ [CB (24 - k) bs; C1 b; CB 7 r;
     CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply op4_rw_app. split; [exact H2|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H3. }
  assert (H123 : rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] ++
     [CB k src; CB (24 - k) bs; C1 b; CB 7 r] ++
     [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply op4_rw_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 80) with 80.
    exact H23. }
  apply (op4_rw_mid m Sp _ _ [CB 32 cs] _ H123).
  - cbn [cells_wf cell_wf]. rewrite <- E, !length_app. cbn [length]. rewrite L2, L3, L4.
    split; [lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. rewrite <- E. reflexivity.
Qed.

(* 0x13ed0 (the take's n in a2) -> 0x13ee8: s0 = s3 + n, s6 = s7 - n (the cursor after the take, :1079),
   c.len = n (0x13ed8 sb a2, 0x68(sp)), memcpy(&c.bytes, p, n) (:1080) *)
Lemma o4r_copy : forall Sp lo ops c4 n B1 B2 B3 B4 rc before display key m0 m gp tp
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q j10 j30 j70
    rz e0 e1 e2 x8 q0 q1 q3 q4 q5 q6 q7 x20 x22 e3 e4 e5 e6,
  memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract -> settle_contract ->
  op4_mem data D Sp lo B1 m0 m
    (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (cmd_struct (repeat (b8 0) 24) 0 display key) j70
            ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  0 <= ops < OPS_MAX -> llvm_cursor D c4 -> 0 <= n <= 24 -> n <= fi_n c4 -> 0 <= before < 2 ^ 32 ->
  diginet_session_submit_m B1 (o4r_cs c4 n display key) = Some (B2, rc) ->
  check_refusal_submit_m B2 (o4r_cs c4 n display key) rc before = Some (B3, tt) ->
  settle_m B3 0 = Some (B4, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops (o4r_cout c4 n) B4
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 x8 (Z_to_bv 64 7) q0 q1 (Z_to_bv 64 n) q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c4)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             x22 (Z_to_bv 64 (fi_n c4)) (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13ed0) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c4 n B1 B2 B3 B4 rc before display key m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc Q j10 j30 j70 rz e0 e1 e2 x8 q0 q1 q3 q4 q5 q6 q7 x20 x22 e3 e4 e5 e6
    MCP SUB CRS STC HM HOPS HC HN HNC HBF HS1 HS2 HS3 HK.
  pose proof HM as HM0. unfold op4_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  unfold llvm_cursor in HC.
  wk_facts.
  clear HMU0 HWMO0 HRO HSZ.
  (* c.bytes as 24 bytes, and the 8 bytes len, display, pad, key *)
  apply (o4r_fr_mid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           [CB 24 (repeat (b8 0) 24); CB 8 ([b8 0; b8 display; b8 0; b8 0] ++ put 4 key)]) in HRW;
    [ | cbn [cells_wf cell_wf]; rewrite repeat_length, length_app, length_put; cbn [length];
        split; [reflexivity|]; split; [reflexivity | exact I]
      | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity ].
  cbn [app] in HRW.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WMO1.
  (* 0x13ed0 add s0, s3, a2; 0x13ed4 sub s6, s7, a2; 0x13ed8 sb a2, 0x68(sp) *)
  do 3 zstep.
  (* 0x13edc addi a0, sp, 0x50; 0x13ee0 mv a1, s3; 0x13ee4 jal memcpy *)
  do 3 zstep.
  (* memcpy's destination: the first n bytes of c.bytes (trap 8) *)
  apply (o4r_cut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.to_nat n)) in HRW; [| lia].
  destruct HRW as (F1 & F2 & F3).
  eapply evt_cut.
  { eapply MCP with (src := sub D (fi_off c4) (Z.to_nat n)) (junk := firstn (Z.to_nat n) (repeat (b8 0) 24)).
    - destruct (Z.eq_dec n 0) as [E0|E0].
      + subst n. change (sub D (fi_off c4) (Z.to_nat 0)) with (@nil byte).
        pose proof (wk_word_range (Z_to_bv 64 (data + fi_off c4))) as R. apply o4r_bytes_nil. lia.
      + rewrite unsigned_lit by lia. apply op4_bytes_sub; [exact HD | lia | lia].
    - rewrite unsigned_lit by lia. apply length_sub; lia.
    - rewrite !unsigned_lit by lia. exact F2.
    - rewrite (unsigned_lit (Sp + 80)), (unsigned_lit n) by lia.
      destruct (Z.eq_dec n 0) as [E0|E0]; [lia|].
      rewrite unsigned_lit by lia. lia.
    - assumption. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (k0 & k1 & k2 & ka1 & ka2 & ka3 & ka4 & ka5 & ka6 & ka7 & kt3 & kt4 & kt5 & kt6 & m2 &
                     -> & MU2 & WMO2 & MI2 & CP2 & SRC2).
  rewrite !unsigned_lit in MU2, CP2 by lia.
  eapply rw_cells_transport in F1;
    [ | exact MU2 | exact WMO2 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I] ].
  eapply rw_cells_transport in F3;
    [ | exact MU2 | exact WMO2 | cbn [disjoint_from]; split; [lia | exact I] ].
  pose proof (o4r_join m2 Sp j10 (Z_to_bv 64 (bv_swrap 32 before)) j30 (Z.to_nat n)
                (sub D (fi_off c4) (Z.to_nat n)) _ _ _ j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (o4r_cs c4 n display key) F1 CP2 F3 ltac:(lia)) as HRW2.
  assert (EB : sub D (fi_off c4) (Z.to_nat n) ++ skipn (Z.to_nat n) (repeat (b8 0) 24) ++
               Z_to_bv 8 (bv_unsigned (Z_to_bv 64 n)) :: skipn 1 (b8 0 :: b8 display :: b8 0 :: b8 0 :: put 4 key)
               = o4r_cs c4 n display key).
  { unfold o4r_cs, cmd_struct. rewrite o4r_skipn_repeat, o4r_sb. cbn [skipn].
    replace (Z.to_nat (24 - n)) with (24 - Z.to_nat n)%nat by lia.
    rewrite <- !app_assoc. reflexivity. }
  specialize (HRW2 EB). clear EB F1 F3 CP2.
  assert (HM2 : op4_mem data D Sp lo B1 m0 m2
    (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (o4r_cs c4 n display key) j70
            ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply (op4_mem_after data D Sp lo 0 B1 B1 m0 m m2); [exact HM0 | unfold LLVM_LOOP_K; lia | | | exact MI2 | | | exact HFN
      | exact HRW2 | reflexivity].
    - eapply munch_trans; [exact MU1|].
      intros x Hx. apply MU2. cbn [outside] in Hx |- *. unfold LLVM_FRAME in Hx.
      destruct Hx as (Hx1 & _). split; [lia | exact I].
    - eapply wmono_trans; [exact WMO1 | exact WMO2].
    - eapply stk_transport_disjoint; [exact HSTK | exact MU2 | exact WMO2 |].
      cbn [disjoint_from]. split; [lia | exact I].
    - eapply rw_cells_transport; [exact HWM | exact MU2 | exact WMO2 |]. wk_disj_side. }
  rewrite (ret_pc_even 0x13ee8) by (first [lia | reflexivity]).
  replace (data + fi_off c4 + n) with (data + fi_off (o4r_cout c4 n)) by (unfold o4r_cout; cbn [fi_off]; lia).
  replace (fi_n c4 - n) with (fi_n (o4r_cout c4 n)) by (unfold o4r_cout; cbn [fi_n]; lia).
  eapply (o4r_calls Sp lo ops (o4r_cout c4 n) B1 B2 B3 B4 rc before (o4r_cs c4 n display key) m0 m2 gp tp);
    [ exact SUB | exact CRS | exact STC | exact HM2 | exact HBF | | exact HOPS | exact HS1 | exact HS2 | exact HS3
    | exact HK ].
  unfold llvm_cursor, o4r_cout. cbn [fi_off fi_n]. lia.
Qed.

(* 0x13e88 (the two bytes of the u16 in a0 / a1) -> 0x13ed0: w = a1 << 8 | a0 (:1078), w % 25 (0x13e90-0x13ebc,
   the compiler's reciprocal), & 0xffff (0x13ec0 ld of the frame constant at sp+0x20), n = min(w % 25, in.n)
   (0x13ec8 bltu / 0x13ecc mv: fuzz_take's n, :1079) *)
Lemma o4r_mod : forall Sp lo ops c4 lo8 hi8 w B1 B2 B3 B4 rc before display key m0 m gp tp
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q j10 j30 j70
    rz e0 e1 e2 x8 q2 q3 q4 q5 q6 q7 x20 x22 e3 e4 e5 e6,
  memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract -> settle_contract ->
  op4_mem data D Sp lo B1 m0 m
    (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (cmd_struct (repeat (b8 0) 24) 0 display key) j70
            ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  0 <= ops < OPS_MAX -> llvm_cursor D c4 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> w = lo8 + 256 * hi8 ->
  0 <= before < 2 ^ 32 ->
  diginet_session_submit_m B1 (o4r_cs c4 (o4r_n c4 w) display key) = Some (B2, rc) ->
  check_refusal_submit_m B2 (o4r_cs c4 (o4r_n c4 w) display key) rc before = Some (B3, tt) ->
  settle_m B3 0 = Some (B4, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops (o4r_cout c4 (o4r_n c4 w)) B4
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 x8 (Z_to_bv 64 7) (Z_to_bv 64 lo8) (Z_to_bv 64 hi8) q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c4)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             x22 (Z_to_bv 64 (fi_n c4)) (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13e88) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c4 lo8 hi8 w B1 B2 B3 B4 rc before display key m0 m gp tp
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q j10 j30 j70 rz e0 e1 e2 x8 q2 q3 q4 q5 q6 q7 x20 x22 e3 e4 e5 e6
    MCP SUB CRS STC HM HOPS HC HLO8 HHI8 HW HBF HS1 HS2 HS3 HK.
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW & _).
  unfold op4_fr in HRW. cbn [app] in HRW.
  pose proof HC as HC'. unfold llvm_cursor, FUZZ_INPUT_MAX in HC'.
  (* 0x13e88 slli a1, a1, 8; 0x13e8c or a0, a1, a0; 0x13e90-0x13ebc a0 = w % 25; 0x13ec0 ld a2, 0x20(sp) (0xffff,
     stored by the loop entry 0x138a4); 0x13ec4 and a2, a0, a2 *)
  do 16 zstep.
  rewrite (o4r_mod25 (Z.lor (Z.shiftl hi8 8 mod 18446744073709551616) lo8))
    by (rewrite (o4r_w16 lo8 hi8 HLO8 HHI8); lia).
  rewrite (o4r_w16 lo8 hi8 HLO8 HHI8), <- HW.
  assert (HM25 : 0 <= w mod 25 < 25) by (apply Z.mod_pos_bound; lia).
  (* 0x13ec8 bltu a2, s7 *)
  zstep.
  destruct (Z.ltb_spec (w mod 25) (fi_n c4)) as [LT|GE].
  - o4r_brv true.
    assert (EN : o4r_n c4 w = w mod 25) by (unfold o4r_n; rewrite (proj2 (Z.ltb_lt _ _) LT); reflexivity).
    rewrite EN in HS1, HS2, HK.
    eapply (o4r_copy Sp lo ops c4 (w mod 25) B1 B2 B3 B4 rc before display key m0 m gp tp);
      [ exact MCP | exact SUB | exact CRS | exact STC | exact HM | exact HOPS | exact HC | lia | lia | exact HBF
      | exact HS1 | exact HS2 | exact HS3 | exact HK ].
  - o4r_brv false.
    (* 0x13ecc mv a2, s7 *)
    zstep.
    assert (EN : o4r_n c4 w = fi_n c4) by (unfold o4r_n; rewrite (proj2 (Z.ltb_ge _ _) GE); reflexivity).
    rewrite EN in HS1, HS2, HK.
    eapply (o4r_copy Sp lo ops c4 (fi_n c4) B1 B2 B3 B4 rc before display key m0 m gp tp);
      [ exact MCP | exact SUB | exact CRS | exact STC | exact HM | exact HOPS | exact HC | lia | lia | exact HBF
      | exact HS1 | exact HS2 | exact HS3 | exact HK ].
Qed.

(* the raw arm's model (op4_raw_m) after its u16: the take's n is o4r_n, len = n (n <= 24 < 2^8) *)
Lemma o4r_model : forall B1 c3 before display key B' cout c4 w,
  op4_raw_m B1 D c3 before display key = Some (B', cout) ->
  fuzz_u16_m D c3 = (c4, w) -> 0 <= fi_n c4 ->
  exists B2 rc B3,
    diginet_session_submit_m B1 (o4r_cs c4 (o4r_n c4 w) display key) = Some (B2, rc) /\
    check_refusal_submit_m B2 (o4r_cs c4 (o4r_n c4 w) display key) rc before = Some (B3, tt) /\
    settle_m B3 0 = Some (B', tt) /\ cout = o4r_cout c4 (o4r_n c4 w).
Proof.
  intros B1 c3 before display key B' cout c4 w H EU HN.
  unfold op4_raw_m in H. rewrite EU in H. cbv beta iota zeta in H.
  assert (ET : fuzz_take_m c4 (w mod (SPEC_CMD_MAX + 1)) = (o4r_cout c4 (o4r_n c4 w), fi_off c4, o4r_n c4 w))
    by reflexivity.
  rewrite ET in H. cbv beta iota zeta in H.
  assert (HB : 0 <= o4r_n c4 w <= 24).
  { unfold o4r_n. pose proof (Z.mod_pos_bound w 25 ltac:(lia)) as R.
    destruct (Z.ltb_spec (w mod 25) (fi_n c4)); lia. }
  rewrite (Z.mod_small (o4r_n c4 w) (2 ^ 8)) in H by (change (2 ^ 8) with 256; lia).
  change (cmd_struct (sub D (fi_off c4) (Z.to_nat (o4r_n c4 w)) ++ repeat (b8 0) (Z.to_nat (24 - o4r_n c4 w)))
            (o4r_n c4 w) display key) with (o4r_cs c4 (o4r_n c4 w) display key) in H.
  destruct (diginet_session_submit_m B1 (o4r_cs c4 (o4r_n c4 w) display key)) as [[B2 rc]|] eqn:HS1;
    [|discriminate H].
  destruct (check_refusal_submit_m B2 (o4r_cs c4 (o4r_n c4 w) display key) rc before) as [[B3 u3]|] eqn:HS2;
    [|discriminate H].
  destruct u3.
  destruct (settle_m B3 0) as [[B4 u4]|] eqn:HS3; [|discriminate H].
  destruct u4.
  apply o4r_pair_inv in H. destruct H as [-> ->].
  exists B2, rc, B3.
  split; [first [exact HS1 | reflexivity]|]. split; [first [exact HS2 | reflexivity]|].
  split; [first [exact HS3 | reflexivity] | reflexivity].
Qed.

(* the frame after the sb of c.display (0x13df8): the struct cell whole again *)
Lemma o4r_join_d : forall cs m Sp j10 bf j30 x b y j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30; CB 25 x; C1 b; CB 6 y;
     CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  x ++ b :: y = cs ->
  rw_cells rsegs m Sp (op4_fr (CB 8 j10) bf j30 cs j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros cs m Sp j10 bf j30 x b y j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H E.
  pose proof (proj1 (proj1 H)) as WF. cbn [cells_wf cell_wf] in WF.
  assert (Lx : length x = 25%nat) by tauto.
  assert (Ly : length y = 6%nat) by tauto.
  apply (op4_rw_mid m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30] [CB 25 x; C1 b; CB 6 y] [CB 32 cs]
    [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] H).
  - cbn [cells_wf cell_wf]. rewrite <- E, length_app. cbn [length]. rewrite Lx, Ly. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. rewrite <- E. reflexivity.
Qed.

(* one input byte, for the load hook (the ubsan twin's lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_lib.v op4_read1) *)
Lemma o4r_read1 : forall m k, bytes_at rsegs m data D -> 0 <= k -> k < Z.of_nat (length D) ->
  ov_read_bytes rsegs m (wa (data + k)) 1 = Some [nth (Z.to_nat k) D (b8 0)].
Proof.
  intros m k HD Hk Hl.
  rewrite (bytes_at_read rsegs m data D k 1 HD Hk) by lia.
  rewrite o4r_sub1 by lia. reflexivity.
Qed.

(* fuzz_u8 on a nonempty / an empty cursor (the ubsan twin's
   lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_lib.v fu8_nz / fu8_z) *)
Lemma o4r_fu8_nz : forall c, fi_n c <> 0 ->
  fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c))).
Proof. intros c H. unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia | reflexivity]. Qed.

Lemma o4r_fu8_z : forall c, fi_n c = 0 -> fuzz_u8_m D c = (c, 0).
Proof. intros c H. unfold fuzz_u8_m. rewrite H. reflexivity. Qed.

(* 0x13df4 -> the latch *)
Lemma o4r_main : op4_raw_stmt data D.
Proof.
  unfold op4_raw_stmt.
  intros Sp lo ops c3 B1 before display key B' cout m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    MCP SUB CRS STC H HRAW HMOD HK.
  destruct H as (rr & t0 & t1 & t2 & x8 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x20 & x22 & t3 & t4 & t5 & t6 & m &
                 j10 & j30 & j70 & -> & HOK & HM).
  destruct HOK as (HOPS & HC & HBF & HDSP & HKEY).
  pose proof HM as HM0. unfold op4_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  unfold op4_fr in HRW; cbn [app] in HRW.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  pose proof HC as HC'. unfold llvm_cursor, FUZZ_INPUT_MAX in HC'.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_raw.
  clear HMU0 HWMO0 HRO HSZ.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WMO1.
  (* 0x13df4 lw a1, 4(s9) (g_raw, W_BASE_PLAIN + OFF_g_raw); 0x13df8 sb a0, 0x69(sp) (c.display);
     0x13dfc beqz a1 *)
  do 3 zstep.
  if_cases K0; zify_cond K0.
  { (* g_raw = 0: the tagged arm, excluded *)
    exfalso. apply HRAW. unfold g_raw, OFF_g_raw.
    apply (proj1 (o4r_s32_eq (s32_at B1 0xfdcc) 0 (s32_range B1 0xfdcc) ltac:(lia))). exact K0. }
  (* the frame: the struct is the model's but for c.len and c.bytes *)
  apply (o4r_join_d (cmd_struct (repeat (b8 0) 24) 0 display key)) in HRW;
    [| rewrite o4r_sb; unfold cmd_struct; cbn [repeat app firstn skipn]; reflexivity ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HM1 : op4_mem data D Sp lo B1 m0 mm
      (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (cmd_struct (repeat (b8 0) 24) 0 display key) j70
              ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply (op4_mem_after data D Sp lo 0 B1 B1 m0 m mm);
          [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MU1 | exact WMO1 | assumption | assumption | assumption
          | exact HFN | exact HRW | reflexivity ])
  end.
  clear HM0 MU1 WMO1 HRW HSTK HMI HWM.
  (* fuzz_u16 inline (:1078, fuzz.h:48-55): 0x13e00 beqz s7 *)
  zstep.
  if_cases K1; zify_cond K1.
  - (* in.n = 0: w = 0 (0x13e70 mv a0, zero; 0x13e74 mv a1, zero; 0x13e78 j 0x13e88) *)
    assert (EU : fuzz_u16_m D c3 = (c3, 0)).
    { unfold fuzz_u16_m. rewrite (o4r_fu8_z c3 K1). cbv beta iota. rewrite (o4r_fu8_z c3 K1). reflexivity. }
    destruct (o4r_model B1 c3 before display key B' cout c3 0 HMOD EU ltac:(lia))
      as (B2 & rc & B3 & HS1 & HS2 & HS3 & ->).
    do 3 zstep.
    eapply (o4r_mod Sp lo ops c3 0 0 0 B1 B2 B3 B' rc before display key m0 _ gp tp);
      [ exact MCP | exact SUB | exact CRS | exact STC | exact HM1 | exact HOPS | exact HC | lia | lia
      | reflexivity | exact HBF | exact HS1 | exact HS2 | exact HS3 | exact HK ].
  - (* 0x13e04 lbu a0, 0(s3) (the low byte); 0x13e08 bne s7, s8 (s8 = 1) *)
    pose proof (o4r_read1 _ (fi_off c3) HD ltac:(lia) ltac:(lia)) as HR0.
    do 2 zstep.
    if_cases K2; zify_cond K2.
    + (* in.n >= 2: 0x13e7c lbu a1, 1(s3) (the high byte); 0x13e80 addi s3, s3, 2; 0x13e84 addi s7, s7, -2 *)
      pose proof (o4r_read1 _ (fi_off c3 + 1) HD ltac:(lia) ltac:(lia)) as HR1.
      do 3 zstep.
      assert (EU : fuzz_u16_m D c3 = (FuzzIn (fi_off c3 + 2) (fi_n c3 + -2),
                                        at8 D (Z.to_nat (fi_off c3)) + 256 * at8 D (Z.to_nat (fi_off c3 + 1)))).
      { unfold fuzz_u16_m. rewrite (o4r_fu8_nz c3 K1). cbv beta iota.
        rewrite (o4r_fu8_nz (FuzzIn (fi_off c3 + 1) (fi_n c3 - 1))) by (cbn [fi_n]; lia).
        cbv beta iota. cbn [fi_off fi_n].
        rewrite o4r_u16 by apply o4r_at8_range.
        replace (fi_off c3 + 1 + 1) with (fi_off c3 + 2) by lia.
        replace (fi_n c3 - 1 - 1) with (fi_n c3 + -2) by lia. reflexivity. }
      destruct (o4r_model B1 c3 before display key B' cout _ _ HMOD EU ltac:(cbn [fi_n]; lia))
        as (B2 & rc & B3 & HS1 & HS2 & HS3 & ->).
      replace (data + fi_off c3 + 2) with (data + fi_off (FuzzIn (fi_off c3 + 2) (fi_n c3 + -2)))
        by (cbn [fi_off]; lia).
      eapply (o4r_mod Sp lo ops (FuzzIn (fi_off c3 + 2) (fi_n c3 + -2)) (at8 D (Z.to_nat (fi_off c3)))
                (at8 D (Z.to_nat (fi_off c3 + 1))) _ B1 B2 B3 B' rc before display key m0 _ gp tp);
        [ exact MCP | exact SUB | exact CRS | exact STC | exact HM1 | exact HOPS
        | unfold llvm_cursor, FUZZ_INPUT_MAX; cbn [fi_off fi_n]; lia | apply o4r_at8_range | apply o4r_at8_range
        | reflexivity | exact HBF | exact HS1 | exact HS2 | exact HS3 | exact HK ].
    + (* in.n = 1: 0x13e0c mv s7, zero; 0x13e10 mv a1, zero; 0x13e14 addi s3, s3, 1; 0x13e18 j 0x13e88 *)
      do 4 zstep.
      assert (EU : fuzz_u16_m D c3 = (FuzzIn (fi_off c3 + 1) 0, at8 D (Z.to_nat (fi_off c3)) + 256 * 0)).
      { unfold fuzz_u16_m. rewrite (o4r_fu8_nz c3 K1). cbv beta iota.
        rewrite (o4r_fu8_z (FuzzIn (fi_off c3 + 1) (fi_n c3 - 1))) by (cbn [fi_n]; lia).
        cbv beta iota.
        rewrite o4r_u16 by (first [apply o4r_at8_range | lia]).
        rewrite K2. reflexivity. }
      destruct (o4r_model B1 c3 before display key B' cout _ _ HMOD EU ltac:(cbn [fi_n]; lia))
        as (B2 & rc & B3 & HS1 & HS2 & HS3 & ->).
      replace (data + fi_off c3 + 1) with (data + fi_off (FuzzIn (fi_off c3 + 1) 0)) by (cbn [fi_off]; lia).
      eapply (o4r_mod Sp lo ops (FuzzIn (fi_off c3 + 1) 0) (at8 D (Z.to_nat (fi_off c3))) 0 _
                B1 B2 B3 B' rc before display key m0 _ gp tp);
        [ exact MCP | exact SUB | exact CRS | exact STC | exact HM1 | exact HOPS
        | unfold llvm_cursor, FUZZ_INPUT_MAX; cbn [fi_off fi_n]; lia | apply o4r_at8_range | lia
        | reflexivity | exact HBF | exact HS1 | exact HS2 | exact HS3 | exact HK ].
Qed.

End OP4R.

Lemma op4_raw : forall data D, op4_raw_stmt data D.
Proof. exact o4r_main. Qed.
