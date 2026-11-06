(* Case 4 of the plain op loop, the tagged arm's record of the command: 0x140ec-0x14260 (fuzz_transport.c:1104-1115,
   op_submit inlined). When want = SPEC_OK the command is written into g_cmd[serial] (st, key, display, len, the
   first len bytes) and either replaces g_q[at] (marking the old command REPLACED) or is appended at g_q[g_nq++]. *)
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

(* ---------------------------------------------------------------- bytes and words *)

(* the struct diginet_cmd c at sp + 0x50 (TOps.v cmd_struct) as the cells the three loads of 0x140f8-0x14100 read *)
Lemma o4t4_cb_len : forall cb len display key, length (cmd_struct cb len display key) = 32%nat -> length cb = 24%nat.
Proof. intros cb len display key H. unfold cmd_struct in H. rewrite !length_app, length_put in H. cbn [length] in H. lia. Qed.

Lemma o4t4_cs_cells : forall (cb : list byte) len display key,
  cells_bytes [CB 24 cb; CB 1 [b8 len]; CB 1 [b8 display]; CB 2 [b8 0; b8 0]; CB 4 (put 4 key)]
  = cells_bytes [CB 32 (cmd_struct cb len display key)].
Proof. intros. unfold cmd_struct. cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity. Qed.

(* the bytes of one CB cell of a frame *)
Lemma o4t4_cell_bytes : forall m A pre n bs post k, rw_cells rsegs m A (pre ++ CB n bs :: post) ->
  Z.of_nat (cells_size pre) = k -> bytes_at rsegs m (A + k) bs.
Proof.
  intros m A pre n bs post k H <-. apply op4_rw_app in H. destruct H as [_ H].
  change (CB n bs :: post) with ([CB n bs] ++ post) in H. apply op4_rw_app in H. destruct H as [H _].
  destruct H as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

(* lbu of a byte cell [b8 z] (0x140fc, 0x14100) *)
Lemma o4t4_b8u : forall z, 0 <= z < 256 -> bv_unsigned (b8 z) = z.
Proof.
  intros z Hz. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* lw of the key cell put 4 key (0x140f8) *)
Lemma o4t4_lw_put : forall v,
  sext 64 (bv_extract 0 32 (le_bytes_to_word (put 4 v))) = Z_to_bv 64 (s32_at (put 4 v) 0).
Proof. intros v. rewrite <- wm_lw. rewrite sub_all; [reflexivity | apply length_put]. Qed.

Lemma o4t4_put4_mod : forall x, put 4 (x mod 2 ^ 32) = put 4 x.
Proof. intros x. unfold put. rewrite <- (Z_to_le_bytes_mod 4 x 32) by lia. reflexivity. Qed.

Lemma o4t4_swrap_mod : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* the word the lw / sw pair of 0x140f8 / 0x14108 moves is the key *)
Lemma o4t4_put_s32 : forall v, put 4 (s32_at (put 4 v) 0) = put 4 v.
Proof.
  intros v.
  assert (E : s32_at (put 4 v) 0 mod 2 ^ 32 = v mod 2 ^ 32).
  { unfold s32_at. rewrite o4t4_swrap_mod, u_at_put. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    apply Z.mod_mod. lia. }
  transitivity (put 4 (s32_at (put 4 v) 0 mod 2 ^ 32)); [symmetry; apply o4t4_put4_mod|].
  rewrite E. apply o4t4_put4_mod.
Qed.

(* ---------------------------------------------------------------- the world the record writes *)

(* a write below g_fail_next (0xfdc8) keeps the world's length and g_fail_next *)
Lemma o4t4_wr : forall (u v : list byte) k, Z.of_nat (length u) = W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= OFF_g_fail_next ->
  Z.of_nat (length (upd u k v)) = W_LEN /\ g_fail_next (upd u k v) = g_fail_next u.
Proof.
  intros u v k Hu Hk Hv. split.
  - rewrite length_upd; [exact Hu | exact Hk | rewrite Hu; unfold OFF_g_fail_next, W_LEN in *; lia].
  - unfold g_fail_next. apply u_at_upd_out;
      [exact Hk | unfold OFF_g_fail_next; lia | right; exact Hv | rewrite Hu; unfold OFF_g_fail_next, W_LEN in *; lia].
Qed.

(* the four field stores 0x14104-0x14110 (:1108-1111), in the machine's order = the model's *)
Lemma o4t4_w4 : forall B5 s key display len,
  upd (upd (upd (upd B5 (A_Cmd_st s) (put 4 1)) (4 + 1 * A_Cmd_st s) (put 4 (s32_at (put 4 key) 0)))
           (8 + 1 * A_Cmd_st s) (put 4 display))
      (36 + 1 * A_Cmd_st s) (put 1 len)
  = set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 s PENDING) s key) s display) s len.
Proof.
  intros. unfold set_Cmd_len, set_Cmd_display, set_Cmd_key, set_Cmd_st.
  rewrite o4t4_put_s32.
  replace (4 + 1 * A_Cmd_st s) with (A_Cmd_key s) by (unfold A_Cmd_key, A_Cmd_st; lia).
  replace (8 + 1 * A_Cmd_st s) with (A_Cmd_display s) by (unfold A_Cmd_display, A_Cmd_st; lia).
  replace (36 + 1 * A_Cmd_st s) with (A_Cmd_len s) by (unfold A_Cmd_len, A_Cmd_st; lia).
  reflexivity.
Qed.

Lemma o4t4_w4_facts : forall B5 s key display len, Z.of_nat (length B5) = W_LEN -> 0 <= s < 1024 ->
  Z.of_nat (length (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 s PENDING) s key) s display) s len))
    = W_LEN /\
  g_fail_next (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 s PENDING) s key) s display) s len)
    = g_fail_next B5.
Proof.
  intros B5 s key display len HL Hs.
  unfold set_Cmd_len, set_Cmd_display, set_Cmd_key, set_Cmd_st.
  assert (EOF : OFF_g_fail_next = 64968) by reflexivity.
  assert (EOC : OFF_g_cmd = 19912) by reflexivity.
  pose proof (o4t4_wr B5 (put 4 PENDING) (A_Cmd_st s) HL ltac:(unfold A_Cmd_st; lia)
                ltac:(rewrite length_put; unfold A_Cmd_st; lia)) as [L1 F1].
  pose proof (o4t4_wr _ (put 4 key) (A_Cmd_key s) L1 ltac:(unfold A_Cmd_key; lia)
                ltac:(rewrite length_put; unfold A_Cmd_key; lia)) as [L2 F2].
  pose proof (o4t4_wr _ (put 4 display) (A_Cmd_display s) L2 ltac:(unfold A_Cmd_display; lia)
                ltac:(rewrite length_put; unfold A_Cmd_display; lia)) as [L3 F3].
  pose proof (o4t4_wr _ (put 1 len) (A_Cmd_len s) L3 ltac:(unfold A_Cmd_len; lia)
                ltac:(rewrite length_put; unfold A_Cmd_len; lia)) as [L4 F4].
  split; [exact L4 | rewrite F4, F3, F2, F1; reflexivity].
Qed.

(* :1117, the append arm: the machine stores g_nq before g_q[nq], the model after; the spans are disjoint (from
   the ubsan twin, lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_m.v t4_appw) *)
Lemma o4t4_appw : forall Bw nq serial, Z.of_nat (length Bw) = W_LEN -> 0 <= nq < 1024 ->
  upd (upd Bw OFF_g_nq (put 4 (nq + 1))) (OFF_g_q + 4 * nq) (put 4 serial)
  = set_g_nq (set_Q_at Bw nq serial) ((nq + 1) mod 2 ^ 32).
Proof.
  intros Bw nq serial HL Hnq. unfold set_g_nq, set_Q_at.
  rewrite (o4t4_put4_mod (nq + 1)).
  apply upd_upd_comm; rewrite ?length_put, ?HL; unfold OFF_g_nq, OFF_g_q, W_LEN in *; lia.
Qed.

Section T4.
Context (data : Z) (D : list byte).

Lemma o4t4_len_rng : forall c3, 3 <= o4_len D c3 <= 24.
Proof. intros c3. unfold o4_len. pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c3)) 22 ltac:(lia)). lia. Qed.

Lemma o4t4_want_rng : forall B1 c3 at_,
  o4_want D B1 c3 at_ = SPEC_E_REFUSED \/ o4_want D B1 c3 at_ = SPEC_E_SPACE \/ o4_want D B1 c3 at_ = SPEC_OK.
Proof.
  intros B1 c3 at_. unfold o4_want. destruct (o4_sys D B1 c3); [left; reflexivity|].
  destruct ((at_ <? 0) && (g_nq (o4_B2 B1) =? QUEUE_MAX)); [right; left | right; right]; reflexivity.
Qed.

(* ---------------------------------------------------------------- 0x14120 -> 0x14260, at < 0: append *)
Lemma o4t4_app : forall Sp lo ops c3 B1 before display key Bw B6 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
    s11 F fc (Q : machine_state -> Prop) (rr t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) m,
  o4_tok D ops c3 B1 before display key ->
  o4_tmem data D Sp lo c3 B1 before display key Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  g_nq Bw < CMDS_MAX ->
  B6 = set_g_nq (set_Q_at Bw (g_nq Bw) (g_ncmd B1)) ((g_nq Bw + 1) mod 2 ^ 32) ->
  (forall ms', op4_t4 data D m0 gp tp Sp lo ops c3 B1 before display key B6
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 x8 (Z_to_bv 64 (g_ncmd B1)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 4294967295) (Z_to_bv 64 (data + fi_off (o4_c4 D c3))) (Z_to_bv 64 0x37558)
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (o4_n D c3)) x23 (Z_to_bv 64 1)
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
             (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14120) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 B1 before display key Bw B6 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    rr t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 m HOK (j30 & j70 & HM) HNQ EB6 HK.
  pose proof HOK as (_ & HSER). unfold CMDS_MAX in HSER, HNQ.
  pose proof HM as HM0. unfold op4_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  clear HMU0 HWMO0 HD HRO HRW HOW HOWIN.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length Bw) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_LOOP_K, LLVM_FRAME in HLO, HSP2.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_nq. wk_eq_fact OFF_g_q.
  pose proof (u_at_range Bw OFF_g_nq 4) as RNQ. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RNQ.
  change (u_at Bw OFF_g_nq 4) with (g_nq Bw) in RNQ.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU6.
  pose proof (wmono_refl rsegs m) as WMO6.
  (* 0x14120 sext.w a0, s2 (at = -1); 0x14124 bltz a0 -> 0x14240 *)
  do 2 zstep.
  if_cases K; zify_cond K.
  2:{ exfalso. lia. }
  (* 0x14240 lwu a0, 0xc(s9) (g_nq: 0xc(s9) = W_BASE_PLAIN + OFF_g_nq) *)
  zstep.
  change (u_at Bw 64980 4) with (g_nq Bw).
  (* 0x14244 addi a1, a0, 1; 0x14248 sw a1, 0xc(s9) (g_nq + 1) *)
  do 2 zstep.
  (* 0x1424c auipc a1, 0x2d; 0x14250 addi a1, a1, 0x30c (0x41558 = W_BASE_PLAIN + OFF_g_q); 0x14254 slli a0, a0, 2;
     0x14258 add a0, a1, a0 (&g_q[nq]) *)
  do 4 zstep.
  (* a0 = 0x41558 + (g_nq << 2), the address of g_q[g_nq] *)
  lazymatch goal with |- context [Z_to_bv 64 (267608 + ?X)] =>
    replace (Z_to_bv 64 (267608 + X)) with (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_q + 4 * g_nq Bw)))
      by (f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.mod_small by lia; unfold W_BASE_PLAIN, OFF_g_q; lia)
  end.
  (* 0x1425c sw s1, 0(a0) (g_q[nq] = serial) *)
  zstep.
  (* the two stores are the model's set_Q_at then set_g_nq (o4t4_appw) *)
  assert (L1 : Z.of_nat (length (upd Bw (OFF_g_q + 4 * g_nq Bw) (put 4 (g_ncmd B1)))) = W_LEN)
    by (apply op4_len_put; [exact LBz | lia | cbn [Z.of_nat]; lia]).
  assert (F1 : g_fail_next (upd Bw (OFF_g_q + 4 * g_nq Bw) (put 4 (g_ncmd B1))) = g_fail_next Bw)
    by (apply op4_fn_put; [exact LBz | lia | cbn [Z.of_nat]; lia | left; cbn [Z.of_nat]; lia]).
  assert (FN6 : g_fail_next B6 <= 1).
  { rewrite EB6. unfold set_g_nq, set_Q_at.
    rewrite op4_fn_put; [rewrite F1; exact HFN | exact L1 | lia | cbn [Z.of_nat]; lia | right; lia]. }
  lazymatch goal with HW : rw_cells rsegs ?m6 W_BASE_PLAIN [CB _ ?W6] |- _ =>
    replace W6 with B6 in HW
      by (rewrite EB6; symmetry; change 64980 with OFF_g_nq; apply o4t4_appw; [exact LBz | lia]);
    pose proof (op4_mem_after_call data D Sp lo 0 Bw B6 m0 m m6 _ HM0 ltac:(unfold LLVM_LOOP_K; lia)
                  MU6 WMO6 HMI HSTK HW FN6) as HM6
  end.
  apply HK. unfold op4_t4. do 21 eexists. split; [reflexivity|]. split; [exact HOK|].
  exists j30, j70. exact HM6.
Qed.

(* ---------------------------------------------------------------- 0x14120 -> 0x14260, at >= 0: replace *)
Lemma o4t4_coal : forall Sp lo ops c3 B1 before display key at_ Bw B6 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
    s11 F fc (Q : machine_state -> Prop) (rr t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) m,
  o4_tok D ops c3 B1 before display key ->
  o4_tmem data D Sp lo c3 B1 before display key Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  0 <= at_ < CMDS_MAX -> Q_at Bw at_ < CMDS_MAX ->
  B6 = set_Q_at (set_Cmd_st Bw (Q_at Bw at_) REPLACED) at_ (g_ncmd B1) ->
  (forall ms', op4_t4 data D m0 gp tp Sp lo ops c3 B1 before display key B6
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 x8 (Z_to_bv 64 (g_ncmd B1)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 at_) (Z_to_bv 64 (data + fi_off (o4_c4 D c3))) (Z_to_bv 64 0x37558)
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (o4_n D c3)) x23 (Z_to_bv 64 1)
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
             (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14120) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 B1 before display key at_ Bw B6 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    rr t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 m HOK (j30 & j70 & HM) HAT HQ EB6 HK.
  pose proof HOK as (_ & HSER). unfold CMDS_MAX in HSER, HAT, HQ.
  pose proof HM as HM0. unfold op4_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  clear HMU0 HWMO0 HD HRO HRW HOW HOWIN.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length Bw) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_LOOP_K, LLVM_FRAME in HLO, HSP2.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_cmd. wk_eq_fact OFF_g_q.
  pose proof (u_at_range Bw (OFF_g_q + 4 * at_) 4) as RQ. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ.
  change (u_at Bw (OFF_g_q + 4 * at_) 4) with (Q_at Bw at_) in RQ.
  assert (EAq : A_Cmd_st (Q_at Bw at_) = 19912 + 40 * Q_at Bw at_) by (unfold A_Cmd_st, OFF_g_cmd; lia).
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU6.
  pose proof (wmono_refl rsegs m) as WMO6.
  (* 0x14120 sext.w a0, s2 (at >= 0); 0x14124 bltz a0, falls through to 0x14128 *)
  do 2 zstep.
  if_cases K; zify_cond K.
  { exfalso. rewrite Z.add_0_r, (bv_swrap_small 32) in K by (change (bv_half_modulus 32) with (2 ^ 31); lia).
    rewrite Z.mod_small in K by lia. lia. }
  (* 0x14128 slli s2, s2, 2; 0x1412c auipc a0, 0x2d; 0x14130 addi a0, a0, 0x42c (0x41558 = W_BASE_PLAIN + OFF_g_q);
     0x14134 add a0, a0, s2 (&g_q[at]) *)
  do 4 zstep.
  (* a0 = 0x41558 + (at << 2), the address of g_q[at] *)
  lazymatch goal with |- context [Z_to_bv 64 (267608 + ?X)] =>
    replace (Z_to_bv 64 (267608 + X)) with (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_q + 4 * at_)))
      by (f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.mod_small by lia; unfold W_BASE_PLAIN, OFF_g_q; lia)
  end.
  (* 0x14138 lwu a1, 0(a0) (q = g_q[at]) *)
  zstep.
  change (u_at Bw (OFF_g_q + 4 * at_) 4) with (Q_at Bw at_).
  (* 0x1413c li a2, 0x28; 0x14140 mul a1, a1, a2; 0x14144 add a1, s4, a1 (s4 = 0x37558 = W_BASE_PLAIN + OFF_g_cmd:
     &g_cmd[q]) *)
  do 3 zstep.
  (* a1 = 0x37558 + q * 40 *)
  lazymatch goal with |- context [Z_to_bv 64 (226648 + ?X)] =>
    replace (Z_to_bv 64 (226648 + X)) with (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (Q_at Bw at_)))
      by (f_equal; rewrite ?Z.mod_small by lia; unfold W_BASE_PLAIN; lia)
  end.
  (* 0x14148 li a2, 3; 0x1414c sw a2, 0(a1) (g_cmd[q].st = REPLACED); 0x14150 j 0x1425c;
     0x1425c sw s1, 0(a0) (g_q[at] = serial) *)
  do 4 zstep.
  pose proof (o4t4_wr Bw (put 4 REPLACED) (A_Cmd_st (Q_at Bw at_)) LBz ltac:(lia)
                ltac:(rewrite length_put; cbn [Z.of_nat]; lia)) as [L1 F1].
  pose proof (o4t4_wr _ (put 4 (g_ncmd B1)) (OFF_g_q + 4 * at_) L1 ltac:(lia)
                ltac:(rewrite length_put; cbn [Z.of_nat]; lia)) as [L2 F2].
  assert (FN6 : g_fail_next B6 <= 1)
    by (rewrite EB6; unfold set_Q_at, set_Cmd_st; rewrite F2, F1; exact HFN).
  lazymatch goal with HW : rw_cells rsegs ?m6 W_BASE_PLAIN [CB _ ?W6] |- _ =>
    replace W6 with B6 in HW by (rewrite EB6; reflexivity);
    pose proof (op4_mem_after_call data D Sp lo 0 Bw B6 m0 m m6 _ HM0 ltac:(unfold LLVM_LOOP_K; lia)
                  MU6 WMO6 HMI HSTK HW FN6) as HM6
  end.
  apply HK. unfold op4_t4. do 21 eexists. split; [reflexivity|]. split; [exact HOK|].
  exists j30, j70. exact HM6.
Qed.

Lemma op4_tag4 : op4_tag4_stmt data D.
Proof.
  intros Sp lo ops c3 B1 before display key at_ B5 B6 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    MCC H HAT HB6 HK.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x21 & x24 & t3 & t4 & t5 & t6 & m &
                 -> & HOK & (j30 & j70 & HM)).
  pose proof HOK as ((HOPS & HC & HBEF & HDISP & HKEY) & HSER).
  unfold CMDS_MAX in HSER, HAT.
  pose proof HM as HM0.
  unfold op4_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  clear HMU0 HWMO0 HRO HD HOW HOWIN.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B5) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_LOOP_K, LLVM_FRAME in HLO, HSP2.
  unfold op4_fr in HRW. cbn [app] in HRW.
  pose proof (proj1 (proj1 HRW)) as WFR. cbn [cells_wf cell_wf] in WFR.
  destruct WFR as (_ & _ & _ & _ & _ & _ & LJ30 & LCS & LJ70 & _).
  pose proof (o4t4_cb_len _ _ _ _ LCS) as LCB.
  pose proof (o4t4_len_rng c3) as HLEN.
  (* the struct cell as the cells its fields are, for the three loads *)
  assert (HRWs : rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)));
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 (Z_to_bv 64 (bv_swrap 32 before)); CB 32 j30] ++
     [CB 24 (o4_cb D B1 c3); CB 1 [b8 (o4_len D c3)]; CB 1 [b8 display]; CB 2 [b8 0; b8 0]; CB 4 (put 4 key)] ++
     [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { eapply (op4_rw_mid m Sp _ [CB 32 (o4_cs D B1 c3 display key)]); [exact HRW | | apply o4t4_cs_cells].
    cbn [cells_wf cell_wf length]. rewrite length_put. repeat split. exact LCB. }
  cbn [app] in HRWs. clear HRW.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_s. wk_eq_fact OFF_g_cmd. wk_eq_fact OFF_g_q.
  wk_eq_fact OFF_g_nq.
  (* 0x140ec ld s5, 8(sp) (&g_s); 0x140f0 addi s8, zero, 1; 0x140f4 bnez s7 (want) *)
  do 3 zstep.
  if_cases K; zify_cond K.
  - (* want <> SPEC_OK: straight to 0x14260, nothing recorded, B6 = B5 *)
    assert (EW : (o4_want D B1 c3 at_ =? SPEC_OK) = false)
      by (apply Z.eqb_neq; intros E; apply K; rewrite E; reflexivity).
    rewrite EW in HB6. injection HB6 as <-.
    apply HK. unfold op4_t4. do 21 eexists. split; [reflexivity|]. split; [exact HOK|].
    exists j30, j70. exact HM0.
  - (* want = SPEC_OK *)
    assert (EW0 : o4_want D B1 c3 at_ = SPEC_OK).
    { destruct (o4t4_want_rng B1 c3 at_) as [E|[E|E]]; [| |exact E]; exfalso; rewrite E in K;
        unfold SPEC_E_REFUSED, SPEC_E_SPACE in K; cbv in K; congruence. }
    rewrite EW0, Z.eqb_refl in HB6.
    (* 0x140f8 lw a0, 0x6c(sp) (c.key); 0x140fc lbu a1, 0x69(sp) (c.display); 0x14100 lbu a2, 0x68(sp) (c.len) *)
    do 3 zstep.
    cbv beta.
    rewrite (o4t4_b8u display) by lia. rewrite (o4t4_b8u (o4_len D c3)) by lia. rewrite o4t4_lw_put.
    clear HRWs.
    assert (EA : A_Cmd_st (g_ncmd B1) = 19912 + 40 * g_ncmd B1) by (unfold A_Cmd_st, OFF_g_cmd; lia).
    pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU6.
    pose proof (wmono_refl rsegs m) as WMO6.
    (* 0x14104 sw s8, 0(s0) (st = PENDING); 0x14108 sw a0, 4(s0) (key); 0x1410c sw a1, 8(s0) (display);
       0x14110 sb a2, 0x24(s0) (len) *)
    do 4 zstep.
    pose proof (o4t4_w4_facts B5 (g_ncmd B1) key display (o4_len D c3) LBz ltac:(lia)) as (LW4 & FW4).
    lazymatch goal with HW : rw_cells rsegs ?m4 W_BASE_PLAIN [CB _ _] |- _ =>
      rewrite o4t4_w4 in HW;
      assert (HM4 : op4_mem data D Sp lo
                      (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 (g_ncmd B1) PENDING) (g_ncmd B1) key)
                                     (g_ncmd B1) display) (g_ncmd B1) (o4_len D c3)) m0 m4
                      (op4_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
                         (o4_cs D B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
        by (eapply (op4_mem_after_call data D Sp lo 0 B5 _ m0 m m4);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MU6 | exact WMO6 | exact HMI | exact HSTK | exact HW
            | rewrite FW4; exact HFN ])
    end.
    (* 0x14114 addi a0, s0, 0xc (&g_cmd[serial].bytes); 0x14118 addi a1, sp, 0x50 (c.bytes); 0x1411c jal memcpy
       (a2 = c.len from 0x14100): memcpy(g_cmd[serial].bytes, c.bytes, c.len) (:1112) *)
    do 3 zstep.
    pose proof HM4 as HM4c. unfold op4_mem in HM4c.
    destruct HM4c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMI4 & _ & HWM4 & _ & HRW4 & _).
    (* the source: the first len bytes of the struct at sp + 0x50, which are the first len of its 24 bytes *)
    pose proof (o4t4_cell_bytes _ Sp
                  [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s));
                   C8 (Z_to_bv 64 (fi_n (o4_c4 D c3))); C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
                   C8 (Z_to_bv 64 (bv_swrap 32 before)); CB 32 j30]
                  32 (o4_cs D B1 c3 display key)
                  [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                  80 HRW4 eq_refl) as CS4.
    unfold o4_cs, cmd_struct in CS4. apply bytes_at_app in CS4. destruct CS4 as [CB4 _].
    rewrite <- (firstn_skipn (Z.to_nat (o4_len D c3)) (o4_cb D B1 c3)) in CB4.
    apply bytes_at_app in CB4. destruct CB4 as [SRC _].
    (* the destination: len bytes of the world at W_BASE_PLAIN + A_Cmd_bytes serial *)
    pose proof (wm_piece rsegs W_BASE_PLAIN _ _ (A_Cmd_bytes (g_ncmd B1)) (o4_len D c3) _ HWM4 eq_refl
                  ltac:(unfold A_Cmd_bytes; lia) ltac:(lia) ltac:(unfold A_Cmd_bytes; lia)) as DST.
    replace (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1) + 12))
      with (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_bytes (g_ncmd B1)))
      by (f_equal; unfold A_Cmd_bytes, A_Cmd_st; lia).
    eapply evt_cut.
    { eapply MCC with (src := firstn (Z.to_nat (o4_len D c3)) (o4_cb D B1 c3)).
      - rewrite unsigned_lit by lia. exact SRC.
      - rewrite unsigned_lit by lia. rewrite length_firstn. lia.
      - rewrite !unsigned_lit by (unfold A_Cmd_bytes; lia). exact DST.
      - rewrite !unsigned_lit by (unfold A_Cmd_bytes; lia). right. unfold A_Cmd_bytes. lia.
      - exact HMI4. }
    intros ms' Hpost. unfold memcpy_post in Hpost.
    destruct Hpost as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m5 &
                       -> & MU5 & WMO5 & MI5 & CZ5 & _).
    rewrite !unsigned_lit in MU5, CZ5 by (unfold A_Cmd_bytes; lia).
    pose proof (o4t4_wr _ (firstn (Z.to_nat (o4_len D c3)) (o4_cb D B1 c3)) (A_Cmd_bytes (g_ncmd B1)) LW4
                  ltac:(unfold A_Cmd_bytes; lia)
                  ltac:(rewrite length_firstn; unfold A_Cmd_bytes, OFF_g_fail_next; lia)) as [LBw FBw].
    pose proof (op4_mem_after_fill data D Sp lo _ m0 _ m5 (A_Cmd_bytes (g_ncmd B1)) (o4_len D c3) _ _ HM4 MU5 WMO5
                  MI5 CZ5 ltac:(unfold A_Cmd_bytes; lia) ltac:(lia) ltac:(unfold A_Cmd_bytes; lia)
                  ltac:(rewrite FBw, FW4; exact HFN)) as HM5.
    rewrite (ret_pc_even 0x14120) by (first [lia | reflexivity]).
    (* 0x14120: the model's two arms (o4_rec, :1113-1115) *)
    unfold o4_rec in HB6. cbv zeta in HB6.
    destruct HAT as [-> | HAT].
    + (* at = -1: append at g_q[g_nq] *)
      change ((-1) mod 4294967296) with 4294967295.
      change (0 <=? -1) with false in HB6. cbv iota in HB6.
      lazymatch type of HB6 with context [if CMDS_MAX <=? ?nq then _ else _] =>
        destruct (CMDS_MAX <=? nq) eqn:ENQ end; [discriminate HB6|].
      injection HB6 as EB6. apply Z.leb_gt in ENQ.
      eapply o4t4_app; [exact HOK | exists j30, j70; exact HM5 | exact ENQ | exact (eq_sym EB6) | exact HK].
    + (* 0 <= at < CMDS_MAX: replace g_q[at] *)
      rewrite (Z.mod_small at_ 4294967296) by lia.
      replace (0 <=? at_) with true in HB6 by (symmetry; apply Z.leb_le; lia). cbv iota in HB6.
      lazymatch type of HB6 with context [if CMDS_MAX <=? ?q then _ else _] =>
        destruct (CMDS_MAX <=? q) eqn:EQ end; [discriminate HB6|].
      injection HB6 as EB6. apply Z.leb_gt in EQ.
      eapply o4t4_coal; [exact HOK | exists j30, j70; exact HM5 | unfold CMDS_MAX; lia | exact EQ
        | exact (eq_sym EB6) | exact HK].
Qed.

End T4.
